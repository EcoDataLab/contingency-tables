#!/usr/bin/env python3
"""Private Windows/WHPX revised-sampler supervisor using the retained bootstrap.

prepare creates one fresh sparse child/config after immutable-byte/backing checks.
detach starts the separately authorized owned VM; nothing launches on import.
No installers, services, settings, sharing, forwarding or arbitrary console inbox.
"""
from __future__ import annotations
import argparse
import ctypes
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

GIB = 1024**3
ACTIVE_MEMORY_FLOOR = int(1.5 * GIB)
ACTIVE_DISK_FLOOR = 20 * GIB
MIN_BACKING_FREE = 40 * GIB
MAX_OWNED_OVERLAY = 16 * GIB
RESOURCE_POLL_SECONDS = 1
EXPECTED = {
    "stonking-server-cloudimg-amd64.img": "c93d013ac1116adf585bdd84d2e8b51039fc623fb8c6d33b70da4075c4934118",
    "preflight-overlay.qcow2": "5bde6d27a87b66365f35c87e03144f914c864dda47beccc2b0734f3edfcef1b7",
    "tool-bootstrap-overlay.qcow2": "da762be8cf147ef834961359511d3cf7cf5d47e04da2ed440f2c898befca9a91",
    "qemu/ucrt64/bin/qemu-system-x86_64.exe": "a812b50865ffcc7ddd43f9c33e9bb1ed7b3501c1f847ee99ede8d4b4a4a93742",
    "qemu/ucrt64/bin/qemu-img.exe": "b4ef313ad2bd5070e44a5cccb50d8c2529dd68303c44ef8926b4c5a38ca219ff",
}
COMMAND = b"bash /home/verifier/checkpoint11-start.sh\r\n"
CAP = 12600
PHASE_CAPS = {"install":600,"preflight":300,"authenticate":5400,"repair":7200,"proof":8100,"collect":600}
BOOT_CAP = 600
CLEANUP_RESERVE = 600
TAIL_LIMIT = 256 * 1024
STATUS_REPLACE_RETRY_SECONDS = 2
STATUS_REPLACE_ATTEMPTS = 21

class SupervisorError(RuntimeError):
    pass

def digest(path, deadline=None):
    with Path(path).open("rb") as stream:
        if deadline is None:
            return hashlib.file_digest(stream, "sha256").hexdigest()
        value = hashlib.sha256()
        while True:
            if time.monotonic() >= deadline:
                raise SupervisorError("Bounded immutable-file recheck exhausted")
            chunk = stream.read(1024 * 1024)
            if not chunk:
                return value.hexdigest()
            value.update(chunk)

def save(path, value):
    path = Path(path)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    deadline = time.monotonic() + STATUS_REPLACE_RETRY_SECONDS
    for attempt in range(STATUS_REPLACE_ATTEMPTS):
        try:
            temporary.replace(path)
            return
        except PermissionError as error:
            if (os.name != "nt" or getattr(error, "winerror", None) not in (5, 32)
                    or attempt + 1 == STATUS_REPLACE_ATTEMPTS or time.monotonic() >= deadline):
                raise
            time.sleep(min(0.1, max(0, deadline - time.monotonic())))

class Memory(ctypes.Structure):
    _fields_ = [("length", ctypes.c_uint32), ("load", ctypes.c_uint32)] + [
        (name, ctypes.c_uint64) for name in ("total_phys", "avail_phys", "total_page", "avail_page",
                                           "total_virtual", "avail_virtual", "avail_extended")]

class ProcessMemory(ctypes.Structure):
    _fields_ = [("cb", ctypes.c_uint32), ("page_faults", ctypes.c_uint32)] + [
        (name, ctypes.c_size_t) for name in ("peak_working_set", "working_set", "quota_peak_paged",
            "quota_paged", "quota_peak_nonpaged", "quota_nonpaged", "pagefile", "peak_pagefile")]

def available_memory():
    memory = Memory()
    memory.length = ctypes.sizeof(memory)
    if not ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(memory)):
        raise SupervisorError("Cannot measure current Windows available memory")
    return memory.avail_phys

def process_memory(process):
    memory = ProcessMemory()
    memory.cb = ctypes.sizeof(memory)
    if not ctypes.windll.psapi.GetProcessMemoryInfo(ctypes.c_void_p(int(process._handle)), ctypes.byref(memory), memory.cb):
        raise SupervisorError("Cannot measure owned emulator working set")
    return {"qemu_working_set_bytes": memory.working_set, "qemu_peak_working_set_bytes": memory.peak_working_set}

def check_files(retained, deadline=None):
    deadline = time.monotonic() + 300 if deadline is None else deadline
    observed = {}
    for relative, expected in EXPECTED.items():
        path = retained / relative
        if not path.is_file() or path.is_symlink() or digest(path, deadline) != expected:
            raise SupervisorError(f"Retained artifact mismatch: {relative}")
        observed[relative] = expected
    return observed

def image_info(retained, image):
    result = subprocess.run([str(retained / "qemu/ucrt64/bin/qemu-img.exe"), "info", "--backing-chain",
                             "--output=json", str(image)], text=True, capture_output=True, timeout=60)
    if result.returncode:
        raise SupervisorError("Pinned image utility could not inspect backing chain")
    return json.loads(result.stdout)

def check_bootstrap_chain(retained, chain):
    expected = [retained / name for name in ("tool-bootstrap-overlay.qcow2", "preflight-overlay.qcow2",
                                            "stonking-server-cloudimg-amd64.img")]
    if len(chain) != 3 or [Path(entry["filename"]).resolve() for entry in chain] != expected:
        raise SupervisorError("Retained bootstrap backing chain differs from exact preserved layers")
    if any(entry["format"] != "qcow2" for entry in chain):
        raise SupervisorError("Unexpected retained image format")
    if any(entry.get("dirty-flag") or entry.get("format-specific", {}).get("data", {}).get("corrupt") for entry in chain):
        raise SupervisorError("Retained layer reports dirty/corrupt state")

def prepare(retained: Path, run: Path, seed: Path, min_memory_gib: float):
    if os.name != "nt":
        raise SupervisorError("Retained runtime supervisor requires Windows")
    retained, run, seed = retained.resolve(), run.resolve(), seed.resolve()
    if run.exists() or not run.is_relative_to(retained) or not seed.is_file() or not seed.is_relative_to(retained):
        raise SupervisorError("Requires fresh run below retained directory and an existing reviewed local seed")
    if not 12 <= min_memory_gib <= 128:
        raise SupervisorError("Standalone sampler minimum memory gate must be at least 12 GiB")
    seed_manifest = json.loads(seed.with_suffix(".manifest.json").read_text())
    if seed_manifest.get("entrypoint_audit_status") != "compiled_and_standard_axiom_audited" or seed_manifest.get("iso_sha256") != digest(seed):
        raise SupervisorError("Actual native audit and authenticated ISO binding required before preparation")
    hashes = check_files(retained)
    chain = image_info(retained, retained / "tool-bootstrap-overlay.qcow2")
    check_bootstrap_chain(retained, chain)
    if shutil.disk_usage(retained).free < MIN_BACKING_FREE:
        raise SupervisorError("Less than versioned 40 GiB backing disk free")
    run.mkdir()
    overlay = run / "sampler-overlay.qcow2"
    result = subprocess.run([str(retained / "qemu/ucrt64/bin/qemu-img.exe"), "create", "-f", "qcow2", "-F", "qcow2",
                             "-b", str(retained / "tool-bootstrap-overlay.qcow2"), str(overlay), "80G"],
                            text=True, capture_output=True, timeout=60)
    if result.returncode:
        raise SupervisorError("Could not create fresh owned sparse child")
    config = {"schema_version": 1, "scope": "original authentication then bounded historical cold serial proof; v2 guard", "retained_root": str(retained),
              "run_dir": str(run), "seed": str(seed), "seed_sha256": digest(seed),
              "overlay": str(overlay), "overlay_sha256_before_launch": digest(overlay),
              "preserved_sha256": hashes, "bootstrap_backing_chain": chain,
              "wall_clock_cap_seconds": CAP, "guest_vcpus": 1, "guest_ram_mib": 10240,
              "minimum_available_host_bytes": int(min_memory_gib * GIB),
              "minimum_free_backing_disk_bytes": MIN_BACKING_FREE,
              "network": "none; no NIC/forwarding/listeners/TAP/sharing",
              "prepared_unix": time.time(), "preparation_stdout": result.stdout,
              "supervisor_sha256": digest(__file__)}
    config["python_executable"] = str(Path(sys.executable).resolve())
    config["python_executable_sha256"] = digest(sys.executable)
    config["seed_manifest_sha256"] = digest(seed.with_suffix(".manifest.json"))
    config["phase_caps_seconds"] = PHASE_CAPS
    config["active_host_available_floor_bytes"] = ACTIVE_MEMORY_FLOOR
    config["active_backing_disk_floor_bytes"] = ACTIVE_DISK_FLOOR
    config["maximum_owned_overlay_bytes"] = MAX_OWNED_OVERLAY
    config["resource_poll_seconds"] = RESOURCE_POLL_SECONDS
    save(run / "supervisor-config.json", config)
    print(json.dumps(config, indent=2))

def validate_config(config, config_path):
    retained, run = Path(config["retained_root"]).resolve(), Path(config["run_dir"]).resolve()
    if config_path.resolve() != run / "supervisor-config.json" or not run.is_relative_to(retained):
        raise SupervisorError("Run/config path mismatch")
    if config["wall_clock_cap_seconds"] != CAP or config["guest_vcpus"] != 1 or config["guest_ram_mib"] != 10240:
        raise SupervisorError("Sampler resource/cap profile changed")
    if config.get("phase_caps_seconds") != PHASE_CAPS:
        raise SupervisorError("Phase caps changed")
    if config.get("maximum_owned_overlay_bytes") != MAX_OWNED_OVERLAY or config.get("resource_poll_seconds") != RESOURCE_POLL_SECONDS:
        raise SupervisorError("Versioned physical growth profile changed")
    if config.get("active_host_available_floor_bytes") != ACTIVE_MEMORY_FLOOR or config.get("active_backing_disk_floor_bytes") != ACTIVE_DISK_FLOOR:
        raise SupervisorError("Active resource stop floors changed")
    if config["preserved_sha256"] != EXPECTED or config["minimum_available_host_bytes"] < 12 * GIB:
        raise SupervisorError("Artifact pins or host memory gate changed")
    if config["minimum_free_backing_disk_bytes"] != MIN_BACKING_FREE or config["supervisor_sha256"] != digest(__file__):
        raise SupervisorError("Disk gate or supervisor body changed")
    if str(Path(sys.executable).resolve()) != config["python_executable"] or digest(sys.executable) != config["python_executable_sha256"]:
        raise SupervisorError("Prepared host Python runtime changed")
    seed, overlay = Path(config["seed"]).resolve(), Path(config["overlay"]).resolve()
    if not seed.is_relative_to(retained) or overlay != run / "sampler-overlay.qcow2":
        raise SupervisorError("Seed/owned overlay scope changed")
    if digest(seed) != config["seed_sha256"] or digest(overlay) != config["overlay_sha256_before_launch"]:
        raise SupervisorError("Seed or fresh unused child changed")
    if digest(seed.with_suffix(".manifest.json")) != config["seed_manifest_sha256"]:
        raise SupervisorError("Seed/audit manifest changed")
    check_files(retained)
    check_bootstrap_chain(retained, image_info(retained, retained / "tool-bootstrap-overlay.qcow2"))
    child_chain = image_info(retained, overlay)
    if len(child_chain) != 4 or Path(child_chain[0]["filename"]).resolve() != overlay or child_chain[0]["virtual-size"] != 80 * GIB:
        raise SupervisorError("Fresh sampler child chain/size changed")
    check_bootstrap_chain(retained, child_chain[1:])
    return retained, run, seed, overlay

def qemu_argv(retained, seed, overlay):
    return [str(retained / "qemu/ucrt64/bin/qemu-system-x86_64.exe"), "-L", str(retained / "qemu/ucrt64/share/qemu"),
            "-machine", "pc-q35-11.1", "-accel", "whpx,kernel-irqchip=off", "-cpu", "max", "-smp", "1", "-m", "10240",
            "-display", "none", "-serial", "stdio", "-monitor", "none", "-nic", "none", "-no-reboot",
            "-drive", f"if=virtio,format=qcow2,file={overlay}", "-drive", f"format=raw,media=cdrom,readonly=on,file={seed}"]

def stop_owned(process, state):
    if process.poll() is None:
        process.terminate()
        state["owned_qemu_terminate_sent"] = True
    try:
        return process.wait(timeout=15)
    except subprocess.TimeoutExpired:
        process.kill()
        state["owned_qemu_kill_after_grace"] = True
        return process.wait(timeout=5)

def research_processes():
    # Flat primitive projection only; never serialize a provider object graph.
    script = "$p=@(Get-CimInstance Win32_Process -Filter \"Name='qemu-system-x86_64.exe' OR Name='lean.exe' OR Name='leanir.exe'\"); @($p | ForEach-Object { [pscustomobject]@{pid=[int]$_.ProcessId;name=[string]$_.Name} }) | ConvertTo-Json -Compress -Depth 3"
    result = subprocess.run(["powershell", "-NoProfile", "-NonInteractive", "-Command", script], text=True, capture_output=True, timeout=15)
    if result.returncode:
        raise SupervisorError("Cannot measure current research process admission")
    return json.loads(result.stdout) if result.stdout.strip() else []

def owned_identity(process, argv):
    # The held Popen handle remains the termination authority. CIM independently
    # records only this launched child's primitive identity and command hash.
    script = "$p=Get-CimInstance Win32_Process -Filter 'ProcessId=" + str(process.pid) + "'; if($null -eq $p){exit 2}; $h=[Security.Cryptography.SHA256]::Create(); $c=[BitConverter]::ToString($h.ComputeHash([Text.Encoding]::UTF8.GetBytes([string]$p.CommandLine))).Replace('-','').ToLowerInvariant(); [pscustomobject]@{pid=[int]$p.ProcessId;parent_pid=[int]$p.ParentProcessId;creation_utc=$p.CreationDate.ToUniversalTime().ToString('o');exe_path=[string]$p.ExecutablePath;command_sha256=$c} | ConvertTo-Json -Compress -Depth 3"
    result = subprocess.run(["powershell", "-NoProfile", "-NonInteractive", "-Command", script], text=True, capture_output=True, timeout=15)
    if result.returncode:
        raise SupervisorError("Owned QEMU identity could not be observed")
    identity = json.loads(result.stdout)
    expected = hashlib.sha256(subprocess.list2cmdline(argv).encode()).hexdigest()
    if identity["pid"] != process.pid or identity["parent_pid"] != os.getpid() or Path(identity["exe_path"]).resolve() != Path(argv[0]).resolve() or identity["command_sha256"] != expected:
        raise SupervisorError("Owned QEMU identity disagrees with exact launch")
    identity["held_popen_handle"] = True
    return identity

def parse_tail(tail, state):
    text = tail.decode("utf-8", errors="replace").replace("\r\n", "\n").replace("\r", "\n")
    text = re.sub(r"\x1b\][\s\S]*?(?:\x07|\x1b\\)", "", text)
    text = re.sub(r"\x1b\[[0-?]*[ -/]*[@-~]", "", text)
    # cloud-init's serial output prefixes runcmd lines with guest uptime and
    # its process ID. Accept that exact observed logger form or the bare
    # marker; preserve anchoring and require a completed newline.
    if re.search(r"(?m)^(?:\[[ \t]*\d+(?:\.\d+)?\][ \t]+cloud-init\[\d+\]:[ \t]+)?MATH115_C11_PROVISION_READY\n", text):
        state["guest_provisioning_ready"] = True
    if re.search(r"(?m)(?:^|\n)verifier@[^\n:]+:[^\n]*\$ ", text):
        state["normal_verifier_console_prompt_observed"] = True
    for marker, field in (("MATH115_C11_CHECK_RESULT", "strict_exit_code"),
                          ("MATH115_C11_EVIDENCE_COLLECTION_RESULT", "collection_exit_code")):
        for value in re.findall(r"(?m)^" + marker + r"=(-?\d+)\n", text):
            code = int(value)
            if field in state and state[field] != code:
                raise SupervisorError("Conflicting result markers")
            state[field] = code
    phases = re.findall(r"(?m)^MATH115_C11_STAGE=(install|preflight|authenticate|repair|proof|collect)\n", text)
    if phases:
        phase = phases[-1]
        if phase != state.get("guest_phase"):
            if state.get("guest_phase") and list(PHASE_CAPS).index(phase) < list(PHASE_CAPS).index(state["guest_phase"]):
                raise SupervisorError("Guest phase moved backwards")
            state["guest_phase"] = phase
            state["guest_phase_observed_monotonic"] = time.monotonic()
    for digest_value in re.findall(r"(?m)^MATH115_C11_RUNTIME_FREEZE_SHA256=([0-9a-f]{64})\n", text):
        if state.get("runtime_freeze_sha256", digest_value) != digest_value:
            raise SupervisorError("Conflicting authenticated runtime hashes")
        state["runtime_freeze_sha256"] = digest_value
    for line in re.findall(r"(?m)^MATH115_C11_PROOF_PROGRESS=([^\n]{1,4096})\n", text):
        row = json.loads(line)
        if not isinstance(row, dict) or not (type(row.get("completed_modules")) is int and 0 <= row["completed_modules"] <= 679
                and type(row.get("completed_stages")) is int and 0 <= row["completed_stages"] <= 1362
                and isinstance(row.get("last_stage"), str) and len(row["last_stage"]) <= 256
                and row.get("last_status") in {"running", "passed", "failed", "none"}):
            raise SupervisorError("Malformed owned proof progress data")
        state["proof_progress"] = row  # Telemetry only; never an acceptance marker.
    return tail[-TAIL_LIMIT:]

def supervise(config_path):
    if os.name != "nt":
        raise SupervisorError("Requires Windows")
    config = json.loads(config_path.read_text())
    retained, run, seed, overlay = validate_config(config, config_path)
    status = run / "status.json"
    if status.exists():
        raise SupervisorError("Existing status; no duplicate/resume")
    free_memory, free_disk = available_memory(), shutil.disk_usage(run).free
    if free_memory < config["minimum_available_host_bytes"] or free_disk < config["minimum_free_backing_disk_bytes"]:
        raise SupervisorError("Fresh host resource gate not met; no VM spawned")
    existing = research_processes()
    if existing:
        raise SupervisorError("Standalone run requires no current Lean/LeanIR/QEMU process")
    argv = qemu_argv(retained, seed, overlay)
    state = {"status": "launching", "supervisor_pid": os.getpid(), "started_unix": time.time(),
             "wall_clock_cap_seconds": CAP, "argv": argv, "host_available_bytes_before": free_memory,
             "host_free_disk_bytes_before": free_disk, "seed_sha256": config["seed_sha256"],
             "scope": "bounded cold historical679-module proof after pre-admission normalization; no current research module claim", "console_command_dispatched": False}
    # Atomic reservation prevents two supervisors from opening the same child.
    with status.open("x") as reservation:
        reservation.write(json.dumps(state) + "\n")
    serial, stderr = run / "serial.log", run / "qemu-stderr.log"
    offset, tail, terminal, last_record = 0, b"", None, 0.0
    with serial.open("wb") as out, stderr.open("wb") as err:
        try:
            process = subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=out, stderr=err, close_fds=True)
        except BaseException as error:
            state.update(status="qemu_spawn_failed", error=repr(error))
            save(status, state)
            raise
        started = time.monotonic()
        deadline = started + CAP - CLEANUP_RESERVE
        cleanup_deadline = started + CAP
        state["qemu_pid"] = process.pid
        try:
            state["owned_qemu_identity"] = owned_identity(process, argv)
            save(status, state)
            while process.poll() is None:
                now = time.monotonic()
                if now >= deadline or time.time() >= state["started_unix"] + CAP - CLEANUP_RESERVE:
                    state["status"] = "timed_out"
                    break
                if (not state["console_command_dispatched"] or not state.get("guest_phase")) and now-started >= BOOT_CAP:
                    state["status"] = "boot_or_console_admission_timed_out"
                    break
                if state.get("guest_phase") and now-state["guest_phase_observed_monotonic"] >= PHASE_CAPS[state["guest_phase"]]:
                    state["status"] = "guest_phase_timed_out"
                    break
                with serial.open("rb") as log:
                    log.seek(offset)
                    chunk = log.read(65536)
                    offset = log.tell()
                tail = parse_tail(tail + chunk, state)
                if state.get("guest_provisioning_ready") and state.get("normal_verifier_console_prompt_observed") and not state["console_command_dispatched"]:
                    for byte in COMMAND:
                        if time.monotonic() >= deadline:
                            raise SupervisorError("Outer deadline reached during console dispatch")
                        process.stdin.write(bytes([byte]))
                        process.stdin.flush()
                        time.sleep(0.02)
                    state["console_command_dispatched"] = True
                    state["console_command"] = COMMAND.decode().rstrip("\r\n")
                if "strict_exit_code" in state and "collection_exit_code" in state:
                    terminal = terminal if terminal is not None else now
                    state["status"] = "bounded_proof_reported_pass" if state["strict_exit_code"] == state["collection_exit_code"] == 0 else "bounded_proof_reported_failure"
                    # The wrapper synchronizes its private layer before printing
                    # the final marker. Raw collection hash validation is later.
                    if now - terminal >= 10:
                        break
                if now - last_record >= RESOURCE_POLL_SECONDS:
                    state.update(process_memory(process), elapsed_seconds=now-started,
                                 host_available_bytes=available_memory(), host_free_disk_bytes=shutil.disk_usage(run).free,
                                 serial_bytes_read=offset, serial_parser_tail_bytes=len(tail), overlay_bytes=overlay.stat().st_size)
                    save(status, state)
                    if state["host_available_bytes"] < ACTIVE_MEMORY_FLOOR or state["host_free_disk_bytes"] < ACTIVE_DISK_FLOOR or state["overlay_bytes"] > MAX_OWNED_OVERLAY:
                        state.update(status="active_host_resource_floor_reached",
                                     active_host_available_floor_bytes=ACTIVE_MEMORY_FLOOR,
                                     active_backing_disk_floor_bytes=ACTIVE_DISK_FLOOR, maximum_owned_overlay_bytes=MAX_OWNED_OVERLAY)
                        break  # finally stops only this held, identified QEMU
                    last_record = now
                # Drain an existing full chunk promptly. A large evidence stream
                # must not be artificially limited to one 64-KiB read/250 ms.
                if len(chunk) < 65536:
                    time.sleep(0.25)
        except BaseException as error:
            state.update(status="supervisor_error", error=repr(error))
        finally:
            try:
                state["qemu_exit_code"] = stop_owned(process, state)
            except BaseException as error:
                state.update(status="owned_vm_cleanup_failed", cleanup_error=repr(error))
                save(status, state)
                raise
    # Drain bytes written immediately before natural process exit or shutdown.
    try:
        with serial.open("rb") as log:
            log.seek(offset)
            while chunk := log.read(65536):
                if time.monotonic() >= cleanup_deadline:
                    raise SupervisorError("Bounded terminal serial drain exhausted")
                tail = parse_tail(tail + chunk, state)
    except BaseException as error:
        state.update(status="terminal_serial_drain_failed", serial_drain_error=repr(error))
        save(status, state)
    if state["status"] == "launching":
        if "strict_exit_code" in state and "collection_exit_code" in state:
            state["status"] = "bounded_proof_reported_pass" if state["strict_exit_code"] == state["collection_exit_code"] == 0 else "bounded_proof_reported_failure"
        else:
            state["status"] = "vm_exited_without_complete_result"
    state.update(ended_unix=time.time(), elapsed_seconds=time.monotonic()-started,
                 owned_qemu_reaped=True)
    try:
        state["serial_sha256"] = digest(serial, cleanup_deadline)
        state["qemu_stderr_sha256"] = digest(stderr, cleanup_deadline)
        state["preserved_sha256_after"] = check_files(retained, cleanup_deadline)
    except BaseException as error:
        state.update(status="terminal_authentication_recheck_failed", immutable_recheck_error=repr(error))
    save(status, state)
    print(json.dumps(state, indent=2))
    return 0 if state["status"] == "bounded_proof_reported_pass" else 1

def detach(config_path):
    if os.name != "nt":
        raise SupervisorError("Requires Windows")
    config = json.loads(config_path.read_text())
    run = Path(config["run_dir"]).resolve()
    launch = run / "detached-launch.json"
    if launch.exists() or (run / "status.json").exists():
        raise SupervisorError("Existing launch/status; no duplicate")
    if digest(__file__) != config["supervisor_sha256"]:
        raise SupervisorError("Supervisor body changed after preparation")
    with launch.open("x") as reservation:
        reservation.write(json.dumps({"status": "detached_launch_reserved", "reserved_unix": time.time()}) + "\n")
    flags = subprocess.DETACHED_PROCESS | subprocess.CREATE_NEW_PROCESS_GROUP | subprocess.CREATE_BREAKAWAY_FROM_JOB
    with (run / "supervisor-stdout.log").open("wb") as out, (run / "supervisor-stderr.log").open("wb") as err:
        process = subprocess.Popen([sys.executable, str(Path(__file__).resolve()), "run", "--config", str(config_path.resolve())],
                                   stdin=subprocess.DEVNULL, stdout=out, stderr=err, close_fds=True, creationflags=flags)
    save(launch, {"supervisor_pid": process.pid, "launched_unix": time.time(), "creationflags": flags,
                  "supervisor_sha256": digest(__file__), "config_sha256": digest(config_path), "parent_exits_immediately": True})
    print(json.dumps({"supervisor_pid": process.pid, "launch_receipt": str(launch)}))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="mode", required=True)
    prep = sub.add_parser("prepare")
    prep.add_argument("--retained-root", type=Path, required=True)
    prep.add_argument("--run-dir", type=Path, required=True)
    prep.add_argument("--seed", type=Path, required=True)
    prep.add_argument("--minimum-free-host-gib", type=float, default=12)
    for mode in ("run", "detach"):
        sub.add_parser(mode).add_argument("--config", type=Path, required=True)
    args = parser.parse_args()
    if args.mode == "prepare":
        prepare(args.retained_root, args.run_dir, args.seed, args.minimum_free_host_gib)
    elif args.mode == "run":
        return supervise(args.config.resolve())
    else:
        detach(args.config.resolve())
    return 0

if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (SupervisorError, OSError, ValueError, KeyError) as error:
        print(f"Strict sampler VM refused: {error}", file=sys.stderr)
        raise SystemExit(1)
