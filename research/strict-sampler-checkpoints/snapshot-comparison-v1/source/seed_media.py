#!/usr/bin/env python3
"""Guest provisioning only: authenticated bytes from the already attached ISO.

No checking process, package installation, networking or host control occurs.
Readiness is emitted only after the owned read-only mount has been removed.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import pwd
import signal
import stat
import subprocess
import tempfile
import time

INPUT = Path('/home/verifier/checking/.tools/linux-verification/checkpoint11-inputs')
DEVICE = Path('/dev/sr0')
MOUNT_PARENT = Path('/run')
READY = Path('/var/lib/math115-c11-provision.ready')
WORK_CAP = 150
CLEANUP_CAP = 30
CURRENT_STEP = 'not_started'

def step(name):
    global CURRENT_STEP
    CURRENT_STEP = name

def mounted_names(mount):
    names = []
    with os.scandir(mount) as entries:
        for item in entries:
            names.append(item.name[:160])
            if len(names) == 8: break
    return names

def failed(error, names=()):
    """Attach bounded primitive diagnostics only for a failed operation."""
    error.media_step = CURRENT_STEP
    error.media_names = list(names)
    return error

def failure_data(error):
    return {'step':getattr(error,'media_step',CURRENT_STEP), 'error_type':type(error).__name__,
            'errno':getattr(error,'errno',None), 'filename':str(getattr(error,'filename',None))[:512],
            'filename2':str(getattr(error,'filename2',None))[:512],
            'message':str(error)[:512], 'mounted_root_names':getattr(error,'media_names',[])}

def require(ok, message):
    if not ok: raise RuntimeError(message)

def regular(path):
    require(not any(x.is_symlink() for x in (path, *path.parents)), 'Symlinked media input/destination')
    require(stat.S_ISREG(path.stat().st_mode), 'Need a regular media/input file')

def timed_out(*unused):
    raise TimeoutError('Seed media work cap reached')

def digest_file(path):
    with path.open('rb') as stream: return hashlib.file_digest(stream, 'sha256').hexdigest()

def run(manifest_sha):
    step('admission')
    require(os.geteuid() == 0, 'Media helper is only a cloud-init provisioning step')
    require(not READY.exists() and not READY.is_symlink(), 'Readiness already exists')
    manifest = INPUT / 'installation-manifest.json'
    step('installation_manifest')
    regular(manifest)
    raw = manifest.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == manifest_sha, 'Installation manifest hash changed')
    data = json.loads(raw)
    expected, size = data['archive_sha256'], data['archive_bytes']
    require(expected == '47e864e49025da1e505c32ae1c5f23428ed900b1ecc64468cb72478095824a84' and size == 82718286, 'Wrong frozen source archive')
    step('device')
    require(not DEVICE.is_symlink() and stat.S_ISBLK(DEVICE.stat().st_mode), 'Need the existing guest CD-ROM block device')
    target = INPUT / 'sources.tar.gz'
    require(not target.exists() and not target.is_symlink(), 'Existing archive; no duplicate provisioning')
    account = pwd.getpwnam('verifier')
    require(account.pw_uid > 0, 'Checking owner must be non-root')
    step('owned_mount_directory')
    mount = Path(tempfile.mkdtemp(prefix='math115-c11-seed-', dir=MOUNT_PARENT))
    temp = None; fd = None; published = None; error = None; mounted = False; names = []
    started = time.monotonic()
    previous = signal.signal(signal.SIGALRM, timed_out)
    signal.alarm(WORK_CAP)
    try:
        step('mount')
        subprocess.run(['/usr/bin/mount', '-t', 'iso9660', '-o', 'ro,nosuid,nodev,noexec', str(DEVICE), str(mount)], check=True, timeout=30, stdin=subprocess.DEVNULL)
        mounted = True
        require(os.path.ismount(mount), 'Owned seed mount was not observed')
        step('media_directory')
        names = mounted_names(mount)  # collected under work alarm; emitted only on failure
        step('media_archive')
        source = mount / 'sources.gz'; regular(source)
        require(source.stat().st_size == size, 'Media archive size differs')
        step('copy')
        fd, name = tempfile.mkstemp(prefix='.sources-', dir=INPUT); temp = Path(name)
        count = 0; digest = hashlib.sha256()
        output = os.fdopen(fd, 'wb'); fd = None
        with output, source.open('rb') as stream:
            while chunk := stream.read(1024 * 1024):
                count += len(chunk)
                require(count <= size, 'Media archive exceeded frozen size')
                digest.update(chunk); output.write(chunk)
            require(count == size and digest.hexdigest() == expected, 'Media archive digest/length differs')
            output.flush(); os.fsync(output.fileno())
            os.fchown(output.fileno(), account.pw_uid, account.pw_gid)
            os.fchmod(output.fileno(), 0o644)
        regular(temp)
        item = temp.stat()
        require(item.st_uid == account.pw_uid and item.st_gid == account.pw_gid and stat.S_IMODE(item.st_mode) == 0o644, 'Archive owner/mode differs')
        # Exclusive publication: never overwrite an existing checking input.
        step('publish')
        os.link(temp, target, follow_symlinks=False)
        published = (item.st_dev, item.st_ino)
        temp.unlink(); temp = None
        require(digest_file(target) == expected, 'Published archive digest differs')
        delivered = target.stat()
    except BaseException as failure:
        error = failed(failure, names)
    finally:
        signal.alarm(0)
        try:
            step('cleanup')
            # A timed-out mount may have attached before returning. Only this
            # newly created mountpoint is eligible for cleanup.
            if mounted or os.path.ismount(mount):
                subprocess.run(['/usr/bin/umount', str(mount)], check=True, timeout=CLEANUP_CAP, stdin=subprocess.DEVNULL)
                require(not os.path.ismount(mount), 'Owned seed mount remains')
            mount.rmdir()
        except BaseException as failure:
            error = failed(failure, names)
        finally:
            signal.signal(signal.SIGALRM, previous)
            try:
                if fd is not None: os.close(fd)
                if temp is not None: temp.unlink(missing_ok=True)
            except BaseException as failure:
                step('temporary_cleanup')
                error = failed(failure)
        if error is not None and published is not None and target.exists():
            item = target.lstat()
            if (item.st_dev, item.st_ino) == published: target.unlink()
    if error is not None: raise error
    try:
        step('delivered_archive')
        regular(target)
        current = target.stat()
        fields = ('st_dev', 'st_ino', 'st_size', 'st_uid', 'st_gid', 'st_mode', 'st_mtime_ns', 'st_ctime_ns')
        require(all(getattr(current,k) == getattr(delivered,k) for k in fields), 'Published archive changed during cleanup')
        step('readiness_file')
        READY.open('x').close()
    except BaseException as failure:
        if target.exists():
            item = target.lstat()
            if (item.st_dev, item.st_ino) == published: target.unlink()
        raise failed(failure)
    print('MATH115_C11_MEDIA_COPY_RESULT=' + json.dumps({'status':'passed', 'archive_sha256':expected, 'archive_bytes':size, 'checking_uid':account.pw_uid, 'checking_gid':account.pw_gid, 'owned_mount_removed':True, 'elapsed_seconds':time.monotonic()-started, 'work_cap_seconds':WORK_CAP, 'cleanup_cap_seconds':CLEANUP_CAP}, sort_keys=True), flush=True)
    print('MATH115_C11_PROVISION_READY', flush=True)

if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--installation-manifest-sha256', required=True)
    a = p.parse_args()
    try: run(a.installation_manifest_sha256)
    except BaseException as error:
        print('MATH115_C11_MEDIA_COPY_FAILED=' + json.dumps(failure_data(error),sort_keys=True), flush=True)
        raise SystemExit(1)
