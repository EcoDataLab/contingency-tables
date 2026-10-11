# Exact unused-cache policy: startup authentication timeout

The reviewed source/policy passed **102 author offline tests and seven independent focused probes**. In the actual startup-only attempt, installation and real non-root sandbox preflight passed. Authentication then reached its **600-second deadline** with both stdout and stderr empty. No authentication return code or measured phase-elapsed field was captured, and no runtime freeze or plan output was produced.

The exact Cli policy was delivered and named in the invocation. **Its live acceptance or rejection is unobserved**; this timeout does not show that the Cli fix passed or failed. Live resolution/coverage of the 82 direct external imports remains unverified. Proof loading/compilation, export, kernel comparison and full strict checking were not run. This timeout remains permanent evidence; no future retry result is assumed.

| Actual stage | Captured result | Evidence |
| --- | --- | --- |
| Installation | Exit 0, 9.94 s; exact policy and repaired runner delivered | [Log](evidence/startup/install.stdout.log) |
| Strict sandbox preflight | Exit 0, 3.65 s; Landlock ABI 11/systemd/Landrun probes passed | [Log](evidence/startup/preflight.stdout.log) |
| Authentication | Timing stop at fixed 600 s; empty streams; no return code or measured elapsed captured | [Exact error framing](evidence/startup/failure.json), [stdout](evidence/startup/authenticate.stdout.log), [stderr](evidence/startup/authenticate.stderr.log) |
| Runtime freeze / plan | Not produced / not run | [Outcome](evidence/startup/outcome.json) |
| Cleanup | Owned guest/supervisor absent, guest reaped, tree empty, five pins/limits unchanged | [Receipt](evidence/startup/cleanup.json) |

The failure-file mtime minus recorded authentication start is about 600.04 seconds; it is timing corroboration, not a measured authentication elapsed field, CPU or I/O result. Per-phase authentication CPU, memory and cache I/O were not instrumented. No causal performance diagnosis is claimed.

The [configuration-repair checkpoint](../configuration-repair-v1/README.md), [later partial cache observation](../cache-observation-v1/README.md) and [original strict corpus](../../strict-sampler-challenge/README.md) remain unchanged. The earlier unnamed failure remains unnamed in its original receipt; only the later observation identified the absent Cli ancestor.

## Exact reviewed policy and source

[Policy](unused-cache-policy-candidate.json) SHA `4a73417e7aee4941a395d09c645f3622404643a74999f57d144e5f8b8a489833` names only

```
requested root: formal/.lake/packages/Cli/.lake/build/lib/lean
first missing:  formal/.lake/packages/Cli/.lake
required owner: Cli
```

A separate caller SHA binds those policy bytes. It neither creates a directory nor drops a root from the ten-root state/search inventory. Present Cli `.lake`, a different missing ancestor/root, files, links, filesystem errors, required Cli ownership or subsequent state drift reject. This is deliberately specific to the observed absent context, not a general unused-directory exception.

[Runner](runner/strict_sampler.py) SHA `acebbe349c5eb0d24cdba0181cc852f2f95c91ca94c56bfe056864dffb656e11` and [authenticator](runner/authenticate_runtime.py) SHA `82731b1ae43ee0d615aea6fe4420f29d224809b31b4dbfdd0bcbff9a519fee94` retain runtime schema 2, full ten-root states and fresh parent/present-root identity guards. Authentication and independent admission must rederive tracked source ownership and one present selected object for each of the **82 direct external imports**. If actual runtime confirms zero Cli ownership, report it only for that resolved direct set; it is not an independently audited complete transitive external-cache dependency graph. The expected two builtin/80 mathlib distribution remains source-only here.

All present cache directories retain complete keyset/byte/stat inventories and strict traversal-error checks. Create/remove cycles, changed parents, links and appearance of the permitted absent ancestor reject. Observer device/inode values are not reused as current identities. Source/policy/configuration/tool/cache/source-owner guards, original 679-source freeze, cold submitted proofs, aliases/symlinks, descriptor/native pins, standard axioms/default kernel and real strict sandbox rules remain in force. The [patch](implementation.patch) records the reviewed delta; the ineligible [runtime template](runner/runtime-template.json) remains a template, not actual evidence.

## Evidence boundaries

[Verification](verification.json), [provenance bindings](provenance-bindings.json), [independent saved-artifact review](evidence/independent-review.json) and [projection mappings](projection-map.json) bind the exact prepared bodies, delivered policy, actual invocation, seven locally rehashed host downloads/eight-member inventory, nine regular guest archive members and closed timeout/cleanup. The remote-only checking disk is a metadata pin, not a locally supplied/rehashed image. Process identities, account/host paths and serial/QMP transcripts are omitted. Relevant stage streams and complete timeout framing remain with declared guest-prefix substitutions; original/public hashes are separate.

The 102+7 tests are historical offline/mocked source-policy evidence, not a guest freeze. The final startup media's 54 package checks and metadata-only native-closure label review are preparation scopes. No tests or VM were rerun during this projection. Native-job closure is a resource/admission prerequisite, not new mathematical proof evidence for this startup. This attempt is separate from ordinary native/formal, default Linux and full strict checking. No numerical runtime degree is supplied.

Official pinned caches and sealed retained provenance remain trust inputs. The retained image is not externally reproducible exactly, and no measured portable Linux full-workload outer supervisor is supplied. A new compatible environment needs independently reviewed provenance and origin/runner freeze rather than editing the existing origin fields. Full submitted proof loading/export remain unexecuted even if a later plan succeeds.

## Source/test reproduction and retained-context replay

Location: `research/strict-sampler-checkpoints/unused-cache-policy-v1/`. Exact reviewed public-safe source, policy and tests are unchanged. These contributor commands are syntax-checked instructions, not actions performed during projection:

```sh
bash scripts/bootstrap_lean.sh
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover \
  -s research/strict-sampler-checkpoints/unused-cache-policy-v1/runner \
  -p 'test_*.py' -v
```

Use the original separate checking checkout/source overlays/Statement/Solution/native inputs and cold submitted proofs. Keep `unused-cache-policy-candidate.json` in this source package for the exact test imports; install its unchanged bytes as `strict-sampler-inputs/unused-cache-policy.json` under the trusted checkout `.tools/linux-verification`.

For the retained checking context only, use exact independent configuration and policy SHAs:

```sh
# CHECKOUT, RUNNER, RUNTIME and NATIVE_AUDIT are actual checking paths.
# CONFIG_PROVENANCE/CONFIG_SHA and POLICY/POLICY_SHA are separately bound inputs.
python3 -I "$RUNNER/authenticate_runtime.py" --root "$CHECKOUT" \
  --runner "$RUNNER/strict_sampler.py" --output "$RUNTIME" \
  --native-audit "$NATIVE_AUDIT" \
  --lake-config-provenance "$CONFIG_PROVENANCE" \
  --lake-config-provenance-sha256 "$CONFIG_SHA" \
  --unused-cache-policy "$POLICY" --unused-cache-policy-sha256 "$POLICY_SHA"
# Only if actual authentication emits a freeze: use its MATH115_C11_RUNTIME_FREEZE_SHA256.
python3 -I "$RUNNER/strict_sampler.py" --root "$CHECKOUT" \
  --runtime-freeze "$RUNTIME" --runtime-freeze-sha256 "$RUNTIME_SHA" \
  --plan --output "$CHECKOUT/.tools/linux-verification/unused-cache-plan-01"
```

The recorded attempt never reached the final command. Real non-root PAM/systemd/Landrun probes, source/resource/ownership gates and durable outer supervision remain required. No larger cap/profile, diagnostic mutation or automatic retry follows from this timeout. A later bounded performance investigation or retry must preserve this evidence and report its own outcome separately.
