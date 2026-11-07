# Workflow YAML repair

[GitHub run 42304815295](https://github.com/EcoDataLab/contingency-tables/actions/runs/42304815295), at commit `95016355464ae4627a6805667fd4f8e8bba6cb08`, failed before any jobs were created. The public API reported failure and zero jobs. The install command on [line 20 of the submitted workflow](https://github.com/EcoDataLab/contingency-tables/blob/95016355464ae4627a6805667fd4f8e8bba6cb08/.github/workflows/tests.yml#L20) contained `--only-binary=:all:` in an unquoted YAML plain scalar. The colon followed by a space made the workflow invalid YAML.

The repair places the same shell command in a literal block scalar:

```yaml
run: |
  python -m pip install --only-binary=:all: -e '.[test]'
```

The old file's SHA-256 is `7217cfbcf3ba2fbdc76e8a9e194748805e9cb233478b113e021ba114a5a49c98`; the repaired file's is `eb7ad625139dd2e92e29220f06d8ea757b9b52a52ef6a3c584b674e9004893a2`. Byte comparison confirmed that this scalar representation is the only change. The shell command, dependency extra and test behavior are unchanged.

Local validation independently reproduced the old `Psych::SyntaxError`: “mapping values are not allowed in this context,” line 20, column 54. Both current workflow files parsed successfully, and all 15 `run` blocks passed `bash -n` without executing their commands. [verification.json](verification.json) records the failed run metadata, exact file and command hashes, parser error, tool versions and individual syntax-check results. This is local syntax validation, rather than a successful hosted CI run or a GitHub expression/schema validation.

The [original Python reliability receipt](../python-reliability-2026-11-06/README.md) remains unchanged, including its historical workflow hash. Its completed local runs remain 468 passed with no skips in the existing environment, and 468 tests run with 467 passed and one explicit formal-bootstrap skip in the fresh environment. Those local test executions did not parse the GitHub workflow. No Python suite was rerun for this YAML repair.

The YAML parsing check can be repeated without additional packages:

```sh
ruby -ryaml -e 'ARGV.each { |p| YAML.parse_file(p); puts "parsed #{p}" }' .github/workflows/*.yml
```

For the shell check, parse each workflow, extract every `jobs.*.steps[*].run` string, and pass that string to `bash -n` on standard input. The saved results cover both `.github/workflows/tests.yml` and `.github/workflows/formal-linux.yml`; they do not execute dependency installation, tests, formal builds or remote jobs.
