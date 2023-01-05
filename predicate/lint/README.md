Predicate linter will help policy writers author safe and consistent rules.

```
# test single policy
$ predicate lint examples/access.py

# test policy directory
$ predicate lint examples

# JSON output
$ predicate lint examples/access.py --out=json
```

## How it works

- `Lint rule`: Defines what and how policy codes/files should be linted.
- `Lint rule file`: Rule file that extends `Lint rule` with configurable rules and policies. Some `Lint rule` such as detecting two duplicate policies can be self-contained (no additional configuration is required) while others, such as `no_allow` rule, requires an additional rule file. In practice, users will only need to update rule files. Check out sample [`no_allow` rule file](./tests/data/no_allow.py).
- `Lint config file`: Config file `predicatelint.yml` with active lint rules, rule files path, etc. Any configuration to update linter runtime will go here. Currently lint command expects this config file in the root directory of predicate. Here's a working [config file sample](../predicatelint.yml).
- Lint results are printed to stdout. JSON output is also supported.

## Lint rules:

### `no_allow`

Lint rule which enables policy administrators to forbid certain rules to be added to `allow` rule. When a new policy is created with a matching forbidden rule, running linter will verify the rule using `Predicate.equivalent` and report back with details. Only `allow` rule is evaluated.

Updating `no_allow` rule:

- First update the [`no_allow` rule file](./tests/data/no_allow.py) with new rule.
- Create a test policy file with violating "allow" rule.
- Run linter on this new policy file as `$ predicate lint <new policy file>`

## Dev workflow

### Adding new lint rule:

The process to add an entirely new lint rule would be:

- Write a new rule class in `lint/rule.py`.
- Update `predicatelint.yaml`.
- Update `Linter` class in `lint/linter.py` to add new lint rule class.

### Run tests

Test is expected to run from `predicate` directory.

```
# run all tests
$ pytest

# run linter tests
$ pytest lint/tests

```
