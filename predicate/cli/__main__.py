from pathlib import Path
from runpy import run_path
from types import FunctionType

import click
import yaml

from solver import (
    Case,
    Default,
    Duration,
    ParameterError,
    Predicate,
    Select,
    StringLiteral,
    StringSetMap,
)

from solver.teleport import (
    LoginRule,
    Node,
    Options,
    OptionsSet,
    Policy,
    PolicyMap,
    PolicySet,
    Request,
    Review,
    Role,
    Rules,
    Thresholds,
    map_policies,
    try_login,
    User,
)

env = {item.__name__: item for item in [
    # General
    Case,
    Default,
    Duration,
    ParameterError,
    Predicate,
    Select,
    StringLiteral,
    StringSetMap,

    # Teleport
    LoginRule,
    Node,
    Options,
    OptionsSet,
    Policy,
    PolicyMap,
    PolicySet,
    Request,
    Review,
    Role,
    Rules,
    Thresholds,
    map_policies,
    try_login,
    User,
]}

@click.group()
def main():
    pass

@main.command()
@click.argument("policy-file")
def export(policy_file):
    # Ugly python hack to load a module with a defined environment
    module = run_path(policy_file, env)

    # Grabs the class and directly reads the policy since it's a static member.
    policy = module["Teleport"].p

    obj = policy.export()
    serialized = yaml.dump(obj)
    click.echo(serialized)

@main.command()
@click.argument("policy-file")
def test(policy_file):
    # Ugly python hack to load a module with a defined environment
    module = run_path(policy_file, env)

    # Extract the defined policy class and filter out all test functions
    policyClass = module["Teleport"]
    fns = {
        x: y
        for x, y in policyClass.__dict__.items()
        if isinstance(y, FunctionType) and x.startswith("test_")
    }

    # Run all the tests, catching any exceptions and reporting success/failure accordingly
    click.echo(f"Running {len(fns)} tests:")
    for name, fn in fns.items():
        try:
            fn(policyClass)
        except Exception as err:
            out = f"error -> {err}"
        else:
            out = "ok"

        click.echo(f"  - {name}: {out}")


if __name__ == "__main__":
    main()
