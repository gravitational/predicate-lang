from pathlib import Path
from runpy import run_path
from types import FunctionType

import click

from solver.teleport import Node, Policy, Rules, User


@click.group()
def main():
    pass


@main.command()
@click.argument("policy-file")
def test(policy_file):
    # These are the predicate items we supply to the policy definition
    env = {"Policy": Policy, "Rules": Rules, "User": User, "Node": Node}

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
            fn()
        except:
            out = "error"
        else:
            out = "ok"

        click.echo(f"  - {name}: {out}")


if __name__ == "__main__":
    main()
