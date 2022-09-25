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
    env = {"Policy": Policy, "Rules": Rules, "User": User, "Node": Node}
    module = run_path(policy_file, env)
    policyClass = module["Test"]
    testFns = {
        x: y
        for x, y in policyClass.__dict__.items()
        if type(y) == FunctionType and x.startswith("test_")
    }
    for testName, testFn in testFns.items():
        success = False
        try:
            testFn()
        except:
            pass
        else:
            success = True

        out = "yes" if success else "no"
        click.echo(f"{testName}: {out}")


if __name__ == "__main__":
    main()
