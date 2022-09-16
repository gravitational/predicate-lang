from pathlib import Path
from runpy import run_path
from types import FunctionType
import click

from solver.teleport import (
    Node,
    Rules,
    Policy,
    User
)

@click.group()
def main():
    pass

@main.command()
@click.argument('policy-file')
def test(policy_file):
    env = {"Policy": Policy, "Rules": Rules, "User": User, "Node": Node}
    module = run_path(policy_file, env)
    policyClass = module["Policy"]
    testMethods = [x for x, y in policyClass.__dict__.items() if type(y) == FunctionType and x.startswith("test_")]
    click.echo(testMethods)

if __name__ == "__main__":
    main()
