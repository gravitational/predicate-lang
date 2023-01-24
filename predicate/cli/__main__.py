import subprocess
from runpy import run_path
from types import FunctionType

import click
import yaml

from cli.policy_utils import create_policy_file, get_policy
from lint.linter import Linter
from cli.output import print_colored, print_json


@click.group()
def main():
    pass


@main.command()
@click.argument("policy-file")
def export(policy_file):
    """
    Export to YAML compatible policy.
    """
    _, policy = get_policy(policy_file)

    # Dump the policy into a Teleport resource and write it to the terminal.
    obj = policy.export()
    serialized = yaml.dump(obj)
    click.echo(serialized)


@main.command()
@click.argument("policy-file")
@click.option("--sudo", "-s", is_flag=True)
def deploy(policy_file, sudo):
    """
    Export to YAML compatible policy and deploy to Teleport.
    """
    click.echo("parsing policy...")
    _, policy = get_policy(policy_file)

    click.echo("translating policy...")
    obj = policy.export()
    serialized = yaml.dump(obj)

    click.echo("deploying policy...")
    args = ["tctl", "create", "-f"]
    if sudo:
        args.insert(0, "sudo")

    subprocess.run(args, text=True, input=serialized, check=True)
    click.echo(f'policy deployed as resource "{policy.name}"')


@main.command()
@click.argument("policy-file")
def test(policy_file):
    """
    Test policy
    """

    # Extract the defined policy class and filter out all test functions
    class_name, _ = get_policy(policy_file)
    module = run_path(policy_file)
    policy_class = module[class_name]
    fns = {
        x: y
        for x, y in policy_class.__dict__.items()
        if isinstance(y, FunctionType) and x.startswith("test_")
    }

    # Run all the tests, catching any exceptions and reporting success/failure accordingly
    click.echo(f"Running {len(fns)} tests:")
    for name, functions in fns.items():
        try:
            functions(policy_class)
        except Exception as err:
            out = f"error -> {err}"
        else:
            out = "ok"

        click.echo(f"  - {name}: {out}")


@main.command()
@click.option("--policy", "-p", is_flag=True)
def new(policy):
    """
    Create a new policy based on template
    """
    if policy:
        value = click.prompt("Please enter a policy name", type=str)
        click.echo("creating policy...")
        # keeping "policies" as a default directory
        create_policy_file(value, "")
        click.echo(f'policy "{value}" created.')


@main.command()
@click.option('--out', type=click.Choice(['stdout', 'json'], case_sensitive=False))
@click.argument("policy_file_path")
def lint(out, policy_file_path):
    """
    Run Predicate linter on given file
    """
    lint_result = Linter(policy_file_path).run()
    if out is not None:
        if out.strip() == "json":
            print_json(lint_result)
    else:
        print_colored(lint_result)

if __name__ == "__main__":
    main()
