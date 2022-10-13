import subprocess
from runpy import run_path
from types import FunctionType

import click
import yaml


@click.group()
def main():
    pass


@main.command()
@click.argument("policy-file")
def export(policy_file):
    # Ugly python hack to load a module with a defined environment
    module = run_path(policy_file)

    # Grabs the class and directly reads the policy since it's a static member.
    policy = module["Teleport"].p

    # Dump the policy into a Teleport resource and write it to the terminal.
    obj = policy.export()
    serialized = yaml.dump(obj)
    click.echo(serialized)


@main.command()
@click.argument("policy-file")
@click.option("--sudo", "-s", is_flag=True)
def deploy(policy_file, sudo):
    click.echo("parsing policy...")
    module = run_path(policy_file)
    policy = module["Teleport"].p
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
    # Ugly python hack to load a module with a defined environment
    module = run_path(policy_file)

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
