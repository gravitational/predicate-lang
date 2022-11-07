import subprocess
from runpy import run_path
from types import FunctionType

from solver.teleport import TeleportNode, TeleportUser

import click
import yaml
import json

@click.group()
def main():
    pass


@main.command()
@click.argument("policy-file")
def export(policy_file):
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
@click.option("--sudo", "-s", is_flag=True)
@click.option("--debug", "-d", is_flag=True)
@click.option("--max", "-m", default=3)
@click.option("--username", "-u", type=str)
@click.option("--hostname", "-h", type=str)
def logins(policy_file, sudo, debug, max, username, hostname):
    click.echo("parsing policy...")
    module = run_path(policy_file)
    policy = module["Teleport"].p

    click.echo("listing users...")
    users = set(map(TeleportUser.parse, tctl_get(sudo, "users", username)))
    click.echo("found {} user(s)...".format(len(users)))
    for user in users:
        print(" - {}".format(user))

    click.echo("listing nodes...")
    nodes = set(map(TeleportNode.parse, tctl_get(sudo, "nodes", hostname)))
    click.echo("found {} node(s)...".format(len(nodes)))
    for node in nodes:
        print(" - {}".format(node ))

    for user in users:
        for node in nodes:
            logins = user.logins(node, policy, loud=debug, max=max)
            if len(logins) == 0:
                print("> user '{}' cannot access node '{}'".format(user.name, node.hostname))
            else:
                print("> user '{}' can access node '{}' with the following logins: {}".format(user.name, node.hostname, logins))

def tctl_get(sudo, resource_type, resource_name):
    if resource_name == None:
        query = resource_type
    else:
        query = "{}/{}".format(resource_type, resource_name)
    args = ["tctl", "get", query, "--format=json"]
    if sudo:
        args.insert(0, "sudo")

    result = subprocess.run(args, text=True, check=True, stdout=subprocess.PIPE)
    return json.loads(result.stdout)

@main.command()
@click.argument("policy-file")
def test(policy_file):
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
