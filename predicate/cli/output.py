import click
from shutil import get_terminal_size
import json

def print_colored(lint_result):
    """Default output"""
    if len(lint_result[1]) >= 1:
        click.secho("-" * (get_terminal_size().columns // 2), fg='red')
        click.secho(f"Found {len(lint_result[1])} error(s) during scan. \n", fg='red' )
        for errors in lint_result[1]:
            click.echo(f"{errors}")
            click.secho("-" * (get_terminal_size().columns // 4), fg='red')
        click.secho("-" * (get_terminal_size().columns // 2), fg='blue')

    for report in lint_result[0]:
        if len(lint_result[0]) > 1:
            click.secho("-" * (get_terminal_size().columns // 2), fg='yellow')
        for key, value in report.items():
            if key == "code_snippet":
                click.echo(f"{key}: \n{value}")
            else:
                click.echo(f"{key}: {value}")

    click.secho(f"Found {len(lint_result[0])} rule violation(s). \n", fg='red' if len(lint_result[0]) >= 1 else 'green')

def print_json(lint_result):
    """Prints JSON output"""
    click.echo(json.dumps(lint_result[0], sort_keys=True, indent=4))
