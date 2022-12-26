"""
Copyright 2022 Gravitational, Inc

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
"""

from shutil import get_terminal_size
import json
import click


def print_colored(lint_result):
    """Default output"""
    if len(lint_result[1]) >= 1:
        click.secho("-" * (get_terminal_size().columns // 2), fg='red')
        click.secho(f"Found {len(lint_result[1])} error(s) during scan. \n", fg='red')
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
