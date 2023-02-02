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

    click.secho("-" * 9, fg='yellow')
    click.echo("Running predicate linter with config predicatelint.yml")
    click.echo("")

    total_reports = 0

    def print_report(elements):
        for key, value in elements.items():
            if key == "description":
                click.secho(value, fg='red')

            elif key == "category":
                if 'findings' in elements:
                    # we handle findings below separately
                    pass
                else:
                    click.echo(f"{key}: {value}")

            elif key == "code_snippet":
                # newline for code snippet
                click.echo(f"{key}: \n{value}")

            # In duplciate rule category, findings is a list of duplicate reports.
            elif key == "findings" and isinstance(value, list):
                for f in value:
                    for k, v in f.items():
                        if k == "description":
                            click.secho(v, fg='red')
                        elif k == "code_snippet":
                            click.echo(f"{k}: \n{v}")
                        else:
                            click.echo(f"{k}: {v}")

            else:
                click.echo(f"{key}: {value}")

    if len(lint_result[0]) >= 1:
        for file, data in lint_result[0].items():
            click.secho("-" * (get_terminal_size().columns // 2), fg='red')
            total_reports = total_reports + len(data)
            click.echo(f"File: {file}. " + click.style(f"Found {len(data)} rule violation(s).\n", fg='red'))

            for elements in data:
                print_report(elements)

    click.secho("-" * (get_terminal_size().columns // 2), fg='red')
    click.secho(f"Found total {total_reports} rule violation(s) in {len(lint_result[0])} file. \n", fg='red' if total_reports >= 1 else 'green')


def print_json(lint_result):
    """Prints JSON output"""
    total_reports = 0

    if len(lint_result[0]) >= 1:
        for _, data in lint_result[0].items():
            total_reports = total_reports + len(data)

    final_report = {
        "report_count": total_reports,
        "lint_report": lint_result[0]
    }
    click.echo(json.dumps(final_report, sort_keys=True, indent=4))
