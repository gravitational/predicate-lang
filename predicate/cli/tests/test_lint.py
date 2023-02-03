from click.testing import CliRunner
from cli.__main__ import lint
import json


class TestLint():
    runner = CliRunner()

    def test_passing_command(self):
        result = self.runner.invoke(lint, ['cli/tests/data/policy.py', '--out=json'])
        assert result.exit_code == 0

        report = json.loads(result.output)
        assert report["report_count"] == 0

    def file_not_found(self):
        result = self.runner.invoke(lint, 'non_existing_dir')
        assert result.exit_code == 1 and isinstance(result.exception, FileNotFoundError)

    def valid_file_buggy_policy(self):
        result = self.runner.invoke(lint, 'cli/tests/data/buggy_policy.py')

        assert result.exit_code == 0
