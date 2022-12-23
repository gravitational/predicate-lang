from click.testing import CliRunner
from cli.__main__ import lint


class TestLint():
    runner = CliRunner()

    def test_passing_command(self):
        result = self.runner.invoke(lint, 'cli/tests/mock_policy.py')
        assert result.exit_code == 0
        assert result.output.strip().replace(" ", "") == "Found0ruleviolation(s)."

    def file_not_found(self):
        result = self.runner.invoke(lint, 'non_existing_dir')
        assert result.exit_code == 1 and isinstance(result.exception, FileNotFoundError)

    def valid_file_buggy_policy(self):
        result = self.runner.invoke(lint, 'cli/tests/buggy_policy.py')

        assert result.exit_code == 0

