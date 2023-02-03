from lint.linter import Linter


class TestLinter:

    def test_matching_file(self):
        policy_file = "lint/tests/data/policy_sample/access.py"
        lint_result = Linter(policy_file).run()
        assert len(lint_result[0]) == 1

    def test_matching_dir(self):
        policy_file_dir = "lint/tests/data/policy_sample/"
        lint_result = Linter(policy_file_dir).run()
        assert len(lint_result[0]) == 4

    def test_nonmatching_policy(self):
        policy_file_dir = "lint/tests/data/policy_sample/list_nodes.py"
        lint_result = Linter(policy_file_dir).run()

        assert len(lint_result[0]) == 0
