from lint.linter import Linter


class TestLinter:

    def test_matching_file(self):
        policy_file = "lint/tests/data/policy_example/access.py"
        lint_result = Linter(policy_file).run()
        print(lint_result)
        assert len(lint_result[0]) == 1


    def test_matching_dir(self):
        policy_file_dir = "lint/tests/data/policy_example/"
        lint_result = Linter(policy_file_dir).run()

        assert len(lint_result[0]) == 2

    def test_nonmatching_policy(self):
        policy_file_dir = "lint/tests/data/policy_example/list_nodes.py"
        lint_result = Linter(policy_file_dir).run()

        assert len(lint_result[0]) == 0



