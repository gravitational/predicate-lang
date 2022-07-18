import pytest
from predicate import ast, Predicate, String, Map, ParameterError, regex, StringTuple
from predicate.teleport import *


class TestTeleport:
    def test_simple(self):
        p = Policy(
            allow=(
#                Node.login == "root" & Node.label["env"] == "prod"
            )
        )
