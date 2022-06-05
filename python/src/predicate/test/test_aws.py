import pytest
from predicate import ast, Predicate, String, Map, ParameterError, regex, StringTuple
from predicate import aws

class TestAst:
    def test_aws_allow(self):
        p = aws.statement({
            "Effect": "Allow",
            "Action": [
                "s3:*",
                "cloudwatch:*",
                "ec2:*"
            ],
            "Resource": [
                "arn:aws:s3:::example_bucket"
            ]
        })

        ret, _ = p.check(Predicate(
            (aws.Action.resource == "arn:aws:s3:::example_bucket") & (aws.Action.action == "s3:ListBucket")))
        assert ret == True

