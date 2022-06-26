import pytest
from predicate import ast, Predicate, String, Map, ParameterError, regex, StringTuple
from predicate import aws


class TestAst:
    def test_aws_allow_policy(self, mixed_statement_policy):
        return
        p = Predicate(aws.policy(mixed_statement_policy))

        ret, _ = p.check(Predicate(
            (aws.Action.resource == "arn:aws:s3:::example_bucket") & (aws.Action.action == "s3:ListBucket")))
        assert ret == True        

    def test_aws_policy(self, s3_policy):
        p = Predicate(aws.policy(s3_policy))

        # get bucket location on any bucket works
        ret, d = p.check(Predicate(
            (aws.Action.resource == "arn:aws:s3:::example_bucket") & (aws.Action.action == "s3:GetBucketLocation")))
        assert ret == True

        # listing bucket logs is not allowed
        ret, d = p.check(Predicate(
            (aws.Action.resource == "arn:aws:s3:::example_bucket/logs") & (aws.Action.action == "s3:GetObject")))
        assert ret == False

        # can get a random doc from a bucket
        ret, d = p.check(Predicate(
            (aws.Action.resource == "arn:aws:s3:::carlossalazar/document") & (aws.Action.action == "s3:GetObject")))
        assert ret == True



@pytest.fixture
def mixed_statement_policy():
    return {
        "Statement":{
            "Effect": "Allow",
            "Action": [
                "s3:*",
                "cloudwatch:*",
                "ec2:*"
            ],
            "Resource": [
                "arn:aws:s3:::example_bucket"
            ]
        }
    }

@pytest.fixture
def s3_policy():
    return {
    "Version": "2012-10-17",
    "Statement": [
        {
            "Sid": "AllowS3ListRead",
            "Effect": "Allow",
            "Action": [
                "s3:GetBucketLocation",
                "s3:GetAccountPublicAccessBlock",
                "s3:ListAccessPoints",
                "s3:ListAllMyBuckets"
            ],
            "Resource": "arn:aws:s3:::*"
        },
        {
            "Sid": "AllowS3Self",
            "Effect": "Allow",
            "Action": "s3:*",
            "Resource": [
                "arn:aws:s3:::carlossalazar/*",
                "arn:aws:s3:::carlossalazar"
            ]
        },
        {
            "Sid": "DenyS3Logs",
            "Effect": "Deny",
            "Action": "s3:*",
            "Resource": "arn:aws:s3:::*log*"
        }
    ]
}
