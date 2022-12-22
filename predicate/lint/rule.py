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
from runpy import run_path
import traceback


class NoAllow():
    """Checks if Policy contains spcefic rules denied by administrator"""

    def check(self, rule, policy):
        """check predicate"""
        check = None
        try:
            check = policy.equivalent(rule, "allow")
            if check is not None:
                return check[0]
        except Exception:
            return False
        else:
            return False


def get_rules(path: str, name: str):
    """Returns linter rules"""
    try:
        module = run_path(path)
        return module[name]
    except AttributeError:
        # TODO: replace traceback once structured logging is implemented?
        traceback.print_exc()
        print(f"Invalid rule found in {path}")
        return None


    
