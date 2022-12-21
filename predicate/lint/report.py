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

class LinterMessage:
    """ Defines reporting variables"""
    def __init__(
        self,
        line_number: str,
        code_snippet: str,
        description=str,
        file_name= str,
        ):
        self.line_number = line_number
        self.code_snippet = code_snippet
        self.description = description
        self.file_name = file_name

    def __str__(self):
        return f"File: {self.file_name}, Line number: {self.line_number} \nDescription: {self.description} \nCode: \n {self.code_snippet}"


