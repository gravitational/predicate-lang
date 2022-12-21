---
authors: Sakshyam Shah (sshah@goteleport.com)
state: draft
---

# RFD 2 - Linter
Predicate linter will help policy writers author safe and consistent rules.

Linters are a popular way to enforce style and security best practices and keep code or config files consistent. These coding styles and best practices are usually a mix of opinionated (defined by project authors) and community-driven definitions. This RFD primarily concerns design decision and the scope of the linter that we would like to start with.  


## Scope
Linter will scan and report violating lint rules (predicate-lang specific) in a given policy file or directory. Rules will be specific to how policies are authored using `Policy` and `Rules` classes imported from predicate solver (`solver.teleport`) module. 

### Out of scope
Programming language specefic rules. Since predicate policies are authored in python, policy authors can take advantage of available python language linters such as [pylint](https://pylint.pycqa.org/en/latest/) to enforce python code-specific best practices. Predicate classes and methods will also be readily available on autosuggestions when using extensions such as the one available in [Python VS Code extension](https://code.visualstudio.com/docs/python/linting). 


## Lint rules
Rules are the core part of a linter. For predicate we can basically divide rules into two categories:

1. Styles rules: 
    - Opinionated rules on how a policy should be authored.

2. Policy rules: 
    - Ensure risky policies are never authored/pushed in production. 
    - Rules that utilize z3 to report duplicate rules, reducible rules, etc. 


### Style rules
Style and consistency rules are specific to how policies should be authored using a predicate. These rules will be mostly opinionated and gives us a chance to enforce authoring guidelines that would help us to easily parse and compute predicate policies. 

Examples of style rules may include:
- One instance of Policy class per policy file.
- Writing a description of the policy.
- Missing policy test.

### Policy rules
Rules to check if policies are compliant to certain allow/deny rules, report duplicate rules etc. For example, if an organization's security policy disallows `root` access, in any case, the administrator will configure the predicate linter to flag and report when a new policy is created permitting `root` access. 

Examples of policy rules may include:
- Forbid authoring policies with certain allow rules (deny list) like the following:
    - `AccessNode(AccessNode.login == root) & (User.traits["team"] == ("dev",)`
    - `AccessNode((Node.labels["env"] == "prod") & (User.name == "dbadmin"))`
- Flag duplicate rules, redundant rules.

Policy rules are usually user/organization specific. As usage of predicate grows, we may also be able to curate community or Teleport provided "rule collection" for generic Linux server SSH access, database access or compliance specific (such as PCI DSS, HIPAA, etc) rules for infrastructure access. 

Security teams and Teleport administrators will benefit from these types of policies. Once a CI/CD pipeline is set up in such a way that Teleport policies can only be deployed from the CI and only if all the linter deny rule passes, one can rest assured that risky policies are never pushed to production. 

Note: While preventive methods like rule blacklisting enbales easy way to block authoring risky policies, a [permission boundary](https://github.com/gravitational/predicate-lang/issues/34) will be more effective to catch escaping and escalating roles.   


## Implementation
### predicate lint command
A new "lint" command will be added to the predicate CLI which can be invoked as:
```
$ predicate lint -o <output type> -config <config file> <file> <dir>
```

### Defining Rules
All the supported rules are defined as a python class within linter package. Some rules like “checking if policy tests are written" can be fully self-contained while rules like allowing administrators to define a list of “deny rules” will require additional rule file maintained by predicate users.  

### Linter techniques
For styling, we will be mostly utilizing python AST parser. 

For policy specific lint rules, we will be mostly utilizing predicate solvers.

### Configuration
A config file `predicatelint.yml` will be added to configure linter.


### Reporting and output
When rules are violated, linter will report description of violated rule, along with line number and code snippet of policy file. By default reports will be printed to stdout.  
```
$ predicate lint -o <output format>
```

`-o json` will return output in JSON format which can be consumed by external callers such as VS Code extension.

Real-time reporting can be available to Language Server Protocol (LSP) supported IDE extensions such as VS Code extension for predicate lint.