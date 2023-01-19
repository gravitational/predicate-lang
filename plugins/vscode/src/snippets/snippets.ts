export const predicateSnippet = {
  'From solver classes': {
    prefix: 'from solver',
    body: 'from solver.teleport import ${1|AccessNode,Node,Options,OptionsSet,Policy,Rules,User,Session,JoinSession|}',
    description: 'Import policy solver classes from solver.teleport.',
  },
  'Import solver class': {
    prefix: 'import',
    body: '${1|AccessNode,Node,Options,OptionsSet,Policy,Rules,User,Session,JoinSession|}$0',
    description: 'Import policy solver class from solver.teleport.',
  },
  'New policy class': {
    prefix: 'class',
    body: [
      'class ${1:ClassName}():',
      '\t"""Policy for $1."""',
      '\tp = Policy(',
      '\t\tname="${1/(.*)/${1:/downcase}/}",',
      '\t\tallow=Rules($2),',
      '\t\toptions=($3),',
      '\t\tdeny=($4),',
      '\t)',
      '',
      '\tdef test_${1/(.*)/${1:/downcase}/}(self):',
      '\t\tres, _ = self.p.check()',
      '\t\tassert res is ${5|True,False|}, "${6:test_description}"',
      '$0',
    ],
    description: 'Create new policy class.',
  },
  'Create policy': {
    prefix: 'p =',
    body: [
      'p = Policy(',
      '\tname="$1",',
      '\tallow=Rules($2),',
      '\toptions=OptionsSet($3),',
      '\tdeny=Rules($4),',
      ')',
      '$0',
    ],
    description: 'Create a new policy object.',
  },
  'Policy test method': {
    prefix: 'def',
    body: [
      'def test_${1:test_method_name}(self):',
      '\tres, _ = self.p.check(${2:"predicate_policy_to_test"})',
      '\tassert res is ${3|True,False|}, "${4:test_description}"$0',
    ],
    description: 'Policy test method.',
  },
  'New AccessNode': {
    prefix: 'accessnode',
    body: ['AccessNode($1)'],
    description: 'AccessNode snippet.',
  },
};
