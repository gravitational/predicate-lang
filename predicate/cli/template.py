import os
from jinja2 import Template, FileSystemLoader, Environment, select_autoescape




def create_dir_if_not_exist():
    path = "policies"
    isExist = os.path.exists(path)
    if not isExist:
        os.makedirs(path)
        print("The new directory is created!")


def create_default_policy(name: str): 
    template_loader = FileSystemLoader(searchpath="./")
    template_env = Environment(loader=template_loader, autoescape=select_autoescape())
    template = template_env.get_template("template/default.txt")
    template_arguments = template_values(name)
    policy_file = template.render(template_arguments) 
    create_dir_if_not_exist()
    f = open('policies/{}.py'.format(name.lower()),'w')
    f.write(policy_file)
    f.close()




def template_values(name: str):
    values = {
        "policyclass" : name.capitalize(),
        "policyname" : name.lower(),
        "testname" : 'test_{}'.format(name.lower())
    }
   
    return values