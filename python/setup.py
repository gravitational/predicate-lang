import setuptools

with open("README.md", "r", encoding="utf-8") as fh:
    long_description = fh.read()

setuptools.setup(
    name="predicate",
    version="0.0.1",
    author="Alexander K",
    author_email="sasha@goteleport.com",
    description="Predicate langugage",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/gravitational/predicate-lang",
    project_urls={
        "Bug Tracker": "https://github.com/gravitational/predicate-lang",
    },
    classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
    ],
    package_dir={"": "src"},
    packages=setuptools.find_packages(where="src"),
    python_requires=">=3.9",
    tests_require = [
        "pytest>=7.1.2",
        "pluggy>=1.0.0"
    ],
    install_requires=[
        "z3-solver>=4.8.12.0"
    ]
)
