import setuptools

setuptools.setup(
    name="easyila",
    version="0.0.1",

    package_dir={"": "src"},
    package_data={"easyila": ["py.typed"]},
    packages=setuptools.find_packages(where="src"),
    python_requires="~=3.9",
    install_requires=["numpy","pyverilog"],
    dependency_links=["git+https://github.com/cvc5/cvc5.git"],
)
