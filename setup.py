from setuptools import setup, find_packages

setup(name="cockerel",
      version="0.1",
      packages=find_packages(),

      install_requires=[
        'flask',
        'twisted',
        'pexpect',
        ],
      test_require=[
        'nose == 0.11.3',
        ]
      )
