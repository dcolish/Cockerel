from setuptools import setup, find_packages

setup(name="cockerel",
      version="0.1",
      packages=find_packages(),

      author='Dan Colish',
      author_email='dcolish@gmail.com',

      description='Simplified Theorem Checker for the Web',
      long_description='TBW',
      license='BSD',
      url='http://dcolish.github.com/cockerel',

      classifiers=[
        'Development Status :: 2 - Pre-Alpha',
        'Enviroment :: Console :: Web Enviroment',
        'Intended Audience :: Education',
        'License :: OSI Approved :: BSD License',
        'Programming Language :: Python',
        'Programming Language :: Python :: 2',
        'Programming Language :: Python :: 2.6',
        'Programming Language :: Python :: 2.7',
        'Programming Language :: Coq :: 8.2pl1',
        'Programming Language :: Coq :: 8.3',
        'Operating System :: MacOS :: Posix :: Unix',
        ],

      entry_points={
        'console_scripts': [
            'cockerel=cockerel.',
            'coqd=coqd.',
            ],
        },

      install_requires=[
        'flask',
        'Flask-SQLAlchemy',
        'twisted',
        'pexpect',
        'ply',
        'SQLAlchemy',
        ],

      tests_requires=[
        'nose == 0.11.3',
        ],
      )
