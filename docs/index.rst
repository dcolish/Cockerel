Welcome to Cockerel's documentation!
====================================

Cockerel is a prover, a lesson planner, and a companion for all
education in all areas of mathematics. My experience in mathematical
education is only as a student, however it has shown me that no good
tools exist for providing a long distance interactive
experience. Students have to deal with a system the expects perfection
and understanding without any feedback and little to no motivation
beyond the threat of failure.

Cockerel is different. It provides an environment that is easy for
instructors and students to use by focusing solely on lesson
planning. Each class has a number of lesson plans associated with
it. The lesson plan is simply a wiki document that instructors can use
however they like. By providing any questions and proofs in-line with
the instruction, students will have clear references for all their
assignments. Additionally, each question or theorem, will be a
clickable link to a prover in which the students can complete the
questions.


System Overview
---------------

Pre-Requisites
~~~~~~~~~~~~~~
The Cockerel system is simple to install provided you have the
following requirements satisfied:

- `Ocaml`_ >= 3.11
- `Coq`_ >= 8.2pl1
- `Python`_ >= 2.6 
- `Virtualenv`_
- `Pip`_

For information on installing these see their respective sites.

Installation
~~~~~~~~~~~~

Since Cockerel is in a heavy development phase is it signficantly more
reliable to install the system using the latest code on `Github`_ and
activating a development enviroment. Future releases will be packaged
for Ubuntu/Debian and PyPi, but until then follow these directions.

I strongly recommend using the virtualenv project for managing the
install. Assuming you have satisfied the above pre-requisites you can
create a new virtualenv around the project directory to install
into. This can be done with:: 

    git clone git://github.com/dcolish/Cockerel.git

Now you are ready to active the development branch using the following
commands:: 

    cd path/to/Cockerel
    virtualenv dev_env
    . dev_env/bin/activate
    python setup.py develop


Running the Servers
~~~~~~~~~~~~~~~~~~~

Begin activating your install::

   cd path/to/Cockerel
   . dev_env/bin/activate

Now you will have the commands required to run Cockerel and Coqd in
your path. To start Cockerel run::

   cockerel
     
To start Coqd run::

   coqd

The Cockerel webpage will be at http://localhost:5000 by default. Note
that both of these commands will run in the foreground of your
terminal. If you do not want this they can also be run using a few
shell commands to control the program output. In order to stop them
you will eventually need to foreground them again and press Ctrl-C. A
session could look something like this::
   
   cockerel > cockerel.log 2>&1 &
   # [1] 4199
   coqd > coqd.log 2>&1 &
   # [2] 4211
   jobs
   # [1]-  Running                 cockerel > cockerel.log 2>&1 &
   # [2]+  Running                 coqd > coqd.log 2>&1 &
   fg %1
   #NOW PRESS Ctrl-C to stop => cockerel > cockerel.log 2>&1 
   fg %2
   #NOW PRESS Ctrl-C to stop => coqd > coqd.log 2>& 



Contents
--------

.. toctree::
   :maxdepth: 2

   cockerel/index
   coqd/index


Indices and tables
------------------

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`


.. _`Pip`: http://pip.openplans.org/
.. _`Virtualenv`: http://virtualenv.openplans.org/
.. _`Python`: http://www.python.org/
.. _`Ocaml`: http://caml.inria.fr/
.. _`Coq`: http://coq.inria.fr/
.. _`Github`: http://github.com/dcolish/Cockerel
