Cockerel
====================================
The main web application

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

I strongly recommend using the virtualenv project for managing the
python namespace. Assuming you have a project python install with setuptools,
you can create a new virtualenv around the project directory to install
into. This can be done with:

    git clone git://github.com/dcolish/Cockerel.git

Then

    virtualenv some_env_path
    . some_env_path/bin/activate
    python setup.py develop


To start Cockerel run
    cockerel
     
To start Coqd run
   coqd

The Cockerel webpage will be at http://localhost:5000 by default




API Reference
-------------

.. automodule:: cockerel.webapp
   :members:

.. automodule:: cockerel.webapp.views.admin
   :members:

.. automodule:: cockerel.webapp.views.classes
   :members:

.. automodule:: cockerel.webapp.views.frontend
   :members:

.. automodule:: cockerel.webapp.views.lessons
   :members:

.. automodule:: cockerel.webapp.views.prover.mdx_prover
   :members:

.. automodule:: cockerel.webapp.views.prover.prover
   :members:

.. automodule:: cockerel.webapp.views.util
   :members:

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
