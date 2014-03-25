#User Manual for Extraction from Inductive Specifications

##Installation

### Prerequisites
You need to have Ocaml and Coq 8.4. 
The COQBIN (/usr/local/bin/ by default) and the COQDIR (/usr/local/
by default) environment variables must be set prior to use this plugin.
For example in a linux environment, type the following lines in a bash terminal or in the .bashrc file

   export COQBIN=/usr/local/bin/
   
   export COQDIR=/usr/local/


### Building the plugin
Simply type ``make'' in the plugin source directory. This will build the
plugin and laungh a test suite, which contains many examples.
Be sure the Ocaml used to compile Coq is the one used to compile the plugin.

## Usage

  First of all, many examples are given in the ``test'' directory. They show
many possible usage of the plugin. To use the plugin in a Coq file, you need
to add two lines at top of this file:

    Add LoadPath "<path>".
    Declare ML Module "relation_extraction_plugin".

where <path> is the plugin source directory. Then the relation extraction
commands can be used everywhere in the file. 

##Extraction to OCaml
The syntax of the command is:

    Extraction Relation [Single] [Relaxed] \
      rel mode [with rel1 mode1 rel2 mode2...]

where rel, rel1, rel2 are inductive definitions of relations and mode, mode1,
mode2 their respective extraction modes. 

When the Single flag is set, the plugin
only extracts the first relation (rel) whereas when it is not set, all the
relations and their depedencies (Fixpoints, Definitions, Inductive data types)
are extracted. 

The Relaxed flag activates an optimisation relative to non-deterministic specifications.
(see [1] for further details on non-deterministic specifications) 

Modes are given as an integer list ([1], [1 3] for examples). 
Each integer denotes an argument (of the inductive relation) position, starting with 1.

This command produces OCaml code on the standard output. 
The names of the extracted functions are obtained by concatenating the name of the inductive relation and the mode.

##Extraction to Haskell
Please type the following line before using the previously described command:

    Extraction Language Haskell.

##Extraction to Coq

The syntax of the command is:

    Extraction Relation Fixpoint [Single] [Relaxed] \
      rel mode [termination argument] [with rel1 mode1 rel2 mode2...]

If the termination argument is not specified, the first argument of the expected Coq functions is assumed 
to be the decreasing argument.
If a termination argument is provided, it may be one of the following cases:
- Struct n: the nth argument of the expected Coq functions is assumed to be the decreasing argument,
- Counter : the expected Coq functions are fixpoints using a supplementary argument which is a counter 
decreasing at each recursive call. 


The same convention for names of extracted functions as in Ocaml applies in Coq. 
To see the extracted functions, use Print.

For the moment, soundness proofs are produced in the simplest cases (see [1] for further details). 



##License

This program is free software: you can redistribute it and/or modify it under the terms of the 
GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or 
(at your option) any later version.

This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of 
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details. 

You should have received a copy of the GNU General Public License 
along with this program. If not, see <http://www.gnu.org/licenses/>. 

Copyright 2011, 2012 CNAM-ENSIIE

##Contacts

Catherine Dubois <catherine.dubois@ensiie.fr>
David Delahaye <david.delahaye@cnam.fr> 
Pierre-Nicolas Tollitte <pierrenicolas.tollitte@gmail.com>




[1] P.-N. Tollitte, D. Delahaye, C. Dubois. Producing Certied Functional Code from Inductive
Specications. International Conference on Certied Programs and Proofs (CPP 2012), dcembre 2012,
Vol. 7679, Series LNCS, pp. 76-91, Kyoto, Japon
