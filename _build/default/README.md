<p align="center">
  <img src="images/neutron.png">
</p>

# Neutron

Neutron is a simple SAT solver written in OCaml and C.

# Architecture

The core algorithm behind Neutron is implemented in plain C allowing for a full control on the memory model. In the other hand, the interface is written in OCaml, a language of choice to manipulate symbolic expressions. Inputs are processed by tools developed in OCaml (parsing, cnf conversion, optimization, rewriting...) before being sent to the optimized C solver.




