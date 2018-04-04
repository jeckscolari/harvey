# HarVey


## Installation

On Ubuntu 16.04

```sh
sudo apt install ocaml opam
opam init
opam install lymp
eval $(opam config env)
cd monitor/monpoly-2.0.0
ocamlbuild -use-ocamlfind -pkgs lymp -pkgs str -tag thread main.native && ./main.native
```

You'll also need these python modules

```sh
pip install flask
pip install pyyaml
pip install networkx
pip install pyparsing
```


## Usage

Start HarVey server:

```sh
python3 server/server.py path/to/model.yaml
```

Start a monitor:

```sh
python3 monitor/monitor.py path/to/formula.bgf
```



## Dependencies

- [python](https://www.python.org/)
- [OCaml](https://ocaml.org/)
- [lymp](https://github.com/dbousque/lymp)
- [Flask](http://flask.pocoo.org/)
