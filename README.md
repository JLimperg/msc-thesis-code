# A Reflexive Graph Model of Sized Types

This is the companion formalisation for my Master's thesis. To build it, you'll
need [Agda](https://agda.readthedocs.io/en/v2.9.0/) version 2.9.0 and a
registered [agda-stdlib](https://github.com/agda/agda-stdlib) version 2.4. Then
proceed as follows:

```
git clone https://github.com/JLimperg/msc-thesis-code <dir>
cd <dir>
git submodule init
git submodule update
agda src/index.agda
```

The last command typechecks all modules belonging to the formalisation.
