There is the beginning of a pretty printer for terms, however, I did
not manage to automatically install the pretty printers. Too much of
fiddling with the internals for the toplevel, so I run out of time.
The code is now commented, for a future time when I come around to do
this (possibly never).

The files *.pp are modifications that load the appropriate libraries,
and there are comments for the code generation that tries (and fails)
to install the pretty printer in astgen.ml
