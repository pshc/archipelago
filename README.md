The Archipelago programming environment is MIT licensed.

Its graphical editor will be GPL licensed.


This code will seem arcane, labyrinthine, and often broken.
That's because it is. This form is only an intermediate stage.

Eventually, all this will be ASTs.

==================================

If you want to get a basic idea of what the ASTs look like:

Running `VIEW=true make test` will dump trees as plain text in views/.
If you have LLVM installed, you can see the generated IR in ir/.
The actual native (binary) module serializations are put in mods/.

Good luck!
