Leg 0.1.3
=========

This is a release of Leg, a Lua library exporting a complete Lua 5.1 grammar 
and a small API for user manipulation.

Erratum
-------

- 2020-4-11: Update leg to work with Lpeg 1.0.2. Some minor fixes. Ongoing
maintenance is not guaranteed. Still expects Lua 5.1; no goto/label support.

- 2020-7-30: Modify leg to use the new package format rather than the `module`
function. Allows leg to compile under newer versions of Lua. However, I have
not yet expanded the grammar to include 5.2+ features -- doing so in this
repository is not a priority for me.

- This version is still available under the original licence in COPYRIGHT.

Dependencies
------------

* You need, understandably, to have Lua 5.1 up and running to be able to use
this library :)

* Also, Leg uses LPeg 0.7 extensively for pattern matching, so LPeg is 
expected be installed. You can get LPeg at 

http://www.inf.puc-rio.br/~roberto/lpeg.html


Basic Installation
------------------

There are three ways to install Leg:

* `make install`

  Run `make install`, and a directory called `leg` with the source files inside
  will be put in a specific path. Tweak Makefile's LUA_LIB variable to 
  indicate the appropriate path for your system; Makefile ships with it set 
  to /usr/local/share/lua/5.1 . Make sure you have the proper permissions to
  access the path you want; if not or in doubt, use the `make` option below.
  
* `make` or `make leg`
  
  A directory `leg` will be created in your working directory, with the 
  source files inside. Just put it in a LUA_PATH-visible place and you're 
  ready to go.
  
* by hand

  If you don't have, don't want to or can't use `make`, you can just put all 
  the files in `src` inside a directory called `leg`, and put that directory 
  in your LUA_PATH.


Read the Lua Reference Manual for the LUA_PATH and the LUA_CPATH syntax
(http://www.lua.org/manual/5.1/manual.html#pdf-package.path).


Copyright
---------

See the file "COPYRIGHT".


Bug Fixes and New Stuff
-----------------------

See the file "release".


Testing
-------

You can either:

* run `make test`; or

* go to the directory `tests` and run `test.lua`.

Both do the same thing.


Work to do
----------

* Improve error checking: currently it is bolted on and not extensible, and 
  different patterns react differently to mismatching: scanner.STRING throws 
  an error when a mismatch happens, but some errors simply return false and an
  error message. I don't know a good way to handle this.

* A better API for grammar extensions. The current one is very ad hoc, and
  requires some fine tuning to make sure it works correctly. Metalua's API 
  seems interesting, and was originally based on Parsec. Investigation is 
  under way.

* The binary operators' precedences isn't enforced in the grammar; one must 
  enforce it by hand when capturing expressions. This can be very annoying.

* More thorough testing.
