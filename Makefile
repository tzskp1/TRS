all: examples

orders.cmx: orders.ml term.cmx
unification.cmx: unification.ml utils.cmx term.cmx
completion.cmx: completion.ml utils.cmx term.cmx unification.cmx
examples: examples.ml utils.cmx term.cmx orders.cmx unification.cmx completion.cmx

# rules
OL := ocamllex
OY := ocamlyacc
OO := ocamlfind opt
PACKAGES := ppx_deriving.show str
OOC := $(OO) $(addprefix -package ,$(PACKAGES)) -linkpkg -c
OOO := $(OO) $(addprefix -package ,$(PACKAGES)) -linkpkg -linkall -o

.PHONY : clean all

%.ml : %.mll
	$(OL) $<

%.ml : %.mly
	$(OY) $<

%.mli : %.mly
	$(OY) $<

%.cmx : %.ml
	$(OOC) $< $(filter %.cmx,$^)

%.cmi : %.mli
	$(OOC) $< 

% : %.ml
	$(OOC) $< 
	$(OOO) $@ $(filter %.cmx,$^) $@.cmx 

clean : 
	$(RM) *.o
	$(RM) *.cmx
	$(RM) *.cmi

