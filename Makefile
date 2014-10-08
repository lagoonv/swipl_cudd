.PHONY= clean pack dynamic

CUDD_HOME	:=	/home/vit/Dev/cudd-2.5.0

PLBASE		:=	$(shell (eval `swipl -dump-runtime-variables` && echo $$PLBASE))
PLCFLAGS	:=	$(shell (eval `swipl -dump-runtime-variables` && echo $$PLCFLAGS))
PLLDFLAGS	:=	$(shell (eval `swipl -dump-runtime-variables` && echo $$PLLDFLAGS))

CUDD_LIBS	:=	-lcudd -lmtr -lutil -lst -lepd 
CUDD_LIBDIR	:= 	-L $(CUDD_HOME)/cudd	\
			-L $(CUDD_HOME)/util	\
			-L $(CUDD_HOME)/epd	\
			-L $(CUDD_HOME)/mtr	\
			-L $(CUDD_HOME)/st   

ifdef DEBUG
C_OPT = $(DEBUG) -g -DDEBUG_GC
else
C_OPT = -O3 -s -DNDEBUG
endif

dynamic:	pl_cudd.so

pl_cudd.so:	pl_cudd.o
		$(CC) $(C_OPT) $(PLLDFLAGS) -shared -o pl_cudd.so pl_cudd.o \
		-I $(CUDD_HOME)/include	-I $(PLBASE)/include \
		$(CUDD_LIBDIR) $(CUDD_LIBS)


pl_cudd.o:	pl_cudd.c pl_cudd.h
		$(CC) -c $(C_OPT) $(PLCFLAGS) -fPIC -I $(CUDD_HOME)/include -I $(PLBASE)/include \
		pl_cudd.c

clean:		
		\rm -f *.o *.so


pack:		
		tar zcvf pl_cudd.tgz Makefile pl_cudd.c pl_cudd.h cudd.pl \
		stub.c 
