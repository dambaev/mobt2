######
#
# Note that
# certain installations require the following changes:
#
# atscc -> patscc
# atsopt -> patsopt
# ATSHOME -> PATSHOME
#
######
#
#
######
#
ATSHOME=$(shell dirname $(shell dirname $(shell readlink $(shell which patscc))))
ATSCC=patscc
ATSOPT=patsopt
#
ATSCCFLAGS=-O2 -DATS_MEMALLOC_LIBC -I"../libs/"
ATSLIBS=
# ATSCCFLAGS=-O2
#
# '-flto' enables link-time optimization such as inlining lib functions
#
# ATSCCFLAGS=-O2 -flto
#
#
ATS_DATS=
ATS_SATS=
######
#

ATS_OBJS= $(ATS_SATS:.sats=_sats.o) $(ATS_DATS:.dats=_dats.o)

.PHONY: all clean

all: test

cleanall::
#
######
#
# Please uncomment the following three lines and replace the name [foo]
# with the name of the file you want to compile
#


test: \
    test7 \
    test5 \
    test4 \
		test3 \
    test1_gc \
		test1

test7: $(ATS_OBJS) TEST/test7.dats
	$(ATSCC) $(ATSCCFLAGS) -o $@ $(ATS_OBJS) TEST/$@.dats $(ATSLIBS)
	$(shell which time) ./$@
test6: $(ATS_OBJS) TEST/test6.dats
	$(ATSCC) $(ATSCCFLAGS) -o $@ $(ATS_OBJS) TEST/$@.dats $(ATSLIBS)
	$(shell which time) ./$@
test5: $(ATS_OBJS) TEST/test5.dats
	$(ATSCC) $(ATSCCFLAGS) -o $@ $(ATS_OBJS) TEST/$@.dats $(ATSLIBS)
	$(shell which time) ./$@
test4: $(ATS_OBJS) TEST/test4.dats
	$(ATSCC) -O2 -DATS_MEMALLOC_GCBDW -lgc -o $@ $(ATS_OBJS) TEST/$@.dats $(ATSLIBS)
	$(shell which time) ./$@
test3: $(ATS_OBJS) TEST/test3.dats
	$(ATSCC) $(ATSCCFLAGS) -o $@ $(ATS_OBJS) TEST/$@.dats $(ATSLIBS)
	$(shell which time) ./$@
test2: $(ATS_OBJS) TEST/test2.dats
	$(ATSCC) $(ATSCCFLAGS) -o $@ $(ATS_OBJS) TEST/$@.dats $(ATSLIBS)
	$(shell which time) ./$@
test1_gc: $(ATS_OBJS) TEST/test1.dats
	$(ATSCC) -O2 -DATS_MEMALLOC_GCBDW -lgc -o $@ $(ATS_OBJS) TEST/test1.dats $(ATSLIBS)
	$(shell which time) ./$@
test1: $(ATS_OBJS) TEST/test1.dats
	$(ATSCC) $(ATSCCFLAGS) -o $@ $(ATS_OBJS) TEST/$@.dats $(ATSLIBS)
	$(shell which time) ./$@
#_bin
#	@touch $@
cleanall:: ; $(RMF) test*
#
######
#
# You may find these rules useful
#
%_sats.o: %.sats ; $(ATSCC) $(ATSCCFLAGS) -c -o $@ $<
%_dats.o: %.dats ; $(ATSCC) $(ATSCCFLAGS) -c -o $@ $<
#
######
#
RMF=rm -f
#
######
#
clean:: ; $(RMF) test*
clean:: ; $(RMF) *~
clean:: ; find -name '*_?ats.o' -exec $(RMF) {} \;
clean:: ; find -name '*_?ats.c' -exec $(RMF) {} \;
#
cleanall:: clean
#
###### end of [Makefile] ######

