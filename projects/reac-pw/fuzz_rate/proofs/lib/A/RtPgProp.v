(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): the four pieces of one turn of the property loop
   of LLVMFuzzerTestOneInput (0x80714) as lib/A/RtPgSeg.v states them, gathered for the assembly. Proves no function
   (kind: segment lemma).
     pa_piece_sel   : rs_piece_W4_sel_stmt    N 0x80e10 -> SEL7 0x80e6c / SELK 0x81018        (lib/A/RtPgPropSelB.v)
     pa_piece_int7  : rs_piece_W4_int7_stmt   SEL7 0x80e6c -> LATCH7 0x82530                  (lib/A/RtPgPropIntB.v)
     pa_piece_key   : rs_piece_W4_key_stmt    SELK 0x81018 -> SELS 0x81150 / SELI 0x82280     (lib/A/RtPgPropKeyB.v)
     pa_piece_latch : rs_piece_W4_latch_stmt  LATCH / LATCHI / LATCH7 -> N 0x80e10 / P1 0x826d4 (lib/A/RtPgPropSel.v)
   Each takes the Section hypotheses MTL (ameter_laws) and LAWS (AR_laws of image A); pa_piece_int7 also AMEMSET, the
   __asan_memset contract at 0x51cfc (YG0d.aintrin_realizes OSet), which the shape-7 pod's pad calls. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Export RtPgPropSel RtPgPropSelB RtPgPropIntB RtPgPropKeyB.

Print Assumptions pa_piece_sel.
Print Assumptions pa_piece_int7.
Print Assumptions pa_piece_key.
Print Assumptions pa_piece_latch.
