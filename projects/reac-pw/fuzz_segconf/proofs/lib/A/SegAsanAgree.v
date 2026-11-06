(* reac-pw/fuzz_segconf, image A: lib/A/SegAsanTop.v's asan_agrees with its plain side discharged by the plain tree.
   SegAsanTop.seg_asan_agrees_of_tfib takes three Section arguments for the plain side (the interim hypothesis of
   2026-10-30 17:11Z: plain_slot_ag, at a cut record CPp, from the plain segment lemmas plain_segs, until the plain
   tree is merged) and TFIB_T. Here the plain tree is merged, and the three are given by its own texts:
   - plain_slot_ag := lib/AgreeSeg.v plain_slot_ag (the same statement, proved there from Prog/SegSlotAG);
   - CPp := Prog/Seg/SegWalkMainA.CPseg, the cut record the plain walks are proved at;
   - plain_segs := Prog/SegEnd.segs_holds over exactly the plain walks and callee bundles that lib/AgreeSegTop.v and
     lib/SegTopAgree.v (the plain tree's ubsan_agrees) take: Prog/Seg E01, M01, L01, L02T, L03, M02, V01, X01,
     AgreeSegTop.plain_init_holds, Prog/memchr.memchr_holds, Prog/SegTop K_L02_holds, K_M02_holds, K_V01_holds and
     AgreeSeg.plain_calloc_concrete.
   seg_asan_agrees_of_tfib_plain is therefore asan_agrees under TFIB_T alone; lib/A/SegClose.v gives it TFIB_T.
   This file is separate from SegAsanTop.v because the plain tree's agreement files load the UBSan tree's modules of
   the same short names (SlotFR, Tac_slot, FrameAPI, ...), which would change what SegAsanTop's qualified names mean.
   Proves no function (kind: merge; the instantiation of SegAsanTop's plain side). *)
From OSSVerify.reac_pw.fuzz_segconf Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require SegAsanTop SegTFIB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require AgreeSeg AgreeSegTop.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require LLVMFuzzerTestOneInput_c SegEnd memchr SegTop.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require SegWalkMainA E01 M01 L01 L02T L03 M02 V01 X01.

(* the plain segment lemmas at the plain walks' cut record, from the plain walks *)
Lemma seg_plain_segs_closed : forall (fx : OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YK11.FPState)
  (rc : OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YM05.RunCeil),
  lib.Prog.LLVMFuzzerTestOneInput_c.seg_lemmas
    OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YH02.src0_msyms
    (@OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.ZAllocator.zlib_API)
    OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YL0s.RA_LIB
    OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YL0s.EMPTY
    lib.Prog.Seg.SegWalkMainA.CPseg.
Proof.
  exact (lib.Prog.SegEnd.segs_holds _ _ _ _ _ _
           lib.Prog.Seg.E01.seg_E01_holds lib.Prog.Seg.M01.seg_M01_holds lib.Prog.Seg.L01.seg_L01_holds
           lib.Prog.Seg.L02T.seg_L02 lib.Prog.Seg.L03.seg_L03_holds lib.Prog.Seg.M02.seg_M02 lib.Prog.Seg.V01.seg_V01
           lib.Prog.Seg.X01.seg_X01_holds
           lib.AgreeSegTop.plain_init_holds lib.Prog.memchr.memchr_holds
           lib.Prog.SegTop.K_L02_holds lib.Prog.SegTop.K_M02_holds lib.Prog.SegTop.K_V01_holds
           lib.AgreeSeg.plain_calloc_concrete).
Qed.

(* asan_agrees under TFIB_T alone: SegAsanTop's plain side given by the plain tree *)
Theorem seg_asan_agrees_of_tfib_plain : lib.A.SegTFIB.TFIB_T -> Statements.asan_agrees.
Proof.
  exact (lib.A.SegAsanTop.seg_asan_agrees_of_tfib lib.AgreeSeg.plain_slot_ag lib.Prog.Seg.SegWalkMainA.CPseg
           seg_plain_segs_closed).
Qed.
