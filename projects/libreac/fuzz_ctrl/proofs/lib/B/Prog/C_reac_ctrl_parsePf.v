(* lib/B/Prog/C_reac_ctrl_parsePf.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): the pieces of pb_reac_ctrl_parse,
   the cgif-form glue of reac_ctrl_parse (0x83e04), stretch by stretch (brief
   parse-glue-brief.md (a working note, not in this delivery); pattern: a Theorem Labs lane's plan of record
   proofs/libreac/fuzz_ctrl/doc/pb_reac_ctrl_identity_reply.plan.md section 1 (a working note, not in this delivery), with ONE fake-stack event).

     S-A + J1   rcpB_to_E1   entry -> the first slot of __asan_stack_malloc_1: C_reac_ctrl_parseLib.rcpB_pre_F run on
                             normalize memc, lifted by rrB_lift; the journal across its window writes [S - 128, S) by
                             rrB_journal_win.
     E1         rcpB_E1      the class-1 request (C_reac_ctrl_parseE1.aj_stack_malloc_at_raw at cid 1), then
                             lib.B.ProgWorldAstack.ctl_fs_of_astack 1 on its raw post: the new frame's facts at the return
                             memory, in SetupFB's terms (Fr = frame_addr lyc 1 pos, FL = flag_addr lyc 1 pos).
     RoFB       GlueLift.rrB_lift_st the re-based stretch 0x83e78 -> the return: C_reac_ctrl_parseLib.rcpB_post_F_ro at the
                             return memory mem2 of the request, lifted with its run (YK04R.fsteps).  The callees' writable
                             shadow is the region P2 := cut_shadow of S2 or the image's shadow (W11), with W12 / W13 /
                             rcpB_sh_word_bc covering the frame's, f's, o's and .str.4's shadow words.
     release    the frame release by lib.B.ProgWorldAstack.ctl_release_of_free_law 1 across that run (the journal
                             drops (1, pos)), then the post with acall_kept by C_reac_ctrl_parseK.rcpK_compose.
     pb_reac_ctrl_parse      the theorem: treac_ctrl_parse_spec (C_reac_ctrl_parse.v) at tfibsegs and the core's sink
                             head, from these pieces and the world facts C_reac_ctrl_parseW.v (W1-W13).

   Every lemma is Qed.  The image-B facts that are not proved on this base are Section hypotheses named after the
   statement that will supply them, each with its owner (same names and texts as a Theorem Labs lane's Section Journal).
   rule 24: no function proved. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_parseF C_reac_ctrl_parseLib
  C_reac_ctrl_parseE1 GlueLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK04 YK04R YA0n YA0nR.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05 YI16 YG0f YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0n YG0v YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormTr MemNormF ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorld ProgWorldAstack.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds.
Import ListNotations.
Open Scope Z_scope.

(* The register file at the first slot of __asan_stack_malloc_1 (rcpB_pre_F's post): ra = the return 0x83e78,
   sp = s1 = A = (S - 128) & -32, a0 = 128, s0 = S, s4 / s5 / s6 = o / f / n, s9 = the shadow offset. *)
Definition rcpB_regsE (gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s7 s8 s10 s11 t3 t4 t5 t6 : word) (f n o S : Z)
  : bvmap 5 word :=
  mkR (Z_to_bv 64 0x83e78) (Z_to_bv 64 ((S - 128) / 32 * 32)) gp tp t0 t1 t2 (Z_to_bv 64 S)
      (Z_to_bv 64 ((S - 128) / 32 * 32)) (Z_to_bv 64 128) (wa CELL_K) (sx32 (wa 1)) a3 a4 a5 a6 a7
      s2 s3 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 n) s7 s8 (wa ASAN_K) s10 s11 t3 t4 t5 t6.

Section Pf.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
(* As a Theorem Labs lane's Section Journal (lib/B/Prog/GlueLift.v): YCbq's Section premises for B's
   bundle.  LAWS, segs_low, errno_low, ML: core, PENDING THE RECORD CORE (Reusable.YCeg.tfib_segs_low / tl_env /
   TfibLib, YCeg.v; its line 25 records the relocation's refused starts).  SMP, ASM1: a Theorem Labs lane's class-1 fake-stack
   rules (a working branch ff613211c11).  PC1: the class-1 entry of B's code table; core, the TfibLib code table. *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.
Hypothesis segs_low : forall a, lib.Reusable.YG0d.in_img rsegs a -> 0 <= a < lib.Reusable.YG0f.kLowMemEnd.
Hypothesis errno_low : lib.Reusable.YCbq.api_env rsegs B.
Hypothesis ML : lib.Reusable.YG0d.model_laws (lib.Reusable.YG0f.as_universe B).
Hypothesis SMP : lib.Reusable.YCbq.stack_malloc_progressP B.
Hypothesis ASM1 : lib.Reusable.YG0d.astack_malloc_realizes rsegs B 1.
Hypothesis PC1 : lib.Reusable.YG0f.pc_stack_malloc (lib.Reusable.YG0f.as_code B) 1 = ASAN_STACK_MALLOC_1.

(* ---- S-A + J1: the entry 0x83e04 to the first slot of __asan_stack_malloc_1, lifted, with the journal at the real
   memory m1 there.  The continuation also receives the normalized end memory m1n with rcpB_pre_F's post over it. ---- *)
Lemma rcpB_to_E1 : lib.Reusable.YK04.wx_segs_nowrap rsegs ->
  forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc
    (W : lib.Reusable.YA0n.world rsegs) memc mdc k
    (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (f n o S : Z) (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ->
    sp0 - STK <= S - 8800 -> S <= sp0 ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= o < 2^64 -> 8800 <= S < 2^64 -> S mod 16 = 0 ->
    HIGHMEM_BEG <= S - 8800 -> S <= APPMEM_END ->
    lib.B.MemNorm.ro_agree rsegs memc -> stk rsegs memc (S - 8800) S ->
    bytes_at rsegs memc CELL_K (le8 (wa ASAN_K)) -> bytes_at rsegs memc GOT_CELL_K (le8 (wa CELL_K)) ->
    bytes_at rsegs memc UAR (le4 (wa 1)) -> bytes_at rsegs memc GOT_UAR (le8 (wa UAR)) ->
    lib.B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) (S - 8800) 8800 ->
    (forall (m1 m1n : word -> option byte) mdc1,
       munch [(S - 128, S)] (lib.B.MemNorm.normalize rsegs memc) m1n ->
       wmono rsegs (lib.B.MemNorm.normalize rsegs memc) m1n -> reac_ctrl_parseF.rd_mono (lib.B.MemNorm.normalize rsegs memc) m1n ->
       mem_inv rsegs m1n ->
       rw_cells rsegs m1n (S - 96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
       lib.B.MemNorm.mem_rel rsegs m1 m1n -> lib.B.MemNorm.ro_same rsegs memc m1 ->
       lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc1 k ->
       lib.Reusable.YA0n.SRr rsegs W
         (mkCfg (MS (rcpB_regsE gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s7 s8 s10 s11 t3 t4 t5 t6 f n o S)
                    F (Z_to_bv 64 0x3d868) fc None m1 (seg_rom rsegs)) mdc1) Q) ->
    lib.Reusable.YA0n.SRr rsegs W
      (mkCfg (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 o)
                      a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 REAC_CTRL_PARSE) fc None memc (seg_rom rsegs)) mdc) Q.
Proof using LAWS segs_low.
  intros Hwx STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k
    ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc f n o S Q
    HJ Hlo Hhi Rf Rn Ro RS S16 HHM HAE RO ST CK GCK UA GUA VW K.
  assert (STn : stk rsegs (lib.B.MemNorm.normalize rsegs memc) (S - 8800) S).
  { apply lib.B.MemNormTr.stk_normalize_ro; [exact RO | | exact ST].
    unfold lib.B.Prog.ImgBounds.IMG_HI. unfold HIGHMEM_BEG in HHM. lia. }
  eapply (GlueLift.rrB_lift Hwx W mdc); [exact RO | | ].
  - apply (C_reac_ctrl_parseLib.rcpB_pre_F (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W))
             ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
             (lib.B.MemNorm.normalize rsegs memc) f n o S Rf Rn Ro RS S16 HHM HAE STn (lib.B.MemNorm.mem_inv_normalize rsegs memc)
             (lib.B.MemNorm.bytes_at_normalize rsegs memc _ _ RO CK) (lib.B.MemNorm.bytes_at_normalize rsegs memc _ _ RO GCK)
             (lib.B.MemNorm.bytes_at_normalize rsegs memc _ _ RO UA) (lib.B.MemNorm.bytes_at_normalize rsegs memc _ _ RO GUA)).
    + pose proof (lib.B.ProgBridge.rng_of_visible _ _ _ (lib.B.ProgBridge.img_vis_W W)) as R.
      unfold lib.B.Prog.ImgBounds.IMG_LO, lib.B.Prog.ImgBounds.IMG_HI in R. exact R.
    + exact (lib.B.ProgBridge.rng_of_visible _ _ _ VW).
  - intros ms' md' (s' & (m1n & Es' & MU & WM & RM & MI & SV) & HREL & HROS) Hhid Hsame.
    rewrite Es' in HREL. destruct (lib.B.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL) as [Ems HMR].
    rewrite Ems.
    apply (K (ms_mem ms') m1n md' MU WM RM MI SV HMR HROS).
    apply (GlueLift.rrB_journal_win B LAWS segs_low STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W
             memc mdc k (ms_mem ms') m1n md' (S - 128) S HJ);
      [lia | lia | unfold lib.B.Prog.ImgBounds.IMG_HI; unfold HIGHMEM_BEG in HHM; lia | lia | exact MU | | exact HMR | exact HROS
      | exact Hhid | exact Hsame].
    intros a Ha. destruct STn as (_ & _ & Hs). destruct (Hs a ltac:(lia)) as [_ Hb]. exact (RM _ Hb).
Qed.

(* ---- E1: the class-1 request at the state rcpB_to_E1 ends in, then the new frame's facts by
   lib.B.ProgWorldAstack.ctl_fs_of_astack 1 (with lo := S - 8800 and L := 128).  The continuation receives the journal with
   (1, pos) owned, the call's acall_kept over its window [A - ESTACK, A), S2 = set_fs f2 Sc, and the frame's facts at
   the return memory mem2 in the terms of C_reac_ctrl_parseLib's Section SetupFB. ---- *)
Lemma rcpB_E1 :
  forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc (W : lib.Reusable.YA0n.world rsegs)
    (m1 : word -> option byte) mdc1 k (gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s7 s8 s10 s11 t3 t4 t5 t6 : word)
    (f n o S : Z) (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc1 k ->
    sp0 - STK <= S - 8800 -> S <= sp0 -> 8800 <= S < 2^64 -> S mod 16 = 0 ->
    gp = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_gp B) -> tp = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_tp B) ->
    lib.Reusable.YG01.count_cid 1 (lib.Reusable.YG01.frames Sc) < lib.Reusable.YG00.fs_frames 1 ->
    (forall S2 regs2 mem2 md2 pos f2,
       let regsT := rcpB_regsE gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s7 s8 s10 s11 t3 t4 t5 t6 f n o S in
       let A := (S - 128) / 32 * 32 in
       let Fr := lib.Reusable.YG0f.frame_addr lyc 1 pos in
       let FL := lib.Reusable.YG0f.flag_addr lyc 1 pos in
       lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem2 md2 k ->
       lib.Reusable.YG0d.aregs_preserved regsT regs2 ->
       lib.Reusable.YK11.getr regs2 10 = Z_to_bv 64 Fr ->
       lib.Reusable.YG0d.ablocks B lyc S2 = lib.Reusable.YG0d.ablocks B lyc Sc ->
       lib.Reusable.YG01.frames S2 = (1, pos) :: lib.Reusable.YG01.frames Sc ->
       ~ In (1, pos) (lib.Reusable.YG01.frames Sc) ->
       S2 = lib.Reusable.YG00.set_fs f2 Sc ->
       lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W m1 W mem2 (A - lib.Reusable.YG0d.ESTACK) A (fun _ => False) ->
       bytes_at rsegs mem2 FL [Z_to_bv 8 1] ->
       bytes_at rsegs mem2 (Fr + 120) (le8 (Z_to_bv 64 FL)) ->
       stk rsegs mem2 Fr (Fr + 128) ->
       (forall a, Fr <= a < Fr + 128 -> app_mem a) ->
       Fr mod 64 = 0 -> ASAN_GT <= Fr ->
       lib.Reusable.YG0f.ly_F lyc <= Fr -> Fr + 128 <= lib.Reusable.YG0f.ly_F lyc + FS_SIZE ->
       stk rsegs mem2 (S - 8800) A ->
       lib.Reusable.YA0n.SRr rsegs W
         (mkCfg (lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 0x83e78) mem2 (lib.Reusable.YK11.seg_rom rsegs)) md2) Q) ->
    lib.Reusable.YA0n.SRr rsegs W
      (mkCfg (MS (rcpB_regsE gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s7 s8 s10 s11 t3 t4 t5 t6 f n o S)
                 lib.Reusable.YK11.fp_regs (Z_to_bv 64 ASAN_STACK_MALLOC_1) lib.Reusable.YK11.fp_csr None m1
                 (seg_rom rsegs)) mdc1) Q.
Proof using LAWS segs_low errno_low ML SMP ASM1 PC1.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc1 k gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s7 s8 s10 s11
    t3 t4 t5 t6 f n o S Q HJ Hlo Hhi RS S16 Egp Etp Hcnt K.
  set (regsT := rcpB_regsE gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s7 s8 s10 s11 t3 t4 t5 t6 f n o S).
  set (A := (S - 128) / 32 * 32).
  assert (HA : A mod 32 = 0 /\ S - 160 < A <= S - 128) by (unfold A; Z.div_mod_to_equations; lia).
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (H16 & _ & _ & Hslo & _) & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & _).
  assert (Hsp : lib.Reusable.YG0d.spZ regsT = sp0 + (A - sp0)).
  { unfold lib.Reusable.YG0d.spZ.
    change (lib.Reusable.YK11.getr regsT 2) with (Z_to_bv 64 A).
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_small by lia. lia. }
  assert (Hal : (A - sp0) mod 16 = 0) by (Z.div_mod_to_equations; lia).
  assert (Hraw : lib.Reusable.YK0s.ret_ok (Z_to_bv 64 0x83e78))
    by (unfold lib.Reusable.YK0s.ret_ok; vm_compute; reflexivity).
  rewrite <- PC1.
  eapply lib.Reusable.YA0n.SRr_bind.
  - exact (C_reac_ctrl_parseE1.aj_stack_malloc_at_raw rsegs B LAWS segs_low errno_low ML SMP 1 ASM1 ltac:(lia) W regsT m1
             STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc mdc1 k (A - sp0) (Z_to_bv 64 0x83e78) HJ Hsp Hal ltac:(lia)
             ltac:(unfold lib.Reusable.YG0d.ESTACK; lia) ltac:(subst gp; reflexivity) ltac:(subst tp; reflexivity)
             eq_refl Hraw Hcnt).
  - intros W2 c2 Hle (EW & S2 & regs2 & mem2 & md2 & pos & Ec & HJ2 & HP & H10 & HAB & HFR & HNI & HNEV & HBB & HZ &
      HFL & HKEPT & HPRE & HAR2 & (f2 & ES2) & HFP & HKV & HWP).
    subst W2 c2.
    assert (EB : lib.Reusable.YG00.fs_frame_bytes 1 = 128) by reflexivity.
    assert (P1 : lib.Reusable.YG0f.ly_stk_lo lyc <= S - 8800) by (rewrite Eslo; lia).
    assert (P2 : S - 8800 <= lib.Reusable.YG0d.spZ regsT - lib.Reusable.YG0d.ESTACK)
      by (rewrite Hsp; unfold lib.Reusable.YG0d.ESTACK; lia).
    assert (P3 : forall a, S - 8800 <= a < lib.Reusable.YG0d.spZ regsT - lib.Reusable.YG0d.ESTACK ->
                   lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m1 a)
      by (intros a Ha; rewrite Hsp in Ha; apply Hpres; unfold lib.Reusable.YG0d.ESTACK in Ha; lia).
    assert (P4 : 1 <= 128 <= lib.Reusable.YG00.fs_frame_bytes 1) by (rewrite EB; lia).
    pose proof (lib.B.ProgWorldAstack.ctl_fs_of_astack B 1 lib.B.ProgWorld.ctl_fs_geom LAWS ltac:(lia) lyc Sc S2 W regsT regs2
                  m1 mem2 mdc1 md2 pos (S - 8800) 128 HPRE P1 P2 P3 HFR HNI HAR2 H10 HZ HFL HWP HKV P4) as CF.
    cbv zeta in CF.
    destruct (lib.B.ProgWorld.ctl_fs_geom (lib.Reusable.YG0f.ly_F lyc) 1 pos ltac:(lia)) as (G1 & G2 & G3 & G4 & _).
    change (Z.to_nat 1) with 1%nat in CF, G1, G2, G3, G4.
    rewrite G2, G3, G4, EB in CF.
    change (lib.Reusable.YG0f.ly_F lyc + lib.Reusable.YG0f.fs_frame_off 1 pos)
      with (lib.Reusable.YG0f.frame_addr lyc 1 pos) in CF.
    change (lib.Reusable.YG0f.ly_F lyc + lib.Reusable.YG0f.fs_flag_off 1 pos)
      with (lib.Reusable.YG0f.flag_addr lyc 1 pos) in CF.
    destruct CF as (Cpos & C10 & CFL & C120 & CSH & CAD & CST & CAPP & C64 & CFS & CFE & CGT & CWIN).
    rewrite Hsp in CWIN. replace (sp0 + (A - sp0)) with A in CWIN by lia.
    replace (sp0 + (A - sp0)) with A in HKEPT by lia.
    replace (lib.Reusable.YG0f.frame_addr lyc 1 pos + 128 - 8) with (lib.Reusable.YG0f.frame_addr lyc 1 pos + 120)
      in C120 by lia.
    exact (K S2 regs2 mem2 md2 pos f2 HJ2 HP C10 HAB HFR HNI ES2 HKEPT CFL C120 CST CAPP C64 CGT CFS CFE CWIN).
Qed.

End Pf.

(* ================================================================================================================
   The theorem.  pb_reac_ctrl_parse : treac_ctrl_parse_spec (lib/B/Prog/C_reac_ctrl_parse.v, a Theorem Labs lane's spec of record,
   unchanged) at SEGS := Reusable.YB1v.tfibsegs (= B.Img0.rsegs, ProgBridge.tfibsegs_rsegs), in this file
   (the spec file stays Definitions-only).  Its shape follows a Theorem Labs lane's proved image-B glue
   lib/B/Prog/C_reac_ctrl_classify_box_frame.v (pb_reac_ctrl_classify_box_frame), whose helper lemmas it reuses. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require C_reac_ctrl_parse C_reac_ctrl_classify_box_frame
  C_reac_ctrl_parseK C_reac_ctrl_parseW asan_memsetF_on asan_memcpyF_on bcmp_wrap_on kind_of_link1F memset sh_word_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorldCtlRtC ProgWorldShadow ProgWorldVisWin
  ProgWorldVisFrame ProgWorldVisHeap ProgWorld_Fs ProgBridgeData ShadowRwOn ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v YE01 YE2k YF0m APostBase YP09 YG0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse.
(* reg_get (LinuxProcessSemantics.Riscv.Sem, the register-map read the register forms below name), as
   C_reac_ctrl_parseLib.v Imports it *)
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
Open Scope Z_scope.
Module BPS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.C_reac_ctrl_parse.
Module CLS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.C_reac_ctrl_classify_box_frame.
Module PL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.C_reac_ctrl_parseLib.
Module PK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.C_reac_ctrl_parseK.
Module PWW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.C_reac_ctrl_parseW.

(* ---- Helpers of the theorem (generic, Qed). ---- *)

(* Two ranges with no common byte are apart. *)
Lemma rcpB_dj_of_pt : forall a la b lb, 0 < la -> 0 < lb ->
  (forall x, a <= x < a + la -> ~ (b <= x < b + lb)) -> PL.rcpB_dj a la b lb.
Proof.
  intros a la b lb Ha Hb H. unfold PL.rcpB_dj.
  destruct (Z_le_gt_dec (a + la) b) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec (b + lb) a) as [R|R]; [right; exact R|].
  exfalso. apply (H (Z.max a b)); lia.
Qed.

(* The core's two shadow-address functions agree (SHADOW_OFF = ASAN_K = 0x7fff8000). *)
Lemma rcpB_sh_eq : forall x, lib.Reusable.YG0f.shadow_addr x = lib.B.AsanRT.shadow_addr x.
Proof.
  intros x. unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, lib.B.AsanRT.shadow_addr,
    lib.B.AsanRT.ASAN_K. lia.
Qed.

(* A byte the stretch's write list Wq (C_reac_ctrl_parseLib.v) names lies in one of its five ranges. *)
Lemma rcpB_wq_cases : forall o S Fr FL a, ~ outside (PL.Wq o S Fr FL) a ->
  (S - 8800 <= a < S) \/ (Fr <= a < Fr + 128) \/
  (lib.B.AsanRT.shadow_addr Fr <= a < lib.B.AsanRT.shadow_addr Fr + 16) \/ a = FL \/ (o <> 0 /\ o <= a < o + 36).
Proof.
  intros o S Fr FL a Ho. unfold PL.Wq in Ho.
  destruct (Z.eq_dec o 0) as [E0|E0].
  - rewrite (proj2 (Z.eqb_eq o 0) E0) in Ho. cbn [app outside] in Ho. lia.
  - rewrite (proj2 (Z.eqb_neq o 0) E0) in Ho. cbn [app outside] in Ho. lia.
Qed.

(* A frame byte or a frame-shadow byte, from acall_kept's form to C_reac_ctrl_parseW.rcpW_apart_frame's. *)
Lemma rcpB_fr_or : forall ly c q a,
  lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng ly (c, q)) \/
  lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr ly c q),
                             lib.Reusable.YG00.fs_frame_bytes c / 8) ->
  (lib.Reusable.YG0f.frame_addr ly c q <= a < lib.Reusable.YG0f.frame_addr ly c q + lib.Reusable.YG00.fs_frame_bytes c \/
   lib.B.AsanRT.shadow_addr (lib.Reusable.YG0f.frame_addr ly c q) <= a <
     lib.B.AsanRT.shadow_addr (lib.Reusable.YG0f.frame_addr ly c q) + lib.Reusable.YG00.fs_frame_bytes c / 8).
Proof.
  intros ly c q a H. unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in H. cbn [fst snd] in H.
  rewrite rcpB_sh_eq in H. exact H.
Qed.

(* .str.4's six bytes lie in the image: the shadow words the bcmp wrapper's checks load for any sub-range of them
   (sh_word_on) are the shadow of image addresses (ACtlRtC.img_shadow). *)
Lemma rcpB_sh_word_bc : forall p k a, REAC_CTRL_PARSE_BC <= p -> p + k <= REAC_CTRL_PARSE_BC + 6 ->
  lib.B.Prog.sh_word_on.sh_word_on p k a -> lib.B.ACtlRtC.img_shadow a.
Proof.
  intros p k a Hp Hk Hw.
  pose proof (PWW.rcpW_sh_word_cover _ _ p k a Hp Hk Hw) as [C1 C2].
  assert (E1 : lib.Reusable.YG0f.shadow_addr REAC_CTRL_PARSE_BC / 8 * 8 = 2147467840) by reflexivity.
  assert (E2 : lib.Reusable.YG0f.shadow_addr (REAC_CTRL_PARSE_BC + 6 - 1) / 8 * 8 + 8 = 2147467848) by reflexivity.
  rewrite E1 in C1. rewrite E2 in C2.
  unfold lib.B.ACtlRtC.img_shadow. exists ((a - lib.Reusable.YG0f.SHADOW_OFF) * 8).
  unfold lib.B.Prog.CtrlRo.IMG_LO, lib.B.Prog.CtrlRo.IMG_HI, lib.Reusable.YG0f.shadow_addr,
    lib.Reusable.YG0f.SHADOW_OFF.
  rewrite Z.div_mul by lia. lia.
Qed.

Section PBH.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.

(* At a byte the hidden set does not hide, the core's view is ctrl's mrd (ProgWorld.aview_vis_mrd, for any H). *)
Lemma rcpB_aview_mrd : forall (H : word -> bool) (m : word -> option byte) a, H (Z_to_bv 64 a) = false ->
  lib.Reusable.YG0n.aview rsegs H m a = option_map (fun b : byte => bv_unsigned b) (mrd rsegs m (wa a)).
Proof.
  intros H m a Hh.
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict, mrd, wa.
  rewrite Hh. reflexivity.
Qed.

(* Equal views at a visible byte: equal mrd. *)
Lemma rcpB_mrd_of_view : forall (H : word -> bool) (m m' : word -> option byte) a,
  H (Z_to_bv 64 a) = false ->
  lib.Reusable.YG0n.aview rsegs H m' a = lib.Reusable.YG0n.aview rsegs H m a ->
  mrd rsegs m' (wa a) = mrd rsegs m (wa a).
Proof.
  intros H m m' a Hh E. rewrite (rcpB_aview_mrd H m' a Hh), (rcpB_aview_mrd H m a Hh) in E.
  destruct (mrd rsegs m' (wa a)) as [b'|], (mrd rsegs m (wa a)) as [b|]; cbn [option_map] in E;
    try discriminate E; [|reflexivity].
  injection E as Eb. f_equal. apply bv_eq. exact Eb.
Qed.

(* Bytes the view reads at visible addresses are a bytes_at. *)
Lemma rcpB_bytes_of_view : forall (H : word -> bool) (m : word -> option byte) a (bs : list byte) (d : byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, (i < length bs)%nat -> H (Z_to_bv 64 (a + Z.of_nat i)) = false) ->
  (forall i, (i < length bs)%nat ->
     lib.Reusable.YG0n.aview rsegs H m (a + Z.of_nat i) = Some (bv_unsigned (nth i bs d))) ->
  bytes_at rsegs m a bs.
Proof.
  intros H m a bs d H0 H1 Hh Hv. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (Hv i Hi) as V. rewrite (rcpB_aview_mrd H m _ (Hh i Hi)) in V.
  rewrite (nth_error_nth' bs d Hi).
  destruct (mrd rsegs m (wa (a + Z.of_nat i))) as [b|]; cbn [option_map] in V; [|discriminate V].
  injection V as V. f_equal. apply bv_eq. exact V.
Qed.

(* A writable range above the image whose bytes are not hidden is present. *)
Lemma rcpB_pres_of_stk : forall (H : word -> bool) (m : word -> option byte) lo hi,
  lib.B.Prog.ImgBounds.IMG_HI <= lo -> stk rsegs m lo hi ->
  (forall a, lo <= a < hi -> H (Z_to_bv 64 a) = false) ->
  forall a, lo <= a < hi -> lib.Reusable.YG0n.apresent H m a.
Proof.
  intros H m lo hi Hlo (H0 & H1 & Hs) Hh a Ha.
  unfold lib.B.Prog.ImgBounds.IMG_HI in Hlo.
  split; [exact (Hh a Ha)|].
  destruct (Hs a Ha) as [_ (b & Hb)]. unfold mrd in Hb.
  assert (Hr : seg_rom rsegs (wa a) = None).
  { apply CLS.cls_noimg_rom. rewrite wa_unsigned by lia. apply CLS.cls_hi_noimg. lia. }
  destruct (m (wa a)) as [b'|] eqn:E; [exists b'; exact E|]. rewrite Hr in Hb. discriminate Hb.
Qed.
End PBH.

Section PB.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
(* The journal's sink head is generic: lib.B.ProgWorldAstack.ctl_release_of_free_law is generic in SK since B ProgWorld
   (6ea7ff50f8f, Section Fs's Context); a Theorem Labs lane's consumer instantiates SK := Reusable.YE2k.tfib_sink_head. *)
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
Variables RLO RHI : Z.
(* The named premises still carried, each with its owner:
     errno_low api_env (YCbq.v:808)                                   core, PENDING THE RECORD CORE (YCeg.tl_env)
     ML        model_laws of B's universe                             core (TfibLib)
     PC1       the class-1 entry of B's code table = 0x3d868           core (TfibLib code table)
     TS        CtrlTSyms B, the bundle law                            core (YF0m.v)
     SMP, ASM1 class-1 fake-stack rules                               a working branch
     ASF       astack_free_law (YG0d.v:301), the frame release         a working branch
   No AR_states law is a premise: the callees' route-(C) _on texts (asan_memset_cF_on.v, asan_memcpy_cF_on.v,
   bcmp_wrap_c_on.v) take shadow_rw_on over the shadow they touch, which W11 (rcpW_rt) supplies at mem2 from
   ProgWorldCtlRtC.ctl_rt_C_of_AR, whose premises are TS and the AR laws only.  .str.4 (REAC_CTRL_PARSE_BC) is no
   longer a premise: rcpB_str4_sh / rcpB_str4_vis below derive it from ProgBridgeData's facts, which take TS. *)
(* AR_laws of B's bundle: proved by the core, Reusable.YG0q.AR_laws_ok (no premise). *)
Lemma LAWS : lib.Reusable.YG0d.AR_laws rsegs B.
Proof. exact (lib.Reusable.YG0q.AR_laws_ok rsegs B). Qed.
Hypothesis errno_low : lib.Reusable.YCbq.api_env rsegs B.
Hypothesis ML : lib.Reusable.YG0d.model_laws (lib.Reusable.YG0f.as_universe B).
Hypothesis SMP : lib.Reusable.YCbq.stack_malloc_progressP B.
Hypothesis ASM1 : lib.Reusable.YG0d.astack_malloc_realizes rsegs B 1.
Hypothesis PC1 : lib.Reusable.YG0f.pc_stack_malloc (lib.Reusable.YG0f.as_code B) 1 = ASAN_STACK_MALLOC_1.
Hypothesis ASF : lib.Reusable.YG0d.astack_free_law rsegs B.
Hypothesis TS : lib.Reusable.YF0m.CtrlTSyms B.
(* .str.4 (REAC_CTRL_PARSE_BC, the 6 bytes the bcmp wrapper reads): its shadow is zero, and its 8-aligned shadow cover is
   visible, at every AR state: ProgBridgeData's facts ctl_parse_bc_addressable / ctl_parse_bc_shadow_vis (BridgeDataB,
   a working branch 7b1b48d7262; they take CtrlTSyms B = TS). *)
Lemma rcpB_str4_sh : forall ly S (W : lib.Reusable.YA0n.world rsegs) m md,
  lib.Reusable.YG0n.AR rsegs B ly S W m md -> addressable m REAC_CTRL_PARSE_BC 6.
Proof using TS. exact (lib.B.ProgBridgeData.ctl_parse_bc_addressable B TS). Qed.

Lemma rcpB_str4_vis : forall ly S (W : lib.Reusable.YA0n.world rsegs) m md,
  lib.Reusable.YG0n.AR rsegs B ly S W m md ->
  PWW.rcpW_shk (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) REAC_CTRL_PARSE_BC 6.
Proof using TS.
  intros ly S W m md HAR.
  pose proof (lib.B.ProgBridgeData.ctl_parse_bc_shadow_vis B TS ly S W m md HAR) as (V0 & V1 & V).
  apply (PWW.rcpW_cover (lib.Reusable.YA0n.w_H W) REAC_CTRL_PARSE_BC 6).
  intros a b Ha Hab Hb.
  unfold lib.B.Prog.rng_asan.sh_al8_lo, lib.B.Prog.rng_asan.sh_al8_hi, shadow_addr in *.
  unfold REAC_CTRL_PARSE_BC, ASAN_K in *.
  assert (E1 : (a / 8 + 2147450880) / 8 * 8 = (0x21200 / 8 + 2147450880) / 8 * 8) by (Z.div_mod_to_equations; lia).
  assert (E2 : (a + (b - a + 1) - 1) / 8 = b / 8) by (f_equal; lia).
  assert (E3 : (b / 8 + 2147450880) / 8 * 8 = ((0x21200 + 6 - 1) / 8 + 2147450880) / 8 * 8)
    by (Z.div_mod_to_equations; lia).
  rewrite E2. rewrite E1, E3. split; [exact V0|]. split; [exact V1 | exact V].
Qed.

Theorem pb_reac_ctrl_parse :
  BPS.treac_ctrl_parse_spec (SK := SK) lib.Reusable.YB1v.tfibsegs B RLO RHI.
Proof.
  unfold BPS.treac_ctrl_parse_spec.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs f n o fr
    HJ ARO HRA HRA4 Hgp Htp H10 H11 H12 Hn HS16 Hlo Hhi Hcnt HFB Hof Hawr Lfr Hfr.
  change lib.Reusable.YB1v.tfibsegs with rsegs in *.
  set (S := lib.Reusable.YG0d.spZ regs) in *.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _ & _).
  destruct Hastk as (H16sp0 & HSTK & Hceil & Hslo & Hshi & H47 & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 Hc1] _].
  pose proof (@lib.Reusable.YM05.alloc_ceiling_lt rc) as Hclt.
  unfold BPS.REAC_CTRL_PARSE_STK in Hlo.
  assert (B1 : lib.Reusable.YM05.alloc_ceiling <= S - 8800) by lia.
  assert (B2 : S <= 2 ^ 47) by lia.
  assert (B3 : HIGHMEM_BEG <= S - 8800) by (unfold HIGHMEM_BEG; lia).
  assert (B4 : S <= APPMEM_END) by (unfold APPMEM_END; lia).
  assert (RS : 8800 <= S < 2 ^ 64) by lia.
  (* the runtime at the caller memory: asan_cells and ro_agree of ctl_rt_C (ProgWorldCtlRtC.ctl_rt_C_of_AR) *)
  destruct (lib.B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TS LAWS RLO RHI _ _ _ _ _ HAR
              (lib.B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ ARO (Z.le_refl _) (Z.le_refl _)))
    as (RACc & _ & _ & ROc0).
  assert (ROc : lib.B.MemNorm.ro_agree rsegs memc) by exact ROc0.
  pose proof RACc as (CK & GCK & _ & _ & _ & UA & GUA & _).
  (* a0 / a2 as numbers *)
  set (fZ := bv_unsigned (lib.Reusable.YK11.getr regs 10)).
  assert (RfZ : 0 <= fZ < 2 ^ 64).
  { pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs 10)) as R.
    change (bv_modulus 64) with (2 ^ 64) in R. exact R. }
  assert (EfZ : 50 <= n -> fZ = f /\ exists Lf, In (f, Lf) (lib.Reusable.YG0d.ablocks B lyc Sc) /\
                  50 <= lib.Reusable.YG00.req_size Lf /\ 4096 <= f /\
                  f + lib.Reusable.YG00.req_size Lf <= lib.Reusable.YM05.alloc_ceiling).
  { intros Hn50. destruct (HFB Hn50) as (Lf & InF & HLf).
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS _ _ _ _ _ f Lf HAR InF) as (_ & Hf0 & Hf1 & _).
    split; [|exists Lf; repeat split; assumption].
    unfold fZ. rewrite H10. unfold lib.Reusable.YG0d.w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  assert (HoF : o <> 0 -> exists co po, In (co, po) (lib.Reusable.YG01.frames Sc) /\
            lib.Reusable.YG0f.frame_addr lyc co po <= o /\
            o + 36 <= lib.Reusable.YG0f.frame_addr lyc co po + lib.Reusable.YG00.fs_frame_bytes co).
  { intros Hne. destruct (Hof Hne) as ((co & po & Ino & _ & _ & Hf1 & Hf2) & _ & _).
    exists co, po. repeat split; assumption. }
  assert (Ro : 0 <= o < 2 ^ 64).
  { destruct (Z.eq_dec o 0) as [->|Hne]; [lia|]. destruct (HoF Hne) as (co & po & Ino & Hf1 & Hf2).
    destruct (lib.Reusable.YCbq.frames_bounds rsegs B LAWS lyc Sc W memc mdc co po HAR Ino) as (F1 & F2 & _).
    pose proof (lib.Reusable.YCbq.fs_frame_bytes_nonneg co). lia. }
  (* G0: the entry state in the form of rcpB_to_E1 *)
  rewrite lib.B.ProgBridge.cfg_at_MS. unfold BPS.A_reac_ctrl_parseP.
  assert (XR0 : Regs6ss.xregs_eqv
    (mkR (reg_get regs 1) (Z_to_bv 64 S) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5) (reg_get regs 6)
       (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (Z_to_bv 64 fZ) (Z_to_bv 64 n) (Z_to_bv 64 o)
       (reg_get regs 13) (reg_get regs 14) (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (reg_get regs 18)
       (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24)
       (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30)
       (reg_get regs 31)) regs).
  { apply Regs6ss.xregs_eqv_sym. apply Regs6ss.mkR_eqv_of;
      first [ reflexivity | exact H11 | exact H12
            | (unfold fZ; rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned; reflexivity)
            | (unfold S, lib.Reusable.YG0d.spZ; rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned; reflexivity) ]. }
  refine (lib.Reusable.YA0nR.SRr_xregs_eqv rsegs W _ regs _ _ _ _ _ _ _ _ _ XR0).
  change (lib.Reusable.YK11.seg_rom rsegs) with (seg_rom rsegs).
  change (Z_to_bv 64 0x83e04) with (Z_to_bv 64 REAC_CTRL_PARSE).
  (* S-A + J1 *)
  apply (rcpB_to_E1 B LAWS CLS.cls_segs_low lib.B.ProgBridgeData.rsegs_wx_nowrap STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc
           W memc mdc k (reg_get regs 1) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5) (reg_get regs 6)
           (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15)
           (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21)
           (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27)
           (reg_get regs 28) (reg_get regs 29) (reg_get regs 30) (reg_get regs 31) lib.Reusable.YK11.fp_regs
           lib.Reusable.YK11.fp_csr fZ n o S _ HJ Hlo Hhi RfZ Hn Ro RS HS16 B3 B4 ROc
           (CLS.cls_stk_of_pres (lib.Reusable.YA0n.w_H W) memc (S - 8800) S ltac:(lia) ltac:(lia)
              (fun a Ha => Hpres a ltac:(lia)))
           CK GCK UA GUA).
  { split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hpres a ltac:(lia))). }
  intros m1 m1n mdc1 MU1 WM1 RM1 MI1 SV1 HMR1 HROS1 HJ1.
  (* E1 *)
  apply (rcpB_E1 B LAWS CLS.cls_segs_low errno_low ML SMP ASM1 PC1 STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc1 k
           (reg_get regs 3) (reg_get regs 4) (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (reg_get regs 13)
           (reg_get regs 14) (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19)
           (reg_get regs 23) (reg_get regs 24) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29)
           (reg_get regs 30) (reg_get regs 31) fZ n o S _ HJ1 Hlo Hhi RS HS16 Hgp Htp Hcnt).
  intros S2 regs2 mem2 md2 pos f2. cbv zeta.
  intros HJ2 HP C10 HAB HFR HNI ES2 HKEPT CFL C120 CST CAPP C64 CGT CFS CFE CWIN.
  (* ================= the facts at the return memory mem2 of the class-1 request ================= *)
  pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _ & _ & _).
  assert (HA : ((S - 128) / 32 * 32) mod 32 = 0 /\ S - 160 < (S - 128) / 32 * 32 <= S - 128)
    by (Z.div_mod_to_equations; lia).
  assert (In1 : In (1, pos) (lib.Reusable.YG01.frames S2)) by (rewrite HFR; left; reflexivity).
  assert (InSc : forall c q, In (c, q) (lib.Reusable.YG01.frames Sc) -> In (c, q) (lib.Reusable.YG01.frames S2))
    by (intros c q Hcq; rewrite HFR; right; exact Hcq).
  assert (Ne1 : forall c q, In (c, q) (lib.Reusable.YG01.frames Sc) -> (c, q) <> (1, pos))
    by (intros c q Hcq E; rewrite E in Hcq; exact (HNI Hcq)).
  assert (InB2 : forall p m, In (p, m) (lib.Reusable.YG0d.ablocks B lyc Sc) ->
                   In (p, m) (lib.Reusable.YG0d.ablocks B lyc S2))
    by (intros p m Hpm; rewrite HAB; exact Hpm).
  assert (EB1 : lib.Reusable.YG00.fs_frame_bytes 1 = 128) by reflexivity.
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  pose proof (PWW.rcpW_frame B LAWS lyc S2 W mem2 md2 pos HAR2 In1) as WF. cbv zeta in WF.
  destruct WF as (FkLo & FkCeil & FLimg & FLceil & FlApp & FlSt & FLvis & SHimg & SHceil).
  (* the views at mem2: the prologue kept every byte off [S - 128, S), the call keeps (acall_kept) *)
  pose proof (PK.rcpK_raw_SA memc m1 m1n (S - 128) S HMR1 HROS1 MU1) as RA1.
  pose proof HKEPT as (KP1 & KP2 & KP3 & KP4 & KP5 & KP6).
  assert (VA : forall H a, 0 <= a < S - 128 ->
                 lib.Reusable.YG0n.aview rsegs H m1 a = lib.Reusable.YG0n.aview rsegs H memc a).
  { intros H a Ha. apply PK.rcpK_aview_eq. apply RA1. rewrite PK.rcpK_u64 by lia. lia. }
  assert (ARO2 : lib.Reusable.YE01.arodata_okS rsegs B RLO RLO
                   (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2)).
  { intros a Hro Hst Her. destruct Hro as [(sg & Hsg & Hwr & Hr) | Hg]; [|lia].
    assert (Hai : lib.Reusable.YG0d.in_img rsegs a) by (exists sg; split; [exact Hsg | exact Hr]).
    pose proof (CLS.cls_img_lt a Hai) as Hia.
    rewrite (KP3 a Hai Hst Her). rewrite (VA _ a ltac:(lia)).
    exact (ARO a (or_introl (ex_intro _ sg (conj Hsg (conj Hwr Hr)))) Hst Her). }
  (* the runtime cells, the read-only agreement, the bcmp wrapper's cells and the writable shadow region at mem2 (W11) *)
  destruct (PWW.rcpW_rt B LAWS TS RLO RLO lyc S2 W mem2 md2 HAR2 ARO2)
    as (RO2 & AC2 & SR2 & HBC2 & HMC2 & HGC2 & H254 & H255).
  (* the window at mem2 (W7, W10) *)
  assert (ST2 : stk rsegs mem2 (S - 8800) S)
    by exact (CLS.cls_stk_of_pres (lib.Reusable.YA0n.w_H W) mem2 (S - 8800) S ltac:(lia) ltac:(lia)
                (fun a Ha => Hpres2 a ltac:(lia))).
  assert (AW2 : addressable mem2 (S - 8800) 8800).
  { destruct (PWW.rcpW_win B LAWS STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem2 md2 k (S - 8800) S HJ2
                ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & AW & _).
    replace (S - (S - 8800)) with 8800 in AW by lia. exact AW. }
  destruct (PWW.rcpW_vis_win B LAWS STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem2 md2 k (S - 8800) 8800
              HJ2 ltac:(lia) ltac:(lia) ltac:(lia)) as (RWIN & SCW & _).
  destruct (PWW.rcpW_vis_win B LAWS STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem2 md2 k (S - 2560) 2432
              HJ2 ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & SKW).
  (* the caller's block f (n >= 50) *)
  assert (BLK : 50 <= n -> fZ = f /\ exists Lf, In (f, Lf) (lib.Reusable.YG0d.ablocks B lyc Sc) /\
                  In (f, Lf) (lib.Reusable.YG0d.ablocks B lyc S2) /\ 50 <= lib.Reusable.YG00.req_size Lf /\
                  4096 <= f /\ f + lib.Reusable.YG00.req_size Lf <= lib.Reusable.YM05.alloc_ceiling).
  { intros Hn50. destruct (EfZ Hn50) as (E & Lf & InF & HLf & H4 & Hc). split; [exact E|].
    exists Lf. split; [exact InF|]. split; [exact (InB2 _ _ InF)|]. split; [exact HLf|]. split; [exact H4 | exact Hc]. }
  (* the record buffer o's 36 bytes: some bytes, present (they lie in a caller's frame) *)
  assert (HJK : exists junk : list byte, o <> 0 -> rw_cells rsegs mem2 o [CB 36 junk]).
  { destruct (Z.eq_dec o 0) as [E0|Hne]; [exists []; intros H; exfalso; exact (H E0)|].
    destruct (Hof Hne) as ((co & po & Ino & _ & _ & Hf1 & Hf2) & _ & _).
    destruct (PWW.rcpW_in_frame B LAWS lyc S2 W mem2 md2 co po o 36 HAR2 (InSc co po Ino) ltac:(lia) Hf1 Hf2)
      as (_ & _ & _ & _ & STo).
    destruct (stk_carve rsegs mem2 o (o + 36) 36 STo ltac:(lia)) as [_ [junk Hj]].
    replace (o + 36 - Z.of_nat 36) with o in Hj by lia.
    exists junk. intros _. exact Hj. }
  destruct HJK as (junk & Hjunk).
  (* ---- C_reac_ctrl_parseLib's Section RoFB hypotheses at mem2 ---- *)
  assert (HF : 50 <= n -> 0 < fZ /\ fZ + 50 <= 2 ^ 64 /\ (fZ + 50 <= S - 8800 \/ S <= fZ)).
  { intros Hn50. destruct (BLK Hn50) as (E & Lf & _ & _ & HLf & H4 & Hc). rewrite E. lia. }
  assert (BYf : 50 <= n -> bytes_at rsegs mem2 fZ fr).
  { intros Hn50. destruct (BLK Hn50) as (E & Lf & InF & InF2 & HLf & H4 & Hc). rewrite E.
    pose proof (lib.B.ProgWorldVisHeap.heap_vis B LAWS lyc S2 W mem2 md2 f Lf f 50 HAR2 InF2 ltac:(lia) ltac:(lia))
      as (_ & _ & VF).
    apply (rcpB_bytes_of_view (lib.Reusable.YA0n.w_H W) mem2 f fr lib.Prog.RcParse.cp_z);
      [lia | rewrite Lfr; lia | |].
    - intros i Hi. rewrite Lfr in Hi. apply VF. lia.
    - intros i Hi. rewrite Lfr in Hi.
      rewrite (KP2 f Lf (Z.of_nat i) InF ltac:(lia) ltac:(intros [])).
      rewrite VA by lia. exact (Hfr Hn50 i Hi). }
  assert (Hrd : forall i, In i (lib.Prog.RcParse.cp_rd n fr) ->
                  mrd rsegs mem2 (wa (fZ + Z.of_nat i)) = nth_error fr i).
  { intros i Hi. destruct (Z_le_gt_dec 50 n) as [Hn50|Hn50].
    - destruct (BYf Hn50) as (_ & _ & Hb). apply Hb. rewrite Lfr.
      pose proof (lib.Prog.RcParse.cp_rd_lt39 n fr i Hi). lia.
    - exfalso. unfold lib.Prog.RcParse.cp_rd in Hi.
      replace (50 <=? n) with false in Hi by (symmetry; apply Z.leb_gt; lia). cbn in Hi. exact Hi. }
  assert (HOK : o <> 0 -> o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs mem2 o [CB 36 junk] /\
                  (o + 36 <= S - 8800 \/ S <= o) /\ (50 <= n -> o + 36 <= fZ \/ fZ + 50 <= o)).
  { intros Hne. destruct (Hof Hne) as ((co & po & Ino & _ & Hf8 & Hf1 & Hf2) & Ho8 & _).
    destruct (lib.Reusable.YCbq.frames_bounds rsegs B LAWS lyc Sc W memc mdc co po HAR Ino) as (F1 & F2 & F3).
    split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [exact (Hjunk Hne)|]. split; [left; lia|].
    intros Hn50. destruct (BLK Hn50) as (E & Lf & InF & _ & HLf & _). rewrite E.
    pose proof (lib.Reusable.YCbq.sep_block_frame rsegs B LAWS lyc Sc W memc mdc f Lf co po HAR InF Ino) as D.
    unfold lib.Reusable.YG0f.zdisjoint in D. cbn [fst snd] in D. lia. }
  assert (AF0 : 50 <= n -> addressable mem2 fZ 50).
  { intros Hn50. destruct (BLK Hn50) as (E & Lf & _ & InF2 & HLf & _). rewrite E.
    exact (lib.B.ProgWorldShadow.ctl_block_shadow_of_AR B LAWS lyc S2 W mem2 md2 f Lf f 50 HAR2 InF2
             (Z.le_refl _) ltac:(lia) ltac:(lia)). }
  assert (AO0 : o <> 0 -> addressable mem2 o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)).
  { intros Hne. destruct (Hof Hne) as ((co & po & Ino & _ & Hf8 & Hf1 & Hf2) & Ho8 & RAo).
    destruct (lib.Reusable.YCbq.frames_bounds rsegs B LAWS lyc Sc W memc mdc co po HAR Ino) as (F1 & F2 & F3).
    destruct (PWW.rcpW_in_frame B LAWS lyc Sc W memc mdc co po o 36 HAR Ino ltac:(lia) Hf1 Hf2) as (_ & OH & _).
    destruct (CLS.cls_frame_al64 B lyc Sc W memc mdc co po HAR Ino) as (Ao1 & Ao2 & Ao3).
    split; [|split].
    - apply (CLS.cls_addressable_of_view W mem2 o 36); [lia | lia | unfold APPMEM_END; lia | |].
      + intros i Hi. apply (CLS.cls_app_of_in_app _ _ (o + i) F3). lia.
      + apply (CLS.cls_ra_transfer (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc)); [|exact RAo].
        intros x Hx.
        assert (Hsx : lib.Reusable.YG0n.in_zr (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF x)
                  (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr lyc co po),
                   lib.Reusable.YG00.fs_frame_bytes co / 8)).
        { apply CLS.cls_sh_in_frame; [exact Hf8 | Z.div_mod_to_equations; lia | lia]. }
        transitivity (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m1
                        (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF x)).
        * exact (KP4 co po _ Ino (or_intror Hsx) (fun H => H)).
        * apply VA. unfold lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF.
          Z.div_mod_to_equations. lia.
    - destruct F3 as [_ F3].
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END.
      unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg, lib.Reusable.YG0f.ASAN_CEIL in F3. lia.
    - right. unfold CF, lib.B.Prog.ImgBounds.IMG_HI in *. lia. }
  assert (HOro : o <> 0 -> forall i, 0 <= i < 36 -> ro_addr rsegs (wa (o + i)) = false).
  { intros Hne. destruct (Hof Hne) as ((co & po & Ino & _ & _ & Hf1 & Hf2) & _ & _).
    exact (proj1 (proj2 (proj2
             (PWW.rcpW_in_frame B LAWS lyc Sc W memc mdc co po o 36 HAR Ino ltac:(lia) Hf1 Hf2)))). }
  pose proof (rcpB_str4_sh lyc S2 W mem2 md2 HAR2) as ABC.
  (* the callees' writable shadow P2 (route (C)): the shadow of S2's own regions or of the image, writable at mem2 (W11),
     covering the shadow words the checks load for the new frame (W12 at (1, pos)), f's 50 bytes (W13 at f's block),
     o's 36 bytes (W12 at o's frame, a frame of Sc, so of S2) and .str.4's 6 bytes (rcpB_sh_word_bc) *)
  pose (P2 := fun a : Z => lib.B.ACtlRtC.cut_shadow B lyc S2 a \/ lib.B.ACtlRtC.img_shadow a).
  assert (SR0 : lib.B.ShadowRwOn.shadow_rw_on P2 mem2) by exact SR2.
  assert (SRFr : forall p k a, lib.Reusable.YG0f.frame_addr lyc 1 pos <= p ->
                   p + k <= lib.Reusable.YG0f.frame_addr lyc 1 pos + 128 ->
                   lib.B.Prog.sh_word_on.sh_word_on p k a -> P2 a).
  { intros pw kw aw Hp Hk Hw. cbv beta delta [P2]. left.
    exact (PWW.rcpW_sh_word_frame B lyc S2 W mem2 md2 1 pos pw kw aw HAR2 In1 Hp ltac:(rewrite EB1; exact Hk) Hw). }
  assert (SRf : 50 <= n -> forall p k a, fZ <= p -> p + k <= fZ + 50 ->
                  lib.B.Prog.sh_word_on.sh_word_on p k a -> P2 a).
  { intros Hn50 pw kw aw Hp Hk Hw. destruct (BLK Hn50) as (E & Lf & _ & InF2 & HLf & _). rewrite E in Hp, Hk.
    cbv beta delta [P2]. left.
    exact (PWW.rcpW_sh_word_block B lyc S2 f Lf pw kw aw InF2 Hp ltac:(lia) Hw). }
  assert (SRo : o <> 0 -> forall p k a, o <= p -> p + k <= o + 36 ->
                  lib.B.Prog.sh_word_on.sh_word_on p k a -> P2 a).
  { intros Hne pw kw aw Hp Hk Hw. destruct (Hof Hne) as ((co & po & Ino & _ & _ & Hf1 & Hf2) & _ & _).
    cbv beta delta [P2]. left.
    exact (PWW.rcpW_sh_word_frame B lyc S2 W mem2 md2 co po pw kw aw HAR2 (InSc co po Ino) ltac:(lia) ltac:(lia)
             Hw). }
  assert (SRbc : forall p k a, REAC_CTRL_PARSE_BC <= p -> p + k <= REAC_CTRL_PARSE_BC + 6 ->
                   lib.B.Prog.sh_word_on.sh_word_on p k a -> P2 a).
  { intros pw kw aw Hp Hk Hw. cbv beta delta [P2]. right. exact (rcpB_sh_word_bc pw kw aw Hp Hk Hw). }
  (* the new frame and its flag byte (W1-W3) *)
  assert (FkAl : lib.Reusable.YG0f.frame_addr lyc 1 pos mod 32 = 0) by (Z.div_mod_to_equations; lia).
  assert (FkApp : forall i, 0 <= i < 128 -> app_mem (lib.Reusable.YG0f.frame_addr lyc 1 pos + i))
    by (intros i Hi; apply CAPP; lia).
  assert (FkHi : lib.Reusable.YG0f.frame_addr lyc 1 pos + 128 <= S - 8800) by lia.
  assert (FkImg : PL.rcpB_dj (lib.Reusable.YG0f.frame_addr lyc 1 pos) 128 lib.B.Prog.ImgBounds.IMG_LO
                    (lib.B.Prog.ImgBounds.IMG_HI - lib.B.Prog.ImgBounds.IMG_LO)).
  { right. unfold lib.B.Prog.ImgBounds.IMG_LO, lib.B.Prog.ImgBounds.IMG_HI. unfold ASAN_GT in CGT. lia. }
  assert (FkF : 50 <= n -> PL.rcpB_dj fZ 50 (lib.Reusable.YG0f.frame_addr lyc 1 pos) 128).
  { intros Hn50. destruct (BLK Hn50) as (E & Lf & _ & InF2 & HLf & _). rewrite E.
    apply rcpB_dj_of_pt; [lia | lia |]. intros x Hx.
    exact (proj1 (PWW.rcpW_apart_block B LAWS lyc S2 W mem2 md2 pos f Lf x HAR2 In1 InF2 ltac:(lia))). }
  assert (FkO : o <> 0 -> PL.rcpB_dj o 36 (lib.Reusable.YG0f.frame_addr lyc 1 pos) 128).
  { intros Hne. destruct (Hof Hne) as ((co & po & Ino & _ & _ & Hf1 & Hf2) & _ & _).
    apply rcpB_dj_of_pt; [lia | lia |]. intros x Hx.
    exact (proj1 (PWW.rcpW_apart_frame B lyc S2 W mem2 md2 pos co po x HAR2 In1 (InSc co po Ino)
                    (Ne1 co po Ino) ltac:(left; lia))). }
  assert (FlHi : lib.Reusable.YG0f.flag_addr lyc 1 pos + 1 <= S - 8800) by lia.
  assert (FlImg : PL.rcpB_dj (lib.Reusable.YG0f.flag_addr lyc 1 pos) 1 lib.B.Prog.ImgBounds.IMG_LO
                    (lib.B.Prog.ImgBounds.IMG_HI - lib.B.Prog.ImgBounds.IMG_LO)).
  { right. unfold lib.B.Prog.ImgBounds.IMG_LO, lib.B.Prog.ImgBounds.IMG_HI in *. lia. }
  assert (FlF : 50 <= n -> PL.rcpB_dj fZ 50 (lib.Reusable.YG0f.flag_addr lyc 1 pos) 1).
  { intros Hn50. destruct (BLK Hn50) as (E & Lf & _ & InF2 & HLf & _). rewrite E.
    apply rcpB_dj_of_pt; [lia | lia |]. intros x Hx.
    pose proof (proj1 (proj2 (PWW.rcpW_apart_block B LAWS lyc S2 W mem2 md2 pos f Lf x HAR2 In1 InF2 ltac:(lia)))).
    lia. }
  assert (FlO : o <> 0 -> PL.rcpB_dj o 36 (lib.Reusable.YG0f.flag_addr lyc 1 pos) 1).
  { intros Hne. destruct (Hof Hne) as ((co & po & Ino & _ & _ & Hf1 & Hf2) & _ & _).
    apply rcpB_dj_of_pt; [lia | lia |]. intros x Hx.
    pose proof (proj1 (proj2 (PWW.rcpW_apart_frame B lyc S2 W mem2 md2 pos co po x HAR2 In1 (InSc co po Ino)
                                (Ne1 co po Ino) ltac:(left; lia)))).
    lia. }
  (* the footprint premises at RNG := RNG_W (w_H W) (W7-W9, ProgBridge) *)
  assert (RIMG : lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) 0x10000 0x5ee000).
  { pose proof (lib.B.ProgBridge.rng_of_visible _ _ _ (lib.B.ProgBridge.img_vis_W W)) as R.
    unfold lib.B.Prog.ImgBounds.IMG_LO, lib.B.Prog.ImgBounds.IMG_HI in R. exact R. }
  assert (RBC : lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) REAC_CTRL_PARSE_BC 6).
  { apply (lib.Lib.ExecF.rng_sub _ 0x10000 0x5ee000 _ _ RIMG); unfold REAC_CTRL_PARSE_BC; lia. }
  assert (SKBC : lib.B.Prog.reac_ctrl_parseF.shkov (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W))
                   REAC_CTRL_PARSE_BC 6)
    by exact (rcpB_str4_vis lyc S2 W mem2 md2 HAR2).
  assert (VF2 : 50 <= n ->
    lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) fZ 50 /\
    PWW.rcpW_shc (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) fZ 50 /\
    PWW.rcpW_shk (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) fZ 50).
  { intros Hn50. destruct (BLK Hn50) as (E & Lf & _ & InF2 & HLf & _). rewrite E.
    exact (PWW.rcpW_vis_block B LAWS lyc S2 W mem2 md2 f Lf f 50 HAR2 InF2 (Z.le_refl _) ltac:(lia) ltac:(lia)). }
  assert (RINF : 50 <= n -> lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) fZ 50)
    by (intros Hn50; exact (proj1 (VF2 Hn50))).
  assert (SCF : 50 <= n -> lib.B.Prog.reac_ctrl_parseF.shcov (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) fZ 50)
    by (intros Hn50; exact (proj1 (proj2 (VF2 Hn50)))).
  assert (SKF : 50 <= n -> lib.B.Prog.reac_ctrl_parseF.shkov (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) fZ 50)
    by (intros Hn50; exact (proj2 (proj2 (VF2 Hn50)))).
  assert (VO2 : o <> 0 ->
    lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) o 36 /\
    PWW.rcpW_shc (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) o 36 /\
    PWW.rcpW_shk (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) o 36).
  { intros Hne. destruct (Hof Hne) as ((co & po & Ino & _ & _ & Hf1 & Hf2) & _ & _).
    exact (PWW.rcpW_vis_frame B LAWS lyc S2 W mem2 md2 co po o 36 HAR2 (InSc co po Ino) Hf1 Hf2 ltac:(lia)). }
  assert (ROUT : o <> 0 -> lib.Lib.ExecF.rng (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) o 36)
    by (intros Hne; exact (proj1 (VO2 Hne))).
  assert (SCO : o <> 0 -> lib.B.Prog.reac_ctrl_parseF.shcov (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) o 36)
    by (intros Hne; exact (proj1 (proj2 (VO2 Hne)))).
  assert (SKO : o <> 0 -> lib.B.Prog.reac_ctrl_parseF.shkov (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) o 36)
    by (intros Hne; exact (proj2 (proj2 (VO2 Hne)))).
  destruct (PWW.rcpW_vis_frame B LAWS lyc S2 W mem2 md2 1 pos (lib.Reusable.YG0f.frame_addr lyc 1 pos) 128 HAR2 In1
              (Z.le_refl _) ltac:(rewrite EB1; lia) ltac:(lia)) as (RFk & SCFk & SKFk).
  pose proof (lib.B.ProgBridge.rng_of_visible _ _ _ FLvis) as RFl.
  (* the 12 saved registers at [S - 96, S): rcpB_pre_F's cells (normalized memory m1n), read at m1, kept by the call
     (above alloc_ceiling and off its window [A - ESTACK, A)) *)
  assert (SVm : rw_cells rsegs mem2 (S - 96)
      [C8 (reg_get regs 26); C8 (reg_get regs 25); C8 (reg_get regs 24); C8 (reg_get regs 23); C8 (reg_get regs 22);
       C8 (reg_get regs 21); C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9);
       C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { pose proof (lib.B.MemNormTr.rw_cells_of_rel m1 m1n _ _ HMR1 SV1) as SV1r.
    apply (PK.rcpK_rw_cells_tr m1 mem2 (S - 96) _ SV1r).
    - intros i Hi. cbn [cells_size csize Nat.add] in Hi.
      apply (rcpB_mrd_of_view (lib.Reusable.YA0n.w_H W)).
      + exact (proj1 (Hpres2 (S - 96 + i) ltac:(lia))).
      + apply KP1; [lia | unfold lib.Reusable.YG0d.ESTACK; lia].
    - cbn [cells_size csize Nat.add]. apply (CLS.cls_stk_of_pres (lib.Reusable.YA0n.w_H W)); [lia | lia |].
      intros a Ha. apply Hpres2. lia. }
  (* ================= (a) the state at 0x83e78 in rcpB_post_F_ro's register form ================= *)
  assert (XR2 : Regs6ss.xregs_eqv
    (mkR (reg_get regs2 1) (Z_to_bv 64 ((S - 128) / 32 * 32)) (reg_get regs 3) (reg_get regs 4) (reg_get regs2 5)
       (reg_get regs2 6) (reg_get regs2 7) (Z_to_bv 64 S) (Z_to_bv 64 ((S - 128) / 32 * 32))
       (Z_to_bv 64 (lib.Reusable.YG0f.frame_addr lyc 1 pos)) (reg_get regs2 11) (reg_get regs2 12)
       (reg_get regs2 13) (reg_get regs2 14) (reg_get regs2 15) (reg_get regs2 16) (reg_get regs2 17)
       (reg_get regs2 18) (reg_get regs2 19) (Z_to_bv 64 o) (Z_to_bv 64 fZ) (Z_to_bv 64 n) (reg_get regs2 23)
       (reg_get regs2 24) (wa ASAN_K) (reg_get regs2 26) (reg_get regs 27) (reg_get regs2 28) (reg_get regs2 29)
       (reg_get regs2 30) (reg_get regs2 31)) regs2).
  { apply Regs6ss.xregs_eqv_sym. apply Regs6ss.mkR_eqv_of;
      first [ reflexivity | exact C10
            | exact (HP 2 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))
            | exact (HP 3 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))
            | exact (HP 4 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))
            | exact (HP 8 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))
            | exact (HP 9 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))
            | exact (HP 20 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))
            | exact (HP 21 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))
            | exact (HP 22 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))
            | exact (HP 25 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))
            | exact (HP 27 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)) ]. }
  change (lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 0x83e78) mem2 (lib.Reusable.YK11.seg_rom rsegs))
    with (MS regs2 lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x83e78) lib.Reusable.YK11.fp_csr None mem2 (seg_rom rsegs)).
  refine (lib.Reusable.YA0nR.SRr_xregs_eqv rsegs W _ regs2 _ _ _ _ _ _ _ _ _ XR2).
  (* ================= (b) + (c) the re-based stretch, lifted with its run ================= *)
  eapply (GlueLift.rrB_lift_st lib.B.ProgBridgeData.rsegs_wx_nowrap W md2).
  { eapply (PL.rcpB_post_F_ro (reg_get regs 1) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8) (reg_get regs 9)
             (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
             (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27)
             lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem2 fZ n o S fr junk
             (lib.B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W))
             (lib.Reusable.YG0f.frame_addr lyc 1 pos) (lib.Reusable.YG0f.flag_addr lyc 1 pos) P2).
    all: first [ assumption
               | exact (lib.B.ProgBridge.rng_bytes_RNG_W _)
               | exact (lib.B.Prog.asan_memsetF_on.asan_memset_holds_F_on lib.B.Prog.memset.memset_holds)
               | exact lib.B.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on
               | exact lib.B.Prog.bcmp_wrap_on.bcmp_wrap_holds_F_on
               | exact lib.B.Prog.kind_of_link1F.kind_of_link1_F_holds ]. }
  intros ms' md' Hrun HQ Hhid Hs.
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E' & MU' & WM' & RM' & RO' & ST' & HREC' & AW' & HFL').
  subst ms'.
  (* ================= (d) the release: the journal at m' with own and stack_free_state 1 pos S2 ================= *)
  assert (J3 : lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc
                 (lib.Reusable.YG01.stack_free_state 1 pos S2) W m' md' k).
  { lazymatch type of Hrun with
    | lib.Reusable.YK04R.fsteps _ _ ?ms0 ?ms1 =>
        apply (lib.B.ProgWorldAstack.ctl_release_of_free_law B 1 LAWS ASF lib.B.ProgBridgeData.rsegs_wx_nowrap
                 ltac:(lia) STK sp0 FP ly S0 W0 mem0 md0 own lyc S2 W ms0 ms1 md2 md' k pos _
                 (PL.Wq o S (lib.Reusable.YG0f.frame_addr lyc 1 pos) (lib.Reusable.YG0f.flag_addr lyc 1 pos))
                 HJ2 Hrun (lib.B.ProgBridge.fp_avoids_RNG_W _) MU' Hs)
    end.
    - intros a Ha Ho.
      destruct (rcpB_wq_cases o S _ _ a Ho) as [Hw|[Hf|[Hsh|[Hl|[Hne Hoa]]]]].
      + left. left. lia.
      + left. right. right. right. exists 1, pos. split; [left; reflexivity|]. left.
        unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite EB1. lia.
      + left. right. right. right. exists 1, pos. split; [left; reflexivity|]. right.
        unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite EB1, rcpB_sh_eq. lia.
      + right. exact Hl.
      + left. pose proof (Hawr Hne a Hoa) as Haw. rewrite HAB.
        destruct Haw as [Q|[Q|[Q|(cid & pos' & Hown & Q)]]];
          [left; exact Q | right; left; exact Q | right; right; left; exact Q | right; right; right].
        exists cid, pos'. split; [right; exact Hown | exact Q].
    - exact HFL'. }
  (* ================= (e) the post ================= *)
  apply lib.Reusable.YA0n.SRr_ret. unfold BPS.treac_ctrl_parse_post. cbv beta.
  exists lyc, (lib.Reusable.YG01.stack_free_state 1 pos S2).
  eexists _, m', md'.
  split.
  { rewrite (CLS.cls_ret_pc_ok (reg_get regs 1) HRA). reflexivity. }
  split; [exact J3|].
  split.
  { intros r Hr. unfold lib.Reusable.YG0d.acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]; try reflexivity.
    change (lib.Reusable.YK11.getr regs (Z_to_bv 5 2)) with (reg_get regs 2).
    change (lib.Reusable.YK11.getr _ (Z_to_bv 5 2)) with (Z_to_bv 64 S).
    unfold S, lib.Reusable.YG0d.spZ. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. reflexivity. }
  split.
  { change (lib.Reusable.YG01.frames (lib.Reusable.YG01.stack_free_state 1 pos S2))
      with (lib.Reusable.YG00.del_pos (lib.Reusable.YG01.frames S2) 1 pos).
    rewrite HFR. cbn [lib.Reusable.YG00.del_pos]. rewrite !Z.eqb_refl. reflexivity. }
  split.
  { change (lib.Reusable.YG0d.ablocks B lyc (lib.Reusable.YG01.stack_free_state 1 pos S2))
      with (lib.Reusable.YG0d.ablocks B lyc S2). exact HAB. }
  split.
  { exists (lib.Reusable.YG00.mkFS (lib.Reusable.YG00.fs_hint (lib.Reusable.YG00.st_fs S2))
              (lib.Reusable.YG00.del_pos (lib.Reusable.YG00.fs_live (lib.Reusable.YG00.st_fs S2)) 1 pos)).
    rewrite ES2. reflexivity. }
  split; [reflexivity|].
  split.
  { intros Hne i Hi.
    destruct (Hof Hne) as ((co & po & Ino & _ & _ & Hf1 & Hf2) & _ & _).
    pose proof (proj1 (lib.B.ProgWorldVisFrame.frame_vis B LAWS lyc Sc W memc mdc co po o 36 HAR Ino Hf1 Hf2))
      as (_ & _ & VO).
    destruct (HREC' Hne) as ((_ & Bo3) & _). destruct Bo3 as (_ & _ & Bo3).
    assert (Hi' : (i < length (cells_bytes [CB 36 (snd (lib.Prog.RcParse.ctrlparse n fr))]))%nat)
      by (cbn [cells_bytes cbytes]; rewrite app_nil_r, lib.Prog.RcParse.ctrlparse_length; exact Hi).
    pose proof (Bo3 i Hi') as Bi. cbn [cells_bytes cbytes] in Bi. rewrite app_nil_r in Bi.
    rewrite (rcpB_aview_mrd (lib.Reusable.YA0n.w_H W) m' (o + Z.of_nat i) (VO (o + Z.of_nat i) ltac:(lia))), Bi.
    rewrite (nth_error_nth' (snd (lib.Prog.RcParse.ctrlparse n fr)) lib.Prog.RcParse.cp_z
               ltac:(rewrite lib.Prog.RcParse.ctrlparse_length; exact Hi)).
    reflexivity. }
  (* acall_kept from memc to m' over [S - 8800, S), E = the record *)
  unfold BPS.REAC_CTRL_PARSE_STK.
  apply (PK.rcpK_compose B lyc Sc W memc m1 mem2 m' S ((S - 128) / 32 * 32) o
           (PL.Wq o S (lib.Reusable.YG0f.frame_addr lyc 1 pos) (lib.Reusable.YG0f.flag_addr lyc 1 pos))
           B1 ltac:(unfold lib.Reusable.YG0d.ESTACK; lia) ltac:(lia) ltac:(lia) RA1 HKEPT MU').
  - intros b m i Hb Hi.
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & Hb4 & Hbc & _). lia.
  - intros cid pos' a Hin Hr.
    destruct (lib.Reusable.YCbq.frames_bounds rsegs B LAWS lyc Sc W memc mdc cid pos' HAR Hin) as (F1 & F2 & _).
    pose proof (lib.Reusable.YCbq.fs_frame_bytes_nonneg cid).
    unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in Hr. cbn [fst snd] in Hr.
    unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF in Hr.
    Z.div_mod_to_equations. lia.
  - intros a Hi. pose proof (CLS.cls_img_lt a Hi). lia.
  - intros a Ha Ho Hw.
    destruct (rcpB_wq_cases o S _ _ a Ho) as [Hw'|[Hf|[Hsh|[Hl|[Hne Hoa]]]]]; [lia | | | |].
    + (* a byte of the new frame *)
      split; [lia|]. split.
      { intros Hi. exact (proj1 (PWW.rcpW_apart_img B lyc S2 W mem2 md2 pos a HAR2 In1 Hi) Hf). }
      split.
      { intros b m i Hb Hi Ea. exfalso. rewrite Ea in Hf.
        exact (proj1 (PWW.rcpW_apart_block B LAWS lyc S2 W mem2 md2 pos b m (b + i) HAR2 In1 (InB2 _ _ Hb)
                        ltac:(lia)) Hf). }
      { intros cid pos' Hin Hr. exfalso.
        exact (proj1 (PWW.rcpW_apart_frame B lyc S2 W mem2 md2 pos cid pos' a HAR2 In1 (InSc _ _ Hin)
                        (Ne1 _ _ Hin) (rcpB_fr_or _ _ _ _ Hr)) Hf). }
    + (* a shadow byte of the new frame *)
      split; [lia|]. split.
      { intros Hi. exact (proj2 (proj2 (PWW.rcpW_apart_img B lyc S2 W mem2 md2 pos a HAR2 In1 Hi)) Hsh). }
      split.
      { intros b m i Hb Hi Ea. exfalso. rewrite Ea in Hsh.
        exact (proj2 (proj2 (PWW.rcpW_apart_block B LAWS lyc S2 W mem2 md2 pos b m (b + i) HAR2 In1 (InB2 _ _ Hb)
                               ltac:(lia))) Hsh). }
      { intros cid pos' Hin Hr. exfalso.
        exact (proj2 (proj2 (PWW.rcpW_apart_frame B lyc S2 W mem2 md2 pos cid pos' a HAR2 In1 (InSc _ _ Hin)
                               (Ne1 _ _ Hin) (rcpB_fr_or _ _ _ _ Hr))) Hsh). }
    + (* the flag byte *)
      split; [lia|]. split.
      { intros Hi. exact (proj1 (proj2 (PWW.rcpW_apart_img B lyc S2 W mem2 md2 pos a HAR2 In1 Hi)) Hl). }
      split.
      { intros b m i Hb Hi Ea. exfalso. rewrite Ea in Hl.
        exact (proj1 (proj2 (PWW.rcpW_apart_block B LAWS lyc S2 W mem2 md2 pos b m (b + i) HAR2 In1 (InB2 _ _ Hb)
                               ltac:(lia))) Hl). }
      { intros cid pos' Hin Hr. exfalso.
        exact (proj1 (proj2 (PWW.rcpW_apart_frame B lyc S2 W mem2 md2 pos cid pos' a HAR2 In1 (InSc _ _ Hin)
                               (Ne1 _ _ Hin) (rcpB_fr_or _ _ _ _ Hr))) Hl). }
    + (* a byte of the record at o *)
      destruct (Hof Hne) as ((co & po & Ino & _ & _ & Hf1 & Hf2) & _ & _).
      destruct (lib.Reusable.YCbq.frames_bounds rsegs B LAWS lyc Sc W memc mdc co po HAR Ino) as (F1 & F2 & _).
      destruct (PWW.rcpW_in_frame B LAWS lyc Sc W memc mdc co po o 36 HAR Ino ltac:(lia) Hf1 Hf2) as (_ & OH & _).
      split; [lia|]. split.
      { apply CLS.cls_hi_noimg. unfold lib.B.Prog.ImgBounds.IMG_HI in OH. lia. }
      split; [intros; exact Hoa | intros; exact Hoa].
  - apply (rcpB_pres_of_stk _ m' (S - 8800) S); [unfold lib.B.Prog.ImgBounds.IMG_HI; lia | exact ST' |].
    intros a Ha. exact (proj1 (Hpres2 a ltac:(lia))).
Qed.
End PB.
