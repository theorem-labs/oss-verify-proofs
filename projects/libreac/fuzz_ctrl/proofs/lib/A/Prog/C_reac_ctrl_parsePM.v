(* lib/A/Prog/C_reac_ctrl_parsePM.v -- fuzz_ctrl image A (asan, libreac v1.9.0): the class-1 fake-stack event of the
   cgif-form glue pb_reac_ctrl_parse (lib/A/Prog/C_reac_ctrl_parseP.v).
     rcpPM_E1   the call of __asan_stack_malloc_1 (jal at 0x835e8, return 0x835ec), from the callee's first slot with
                the register file C_reac_ctrl_parseK.rcpK_regsE (reac_ctrl_parseF_bnd.BndFOn.PreCall's post): the
                core's class-1 rule A.Prog.YC85.aj_stack_malloc_atS, then at the return memory the new frame's flag
                byte (1) and its back pointer (the flag address, at frame_addr + 120) in ctrl's bytes_at form.
   Ported from a Theorem Labs lane's lib/B/Prog/C_reac_ctrl_parsePf.v @ 258208c7d59, image A addresses: B's rcpB_E1 -> rcpPM_E1.
   Changes from B: the request is YC85.aj_stack_malloc_atS (it gives S2 = set_fs f2 Sc and the journal), not
   C_reac_ctrl_parseE1.aj_stack_malloc_at_raw; the two frame facts come from AR at S2 (the journal's first conjunct:
   YG0s.frame_facts for the bounds, YG0n.am_flags with mem_pos (frames S2) 1 pos = true, as (1, pos) heads frames S2)
   and from the rule's rdword view fact (fs_frame_bytes 1 = 128), not from ProgWorldAstack.ctl_fs_of_astack; B's PC1
   is proved from TS (AF0m.ts_code: as_code B = Tfib_code); the continuation takes only the facts the glue reads.
   A lemmas cited: A.Prog.YC85.aj_stack_malloc_atS, A.ProgWorldAstack.pwfs_byte_of_view / pwfs_rdword_bytes /
   pwfs_F_range, A.Prog.CtrlImg.ctrl_segs_low, A.AF0m.ts_code, A.Prog.C_reac_ctrl_parseK.rcpK_regsE / rcpK_u64; core:
   Reusable.YG0q.AR_laws_ok, YG0s.frame_facts, YG0n.am_flags, YA0n.SRr_bind.
   Twin rule: every project module is Required without Import and named through a full-path Module alias.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem PropExec MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Img0 AF0m ProgWorldAstack.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_stack_malloc_c CtrlImg YC85 C_reac_ctrl_parseK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK0s YA0n YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0f YG0n YG0d YG0s YG0q YCbq.
Import ListNotations.
Local Open Scope Z_scope.

Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module AI0 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Img0.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AF0m.
Module PWA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ProgWorldAstack.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.
Module CI := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.CtrlImg.
Module YC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.YC85.
Module K := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.C_reac_ctrl_parseK.
Module RK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module RK0s := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK0s.
Module RA0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YA0n.
Module RM05 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.
Module RI16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16.
Module RG00 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG00.
Module RG01 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG01.
Module RG0f := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0f.
Module RG0n := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0n.
Module RG0d := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0d.
Module RG0s := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0s.
Module RG0q := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YG0q.
Module RCbq := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YCbq.
Local Notation rsegs := AI0.rsegs (only parsing).

Section PM.
Context {fx : RK11.FPState} {rc : RM05.RunCeil} {SK : RI16.sink_head}.
Variable B : RG0f.asyms.
(* The open premises of the core, carried by every ctrl glue (B's Section Pf: errno_low, ML, SMP, ASM1).  B's
   LAWS and segs_low are proved on image A (YG0q.AR_laws_ok, CtrlImg.ctrl_segs_low); B's PC1 follows from TS. *)
Hypothesis errno_low : RCbq.api_env rsegs B.
Hypothesis ML : RG0d.model_laws (RG0f.as_universe B).
Hypothesis SMP : RCbq.stack_malloc_progressP B.
Hypothesis ASM1 : RG0d.astack_malloc_realizes rsegs B 1.
Hypothesis TS : AF.CtrlTSyms B.

(* ---- E1: the class-1 request at the state the pre-call stretch ends in (sp = A = (S - 128) / 32 * 32, ra = 0x835ec).
   The continuation receives the journal with (1, pos) owned, the call's acall_kept over its window [A - ESTACK, A),
   S2 = set_fs f2 Sc, and the new frame's flag byte and back pointer at the return memory mem2. ---- *)
Lemma rcpPM_E1 :
  forall STK sp0 FP ly S0 (W0 : RA0n.world rsegs) mem0 md0 own lyc Sc (W : RA0n.world rsegs)
    (m1 : word -> option byte) mdc1 k (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s7 s8 s10 s11 t3 t4 t5 t6 : word)
    (f n o S : Z) (Q : RA0n.world rsegs -> config -> Prop),
  RCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc1 k ->
  sp0 - STK <= S - 8800 -> S <= sp0 -> 8800 <= S < 2^64 -> S mod 16 = 0 ->
  gp = RG0d.w64 (RG0f.as_gp B) -> tp = RG0d.w64 (RG0f.as_tp B) ->
  RG01.count_cid 1 (RG01.frames Sc) < RG00.fs_frames 1 ->
  (forall S2 regs2 mem2 md2 pos f2,
     RCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem2 md2 k ->
     RG0d.aregs_preserved (K.rcpK_regsE gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s7 s8 s10 s11 t3 t4 t5 t6 f n o S) regs2 ->
     RK11.getr regs2 10 = Z_to_bv 64 (RG0f.frame_addr lyc 1 pos) ->
     RG0d.ablocks B lyc S2 = RG0d.ablocks B lyc Sc ->
     RG01.frames S2 = (1, pos) :: RG01.frames Sc -> ~ In (1, pos) (RG01.frames Sc) ->
     S2 = RG00.set_fs f2 Sc ->
     RCbq.acall_kept rsegs B lyc Sc W m1 W mem2 ((S - 128) / 32 * 32 - RG0d.ESTACK) ((S - 128) / 32 * 32) (fun _ => False) ->
     LM.bytes_at rsegs mem2 (RG0f.flag_addr lyc 1 pos) [Z_to_bv 8 1] ->
     LM.bytes_at rsegs mem2 (RG0f.frame_addr lyc 1 pos + 120) (LM.le8 (Z_to_bv 64 (RG0f.flag_addr lyc 1 pos))) ->
     RA0n.SRr rsegs W (mkCfg (RK11.mkst regs2 (Z_to_bv 64 0x835ec) mem2 (RK11.seg_rom rsegs)) md2) Q) ->
  RA0n.SRr rsegs W (mkCfg (LMS.MS (K.rcpK_regsE gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s7 s8 s10 s11 t3 t4 t5 t6 f n o S)
                             RK11.fp_regs (Z_to_bv 64 SMC.ASAN_STACK_MALLOC_1) RK11.fp_csr None m1 (LP.seg_rom rsegs)) mdc1) Q.
Proof using errno_low ML SMP ASM1 TS.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc1 k gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s7 s8 s10 s11
    t3 t4 t5 t6 f n o S Q HJ Hlo Hhi RS S16 Egp Etp Hcnt K.
  (* B's PC1: the class-1 entry of image A's code table *)
  assert (PC1 : RG0f.pc_stack_malloc (RG0f.as_code B) 1 = SMC.ASAN_STACK_MALLOC_1)
    by (rewrite (AF.ts_code B TS); vm_compute; reflexivity).
  set (regsT := K.rcpK_regsE gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s7 s8 s10 s11 t3 t4 t5 t6 f n o S).
  set (A := (S - 128) / 32 * 32).
  assert (HA : A mod 32 = 0 /\ S - 160 < A <= S - 128) by (unfold A; Z.div_mod_to_equations; lia).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (H16 & _) & _).
  assert (Hsp : RG0d.spZ regsT = sp0 + (A - sp0)).
  { unfold RG0d.spZ. change (RK11.getr regsT 2) with (Z_to_bv 64 A). rewrite K.rcpK_u64 by lia. lia. }
  assert (Hal : (A - sp0) mod 16 = 0) by (Z.div_mod_to_equations; lia).
  assert (Hraw : RK0s.ret_ok (Z_to_bv 64 0x835ec)) by (unfold RK0s.ret_ok; vm_compute; reflexivity).
  rewrite <- PC1.
  eapply RA0n.SRr_bind.
  - exact (YC.aj_stack_malloc_atS rsegs B (RG0q.AR_laws_ok rsegs B) CI.ctrl_segs_low errno_low ML SMP 1 ASM1
             ltac:(lia) W regsT m1 STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc mdc1 k (A - sp0) (Z_to_bv 64 0x835ec)
             HJ Hsp Hal ltac:(lia) ltac:(unfold RG0d.ESTACK; lia) ltac:(rewrite <- Egp; reflexivity)
             ltac:(rewrite <- Etp; reflexivity) eq_refl Hraw Hcnt).
  - intros W2 c2 _ (EW & S2 & regs2 & mem2 & md2 & pos & Ec & HJ2 & HP & H10 & HAB & HFR & HNI & _ & _ & _ & HRD &
      HKEPT & _ & (f2 & ES2)).
    subst W2 c2.
    replace (sp0 + (A - sp0)) with A in HKEPT by lia.
    (* the new frame's bounds, from AR at S2 (the journal's first conjunct) *)
    assert (Hin : In (1, pos) (RG01.frames S2)) by (rewrite HFR; left; reflexivity).
    pose proof HJ2 as ((M2 & _) & _).
    destruct (RG0s.frame_facts B lyc S2 _ 1 pos M2 Hin) as (_ & Hpos & HFapp & _ & _ & Hfo1 & Hfo2 & _ & _ & _ & Hflb).
    destruct (PWA.pwfs_F_range lyc HFapp) as [HF0 HF1].
    assert (EB : RG00.fs_frame_bytes 1 = 128) by reflexivity.
    assert (Efa : RG0f.frame_addr lyc 1 pos = RG0f.ly_F lyc + RG0f.fs_frame_off 1 pos) by reflexivity.
    assert (Efl : RG0f.flag_addr lyc 1 pos = RG0f.ly_F lyc + RG0f.fs_flag_off 1 pos) by reflexivity.
    rewrite EB in Hfo2, HRD. replace (2 ^ 20) with 1048576 in Hfo1 by reflexivity.
    unfold RG0f.kFakeStackSize, RG0f.kFakeFlagsOff, RG0f.kFakeFramesOff in HF1, Hfo1, Hfo2, Hflb.
    (* the flag byte reads 1: fs_flags_ok at S2, where (1, pos) is live *)
    assert (Hfl : RG0n.aview rsegs (RA0n.w_H W) mem2 (RG0f.flag_addr lyc 1 pos) = Some 1).
    { pose proof (RG0n.am_flags _ _ _ _ M2 1 pos ltac:(lia) Hpos) as Hf.
      rewrite HFR in Hf. cbn [RG00.mem_pos] in Hf. rewrite !Z.eqb_refl in Hf. exact Hf. }
    assert (CFL : LM.bytes_at rsegs mem2 (RG0f.flag_addr lyc 1 pos) [Z_to_bv 8 1]).
    { apply (PWA.pwfs_byte_of_view W mem2 _ 1 Hfl); [rewrite Efl; lia | lia]. }
    (* the back pointer: the rule's rdword of the view at frame_addr + 128 - 8 *)
    assert (C120 : LM.bytes_at rsegs mem2 (RG0f.frame_addr lyc 1 pos + 120)
                     (LM.le8 (Z_to_bv 64 (RG0f.flag_addr lyc 1 pos)))).
    { replace (RG0f.frame_addr lyc 1 pos + 120) with (RG0f.frame_addr lyc 1 pos + 128 - 8) by lia.
      apply (PWA.pwfs_rdword_bytes W mem2 _ _ HRD); rewrite Efa; lia. }
    exact (K S2 regs2 mem2 md2 pos f2 HJ2 HP H10 HAB HFR HNI ES2 HKEPT CFL C120).
Qed.

End PM.
