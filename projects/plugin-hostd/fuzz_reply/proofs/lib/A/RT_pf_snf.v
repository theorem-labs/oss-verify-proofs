(* ___interceptor_snprintf at fuzz_reply.asan: RT_pf_stmt.v snprintf_icpt_stmt, at __wrap_snprintf 0x421dc, assembled
   from pieces that are already proved - no function is walked here:
   - R4Printf's RELOCATED Bz walk (a working branch 5247aa4d0b9, lib/A/Bz/K/I_snprintfw.v): snprintf_walkA (the
     trampoline, the frame of 96, the va_start spill of a3..a7 at [q-40, q), TryAsanInitFromRtl, to the call of
     ___interceptor_vsnprintf 0x464e0 with va_list = q-40) and snprintf_walkB (the epilogue);
   - the vsnprintf interceptor's own statement entered at its body 0x464e0, taken as the Section hypothesis VSNI
     (RT_pf_vsn.v and RT_pf_vsn_body.v prove it);
   - the va_start spill seam: the statement's premise snf_spill_ok xs (discharged for every xs by RT_pf_stmt.v
     snf_spill_ok_all) turns the five spilled cells and the caller's stack words into the va_list area.

   TWO TREES, ONE INSTANCE.  Both statements here are at RT_IImgA.v's A_img, so no fact crosses to A_img_vsn.  What
   does cross is the TREE: the walks speak lib/A/Bz/Lib, the statements lib/CJ/Lib, whose `cell` (and `msteps`) are
   distinct inductives (RT_pf_kit.v).  So every CJ cell fact (the destination, the stack-protector cells) is carried
   with CJ's Frame lemmas over a munch cast from the walk's, every Bz cell fact (the frame, the spill, the runtime
   cells) with Bz's; the one place a concrete cell list has to cross, the five spilled words handed to
   snf_spill_ok, is spill_cells_bz_cj below, by unfolding both sides to their bytes.

   lia hygiene (measured on RT_pf_vsn.v): the destination's two separation premises are disjunctions and the two
   Z.min equations split too, so all four are hidden right after the facts this proof needs from them are derived. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.K Require Import I_snprintfw.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RT_pf_Tbl.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_m2s.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Cells.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.MState.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Spec.Prelim.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RStep.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.G_pad.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.G_fmt_fp_lib.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_printf_core_common.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_vfprintf_snf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.VfprintfCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_vsnprintf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_IImgA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_bz.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_stmt.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module BzE := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Exec.
Module BzM2 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_m2s.
Module CJC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Cells.
Module CJS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.
Module CJF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.
Module CJMS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.MState.
Module SPL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Spec.Prelim.
Module CJR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RStep.
Module GP := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.G_pad.
Module GFL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.G.G_fmt_fp_lib.
Module GVF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GX.G_vfprintf_snf.
Module VFC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.VfprintfCall.
Module GVS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.G_vsnprintf.
Module RTA := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_IImgA.
Module GC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls.
Module PB := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_bz.
Module PS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_stmt.
Module PK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_pf_kit.

(* the five spilled words, from the Bz walk's cells to the CJ cells snf_spill_ok takes: a CONCRETE cell list, so
   both sides unfold to the same bytes and the same write range (no generic rw_cells cast exists, RT_pf_kit.v) *)
Lemma spill_cells_bz_cj : forall m VA (a3 a4 a5 a6 a7 : word),
  rw_cells asegs m VA [C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
  CJS.rw_cells (@CJR.img_segs RTA.A_img) m VA [CJC.C8 a3; CJC.C8 a4; CJC.C8 a5; CJC.C8 a6; CJC.C8 a7].
Proof.
  intros m VA a3 a4 a5 a6 a7 [[_ B] W].
  split; [split; [cbn; tauto | exact B] | exact W].
Qed.

Section Snf.
Variable set_ready : (word -> option byte) -> Z -> Z -> Z -> Prop.
Variable vf_ready : VFC.vf_guard.
Hypothesis VSNI : PS.vsnprintf_icpt_stmt set_ready vf_ready PF_ICPT_VSNPRINTF.

Theorem snprintf_icpt_ok : PS.snprintf_icpt_stmt set_ready vf_ready.
Proof.
  unfold PS.snprintf_icpt_stmt. intros until o. cbv zeta.
  intros -> -> -> DST HDN BY HF P1 XS XHI SPILL AOK MODEL R0 R31 Hn ST LO GLO LOLO QHI Q16 SSP MI FRM HA HA0
    D0 DHI DMH DD1 DD2 CELLS PCOM READY.
  set (q := bv_unsigned sp) in *.
  (* the numbers the arithmetic needs, once, without touching the premises VSNI takes verbatim *)
  pose proof LO as LOn. unfold PS.SNI_DEPTH, PF_SNF_FRAME, PF_VSN_FRAME, GVS.VSN_DEPTH in LOn.
  pose proof GLO as GLOn. rewrite PK.globals_top_val in GLOn. unfold PF_GLOBALS_TOP in GLOn.
  pose proof HA as HAn. rewrite PK.globals_top_val in HAn. unfold PF_GLOBALS_TOP, SPL.zlength in HAn.
  (* the destination's separation: once for D-cells carried over a stack window [x, y), once for stack cells
     [a, a + k) carried over a window holding [D, D + dn); then the disjunctions leave lia's view *)
  assert (DSEPa : forall x y, lo <= x -> y <= q -> D + Z.of_nat dn <= x \/ y <= D).
  { intros x y Hx Hy. destruct DD1 as [E|E]; [left; lia | right; unfold SPL.zlength in E; lia]. }
  assert (DSEPb : forall a k, lo <= a -> a + k <= q -> a + k <= D \/ D + Z.of_nat dn <= a).
  { intros a k Ha Hk. destruct DD1 as [E|E]; [right; lia | left; unfold SPL.zlength in E; lia]. }
  PK.hide DD1. PK.hide DD2. PK.hide HDN. PK.hide DMH.
  assert (EUq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (EU96 : bv_unsigned (Z_to_bv 64 (q + -96)) = q - PF_SNF_FRAME)
    by (rewrite unsigned_lit by lia; unfold PF_SNF_FRAME; lia).
  assert (ESP : sp = Z_to_bv 64 q) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (ERET : CJMS.ret_pc (Z_to_bv 64 PF_RA_SNF_VSN) = Z_to_bv 64 PF_RA_SNF_VSN)
    by (apply CJMS.ret_pc_even; unfold PF_RA_SNF_VSN; [lia | reflexivity]).
  pose proof CELLS as (AI & _ & _ & _).
  pose proof (GC.mem_inv_cj_bz m MI) as MIb.
  pose proof (PK.stk_cj_bz _ _ _ ST) as STb.
  rewrite ESP. unfold PF_WRAP_SNPRINTF.
  apply GC.bz_cj_evt.
  (* --- the frame, the spill, TryAsanInitFromRtl, to the call of ___interceptor_vsnprintf --- *)
  eapply BzE.evt_cut.
  { exact (snprintf_walkA q lo ra gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 A)
             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             STb ltac:(lia) GLOn QHI AI MIb). }
  intros ms1 H1. unfold snw_call in H1.
  destruct H1 as (m1 & u0 & u1 & u2 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & j0 & j1 & -> & MU1 & WM1 & MI1b
                  & ST1b & FRp1 & FRva1).
  pose proof (PK.munch_bz_cj _ _ _ MU1) as MU1c.
  pose proof (PK.wmono_bz_cj _ _ WM1) as WM1c.
  pose proof (GC.mem_inv_bz_cj m1 MI1b) as MI1.
  assert (MUw : CJF.munch [(lo, q); (D, D + Z.of_nat dn)] m m1).
  { apply PK.munch_bz_cj. eapply munch_weaken; [| exact MU1].
    unfold sub_fp. cbn [outside]. intros x (Hx & _). split; [lia | exact I]. }
  (* --- the vsnprintf interceptor, at its body: one directed proof per premise, in the statement's order --- *)
  eapply BzE.evt_cut.
  { apply PK.cj_bz_evt.
    apply (VSNI (Z_to_bv 64 PF_RA_SNF_VSN) (Z_to_bv 64 (q + -96)) gp tp u0 u1 u2 (Z_to_bv 64 A) (Z_to_bv 64 n)
             (Z_to_bv 64 D) (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 (q + -40)) e4 e5 e6 e7
             (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
             F fc m1 D n A (q - PF_SPILL) dn junkd fmt ([a3; a4; a5; a6; a7] ++ xs) args lo canary r o).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - apply f_equal. unfold PF_SPILL. lia.
    - eapply CJF.rw_cells_transport; [exact DST | exact MU1c | exact WM1c |].
      cbn [CJF.disjoint_from CJC.cells_size CJC.csize]. split; [| exact I].
      destruct (DSEPa (q - 112) q ltac:(lia) ltac:(lia)) as [E|E]; [left | right]; lia.
    - exact HDN.
    - eapply CJF.bytes_at_transport; [exact BY | exact MU1c |].
      cbn [CJF.disjoint_from]. unfold GFL.zb. rewrite length_map. split; [left; lia | exact I].
    - exact HF.
    - exact P1.
    - apply (SPILL m1 (q - PF_SPILL) a3 a4 a5 a6 a7).
      + replace (q - PF_SPILL) with (q + -40) by (unfold PF_SPILL; lia).
        exact (spill_cells_bz_cj m1 (q + -40) a3 a4 a5 a6 a7 FRva1).
      + replace (q - PF_SPILL + PF_SPILL) with q by lia.
        eapply CJF.bytes_at_transport; [exact XS | exact MU1c |].
        cbn [CJF.disjoint_from]. split; [right; lia | exact I].
    - rewrite EU96.
      eapply GVF.args_ok_rebase; [exact AOK | | | right; reflexivity | right; split; reflexivity
                                 | right; split; reflexivity | right; reflexivity].
      + apply PK.munch_bz_cj. eapply munch_weaken; [| exact MU1].
        unfold sub_fp. cbn [outside]. intros x (Hx & _). split; [lia | exact I].
      + unfold PF_SNF_FRAME. lia.
    - exact MODEL.
    - exact R0.
    - exact R31.
    - exact Hn.
    - rewrite EU96. exact (PK.stk_bz_cj _ _ _ ST1b).
    - rewrite EU96. unfold PS.VSNI_DEPTH, PF_SNF_FRAME, PF_VSN_FRAME, GVS.VSN_DEPTH. lia.
    - exact GLO.
    - exact LOLO.
    - rewrite EU96. unfold PF_SNF_FRAME. lia.
    - rewrite EU96. unfold PF_SNF_FRAME.
      replace (q - 96) with (q + (-6) * 16) by lia. rewrite Z_mod_plus_full. exact Q16.
    - destruct SSP as [S1 S2]. split.
      + eapply CJF.rw_cells_transport; [exact S1 | exact MU1c | exact WM1c |].
        cbn [CJF.disjoint_from CJC.cells_size CJC.csize]. rewrite PK.got_ssp_val. unfold PF_GOT_SSP.
        split; [left; lia | exact I].
      + eapply CJF.rw_cells_transport; [exact S2 | exact MU1c | exact WM1c |].
        cbn [CJF.disjoint_from CJC.cells_size CJC.csize]. rewrite PK.ssp_guard_val. unfold PF_SSP_GUARD.
        split; [left; lia | exact I].
    - exact MI1.
    - exact FRM.
    - exact HA.
    - exact HA0.
    - rewrite EU96. unfold PF_SNF_FRAME, PF_SPILL. lia.
    - unfold SPL.zlength in XHI |- *. rewrite length_app. cbn [length]. unfold PF_SPILL. lia.
    - exact D0.
    - exact DHI.
    - exact DMH.
    - destruct DD1 as [E|E]; [left; exact E | right].
      unfold SPL.zlength in E |- *. rewrite length_app. cbn [length]. unfold PF_SPILL. lia.
    - exact DD2.
    - destruct CELLS as (AI1 & GCF & CPF & RVS).
      split; [| split; [| split]].
      + eapply rw_cells_transport; [exact AI1 | exact MU1 | exact WM1 |].
        cbn [disjoint_from cells_size csize]. unfold PF_ASAN_INITED. split; [left; lia | exact I].
      + eapply ro_cells_transport; [exact GCF | exact MU1 |].
        cbn [disjoint_from cells_size csize]. unfold PF_GOT_COMMON_FLAGS. split; [left; lia | exact I].
      + eapply ro_cells_transport; [exact CPF | exact MU1 |].
        cbn [disjoint_from cells_size csize]. unfold PF_CHECK_PRINTF. split; [left; lia | exact I].
      + eapply ro_cells_transport; [exact RVS | exact MU1 |].
        cbn [disjoint_from cells_size csize]. unfold PF_REAL_VSNPRINTF. split; [left; lia | exact I].
    - rewrite EU96. intros m' MU' WM' MI' VA'.
      apply (PCOM m').
      + apply (CJF.munch_trans _ m m1 m').
        * apply PK.munch_bz_cj. eapply munch_weaken; [| exact MU1].
          unfold sub_fp. cbn [outside]. intros x (Hx & _).
          unfold PF_SNF_FRAME, PF_VSN_FRAME, PF_TRYINIT in Hx. split; [lia | exact I].
        * eapply CJF.munch_weaken; [| exact MU'].
          unfold CJF.sub_fp. cbn [CJF.outside]. intros x (Hx & _).
          unfold PF_SNF_FRAME, PF_VSN_FRAME, PF_TRYINIT in Hx |- *. split; [lia | exact I].
      + exact (CJF.wmono_trans _ m m1 m' WM1c WM').
      + exact MI'.
      + exact VA'.
    - rewrite EU96. intros m' MU' WM'.
      apply (READY m').
      + apply (CJF.munch_trans _ m m1 m'); [exact MUw |].
        eapply CJF.munch_weaken; [| exact MU'].
        unfold CJF.sub_fp. cbn [CJF.outside]. intros x (Hx & Hy & _).
        split; [unfold PF_SNF_FRAME; lia | split; [exact Hy | exact I]].
      + exact (CJF.wmono_trans _ m m1 m' WM1c WM').
    - rewrite ERET. unfold PF_RA_SNF_VSN, PF_WRAP_VSNPRINTF. intros E.
      apply (f_equal (@bv_unsigned 64)) in E. rewrite !unsigned_lit in E by lia. lia. }
  cbv beta. intros ms2 H2. unfold GVS.vsnprintf_x_post in H2. rewrite !EU96 in H2.
  destruct H2 as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & Ft & fc' & m2
                  & -> & MU2 & WM2 & MI2 & FRM' & FOK & ST2 & SSP2 & DST2).
  rewrite ERET.
  pose proof (PK.munch_cj_bz _ _ _ MU2) as MU2b.
  pose proof (PK.wmono_cj_bz _ _ WM2) as WM2b.
  (* the interceptor's own frame and spill, past the vsnprintf call: Bz cells, carried with Bz's lemma *)
  assert (FRp2 : rw_cells asegs m2 (q + -96) (snfr q j0 j1 ra s0 s1 s2)).
  { eapply rw_cells_transport; [exact FRp1 | exact MU2b | exact WM2b |].
    unfold snfr. cbn [disjoint_from cells_size csize].
    split; [right; unfold PF_SNF_FRAME; lia | split; [| exact I]].
    destruct (DSEPb (q + -96) 56 ltac:(lia) ltac:(lia)) as [E|E]; [left | right]; lia. }
  assert (FRva2 : rw_cells asegs m2 (q + -40) [C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]).
  { eapply rw_cells_transport; [exact FRva1 | exact MU2b | exact WM2b |].
    cbn [disjoint_from cells_size csize].
    split; [right; unfold PF_SNF_FRAME; lia | split; [| exact I]].
    destruct (DSEPb (q + -40) 40 ltac:(lia) ltac:(lia)) as [E|E]; [left | right]; lia. }
  (* --- the epilogue --- *)
  eapply BzE.evt_cut.
  { exact (snprintf_walkB q lo j0 j1 ra s0 s1 s2 a3 a4 a5 a6 a7
             (Z_to_bv 64 PF_RA_SNF_VSN) gp tp v0 v1 v2 (Z_to_bv 64 A) (Z_to_bv 64 n) (Z_to_bv 64 r)
             c1 c2 c3 c4 c5 c6 c7 (Z_to_bv 64 D) s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 Ft fc' m2
             (PK.stk_cj_bz _ _ _ ST2) ltac:(lia) QHI FRp2 FRva2 (GC.mem_inv_cj_bz m2 MI2)). }
  cbv beta. intros ms3 H3.
  destruct H3 as ((w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & ->) & ST3).
  apply BzE.evt_done.
  unfold GVS.vsnprintf_x_post.
  exists w0, w1, w2, d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, Ft, fc', m2.
  rewrite EUq.
  split; [reflexivity|].
  split.
  { apply (CJF.munch_trans _ m m1 m2); [exact MUw |].
    eapply CJF.munch_weaken; [| exact MU2].
    unfold CJF.sub_fp. cbn [CJF.outside]. intros x (Hx & Hy & _).
    split; [unfold PF_SNF_FRAME; lia | split; [exact Hy | exact I]]. }
  split; [exact (CJF.wmono_trans _ m m1 m2 WM1c WM2)|].
  split; [exact MI2|].
  split; [exact FRM'|].
  split; [exact FOK|].
  split; [exact (PK.stk_bz_cj _ _ _ ST3)|].
  split; [exact SSP2 | exact DST2].
Qed.

End Snf.
