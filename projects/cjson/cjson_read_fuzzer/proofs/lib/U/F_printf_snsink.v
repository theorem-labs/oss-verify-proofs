(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_memcpy F_fwritex F_pad F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require NumFacts_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Printf_model Printf_mlib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require NumFacts_iface.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Exit.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.
#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit.F_memset.U_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_memcpy.U_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad.U_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.NumFacts_iface.F_fmt_fp.U_fmt_fp_contract.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.


Lemma zb_length : forall l, length (zb l) = length l.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_length | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_length as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_length | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_length | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_length OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_app | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_app as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_app | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_app | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_app OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.

Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
  Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.Forall_disjoint_from | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.Forall_disjoint_from as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.Forall_disjoint_from | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.Forall_disjoint_from | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.Forall_disjoint_from OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.
Lemma C8_func : forall m a (v w : word), rw_cells usegs m a [C8 v] -> rw_cells usegs m a [C8 w] -> v = w.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.C8_func | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.C8_func as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.C8_func | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.C8_func | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.C8_func OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgU.U_img); typeclasses eauto) ]. Qed.

Section SnProofs.
  Variables (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (frest : list cell) (B TOP : Z).
  Let SINK := SINK_sn Fp fl0 j1 j2 lbfw frest B TOP.

  Lemma sn_sink_frame : sink_frame_stmt Fp B 80 SINK.
  Proof.
    unfold sink_frame_stmt. intros W m m' o (junk & WF & FR & FRL & LEN & SEPB & T1 & T2) MU WM D1 D2.
    exists junk. split; [|split; [|split; [exact FRL | split; [exact LEN | split; [exact SEPB | split; assumption]]]]].
    - destruct WF as (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb).
      pose proof (zb_length o) as LZ. unfold zlength, SN_CAP in LEN.
      split; [|split; [|repeat split; assumption]].
      + eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
        eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size FILE_cells csize Nat.add]; lia | cbn [cells_size FILE_cells csize Nat.add]; lia].
      + eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
        eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; rewrite LZ; lia | cbn [cells_size csize Nat.add]; lia].
    - eapply rw_cells_transport; [exact FR | exact MU | exact WM |].
      eapply Forall_disjoint_from; [exact D1 | lia | lia | lia].
  Qed.

  Lemma sn_sink_flags : sink_flags_stmt Fp SINK.
  Proof.
    unfold sink_flags_stmt. intros m o (junk & (FC & BUF & FL & _) & _).
    exists fl0. split; [|exact FL].
    apply (proj1 (rw_cells_app usegs m Fp [CB 1 [fl0]] _)) in FC. exact (proj1 FC).
  Qed.

  Lemma sn_topok : topok_stmt (TOPOK_sn TOP).
  Proof. unfold topok_stmt, TOPOK_sn. intros. lia. Qed.

  (* [comment removed for export] *)
  Lemma sn_out : out_stmt Fp B 80 SINK (TOPOK_sn TOP) OUT_sn.
  Proof.
    unfold out_stmt. intros until canary. intros HS SRC RNG LB Ha1 Ha2 ST LO GLO SPHI TQ SSP MI D1 D2 D3 D4 D5. rename st into o.
    destruct HS as (junk & WF & FR & FRL & LEN & SEPB & T1 & T2). unfold TOPOK_sn in TQ. unfold OUT_DEPTH, GLOBALS_TOP, SN_CAP in *.
    pose proof WF as WF'. destruct WF' as (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb).
    pose proof (zb_length o) as LZo. pose proof (zb_length bs) as LZb. rewrite LZo in *. unfold zlength in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size FILE_cells csize Nat.add] in FB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite LZb in SB.
    assert (EFp : bv_unsigned a2 = Fp) by (subst a2; apply unsigned_lit; lia).
    unfold OUT_sn. apply implM_get_l. unfold zlength, SN_CAP.
    destruct (Z.leb_spec0 (Z.of_nat (length o) + Z.of_nat (length bs)) 80) as [FIT|NOFIT]; [|apply implM_unr].
    apply implM_put.
    destruct (stk_split _ _ _ (bv_unsigned sp - 64) _ ST ltac:(lia)) as [ST1 ST2].
    eapply evt_mono.
    { eapply (fwritex_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fl0 j1 j2 lbfw B (zb o) junk (zb bs));
        rewrite ?EFp, ?LZo, ?LZb.
      - exact WF. - exact SRC. - subst a1. rewrite unsigned_lit by lia. reflexivity. - lia. - exact ST2. - exact MI.
      - lia. - lia. - lia. - lia. - lia. - lia. }
    cbv beta. intros ms' P. unfold fwritex_post in P. rewrite ?EFp, ?LZo, ?LZb in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & WF2 & SRC').
    unfold out_post, SR. eexists x5, x6, x7, _, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
    split; [reflexivity|].
    split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [exact WM|]. split; [exact MI'|].
    split. { eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; lia] | exact ST' | lia ]. }
    split. { exists (skipn (length bs) junk). split; [rewrite zb_app; exact WF2|].
             split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM | cbn [disjoint_from]; lia]. }
             split; [exact FRL|]. unfold zlength, SN_CAP. rewrite length_app, length_skipn. split; [lia|]. split; [lia|]. split; assumption. }
    split. { destruct SSP as [S1 S2]. unfold ssp_cells, got_ssp, ssp_guard in *. split.
             - eapply rw_cells_transport; [exact S1 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia].
             - eapply rw_cells_transport; [exact S2 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    exact SRC'.
  Qed.

  (* [comment removed for export] *)
  Lemma sn_fpcall : forall y w p fl t, fmt_fp_facts y fl p t ->
    fpcall_stmt Fp B 80 SINK (TOPOK_sn TOP) OUTFP_sn (y, w, p, fl, t).
  Proof.
    intros y w p fl t FACTS. unfold fpcall_stmt. intros until canary.
    intros HS Hy Ha0 Ha3 Ha4 Ha5 Ha6 Ha7 Hw Hp Hfl Ht Hta ST LO GLO SPHI TQ SSP MI FRM D1 D2. rename st into o.
    destruct HS as (junk & WF & FR & FRL & LEN & SEPB & T1 & T2). unfold TOPOK_sn in TQ. unfold FMT_FP_DEPTH, GLOBALS_TOP, SN_CAP in *.
    pose proof WF as WF'. destruct WF' as (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb).
    pose proof (zb_length o) as LZo. rewrite LZo in *. unfold zlength in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size FILE_cells csize Nat.add] in FB.
    assert (EFp : bv_unsigned a0 = Fp) by (subst a0; apply unsigned_lit; lia).
    unfold OUTFP_sn. apply implM_get_l.
    destruct (fmt_fp o y w p fl t) as [[o1 r]|] eqn:HM; [|apply implM_unr].
    unfold zlength, SN_CAP. destruct (Z.leb_spec0 (Z.of_nat (length o1)) 80) as [FIT|NOFIT]; [|apply implM_unr].
    apply implM_put_l. apply implM_ret.
    destruct (stk_split _ _ _ (bv_unsigned sp - 4640) _ ST ltac:(lia)) as [ST1 ST2].
    pose proof (zb_length o1) as LZ1.
    eapply evt_mono.
    { pose proof (fmt_fp_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fl0 j1 j2 lbfw B junk canary w p fl t o o1 r) as SP.
      cbv zeta in SP. rewrite <- Hy, EFp, ?LZ1, ?LZo in SP.
      apply SP; first [exact HM | exact FACTS | exact ST2 | exact MI | exact FRM | exact WF | exact SSP | assumption | unfold FMT_FP_DEPTH; lia]. }
    cbv beta. intros ms' P. unfold fmt_fp_post in P. rewrite ?EFp, ?LZo, ?LZ1 in P. unfold FMT_FP_DEPTH in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & ST' & WF2 & SSP' & FOK).
    (* [comment removed for export] *)
    assert (LEN' : Z.of_nat (length o1) + Z.of_nat (length (skipn (length o1 - length o) junk)) = 80).
    { destruct WF2 as (FC2 & _ & _ & _ & _ & Bhi2 & _). rewrite LZ1 in FC2, Bhi2.
      apply (proj1 (rw_cells_app usegs _ Fp [CB 1 [fl0]; CB 31 j1] _)) in FC2. destruct FC2 as [_ FC2].
      apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FC2. destruct FC2 as [FC2 _]. cbn [cells_size csize Nat.add app] in FC2.
      pose proof FC as FC1.
      apply (proj1 (rw_cells_app usegs _ Fp [CB 1 [fl0]; CB 31 j1] _)) in FC1. destruct FC1 as [_ FC1].
      apply (proj1 (rw_cells_app usegs _ _ [_] _)) in FC1. destruct FC1 as [FC1 _]. cbn [cells_size csize Nat.add app] in FC1.
      eapply rw_cells_transport in FC1; [ | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia ].
      pose proof (C8_func _ _ _ _ FC1 FC2) as E.
      apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia. }
    unfold fpcall_post, SR. exists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, Ft, fc', m'.
    split; [reflexivity|].
    split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact FOK|].
    split. { eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; lia] | exact ST' | lia ]. }
    split. { exists (skipn (length o1 - length o) junk). split; [exact WF2|].
             split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM | cbn [disjoint_from]; lia]. }
             split; [exact FRL|]. unfold zlength, SN_CAP. split; [exact LEN'|]. split; [lia|]. split; assumption. }
    exact SSP'.
  Qed.
End SnProofs.
