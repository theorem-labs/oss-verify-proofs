(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_fmt_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_mlib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I Require IImgP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_snsink.
Module F_printf_snsink.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset.P_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad.P_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad.P_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp.P_fmt_fp_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.


Lemma zb_length : forall l, length (zb l) = length l.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_length | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_length as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_length | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_length | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_length OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img); typeclasses eauto) ]. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_app | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_app as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_app | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_app | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.zb_app OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img); typeclasses eauto) ]. Qed.

Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
  Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.Forall_disjoint_from | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.Forall_disjoint_from as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.Forall_disjoint_from | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.Forall_disjoint_from | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.Forall_disjoint_from OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img); typeclasses eauto) ]. Qed.
Lemma C8_func : forall m a (v w : word), rw_cells psegs m a [C8 v] -> rw_cells psegs m a [C8 w] -> v = w.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.C8_func | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.C8_func as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.C8_func | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.C8_func | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_snsink.C8_func OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img); typeclasses eauto) ]. Qed.

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
    apply (proj1 (rw_cells_app psegs m Fp [CB 1 [fl0]] _)) in FC. exact (proj1 FC).
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
      apply (proj1 (rw_cells_app psegs _ Fp [CB 1 [fl0]; CB 31 j1] _)) in FC2. destruct FC2 as [_ FC2].
      apply (proj1 (rw_cells_app psegs _ _ [_] _)) in FC2. destruct FC2 as [FC2 _]. cbn [cells_size csize Nat.add app] in FC2.
      pose proof FC as FC1.
      apply (proj1 (rw_cells_app psegs _ Fp [CB 1 [fl0]; CB 31 j1] _)) in FC1. destruct FC1 as [_ FC1].
      apply (proj1 (rw_cells_app psegs _ _ [_] _)) in FC1. destruct FC1 as [FC1 _]. cbn [cells_size csize Nat.add app] in FC1.
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
End F_printf_snsink.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_strnlen.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_pop_arg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_zfacts.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_printf_core.
Module F_printf_core_width.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_printf_core_conv.F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset.P_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.P_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad.P_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad.P_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp.P_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.P_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
End F_printf_core_width.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_end.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_exit1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_scan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_flags.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_prec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_state.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_dir.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_t6.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_t5.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_t4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_t3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_t2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_t1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_tail.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_intc2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_intc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_dloop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_fmtu2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_fmtu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_cvd.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_cvu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_xloop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_cvx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_cvs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_cvfp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_head.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_p1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_printf_core_pro.
Module F_printf_core.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_zfacts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_printf_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.

Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_printf_core_conv.F_printf_core_common.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".


#[local] Existing Instances OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset.P_memset_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy.P_memcpy_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.F_memchr.P_memchr_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_strnlen.P_strnlen_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad.P_pad_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad.P_pad_call_c OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp.P_fmt_fp_contract OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg.P_pop_arg_contract.

#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_contract) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fwritex.fwritex_spec : typeclass_instances.
#[local] Hint Extern 0 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fwritex.fwritex_call_c) => exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fwritex.fwritex_call : typeclass_instances.
(* [comment removed for export] *)
#[local] Existing Instance OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAtT _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.CodeAt _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RoB _ _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelCode _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelSym _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 1 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.RelNear _ _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.
#[local] Hint Extern 2 (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RStep.ZFact _) => OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IInst.inst : typeclass_instances.



(* [comment removed for export] *)
Theorem printf_core_proof : forall (St : Type) (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
    (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z),
  sink_frame_stmt Fp B BS SINK -> sink_flags_stmt Fp SINK -> topok_stmt TOPOK -> out_stmt Fp B BS SINK TOPOK OUT ->
  printf_core_stmt Fp B BS SINK TOPOK OUT OUTFP.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core_proof | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core_proof as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core_proof | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core_proof | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core_proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img); typeclasses eauto) ]. Qed.

Theorem printf_core1_proof : printf_core1_stmt.
Proof. first [ exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core1_proof | (pose proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core1_proof as T_; exact T_) | exact @OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core1_proof | apply OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core1_proof | (apply (@OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core1_proof OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.I.IImgP.P_img); typeclasses eauto) ]. Qed.
#[export] Instance P_printf_core_proof_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core_proof_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core_proof_c_ok.
#[export] Instance P_printf_core1_proof_c : OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core1_proof_c := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_printf_core.printf_core1_proof_c_ok.
End F_printf_core.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_sn_write.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From Stdlib Require Zify.
Module F_vfprintf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_printf_iface F_printf_core.
Import F_printf_snsink OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_sn_write.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac lia ::= lia3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)

Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)
Notation z64 := (Z_to_bv 64 0) (only parsing).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gfile_cells (flags : word) (rpos rend close wend wpos wbase writefn seekfn buf bufsize fd : Z) (mode lock : word) (lbf : Z) : list cell :=
  [C4 flags; C4 z64; C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend); C8 (Z_to_bv 64 close);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 z64;
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 seekfn); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 z64; C8 z64; C4 (Z_to_bv 64 fd); C4 z64; C8 z64; C4 mode; C4 lock; C4 (Z_to_bv 64 lbf)].

Lemma file_cells_g : forall flags wend wpos wbase writefn buf bufsize fd mode lbf tail,
  file_cells flags wend wpos wbase writefn buf bufsize fd mode lbf tail
  = gfile_cells flags 0 0 0x17a44 wend wpos wbase writefn 0x17c00 buf bufsize fd mode (Z_to_bv 64 0xffffffff) lbf ++ [C4 z64; CB 80 tail].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition towrite_g_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (flags mode lock : word) (rpos rend close wend wpos wbase writefn seekfn buf bufsize fd lbf : Z),
    rw_cells psegs m (bv_unsigned a0) (gfile_cells flags rpos rend close wend wpos wbase writefn seekfn buf bufsize fd mode lock lbf) ->
    Z.land (bv_unsigned flags) 8 = 0 ->
    (0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
    mem_inv psegs m ->
    evt psegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom psegs)
                 /\ munch [(bv_unsigned a0, bv_unsigned a0 + 148)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
                 /\ rw_cells psegs m' (bv_unsigned a0) (gfile_cells flags 0 0 close (buf + bufsize) buf buf writefn seekfn buf bufsize fd mode' lock lbf))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x17744) fc None m (seg_rom psegs)).

Theorem towrite_g_proof : towrite_g_stmt.
Proof.
  unfold towrite_g_stmt. intros until lbf. intros FC NOWR B0 BHI BS0 MI.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size gfile_cells csize Nat.add] in FB.
  set (Fp := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(Fp, Fp + 148)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold gfile_cells in FC.
  assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
  { unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
    rewrite <- Z.land_ones by lia.
    rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
  do 5 zs. rewrite FL8. zs. zs. if_lit.
  do 10 zs.
  apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  unfold gfile_cells. match goal with H : rw_cells _ _ Fp _ |- _ => exact H end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem towrite_proof : towrite_stmt.
Proof.
  unfold towrite_stmt. intros until tail. intros FC NOWR B0 BHI BS0 MI.
  pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size file_cells csize Nat.add] in FB.
  set (Fp := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold file_cells in FC.
  assert (FL8 : Z.land (bv_unsigned (zx32 flags)) 8 = 0%Z).
  { unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
    rewrite <- Z.land_ones by lia.
    rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8%Z. exact NOWR. }
  do 5 zs. rewrite FL8. zs. zs. if_lit.
  do 10 zs.
  apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  unfold file_cells. match goal with H : rw_cells _ _ Fp _ |- _ => first [exact H | let t := type of H in idtac "FC:" t; fail] end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma arg_ok_vf : forall Fp B BS m m' lo sp sp' ap w a,
  arg_ok Fp B BS m lo sp ap w a -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> arg_ok Fp B BS m' lo sp' ap w a.
Proof.
  intros Fp B BS m m' lo sp sp' ap w a H Hsp MU. destruct a as [s|i|u|d]; cbn in H |- *; try exact H.
  (nelim H 9%nat; intros slack BY HF PAD NZ D1 D2 D3 D4). exists slack.
  split; [|repeat (split; [first [assumption | lia]|]); exact D4].
  eapply bytes_at_transport; [exact BY | exact MU |].
  cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
Qed.
Lemma args_ok_vf : forall Fp B BS m m' lo sp sp' ap ws args,
  args_ok Fp B BS m lo sp ap ws args -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> args_ok Fp B BS m' lo sp' ap ws args.
Proof.
  intros Fp B BS m m' lo sp sp' ap ws args. revert ws. induction args as [|a args IH]; intros ws H Hsp MU; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_ok_vf; eassumption | apply IH; assumption].
Qed.

Lemma rw_cells_unmerge : forall m A pre mid post,
  rw_cells psegs m A (pre ++ CB (cells_size mid) (cells_bytes mid) :: post) -> cells_wf mid ->
  rw_cells psegs m A (pre ++ mid ++ post).
Proof.
  intros m A pre mid post [[Hwf Hb] Hw] WF.
  apply cells_wf_app in Hwf. (nelim Hwf 3%nat; intros H1 H2 H3).
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. apply cells_wf_app. split; [exact WF | exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb. rewrite ?app_assoc in Hb |- *. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw. rewrite ?Nat.add_assoc in Hw |- *. exact Hw.
Qed.

Lemma rwc_eq : forall m A A' cs, rw_cells psegs m A cs -> A = A' -> rw_cells psegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.
Ltac piece H := eapply rwc_eq; [exact H | cbn [cells_size csize Nat.add app]; lia].

Lemma rw_cells_CB0 : forall m B, 0 <= B -> B <= 2^64 -> rw_cells psegs m B [CB 0 []].
Proof.
  intros m B H0 H1. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes app]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition snfile_head (wend wpos wbase buf bufsize : Z) (mode : word) : list cell :=
  gfile_cells (Z_to_bv 64 0) 0 0 0 wend wpos wbase 0x1c804 0 buf bufsize 0 mode (Z_to_bv 64 0xffffffff) 0xffffffff.
Definition snfile_rest (CK : Z) : list cell :=
  [C4 z64; C8 (Z_to_bv 64 CK); C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64].

Definition VF_FRAME : Z := 368.

Definition vfprintf_sn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (Fp CK D n : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (fjunk : list byte) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ frm0 fc'
    /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells psegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)]
    /\ rw_cells psegs m' CK [C8 (Z_to_bv 64 (D + zlength o)); C8 (Z_to_bv 64 (n - zlength o))]
    /\ rw_cells psegs m' Fp [CB 232 fjunk].

Definition vfprintf_sn_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (Fp CK D n bufp A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells psegs m Fp (snfile_head 0 0 0 bufp 0 (Z_to_bv 64 0)) -> rw_cells psegs m (Fp + 148) (snfile_rest CK) ->
    rw_cells psegs m CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] ->
    rw_cells psegs m D [CB dn junkd] ->
    bytes_at psegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    va_area m VA slots -> args_ok Fp (q - 352) 80 m lo q (q - VF_FRAME) slots args ->
    printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, o)) ->
    Forall (fun c => let '(y, w, p, fl, t) := c in fmt_fp_facts y fl p t) (fp_calls (length fmt) fmt args) ->
    (length o < dn)%nat -> (zlength o <= n < 2^63) -> (0 < bufp < 2^64) ->
    stk psegs m lo q -> (lo <= q - VF_FRAME - PC_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv psegs m -> frm0 fc ->
    (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
    (q <= Fp) -> (Fp + 232 <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
    (q <= CK) -> (CK + 16 <= Fp \/ Fp + 232 <= CK) -> (CK + 16 < 2^64) ->
    (D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= Fp \/ Fp + 232 <= D) -> (D + Z.of_nat dn <= CK \/ CK + 16 <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    evt psegs (vfprintf_sn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D n dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x17ca8) fc None m (seg_rom psegs)).

Theorem vfprintf_sn_proof : vfprintf_sn_stmt.
Proof.
  unfold vfprintf_sn_stmt. intros until o. cbv zeta.
  intros -> -> -> FH FR CKC DST BY HF P1 VAA AOK MODEL FPF ROOM Hn Hbufp ST LO GLO QHI SSP MI FRM HA0 HA QF FVA VAHI QCK CKF CKHI DD1 DD2 DD3 GD.
  unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
  pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. idtac. fold psegs in SSP1, SSP2.
  pose proof (wmono_refl psegs m) as WM.
  unfold snfile_head, gfile_cells in FH. unfold snfile_rest in FR.
  carve_frame 368%nat ST.
  (* [comment removed for export] *)
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MUp.
  stash FH. stash FR. stash CKC. stash DST. stash BY. stash VAA.
  do 12 zs. do 14 zs.
  unstash.
  lazymatch type of MUp with munch ?Wp ?ma ?mb =>
    transport_after_call psegs ma mb MUp WM;
    assert (MU : munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)]%Z ma mb)
      by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; intros; slia | exact MUp]);
    assert (MU1 : munch [(lo, bv_unsigned sp); (Fp, Fp + 232)]%Z ma mb)
      by (apply (munch_weaken Wp); [unfold sub_fp; cbn [outside]; intros; slia | exact MUp])
  end.
  clear MUp.
  (* [comment removed for export] *)
  pose proof printf_core1_proof as PC1. unfold printf_core1_stmt in PC1.
  eapply evt_cut.
  { eapply PC1; rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength;
      [ exact BY | exact HF | exact P1 | reflexivity | exact ST | lia | lia | lia
      | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | lia | lia | lia ]. }
  cbv beta. intros ms' P. clear PC1. unfold printf_core1_post in P.
  (nelim P 21%nat; intros x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 m' -> MUc WMc MIc STc SSPc).
  rewrite !unsigned_lit in MUc, STc by lia.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call psegs mm m' MUc WMc; clear MUc WMc; try clear MI end.
  fix_ret.
  clear SSP1 SSP2. destruct SSPc as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. idtac. fold psegs in SSP1, SSP2.
  (* [comment removed for export] *)
  zs. if_lit. zs. zs. if_lit. zs. zs. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) in *. zs. zs. zs. zs. if_lit.
  do 10 zs.
  pose proof (rw_cells_bound _ _ _ _ FH) as FB. cbn [cells_size csize Nat.add] in FB.
  (* [comment removed for export] *)
  pose proof towrite_g_proof as TW. unfold towrite_g_stmt in TW.
  eapply evt_cut.
  { eapply (TW _ _ _ _ _ _ _ _ _ (Z_to_bv 64 Fp)) with (flags := Z_to_bv 64 0) (rpos := 0) (rend := 0) (close := 0) (wend := 0) (wpos := 0) (wbase := 0)
      (writefn := 116740) (seekfn := 0) (buf := bv_unsigned sp + -352) (bufsize := 80) (fd := 0) (mode := Z_to_bv 64 0) (lock := Z_to_bv 64 4294967295) (lbf := 4294967295);
      rewrite ?unsigned_lit by lia; [ unfold gfile_cells; exact FH | reflexivity | lia | lia | lia | assumption ]. }
  cbv beta. intros ms' P. clear TW.
  (nelim P 21%nat; intros x5' x6' x7' c1 c2 c3 c4 c5 c6 c7 x28' x29' x30' x31' mode' m'' -> MUc WMc MIt FH').
  rewrite !unsigned_lit in MUc, FH' by lia. clear FH.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call psegs mm m'' MUc WMc; clear MUc WMc; try clear MIc end.
  fix_ret.
  zs. if_lit. do 6 zs.
  (* [comment removed for export] *)
  set (B := bv_unsigned sp + -352) in *.
  unfold gfile_cells in FH'.
  apply (rw_cells_merge psegs _ _ [] [C4 (Z_to_bv 64 0); C4 z64; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in FH'.
  apply (rw_cells_split_CB psegs _ _ [] _ _ _ [1; 31]%nat) in FH'; [|reflexivity].
  apply (rw_cells_merge psegs _ _ [_; _; _; _]
           [C8 z64; C8 (Z_to_bv 64 B); C8 z64; C8 (Z_to_bv 64 116740); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 80);
            C8 z64; C8 z64; C4 (Z_to_bv 64 0); C4 z64; C8 z64; C4 mode'; C4 (Z_to_bv 64 4294967295)]) in FH'.
  cbn [app mk_CB_cells cells_size csize Nat.add] in FH'.
  match type of FH' with rw_cells _ _ _ (CB 1 ?b1 :: CB 31 ?b31 :: _ :: _ :: CB 96 ?b96 :: _) =>
    let v1 := eval vm_compute in b1 in change b1 with v1 in FH'; set (j1 := b31) in FH'; set (j2 := b96) in FH' end.
  (* [comment removed for export] *)
  match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z _ |- _ => rename H into FRv end.
  apply (rw_cells_split_CB psegs _ _ [_; _] 248 _ _ [80; 168]%nat) in FRv; [|reflexivity]. cbn [app mk_CB_cells] in FRv.
  apply (proj1 (rw_cells_app psegs _ _ [_] _)) in FRv. destruct FRv as [APC FRv]. cbn [cells_size csize Nat.add app] in FRv.
  apply (proj1 (rw_cells_app psegs _ _ [_] _)) in FRv. destruct FRv as [AP2 FRv]. cbn [cells_size csize Nat.add app] in FRv.
  apply (proj1 (rw_cells_app psegs _ _ [_] _)) in FRv. destruct FRv as [BUFc FRv]. cbn [cells_size csize Nat.add app] in FRv.
  replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8)%Z with B in BUFc by lia.
  replace (bv_unsigned sp + -368 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 80)%Z with (bv_unsigned sp + -272)%Z in FRv by lia.
  replace (bv_unsigned sp + -368 + Z.of_nat 8)%Z with (bv_unsigned sp + -360)%Z in AP2 by lia.
  match type of BUFc with rw_cells _ _ _ [CB 80 ?b] => set (jb := b) in BUFc end. clearbody jb.
  match type of FRv with rw_cells _ _ _ (CB 168 ?b :: _) => set (jn := b) in FRv end. clearbody jn.
  pose proof (rw_CB_length _ _ _ _ BUFc) as LJB.
  replace (Z_to_bv 64 VA) with (Z_to_bv 64 (VA + 8 * 0)) in APC by (f_equal; lia).
  (* [comment removed for export] *)
  assert (SNK : SINK_sn Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368) m'' []).
  { exists jb. split; [|split; [exact FR | split; [reflexivity | split; [unfold zlength, SN_CAP; rewrite LJB; reflexivity | unfold SN_CAP; split; [lia | split; lia]]]]].
    unfold wfile. cbn [zb map length Z.of_nat]. rewrite LJB. rewrite !Z.add_0_r.
    split; [unfold FILE_cells; exact FH'|].
    split. { apply (proj2 (rw_cells_app psegs _ _ [CB 0 []] [CB 80 jb])). split; [apply rw_cells_CB0; lia|]. cbn [cells_size csize Nat.add]. rewrite Z.add_0_r. exact BUFc. }
    split; [reflexivity|]. split; [vm_compute; discriminate|]. lia. }
  (* [comment removed for export] *)
  assert (PCALL : forall Q ms, implM psegs (printf_model OUT_sn OUTFP_sn fmt args) [] Q ms -> evt psegs (Q r o) ms).
  { intros Q ms H. unfold implM in H. rewrite MODEL in H. exact H. }
  pose proof (printf_core_proof (list Z) Fp B 80 _ _ OUT_sn OUTFP_sn
                (sn_sink_frame Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368))
                (sn_sink_flags Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368))
                (sn_topok (bv_unsigned sp + -368))
                (sn_out Fp (Z_to_bv 8 0) j1 j2 (Z_to_bv 64 4294967295) (snfile_rest CK) B (bv_unsigned sp + -368))) as PC2.
  unfold printf_core_stmt in PC2.
  eapply evt_cut.
  { apply PCALL. eapply PC2 with (i := 0%Z) (slots := slots); rewrite ?unsigned_lit by lia; unfold PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, TOPOK_sn, zlength;
      [ exact SNK | exact BY | exact HF | reflexivity | exact APC | exact VAA | lia | | | match goal with H : stk _ _ lo _ |- _ => exact H end | lia | lia | lia | lia
      | unfold ssp_cells, got_ssp, ssp_guard; split; [exact SSP1 | exact SSP2] | assumption | exact FRM | lia | lia | lia | lia | lia | lia | lia ].
    - (* [comment removed for export] *) cbn [skipn Z.to_nat]. eapply args_ok_vf; [exact AOK | lia |].
      exact MU1.
    - (* [comment removed for export] *)
      eapply Forall_impl; [|exact FPF]. intros [[[[y w] p] fl] t] FF. apply sn_fpcall. exact FF. }
  cbv beta. intros ms' P. clear PC2 PCALL MODEL FPF AOK HF BY VAA P1.
  unfold printf_core_post in P. rewrite !unsigned_lit in P by lia.
  (nelim P 29%nat; intros y5 y6 y7 d1 d2 d3 d4 d5 d6 d7 y28 y29 y30 y31 Ft fc' apv m3 -> MUc WMc MI3 FRM' FOK ST3 SNK3 SSP3 APC3 Hr).
  unfold INT_MAX in Hr.
  unfold SR in MUc. cbn [app] in MUc.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call psegs mm m3 MUc WMc; clear MUc WMc; try clear MIt end.
  fix_ret.
  (* [comment removed for export] *)
  (nelim SNK3 8%nat; intros junk3 WF3 FR3 FRL3 LEN3 SEPB3 T13 T23).
  (nelim WF3 7%nat; intros FC3 BUF3 FL3 LBF3 B03 BHI3 SEPfb3).
  pose proof (zb_length o) as LZo. rewrite LZo in *. unfold zlength, SN_CAP in LEN3.
  unfold FILE_cells in FC3. subst j2.
  (* [comment removed for export] *)
  lazymatch type of FC3 with rw_cells _ ?mm _ [?c1; ?c2; ?c3; ?c4; CB 96 _; ?c6] =>
    pose proof (rw_cells_unmerge mm Fp [c1; c2; c3; c4]
           [C8 z64; C8 (Z_to_bv 64 B); C8 z64; C8 (Z_to_bv 64 116740); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 80);
            C8 z64; C8 z64; C4 (Z_to_bv 64 0); C4 z64; C8 z64; C4 mode'; C4 (Z_to_bv 64 4294967295)] [c6]) as UM end.
  cbn [cells_size csize cells_bytes cbytes Nat.add app] in UM.
  specialize (UM FC3 ltac:(cbn [cells_wf cell_wf]; repeat split)). clear FC3. rename UM into FC3.
  subst j1.
  apply (rw_cells_merge psegs _ _ [] [CB 1 _; CB 31 _]) in FC3. cbn [app cells_size csize Nat.add cells_bytes cbytes] in FC3.
  match type of FC3 with rw_cells _ _ _ (CB 32 ?b :: _) => let v := eval vm_compute in b in change b with v in FC3 end.
  lazymatch type of FC3 with rw_cells _ ?mm _ (CB 32 _ :: ?rest) =>
    pose proof (rw_cells_unmerge mm Fp [] [C4 (Z_to_bv 64 0); C4 z64; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] rest) as UM end.
  cbn [cells_size csize cells_bytes cbytes Nat.add app] in UM.
  lazymatch type of UM with rw_cells _ _ _ (CB 32 ?b :: _) -> _ => let v := eval vm_compute in b in change b with v in UM end.
  specialize (UM FC3 ltac:(cbn [cells_wf cell_wf]; repeat split)). clear FC3. rename UM into FC3.
  zs. zs. zs. brf Kb; [exfalso; lia|].
  zs. zs. zs. zs. zs.
  (* [comment removed for export] *)
  apply (proj1 (rw_cells_app psegs _ _ [_; _; _; _; _; _] _)) in FC3. destruct FC3 as [F0 FC3]. cbn [cells_size csize Nat.add app] in FC3.
  apply (proj1 (rw_cells_app psegs _ _ [_] _)) in FC3. destruct FC3 as [F40 FC3]. cbn [cells_size csize Nat.add app] in FC3.
  apply (proj1 (rw_cells_app psegs _ _ [_] _)) in FC3. destruct FC3 as [F48 FC3]. cbn [cells_size csize Nat.add app] in FC3.
  apply (proj1 (rw_cells_app psegs _ _ [_] _)) in FC3. destruct FC3 as [F56 FC3]. cbn [cells_size csize Nat.add app] in FC3.
  apply (proj1 (rw_cells_app psegs _ _ [_; _; _] _)) in FC3. destruct FC3 as [F64 FC3]. cbn [cells_size csize Nat.add app] in FC3.
  apply (proj1 (rw_cells_app psegs _ _ [_] _)) in FC3. destruct FC3 as [F88 F96]. cbn [cells_size csize Nat.add app] in F96.
  replace (Fp + Z.of_nat 40)%Z with (Fp + 40)%Z in F40 by lia.
  replace (Fp + Z.of_nat 40 + Z.of_nat 8)%Z with (Fp + 48)%Z in F48 by lia.
  replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8)%Z with (Fp + 56)%Z in F56 by lia.
  replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8)%Z with (Fp + 64)%Z in F64 by lia.
  replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 24)%Z with (Fp + 88)%Z in F88 by lia.
  replace (Fp + Z.of_nat 40 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 24 + Z.of_nat 8)%Z with (Fp + 96)%Z in F96 by lia.
  unfold snfile_rest in FR3.
  apply (proj1 (rw_cells_app psegs _ _ [_] _)) in FR3. destruct FR3 as [F148 FR3]. cbn [cells_size csize Nat.add app] in FR3.
  apply (proj1 (rw_cells_app psegs _ _ [_] _)) in FR3. destruct FR3 as [F152 F160]. cbn [cells_size csize Nat.add app] in F160.
  replace (Fp + 148 + Z.of_nat 4)%Z with (Fp + 152)%Z in F152 by lia.
  replace (Fp + 148 + Z.of_nat 4 + Z.of_nat 8)%Z with (Fp + 160)%Z in F160 by lia.
  pose proof (rw_cells_bytes_at' _ _ _ _ BUF3) as SRC3. cbn [cells_bytes cbytes app] in SRC3. rewrite app_nil_r in SRC3.
  apply bytes_at_app in SRC3. destruct SRC3 as [SRC3 _].
  replace (Z_to_bv 64 (B + Z.of_nat (length o))) with (Z_to_bv 64 (B + zlength o)) in F40 by reflexivity.
  clear MU1. clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  change psegs with psegs in SSP1, SSP2, BUF3.
  match goal with H : stk _ ?mm lo (bv_unsigned sp + -368)%Z |- _ => destruct (stk_split _ _ _ (bv_unsigned sp + -368 - 64) _ H ltac:(lia)) as [ST4a ST4b]; clear H end.
  eapply evt_cut.
  { eapply sn_write_spec with (o := o) (B := B) (n := n) (D := D) (CK := CK) (dn := dn) (bufp := B) (Fp := Fp) (junk := junkd);
      rewrite ?unsigned_lit by lia; unfold zlength;
      [ reflexivity | reflexivity | exact F40 | exact F56 | exact F88 | exact F152 | | exact SRC3 | | exact ROOM | lia | lia | lia | exact ST4b | lia | assumption
      | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia ].
    all: lazymatch goal with |- rw_cells _ _ ?a _ => match goal with H : rw_cells _ _ a _ |- _ => exact H end end. }
  cbv beta. intros ms' P.
  unfold sn_write_post in P. rewrite !unsigned_lit in P by lia.
  (nelim P 25%nat; intros z5 z6 z7 e1 e2 e3 e4 e5 e6 e7 z28 z29 z30 z31 m4 -> MUc WMc MI4 ST4b' CK4 DST4 F40' F56' SRC4).
  rewrite ?unsigned_lit in ST4b' by lia.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call psegs mm m4 MUc WMc; clear MUc WMc; try clear MI3 end.
  fix_ret.
  (* [comment removed for export] *)
  zs. zs. zs. zs. zs.
  zs. replace (0 <? B)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  zs. zs. rewrite ?Z.lor_0_l. zs.
  zs. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zs. zs. zs. zs. zs. rewrite ?Z.lor_0_l. zs. zs. if_lit.
  zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
  do 9 zs.
  try rewrite (land_M64_id r) by lia.
  (* [comment removed for export] *)
  match goal with H : rw_cells _ ?mm (bv_unsigned sp + -368)%Z [C8 apv] |- _ => rename H into APC4 end.
  match goal with H : rw_cells _ ?mm B _ |- _ => rename H into BUF4 end.
  match goal with H : stk _ ?mm lo (bv_unsigned sp + -368 - 64)%Z, H' : stk _ ?mm (bv_unsigned sp + -368 - 64)%Z _ |- _ =>
    pose proof (stk_merge _ _ _ _ _ H H' ltac:(lia)) as ST5; clear H H' end.
  release_frame APC4 ST5 (bv_unsigned sp + -360)%Z.
  release_frame AP2 ST5 B.
  release_frame BUF4 ST5 (bv_unsigned sp + -272)%Z.
  release_frame FRv ST5 (bv_unsigned sp).
  lazymatch goal with F0 : rw_cells _ ?mm Fp _, F40 : rw_cells _ ?mm (Fp + 40)%Z _, F48 : rw_cells _ ?mm (Fp + 48)%Z _, F56 : rw_cells _ ?mm (Fp + 56)%Z _,
                   F64 : rw_cells _ ?mm (Fp + 64)%Z _, F88 : rw_cells _ ?mm (Fp + 88)%Z _, F96 : rw_cells _ ?mm (Fp + 96)%Z _,
                   F148 : rw_cells _ ?mm (Fp + 148)%Z _, F152 : rw_cells _ ?mm (Fp + 152)%Z _, F160 : rw_cells _ ?mm (Fp + 160)%Z _ |- _ =>
    assert (FALL : rw_cells psegs mm Fp ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
              ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 116740); C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 bufp)]
              ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode'; C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295)]
              ++ [C4 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 CK)] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]));
    [ apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [piece F0|];
      apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [piece F40|];
      apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [piece F48|];
      apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [piece F56|];
      apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [piece F64|];
      apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [piece F88|];
      apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [piece F96|];
      apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [piece F148|];
      apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [piece F152|];
      piece F160
    | ] end.
  destruct (rw_cells_forget _ _ _ _ FALL) as [fjunk FJ]. cbn [cells_size csize Nat.add app] in FJ.
  apply evt_done. unfold vfprintf_sn_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact FOK|].
  split; [exact ST5|].
  split; [split; [exact SSP1 | exact SSP2]|].
  split; [exact DST4|]. split; [exact CK4|]. exact FJ.
Qed.
End F_vfprintf.

(* [comment removed for export] *)
Module Printf_sn.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_printf_iface F_printf_core.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zlength_app : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_nil : zlength (@nil Z) = 0.
Proof. reflexivity. Qed.
Lemma zlength_concat_cons : forall {A} (p : list A) ps, zlength (concat (p :: ps)) = zlength p + zlength (concat ps).
Proof. intros. cbn [concat]. apply zlength_app. Qed.
Lemma zlength_concat_app : forall {A} (ps qs : list (list A)), zlength (concat (ps ++ qs)) = zlength (concat ps) + zlength (concat qs).
Proof. intros. rewrite concat_app. apply zlength_app. Qed.
Lemma zlength_nonneg : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

Lemma mbind_eq : forall {St A B} (m : M St A) (f : A -> M St B) s a s',
  m s = ITree.Ret (Ok (a, s')) -> mbind m f s = f a s'.
Proof. intros St A B m f s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Lemma OUT_sn_eq : forall bs o, zlength o + zlength bs <= SN_CAP -> OUT_sn bs o = ITree.Ret (Ok (tt, o ++ bs)).
Proof.
  intros bs o H. unfold OUT_sn. rewrite (mbind_eq mget _ o o o) by reflexivity.
  replace (zlength o + zlength bs <=? SN_CAP) with true by (symmetry; apply Z.leb_le; exact H). reflexivity.
Qed.

Lemma OUTFP_sn_eq : forall y w p fl t o o1 r, fmt_fp o y w p fl t = Some (o1, r) -> zlength o1 <= SN_CAP ->
  OUTFP_sn y w p fl t o = ITree.Ret (Ok (r, o1)).
Proof.
  intros y w p fl t o o1 r E H. unfold OUTFP_sn. rewrite (mbind_eq mget _ o o o) by reflexivity.
  rewrite E. replace (zlength o1 <=? SN_CAP) with true by (symmetry; apply Z.leb_le; exact H). reflexivity.
Qed.

Lemma mbind_mbind_eq : forall {St A B C} (m : M St A) (f : A -> M St B) (g : B -> M St C) s a s',
  m s = ITree.Ret (Ok (a, s')) -> mbind (mbind m f) g s = mbind (f a) g s'.
Proof. intros St A B C m f g s a s' H. unfold mbind, ebind. rewrite H. reflexivity. Qed.

Lemma mpad_sn_eq : forall c w l fl o ps,
  pad_pieces c w l fl = Some ps -> zlength o + zlength (concat ps) <= SN_CAP ->
  mpad OUT_sn c w l fl o = ITree.Ret (Ok (tt, o ++ concat ps)).
Proof.
  intros c w l fl o ps P H. unfold mpad, pad_pieces in *.
  destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
  - inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity.
  - destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [concat] in *. rewrite app_nil_r in *.
    apply OUT_sn_eq. exact H.
Qed.

(* [comment removed for export] *)
Ltac msn E := first [ rewrite (mbind_mbind_eq _ _ _ _ _ _ E) | rewrite (mbind_eq _ _ _ _ _ E) ]; cbv beta.

Lemma conv_tail_sn : forall cnt fl w p prefix body (k : Z -> M (list Z) Z) o ps r,
  tail_pieces cnt fl w p prefix body = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
  mbind (conv_tail OUT_sn cnt fl w p prefix body) k o = k r (o ++ concat ps).
Proof.
  intros cnt fl w p prefix body k o ps r T H. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta.
  destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
  destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
  destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
  destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
  destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
  destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
  inversion T; subst. clear T.
  repeat first [rewrite zlength_concat_app in H | rewrite zlength_concat_cons in H]. rewrite ?zlength_nil in H. cbn [concat] in H. rewrite ?app_nil_r, ?zlength_nil in H.
  pose proof (zlength_nonneg (concat p1)). pose proof (zlength_nonneg (concat p2)). pose proof (zlength_nonneg (concat p3)).
  pose proof (zlength_nonneg (concat p4)). pose proof (zlength_nonneg prefix). pose proof (zlength_nonneg body). pose proof (zlength_nonneg o).
  pose proof (mpad_sn_eq _ _ _ _ o _ P1 ltac:(lia)) as E1. msn E1.
  pose proof (OUT_sn_eq prefix (o ++ concat p1) ltac:(rewrite zlength_app; lia)) as E2. msn E2.
  pose proof (mpad_sn_eq _ _ _ _ ((o ++ concat p1) ++ prefix) _ P2 ltac:(rewrite !zlength_app; lia)) as E3. msn E3.
  pose proof (mpad_sn_eq _ _ _ _ (((o ++ concat p1) ++ prefix) ++ concat p2) _ P3 ltac:(rewrite !zlength_app; lia)) as E4. msn E4.
  pose proof (OUT_sn_eq body ((((o ++ concat p1) ++ prefix) ++ concat p2) ++ concat p3) ltac:(rewrite !zlength_app; lia)) as E5. msn E5.
  pose proof (mpad_sn_eq _ _ _ _ (((((o ++ concat p1) ++ prefix) ++ concat p2) ++ concat p3) ++ body) _ P4 ltac:(rewrite !zlength_app; lia)) as E6. msn E6.
  rewrite mbind_mret. rewrite ?concat_app. cbn [concat]. rewrite ?concat_app. cbn [concat]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma conv_int_sn : forall cnt fl w p xp argi prefix body (k : Z -> M (list Z) Z) o ps r,
  int_pieces cnt fl w p xp argi prefix body = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
  mbind (conv_int OUT_sn cnt fl w p xp argi prefix body) k o = k r (o ++ concat ps).
Proof.
  intros cnt fl w p xp argi prefix body k o ps r T H. unfold conv_int, int_pieces in *.
  destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta.
  destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_sn; eassumption.
Qed.

Lemma conv_sn : forall cnt d a (k : Z -> M (list Z) Z) o ps r,
  conv_pieces cnt d a = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
  mbind (conv OUT_sn OUTFP_sn cnt d a) k o = k r (o ++ concat ps).
Proof.
  intros cnt d a k o ps r T H. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta.
  destruct a as [s|i|u|dd].
  - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
    destruct ((d_p d <? 0) && (INT_MAX <=? zlength s))%bool; [discriminate|].
    eapply conv_tail_sn; eassumption.
  - destruct (negb (d_ty d =? T_INT)); [discriminate|].
    destruct (INTMAX_MAX <? i mod 2 ^ 64);
      [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
      eapply conv_int_sn; eassumption.
  - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
    destruct (d_t d =? 117); eapply conv_int_sn; eassumption.
  - discriminate.
Qed.

Lemma printf_loop_sn : forall fuel s args cnt o ps r,
  printf_pieces_loop fuel s args cnt = Some (ps, r) -> zlength o + zlength (concat ps) <= SN_CAP ->
  printf_loop OUT_sn OUTFP_sn fuel s args cnt o = ITree.Ret (Ok (r, o ++ concat ps)).
Proof.
  induction fuel as [|fuel IH]; intros s args cnt o ps r P H; [discriminate|].
  cbn [printf_pieces_loop] in P. cbn [printf_loop].
  destruct s as [|c s1]; [discriminate|].
  destruct (c =? 0). { inversion P; subst. cbn [concat]. rewrite app_nil_r. reflexivity. }
  cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
  destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
  destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
  pose proof (zlength_nonneg o) as Ho.
  destruct (0 <? zlength lit).
  - destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
    destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
    inversion P; subst. clear P. rewrite zlength_concat_cons in H. pose proof (zlength_nonneg (concat ps')).
    pose proof (OUT_sn_eq lit o ltac:(lia)) as E1. msn E1.
    rewrite (IH _ _ _ _ _ _ R) by (rewrite zlength_app; lia). cbn [concat]. rewrite <- ?app_assoc. rewrite ?app_nil_l, ?app_nil_r. reflexivity.
  - destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
    destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
    destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
    inversion P; subst. clear P. rewrite zlength_concat_cons, zlength_concat_app, zlength_nil in H.
    pose proof (zlength_nonneg (concat ps1)). pose proof (zlength_nonneg (concat ps2)).
    pose proof (OUT_sn_eq [] o ltac:(rewrite zlength_nil; lia)) as E1. msn E1. rewrite app_nil_r.
    rewrite (conv_sn _ _ _ _ _ _ _ C) by lia.
    rewrite (IH _ _ _ _ _ _ R) by (rewrite ?zlength_app; lia). cbn [concat]. rewrite ?concat_app. rewrite <- ?app_assoc. rewrite ?app_nil_l, ?app_nil_r. reflexivity.
Qed.

Theorem printf_model_sn : forall fmt args ps r,
  printf_pieces fmt args = Some (ps, r) -> zlength (concat ps) <= SN_CAP ->
  printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, concat ps)).
Proof.
  intros fmt args ps r P H. unfold printf_model, printf_pieces in *.
  exact (printf_loop_sn _ _ _ _ [] _ _ P ltac:(rewrite zlength_nil; lia)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dec_digits_step1 : forall x, 1 <= x < 2^64 -> dec_digits x = dec_digits (x / 10) ++ [48 + x mod 10].
Proof.
  intros x Hx. destruct (Z_lt_le_dec x 10).
  - rewrite dec_digits_small by lia. rewrite Z.div_small, Z.mod_small, dec_digits_0 by lia. reflexivity.
  - apply dec_digits_step. lia.
Qed.

Lemma dec_digits_pos_length : forall x, 1 <= x < 2^64 -> (1 <= length (dec_digits x))%nat.
Proof. intros x Hx. rewrite dec_digits_step1 by lia. rewrite length_app. cbn. lia. Qed.

Lemma dec_digits_len_bound : forall n x, 0 <= x < 10 ^ Z.of_nat n -> x < 2^64 -> (length (dec_digits x) <= n)%nat.
Proof.
  induction n as [|n IH]; intros x Hx H64.
  - cbn in Hx. replace x with 0 by lia. rewrite dec_digits_0. cbn. lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia.
    destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite dec_digits_0; cbn; lia|].
    rewrite dec_digits_step1 by lia. rewrite length_app. cbn [length].
    specialize (IH (x / 10) ltac:(split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]) ltac:(apply Z.div_lt_upper_bound; lia)). lia.
Qed.

Lemma firstn_S_snoc : forall (l : list Z) k, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l 0].
Proof.
  induction l as [|x l IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k]; [reflexivity|]. cbn [firstn nth]. rewrite IH by (cbn in Hk; lia). reflexivity.
Qed.

Lemma zsub_snoc : forall l i n, 0 <= i -> 0 <= n -> i + n + 1 <= zlength l ->
  zsub l i (n + 1) = zsub l i n ++ [znth l (i + n)].
Proof.
  intros l i n Hi Hn H. unfold zsub, zlength in *.
  replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  rewrite firstn_S_snoc by (rewrite length_skipn; lia). rewrite nth_skipn.
  unfold znth. destruct (Z.ltb_spec0 (i + n) 0); [lia|].
  replace (Z.to_nat (i + n)) with (Z.to_nat i + Z.to_nat n)%nat by lia. reflexivity.
Qed.

Lemma zsub_0 : forall l i, zsub l i 0 = [].
Proof. intros. reflexivity. Qed.

Lemma fmt_u_loop_dec : forall (n : nat) fuel y s b,
  (n < fuel)%nat -> 0 <= y < 10 ^ Z.of_nat n -> y < 2^64 -> Z.of_nat n <= s -> s <= zlength b ->
  exists b', fmt_u_loop fuel (y, s, b) = Some (0, s - zlength (dec_digits y), b')
    /\ length b' = length b
    /\ zsub b' (s - zlength (dec_digits y)) (zlength (dec_digits y)) = dec_digits y
    /\ (forall i, ~ (s - zlength (dec_digits y) <= i < s) -> znth b' i = znth b i).
Proof.
  induction n as [|n IH]; intros fuel y s b Hf Hy Hy64 Hs Hb.
  - cbn in Hy. destruct fuel as [|fuel]; [lia|]. exists b. cbn [fmt_u_loop].
    replace (y =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
    replace y with 0 by lia. rewrite dec_digits_0, zlength_nil, Z.sub_0_r, zsub_0. repeat split; intros; lia.
  - destruct fuel as [|fuel]; [lia|].
    destruct (Z.eq_dec y 0) as [->|NZ].
    + exists b. cbn [fmt_u_loop Z.eqb negb]. rewrite dec_digits_0, zlength_nil, Z.sub_0_r, zsub_0. repeat split; intros; lia.
    + cbn [fmt_u_loop]. replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
      unfold fmt_u_loop_body at 1.
      rewrite Nat2Z.inj_succ in Hy, Hs. rewrite Z.pow_succ_r in Hy by lia.
      destruct (IH fuel (y / 10) (s - 1) (zupd b (s - 1) (CHR_0 + y mod 10)) ltac:(lia)
                  ltac:(split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]) ltac:(apply Z.div_lt_upper_bound; lia)
                  ltac:(lia) ltac:(rewrite zlength_zupd; lia))
        as (b' & E & LEN & SUB & OUT).
      pose proof (dec_digits_step1 y ltac:(lia)) as DD.
      assert (LD : zlength (dec_digits y) = zlength (dec_digits (y / 10)) + 1) by (rewrite DD, zlength_app; reflexivity).
      pose proof (zlength_nonneg (dec_digits (y / 10))) as L0.
      pose proof (dec_digits_len_bound n (y / 10) ltac:(split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]) ltac:(apply Z.div_lt_upper_bound; lia)) as L20.
      unfold zlength in *.
      exists b'. split; [rewrite E; f_equal; f_equal; f_equal; lia|].
      split; [rewrite LEN; apply zupd_length|].
      split.
      * rewrite LD. replace (s - (Z.of_nat (length (dec_digits (y / 10))) + 1)) with (s - 1 - Z.of_nat (length (dec_digits (y / 10)))) by lia.
        rewrite zsub_snoc by (unfold zlength; rewrite ?LEN, ?zupd_length; lia).
        rewrite SUB. replace (s - 1 - Z.of_nat (length (dec_digits (y / 10))) + Z.of_nat (length (dec_digits (y / 10)))) with (s - 1) by lia.
        rewrite OUT by lia. rewrite znth_zupd_eq by (unfold zlength; lia). rewrite DD. unfold CHR_0. reflexivity.
      * intros i Hi. rewrite OUT by lia. apply znth_zupd_neq. lia.
Qed.

Lemma pow10_20 : 2^64 < 10 ^ Z.of_nat 20.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fmt_u_dec : forall x, 0 <= x < 2^64 ->
  exists b', fmt_u x (zrepeat 0 24) 24 = Some (24 - zlength (dec_digits x), b')
    /\ zlength b' = 24 /\ zsub b' (24 - zlength (dec_digits x)) (zlength (dec_digits x)) = dec_digits x.
Proof.
  intros x Hx. unfold fmt_u. change FMT_U_FUEL with 21%nat.
  destruct (fmt_u_loop_dec 20 21 x 24 (zrepeat 0 24) ltac:(lia) ltac:(pose proof pow10_20; lia) ltac:(lia) ltac:(change (Z.of_nat 20) with 20; lia) ltac:(change (zlength (zrepeat 0 24)) with 24; lia))
    as (b' & E & LEN & SUB & _).
  exists b'. rewrite E. split; [reflexivity|]. split; [unfold zlength; rewrite LEN; reflexivity| exact SUB].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zb1 :=
  match goal with
  | |- context [?a <=? ?b] => first [replace (a <=? b) with true by (symmetry; apply Z.leb_le; lia) | replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia)]
  | |- context [?a <? ?b] => first [replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia)]
  | |- context [?a =? ?b] => first [replace (a =? b) with true by (symmetry; apply Z.eqb_eq; lia) | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; lia)]
  end; cbn [andb orb negb]; cbv beta iota.

(* [comment removed for export] *)
Lemma FL1 : (Z.land 0 (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = true. Proof. reflexivity. Qed.
Lemma FL2 : (Z.land (Z.lxor 0 ZERO_PAD) (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = false. Proof. reflexivity. Qed.
Lemma FL3 : (Z.land (Z.lxor 0 LEFT_ADJ) (Z.lor LEFT_ADJ ZERO_PAD) =? 0) = false. Proof. reflexivity. Qed.
Lemma FL4 : (Z.land 0 MARK_POS =? 0) = true. Proof. reflexivity. Qed.
Lemma FL5 : (Z.land 0 PAD_POS =? 0) = true. Proof. reflexivity. Qed.
Ltac fl0 := rewrite ?FL1, ?FL2, ?FL3, ?FL4, ?FL5; cbn [negb orb andb].

(* [comment removed for export] *)
Ltac lhs_cbv1 := match goal with |- ?l = _ => let l' := eval cbv -[conv_pieces dec_digits] in l in change l with l' end.
Ltac lhs_cbv2 := match goal with |- ?l = _ => let l' := eval cbv -[int_pieces Z.modulo Z.pow Z.ltb INTMAX_MAX Z.opp dec_digits] in l in change l with l' end.

(* [comment removed for export] *)
Lemma tail_pieces_d : forall prefix body, zlength prefix <= 1 -> 1 <= zlength body <= 20 ->
  tail_pieces 0 0 0 (Z.max (-1) (zlength body + 0)) prefix body = Some ([prefix; body], zlength prefix + zlength body).
Proof.
  intros prefix body Hp Hb. pose proof (zlength_nonneg prefix). unfold tail_pieces. cbv zeta.
  replace (Z.max (Z.max (-1) (zlength body + 0)) (zlength body)) with (zlength body) by lia.
  replace (Z.max 0 (zlength prefix + zlength body)) with (zlength prefix + zlength body) by lia.
  unfold INT_MAX. zb1. zb1.
  unfold pad_pieces. fl0. zb1. zb1. reflexivity.
Qed.

Lemma printf_pieces_d_pos : forall x, 1 <= x < 2^31 ->
  printf_pieces FMT_d [PA_i x] = Some ([[]; []; dec_digits x], zlength (dec_digits x)).
Proof.
  intros x Hx. unfold printf_pieces. lhs_cbv1. unfold conv_pieces. lhs_cbv2.
  rewrite Z.mod_small by lia. unfold INTMAX_MAX. zb1.
  unfold int_pieces. cbv beta iota zeta delta [andb Z.ltb].
  pose proof (dec_digits_pos_length x ltac:(lia)). pose proof (dec_digits_length x).
  zb1. rewrite tail_pieces_d by (unfold zlength; cbn [length]; lia). reflexivity.
Qed.

Lemma printf_pieces_d_neg : forall x, -2^31 <= x < 0 ->
  printf_pieces FMT_d [PA_i x] = Some ([[]; [45]; dec_digits (- x)], 1 + zlength (dec_digits (- x))).
Proof.
  intros x Hx. unfold printf_pieces. lhs_cbv1. unfold conv_pieces. lhs_cbv2.
  replace (x mod 2 ^ 64) with (x + 2^64) by (apply Z.mod_unique with (q := -1); lia).
  unfold INTMAX_MAX. zb1.
  replace ((- (x + 2 ^ 64)) mod 2 ^ 64) with (- x) by (apply Z.mod_unique with (q := -1); lia).
  unfold int_pieces. cbv beta iota zeta delta [andb Z.ltb].
  pose proof (dec_digits_pos_length (- x) ltac:(lia)). pose proof (dec_digits_length (- x)).
  zb1. rewrite tail_pieces_d by (unfold zlength; cbn [length]; lia). reflexivity.
Qed.

Lemma fmt_d_pos : forall x, 1 <= x < 2^31 -> fmt_d x = Some (dec_digits x, zlength (dec_digits x)).
Proof.
  intros x Hx. unfold fmt_d. cbv zeta. unfold u64. rewrite Z.mod_small by lia. unfold INTMAX_MAX. zb1. fl0.
  destruct (fmt_u_dec x ltac:(lia)) as (b' & E & LEN & SUB). rewrite E.
  pose proof (dec_digits_pos_length x ltac:(lia)). pose proof (dec_digits_length x). unfold zlength in *.
  repeat zb1.
  replace (Z.max (-1) (24 - (24 - Z.of_nat (length (dec_digits x))) + 0)) with (Z.of_nat (length (dec_digits x))) by lia.
  unfold INT_MAX. repeat zb1.
  rewrite !pad_model by lia. unfold pad_n. fl0. repeat zb1. unfold out.
  change (zrepeat CHR_sp 0) with (@nil Z). change (zrepeat CHR_0 0) with (@nil Z). change (zsub PREFIX_D 0 0) with (@nil Z). cbn [app]. rewrite app_nil_r.
  replace (24 - (24 - Z.of_nat (length (dec_digits x)))) with (Z.of_nat (length (dec_digits x))) by lia.
  rewrite SUB. repeat f_equal; lia.
Qed.

Lemma fmt_d_neg : forall x, -2^31 <= x < 0 -> fmt_d x = Some (45 :: dec_digits (- x), 1 + zlength (dec_digits (- x))).
Proof.
  intros x Hx. unfold fmt_d. cbv zeta. unfold u64.
  replace (x mod 2 ^ 64) with (x + 2^64) by (apply Z.mod_unique with (q := -1); lia).
  unfold INTMAX_MAX. zb1.
  replace ((- (x + 2 ^ 64)) mod 2 ^ 64) with (- x) by (apply Z.mod_unique with (q := -1); lia).
  destruct (fmt_u_dec (- x) ltac:(lia)) as (b' & E & LEN & SUB). rewrite E.
  pose proof (dec_digits_pos_length (- x) ltac:(lia)). pose proof (dec_digits_length (- x)). unfold zlength in *.
  repeat zb1.
  replace (Z.max (-1) (24 - (24 - Z.of_nat (length (dec_digits (- x)))) + 0)) with (Z.of_nat (length (dec_digits (- x)))) by lia.
  unfold INT_MAX. repeat zb1.
  rewrite !pad_model by lia. unfold pad_n. fl0. repeat zb1. unfold out.
  change (zrepeat CHR_sp 0) with (@nil Z). change (zrepeat CHR_0 0) with (@nil Z). change (zsub PREFIX_D 0 1) with [45]. cbn [app]. rewrite app_nil_r.
  replace (24 - (24 - Z.of_nat (length (dec_digits (- x))))) with (Z.of_nat (length (dec_digits (- x)))) by lia.
  rewrite SUB. repeat f_equal; lia.
Qed.

Theorem printf_sn_d : forall i o r, -2^31 <= i < 2^31 -> fmt_d i = Some (o, r) ->
  printf_model OUT_sn OUTFP_sn FMT_d [PA_i i] [] = ITree.Ret (Ok (r, o)).
Proof.
  intros i o r Hi E.
  destruct (Z.eq_dec i 0) as [->|NZ].
  { vm_compute in E. inversion E; subst. vm_compute. reflexivity. }
  pose proof (dec_digits_length (Z.abs i)) as L.
  destruct (Z_lt_le_dec i 0).
  - rewrite fmt_d_neg in E by lia. inversion E; subst. rewrite Z.abs_neq in L by lia.
    rewrite (printf_model_sn _ _ _ _ (printf_pieces_d_neg i ltac:(lia))); cbn [concat app]; rewrite ?app_nil_r; [reflexivity|].
    unfold zlength, SN_CAP. cbn [length]. lia.
  - rewrite fmt_d_pos in E by lia. inversion E; subst. rewrite Z.abs_eq in L by lia.
    rewrite (printf_model_sn _ _ _ _ (printf_pieces_d_pos i ltac:(lia))); cbn [concat app]; rewrite ?app_nil_r; [reflexivity|].
    unfold zlength, SN_CAP. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lhs_cbvg1 := match goal with |- ?l = _ => let l' := eval cbv -[fmt_fp f128_of_d conv OUT_sn OUTFP_sn mbind mret] in l in change l with l' end.
Ltac lhs_cbvg2 := match goal with |- ?l = _ => let l' := eval cbv -[fmt_fp f128_of_d OUT_sn OUTFP_sn mbind mret munr Z.ltb Z.leb orb Z.sub Z.add] in l in change l with l' end.

Lemma printf_sn_g_prec : forall d prec o l, (prec = 15 \/ prec = 17) ->
  fmt_fp [] (f128_of_d d) 1 prec 0 CHR_g = Some (o, l) -> 0 <= l <= INT_MAX -> zlength o <= SN_CAP ->
  printf_model OUT_sn OUTFP_sn (if prec =? 15 then FMT_g15 else FMT_g17) [PA_g d] [] = ITree.Ret (Ok (l, o)).
Proof.
  intros d prec o l Hp F Hl Ho.
  destruct Hp as [-> | ->]; cbn [Z.eqb Pos.eqb];
    unfold printf_model; lhs_cbvg1;
    (pose proof (OUT_sn_eq [] [] ltac:(rewrite zlength_nil; unfold SN_CAP; lia)) as E0; msn E0; clear E0);
    unfold conv; lhs_cbvg2.
  - replace (15 <? 0) with false by reflexivity. replace ((1 <? 1) || (1048576 <=? 15))%bool with false by reflexivity.
    change CHR_g with 103 in F.
    pose proof (OUTFP_sn_eq _ _ _ _ _ _ _ _ F Ho) as E1. msn E1.
    replace ((l <? 0) || (2147483647 - 0 <? l))%bool with false by (symmetry; apply Bool.orb_false_intro; apply Z.ltb_ge; unfold INT_MAX in Hl; lia).
    rewrite mbind_mret. cbv -[Z.add]. rewrite Z.add_0_l. reflexivity.
  - replace (17 <? 0) with false by reflexivity. replace ((1 <? 1) || (1048576 <=? 17))%bool with false by reflexivity.
    change CHR_g with 103 in F.
    pose proof (OUTFP_sn_eq _ _ _ _ _ _ _ _ F Ho) as E1. msn E1.
    replace ((l <? 0) || (2147483647 - 0 <? l))%bool with false by (symmetry; apply Bool.orb_false_intro; apply Z.ltb_ge; unfold INT_MAX in Hl; lia).
    rewrite mbind_mret. cbv -[Z.add]. rewrite Z.add_0_l. reflexivity.
Qed.

Theorem printf_sn_g : forall d prec o r, FMT_G_RET -> FMT_G_LEN25 -> (prec = 15 \/ prec = 17) ->
  fmt_g d prec = Some (o, r) ->
  printf_model OUT_sn OUTFP_sn (if prec =? 15 then FMT_g15 else FMT_g17) [PA_g d] [] = ITree.Ret (Ok (r, o)).
Proof.
  intros d prec o r RET LEN Hp E. unfold fmt_g in E.
  destruct (fmt_fp [] (f128_of_d d) 1 prec 0 CHR_g) as [[o1 l]|] eqn:F; [|discriminate].
  pose proof (RET _ _ _ _ Hp F) as Hl. pose proof (LEN _ _ _ _ Hp F) as Ho. pose proof (zlength_nonneg o1).
  inversion E; subst. replace (zlength o <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  apply printf_sn_g_prec; [exact Hp | exact F | unfold INT_MAX; lia | unfold SN_CAP; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint lzeqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && lzeqb a' b'
  | _, _ => false
  end.
Lemma lzeqb_eq : forall a b, lzeqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. subst. f_equal. apply IH. exact H2.
Qed.

Definition u04x_check (c : Z) : bool :=
  match printf_model OUT_sn OUTFP_sn FMT_u04x [PA_u c] [] with
  | ITree.Ret (Ok (r, o)) => (r =? 5) && lzeqb o (117 :: hex4_lower c)
  | _ => false
  end.
Lemma u04x_check_all : forallb u04x_check (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem printf_sn_u04x : forall c, 0 <= c < 256 ->
  printf_model OUT_sn OUTFP_sn FMT_u04x [PA_u c] [] = ITree.Ret (Ok (5, 117 :: hex4_lower c)).
Proof.
  intros c Hc.
  assert (CK : u04x_check c = true).
  { pose proof u04x_check_all as A. rewrite forallb_forall in A. apply A.
    apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. }
  unfold u04x_check in CK.
  destruct (printf_model OUT_sn OUTFP_sn FMT_u04x [PA_u c] []) as [[|[r o]]|n k]; try discriminate.
  apply andb_prop in CK. destruct CK as [H1 H2]. apply Z.eqb_eq in H1. apply lzeqb_eq in H2. subst. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pass1_ok_d : pass1_ok FMT_d = true. Proof. reflexivity. Qed.
Lemma pass1_ok_g15 : pass1_ok FMT_g15 = true. Proof. reflexivity. Qed.
Lemma pass1_ok_g17 : pass1_ok FMT_g17 = true. Proof. reflexivity. Qed.
Lemma pass1_ok_g : forall prec, pass1_ok (if prec =? 15 then FMT_g15 else FMT_g17) = true.
Proof. intros prec. destruct (prec =? 15); reflexivity. Qed.
Lemma pass1_ok_u04x : pass1_ok FMT_u04x = true. Proof. reflexivity. Qed.
Lemma fp_calls_d : forall i, fp_calls (length FMT_d) FMT_d [PA_i i] = [].
Proof. intros. reflexivity. Qed.
Lemma fp_calls_u04x : forall u, fp_calls (length FMT_u04x) FMT_u04x [PA_u u] = [].
Proof. intros. reflexivity. Qed.
Lemma fp_calls_g : forall prec d, (prec = 15 \/ prec = 17) ->
  fp_calls (length (if prec =? 15 then FMT_g15 else FMT_g17)) (if prec =? 15 then FMT_g15 else FMT_g17) [PA_g d] = [(f128_of_d d, 1, prec, 0, CHR_g)].
Proof. intros prec d [-> | ->]; reflexivity. Qed.
End Printf_sn.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_memcpy F_fwritex F_pad F_fmt_fp_lib F_fmt_fp F_pop_arg Exit Printf_model Printf_mlib F_printf_iface.
Import F_printf_core.
Import F_printf_snsink.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_sn_write.
Import F_vfprintf.
Import Printf_sn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac arith_goal := lazymatch goal with
  | |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ >= _)%Z => idtac | |- (_ > _)%Z => idtac
  | |- @eq Z _ _ => idtac | |- @eq nat _ _ => idtac | |- (_ <= _)%nat => idtac | |- (_ < _)%nat => idtac
  | |- ~ _ => idtac | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- False => idtac | |- True => idtac
  end.   (* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac lia ::= lia3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Local Ltac step ::= step2_fast. Local Ltac stepz ::= stepz_fast.   (* [comment removed for export] *)
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

(* [comment removed for export] *)
Lemma rw_cells_recast : forall m A cs cs', rw_cells psegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells psegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

Lemma rw_cells_C4_eqv : forall m A pre v v' post, rw_cells psegs m A (pre ++ C4 v :: post) -> le4 v = le4 v' -> rw_cells psegs m A (pre ++ C4 v' :: post).
Proof.
  intros m A pre v v' post H E. eapply rw_cells_recast; [exact H| |].
  - destruct H as [[W _] _]. apply cells_wf_app in W. (nelim W 3%nat; intros W1 _ W2). apply cells_wf_app. split; [exact W1|]. split; [exact I| exact W2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite E. reflexivity.
Qed.
(* [comment removed for export] *)
Ltac c4_eqv H k v' :=
  lazymatch type of H with rw_cells _ ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
    let post := eval cbv beta iota delta [skipn] in (skipn (S k) cs) in
    lazymatch eval cbv beta iota delta [nth_error] in (nth_error cs k) with Some (C4 ?v) =>
      let H' := fresh in
      pose proof (rw_cells_C4_eqv m A pre v v' post) as H'; cbn [app] in H';
      specialize (H' H ltac:(unfold le4; cbn [Z_to_le_bytes]; repeat (apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|]); reflexivity)); clear H; rename H' into H
    end end.

(* [comment removed for export] *)
Definition no_s (a : parg) : Prop := match a with PA_s _ => False | _ => True end.
Lemma args_ok_nos : forall Fp B BS Fp' B' BS' m m' lo sp ap lo' sp' ap' ws args,
  Forall no_s args -> args_ok Fp B BS m lo sp ap ws args -> args_ok Fp' B' BS' m' lo' sp' ap' ws args.
Proof.
  intros Fp B BS Fp' B' BS' m m' lo sp ap lo' sp' ap' ws args NS. revert ws.
  induction NS as [|a args Ha _ IH]; intros ws H; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [|apply IH; exact H2]. destruct a; cbn in Ha, H1 |- *; [contradiction|exact H1|exact H1|exact H1].
Qed.

Definition VSN_FRAME : Z := 304.
Definition VSN_DEPTH : Z := 5856.   (* [comment removed for export] *)

Definition vsnprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (D : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ frm0 fc'
    /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells psegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)].

(* [comment removed for export] *)
Definition vsnprintf_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (D n A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
    rw_cells psegs m D [CB dn junkd] ->
    bytes_at psegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    va_area m VA slots -> Forall no_s args -> args_ok 0 0 0 m lo q 0 slots args ->
    printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, o)) ->
    Forall (fun c => let '(y, w, p, fl, t) := c in fmt_fp_facts y fl p t) (fp_calls (length fmt) fmt args) ->
    (length o < dn)%nat -> (zlength o <= n - 1) -> (1 <= n < 2^63) ->
    stk psegs m lo q -> (lo <= q - VSN_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv psegs m -> frm0 fc ->
    (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
    (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
    (D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= VA \/ VA + 8 * zlength slots <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    evt psegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1c738) fc None m (seg_rom psegs)).

Theorem vsnprintf_proof : vsnprintf_stmt.
Proof.
  unfold vsnprintf_stmt. intros until o. cbv zeta.
  intros -> -> -> -> DST BY HF P1 VAA NOS AOK MODEL FPF ROOM Hn Hn1 ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI DD1 DVA GD.
  unfold VSN_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB.
  pose proof (u64s_length slots) as LU. unfold va_area in VAA. unfold zlength in *.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. idtac. fold psegs in SSP1, SSP2.
  pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  carve_frame 304%nat ST.
  do 12 zs.
  zs. zs. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  zs. zs. zs. zs. zs.
  (* [comment removed for export] *)
  replace (n <? n + -1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.add].
  change (Z.land (0 + -1) 18446744073709551615) with 18446744073709551615.
  replace (Z.land 18446744073709551615 (n + -1)) with (n + -1)
    by (rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
  zs. zs. zs. zs. zs.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -304)%Z (CB 232 ?j :: _) |- _ => rename H into FRv; set (j0 := j) in FRv; clearbody j0 end.
  match type of FRv with rw_cells _ _ _ [_; _; _; CB 8 ?j; _; _; _; _; _; _] => set (j8 := j) in FRv; clearbody j8 end.
  apply (proj1 (rw_cells_app psegs _ _ [_] _)) in FRv. destruct FRv as [FZ FRv]. cbn [cells_size csize Nat.add app] in FRv.
  replace (bv_unsigned sp + -304 + Z.of_nat 232)%Z with (bv_unsigned sp + -72)%Z in FRv by lia.
  (* [comment removed for export] *)
  zs. eapply evt_cut.
  { eapply memset_spec; rewrite ?unsigned_lit by lia; [ | eassumption ]. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact FZ. }
  cbv beta. intros ms' P. unfold memset_post in P. rewrite !unsigned_lit in P by lia.
  (nelim P 20%nat; intros x5 x6 x7 b1 b2 b3 b4 b5 b6 b7 x28 x29 x30 x31 m2 -> MUc WMc MI2 FZ').
  clear FZ.
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call psegs mm m2 MUc WMc; clear MUc WMc; try clear MI end.
  fix_ret.
  (* [comment removed for export] *)
  pose proof (rw_cells_recast _ _ _ (gfile_cells (Z_to_bv 64 0) 0 0 0 0 0 0 0 0 0 0 0 (Z_to_bv 64 0) (Z_to_bv 64 0) 0 ++ snfile_rest 0) FZ'
                ltac:(cbn [cells_wf cell_wf gfile_cells snfile_rest app]; repeat split) ltac:(vm_compute; reflexivity)) as FC. clear FZ'.
  unfold gfile_cells, snfile_rest in FC. cbn [app] in FC.
  do 10 zs.
  c4_eqv FC 20%nat (Z_to_bv 64 4294967295). c4_eqv FC 21%nat (Z_to_bv 64 4294967295).
  (* [comment removed for export] *)
  pose proof (rw_CB_length _ _ _ _ DST) as LJ.
  pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DA. clear DST.
  pose proof (u8arr_store_ok psegs _ _ _ 0%Z (Z_to_bv 64 D) DA ltac:(rewrite LJ; lia) ltac:(f_equal; lia)) as SOK.
  zs. rewrite le1_zero. replace (Z_to_bv 64 D) with (wa (D + 0)) by (unfold wa; f_equal; lia).
  pose proof (u8arr_write psegs _ _ _ 0%Z (Z_to_bv 8 0) DA ltac:(rewrite LJ; lia)) as DA2. clear DA. store_done.
  pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DST. rewrite upd_length, LJ in DST. clear DA2.
  zs. zs. zs. zs.
  (* [comment removed for export] *)
  apply (proj1 (rw_cells_app psegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in FC. destruct FC as [FH FR]. cbn [cells_size csize Nat.add app] in FR.
  replace (bv_unsigned sp + -304 + Z.of_nat 148)%Z with (bv_unsigned sp + -304 + 148)%Z in FR by lia.
  apply (proj1 (rw_cells_app psegs _ _ [_;_] _)) in FRv. destruct FRv as [CKC FRv]. cbn [cells_size csize Nat.add app] in FRv.
  replace (bv_unsigned sp + -72 + Z.of_nat 16)%Z with (bv_unsigned sp + -56)%Z in FRv by lia.
  pose proof vfprintf_sn_proof as VF. unfold vfprintf_sn_stmt in VF.
  eapply evt_cut.
  { eapply VF with (Fp := bv_unsigned sp + -304) (CK := bv_unsigned sp + -72) (D := D) (n := n + -1) (bufp := bv_unsigned sp + -49) (A := A) (VA := VA)
                   (dn := dn) (junkd := upd junkd (Z.to_nat 0) (Z_to_bv 8 0)) (fmt := fmt) (slots := slots) (args := args) (lo := lo) (canary := canary) (r := r) (o := o);
      clear VF; rewrite ?unsigned_lit by lia; unfold VF_FRAME, PC_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength.
    all: try reflexivity.
    all: try (arith_goal; lia).
    - unfold snfile_head, gfile_cells. exact FH.
    - unfold snfile_rest. exact FR.
    - exact CKC.
    - exact DST.
    - exact BY.
    - exact HF.
    - exact P1.
    - exact VAA.
    - eapply args_ok_nos; [exact NOS | exact AOK].
    - exact MODEL.
    - exact FPF.
    - exact ST.
    - split; [exact SSP1 | exact SSP2].
    - exact MI2.
    - exact FRM. }
  cbv beta. intros ms' P. clear VF.
  unfold vfprintf_sn_post in P. rewrite !unsigned_lit in P by lia.
  (nelim P 29%nat; intros y5 y6 y7 d1 d2 d3 d4 d5 d6 d7 y28 y29 y30 y31 Ft fc' fjunk m3 -> MUc WMc MI3 FRM' FOK ST3 SSP3 DST3 CK3 FJ3).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call psegs mm m3 MUc WMc; clear MUc WMc; try clear MI2 end.
  fix_ret.
  clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  change psegs with psegs in SSP1, SSP2.
  (* [comment removed for export] *)
  zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
  do 7 zs.
  lazymatch goal with FJ : rw_cells _ ?mm (bv_unsigned sp + -304)%Z _, CK : rw_cells _ ?mm (bv_unsigned sp + -72)%Z _, FR : rw_cells _ ?mm (bv_unsigned sp + -56)%Z _ |- _ =>
    assert (FALL : rw_cells psegs mm (bv_unsigned sp + -304) ([CB 232 fjunk] ++ [C8 (Z_to_bv 64 (D + zlength o)); C8 (Z_to_bv 64 (n + -1 - zlength o))] ++ [CB 8 j8; C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]));
    [ apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [exact FJ|];
      apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact CK | lia] |];
      cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact FR | lia]
    | clear FJ CK FR ] end.
  cbn [app] in FALL.
  release_frame FALL ST3 (bv_unsigned sp).
  apply evt_done. unfold vsnprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
  split; [exact ST3|].
  split; [split; [exact SSP1 | exact SSP2]|].
  rewrite upd_firstn_skipn in DST3 by (rewrite LJ; lia). change (Z.to_nat 0) with 0%nat in DST3.
  change (firstn 0 junkd) with (@nil byte) in DST3. rewrite app_nil_l in DST3.
  change (skipn (S (length o)) (Z_to_bv 8 0 :: skipn 1 junkd)) with (skipn (length o) (skipn 1 junkd)) in DST3.
  rewrite skipn_skipn, Nat.add_1_r in DST3. exact DST3.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vsprintf_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (D A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells psegs m D [CB dn junkd] ->
    bytes_at psegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    va_area m VA slots -> Forall no_s args -> args_ok 0 0 0 m lo q 0 slots args ->
    printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, o)) ->
    Forall (fun c => let '(y, w, p, fl, t) := c in fmt_fp_facts y fl p t) (fp_calls (length fmt) fmt args) ->
    (length o < dn)%nat -> (zlength o <= 2147483646) ->
    stk psegs m lo q -> (lo <= q - VSN_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv psegs m -> frm0 fc ->
    (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
    (q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
    (D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= VA \/ VA + 8 * zlength slots <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    evt psegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1c724) fc None m (seg_rom psegs)).

Theorem vsprintf_proof : vsprintf_stmt.
Proof.
  unfold vsprintf_stmt. intros until o. cbv zeta.
  intros -> -> -> DST BY HF P1 VAA NOS AOK MODEL FPF ROOM Hn ST LO GLO QHI SSP MI FRM HA0 HA QVA VAHI DD1 DVA GD.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  zs. zs. zs. zs. zs.
  pose proof vsnprintf_proof as VS. unfold vsnprintf_stmt in VS. cbv zeta in VS.
  eapply VS; clear VS; first [reflexivity | eassumption | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sprintf_gen_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (A : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in let D := bv_unsigned a0 in
    a1 = Z_to_bv 64 A ->
    rw_cells psegs m D [CB dn junkd] ->
    bytes_at psegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    Forall no_s args -> args_ok 0 0 0 m lo q 0 [a2; a3; a4; a5; a6; a7] args ->
    printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, o)) ->
    Forall (fun c => let '(y, w, p, fl, t) := c in fmt_fp_facts y fl p t) (fp_calls (length fmt) fmt args) ->
    (length o < dn)%nat -> (dn <= 80)%nat ->
    stk psegs m lo q -> (lo <= q - SPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv psegs m -> frm0 fc ->
    (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
    (D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    evt psegs (sprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn o r junkd lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x17978) fc None m (seg_rom psegs)).

Theorem sprintf_gen_proof : sprintf_gen_stmt.
Proof.
  unfold sprintf_gen_stmt. intros until o. cbv zeta.
  intros -> DST BY HF P1 NOS AOK MODEL FPF ROOM Hdn ST LO GLO QHI SSP MI FRM HA0 HA DD1 GD.
  unfold SPRINTF_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (bytes_at_bound _ _ _ _ BY) as AB. pose proof (zb_length fmt) as LZB. rewrite LZB in AB. unfold zlength in *.
  set (D := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 D) by (unfold D; rewrite Z_to_bv_bv_unsigned; reflexivity).
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. idtac. fold psegs in SSP1, SSP2.
  pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  carve_frame 80%nat ST.
  do 17 zs.
  apply (proj1 (rw_cells_app psegs _ _ [_;_;_;_] _)) in FR. destruct FR as [FR VAC]. cbn [cells_size csize Nat.add app] in VAC.
  replace (bv_unsigned sp + -80 + Z.of_nat 32)%Z with (bv_unsigned sp + -48)%Z in VAC by lia.
  pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. cbn [cells_bytes cbytes] in VAA.
  change (le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a2; a3; a4; a5; a6; a7]) in VAA.
  (* [comment removed for export] *)
  pose proof vsprintf_proof as VS. unfold vsprintf_stmt in VS. cbv zeta in VS.
  eapply evt_cut.
  { eapply VS with (D := D) (A := A) (VA := bv_unsigned sp + -48) (dn := dn) (junkd := junkd) (fmt := fmt) (slots := [a2; a3; a4; a5; a6; a7]) (args := args)
                   (lo := lo) (canary := canary) (r := r) (o := o);
      clear VS; rewrite ?unsigned_lit by lia; unfold VSN_DEPTH, GLOBALS_TOP, STATIC_SPLIT, zlength; cbn [length].
    all: try reflexivity.
    all: try (arith_goal; lia).
    all: try eassumption.
    - eapply args_ok_nos; [exact NOS | exact AOK].
    - split; [exact SSP1 | exact SSP2]. }
  cbv beta. intros ms' P.
  unfold vsnprintf_post in P. rewrite !unsigned_lit in P by lia.
  (nelim P 26%nat; intros y5 y6 y7 d1 d2 d3 d4 d5 d6 d7 y28 y29 y30 y31 Ft fc' m3 -> MUc WMc MI3 FRM' FOK ST3 SSP3 DST3).
  lazymatch type of MUc with munch _ ?mm _ => transport_after_call psegs mm m3 MUc WMc; clear MUc WMc; try clear MI end.
  fix_ret.
  clear SSP1 SSP2. destruct SSP3 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
  change psegs with psegs in SSP1, SSP2.
  (* [comment removed for export] *)
  zs. zs. zs. if_cases Kc; zify_cond Kc. { exfalso. clear -Kc. apply Kc. reflexivity. }
  zs. zs. zs. zs.
  lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -80)%Z _, VAC : rw_cells _ ?mm (bv_unsigned sp + -48)%Z _ |- _ =>
    assert (FALL : rw_cells psegs mm (bv_unsigned sp + -80) ([C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 canary; C8 s0; C8 ra] ++ [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]));
    [ apply (proj2 (rw_cells_app psegs _ _ _ _)); split; [exact FR|]; cbn [cells_size csize Nat.add app]; eapply rwc_eq; [exact VAC | lia]
    | clear FR VAC ] end.
  cbn [app] in FALL.
  release_frame FALL ST3 (bv_unsigned sp).
  apply evt_done. unfold sprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
  split; [exact ST3|].
  split; [exact DST3|].
  split; [exact SSP1 | exact SSP2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fmt_bytes_at : forall m A f, mem_inv psegs m -> ro_bytes_b psegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
  bytes_at psegs m A (zb f).
Proof.
  intros m A f MI RB H0 H1.
  pose proof (ro_cells_bytes_at psegs m A _ (ro_cells_image psegs m A (zb f) MI RB H0 ltac:(rewrite zb_length; unfold zlength in H1; lia))) as B.
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.

Theorem sprintf_d_proof : sprintf_d_stmt.
Proof.
  unfold sprintf_d_stmt. intros until r. intros DST Ha1 Ha2 Hi FD ROOM Hn ST LO GLO QHI DD1 GD SSP MI FRM.
  pose proof sprintf_gen_proof as SG. unfold sprintf_gen_stmt in SG. cbv zeta in SG.
  eapply SG with (fmt := FMT_d) (args := [PA_i i]) (A := A_FMT_d); clear SG;
    first [ exact Ha1 | exact DST | exact ST | exact SSP | exact MI | exact FRM
          | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_d; lia | vm_compute; discriminate]
          | unfold FMT_d; forall_range
          | apply pass1_ok_d
          | apply Forall_cons; [exact I | apply Forall_nil]
          | cbn [args_ok arg_ok]; split; [split; [exact Hi | exact Ha2] | exact I]
          | apply printf_sn_d; [exact Hi | exact FD]
          | rewrite fp_calls_d; apply Forall_nil
          | unfold A_FMT_d, STATIC_SPLIT, FMT_d, zlength; cbn; lia
          | lia ].
Qed.

Theorem sprintf_g_proof : forall prec, sprintf_g_stmt prec.
Proof.
  intros prec. unfold sprintf_g_stmt. intros until r. intros RET LEN DST Ha1 Hp FG FACTS ROOM Hn ST LO GLO QHI DD1 GD SSP MI FRM.
  pose proof sprintf_gen_proof as SG. unfold sprintf_gen_stmt in SG. cbv zeta in SG.
  eapply SG with (fmt := if prec =? 15 then FMT_g15 else FMT_g17) (args := [PA_g (bv_unsigned a2)]) (A := if prec =? 15 then A_FMT_g15 else A_FMT_g17); clear SG;
    first [ exact Ha1 | exact DST | exact ST | exact SSP | exact MI | exact FRM
          | destruct Hp as [-> | ->]; cbn [Z.eqb Pos.eqb]; (apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_g15, A_FMT_g17; lia | vm_compute; discriminate])
          | destruct Hp as [-> | ->]; cbn [Z.eqb Pos.eqb]; unfold FMT_g15, FMT_g17; forall_range
          | apply pass1_ok_g
          | apply Forall_cons; [exact I | apply Forall_nil]
          | cbn [args_ok arg_ok]; split; [reflexivity | exact I]
          | apply printf_sn_g; assumption
          | rewrite fp_calls_g by exact Hp; apply Forall_cons; [exact FACTS | apply Forall_nil]
          | destruct Hp as [-> | ->]; cbn [Z.eqb Pos.eqb]; unfold A_FMT_g15, A_FMT_g17, STATIC_SPLIT, FMT_g15, FMT_g17, zlength; cbn; lia
          | lia ].
Qed.

Theorem sprintf_u04x_proof : sprintf_u04x_stmt.
Proof.
  unfold sprintf_u04x_stmt. intros until c. intros DST Ha1 Ha2 Hc Hn6 Hn ST LO GLO QHI DD1 GD SSP MI FRM.
  pose proof sprintf_gen_proof as SG. unfold sprintf_gen_stmt in SG. cbv zeta in SG.
  eapply SG with (fmt := FMT_u04x) (args := [PA_u c]) (A := A_FMT_u04x); clear SG;
    first [ exact Ha1 | exact DST | exact ST | exact SSP | exact MI | exact FRM
          | apply fmt_bytes_at; [exact MI | vm_compute; reflexivity | unfold A_FMT_u04x; lia | vm_compute; discriminate]
          | unfold FMT_u04x; forall_range
          | apply pass1_ok_u04x
          | apply Forall_cons; [exact I | apply Forall_nil]
          | cbn [args_ok arg_ok]; split; [split; [lia | exact Ha2] | exact I]
          | apply printf_sn_u04x; exact Hc
          | rewrite fp_calls_u04x; apply Forall_nil
          | unfold A_FMT_u04x, STATIC_SPLIT, FMT_u04x, zlength; cbn; lia
          | unfold hex4_lower; cbn [length]; lia
          | lia ].
Qed.
