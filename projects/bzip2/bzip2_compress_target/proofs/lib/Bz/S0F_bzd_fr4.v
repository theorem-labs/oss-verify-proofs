(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0 StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzDefs BzInv BzTables BzLemmasT BzLemmasMtf BzWalkArith S0_bzd_out BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp DecCutF DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_out.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_vspec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_fr1 S0F_bzd_fr2 S0F_bzd_fr3.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Ltac unhide_disj := repeat match goal with H : id (?A \/ ?B) |- _ => unfold id in H end.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.

(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast RelLiaA SasFastF RelLiaS.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac tlia ::= RelLiaS.tlia_bzd_r.
Local Ltac BzSepTac.tlia1 ::= RelLiaS.tlia1_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section FR.
  Variable c : foctx.
  Notation cx := (o_cx c). Notation J := (o_J c). Notation d0 := (o_d c). Notation s0 := (o_s c).
  Notation S := (b_s (o_cx c)). Notation STRM := (b_strm (o_cx c)). Notation DST := (b_dst (o_cx c)). Notation dlen := (b_dlen (o_cx c)).
  Notation n := (b_n (o_cx c)). Notation TT := (b_tt (o_cx c)).
  Notation snb := (sv_nblock (d_sv (o_d c))). Notation av0 := (s_avail_out (o_s c)). Notation PP := (sv_nblock (d_sv (o_d c)) + 1)%Z.
  Notation cap := (100000 * b_n (o_cx c))%Z.
  Notation F := (o_F c). Notation fc := (o_fc c). Notation KQ := (o_KQ c). Notation m0 := (o_m0 c).
  Notation RO := (FROf c). Notation WB := (FWB c).
  Notation RR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 :=
    (mkR ra (o_SP c) (o_gp c) (o_tp c) t0 t1 t2 (Z_to_bv 64 (b_s (o_cx c))) (o_s1v c) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (b_s (o_cx c) + 2047)) (Z_to_bv 64 (b_s (o_cx c) + 1096))
         (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 100000) (Z_to_bv 64 (b_s (o_cx c) + 64080)) s8 s9 (Z_to_bv 64 4) (Z_to_bv 64 10) t3 t4 t5 t6) (only parsing).
  Notation csnb := (Z_to_bv 64 snb). Notation cnn := (Z_to_bv 64 (n * 100000)). Notation cstrm := (Z_to_bv 64 STRM).
  Notation c14 := (Z_to_bv 64 14). Notation c3 := (Z_to_bv 64 3). Notation cm4 := (Z_to_bv 64 (-4)).
  (* [comment removed for export] *)
  Notation D8 oc ol nu k0 tp rn rt cb := (set8 (o_d c) oc ol nu k0 tp rn rt cb).
  Notation S3 out av tout := (smod (o_s c) out av tout).
  Notation JJ tol toh := (jk_set_o (o_J c) tol toh).
  Hypothesis OK : foctx_ok c. Hypothesis OKF : foctx_okF c.
  Hypothesis RD1 : d_rand (o_d c) = 1%Z.
  Hypothesis KJ : FKjoin c (FROf c).
  Hypothesis KE : FKexit c (FROf c).

  (* [comment removed for export] *)
  Notation finv := (S0F_bzd_fr1.finv c).
  Notation OUTS := (S0F_bzd_fr1.OUTS c). Notation HS := (S0F_bzd_fr1.HS c). Notation GS := (S0F_bzd_fr1.GS c).
  Notation MSx := (S0F_bzd_fr1.MSx c).
  Notation R1S := (S0F_bzd_fr1.R1S c). Notation R2S := (S0F_bzd_fr1.R2S c). Notation R3S := (S0F_bzd_fr1.R3S c).
  Notation R4S := (S0F_bzd_fr1.R4S c). Notation R5S := (S0F_bzd_fr1.R5S c).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac unRO H := let GOT := ident:(GOT) in cps_destruct H as (SAV & TTA & CRC & RNA & GOT & MI); unfold FGOT in GOT.
  Ltac unDS H := cps_destruct H as (HD & NBU & MID & SM).
  Ltac prep :=
    let JWF := ident:(JWF) in let ENT := ident:(ENT) in let OK' := fresh "OK" in pose proof OK as OK';
    cps_destruct OK' as (HS & HSTRM & HDST & Hdlen & SEP_SD & IAS & IAD & JWF & ENT);
    let OKF' := fresh "OKF" in pose proof OKF as OKF';
    cps_destruct OKF' as (HSM & HTT & SEP_ST & SEP_DT);
    cps_destruct ENT as (En & Rn & Esm & Rsnb & Rsnb1 & Rav0 & Lout0 & Eol0 & RtP0 & NK0 & Rcb0 & Roc0 & Rr01 & Rrnd & Rcf & Rtt & Rl16 & Rl4);
    cps_destruct JWF as (Lp1 & Lp2 & Lp3 & Ls1 & Ls2 & Lq1 & Lq2);
    unfold FWB in *; pose proof alloc_ceiling_range as ACR;
    pose proof (zw32_length (d_tt d0) cap ltac:(lia)) as TTL; pose proof rnums_words_length as RNL; pose proof crc_words_length as CRCL; hide_disj.
  Ltac unFI H := cps_destruct H as (Ioc & Iol & Inu & Ik0 & Itp & Irn & Irt & Icb & Iav).
  Ltac ro_close := unfold FROf, FGOT; repeat match goal with |- _ /\ _ => split end; assumption.
  Ltac dsg_close HD NBU MID SM := unfold DSg; focbn; repeat match goal with |- _ /\ _ => split end; [exact_cells HD| exact_cells NBU| exact_cells MID| exact_cells SM].
  Ltac destg_close DSTA DL Edb Lout := unfold DESTg; focbn; repeat match goal with |- _ /\ _ => split end; [exact DSTA| exact DL| exact Edb| exact Lout].
  (* [comment removed for export] *)
  Ltac goJ HD NBU MID SM DSTA DL Edb Lout MU WM :=
    eapply KJ; [dsg_close HD NBU MID SM| destg_close DSTA DL Edb Lout| ro_close| exact MU| exact WM
               | unfold ojoin; focbn; repeat match goal with |- _ /\ _ => split end].
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac cs_split cs w := lazymatch cs with | C4 w :: ?post => constr:((@nil cell, post)) | ?c1 :: ?cs' => let r := cs_split cs' w in lazymatch r with (?pre, ?post) => constr:((c1 :: pre, post)) end end.
  Ltac recell H w v := lazymatch type of H with rw_cells ?sg ?mm ?A ?cs => let r := cs_split cs w in lazymatch r with (?pre, ?post) => apply (C4_recell sg mm A pre w v post) in H; [ cbn [app] in H | ] end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fr_OUT : forall f, GS f -> OUTS f.
  Proof using ACEIL__ c OK OKF RD1 KJ.
    intros f G. unfold S0F_bzd_fr1.OUTS. intros until m. intros oc ol.
    remember (Z.to_nat ol) as cnt eqn:Hcnt. revert ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m oc ol Hcnt.
    induction cnt as [cnt IH] using lt_wf_ind.
    intros until rest. intros DSm DE ROm MU WM FI Hf Hol Hav1.
    unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & Lout). prep. unFI FI.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in Lout. focbn_in Edb.
    rewrite K_PH_step by (g8; lia). cbv zeta. g8.
    wstep.
    cbv beta. rewrite (byte_lit_unsigned oc) by lia.
    wstep.
    pose proof (u8arr_store_ok s0segs _ DST _ (dlen - av) _ DSTA ltac:(lia) eq_refl) as SOK.
    step.
    rewrite BzInv.le1_lit.
    pose proof (u8arr_write s0segs _ DST _ (dlen - av) (Z_to_bv 8 oc) DSTA ltac:(lia)) as DSTB.
    clear DSTA. store_done. try clear SOK. rename DSTB into DSTA.
    pose proof DL as DL'. rewrite <- (upd_length dbytes (Z.to_nat (dlen - av)) (Z_to_bv 8 oc)) in DL'. clear DL.
    destruct rest as [|r0 rest']. { exfalso. pose proof (f_equal (@length byte) Edb) as X. rewrite length_app, length_map, length_rev in X. cbn [length] in X. clear -X DL' Lout Hav1. rewrite upd_length in DL'. lia. }
    rewrite Edb in DSTA. replace (Z.to_nat (dlen - av)) with (length out) in DSTA by (clear -Lout; lia).
    rewrite (dest_snoc out (r0 :: rest') oc r0 rest' eq_refl) in DSTA.
    remember (upd dbytes (Z.to_nat (dlen - av)) (Z_to_bv 8 oc)) as dbytes' eqn:Xdb.
    assert (Edb' : dbytes' = map (Z_to_bv 8) (rev (oc :: out)) ++ rest') by (rewrite Xdb, Edb; replace (Z.to_nat (dlen - av)) with (length out) by (clear -Lout; lia); apply (dest_snoc out (r0 :: rest') oc r0 rest' eq_refl)).
    rewrite <- Edb' in DSTA. clear Xdb Edb. rename Edb' into Edb. rename DL' into DL.
    assert (Lout' : Z.of_nat (length (oc :: out)) = (dlen - (av - 1))%Z) by (cbn [length]; clear -Lout; lia). clear Lout. rename Lout' into Lout.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    rewrite (sx32_mod32 cb) by lia.
    pose proof (crc_idx_byte cb oc ltac:(lia) ltac:(lia)) as Hidx.
    pose proof (u32arr_read s0segs _ 169656 crc_words (Z.lxor (cb / 16777216) oc) _ _ CRC (crc_words_nth _ Hidx) ltac:(lia) eq_refl) as RD.
    wstep.
    clear RD.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    pose proof (crc_update_range cb oc ltac:(lia)) as Rcb'.
    lazymatch type of MID with context [C4 (Z_to_bv 64 (Z.lxor ?a ?b))] => recell MID (Z_to_bv 64 (Z.lxor a b)) (crc_update cb oc) end.
    2:{ rewrite (Z.mod_small (crc_update cb oc) 4294967296) by exact Rcb'. apply crc_step_rel; [apply sx32_mod32; lia| lia| lia]. }
    set (cb' := crc_update cb oc) in *.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    if_cases Kt; [clear Kt| clear Kt].
    all: cycle 1.
    all: wstep.
    1: wstep.
    1: wstep.
    1: wstep.
    all: if_cases K1; zify_cond K1.
    1,3: replace (av - 1 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; clear -K1; lia).
    1,2: goJ HD NBU MID SM DSTA DL Edb Lout MU WM.
    all: try (unfold id in Ik0; clear -Ioc Iol Inu Ik0 Itp Irn Irt Icb Iav Rrnd K1 Rsnb Rcb' Hol Hav1; first [lia | intros; lia]).
    all: replace (av - 1 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; clear -K1; lia).
    all: wstep.
    all: wstep; if_cases K2; zify_cond K2.
    1,3: eapply (IH (Z.to_nat (ol - 1)) ltac:(clear -Hol Hcnt; lia) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ oc (ol - 1)%Z eq_refl nu k0 tp rn rt cb' (oc :: out) (av - 1)%Z (tout + 1)%Z _ _ _ rest'); [dsg_close HD NBU MID SM| destg_close DSTA DL Edb Lout| ro_close| exact MU| exact WM| | exact Hf| clear -Hol K2; lia| clear -Hav1 K1; lia].
    1,2: unfold S0F_bzd_fr1.finv; clear -Ioc Iol Inu Ik0 Itp Irn Irt Icb Iav Rcb' Hol Hav1; repeat match goal with |- _ /\ _ => split end; lia.
    all: replace (ol - 1)%Z with 0%Z by (clear -K2; lia).
    all: rewrite K_PH_0 by (g8; reflexivity).
    all: unfold S0F_bzd_fr1.GS in G.
    all: eapply (G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ oc nu k0 tp rn rt cb' (oc :: out) (av - 1)%Z (tout + 1)%Z _ _ _ rest'); [dsg_close HD NBU MID SM| destg_close DSTA DL Edb Lout| ro_close| exact MU| exact WM| | exact Hf| clear -Hav1 K1; lia].
    all: unfold S0F_bzd_fr1.finv; clear -Ioc Iol Inu Ik0 Itp Irn Irt Icb Iav Rcb' Hol Hav1; repeat match goal with |- _ /\ _ => split end; lia.
    Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fr_M : forall f, OUTS f -> MSx f.
  Proof.
    intros f O. unfold S0F_bzd_fr1.MSx. intros until rest. intros DSm DE ROm MU WM FI Hf Hol Hk0.
    unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & Lout). prep. unFI FI.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in Lout.
    rewrite K_PM_eq. g8.
    wstep.
    wstep.
    if_cases K1; zify_cond K1.
    { replace (av =? 0)%Z with true by (symmetry; apply Z.eqb_eq; clear -K1; lia). goJ HD NBU MID SM DSTA DL Edb Lout MU WM. all: unfold id in Ik0; clear -Ioc Iol Inu Ik0 Itp Irn Irt Icb Iav Rrnd K1 Rsnb Hol; first [lia | intros; lia]. }
    replace (av =? 0)%Z with false by (symmetry; apply Z.eqb_neq; clear -K1; lia).
    unfold S0F_bzd_fr1.OUTS in O.
    eapply (O _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest); [dsg_close HD NBU MID SM| destg_close DSTA DL Edb Lout| ro_close| exact MU| exact WM| | exact Hf| exact Hol| clear -Iav K1; lia].
    unfold S0F_bzd_fr1.finv; clear -Ioc Iol Inu Ik0 Itp Irn Irt Icb Iav; repeat match goal with |- _ /\ _ => split end; lia.
  Time Qed.
  Lemma fr_H : forall f, OUTS f -> GS f -> HS f.
  Proof.
    intros f O G. unfold S0F_bzd_fr1.HS. intros until rest. intros DSm DE ROm MU WM FI Hf Hav1.
    unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & Lout). prep. unFI FI.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in Lout.
    wstep.
    if_cases K1; zify_cond K1.
    { unfold S0F_bzd_fr1.OUTS in O. eapply (O _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest); [dsg_close HD NBU MID SM| destg_close DSTA DL Edb Lout| ro_close| exact MU| exact WM| | exact Hf| clear -Iol K1; lia| exact Hav1].
    unfold S0F_bzd_fr1.finv; clear -Ioc Iol Inu Ik0 Itp Irn Irt Icb Iav; repeat match goal with |- _ /\ _ => split end; lia. }
    assert (E0 : ol = 0%Z) by (clear -K1 Iol; lia). subst ol.
    rewrite K_PH_0 by (g8; reflexivity).
    unfold S0F_bzd_fr1.GS in G. eapply (G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ oc nu k0 tp rn rt cb out av tout tol toh dbytes rest); [dsg_close HD NBU MID SM| destg_close DSTA DL Edb Lout| ro_close| exact MU| exact WM| | exact Hf| exact Hav1].
    unfold S0F_bzd_fr1.finv; clear -Ioc Inu Ik0 Itp Irn Irt Icb Iav; repeat match goal with |- _ /\ _ => split end; lia.
  Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let fr_G1 := S0F_bzd_fr1.fr_G1 c OK OKF RD1 KJ KE.
  Let fr_L1 := S0F_bzd_fr2.fr_L1 c OK OKF RD1 KE.
  Let fr_L2 := S0F_bzd_fr2.fr_L2 c OK OKF RD1 KE.
  Let fr_L3 := S0F_bzd_fr3.fr_L3 c OK OKF RD1 KE.
  Let fr_L4 := S0F_bzd_fr3.fr_L4 c OK OKF RD1 KE.
  Let fr_L5 := S0F_bzd_fr3.fr_L5 c OK OKF.
  Lemma fr_knot : forall f, MSx f /\ HS f /\ GS f /\ OUTS f.
  Proof.
    induction f as [|f IH].
    all: match goal with |- MSx ?g /\ _ => assert (IHM : forall f', g = Datatypes.S f' -> MSx f') by (intros f' E; first [discriminate E | injection E as <-; exact (proj1 IH)]) end.
    all: match goal with |- MSx ?g /\ _ => pose proof (fr_G1 g (fr_L1 g (fr_L2 g (fr_L3 g (fr_L4 g (fr_L5 g IHM)) IHM) IHM) IHM)) as G; pose proof (fr_OUT g G) as O; split; [exact (fr_M g O)| split; [exact (fr_H g O G)| split; [exact G| exact O]]] end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem S0F_fastr0 : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (dbytes rest : list byte),
    DSg c m J d0 s0 -> DESTg c m s0 dbytes rest -> RO m -> munch WB m0 m -> wmono s0segs m0 m ->
    evt s0segs (KQ (unRLE d0 s0)) (MS (RR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 c14 c3 t3 t4 t5 t6) F (Z_to_bv 64 0x14b04) fc None m (seg_rom s0segs)).
  Proof.
    intros until rest. intros DSm DE ROm MU WM. unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & Lout). prep.
    rewrite (unRLE_plain d0 s0 (Z.to_nat (PP + 2 - d_nused d0))); [| rewrite RD1; destruct (smallb d0); reflexivity | unfold id in NK0; clear -NK0 Rsnb; lia].
    cps_destruct (fr_knot (Z.to_nat (PP + 2 - d_nused d0))) as (_ & Hh & _ & _).
    remember (Z.to_nat (PP + 2 - d_nused d0)) as f eqn:Hf.
    unfold DSg in *. dvF_cbn_in HD. dvF_cbn_in MID. dvF_cbn_in SM.
    rewrite K_PM_eq.
    wstep.
    wstep.
    wstep.
    if_cases K1; zify_cond K1.
    { replace (av0 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; clear -K1; lia). rewrite <- (set8_id d0), <- (smod_id s0). rewrite <- (jk_set_o_id J) in HD, SM. goJ HD NBU MID SM DSTA DL Edb Lout MU WM. all: unfold id in NK0; clear -Roc0 Eol0 NK0 RtP0 Rrnd Rr01 Rcb0 Rav0 Rsnb En K1; first [lia | intros; lia]. }
    replace (av0 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; clear -K1; lia).
    wstep.
    rewrite <- (set8_id d0), <- (smod_id s0). rewrite <- (jk_set_o_id J) in HD, SM.
    unfold S0F_bzd_fr1.HS in Hh.
    eapply (Hh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (d_out_ch d0) (d_out_len d0) (d_nused d0) (d_k0 d0) (d_tPos d0) (d_rNToGo d0) (d_rTPos d0) (d_cbcrc d0) (s_out s0) av0 (s_tout s0) (j_tol J) (j_toh J) dbytes rest); [dsg_close HD NBU MID SM| destg_close DSTA DL Edb Lout| ro_close| exact MU| exact WM| | subst f; clear -NK0 Rsnb; unfold id in NK0; lia| clear -K1 Rav0; lia].
    unfold S0F_bzd_fr1.finv. unfold id in NK0. destruct (Rrnd RD1) as [RrN RrT]. clear -Roc0 Eol0 NK0 RtP0 RrN RrT Rcb0 Rav0 Rsnb En. rewrite <- En. repeat match goal with |- _ /\ _ => split end; lia.
    Time Qed.
End FR.

Theorem FASTR_ok : FASTR_spec.
Proof.
  intros c OK OKF KJ KE. intros until rest. intros DSm DE ROm MU WM RD1.
  exact (S0F_fastr0 c OK OKF RD1 KJ KE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m dbytes rest DSm DE ROm MU WM).
Qed.
End ACeilS1.
