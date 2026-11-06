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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_fr1 S0F_bzd_fr2.
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
Lemma PG5b_k0 : forall f k5 d oc ol nu ka kb tp rn rt cb s,
  PG5b f k5 (set8 d oc ol nu ka tp rn rt cb) s = PG5b f k5 (set8 d oc ol nu kb tp rn rt cb) s.
Proof. intros; unfold PG5b; g8; reflexivity. Qed.

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
  Ltac goE HD NBU MID SM DSTA DL Edb Lout MU WM :=
    eapply KE; [dsg_close HD NBU MID SM| destg_close DSTA DL Edb Lout| ro_close| exact MU| exact WM
               | unfold oexit; focbn].
  (* [comment removed for export] *)
  Ltac tt_load i :=
    lazymatch goal with TTA : u32arr _ ?mm TT _ |- _ =>
      let RD := fresh "RD" in
      pose proof (zw32_read s0segs mm TT (d_tt d0) cap i _ TTA ltac:(lia) eq_refl) as RD; wstep; clear RD end.
  (* [comment removed for export] *)
  Ltac rn_load i :=
    lazymatch goal with RNA : u32arr _ ?mm 0x29ab8 rnums_words |- _ =>
      let RD := fresh "RD" in
      pose proof (u32arr_read s0segs mm 0x29ab8 rnums_words i (Z_to_bv 64 (rNums i)) _ RNA (rnums_words_nth i ltac:(lia)) ltac:(lia) eq_refl) as RD;
      wstep; clear RD; rewrite ?(sx32_of_Z (rNums i)) by lia end.

  (* [comment removed for export] *)
  Ltac goM IHM oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest HD NBU MID SM DSTA DL Edb Lout MU WM :=
    unfold S0F_bzd_fr1.MSx in IHM;
    eapply (IHM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ oc ol nu k0 tp rn rt cb out av tout tol toh dbytes rest);
    [ dsg_close HD NBU MID SM | destg_close DSTA DL Edb Lout | ro_close | exact MU | exact WM | | | | ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fr_L3 : forall f, R4S f -> (forall f', f = Datatypes.S f' -> MSx f') -> R3S f.
  Proof.
    intros f R4 IHM. unfold S0F_bzd_fr1.R3S. intros until rest. intros DSm DE ROm MU WM FI Hf Hav1 Hk0 Hnu Rw1 RrN1.
    unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & Lout). prep. unFI FI.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in Lout.
    destruct f as [|f']; [exfalso; clear -Hf Hnu; cbn in Hf; lia|].
    specialize (IHM f' eq_refl). rewrite Nat2Z.inj_succ in Hf.
    rewrite PG3b_eq. cbv zeta. g8.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    if_cases K1; zify_cond K1.
    { replace (nu + 3 =? PP)%Z with true by (symmetry; apply Z.eqb_eq; clear -K1; lia).
    goM IHM k0 3%Z (nu + 3)%Z k0 (w / 256)%Z (rN1 - 1)%Z rt cb out av tout tol toh dbytes rest HD NBU MID SM DSTA DL Edb Lout MU WM.
    - unfold S0F_bzd_fr1.finv. clear -Ioc Iol Inu Hk0 Itp Irn Irt Icb Iav Rw1 RrN1 Hnu. repeat match goal with |- _ /\ _ => split end; lia.
    - clear -Hf. lia.
    - lia.
    - exact Hk0. }
    replace (nu + 3 =? PP)%Z with false by (symmetry; apply Z.eqb_neq; clear -K1; lia).
    wstep.
    wstep.
    wstep.
    wstep.
    rewrite (mask_b2z rN1 RrN1).
    set (k3 := Z.lxor (Z.land w 255) (if (rN1 - 1 =? 1)%Z then 1%Z else 0%Z)) in *.
    pose proof (mask_byte w rN1) as Rk3. fold k3 in Rk3.
    wstep.
    if_cases K2; zify_cond K2.
    { replace (k3 =? k0)%Z with false by (symmetry; apply Z.eqb_neq; exact K2). cbn [negb].
    wstep.
    wstep.
    goM IHM k0 3%Z (nu + 3)%Z k3 (w / 256)%Z (rN1 - 1)%Z rt cb out av tout tol toh dbytes rest HD NBU MID SM DSTA DL Edb Lout MU WM.
    - unfold S0F_bzd_fr1.finv. clear -Ioc Iol Inu Hk0 Itp Irn Irt Icb Iav Rw1 RrN1 Hnu Rk3. repeat match goal with |- _ /\ _ => split end; lia.
    - clear -Hf. lia.
    - lia.
    - exact Rk3. }
    replace (k3 =? k0)%Z with true by (symmetry; apply Z.eqb_eq; clear -K2; lia). cbn [negb].
    wstep.
    if_cases K3; zify_cond K3.
    { rewrite PG4_None by (apply get_sym_None; g8; unfold blk_cap; rewrite En; clear -K3 Rn; lia). goE HD NBU MID SM DSTA DL Edb Lout MU WM. clear -Inu Iav; lia. }
    eassert (GS4 : get_sym (D8 k0 3 (nu + 3) k0 (w / 256) (rN1 - 1) rt cb) = Some _).
    { apply get_sym_FR; g8; [unfold blk_cap; rewrite En; clear -K3 Rn; lia | rewrite Esm; exact HSM | rewrite RD1; lia]. }
    rewrite (PG4_b _ _ _ _ _ GS4). clear GS4. g8.
    wstep.
    wstep.
    tt_load (w / 256)%Z.
    pose proof (Rtt (w / 256)%Z) as Rw4. set (w4 := zget (d_tt d0) (w / 256)) in *.
    wstep.
    wstep.
    wstep.
    if_cases K4; zify_cond K4.
    { rewrite (rNn_nz (rN1 - 1) rt K4), (rTn_nz (rN1 - 1) rt K4).
    unfold S0F_bzd_fr1.R4S in R4.
    eapply (R4 ra _ _ _ _ t4 t5 t6 _ nu k0 (rN1 - 1)%Z rt cb out av tout tol toh w4 (rN1 - 1)%Z dbytes rest).
    - dsg_close HD NBU MID SM.
    - destg_close DSTA DL Edb Lout.
    - ro_close.
    - exact MU.
    - exact WM.
    - unfold S0F_bzd_fr1.finv. clear -Ioc Iol Inu Hk0 Itp Irn Irt Icb Iav Rw4 RrN1 Hnu. repeat match goal with |- _ /\ _ => split end; lia.
    - clear -Hf. lia.
    - exact Hav1.
    - exact Hk0.
    - clear -Hnu K1. lia.
    - exact Rw4.
    - clear -RrN1 K4. lia. }
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    rn_load rt.
    pose proof (rNums_range rt ltac:(clear -Irt; lia)) as RNR.
    wstep.
    wstep.
    wstep.
    rewrite (rtpos_wrap rt) by (clear -Irt; lia).
    wstep.
    pose proof (Z.mod_pos_bound (rt + 1) 512 ltac:(lia)) as RT'.
    assert (Ez : (rN1 - 1 = 0)%Z) by (clear -K4; lia).
    rewrite Ez. rewrite rNn_z, (rTn_z rt) by (clear -Irt; lia).
    unfold S0F_bzd_fr1.R4S in R4.
    eapply (R4 ra _ _ _ _ t4 t5 t6 _ nu k0 (rN1 - 1)%Z ((rt + 1) mod 512)%Z cb out av tout tol toh w4 (rNums rt) dbytes rest).
    - dsg_close HD NBU MID SM.
    - destg_close DSTA DL Edb Lout.
    - ro_close.
    - exact MU.
    - exact WM.
    - unfold S0F_bzd_fr1.finv. clear -Ioc Iol Inu Hk0 Itp Irn Irt Icb Iav Rw4 RrN1 Hnu RT'. repeat match goal with |- _ /\ _ => split end; lia.
    - clear -Hf. lia.
    - exact Hav1.
    - exact Hk0.
    - clear -Hnu K1. lia.
    - exact Rw4.
    - clear -RNR. lia.
    Time Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fr_L4 : forall f, R5S f -> R4S f.
  Proof.
    intros f R5. unfold S0F_bzd_fr1.R4S. intros until rest. intros DSm DE ROm MU WM FI Hf Hav1 Hk0 Hnu Rw1 RrN1.
    unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & Lout). prep. unFI FI.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in Lout.
    unfold PG4b. g8.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    rewrite (mask_b2z rN1 RrN1).
    set (k4 := Z.lxor (Z.land w 255) (if (rN1 - 1 =? 1)%Z then 1%Z else 0%Z)) in *.
    pose proof (mask_byte w rN1) as Rk4. fold k4 in Rk4.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    if_cases K3; zify_cond K3.
    { rewrite PG5_None by (apply get_sym_None; g8; unfold blk_cap; rewrite En; clear -K3 Rn; lia). goE HD NBU MID SM DSTA DL Edb Lout MU WM. clear -Inu Iav; lia. }
    eassert (GS5 : get_sym (D8 k0 (k4 + 4) (nu + 4) k0 (w / 256) (rN1 - 1) rt cb) = Some _).
    { apply get_sym_FR; g8; [unfold blk_cap; rewrite En; clear -K3 Rn; lia | rewrite Esm; exact HSM | rewrite RD1; lia]. }
    rewrite (PG5_b _ _ _ _ _ GS5). clear GS5. g8.
    wstep.
    wstep.
    tt_load (w / 256)%Z.
    pose proof (Rtt (w / 256)%Z) as Rw5. set (w5 := zget (d_tt d0) (w / 256)) in *.
    wstep.
    wstep.
    rewrite (sx32_mod32 w5) by lia.
    rewrite (sx32_land255 w5) by lia.
    wstep.
    wstep.
    wstep.
    if_cases K4; zify_cond K4.
    { rewrite (rNn_nz (rN1 - 1) rt K4), (rTn_nz (rN1 - 1) rt K4).
    rewrite (PG5b_k0 _ _ _ _ _ _ k0 (Z.land w5 255)).
    unfold S0F_bzd_fr1.R5S in R5.
    eapply (R5 ra _ _ _ _ _ _ _ _ t4 t5 t6 _ k0 (k4 + 4)%Z nu (rN1 - 1)%Z rt cb out av tout tol toh w5 (rN1 - 1)%Z dbytes rest).
    - dsg_close HD NBU MID SM.
    - destg_close DSTA DL Edb Lout.
    - ro_close.
    - exact MU.
    - exact WM.
    - unfold S0F_bzd_fr1.finv. pose proof (BzWalkArith.land255_range w5) as R5b. clear -Ioc Iol Inu Hk0 Itp Irn Irt Icb Iav Rw5 RrN1 Hnu Rk4 R5b. repeat match goal with |- _ /\ _ => split end; lia.
    - clear -Hf. lia.
    - exact Hav1.
    - clear -Hnu. lia.
    - exact Rw5.
    - clear -RrN1 K4. lia.
    - clear -Rk4. lia. }
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    rn_load rt.
    pose proof (rNums_range rt ltac:(clear -Irt; lia)) as RNR.
    wstep.
    wstep.
    wstep.
    rewrite (rtpos_wrap rt) by (clear -Irt; lia).
    wstep.
    pose proof (Z.mod_pos_bound (rt + 1) 512 ltac:(lia)) as RT'.
    assert (Ez : (rN1 - 1 = 0)%Z) by (clear -K4; lia).
    rewrite Ez. rewrite rNn_z, (rTn_z rt) by (clear -Irt; lia).
    rewrite (PG5b_k0 _ _ _ _ _ _ k0 (Z.land w5 255)).
    unfold S0F_bzd_fr1.R5S in R5.
    eapply (R5 ra _ _ _ _ _ _ _ _ t4 t5 t6 _ k0 (k4 + 4)%Z nu (rN1 - 1)%Z ((rt + 1) mod 512)%Z cb out av tout tol toh w5 (rNums rt) dbytes rest).
    - dsg_close HD NBU MID SM.
    - destg_close DSTA DL Edb Lout.
    - ro_close.
    - exact MU.
    - exact WM.
    - unfold S0F_bzd_fr1.finv. pose proof (BzWalkArith.land255_range w5) as R5b. clear -Ioc Iol Inu Hk0 Itp Irn Irt Icb Iav Rw5 RrN1 Hnu Rk4 R5b RT'. repeat match goal with |- _ /\ _ => split end; lia.
    - clear -Hf. lia.
    - exact Hav1.
    - clear -Hnu. lia.
    - exact Rw5.
    - clear -RNR. lia.
    - clear -Rk4. lia.
    Time Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fr_L5 : forall f, (forall f', f = Datatypes.S f' -> MSx f') -> R5S f.
  Proof.
    intros f IHM. unfold S0F_bzd_fr1.R5S. intros until rest. intros DSm DE ROm MU WM FI Hf Hav1 Hnu Rw1 RrN1 Hol.
    unDS DSm. unRO ROm. cps_destruct DE as (DSTA & DL & Edb & Lout). prep. unFI FI.
    unfold DSg in *. focbn_in HD. focbn_in NBU. focbn_in MID. focbn_in SM. focbn_in Lout.
    destruct f as [|f']; [exfalso; clear -Hf Hnu; cbn in Hf; lia|].
    specialize (IHM f' eq_refl). rewrite Nat2Z.inj_succ in Hf.
    rewrite PG5b_eq. g8.
    wstep.
    wstep.
    wstep.
    wstep.
    rewrite (mask_b2z rN1 RrN1).
    set (k5 := Z.lxor (Z.land w 255) (if (rN1 - 1 =? 1)%Z then 1%Z else 0%Z)) in *.
    pose proof (mask_byte w rN1) as Rk5. fold k5 in Rk5.
    wstep.
    wstep.
    wstep.
    wstep.
    wstep.
    goM IHM oc ol (nu + 5)%Z k5 (w / 256)%Z (rN1 - 1)%Z rt cb out av tout tol toh dbytes rest HD NBU MID SM DSTA DL Edb Lout MU WM.
    - unfold S0F_bzd_fr1.finv. clear -Ioc Iol Inu Ik0 Itp Irn Irt Icb Iav Rw1 RrN1 Hnu Rk5. repeat match goal with |- _ /\ _ => split end; try lia.
    - clear -Hf. lia.
    - clear -Hol. lia.
    - exact Rk5.
    Time Qed.
End FR.
End ACeilS1.
