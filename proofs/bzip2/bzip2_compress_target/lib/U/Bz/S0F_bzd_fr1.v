(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzDefs BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzLemmasT BzLemmasMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzWalkArith S0_bzd_out. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzSepTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0F_bzd_out.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Ltac unhide_disj := repeat match goal with H : id (?A \/ ?B) |- _ => unfold id in H end.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLiaS.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac tlia ::= RelLiaS.tlia_bzd_r.
Local Ltac BzSepTac.tlia1 ::= RelLiaS.tlia1_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section Set8.
  Variables (d : dst) (s : dstrm) (oc ol nu k0 tp rn rt cb : Z) (out : list Z) (av tout : Z).
  Notation D := (set8 d oc ol nu k0 tp rn rt cb).
  Lemma set8_out_ch : forall v, d_set_out_ch D v = set8 d v ol nu k0 tp rn rt cb. Proof. intros; destruct d; cbv; reflexivity. Qed.
  Lemma set8_out_len : forall v, d_set_out_len D v = set8 d oc v nu k0 tp rn rt cb. Proof. intros; destruct d; cbv; reflexivity. Qed.
  Lemma set8_nused : forall v, d_set_nused D v = set8 d oc ol v k0 tp rn rt cb. Proof. intros; destruct d; cbv; reflexivity. Qed.
  Lemma set8_k0 : forall v, d_set_k0 D v = set8 d oc ol nu v tp rn rt cb. Proof. intros; destruct d; cbv; reflexivity. Qed.
  Lemma set8_tPos : forall v, d_set_tPos D v = set8 d oc ol nu k0 v rn rt cb. Proof. intros; destruct d; cbv; reflexivity. Qed.
  Lemma set8_rNToGo : forall v, d_set_rNToGo D v = set8 d oc ol nu k0 tp v rt cb. Proof. intros; destruct d; cbv; reflexivity. Qed.
  Lemma set8_rTPos : forall v, d_set_rTPos D v = set8 d oc ol nu k0 tp rn v cb. Proof. intros; destruct d; cbv; reflexivity. Qed.
  Lemma set8_cbcrc : forall v, d_set_cbcrc D v = set8 d oc ol nu k0 tp rn rt v. Proof. intros; destruct d; cbv; reflexivity. Qed.
  Lemma g8_out_ch : d_out_ch D = oc. Proof. destruct d; reflexivity. Qed.
  Lemma g8_out_len : d_out_len D = ol. Proof. destruct d; reflexivity. Qed.
  Lemma g8_nused : d_nused D = nu. Proof. destruct d; reflexivity. Qed.
  Lemma g8_k0 : d_k0 D = k0. Proof. destruct d; reflexivity. Qed.
  Lemma g8_tPos : d_tPos D = tp. Proof. destruct d; reflexivity. Qed.
  Lemma g8_rNToGo : d_rNToGo D = rn. Proof. destruct d; reflexivity. Qed.
  Lemma g8_rTPos : d_rTPos D = rt. Proof. destruct d; reflexivity. Qed.
  Lemma g8_cbcrc : d_cbcrc D = cb. Proof. destruct d; reflexivity. Qed.
  Lemma g8_sv : d_sv D = d_sv d. Proof. destruct d; reflexivity. Qed.
  Lemma g8_tt : d_tt D = d_tt d. Proof. destruct d; reflexivity. Qed.
  Lemma g8_small : d_small D = d_small d. Proof. destruct d; reflexivity. Qed.
  Lemma g8_rand : d_rand D = d_rand d. Proof. destruct d; reflexivity. Qed.
  Lemma g8_bs100k : d_bs100k D = d_bs100k d. Proof. destruct d; reflexivity. Qed.
  Lemma g8_cap : blk_cap D = blk_cap d. Proof. destruct d; reflexivity. Qed.
  Lemma g3_av : s_avail_out (smod s out av tout) = av. Proof. destruct s; reflexivity. Qed.
  Lemma g3_out : s_out (smod s out av tout) = out. Proof. destruct s; reflexivity. Qed.
  Lemma pwd_set8 : pwd D = set8 d oc (ol - 1) nu k0 tp rn rt (crc_update cb oc). Proof. destruct d; reflexivity. Qed.
  Lemma pws_set8 : pws D (smod s out av tout) = smod s (oc :: out) (av - 1) (tout + 1). Proof. destruct s; reflexivity. Qed.
  (* [comment removed for export] *)
  Definition rNn : Z := if (rn =? 0)%Z then rNums rt else rn.
  Definition rTn : Z := if (rn =? 0)%Z then (if (rt + 1 =? 512)%Z then 0%Z else (rt + 1)%Z) else rt.
  Lemma rand_upd_set8 : rand_upd D = set8 d oc ol nu k0 tp (rNn - 1) rTn cb.
  Proof.
    unfold rNn, rTn. destruct (Z.eqb_spec rn 0) as [E|E].
    - rewrite rand_upd_z by (destruct d; cbn; exact E). destruct d; cbv -[rNums Z.sub Z.add Z.eqb]; reflexivity.
    - rewrite rand_upd_nz by (destruct d; cbn; exact E). destruct d; cbv -[rNums Z.sub Z.add Z.eqb]; reflexivity.
  Qed.
  Lemma rand_mask_set8 : rand_mask D = (if (rn =? 1)%Z then 1%Z else 0%Z). Proof. destruct d; reflexivity. Qed.
End Set8.
(* [comment removed for export] *)
Ltac g8 := repeat progress rewrite ?g8_out_ch, ?g8_out_len, ?g8_nused, ?g8_k0, ?g8_tPos, ?g8_rNToGo, ?g8_rTPos, ?g8_cbcrc, ?g8_sv, ?g8_tt,
                   ?g8_small, ?g8_rand, ?g8_bs100k, ?g8_cap, ?g3_av, ?g3_out,
                   ?set8_out_ch, ?set8_out_len, ?set8_nused, ?set8_k0, ?set8_tPos, ?set8_rNToGo, ?set8_rTPos, ?set8_cbcrc,
                   ?rand_upd_set8, ?rand_mask_set8, ?pwd_set8, ?pws_set8.

(* [comment removed for export] *)
Lemma gsF_set8 : forall d oc ol nu k0 tp rn rt cb,
  gsF (set8 d oc ol nu k0 tp rn rt cb) =
    let w := zget (d_tt d) tp in
    (Z.lxor (Z.land w 255) (if (rNn rn rt - 1 =? 1)%Z then 1%Z else 0%Z),
     set8 d oc ol nu k0 (w / 256) (rNn rn rt - 1) (rTn rn rt) cb).
Proof.
  intros. unfold gsF. replace (d_tt (set8 d oc ol nu k0 tp rn rt cb)) with (d_tt d) by (destruct d; reflexivity).
  replace (d_tPos (set8 d oc ol nu k0 tp rn rt cb)) with tp by (destruct d; reflexivity).
  rewrite set8_tPos, rand_upd_set8, rand_mask_set8. reflexivity.
Qed.

Lemma rNn_range : forall rn rt, (0 <= rn < 2147483648)%Z -> (0 <= rt < 512)%Z -> (1 <= rNn rn rt < 2147483648)%Z.
Proof.
  intros rn rt H1 H2. unfold rNn. destruct (Z.eqb_spec rn 0); [| lia]. pose proof (rNums_range rt H2). lia.
Qed.
Lemma rTn_range : forall rn rt, (0 <= rt < 512)%Z -> (0 <= rTn rn rt < 512)%Z.
Proof. intros rn rt H. unfold rTn. destruct (rn =? 0)%Z; [| lia]. destruct (Z.eqb_spec (rt + 1) 512); lia. Qed.

Lemma rNn_nz : forall rn rt, rn <> 0%Z -> rNn rn rt = rn.
Proof. intros rn rt H; unfold rNn; destruct (Z.eqb_spec rn 0); [lia| reflexivity]. Qed.
Lemma rTn_nz : forall rn rt, rn <> 0%Z -> rTn rn rt = rt.
Proof. intros rn rt H; unfold rTn; destruct (Z.eqb_spec rn 0); [lia| reflexivity]. Qed.
Lemma rNn_z : forall rt, rNn 0 rt = rNums rt. Proof. reflexivity. Qed.
Lemma rTn_z : forall rt, (0 <= rt < 512)%Z -> rTn 0 rt = ((rt + 1) mod 512)%Z.
Proof.
  intros rt H. unfold rTn. cbn [Z.eqb].
  destruct (Z.eqb_spec (rt + 1) 512) as [E|E]; [rewrite E; reflexivity| rewrite Z.mod_small by lia; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma byte_of_u64 : forall z, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 8 z.
Proof.
  intros z. apply Z_to_bv8_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  apply Z.mod_mod_divide. exists (2^56)%Z. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma sx32_cases : forall tq, (0 <= tq < 4294967296)%Z ->
  ((tq < 2147483648)%Z /\ sx32 (Z_to_bv 64 tq) = Z_to_bv 64 tq) \/
  ((2147483648 <= tq)%Z /\ bv_unsigned (sx32 (Z_to_bv 64 tq)) = (tq - 4294967296 + 18446744073709551616)%Z).
Proof.
  intros tq Hq. unfold sx32. rewrite (unsigned_lit tq) by lia. destruct (Z_lt_le_dec tq 2147483648) as [L|L].
  - left. split; [exact L|]. rewrite swrap32_small by lia. reflexivity.
  - right. split; [exact L|]. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 `div` 2)%Z with 2147483648%Z.
    rewrite unsigned_lit_neg by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma rnums_words_model : map bv_unsigned rnums_words = rNums_list.
Proof. vm_compute. reflexivity. Qed.
Lemma rnums_words_tbl : forall i, (0 <= i < 512)%Z -> wnth rnums_words i = Z_to_bv 64 (rNums i).
Proof.
  intros i Hi. unfold rNums. rewrite <- rnums_words_model. unfold wnth.
  rewrite <- (Z_to_bv_bv_unsigned (nth (Z.to_nat i) rnums_words (Z_to_bv 64 0))). f_equal.
  change 0%Z with (bv_unsigned (Z_to_bv 64 0)) at 2. rewrite map_nth. reflexivity.
Qed.
Lemma rnums_words_nth : forall i, (0 <= i < 512)%Z -> nth_error rnums_words (Z.to_nat i) = Some (Z_to_bv 64 (rNums i)).
Proof.
  intros i Hi. rewrite <- rnums_words_tbl by lia. apply nth_error_wnth; [lia|]. rewrite rnums_words_length. lia.
Qed.

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
  Notation RR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s3 s8 t3 t4 t5 t6 :=
    (mkR ra (o_SP c) (o_gp c) (o_tp c) t0 t1 t2 (Z_to_bv 64 (b_s (o_cx c))) s1 a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (b_s (o_cx c) + 1096)) s3 (Z_to_bv 64 (b_s (o_cx c) + 2047))
         (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 (-1)) s8 (Z_to_bv 64 100000) (Z_to_bv 64 (b_s (o_cx c) + 64080)) (Z_to_bv 64 10) t3 t4 t5 t6) (only parsing).
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
  Definition finv (oc ol nu k0 tp rn rt cb av : Z) : Prop :=
    (0 <= oc < 256)%Z /\ (0 <= ol <= 260)%Z /\ (0 <= nu <= PP + 1)%Z /\
    ((0 <= k0 < 256)%Z \/ (nu = 0%Z /\ (cap <= tp)%Z)) /\ (0 <= tp < 4294967296)%Z /\
    (0 <= rn < 2147483648)%Z /\ (0 <= rt < 512)%Z /\ (0 <= cb < 4294967296)%Z /\ (0 <= av <= av0)%Z.

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
    lazymatch goal with RNA : u32arr _ ?mm 0x335b0 rnums_words |- _ =>
      let RD := fresh "RD" in
      pose proof (u32arr_read s0segs mm 0x335b0 rnums_words i (Z_to_bv 64 (rNums i)) _ RNA (rnums_words_nth i ltac:(lia)) ltac:(lia) eq_refl) as RD;
      wstep; clear RD; rewrite ?(sx32_of_Z (rNums i)) by lia end.
End FR.
End ACeilS1.
