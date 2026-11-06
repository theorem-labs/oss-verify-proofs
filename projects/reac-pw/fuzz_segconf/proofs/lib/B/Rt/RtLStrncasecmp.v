(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_ubjson_encoder/lib/S8/AsanAcct.v, with its module paths and module names changed; 403 of its 523 lines of code are new or changed and 1138 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/FMbz_clean.v, with its module paths and module names changed; 344 of its 386 lines of code are new or changed and 481 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/A/HPgWrapNcmp.v's hd_strncmp_core (itself reac-pw/fuzz_pin's
   lib/A/PPgWrapNcmp.v pin_strncmp_core at 90722657971) re-run with the caller's frame hole of lib/A/HPgHole.v
   (ecall_preH in, the hole post out), as lib/A/Rt/FMrt_lift.v rt_post_roU_win re-runs rt_post_ro_win with
   lib/A/Rt/FMupoison.v ARU_frame: hd_rt_post_roH_win is rt_post_roU_win with HPgHole.ARH_frame in place of
   ARU_frame; the walk's premises that AR gives (the stack window, the runtime cells, the read-only views) are read
   off AR of the unpoisoned memory and carried to the memory itself, which agrees with it off the hole; the rest
   is pin's proof. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgWrapNcmpH.v, with its module paths and module names changed; 210 of its 305 lines of code are new or changed and 291 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Rt/RtLStrncmp.v, with its module paths and module names changed; 267 of its 357 lines of code are new or changed and 215 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Rt/RtLStrncasecmp.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* Row 7 of the interceptor interface (provenance/evidence/interceptors/INTERFACE-A-interceptors.md): strncasecmp at
   SegRtPC.PC_strncasecmp = 0x43aac, the one-instruction trampoline A/Bz/A/I_trampfm.v tramp_strncasecmp in front of
   __interceptor_strncasecmp 0x45088, stated as RtSeg.astrncasecmp_realizes.
   - the walk: A/Bz/A/I_scase.v istrncasecmp_spec (relocated from omx-clap-core/fuzz_manifest), its range check's
     Section hypothesis discharged by A/Bz/A/R_isPoisoned.v rip_proof; for n = 0 the walk's own zero branch
     (I_scase.v iscc_zero), which asks nothing of the strings;
   - the compared length: the walk reads only scase_sz n b1 b2 bytes of each string, so it is given the strings
     TRUNCATED to that length (I_scase.v cc_trunc keeps the answer), and RtSeg's aread_ok over min (n, len + 1) bytes
     is enough for them - the way fuzz_command's RtLStrncmpR.v lifts the strncmp walk to RtString's form;
   - pre and post sides: RtBzAdapt.v / RtBzClean.v / RtBzAdaptP.v as for strncmp; the interceptor's fixed cells are
     the strncmp interceptor's (I_strncmpw.v icells_sc), read by RtLStrncmp.v icells_sc_of_ARm_clean;
   - the answer: the walk returns I_scasem.v scase_res, which is 0 exactly when the compared prefixes of the two
     strings with their NULs agree under ToLower (RtSeg.strncase_eq); the list facts are fuzz_manifest's
     lib/A/FMspec_str.v and lib/A/FMstrncasecmp.v ones, restated over RtSeg's lc. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YK1b YP03 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import
RtDefs RtBzHBase RtBzLift RtBzPre RtBzClean RtBzAdapt RtBzAdaptP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg SegRtPC RtBzSpecStrn RtLStrncmp.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_scasem.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_scase.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strncmpw3.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_trampfm.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_isPoisoned.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module SCM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_scasem.
Module SCW := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_scase.
Module SCP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strncmpw3.
Module TRF := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_trampfm.
Module RIP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_isPoisoned.
Module SN := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt.RtBzSpecStrn.

(* ---- the walk's answer, read on the byte values (fm lib/A/FMspec_str.v:98-237) ---- *)

(* the walk's ToLower (I_scasem.v zlw) and the contract's (RtSeg.lc) are one function *)
Lemma lc_is_zlw : RtSeg.lc = SCM.zlw.
Proof. reflexivity. Qed.

(* the index the walk stops at *)
Fixpoint zcase_idx (k : nat) (m1 m2 : list Z) {struct k} : nat :=
  match k with
  | O => O
  | S k' => match m1, m2 with
            | x :: r1, y :: r2 => if negb (SCM.zlw x =? SCM.zlw y) || (x =? 0) then O else S (zcase_idx k' r1 r2)
            | _, _ => O
            end
  end.

Lemma scase_idx_aux_z : forall (k : nat) (m1 m2 : list Z),
  Forall (fun c => 0 <= c < 256) m1 -> Forall (fun c => 0 <= c < 256) m2 ->
  SCM.scase_idx_aux (map (Z_to_bv 8) m1) (map (Z_to_bv 8) m2) k = zcase_idx k m1 m2.
Proof.
  induction k as [|k IH]; intros m1 m2 H1 H2; [reflexivity|].
  destruct m1 as [|x r1]; [reflexivity|]. destruct m2 as [|y r2]; [reflexivity|].
  inversion H1 as [|? ? Hx H1']; subst. inversion H2 as [|? ? Hy H2']; subst.
  cbn [map SCM.scase_idx_aux zcase_idx].
  rewrite (SN.u8 x Hx), (SN.u8 y Hy).
  destruct (negb (SCM.zlw x =? SCM.zlw y) || (x =? 0))%bool; [reflexivity|].
  rewrite (IH r1 r2 H1' H2'). reflexivity.
Qed.

(* the walk's answer *)
Definition zcase_res (k : nat) (m1 m2 : list Z) : Z :=
  let i := zcase_idx k m1 m2 in
  if (i =? k)%nat then 0 else SCM.zlw (nth i m1 0) - SCM.zlw (nth i m2 0).

Lemma lc_zero : forall c, 0 <= c -> SCM.zlw c = 0 -> c = 0.
Proof.
  intros c Hc. unfold SCM.zlw. destruct ((65 <=? c) && (c <=? 90))%bool eqn:E; [|exact (fun H => H)].
  apply andb_prop in E as [E1 _]. apply Z.leb_le in E1. lia.
Qed.

Lemma nul_last_nonempty : forall m, SN.nul_last m -> m <> [].
Proof. intros m (l & -> & _). destruct l; discriminate. Qed.

(* a zero answer and RtSeg.strncase_eq are the same claim *)
Lemma zcase_res_zero : forall (k : nat) (m1 m2 : list Z),
  SN.nul_last m1 -> SN.nul_last m2 ->
  (zcase_res k m1 m2 = 0 <-> map SCM.zlw (firstn k m1) = map SCM.zlw (firstn k m2)).
Proof.
  induction k as [|k IH]; intros m1 m2 N1 N2.
  { unfold zcase_res. cbn [zcase_idx firstn map]. split; reflexivity. }
  destruct m1 as [|x r1]; [exfalso; exact (nul_last_nonempty _ N1 eq_refl)|].
  destruct m2 as [|y r2]; [exfalso; exact (nul_last_nonempty _ N2 eq_refl)|].
  unfold zcase_res. cbn [zcase_idx firstn map nth].
  destruct (negb (SCM.zlw x =? SCM.zlw y) || (x =? 0))%bool eqn:EB.
  - cbn [Nat.eqb]. apply orb_true_iff in EB as [EB|EB].
    + apply negb_true_iff, Z.eqb_neq in EB.
      split; [intros Hz; exfalso; apply EB; lia | intros Heq; exfalso; apply EB; injection Heq as Hh _; exact Hh].
    + apply Z.eqb_eq in EB. subst x.
      assert (Hr1 : r1 = []) by (apply (SN.nul_last_cons 0 r1 N1); reflexivity).
      destruct (Z.eq_dec y 0) as [->|NY].
      * assert (Hr2 : r2 = []) by (apply (SN.nul_last_cons 0 r2 N2); reflexivity).
        subst r1 r2. cbn [firstn map]. split; [reflexivity | intros _; unfold SCM.zlw; cbn; lia].
      * assert (Hy0 : 0 <= y < 256) by (apply (SN.nul_last_hd_range y r2 N2)).
        assert (Hne : SCM.zlw 0 <> SCM.zlw y)
          by (intros Hc; apply NY; apply lc_zero; [lia | rewrite <- Hc; reflexivity]).
        split; [intros Hz; exfalso; apply Hne; lia
               | intros Heq; exfalso; apply Hne; injection Heq as Hh _; exact Hh].
  - apply orb_false_iff in EB as [EL EX]. apply negb_false_iff, Z.eqb_eq in EL. apply Z.eqb_neq in EX.
    cbn [Nat.eqb nth].
    assert (Hx0 : 0 <= x < 256) by (apply (SN.nul_last_hd_range x r1 N1)).
    assert (HY : y <> 0) by (intros ->; apply EX; apply lc_zero; [lia | rewrite EL; reflexivity]).
    rewrite (IH r1 r2 (SN.nul_last_tl x r1 N1 EX) (SN.nul_last_tl y r2 N2 HY)).
    split; [intros H; rewrite EL, H; reflexivity | intros H; injection H as _ H; exact H].
Qed.

Lemma scase_res_z : forall (n : Z) (m1 m2 : list Z),
  0 <= n -> Forall (fun c => 0 <= c < 256) m1 -> Forall (fun c => 0 <= c < 256) m2 ->
  (zcase_idx (Z.to_nat n) m1 m2 < length m1)%nat -> (zcase_idx (Z.to_nat n) m1 m2 < length m2)%nat ->
  SCM.scase_res n (map (Z_to_bv 8) m1) (map (Z_to_bv 8) m2) = zcase_res (Z.to_nat n) m1 m2.
Proof.
  intros n m1 m2 Hn H1 H2 L1 L2.
  unfold SCM.scase_res, zcase_res, SCM.scase_idx.
  rewrite (scase_idx_aux_z (Z.to_nat n) m1 m2 H1 H2).
  set (i := zcase_idx (Z.to_nat n) m1 m2) in *.
  assert (Hi : Z.to_nat (Z.of_nat i) = i) by apply Nat2Z.id.
  rewrite Hi.
  destruct (Nat.eq_dec i (Z.to_nat n)) as [E|NE].
  - rewrite E. replace (Z.of_nat (Z.to_nat n) =? n) with true by (symmetry; apply Z.eqb_eq; lia).
    rewrite Nat.eqb_refl. reflexivity.
  - replace (Z.of_nat i =? n) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (i =? Z.to_nat n)%nat with false by (symmetry; apply Nat.eqb_neq; exact NE).
    rewrite (SN.nth_error_map_nth m1 i L1), (SN.nth_error_map_nth m2 i L2).
    rewrite !SN.u8; [reflexivity | |].
    + apply (proj1 (Forall_forall _ _) H2 (nth i m2 0)). apply nth_In. exact L2.
    + apply (proj1 (Forall_forall _ _) H1 (nth i m1 0)). apply nth_In. exact L1.
Qed.

(* the walk stops at the first NUL at the latest (fm lib/A/FMstrncasecmp.v:61) *)
Lemma zcase_idx_lt : forall k m1 m2, SN.nul_last m1 -> SN.nul_last m2 ->
  (zcase_idx k m1 m2 < length m1)%nat /\ (zcase_idx k m1 m2 < length m2)%nat.
Proof.
  induction k as [|k IH]; intros m1 m2 N1 N2.
  - destruct N1 as (l1 & -> & _). destruct N2 as (l2 & -> & _).
    cbn [zcase_idx]. rewrite !length_app. cbn [length]. lia.
  - destruct m1 as [|x r1]; [exfalso; exact (nul_last_nonempty _ N1 eq_refl)|].
    destruct m2 as [|y r2]; [exfalso; exact (nul_last_nonempty _ N2 eq_refl)|].
    cbn [zcase_idx length].
    destruct (negb (SCM.zlw x =? SCM.zlw y) || (x =? 0))%bool eqn:EB; [lia|].
    apply orb_false_iff in EB as [EL EX]. apply negb_false_iff, Z.eqb_eq in EL. apply Z.eqb_neq in EX.
    assert (Hx0 : 0 <= x < 256) by exact (SN.nul_last_hd_range x r1 N1).
    assert (HY : y <> 0) by (intros ->; apply EX; apply lc_zero; [lia | rewrite EL; reflexivity]).
    destruct (IH r1 r2 (SN.nul_last_tl x r1 N1 EX) (SN.nul_last_tl y r2 N2 HY)) as [L1 L2].
    lia.
Qed.

Lemma zcase_res_range : forall k m1 m2,
  Forall (fun c => 0 <= c < 256) m1 -> Forall (fun c => 0 <= c < 256) m2 ->
  (zcase_idx k m1 m2 < length m1)%nat -> (zcase_idx k m1 m2 < length m2)%nat ->
  -256 < zcase_res k m1 m2 < 256.
Proof.
  intros k m1 m2 R1 R2 L1 L2. unfold zcase_res. cbv zeta.
  set (i := zcase_idx k m1 m2) in *.
  destruct (Nat.eqb i k); [lia|].
  assert (H1 : 0 <= nth i m1 0 < 256) by (apply (proj1 (Forall_forall _ _) R1); apply nth_In; exact L1).
  assert (H2 : 0 <= nth i m2 0 < 256) by (apply (proj1 (Forall_forall _ _) R2); apply nth_In; exact L2).
  pose proof (SCM.zlw_range _ H1). pose proof (SCM.zlw_range _ H2). lia.
Qed.

(* what the walk needs of two C strings and what it answers (fm lib/A/FMstrncasecmp.v:91 ncase_facts, in the
   shape of fuzz_command's RtLStrncmp.v strncmp_strs) *)
Lemma ncase_strs : forall (n : Z) (l1 l2 : list Z), 0 <= n ->
  Forall (fun c => 0 <= c < 256 /\ c <> 0) l1 -> Forall (fun c => 0 <= c < 256 /\ c <> 0) l2 ->
  SCM.scase_ok n (map (Z_to_bv 8) l1 ++ [Z_to_bv 8 0]) (map (Z_to_bv 8) l2 ++ [Z_to_bv 8 0]) /\
  0 <= SCM.scase_sz n (map (Z_to_bv 8) l1 ++ [Z_to_bv 8 0]) (map (Z_to_bv 8) l2 ++ [Z_to_bv 8 0])
    <= Z.of_nat (length l1) + 1 /\
  0 <= SCM.scase_sz n (map (Z_to_bv 8) l1 ++ [Z_to_bv 8 0]) (map (Z_to_bv 8) l2 ++ [Z_to_bv 8 0])
    <= Z.of_nat (length l2) + 1 /\
  -256 < SCM.scase_res n (map (Z_to_bv 8) l1 ++ [Z_to_bv 8 0]) (map (Z_to_bv 8) l2 ++ [Z_to_bv 8 0]) < 256 /\
  (SCM.scase_res n (map (Z_to_bv 8) l1 ++ [Z_to_bv 8 0]) (map (Z_to_bv 8) l2 ++ [Z_to_bv 8 0]) = 0 <->
   RtSeg.strncase_eq (Z.to_nat n) l1 l2).
Proof.
  intros n l1 l2 Hn F1 F2.
  assert (Eb1 : map (Z_to_bv 8) l1 ++ [Z_to_bv 8 0] = map (Z_to_bv 8) (l1 ++ [0])) by (rewrite map_app; reflexivity).
  assert (Eb2 : map (Z_to_bv 8) l2 ++ [Z_to_bv 8 0] = map (Z_to_bv 8) (l2 ++ [0])) by (rewrite map_app; reflexivity).
  rewrite Eb1, Eb2.
  assert (N1 : SN.nul_last (l1 ++ [0])).
  { exists l1. split; [reflexivity|].
    split; (eapply Forall_impl; [|exact F1]); intros c Hc; first [exact (proj2 Hc) | exact (proj1 Hc)]. }
  assert (N2 : SN.nul_last (l2 ++ [0])).
  { exists l2. split; [reflexivity|].
    split; (eapply Forall_impl; [|exact F2]); intros c Hc; first [exact (proj2 Hc) | exact (proj1 Hc)]. }
  assert (R1 : Forall (fun c => 0 <= c < 256) (l1 ++ [0])).
  { apply Forall_app. split; [eapply Forall_impl; [|exact F1]; intros c Hc; exact (proj1 Hc)|].
    apply Forall_cons; [lia | apply Forall_nil]. }
  assert (R2 : Forall (fun c => 0 <= c < 256) (l2 ++ [0])).
  { apply Forall_app. split; [eapply Forall_impl; [|exact F2]; intros c Hc; exact (proj1 Hc)|].
    apply Forall_cons; [lia | apply Forall_nil]. }
  destruct (zcase_idx_lt (Z.to_nat n) _ _ N1 N2) as (L1 & L2).
  assert (EI : SCM.scase_idx n (map (Z_to_bv 8) (l1 ++ [0])) (map (Z_to_bv 8) (l2 ++ [0]))
             = Z.of_nat (zcase_idx (Z.to_nat n) (l1 ++ [0]) (l2 ++ [0]))).
  { unfold SCM.scase_idx. rewrite (scase_idx_aux_z _ _ _ R1 R2). reflexivity. }
  assert (ES : SCM.scase_sz n (map (Z_to_bv 8) (l1 ++ [0])) (map (Z_to_bv 8) (l2 ++ [0]))
             = Z.min (Z.of_nat (zcase_idx (Z.to_nat n) (l1 ++ [0]) (l2 ++ [0])) + 1) n).
  { unfold SCM.scase_sz. rewrite EI. reflexivity. }
  pose proof L1 as L1'. pose proof L2 as L2'.
  rewrite length_app in L1', L2'. cbn [length] in L1', L2'.
  split; [unfold SCM.scase_ok; rewrite ES, !length_map, !length_app; cbn [length]; lia|].
  split; [rewrite ES; lia|]. split; [rewrite ES; lia|].
  rewrite (scase_res_z n _ _ Hn R1 R2 L1 L2).
  split; [exact (zcase_res_range _ _ _ R1 R2 L1 L2)|].
  unfold RtSeg.strncase_eq. rewrite lc_is_zlw. apply zcase_res_zero; assumption.
Qed.

(* ---- byte lists (fuzz_command's RtLStrncmpR.v:49-76) ---- *)

Lemma map_bv_roundtrip : forall s : list byte, map (Z_to_bv 8) (map (fun b : byte => bv_unsigned b) s) = s.
Proof.
  induction s as [|b s IH]; [reflexivity|].
  cbn [map]. rewrite IH. f_equal. apply Z_to_bv_bv_unsigned.
Qed.

Lemma bytes_nz_forall : forall s : list byte, ~ In (Z_to_bv 8 0) s ->
  Forall (fun c => 0 <= c < 256 /\ c <> 0) (map (fun b : byte => bv_unsigned b) s).
Proof.
  intros s HN. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (bb & <- & Hin).
  pose proof (bv_unsigned_in_range 8 bb) as HR. unfold bv_modulus in HR. cbn [Z.of_N] in HR.
  change (2 ^ 8) with 256 in HR.
  split; [lia|]. intros E. apply HN.
  replace (Z_to_bv 8 0) with bb; [exact Hin | apply bv_eq; rewrite E; reflexivity].
Qed.

Lemma nth_firstn_lt : forall (l : list byte) j i d, (i < j)%nat -> nth i (firstn j l) d = nth i l d.
Proof.
  induction l as [|b l IH]; intros j i d Hi; [rewrite firstn_nil; destruct i; reflexivity|].
  destruct j as [|j]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

Lemma abytes_firstn : forall (W : world tfibsegs) mem a (l : list byte) j,
  abytes_at tfibsegs W mem a l -> abytes_at tfibsegs W mem a (firstn j l).
Proof.
  intros W mem a l j HB i Hi. rewrite length_firstn in Hi.
  rewrite nth_firstn_lt by lia. apply HB. lia.
Qed.

(* n = 0: the walk compares nothing and answers 0 *)
Lemma idx_zero : forall b1 b2, SCM.scase_idx 0 b1 b2 = 0.
Proof. intros b1 b2. reflexivity. Qed.

Lemma res_zero : forall b1 b2, SCM.scase_res 0 b1 b2 = 0.
Proof. intros b1 b2. unfold SCM.scase_res. rewrite (idx_zero b1 b2). reflexivity. Qed.

(* ---- the contract ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : SegBSyms B.

Theorem seg_strncasecmp : RtSeg.astrncasecmp_realizes tfibsegs B SegRtPC.PC_strncasecmp.
Proof.
  unfold RtSeg.astrncasecmp_realizes.
  intros ly S W regs mem md x y n sx sy HPRE G10 G11 G12 Hn Hx Hy SX SY RDX AMX RDY AMY TX TY HROM.
  pose proof HPRE as (HEP & HSLO & HPRS).
  pose proof HEP as (HAR & _).
  pose proof RDX as (RX0 & RX1 & RX2 & _).
  pose proof RDY as (RY0 & RY1 & RY2 & _).
  pose proof AMX as AMX'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AMX'.
  pose proof AMY as AMY'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AMY'.
  unfold astr_len in *.
  (* ---- the answer ---- *)
  pose proof (bytes_nz_forall sx (proj2 SX)) as F1.
  pose proof (bytes_nz_forall sy (proj2 SY)) as F2.
  destruct (ncase_strs n (map (fun b : byte => bv_unsigned b) sx)
              (map (fun b : byte => bv_unsigned b) sy) ltac:(lia) F1 F2) as (OK & SZ1 & SZ2 & RNG & RES).
  rewrite !map_bv_roundtrip in OK. rewrite !map_bv_roundtrip, !length_map in SZ1.
  rewrite !map_bv_roundtrip, !length_map in SZ2. rewrite !map_bv_roundtrip in RNG, RES.
  assert (SZN : SCM.scase_sz n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) <= n)
    by (unfold SCM.scase_sz; lia).
  (* ---- the cleaned store ---- *)
  pose proof (rom_eq_of_rt B TB ly S W mem md HAR HROM) as RE.
  pose proof (RtBzClean.mem_inv_clean (mrestrict (w_H W) mem)) as MI.
  destruct (stk_of_stk_pre B (2 * ESTACK) ly S W regs mem md HPRE ltac:(unfold ESTACK; lia))
    as (ST0 & HC0 & HCs & Hsp47).
  assert (ST : BF.stk BI.asegs (clean (mrestrict (w_H W) mem)) (spZ regs - 2 * ESTACK) (spZ regs)).
  { apply (RtBzClean.stk_clean (mrestrict (w_H W) mem) (spZ regs - 2 * ESTACK) (spZ regs));
      [unfold TFIB_IMG_END, ESTACK in *; lia | unfold BM.UTOP; lia | exact ST0]. }
  pose proof (m2s_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as M2S.
  pose proof (RtLStrncmp.icells_sc_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as IC.
  (* ---- the run ---- *)
  apply (RtBzClean.bz_run_clean B TB W SegRtPC.PC_strncasecmp regs mem md
           (fun ms1 => SCP.istrncmp_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
              (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
              (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
              (reg_get regs 26) (reg_get regs 27) fp_regs fp_csr
              (SCM.scase_res n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]))
              (spZ regs - 2 * ESTACK) (clean (mrestrict (w_H W) mem)) ms1
            /\ YK1b.mem_grows (clean (mrestrict (w_H W) mem)) (ms_mem ms1)) _
           (romN_of_rt B W mem HROM) (rom_viewO_of_ARm B TB ly S W mem (proj1 HAR))).
  - apply RtBzAdaptP.evt_grows. apply RtBzPre.bz_canon. apply TRF.tramp_strncasecmp.
    destruct (Z.eq_dec n 0) as [->|Hn0].
    + (* n = 0: the walk's own zero branch asks nothing of the strings *)
      rewrite (res_zero (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0])).
      apply (SCW.iscc_zero (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
               (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9)
               (reg_get regs 10) (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14)
               (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19)
               (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24)
               (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29)
               (reg_get regs 30) (reg_get regs 31) fp_regs fp_csr (clean (mrestrict (w_H W) mem)) x y
               (spZ regs - 2 * ESTACK));
        [exact G10 | exact G11 | exact G12
         | exact ST
         | change (bv_unsigned (reg_get regs 2)) with (spZ regs); unfold ESTACK in *; lia
         | unfold BR.kHighShadowEnd; lia
         | change (bv_unsigned (reg_get regs 2)) with (spZ regs); lia
         | lia | lia | exact IC | exact MI].
    + (* 0 < n: the strings, truncated to the compared length *)
      destruct (SCW.cc_trunc n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) ltac:(lia) OK)
        as (EIc & ERc & ESc & OKc & LC1 & LC2).
      rewrite <- ERc.
      apply (SCW.istrncasecmp_spec RIP.rip_proof (reg_get regs 1) (reg_get regs 2) (reg_get regs 3)
               (reg_get regs 4) (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (reg_get regs 8)
               (reg_get regs 9) (reg_get regs 10) (reg_get regs 11) (reg_get regs 12) (reg_get regs 13)
               (reg_get regs 14) (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (reg_get regs 18)
               (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23)
               (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28)
               (reg_get regs 29) (reg_get regs 30) (reg_get regs 31) fp_regs fp_csr
               (clean (mrestrict (w_H W) mem)) x y n
               (firstn (Z.to_nat (SCM.scase_sz n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0])))
                  (sx ++ [Z_to_bv 8 0]))
               (firstn (Z.to_nat (SCM.scase_sz n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0])))
                  (sy ++ [Z_to_bv 8 0]))
               (spZ regs - 2 * ESTACK));
        [exact G10 | exact G11 | exact G12 | exact ST
         | change (bv_unsigned (reg_get regs 2)) with (spZ regs); unfold ESTACK in *; lia
         | unfold BR.kHighShadowEnd; lia
         | change (bv_unsigned (reg_get regs 2)) with (spZ regs); lia
         | lia | | | exact OKc | | | | | | | exact M2S | exact IC | exact MI].
      * (* the first string's bytes, on the cleaned store *)
        apply (RtBzClean.bytes_at_clean (mrestrict (w_H W) mem) x _ RE);
          [rewrite LC1; unfold BM.UTOP; lia|].
        apply bz_bytes_of_abytes; [apply abytes_firstn; exact (proj1 SX) | lia | rewrite LC1; lia].
      * apply (RtBzClean.bytes_at_clean (mrestrict (w_H W) mem) y _ RE);
          [rewrite LC2; unfold BM.UTOP; lia|].
        apply bz_bytes_of_abytes; [apply abytes_firstn; exact (proj1 SY) | lia | rewrite LC2; lia].
      * rewrite ESc. lia.
      * rewrite ESc. lia.
      * rewrite ESc. change (bv_unsigned (reg_get regs 2)) with (spZ regs).
        destruct (sep_of_read (2 * ESTACK) W regs mem x (Z.min n (Z.of_nat (length sx) + 1))
                    ltac:(unfold ESTACK; lia) ltac:(lia) RDX) as [HL|HR];
          [left; unfold ESTACK in *; lia | right; lia].
      * rewrite ESc. change (bv_unsigned (reg_get regs 2)) with (spZ regs).
        destruct (sep_of_read (2 * ESTACK) W regs mem y (Z.min n (Z.of_nat (length sy) + 1))
                    ltac:(unfold ESTACK; lia) ltac:(lia) RDY) as [HL|HR];
          [left; unfold ESTACK in *; lia | right; lia].
      * rewrite ESc.
        apply (RtBzClean.chk_ok_clean (mrestrict (w_H W) mem) x
                 (SCM.scase_sz n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0])) RE ltac:(lia) ltac:(lia)).
        exact (chk_of_read (2 * ESTACK) W regs mem x (Z.min n (Z.of_nat (length sx) + 1))
                 (SCM.scase_sz n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]))
                 (Z.of_nat (length sx)) RDX AMX ltac:(lia) ltac:(lia) ltac:(lia)).
      * rewrite ESc.
        apply (RtBzClean.chk_ok_clean (mrestrict (w_H W) mem) y
                 (SCM.scase_sz n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0])) RE ltac:(lia) ltac:(lia)).
        exact (chk_of_read (2 * ESTACK) W regs mem y (Z.min n (Z.of_nat (length sy) + 1))
                 (SCM.scase_sz n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]))
                 (Z.of_nat (length sy)) RDY AMY ltac:(lia) ltac:(lia) ltac:(lia)).
  - (* ---- the post ---- *)
    intros msc ms' model' (HQ & GROW) Hcl Heqv Hsbm _.
    unfold SCP.istrncmp_post in HQ.
    destruct HQ as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM
                    & MI' & ST').
    destruct (RtBzPre.bz_window (clean (mrestrict (w_H W) mem)) m' (spZ regs) 2256
                (spZ regs - 2 * ESTACK) MU ST') as (MO & MN);
      [unfold ESTACK; lia | unfold TFIB_IMG_END, ESTACK in *; lia |].
    apply (RtBzAdaptP.art_post_ro_clean B LAWS (2 * ESTACK) 2256 ly S W regs mem md _ _ ms' model' HPRE
             ltac:(unfold ESTACK; lia) Hcl Heqv Hsbm
             eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(keep_regs) MO MN GROW).
    intros regs' mem' HR _.
    assert (A10 : getr regs' 10%bv
                  = Z_to_bv 64 (SCM.scase_res n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0])))
      by (rewrite (HR 10%bv); reflexivity).
    rewrite A10. rewrite <- RES.
    split.
    + intros E.
      apply (f_equal (fun w : word => bv_unsigned w)) in E. unfold w64 in E.
      rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
      change (bv_modulus 64) with (2 ^ 64) in E.
      rewrite (Z.mod_small 0 (2 ^ 64) ltac:(lia)) in E.
      revert E. Z.div_mod_to_equations. lia.
    + intros E. rewrite E. reflexivity.
Qed.

End s.

(* ---- the closing form: AR_laws discharged by the core's law proof, the record SegBSyms B the one residual ---- *)
Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis HB : SegBSyms B.

Theorem seg_strncasecmp_closed : RtSeg.astrncasecmp_realizes tfibsegs B SegRtPC.PC_strncasecmp.
Proof. exact (seg_strncasecmp B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

End closed.

Print Assumptions seg_strncasecmp_closed.
