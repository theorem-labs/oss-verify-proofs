(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem Bytes.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim CtTime.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApWalkTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeDefs TimeKit TimeFmtPure.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_JTAB : Z := 0x418ec.
Definition A_MINTAB : Z := 0x41908.
Definition A_MAXTAB : Z := 0x4192c.
Definition A_MDAYS : Z := 0x41950.
Definition A_YDAYS : Z := 0x419b0.

Definition mintab (i : Z) : Z := if (i =? 2) || (i =? 3) then 1 else 0.
Definition maxtab (i : Z) : Z :=
  if i =? 0 then 99 else if i =? 1 then 99 else if i =? 2 then 12 else if i =? 3 then 31 else if i =? 4 then 23 else 59.
Definition mdaystab (k : Z) : Z := nth (Z.to_nat k) [31; 28; 31; 30; 31; 30; 31; 31; 30; 31; 30; 31] 0.
Definition ydaystab (k : Z) : Z := nth (Z.to_nat k) [0; 31; 59; 90; 120; 151; 181; 212; 243; 273; 304; 334] 0.
(* [comment removed for export] *)
Definition case_pc (i : Z) : Z :=
  if i =? 0 then 0x12c3d0 else if i =? 1 then 0x12c478 else if i =? 2 then 0x12c3ec else if i =? 3 then 0x12c3fc
  else if i =? 4 then 0x12c3e4 else if i =? 5 then 0x12c498 else 0x12c4a0.
Definition jtab (i : Z) : Z := case_pc i - A_JTAB.

(* [comment removed for export] *)
Definition MASK47 : Z := 140737488355333.      (* [comment removed for export] *)
Definition T2T_CONSTS (l mo yr tm : Z) : list cell :=
  [C8 (Z_to_bv 64 0x28f5c28); C8 (Z_to_bv 64 18446744071868851347); C8 (Z_to_bv 64 0x51eb851f); C8 (Z_to_bv 64 0xa3d70b);
   C8 (Z_to_bv 64 0x51eb850); C8 (Z_to_bv 64 18446744072678759465); C8 (Z_to_bv 64 l); C8 (Z_to_bv 64 MASK47);
   C8 (Z_to_bv 64 mo); C8 (Z_to_bv 64 yr); C8 (Z_to_bv 64 tm); C8 (Z_to_bv 64 7)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fld (i : Z) (t : tm6) : Z :=
  if i =? 0 then t_year t / 100 else if i =? 1 then t_year t mod 100 else if i =? 2 then t_mon t else if i =? 3 then t_mday t
  else if i =? 4 then t_hour t else if i =? 5 then t_min t else t_sec t.
Definition chi (i : Z) (t : tm6) : Z := digit (fld i t / 10).
Definition clo (i : Z) (t : tm6) : Z := digit (fld i t mod 10).
Definition zb8 (c : Z) : cell := C1 (Z_to_bv 8 c).
Definition gcells (t : tm6) (ms : Z) : list cell :=
  [zb8 (chi 0 t); zb8 (clo 0 t); zb8 (chi 1 t); zb8 (clo 1 t); zb8 (chi 2 t); zb8 (clo 2 t); zb8 (chi 3 t); zb8 (clo 3 t);
   zb8 (chi 4 t); zb8 (clo 4 t); zb8 (chi 5 t); zb8 (clo 5 t); zb8 (chi 6 t); zb8 (clo 6 t);
   zb8 CH_DOT; zb8 (digit (ms / 100)); zb8 (digit ((ms / 10) mod 10)); zb8 (digit (ms mod 10)); zb8 CH_Z].

Lemma fld_range : forall i t, tm_valid t -> 0 <= i <= 6 -> mintab i <= fld i t <= maxtab i /\ 0 <= fld i t <= 99.
Proof.
  intros i t (Y & MO & MD & HH & MI & SS) Hi. pose proof (days_in_month_le31 (t_year t) (t_mon t)) as DM.
  unfold fld, mintab, maxtab.
  assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
  destruct Hi' as [->|[->|[->|[->|[->|[->| ->]]]]]]; cbn [Z.eqb orb Pos.eqb];
    try (pose proof (Z.div_pos (t_year t) 100 ltac:(lia) ltac:(lia)); pose proof (Z.div_lt_upper_bound (t_year t) 100 100 ltac:(lia) ltac:(lia)); lia);
    try (pose proof (Z.mod_pos_bound (t_year t) 100 ltac:(lia)); lia); lia.
Qed.

Lemma chi_val : forall i t, tm_valid t -> 0 <= i <= 6 -> chi i t = 48 + fld i t / 10 /\ 48 <= chi i t <= 57.
Proof.
  intros i t TV Hi. destruct (fld_range i t TV Hi) as [_ R]. unfold chi, digit, CH_0.
  pose proof (Z.div_pos (fld i t) 10 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (fld i t) 10 10 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma clo_val : forall i t, tm_valid t -> 0 <= i <= 6 -> clo i t = 48 + fld i t mod 10 /\ 48 <= clo i t <= 57.
Proof.
  intros i t TV Hi. destruct (fld_range i t TV Hi) as [_ R]. unfold clo, digit, CH_0. pose proof (Z.mod_pos_bound (fld i t) 10 ltac:(lia)). lia.
Qed.
Lemma pair_val : forall i t, tm_valid t -> 0 <= i <= 6 -> 10 * chi i t + clo i t - 528 = fld i t.
Proof.
  intros i t TV Hi. destruct (chi_val i t TV Hi) as [-> _]. destruct (clo_val i t TV Hi) as [-> _].
  pose proof (Z.div_mod (fld i t) 10 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma div10_mod10 : forall y, 0 <= y -> (y / 10) mod 10 = (y mod 100) / 10.
Proof.
  intros y Hy.
  pose proof (Z.div_mod y 100 ltac:(lia)) as E. pose proof (Z.mod_pos_bound y 100 ltac:(lia)) as B.
  set (q := y / 100) in *. set (r := y mod 100) in *.
  rewrite E. replace (100 * q + r) with (q * 10 * 10 + r) by lia.
  rewrite Z.div_add_l by lia. rewrite Z.add_comm, Z.mod_add by lia.
  apply Z.mod_small. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
Qed.
Lemma mod10_mod100 : forall y, 0 <= y -> y mod 10 = (y mod 100) mod 10.
Proof.
  intros y Hy. pose proof (Z.div_mod y 100 ltac:(lia)) as E. rewrite E at 1.
  replace (100 * (y / 100) + y mod 100) with (y mod 100 + (y / 100 * 10) * 10) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma genstr_gcells : forall ts t, gentime_adj ts = Some t -> map (Z_to_bv 8) (genstr ts) = cells_bytes (gcells t (ts_ms ts)).
Proof.
  intros ts t GA. pose proof (gentime_adj_valid ts t GA) as (Y & _).
  unfold genstr. rewrite GA. unfold gen15, dec4, dec2, dec3, gcells, chi, clo, fld. cbn -[digit Z.div Z.modulo Z_to_bv].
  rewrite (Z.div_div (t_year t) 100 10) by lia. change (100 * 10) with 1000.
  rewrite <- (div10_mod10 (t_year t)) by lia. rewrite <- (mod10_mod100 (t_year t)) by lia.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition low32 (x : Z) : Z := x mod 2^32.
Definition sext32 (x : Z) : Z := bv_swrap 32 x.
(* [comment removed for export] *)
Definition feb_w (y : Z) : Z := ((y * 18446744072678759465) mod 2^64 + 0x51eb850) mod 2^64.
Definition rot_or (w : Z) (k : Z) : Z := Z.lor ((sext32 (Z.shiftl (low32 w) (32 - k))) mod 2^64) (Z.shiftr (low32 w) k).
Definition feb_md (y : Z) : Z :=
  let w := feb_w y in
  if rot_or w 4 <? 0xa3d70b then 29
  else 28 + Z.b2z ((0x28f5c28 <? rot_or w 2) && (Z.land (y - 1900) 3 =? 0)).

Definition feb_md_checkf (y : Z) : bool := feb_md y =? days_in_month y 2.
Lemma feb_md_check_all : check_from feb_md_checkf (Z.to_nat 10000) 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma feb_md_ok : forall y, 0 <= y <= 9999 -> feb_md y = days_in_month y 2.
Proof.
  intros y Hy. apply Z.eqb_eq. apply (check_from_ok feb_md_checkf (Z.to_nat 10000) 0); [exact feb_md_check_all| rewrite Z2Nat.id by lia; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeiling. Context {CE__ : Ceiling}.

Lemma ro_C4_of_image : forall m A v, mem_inv ctusegs m -> ro_bytes_b ctusegs A (le4 (Z_to_bv 64 v)) = true -> 0 <= A -> A + 4 <= 2^64 ->
  ro_cells ctusegs m A [C4 (Z_to_bv 64 v)].
Proof.
  intros m A v MI RB A0 A4. pose proof (ro_cells_image ctusegs m A (le4 (Z_to_bv 64 v)) MI RB A0 ltac:(rewrite length_le4; exact A4)) as H.
  destruct H as [_ HB]. split; [cbn; tauto|]. cbn [cells_bytes cbytes app] in HB |- *. exact HB.
Qed.

Lemma mintab_cell : forall m i, mem_inv ctusegs m -> 0 <= i <= 6 -> ro_cells ctusegs m (A_MINTAB + 4 * i) [C4 (Z_to_bv 64 (mintab i))].
Proof.
  intros m i MI Hi. assert (H : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
  destruct H as [->|[->|[->|[->|[->|[->| ->]]]]]]; (apply ro_C4_of_image; [exact MI| vm_compute; reflexivity| unfold A_MINTAB, A_MAXTAB, A_JTAB, A_MDAYS, A_YDAYS; lia| unfold A_MINTAB, A_MAXTAB, A_JTAB, A_MDAYS, A_YDAYS; lia]).
Qed.
Lemma maxtab_cell : forall m i, mem_inv ctusegs m -> 0 <= i <= 6 -> ro_cells ctusegs m (A_MAXTAB + 4 * i) [C4 (Z_to_bv 64 (maxtab i))].
Proof.
  intros m i MI Hi. assert (H : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
  destruct H as [->|[->|[->|[->|[->|[->| ->]]]]]]; (apply ro_C4_of_image; [exact MI| vm_compute; reflexivity| unfold A_MINTAB, A_MAXTAB, A_JTAB, A_MDAYS, A_YDAYS; lia| unfold A_MINTAB, A_MAXTAB, A_JTAB, A_MDAYS, A_YDAYS; lia]).
Qed.
Lemma jtab_cell : forall m i, mem_inv ctusegs m -> 0 <= i <= 6 -> ro_cells ctusegs m (A_JTAB + 4 * i) [C4 (Z_to_bv 64 (jtab i))].
Proof.
  intros m i MI Hi. assert (H : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
  destruct H as [->|[->|[->|[->|[->|[->| ->]]]]]]; (apply ro_C4_of_image; [exact MI| vm_compute; reflexivity| unfold A_MINTAB, A_MAXTAB, A_JTAB, A_MDAYS, A_YDAYS; lia| unfold A_MINTAB, A_MAXTAB, A_JTAB, A_MDAYS, A_YDAYS; lia]).
Qed.
Lemma mdays_cell : forall m k, mem_inv ctusegs m -> 0 <= k <= 11 -> ro_cells ctusegs m (4 * k + A_MDAYS) [C4 (Z_to_bv 64 (mdaystab k))].
Proof.
  intros m k MI Hk. assert (H : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; (apply ro_C4_of_image; [exact MI| vm_compute; reflexivity| unfold A_MINTAB, A_MAXTAB, A_JTAB, A_MDAYS, A_YDAYS; lia| unfold A_MINTAB, A_MAXTAB, A_JTAB, A_MDAYS, A_YDAYS; lia]).
Qed.
Lemma ydays_cell : forall m k, mem_inv ctusegs m -> 0 <= k <= 11 -> ro_cells ctusegs m (4 * k + A_YDAYS) [C4 (Z_to_bv 64 (ydaystab k))].
Proof.
  intros m k MI Hk. assert (H : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; (apply ro_C4_of_image; [exact MI| vm_compute; reflexivity| unfold A_MINTAB, A_MAXTAB, A_JTAB, A_MDAYS, A_YDAYS; lia| unfold A_MINTAB, A_MAXTAB, A_JTAB, A_MDAYS, A_YDAYS; lia]).
Qed.

Lemma mdaystab_ge : forall y k, 0 <= k <= 11 -> k <> 1 -> days_in_month y (k + 1) <= mdaystab k.
Proof.
  intros y k Hk NE. assert (H : k = 0 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; unfold days_in_month, mdaystab; cbv -[leap_year]; try discriminate;
    destruct (leap_year y); cbv; discriminate.
Qed.

End WithCeiling.
