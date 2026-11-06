(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegLin SegTmpl SegGhost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module SDG.

Local Notation u := bv_unsigned.

Section Mem.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition mbr (M : word -> option byte) (a : Z) : Z :=
  match (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 a) end) with
  | Some b => u b | None => 0 end.

Fixpoint mdec_n (M : word -> option byte) (a : Z) (n : nat) : Z :=
  match n with O => 0 | S k => 10 * mdec_n M a k + (mbr M (a + Z.of_nat k) - 48) end.
Definition mdec (M : word -> option byte) (a n : Z) : Z := mdec_n M a (Z.to_nat n).
Definition isdig (c : Z) : Prop := 48 <= c <= 57.

Lemma mdec_step : forall M a n, 0 <= n -> mdec M a (n + 1) = 10 * mdec M a n + (mbr M (a + n) - 48).
Proof.
  intros M a n H. unfold mdec. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  cbn [mdec_n]. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma mdec_n_bound : forall M a n, (forall i, 0 <= i < Z.of_nat n -> isdig (mbr M (a + i))) -> 0 <= mdec_n M a n < 10 ^ Z.of_nat n.
Proof.
  intros M a n. induction n as [|n IH]; intros HD.
  - cbn. lia.
  - cbn [mdec_n]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    assert (IH' : 0 <= mdec_n M a n < 10 ^ Z.of_nat n) by (apply IH; intros i Hi; apply HD; lia).
    pose proof (HD (Z.of_nat n) ltac:(lia)) as Hd. unfold isdig in Hd. nia.
Qed.

Lemma mdec_bound : forall M a n, 0 <= n -> (forall i, 0 <= i < n -> isdig (mbr M (a + i))) -> 0 <= mdec M a n < 10 ^ n.
Proof.
  intros M a n H HD. unfold mdec. pose proof (mdec_n_bound M a (Z.to_nat n)) as B. rewrite Z2Nat.id in B by lia. apply B.
  intros i Hi. apply HD. lia.
Qed.

(* [comment removed for export] *)
Lemma mdec_n_zero_head : forall M a n, mbr M a = 48 -> mdec_n M a (S n) = mdec_n M (a + 1) n.
Proof.
  intros M a n Hz. induction n as [|n IH].
  - cbn [mdec_n]. rewrite Z.add_0_r, Hz. reflexivity.
  - cbn [mdec_n] in *. rewrite IH. f_equal. f_equal. f_equal. lia.
Qed.

Lemma mdec_zeros : forall M a z n, 0 <= z <= n -> (forall i, 0 <= i < z -> mbr M (a + i) = 48) -> mdec M a n = mdec M (a + z) (n - z).
Proof.
  intros M a z n Hz HZ. unfold mdec. remember (Z.to_nat z) as k eqn:Hk. revert a z n Hz HZ Hk.
  induction k as [|k IH]; intros a z n Hz HZ Hk.
  - assert (z = 0) by lia. subst z. rewrite Z.add_0_r, Z.sub_0_r. reflexivity.
  - replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia.
    rewrite mdec_n_zero_head by (specialize (HZ 0 ltac:(lia)); rewrite Z.add_0_r in HZ; exact HZ).
    replace (Z.to_nat (n - 1)) with (Z.to_nat ((n - 1))) by reflexivity.
    rewrite (IH (a + 1) (z - 1) (n - 1)); [| lia | | lia].
    + replace (a + 1 + (z - 1)) with (a + z) by lia. replace (n - 1 - (z - 1)) with (n - z) by lia. reflexivity.
    + intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. apply HZ. lia.
Qed.

Lemma mbr_frame : forall M M' a, M' (Z_to_bv 64 a) = M (Z_to_bv 64 a) -> mbr M' a = mbr M a.
Proof. intros M M' a H. unfold mbr. rewrite H. reflexivity. Qed.

Lemma mdec_n_frame : forall M M' a n, (forall i, 0 <= i < Z.of_nat n -> M' (Z_to_bv 64 (a + i)) = M (Z_to_bv 64 (a + i))) ->
  mdec_n M' a n = mdec_n M a n.
Proof.
  intros M M' a n. induction n as [|n IH]; intros H; [reflexivity|].
  cbn [mdec_n]. rewrite IH by (intros i Hi; apply H; lia). rewrite (mbr_frame M M') by (apply H; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Definition gdm (id : nat) (args : list word) (M : word -> option byte) : Prop :=
  match id, args with
  | 20%nat, [a; n; x] =>
      u n <= 2 ^ 20 /\ u a + u n < 2 ^ 64 /\ (forall i, 0 <= i < u n -> isdig (mbr M (u a + i)))
      /\ u x = mdec M (u a) (u n) mod 2 ^ 64
  | 21%nat, [p; d] => mbr M (u p) = u d + 48 /\ u d <= 9
  | 22%nat, [a; z; n; x] =>
      u z <= u n <= 2 ^ 20 /\ u a + u n + 1 < 2 ^ 64 /\ (forall i, 0 <= i < u z -> mbr M (u a + i) = 48)
      /\ (forall i, 0 <= i < u n -> isdig (mbr M (u a + i))) /\ ~ isdig (mbr M (u a + u n))
      /\ u x = mdec M (u a) (u n) mod 2 ^ 64
  | _, _ => False
  end.

Definition gpx (GP : nat -> list word -> (word -> option byte) -> Prop) (id : nat) (args : list word) (M : word -> option byte) : Prop :=
  if Nat.leb 20 id then gdm id args M else GP id args M.

Definition gfpd (id : nat) (args : list expr) : list SG.gwin :=
  match id, args with
  | 20%nat, [a; n; _] => [(a, 0, n)]
  | 21%nat, [p; _] => [(p, 0, ELit 1)]
  | 22%nat, [a; _; n; _] => [(a, 0, EAlu ALU_ADD n (ELit 1))]
  | _, _ => []
  end.
Definition gfpx (gfp : nat -> list expr -> list SG.gwin) (id : nat) (args : list expr) : list SG.gwin :=
  if Nat.leb 20 id then gfpd id args else gfp id args.

Lemma gdm_frame : forall id args E (M M' : word -> option byte),
  (forall x : word, (exists w, In w (gfpd id args) /\ let '(lo, hi) := SG.win_den E w in (lo <= u x < hi)%Z) -> M' x = M x) ->
  gdm id (map (edenot E) args) M -> gdm id (map (edenot E) args) M'.
Proof.
  intros id args E M M' HF H.
  destruct id as [|id]; [destruct args; contradiction|].
  do 19 (destruct id as [|id]; [destruct args as [|? [|? [|? [|? ?]]]]; cbn in H; contradiction|]).
  destruct id as [|[|[|id]]].
  - (* [comment removed for export] *) destruct args as [|a [|n [|x [|? ?]]]]; cbn in H |- *; try contradiction.
    destruct H as (H1 & H2 & H3 & H4).
    assert (FR : forall i, 0 <= i < u (edenot E n) -> M' (Z_to_bv 64 (u (edenot E a) + i)) = M (Z_to_bv 64 (u (edenot E a) + i))).
    { intros i Hi. apply HF. exists (a, 0, n). split; [left; reflexivity|]. cbn [SG.win_den].
      rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
      rewrite Z.mod_small by (pose proof (bv_unsigned_in_range _ (edenot E a)); lia). lia. }
    split; [exact H1|]. split; [exact H2|]. split.
    + intros i Hi. rewrite (mbr_frame M M') by (apply FR; exact Hi). apply H3. exact Hi.
    + rewrite H4. unfold mdec. rewrite (mdec_n_frame M M'); [reflexivity|].
      intros i Hi. rewrite Z2Nat.id in Hi by lia. apply FR. exact Hi.
  - (* [comment removed for export] *) destruct args as [|p [|d [|? ?]]]; cbn in H |- *; try contradiction.
    destruct H as (H1 & H2). split; [|exact H2]. rewrite (mbr_frame M M'); [exact H1|].
    apply HF. exists (p, 0, ELit 1). split; [left; reflexivity|]. cbn [SG.win_den edenot].
    rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    change (1 mod 2 ^ 64) with 1.
    rewrite Z.mod_small by (pose proof (bv_unsigned_in_range _ (edenot E p)); unfold bv_modulus in *; cbn in *; lia). lia.
  - (* [comment removed for export] *) destruct args as [|a [|z [|n [|x [|? ?]]]]]; cbn in H |- *; try contradiction.
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6).
    assert (FR : forall i, 0 <= i <= u (edenot E n) -> M' (Z_to_bv 64 (u (edenot E a) + i)) = M (Z_to_bv 64 (u (edenot E a) + i))).
    { intros i Hi. apply HF. exists (a, 0, EAlu ALU_ADD n (ELit 1)). split; [left; reflexivity|]. cbn [SG.win_den edenot].
      rewrite alu_add. unfold v_add. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
      change (1 mod 2 ^ 64) with 1.
      rewrite (Z.mod_small (u (edenot E n) + 1)) by (pose proof (bv_unsigned_in_range _ (edenot E n)); unfold bv_modulus in *; cbn in *; lia).
      rewrite Z.mod_small by (pose proof (bv_unsigned_in_range _ (edenot E a)); unfold bv_modulus in *; cbn in *; lia). lia. }
    pose proof (bv_unsigned_in_range _ (edenot E n)) as Rn. pose proof (bv_unsigned_in_range _ (edenot E z)) as Rz.
    unfold bv_modulus in Rn, Rz.
    split; [exact H1|]. split; [exact H2|]. split; [|split; [|split]].
    + intros i Hi. rewrite (mbr_frame M M') by (apply FR; lia). apply H3. exact Hi.
    + intros i Hi. rewrite (mbr_frame M M') by (apply FR; lia). apply H4. exact Hi.
    + rewrite (mbr_frame M M') by (apply FR; lia). exact H5.
    + rewrite H6. unfold mdec. rewrite (mdec_n_frame M M'); [reflexivity|].
      intros i Hi. rewrite Z2Nat.id in Hi by lia. apply FR. lia.
  - destruct args as [|? [|? [|? [|? ?]]]]; cbn in H; contradiction.
Qed.

Lemma gpx_frame : forall GP gfp, SG.gp_frameP GP gfp -> SG.gp_frameP (gpx GP) (gfpx gfp).
Proof.
  intros GP gfp HF id args E M M' Hx H. unfold gpx, gfpx in *. destruct (Nat.leb 20 id).
  - exact (gdm_frame id args E M M' Hx H).
  - exact (HF id args E M M' Hx H).
Qed.

End Mem.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Chk.
Variable segs : list Segment.

Definition leqx (a b : expr) : bool :=
  match lin_of (mkAlu ALU_SUB a b) with (c, []) => Z.eqb (c mod 2 ^ 64) 0 | _ => false end.
Definition x1 (v : nat) : expr := EExt false 0 1 (EVar v).
Definition rd1 (s : sidecond) : option (expr * nat) :=
  match s with
  | SCReadBase a 1%nat false (EVar v) => Some (EAlu ALU_ADD (a_base a) (ELit (a_off a)), v)
  | _ => None
  end.
Definition kimp (kn : list kentry) (K : kentry) : bool := ST.kimplied segs kn K.
Definition dtest (v : nat) : expr := EAlu ALU_AND (EAlu ALU_ADD (x1 v) (ELit (-48))) (ELit 255).
Definition dig_known (kn : list kentry) (v : nat) : bool :=
  if kimp kn (KRange (x1 v) 48 57) then true else kimp kn (KRange (dtest v) 0 9).
Definition zero_known (kn : list kentry) (v : nat) : bool :=
  if kimp kn (KRange (x1 v) 48 48) then true else kimp kn (KRange (EVar v) 48 48).
Definition nodig_known (kn : list kentry) (v : nat) : bool := kimp kn (KRange (dtest v) 10 (2 ^ 64 - 1)).
Definition atoms (id : nat) (l : list ST.gatom) : list (list expr) :=
  map ST.g_args (List.filter (fun g => Nat.eqb (ST.g_id g) id) l).
Definition eadd (a b : expr) : expr := mkAlu ALU_ADD a b.
Definition e1 (a : expr) : expr := mkAlu ALU_ADD a (ELit 1).

(* [comment removed for export] *)
Definition rd_at (path : list sidecond) (P : expr) (f : nat -> bool) : bool :=
  SLin.lex (fun s => match rd1 s with Some (AP, v) => if leqx AP P then f v else false | None => false end) path.

Definition step_val (X X' D : expr) : bool :=
  if leqx X' (eadd (mkMd M_MUL (ELit 10) X) D) then true
  else leqx X' (eadd (mkMd M_MUL (ELit 10) X) (mkAlu ALU_AND D (ELit 255))).

(* [comment removed for export] *)
Definition gdb_step (src : list ST.gatom) (A N X X' : expr) : bool :=
  SLin.lex (fun b => match b with [P; D] => if leqx P (eadd A N) then step_val X X' D else false | _ => false end) (atoms 21 src).

Definition gdbm_ok (kn : list kentry) (path : list sidecond) (lg : list sentry) (P' D' : expr) : bool :=
  if SG.log_apart kn lg [(P', 0, ELit 1)] then
    rd_at path P' (fun v => if dig_known kn v then leqx D' (mkAlu ALU_SUB (x1 v) (ELit 48)) else false)
  else false.

Definition gdm_ok (kn : list kentry) (src : list ST.gatom) (lg : list sentry) (A' N' X' : expr) : bool :=
  if kimp kn (KRange N' 0 0) then leqx X' (ELit 0) else
  if SG.log_apart kn lg [(A', 0, N')] then
    SLin.lex (fun a => match a with
      | [A; N; X] => if leqx A' A then if leqx N' (e1 N) then if kimp kn (KRange N 0 (2 ^ 20 - 1)) then
                       if kimp kn (KRange A 0 (2 ^ 62)) then gdb_step src A N X X' else false else false else false else false
      | _ => false end) (atoms 20 src)
  else false.

Definition gdzm_ok (kn : list kentry) (path : list sidecond) (src : list ST.gatom) (lg : list sentry) (A' Z' N' X' : expr) : bool :=
  if SG.log_apart kn lg [(A', 0, e1 N')] then
    if SLin.lex (fun a => match a with
         | [A; N; X] => if leqx A' A then if leqx N' (e1 N) then if leqx Z' (ELit 1) then if kimp kn (KRange N 0 (2 ^ 20 - 2)) then
                          if kimp kn (KRange A 0 (2 ^ 62)) then if gdb_step src A N X X' then
                          if rd_at path (e1 (eadd A N)) (nodig_known kn) then rd_at path A (zero_known kn)
                          else false else false else false else false else false else false else false
         | _ => false end) (atoms 20 src) then true
    else SLin.lex (fun a => match a with
         | [A; Z; N; X] => if leqx A' A then if leqx N' N then if leqx X' X then if leqx Z' (e1 Z) then
                             rd_at path (eadd A Z) (zero_known kn) else false else false else false else false
         | _ => false end) (atoms 22 src)
  else false.

Definition atom_ok (kn : list kentry) (path : list sidecond) (src : list ST.gatom) (lg : list sentry) (g : ST.gatom) : bool :=
  match ST.g_id g, ST.g_args g with
  | 20%nat, [A'; N'; X'] => gdm_ok kn src lg A' N' X'
  | 21%nat, [P'; D'] => gdbm_ok kn path lg P' D'
  | 22%nat, [A'; Z'; N'; X'] => gdzm_ok kn path src lg A' Z' N' X'
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition le18 (kn : list kentry) (A P : expr) : bool :=
  if kimp kn (KRange (mkAlu ALU_SUB P A) 0 18) then true else kimp kn (KRange (mkAlu ALU_SUB (eadd A (ELit 18)) P) 0 (2 ^ 62)).

Definition fact_ok (kn : list kentry) (src : list ST.gatom) (K : kentry) : bool :=
  match K with
  | KRange X' lo hi =>
      if Z.eqb lo 0 then if Z.eqb hi 999999999999999999 then
        if SLin.lex (fun a => match a with
             | [A; N; X] => if leqx X' X then kimp kn (KRange N 0 18)
                            else if kimp kn (KRange N 0 17) then gdb_step src A N X X' else false
             | _ => false end) (atoms 20 src) then true
        else SLin.lex (fun a => match a with
             | [A; Z; N; X] => if leqx X' X then le18 kn Z N else false
             | _ => false end) (atoms 22 src)
      else false else false
  | _ => false
  end.

Definition mine (g : ST.gatom) : bool := Nat.leb 20 (ST.g_id g).

Definition gsplit (g0 : SG.vc -> bool) (c : SG.vc) : bool :=
  let kn := SG.vc_kn c in
  if SLin.lall (atom_ok kn (SG.vc_path c) (SG.vc_src c) (SG.vc_log c)) (List.filter mine (SG.vc_tgt c)) then
    g0 (SG.VC kn (SG.vc_path c) (SG.vc_log c) (List.filter (fun g => negb (mine g)) (SG.vc_src c))
              (List.filter (fun g => negb (mine g)) (SG.vc_tgt c)) (List.filter (fun K => negb (fact_ok kn (SG.vc_src c) K)) (SG.vc_facts c)))
  else false.

End Chk.

End SDG.
