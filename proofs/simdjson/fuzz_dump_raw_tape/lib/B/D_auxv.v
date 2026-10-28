(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Definition EL_AUXV_CELL : Z := 0x6cc080.

Definition EL_XDATA1 : Z := 0x172ea8.
Definition EL_XDATA2 : Z := 0x173288.
Definition el_xdataA (m : mem) : Prop :=
  rw_cells bsegs m 0x172ea8 [C8 (Z_to_bv 64 0x10ba00)]
  /\ rw_cells bsegs m 0x173288 [C8 (Z_to_bv 64 0xee800); C8 (Z_to_bv 64 0xee90c)].
Lemma el_xdata_agree : forall m m' : mem, el_xdataA m ->
  agree_on (fun x => 0x172ea8 <= x < 0x172ea8 + 8 \/ 0x173288 <= x < 0x173288 + 16) m m' -> el_xdataA m'.
Proof.
  intros m m' [X1 X2] AG. split.
  - apply (rw_cells_agree_nw bsegs m m' _ _ X1). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. left. lia.
  - apply (rw_cells_agree_nw bsegs m m' _ _ X2). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. right. lia.
Qed.
Definition EL_AT_PHDR : Z := 0x10040.

Definition el_auxv_words (x16 x11 rnd : Z) : list Z :=
  [3; EL_AT_PHDR; 4; 56; 5; 11; 16; x16; 6; 4096; 11; x11; 12; x11; 23; 0; 25; rnd; 0; 0].

Definition el_auxvA (lo : Z) (m : mem) : Prop :=
  exists av x16 x11 rnd,
    ro_cells bsegs m EL_AUXV_CELL [C8 (Z_to_bv 64 av)]
    /\ bytes_at bsegs m av (u64s (map (Z_to_bv 64) (el_auxv_words x16 x11 rnd)))
    /\ lo <= av /\ av + 160 <= USTACK_TOP /\ av mod 8 = 0 /\ 0 <= x16 < 2^64 /\ 0 <= x11 < 2^64 /\ 0 <= rnd < 2^64.

Definition auxc (x : Z) : Prop := EL_AUXV_CELL <= x < EL_AUXV_CELL + 8.

Lemma el_auxv_weaken : forall lo lo' m, el_auxvA lo m -> lo' <= lo -> el_auxvA lo' m.
Proof.
  intros lo lo' m (av & x16 & x11 & rnd & C & B & H) Hle. exists av, x16, x11, rnd. split; [exact C|]. split; [exact B|]. lia.
Qed.

Lemma el_auxv_agree : forall lo m m', el_auxvA lo m ->
  agree_on auxc m m' -> agree_on (fun x => lo <= x < USTACK_TOP) m m' -> el_auxvA lo m'.
Proof.
  intros lo m m' (av & x16 & x11 & rnd & C & B & H) AGC AGS. exists av, x16, x11, rnd. split; [| split; [| exact H]].
  - apply (ro_cells_agree bsegs m m' _ _ C). intros x Hx. apply AGC. unfold auxc. cbn [cells_size csize Nat.add] in Hx. lia.
  - apply (bytes_at_agree bsegs m m' _ _ B). intros x Hx. apply AGS. cbv beta.
    rewrite u64s_length, length_map in Hx. unfold el_auxv_words in Hx. cbn [length Nat.mul Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia.
Qed.

Lemma auxc_client_static : forall x, auxc x -> client_static x.
Proof.
  intros x Hx. unfold auxc, EL_AUXV_CELL in Hx. split.
  - exists 0x6aa210, 0x6cd7d8. split; [unfold CLIENT_STATIC; cbn; tauto| lia].
  - intros (lo & hi & Hin & Hlh). unfold RT_STATIC in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

Lemma auxc_of_pres : forall live frames sp m m', rt_pres live frames sp m m' -> agree_on auxc m m'.
Proof. intros live frames sp m m' P x Hx. apply P. right; left. exact (auxc_client_static _ Hx). Qed.

Lemma auxc_of_pres_ex : forall live frames sp d n m m', rt_pres_ex live frames sp d n m m' ->
  (d + n <= EL_AUXV_CELL \/ EL_AUXV_CELL + 8 <= d) -> agree_on auxc m m'.
Proof.
  intros live frames sp d n m m' P Hd x Hx. apply P; [right; left; exact (auxc_client_static _ Hx)|]. unfold auxc in Hx. lia.
Qed.

Lemma auxc_of_pres_fp : forall live frames sp W m m', rt_pres_fp live frames sp W m m' ->
  (forall x, auxc x -> outside W x) -> agree_on auxc m m'.
Proof. intros live frames sp W m m' P HW x Hx. apply P; [right; left; exact (auxc_client_static _ Hx)| exact (HW _ Hx)]. Qed.

Lemma auxc_of_munch : forall W m m', munch W m m' -> (forall x, auxc x -> outside W x) -> agree_on auxc m m'.
Proof. intros W m m' MU HW x Hx. apply MU. exact (HW _ Hx). Qed.

Lemma agree_on_auxc_trans : forall m1 m2 m3, agree_on auxc m1 m2 -> agree_on auxc m2 m3 -> agree_on auxc m1 m3.
Proof. intros m1 m2 m3 A B x Hx. rewrite (B x Hx). exact (A x Hx). Qed.

Lemma el_auxv_munch : forall lo W m m', el_auxvA lo m -> munch W m m' ->
  (forall x, auxc x \/ lo <= x < USTACK_TOP -> outside W x) -> el_auxvA lo m'.
Proof.
  intros lo W m m' H MU HW. apply (el_auxv_agree lo m m' H).
  - apply (auxc_of_munch W m m' MU). intros x Hx. apply HW. left. exact Hx.
  - intros a Ha. apply MU. apply HW. right. exact Ha.
Qed.

Lemma el_auxv_pres : forall lo live frames sp m m', el_auxvA lo m -> rt_pres live frames sp m m' -> sp <= lo -> el_auxvA lo m'.
Proof.
  intros lo live frames sp m m' H P Hsp. apply (el_auxv_agree lo m m' H (auxc_of_pres _ _ _ _ _ P)).
  intros a Ha. apply P. left. cbv beta in Ha. lia.
Qed.

Lemma el_auxv_pres_ex : forall lo live frames sp d n m m', el_auxvA lo m -> rt_pres_ex live frames sp d n m m' -> sp <= lo ->
  (d + n <= EL_AUXV_CELL \/ EL_AUXV_CELL + 8 <= d) -> d + n <= lo -> el_auxvA lo m'.
Proof.
  intros lo live frames sp d n m m' H P Hsp Hd Hdl. apply (el_auxv_agree lo m m' H (auxc_of_pres_ex _ _ _ _ _ _ _ P Hd)).
  intros a Ha. cbv beta in Ha. apply P; [left; lia| lia].
Qed.

Lemma el_auxv_pres_fp : forall lo live frames sp W m m', el_auxvA lo m -> rt_pres_fp live frames sp W m m' -> sp <= lo ->
  (forall x, auxc x \/ lo <= x < USTACK_TOP -> outside W x) -> el_auxvA lo m'.
Proof.
  intros lo live frames sp W m m' H P Hsp HW. apply (el_auxv_agree lo m m' H).
  - apply (auxc_of_pres_fp _ _ _ _ _ _ P). intros x Hx. apply HW. left. exact Hx.
  - intros a Ha. cbv beta in Ha. apply P; [left; lia| apply HW; right; exact Ha].
Qed.

Lemma auxc_range : forall x, auxc x -> 0x6cc080 <= x < 0x6cc088.
Proof. intros x Hx. unfold auxc, EL_AUXV_CELL in Hx. lia. Qed.

Lemma bytes_at_u64s : forall (m : mem) a ws,
  0 <= a -> a + 8 * Z.of_nat (length ws) <= 2 ^ 64 ->
  (forall j w, nth_error ws j = Some w -> bytes_at bsegs m (a + 8 * Z.of_nat j) (le8 w)) -> bytes_at bsegs m a (u64s ws).
Proof.
  intros m a ws. revert a. induction ws as [|w ws IH]; intros a Ha Hl H.
  - apply bytes_at_nil. cbn [length Z.of_nat] in Hl. lia.
  - cbn [u64s]. apply (proj2 (bytes_at_app _ _ _ _ _)). split.
    + pose proof (H 0%nat w eq_refl) as X. rewrite Z.mul_0_r, Z.add_0_r in X. exact X.
    + rewrite length_le8. change (Z.of_nat 8) with 8. apply IH; [lia| cbn [length] in Hl; lia|].
      intros j w' Hn. pose proof (H (S j) w' Hn) as X. replace (a + 8 * Z.of_nat (S j)) with (a + 8 + 8 * Z.of_nat j) in X by lia. exact X.
Qed.
