(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange KXTac KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AZ_kit AZ_huf_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma land7 : forall x, 0 <= x -> Z.land x 7 = x - 8 * (x / 8).
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. pose proof (Z.div_mod x 8 ltac:(lia)). lia. Qed.
Ltac land7_lin :=
  repeat match goal with |- context [Z.land ?x 7] => rewrite (land7 x) by lia end;
  repeat match goal with H : context [Z.land ?x 7] |- _ => rewrite (land7 x) in H by lia end.

(* [comment removed for export] *)
Definition SINVA (off len bc : Z) : Prop := off = 0 \/ (1 <= off /\ off + 8 <= len /\ bc <= 64).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma unp_carryW : forall (m mm : amem) W lo0 hi0,
  unpoisoned m lo0 hi0 -> munch W m mm -> aappW W -> 4096 <= lo0 -> lo0 < hi0 -> hi0 <= 2^47 -> unpoisoned mm lo0 hi0.
Proof.
  intros m mm W lo0 hi0 U MU HW L0 LT H0.
  eapply unpoisoned_munch; [exact U | exact MU |].
  apply aappW_shadow_disjoint; [exact HW | | | |]; rewrite ?shad_div; unfold ASHOFF, KEND in *; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Definition aunp (mm : amem) (DST dcap SRC n DT : Z) : Prop :=
  (0 < n -> unpoisoned mm SRC (SRC + n)) /\ unpoisoned mm DT (DT + 16388) /\ (0 < dcap -> unpoisoned mm DST (DST + dcap)).

Lemma aunp_carry : forall (m mm : amem) W DST dcap SRC n DT,
  aunp m DST dcap SRC n DT -> munch W m mm -> aappW W ->
  4096 <= DST -> DST + dcap < 2^47 -> 4096 <= SRC -> SRC + n < 2^47 -> 4096 <= DT -> DT + 16388 < 2^47 ->
  aunp mm DST dcap SRC n DT.
Proof.
  intros m mm W DST dcap SRC n DT (US & UD & UO) MU HW A1 A2 B1 B2 C1 C2. split; [| split].
  - intros Hn. eapply unp_carryW; [exact (US Hn) | exact MU | exact HW | lia | lia | lia].
  - eapply unp_carryW; [exact UD | exact MU | exact HW | lia | lia | lia].
  - intros Hd. eapply unp_carryW; [exact (UO Hd) | exact MU | exact HW | lia | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma aappW_D : forall DST dcap, (dcap <= 0 \/ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST)) -> 0 < dcap ->
  aappW [(DST, DST + dcap)].
Proof. intros DST dcap DA HD. constructor; [cbn [fst snd]; unfold KLOW, KHIGH; lia | constructor]. Qed.
Lemma aappW_cons_hi : forall A B W, 0x10007fff8000 <= A -> aappW W -> aappW ((A, B) :: W).
Proof. intros A B W HA HW. constructor; [cbn [fst snd]; unfold KHIGH; lia | exact HW]. Qed.
Lemma aappW_cons_D : forall DST dcap W, (dcap <= 0 \/ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST)) -> 0 < dcap ->
  aappW W -> aappW ((DST, DST + dcap) :: W).
Proof. intros DST dcap W DA HD HW. constructor; [cbn [fst snd]; unfold KLOW, KHIGH; lia | exact HW]. Qed.
Lemma aappW_nil : aappW [].
Proof. constructor. Qed.

(* [comment removed for export] *)
Lemma munch_drop_empty : forall (m mm : amem) A W, munch ((A, A) :: W) m mm -> munch W m mm.
Proof.
  intros m mm A W MU. eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside]. split; [lia | exact Hx].
Qed.

Lemma aunp_carryD : forall (m mm : amem) W DST dcap SRC n DT,
  aunp m DST dcap SRC n DT -> munch ((DST, DST + dcap) :: W) m mm -> aappW W ->
  (dcap <= 0 \/ (DST + dcap <= 0x7fff7000 \/ 0x10007fff8000 <= DST)) -> 0 <= dcap ->
  4096 <= DST -> DST + dcap < 2^47 -> 4096 <= SRC -> SRC + n < 2^47 -> 4096 <= DT -> DT + 16388 < 2^47 ->
  aunp mm DST dcap SRC n DT.
Proof.
  intros m mm W DST dcap SRC n DT AU MU HW DA D0 A1 A2 B1 B2 C1 C2.
  destruct (Z_lt_le_dec 0 dcap) as [HD|HD].
  - eapply aunp_carry; [exact AU | exact MU | apply aappW_cons_D; [exact DA | exact HD | exact HW] | lia..].
  - replace (DST + dcap) with DST in MU by lia.
    eapply aunp_carry; [exact AU | exact (munch_drop_empty _ _ _ _ MU) | exact HW | lia..].
Qed.

(* [comment removed for export] *)
Lemma rng_shspanZ_sub : forall RNG A n S len, rng RNG (shad A) (shspan A n) -> A <= S -> 0 <= len -> S + len <= A + n -> 0 <= A ->
  rng RNG (KXSHLO + S / 8) (shspanZ S len).
Proof.
  intros RNG A n S len H H1 H2 H3 H4. apply (shad_shspan_rng RNG S len (shad A) (shspan A n) H).
  - rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
  - unfold shspanZ, shspan. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
  - lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma x42_lenword : forall (DT tl : Z) (dtb : list byte) mm idx,
  bytes_at bsegs mm DT dtb -> zlen dtb = 16388 -> huf_x2_ok dtb tl -> 1 <= tl <= 12 -> 0 <= idx < 2 ^ tl ->
  exists lv, 1 <= lv <= 2 /\ rdn bsegs mm (wa (DT + 4 * idx + 7)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 lv)).
Proof.
  intros DT tl dtb mm idx DTB DL X2 TL HI. destruct (X2 idx HI) as (b & NTH & BR).
  exists (bv_unsigned b). split; [exact BR|].
  assert (L : (Z.to_nat (4 * idx + 7) + 1 <= length dtb)%nat).
  { assert (Z.to_nat (4 * idx + 7) < length dtb)%nat by (apply nth_error_Some; rewrite NTH; discriminate). lia. }
  pose proof (bytes_at_rdn bsegs mm DT dtb (Z.to_nat (4 * idx + 7)) 1 DTB L) as R.
  rewrite Z2Nat.id in R by lia. replace (DT + 4 * idx + 7) with (DT + (4 * idx + 7)) by lia. rewrite R.
  rewrite (firstn1_skipn _ _ _ NTH). unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal. f_equal.
  symmetry. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 8 b) as RB. unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in RB.
  rewrite Z_to_bv_unsigned. rewrite !bv_wrap_small; [reflexivity| |]; unfold bv_modulus.
  - change (2 ^ Z.of_N 64) with (2^64). lia.
  - change (2 ^ Z.of_N 8) with 256. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). lia.
Qed.

(* [comment removed for export] *)
Lemma x42_idx_lt : forall (tl : Z) (w : word) e, e = 64 - tl -> 1 <= tl <= 12 -> 0 <= bv_unsigned w / 2 ^ e < 2 ^ tl.
Proof.
  intros tl w e -> TL. pose proof (bv_unsigned_in_range 64 w) as HX. unfold bv_modulus in HX. change (2 ^ Z.of_N 64) with (2^64) in HX.
  split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (64 - tl + tl) with 64 by lia. lia.
Qed.

Lemma x42_len_ob : forall lv, 1 <= lv <= 2 -> 1 <= bv_unsigned (Z_to_bv 64 lv) <= 2.
Proof.
  intros lv H. rewrite Z_to_bv_unsigned, bv_wrap_small; [exact H|]. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). lia.
Qed.

(* [comment removed for export] *)
Lemma x42_tblA : forall (dtb : list byte) (tl DT : Z) (mm : amem),
  zlen dtb = 16388 -> 1 <= tl <= 12 -> huf_x2_ok dtb tl -> bytes_at bsegs mm DT dtb -> tbl_in_log bsegs mm DT (64 - tl) 4 7 1 2.
Proof.
  intros dtb tl DT mm DL TL X2OK DTB. apply (tbl_in_log_bytes_at bsegs mm DT dtb (64 - tl) 4 7 1 2 DTB); [lia | lia |].
  intros i Hi. replace (64 - (64 - tl)) with tl in Hi by lia. exact (X2OK i Hi).
Qed.

(* [comment removed for export] *)
Lemma disjoint_from_aboveK42 : forall W A n K, Forall (fun iv : Z * Z => K <= fst iv) W -> A + n <= K -> disjoint_from W A n.
Proof.
  intros W A n K HW LE. induction HW as [|[x y] W Hx HW IH]; cbn [disjoint_from]; [exact I|].
  cbn [fst] in Hx. split; [lia | exact IH].
Qed.
Lemma art_transportW42 : forall W m m', art m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => 0xd1740 <= fst iv) W -> art m'.
Proof.
  intros W m m' (GOT & RIC & SHB & INI & LAY & REAL) MU WM HW.
  unfold art. repeat split.
  all: first [ eapply rw_cells_transport; [eassumption| exact MU| exact WM| eapply disjoint_from_aboveK42; [exact HW| cbn; lia]]
             | eapply ro_cells_transport; [eassumption| exact MU| eapply disjoint_from_aboveK42; [exact HW| cbn; lia]] ].
Qed.
End CANSEC1.
