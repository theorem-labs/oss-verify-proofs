(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require PropExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import Tac Image ZBridge Walk Arr InitMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CkP Require Import RegsFull BridgeKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import PImg.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0 Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma le8_lit : forall z, 0 <= z < 2^64 -> le8 (Z_to_bv 64 z) = Z_to_le_bytes 8 z.
Proof. intros z Hz. unfold le8, word_to_le_bytes. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma le4_lit : forall z, 0 <= z < 2^32 -> le4 (Z_to_bv 64 z) = Z_to_le_bytes 4 z.
Proof. intros z Hz. unfold le4, word_to_le_bytes. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma ovr_of_rdn_Z : forall (M : word -> option byte) a a' z,
  OP.rdn psegs M (Z_to_bv 64 a) 8 = Some (Z_to_le_bytes 8 z) -> 0 <= z < 2^64 -> a = a' ->
  ov_read_bytes psegs M (Z_to_bv 64 a') 8 = Some (le8 (Z_to_bv 64 z)).
Proof. intros M a a' z H Hz <-. rewrite ov_rdn, le8_lit by lia. exact H. Qed.



Lemma bytes_at_of_rdn : forall (M : word -> option byte) n a bs,
  OP.rdn psegs M (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2^64 -> bytes_at psegs M a bs.
Proof.
  intros M n. induction n as [|n IH]; intros a bs H Ha Hn.
  - cbn in H. injection H as <-. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - rewrite rdn_conv, rdn_unfold in H. fold (wa a) in H.
    destruct (mrd psegs M (wa a)) as [b|] eqn:E; [|discriminate].
    rewrite wa_succ, <- rdn_conv in H.
    destruct (OP.rdn psegs M (wa (a + 1)) n) as [r|] eqn:E2; [|discriminate]. injection H as <-.
    pose proof (IH (a + 1) r E2 ltac:(lia) ltac:(lia)) as (_ & L & B).
    split; [lia|]. split; [cbn [length]; lia|].
    intros [|i] Hi; cbn [nth_error].
    + rewrite Z.add_0_r. exact E.
    + replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply B. cbn in Hi. lia.
Qed.

Lemma ro_C8_of_rdn_w : forall (M : word -> option byte) a (v : word),
  OP.rdn psegs M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v) -> 0 <= a -> a + 8 <= 2^64 -> ro_cells psegs M a [C8 v].
Proof.
  intros M a v H Ha H8. split; [cbn; split; exact I|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  exact (bytes_at_of_rdn M 8 a _ H Ha H8).
Qed.

Lemma ro_C8_of_rdn_Z : forall (M : word -> option byte) a z,
  OP.rdn psegs M (Z_to_bv 64 a) 8 = Some (Z_to_le_bytes 8 z) -> 0 <= z < 2^64 -> 0 <= a -> a + 8 <= 2^64 ->
  ro_cells psegs M a [C8 (Z_to_bv 64 z)].
Proof. intros M a z H Hz Ha H8. apply ro_C8_of_rdn_w; [| exact Ha| exact H8]. unfold word_to_le_bytes. rewrite unsigned_lit by lia. exact H. Qed.

Lemma ro_C4_of_rdn_Z : forall (M : word -> option byte) a z,
  OP.rdn psegs M (Z_to_bv 64 a) 4 = Some (Z_to_le_bytes 4 z) -> 0 <= z < 2^32 -> 0 <= a -> a + 4 <= 2^64 ->
  ro_cells psegs M a [C4 (Z_to_bv 64 z)].
Proof.
  intros M a z H Hz Ha H4. split; [cbn; split; exact I|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  rewrite le4_lit by lia. exact (bytes_at_of_rdn M 4 a _ H Ha H4).
Qed.

Ltac cell_fact H k :=
  lazymatch goal with |- OP.rdn _ ?m (Z_to_bv 64 ?E) ?n = Some _ =>
    lazymatch type of H with
    | rw_cells ?segs m ?A ?cs =>
      let c := eval_cell_at cs k in
      lazymatch c with Some ?c0 =>
        let X := fresh "X" in
        pose proof (rw_cells_read_at segs m A cs k c0 n (wa (A + Z.of_nat k)) H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as X;
        rewrite ov_rdn in X; cbv beta iota delta [cbytes] in X;
        replace E with (A + Z.of_nat k) by (cbn; lia);
        first [ exact X | rewrite le8_lit in X by lia; first [ exact X | replace_val X ] | rewrite le4_lit in X by lia; first [ exact X | replace_val X ]
              | unfold le4, le8 in X; rewrite unsigned_lit in X by lia; first [ exact X | replace_val X ] ]
      end
    | ro_cells ?segs m ?A ?cs =>
      let c := eval_cell_at cs k in
      lazymatch c with Some ?c0 =>
        let X := fresh "X" in
        pose proof (ro_cells_read_at segs m A cs k c0 n (wa (A + Z.of_nat k)) H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as X;
        rewrite ov_rdn in X; cbv beta iota delta [cbytes] in X;
        replace E with (A + Z.of_nat k) by (cbn; lia);
        first [ exact X | rewrite le8_lit in X by lia; first [ exact X | replace_val X ] | rewrite le4_lit in X by lia; first [ exact X | replace_val X ]
              | unfold le4, le8 in X; rewrite unsigned_lit in X by lia; first [ exact X | replace_val X ] ]
      end
    end end
with replace_val X :=
  lazymatch type of X with _ = Some (Z_to_le_bytes _ ?z) =>
    lazymatch goal with |- _ = Some (Z_to_le_bytes _ ?z') => replace z' with z by lia; exact X end end.

Ltac br_false := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let C := fresh "C" in assert (C : c = false);
    [ unfold bv_eqb; rewrite !unsigned_lit by lia; first [apply Z.eqb_neq; lia | apply negb_false_iff, Z.eqb_eq; lia] | rewrite C; cbv iota; clear C ] end.
Ltac br_true := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let C := fresh "C" in assert (C : c = true);
    [ unfold bv_eqb; rewrite !unsigned_lit by lia; first [apply Z.eqb_eq; lia | apply negb_true_iff, Z.eqb_neq; lia] | rewrite C; cbv iota; clear C ] end.

Definition RELRO_LO : Z := 0x2c000.
Definition RELRO_HI : Z := 0x2c3f8.
Definition relro_pristine (M : word -> option byte) : Prop :=
  forall x : word, RELRO_LO <= bv_unsigned x < RELRO_HI -> M x = None.


Lemma bytes_at_pristine : forall (M : word -> option byte) a n bs,
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat n -> M x = None) ->
  image_bytes psegs a n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2^64 -> bytes_at psegs M a bs.
Proof.
  intros M a n. revert a. induction n as [|n IH]; intros a bs HP HI Ha Hn; cbn [image_bytes] in HI.
  - injection HI as <-. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (seg_rom psegs (wa a)) as [b|] eqn:E; [|discriminate].
    destruct (image_bytes psegs (a + 1) n) as [r|] eqn:E2; [|discriminate]. injection HI as <-.
    pose proof (IH (a + 1) r ltac:(intros x Hx; apply HP; lia) E2 ltac:(lia) ltac:(lia)) as (_ & L & B).
    split; [lia|]. split; [cbn [length]; lia|].
    intros [|i] Hi; cbn [nth_error].
    + rewrite Z.add_0_r. unfold mrd. rewrite (HP (wa a)) by (rewrite wa_unsigned by lia; lia). exact E.
    + replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply B. cbn in Hi. lia.
Qed.

Lemma ro_CB_pristine : forall (M : word -> option byte) a n bs,
  relro_pristine M -> image_bytes psegs a n = Some bs -> RELRO_LO <= a -> a + Z.of_nat n <= RELRO_HI ->
  ro_cells psegs M a [CB n bs].
Proof.
  intros M a n bs HP HI Hlo Hhi. unfold RELRO_LO, RELRO_HI in *.
  pose proof (image_bytes_length psegs n a bs HI) as L.
  split; [cbn; split; [exact L| exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  apply (bytes_at_pristine M a n bs); [| exact HI| lia| lia].
  intros x Hx. apply HP. unfold RELRO_LO, RELRO_HI. lia.
Qed.

Ltac relro_cell HP a n :=
  let X := fresh "RR" in
  pose proof (ro_CB_pristine _ a n _ HP ltac:(vm_compute; reflexivity) ltac:(unfold RELRO_LO; lia) ltac:(unfold RELRO_HI; cbn; lia)) as X.
Ltac relro_cells HP :=
  relro_cell HP 0x2c3b0 8%nat; relro_cell HP 0x2c360 8%nat; relro_cell HP 0x2c3c8 8%nat; relro_cell HP 0x2c2e0 8%nat;
  relro_cell HP 0x2c2c8 8%nat; relro_cell HP 0x2c2d0 8%nat.

Lemma rw_cells_CB_split : forall (M : word -> option byte) A n k bs,
  rw_cells psegs M A [CB (Z.to_nat n) bs] -> 0 <= k <= n ->
  rw_cells psegs M A [CB (Z.to_nat k) (firstn (Z.to_nat k) bs)]
  /\ rw_cells psegs M (A + k) [CB (Z.to_nat (n - k)) (skipn (Z.to_nat k) bs)].
Proof.
  intros M A n k bs [[Hwf HB] HW] Hk. cbn in Hwf. destruct Hwf as [L _].
  cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. destruct HB as (H0 & H1 & HB).
  destruct HW as (W0 & W1 & HW). cbn [cells_size csize] in HW, W1. rewrite Nat.add_0_r in HW, W1.
  split.
  - split; [split|].
    + cbn. split; [| exact I]. rewrite length_firstn. lia.
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite length_firstn; lia|].
      intros i Hi. rewrite length_firstn in Hi. rewrite (HB i) by lia.
      rewrite (nth_error_firstn (Z.to_nat k) bs i). replace (i <? Z.to_nat k)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
    + cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
  - split; [split|].
    + cbn. split; [| exact I]. rewrite length_skipn. lia.
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite length_skipn; lia|].
      intros i Hi. rewrite length_skipn in Hi. replace (A + k + Z.of_nat i) with (A + Z.of_nat (Z.to_nat k + i)) by lia.
      rewrite (HB (Z.to_nat k + i)%nat) by lia. rewrite nth_error_skipn. reflexivity.
    + cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + k + i) with (A + (k + i)) by lia. apply HW. lia.
Qed.

Lemma wr_at_app : forall (M : word -> option byte) A n1 n2,
  wr_at psegs M A n1 -> wr_at psegs M (A + n1) n2 -> 0 <= n1 -> 0 <= n2 -> wr_at psegs M A (n1 + n2).
Proof.
  intros M A n1 n2 (A0 & A1 & W1) (B0 & B1 & W2) H1 H2. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z.lt_ge_cases i n1); [apply W1; lia|].
  replace (A + i) with (A + n1 + (i - n1)) by lia. apply W2. lia.
Qed.

Definition fl_cb (n : Z) : Z := n + n / 4096 + n / 16384 + n / 33554432 + 13.
Lemma fl_cb_range : forall n, 0 <= n <= 2^20 -> 13 <= fl_cb n < 2^21.
Proof. intros n Hn. unfold fl_cb. split; [lia|]. change (2^21) with 2097152. change (2^20) with 1048576 in Hn. lia. Qed.
Definition fl_cl (n : Z) : Z := 100 + 2 * fl_cb n.

Lemma rw_CB_image_any : forall (bs0 : list byte) A (m : word -> option byte),
  rw_bytes_b psegs A bs0 = true -> 0 <= A -> A + Z.of_nat (length bs0) <= 2^64 ->
  exists bs, rw_cells psegs m A [CB (length bs0) bs].
Proof.
  induction bs0 as [|b0 bs0 IH]; intros A m Hb HA Hl.
  - exists []. split; [split|].
    + cbn. split; [reflexivity| exact I].
    + cbn [cells_bytes cbytes]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    + cbn [cells_size csize length Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. cbn in Hi. lia.
  - cbn [rw_bytes_b] in Hb.
    destruct (seg_rom psegs (wa A)) as [b'|] eqn:Er; [|discriminate].
    destruct (wview psegs (fun _ => None) (wa A)) as [bw|] eqn:Ew; [|discriminate].
    apply andb_prop in Hb. destruct Hb as [_ Hb]. cbn [length] in Hl.
    destruct (IH (A + 1)%Z m Hb ltac:(lia) ltac:(lia)) as (bs & [[Hwf (B0 & B1 & HB)] (W0 & W1 & HW)]).
    cbn in Hwf. destruct Hwf as [L _]. cbn [cells_bytes cbytes] in HB, B1. rewrite app_nil_r in HB, B1.
    cbn [cells_size csize] in HW, W1. rewrite Nat.add_0_r in HW, W1.
    set (b := match m (wa A) with Some b => b | None => b' end).
    exists (b :: bs). split; [split|].
    + cbn. split; [cbn; rewrite L; reflexivity| exact I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [cbn [length]; lia|].
      intros [|i] Hi; cbn [nth_error].
      * rewrite Z.add_0_r. unfold mrd, b. destruct (m (wa A)); [reflexivity| exact Er].
      * replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply HB. cbn in Hi. lia.
    + cbn [cells_size csize]. rewrite Nat.add_0_r. cbn [length]. split; [lia|]. split; [lia|].
      intros i Hi. destruct (Z.eq_dec i 0) as [->|NE].
      * rewrite Z.add_0_r. unfold wview in *. destruct (m (wa A)); [discriminate| exact (fun C => ltac:(rewrite C in Ew; discriminate))].
      * replace (A + i) with (A + 1 + (i - 1)) by lia. apply HW. lia.
Qed.

Lemma statics_chunk : forall (m : word -> option byte), exists old, rw_cells psegs m 0x3d6a0 [CB 16 old].
Proof.
  intros m.
  destruct (rw_CB_image_any (repeat (Z_to_bv 8 0) 16) 0x3d6a0 m ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as [bs H].
  exists bs. exact H.
Qed.

Ltac brw_side :=
  symmetry; unfold bv_eqb, bv_ltu; rewrite !unsigned_lit_wrap; change (2^64) with 18446744073709551616;
  first [ apply Z.eqb_neq; lia | apply Z.eqb_eq; lia
        | apply negb_false_iff; first [apply Z.eqb_eq; lia | apply Z.ltb_lt; lia]
        | apply negb_true_iff; first [apply Z.eqb_neq; lia | apply Z.ltb_ge; lia]
        | apply Z.ltb_ge; lia | apply Z.ltb_lt; lia ].
Ltac brw_false := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with false; [cbv iota| brw_side] end.
Ltac brw_true := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with true; [cbv iota| brw_side] end.

Lemma land7_of_mod8 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. exact H. Qed.
Lemma mod8_of_mod16 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof.
  intros x H. apply (proj1 (Z.mod_divide x 16 ltac:(lia))) in H. destruct H as [q ->].
  replace (q * 16) with ((q * 2) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma mod8_off : forall x k, x mod 16 = 0 -> k mod 8 = 0 -> (x + k) mod 8 = 0.
Proof.
  intros x k Hx Hk. apply (proj1 (Z.mod_divide x 16 ltac:(lia))) in Hx. destruct Hx as [q ->].
  replace (q * 16 + k) with (k + (q * 2) * 8) by lia. rewrite Z_mod_plus_full. exact Hk.
Qed.
Ltac br_align8 :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    lazymatch c with context [Z.land (bv_unsigned (Z_to_bv 64 ?e)) 7] =>
      replace c with false;
      [ cbv iota
      | symmetry; rewrite (unsigned_lit e) by lia; rewrite (land7_of_mod8 e);
        [ reflexivity
        | first [ apply mod8_of_mod16; assumption
                | apply mod8_off; [assumption| reflexivity]
                | lazymatch goal with H : ?x mod 16 = 0 |- _ => replace e with (x + (e - x)) by lia; apply mod8_off; [exact H| ] end ] ] ]
    end end.
