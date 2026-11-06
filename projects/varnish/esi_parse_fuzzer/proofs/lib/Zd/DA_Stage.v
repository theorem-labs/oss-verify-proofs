(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Cells.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require SegScan.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Set Warnings "-abstract-large-number".
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Definition wr1 (x : Z) : bool :=
  match find_segment rsegs x 1 with
  | Some seg => seg_writable seg &&
                match segment_byte_at (seg_bytes seg) (Z.to_N (x - Z.of_N (seg_base seg))) with Some _ => true | None => false end
  | None => false
  end.
Definition rom1 (x : Z) : bool := match seg_rom rsegs (wz x) with Some _ => true | None => false end.

Fixpoint wr_ok_lin (a : Z) (n : nat) : bool :=
  match n with O => true | S n' => if wr1 a then wr_ok_lin (a + 1) n' else false end.
Fixpoint rom_ok_lin (a : Z) (n : nat) : bool :=
  match n with O => true | S n' => if rom1 a then rom_ok_lin (a + 1) n' else false end.

Lemma wr_ok_lin_sound : forall n a i, wr_ok_lin a n = true -> 0 <= i < Z.of_nat n -> wr1 (a + i) = true.
Proof.
  induction n as [|n IH]; intros a i H Hi; [lia|]. cbn [wr_ok_lin] in H.
  destruct (wr1 a) eqn:E; [|discriminate].
  destruct (Z.eq_dec i 0) as [->|NZ]; [rewrite Z.add_0_r; exact E|].
  replace (a + i) with (a + 1 + (i - 1)) by lia. apply (IH (a + 1) (i - 1) H). lia.
Qed.
Lemma rom_ok_lin_sound : forall n a i, rom_ok_lin a n = true -> 0 <= i < Z.of_nat n -> rom1 (a + i) = true.
Proof.
  induction n as [|n IH]; intros a i H Hi; [lia|]. cbn [rom_ok_lin] in H.
  destruct (rom1 a) eqn:E; [|discriminate].
  destruct (Z.eq_dec i 0) as [->|NZ]; [rewrite Z.add_0_r; exact E|].
  replace (a + i) with (a + 1 + (i - 1)) by lia. apply (IH (a + 1) (i - 1) H). lia.
Qed.

Lemma wr_at_of_lin : forall M a n, 0 <= a -> a + Z.of_nat n <= 2^64 -> wr_ok_lin a n = true -> wr_at rsegs M a (Z.of_nat n).
Proof.
  intros M a n H0 H1 Hb. split; [lia|]. split; [lia|]. intros i Hi.
  pose proof (wr_ok_lin_sound n a i Hb Hi) as W. unfold wr1 in W.
  unfold wview, wa. destruct (M (Z_to_bv 64 (a + i))); [discriminate|].
  rewrite unsigned_lit by lia.
  destruct (find_segment rsegs (a + i) 1) as [seg|]; [|discriminate].
  apply andb_prop in W. destruct W as [W B]. rewrite W.
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (a + i - Z.of_N (seg_base seg)))); [discriminate| discriminate].
Qed.

(* [comment removed for export] *)
Definition ov_byte (M : word -> option byte) (x : Z) : byte :=
  match M (wz x) with Some b => b | None => match seg_rom rsegs (wz x) with Some b => b | None => Z_to_bv 8 0 end end.
Definition ov_junk (M : word -> option byte) (a : Z) (n : nat) : list byte := map (fun i => ov_byte M (a + Z.of_nat i)) (seq 0 n).

Lemma ov_junk_length : forall M a n, length (ov_junk M a n) = n.
Proof. intros. unfold ov_junk. rewrite length_map, length_seq. reflexivity. Qed.

Lemma bytes_at_ov_junk : forall M a n, 0 <= a -> a + Z.of_nat n <= 2^64 -> rom_ok_lin a n = true ->
  bytes_at rsegs M a (ov_junk M a n).
Proof.
  intros M a n H0 H1 RB. split; [lia|]. split; [rewrite ov_junk_length; lia|].
  intros i Hi. rewrite ov_junk_length in Hi. unfold ov_junk.
  rewrite nth_error_map, (nth_error_nth' (seq 0 n) 0%nat) by (rewrite length_seq; lia).
  rewrite seq_nth by lia. cbn [option_map Nat.add]. unfold mrd, wa, ov_byte.
  destruct (M (Z_to_bv 64 (a + Z.of_nat i))) as [b|]; [reflexivity|].
  pose proof (rom_ok_lin_sound n a (Z.of_nat i) RB ltac:(lia)) as R. unfold rom1 in R.
  destruct (seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i))); [reflexivity| discriminate].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wr_ok_lin_of_range : forall n a, SegScan.SEGSCAN.range_okI seg_writable rsegs a n = true -> wr_ok_lin a n = true.
Proof.
  intros n a H. pose proof (SegScan.SEGSCAN.range_okI_spec _ _ _ _ H) as HS. clear H.
  revert a HS. induction n as [|n IH]; intros a HS; [reflexivity|].
  cbn [wr_ok_lin]. assert (W : wr1 a = true).
  { unfold wr1. destruct (HS a) as (seg & F & Wr & B); [rewrite Nat2Z.inj_succ; lia|]. rewrite F, Wr.
    destruct (segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg)))); [reflexivity|congruence]. }
  rewrite W. apply IH. intros u Hu. apply HS. rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma rom_ok_lin_of_range : forall n a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  SegScan.SEGSCAN.range_okI seg_readable rsegs a n = true -> rom_ok_lin a n = true.
Proof.
  intros n a Ha Hn H. pose proof (SegScan.SEGSCAN.range_okI_spec _ _ _ _ H) as HS. clear H.
  revert a Ha Hn HS. induction n as [|n IH]; intros a Ha Hn HS; [reflexivity|].
  rewrite Nat2Z.inj_succ in Hn.
  cbn [rom_ok_lin]. assert (W : rom1 a = true).
  { unfold rom1, seg_rom, memory_read. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
    change (Z.of_N 1) with 1. destruct (HS a) as (seg & F & Rd & B); [rewrite Nat2Z.inj_succ; lia|]. rewrite F, Rd.
    change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
    destruct (segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg)))); [reflexivity|congruence]. }
  rewrite W. apply IH; [lia|lia|]. intros u Hu. apply HS. rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma stage_wr_ok : wr_ok_lin READ_STAGE (Z.to_nat 65536) = true.
Proof. apply wr_ok_lin_of_range. lazymatch goal with |- @eq ?T _ ?r => vm_cast_no_check (@eq_refl T r) end. Qed.
Lemma stage_rom_ok : rom_ok_lin READ_STAGE (Z.to_nat 65536) = true.
Proof.
  apply rom_ok_lin_of_range; [unfold READ_STAGE; lia|unfold READ_STAGE; rewrite Z2Nat.id by lia; lia|].
  lazymatch goal with |- @eq ?T _ ?r => vm_cast_no_check (@eq_refl T r) end.
Qed.

(* [comment removed for export] *)
Lemma stage_any : forall M, exists junk, rw_cells rsegs M READ_STAGE [CB (Z.to_nat 65536) junk].
Proof.
  intros M. exists (ov_junk M READ_STAGE (Z.to_nat 65536)). split.
  - split; [cbn [cells_wf cell_wf]; rewrite ov_junk_length; split; [reflexivity| exact I]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply bytes_at_ov_junk; [unfold READ_STAGE; lia| unfold READ_STAGE; rewrite Z2Nat.id by lia; lia| exact stage_rom_ok].
  - cbn [cells_size csize]. rewrite Nat.add_0_r. apply (wr_at_of_lin M READ_STAGE (Z.to_nat 65536));
      [unfold READ_STAGE; lia| unfold READ_STAGE; rewrite Z2Nat.id by lia; lia| exact stage_wr_ok].
Qed.

(* [comment removed for export] *)
Lemma stage_cells : forall M cnt, 1 <= cnt <= 65536 -> exists junk, rw_cells rsegs M READ_STAGE [CB (Z.to_nat cnt) junk].
Proof.
  intros M cnt Hc. destruct (stage_any M) as [junk RW].
  exists (firstn (Z.to_nat cnt) junk).
  destruct RW as [[WF BA] WR]. cbn [cells_wf cell_wf] in WF. destruct WF as [LJ _].
  cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA. cbn [cells_size csize] in WR. rewrite Nat.add_0_r in WR.
  split.
  - split; [cbn [cells_wf cell_wf]; rewrite length_firstn; split; [lia| exact I]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r.
    destruct BA as (B0 & B1 & B). split; [lia|]. split; [rewrite length_firstn; lia|].
    intros i Hi. rewrite length_firstn in Hi. rewrite (B i) by lia.
    rewrite nth_error_firstn. destruct (PeanoNat.Nat.ltb_spec i (Z.to_nat cnt)); [reflexivity| lia].
  - cbn [cells_size csize]. rewrite Nat.add_0_r. destruct WR as (W0 & W1 & W). split; [lia|]. split; [lia|].
    intros i Hi. apply W. lia.
Qed.
