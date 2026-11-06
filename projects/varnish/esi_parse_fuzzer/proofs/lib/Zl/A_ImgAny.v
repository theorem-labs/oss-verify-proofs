(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Stgw7 V_CrcLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

Fixpoint rom_bytes_b (A : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: bs' => match seg_rom rsegs (wa A) with
               | Some b' => bv_eqb b b' && rom_bytes_b (A + 1) bs'
               | None => false
               end
  end.

Lemma rom_bytes_b_sound : forall bs A i, rom_bytes_b A bs = true -> (i < length bs)%nat ->
  seg_rom rsegs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  induction bs as [|b bs IH]; intros A i H Hi; cbn in *; [lia|].
  destruct (seg_rom rsegs (wa A)) as [b'|] eqn:E; [|discriminate].
  apply andb_prop in H. destruct H as [H1 H2].
  unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1. subst b'.
  destruct i as [|i].
  - cbn. rewrite Z.add_0_r. exact E.
  - cbn. rewrite <- (IH (A + 1) i H2) by lia. f_equal. f_equal. lia.
Qed.

Definition wr_ok_b (a : Z) (n : nat) : bool :=
  forallb (fun i => match find_segment rsegs (a + Z.of_nat i) 1 with
                    | Some seg => seg_writable seg &&
                                  match segment_byte_at (seg_bytes seg) (Z.to_N (a + Z.of_nat i - Z.of_N (seg_base seg))) with
                                  | Some _ => true | None => false end
                    | None => false end) (seq 0 n).

Lemma wr_at_of_b : forall M a n, 0 <= a -> a + Z.of_nat n <= 2^64 -> wr_ok_b a n = true -> wr_at rsegs M a (Z.of_nat n).
Proof.
  intros M a n H0 H1 Hb. split; [lia|]. split; [lia|]. intros i Hi.
  unfold wr_ok_b in Hb. rewrite forallb_forall in Hb.
  specialize (Hb (Z.to_nat i) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in Hb by lia.
  unfold wview, wa. destruct (M (Z_to_bv 64 (a + i))); [discriminate|].
  rewrite unsigned_lit by lia.
  destruct (find_segment rsegs (a + i) 1) as [seg|]; [|discriminate].
  apply andb_prop in Hb. destruct Hb as [W B]. rewrite W.
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (a + i - Z.of_N (seg_base seg)))); [discriminate| discriminate].
Qed.

(* [comment removed for export] *)
Definition ov_bytes (M : mem) (a : Z) (rom : list byte) : list byte :=
  map (fun i => match M (Z_to_bv 64 (a + Z.of_nat i)) with Some b => b | None => nth i rom (Z_to_bv 8 0) end) (seq 0 (length rom)).
Lemma ov_bytes_length : forall M a rom, length (ov_bytes M a rom) = length rom.
Proof. intros. unfold ov_bytes. rewrite length_map, length_seq. reflexivity. Qed.

Lemma bytes_at_ov : forall M a rom,
  0 <= a -> a + Z.of_nat (length rom) <= 2^64 -> rom_bytes_b a rom = true ->
  bytes_at rsegs M a (ov_bytes M a rom).
Proof.
  intros M a rom H0 H1 RB. split; [lia|]. split; [rewrite ov_bytes_length; lia|].
  intros i Hi. rewrite ov_bytes_length in Hi. unfold mrd, wa, ov_bytes.
  rewrite nth_error_map, (nth_error_nth' (seq 0 (length rom)) 0%nat) by (rewrite length_seq; lia).
  rewrite seq_nth by lia. cbn [option_map Nat.add].
  destruct (M (Z_to_bv 64 (a + Z.of_nat i))) as [b|]; [reflexivity|].
  pose proof (rom_bytes_b_sound rom a i RB Hi) as E. unfold wa in E. rewrite E. apply nth_error_nth'. exact Hi.
Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_nonneg bs) as H0. pose proof (bytes_le_to_Z_bound bs) as H1. rewrite Hl in H1.
  change (256 ^ Z.of_nat 8)%Z with 18446744073709551616%Z in H1.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  rewrite Z.mod_small by lia. rewrite <- Hl. apply Z_to_le_bytes_roundtrip.
Qed.

Lemma rw_C8_any : forall M a, 0 <= a -> a + 8 <= 2^64 ->
  rom_bytes_b a (repeat (Z_to_bv 8 0) 8) = true -> wr_ok_b a 8 = true ->
  exists w, rw_cells rsegs M a [C8 w].
Proof.
  intros M a H0 H1 RB WB. exists (le_bytes_to_word (ov_bytes M a (repeat (Z_to_bv 8 0) 8))). split.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    rewrite le8_of_bytes by (rewrite ov_bytes_length; reflexivity).
    apply bytes_at_ov; [lia| cbn; lia| exact RB].
  - cbn [cells_size csize]. apply (wr_at_of_b M a 8); [lia| lia| exact WB].
Qed.

Lemma Z_to_le_bytes_firstn : forall n k z, Z_to_le_bytes n z = firstn n (Z_to_le_bytes (n + k) z).
Proof. induction n as [|n IH]; intros k z; cbn; [reflexivity|]. f_equal. apply IH. Qed.

Lemma le4_of_bytes4 : forall bs : list byte, length bs = 4%nat ->
  Z_to_le_bytes 4 (bv_unsigned (le_bytes_to_word (bs ++ repeat (Z_to_bv 8 0) 4))) = bs.
Proof.
  intros bs Hl.
  pose proof (le8_of_bytes (bs ++ repeat (Z_to_bv 8 0) 4) ltac:(rewrite length_app, Hl; reflexivity)) as E8.
  unfold le8, word_to_le_bytes in E8.
  rewrite (Z_to_le_bytes_firstn 4 4). cbn [Nat.add]. rewrite E8.
  rewrite firstn_app, Hl, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all2. lia.
Qed.


Lemma rw_errno_any : forall M, exists e, rw_cells rsegs M ERRNOA [C4 e].
Proof.
  intros M. unfold ERRNOA. exists (le_bytes_to_word (ov_bytes M 0x5e7b34 (repeat (Z_to_bv 8 0) 4) ++ repeat (Z_to_bv 8 0) 4)). split.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    unfold le4, word_to_le_bytes. rewrite le4_of_bytes4 by (apply ov_bytes_length).
    apply bytes_at_ov; [lia| cbn; lia| vm_compute; reflexivity].
  - cbn [cells_size csize]. apply (wr_at_of_b M 0x5e7b34 4); [lia| lia| vm_compute; reflexivity].
Qed.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma errno_shadow_byte : forall v, consts_hold LPA v -> bytes_at rsegs v (sh 0x5e7b30) [Z_to_bv 8 0].
Proof.
  intros v CH. unfold consts_hold in CH. rewrite Forall_forall in CH.
  assert (EX : existsb (fun p : Z * nat => (Z.eqb (fst p) 0x800b4e58 && Nat.eqb (snd p) 17832)%bool) pa_zero_shadow = true)
    by (vm_compute; reflexivity).
  apply existsb_exists in EX as (pz & HIn & Heq). destruct pz as [pa pn]. cbn [fst snd] in Heq.
  apply andb_prop in Heq as [H1 H2]. apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. subst pa pn.
  assert (X : bytes_at rsegs v 0x800b4e58 (repeat (Z_to_bv 8 0) 17832)).
  { apply (CH (0x800b4e58, repeat (Z_to_bv 8 0) 17832%nat)).
    change (cl_consts LPA) with (pa_cells ++ pa_gshadow ++ pa_zshadow).
    apply in_or_app; right. apply in_or_app; right. unfold pa_zshadow.
    exact (in_map (fun p : Z * nat => (fst p, repeat (Z_to_bv 8 0) (snd p))) pa_zero_shadow (0x800b4e58, 17832%nat) HIn). }
  replace 17832%nat with (270 + (1 + 17561))%nat in X by reflexivity. rewrite repeat_app, repeat_app in X.
  apply bytes_at_app in X as [_ X]. apply bytes_at_app in X as [X _]. rewrite repeat_length in X.
  exact X.
Qed.

Lemma errno_shadowed {AI : AsanAlloc LPA} : forall v, consts_hold LPA v -> shadowed LPA v ERRNOA 4.
Proof.
  intros v CH. exists 0x5e7b30, 8. split; [change (shpat 8) with [Z_to_bv 8 0]; apply errno_shadow_byte; exact CH|].
  unfold ERRNOA. pose proof alloc_ceiling_num. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity; lia.
Qed.

End CEIL.
