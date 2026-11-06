(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK15 YM06.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP01.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI06 YI09 YI16 YI00 YI14.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition LAY_FILE : layout_t :=
[(0, 4%N)  ; (8, 8%N)  ; (16, 8%N)  ; (24, 8%N)  ; (32, 8%N)  ;
(40, 8%N)  ; (48, 8%N)  ; (56, 8%N)  ; (64, 8%N)  ; (72, 8%N)  ;
(80, 8%N)  ; (88, 8%N)  ; (96, 8%N)  ; (104, 8%N)  ; (112, 8%N)  ;
(120, 4%N)  ; (124, 4%N)  ; (128, 8%N)  ; (136, 4%N)  ; (140, 4%N)  ;
(144, 4%N)  ; (152, 8%N)  ; (160, 8%N)  ; (168, 8%N)  ; (176, 8%N)  ;
(184, 8%N)  ; (192, 8%N)  ; (200, 8%N)  ; (208, 8%N)  ;
(216, 8%N)  ; (224, 8%N)  ].
Definition FILE_HDR : Z := 232.
Definition FL_flags := 0%nat. Definition FL_rpos := 1%nat. Definition FL_rend := 2%nat. Definition FL_close := 3%nat.
Definition FL_wend := 4%nat.  Definition FL_wpos := 5%nat. Definition FL_wbase := 7%nat. Definition FL_write := 9%nat.
Definition FL_buf := 11%nat.  Definition FL_bufsz := 12%nat. Definition FL_prev := 13%nat. Definition FL_next := 14%nat.
Definition FL_fd := 15%nat.   Definition FL_mode := 18%nat. Definition FL_lock := 19%nat. Definition FL_lbf := 20%nat.
Lemma LAY_FILE_ok : lay_inside LAY_FILE FILE_HDR = true /\ lay_widths_ok LAY_FILE = true.
Proof. split; reflexivity. Qed.
Section c.
Variable segs : list Segment.
Lemma val_of_chunk_ok_mod : forall E mem base off (n : N) (e : sv) v,
chunk_ok segs E mem base (mkChunk off (CVal n e)) ->
bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N n) = v -> (Z.of_N n <= 8) ->
val_mem segs mem (base + off) (N.to_nat n) v.
Proof.
intros E mem base off n e v H He Hn k Hk. unfold chunk_ok in H. cbn [c_off c_val c_len cv_len] in H.
pose proof (N_nat_Z n) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [cbyte] in Hb1.
unfold byte_of_word in Hb1. injection Hb1 as <-. rewrite Hb2. f_equal.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold le_byte. rewrite Z.mod_mod by lia. subst v. rewrite Hnn.
set (w := bv_unsigned (sv_denot E e)). set (K := Z.of_nat k). set (N8 := Z.of_N n).
assert (HK : 0 <= K < N8) by (subst K N8; lia).
rewrite (Z.mod_small (w mod 2 ^ (8 * N8)) (2 ^ (8 * N8))) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
rewrite !Z.shiftr_div_pow2 by lia.
replace (2 ^ (8 * N8)) with (2 ^ (8 * K) * 2 ^ (8 * (N8 - K))) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite Z.rem_mul_r by (try apply Z.pow_nonzero; try (apply Z.pow_pos_nonneg); lia).
rewrite (Z.mul_comm (2 ^ (8 * K))), Z.div_add by (apply Z.pow_nonzero; lia).
rewrite (Z.div_small (w mod 2 ^ (8 * K))) by (apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
rewrite Z.add_0_l.
replace (2 ^ (8 * (N8 - K))) with (256 * 2 ^ (8 * (N8 - K) - 8)) by (change 256 with (2 ^ 8); rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite Z.rem_mul_r by (try apply Z.pow_nonzero; try (apply Z.pow_pos_nonneg); lia).
rewrite (Z.mul_comm 256), Z.mod_add by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma obj_at_of_chunks_sv : forall E mem a (cs : list chunk) lay vals,
Forall (chunk_ok segs E mem a) cs -> lay_widths_ok lay = true ->
Forall2 (fun (f : Z * N) v => 0 <= v < 2 ^ (8 * Z.of_N (snd f)) /\
exists e, In (mkChunk (fst f) (CVal (snd f) e)) cs /\ bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N (snd f)) = v) lay vals ->
obj_at segs mem a lay vals.
Proof.
intros E mem a cs lay vals Hcs. revert vals. induction lay as [|f lay IH]; intros vals Hw H2; inversion H2; subst; [exact I|].
unfold lay_widths_ok in Hw. cbn [forallb] in Hw. apply andb_prop in Hw as [Hw1 Hw]. apply Z.leb_le in Hw1.
cbn [obj_at]. split; [|apply IH; assumption].
match goal with H : _ /\ _ |- _ => destruct H as (Hr & e & Hin & He) end.
split; [|exact Hr]. destruct f as [o w]. cbn [fst snd] in *.
rewrite Forall_forall in Hcs. exact (val_of_chunk_ok_mod E mem a o w e _ (Hcs _ Hin) He Hw1).
Qed.
End c.
Section d.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Context {SH : sink_head} {SK : sink_syms}.
Local Notation segs := (ms_segs B).
Definition file_vals (f fd wend wpos wbase mode : Z) : list Z :=
[4; 0; 0; sk_close; wend; wpos; 0; wbase; sk_read; sk_write; sk_seek; f + FILE_BUF_OFF; FILE_BUFSIZ; 0; 0; fd; 0; 0; mode;
U32M1; U32M1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].
Definition sink_code_ok : Prop :=
0 <= sk_close < 2 ^ 64 /\ 0 <= sk_read < 2 ^ 64 /\ 0 <= sk_write < 2 ^ 64 /\ 0 <= sk_seek < 2 ^ 64.
Lemma file_at_obj : forall mem f fd P,
sink_code_ok -> 0 <= f -> f + FILE_BLOCK < 2 ^ 64 ->
file_at B mem f fd P ->
0 <= fd < 2 ^ 31 /\
((P = [] /\ obj_at segs mem f LAY_FILE (file_vals f fd 0 0 0 0)) \/
(obj_at segs mem f LAY_FILE (file_vals f fd (f + FILE_BUF_OFF + FILE_BUFSIZ) (f + FILE_BUF_OFF + Z.of_nat (length P)) (f + FILE_BUF_OFF) U32M1) /\
garr8 segs mem (f + FILE_BUF_OFF) P /\ Z.of_nat (length P) <= FILE_BUFSIZ)).
Proof.
intros mem f fd P (C1 & C2 & C3 & C4) Hf0 Hf1 [Hs Hw].
assert (HFB : FILE_BLOCK = 1264) by reflexivity. assert (HBO : FILE_BUF_OFF = 240) by reflexivity.
assert (HBS : FILE_BUFSIZ = 1024) by reflexivity. assert (HU : U32M1 = 4294967295) by reflexivity.
unfold file_static in Hs.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
split; [lia|].
destruct Hw as [(HP & W1 & W2 & W3 & W4) | (W1 & W2 & W3 & W4 & HG & HL)]; [left; split; [exact HP|] | right; split; [|split; [exact HG | exact HL]]];
cbn [obj_at LAY_FILE file_vals]; unfold field_ok; cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add];
change (8 * Z.of_N 8) with 64; change (8 * Z.of_N 4) with 32;
repeat match goal with |- _ /\ _ => split end; first [ exact I | assumption | lia ].
Qed.
Lemma obj_file_at_fresh : forall mem f fd,
0 <= fd < 2 ^ 31 -> obj_at segs mem f LAY_FILE (file_vals f fd 0 0 0 0) -> file_at B mem f fd [].
Proof.
intros mem f fd Hfd H. cbn [obj_at LAY_FILE file_vals] in H. unfold field_ok in H. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in H.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
split.
- unfold file_static. repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
- left. repeat match goal with |- _ /\ _ => split end; first [reflexivity | assumption].
Qed.
Lemma obj_file_at_buf : forall mem f fd P,
0 <= fd < 2 ^ 31 ->
obj_at segs mem f LAY_FILE (file_vals f fd (f + FILE_BUF_OFF + FILE_BUFSIZ) (f + FILE_BUF_OFF + Z.of_nat (length P)) (f + FILE_BUF_OFF) U32M1) ->
garr8 segs mem (f + FILE_BUF_OFF) P -> Z.of_nat (length P) <= FILE_BUFSIZ ->
file_at B mem f fd P.
Proof.
intros mem f fd P Hfd H HG HL. cbn [obj_at LAY_FILE file_vals] in H. unfold field_ok in H. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in H.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
split.
- unfold file_static. repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
- right. repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
Qed.
End d.
