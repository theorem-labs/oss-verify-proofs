(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bk X1bs X1c2 X1bn X1cc X1c6.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1rl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qv X0pw.
Import ListNotations.
Open Scope bv_scope.
Import X1bs.Exc.

Lemma impl_post_evt : forall segs (atn : node -> machine_state -> Prop) {R} (t : itree node R) Q Q' ms,
impl segs atn t Q' ms -> (forall r ms', Q' r ms' -> evt segs (Q r) ms') -> impl segs atn t Q ms.
Proof.
intros segs atn R t; induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
- eapply evt_cut; eauto.
- eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

Lemma impl_epost_evt : forall segs (atn : node -> machine_state -> Prop) {A} (t : itree node (exc A)) Q Q' ms,
impl segs atn t (epost Q') ms -> (forall a ms', Q' a ms' -> evt segs (Q a) ms') -> impl segs atn t (epost Q) ms.
Proof.
intros segs atn A t Q Q' ms H HQ. eapply impl_post_evt; [exact H|].
intros [|a] ms' Hp; cbn in *; [apply evt_done; exact I | apply HQ; exact Hp].
Qed.

Ltac astep := lstep; try (first [if_true | if_false]).

Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).

Tactic Notation "icallk" uconstr(SPEC) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply impl_epost_evt; [ eapply SPEC | ].

Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256%Z in Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hr.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap8_mod.
apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 8).
+ rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
rewrite (Z.testbit_neg_r _ (i - 8)) by lia. apply orb_false_r.
+ rewrite Z.mod_pow2_bits_high by lia. symmetry. apply (Z_testbit_high 8); lia.
- rewrite <- IH at 3. f_equal. apply Z.bits_inj'. intros i Hi.
rewrite Z.shiftr_spec, Z.lor_spec, Z.shiftl_spec by lia.
rewrite (Z_testbit_high 8 (bv_unsigned b) (i + 8)) by lia. cbn [orb]. f_equal. lia.
Qed.

Lemma le8_le_bytes_to_word : forall bs, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word.
rewrite Z_to_bv_unsigned. pose proof (bytes_le_to_Z_nonneg bs). pose proof (bytes_le_to_Z_bound bs) as B. rewrite Hl in B.
rewrite bv_wrap_small by (change (bv_modulus 64) with (2^64)%Z; cbn in B; lia).
rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Definition canary_of_bytes (cw : word) : list byte := firstn 1 (le8 cw) ++ Z_to_bv 8 0 :: skipn 2 (le8 cw).
Definition canary_of (cw : word) : word := le_bytes_to_word (canary_of_bytes cw).

Lemma length_canary_of_bytes : forall cw, length (canary_of_bytes cw) = 8%nat.
Proof. intros cw. unfold canary_of_bytes. rewrite length_app, length_firstn, length_le8. cbn [length]. rewrite length_skipn, length_le8. reflexivity. Qed.

Lemma le8_canary_of : forall cw, le8 (canary_of cw) = canary_of_bytes cw.
Proof. intros cw. unfold canary_of. apply le8_le_bytes_to_word. apply length_canary_of_bytes. Qed.

Definition td_cells (self prev next sysinfo : word) (tid errno detach : word) (robust locale dtvp dtv0 : word) : list cell :=
[C8 self; C8 prev; C8 next; C8 sysinfo; C4 tid; C4 errno; C4 detach; CB 76 (repeat (Z_to_bv 8 0) 76);
C8 robust; CB 24 (repeat (Z_to_bv 8 0) 24); C8 locale; CB 32 (repeat (Z_to_bv 8 0) 32);
C8 dtvp; CB 16 (repeat (Z_to_bv 8 0) 16); C8 dtv0; CB 112 (repeat (Z_to_bv 8 0) 112)].
Notation z64 := (Z_to_bv 64 0).

Definition libc_cells (can_do : byte) (auxv tls_size tls_align page_size : word) : list cell :=
[C1 can_do; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64; C8 auxv;
C8 z64; C8 tls_size; C8 tls_align; C8 z64; C8 page_size; CB 48 (repeat (Z_to_bv 8 0) 48)].
