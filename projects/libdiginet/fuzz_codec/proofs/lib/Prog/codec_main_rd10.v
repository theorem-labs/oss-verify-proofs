(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 129 of its 150 lines of code are new or changed and 123 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_main_inv
  LLVMFuzzerTestOneInput_c codec_main_rda_lib.
Import ListNotations.
Open Scope Z_scope.

(** Segment RD10 (COUNTER) of the walk of LLVMFuzzerTestOneInput in the plain image: the inlined u8 read of b,
    the 8-byte read loop into k.bytes, run()'s switch through T2 and its lbu of k.b, to ENC10. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** A byte store (sb) of a register v writes the cell C1 of v's low byte. *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

Lemma zb_range10 : forall l : list byte, Forall (fun x => 0 <= x < 256) (zb l).
Proof.
  induction l as [|b l IH]; cbn; constructor; [|exact IH].
  pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia.
Qed.

Lemma rdr_bytes10 : forall b l, 0 <= b < 256 -> length l = 24%nat -> reader_ok 10 0 b 0 0 (zb l) 0.
Proof.
  intros b l Hb Hl. unfold reader_ok, zb. rewrite length_map, Hl.
  repeat split; try lia. apply zb_range10.
Qed.

Lemma b8_val : forall x, 0 <= x < 256 -> bv_unsigned (b8 x) = x.
Proof.
  intros x Hx. unfold b8. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

(** k.b holds a byte: its 4 bytes are the byte and three zeros (run()'s lbu reads the first). *)
Lemma le4_small : forall v, 0 <= v < 256 -> le4 (Z_to_bv 64 v) = [b8 v; b8 0; b8 0; b8 0].
Proof.
  intros v Hv. unfold le4. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. unfold b8.
  repeat (apply f_equal2; [ apply Z_to_bv8_mod; rewrite ?Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia | ]).
  reflexivity.
Qed.

Lemma c4_split : forall m A pre post v, 0 <= v < 256 ->
  rw_cells rsegs m A (pre ++ C4 (Z_to_bv 64 v) :: post) ->
  rw_cells rsegs m A (pre ++ C1 (b8 v) :: CB 3 (fz0 3) :: post).
Proof.
  intros m A pre post v Hv H. eapply rw_cells_same; [ | | | exact H ].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [W1 [_ W2]].
    apply cells_wf_app. split; [exact W1|]. cbn. split; [exact I|]. split; [reflexivity | exact W2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite le4_small by exact Hv. reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.

Lemma c4_join : forall m A pre post v, 0 <= v < 256 ->
  rw_cells rsegs m A (pre ++ C1 (b8 v) :: CB 3 (fz0 3) :: post) ->
  rw_cells rsegs m A (pre ++ C4 (Z_to_bv 64 v) :: post).
Proof.
  intros m A pre post v Hv H. eapply rw_cells_same; [ | | | exact H ].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [W1 [_ [_ W2]]].
    apply cells_wf_app. split; [exact W1|]. cbn. split; [exact I | exact W2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite le4_small by exact Hv. reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.

(** Pieces of a flat frame list: the first n cells, the cells after them, the last 12 cells and the cells before. *)
Ltac take7 l :=
  lazymatch l with
  | ?x0 :: ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?x6 :: _ => constr:([x0; x1; x2; x3; x4; x5; x6])
  end.
Ltac drop8 l := lazymatch l with _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: ?r => r end.
Ltac drop9 l := lazymatch l with _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: ?r => r end.
Ltac take10 l :=
  lazymatch l with
  | ?x0 :: ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?x6 :: ?x7 :: ?x8 :: ?x9 :: _ =>
      constr:([x0; x1; x2; x3; x4; x5; x6; x7; x8; x9])
  end.
Ltac drop10 l := lazymatch l with _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: ?r => r end.
Ltac last12 l :=
  lazymatch l with
  | [_; _; _; _; _; _; _; _; _; _; _; _] => l
  | _ :: ?r => last12 r
  end.
Ltac but_last12 l :=
  lazymatch l with
  | [_; _; _; _; _; _; _; _; _; _; _; _] => constr:(@nil cell)
  | ?x :: ?r => let r' := but_last12 r in constr:(x :: r')
  end.

Section RD10.
Variable e : env.
Variable fuel : nat.
Hypothesis HE : env_ok e.
Hypothesis EN10 : enc10_ok e fuel.

(** 0x13af0-0x13af4: b stored, a3 = &k.bytes; 0x13af8-0x13b24: k.bytes[0..8) read one byte each (a byte past the
    input reads 0); 0x13c24-0x13c44: run()'s switch, T2[10]; 0x13c48: lbu a0, k.b; to ENC10. *)
Lemma rd10_mid : forall (ra' t0' t1' t2' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops : word)
    (x pv dv : Z) (od : option desk) (cur rem : Z) (tl : list byte) (m : word -> option byte),
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400) (rd_cells 10 pv dv 0 0 0 0 cur rem tl) ->
  fuel_ok ops (S fuel) -> pd_ok pv dv od -> 0 <= x < 256 ->
  bv_unsigned (e_p e) <= cur -> 0 <= rem -> cur - bv_unsigned (e_p e) + rem = Z.of_nat (length (e_data e)) ->
  fr_ok e m ->
  evt rsegs (Qk e)
    (st e (body_regs e ra' t0' t1' t2' (Z_to_bv 64 10) (Z_to_bv 64 rem) (Z_to_bv 64 cur) (Z_to_bv 64 x)
                     a4' a5' a6' a7' (Z_to_bv 64 pv) ops s8' s10' t3' t4' t5' t6') 0x13af0 m).
Proof.
  intros ra' t0' t1' t2' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops x pv dv od cur rem tl m
    FR HF HPD Hx Hc0 Hr0 Hcr HFR.
  unfold st, body_regs. rd_setup HE HFR. unfold rd_cells in FR.
  zstep. zstep.
  assert (rem = 0 \/ rem = 1 \/ rem = 2 \/ rem = 3 \/ rem = 4 \/ rem = 5 \/ rem = 6 \/ rem = 7 \/ rem = 8 \/ 9 <= rem)
    as [R | [R | [R | [R | [R | [R | [R | [R | [R | R]]]]]]]]] by lia; try subst rem.
  all: drive 0x13c48.
  all: lazymatch goal with FR : rw_cells _ ?mm ?A ?cs |- _ =>
         let pre := take7 cs in let post := drop8 cs in
         pose proof (c4_split mm A pre post x Hx FR) as FS; clear FR; cbn [app] in FS
       end.
  all: zstep.
  all: cbv beta; rewrite (b8_val x) by exact Hx.
  all: lazymatch goal with FS : rw_cells _ ?mm ?A ?cs |- _ =>
         let pre := take7 cs in let post := drop9 cs in
         pose proof (c4_join mm A pre post x Hx FS) as FR; clear FS; cbn [app] in FR
       end.
  all: lazymatch goal with FR : rw_cells _ ?mm ?A ?cs |- _ =>
         let pre := take10 cs in let r := drop10 cs in
         let mid := but_last12 r in let post := last12 r in
         pose proof (rw_cells_merge rsegs mm A pre mid post FR) as FB; clear FR;
         cbn [cells_size csize Nat.add app] in FB;
         set (BY := cells_bytes mid) in FB;
         assert (LB : length BY = 24%nat) by reflexivity;
         clearbody BY
       end.
  all: lazymatch type of FB with context [C8 (Z_to_bv 64 ?X) :: C8 (Z_to_bv 64 ?Y) :: CB 80 _ :: _] =>
         replace (Z_to_bv 64 X) with (Z_to_bv 64 (bv_unsigned (e_p e) + (X - bv_unsigned (e_p e)))) in FB
           by (f_equal; lia);
         pose proof EN10 as J; unfold enc10_ok, st, body_regs in J;
         eapply J with (k := mkKcall 10 (fz0 4) pv dv 0 x 0 0 BY 0 0 (fa5 32) (fa5 32) 0 (fz0 24) 0 0 0)
                       (od := od) (c := X - bv_unsigned (e_p e)) (rem := Y) (tl := tl);
         [ exact HF | reflexivity | exact HPD | apply rdr_bytes10; assumption | reflexivity | reflexivity
         | unfold cur_ok; lia | exact FB | exact (conj SV (conj ST (conj MU (conj WM HMI)))) ]
       end.
Qed.

(** 0x13910: the u8 read of b, to 0x13af0. *)
Lemma rd10_rd : rd_ok e 10 fuel.
Proof.
  unfold rd_ok, st, body_regs.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops pv dv od c rem tl m1
    HF HPD HC FR HFR.
  change (rd_pc 10) with 0x13910.
  rd_setup HE HFR. destruct HC as (Hc0 & Hr0 & Hcr).
  unfold body_cells, k_rd in FR.
  cbn [kcall_cells app k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
       k_want_len k_want_key k_want_display] in FR.
  assert (rem = 0 \/ 1 <= rem) as [R | R] by lia; try subst rem.
  all: drive 0x13af0.
  all: eapply rd10_mid; [ exact FR | rd_side .. ].
Qed.

End RD10.

Lemma codec_main_rd10 : S_rd10.
Proof. unfold S_rd10. intros e fuel HE EN10. eapply rd10_rd; eassumption. Qed.
