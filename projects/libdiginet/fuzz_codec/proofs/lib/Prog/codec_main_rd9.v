(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 88 of its 110 lines of code are new or changed and 122 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_main_inv
  LLVMFuzzerTestOneInput_c codec_main_rda_lib.
Import ListNotations.
Open Scope Z_scope.

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

(** Any 24 bytes as the record's bytes field. *)
Lemma zb_range : forall l : list byte, Forall (fun x => 0 <= x < 256) (zb l).
Proof.
  induction l as [|b l IH]; cbn; constructor; [|exact IH].
  pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia.
Qed.

Lemma rdr_bytes9 : forall a l, 0 <= a < 2 ^ 32 -> length l = 24%nat -> reader_ok 9 a 0 0 0 (zb l) 0.
Proof.
  intros a l Ha Hl. unfold reader_ok, zb. rewrite length_map, Hl.
  repeat split; try lia. apply zb_range.
Qed.

(** The cells of the bytes field after the loop, between the 10 cells before it and the 12 after it. *)
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

Section RD9.
Variable e : env.
Variable fuel : nat.
Hypothesis HE : env_ok e.
Hypothesis EN9 : enc9_ok e fuel.

(** 0x13bdc-0x13bf0: a = lo | hi << 16 stored, a3 = &k.bytes; 0x13bf4-0x13c20: k.bytes[0..8) read one byte each
    (a byte past the input reads 0); 0x13c24-0x13c44: run()'s switch, T2[9] = ENC9. *)
Lemma rd9_mid : forall (ra' t0' t1' t2' a7' s8' s10' t3' t4' t5' t6' ops : word)
    (x1 x2 x3 x4 pv dv : Z) (od : option desk) (cur rem : Z) (tl : list byte) (m : word -> option byte),
  rw_cells rsegs m (bv_unsigned (e_sp e) + -400) (rd_cells 9 pv dv 0 0 0 0 cur rem tl) ->
  fuel_ok ops (S fuel) -> pd_ok pv dv od ->
  0 <= x1 < 2 ^ 16 -> 0 <= x2 < 2 ^ 16 -> 0 <= x3 < 2 ^ 16 -> 0 <= x4 < 2 ^ 16 ->
  bv_unsigned (e_p e) <= cur -> 0 <= rem -> cur - bv_unsigned (e_p e) + rem = Z.of_nat (length (e_data e)) ->
  fr_ok e m ->
  evt rsegs (Qk e)
    (st e (body_regs e ra' t0' t1' t2' (Z_to_bv 64 9) (Z_to_bv 64 cur) (Z_to_bv 64 rem) (Z_to_bv 64 x1)
                     (Z_to_bv 64 x2) (Z_to_bv 64 x3) (Z_to_bv 64 x4) a7' (Z_to_bv 64 pv) ops s8' s10' t3' t4' t5' t6')
       0x13bdc m).
Proof.
  intros ra' t0' t1' t2' a7' s8' s10' t3' t4' t5' t6' ops x1 x2 x3 x4 pv dv od cur rem tl m
    FR HF HPD H1 H2 H3 H4 Hc0 Hr0 Hcr HFR.
  unfold st, body_regs. rd_setup HE HFR. unfold rd_cells in FR.
  do 5 zstep.
  match type of FR with context [C4 (Z_to_bv 64 (Z.lor ?X ?Y))] => set (va := Z.lor X Y) in * end.
  assert (Hva : 0 <= va < 2 ^ 32) by (unfold va; apply cmp_range; assumption).
  clearbody va.
  zstep.
  assert (rem = 0 \/ rem = 1 \/ rem = 2 \/ rem = 3 \/ rem = 4 \/ rem = 5 \/ rem = 6 \/ rem = 7 \/ 8 <= rem)
    as [R | [R | [R | [R | [R | [R | [R | [R | R]]]]]]]] by lia; try subst rem.
  all: drive 0x13560.
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
         pose proof EN9 as J; unfold enc9_ok, st, body_regs in J;
         eapply J with (k := mkKcall 9 (fz0 4) pv dv va 0 0 0 BY 0 0 (fa5 32) (fa5 32) 0 (fz0 24) 0 0 0)
                       (od := od) (c := X - bv_unsigned (e_p e)) (rem := Y) (tl := tl);
         [ exact HF | reflexivity | exact HPD | apply rdr_bytes9; assumption | reflexivity | reflexivity
         | unfold cur_ok; lia | exact FB | exact (conj SV (conj ST (conj MU (conj WM HMI)))) ]
       end.
Qed.

(** 0x13578: the read of a, to 0x13bdc. *)
Lemma rd9_rd : rd_ok e 9 fuel.
Proof.
  unfold rd_ok, st, body_regs.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s8' s10' t3' t4' t5' t6' ops pv dv od c rem tl m1
    HF HPD HC FR HFR.
  change (rd_pc 9) with 0x13578.
  rd_setup HE HFR. destruct HC as (Hc0 & Hr0 & Hcr).
  unfold body_cells, k_rd in FR.
  cbn [kcall_cells app k_kind k_pad k_p k_desk k_a k_b k_c k_delta k_bytes k_n k_rc k_before k_out k_want_rc k_want
       k_want_len k_want_key k_want_display] in FR.
  destruct (rem_cases rem Hr0) as [R | [R | [R | [R | R]]]]; try subst rem.
  all: drive 0x13bdc.
  all: eapply rd9_mid; [ exact FR | rd_side .. ].
Qed.

End RD9.

Lemma codec_main_rd9 : S_rd9.
Proof. unfold S_rd9. intros e fuel HE EN9. eapply rd9_rd; eassumption. Qed.
