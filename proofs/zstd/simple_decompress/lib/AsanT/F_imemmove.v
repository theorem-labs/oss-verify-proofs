(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StrwF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition imemmove_entry := 0x65ea8%Z.

Definition imemmove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2)
    /\ rdbl bsegs m' (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2).

Section Proofs.
  Variables (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Notation S := (bv_unsigned a1).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Hypothesis AB : (S + n <= 2^63 /\ D + n <= 2^63)%Z.
  (* [comment removed for export] *)
  Hypothesis RS : rng RNG S n.
  Hypothesis RD : rng RNG D n.

  Notation POST := (imemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m).
  Notation INV m1 := (mv_inv bsegs S D n m m1).
  (* [comment removed for export] *)
  Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Lemma rng64 : (0 <= S < 2^64 /\ 0 <= D < 2^64 /\ 0 <= n < 2^64)%Z.
  Proof.
    pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1. pose proof (bv_unsigned_in_range 64 a2) as R2.
    unfold bv_modulus in *. cbn in R0, R1, R2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma im_ret : forall m1 x11 x12 x13 x14 x15 x16, INV m1 -> evtF bsegs RNG POST (ST 0x65efc m1 x11 x12 x13 x14 x15 x16).
  Proof.
    intros m1 x11 x12 x13 x14 x15 x16 I. destruct I as (SD & SS & MI & MU & WM). zstep. finish2.
  Qed.

  (* [comment removed for export] *)
  Ltac ldk P k bs :=
    lazymatch goal with I : mv_inv ?segs ?S0 ?D0 ?n0 ?m0 ?m1 |- _ =>
      let a := cur_mem_addr in
      let RD := fresh "RD" in let L := fresh "L" bs in
      destruct (mv_read segs S0 D0 n0 m0 m1 P k a I ltac:(lia) ltac:(lia) ltac:(addr_tac)) as [bs [L RD]];
      zstep; try clear RD
    end.
  Ltac stk_ P k :=
    lazymatch goal with I : mv_inv ?segs ?S0 ?D0 ?n0 ?m0 ?m1 |- _ =>
      let a := cur_mem_addr in
      let SOK := fresh "SOK" in
      pose proof (mv_store_ok segs S0 D0 n0 m0 m1 P k a I ltac:(lia) ltac:(lia) ltac:(addr_tac)) as SOK;
      zstep;
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem m1 ?a' ?xs) _) =>
        let I' := fresh "I" in
        pose proof (mv_store segs S0 D0 n0 m0 m1 P k xs a' I ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(addr_tac)) as I';
        clear I SOK;
        let m' := fresh "m" in remember (write_to_mem m1 a' xs) as m' eqn:Heqm; clear Heqm; try clear m1;
        rename I' into I
      end
    end.

  (* [comment removed for export] *)
  Tactic Notation "use" uconstr(L) :=
    eapply L; first [ eassumption | idtac ]; try (f_equal; lia); try lia;
    try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).

  (* [comment removed for export] *)
  Lemma im_fl : forall (k : nat) m1 (P : Z) xa1 xa2 xa3 x14,
    INV m1 -> (0 <= P)%Z -> (P + Z.of_nat k + 1 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (D + n) -> xa3 = Z_to_bv 64 (D + P) ->
    evtF bsegs RNG POST (ST 0x65eb8 m1 xa1 xa2 xa3 x14 a5 a6).
  Proof.
    pose proof rng64 as R64.
    induction k as [|k IH]; intros m1 P xa1 xa2 xa3 x14 I HP HK -> -> ->.
    - ldk P 1%nat bs. stk_ P 1%nat. zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
      zstep. use im_ret.
    - ldk P 1%nat bs. stk_ P 1%nat. zstep. zstep. zstep. if_cases K; zify_cond K; [| exfalso; lia].
      use (IH _ (P + 1)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma im_bl : forall (k : nat) m1 (j : Z) xa3 x14 x15 x16,
    INV m1 -> j = Z.of_nat k -> (j < n)%Z -> xa3 = Z_to_bv 64 j ->
    evtF bsegs RNG POST (ST 0x65ee0 m1 a1 (Z_to_bv 64 1) xa3 x14 x15 x16).
  Proof.
    pose proof rng64 as R64.
    induction k as [|k IH]; intros m1 j xa3 x14 x15 x16 I Hj Hn ->.
    - zstep. ldk j 1%nat bs. zstep. zstep. zstep. stk_ j 1%nat. zstep. if_cases K; zify_cond K; [exfalso; lia|]. use im_ret.
    - zstep. ldk j 1%nat bs. zstep. zstep. zstep. stk_ j 1%nat. zstep. if_cases K; zify_cond K; [| exfalso; lia].
      use (IH _ (j - 1)%Z).
  Qed.

  Lemma imemmove_body : forall (mm : word -> option byte),
    mm = m -> stk bsegs m D (D + n) -> rdbl bsegs m S (S + n) -> mem_inv bsegs m ->
    evtF bsegs RNG POST (ST 0x65ea8 mm a1 a2 a3 a4 a5 a6).
  Proof.
    pose proof rng64 as R64.
    intros mm -> SD SS MI. pose proof (mv_inv_init bsegs S D n m SD SS MI) as I.
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *) use im_ret.
      + zstep. if_cases K2; zify_cond K2.
        * (* [comment removed for export] *) use im_ret.
        * zstep. zstep. use (im_bl (Z.to_nat (n - 1)) _ (n - 1)%Z).
    - (* [comment removed for export] *)
      zstep. if_cases K2; zify_cond K2.
      + use im_ret.
      + zstep. zstep. use (im_fl (Z.to_nat (n - 1)) _ 0%Z).
  Qed.
End Proofs.

Lemma imemmove_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  (bv_unsigned a1 + bv_unsigned a2 <= 2^63 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^63)%Z ->
  stk bsegs m (bv_unsigned a0) (bv_unsigned a0 + bv_unsigned a2) -> rdbl bsegs m (bv_unsigned a1) (bv_unsigned a1 + bv_unsigned a2) ->
  mem_inv bsegs m ->
  rng RNG (bv_unsigned a1) (bv_unsigned a2) -> rng RNG (bv_unsigned a0) (bv_unsigned a2) ->
  evtF bsegs RNG (imemmove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 imemmove_entry) fc None m (seg_rom bsegs)).
Proof. intros. eapply imemmove_body; eauto. Qed.
End CANSEC1.
