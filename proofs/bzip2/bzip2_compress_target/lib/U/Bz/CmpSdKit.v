(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Definition isite (segs : list Segment) (a q : Z) : Prop :=
  exists w, fetch_word segs (Z_to_bv 64 a) = Some w /\ fetch_word segs (Z_to_bv 64 q) = Some w.

(* [comment removed for export] *)
Fixpoint same_code (segs : list Segment) (p q : Z) (n : nat) : Prop :=
  match n with O => True | S n' => isite segs p q /\ same_code segs (p + 4) (q + 4) n' end.

Lemma same_code_nth : forall segs n p q k, same_code segs p q n -> (k < n)%nat ->
  isite segs (p + 4 * Z.of_nat k) (q + 4 * Z.of_nat k).
Proof.
  induction n as [|n IH]; intros p q k SC Hk; [lia|].
  destruct SC as [H0 SC]. destruct k as [|k].
  - rewrite !Z.mul_0_r, !Z.add_0_r. exact H0.
  - specialize (IH (p + 4) (q + 4) k SC ltac:(lia)).
    replace (p + 4 * Z.of_nat (S k)) with (p + 4 + 4 * Z.of_nat k) by lia.
    replace (q + 4 * Z.of_nat (S k)) with (q + 4 + 4 * Z.of_nat k) by lia. exact IH.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
End ACeilS1.


(* [comment removed for export] *)
Ltac same_code_tac :=
  cbn [same_code]; repeat match goal with |- _ /\ _ => split end; try exact I;
  lazymatch goal with
  | |- isite ?segs ?a ?q =>
      let aa := eval vm_compute in a in let qq := eval vm_compute in q in
      change (isite segs aa qq);
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 qq)) in
      lazymatch fw with Some ?w => exists w; split; vm_compute; reflexivity end
  end.

(* [comment removed for export] *)
Ltac pstep_with SC p q n k :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pce ?fc ?rv ?m ?ro) =>
    let kn := eval vm_compute in (Z.to_nat (k / 4)) in
    let qa := eval vm_compute in (q + k)%Z in
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 qa)) in
    lazymatch fw with
    | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        let Hs := fresh "Hs" in
        pose proof (same_code_nth segs n p q kn SC ltac:(lia)) as Hs;
        replace (p + 4 * Z.of_nat kn)%Z with (p + k)%Z in Hs by lia;
        replace (q + 4 * Z.of_nat kn)%Z with qa in Hs by lia;
        let wv := fresh "wv" in let H1 := fresh "Hf1" in let H2 := fresh "Hf2" in
        cps_destruct Hs as (wv & H1 & H2);
        assert (wv = w) by (apply (f_equal (fun o => match o with Some x => x | None => w end)) in H2;
                            rewrite <- H2; vm_compute; reflexivity);
        subst wv; clear H2;
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F pce fc rv m ro w i sz H1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
          exec_pre i;
          exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | simp_regs; vnorm_for i; mem_after_store_opt; post_step i ];
        clear H1
      | None => fail "undecodable instruction at" qa
      end
    | None => fail "no instruction at" qa
    end
  end.

(* [comment removed for export] *)
Ltac pcnorm p :=
  let fix1 e :=
    lazymatch e with
    | (p + ?a + ?b)%Z => let c := eval vm_compute in (a + b)%Z in
        replace (Z_to_bv 64 e) with (Z_to_bv 64 (p + c)%Z) by (f_equal; lia)
    | (p + ?a)%Z => idtac
    | p => idtac
    | _ => idtac
    end in
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then Z_to_bv 64 ?e1 else Z_to_bv 64 ?e2) ?fc ?rv ?m ?ro) => fix1 e1; fix1 e2
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?e) ?fc ?rv ?m ?ro) => fix1 e
  | _ => idtac
  end.

Ltac pstep0 SC :=
  lazymatch type of SC with
  | same_code ?segs ?p ?q ?n =>
    pcnorm p;
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 (p + ?k)%Z) _ _ _ _) => pstep_with SC p q n k
    | |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) =>
        replace (Z_to_bv 64 p) with (Z_to_bv 64 (p + 0)%Z) by (f_equal; lia); pstep_with SC p q n 0%Z
    | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pstep: pc not of the form p+k:" pc
    end
  end.
(* [comment removed for export] *)
Ltac pstep SC := pstep0 SC; zsimp; bz32; lazymatch type of SC with same_code _ ?p _ _ => pcnorm p end.
Section ACeilS2. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Lemma shl_mod32_congr : forall a b s, 0 <= s -> a mod 4294967296 = b mod 4294967296 ->
  Z.shiftl a s mod 4294967296 = Z.shiftl b s mod 4294967296.
Proof.
  intros a b s Hs H. rewrite !Z.shiftl_mul_pow2 by lia.
  rewrite <- (Zmult_mod_idemp_l a), <- (Zmult_mod_idemp_l b), H. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma same_code_prefix : forall segs n n' p q, same_code segs p q n' -> (n <= n')%nat -> same_code segs p q n.
Proof.
  intros segs n. induction n as [|n IH]; intros n' p q SC Hn; [exact I|].
  destruct n' as [|n']; [lia|]. destruct SC as [H SC]. split; [exact H|]. eapply IH; [exact SC| lia].
Qed.
Lemma same_code_skip : forall segs k p q n, same_code segs p q n ->
  same_code segs (p + 4 * Z.of_nat k) (q + 4 * Z.of_nat k) (n - k).
Proof.
  intros segs k. induction k as [|k IH]; intros p q n SC.
  - rewrite !Z.mul_0_r, !Z.add_0_r, Nat.sub_0_r. exact SC.
  - destruct n as [|n]; [exact I|]. destruct SC as [_ SC]. cbn [Nat.sub].
    specialize (IH (p + 4) (q + 4) n SC).
    replace (p + 4 * Z.of_nat (S k)) with (p + 4 + 4 * Z.of_nat k) by lia.
    replace (q + 4 * Z.of_nat (S k)) with (q + 4 + 4 * Z.of_nat k) by lia. exact IH.
Qed.

End ACeilS2.
