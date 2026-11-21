(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import PropExec Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma ub_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma ub_land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma ub_land1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac ub_norm K := rewrite ?ub_land7, ?ub_land3, ?ub_land1 in K.

Lemma ub_m_add : forall n p k, p mod n = 0 -> k mod n = 0 -> (p + k) mod n = 0.
Proof. intros n p k Hp Hk. destruct (Z.eq_dec n 0) as [->|N]; [rewrite Zmod_0_r in *; lia|]. rewrite Z.add_mod by exact N. rewrite Hp, Hk. apply Z.mod_0_l. exact N. Qed.
Lemma ub_m_mul_l : forall n a x, a mod n = 0 -> (a * x) mod n = 0.
Proof. intros n a x Ha. destruct (Z.eq_dec n 0) as [->|N]; [rewrite Zmod_0_r in *; subst a; reflexivity|]. rewrite Z.mul_mod by exact N. rewrite Ha. rewrite Z.mul_0_l. apply Z.mod_0_l. exact N. Qed.
Lemma ub_m_mul_r : forall n a x, a mod n = 0 -> (x * a) mod n = 0.
Proof. intros n a x Ha. rewrite Z.mul_comm. apply ub_m_mul_l. exact Ha. Qed.
Lemma ub_m_weaken : forall n m p, p mod m = 0 -> m mod n = 0 -> 0 < n -> 0 < m -> p mod n = 0.
Proof.
  intros n m p Hp Hm N M. apply Z.mod_divide in Hp; [| lia]. apply Z.mod_divide in Hm; [| lia]. apply Z.mod_divide; [lia|].
  eapply Z.divide_trans; eassumption.
Qed.
Ltac ub_al :=
  first [ eassumption
        | reflexivity
        | apply ub_m_add; ub_al
        | apply ub_m_mul_l; reflexivity
        | apply ub_m_mul_r; reflexivity
        | eapply ub_m_weaken; [eassumption| reflexivity| lia| lia] ].

Lemma ub_b2z_range : forall b, 0 <= Z.b2z b <= 1.
Proof. intros []; cbn; lia. Qed.
Lemma ub_swrap_mod : forall e, 0 <= e < 2147483648 ->
  bv_swrap 32 (e mod 18446744073709551616) mod 18446744073709551616 = e mod 18446744073709551616.
Proof. intros e H. rewrite (Z.mod_small e) by lia. rewrite swrap32_small by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Ltac ub_bound :=
  rewrite ?Z.shiftl_mul_pow2 by lia;
  repeat match goal with |- context [2 ^ ?k] => is_Zlit k; let p := eval vm_compute in (2 ^ k) in change (2 ^ k) with p end;
  repeat match goal with
  | |- context [Z.b2z ?b] =>
      let v := fresh "bz" in let H := fresh "BZ" in
      pose proof (ub_b2z_range b) as H; set (v := Z.b2z b) in *; clearbody v
  end;
  lia.

Lemma ub_lor_b2z : forall a b, Z.lor (Z.b2z a) (Z.b2z b) = Z.b2z (a || b).
Proof. intros [] []; reflexivity. Qed.
Lemma ub_land_b2z : forall a b, Z.land (Z.b2z a) (Z.b2z b) = Z.b2z (a && b).
Proof. intros [] []; reflexivity. Qed.
Ltac ub_prep :=
  rewrite ?ub_lor_b2z, ?ub_land_b2z;
  rewrite ?Z.shiftl_mul_pow2 by lia;
  repeat match goal with |- context [2 ^ ?k] => is_Zlit k; let p := eval vm_compute in (2 ^ k) in change (2 ^ k) with p end;
  repeat match goal with
  | |- context [Z.b2z ?b] =>
      let v := fresh "bz" in let H := fresh "BZ" in
      pose proof (ub_b2z_range b) as H; set (v := Z.b2z b) in *; clearbody v
  end.
Ltac ub_close_pat K :=
  lazymatch type of K with
  | ?x mod ?n <> 0 => apply K; ub_al
  | bv_swrap 32 _ mod _ <> _ =>
      apply K; ub_prep; rewrite ?Z.mod_small by lia; rewrite swrap32_small by lia; rewrite ?Z.mod_small by lia; reflexivity
  end.
Ltac ub_close_ne_fast K :=
  lazymatch type of K with
  | _ <> _ =>
      apply K; rewrite ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r, ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r, ?Zmod_mod; reflexivity
  end.
Ltac ub_close_ne_slow K :=
  lazymatch type of K with
  | _ <> _ => apply K; ub_prep; rewrite ?Z.mod_small by lia; first [ reflexivity | lia ]
  end.
Ltac ub_close_guard K := first [ ub_close_pat K | ub_close_ne_fast K | ub_close_ne_slow K | lia ].
Ltac ub_close K := first [ lia | ub_close_pat K | ub_close_ne_fast K ].

Ltac ub_is_trap pc := fail.
Ltac ub_in_traps L pc :=
  let b := eval vm_compute in (existsb (Z.eqb pc) L) in
  lazymatch b with true => idtac end.

Lemma ub_eqb_mod : forall A B, A mod 2^64 = B mod 2^64 -> bv_eqb (Z_to_bv 64 A) (Z_to_bv 64 B) = true.
Proof. intros A B H. rewrite <- (Z_to_bv_mod64 A), <- (Z_to_bv_mod64 B), H. apply PropExec.bv_eqb_refl. Qed.
Ltac ub_mod_alg :=
  change (2 ^ 64) with 18446744073709551616;
  rewrite ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r, ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r, ?Zmod_mod; reflexivity.

Ltac pc_dec ::=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      lazymatch goal with _ : pcd_live c |- _ => fail | _ => idtac end;
      first [
              lazymatch a with Z_to_bv 64 ?pa => ub_is_trap pa end;
              lazymatch c with negb (bv_eqb (Z_to_bv 64 ?A) (Z_to_bv 64 ?B)) =>
                replace (if c then a else b) with b
                  by (replace c with false by (symmetry; apply Bool.negb_false_iff; apply ub_eqb_mod; ub_mod_alg); reflexivity)
              end
            |
              lazymatch a with Z_to_bv 64 ?pa => ub_is_trap pa end;
              replace (if c then a else b) with b
                by (let K := fresh "K" in destruct c eqn:K; [exfalso; zify_cond K; ub_norm K; ub_close_guard K | reflexivity])
            |
              lazymatch b with Z_to_bv 64 ?pb => ub_is_trap pb end;
              replace (if c then a else b) with a
                by (let K := fresh "K" in destruct c eqn:K; [reflexivity | exfalso; zify_cond K; ub_norm K; ub_close_guard K])
            | replace (if c then a else b) with a
                by (let K := fresh "K" in destruct c eqn:K; [reflexivity | exfalso; zify_cond K; ub_norm K; ub_close K])
            | replace (if c then a else b) with b
                by (let K := fresh "K" in destruct c eqn:K; [exfalso; zify_cond K; ub_norm K; ub_close K | reflexivity])
            | let H := fresh "PCDL" in assert (H : pcd_live c) by exact I ]
  end.

Ltac ub_small := first [ lia | ub_prep; rewrite ?Z.mod_small by lia; lia ].
Ltac znorm ::=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?e)] =>
      nz_fresh e; first [ rewrite (sx32_small e) by ub_small | rewrite (sx32_sint e) by lia | nz_mark e ]
  | |- context [bv_swrap 32 (?e + ?l)] =>
      is_Zlit l;
      let big := eval vm_compute in (9223372036854775808 <=? l) in
      lazymatch big with true => idtac end;
      nz_fresh (e + l);
      first [ let k := eval vm_compute in (18446744073709551616 - l) in
              change l with (18446744073709551616 - k); rewrite (swrap32_sublit e k) by lia
            | nz_mark (e + l) ]
  | |- context [bv_swrap 32 ?e] => nz_fresh e; first [ rewrite (swrap32_small e) by ub_small | nz_mark e ]
  end.

Ltac show_cond :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      let K := fresh "K" in destruct c eqn:K; [ zify_cond K; ub_norm K; let t := type of K in idtac "TAKEN:" t | zify_cond K; ub_norm K; let t := type of K in idtac "NOT TAKEN:" t ]
  end.
