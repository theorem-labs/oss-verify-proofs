(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AIcpm9j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma sh_mul8 : forall q, sh (8 * q) = q + kShadowOffset.
Proof. intros. unfold sh. f_equal. lia. Qed.
(* [comment removed for export] *)
Lemma shiftr3_mul8 : forall q, 0 <= q -> Z.shiftr (8 * q) 3 = q.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. Qed.
Lemma div8_mul8 : forall d, 8 * d / 8 = d.
Proof. intros. lia. Qed.
Lemma land_mask48_m8 : forall d e, 0 <= e < 8 -> 0 <= d -> 8 * d + e < 2^48 -> Z.land (8 * d + e) 281474976710648 = 8 * d.
Proof.
  intros d e He Hd Hx.
  replace 281474976710648 with (Z.land (Z.ones 48) (2^64 - 2^3)) by reflexivity.
  rewrite Z.land_assoc.
  rewrite Z.land_ones_low; [| lia |].
  2:{ destruct (Z.eq_dec (8 * d + e) 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  rewrite land_align_down by lia. change (2^3) with 8. lia.
Qed.
Lemma mod8_mul8 : forall d, (8 * d) mod 8 = 0.
Proof. intros. lia. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_land_ones7 : forall n d e, n = 8 * d + e -> 0 <= e < 8 -> 0 <= d -> n < 2^64 ->
  Z.land (Z.land n 18446744073709551615) 7 = e.
Proof.
  intros n d e H He Hd Hn. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite Z.mod_small by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. subst. lia.
Qed.
Lemma swrap32_small : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (Z.of_N 32) with 32. change (2 ^ 32 / 2) with (2^31). rewrite Z.mod_small; lia.
Qed.
Lemma sllw_rz : forall n, bv_swrap 32 (Z.shiftl 16 (rz_log n mod 32)) = rz_size n.
Proof.
  intros n. pose proof (rz_log_range n). pose proof (rz_size_range n). rewrite Z.mod_small by lia.
  rewrite <- rz_size_eq. apply swrap32_small. lia.
Qed.

(* [comment removed for export] *)

Ltac solve_amo_align :=
  repeat match goal with
  | |- context [negb (Z.eqb (Z.modulo (bv_unsigned ?x) ?b) 0)] =>
      let E := fresh "AL" in
      assert (E : negb (Z.eqb (Z.modulo (bv_unsigned x) b) 0) = false)
        by (rewrite ?unsigned_lit by lia; apply (proj2 (Bool.negb_false_iff _)); apply Z.eqb_eq; lia);
      rewrite E; clear E; cbv beta iota
  end.
Ltac amstep_core segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbv; cbv beta iota zeta delta [amo_aligned amo_bytes]; simp_is_x0; simp_regs; fold_lit_ux; fold_xlits;
          eval_lit_tests; solve_amo_align; vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | simp_regs; vnorm_for i; try fix_lit_store; fix_le1_lit; mem_after_store_opt; post_step i; fold_xlits ]
      | None => fail "undecodable instruction at" pc
      end
  | None => fail "no instruction at" pc
  end.
Ltac amstep :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => amstep_core segs R F pc fc rv m ro
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.
Ltac amz := amstep; zsimp.
Ltac cur := match goal with |- evt _ _ (MS ?R _ ?pc _ _ ?mm _) => idtac pc end.

Lemma lxor_ones64 : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite <- Z.ldiff_ones_l_low; [| lia |].
  2:{ destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  rewrite Z.sub_nocarry_ldiff; [reflexivity|].
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma b2z_ltb_false : forall a b, b <= a -> Z.b2z (a <? b) = 0.
Proof. intros a b H. destruct (Z.ltb_spec a b); [lia| reflexivity]. Qed.
Lemma b2z_ltb_true : forall a b, a < b -> Z.b2z (a <? b) = 1.
Proof. intros a b H. destruct (Z.ltb_spec a b); [reflexivity| lia]. Qed.

Lemma sx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (Z.of_N 32) with 32. rewrite Z.mod_small; [change (2 ^ 32 / 2) with (2^31); lia|].
  change (2 ^ 32 / 2) with (2^31). lia.
Qed.
Lemma zx32_small : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite unsigned_lit by lia. f_equal. apply Z.mod_small. lia. Qed.
Lemma zx32_word : forall w : word, bv_unsigned w < 2^32 -> zx32 w = w.
Proof. intros w Hw. unfold zx32. pose proof (bv_unsigned_in_range _ w). rewrite Z.mod_small by lia. apply Z_to_bv_bv_unsigned. Qed.

Lemma slli32_srli30 : forall x, 0 <= x < 2^30 -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 30 = x * 4.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (change 18446744073709551616 with (2^32 * 2^32); nia).
  rewrite Z.shiftr_div_pow2 by lia. replace (x * 2 ^ 32) with ((x * 4) * 2 ^ 30) by (change (2^32) with (4 * 2^30); lia).
  rewrite Z.div_mul by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma pc_chunks_u32arr : forall (m : word -> option byte) E a b d ks,
  rw_cells rsegs m E [C4 a; C4 b; C8 d; CB 64 (u32s ks)] -> length ks = 16%nat -> u32arr rsegs m (E + 16) ks.
Proof.
  intros m E a b d ks [[WFc B] W] L. cbn [cells_bytes cbytes app] in B.
  assert (B16 : bytes_at rsegs m (E + 16) (u32s ks)).
  { apply bytes_at_app in B as [_ B]. rewrite length_le4 in B. apply bytes_at_app in B as [_ B]. rewrite length_le4 in B.
    apply bytes_at_app in B as [_ B]. rewrite length_le8 in B.
    lazymatch type of B with bytes_at _ _ ?a ?l =>
      first [ apply bytes_at_app in B as [B _] | idtac ];
      replace (E + 16) with a by lia end.
    lazymatch type of B with bytes_at _ _ _ (u32s ks ++ []) => rewrite app_nil_r in B | _ => idtac end. exact B. }
  split; [exact B16|]. destruct W as (W0 & W1 & W2). cbn [cells_size csize Nat.add] in W1, W2.
  split; [lia|]. split; [rewrite L; lia|]. intros i Hi. rewrite L in Hi. replace (E + 16 + i) with (E + (16 + i)) by lia. apply W2. lia.
Qed.

Lemma mod_add_lit : forall a b k, 0 < k -> a mod k = 0 -> b mod k = 0 -> (a + b) mod k = 0.
Proof. intros a b k K A B. rewrite Z.add_mod, A, B by lia. rewrite Z.mod_small; lia. Qed.
Ltac modtac := first [ assumption | reflexivity | apply mod8_mul8 | apply needed_size_mod8 | apply rounded_size_mod8
                     | apply mod_add_lit; [lia | modtac | modtac]
                     | apply (fun a => mod0_down a 32 8 ltac:(exists 4; reflexivity)); modtac
                     | apply (fun a => mod0_down a 16 8 ltac:(exists 2; reflexivity)); modtac
                     | apply rz_size_mod16 ].
Ltac kun := cbv delta [kHighMemBeg kDepotNodesBlock kStackStoreBlockBytes kShadowOffset kStackStoreBlockFrames kMaxSize
                       kAsanHeapLeftRedzoneMagic kMaxPrimaryUser] in *.
Ltac sides1 := first [ eassumption | reflexivity | lia | kun; lia | modtac
                     | rewrite ?unsigned_lit by lia; first [eassumption | reflexivity | lia | modtac] ].
Ltac sides := lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- _ /\ _ => split; sides
  | |- _ => sides1 end.
Ltac sregs := let v := reg_val 10 in idtac "a0" v; let v := reg_val 11 in idtac "a1" v; let v := reg_val 12 in idtac "a2" v;
  let v := reg_val 8 in idtac "s0" v; let v := reg_val 9 in idtac "s1" v; let v := reg_val 18 in idtac "s2" v;
  let v := reg_val 19 in idtac "s3" v; let v := reg_val 20 in idtac "s4" v; let v := reg_val 21 in idtac "s5" v;
  let v := reg_val 22 in idtac "s6" v; let v := reg_val 23 in idtac "s7" v; let v := reg_val 24 in idtac "s8" v;
  let v := reg_val 25 in idtac "s9" v; let v := reg_val 26 in idtac "s10" v; let v := reg_val 27 in idtac "s11" v.
Lemma le1_any : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. rewrite le1_single. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64%N) with (2^64). change (bv_modulus 8%N) with (2^8).
  symmetry. apply Znumtheory.Zmod_div_mod; [lia|lia|]. exists (2^56). reflexivity.
Qed.
Ltac sb_done := lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) => rewrite (le1_any z); mem_after_store
  end.

Ltac arun_to pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => first [amz | if_false | if_true] end).

(* [comment removed for export] *)
Definition alloc_s1a_frame (sp : word) (canfill : Z) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) (junk0 : list byte) : list cell :=
  [CB 8 junk0; C8 (Z_to_bv 64 canfill); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition b1_mid (old : Z) : Z := Z.lor (Z.land (Z.lor (Z.land old 18446744073709551612) 1) 143) 16.
(* [comment removed for export] *)
Definition fill_result (canfill : Z) (uj : list byte) (k : nat) : list byte :=
  if canfill =? 0 then uj else repeat (Z_to_bv 8 kMallocFillByte) k.
