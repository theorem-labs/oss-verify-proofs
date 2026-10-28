(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_stage2_traps Sj_stage2_guard.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma tape_img_app2w : forall E tws sbs (m1 : mem) (w1 w2 : word) A1 A2, env_ok E -> tape_img E tws sbs m1 ->
  bytes_at usegs m1 A1 (le8 w1) -> bytes_at usegs m1 A2 (le8 w2) ->
  A1 = (e_TAPE E + 8 * Z.of_nat (length tws))%Z -> A2 = (A1 + 8)%Z -> (Z.of_nat (length tws) + 2 <= e_tcap E)%Z ->
  tape_img E (tws ++ [bv_unsigned w1; bv_unsigned w2]) (sbs ++ []) m1.
Proof.
  intros E tws sbs m1 w1 w2 A1 A2 OK TI B1 B2 E1 E2 HL.
  pose proof (bv_unsigned_in_range 64 w1) as R1. pose proof (bv_unsigned_in_range 64 w2) as R2. unfold bv_modulus in R1, R2. cbn in R1, R2.
  apply (tape_img_app2 E tws sbs m1 (bv_unsigned w1) (bv_unsigned w2) A1 A2 OK TI); rewrite ?Z_to_bv_bv_unsigned;
    [exact B1 | exact B2 | exact E1 | exact E2 | exact HL | lia | lia].
Qed.

Lemma tape_img_app1w : forall E tws sbs (m1 : mem) (w1 : word) A1, env_ok E -> tape_img E tws sbs m1 ->
  bytes_at usegs m1 A1 (le8 w1) -> A1 = (e_TAPE E + 8 * Z.of_nat (length tws))%Z -> (Z.of_nat (length tws) + 1 <= e_tcap E)%Z ->
  tape_img E (tws ++ [bv_unsigned w1]) (sbs ++ []) m1.
Proof.
  intros E tws sbs m1 w1 A1 OK TI B1 E1 HL.
  pose proof (bv_unsigned_in_range 64 w1) as R1. unfold bv_modulus in R1. cbn in R1.
  apply (tape_img_app1 E tws sbs m1 (bv_unsigned w1) A1 OK TI); rewrite ?Z_to_bv_bv_unsigned; [exact B1 | exact E1 | exact HL | lia].
Qed.

Ltac s2_tape2 :=
  match goal with
  | OKh : env_ok ?E0, TI : tape_img ?E0 ?tws ?sbs ?m, N1 : bytes_at _ ?m ?A1 (le8 ?w1), N2 : bytes_at _ ?m ?A2 (le8 ?w2) |- _ =>
      let TI2 := fresh "TIMG" in
      pose proof (tape_img_app2w E0 tws sbs m w1 w2 A1 A2 OKh TI N1 N2 ltac:(tlia) ltac:(tlia) ltac:(tlia)) as TI2;
      clear TI; clear N1 N2
  | _ => fail 100 "s2_tape2: no pair of noted tape chunks right after the written prefix"
  end.

Ltac s2_num_word :=
  lazymatch goal with
  | |- num_word _ => vm_compute; first [left; reflexivity | right; left; reflexivity | right; right; reflexivity]
  | |- _ => fail 100 "s2_num_word: not a num_word goal"
  end.

Ltac s2_a09 :=
  first [ left; reflexivity | right; reflexivity
        | lazymatch goal with |- (?x = _ \/ _)%Z =>
            lazymatch x with context [if ?f then _ else _] => destruct f; first [left; reflexivity | right; reflexivity] end end
        | fail 100 "s2_a09: cannot show the flag is 0 or 9" ].

Ltac s2_has_var t := match t with context [?x] => is_var x end.
Ltac s2_errok_lit := left; vm_compute; split; [discriminate | reflexivity].

Ltac s2_bv_ranges H :=
  repeat match type of H with context [bv_unsigned ?w] =>
    is_var w;
    lazymatch goal with
    | _ : (0 <= bv_unsigned w < _)%Z |- _ => fail
    | _ => let R := fresh "BR" in pose proof (bv_unsigned_in_range _ w) as R; unfold bv_modulus in R; cbn in R
    end end.

Ltac s2_errok_refute :=
  exfalso;
  repeat match goal with H : @eq bool ?a _ |- _ =>
    lazymatch a with
    | context [usegs] => fail
    | context [write_to_mem] => fail
    | _ => progress (zify_cond H); try s2_bv_ranges H
    end end;
  lia.
Ltac s2_errok_code :=
  lazymatch goal with
  | |- s2_errok _ ?V =>
      tryif s2_has_var V then
        first [ is_var V;
                match goal with H09 : (V = 0 \/ V = 9)%Z |- _ =>
                  destruct H09 as [H09 | H09]; subst V; [ s2_errok_refute | s2_errok_lit ] end
              | match V with context [Z.b2z ?c] =>
                  let Hc := fresh "Hc" in destruct c eqn:Hc; cbn [Z.b2z];
                  first [ s2_errok_lit | zify_cond Hc; try s2_bv_ranges Hc; s2_errok_refute ] end
              | fail 100 "s2_errok_code: cannot bound the (open) error code" V ]
      else first [ s2_errok_lit | fail 100 "s2_errok_code: the closed error code is not in [1,64)" V ]
  | |- _ => fail 100 "s2_errok_code: not an s2_errok goal"
  end.

Ltac s2_kvr K :=
  lazymatch goal with
  | TI : tape_img _ (_ ++ [?v; ?r]) (_ ++ []) _ |- _ => eapply (K v r)
  | |- _ => fail 100 "s2_kvr: no extended tape image in the context (run s2_tape2 first)"
  end.

Lemma disjoint_from_sub : forall W a n a' n', disjoint_from W a n -> (a <= a')%Z -> (a' + n' <= a + n)%Z -> (0 <= n')%Z -> disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros a n a' n' H H1 H2 H3; [exact I|].
  destruct H as [H HW]. split; [lia | eapply IH; eauto].
Qed.

Lemma tape_img_call : forall E tws sbs W (m m' : mem), tape_img E tws sbs m -> munch W m m' -> wmono usegs m m' ->
  disjoint_from W (e_TAPE E) (8 * e_tcap E) -> disjoint_from W (e_SBUF E) (e_scap E) -> tape_img E tws sbs m'.
Proof.
  intros E tws sbs W m m' (T1 & T2 & T3 & T4 & S1 & S2 & SB) MU WM D1 D2.
  pose proof (Zle_0_nat (length tws)). pose proof (Zle_0_nat (length sbs)).
  split; [|split; [|split; [exact T3|split; [exact T4|split; [|split; [|exact SB]]]]]].
  - eapply bytes_at_transport; [exact T1 | exact MU |]. eapply disjoint_from_sub; [exact D1 | lia | rewrite twords_length; lia | lia].
  - eapply bytes_at_transport; [exact T2 | exact MU |]. eapply disjoint_from_sub; [exact D2 | lia | rewrite zbytes_length; lia | lia].
  - eapply stk_transport_disjoint; [exact S1 | exact MU | exact WM |]. eapply disjoint_from_sub; [exact D1 | lia | lia | lia].
  - eapply stk_transport_disjoint; [exact S2 | exact MU | exact WM |]. eapply disjoint_from_sub; [exact D2 | lia | lia | lia].
Qed.

Ltac s2_timg_call segs W m m' MU WM :=
  lazymatch goal with
  | H : tape_img ?E ?tws ?sbs m |- _ =>
      first [ apply (tape_img_call E tws sbs W m m') in H; [ | exact MU | exact WM | cbn [disjoint_from]; repeat split; first [exact I | tlia] | cbn [disjoint_from]; repeat split; first [exact I | tlia] ]
            | fail 100 "tape_img: cannot transport across the call (footprint not provably disjoint from tape / string buffer)" ]
  | _ => idtac
  end.

Lemma u_start_word : forall oc x, (0 <= x < 2^32)%Z -> (0 <= oc < 256)%Z -> Z.lor x (oc * 72057594037927936) = cword oc x 0.
Proof.
  intros oc x Hx Hoc. unfold cword. replace (x + 0 * 2^32)%Z with x by lia. change 72057594037927936%Z with (2^56)%Z.
  rewrite <- Z.shiftl_mul_pow2 by lia. apply tword_lor'. lia.
Qed.
Lemma u_close_word : forall t x, (0 <= x < 2^32)%Z -> (0 <= t < 256)%Z -> Z.lor (Z.land x 4294967295) (t * 72057594037927936) = tword t x.
Proof.
  intros t x Hx Ht. change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  change 72057594037927936%Z with (2^56)%Z. rewrite <- Z.shiftl_mul_pow2 by lia. apply tword_lor'. lia.
Qed.

Ltac s2_empty_words oc :=
  lazymatch goal with
  | TI : tape_img _ (_ ++ [bv_unsigned (Z_to_bv 64 (Z.lor ?x ?c1)); bv_unsigned (Z_to_bv 64 (Z.lor (Z.land ?y 4294967295) ?c2))]) _ _ |- _ =>
      let k1 := eval cbv in (oc * 72057594037927936)%Z in change c1 with (oc * 72057594037927936)%Z in TI;
      let k2 := eval cbv in ((oc + 2) * 72057594037927936)%Z in change c2 with ((oc + 2) * 72057594037927936)%Z in TI;
      rewrite (u_start_word oc x) in TI by lia; rewrite (u_close_word (oc + 2) y) in TI by lia;
      rewrite (u64_small (cword oc x 0)) in TI by (apply cword_range; lia); rewrite (u64_small (tword (oc + 2) y)) in TI by (apply tword_range; lia)
  | |- _ => fail 100 "s2_empty_words: no extended tape image with the two machine words"
  end.

Ltac s2_lit_words w1 w2 :=
  lazymatch goal with
  | TI : tape_img _ (_ ++ [bv_unsigned (Z_to_bv 64 ?a); bv_unsigned (Z_to_bv 64 ?b)]) _ _ |- _ =>
      change (bv_unsigned (Z_to_bv 64 a)) with w1 in TI; change (bv_unsigned (Z_to_bv 64 b)) with w2 in TI
  | |- _ => fail 100 "s2_lit_words: no extended tape image with two words"
  end.

Definition endc_env (E : s2env) (oc ti Wv cv : Z) : s2env := gapp (gpatch E ti (cword oc (Wv + 1) cv)) [tword (oc + 2) ti] [].

Lemma u_tword_machine : forall t v K, K = (t * 72057594037927936)%Z -> (0 <= v < 2^56)%Z -> (0 <= t < 256)%Z -> Z.lor v K = tword t v.
Proof.
  intros t v K -> Hv Ht. change 72057594037927936%Z with (2^56)%Z. rewrite <- Z.shiftl_mul_pow2 by lia. apply tword_lor'. exact Hv.
Qed.
Lemma u_cword_machine : forall A Wv cv oc K, K = (oc * 72057594037927936)%Z -> (0 <= Wv + 1 < 2^32)%Z -> (0 <= cv < 2^24)%Z -> (0 <= oc < 256)%Z ->
  Z.lor (Z.lor (Z.shiftr (Z.shiftl (A + 8 * Wv + 8 - A) 29 mod 18446744073709551616) 32) (Z.shiftl cv 32 mod 18446744073709551616)) K
  = cword oc (Wv + 1) cv.
Proof.
  intros A Wv cv oc K -> HW Hc Hoc.
  replace (A + 8 * Wv + 8 - A)%Z with ((Wv + 1) * 2^3)%Z by lia.
  rewrite !Z.shiftl_mul_pow2 by lia. rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. change (3 + 29)%Z with 32%Z.
  rewrite (Z.mod_small ((Wv + 1) * 2^32)) by lia. rewrite Z.shiftr_div_pow2, Z.div_mul by lia.
  rewrite (Z.mod_small (cv * 2^32)) by lia.
  rewrite <- Z.lor_assoc. change 72057594037927936%Z with (2^56)%Z.
  rewrite <- (Z.shiftl_mul_pow2 cv 32), <- (Z.shiftl_mul_pow2 oc 56) by lia.
  apply cword_lor; lia.
Qed.

Ltac s2_endc_patch oc ti cv :=

  (lazymatch cv with
   | Zpos _ => let k := eval cbv in (Z.shiftl cv 32 mod 18446744073709551616)%Z in change k with (Z.shiftl cv 32 mod 18446744073709551616)%Z
   | _ => idtac end);
  lazymatch goal with
  | OKh : env_ok ?E, TI : tape_img ?E _ _ ?m |- context [Z.lor (Z.lor (Z.shiftr (Z.shiftl (e_TAPE ?E + 8 * ?Wv + 8 - e_TAPE ?E) 29 mod 18446744073709551616) 32) _) ?K] =>
      rewrite (u_cword_machine (e_TAPE E) Wv cv oc K) by (first [reflexivity | lia]);
      apply (tape_img_patchZ E _ _ m ti (cword oc (Wv + 1) cv) OKh) in TI; [ | lia | apply cword_range; lia ];
      s2_store_done_wr_v2
  | |- _ => fail 100 "s2_endc_patch: the goal is not the back-patch store"
  end.

Ltac s2_endc_close oc ti :=
  match goal with
  | OKh : env_ok ?E, TI : tape_img ?E _ _ ?m, NW : bytes_at _ ?m ?A (le8 (Z_to_bv 64 (Z.lor ti ?K))) |- _ =>
      rewrite (u_tword_machine (oc + 2) ti K) in NW by (first [reflexivity | lia]);
      apply (tape_img_app1 E _ _ m (tword (oc + 2) ti) A OKh) in TI; [ | exact NW | rewrite zupd_length; lia | rewrite zupd_length; lia | apply tword_range; lia ];
      clear NW
  | |- _ => fail 100 "s2_endc_close: no noted close word / patched image in the context"
  end.
