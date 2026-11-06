(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Sj_stage2_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma tape_img_app2w : forall E tws sbs (m1 : mem) (w1 w2 : word) A1 A2, env_ok E -> tape_img E tws sbs m1 ->
  bytes_at psegs m1 A1 (le8 w1) -> bytes_at psegs m1 A2 (le8 w2) ->
  A1 = (e_TAPE E + 8 * Z.of_nat (length tws))%Z -> A2 = (A1 + 8)%Z -> (Z.of_nat (length tws) + 2 <= e_tcap E)%Z ->
  tape_img E (tws ++ [bv_unsigned w1; bv_unsigned w2]) (sbs ++ []) m1.
Proof.
  intros E tws sbs m1 w1 w2 A1 A2 OK TI B1 B2 E1 E2 HL.
  pose proof (bv_unsigned_in_range 64 w1) as R1. pose proof (bv_unsigned_in_range 64 w2) as R2. unfold bv_modulus in R1, R2. cbn in R1, R2.
  apply (tape_img_app2 E tws sbs m1 (bv_unsigned w1) (bv_unsigned w2) A1 A2 OK TI); rewrite ?Z_to_bv_bv_unsigned;
    [exact B1 | exact B2 | exact E1 | exact E2 | exact HL | lia | lia].
Qed.

Lemma tape_img_app1w : forall E tws sbs (m1 : mem) (w1 : word) A1, env_ok E -> tape_img E tws sbs m1 ->
  bytes_at psegs m1 A1 (le8 w1) -> A1 = (e_TAPE E + 8 * Z.of_nat (length tws))%Z -> (Z.of_nat (length tws) + 1 <= e_tcap E)%Z ->
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

Ltac s2_refute_by_closed_hyp :=
  match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | context [psegs] => fail
      | context [write_to_mem] => fail
      | context [evt] => fail
      | @eq bool _ _ => exfalso; clear - H; revert H; vm_compute; first [discriminate | congruence]
      | not _ => exfalso; clear - H; revert H; vm_compute;
                 let H' := fresh in intros H'; first [exact (H' eq_refl) | congruence]
      end
  end.

Ltac s2_errnz_lit := lazymatch goal with |- s2_fail (Z_to_bv 64 ?V) => is_Zlit V; s2_errnz end.

Ltac s2_err_code :=
  first [ s2_errnz_lit
        | lazymatch goal with |- s2_fail (Z_to_bv 64 ?V) =>
            first [ is_var V;
                    match goal with H09 : (V = 0 \/ V = 9)%Z |- _ =>
                      destruct H09 as [H09 | H09]; subst V; first [s2_errnz_lit | s2_refute_by_closed_hyp] end
                  | match V with context [Z.b2z ?c] =>

                      repeat match goal with H : context [Z.b2z c] |- _ => revert H end;
                      destruct c; cbn [Z.b2z]; intros; first [s2_errnz | s2_refute_by_closed_hyp] end ]
          end
        | fail 100 "s2_err_code: cannot bound the error code" ].

Ltac s2_err_exit9 KX := apply KX; [ | s2_err_code ].
Ltac s2_fail09 H := s2_err_code.

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

Lemma tape_img_call : forall E tws sbs W (m m' : mem), tape_img E tws sbs m -> munch W m m' -> wmono psegs m m' ->
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
