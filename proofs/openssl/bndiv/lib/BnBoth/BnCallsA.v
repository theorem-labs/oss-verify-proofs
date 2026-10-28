(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import AW_add_words AW_sub_words.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2253528 => 1
  | 2253532 => 1
  | 2253536 => 1
  | 2253552 => 1
  | 2253556 => 1
  | 2253560 => 1
  | 2253564 => 1
  | 2253580 => 1
  | 2253588 => 2
  | 2253592 => 2
  | 2253600 => 2
  | 2253604 => 2
  | 2253628 => 2
  | 2253632 => 2
  | 2253664 => 2
  | 2253668 => 2
  | 2253712 => 2
  | 2253768 => 2
  | 2253772 => 2
  | 2253816 => 2
  | 2253872 => 2
  | 2253876 => 2
  | 2253920 => 2
  | 2253976 => 2
  | 2253980 => 2
  | 2253984 => 2
  | 2253992 => 2
  | 2254056 => 1
  | 2254060 => 1
  | 2254064 => 1
  | 2254092 => 1
  | 2254100 => 2
  | 2254104 => 2
  | 2254112 => 2
  | 2254116 => 2
  | 2254140 => 2
  | 2254144 => 2
  | 2254176 => 2
  | 2254180 => 2
  | 2254184 => 2
  | 2254192 => 2
  | 2254528 => 1
  | 2254532 => 1
  | 2254536 => 1
  | 2254552 => 1
  | 2254556 => 1
  | 2254560 => 1
  | 2254564 => 1
  | 2254580 => 1
  | 2254588 => 2
  | 2254592 => 2
  | 2254600 => 2
  | 2254604 => 2
  | 2254612 => 2
  | 2254616 => 2
  | 2254668 => 2
  | 2254692 => 2
  | 2254696 => 2
  | 2254776 => 2
  | 2254800 => 2
  | 2254804 => 2
  | 2254884 => 2
  | 2254908 => 2
  | 2254912 => 2
  | 2254992 => 2
  | 2254996 => 2
  | 2255000 => 2
  | 2255008 => 2
  | 2255072 => 1
  | 2255076 => 1
  | 2255080 => 1
  | 2255108 => 1
  | 2255116 => 2
  | 2255120 => 2
  | 2255128 => 2
  | 2255132 => 2
  | 2255140 => 2
  | 2255144 => 2
  | 2255196 => 2
  | 2255200 => 2
  | 2255204 => 2
  | 2255212 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Section Calls.
  Variable POST : machine_state -> Prop.
  Variables (wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo SPz RET : Z).
  Hypothesis ESP : bv_unsigned wsp = SPz.
  Hypothesis ERET : ret_pc (Z_to_bv 64 RET) = Z_to_bv 64 RET.
  Hypothesis STK : stk bsegs m lo SPz.
  Hypothesis MI0 : mem_inv bsegs m.
  Hypothesis SHBC : shb_cells bsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m.

  Notation ENTRY pc := (MS (mkR (Z_to_bv 64 RET) wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).
  Notation AFTER m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 :=
    (MS (mkR (Z_to_bv 64 RET) wsp gp tp u0 u1 u2 s0 s1 v0 v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 RET) fc None m2 (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma call_add_wordsA : forall (a b : list Z) (RP AP BP : Z),
    limbs a -> limbs b -> length b = length a -> (Z.of_nat (length a) < 2^31)%Z ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP -> bv_unsigned w3 = Z.of_nat (length a) ->
    limbs_at bsegs m AP a -> limbs_at bsegs m BP b -> wr_at bsegs m RP (8 * Z.of_nat (length a)) ->
    alias_ok RP AP (Z.of_nat (length a)) -> alias_ok RP BP (Z.of_nat (length a)) ->
    (lo <= SPz - 112)%Z ->
    (RP + 8 * Z.of_nat (length a) <= SPz - 112 \/ SPz <= RP)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - 112 \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length a) <= SPz - 112 \/ SPz <= BP)%Z ->
    acc bsegs m RP (8 * Z.of_nat (length a)) -> acc bsegs m AP (8 * Z.of_nat (length a)) -> acc bsegs m BP (8 * Z.of_nat (length a)) ->
    aptrs3 RP AP BP (Z.of_nat (length a)) lo ->
    ub_ptr_ok (Z.of_nat (length a)) RP -> ub_ptr_ok (Z.of_nat (length a)) AP -> ub_ptr_ok (Z.of_nat (length a)) BP ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * Z.of_nat (length a)); (SPz - 112, SPz)]%Z m m2 -> wmono bsegs m m2 -> mem_inv bsegs m2 ->
       limbs_at bsegs m2 RP (fst (add_words a b)) -> stk bsegs m2 lo SPz ->
       evt bsegs POST (AFTER m2 u0 u1 u2 (Z_to_bv 64 (snd (add_words a b))) v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt bsegs POST (ENTRY 0x22626c).
  Proof using ESP ERET STK MI0 SHBC.
    intros a b RP AP BP LA LB LEN N31 E0 E1 E2 E3 RA RB WR ALA ALB LO SEPR SEPA SEPB ACR ACA ACB APT UBR UBA UBB K.
    subst RP AP BP SPz.
    eapply evt_cut; [ eapply bn_add_words_aspec with (a := a) (b := b) (lo := lo); eassumption | ].
    intros ms' PO. unfold aw_apost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma call_sub_wordsA : forall (a b : list Z) (RP AP BP : Z),
    limbs a -> limbs b -> length b = length a -> (Z.of_nat (length a) < 2^31)%Z ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP -> bv_unsigned w3 = Z.of_nat (length a) ->
    limbs_at bsegs m AP a -> limbs_at bsegs m BP b -> wr_at bsegs m RP (8 * Z.of_nat (length a)) ->
    alias_ok RP AP (Z.of_nat (length a)) -> alias_ok RP BP (Z.of_nat (length a)) ->
    (lo <= SPz - 112)%Z ->
    (RP + 8 * Z.of_nat (length a) <= SPz - 112 \/ SPz <= RP)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - 112 \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length a) <= SPz - 112 \/ SPz <= BP)%Z ->
    acc bsegs m RP (8 * Z.of_nat (length a)) -> acc bsegs m AP (8 * Z.of_nat (length a)) -> acc bsegs m BP (8 * Z.of_nat (length a)) ->
    aptrs3 RP AP BP (Z.of_nat (length a)) lo ->
    ub_ptr_ok (Z.of_nat (length a)) RP -> ub_ptr_ok (Z.of_nat (length a)) AP -> ub_ptr_ok (Z.of_nat (length a)) BP ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * Z.of_nat (length a)); (SPz - 112, SPz)]%Z m m2 -> wmono bsegs m m2 -> mem_inv bsegs m2 ->
       limbs_at bsegs m2 RP (fst (sub_words a b)) -> stk bsegs m2 lo SPz ->
       evt bsegs POST (AFTER m2 u0 u1 u2 (Z_to_bv 64 (snd (sub_words a b))) v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt bsegs POST (ENTRY 0x226654).
  Proof using ESP ERET STK MI0 SHBC.
    intros a b RP AP BP LA LB LEN N31 E0 E1 E2 E3 RA RB WR ALA ALB LO SEPR SEPA SEPB ACR ACA ACB APT UBR UBA UBB K.
    subst RP AP BP SPz.
    eapply evt_cut; [ eapply bn_sub_words_aspec with (a := a) (b := b) (lo := lo); eassumption | ].
    intros ms' PO. unfold sw_apost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.
End Calls.
