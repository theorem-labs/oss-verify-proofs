(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr. 
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import AW_add_words AW_sub_words.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2273656 => 1
  | 2273660 => 1
  | 2273664 => 1
  | 2273680 => 1
  | 2273684 => 1
  | 2273688 => 1
  | 2273692 => 1
  | 2273708 => 1
  | 2273716 => 2
  | 2273720 => 2
  | 2273728 => 2
  | 2273732 => 2
  | 2273756 => 2
  | 2273760 => 2
  | 2273792 => 2
  | 2273796 => 2
  | 2273840 => 2
  | 2273896 => 2
  | 2273900 => 2
  | 2273944 => 2
  | 2274000 => 2
  | 2274004 => 2
  | 2274048 => 2
  | 2274104 => 2
  | 2274108 => 2
  | 2274112 => 2
  | 2274120 => 2
  | 2274184 => 1
  | 2274188 => 1
  | 2274192 => 1
  | 2274220 => 1
  | 2274228 => 2
  | 2274232 => 2
  | 2274240 => 2
  | 2274244 => 2
  | 2274268 => 2
  | 2274272 => 2
  | 2274304 => 2
  | 2274308 => 2
  | 2274312 => 2
  | 2274320 => 2
  | 2274656 => 1
  | 2274660 => 1
  | 2274664 => 1
  | 2274680 => 1
  | 2274684 => 1
  | 2274688 => 1
  | 2274692 => 1
  | 2274708 => 1
  | 2274716 => 2
  | 2274720 => 2
  | 2274728 => 2
  | 2274732 => 2
  | 2274740 => 2
  | 2274744 => 2
  | 2274796 => 2
  | 2274820 => 2
  | 2274824 => 2
  | 2274904 => 2
  | 2274928 => 2
  | 2274932 => 2
  | 2275012 => 2
  | 2275036 => 2
  | 2275040 => 2
  | 2275120 => 2
  | 2275124 => 2
  | 2275128 => 2
  | 2275136 => 2
  | 2275200 => 1
  | 2275204 => 1
  | 2275208 => 1
  | 2275236 => 1
  | 2275244 => 2
  | 2275248 => 2
  | 2275256 => 2
  | 2275260 => 2
  | 2275268 => 2
  | 2275272 => 2
  | 2275324 => 2
  | 2275328 => 2
  | 2275332 => 2
  | 2275340 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Section Calls.
  Variable POST : machine_state -> Prop.
  Variables (wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo SPz RET : Z).
  Hypothesis ESP : bv_unsigned wsp = SPz.
  Hypothesis ERET : ret_pc (Z_to_bv 64 RET) = Z_to_bv 64 RET.
  Hypothesis STK : stk bgbsegs m lo SPz.
  Hypothesis MI0 : mem_inv bgbsegs m.
  Hypothesis SHBC : shb_cells bgbsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m.

  Notation ENTRY pc := (MS (mkR (Z_to_bv 64 RET) wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 pc) fc None m (seg_rom bgbsegs)).
  Notation AFTER m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 :=
    (MS (mkR (Z_to_bv 64 RET) wsp gp tp u0 u1 u2 s0 s1 v0 v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 RET) fc None m2 (seg_rom bgbsegs)).

  Lemma call_add_wordsA : forall (a b : list Z) (RP AP BP : Z),
    limbs a -> limbs b -> length b = length a -> (Z.of_nat (length a) < 2^31)%Z ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP -> bv_unsigned w3 = Z.of_nat (length a) ->
    limbs_at bgbsegs m AP a -> limbs_at bgbsegs m BP b -> wr_at bgbsegs m RP (8 * Z.of_nat (length a)) ->
    alias_ok RP AP (Z.of_nat (length a)) -> alias_ok RP BP (Z.of_nat (length a)) ->
    (lo <= SPz - 112)%Z ->
    (RP + 8 * Z.of_nat (length a) <= SPz - 112 \/ SPz <= RP)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - 112 \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length a) <= SPz - 112 \/ SPz <= BP)%Z ->
    acc bgbsegs m RP (8 * Z.of_nat (length a)) -> acc bgbsegs m AP (8 * Z.of_nat (length a)) -> acc bgbsegs m BP (8 * Z.of_nat (length a)) ->
    aptrs3 RP AP BP (Z.of_nat (length a)) lo ->
    ub_ptr_ok (Z.of_nat (length a)) RP -> ub_ptr_ok (Z.of_nat (length a)) AP -> ub_ptr_ok (Z.of_nat (length a)) BP ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * Z.of_nat (length a)); (SPz - 112, SPz)]%Z m m2 -> wmono bgbsegs m m2 -> mem_inv bgbsegs m2 ->
       limbs_at bgbsegs m2 RP (fst (add_words a b)) -> stk bgbsegs m2 lo SPz ->
       evt bgbsegs POST (AFTER m2 u0 u1 u2 (Z_to_bv 64 (snd (add_words a b))) v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt bgbsegs POST (ENTRY 0x22b10c).
  Proof using ESP ERET STK MI0 SHBC.
    intros a b RP AP BP LA LB LEN N31 E0 E1 E2 E3 RA RB WR ALA ALB LO SEPR SEPA SEPB ACR ACA ACB APT UBR UBA UBB K.
    subst RP AP BP SPz.
    eapply evt_cut; [ eapply bn_add_words_aspec with (a := a) (b := b) (lo := lo); eassumption | ].
    intros ms' PO. unfold aw_apost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  Lemma call_sub_wordsA : forall (a b : list Z) (RP AP BP : Z),
    limbs a -> limbs b -> length b = length a -> (Z.of_nat (length a) < 2^31)%Z ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP -> bv_unsigned w3 = Z.of_nat (length a) ->
    limbs_at bgbsegs m AP a -> limbs_at bgbsegs m BP b -> wr_at bgbsegs m RP (8 * Z.of_nat (length a)) ->
    alias_ok RP AP (Z.of_nat (length a)) -> alias_ok RP BP (Z.of_nat (length a)) ->
    (lo <= SPz - 112)%Z ->
    (RP + 8 * Z.of_nat (length a) <= SPz - 112 \/ SPz <= RP)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - 112 \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length a) <= SPz - 112 \/ SPz <= BP)%Z ->
    acc bgbsegs m RP (8 * Z.of_nat (length a)) -> acc bgbsegs m AP (8 * Z.of_nat (length a)) -> acc bgbsegs m BP (8 * Z.of_nat (length a)) ->
    aptrs3 RP AP BP (Z.of_nat (length a)) lo ->
    ub_ptr_ok (Z.of_nat (length a)) RP -> ub_ptr_ok (Z.of_nat (length a)) AP -> ub_ptr_ok (Z.of_nat (length a)) BP ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * Z.of_nat (length a)); (SPz - 112, SPz)]%Z m m2 -> wmono bgbsegs m m2 -> mem_inv bgbsegs m2 ->
       limbs_at bgbsegs m2 RP (fst (sub_words a b)) -> stk bgbsegs m2 lo SPz ->
       evt bgbsegs POST (AFTER m2 u0 u1 u2 (Z_to_bv 64 (snd (sub_words a b))) v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt bgbsegs POST (ENTRY 0x22b4f4).
  Proof using ESP ERET STK MI0 SHBC.
    intros a b RP AP BP LA LB LEN N31 E0 E1 E2 E3 RA RB WR ALA ALB LO SEPR SEPA SEPB ACR ACA ACB APT UBR UBA UBB K.
    subst RP AP BP SPz.
    eapply evt_cut; [ eapply bn_sub_words_aspec with (a := a) (b := b) (lo := lo); eassumption | ].
    intros ms' PO. unfold sw_apost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.
End Calls.
