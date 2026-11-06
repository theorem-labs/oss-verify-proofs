(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr. 
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop BnCmp.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require W_mul_normal.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import UbKit.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop AsLeaf.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import AW_mul_words AW_mul_add_words.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2265248 => 1
  | 2265252 => 1
  | 2265256 => 2
  | 2265260 => 1
  | 2265264 => 1
  | 2265268 => 1
  | 2265272 => 1
  | 2265276 => 2
  | 2265284 => 2
  | 2265288 => 1
  | 2265292 => 2
  | 2265344 => 2
  | 2265348 => 1
  | 2265352 => 2
  | 2265528 => 1
  | 2265532 => 2
  | 2265540 => 1
  | 2265544 => 2
  | 2265596 => 1
  | 2265600 => 2
  | 2265640 => 1
  | 2265644 => 2
  | 2265648 => 1
  | 2265652 => 2
  | 2265700 => 1
  | 2265704 => 2
  | 2265744 => 1
  | 2265748 => 2
  | 2265752 => 1
  | 2265756 => 2
  | 2265804 => 1
  | 2265808 => 2
  | 2265848 => 1
  | 2265852 => 2
  | 2265856 => 1
  | 2265860 => 2
  | 2265904 => 1
  | 2265908 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Definition bn_mul_normal_aentry := 0x229030%Z.

Notation vl_post := W_mul_normal.vl_post.
Notation mn_model := W_mul_normal.mn_model.
Notation mul_normal_mn := W_mul_normal.mul_normal_mn.
Notation skipn_nth_error_cons := W_mul_normal.skipn_nth_error_cons.
Notation lts_words_small := W_mul_normal.lts_words_small.

Section Core.
  Variables (sp a0 : word) (m : word -> option byte) (lo : Z) (A B : list Z) (PA PB : Z).
  Notation rp := (bv_unsigned a0).
  Notation SP := (bv_unsigned sp).
  Notation NA := (Z.of_nat (length A)).
  Notation NB := (Z.of_nat (length B)).
  Notation NN := (Z.of_nat (length A) + Z.of_nat (length B))%Z.
  Notation Wfin := [(bv_unsigned a0, bv_unsigned a0 + 8 * (Z.of_nat (length A) + Z.of_nat (length B))); (bv_unsigned sp - 240, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs A.
  Hypothesis LB : limbs B.
  Hypothesis DRA : (rp + 8 * NN <= PA \/ PA + 8 * NA <= rp)%Z.
  Hypothesis DRB : (rp + 8 * NN <= PB \/ PB + 8 * NB <= rp)%Z.
  Hypothesis SEPR : (rp + 8 * NN <= SP - 240 \/ SP <= rp)%Z.
  Hypothesis SEPA : (PA + 8 * NA <= SP - 240 \/ SP <= PA)%Z.
  Hypothesis SEPB : (PB + 8 * NB <= SP - 240 \/ SP <= PB)%Z.

  Definition MNB (cells : list cell) (m1 : word -> option byte) : Prop :=
    limbs_at bgbsegs m1 PA A /\ limbs_at bgbsegs m1 PB B /\ wr_at bgbsegs m1 rp (8 * NN) /\
    rw_cells bgbsegs m1 (SP + -112) cells /\ stk bgbsegs m1 lo (SP + -112) /\
    mem_inv bgbsegs m1 /\ munch Wfin m m1 /\ wmono bgbsegs m m1.
  Definition MNI (cells : list cell) (m1 : word -> option byte) (R : list Z) : Prop :=
    limbs R /\ limbs_at bgbsegs m1 rp R /\ MNB cells m1.

  Lemma mn_after_call : forall cells m1 m2 P (i : nat) seg fsz,
    Z.of_nat (cells_size cells) = 112%Z ->
    MNB cells m1 -> limbs P -> limbs_at bgbsegs m1 rp P -> length P = i -> (Z.of_nat i + 1 <= NB)%Z ->
    (0 <= fsz <= 128)%Z ->
    munch [(rp + 8 * Z.of_nat i, rp + 8 * Z.of_nat i + 8 * NA); (SP + -112 - fsz, SP + -112)]%Z m1 m2 ->
    wmono bgbsegs m1 m2 -> mem_inv bgbsegs m2 -> limbs_at bgbsegs m2 (rp + 8 * Z.of_nat i) seg -> stk bgbsegs m2 lo (SP + -112) ->
    limbs seg -> length seg = length A ->
    MNI cells m2 (P ++ seg).
  Proof using DRA DRB SEPR SEPA SEPB.
    intros cells m1 m2 P i seg fsz CS (HA & HB & HW & FR & ST & MI & MU & WM) LP HP EP Hi Hf MUc WMc MIc HS STc LS ES.
    subst i.
    pose proof (limbs_at_bound _ _ _ _ HA) as BA. pose proof (limbs_at_bound _ _ _ _ HB) as BB.
    change (2 ^ 64)%Z with 18446744073709551616%Z in *.
    split. { apply limbs_app; [exact LP | exact LS]. }
    split. { apply limbs_at_app. split; [|exact HS].
             eapply limbs_at_transport; [exact HP | exact MUc | cbn [disjoint_from]; clear - SEPR Hi Hf; lia]. }
    split. { eapply limbs_at_transport; [exact HA | exact MUc | cbn [disjoint_from]; clear - DRA SEPA Hi Hf; lia]. }
    split. { eapply limbs_at_transport; [exact HB | exact MUc | cbn [disjoint_from]; clear - DRB SEPB Hi Hf; lia]. }
    split. { eapply wr_at_transport; [exact HW | exact WMc]. }
    split. { eapply rw_cells_transport; [exact FR | exact MUc | exact WMc | cbn [disjoint_from]; rewrite CS; clear - SEPR Hi Hf; lia]. }
    split; [exact STc|]. split; [exact MIc|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc].
             unfold sub_fp. cbn [outside]. intros x Hx. clear - Hx Hi Hf. lia. }
    eapply wmono_trans; [exact WM | exact WMc].
  Qed.

  Lemma mn_carry : forall cells m2 Q (i : nat) c,
    Z.of_nat (cells_size cells) = 112%Z ->
    MNI cells m2 Q -> length Q = (length A + i)%nat -> (Z.of_nat i + 1 <= NB)%Z -> (0 <= c < 18446744073709551616)%Z ->
    store_ok bgbsegs m2 (wa (rp + 8 * (NA + Z.of_nat i))) 8 = true /\
    MNI cells (write_to_mem m2 (wa (rp + 8 * (NA + Z.of_nat i))) (le8 (Z_to_bv 64 c))) (Q ++ [c]).
  Proof using DRA DRB SEPR SEPA SEPB.
    intros cells m2 Q i c CS (LQ & HQ & HA & HB & HW & FR & ST & MI & MU & WM) EQ Hi Hc.
    pose proof (limbs_at_bound _ _ _ _ HA) as BA. pose proof (limbs_at_bound _ _ _ _ HB) as BB.
    destruct HW as (W0 & W1 & HW'). pose proof (conj W0 (conj W1 HW')) as HW.
    change (2 ^ 64)%Z with 18446744073709551616%Z in *.
    assert (L8 : length (le8 (Z_to_bv 64 c)) = 8%nat) by apply length_le8.
    assert (SOK : store_ok bgbsegs m2 (wa (rp + 8 * (NA + Z.of_nat i))) 8 = true).
    { apply (wr_at_store_ok bgbsegs m2 rp (8 * NN)); [exact HW | lia | lia]. }
    split; [exact SOK|].
    split. { apply limbs_app; [exact LQ|]. constructor; [unfold limb, BW; exact Hc | constructor]. }
    split.
    { replace (rp + 8 * (NA + Z.of_nat i))%Z with (rp + 8 * Z.of_nat (length Q))%Z by (rewrite EQ; lia).
      apply limbs_at_snoc_write; [exact HQ | rewrite EQ; lia]. }
    split. { apply limbs_at_write_other; [ exact HA | lia | rewrite L8; lia | rewrite L8; clear - DRA Hi; lia ]. }
    split. { apply limbs_at_write_other; [ exact HB | lia | rewrite L8; lia | rewrite L8; clear - DRB Hi; lia ]. }
    split. { apply wr_at_write. exact HW. }
    split. { apply rw_cells_frame; [ exact FR | lia | rewrite L8; lia | rewrite L8, CS; clear - SEPR Hi; lia ]. }
    split. { apply stk_write; [exact ST | lia | rewrite L8; lia]. }
    split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
    split. { apply munch_write; [ exact MU | lia | rewrite L8; lia | rewrite L8; cbn [inside]; left; clear - Hi; lia ]. }
    apply wmono_write. exact WM.
  Qed.
End Core.

Section Mach.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (A B : list Z) (wPA wPB wNA : word).
  Notation rp := (bv_unsigned a0).
  Notation SP := (bv_unsigned sp).
  Notation PA := (bv_unsigned wPA).
  Notation PB := (bv_unsigned wPB).
  Notation NA := (Z.of_nat (length A)).
  Notation NB := (Z.of_nat (length B)).
  Notation NN := (Z.of_nat (length A) + Z.of_nat (length B))%Z.
  Notation Wfin := [(bv_unsigned a0, bv_unsigned a0 + 8 * (Z.of_nat (length A) + Z.of_nat (length B))); (bv_unsigned sp - 240, bv_unsigned sp)]%Z.
  Hypothesis LA : limbs A.
  Hypothesis LB : limbs B.
  Hypothesis N31 : (NN < 2147483648)%Z.
  Hypothesis ENA : bv_unsigned wNA = NA.
  Hypothesis DRA : (rp + 8 * NN <= PA \/ PA + 8 * NA <= rp)%Z.
  Hypothesis DRB : (rp + 8 * NN <= PB \/ PB + 8 * NB <= rp)%Z.
  Hypothesis LO : (lo <= SP - 240)%Z.
  Hypothesis SEPR : (rp + 8 * NN <= SP - 240 \/ SP <= rp)%Z.
  Hypothesis SEPA : (PA + 8 * NA <= SP - 240 \/ SP <= PA)%Z.
  Hypothesis SEPB : (PB + 8 * NB <= SP - 240 \/ SP <= PB)%Z.

  Hypothesis SHBC : shb_cells bgbsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m.
  Hypothesis ACR : acc bgbsegs m rp (8 * NN).
  Hypothesis ACA : acc bgbsegs m PA (8 * NA).
  Hypothesis ACB : acc bgbsegs m PB (8 * NB).
  Hypothesis APT : aptrs3 rp PA PB NN lo.
  Hypothesis OFFI : (rp + 8 * NN <= 65536 \/ 12554240 <= rp)%Z.

  Hypothesis UBR : ub_ptr_ok 1 (bv_unsigned a0).
  Hypothesis UBA : ub_ptr_ok 1 (bv_unsigned wPA).
  Hypothesis UBB : ub_ptr_ok 1 (bv_unsigned wPB).
  Variable RES : list Z.

  Notation POST := (vl_post bgbsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) NN 240%Z RES lo m).
  Notation FCELLS jb := [CB 8 jb; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation KMNB jb := (MNB sp a0 m lo A B (bv_unsigned wPA) (bv_unsigned wPB) (FCELLS jb)).
  Notation KMNI jb := (MNI sp a0 m lo A B (bv_unsigned wPA) (bv_unsigned wPB) (FCELLS jb)).
  Notation AFTER := (mn_after_call sp a0 m lo A B (bv_unsigned wPA) (bv_unsigned wPB) DRA DRB SEPR SEPA SEPB).
  Notation CARRY := (mn_carry sp a0 m lo A B (bv_unsigned wPA) (bv_unsigned wPB) DRA DRB SEPR SEPA SEPB).

  Notation ST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 sp wPA x10 x11 x12 x13 x14 x15 x16 x17 a0 x19 wNA x21 x22 x23 x24 x25 x26 wPB
             x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgbsegs)).

  Lemma OFFfin : offshW Wfin.
  Proof using APT LO. destruct APT as (_ & _ & _ & A4' & A5'). cbn [offshW]. unfold SHHI in *. split; [exact A4'|]. split; [right; clear - A5' LO; lia | exact I]. Qed.
  Lemma shb_at : forall m1, munch Wfin m m1 -> shb_cells bgbsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m1.
  Proof using SHBC APT LO OFFI.
    intros m1 MU. eapply shb_cells_munch; [exact SHBC | exact MU | | ];
      unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address; cbn [disjoint_from];
      destruct APT as (_ & _ & _ & _ & A5'); unfold SHHI in A5'; clear - A5' LO OFFI; lia.
  Qed.

  Lemma mn_ret : forall jb m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31,
    KMNI jb m1 RES ->
    evt bgbsegs POST (ST 0x229128 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31).
  Proof.
    intros until x31. intros (LR & HR & HA & HB & HW & FR & ST & MI & MU & WM).
    do 15 zstep.
    release_frame FR ST (bv_unsigned sp).
    finish.
  Qed.

  Lemma ESPc : (112 <= SP)%Z -> bv_unsigned (Z_to_bv 64 (SP + -112)) = (SP + -112)%Z.
  Proof.
    intros H. apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    pose proof (zr_word sp) as R. unfold inr64 in R. change (2 ^ 64)%Z with 18446744073709551616%Z in R. lia.
  Qed.

  Lemma callee_asan : forall cells m1 (i : nat), MNB sp a0 m lo A B (bv_unsigned wPA) (bv_unsigned wPB) cells m1 -> (Z.of_nat i <= NB)%Z ->
    shb_cells bgbsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m1 /\
    acc bgbsegs m1 (rp + 8 * Z.of_nat i) (8 * NA) /\ acc bgbsegs m1 PA (8 * NA) /\
    aptrs3 (rp + 8 * Z.of_nat i) PA (rp + 8 * Z.of_nat i) NA lo /\ aptrs3 (rp + 8 * Z.of_nat i) PA PA NA lo.
  Proof using SHBC ACR ACA APT LO OFFI.
    intros cells m1 i (HA & HB & HW & FR & ST & MI & MU & WM) Hi.
    split; [exact (shb_at m1 MU)|].
    split. { apply (acc_tr bgbsegs _ m m1 rp (8 * NN) (8 * Z.of_nat i) (8 * NA) ACR MU OFFfin); [ | clear; lia | clear - Hi; lia].
             intros Hp. pose proof (wr_at_b47 bgbsegs m1 rp (8 * NN) HW MI ltac:(clear - Hp Hi; lia)) as H. clear - H Hi. lia. }
    split. { pose proof (acc_tr bgbsegs _ m m1 PA (8 * NA) 0 (8 * NA) ACA MU OFFfin) as X. rewrite Z.add_0_r in X. apply X; [ | clear; lia | clear; lia].
             intros Hp. pose proof (limbs_at_b47 bgbsegs m1 PA A HA MI ltac:(clear - Hp; lia)) as H. clear - H. lia. }
    destruct APT as (A1 & A2' & A3' & A4' & A5'). unfold aptrs3.
    assert (E8 : ((rp + 8 * Z.of_nat i) mod 8 = 0)%Z) by (clear - A1; Z.div_mod_to_equations; lia).
    split; (split; [exact E8|]; split; [exact A2'|]; split; [first [exact E8 | exact A2']|]; split; [clear - A4' Hi; lia | exact A5']).
  Qed.

  Lemma mn_call : forall (ij : nat) R jb m1 w (retaddr : Z) (wr0 : word)
      x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    (ij < length B)%nat -> KMNI jb m1 R -> length R = (length A + ij)%nat -> nth_error B ij = Some w ->
    wr0 = Z_to_bv 64 (rp + 8 * Z.of_nat ij) -> ret_pc (Z_to_bv 64 retaddr) = Z_to_bv 64 retaddr ->
    (forall m2 seg c u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       mul_add_words (skipn ij R) A w = (seg, c) -> length (firstn ij R ++ seg) = (length A + ij)%nat ->
       (0 <= c < 18446744073709551616)%Z ->
       KMNI jb m2 (firstn ij R ++ seg) ->
       evt bgbsegs POST
         (MS (mkR (Z_to_bv 64 retaddr) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp u0 u1 u2 x8 x9 (Z_to_bv 64 c) v1 v2 v3 v4 v5 v6 v7
                  x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 u3 u4 u5 u6)
             F (Z_to_bv 64 retaddr) fc None m2 (seg_rom bgbsegs))) ->
    evt bgbsegs POST
      (MS (mkR (Z_to_bv 64 retaddr) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 x8 x9 wr0 wPA wNA (Z_to_bv 64 w) x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x22a24c) fc None m1 (seg_rom bgbsegs)).
  Proof.
    intros until x31. intros Hi I LR Ew Ewr Eret K. subst wr0.
    pose proof I as (LRl & HR & IB). pose proof IB as (HA & HB & HW & FR & ST & MI & MU & WM).
    pose proof (proj1 ST) as LO0.
    assert (SP112 : (112 <= SP)%Z) by (clear - LO LO0; lia).
    pose proof (ESPc SP112) as ESP.
    assert (E0 : bv_unsigned (Z_to_bv 64 (rp + 8 * Z.of_nat ij)) = (rp + 8 * Z.of_nat ij)%Z).
    { apply inr64_unsigned_lit. unfold inr64. destruct HW as (W0 & W1 & _). clear - W0 W1 Hi. lia. }
    assert (LS : length (skipn ij R) = length A) by (rewrite length_skipn; clear - LR; lia).
    pose proof (limbs_nth_error_lit B ij w LB Ew) as Rw.
    assert (Ew64 : bv_unsigned (Z_to_bv 64 w) = w) by (apply inr64_unsigned_lit; unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; exact Rw).
    destruct (callee_asan (FCELLS jb) m1 ij IB ltac:(clear - Hi; lia)) as (SH1 & ACR1 & ACA1 & APT1 & _).
    eapply evt_cut.
    { eapply bn_mul_add_words_aspec with (a := A) (r := skipn ij R) (lo := lo) (m := m1).
      - exact LA.
      - apply limbs_skipn. exact LRl.
      - exact LS.
      - clear - N31. lia.
      - exact ENA.
      - exact HA.
      - rewrite E0. rewrite <- (firstn_skipn ij R) in HR. apply limbs_at_app in HR. destruct HR as [_ HR2].
        rewrite length_firstn in HR2. replace (Nat.min ij (length R)) with ij in HR2 by (clear - LR; lia). exact HR2.
      - rewrite E0. apply (wr_at_sub bgbsegs m1 rp (8 * NN) (8 * Z.of_nat ij) (8 * NA) HW); clear - Hi; lia.
      - rewrite E0. unfold alias_ok. clear - DRA Hi. lia.
      - rewrite ESP. exact ST.
      - rewrite ESP. clear - LO. lia.
      - rewrite E0, ESP. clear - SEPR Hi. lia.
      - rewrite ESP. clear - SEPA. lia.
      - exact MI.
      - exact SH1.
      - rewrite E0. exact ACR1.
      - exact ACA1.
      - rewrite E0. exact APT1.
      - rewrite E0. intros _. destruct (UBR ltac:(lia)) as (NZ & AL). destruct HW as (W0 & _).
        split; [clear - NZ; lia | clear - AL; Z.div_mod_to_equations; lia].
      - intros _. apply UBA. lia. }
    intros ms' PO. unfold maw_apost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HS & STc).
    subst ms'. rewrite E0, ESP, Ew64 in *. rewrite Eret.
    pose proof (mul_add_words_spec (skipn ij R) A w (limbs_skipn _ _ LRl) LA LS Rw) as MSP.
    destruct (mul_add_words (skipn ij R) A w) as [seg c] eqn:EMA. cbn [fst snd] in *.
    destruct MSP as (Lseg & Eseg & Lc & _). unfold limb, BW in Lc.
    assert (HP1 : limbs_at bgbsegs m1 rp (firstn ij R)).
    { rewrite <- (firstn_skipn ij R) in HR. apply limbs_at_app in HR. exact (proj1 HR). }
    assert (LP1 : length (firstn ij R) = ij) by (rewrite length_firstn; clear - LR; lia).
    pose proof (AFTER (FCELLS jb) m1 m2 (firstn ij R) ij seg 128%Z eq_refl IB
                  (limbs_firstn _ _ LRl) HP1 LP1 ltac:(clear - Hi; lia) ltac:(lia) MUc WMc MIc HS STc Lseg Eseg) as I2.
    eapply K; [reflexivity | rewrite !length_app, LP1, Eseg; clear; lia | exact Lc | exact I2].
  Qed.

  Lemma shB_rd : forall cells m1 (k : nat) ad, MNB sp a0 m lo A B (bv_unsigned wPA) (bv_unsigned wPB) cells m1 -> (k < length B)%nat ->
    ad = wa (shad (PB + 8 * Z.of_nat k)) -> ov_read_bytes bgbsegs m1 ad 1 = Some [z8].
  Proof using ACB APT LO.
    intros cells m1 k ad (HA & HB & HW & FR & ST & MI & MU & WM) Hk ->.
    destruct APT as (_ & _ & A3' & _).
    apply (acc_rd_limb bgbsegs _ m m1 PB NB 0 (Z.of_nat k) _ ACB MU OFFfin A3' (limbs_at_b47 bgbsegs m1 PB B HB MI ltac:(clear - Hk; lia)));
      [reflexivity | clear; lia | clear; lia | clear - Hk; lia | rewrite Z.add_0_r; reflexivity].
  Qed.
  Lemma shR_rd : forall cells m1 (k : nat) ad, MNB sp a0 m lo A B (bv_unsigned wPA) (bv_unsigned wPB) cells m1 -> (Z.of_nat k < NN)%Z ->
    ad = wa (shad (rp + 8 * Z.of_nat k)) -> ov_read_bytes bgbsegs m1 ad 1 = Some [z8].
  Proof using ACR APT LO.
    intros cells m1 k ad (HA & HB & HW & FR & ST & MI & MU & WM) Hk ->.
    destruct APT as (A1' & _).
    pose proof (wr_at_b47 bgbsegs m1 rp (8 * NN) HW MI ltac:(clear - Hk; lia)) as BR.
    apply (acc_rd_limb bgbsegs _ m m1 rp NN 0 (Z.of_nat k) _ ACR MU OFFfin A1' BR);
      [reflexivity | clear; lia | clear; lia | clear - Hk; lia | rewrite Z.add_0_r; reflexivity].
  Qed.

  Lemma run_bounds : forall cells m1, MNB sp a0 m lo A B (bv_unsigned wPA) (bv_unsigned wPB) cells m1 -> (1 <= NB)%Z ->
    (0 <= PB /\ PB + 8 * NB <= 140737488355328)%Z /\ (0 <= rp /\ rp + 8 * NN <= 140737488355328)%Z.
  Proof using.
    intros cells m1 (HA & HB & HW & FR & ST & MI & MU & WM) Hn.
    split; [exact (limbs_at_b47 bgbsegs m1 PB B HB MI ltac:(clear - Hn; lia)) | exact (wr_at_b47 bgbsegs m1 rp (8 * NN) HW MI ltac:(clear - Hn; lia))].
  Qed.

  Ltac mn_store SOK0 I2 :=
    lazymatch type of SOK0 with
    | store_ok _ ?m2 ?a0' _ = true =>
        let ad := cur_mem_addr in
        let SOK := fresh "SOK" in
        assert (SOK : store_ok bgbsegs m2 ad 8 = true) by (replace ad with a0' by (unfold wa; f_equal; lia); exact SOK0);
        replace a0' with ad in I2 by (unfold wa; f_equal; lia);
        zstep; clear SOK SOK0;
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => let m' := fresh "m" in gen_mem mm m' end
    end.

  Ltac mn_model_step ER Ew EMA :=
    rewrite (skipn_nth_error_cons B _ _ Ew) in ER; cbn [mul_normal_loop] in ER; rewrite EMA in ER.
  Ltac mn_exit ER I2 :=
    rewrite skipn_all2 in ER by lia; cbn [mul_normal_loop] in ER; rewrite <- ER in I2; eapply mn_ret; exact I2.
  Ltac chkB I k Hk := let IB := fresh "IB" in let RD := fresh "RD" in pose proof I as (_ & _ & IB);
    let ad := cur_mem_addr in
    lazymatch type of IB with MNB _ _ _ _ _ _ _ _ ?cells ?mc =>
       pose proof (shB_rd cells mc k ad IB Hk ltac:(sh_addr)) as RD end; zstep; clear RD IB; chk0.
  Ltac chkR I k Hk := let IB := fresh "IB" in let RD := fresh "RD" in pose proof I as (_ & _ & IB);
    let ad := cur_mem_addr in
    lazymatch type of IB with MNB _ _ _ _ _ _ _ _ ?cells ?mc =>
       pose proof (shR_rd cells mc k ad IB Hk ltac:(sh_addr)) as RD end; zstep; clear RD IB; chk0.

  Lemma mn_loop : forall (K : nat) (i : nat) R jb m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31,
    (length B - i = K)%nat -> (1 <= i < length B)%nat -> KMNI jb m1 R -> length R = (length A + i)%nat ->
    RES = mul_normal_loop A (skipn i B) R i ->
    evt bgbsegs POST (ST 0x2291b4 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (NB - Z.of_nat i + 1)) x21 x22 x23
                       (Z_to_bv 64 SHB) (Z_to_bv 64 (rp + 8 * NA)) (Z_to_bv 64 (8 * (Z.of_nat i - 1))) x28 x29 x30 x31).
  Proof.
    induction K as [K IH] using lt_wf_ind; intros i R jb m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31 HK Hi I LR ER.
    pose proof I as (_ & _ & IB0). pose proof (run_bounds _ _ IB0 ltac:(clear - Hi; lia)) as (BB & BR). clear IB0.
    pose proof (zr_word a0) as Z0. pose proof (zr_word wPB) as ZB. unfold inr64 in Z0, ZB.
    assert (NA0 : (0 <= NA)%Z) by (clear; lia).

    destruct (nth_error B i) as [w0|] eqn:Ew0; [|apply nth_error_None in Ew0; exfalso; clear - Ew0 Hi; lia].
    pose proof I as (_ & _ & _ & HB & _).
    zstep. ub. zstep. ub.
    do 3 zstep. chkB I i (proj2 Hi).
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgbsegs m1 PB B i w0 ad HB Ew0 ltac:(unfold wa; f_equal; clear; lia)) as RD); zstep; clear RD HB.
    do 6 zstep.
    eapply (mn_call i R jb m1 w0); [ clear - Hi; lia | exact I | exact LR | exact Ew0 | f_equal; clear; lia | apply ret_pc_even; [lia | reflexivity] | ].
    intros m2 seg0 c0 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 EMA0 LR0 Rc0 I2.
    mn_model_step ER Ew0 EMA0. clear I EMA0 Ew0 LR.
    ub. do 3 zstep.
    assert (HkR0 : (Z.of_nat (length A + i) < NN)%Z) by (clear - Hi; lia).
    chkR I2 (length A + i)%nat HkR0.
    pose proof (CARRY (FCELLS jb) m2 _ i c0 eq_refl I2 LR0 ltac:(clear - Hi; lia) Rc0) as (SOK0 & I3). clear I2.
    rewrite <- app_assoc in I3.
    assert (LR0' : length (firstn i R ++ seg0 ++ [c0]) = (length A + S i)%nat) by (rewrite app_assoc, length_app, LR0; cbn [length]; clear; lia).
    clear LR0.
    mn_store SOK0 I3.
    zstep.
    zstep. rewrite lts_signed by (clear - Hi N31; lia).
    if_cases K0; zify_cond K0.
    { mn_exit ER I3. }

    destruct (nth_error B (S i)) as [w1|] eqn:Ew1; [|apply nth_error_None in Ew1; exfalso; clear - Ew1 K0 Hi; lia].
    assert (HkB1 : (S i < length B)%nat) by (apply nth_error_Some; rewrite Ew1; discriminate).
    pose proof I3 as (_ & _ & _ & HB & _).
    zstep. setreg 23%Z (Z_to_bv 64 (rp + 8 * (Z.of_nat i - 1))) ltac:(f_equal; clear; lia).
    ub.
    do 3 zstep. chkB I3 (S i) HkB1.
    (let ad := cur_mem_addr in lazymatch type of HB with limbs_at _ ?mc _ _ =>
       pose proof (limbs_at_read_nth bgbsegs mc PB B (S i) w1 ad HB Ew1 ltac:(unfold wa; f_equal; clear; lia)) as RD end); zstep; clear RD HB.
    do 5 zstep.
    eapply (mn_call (S i) _ jb _ w1); [ exact HkB1 | exact I3 | exact LR0' | exact Ew1 | f_equal; clear; lia | apply ret_pc_even; [lia | reflexivity] | ].
    intros mc1 seg1 c1 p0 p1 p2 q1 q2 q3 q4 q5 q6 q7 p3 p4 p5 p6 EMA1 LR1 Rc1 J1.
    mn_model_step ER Ew1 EMA1. clear I3 EMA1 Ew1 LR0'.
    ub. do 3 zstep.
    assert (HkR1 : (Z.of_nat (length A + S i) < NN)%Z) by (clear - HkB1; lia).
    chkR J1 (length A + S i)%nat HkR1.
    pose proof (CARRY (FCELLS jb) mc1 _ (S i) c1 eq_refl J1 LR1 ltac:(clear - HkB1; lia) Rc1) as (SOK1 & I4). clear J1.
    rewrite <- app_assoc in I4.
    assert (LR1' : length (firstn (S i) _ ++ seg1 ++ [c1]) = (length A + S (S i))%nat) by (rewrite app_assoc, length_app, LR1; cbn [length]; clear; lia).
    clear LR1.
    mn_store SOK1 I4.
    zstep.
    zstep. if_cases K1; zify_cond K1.
    { mn_exit ER I4. }

    destruct (nth_error B (S (S i))) as [w2|] eqn:Ew2; [|apply nth_error_None in Ew2; exfalso; clear - Ew2 K0 K1 Hi; lia].
    assert (HkB2 : (S (S i) < length B)%nat) by (apply nth_error_Some; rewrite Ew2; discriminate).
    pose proof I4 as (_ & _ & _ & HB & _).
    zstep. setreg 23%Z (Z_to_bv 64 (rp + 8 * (Z.of_nat i - 1))) ltac:(f_equal; clear; lia).
    ub.
    do 3 zstep. chkB I4 (S (S i)) HkB2.
    (let ad := cur_mem_addr in lazymatch type of HB with limbs_at _ ?mc _ _ =>
       pose proof (limbs_at_read_nth bgbsegs mc PB B (S (S i)) w2 ad HB Ew2 ltac:(unfold wa; f_equal; clear; lia)) as RD end); zstep; clear RD HB.
    do 5 zstep.
    eapply (mn_call (S (S i)) _ jb _ w2); [ exact HkB2 | exact I4 | exact LR1' | exact Ew2 | f_equal; clear; lia | apply ret_pc_even; [lia | reflexivity] | ].
    intros mc2 seg2 c2 pp0 pp1 pp2 qq1 qq2 qq3 qq4 qq5 qq6 qq7 pp3 pp4 pp5 pp6 EMA2 LR2 Rc2 J2.
    mn_model_step ER Ew2 EMA2. clear I4 EMA2 Ew2 LR1'.
    ub. do 3 zstep.
    assert (HkR2 : (Z.of_nat (length A + S (S i)) < NN)%Z) by (clear - HkB2; lia).
    chkR J2 (length A + S (S i))%nat HkR2.
    pose proof (CARRY (FCELLS jb) mc2 _ (S (S i)) c2 eq_refl J2 LR2 ltac:(clear - HkB2; lia) Rc2) as (SOK2 & I5). clear J2.
    rewrite <- app_assoc in I5.
    assert (LR2' : length (firstn (S (S i)) _ ++ seg2 ++ [c2]) = (length A + S (S (S i)))%nat) by (rewrite app_assoc, length_app, LR2; cbn [length]; clear; lia).
    clear LR2.
    zstep. rewrite bn_swrap32_small by (clear - Hi N31 K0 K1; lia).
    mn_store SOK2 I5.
    zstep. if_cases K2; zify_cond K2.
    { mn_exit ER I5. }

    destruct (nth_error B (S (S (S i)))) as [w3|] eqn:Ew3; [|apply nth_error_None in Ew3; exfalso; clear - Ew3 K0 K1 K2 Hi; lia].
    assert (HkB3 : (S (S (S i)) < length B)%nat) by (apply nth_error_Some; rewrite Ew3; discriminate).
    pose proof I5 as (_ & _ & _ & HB & _).
    zstep. setreg 23%Z (Z_to_bv 64 (rp + 8 * (Z.of_nat i - 1))) ltac:(f_equal; clear; lia).
    ub.
    do 3 zstep. chkB I5 (S (S (S i))) HkB3.
    (let ad := cur_mem_addr in lazymatch type of HB with limbs_at _ ?mc _ _ =>
       pose proof (limbs_at_read_nth bgbsegs mc PB B (S (S (S i))) w3 ad HB Ew3 ltac:(unfold wa; f_equal; clear; lia)) as RD end); zstep; clear RD HB.
    do 4 zstep.
    eapply (mn_call (S (S (S i))) _ jb _ w3); [ exact HkB3 | exact I5 | exact LR2' | exact Ew3 | f_equal; clear; lia | apply ret_pc_even; [lia | reflexivity] | ].
    intros mc3 seg3 c3 ppp0 ppp1 ppp2 qqq1 qqq2 qqq3 qqq4 qqq5 qqq6 qqq7 ppp3 ppp4 ppp5 ppp6 EMA3 LR3 Rc3 J3.
    mn_model_step ER Ew3 EMA3. clear I5 EMA3 Ew3 LR2'.
    ub. do 3 zstep.
    assert (HkR3 : (Z.of_nat (length A + S (S (S i))) < NN)%Z) by (clear - HkB3; lia).
    chkR J3 (length A + S (S (S i)))%nat HkR3.
    pose proof (CARRY (FCELLS jb) mc3 _ (S (S (S i))) c3 eq_refl J3 LR3 ltac:(clear - HkB3; lia) Rc3) as (SOK3 & I6). clear J3.
    rewrite <- app_assoc in I6.
    assert (LR3' : length (firstn (S (S (S i))) _ ++ seg3 ++ [c3]) = (length A + S (S (S (S i))))%nat) by (rewrite app_assoc, length_app, LR3; cbn [length]; clear; lia).
    clear LR3.
    mn_store SOK3 I6.
    do 2 zstep.
    zstep. if_cases K3; zify_cond K3.
    -
      setreg 19%Z (Z_to_bv 64 (NB - Z.of_nat (S (S (S (S i)))) + 1)) ltac:(f_equal; clear; lia).
      setreg 26%Z (Z_to_bv 64 (8 * (Z.of_nat (S (S (S (S i)))) - 1))) ltac:(f_equal; clear; lia).
      eapply (IH (length B - S (S (S (S i))))%nat); [ clear - HK Hi; lia | reflexivity | clear - K3 K2 K1 K0 Hi; lia | exact I6 | exact LR3' | exact ER ].
    - zstep. mn_exit ER I6.
  Qed.

  Lemma mn_first : forall (wNB : word) jb m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x26 x28 x29 x30 x31,
    bv_unsigned wNB = NB -> (1 <= length B)%nat -> KMNB jb m1 -> RES = mn_model A B ->
    evt bgbsegs POST (ST 0x2290c4 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 wNB x21 x22 x23 x24 (Z_to_bv 64 (rp + 8 * NA)) x26 x28 x29 x30 x31).
  Proof.
    intros until x31. intros ENB HB1 IB ER.
    pose proof IB as (HA & HB & HW & FR & ST & MI & MU & WM).
    pose proof (proj1 ST) as LO0.
    assert (SP112 : (112 <= SP)%Z) by (clear - LO LO0; lia).
    pose proof (ESPc SP112) as ESP.
    pose proof (run_bounds _ _ IB ltac:(clear - HB1; lia)) as (BB & BR).
    pose proof (zr_word a0) as Z0. pose proof (zr_word wPB) as ZB. unfold inr64 in Z0, ZB.
    assert (NA0 : (0 <= NA)%Z) by (clear; lia).
    destruct (UBR ltac:(lia)) as (NZR & ALR). destruct (UBA ltac:(lia)) as (NZA & ALA). destruct (UBB ltac:(lia)) as (NZB & ALB).
    destruct B as [|w0 B'] eqn:EB; [exfalso; cbn [length] in HB1; lia|]. rewrite <- EB in *.
    assert (Ew0 : nth_error B 0 = Some w0) by (rewrite EB; reflexivity).
    pose proof (limbs_nth_error_lit B 0 w0 LB Ew0) as Rw0.
    assert (Ew64 : bv_unsigned (Z_to_bv 64 w0) = w0) by (apply inr64_unsigned_lit; unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; exact Rw0).
    destruct (callee_asan _ m1 0%nat IB ltac:(clear; lia)) as (SH1 & ACR1 & ACA1 & _ & APT1).
    change (Z.of_nat 0) with 0%Z in ACR1, APT1. rewrite Z.mul_0_r, Z.add_0_r in ACR1, APT1.

    ub.

    pose proof SH1 as [G1 G2]. unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in G1, G2.
    do 3 zstep. clear G1 G2.
    do 2 zstep.
    assert (HkB0 : (0 < length B)%nat) by (clear - HB1; lia).
    (let ad := cur_mem_addr in pose proof (shB_rd _ m1 0%nat ad IB HkB0 ltac:(sh_addr)) as RD); zstep; clear RD. chk0.
    (let ad := cur_mem_addr in pose proof (limbs_at_read_nth bgbsegs m1 PB B 0 w0 ad HB Ew0
        ltac:(unfold wa; change (Z.of_nat 0) with 0%Z; rewrite Z.mul_0_r, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as RD); zstep; clear RD.
    do 4 zstep.
    eapply evt_cut.
    { eapply bn_mul_words_aspec with (a := A) (lo := lo) (m := m1).
      - exact LA.
      - clear - N31. lia.
      - exact ENA.
      - exact HA.
      - apply (wr_at_sub bgbsegs m1 rp (8 * NN) 0 (8 * NA)) in HW; [rewrite Z.add_0_r in HW; exact HW | lia | lia | lia].
      - unfold alias_ok. clear - DRA. lia.
      - rewrite ESP. exact ST.
      - rewrite ESP. clear - LO. lia.
      - rewrite ESP. clear - SEPR. lia.
      - rewrite ESP. clear - SEPA. lia.
      - exact MI.
      - exact SH1.
      - exact ACR1.
      - exact ACA1.
      - exact APT1.
      - intros _. split; assumption.
      - intros _. split; assumption. }
    intros ms' PO. unfold mw_apost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HS & STc).
    subst ms'. rewrite ESP, Ew64 in *.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    pose proof (mul_words_spec A w0 LA Rw0) as MSP.
    destruct (mul_words A w0) as [seg c] eqn:EMW. cbn [fst snd] in *.
    destruct MSP as (Lseg & Eseg & Lc & _). unfold limb, BW in Lc.
    assert (MUc' : munch [(rp + 8 * Z.of_nat 0, rp + 8 * Z.of_nat 0 + 8 * NA); (SP + -112 - 112, SP + -112)]%Z m1 m2).
    { change (Z.of_nat 0) with 0%Z. rewrite Z.mul_0_r, Z.add_0_r. exact MUc. }
    assert (HS' : limbs_at bgbsegs m2 (rp + 8 * Z.of_nat 0) seg) by (change (Z.of_nat 0) with 0%Z; rewrite Z.mul_0_r, Z.add_0_r; exact HS).
    pose proof (AFTER (FCELLS jb) m1 m2 [] 0%nat seg 112%Z eq_refl IB limbs_nil
                  ltac:(apply limbs_at_nil; destruct HW as (W0 & W1 & _); lia) eq_refl ltac:(clear - HB1; lia) ltac:(lia)
                  MUc' WMc MIc HS' STc Lseg Eseg) as I2.
    cbn [app] in I2.
    clear HA HB HW FR ST MI MU WM MUc MUc' WMc MIc HS HS' STc IB.

    ub. do 2 zstep.
    assert (HkR0 : (Z.of_nat (length A + 0) < NN)%Z) by (clear - HB1; lia).
    (let ad := cur_mem_addr in pose proof I2 as (_ & _ & IB2); pose proof (shR_rd _ m2 (length A + 0)%nat ad IB2 HkR0 ltac:(sh_addr)) as RD); zstep; clear RD IB2. chk0.
    zstep.
    assert (LRs : length seg = (length A + 0)%nat) by (rewrite Eseg; clear; lia).
    pose proof (CARRY (FCELLS jb) m2 seg 0%nat c eq_refl I2 LRs ltac:(clear - HB1; lia) Lc) as (SOK0 & I4).
    clear I2.
    mn_store SOK0 I4.
    assert (ER1 : RES = mul_normal_loop A (skipn 1 B) (seg ++ [c]) 1).
    { rewrite ER. unfold W_mul_normal.mn_model. rewrite EB. rewrite <- EB. rewrite EMW. rewrite EB. reflexivity. }
    assert (LR1 : length (seg ++ [c]) = (length A + 1)%nat) by (rewrite length_app, Eseg; reflexivity).
    zstep. if_cases K; zify_cond K.
    -
      rewrite ENB in K.
      zstep.
      eapply evt_eq; [ | eapply (mn_loop (length B - 1)%nat 1%nat (seg ++ [c]) jb); [ reflexivity | clear - K HB1; lia | exact I4 | exact LR1 | exact ER1 ] ].
      replace (NB - Z.of_nat 1 + 1)%Z with NB by (clear; lia). rewrite <- ENB, Z_to_bv_bv_unsigned.
      change (8 * (Z.of_nat 1 - 1))%Z with 0%Z. reflexivity.
    - rewrite ENB in K.
      assert (ERf : RES = seg ++ [c]).
      { rewrite ER1. rewrite skipn_all2 by (clear - K; lia). reflexivity. }
      rewrite <- ERf in I4. eapply mn_ret. exact I4.
  Qed.

  Lemma mn_zero : forall jb m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31,
    length B = 0%nat -> KMNB jb m1 -> RES = mn_model A B ->
    evt bgbsegs POST (ST 0x229164 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31).
  Proof.
    intros until x31. intros HB0 IB ER.
    destruct (callee_asan _ m1 0%nat IB ltac:(clear; lia)) as (SH1 & ACR1 & ACA1 & _ & APT1).
    change (Z.of_nat 0) with 0%Z in ACR1, APT1. rewrite Z.mul_0_r, Z.add_0_r in ACR1, APT1.
    pose proof IB as (HA & HB & HW & FR & ST & MI & MU & WM).
    do 19 zstep.
    release_frame FR ST (bv_unsigned sp).
    eapply evt_mono.
    - eapply bn_mul_words_aspec with (a := A) (lo := lo).
      + exact LA.
      + clear - N31. lia.
      + exact ENA.
      + exact HA.
      + apply (wr_at_sub bgbsegs _ rp (8 * NN) 0 (8 * NA)) in HW; [rewrite Z.add_0_r in HW; exact HW | lia | lia | lia].
      + unfold alias_ok. clear - DRA. lia.
      + exact ST.
      + clear - LO. lia.
      + clear - SEPR. lia.
      + clear - SEPA. lia.
      + exact MI.
      + exact SH1.
      + exact ACR1.
      + exact ACA1.
      + exact APT1.
      + intros _. apply UBR. lia.
      + intros _. apply UBA. lia.
    - intros ms' PO. unfold mw_apost, wl_post in PO.
      destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HS & STc).
      exists u0, u1, u2, (Z_to_bv 64 (snd (mul_words A (bv_unsigned (Z_to_bv 64 0))))), v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, m2.
      split; [exact E|].
      split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc].
               unfold sub_fp. cbn [outside]. intros x Hx. rewrite HB0 in Hx. clear - Hx. lia. }
      split. { eapply wmono_trans; [exact WM | exact WMc]. }
      split; [exact MIc|]. split; [|exact STc].
      rewrite ER. unfold W_mul_normal.mn_model. destruct B; [|discriminate HB0]. exact HS.
  Qed.

  Lemma mn_mid : forall (wNB : word) jb m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31,
    bv_unsigned wNB = NB -> KMNB jb m1 -> RES = mn_model A B ->
    evt bgbsegs POST (ST 0x229098 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 wNB x21 x22 x23 x24 x25 x26 x28 x29 x30 x31).
  Proof.
    intros until x31. intros ENB IB ER.
    destruct (UBR ltac:(lia)) as (NZR & ALR).
    pose proof (zr_word wNA) as ZN. unfold inr64 in ZN.
    assert (P : (rp + 8 * NA < 18446744073709551616)%Z).
    { destruct (Z.eq_dec NN 0) as [E0|NE0].
      - pose proof (zr_word a0) as R0. unfold inr64 in R0. change (2 ^ 64)%Z with 18446744073709551616%Z in R0. clear - E0 R0. lia.
      - pose proof IB as (HA & HB & HW & FR & ST & MI & MU & WM).
        pose proof (wr_at_below bgbsegs m1 rp (8 * NN) MI HW ltac:(clear - NE0; lia)) as T. unfold UTOP in T. clear - T. lia. }
    zstep. rewrite ENA. replace (NA ≪ 3)%Z with (8 * NA)%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.
    ub.
    assert (Lw : (bv_unsigned wNB < 9223372036854775808)%Z) by (rewrite ENB; clear - N31; lia).
    assert (L0 : (bv_unsigned (Z_to_bv 64 0) < 9223372036854775808)%Z) by (vm_compute; reflexivity).
    zstep. rewrite (lts_words_small (Z_to_bv 64 0) wNB L0 Lw). rewrite ENB.
    if_cases K2; zify_cond K2.
    -
      assert (HB0 : length B = 0%nat) by (clear - K2; lia).
      eapply mn_zero; [exact HB0 | exact IB | exact ER].
    - assert (HB1 : (1 <= length B)%nat) by (clear - K2; lia).
      eapply (mn_first wNB); [exact ENB | exact HB1 | exact IB | exact ER].
  Qed.
End Mach.

Section Main.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (lo : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation bp := (bv_unsigned a3).
  Notation SP := (bv_unsigned sp).
  Notation NN := (Z.of_nat (length a) + Z.of_nat (length b))%Z.
  Hypothesis LA : limbs a.
  Hypothesis LB : limbs b.
  Hypothesis N31 : (NN < 2147483648)%Z.
  Hypothesis A2 : bv_unsigned a2 = Z.of_nat (length a).
  Hypothesis A4 : bv_unsigned a4 = Z.of_nat (length b).
  Hypothesis RA : limbs_at bgbsegs m ap a.
  Hypothesis RB : limbs_at bgbsegs m bp b.
  Hypothesis WR : wr_at bgbsegs m rp (8 * NN).
  Hypothesis DRA : (rp + 8 * NN <= ap \/ ap + 8 * Z.of_nat (length a) <= rp)%Z.
  Hypothesis DRB : (rp + 8 * NN <= bp \/ bp + 8 * Z.of_nat (length b) <= rp)%Z.
  Hypothesis STK : stk bgbsegs m lo SP.
  Hypothesis LO : (lo <= SP - 240)%Z.
  Hypothesis SEPR : (rp + 8 * NN <= SP - 240 \/ SP <= rp)%Z.
  Hypothesis SEPA : (ap + 8 * Z.of_nat (length a) <= SP - 240 \/ SP <= ap)%Z.
  Hypothesis SEPB : (bp + 8 * Z.of_nat (length b) <= SP - 240 \/ SP <= bp)%Z.
  Hypothesis MI0 : mem_inv bgbsegs m.

  Hypothesis SHBC : shb_cells bgbsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m.
  Hypothesis ACR : acc bgbsegs m rp (8 * NN).
  Hypothesis ACA : acc bgbsegs m ap (8 * Z.of_nat (length a)).
  Hypothesis ACB : acc bgbsegs m bp (8 * Z.of_nat (length b)).
  Hypothesis APT : aptrs3 rp ap bp NN lo.
  Hypothesis OFFI : (rp + 8 * NN <= 65536 \/ 12554240 <= rp)%Z.

  Hypothesis UBR : ub_ptr_ok 1 (bv_unsigned a0).
  Hypothesis UBA : ub_ptr_ok 1 (bv_unsigned a1).
  Hypothesis UBB : ub_ptr_ok 1 (bv_unsigned a3).

  Lemma bn_mul_normal_aspec :
    evt bgbsegs (vl_post bgbsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) NN 240%Z (mul_normal a b) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x229030) fc None m (seg_rom bgbsegs)).
  Proof.
    pose proof (munch_refl [(rp, rp + 8 * NN); (SP - 240, SP)]%Z m) as MU. pose proof (munch_refl [(SP - 240, SP)]%Z m) as MUF.
    pose proof (wmono_refl bgbsegs m) as WM.
    carve_frame 112%nat STK.
    do 18 zstep.
    assert (RA1 : limbs_at bgbsegs m0 ap a) by (eapply limbs_at_transport; [exact RA | exact MUF | cbn [disjoint_from]; clear - SEPA; lia]).
    assert (RB1 : limbs_at bgbsegs m0 bp b) by (eapply limbs_at_transport; [exact RB | exact MUF | cbn [disjoint_from]; clear - SEPB; lia]).
    clear MUF.
    pose proof (zr_word a2) as R2. pose proof (zr_word a4) as R4. unfold inr64 in R2, R4.
    zstep. rewrite lts_words_small by (rewrite ?A2, ?A4; clear - N31; lia). rewrite A2, A4.
    if_cases K; zify_cond K.
    -
      assert (EM : mul_normal a b = mn_model a b).
      { rewrite mul_normal_mn. destruct (Nat.ltb_spec (length a) (length b)) as [H|H]; [exfalso; clear - H K; lia | reflexivity]. }
      do 4 zstep.
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jbv :: _) =>
        eapply (mn_mid) with (A := a) (B := b) (wPA := a1) (wPB := a3) (wNA := a2) (wNB := a4) (jb := jbv) end;
        try assumption; try (clear - N31; lia).
      split; [exact RA1|]. split; [exact RB1|]. split; [exact WR|]. split; [exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact MU | exact WM].
    -
      assert (EM : mul_normal a b = mn_model b a).
      { rewrite mul_normal_mn. destruct (Nat.ltb_spec (length a) (length b)) as [H|H]; [reflexivity | exfalso; clear - H K; lia]. }
      do 3 zstep.
      assert (WR' : wr_at bgbsegs m0 rp (8 * (Z.of_nat (length b) + Z.of_nat (length a)))).
      { replace (Z.of_nat (length b) + Z.of_nat (length a))%Z with NN by (clear; lia). exact WR. }
      assert (MU' : munch [(rp, rp + 8 * (Z.of_nat (length b) + Z.of_nat (length a))); (SP - 240, SP)]%Z m m0).
      { replace (Z.of_nat (length b) + Z.of_nat (length a))%Z with NN by (clear; lia). exact MU. }
      assert (ACR' : acc bgbsegs m rp (8 * (Z.of_nat (length b) + Z.of_nat (length a)))).
      { replace (Z.of_nat (length b) + Z.of_nat (length a))%Z with NN by (clear; lia). exact ACR. }
      assert (APT' : aptrs3 rp bp ap (Z.of_nat (length b) + Z.of_nat (length a)) lo).
      { clear - APT. unfold aptrs3 in *. replace (Z.of_nat (length b) + Z.of_nat (length a))%Z with NN by lia. tauto. }
      assert (CONV : forall ms', vl_post bgbsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rp
                                   (Z.of_nat (length b) + Z.of_nat (length a)) 240%Z (mul_normal a b) lo m ms' ->
                                 vl_post bgbsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rp NN 240%Z (mul_normal a b) lo m ms').
      { intros ms' H. replace NN with (Z.of_nat (length b) + Z.of_nat (length a))%Z by (clear; lia). exact H. }
      eapply evt_mono; [ | exact CONV ].
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jbv :: _) =>
        eapply (mn_mid) with (A := b) (B := a) (wPA := a3) (wPB := a1) (wNA := a4) (wNB := a2) (jb := jbv) end;
        try assumption; try (clear - N31; lia); try (clear - DRA DRB; lia); try (clear - SEPR; lia); try (clear - OFFI; lia).
      split; [exact RB1|]. split; [exact RA1|]. split; [exact WR'|]. split; [exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact MU' | exact WM].
  Qed.
End Main.
