(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop BnCmp BnKaraX.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require BnKaraMem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require W_mul_recursive W_mul_normal.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnWU Require WU_mul_recursive.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require BnKit2.  (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop AsLeaf.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnIfaceA AsStruct ImplA RtCallA BnKaraMemA BnCallsKA AW_mul_recursive.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Ltac wnorm :=
  rewrite ?land_m64; rewrite ?Z_to_bv_unsigned, ?Z.shiftl_mul_pow2 by lia; change (2 ^ 1)%Z with 2%Z; change (2 ^ 3)%Z with 8%Z;
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus;
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z; change (2 ^ Z.of_N 32)%Z with 4294967296%Z;
  change (4294967296 `div` 2)%Z with 2147483648%Z; change (2 ^ 64)%Z with 18446744073709551616%Z;
  Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition top_preA (CS8 : Z) (N2 da db la lb lR lT : nat) (SK rp tq ap bp SP lo : Z) : Prop :=
  (2 <= Z.of_nat N2 <= 67108864)%Z /\ (da <= 1)%nat /\ (db <= 1)%nat /\
  la = (N2 - da)%nat /\ lb = (N2 - db)%nat /\ lR = (2 * N2)%nat /\ (65536 <= SK /\ CS8 <= SK)%Z /\
  (rp + 8 * Z.of_nat lR <= ap \/ ap + 8 * Z.of_nat la <= rp)%Z /\
  (rp + 8 * Z.of_nat lR <= bp \/ bp + 8 * Z.of_nat lb <= rp)%Z /\
  (tq + 8 * Z.of_nat lT <= ap \/ ap + 8 * Z.of_nat la <= tq)%Z /\
  (tq + 8 * Z.of_nat lT <= bp \/ bp + 8 * Z.of_nat lb <= tq)%Z /\
  (rp + 8 * Z.of_nat lR <= tq \/ tq + 8 * Z.of_nat lT <= rp)%Z /\
  (rp + 8 * Z.of_nat lR <= SP - 160 - SK \/ SP <= rp)%Z /\
  (tq + 8 * Z.of_nat lT <= SP - 160 - SK \/ SP <= tq)%Z /\
  (ap + 8 * Z.of_nat la <= SP - 160 - SK \/ SP <= ap)%Z /\
  (bp + 8 * Z.of_nat lb <= SP - 160 - SK \/ SP <= bp)%Z /\
  (lo <= SP - 160 - SK)%Z /\ (0 <= lo)%Z /\
  (0 < rp /\ rp mod 8 = 0 /\ 0 < ap /\ ap mod 8 = 0 /\ 0 < bp /\ bp mod 8 = 0 /\ 0 < tq /\ tq mod 8 = 0)%Z.

Section Top.
  Context {AR : ARun}.
  Local Notation RT := (@ar_RT AR).
  Local Notation PMc := (@ar_PMc AR).
  Local Notation ACEIL := (@BnHeapA.ACEIL AR).
  Local Notation AHEAP := (@BnHeapA.AHEAP AR).
  Variable CS8 : Z.
  Hypothesis CS8_0 : (0 <= CS8)%Z.
  Hypothesis comba8_ok : comba8_aspec CS8.
  Hypothesis mul_normal_ok : mul_normal_bspec.
  Variables (Σ : rts RT) (OW LB : list block) (bR bT bA bB : block).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : word -> option byte) (a b : list Z) (da db : nat) (R T : list Z) (lo : Z) (N2 : nat) (SK : Z).
  Notation rp := (bv_unsigned a0).
  Notation ap := (bv_unsigned a1).
  Notation bp := (bv_unsigned a2).
  Notation tq := (bv_unsigned a6).
  Notation SP := (bv_unsigned sp).
  Hypothesis PRE : top_preA CS8 N2 da db (length a) (length b) (length R) (length T) SK (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo.
  Hypothesis KBL : kara_blocks OW LB bR bT bA bB rp tq ap bp (length R) (length T) (length a) (length b).
  Hypothesis CEIL : (ACEIL <= lo)%Z.
  Hypothesis SPT16 : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis ETP : tp = wz TP_A.
  Hypothesis LA : limbs a.
  Hypothesis LB' : limbs b.
  Hypothesis A3 : bv_unsigned a3 = Z.of_nat N2.
  Hypothesis A4 : a4 = Z_to_bv 64 (- Z.of_nat da).
  Hypothesis A5 : a5 = Z_to_bv 64 (- Z.of_nat db).

  Variable hn : nat.
  Hypothesis EN2h : N2 = (2 * hn)%nat.
  Lemma HN2 : (2 <= Z.of_nat N2 <= 67108864)%Z. Proof. apply PRE. Qed.
  Lemma Hda : (da <= 1)%nat. Proof. apply PRE. Qed.
  Lemma Hdb : (db <= 1)%nat. Proof. apply PRE. Qed.
  Lemma HLA : length a = (N2 - da)%nat. Proof. apply PRE. Qed.
  Lemma HLB : length b = (N2 - db)%nat. Proof. apply PRE. Qed.
  Lemma HLR : length R = (2 * N2)%nat. Proof. apply PRE. Qed.
  Lemma HSK : (65536 <= SK /\ CS8 <= SK)%Z. Proof. apply PRE. Qed.
  Lemma DRA : (rp + 8 * Z.of_nat (length R) <= ap \/ ap + 8 * Z.of_nat (length a) <= rp)%Z. Proof. apply PRE. Qed.
  Lemma DRB : (rp + 8 * Z.of_nat (length R) <= bp \/ bp + 8 * Z.of_nat (length b) <= rp)%Z. Proof. apply PRE. Qed.
  Lemma DTA : (tq + 8 * Z.of_nat (length T) <= ap \/ ap + 8 * Z.of_nat (length a) <= tq)%Z. Proof. apply PRE. Qed.
  Lemma DTB : (tq + 8 * Z.of_nat (length T) <= bp \/ bp + 8 * Z.of_nat (length b) <= tq)%Z. Proof. apply PRE. Qed.
  Lemma DRT : (rp + 8 * Z.of_nat (length R) <= tq \/ tq + 8 * Z.of_nat (length T) <= rp)%Z. Proof. apply PRE. Qed.
  Lemma SEPR : (rp + 8 * Z.of_nat (length R) <= SP - 160 - SK \/ SP <= rp)%Z. Proof. apply PRE. Qed.
  Lemma SEPT : (tq + 8 * Z.of_nat (length T) <= SP - 160 - SK \/ SP <= tq)%Z. Proof. apply PRE. Qed.
  Lemma SEPA : (ap + 8 * Z.of_nat (length a) <= SP - 160 - SK \/ SP <= ap)%Z. Proof. apply PRE. Qed.
  Lemma SEPB : (bp + 8 * Z.of_nat (length b) <= SP - 160 - SK \/ SP <= bp)%Z. Proof. apply PRE. Qed.
  Lemma LO : (lo <= SP - 160 - SK)%Z. Proof. apply PRE. Qed.
  Lemma LO0 : (0 <= lo)%Z. Proof. apply PRE. Qed.
  Lemma tubs : (0 < rp /\ rp mod 8 = 0 /\ 0 < ap /\ ap mod 8 = 0 /\ 0 < bp /\ bp mod 8 = 0 /\ 0 < tq /\ tq mod 8 = 0)%Z. Proof. apply PRE. Qed.
  Variable RES : list Z * list Z.

  Lemma tSK0 : (0 <= SK)%Z. Proof. pose proof HSK as h. clear - h. lia. Qed.
  Lemma tFS0 : (0 <= 160)%Z. Proof. lia. Qed.
  Lemma tFBE : (SP + -160 = SP - 160)%Z. Proof. reflexivity. Qed.
  Lemma tSPTop : (SP <= USTACK_TOP)%Z. Proof. pose proof SPT16. lia. Qed.
  Lemma tESP160 : bv_unsigned (Z_to_bv 64 (SP + -160)) = (SP + -160)%Z.
  Proof.
    apply inr64_unsigned_lit. unfold inr64. change (2 ^ 64)%Z with 18446744073709551616%Z.
    pose proof (zr_word sp) as RS. unfold inr64 in RS. change (2 ^ 64)%Z with 18446744073709551616%Z in RS.
    pose proof tSK0 as S0. pose proof LO as L1. pose proof LO0 as L2. clear - RS L1 L2 S0. lia.
  Qed.
  Lemma tINR : In bR OW. Proof. apply KBL. Qed.
  Lemma tINT : In bT OW. Proof. apply KBL. Qed.
  Lemma tINA : In bA (OW ++ LB). Proof. apply KBL. Qed.
  Lemma tINB : In bB (OW ++ LB). Proof. apply KBL. Qed.
  Lemma tRGR : (blk_addr bR <= rp /\ rp + 8 * Z.of_nat (length R) <= blk_addr bR + blk_size bR)%Z. Proof. apply KBL. Qed.
  Lemma tRGT : (blk_addr bT <= tq /\ tq + 8 * Z.of_nat (length T) <= blk_addr bT + blk_size bT)%Z. Proof. apply KBL. Qed.
  Lemma tRGA : (blk_addr bA <= ap /\ ap + 8 * Z.of_nat (length a) <= blk_addr bA + blk_size bA)%Z. Proof. apply KBL. Qed.
  Lemma tRGB : (blk_addr bB <= bp /\ bp + 8 * Z.of_nat (length b) <= blk_addr bB + blk_size bB)%Z. Proof. apply KBL. Qed.
  Lemma tAL8 : (rp mod 8 = 0 /\ tq mod 8 = 0 /\ ap mod 8 = 0 /\ bp mod 8 = 0)%Z. Proof. apply KBL. Qed.

  Notation POST := (kpost Σ (ASTA RT Σ PMc (kr_apost ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo
                      (bv_unsigned a0) (Z.of_nat (length R)) (bv_unsigned a6) (Z.of_nat (length T)) (fst RES) (snd RES) m))).
  Notation KS L := (L Σ OW LB m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (length R) (length T)
                      160%Z SK (bv_unsigned sp + -160)%Z bR bT bA bB tFS0 tFBE tSK0 DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB
                      tINR tINT tINA tINB tRGR tRGT tRGA tRGB CEIL LO tSPTop).
  Notation KBS := (KB Σ OW LB m (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp) lo a b (length R) (length T)
                      (bv_unsigned sp + -160)%Z).

  Notation FCELLS0 jb48 := [CB 48 jb48; C8 a0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Notation ST0 F fc pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma T_epi : forall jb48 m1 R1 T1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc,
    KBS (FCELLS0 jb48) m1 R1 T1 -> RES = (R1, T1) ->
    evt bsegs POST (ST0 F fc 0x24d848 m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until fc. intros (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM) E.
    do 15 zstep.
    assert (LO1 : (lo <= SP + -160)%Z) by (pose proof LO as L1; pose proof HSK as L2; clear - L1 L2; lia).
    release_frame FR ST (bv_unsigned sp).
    subst RES. cbn [fst snd].
    apply evt_done. unfold kpost. apply cps_done. unfold kr_apost. rewrite ETP.
    do 18 eexists. split; [reflexivity|].
    split; [exact MI|]. split; [exact ST|]. split; [exact HEAP|]. split; [exact WM|].
    split; [exact MU|]. split; [exact HR | exact HT].
  Qed.

  Ltac tret_even := apply ret_pc_even; [lia | reflexivity].
  Ltac tulit := first [ reflexivity | rewrite inr64_unsigned_lit by (unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; lia); lia | lia ].

  Lemma tgeom : (2 <= Z.of_nat N2 <= 67108864 /\ 0 <= lo /\ lo <= SP - 160 - SK /\ 65536 <= SK /\ CS8 <= SK /\ 0 <= CS8 /\
                 Z.of_nat da <= 1 /\ Z.of_nat db <= 1 /\
                 Z.of_nat (length a) = Z.of_nat N2 - Z.of_nat da /\ Z.of_nat (length b) = Z.of_nat N2 - Z.of_nat db /\
                 Z.of_nat (length R) = 2 * Z.of_nat N2)%Z.
  Proof.
    pose proof HN2 as h1. pose proof LO as h2. pose proof LO0 as h3. pose proof HSK as h4. pose proof Hda as h5. pose proof Hdb as h6.
    pose proof HLA as h7. pose proof HLB as h8. pose proof HLR as h9. clear - h1 h2 h3 h4 h5 h6 h7 h8 h9 CS8_0. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma T_comba : forall jb48 m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc,
    KBS (FCELLS0 jb48) m1 R T -> N2 = 8%nat -> da = 0%nat -> db = 0%nat ->
    RES = (splice R 0 (mul_comba8 a b), T) ->
    evt bsegs POST (ST0 F fc 0x24d170 m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 a2 a1 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until fc. intros I E8 Eda Edb ERES.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof tgeom as G.
    do 18 zstep.
    assert (LO1 : (lo <= SP + -160)%Z) by (clear - G; lia).
    release_frame FR ST (bv_unsigned sp).
    assert (La8 : length a = 8%nat) by (pose proof HLA as h; clear - h E8 Eda; lia). assert (Lb8 : length b = 8%nat) by (pose proof HLB as h; clear - h E8 Edb; lia).
    assert (LR16 : length R = 16%nat) by (pose proof HLR as h; clear - h E8; lia).
    pose proof tAL8 as (AR8 & AT8 & AA8 & AB8). pose proof tRGR as RR'. pose proof tRGA as RA'. pose proof tRGB as RB'.
    pose proof (AH_ceil _ _ _ _ HEAP) as (_ & CSH & _).
    pose proof (AH_offsh _ _ _ _ bR HEAP ltac:(apply in_or_app; left; exact tINR)) as OSH.
    pose proof DRA as D1. pose proof DRB as D2. pose proof SEPR as D3. pose proof SEPA as D4. pose proof SEPB as D5. pose proof DRT as D6. pose proof SEPT as D7.
    eapply evt_mono.
    { eapply comba8_ok with (a := a) (b := b) (lo := lo);
        [ exact LA | exact LB' | exact La8 | exact Lb8 | exact HA | exact HB | rewrite LR16 in WR; exact WR
        | clear - D1 LR16 La8; lia | clear - D2 LR16 Lb8; lia | exact ST | clear - G; lia
        | clear - D3 LR16 G; lia | clear - D4 La8 G; lia | clear - D5 Lb8 G; lia | exact MI
        | exact (AH_shb _ _ _ _ HEAP)
        | eapply (AH_acc_in _ _ _ _ bR); [exact HEAP | apply in_or_app; left; exact tINR | clear - RR'; lia | clear - RR' LR16; lia]
        | eapply (AH_acc_in _ _ _ _ bA); [exact HEAP | exact tINA | clear - RA'; lia | clear - RA' La8; lia]
        | eapply (AH_acc_in _ _ _ _ bB); [exact HEAP | exact tINB | clear - RB'; lia | clear - RB' Lb8; lia]
        | unfold aptrs3; split; [exact AR8|]; split; [exact AA8|]; split; [exact AB8|]; split; [clear - OSH RR' LR16; lia | clear - CSH CEIL; lia]
        | pose proof (AH_range_gen _ _ _ _ bR HEAP ltac:(apply in_or_app; left; exact tINR)) as (P & _); clear - P RR'; lia
        | pose proof (AH_range_gen _ _ _ _ bA HEAP tINA) as (P & _); clear - P RA'; lia
        | pose proof (AH_range_gen _ _ _ _ bB HEAP tINB) as (P & _); clear - P RB'; lia
        | pose proof (AH_range_gen _ _ _ _ bR HEAP ltac:(apply in_or_app; left; exact tINR)) as (_ & _ & _ & _ & P); clear - P RR' LR16; lia ]. }
    intros ms' PO. unfold W_mul_normal.vl_post in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HS & STc).
    assert (HW : Forall (kw_ok rp tq SP lo (length R) (length T)) [(rp, rp + 8 * 16); (SP - CS8, SP)]%Z).
    { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold kw_ok; cbn [fst snd].
      - right; left. clear - LR16. lia.
      - left. clear - G. lia. }
    subst ms'. unfold kpost. apply cps_done. unfold kr_apost. rewrite ETP.
    do 18 eexists. split; [reflexivity|].
    split; [exact MIc|]. split; [exact STc|].
    split; [exact (KS kw_heap _ m1 m2 HEAP MUc WMc HW)|].
    split; [eapply wmono_trans; [exact WM | exact WMc]|].
    split. { eapply agree_on_trans; [exact MU|]. exact (KS kw_agree _ m1 m2 HEAP MUc HW). }
    rewrite ERES. cbn [fst snd].
    destruct (mul_comba8_spec a b LA LB' La8 Lb8) as (_ & Lc & _).
    rewrite splice_all by (rewrite Lc, LR16; reflexivity).
    split; [exact HS|].
    eapply limbs_at_transport; [exact HT | exact MUc | cbn [disjoint_from]; clear - D6 D7 LR16 G; lia].
  Qed.

  (* [comment removed for export] *)
  Ltac tacc I G := first
    [ eapply (KS KB_accRz _ _ _ _ _ _ I); clear - G; lia
    | eapply (KS KB_accaz _ _ _ _ _ _ I); clear - G; lia
    | eapply (KS KB_accbz _ _ _ _ _ _ I); clear - G; lia ].
  Ltac tal8 := repeat apply mod8_add8; apply tAL8.
  Ltac tub_tac G :=
    unfold ub_ptr_ok; intros _; let UB := fresh "UB" in pose proof tubs as UB;
    split; [ clear - UB G; lia | clear - UB; Z.div_mod_to_equations; lia ].

  (* [comment removed for export] *)
  Lemma T_small : forall jb48 m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x17 x19 x20 x21 x22 x24 x26 x27 x28 x29 x30 x31 F fc,
    KBS (FCELLS0 jb48) m1 R T -> (Z.of_nat N2 <= 15)%Z ->
    RES = ((if (0 <? da + db)%nat then splice (splice R 0 (mul_normal a b)) (2 * N2 - da - db) (repeat 0%Z (da + db))
            else splice R 0 (mul_normal a b)), T) ->
    evt bsegs POST (ST0 F fc 0x24d1c0 m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 a2 a1 x17 a3 x19 x20 x21 x22 a5 x24 a4 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until fc. intros I K16 ERES.
    pose proof I as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof tgeom as G. pose proof Hda as HDA. pose proof Hdb as HDB.
    do 2 zstep.
    setreg 12%Z (Z_to_bv 64 (Z.of_nat N2 - Z.of_nat da)) ltac:(rewrite A3, A4; apply Z_to_bv_eqm; clear - HDA G; wnorm).
    setreg 10%Z (Z_to_bv 64 (Z.of_nat N2 - Z.of_nat da)) ltac:(rewrite A3, A4; apply Z_to_bv_eqm; clear - HDA G; wnorm).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    do 2 zstep.
    setreg 10%Z (Z_to_bv 64 (Z.of_nat N2 - Z.of_nat db)) ltac:(rewrite A3, A5; apply Z_to_bv_eqm; clear - HDB G; wnorm).
    setreg 14%Z (Z_to_bv 64 (Z.of_nat N2 - Z.of_nat db)) ltac:(rewrite A3, A5; apply Z_to_bv_eqm; clear - HDB G; wnorm).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    zstep. rewrite ?land_m64. rewrite (bn_swrap32_small (Z.of_nat N2 - Z.of_nat db + 0)), Z.add_0_r by (clear - HDB G; lia).
    do 4 zstep.
    pose proof DRA as D1. pose proof DRB as D2. pose proof SEPR as D3. pose proof SEPA as D4. pose proof SEPB as D5.
    assert (Lab : (Z.of_nat (length a) = Z.of_nat N2 - Z.of_nat da /\ Z.of_nat (length b) = Z.of_nat N2 - Z.of_nat db /\ Z.of_nat (length R) = 2 * Z.of_nat N2)%Z)
      by (clear - G; lia).
    pose proof (KS KB_offR _ _ _ _ I) as (OSH & OFI). pose proof (KS KB_shhi _ _ _ _ I) as CSH.
    eapply call_mul_normalA with (a := a) (b := b) (lo := lo) (SPz := (SP + -160)%Z)
                                (RP := rp) (AP := ap) (BP := bp);
      [ exact tESP160 | tret_even | exact ST | exact MI | exact (AH_shb _ _ _ _ HEAP) | exact mul_normal_ok | exact LA | exact LB' | clear - G K16; lia
      | reflexivity | reflexivity | rewrite inr64_unsigned_lit by (unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; clear - G; lia); clear - Lab; lia
      | reflexivity | rewrite inr64_unsigned_lit by (unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; clear - G; lia); clear - Lab; lia
      | exact HA | exact HB
      | pose proof (wr_at_sub bsegs m1 _ _ 0 (8 * (Z.of_nat (length a) + Z.of_nat (length b))) WR ltac:(lia) ltac:(lia) ltac:(clear - G; lia)) as X;
        rewrite Z.add_0_r in X; exact X
      | clear - D1 G; lia | clear - D2 G; lia | clear - G; lia
      | clear - D3 G; lia | clear - D4 G; lia | clear - D5 G; lia
      | split; [tacc I G|]; split; [tacc I G|]; split; [tacc I G|];
        split; [unfold aptrs3; split; [tal8|]; split; [tal8|]; split; [tal8|]; split; [clear - OSH G; lia | exact CSH] | clear - OFI G; lia]
      | tub_tac G | tub_tac G | tub_tac G | ].
    intros m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 MUc WMc MIc HS STc.
    destruct (mul_normal_spec a b LA LB') as (LMN & _ & EMN).
    assert (EMN' : length (mul_normal a b) = (length a + length b)%nat).
    { rewrite EMN. destruct (Nat.eqb_spec (length a) 0) as [E|_]; [exfalso; clear - E G; lia|].
      destruct (Nat.eqb_spec (length b) 0) as [E|_]; [exfalso; clear - E G; lia|]. reflexivity. }
    clear EMN.
    pose proof (KS KB_after_R (FCELLS0 jb48) m1 m2 R T 0%nat (mul_normal a b) _ 240%Z eq_refl I
                  ltac:(rewrite Z.mul_0_r, Z.add_0_r; exact MUc) ltac:(rewrite EMN'; clear; lia)
                  ltac:(clear - G; lia) WMc MIc ltac:(rewrite Z.mul_0_r, Z.add_0_r; exact HS) STc LMN ltac:(rewrite EMN'; clear - G; lia)) as I2.
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HEAP MUc WMc HS MIc STc I D1 D2 D3 D4 D5 OSH OFI CSH.
    assert (EMOD : RES = ((if (0 <? da + db)%nat then splice (splice R 0 (mul_normal a b)) (2 * N2 - da - db) (repeat 0%Z (da + db))
                           else splice R 0 (mul_normal a b)), T)) by exact ERES.
    do 2 zstep.
    setreg 11%Z (Z_to_bv 64 (- (Z.of_nat da + Z.of_nat db))) ltac:(rewrite A4, A5; apply Z_to_bv_eqm; clear - HDA HDB; wnorm).
    setreg 10%Z (Z_to_bv 64 (- (Z.of_nat da + Z.of_nat db))) ltac:(rewrite A4, A5; apply Z_to_bv_eqm; clear - HDA HDB; wnorm).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    zstep. rewrite lts_signed by (clear - HDA HDB; lia).
    if_cases KZ; zify_cond KZ.
    { (* [comment removed for export] *)
      eapply T_epi; [exact I2|]. rewrite ERES.
      destruct (Nat.ltb_spec 0 (da + db)) as [HH|_]; [exfalso; clear - HH KZ; lia | reflexivity]. }
    destruct (Nat.ltb_spec 0 (da + db)) as [_|HH]; [|exfalso; clear - HH KZ; lia].
    do 2 zstep.
    setreg 18%Z (Z_to_bv 64 (Z.of_nat N2)) ltac:(rewrite <- A3; apply Z_to_bv_bv_unsigned).
    zstep. rewrite lts_signed by (clear - G; lia).
    if_cases C0; [exfalso; zify_cond C0; clear - C0 G; lia | clear C0].
    do 3 zstep.
    setreg 12%Z (Z_to_bv 64 (2 * Z.of_nat N2 - Z.of_nat da)) ltac:(rewrite A4; apply Z_to_bv_eqm; clear - HDA G; wnorm).
    setreg 10%Z (Z_to_bv 64 (2 * Z.of_nat N2 - Z.of_nat da)) ltac:(rewrite A4; apply Z_to_bv_eqm; clear - HDA G; wnorm).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    zstep. rewrite ?land_m64. rewrite (bn_swrap32_small (2 * Z.of_nat N2 - Z.of_nat da + 0)), Z.add_0_r by (clear - HDA G; lia).
    do 2 zstep.
    setreg 10%Z (Z_to_bv 64 (2 * Z.of_nat N2 - Z.of_nat da - Z.of_nat db)) ltac:(rewrite A5; apply Z_to_bv_eqm; clear - HDA HDB G; wnorm).
    setreg 12%Z (Z_to_bv 64 (2 * Z.of_nat N2 - Z.of_nat da - Z.of_nat db)) ltac:(rewrite A5; apply Z_to_bv_eqm; clear - HDA HDB G; wnorm).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    zstep. rewrite ?land_m64. rewrite (bn_swrap32_small (2 * Z.of_nat N2 - Z.of_nat da - Z.of_nat db + 0)), Z.add_0_r by (clear - HDA HDB G; lia).
    zstep. replace ((2 * Z.of_nat N2 - Z.of_nat da - Z.of_nat db) ≪ 3)%Z with (8 * (2 * Z.of_nat N2 - Z.of_nat da - Z.of_nat db))%Z
      by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    pose proof I2 as (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & MU & WM).
    pose proof (wr_at_b47 bsegs m2 _ _ WR MI ltac:(clear - G; lia)) as BR.
    assert (BR' : (0 < rp /\ rp + 16 * Z.of_nat N2 <= 140737488355328)%Z).
    { pose proof tubs as UB. split; [clear - UB; lia|]. clear - BR G. lia. }
    do 4 zstep.
    setreg 13%Z (Z_to_bv 64 1) ltac:(replace (0 <? rp)%Z with true by (symmetry; apply Z.ltb_lt; clear - BR'; lia); reflexivity).
    setreg 14%Z (Z_to_bv 64 0) ltac:(
      replace (rp + 8 * (2 * Z.of_nat N2 - Z.of_nat da - Z.of_nat db) <? 1)%Z with false
        by (symmetry; apply Z.ltb_ge; clear - BR' HDA HDB G; lia); reflexivity).
    zstep. if_false.
    do 5 zstep.
    setreg 12%Z (Z_to_bv 64 1) ltac:(
      replace (rp + 8 * (2 * Z.of_nat N2 - Z.of_nat da - Z.of_nat db) <? rp)%Z with false
        by (symmetry; apply Z.ltb_ge; clear - HDA HDB G; lia);
      rewrite lxor_signbit by (clear - HDA HDB G; lia);
      replace (2 * Z.of_nat N2 - Z.of_nat da - Z.of_nat db + 9223372036854775808 <? 9223372036854775808)%Z with false
        by (symmetry; apply Z.ltb_ge; clear - HDA HDB G; lia);
      reflexivity).
    zstep. if_false.
    do 2 zstep.
    setreg 11%Z (Z_to_bv 64 (Z.of_nat da + Z.of_nat db)) ltac:(apply Z_to_bv_eqm; clear - HDA HDB; wnorm).
    setreg 12%Z (Z_to_bv 64 (Z.of_nat da + Z.of_nat db)) ltac:(apply Z_to_bv_eqm; clear - HDA HDB; wnorm).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    zstep. rewrite ?land_m64. rewrite (bn_swrap32_small (Z.of_nat da + Z.of_nat db + 0)), Z.add_0_r by (clear - HDA HDB; lia).
    zstep. replace ((Z.of_nat da + Z.of_nat db) ≪ 3)%Z with (8 * Z.of_nat (da + db))%Z by (rewrite Z.shiftl_mul_pow2 by lia; clear; lia).
    zstep.
    remember (splice R 0 (mul_normal a b)) as R1 eqn:ER1.
    assert (ED : (rp + 8 * (2 * Z.of_nat N2 - Z.of_nat da - Z.of_nat db) = rp + 8 * Z.of_nat (2 * N2 - da - db))%Z) by (clear - G; lia).
    rewrite ED.
    zstep.
    pose proof tRGR as RR'.
    assert (MS1 : (lo + RT_STACK <= SP + -160 /\ SP + -160 + 16 <= USTACK_TOP /\ (SP + -160) mod 16 = 0)%Z).
    { pose proof SPT16 as S1. pose proof SP16 as S2. unfold RT_STACK.
      split; [clear - G; lia|]. split; [clear - S1; lia|]. clear - S2. Z.div_mod_to_equations. lia. }
    destruct MS1 as (MS1 & MS2 & MS3).
    eapply call_memset0A with (L := repeat 0%Z (da + db)) (lo := lo) (SPz := (SP + -160)%Z) (D := (rp + 8 * Z.of_nat (2 * N2 - da - db))%Z) (bd := bR);
      [ exact tESP160 | tret_even | exact ST | exact MI | exact HEAP | exact CEIL | exact MS1 | exact MS2 | exact MS3 | exact ETP
      | apply in_or_app; left; exact tINR | clear - RR' G; lia | rewrite repeat_length; clear - RR' G; lia | rewrite repeat_length; clear - G; lia
      | apply inr64_unsigned_lit; unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; clear - BR G; lia
      | reflexivity
      | rewrite repeat_length; apply inr64_unsigned_lit; unfold inr64; change (2 ^ 64)%Z with 18446744073709551616%Z; clear - G; lia | ].
    intros m3 w0 w1 w2 y1 y2 y3 y4 y5 y6 y7 w3 w4 w5 w6 F2 fc2 HEAPc AGc WMc MIc HZ STc.
    rewrite repeat_length in HZ.
    assert (I3 : KBS (FCELLS0 jb48) m3 (splice R1 (2 * N2 - da - db) (repeat 0%Z (da + db))) T).
    { eapply (KS KB_cps_R);
        [ reflexivity | exact I2 | exact HEAPc | exact AGc | exact WMc | exact MIc | exact STc
        | exact (limbs_repeat _ _ limb_0) | rewrite repeat_length; clear - G; lia | exact HZ ]. }
    clear LR LT ER ET HR HT HA HB WR WT FR ST MI MU WM HEAP HEAPc AGc WMc HZ MIc STc I2 MS1 MS2 MS3 RR' BR.
    zstep.
    eapply T_epi; [exact I3|]. rewrite ERES. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma T_entry : forall F fc,
    limbs R -> limbs T ->
    limbs_at bsegs m ap a -> limbs_at bsegs m bp b -> limbs_at bsegs m rp R -> limbs_at bsegs m tq T ->
    wr_at bsegs m rp (8 * Z.of_nat (length R)) -> wr_at bsegs m tq (8 * Z.of_nat (length T)) ->
    stk bsegs m lo SP -> mem_inv bsegs m -> AHEAP Σ OW LB m ->
    (N2 = 8%nat -> da = 0%nat -> db = 0%nat -> RES = (splice R 0 (mul_comba8 a b), T)) ->
    (~ (N2 = 8 /\ da = 0 /\ db = 0)%nat -> (Z.of_nat N2 <= 15)%Z ->
     RES = ((if (0 <? da + db)%nat then splice (splice R 0 (mul_normal a b)) (2 * N2 - da - db) (repeat 0%Z (da + db))
             else splice R 0 (mul_normal a b)), T)) ->
    ((16 <= Z.of_nat N2)%Z ->
     forall jb48 m1 x1 x5 x6 x7 x9 x11 x12 x13 x17 x21 x26 x28 x29 x30 x31,
       KBS (FCELLS0 jb48) m1 R T ->
       evt bsegs POST
         (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp x5 x6 x7 sp x9 (Z_to_bv 64 15) x11 x12 x13 (Z_to_bv 64 SHB) a2 a1 x17
                  a3 (Z_to_bv 64 (Z.of_nat hn)) a6 x21 (Z_to_bv 64 (Z.lor (bv_unsigned a5) (bv_unsigned a4))) a5 (Z_to_bv 64 (Z.of_nat hn - Z.of_nat da)) a4 x26
                  (Z_to_bv 64 (Z.of_nat hn - Z.of_nat db)) x28 x29 x30 x31)
             F (Z_to_bv 64 0x24d27c) fc None m1 (seg_rom bsegs))) ->
    evt bsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24d0d8) fc None m (seg_rom bsegs)).
  Proof.
    intros F fc LR LT RA RB RR RT' WR WT STK MI0 HEAP RES8 RESS KARA.
    pose proof tgeom as G. pose proof Hda as HDA. pose proof Hdb as HDB.
    pose proof (AH_shb _ _ _ _ HEAP) as [G1 G2]. unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in G1, G2.
    pose proof (AH_ceil _ _ _ _ HEAP) as (_ & CSH & _).
    assert (LOHI : (17594333495296 <= lo)%Z) by (clear - CSH CEIL; unfold SHHI in CSH; lia).
    assert (LO1 : (lo <= SP - 160)%Z) by (clear - G; lia).
    carve_frame 160%nat STK.
    pose proof (munch_refl [(SP + -160, SP + -160 + 160)]%Z m) as MUF. pose proof (wmono_refl bsegs m) as WMF.
    assert (I0 : KBS [CB 160 junk] m R T).
    { unfold KB. split; [exact LR|]. split; [exact LT|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact RR|]. split; [exact RT'|]. split; [exact RA|]. split; [exact RB|]. split; [exact WR|]. split; [exact WT|].
      split; [exact FR|]. split; [exact STK|]. split; [exact MI0|]. split; [exact HEAP|].
      split; [|exact WMF]. unfold KAG. intros x _. reflexivity. }
    clear RA RB RR RT' WR WT HEAP CSH.
    assert (A3' : bv_unsigned a3 = (2 * Z.of_nat hn)%Z) by (rewrite A3, EN2h; clear; lia).
    assert (HN : (1 <= Z.of_nat hn <= 33554432)%Z) by (pose proof EN2h as E; clear - G E; lia).
    do 20 zstep. rewrite A3', ?land_m64, half_n2 by (clear - HN; lia).
    do 2 zstep.
    setreg 24%Z (Z_to_bv 64 (Z.of_nat hn - Z.of_nat da)) ltac:(rewrite A4; f_equal; symmetry; apply addw_dn; [exact HDA | clear - HN; lia]).
    setreg 11%Z (Z_to_bv 64 (Z.of_nat hn - Z.of_nat da)) ltac:(rewrite A4; apply Z_to_bv_eqm; clear - HDA; wnorm).
    zstep.
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    do 3 zstep.
    setreg 27%Z (Z_to_bv 64 (Z.of_nat hn - Z.of_nat db)) ltac:(rewrite A5; f_equal; symmetry; apply addw_dn; [exact HDB | clear - HN; lia]).
    setreg 10%Z (Z_to_bv 64 (Z.of_nat hn - Z.of_nat db)) ltac:(rewrite A5; apply Z_to_bv_eqm; clear - HDB; wnorm).
    chk ltac:(fun C => first [ (clear - C; lia) | (apply C; f_equal; clear; lia) ]).
    do 8 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (KS KB_frame _ _ m mm R T I0 MUF WMF MI0 STK FR) as I end.
    clear I0 MUF WMF G1 G2.
    eassert (CONT : ~ (N2 = 8 /\ da = 0 /\ db = 0)%nat -> _); cycle 1.
    { zstep. if_cases K8; zify_cond K8.
      { apply CONT. intros (E & _). clear - E K8 A3. lia. }
      zstep. if_cases K0; zify_cond K0.
      { apply CONT. intros (_ & Ea & Eb). apply K0. rewrite A4, A5. apply lor_neg_zero; [exact HDA | exact HDB | split; assumption]. }
      assert (E8 : N2 = 8%nat) by (clear - K8 A3; lia).
      assert (Ed : (da = 0 /\ db = 0)%nat) by (rewrite A4, A5 in K0; apply lor_neg_zero in K0; [exact K0 | exact HDA | exact HDB]).
      destruct Ed as (Eda & Edb).
      eapply T_comba; [exact I | exact E8 | exact Eda | exact Edb | exact (RES8 E8 Eda Edb)]. }
    intros NC.
    do 2 zstep.
    assert (L15 : (bv_unsigned (Z_to_bv 64 15) < 9223372036854775808)%Z) by (vm_compute; reflexivity).
    assert (L3 : (bv_unsigned a3 < 9223372036854775808)%Z) by (rewrite A3; clear - G; lia).
    rewrite (W_mul_normal.lts_words_small (Z_to_bv 64 15) a3 L15 L3). clear L15 L3.
    rewrite A3. if_cases K16; zify_cond K16.
    { eapply KARA; [clear - K16; lia | exact I]. }
    eapply T_small; [exact I | clear - K16; lia | apply RESS; [exact NC | clear - K16; lia]].
  Qed.
End Top.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Main.
  Context {AR : ARun}.
  Local Notation RT := (@ar_RT AR).
  Local Notation PMc := (@ar_PMc AR).
  Local Notation ACEIL := (@BnHeapA.ACEIL AR).
  Local Notation AHEAP := (@BnHeapA.AHEAP AR).
  Variable CS8 : Z.
  Hypothesis CS8_0 : (0 <= CS8)%Z.
  Hypothesis comba8_ok : comba8_aspec CS8.
  Hypothesis sub_part_ok : sub_part_words_bspec.
  Hypothesis mul_normal_ok : mul_normal_bspec.

  Lemma rec_body : forall k, (forall k', k = S k' -> rec_spec_atA CS8 k') -> rec_spec_atA CS8 k.
  Proof.
    intros k IHk. unfold rec_spec_atA.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ OW LB bR bT bA bB a b da db R T lo
           LA LB' LR LT Hk Hda Hdb HLA HLB HLR HLT A3 A4 A5 RA RB RR RT WR WT DRA DRB DTA DTB DRT STK LO SEPR SEPT SEPA SEPB MI0
           HEAP KBL CEIL SPT16 SP16 ETP UB.
    remember (Nat.pow 2 k) as N2 eqn:EN2.
    assert (HN2 : (2 <= Z.of_nat N2 <= 67108864)%Z) by (subst N2; apply W_mul_recursive.pow2_Z_bounds; exact Hk).
    destruct k as [|k']; [exfalso; clear - Hk; lia|].
    remember (Nat.pow 2 k') as n eqn:En.
    assert (EN : N2 = (2 * n)%nat) by (rewrite EN2, En; cbn [Nat.pow]; clear; lia).
    remember (rec_stackA CS8 (S k') - 160)%Z as SK eqn:ESK.
    assert (HSK : (65536 <= SK /\ CS8 <= SK)%Z) by (subst SK; unfold rec_stackA; clear - CS8_0; lia).
    assert (ERS : rec_stackA CS8 (S k') = (160 + SK)%Z) by (subst SK; clear; lia).
    rewrite ERS in LO, SEPR, SEPT, SEPA, SEPB.
    replace (bv_unsigned sp - (160 + SK))%Z with (bv_unsigned sp - 160 - SK)%Z in LO by (clear; lia).
    replace (bv_unsigned sp - (160 + SK))%Z with (bv_unsigned sp - 160 - SK)%Z in SEPR by (clear; lia).
    replace (bv_unsigned sp - (160 + SK))%Z with (bv_unsigned sp - 160 - SK)%Z in SEPT by (clear; lia).
    replace (bv_unsigned sp - (160 + SK))%Z with (bv_unsigned sp - 160 - SK)%Z in SEPA by (clear; lia).
    replace (bv_unsigned sp - (160 + SK))%Z with (bv_unsigned sp - 160 - SK)%Z in SEPB by (clear; lia).
    pose proof (proj1 STK) as LO0.
    assert (UBS : (0 < bv_unsigned a0 /\ bv_unsigned a0 mod 8 = 0 /\ 0 < bv_unsigned a1 /\ bv_unsigned a1 mod 8 = 0 /\
                   0 < bv_unsigned a2 /\ bv_unsigned a2 mod 8 = 0 /\ 0 < bv_unsigned a6 /\ bv_unsigned a6 mod 8 = 0)%Z).
    { destruct UB as (U1 & U2 & U3 & U4). pose proof (U1 ltac:(lia)). pose proof (U2 ltac:(lia)). pose proof (U3 ltac:(lia)). pose proof (U4 ltac:(lia)). tauto. }
    assert (PRE : top_preA CS8 N2 da db (length a) (length b) (length R) (length T) SK (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1)
                           (bv_unsigned a2) (bv_unsigned sp) lo).
    { unfold top_preA.
      split; [exact HN2|]. split; [exact Hda|]. split; [exact Hdb|]. split; [exact HLA|]. split; [exact HLB|]. split; [exact HLR|]. split; [exact HSK|].
      split; [exact DRA|]. split; [exact DRB|]. split; [exact DTA|]. split; [exact DTB|]. split; [exact DRT|].
      split; [exact SEPR|]. split; [exact SEPT|]. split; [exact SEPA|]. split; [exact SEPB|]. split; [exact LO|]. split; [exact LO0 | exact UBS]. }
    apply cps_from_evt'.
    eapply (T_entry CS8 CS8_0 comba8_ok mul_normal_ok) with (N2 := N2) (SK := SK) (da := da) (db := db) (bR := bR) (bT := bT) (bA := bA) (bB := bB) (hn := n);
      [ exact PRE | exact KBL | exact CEIL | exact SPT16 | exact SP16 | exact ETP | exact LA | exact LB' | exact A3 | exact A4 | exact A5 | exact EN
      | exact LR | exact LT | exact RA | exact RB | exact RR | exact RT | exact WR | exact WT | exact STK | exact MI0 | exact HEAP | | | ].
    - (* [comment removed for export] *)
      intros E8 Eda Edb. rewrite Eda, Edb. rewrite mul_recursive_comba by (rewrite <- EN2; exact E8).
      rewrite !firstn_all2 by (clear - HLA HLB E8 Eda Edb; lia). reflexivity.
    - (* [comment removed for export] *)
      intros NC K16. rewrite mul_recursive_small.
      + cbv zeta. rewrite <- EN2. rewrite !firstn_all2 by (clear - HLA HLB; lia). reflexivity.
      + rewrite <- EN2. clear - K16. lia.
      + rewrite <- EN2. destruct (Nat.eqb_spec N2 8) as [E1|_]; [|reflexivity].
        destruct (Nat.eqb_spec da 0) as [E2|_]; [|reflexivity]. destruct (Nat.eqb_spec db 0) as [E3|_]; [|reflexivity].
        exfalso. apply NC. repeat split; assumption.
    - (* [comment removed for export] *)
      intros K16 jb48 m1 x1 x5 x6 x7 x9 x11 x12 x13 x17 x21 x26 x28 x29 x30 x31 I.
      assert (ELR : length R = (4 * n)%nat) by (clear - HLR EN; lia).
      assert (ESK' : SK = rec_stackA CS8 k').
      { clear - ESK. unfold rec_stackA in *. rewrite !Nat2Z.inj_succ in *. lia. }
      assert (KPRE : kara_preA CS8 k' n da db (length a) (length b) (length T) SK (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1)
                              (bv_unsigned a2) (bv_unsigned sp) lo).
      { unfold kara_preA. rewrite <- ELR.
        assert (Hk1 : (1 <= k')%nat) by (destruct k' as [|k'']; [cbn in En; exfalso; clear - En EN K16; lia | clear; lia]).
        split; [exact En|]. split; [clear - Hk Hk1; lia|]. split; [clear - K16 EN; lia|]. split; [clear - HN2 EN; lia|].
        split; [exact Hda|]. split; [exact Hdb|]. split; [clear - HLA EN; lia|]. split; [clear - HLB EN; lia|].
        split. { rewrite scratch_rec_S in HLT by (rewrite <- EN2; clear - K16; lia). rewrite <- EN2 in HLT. clear - HLT EN ELR. lia. }
        split; [exact ESK'|].
        split; [exact DRA|]. split; [exact DRB|]. split; [exact DTA|]. split; [exact DTB|]. split; [exact DRT|].
        split; [exact SEPR|]. split; [exact SEPT|]. split; [exact SEPA|]. split; [exact SEPB|].
        split; [exact LO |]. split; [exact LO0 | exact UBS]. }
      assert (KBL' : kara_blocks OW LB bR bT bA bB (bv_unsigned a0) (bv_unsigned a6) (bv_unsigned a1) (bv_unsigned a2) (4 * n) (length T) (length a) (length b))
        by (rewrite <- ELR; exact KBL).
      rewrite ELR in I. rewrite ELR.
      eapply (B_body CS8 CS8_0 comba8_ok sub_part_ok k' (IHk k' eq_refl)) with (n := n) (nT := length T) (SK := SK) (da := da) (db := db);
        [ exact KPRE | exact KBL' | exact CEIL | exact SPT16 | exact SP16 | exact ETP | exact LA | exact LB' | rewrite A3, EN; clear; lia | exact A4 | exact A5
        | exact I | ].
      rewrite En. apply rec_staged; try assumption; rewrite <- ?EN2; try assumption.
      clear - K16. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem bn_mul_recursive_aspec : forall k, rec_spec_atA CS8 k.
  Proof.
    induction k as [|k IH]; apply rec_body; intros k' E; [discriminate|]. injection E as <-. exact IH.
  Qed.
End Main.
