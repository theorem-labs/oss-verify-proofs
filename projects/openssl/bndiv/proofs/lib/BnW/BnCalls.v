(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import F_memset.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnLoop W_add_words W_sub_words W_cmp_words W_cmp_part_words
  W_sub_part_words W_mul_normal.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma le8_zero : le8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
Proof. vm_compute. reflexivity. Qed.

Lemma lbytes_repeat0 : forall c, lbytes (repeat 0%Z c) = repeat (Z_to_bv 8 0) (8 * c).
Proof.
  induction c as [|c IH]; [reflexivity|].
  cbn [repeat]. rewrite lbytes_cons, IH, le8_zero.
  replace (8 * S c)%nat with (8 + 8 * c)%nat by lia. rewrite repeat_app. reflexivity.
Qed.

(* [comment removed for export] *)
Definition comba8_spec (CS8 : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (lo : Z),
    limbs a -> limbs b -> length a = 8%nat -> length b = 8%nat ->
    limbs_at psegs m (bv_unsigned a1) a -> limbs_at psegs m (bv_unsigned a2) b ->
    wr_at psegs m (bv_unsigned a0) 128 ->
    (bv_unsigned a0 + 128 <= bv_unsigned a1 \/ bv_unsigned a1 + 64 <= bv_unsigned a0)%Z ->
    (bv_unsigned a0 + 128 <= bv_unsigned a2 \/ bv_unsigned a2 + 64 <= bv_unsigned a0)%Z ->
    stk psegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - CS8)%Z ->
    (bv_unsigned a0 + 128 <= bv_unsigned sp - CS8 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a1 + 64 <= bv_unsigned sp - CS8 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    (bv_unsigned a2 + 64 <= bv_unsigned sp - CS8 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
    mem_inv psegs m ->
    evt psegs (vl_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) 16 CS8 (mul_comba8 a b) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xf70a0) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition memset0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (w0 : word) (D : Z) (cnt : nat) (lo SPz : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 w0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch [(D, D + 8 * Z.of_nat cnt)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ limbs_at psegs m' D (repeat 0%Z cnt) /\ stk psegs m' lo SPz.

Lemma memset0_limbs_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (L : list Z) (D lo SPz : Z),
  bv_unsigned a0 = D -> bv_unsigned a1 = 0%Z -> bv_unsigned a2 = (8 * Z.of_nat (length L))%Z ->
  limbs_at psegs m D L -> wr_at psegs m D (8 * Z.of_nat (length L)) -> stk psegs m lo SPz -> mem_inv psegs m ->
  evt psegs (memset0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 D (length L) lo SPz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2769c4) fc None m (seg_rom psegs)).
Proof.
  intros until SPz. intros E0 E1 E2 HL WR STK MI0. subst D.
  assert (En : Z.to_nat (bv_unsigned a2) = (8 * length L)%nat) by (rewrite E2; lia).
  eapply evt_mono.
  { eapply (memset_spec ra sp) with (junk := lbytes L); [|exact MI0].
    rewrite En. split; [split|].
    - cbn. split; [apply lbytes_length | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HL.
    - cbn [cells_size csize]. rewrite Nat.add_0_r. replace (Z.of_nat (8 * length L)) with (8 * Z.of_nat (length L))%Z by lia. exact WR. }
  intros ms' PO. unfold memset_post in PO.
  destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & RW).
  rewrite E1, E2, En in *. change (0 mod 256)%Z with 0%Z in RW.
  destruct RW as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r, <- lbytes_repeat0 in HB.
  exists u0, u1, u2, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, m2.
  split; [exact E|]. split; [exact MUc|]. split; [exact WMc|]. split; [exact MIc|]. split; [exact HB|].
  destruct STK as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. intros x Hx. destruct (S3 x Hx) as [Hw (bx & Hbx)].
  split; [apply WMc; exact Hw|].
  destruct (Z_lt_ge_dec x (bv_unsigned a0)) as [H1|H1]; [|destruct (Z_lt_ge_dec x (bv_unsigned a0 + 8 * Z.of_nat (length L))) as [H2|H2]].
  - exists bx. unfold mrd in *. rewrite MUc; [exact Hbx|]. rewrite wa_unsigned by lia. cbn [outside]. lia.
  - destruct HB as (B1 & B2 & B3).
    assert (Hi : (Z.to_nat (x - bv_unsigned a0) < length (lbytes (repeat 0%Z (length L))))%nat).
    { rewrite lbytes_length, repeat_length. lia. }
    specialize (B3 (Z.to_nat (x - bv_unsigned a0)) Hi).
    replace (bv_unsigned a0 + Z.of_nat (Z.to_nat (x - bv_unsigned a0)))%Z with x in B3 by lia.
    destruct (nth_error (lbytes (repeat 0%Z (length L))) (Z.to_nat (x - bv_unsigned a0))) as [bb|] eqn:EN;
      [exists bb; exact B3 | apply nth_error_None in EN; lia].
  - exists bx. unfold mrd in *. rewrite MUc; [exact Hbx|]. rewrite wa_unsigned by lia. cbn [outside]. lia.
Qed.

Section Calls.
  Variable POST : machine_state -> Prop.
  Variables (wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo SPz RET : Z).
  Hypothesis ESP : bv_unsigned wsp = SPz.
  Hypothesis ERET : ret_pc (Z_to_bv 64 RET) = Z_to_bv 64 RET.
  Hypothesis STK : stk psegs m lo SPz.
  Hypothesis MI0 : mem_inv psegs m.

  Notation ENTRY pc := (MS (mkR (Z_to_bv 64 RET) wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 pc) fc None m (seg_rom psegs)).
  Notation AFTER m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 :=
    (MS (mkR (Z_to_bv 64 RET) wsp gp tp u0 u1 u2 s0 s1 v0 v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 RET) fc None m2 (seg_rom psegs)).

  (* [comment removed for export] *)
  Lemma call_add_words : forall (a b : list Z) (RP AP BP : Z),
    limbs a -> limbs b -> length b = length a -> (Z.of_nat (length a) < 2^31)%Z ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP -> bv_unsigned w3 = Z.of_nat (length a) ->
    limbs_at psegs m AP a -> limbs_at psegs m BP b -> wr_at psegs m RP (8 * Z.of_nat (length a)) ->
    alias_ok RP AP (Z.of_nat (length a)) -> alias_ok RP BP (Z.of_nat (length a)) ->
    (lo <= SPz - 16)%Z ->
    (RP + 8 * Z.of_nat (length a) <= SPz - 16 \/ SPz <= RP)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - 16 \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length a) <= SPz - 16 \/ SPz <= BP)%Z ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * Z.of_nat (length a)); (SPz - 16, SPz)]%Z m m2 -> wmono psegs m m2 -> mem_inv psegs m2 ->
       limbs_at psegs m2 RP (fst (add_words a b)) -> stk psegs m2 lo SPz ->
       evt psegs POST (AFTER m2 u0 u1 u2 (Z_to_bv 64 (snd (add_words a b))) v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt psegs POST (ENTRY 0xf6e68).
  Proof using ESP ERET STK MI0.
    intros a b RP AP BP LA LB LEN N31 E0 E1 E2 E3 RA RB WR ALA ALB LO SEPR SEPA SEPB K.
    subst RP AP BP SPz.
    eapply evt_cut; [ eapply bn_add_words_spec with (a := a) (b := b) (lo := lo); eassumption | ].
    intros ms' PO. unfold aw_post, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma call_sub_words : forall (a b : list Z) (RP AP BP : Z),
    limbs a -> limbs b -> length b = length a -> (Z.of_nat (length a) < 2^31)%Z ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP -> bv_unsigned w3 = Z.of_nat (length a) ->
    limbs_at psegs m AP a -> limbs_at psegs m BP b -> wr_at psegs m RP (8 * Z.of_nat (length a)) ->
    alias_ok RP AP (Z.of_nat (length a)) -> alias_ok RP BP (Z.of_nat (length a)) ->
    (lo <= SPz - 16)%Z ->
    (RP + 8 * Z.of_nat (length a) <= SPz - 16 \/ SPz <= RP)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - 16 \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length a) <= SPz - 16 \/ SPz <= BP)%Z ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * Z.of_nat (length a)); (SPz - 16, SPz)]%Z m m2 -> wmono psegs m m2 -> mem_inv psegs m2 ->
       limbs_at psegs m2 RP (fst (sub_words a b)) -> stk psegs m2 lo SPz ->
       evt psegs POST (AFTER m2 u0 u1 u2 (Z_to_bv 64 (snd (sub_words a b))) v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt psegs POST (ENTRY 0xf6f80).
  Proof using ESP ERET STK MI0.
    intros a b RP AP BP LA LB LEN N31 E0 E1 E2 E3 RA RB WR ALA ALB LO SEPR SEPA SEPB K.
    subst RP AP BP SPz.
    eapply evt_cut; [ eapply bn_sub_words_spec with (a := a) (b := b) (lo := lo); eassumption | ].
    intros ms' PO. unfold sw_post, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma call_cmp_part_words : forall (a b : list Z) (cl da db : nat) (AP BP : Z),
    limbs a -> limbs b -> length a = (cl + da)%nat -> length b = (cl + db)%nat -> (da = 0 \/ db = 0)%nat ->
    (Z.of_nat (cl + da + db) < 2147483648)%Z ->
    bv_unsigned w0 = AP -> bv_unsigned w1 = BP -> bv_unsigned w2 = Z.of_nat cl -> w3 = Z_to_bv 64 (Z.of_nat da - Z.of_nat db) ->
    limbs_at psegs m AP a -> limbs_at psegs m BP b ->
    (lo <= SPz - 16)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - 16 \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length b) <= SPz - 16 \/ SPz <= BP)%Z ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(SPz - 16, SPz)]%Z m m2 -> wmono psegs m m2 -> mem_inv psegs m2 -> stk psegs m2 lo SPz ->
       evt psegs POST (AFTER m2 u0 u1 u2 (Z_to_bv 64 (cmp_part_words a b cl)) v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt psegs POST (ENTRY 0xdeadc).
  Proof using ESP ERET STK MI0.
    intros a b cl da db AP BP LA LB HLA HLB DAB N31 E0 E1 E2 E3 RA RB LO SEPA SEPB K.
    subst AP BP SPz.
    eapply evt_cut; [ eapply bn_cmp_part_words_spec with (a := a) (b := b) (cl := cl) (da := da) (db := db) (lo := lo); eassumption | ].
    intros ms' PO. unfold ro_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma call_sub_part_words : forall (a b : list Z) (cl da db : nat) (RP AP BP : Z),
    limbs a -> limbs b -> length a = (cl + da)%nat -> length b = (cl + db)%nat -> (da = 0 \/ db = 0)%nat ->
    (Z.of_nat (cl + da + db) < 2147483648)%Z ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP -> bv_unsigned w3 = Z.of_nat cl ->
    w4 = Z_to_bv 64 (Z.of_nat da - Z.of_nat db) ->
    limbs_at psegs m AP a -> limbs_at psegs m BP b -> wr_at psegs m RP (8 * Z.of_nat (cl + da + db)) ->
    (RP = AP \/ RP + 8 * Z.of_nat (cl + da + db) <= AP \/ AP + 8 * Z.of_nat (length a) <= RP)%Z ->
    (RP = BP \/ RP + 8 * Z.of_nat (cl + da + db) <= BP \/ BP + 8 * Z.of_nat (length b) <= RP)%Z ->
    (lo <= SPz - 80)%Z ->
    (RP + 8 * Z.of_nat (cl + da + db) <= SPz - 80 \/ SPz <= RP)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - 80 \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length b) <= SPz - 80 \/ SPz <= BP)%Z ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * Z.of_nat (cl + da + db)); (SPz - 80, SPz)]%Z m m2 -> wmono psegs m m2 -> mem_inv psegs m2 ->
       limbs_at psegs m2 RP (fst (sub_part_words a b cl)) -> stk psegs m2 lo SPz ->
       evt psegs POST (AFTER m2 u0 u1 u2 (Z_to_bv 64 (snd (sub_part_words a b cl))) v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt psegs POST (ENTRY 0x1097f4).
  Proof using ESP ERET STK MI0.
    intros a b cl da db RP AP BP LA LB HLA HLB DAB N31 E0 E1 E2 E3 E4 RA RB WR ALA ALB LO SEPR SEPA SEPB K.
    subst RP AP BP SPz.
    eapply evt_cut; [ eapply bn_sub_part_words_spec with (a := a) (b := b) (cl := cl) (da := da) (db := db) (lo := lo); eassumption | ].
    intros ms' PO. unfold spw_post, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma call_mul_normal : forall (a b : list Z) (RP AP BP : Z),
    limbs a -> limbs b -> (Z.of_nat (length a) + Z.of_nat (length b) < 2147483648)%Z ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = Z.of_nat (length a) -> bv_unsigned w3 = BP ->
    bv_unsigned w4 = Z.of_nat (length b) ->
    limbs_at psegs m AP a -> limbs_at psegs m BP b -> wr_at psegs m RP (8 * (Z.of_nat (length a) + Z.of_nat (length b))) ->
    (RP + 8 * (Z.of_nat (length a) + Z.of_nat (length b)) <= AP \/ AP + 8 * Z.of_nat (length a) <= RP)%Z ->
    (RP + 8 * (Z.of_nat (length a) + Z.of_nat (length b)) <= BP \/ BP + 8 * Z.of_nat (length b) <= RP)%Z ->
    (lo <= SPz - 144)%Z ->
    (RP + 8 * (Z.of_nat (length a) + Z.of_nat (length b)) <= SPz - 144 \/ SPz <= RP)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - 144 \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length b) <= SPz - 144 \/ SPz <= BP)%Z ->
    (forall m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * (Z.of_nat (length a) + Z.of_nat (length b))); (SPz - 144, SPz)]%Z m m2 -> wmono psegs m m2 -> mem_inv psegs m2 ->
       limbs_at psegs m2 RP (mul_normal a b) -> stk psegs m2 lo SPz ->
       evt psegs POST (AFTER m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt psegs POST (ENTRY 0x109f10).
  Proof using ESP ERET STK MI0.
    intros a b RP AP BP LA LB N31 E0 E1 E2 E3 E4 RA RB WR DRA DRB LO SEPR SEPA SEPB K.
    subst RP AP BP SPz.
    eapply evt_cut; [ eapply bn_mul_normal_spec with (a := a) (b := b) (lo := lo); eassumption | ].
    intros ms' PO. unfold vl_post in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma call_comba8 : forall (CS8 : Z) (a b : list Z) (RP AP BP : Z),
    comba8_spec CS8 ->
    limbs a -> limbs b -> length a = 8%nat -> length b = 8%nat ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP ->
    limbs_at psegs m AP a -> limbs_at psegs m BP b -> wr_at psegs m RP 128 ->
    (RP + 128 <= AP \/ AP + 64 <= RP)%Z -> (RP + 128 <= BP \/ BP + 64 <= RP)%Z ->
    (lo <= SPz - CS8)%Z ->
    (RP + 128 <= SPz - CS8 \/ SPz <= RP)%Z -> (AP + 64 <= SPz - CS8 \/ SPz <= AP)%Z -> (BP + 64 <= SPz - CS8 \/ SPz <= BP)%Z ->
    (forall m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * 16); (SPz - CS8, SPz)]%Z m m2 -> wmono psegs m m2 -> mem_inv psegs m2 ->
       limbs_at psegs m2 RP (mul_comba8 a b) -> stk psegs m2 lo SPz ->
       evt psegs POST (AFTER m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt psegs POST (ENTRY 0xf70a0).
  Proof using ESP ERET STK MI0.
    intros CS8 a b RP AP BP C8 LA LB HLA HLB E0 E1 E2 RA RB WR DRA DRB LO SEPR SEPA SEPB K.
    subst RP AP BP SPz.
    eapply evt_cut; [ eapply C8 with (a := a) (b := b) (lo := lo); eassumption | ].
    intros ms' PO. unfold vl_post in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma call_memset0 : forall (L : list Z) (D : Z),
    bv_unsigned w0 = D -> bv_unsigned w1 = 0%Z -> bv_unsigned w2 = (8 * Z.of_nat (length L))%Z ->
    limbs_at psegs m D L -> wr_at psegs m D (8 * Z.of_nat (length L)) ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(D, D + 8 * Z.of_nat (length L))]%Z m m2 -> wmono psegs m m2 -> mem_inv psegs m2 ->
       limbs_at psegs m2 D (repeat 0%Z (length L)) -> stk psegs m2 lo SPz ->
       evt psegs POST (AFTER m2 u0 u1 u2 w0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt psegs POST (ENTRY 0x2769c4).
  Proof using ESP ERET STK MI0.
    intros L D E0 E1 E2 HL WR K.
    eapply evt_cut; [ eapply memset0_limbs_spec with (L := L) (D := D) (lo := lo) (SPz := SPz); eassumption | ].
    intros ms' PO. unfold memset0_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HB & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.
End Calls.
