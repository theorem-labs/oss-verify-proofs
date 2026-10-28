(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import F_memset.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnLoop.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnW Require Import W_cmp_words W_mul_normal BnCalls.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require Import WU_add_words WU_sub_words.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition comba8_uspec (CS8 : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (lo : Z),
    limbs a -> limbs b -> length a = 8%nat -> length b = 8%nat ->
    limbs_at bgusegs m (bv_unsigned a1) a -> limbs_at bgusegs m (bv_unsigned a2) b ->
    wr_at bgusegs m (bv_unsigned a0) 128 ->
    (bv_unsigned a0 + 128 <= bv_unsigned a1 \/ bv_unsigned a1 + 64 <= bv_unsigned a0)%Z ->
    (bv_unsigned a0 + 128 <= bv_unsigned a2 \/ bv_unsigned a2 + 64 <= bv_unsigned a0)%Z ->
    stk bgusegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - CS8)%Z ->
    (bv_unsigned a0 + 128 <= bv_unsigned sp - CS8 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a1 + 64 <= bv_unsigned sp - CS8 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    (bv_unsigned a2 + 64 <= bv_unsigned sp - CS8 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
    mem_inv bgusegs m ->
    ub_ptr_ok 1 (bv_unsigned a0) -> ub_ptr_ok 1 (bv_unsigned a1) -> ub_ptr_ok 1 (bv_unsigned a2) ->
    evt bgusegs (vl_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) 16 CS8 (mul_comba8 a b) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1038ec) fc None m (seg_rom bgusegs)).

Definition cmp_part_words_uspec (FS : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (cl da db : nat) (lo : Z),
    limbs a -> limbs b -> length a = (cl + da)%nat -> length b = (cl + db)%nat -> (da = 0 \/ db = 0)%nat ->
    (Z.of_nat (cl + da + db) < 2147483648)%Z ->
    bv_unsigned a2 = Z.of_nat cl -> a3 = Z_to_bv 64 (Z.of_nat da - Z.of_nat db) ->
    limbs_at bgusegs m (bv_unsigned a0) a -> limbs_at bgusegs m (bv_unsigned a1) b ->
    stk bgusegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FS)%Z ->
    (bv_unsigned a0 + 8 * Z.of_nat (length a) <= bv_unsigned sp - FS \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a1 + 8 * Z.of_nat (length b) <= bv_unsigned sp - FS \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    mem_inv bgusegs m ->
    ub_ptr_ok 1 (bv_unsigned a0) -> ub_ptr_ok 1 (bv_unsigned a1) ->
    evt bgusegs (ro_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FS (cmp_part_words a b cl) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xff608) fc None m (seg_rom bgusegs)).

Definition sub_part_words_uspec (FS : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (cl da db : nat) (lo : Z),
    limbs a -> limbs b -> length a = (cl + da)%nat -> length b = (cl + db)%nat -> (da = 0 \/ db = 0)%nat ->
    (Z.of_nat (cl + da + db) < 2147483648)%Z ->
    bv_unsigned a3 = Z.of_nat cl -> a4 = Z_to_bv 64 (Z.of_nat da - Z.of_nat db) ->
    limbs_at bgusegs m (bv_unsigned a1) a -> limbs_at bgusegs m (bv_unsigned a2) b ->
    wr_at bgusegs m (bv_unsigned a0) (8 * Z.of_nat (cl + da + db)) ->
    (bv_unsigned a0 = bv_unsigned a1 \/ bv_unsigned a0 + 8 * Z.of_nat (cl + da + db) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a0)%Z ->
    (bv_unsigned a0 = bv_unsigned a2 \/ bv_unsigned a0 + 8 * Z.of_nat (cl + da + db) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned a0)%Z ->
    stk bgusegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FS)%Z ->
    (bv_unsigned a0 + 8 * Z.of_nat (cl + da + db) <= bv_unsigned sp - FS \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned sp - FS \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    (bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned sp - FS \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
    mem_inv bgusegs m ->
    ub_ptr_ok 1 (bv_unsigned a0) -> ub_ptr_ok 1 (bv_unsigned a1) -> ub_ptr_ok 1 (bv_unsigned a2) ->
    evt bgusegs (wl_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) (Z.of_nat (cl + da + db)) FS
                 (fst (sub_part_words a b cl)) (snd (sub_part_words a b cl)) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1010b8) fc None m (seg_rom bgusegs)).

Definition mul_normal_uspec (FS : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (lo : Z),
    limbs a -> limbs b -> (Z.of_nat (length a) + Z.of_nat (length b) < 2147483648)%Z ->
    bv_unsigned a2 = Z.of_nat (length a) -> bv_unsigned a4 = Z.of_nat (length b) ->
    limbs_at bgusegs m (bv_unsigned a1) a -> limbs_at bgusegs m (bv_unsigned a3) b ->
    wr_at bgusegs m (bv_unsigned a0) (8 * (Z.of_nat (length a) + Z.of_nat (length b))) ->
    (bv_unsigned a0 + 8 * (Z.of_nat (length a) + Z.of_nat (length b)) <= bv_unsigned a1 \/ bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a0)%Z ->
    (bv_unsigned a0 + 8 * (Z.of_nat (length a) + Z.of_nat (length b)) <= bv_unsigned a3 \/ bv_unsigned a3 + 8 * Z.of_nat (length b) <= bv_unsigned a0)%Z ->
    stk bgusegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FS)%Z ->
    (bv_unsigned a0 + 8 * (Z.of_nat (length a) + Z.of_nat (length b)) <= bv_unsigned sp - FS \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned sp - FS \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    (bv_unsigned a3 + 8 * Z.of_nat (length b) <= bv_unsigned sp - FS \/ bv_unsigned sp <= bv_unsigned a3)%Z ->
    mem_inv bgusegs m ->
    ub_ptr_ok 1 (bv_unsigned a0) -> ub_ptr_ok 1 (bv_unsigned a1) -> ub_ptr_ok 1 (bv_unsigned a3) ->
    evt bgusegs (vl_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0)
                 (Z.of_nat (length a) + Z.of_nat (length b)) FS (mul_normal a b) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x101b9c) fc None m (seg_rom bgusegs)).

(* [comment removed for export] *)
Definition umemset0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (w0 : word) (D : Z) (cnt : nat) (lo SPz : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 w0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bgusegs)
    /\ munch [(D, D + 8 * Z.of_nat cnt)]%Z m m' /\ wmono bgusegs m m' /\ mem_inv bgusegs m'
    /\ limbs_at bgusegs m' D (repeat 0%Z cnt) /\ stk bgusegs m' lo SPz.

Lemma umemset0_limbs_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (L : list Z) (D lo SPz : Z),
  bv_unsigned a0 = D -> bv_unsigned a1 = 0%Z -> bv_unsigned a2 = (8 * Z.of_nat (length L))%Z ->
  limbs_at bgusegs m D L -> wr_at bgusegs m D (8 * Z.of_nat (length L)) -> stk bgusegs m lo SPz -> mem_inv bgusegs m ->
  evt bgusegs (umemset0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 D (length L) lo SPz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2bbae4) fc None m (seg_rom bgusegs)).
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

Section CallsU.
  Variable POST : machine_state -> Prop.
  Variables (wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo SPz RET : Z).
  Hypothesis ESP : bv_unsigned wsp = SPz.
  Hypothesis ERET : ret_pc (Z_to_bv 64 RET) = Z_to_bv 64 RET.
  Hypothesis STK : stk bgusegs m lo SPz.
  Hypothesis MI0 : mem_inv bgusegs m.

  Notation ENTRY pc := (MS (mkR (Z_to_bv 64 RET) wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 pc) fc None m (seg_rom bgusegs)).
  Notation AFTER m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 :=
    (MS (mkR (Z_to_bv 64 RET) wsp gp tp u0 u1 u2 s0 s1 v0 v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 RET) fc None m2 (seg_rom bgusegs)).

  (* [comment removed for export] *)
  Lemma ucall_add_words : forall (a b : list Z) (RP AP BP : Z),
    limbs a -> limbs b -> length b = length a -> (Z.of_nat (length a) < 2^31)%Z ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP -> bv_unsigned w3 = Z.of_nat (length a) ->
    limbs_at bgusegs m AP a -> limbs_at bgusegs m BP b -> wr_at bgusegs m RP (8 * Z.of_nat (length a)) ->
    alias_ok RP AP (Z.of_nat (length a)) -> alias_ok RP BP (Z.of_nat (length a)) ->
    (lo <= SPz - 80)%Z ->
    (RP + 8 * Z.of_nat (length a) <= SPz - 80 \/ SPz <= RP)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - 80 \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length a) <= SPz - 80 \/ SPz <= BP)%Z ->
    ub_ptr_ok (Z.of_nat (length a)) RP -> ub_ptr_ok (Z.of_nat (length a)) AP -> ub_ptr_ok (Z.of_nat (length a)) BP ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * Z.of_nat (length a)); (SPz - 80, SPz)]%Z m m2 -> wmono bgusegs m m2 -> mem_inv bgusegs m2 ->
       limbs_at bgusegs m2 RP (fst (add_words a b)) -> stk bgusegs m2 lo SPz ->
       evt bgusegs POST (AFTER m2 u0 u1 u2 (Z_to_bv 64 (snd (add_words a b))) v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt bgusegs POST (ENTRY 0x103454).
  Proof using ESP ERET STK MI0.
    intros a b RP AP BP LA LB LEN N31 E0 E1 E2 E3 RA RB WR ALA ALB LO SEPR SEPA SEPB UBR UBA UBB K.
    subst RP AP BP SPz.
    eapply evt_cut; [ eapply bn_add_words_uspec with (a := a) (b := b) (lo := lo); eassumption | ].
    intros ms' PO. unfold aw_upost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma ucall_sub_words : forall (a b : list Z) (RP AP BP : Z),
    limbs a -> limbs b -> length b = length a -> (Z.of_nat (length a) < 2^31)%Z ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP -> bv_unsigned w3 = Z.of_nat (length a) ->
    limbs_at bgusegs m AP a -> limbs_at bgusegs m BP b -> wr_at bgusegs m RP (8 * Z.of_nat (length a)) ->
    alias_ok RP AP (Z.of_nat (length a)) -> alias_ok RP BP (Z.of_nat (length a)) ->
    (lo <= SPz - 80)%Z ->
    (RP + 8 * Z.of_nat (length a) <= SPz - 80 \/ SPz <= RP)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - 80 \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length a) <= SPz - 80 \/ SPz <= BP)%Z ->
    ub_ptr_ok (Z.of_nat (length a)) RP -> ub_ptr_ok (Z.of_nat (length a)) AP -> ub_ptr_ok (Z.of_nat (length a)) BP ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * Z.of_nat (length a)); (SPz - 80, SPz)]%Z m m2 -> wmono bgusegs m m2 -> mem_inv bgusegs m2 ->
       limbs_at bgusegs m2 RP (fst (sub_words a b)) -> stk bgusegs m2 lo SPz ->
       evt bgusegs POST (AFTER m2 u0 u1 u2 (Z_to_bv 64 (snd (sub_words a b))) v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt bgusegs POST (ENTRY 0x103698).
  Proof using ESP ERET STK MI0.
    intros a b RP AP BP LA LB LEN N31 E0 E1 E2 E3 RA RB WR ALA ALB LO SEPR SEPA SEPB UBR UBA UBB K.
    subst RP AP BP SPz.
    eapply evt_cut; [ eapply bn_sub_words_uspec with (a := a) (b := b) (lo := lo); eassumption | ].
    intros ms' PO. unfold sw_upost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma ucall_cmp_part_words : forall (FS : Z) (a b : list Z) (cl da db : nat) (AP BP : Z),
    cmp_part_words_uspec FS ->
    limbs a -> limbs b -> length a = (cl + da)%nat -> length b = (cl + db)%nat -> (da = 0 \/ db = 0)%nat ->
    (Z.of_nat (cl + da + db) < 2147483648)%Z ->
    bv_unsigned w0 = AP -> bv_unsigned w1 = BP -> bv_unsigned w2 = Z.of_nat cl -> w3 = Z_to_bv 64 (Z.of_nat da - Z.of_nat db) ->
    limbs_at bgusegs m AP a -> limbs_at bgusegs m BP b ->
    (lo <= SPz - FS)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - FS \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length b) <= SPz - FS \/ SPz <= BP)%Z ->
    ub_ptr_ok 1 AP -> ub_ptr_ok 1 BP ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(SPz - FS, SPz)]%Z m m2 -> wmono bgusegs m m2 -> mem_inv bgusegs m2 -> stk bgusegs m2 lo SPz ->
       evt bgusegs POST (AFTER m2 u0 u1 u2 (Z_to_bv 64 (cmp_part_words a b cl)) v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt bgusegs POST (ENTRY 0xff608).
  Proof using ESP ERET STK MI0.
    intros FS a b cl da db AP BP SPEC LA LB HLA HLB DAB N31 E0 E1 E2 E3 RA RB LO SEPA SEPB UBA UBB K.
    subst AP BP SPz.
    eapply evt_cut; [ eapply SPEC with (a := a) (b := b) (cl := cl) (da := da) (db := db) (lo := lo); eassumption | ].
    intros ms' PO. unfold ro_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma ucall_sub_part_words : forall (FS : Z) (a b : list Z) (cl da db : nat) (RP AP BP : Z),
    sub_part_words_uspec FS ->
    limbs a -> limbs b -> length a = (cl + da)%nat -> length b = (cl + db)%nat -> (da = 0 \/ db = 0)%nat ->
    (Z.of_nat (cl + da + db) < 2147483648)%Z ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP -> bv_unsigned w3 = Z.of_nat cl ->
    w4 = Z_to_bv 64 (Z.of_nat da - Z.of_nat db) ->
    limbs_at bgusegs m AP a -> limbs_at bgusegs m BP b -> wr_at bgusegs m RP (8 * Z.of_nat (cl + da + db)) ->
    (RP = AP \/ RP + 8 * Z.of_nat (cl + da + db) <= AP \/ AP + 8 * Z.of_nat (length a) <= RP)%Z ->
    (RP = BP \/ RP + 8 * Z.of_nat (cl + da + db) <= BP \/ BP + 8 * Z.of_nat (length b) <= RP)%Z ->
    (lo <= SPz - FS)%Z ->
    (RP + 8 * Z.of_nat (cl + da + db) <= SPz - FS \/ SPz <= RP)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - FS \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length b) <= SPz - FS \/ SPz <= BP)%Z ->
    ub_ptr_ok 1 RP -> ub_ptr_ok 1 AP -> ub_ptr_ok 1 BP ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * Z.of_nat (cl + da + db)); (SPz - FS, SPz)]%Z m m2 -> wmono bgusegs m m2 -> mem_inv bgusegs m2 ->
       limbs_at bgusegs m2 RP (fst (sub_part_words a b cl)) -> stk bgusegs m2 lo SPz ->
       evt bgusegs POST (AFTER m2 u0 u1 u2 (Z_to_bv 64 (snd (sub_part_words a b cl))) v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt bgusegs POST (ENTRY 0x1010b8).
  Proof using ESP ERET STK MI0.
    intros FS a b cl da db RP AP BP SPEC LA LB HLA HLB DAB N31 E0 E1 E2 E3 E4 RA RB WR ALA ALB LO SEPR SEPA SEPB UBR UBA UBB K.
    subst RP AP BP SPz.
    eapply evt_cut; [ eapply SPEC with (a := a) (b := b) (cl := cl) (da := da) (db := db) (lo := lo); eassumption | ].
    intros ms' PO. unfold wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma ucall_mul_normal : forall (FS : Z) (a b : list Z) (RP AP BP : Z),
    mul_normal_uspec FS ->
    limbs a -> limbs b -> (Z.of_nat (length a) + Z.of_nat (length b) < 2147483648)%Z ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = Z.of_nat (length a) -> bv_unsigned w3 = BP ->
    bv_unsigned w4 = Z.of_nat (length b) ->
    limbs_at bgusegs m AP a -> limbs_at bgusegs m BP b -> wr_at bgusegs m RP (8 * (Z.of_nat (length a) + Z.of_nat (length b))) ->
    (RP + 8 * (Z.of_nat (length a) + Z.of_nat (length b)) <= AP \/ AP + 8 * Z.of_nat (length a) <= RP)%Z ->
    (RP + 8 * (Z.of_nat (length a) + Z.of_nat (length b)) <= BP \/ BP + 8 * Z.of_nat (length b) <= RP)%Z ->
    (lo <= SPz - FS)%Z ->
    (RP + 8 * (Z.of_nat (length a) + Z.of_nat (length b)) <= SPz - FS \/ SPz <= RP)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - FS \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length b) <= SPz - FS \/ SPz <= BP)%Z ->
    ub_ptr_ok 1 RP -> ub_ptr_ok 1 AP -> ub_ptr_ok 1 BP ->
    (forall m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * (Z.of_nat (length a) + Z.of_nat (length b))); (SPz - FS, SPz)]%Z m m2 -> wmono bgusegs m m2 -> mem_inv bgusegs m2 ->
       limbs_at bgusegs m2 RP (mul_normal a b) -> stk bgusegs m2 lo SPz ->
       evt bgusegs POST (AFTER m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt bgusegs POST (ENTRY 0x101b9c).
  Proof using ESP ERET STK MI0.
    intros FS a b RP AP BP SPEC LA LB N31 E0 E1 E2 E3 E4 RA RB WR DRA DRB LO SEPR SEPA SEPB UBR UBA UBB K.
    subst RP AP BP SPz.
    eapply evt_cut; [ eapply SPEC with (a := a) (b := b) (lo := lo); eassumption | ].
    intros ms' PO. unfold vl_post in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma ucall_comba8 : forall (CS8 : Z) (a b : list Z) (RP AP BP : Z),
    comba8_uspec CS8 ->
    limbs a -> limbs b -> length a = 8%nat -> length b = 8%nat ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP ->
    limbs_at bgusegs m AP a -> limbs_at bgusegs m BP b -> wr_at bgusegs m RP 128 ->
    (RP + 128 <= AP \/ AP + 64 <= RP)%Z -> (RP + 128 <= BP \/ BP + 64 <= RP)%Z ->
    (lo <= SPz - CS8)%Z ->
    (RP + 128 <= SPz - CS8 \/ SPz <= RP)%Z -> (AP + 64 <= SPz - CS8 \/ SPz <= AP)%Z -> (BP + 64 <= SPz - CS8 \/ SPz <= BP)%Z ->
    ub_ptr_ok 1 RP -> ub_ptr_ok 1 AP -> ub_ptr_ok 1 BP ->
    (forall m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * 16); (SPz - CS8, SPz)]%Z m m2 -> wmono bgusegs m m2 -> mem_inv bgusegs m2 ->
       limbs_at bgusegs m2 RP (mul_comba8 a b) -> stk bgusegs m2 lo SPz ->
       evt bgusegs POST (AFTER m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt bgusegs POST (ENTRY 0x1038ec).
  Proof using ESP ERET STK MI0.
    intros CS8 a b RP AP BP C8 LA LB HLA HLB E0 E1 E2 RA RB WR DRA DRB LO SEPR SEPA SEPB UBR UBA UBB K.
    subst RP AP BP SPz.
    eapply evt_cut; [ eapply C8 with (a := a) (b := b) (lo := lo); eassumption | ].
    intros ms' PO. unfold vl_post in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma ucall_memset0 : forall (L : list Z) (D : Z),
    bv_unsigned w0 = D -> bv_unsigned w1 = 0%Z -> bv_unsigned w2 = (8 * Z.of_nat (length L))%Z ->
    limbs_at bgusegs m D L -> wr_at bgusegs m D (8 * Z.of_nat (length L)) ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(D, D + 8 * Z.of_nat (length L))]%Z m m2 -> wmono bgusegs m m2 -> mem_inv bgusegs m2 ->
       limbs_at bgusegs m2 D (repeat 0%Z (length L)) -> stk bgusegs m2 lo SPz ->
       evt bgusegs POST (AFTER m2 u0 u1 u2 w0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt bgusegs POST (ENTRY 0x2bbae4).
  Proof using ESP ERET STK MI0.
    intros L D E0 E1 E2 HL WR K.
    eapply evt_cut; [ eapply umemset0_limbs_spec with (L := L) (D := D) (lo := lo) (SPz := SPz); eassumption | ].
    intros ms' PO. unfold umemset0_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HB & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.
End CallsU.
