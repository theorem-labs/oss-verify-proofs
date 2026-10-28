(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require BnCalls W_cmp_words W_mul_normal.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnIfaceA ImplA RtCallA AW_add_words AW_sub_words AW_cmp_part_words.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition comba8_aspec (CS8 : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (lo : Z),
    limbs a -> limbs b -> length a = 8%nat -> length b = 8%nat ->
    limbs_at bsegs m (bv_unsigned a1) a -> limbs_at bsegs m (bv_unsigned a2) b ->
    wr_at bsegs m (bv_unsigned a0) 128 ->
    (bv_unsigned a0 + 128 <= bv_unsigned a1 \/ bv_unsigned a1 + 64 <= bv_unsigned a0)%Z ->
    (bv_unsigned a0 + 128 <= bv_unsigned a2 \/ bv_unsigned a2 + 64 <= bv_unsigned a0)%Z ->
    stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - CS8)%Z ->
    (bv_unsigned a0 + 128 <= bv_unsigned sp - CS8 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a1 + 64 <= bv_unsigned sp - CS8 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    (bv_unsigned a2 + 64 <= bv_unsigned sp - CS8 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
    mem_inv bsegs m ->
    shb_cells bsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m ->
    acc bsegs m (bv_unsigned a0) 128 -> acc bsegs m (bv_unsigned a1) 64 -> acc bsegs m (bv_unsigned a2) 64 ->
    aptrs3 (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) 16 lo ->
    (* [comment removed for export] *)
    (0 < bv_unsigned a0)%Z -> (0 < bv_unsigned a1)%Z -> (0 < bv_unsigned a2)%Z ->
    (bv_unsigned a0 + 128 <= 65536 \/ 12570624 <= bv_unsigned a0)%Z ->
    evt bsegs (W_mul_normal.vl_post bsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) 16 CS8 (mul_comba8 a b) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x226a50) fc None m (seg_rom bsegs)).

Definition sub_part_words_bspec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (cl da db : nat) (lo : Z),
    limbs a -> limbs b -> length a = (cl + da)%nat -> length b = (cl + db)%nat -> (da = 0 \/ db = 0)%nat ->
    (Z.of_nat (cl + da + db) < 2147483648)%Z ->
    bv_unsigned a3 = Z.of_nat cl -> a4 = Z_to_bv 64 (Z.of_nat da - Z.of_nat db) ->
    limbs_at bsegs m (bv_unsigned a1) a -> limbs_at bsegs m (bv_unsigned a2) b ->
    wr_at bsegs m (bv_unsigned a0) (8 * Z.of_nat (cl + da + db)) ->
    (bv_unsigned a0 = bv_unsigned a1 \/ bv_unsigned a0 + 8 * Z.of_nat (cl + da + db) <= bv_unsigned a1 \/
     bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a0)%Z ->
    (bv_unsigned a0 = bv_unsigned a2 \/ bv_unsigned a0 + 8 * Z.of_nat (cl + da + db) <= bv_unsigned a2 \/
     bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned a0)%Z ->
    stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 224)%Z ->
    (bv_unsigned a0 + 8 * Z.of_nat (cl + da + db) <= bv_unsigned sp - 224 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned sp - 224 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    (bv_unsigned a2 + 8 * Z.of_nat (length b) <= bv_unsigned sp - 224 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
    mem_inv bsegs m ->
    shb_cells bsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m ->
    acc bsegs m (bv_unsigned a0) (8 * Z.of_nat (cl + da + db)) -> acc bsegs m (bv_unsigned a1) (8 * Z.of_nat (length a)) ->
    acc bsegs m (bv_unsigned a2) (8 * Z.of_nat (length b)) ->
    aptrs3 (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (Z.of_nat (cl + da + db)) lo ->
    ub_ptr_ok 1 (bv_unsigned a0) -> ub_ptr_ok 1 (bv_unsigned a1) -> ub_ptr_ok 1 (bv_unsigned a2) ->
    evt bsegs (wl_post bsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) (Z.of_nat (cl + da + db)) 224%Z
                 (fst (sub_part_words a b cl)) (snd (sub_part_words a b cl)) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24ca34) fc None m (seg_rom bsegs)).

Definition mul_normal_bspec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (lo : Z),
    limbs a -> limbs b -> (Z.of_nat (length a) + Z.of_nat (length b) < 2147483648)%Z ->
    bv_unsigned a2 = Z.of_nat (length a) -> bv_unsigned a4 = Z.of_nat (length b) ->
    limbs_at bsegs m (bv_unsigned a1) a -> limbs_at bsegs m (bv_unsigned a3) b ->
    wr_at bsegs m (bv_unsigned a0) (8 * (Z.of_nat (length a) + Z.of_nat (length b))) ->
    (bv_unsigned a0 + 8 * (Z.of_nat (length a) + Z.of_nat (length b)) <= bv_unsigned a1 \/
     bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned a0)%Z ->
    (bv_unsigned a0 + 8 * (Z.of_nat (length a) + Z.of_nat (length b)) <= bv_unsigned a3 \/
     bv_unsigned a3 + 8 * Z.of_nat (length b) <= bv_unsigned a0)%Z ->
    stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 240)%Z ->
    (bv_unsigned a0 + 8 * (Z.of_nat (length a) + Z.of_nat (length b)) <= bv_unsigned sp - 240 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a1 + 8 * Z.of_nat (length a) <= bv_unsigned sp - 240 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    (bv_unsigned a3 + 8 * Z.of_nat (length b) <= bv_unsigned sp - 240 \/ bv_unsigned sp <= bv_unsigned a3)%Z ->
    mem_inv bsegs m ->
    shb_cells bsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m ->
    acc bsegs m (bv_unsigned a0) (8 * (Z.of_nat (length a) + Z.of_nat (length b))) ->
    acc bsegs m (bv_unsigned a1) (8 * Z.of_nat (length a)) -> acc bsegs m (bv_unsigned a3) (8 * Z.of_nat (length b)) ->
    aptrs3 (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a3) (Z.of_nat (length a) + Z.of_nat (length b)) lo ->
    (bv_unsigned a0 + 8 * (Z.of_nat (length a) + Z.of_nat (length b)) <= 65536 \/ 12570624 <= bv_unsigned a0)%Z ->
    ub_ptr_ok 1 (bv_unsigned a0) -> ub_ptr_ok 1 (bv_unsigned a1) -> ub_ptr_ok 1 (bv_unsigned a3) ->
    evt bsegs (W_mul_normal.vl_post bsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0)
                 (Z.of_nat (length a) + Z.of_nat (length b)) 240%Z (mul_normal a b) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24d894) fc None m (seg_rom bsegs)).

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
  Lemma call_add_wordsK : forall (a b : list Z) (RP AP BP : Z),
    limbs a -> limbs b -> length b = length a -> (Z.of_nat (length a) < 2^31)%Z ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP -> bv_unsigned w3 = Z.of_nat (length a) ->
    limbs_at bsegs m AP a -> limbs_at bsegs m BP b -> wr_at bsegs m RP (8 * Z.of_nat (length a)) ->
    alias_ok RP AP (Z.of_nat (length a)) -> alias_ok RP BP (Z.of_nat (length a)) ->
    (lo <= SPz - 112)%Z ->
    (RP + 8 * Z.of_nat (length a) <= SPz - 112 \/ SPz <= RP)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - 112 \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length a) <= SPz - 112 \/ SPz <= BP)%Z ->
    (acc bsegs m RP (8 * Z.of_nat (length a)) /\ acc bsegs m AP (8 * Z.of_nat (length a)) /\ acc bsegs m BP (8 * Z.of_nat (length a)) /\
     aptrs3 RP AP BP (Z.of_nat (length a)) lo) ->
    ub_ptr_ok (Z.of_nat (length a)) RP -> ub_ptr_ok (Z.of_nat (length a)) AP -> ub_ptr_ok (Z.of_nat (length a)) BP ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * Z.of_nat (length a)); (SPz - 112, SPz)]%Z m m2 -> wmono bsegs m m2 -> mem_inv bsegs m2 ->
       limbs_at bsegs m2 RP (fst (add_words a b)) -> stk bsegs m2 lo SPz ->
       evt bsegs POST (AFTER m2 u0 u1 u2 (Z_to_bv 64 (snd (add_words a b))) v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt bsegs POST (ENTRY 0x22626c).
  Proof using ESP ERET STK MI0 SHBC.
    intros a b RP AP BP LA LB LEN N31 E0 E1 E2 E3 RA RB WR ALA ALB LO SEPR SEPA SEPB (ACR & ACA & ACB & APT) UBR UBA UBB K.
    subst RP AP BP SPz.
    eapply evt_cut; [ eapply bn_add_words_aspec with (a := a) (b := b) (lo := lo); eassumption | ].
    intros ms' PO. unfold aw_apost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  Lemma call_sub_wordsK : forall (a b : list Z) (RP AP BP : Z),
    limbs a -> limbs b -> length b = length a -> (Z.of_nat (length a) < 2^31)%Z ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP -> bv_unsigned w3 = Z.of_nat (length a) ->
    limbs_at bsegs m AP a -> limbs_at bsegs m BP b -> wr_at bsegs m RP (8 * Z.of_nat (length a)) ->
    alias_ok RP AP (Z.of_nat (length a)) -> alias_ok RP BP (Z.of_nat (length a)) ->
    (lo <= SPz - 112)%Z ->
    (RP + 8 * Z.of_nat (length a) <= SPz - 112 \/ SPz <= RP)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - 112 \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length a) <= SPz - 112 \/ SPz <= BP)%Z ->
    (acc bsegs m RP (8 * Z.of_nat (length a)) /\ acc bsegs m AP (8 * Z.of_nat (length a)) /\ acc bsegs m BP (8 * Z.of_nat (length a)) /\
     aptrs3 RP AP BP (Z.of_nat (length a)) lo) ->
    ub_ptr_ok (Z.of_nat (length a)) RP -> ub_ptr_ok (Z.of_nat (length a)) AP -> ub_ptr_ok (Z.of_nat (length a)) BP ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * Z.of_nat (length a)); (SPz - 112, SPz)]%Z m m2 -> wmono bsegs m m2 -> mem_inv bsegs m2 ->
       limbs_at bsegs m2 RP (fst (sub_words a b)) -> stk bsegs m2 lo SPz ->
       evt bsegs POST (AFTER m2 u0 u1 u2 (Z_to_bv 64 (snd (sub_words a b))) v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt bsegs POST (ENTRY 0x226654).
  Proof using ESP ERET STK MI0 SHBC.
    intros a b RP AP BP LA LB LEN N31 E0 E1 E2 E3 RA RB WR ALA ALB LO SEPR SEPA SEPB (ACR & ACA & ACB & APT) UBR UBA UBB K.
    subst RP AP BP SPz.
    eapply evt_cut; [ eapply bn_sub_words_aspec with (a := a) (b := b) (lo := lo); eassumption | ].
    intros ms' PO. unfold sw_apost, wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma call_cmp_part_wordsA : forall (a b : list Z) (cl da db : nat) (AP BP : Z),
    limbs a -> limbs b -> length a = (cl + da)%nat -> length b = (cl + db)%nat -> (da = 0 \/ db = 0)%nat ->
    (Z.of_nat (cl + da + db) < 2147483648)%Z ->
    bv_unsigned w0 = AP -> bv_unsigned w1 = BP -> bv_unsigned w2 = Z.of_nat cl -> w3 = Z_to_bv 64 (Z.of_nat da - Z.of_nat db) ->
    limbs_at bsegs m AP a -> limbs_at bsegs m BP b ->
    (lo <= SPz - 16)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - 16 \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length b) <= SPz - 16 \/ SPz <= BP)%Z ->
    (acc bsegs m AP (8 * Z.of_nat (length a)) /\ acc bsegs m BP (8 * Z.of_nat (length b)) /\
     (AP mod 8 = 0)%Z /\ (BP mod 8 = 0)%Z /\ (SHHI <= lo)%Z) ->
    ub_ptr_ok 1 AP -> ub_ptr_ok 1 BP ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(SPz - 16, SPz)]%Z m m2 -> wmono bsegs m m2 -> mem_inv bsegs m2 -> stk bsegs m2 lo SPz ->
       evt bsegs POST (AFTER m2 u0 u1 u2 (Z_to_bv 64 (cmp_part_words a b cl)) v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt bsegs POST (ENTRY 0x1f157c).
  Proof using ESP ERET STK MI0 SHBC.
    intros a b cl da db AP BP LA LB HLA HLB DAB N31 E0 E1 E2 E3 RA RB LO SEPA SEPB (ACA & ACB & AL8A & AL8B & SHLO) UBA UBB K.
    subst AP BP SPz.
    eapply evt_cut; [ eapply bn_cmp_part_words_aspec with (a := a) (b := b) (cl := cl) (da := da) (db := db) (lo := lo); eassumption | ].
    intros ms' PO. unfold W_cmp_words.ro_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma call_sub_part_wordsA : forall (a b : list Z) (cl da db : nat) (RP AP BP : Z),
    sub_part_words_bspec ->
    limbs a -> limbs b -> length a = (cl + da)%nat -> length b = (cl + db)%nat -> (da = 0 \/ db = 0)%nat ->
    (Z.of_nat (cl + da + db) < 2147483648)%Z ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP -> bv_unsigned w3 = Z.of_nat cl ->
    w4 = Z_to_bv 64 (Z.of_nat da - Z.of_nat db) ->
    limbs_at bsegs m AP a -> limbs_at bsegs m BP b -> wr_at bsegs m RP (8 * Z.of_nat (cl + da + db)) ->
    (RP = AP \/ RP + 8 * Z.of_nat (cl + da + db) <= AP \/ AP + 8 * Z.of_nat (length a) <= RP)%Z ->
    (RP = BP \/ RP + 8 * Z.of_nat (cl + da + db) <= BP \/ BP + 8 * Z.of_nat (length b) <= RP)%Z ->
    (lo <= SPz - 224)%Z ->
    (RP + 8 * Z.of_nat (cl + da + db) <= SPz - 224 \/ SPz <= RP)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - 224 \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length b) <= SPz - 224 \/ SPz <= BP)%Z ->
    (acc bsegs m RP (8 * Z.of_nat (cl + da + db)) /\ acc bsegs m AP (8 * Z.of_nat (length a)) /\ acc bsegs m BP (8 * Z.of_nat (length b)) /\
     aptrs3 RP AP BP (Z.of_nat (cl + da + db)) lo) ->
    ub_ptr_ok 1 RP -> ub_ptr_ok 1 AP -> ub_ptr_ok 1 BP ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * Z.of_nat (cl + da + db)); (SPz - 224, SPz)]%Z m m2 -> wmono bsegs m m2 -> mem_inv bsegs m2 ->
       limbs_at bsegs m2 RP (fst (sub_part_words a b cl)) -> stk bsegs m2 lo SPz ->
       evt bsegs POST (AFTER m2 u0 u1 u2 (Z_to_bv 64 (snd (sub_part_words a b cl))) v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt bsegs POST (ENTRY 0x24ca34).
  Proof using ESP ERET STK MI0 SHBC.
    intros a b cl da db RP AP BP SPEC LA LB HLA HLB DAB N31 E0 E1 E2 E3 E4 RA RB WR ALA ALB LO SEPR SEPA SEPB (ACR & ACA & ACB & APT) UBR UBA UBB K.
    subst RP AP BP SPz.
    eapply evt_cut; [ eapply SPEC with (a := a) (b := b) (cl := cl) (da := da) (db := db) (lo := lo); eassumption | ].
    intros ms' PO. unfold wl_post in PO.
    destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma call_mul_normalA : forall (a b : list Z) (RP AP BP : Z),
    mul_normal_bspec ->
    limbs a -> limbs b -> (Z.of_nat (length a) + Z.of_nat (length b) < 2147483648)%Z ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = Z.of_nat (length a) -> bv_unsigned w3 = BP ->
    bv_unsigned w4 = Z.of_nat (length b) ->
    limbs_at bsegs m AP a -> limbs_at bsegs m BP b -> wr_at bsegs m RP (8 * (Z.of_nat (length a) + Z.of_nat (length b))) ->
    (RP + 8 * (Z.of_nat (length a) + Z.of_nat (length b)) <= AP \/ AP + 8 * Z.of_nat (length a) <= RP)%Z ->
    (RP + 8 * (Z.of_nat (length a) + Z.of_nat (length b)) <= BP \/ BP + 8 * Z.of_nat (length b) <= RP)%Z ->
    (lo <= SPz - 240)%Z ->
    (RP + 8 * (Z.of_nat (length a) + Z.of_nat (length b)) <= SPz - 240 \/ SPz <= RP)%Z ->
    (AP + 8 * Z.of_nat (length a) <= SPz - 240 \/ SPz <= AP)%Z ->
    (BP + 8 * Z.of_nat (length b) <= SPz - 240 \/ SPz <= BP)%Z ->
    (acc bsegs m RP (8 * (Z.of_nat (length a) + Z.of_nat (length b))) /\ acc bsegs m AP (8 * Z.of_nat (length a)) /\ acc bsegs m BP (8 * Z.of_nat (length b)) /\
     aptrs3 RP AP BP (Z.of_nat (length a) + Z.of_nat (length b)) lo /\
     (RP + 8 * (Z.of_nat (length a) + Z.of_nat (length b)) <= 65536 \/ 12570624 <= RP)%Z) ->
    ub_ptr_ok 1 RP -> ub_ptr_ok 1 AP -> ub_ptr_ok 1 BP ->
    (forall m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * (Z.of_nat (length a) + Z.of_nat (length b))); (SPz - 240, SPz)]%Z m m2 -> wmono bsegs m m2 -> mem_inv bsegs m2 ->
       limbs_at bsegs m2 RP (mul_normal a b) -> stk bsegs m2 lo SPz ->
       evt bsegs POST (AFTER m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt bsegs POST (ENTRY 0x24d894).
  Proof using ESP ERET STK MI0 SHBC.
    intros a b RP AP BP SPEC LA LB N31 E0 E1 E2 E3 E4 RA RB WR DRA DRB LO SEPR SEPA SEPB (ACR & ACA & ACB & APT & OFFI) UBR UBA UBB K.
    subst RP AP BP SPz.
    eapply evt_cut; [ eapply SPEC with (a := a) (b := b) (lo := lo); eassumption | ].
    intros ms' PO. unfold W_mul_normal.vl_post in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma call_comba8A : forall (CS8 : Z) (a b : list Z) (RP AP BP : Z),
    comba8_aspec CS8 ->
    limbs a -> limbs b -> length a = 8%nat -> length b = 8%nat ->
    bv_unsigned w0 = RP -> bv_unsigned w1 = AP -> bv_unsigned w2 = BP ->
    limbs_at bsegs m AP a -> limbs_at bsegs m BP b -> wr_at bsegs m RP 128 ->
    (RP + 128 <= AP \/ AP + 64 <= RP)%Z -> (RP + 128 <= BP \/ BP + 64 <= RP)%Z ->
    (lo <= SPz - CS8)%Z ->
    (RP + 128 <= SPz - CS8 \/ SPz <= RP)%Z -> (AP + 64 <= SPz - CS8 \/ SPz <= AP)%Z -> (BP + 64 <= SPz - CS8 \/ SPz <= BP)%Z ->
    (acc bsegs m RP 128 /\ acc bsegs m AP 64 /\ acc bsegs m BP 64 /\ aptrs3 RP AP BP 16 lo /\
     ((0 < RP)%Z /\ (0 < AP)%Z /\ (0 < BP)%Z /\ (RP + 128 <= 65536 \/ 12570624 <= RP)%Z)) ->
    (forall m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6,
       munch [(RP, RP + 8 * 16); (SPz - CS8, SPz)]%Z m m2 -> wmono bsegs m m2 -> mem_inv bsegs m2 ->
       limbs_at bsegs m2 RP (mul_comba8 a b) -> stk bsegs m2 lo SPz ->
       evt bsegs POST (AFTER m2 u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6)) ->
    evt bsegs POST (ENTRY 0x226a50).
  Proof using ESP ERET STK MI0 SHBC.
    intros CS8 a b RP AP BP C8 LA LB HLA HLB E0 E1 E2 RA RB WR DRA DRB LO SEPR SEPA SEPB (ACR & ACA & ACB & APT & P0 & P1 & P2 & OFI) K.
    subst RP AP BP SPz.
    eapply evt_cut; [ eapply C8 with (a := a) (b := b) (lo := lo); eassumption | ].
    intros ms' PO. unfold W_mul_normal.vl_post in PO.
    destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & E & MUc & WMc & MIc & HR & STc).
    subst ms'. rewrite ERET. eapply K; eassumption.
  Qed.
End Calls.

(* [comment removed for export] *)
Section CpsCalls.
  Context {AR : ARun}.
  Local Notation RT := (@ar_RT AR).
  Local Notation PMc := (@ar_PMc AR).
  Local Notation ACEIL := (@BnHeapA.ACEIL AR).
  Local Notation AHEAP := (@BnHeapA.AHEAP AR).

  (* [comment removed for export] *)
  Definition kpost (Σ : rts RT) (Q : config -> Prop) : machine_state -> Prop :=
    fun ms => cps bsegs (ASTA RT Σ PMc (eq ms)) Q.

  (* [comment removed for export] *)
  Lemma cps_done : forall Σ ms (R : machine_state -> Prop), R ms -> cps bsegs (ASTA RT Σ PMc (eq ms)) (ASTA RT Σ PMc R).
  Proof.
    intros Σ ms R HR. eapply cps_conseq; [apply cps_refl | intros c Hc; exact Hc |].
    intros c Hc. eapply ASTA_conseq; [exact Hc|]. intros ms0 <-. exact HR.
  Qed.

  (* [comment removed for export] *)
  Lemma call_memset0A : forall (Σ : rts RT) (Q : config -> Prop)
      (wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (OW LB : list block) (lo SPz RET : Z) (L : list Z) (D : Z) (bd : block),
    bv_unsigned wsp = SPz -> ret_pc (Z_to_bv 64 RET) = Z_to_bv 64 RET ->
    stk bsegs m lo SPz -> mem_inv bsegs m ->
    AHEAP Σ OW LB m -> (ACEIL <= lo)%Z -> (lo + RT_STACK <= SPz)%Z -> (SPz + 16 <= USTACK_TOP)%Z -> (SPz mod 16 = 0)%Z -> tp = wz TP_A ->
    In bd (OW ++ LB) -> (blk_addr bd <= D)%Z -> (D + 8 * Z.of_nat (length L) <= blk_addr bd + blk_size bd)%Z ->
    (8 * Z.of_nat (length L) < 2^40)%Z ->
    bv_unsigned w0 = D -> bv_unsigned w1 = 0%Z -> bv_unsigned w2 = (8 * Z.of_nat (length L))%Z ->
    (forall m2 u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 (F2 : bvmap 5 word) (fc2 : bv 32),
       AHEAP Σ OW LB m2 ->
       agree_on (fun x => aclient_addr (OW ++ LB) SPz x /\ ~ (D <= x < D + 8 * Z.of_nat (length L))%Z) m m2 ->
       wmono bsegs m m2 -> mem_inv bsegs m2 -> limbs_at bsegs m2 D (repeat 0%Z (length L)) -> stk bsegs m2 lo SPz ->
       evt bsegs (kpost Σ Q)
         (MS (mkR (Z_to_bv 64 RET) wsp gp tp u0 u1 u2 s0 s1 w0 v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
             F2 (Z_to_bv 64 RET) fc2 None m2 (seg_rom bsegs))) ->
    evt bsegs (kpost Σ Q)
      (MS (mkR (Z_to_bv 64 RET) wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1bd0d8) fc None m (seg_rom bsegs)).
  Proof.
    intros until bd. intros ESP ERET STK MI0 HEAP CEIL LO SPT SP16 ETP IND D1 D2 HN E0 E1 E2 K.
    subst SPz.
    apply evt_done. unfold kpost.
    eapply cps_step_same.
    - eapply (asan_memset_cpsA (Z_to_bv 64 RET) wsp gp tp t0 t1 t2 s0 s1 w0 w1 w2 w3 w4 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                 F fc m Σ OW LB lo D (8 * Z.of_nat (length L)) (Z_to_bv 8 0) bd); try eassumption.
      + lia.
      + unfold wz. rewrite <- E0. symmetry. apply Z_to_bv_bv_unsigned.
      + unfold wz. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. rewrite <- E1. symmetry. apply Z_to_bv_bv_unsigned.
      + unfold wz. rewrite <- E2. symmetry. apply Z_to_bv_bv_unsigned.
    - intros ms2 PO. unfold icall_post in PO.
      destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & MI2 & ST2 & HEAP2 & WM2 & AG2 & BZ & WR2).
      rewrite ERET. apply cps_from_evt'.
      assert (Ew0 : wz D = w0) by (unfold wz; rewrite <- E0; apply Z_to_bv_bv_unsigned).
      rewrite Ew0, <- ETP.
      eapply K; try eassumption.
      unfold limbs_at. rewrite BnCalls.lbytes_repeat0.
      replace (8 * length L)%nat with (Z.to_nat (8 * Z.of_nat (length L))) by lia. exact BZ.
  Qed.
End CpsCalls.
