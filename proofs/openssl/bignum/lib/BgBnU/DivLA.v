(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnArith BnLoop.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnP Require Import DivLA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  Variables (m : word -> option byte) (D SP lo : Z) (a : list Z) (lb : Z).
  Variables (FS FB : Z) (FCELLS : list cell).
  Hypothesis FS_ok : Z.of_nat (cells_size FCELLS) = FS.
  Hypothesis FBE : (FB = SP - FS)%Z.
  Hypothesis LB : (0 <= lb < 64)%Z.
  Notation n := (Z.of_nat (length a)).
  Hypothesis SEPR : (D + 8 * n <= SP - FS \/ SP <= D)%Z.

  Notation rsh := ((64 - lb) mod 64)%Z.
  Notation rmask := (if (lb =? 0)%Z then 0 else 18446744073709551615)%Z.
  Notation ND := (Z.lxor (D mod 18446744073709551616) 18446744073709551615).
  (* [comment removed for export] *)
  Notation ST pc mm x5 x6 x11 x16 x17 :=
    (MS (mkR ra sp gp tp x5 x6 t2 s0 (Z_to_bv 64 D) (Z_to_bv 64 rsh) x11 (Z_to_bv 64 lb) (Z_to_bv 64 ND) (Z_to_bv 64 rmask) (Z_to_bv 64 63)
             x16 x17 (Z_to_bv 64 (Z.shiftl n 3)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).

  Lemma LEN : length a = length a. Proof. reflexivity. Qed.
  Lemma ALA : alias_ok D D n. Proof. left. reflexivity. Qed.
  Notation FCR := (la_fc_range lb LB).
  Notation RES := (fst (lshift_limbs a lb 0)).
  Notation CY := (snd (lshift_limbs a lb 0)).
  Notation KINV := (INV bgusegs (la_fl lb) (la_fc lb) 18446744073709551615 m D D D SP lo a FS FB FCELLS RES CY).
  Notation KIT L := (L bgusegs (la_fl lb) (la_fc lb) 18446744073709551615%Z FCR m D D D SP lo a a FS FB FCELLS FS_ok FBE
                        LEN ALA ALA SEPR SEPR SEPR RES CY).
  Notation K_rdA := (KIT INV_rdA).
  Notation K_store := (KIT INV_store).   Notation K_store_ok := (KIT INV_store_ok).
  Notation K_done := (KIT INV_done).   Notation K_len := (KIT INV_len).   Notation K_carry := (KIT INV_carry).
  Notation K_rangeA := (KIT INV_rangeA).   Notation K_ptrs := (KIT INV_ptrs).

  Ltac ldA I := let L := constr:(K_rdA) in ldA_with L I.
  Ltac w64eq := unfold la_fl, shlw; clear - LB; f_equal; rewrite (Z.mod_small lb 64) by lia; rewrite Z.shiftl_mul_pow2 by lia; reflexivity.
  Ltac st_limb I l cn Ecn := let L1 := constr:(K_store_ok) in let L2 := constr:(K_store) in st_limb_with L1 L2 w64eq I l cn Ecn.

  (* [comment removed for export] *)
  Lemma la_uloop : forall la m1 pre c pa x5 x16 x17,
    la <> [] -> KINV m1 pre la la c pa pa pa ->
    (forall m2 x5 x6 x11 x16 x17,
       limbs_at bgusegs m2 D RES -> rw_cells bgusegs m2 FB FCELLS -> stk bgusegs m2 lo FB -> mem_inv bgusegs m2 ->
       munch [(D, D + 8 * n); (SP - FS, SP)]%Z m m2 -> wmono bgusegs m m2 ->
       evt bgusegs POST (ST 0x109938 m2 x5 x6 x11 x16 x17)) ->
    evt bgusegs POST (ST 0x109908 m1 x5 (Z_to_bv 64 c) (Z_to_bv 64 (pa - D)) x16 x17).
  Proof.
    induction la as [|x la IH]; intros m1 pre c pa x5 x16 x17 NE I K; [congruence|].
    pose proof (K_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    pose proof (K_ptrs _ _ _ _ _ _ _ _ I) as (Epa & _ & TOP64).
    pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx. pose proof (K_carry _ _ _ _ _ _ _ _ I) as Hc.
    assert (RPA : (0 <= pa - D /\ pa + 8 <= D + 8 * n /\ D + 8 * n <= 140737488355328 /\ 0 <= D)%Z) by (cbn [length] in *; lia).
    assert (END : (Z.lxor (D mod 18446744073709551616) 18446744073709551615 = 18446744073709551615 - D)%Z)
      by (rewrite Z.mod_small by lia; apply zb_lxor_ones; lia).
    chk ltac:(fun C => rewrite END in C; clear - C RPA; lia).
    chk ltac:(fun C => clear - C LB; lia).
    zstep. replace (D + (pa - D))%Z with pa by (clear; lia).
    ldA I.
    zstep. zstep.
    st_limb I l c' Ec'.
    chk ltac:(fun C => clear - C LB; pose proof (Z.mod_pos_bound (64 - lb) 64 ltac:(lia)); lia).
    zstep. zstep.
    replace (pa - D + 8)%Z with (pa + 8 - D)%Z by (clear; lia).
    zstep.
    rewrite (la_carry lb x x c LB Rx), <- Ec'.
    assert (Hc' : (0 <= c' <= 18446744073709551615)%Z) by (clear - Rx Hc Ec' LB; subst c'; apply (la_fc_range lb LB); assumption).
    clear Ec'.
    zstep. if_cases KB; zify_cond KB.
    - (* [comment removed for export] *)
      eapply IH; [ | exact I | exact K ].
      destruct la; [ exfalso | discriminate ].
      pose proof (K_len _ _ _ _ _ _ _ _ I) as (El2 & En2 & Epr2 & _). cbn [length] in *.
      rewrite Z.shiftl_mul_pow2 in KB by lia. rewrite ?unsigned_lit in KB by lia. lia.
    - (* [comment removed for export] *)
      destruct la as [|x' la'].
      + pose proof (K_done _ _ _ _ _ _ I) as (HP & CYE & FR & ST & MI & MU & WM).
        apply K; assumption.
      + exfalso. pose proof (K_len _ _ _ _ _ _ _ _ I) as (El2 & En2 & Epr2 & _). cbn [length] in *.
        rewrite Z.shiftl_mul_pow2 in KB by lia. rewrite ?unsigned_lit in KB by lia. lia.
  Qed.

  Notation ST2 pc mm x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x18 :=
    (MS (mkR ra sp gp tp x5 x6 t2 s0 (Z_to_bv 64 D) x10 x11 x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgusegs)).

  Lemma la_ublock : forall nb,
    (1 <= nb <= 64)%Z -> lb = (64 - nb)%Z -> (n < 2^31)%Z ->
    limbs a -> limbs_at bgusegs m D a -> wr_at bgusegs m D (8 * n) ->
    rw_cells bgusegs m FB FCELLS -> stk bgusegs m lo FB -> mem_inv bgusegs m ->
    (forall m2 x5 x6 x10 x11 x13 x14 x15 x16 x17 x18,
       limbs_at bgusegs m2 D (fst (lshift_limbs a lb 0)) -> rw_cells bgusegs m2 FB FCELLS -> stk bgusegs m2 lo FB -> mem_inv bgusegs m2 ->
       munch [(D, D + 8 * n); (SP - FS, SP)]%Z m m2 -> wmono bgusegs m m2 ->
       evt bgusegs POST (ST2 0x109938 m2 x5 x6 x10 x11 (Z_to_bv 64 lb) x13 x14 x15 x16 x17 x18)) ->
    evt bgusegs POST (ST2 0x1098c0 m t0 t1 (Z_to_bv 64 nb) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 n)).
  Proof.
    intros nb NB ELB N31 LA RA WR FR STK MI K.
    do 3 zstep.
    rewrite (bn_swrap32_small (64 - nb)) by (clear - NB; lia). rewrite <- ELB.
    chk ltac:(fun C => apply C; reflexivity).
    zstep. if_cases KZ; zify_cond KZ.
    - (* [comment removed for export] *)
      assert (a = []).
      { destruct a; [reflexivity | exfalso]. apply andb_false_iff in KZ. cbn [length] in *. destruct KZ as [KZ|KZ]; apply Z.ltb_ge in KZ; lia. }
      apply K; try assumption.
      + subst a. apply limbs_at_nil. pose proof (limbs_at_bound _ _ _ _ RA). lia.
      + apply munch_refl.
      + apply wmono_refl.
    - do 13 zstep.
      destruct (la_mirror nb NB) as [E1 E2].
      setreg 10%Z (Z_to_bv 64 (la_rsh_m nb)) ltac:(reflexivity).
      setreg 14%Z (Z_to_bv 64 (la_rmask_m nb)) ltac:(reflexivity).
      rewrite E1, E2. rewrite <- ELB.
      assert (I : KINV m [] a a 0 D D D).
      { apply (KIT INV_init); try assumption; try lia.
        - apply munch_refl.
        - apply munch_refl.
        - apply wmono_refl.
        - rewrite lshift_limbs_gen. reflexivity.
        - rewrite lshift_limbs_gen. reflexivity. }
      eapply evt_eq; [ | eapply (la_uloop a m [] 0 D); [ | exact I | ] ].
      + replace (D - D)%Z with 0%Z by lia. reflexivity.
      + destruct a; [ exfalso; cbn [length] in *; lia | discriminate ].
      + intros m2 x5 x6 x11 x16 x17 HP FR2 ST2 MI2 MU2 WM2. apply K; assumption.
  Qed.
End Proofs.
