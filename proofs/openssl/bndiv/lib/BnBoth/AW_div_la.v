(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA ZBridge.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require DivLA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop AsLeaf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2435000 => 1
  | 2435004 => 2
  | 2435064 => 2
  | 2435088 => 2
  | 2435116 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Notation la_fl := DivLA.la_fl.
Notation la_fc := DivLA.la_fc.
Notation la_fc_range := DivLA.la_fc_range.
Notation la_carry := DivLA.la_carry.
Notation la_rsh_m := DivLA.la_rsh_m.
Notation la_rmask_m := DivLA.la_rmask_m.
Notation la_mirror := DivLA.la_mirror.
Notation lshift_limbs_gen := DivLA.lshift_limbs_gen.

Section Proofs.
  Variables (ra sp gp tp t2 s0 s1 s2 s3 s4 s7 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32).
  Variable POST : machine_state -> Prop.
  (* [comment removed for export] *)
  Variables (m : word -> option byte) (D SP lo : Z) (a : list Z) (lb : Z).
  Variables (FS FB : Z) (FCELLS : list cell).
  Hypothesis FS_ok : Z.of_nat (cells_size FCELLS) = FS.
  Hypothesis FBE : (FB = SP - FS)%Z.
  Hypothesis LB : (0 <= lb < 64)%Z.
  Notation n := (Z.of_nat (length a)).
  Hypothesis SEPR : (D + 8 * n <= SP - FS \/ SP <= D)%Z.
  (* [comment removed for export] *)
  Hypothesis ACD : acc bsegs m D (8 * n).
  Hypothesis ALD : (D mod 8 = 0)%Z.
  Hypothesis OFFW : offshW [(D, D + 8 * n); (SP - FS, SP)]%Z.

  Notation rsh := ((64 - lb) mod 64)%Z.
  Notation rmask := (if (lb =? 0)%Z then 0 else 18446744073709551615)%Z.
  (* [comment removed for export] *)
  Notation ND := (18446744073709551615 - D)%Z.

  Notation ST pc mm x5 x6 x10 x11 x17 :=
    (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 x10 x11 (Z_to_bv 64 lb) (Z_to_bv 64 ND) (Z_to_bv 64 rsh) (Z_to_bv 64 rmask) (Z_to_bv 64 63) x17
             s2 s3 s4 (Z_to_bv 64 D) (Z_to_bv 64 (Z.shiftl n 3)) s7 (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Lemma LEN : length a = length a. Proof. reflexivity. Qed.
  Lemma ALA : alias_ok D D n. Proof. left. reflexivity. Qed.
  Notation FCR := (la_fc_range lb LB).
  Notation RES := (fst (lshift_limbs a lb 0)).
  Notation CY := (snd (lshift_limbs a lb 0)).
  Notation KINV := (INV bsegs (la_fl lb) (la_fc lb) 18446744073709551615 m D D D SP lo a FS FB FCELLS RES CY).
  Notation KIT L := (L bsegs (la_fl lb) (la_fc lb) 18446744073709551615%Z FCR m D D D SP lo a a FS FB FCELLS FS_ok FBE
                        LEN ALA ALA SEPR SEPR SEPR RES CY).
  Notation K_rdA := (KIT INV_rdA).
  Notation K_store := (KIT INV_store).   Notation K_store_ok := (KIT INV_store_ok).
  Notation K_done := (KIT INV_done).   Notation K_len := (KIT INV_len).   Notation K_carry := (KIT INV_carry).
  Notation K_rangeA := (KIT INV_rangeA).   Notation K_ptrs := (KIT INV_ptrs).
  Notation PBK := (apure D D D n SP FS).
  Notation K_shA := (INV_shA bsegs (la_fl lb) (la_fc lb) 18446744073709551615%Z m D D D SP lo a FS FB FCELLS RES CY).

  Ltac ldA I := let L := constr:(K_rdA) in ldA_with L I.
  Ltac w64eq := unfold DivLA.la_fl, shlw; clear - LB; f_equal; rewrite (Z.mod_small lb 64) by lia; rewrite Z.shiftl_mul_pow2 by lia; reflexivity.
  Ltac st_limb I l cn Ecn := let L1 := constr:(K_store_ok) in let L2 := constr:(K_store) in st_limb_with L1 L2 w64eq I l cn Ecn.
  Ltac shA P I k := let L := constr:(K_shA P) in ld_sh_with L I ACD k; chk0.

  (* [comment removed for export] *)
  Lemma la_loop : forall la m1 pre c pa x5 x10 x17,
    PBK -> la <> [] -> KINV m1 pre la la c pa pa pa ->
    (forall m2 x5 x6 x10 x11 x17,
       limbs_at bsegs m2 D RES -> rw_cells bsegs m2 FB FCELLS -> stk bsegs m2 lo FB -> mem_inv bsegs m2 ->
       munch [(D, D + 8 * n); (SP - FS, SP)]%Z m m2 -> wmono bsegs m m2 ->
       evt bsegs POST (ST 0x252840 m2 x5 x6 x10 x11 x17)) ->
    evt bsegs POST (ST 0x2527f8 m1 x5 (Z_to_bv 64 c) x10 (Z_to_bv 64 (pa - D)) x17).
  Proof.
    induction la as [|x la IH]; intros m1 pre c pa x5 x10 x17 P NE I K; [congruence|].
    pose proof (K_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    pose proof (K_ptrs _ _ _ _ _ _ _ _ I) as (Epa & _ & TOP64).
    pose proof (apure_bounds _ _ _ _ _ _ P) as (BR & _).
    pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx. pose proof (K_carry _ _ _ _ _ _ _ _ I) as Hc.
    assert (RPA : (0 <= pa - D /\ pa + 8 <= D + 8 * n /\ D + 8 * n <= 140737488355328 /\ 0 <= D)%Z) by (cbn [length] in *; clear - En Epa BR; lia).
    assert (RSH : (0 <= rsh < 64)%Z) by (clear; apply Z.mod_pos_bound; lia).
    clear En Epr TOP R0 Epa BR.
    ub.
    zstep. replace (D + (pa - D))%Z with pa by (clear; lia).
    zstep. zstep.
    shA P I 0%nat.
    ub.
    shA P I 0%nat.
    ldA I.
    zstep. zstep.
    st_limb I l c' Ec'.
    ub.
    zstep. zstep.
    replace (pa - D + 8)%Z with (pa + 8 - D)%Z by (clear; lia).
    zstep.
    rewrite (la_carry lb x x c LB Rx), <- Ec'.
    assert (Hc' : (0 <= c' <= 18446744073709551615)%Z) by (clear - Rx Hc Ec' LB; subst c'; apply (la_fc_range lb LB); assumption).
    clear Ec'.
    zstep. if_cases KB; zify_cond KB.
    - (* [comment removed for export] *)
      eapply IH; [ exact P | | exact I | exact K ].
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

  Notation ST2 pc mm x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 x22 :=
    (MS (mkR ra sp gp tp x5 x6 t2 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 (Z_to_bv 64 D) x22 s7 (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Lemma la_blockA : forall nb x5 x6 x11 x12 x13 x14 x15 x16 x17,
    (1 <= nb <= 64)%Z -> lb = (64 - nb)%Z -> (n < 2^31)%Z ->
    limbs a -> limbs_at bsegs m D a -> wr_at bsegs m D (8 * n) ->
    rw_cells bsegs m FB FCELLS -> stk bsegs m lo FB -> mem_inv bsegs m ->
    (forall m2 x5 x6 x10 x11 x13 x14 x15 x16 x17 x22,
       limbs_at bsegs m2 D RES -> rw_cells bsegs m2 FB FCELLS -> stk bsegs m2 lo FB -> mem_inv bsegs m2 ->
       munch [(D, D + 8 * n); (SP - FS, SP)]%Z m m2 -> wmono bsegs m m2 ->
       evt bsegs POST (ST2 0x252840 m2 x5 x6 x10 x11 (Z_to_bv 64 lb) x13 x14 x15 x16 x17 x22)) ->
    evt bsegs POST (ST2 0x2527b0 m x5 x6 (Z_to_bv 64 nb) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 n)).
  Proof.
    intros nb x5 x6 x11 x12 x13 x14 x15 x16 x17 NB ELB N31 LA RA WR FR STK MI K.
    zstep. zstep.
    rewrite (bn_swrap32_small (64 - nb)) by (clear - NB; lia). rewrite <- ELB.
    ub.
    zstep. rewrite lts_signed by (clear - N31; lia).
    if_cases KZ; zify_cond KZ.
    - (* [comment removed for export] *)
      assert (a = []) by (destruct a; [reflexivity | exfalso; cbn [length] in *; lia]).
      apply K; try assumption.
      + subst a. apply limbs_at_nil. pose proof (limbs_at_bound _ _ _ _ RA). lia.
      + apply munch_refl.
      + apply wmono_refl.
    - assert (Hn : (0 < n)%Z) by (clear - KZ; lia).
      assert (P : PBK).
      { pose proof (limbs_at_b47 bsegs m D a RA MI Hn) as B. unfold apure. repeat split; try exact ALD; try exact OFFW; try (clear - B; lia). 
        all: try (cbn [offshW] in OFFW; tauto). }
      pose proof (apure_bounds _ _ _ _ _ _ P) as (BR & _).
      do 13 zstep.
      destruct (la_mirror nb NB) as [E1 E2].
      setreg 14%Z (Z_to_bv 64 (la_rsh_m nb)) ltac:(reflexivity).
      setreg 15%Z (Z_to_bv 64 (la_rmask_m nb)) ltac:(reflexivity).
      rewrite E1, E2. rewrite <- ELB.
      setreg 13%Z (Z_to_bv 64 ND) ltac:(f_equal; symmetry; rewrite ?(Z.mod_small D 18446744073709551616) by (clear - BR; lia); apply zb_lxor_ones; clear - BR; lia).
      assert (I : KINV m [] a a 0 D D D).
      { apply (KIT INV_init); try assumption; try lia.
        - apply munch_refl.
        - apply munch_refl.
        - apply wmono_refl.
        - rewrite lshift_limbs_gen. reflexivity.
        - rewrite lshift_limbs_gen. reflexivity. }
      eapply evt_eq; [ | eapply (la_loop a m [] 0 D); [ exact P | | exact I | ] ].
      + replace (D - D)%Z with 0%Z by lia. reflexivity.
      + destruct a; [ exfalso; cbn [length] in *; lia | discriminate ].
      + intros m2 y5 y6 y10 y11 y17 HP FR2 ST2 MI2 MU2 WM2. apply K; assumption.
  Qed.
End Proofs.
