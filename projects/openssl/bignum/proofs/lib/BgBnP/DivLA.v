(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnArith BnLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Definition la_fl (lb x y c : Z) : Z := Z.lor (shlw x lb) c.
Definition la_fc (lb x y c : Z) : Z := if (lb =? 0)%Z then 0%Z else shrw x (64 - lb).

Lemma lshift_limbs_gen : forall lb l m, lshift_limbs l lb m = gen_words_c (la_fl lb) (la_fc lb) l l m.
Proof.
  intros lb. induction l as [|x l IH]; intros m; [reflexivity|].
  cbn [lshift_limbs gen_words_c]. rewrite IH. reflexivity.
Qed.

Lemma la_fc_range : forall lb, (0 <= lb < 64)%Z ->
  forall x y c, (0 <= x < 18446744073709551616)%Z -> (0 <= y < 18446744073709551616)%Z -> (0 <= c <= 18446744073709551615)%Z ->
  (0 <= la_fc lb x y c <= 18446744073709551615)%Z.
Proof.
  intros lb Hlb x y c Hx Hy Hc. unfold la_fc, shrw. destruct (lb =? 0)%Z; [lia|].
  assert (0 < 2 ^ (64 - lb))%Z by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|]. assert (x / 2 ^ (64 - lb) <= x)%Z; [|lia].
  apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

Lemma la_carry : forall lb x y c, (0 <= lb < 64)%Z -> (0 <= x < 18446744073709551616)%Z ->
  Z.land (Z.shiftr x (((64 - lb) mod 64) mod 64)) (if (lb =? 0)%Z then 0 else 18446744073709551615)%Z = la_fc lb x y c.
Proof.
  intros lb x y c LB Hx. unfold la_fc. destruct (Z.eqb_spec lb 0) as [E|NE]; [apply Z.land_0_r|].
  rewrite (Z.mod_small (64 - lb)) by lia. rewrite (Z.mod_small (64 - lb)) by lia.
  change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  unfold shrw. rewrite Z.shiftr_div_pow2 by lia. apply Z.mod_small.
  assert (0 < 2 ^ (64 - lb))%Z by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|]. change (2 ^ 64)%Z with 18446744073709551616%Z.
  assert (x / 2 ^ (64 - lb) <= x)%Z; [|lia]. apply Z.div_le_upper_bound; [lia|]. nia.
Qed.

Definition la_rsh_m (nb : Z) : Z :=
  bv_swrap 32 (nb - Z.land ((nb + Z.shiftr ((Z.shiftl nb 1) mod 18446744073709551616) 58) mod 18446744073709551616) 18446744073709551552).
Definition la_rmask_m (nb : Z) : Z :=
  Z.lor (Z.shiftr ((bv_swrap 32 (0 - la_rsh_m nb mod 18446744073709551616)) mod 18446744073709551616) 8)
        ((bv_swrap 32 (0 - la_rsh_m nb mod 18446744073709551616)) mod 18446744073709551616).
Definition la_chk (nb : Z) : bool :=
  (la_rsh_m nb =? (64 - (64 - nb)) mod 64)%Z && (la_rmask_m nb =? (if (64 - nb =? 0)%Z then 0 else 18446744073709551615))%Z.
Lemma la_chk_all : forallb la_chk (map Z.of_nat (seq 1 64)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma la_mirror : forall nb, (1 <= nb <= 64)%Z ->
  la_rsh_m nb = ((64 - (64 - nb)) mod 64)%Z /\ la_rmask_m nb = (if (64 - nb =? 0)%Z then 0 else 18446744073709551615)%Z.
Proof.
  intros nb H. pose proof la_chk_all as A. rewrite forallb_forall in A.
  specialize (A nb). unfold la_chk in A. rewrite andb_true_iff, !Z.eqb_eq in A. apply A.
  apply in_map_iff. exists (Z.to_nat nb). split; [lia|]. apply in_seq. lia.
Qed.

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

  Notation ST pc mm x9 x11 x13 x14 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 x9 (Z_to_bv 64 rsh) x11 (Z_to_bv 64 rmask) x13 x14 a5 a6 a7 s2 (Z_to_bv 64 (D + 8 * n)) s4 s5 (Z_to_bv 64 lb) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgpsegs)).

  Lemma LEN : length a = length a. Proof. reflexivity. Qed.
  Lemma ALA : alias_ok D D n. Proof. left. reflexivity. Qed.
  Notation FCR := (la_fc_range lb LB).
  Notation RES := (fst (lshift_limbs a lb 0)).
  Notation CY := (snd (lshift_limbs a lb 0)).
  Notation KINV := (INV bgpsegs (la_fl lb) (la_fc lb) 18446744073709551615 m D D D SP lo a FS FB FCELLS RES CY).
  Notation KIT L := (L bgpsegs (la_fl lb) (la_fc lb) 18446744073709551615%Z FCR m D D D SP lo a a FS FB FCELLS FS_ok FBE
                        LEN ALA ALA SEPR SEPR SEPR RES CY).
  Notation K_rdA := (KIT INV_rdA).
  Notation K_store := (KIT INV_store).   Notation K_store_ok := (KIT INV_store_ok).
  Notation K_done := (KIT INV_done).   Notation K_len := (KIT INV_len).   Notation K_carry := (KIT INV_carry).
  Notation K_rangeA := (KIT INV_rangeA).   Notation K_ptrs := (KIT INV_ptrs).

  Ltac ldA I := let L := constr:(K_rdA) in ldA_with L I.
  Ltac w64eq := unfold la_fl, shlw; clear - LB; f_equal; rewrite (Z.mod_small lb 64) by lia; rewrite Z.shiftl_mul_pow2 by lia; reflexivity.
  Ltac st_limb I l cn Ecn := let L1 := constr:(K_store_ok) in let L2 := constr:(K_store) in st_limb_with L1 L2 w64eq I l cn Ecn.

  Lemma la_loop : forall la m1 pre c pa x13 x14,
    la <> [] -> KINV m1 pre la la c pa pa pa ->
    (forall m2 x9 x11 x13 x14,
       limbs_at bgpsegs m2 D RES -> rw_cells bgpsegs m2 FB FCELLS -> stk bgpsegs m2 lo FB -> mem_inv bgpsegs m2 ->
       munch [(D, D + 8 * n); (SP - FS, SP)]%Z m m2 -> wmono bgpsegs m m2 ->
       evt bgpsegs POST (ST 0xfec48 m2 x9 x11 x13 x14)) ->
    evt bgpsegs POST (ST 0xfec28 m1 (Z_to_bv 64 pa) (Z_to_bv 64 c) x13 x14).
  Proof.
    induction la as [|x la IH]; intros m1 pre c pa x13 x14 NE I K; [congruence|].
    pose proof (K_len _ _ _ _ _ _ _ _ I) as (El & En & Epr & TOP & R0).
    pose proof (K_rangeA _ _ _ _ _ _ _ _ _ I) as Rx. pose proof (K_carry _ _ _ _ _ _ _ _ I) as Hc.
    ldA I.
    zstep. zstep. zstep.
    st_limb I l c' Ec'.
    zstep. zstep.
    rewrite (la_carry lb x x c LB Rx), <- Ec'.
    assert (Hc' : (0 <= c' <= 18446744073709551615)%Z) by (clear - Rx Hc Ec' LB; subst c'; apply (la_fc_range lb LB); assumption).
    clear Ec'.
    zstep. if_cases KB; zify_cond KB.
    -
      eapply IH; [ | exact I | exact K ].
      destruct la; [ exfalso | discriminate ].
      pose proof (K_len _ _ _ _ _ _ _ _ I) as (El2 & En2 & Epr2 & _). cbn [length] in *. lia.
    -
      destruct la as [|x' la'].
      + pose proof (K_done _ _ _ _ _ _ I) as (HP & CYE & FR & ST & MI & MU & WM).
        apply K; assumption.
      + exfalso. pose proof (K_len _ _ _ _ _ _ _ _ I) as (El2 & En2 & Epr2 & _). cbn [length] in *. lia.
  Qed.

  Notation ST2 pc mm x9 x10 x11 x12 x13 x14 x22 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 x9 x10 x11 x12 x13 x14 a5 a6 a7 s2 (Z_to_bv 64 (D + 8 * n)) s4 s5 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgpsegs)).

  Lemma la_block : forall nb,
    (1 <= nb <= 64)%Z -> lb = (64 - nb)%Z -> bv_unsigned s4 = n -> (n < 2^31)%Z ->
    limbs a -> limbs_at bgpsegs m D a -> wr_at bgpsegs m D (8 * n) ->
    rw_cells bgpsegs m FB FCELLS -> stk bgpsegs m lo FB -> mem_inv bgpsegs m ->
    (forall m2 x9 x10 x11 x12 x13 x14,
       limbs_at bgpsegs m2 D RES -> rw_cells bgpsegs m2 FB FCELLS -> stk bgpsegs m2 lo FB -> mem_inv bgpsegs m2 ->
       munch [(D, D + 8 * n); (SP - FS, SP)]%Z m m2 -> wmono bgpsegs m m2 ->
       evt bgpsegs POST (ST2 0xfec48 m2 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 lb))) ->
    evt bgpsegs POST (ST2 0xfebf8 m (Z_to_bv 64 D) (Z_to_bv 64 nb) a1 a2 a3 a4 s6).
  Proof.
    intros nb NB ELB S4 N31 LA RA WR FR STK MI K.
    zstep. zstep.
    rewrite (bn_swrap32_small (64 - nb)) by (clear - NB; lia). rewrite <- ELB.
    zstep.
    if_cases KZ; zify_cond KZ.
    -
      assert (a = []) by (destruct a; [reflexivity | exfalso; cbn [length] in *; lia]).
      apply K; try assumption.
      + subst a. apply limbs_at_nil. pose proof (limbs_at_bound _ _ _ _ RA). lia.
      + apply munch_refl.
      + apply wmono_refl.
    - do 9 zstep.
      destruct (la_mirror nb NB) as [E1 E2].
      setreg 10%Z (Z_to_bv 64 (la_rsh_m nb)) ltac:(reflexivity).
      setreg 12%Z (Z_to_bv 64 (la_rmask_m nb)) ltac:(reflexivity).
      rewrite E1, E2. rewrite <- ELB.
      assert (I : KINV m [] a a 0 D D D).
      { apply (KIT INV_init); try assumption; try lia.
        - apply munch_refl.
        - apply munch_refl.
        - apply wmono_refl.
        - rewrite lshift_limbs_gen. reflexivity.
        - rewrite lshift_limbs_gen. reflexivity. }
      eapply evt_eq; [ | eapply (la_loop a m [] 0 D); [ | exact I | ] ].
      + reflexivity.
      + destruct a; [ exfalso; cbn [length] in *; lia | discriminate ].
      + intros m2 x9 x11 x13 x14 HP FR2 ST2 MI2 MU2 WM2. apply K; assumption.
  Qed.
End Proofs.
