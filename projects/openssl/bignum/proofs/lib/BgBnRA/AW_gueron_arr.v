(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr ZBridge. 
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BgWords BgExp.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW2 Require W_from_mont_loops.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnE Require W_gueron_arr.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Notation mixl := W_from_mont_loops.mixl.
Notation mixl_length := W_from_mont_loops.mixl_length.
Notation mixl_0 := W_from_mont_loops.mixl_0.
Notation mixl_step := W_from_mont_loops.mixl_step.
Notation gfin := W_gueron_arr.gfin.
Notation gfin_length := W_gueron_arr.gfin_length.
Notation gfin_limbs := W_gueron_arr.gfin_limbs.
Notation gfin_nth0 := W_gueron_arr.gfin_nth0.
Notation gfin_nth := W_gueron_arr.gfin_nth.
Notation gfin_mixl := W_gueron_arr.gfin_mixl.
Notation g_to_bv_mod64 := W_gueron_arr.g_to_bv_mod64.
Notation g_lxor_ones64 := W_gueron_arr.g_lxor_ones64.

Lemma shad_next : forall a, (a mod 8 = 0)%Z -> (shad a + 1 = shad (a + 8))%Z.
Proof. intros a H. unfold shad. Z.div_mod_to_equations. lia. Qed.

Section WithRegs.
  Variables (sp gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Notation SP := (bv_unsigned sp).
  Variables (ra t0 t1 t2 s1 a7 s2 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word)
            (m : word -> option byte) (lo RD MD : Z) (R M : list Z) (j : nat).
  Variable POST : machine_state -> Prop.
  Hypothesis LR : limbs R.
  Hypothesis LM : limbs M.
  Hypothesis J1 : (1 <= j)%nat.
  Hypothesis JR : (j <= length R)%nat.
  Hypothesis JM : (j <= length M)%nat.
  Hypothesis J31 : (Z.of_nat j < 2^31)%Z.
  Hypothesis DJ : (MD + 8 * Z.of_nat (length M) <= RD \/ RD + 8 * Z.of_nat (length R) <= MD)%Z.

  Hypothesis ACM : acc bgasegs m MD (8 * Z.of_nat j).
  Hypothesis ACR : acc bgasegs m RD (8 * Z.of_nat j).
  Hypothesis ALM : (MD mod 8 = 0)%Z.
  Hypothesis ALR : (RD mod 8 = 0)%Z.
  Hypothesis BDM : (0 <= MD /\ MD + 8 * Z.of_nat j <= 140737488355328)%Z.
  Hypothesis BDR : (0 <= RD /\ RD + 8 * Z.of_nat j <= 140737488355328)%Z.
  Hypothesis OFFR : offshW [(RD, RD + 8 * Z.of_nat j)]%Z.

  Notation SH pc mm x10 x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 (Z.of_nat j)) (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgasegs)).

  Definition GKONT : Prop := forall m' x10 x11 x12 x13 x14 x15 x16,
    munch [(RD, RD + 8 * Z.of_nat j)]%Z m m' -> wmono bgasegs m m' -> mem_inv bgasegs m' ->
    u64arr bgasegs m' RD (wlimbs (gfin R M j)) -> u64arr bgasegs m' MD (wlimbs M) -> stk bgasegs m' lo SP ->
    evt bgasegs POST (SH 0x2af684 m' x10 x11 x12 x13 x14 x15 x16).

  Definition GINV (m1 : word -> option byte) (i : nat) : Prop :=
    u64arr bgasegs m1 RD (wlimbs (mixl i (gfin R M j) R)) /\ u64arr bgasegs m1 MD (wlimbs M) /\ mem_inv bgasegs m1
    /\ munch [(RD, RD + 8 * Z.of_nat j)]%Z m m1 /\ wmono bgasegs m m1 /\ stk bgasegs m1 lo SP.

  Lemma gueron_loopA : forall K i m1 (x16 : word),
    GKONT -> (j - i = K)%nat -> (1 <= i < j)%nat -> GINV m1 i ->
    evt bgasegs POST
      (SH 0x2af644 m1 (Z_to_bv 64 (MD + 8 * Z.of_nat i)) (Z_to_bv 64 (RD + 8 * Z.of_nat i)) (Z_to_bv 64 (RD + 8 * Z.of_nat i)) (Z_to_bv 64 (MD + 8 * Z.of_nat i))
          (Z_to_bv 64 (shad (MD + 8 * Z.of_nat i))) (Z_to_bv 64 (Z.of_nat j - Z.of_nat i)) x16).
  Proof.
    intros K. induction K as [|K IH]; intros i m1 x16 KONT HK Hi (UR & UM & MI & MU & WM & ST); [lia|].
    pose proof (gfin_length R M j JR JM) as LS.
    pose proof (u64arr_bound _ _ _ _ UR) as BR. rewrite wlimbs_len, mixl_length in BR by lia.
    pose proof (u64arr_bound _ _ _ _ UM) as BM. rewrite wlimbs_len in BM.
    assert (Rx : (0 <= nth i M 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LM).
    assert (NTHM : nth_error (wlimbs M) (Z.to_nat (Z.of_nat i)) = Some (Z_to_bv 64 (nth i M 0%Z))).
    { rewrite Nat2Z.id. unfold wlimbs. erewrite map_nth_error; [reflexivity|]. rewrite (nth_error_nth' _ 0%Z) by lia. reflexivity. }

    (let ad := cur_mem_addr in
     pose proof (acc_rd_limb bgasegs _ m m1 MD (Z.of_nat j) 0 (Z.of_nat i) ad ACM MU OFFR ALM BDM eq_refl ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - Hi; lia)
                   ltac:(unfold wa; f_equal; f_equal; clear; lia)) as RD0); zstep; clear RD0.
    chk0.

    do 2 zstep.
    (let ad := cur_mem_addr in
     pose proof (acc_rd_limb bgasegs _ m m1 RD (Z.of_nat j) 0 (Z.of_nat i) ad ACR MU OFFR ALR BDR eq_refl ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - Hi; lia)
                   ltac:(sh_addr)) as RD0); zstep; clear RD0.
    chk0.
    (let ad := cur_mem_addr in
     pose proof (u64arr_read bgasegs m1 MD _ (Z.of_nat i) _ ad UM NTHM ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD0); zstep; clear RD0.
    do 4 zstep.
    zstep.
    rewrite (g_lxor_ones64 (nth i M 0%Z)) by lia.
    set (v := (18446744073709551615 - nth i M 0)%Z).
    assert (Ev : v = nth i (gfin R M j) 0%Z) by (subst v; rewrite gfin_nth by lia; unfold BW; lia).
    assert (IDXR : (0 <= Z.of_nat i < Z.of_nat (length (wlimbs (mixl i (gfin R M j) R))))%Z) by (rewrite wlimbs_len, mixl_length by lia; lia).
    pose proof (u64arr_store_ok bgasegs m1 RD _ (Z.of_nat i) (wa (RD + 8 * Z.of_nat i)) UR IDXR eq_refl) as SOKW.
    pose proof (u64arr_write bgasegs m1 RD _ (Z.of_nat i) (Z_to_bv 64 v) UR IDXR) as UR2.
    pose proof (u64arr_frame bgasegs m1 MD _ (RD + 8 * Z.of_nat i) (le8 (Z_to_bv 64 v)) UM ltac:(lia) ltac:(rewrite length_le8; lia)
                  ltac:(rewrite length_le8, wlimbs_len; lia)) as UM2.
    clear UR UM.
    zstep. store_done.
    rewrite Nat2Z.id, Ev, mixl_step in UR2 by lia.
    clear NTHM IDXR Ev Rx. subst v.

    zstep. zstep.
    replace (RD + 8 * Z.of_nat i + 8)%Z with (RD + 8 * Z.of_nat (S i))%Z by lia.
    replace (MD + 8 * Z.of_nat i + 8)%Z with (MD + 8 * Z.of_nat (S i))%Z by lia.
    replace (shad (MD + 8 * Z.of_nat i) + 1)%Z with (shad (MD + 8 * Z.of_nat (S i)))%Z
      by (rewrite shad_next by (clear - ALM; Z.div_mod_to_equations; lia); f_equal; clear; lia).
    replace (Z.of_nat j - Z.of_nat i + -1)%Z with (Z.of_nat j - Z.of_nat (S i))%Z by (clear; lia).
    zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit, ?Z.mod_small in KB by lia.
    - eapply (IH (S i)); [exact KONT| lia| lia|]. split; [exact UR2|]. split; [exact UM2|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM| exact ST].
    - assert (EJ : S i = j) by lia.
      rewrite EJ, gfin_mixl in UR2 by lia.
      eapply KONT; [exact MU| exact WM| exact MI| exact UR2| exact UM2| exact ST].
  Qed.

  Lemma gueron_fill_walkA : forall (x12 x13 x14 x15 x16 : word),
    GKONT ->
    u64arr bgasegs m RD (wlimbs R) -> u64arr bgasegs m MD (wlimbs M) -> mem_inv bgasegs m -> stk bgasegs m lo SP ->
    evt bgasegs POST (SH 0x2af614 m (Z_to_bv 64 MD) (Z_to_bv 64 RD) x12 x13 x14 x15 x16).
  Proof.
    intros x12 x13 x14 x15 x16 KONT UR UM MI ST.
    pose proof (gfin_length R M j JR JM) as LS.
    pose proof (u64arr_bound _ _ _ _ UR) as BR. rewrite wlimbs_len in BR.
    pose proof (u64arr_bound _ _ _ _ UM) as BM. rewrite wlimbs_len in BM.
    pose proof (munch_refl [(RD, RD + 8 * Z.of_nat j)]%Z m) as MU. pose proof (wmono_refl bgasegs m) as WM.
    assert (Rx : (0 <= nth 0 M 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LM).
    assert (NTH0 : nth_error (wlimbs M) (Z.to_nat 0) = Some (Z_to_bv 64 (nth 0 M 0%Z))).
    { change (Z.to_nat 0) with 0%nat. unfold wlimbs. erewrite map_nth_error; [reflexivity|]. rewrite (nth_error_nth' _ 0%Z) by lia. reflexivity. }
    (let ad := cur_mem_addr in
     pose proof (u64arr_read bgasegs m MD _ 0 _ ad UM NTH0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD0); zstep; clear RD0 NTH0.
    zstep.
    rewrite (g_to_bv_mod64 (0 - nth 0 M 0%Z)). change ((0 - nth 0 M 0) mod 18446744073709551616)%Z with (negw (nth 0 M 0%Z)).
    set (v := negw (nth 0 M 0%Z)).
    assert (Ev : v = nth 0 (gfin R M j) 0%Z) by (subst v; rewrite gfin_nth0 by lia; reflexivity).
    zstep.
    assert (IDXR : (0 <= Z.of_nat 0 < Z.of_nat (length (wlimbs R)))%Z) by (rewrite wlimbs_len; lia).
    pose proof (u64arr_store_ok bgasegs m RD _ (Z.of_nat 0) (wa RD) UR IDXR ltac:(unfold wa; f_equal; lia)) as SOKW.
    pose proof (u64arr_write bgasegs m RD _ (Z.of_nat 0) (Z_to_bv 64 v) UR IDXR) as UR2.
    pose proof (u64arr_frame bgasegs m MD _ RD (le8 (Z_to_bv 64 v)) UM ltac:(lia) ltac:(rewrite length_le8; lia)
                  ltac:(rewrite length_le8, wlimbs_len; lia)) as UM2.
    replace (wa (RD + 8 * Z.of_nat 0)) with (wa RD) in UR2 by (unfold wa; f_equal; lia).
    clear UR UM.
    zstep. store_done.
    rewrite Nat2Z.id, Ev in UR2. replace (wlimbs R) with (wlimbs (mixl 0 (gfin R M j) R)) in UR2 by (rewrite mixl_0; reflexivity).
    rewrite mixl_step in UR2 by lia.
    clear IDXR Ev Rx. subst v.

    zstep. rewrite lts_signed by lia.
    destruct (Z.ltb_spec (Z.of_nat j) 2) as [J2|J2].
    -
      assert (EJ : j = 1%nat) by lia.
      replace 1%nat with j in UR2 by lia. rewrite gfin_mixl in UR2 by lia.
      eapply KONT; [exact MU| exact WM| exact MI| exact UR2| exact UM2| exact ST].
    - do 7 zstep.

      replace (RD + 8)%Z with (RD + 8 * Z.of_nat 1)%Z by lia.
      replace (MD + 8)%Z with (MD + 8 * Z.of_nat 1)%Z by lia.
      setreg 14%Z (Z_to_bv 64 (shad (MD + 8 * Z.of_nat 1))) ltac:(unfold shad; f_equal; rewrite ?Z.shiftr_div_pow2 by (clear; lia); clear; lia).
      replace (Z.of_nat j + -1)%Z with (Z.of_nat j - Z.of_nat 1)%Z by (clear; lia).
      eapply (gueron_loopA (j - 1)%nat 1%nat); [exact KONT| lia| lia|].
      split; [exact UR2|]. split; [exact UM2|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM| exact ST].
  Qed.
End WithRegs.
