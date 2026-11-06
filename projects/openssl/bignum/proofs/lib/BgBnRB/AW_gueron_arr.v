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
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem BnArith BnLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW2 Require W_from_mont_loops.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnE Require W_gueron_arr.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop UbKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Notation mixl := W_from_mont_loops.mixl.
Notation mixl_length := W_from_mont_loops.mixl_length.
Notation mixl_step := W_from_mont_loops.mixl_step.
Notation gfin := W_gueron_arr.gfin.
Notation gfin_length := W_gueron_arr.gfin_length.
Notation gfin_nth := W_gueron_arr.gfin_nth.
Notation gfin_mixl := W_gueron_arr.gfin_mixl.
Notation g_lxor_ones64 := W_gueron_arr.g_lxor_ones64.

Definition ub_kind (pc : Z) : Z :=
  match pc with
  | 2857980 => 2
  | 2857984 => 2
  | _ => 0
  end%Z.
Ltac ub := repeat (ub1 ub_kind).

Section WithRegs.
  Variables (sp gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Notation SP := (bv_unsigned sp).
  Variables (ra t2 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (x7 : word)
            (m : word -> option byte) (lo RD MD : Z) (R M : list Z) (j : nat).
  Variable POST : machine_state -> Prop.
  Hypothesis LR : limbs R.
  Hypothesis LM : limbs M.
  Hypothesis J1 : (1 <= j)%nat.
  Hypothesis JR : (j <= length R)%nat.
  Hypothesis JM : (j <= length M)%nat.
  Hypothesis J31 : (Z.of_nat j < 2^31)%Z.
  Hypothesis DJ : (MD + 8 * Z.of_nat (length M) <= RD \/ RD + 8 * Z.of_nat (length R) <= MD)%Z.
  Hypothesis ACM : acc bgbsegs m MD (8 * Z.of_nat j).
  Hypothesis ACR : acc bgbsegs m RD (8 * Z.of_nat j).
  Hypothesis ALM : (MD mod 8 = 0)%Z.
  Hypothesis ALR : (RD mod 8 = 0)%Z.
  Hypothesis BDM : (0 <= MD /\ MD + 8 * Z.of_nat j <= 140737488355328)%Z.
  Hypothesis BDR : (0 <= RD /\ RD + 8 * Z.of_nat j <= 140737488355328)%Z.
  Hypothesis OFFR : offshW [(RD, RD + 8 * Z.of_nat j)]%Z.

  Notation SH pc mm x5 x12 x13 x17 :=
    (MS (mkR ra sp gp tp x5 (Z_to_bv 64 SHB) x7 s0 s1 (Z_to_bv 64 MD) (Z_to_bv 64 RD) x12 x13 (Z_to_bv 64 (18446744073709551615 - MD)) (Z_to_bv 64 (18446744073709551615 - RD))
             (Z_to_bv 64 (8 * Z.of_nat j)) x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bgbsegs)).

  Definition GKONT : Prop := forall m' x5 x12 x13 x17,
    munch [(RD, RD + 8 * Z.of_nat j)]%Z m m' -> wmono bgbsegs m m' -> mem_inv bgbsegs m' ->
    u64arr bgbsegs m' RD (wlimbs (gfin R M j)) -> u64arr bgbsegs m' MD (wlimbs M) -> stk bgbsegs m' lo SP ->
    evt bgbsegs POST (SH 2858048 m' x5 x12 x13 x17).

  Definition GINV (m1 : word -> option byte) (i : nat) : Prop :=
    u64arr bgbsegs m1 RD (wlimbs (mixl i (gfin R M j) R)) /\ u64arr bgbsegs m1 MD (wlimbs M) /\ mem_inv bgbsegs m1
    /\ munch [(RD, RD + 8 * Z.of_nat j)]%Z m m1 /\ wmono bgbsegs m m1 /\ stk bgbsegs m1 lo SP.

  Lemma gueron_loopB : forall K i m1 (x5 x12 x13 : word),
    GKONT -> (j - i = K)%nat -> (1 <= i < j)%nat -> GINV m1 i ->
    evt bgbsegs POST (SH 2857980 m1 x5 x12 x13 (Z_to_bv 64 (8 * Z.of_nat i))).
  Proof.
    intros K. induction K as [|K IH]; intros i m1 x5 x12 x13 KONT HK Hi (UR & UM & MI & MU & WM & ST); [lia|].
    pose proof (gfin_length R M j JR JM) as LS.
    pose proof (u64arr_bound _ _ _ _ UR) as BR. rewrite wlimbs_len, mixl_length in BR by lia.
    pose proof (u64arr_bound _ _ _ _ UM) as BM. rewrite wlimbs_len in BM.
    assert (Rx : (0 <= nth i M 0 < 18446744073709551616)%Z) by (rewrite <- BW_lit; apply limbs_nth; exact LM).
    assert (NTHM : nth_error (wlimbs M) (Z.to_nat (Z.of_nat i)) = Some (Z_to_bv 64 (nth i M 0%Z))).
    { rewrite Nat2Z.id. unfold wlimbs. erewrite map_nth_error; [reflexivity|]. rewrite (nth_error_nth' _ 0%Z) by lia. reflexivity. }
    ub.
    do 3 zstep.
    (let ad := cur_mem_addr in
     pose proof (acc_rd_limb bgbsegs _ m m1 MD (Z.of_nat j) 0 (Z.of_nat i) ad ACM MU OFFR ALM BDM eq_refl ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - Hi; lia)
                   ltac:(sh_addr)) as RD0); zstep; clear RD0.
    chk0.
    do 3 zstep.
    (let ad := cur_mem_addr in
     pose proof (acc_rd_limb bgbsegs _ m m1 RD (Z.of_nat j) 0 (Z.of_nat i) ad ACR MU OFFR ALR BDR eq_refl ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - Hi; lia)
                   ltac:(sh_addr)) as RD0); zstep; clear RD0.
    chk0.
    (let ad := cur_mem_addr in
     pose proof (u64arr_read bgbsegs m1 MD _ (Z.of_nat i) _ ad UM NTHM ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD0); zstep; clear RD0.
    zstep.
    rewrite (g_lxor_ones64 (nth i M 0%Z)) by lia.
    set (v := (18446744073709551615 - nth i M 0)%Z).
    assert (Ev : v = nth i (gfin R M j) 0%Z) by (subst v; rewrite gfin_nth by lia; unfold BW; lia).
    zstep.
    assert (IDXR : (0 <= Z.of_nat i < Z.of_nat (length (wlimbs (mixl i (gfin R M j) R))))%Z) by (rewrite wlimbs_len, mixl_length by lia; lia).
    pose proof (u64arr_store_ok bgbsegs m1 RD _ (Z.of_nat i) (wa (RD + 8 * Z.of_nat i)) UR IDXR eq_refl) as SOKW.
    pose proof (u64arr_write bgbsegs m1 RD _ (Z.of_nat i) (Z_to_bv 64 v) UR IDXR) as UR2.
    pose proof (u64arr_frame bgbsegs m1 MD _ (RD + 8 * Z.of_nat i) (le8 (Z_to_bv 64 v)) UM ltac:(lia) ltac:(rewrite length_le8; lia)
                  ltac:(rewrite length_le8, wlimbs_len; lia)) as UM2.
    clear UR UM.
    zstep. store_done.
    rewrite Nat2Z.id, Ev, mixl_step in UR2 by lia.
    clear NTHM IDXR Ev Rx. subst v.
    replace (8 * Z.of_nat i + 8)%Z with (8 * Z.of_nat (S i))%Z by lia.
    zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit, ?Z.mod_small in KB by lia.
    - eapply (IH (S i)); [exact KONT| lia| lia|]. split; [exact UR2|]. split; [exact UM2|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM| exact ST].
    - assert (EJ : S i = j) by lia.
      rewrite EJ, gfin_mixl in UR2 by lia.
      eapply KONT; [exact MU| exact WM| exact MI| exact UR2| exact UM2| exact ST].
  Qed.
End WithRegs.
