(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemsetLib As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac RefMemcpyLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r7b264_7b528.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import EbtPoison EbtPoisonRun EbtPoison2G Eb0RegionPoisoned EbtAnnotate.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
#[local] Abbreviation SB := EbtPoison.SB.

Definition RD (x : Z) : Z := x - x mod 8.
Definition RU (x : Z) : Z := RD (x + 7).

Lemma RD_eq x : RD x = x / 8 * 8.
Proof. unfold RD. pose proof (Z.div_mod x 8 ltac:(lia)). lia. Qed.
Lemma RD_mod x : RD x mod 8 = 0.
Proof. rewrite RD_eq. apply Z_mod_mult. Qed.
Lemma RD_range x : 0 <= x -> x - 7 <= RD x <= x /\ RD x mod 8 = 0 /\ 0 <= RD x.
Proof. intros Hx. pose proof (RD_mod x) as M8. unfold RD in *. pose proof (Z.mod_pos_bound x 8 ltac:(lia)). pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.div_pos x 8 Hx ltac:(lia)). repeat split; first [assumption | lia]. Qed.
Lemma RU_range x : 0 <= x -> x <= RU x <= x + 7 /\ RU x mod 8 = 0.
Proof. intros Hx. unfold RU. pose proof (RD_range (x + 7) ltac:(lia)) as (A & B & C). repeat split; first [assumption | lia]. Qed.
Lemma RD_div x : 0 <= x -> RD x / 8 = x / 8.
Proof. intros Hx. rewrite RD_eq. apply Z.div_mul. lia. Qed.
Lemma RU_div x : 0 <= x -> RU x / 8 = (x + 7) / 8.
Proof. intros Hx. unfold RU. apply RD_div. lia. Qed.
Lemma RD_mono x y : x <= y -> RD x <= RD y.
Proof. intros H. rewrite !RD_eq. assert (x / 8 <= y / 8) by (apply Z.div_le_mono; lia). lia. Qed.
Lemma RD_id x : x mod 8 = 0 -> RD x = x.
Proof. intros H. unfold RD. lia. Qed.
Lemma RD_add b x : b mod 8 = 0 -> RD (b + x) = b + RD x.
Proof. intros Hb. unfold RD. rewrite Z.add_mod, Hb, Z.add_0_l, Z.mod_mod by lia. lia. Qed.
Lemma RU_add b x : b mod 8 = 0 -> RU (b + x) = b + RU x.
Proof. intros Hb. unfold RU. rewrite <- Z.add_assoc. apply RD_add. exact Hb. Qed.
Lemma mod8_add b x : b mod 8 = 0 -> (b + x) mod 8 = x mod 8.
Proof. intros Hb. rewrite Z.add_mod, Hb, Z.add_0_l, Z.mod_mod by lia. reflexivity. Qed.

Lemma art_annU_and7 : forall x, 0 <= x < 2 ^ 64 -> v_andi (Z_to_bv 64 x) 7 = Z_to_bv 64 (x mod 8).
Proof. intros x Hx. rewrite art_zb_andi by lia. f_equal. rewrite Z.land_ones with (n := 3) by lia. reflexivity. Qed.
Lemma art_annU_andm8 : forall x, 0 <= x < 2 ^ 64 -> v_andi (Z_to_bv 64 x) (-8) = Z_to_bv 64 (RD x).
Proof.
  intros x Hx. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia.
  f_equal. rewrite RD_eq. reflexivity.
Qed.

Lemma art_annU_lb_252 : v_lb (Z_to_bv 8 252) = Z_to_bv 64 18446744073709551612.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma art_signed_range : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small; lia.
Qed.
Lemma art_c_lts_small : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> c_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold c_lts, bv_lts. rewrite !art_signed_range by lia. reflexivity. Qed.
Lemma art_c_lts_neg4 : forall x, 0 <= x < 2 ^ 63 -> c_lts (Z_to_bv 64 x) (Z_to_bv 64 18446744073709551612) = false.
Proof.
  intros x Hx. unfold c_lts, bv_lts. rewrite art_signed_range by lia.
  replace (Z_to_bv 64 18446744073709551612) with (Z_to_bv 64 (-4)) by (apply bv_eq; vm_compute; reflexivity).
  rewrite art_signed_range by lia. apply Z.ltb_ge. lia.
Qed.

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_annU_chk0 : forall regs (M rom : word -> option byte) (b c u u' : Z),
  getr regs 18 = Z_to_bv 64 (b + u') -> getr regs 19 = Z_to_bv 64 (b + u) -> getr regs 20 = Z_to_bv 64 (b + c) ->
  0 <= b -> b + c < 2 ^ 47 -> 0 <= u <= c -> 0 <= u' <= c -> u <> u' -> b mod 8 = 0 -> c mod 8 = 0 ->
  exists regs', msteps ASEGS (mkst regs (0x7cd40 : word) M rom) (mkst regs' (0x7cd4c : word) M rom)
    /\ (forall r : reg, r <> 10%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom b c u u' H18 H19 H20 Hb Hbc Hu Hu' Ne Hb8 Hc8.
  eexists. split.
  { zbft F_7ccf0 D_7ccf0.
    stepn F_7ccf4 D_7ccf4. rwH. rewrite art_annU_and7 by lia. rewrite (mod8_add b c Hb8), Hc8.
    zbft F_7ccf8 D_7ccf8.
    apply mst_refl. }
  intros r Hr. gres. rewrite getr_other by (exact Hr). reflexivity.
Qed.

#[using="Type"] Lemma art_annU_chkU : forall regs (M rom : word -> option byte) (b c u u' v : Z),
  getr regs 18 = Z_to_bv 64 (b + u') -> getr regs 19 = Z_to_bv 64 (b + u) -> getr regs 20 = Z_to_bv 64 (b + c) ->
  0 <= b -> b + c < 2 ^ 47 -> 0 <= u <= c -> 0 <= u' <= c -> u <> u' -> b mod 8 = 0 -> c mod 8 <> 0 ->
  cellA M 0x13d8c8 8 0x1460f8 -> cellA M 0x1460f8 8 SB -> cellA M (SB + (b + c) / 8) 1 v -> (v = 252 \/ 1 <= v <= c mod 8) ->
  exists regs', msteps ASEGS (mkst regs (0x7cd40 : word) M rom) (mkst regs' (0x7cd4c : word) M rom)
    /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 21%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom b c u u' v H18 H19 H20 Hb Hbc Hu Hu' Ne Hb8 Hc8 CG CS CV Hv.
  pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as Rc. pose proof (RD_range (b + c) ltac:(lia)) as (R1 & R2 & R3).
  assert (ERD : RD (b + c) = b + RD c) by (apply RD_add; exact Hb8). pose proof (RD_range c ltac:(lia)) as (Q1 & Q2 & Q3).

  assert (STEP1 : exists r1, msteps ASEGS (mkst regs (0x7cd40 : word) M rom) (mkst r1 (0x7cdb8 : word) M rom)
            /\ getr r1 10 = Z_to_bv 64 (c mod 8) /\ getr r1 11 = Z_to_bv 64 (b + Z.max u u') /\ getr r1 21 = Z_to_bv 64 (RD (b + c))
            /\ getr r1 20 = Z_to_bv 64 (b + c)
            /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 21%bv -> getr r1 r = getr regs r)).
  { destruct (Z_lt_le_dec u' u) as [Lt|Ge].
    - eexists. split.
      { zbft F_7ccf0 D_7ccf0.
        stepn F_7ccf4 D_7ccf4. rwH. rewrite art_annU_and7 by lia. rewrite (mod8_add b c Hb8).
        zbtk F_7ccf8 D_7ccf8.
        stepn F_7cd58 D_7cd58. rwH. rewrite art_annU_andm8 by lia.
        zstep F_7cd5c D_7cd5c.
        zbtk F_7cd60 D_7cd60.
        apply mst_refl. }
      rewrite Z.max_l by lia. split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
      intros r N10 N11 N21. gres. rewrite !getr_other by assumption. reflexivity.
    - eexists. split.
      { zbft F_7ccf0 D_7ccf0.
        stepn F_7ccf4 D_7ccf4. rwH. rewrite art_annU_and7 by lia. rewrite (mod8_add b c Hb8).
        zbtk F_7ccf8 D_7ccf8.
        stepn F_7cd58 D_7cd58. rwH. rewrite art_annU_andm8 by lia.
        zstep F_7cd5c D_7cd5c.
        zbft F_7cd60 D_7cd60.
        zstep F_7cd64 D_7cd64.
        apply mst_refl. }
      rewrite Z.max_r by lia. split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
      intros r N10 N11 N21. gres. rewrite !getr_other by assumption. reflexivity. }
  destruct STEP1 as (r1 & RUN1 & A10 & A11 & A21 & A20 & K1).
  destruct (Z_lt_le_dec (RD (b + c)) (b + Z.max u u')) as [Load|Skip].
  -
    assert (Hcg : (b + c) / 8 = b / 8 + c / 8).
    { pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite Hb8, Z.add_0_r in Db. rewrite Db at 1. rewrite Z.mul_comm, Z.div_add_l by lia. reflexivity. }
    assert (SBr : 0 <= (b + c) / 8 /\ (b + c) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]).
    assert (WALK : forall (P : Prop),
      (v = 252 -> P) -> (1 <= v <= c mod 8 -> P) -> P) by (intros P X Y; destruct Hv as [E|E]; [exact (X E)|exact (Y E)]).
    apply WALK; clear WALK; intros HV.
    + subst v. eexists. split.
      { eapply msteps_trans; [exact RUN1|].
        zbft F_7cd68 D_7cd68.
        zstep F_7cd6c D_7cd6c.
        match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CG' : cellA X 0x13d8c8 8 0x1460f8) by zcell; assert (CS' : cellA X 0x1460f8 8 SB) by zcell;
                                                        assert (CV' : cellA X (SB + (b + c) / 8) 1 252) by zcell end.
        zld F_7cd70 D_7cd70 0x13d8c8 CG'. zld F_7cd74 D_7cd74 0x1460f8 CS'.
        stepn F_7cd78 D_7cd78. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_7cd7c D_7cd7c.
        unfold EbtPoison.SB in *.
        zlb F_7cd80 D_7cd80 (2147450880 + (b + c) / 8) CV'.
        zbft F_7cd84 D_7cd84.
        stepb_tk F_7cd88 D_7cd88 ltac:(rwH; apply art_c_lts_neg4; lia).
        apply mst_refl. }
      intros r N10 N11 N12 N21. gres. rewrite !getr_other by assumption. apply K1; assumption.
    + eexists. split.
      { eapply msteps_trans; [exact RUN1|].
        zbft F_7cd68 D_7cd68.
        zstep F_7cd6c D_7cd6c.
        match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CG' : cellA X 0x13d8c8 8 0x1460f8) by zcell; assert (CS' : cellA X 0x1460f8 8 SB) by zcell;
                                                        assert (CV' : cellA X (SB + (b + c) / 8) 1 v) by zcell end.
        zld F_7cd70 D_7cd70 0x13d8c8 CG'. zld F_7cd74 D_7cd74 0x1460f8 CS'.
        stepn F_7cd78 D_7cd78. rwH. rewrite art_zb_srli by lia. change (2 ^ 3) with 8.
        zstep F_7cd7c D_7cd7c.
        unfold EbtPoison.SB in *.
        zlb F_7cd80 D_7cd80 (2147450880 + (b + c) / 8) CV'. try (rewrite art_v_lb_small by lia).
        zbft F_7cd84 D_7cd84.
        stepb_tk F_7cd88 D_7cd88 ltac:(rwH; rewrite art_c_lts_small by lia; apply Z.ltb_ge; lia).
        apply mst_refl. }
      intros r N10 N11 N12 N21. gres. rewrite !getr_other by assumption. apply K1; assumption.
  - eexists. split.
    { eapply msteps_trans; [exact RUN1|].
      zbtk F_7cd68 D_7cd68.
      apply mst_refl. }
    intros r N10 N11 N12 N21. apply K1; assumption.
Qed.

#[using="Type"] Lemma art_annU_mid : forall regs (M rom : word -> option byte) (b u u' : Z),
  getr regs 9 = Z_to_bv 64 b -> getr regs 18 = Z_to_bv 64 (b + u') -> getr regs 19 = Z_to_bv 64 (b + u) ->
  0 <= b < 2 ^ 47 -> b mod 8 = 0 ->
  exists regs', msteps ASEGS (mkst regs (0x7cd4c : word) M rom) (mkst regs' (0x7cd68 : word) M rom)
    /\ getr regs' 10 = Z_to_bv 64 (b + u) /\ getr regs' 11 = Z_to_bv 64 (b + u) /\ getr regs' 19 = Z_to_bv 64 0
    /\ getr regs' 20 = Z_to_bv 64 (b + u) /\ getr regs' 21 = Z_to_bv 64 (b + u')
    /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 19%bv -> r <> 20%bv -> r <> 21%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom b u u' H9 H18 H19 Hb Hb8.
  eexists. split.
  { zstep F_7ccfc D_7ccfc. zstep F_7cd00 D_7cd00. zstep F_7cd04 D_7cd04.
    stepn F_7cd08 D_7cd08. rwH. rewrite art_annU_and7 by lia. rewrite Hb8.
    zbft F_7cd0c D_7cd0c.
    zstep F_7cd10 D_7cd10. zstep F_7cd14 D_7cd14.
    apply mst_refl. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r N10 N11 N19 N20 N21. gres. rewrite !getr_other by assumption. reflexivity.
Qed.

Lemma RU_RD_partial x : 0 <= x -> x mod 8 <> 0 -> RU x = RD x + 8.
Proof.
  intros Hx H8. unfold RU. rewrite !RD_eq. pose proof (Z.div_mod x 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as R.
  replace (x + 7) with ((x / 8 + 1) * 8 + (x mod 8 - 1)) by lia. rewrite Z.div_add_l by lia. rewrite (Z.div_small (x mod 8 - 1) 8) by lia. lia.
Qed.
Lemma RU_RD_full x : x mod 8 = 0 -> RU x = RD x.
Proof.
  intros H8. unfold RU. rewrite !RD_eq. pose proof (Z.div_mod x 8 ltac:(lia)) as D. rewrite H8 in D.
  replace (x + 7) with ((x / 8) * 8 + 7) by lia. rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia.
Qed.

#[using="Type"] Lemma art_annU_grow_p : forall regs (M rom : word -> option byte) (b c u u' : Z),
  getr regs 10 = Z_to_bv 64 (b + u) -> getr regs 11 = Z_to_bv 64 (b + u) -> getr regs 20 = Z_to_bv 64 (b + u) -> getr regs 21 = Z_to_bv 64 (b + u') ->
  0 <= b -> b + c < 2 ^ 47 -> 0 <= u <= c -> 0 <= u' <= c -> b mod 8 = 0 -> u < u' -> RD u < RD u' ->
  exists regs', msteps ASEGS (mkst regs (0x7cd68 : word) M rom) (mkst regs' (0x7bce4 : word) M rom)
    /\ getr regs' 1 = Z_to_bv 64 0x7ce70 /\ getr regs' 10 = Z_to_bv 64 (b + RD u) /\ getr regs' 11 = Z_to_bv 64 (RD u' - RD u) /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 9 = Z_to_bv 64 (b + RD u') /\ getr regs' 18 = Z_to_bv 64 (b + RU u')
    /\ (forall r : reg, r <> 1%bv -> r <> 9%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 18%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom b c u u' H10 H11 H20 H21 Hb Hbc Hu Hu' Hb8 Lt Hrd.
  pose proof (RD_range u ltac:(lia)) as (R1 & R2 & R3). pose proof (RD_range u' ltac:(lia)) as (Q1 & Q2 & Q3). pose proof (RU_range u' ltac:(lia)) as (P1 & P2).
  eexists. split.
  { zbtk F_7cd18 D_7cd18.
    stepn F_7cde8 D_7cde8. rwH. rewrite art_annU_andm8 by lia. rewrite (RD_add b u Hb8).
    zbft F_7cdec D_7cdec.
    zstep F_7cdf0 D_7cdf0.
    stepn F_7cdf4 D_7cdf4. rwH. rewrite art_annU_andm8 by lia. rewrite (RD_add b u' Hb8).
    zstep F_7cdf8 D_7cdf8.
    stepn F_7cdfc D_7cdfc. rwH. rewrite art_annU_andm8 by lia. replace (b + u' + 7) with (b + (u' + 7)) by lia. rewrite (RD_add b (u' + 7) Hb8). fold (RU u').
    zbtk F_7ce00 D_7ce00.
    zstep F_7cd34 D_7cd34. zstep F_7cd38 D_7cd38.
    stepn F_7cd3c D_7cd3c.
    stepn F_7ce1c D_7ce1c.
    apply mst_refl. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r N1 N9 N10 N11 N12 N18. gres. rewrite !getr_other by assumption. reflexivity.
Qed.

#[using="Type"] Lemma art_annU_grow_d : forall regs (M rom : word -> option byte) (b c u u' : Z),
  getr regs 10 = Z_to_bv 64 (b + u) -> getr regs 11 = Z_to_bv 64 (b + u) -> getr regs 20 = Z_to_bv 64 (b + u) -> getr regs 21 = Z_to_bv 64 (b + u') ->
  0 <= b -> b + c < 2 ^ 47 -> 0 <= u <= c -> 0 <= u' <= c -> b mod 8 = 0 -> u < u' -> RD u = RD u' ->
  exists regs', msteps ASEGS (mkst regs (0x7cd68 : word) M rom) (mkst regs' (0x7ce70 : word) M rom)
    /\ getr regs' 9 = Z_to_bv 64 (b + RD u') /\ getr regs' 18 = Z_to_bv 64 (b + RU u')
    /\ (forall r : reg, r <> 9%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 18%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom b c u u' H10 H11 H20 H21 Hb Hbc Hu Hu' Hb8 Lt Hrd.
  pose proof (RD_range u ltac:(lia)) as (R1 & R2 & R3). pose proof (RD_range u' ltac:(lia)) as (Q1 & Q2 & Q3). pose proof (RU_range u' ltac:(lia)) as (P1 & P2).
  eexists. split.
  { zbtk F_7cd18 D_7cd18.
    stepn F_7cde8 D_7cde8. rwH. rewrite art_annU_andm8 by lia. rewrite (RD_add b u Hb8).
    zbft F_7cdec D_7cdec.
    zstep F_7cdf0 D_7cdf0.
    stepn F_7cdf4 D_7cdf4. rwH. rewrite art_annU_andm8 by lia. rewrite (RD_add b u' Hb8).
    zstep F_7cdf8 D_7cdf8.
    stepn F_7cdfc D_7cdfc. rwH. rewrite art_annU_andm8 by lia. replace (b + u' + 7) with (b + (u' + 7)) by lia. rewrite (RD_add b (u' + 7) Hb8). fold (RU u').
    zbft F_7ce00 D_7ce00.
    zstep F_7ce04 D_7ce04.
    stepn F_7ce08 D_7ce08. rwH. rewrite art_annU_andm8 by lia. replace (b + u' + 7) with (b + (u' + 7)) by lia. rewrite (RD_add b (u' + 7) Hb8). fold (RU u').
    zbtk F_7ce0c D_7ce0c.
    apply mst_refl. }
  split; [kept_solve|]. split; [kept_solve|].
  intros r N9 N10 N11 N12 N18. gres. rewrite !getr_other by assumption. reflexivity.
Qed.

#[using="Type"] Lemma art_annU_shr_p : forall regs (M rom : word -> option byte) (b c u u' : Z),
  getr regs 10 = Z_to_bv 64 (b + u) -> getr regs 11 = Z_to_bv 64 (b + u) -> getr regs 20 = Z_to_bv 64 (b + u) -> getr regs 21 = Z_to_bv 64 (b + u') ->
  0 <= b -> b + c < 2 ^ 47 -> 0 <= u <= c -> 0 <= u' <= c -> b mod 8 = 0 -> u' < u -> RU u' < RU u ->
  exists regs', msteps ASEGS (mkst regs (0x7cd68 : word) M rom) (mkst regs' (0x7bce4 : word) M rom)
    /\ getr regs' 1 = Z_to_bv 64 0x7ce70 /\ getr regs' 10 = Z_to_bv 64 (b + RU u') /\ getr regs' 11 = Z_to_bv 64 (RU u - RU u') /\ getr regs' 12 = Z_to_bv 64 252
    /\ getr regs' 9 = Z_to_bv 64 (b + RD u') /\ getr regs' 18 = Z_to_bv 64 (b + RU u')
    /\ (forall r : reg, r <> 1%bv -> r <> 9%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 18%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom b c u u' H10 H11 H20 H21 Hb Hbc Hu Hu' Hb8 Lt Hru.
  pose proof (RD_range u ltac:(lia)) as (R1 & R2 & R3). pose proof (RD_range u' ltac:(lia)) as (Q1 & Q2 & Q3).
  pose proof (RU_range u' ltac:(lia)) as (P1 & P2). pose proof (RU_range u ltac:(lia)) as (P3 & P4).
  eexists. split.
  { zbft F_7cd18 D_7cd18.
    stepn F_7cd1c D_7cd1c. rwH. rewrite art_annU_andm8 by lia. rewrite (RD_add b u' Hb8).
    zbft F_7cd20 D_7cd20.
    stepn F_7cd24 D_7cd24. rwH. rewrite art_annU_andm8 by lia. rewrite (RD_add b u' Hb8).
    zstep F_7cd28 D_7cd28.
    stepn F_7cd2c D_7cd2c. rwH. rewrite art_annU_andm8 by lia. replace (b + u' + 7) with (b + (u' + 7)) by lia. rewrite (RD_add b (u' + 7) Hb8). fold (RU u').
    zbtk F_7cd30 D_7cd30.
    zstep F_7ce04 D_7ce04.
    stepn F_7ce08 D_7ce08. rwH. rewrite art_annU_andm8 by lia. replace (b + u + 7) with (b + (u + 7)) by lia. rewrite (RD_add b (u + 7) Hb8). fold (RU u).
    zbft F_7ce0c D_7ce0c.
    zstep F_7ce10 D_7ce10. zstep F_7ce14 D_7ce14. zstep F_7ce18 D_7ce18.
    stepn F_7ce1c D_7ce1c.
    apply mst_refl. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r N1 N9 N10 N11 N12 N18. gres. rewrite !getr_other by assumption. reflexivity.
Qed.

#[using="Type"] Lemma art_annU_shr_d : forall regs (M rom : word -> option byte) (b c u u' : Z),
  getr regs 10 = Z_to_bv 64 (b + u) -> getr regs 11 = Z_to_bv 64 (b + u) -> getr regs 20 = Z_to_bv 64 (b + u) -> getr regs 21 = Z_to_bv 64 (b + u') ->
  0 <= b -> b + c < 2 ^ 47 -> 0 <= u <= c -> 0 <= u' <= c -> b mod 8 = 0 -> u' < u -> RU u <= RU u' ->
  exists regs', msteps ASEGS (mkst regs (0x7cd68 : word) M rom) (mkst regs' (0x7ce70 : word) M rom)
    /\ getr regs' 9 = Z_to_bv 64 (b + RD u') /\ getr regs' 18 = Z_to_bv 64 (b + RU u')
    /\ (forall r : reg, r <> 9%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 18%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom b c u u' H10 H11 H20 H21 Hb Hbc Hu Hu' Hb8 Lt Hru.
  pose proof (RD_range u ltac:(lia)) as (R1 & R2 & R3). pose proof (RD_range u' ltac:(lia)) as (Q1 & Q2 & Q3).
  pose proof (RU_range u' ltac:(lia)) as (P1 & P2). pose proof (RU_range u ltac:(lia)) as (P3 & P4).
  eexists. split.
  { zbft F_7cd18 D_7cd18.
    stepn F_7cd1c D_7cd1c. rwH. rewrite art_annU_andm8 by lia. rewrite (RD_add b u' Hb8).
    zbft F_7cd20 D_7cd20.
    stepn F_7cd24 D_7cd24. rwH. rewrite art_annU_andm8 by lia. rewrite (RD_add b u' Hb8).
    zstep F_7cd28 D_7cd28.
    stepn F_7cd2c D_7cd2c. rwH. rewrite art_annU_andm8 by lia. replace (b + u' + 7) with (b + (u' + 7)) by lia. rewrite (RD_add b (u' + 7) Hb8). fold (RU u').
    zbtk F_7cd30 D_7cd30.
    zstep F_7ce04 D_7ce04.
    stepn F_7ce08 D_7ce08. rwH. rewrite art_annU_andm8 by lia. replace (b + u + 7) with (b + (u + 7)) by lia. rewrite (RD_add b (u + 7) Hb8). fold (RU u).
    zbtk F_7ce0c D_7ce0c.
    apply mst_refl. }
  split; [kept_solve|]. split; [kept_solve|].
  intros r N9 N10 N11 N12 N18. gres. rewrite !getr_other by assumption. reflexivity.
Qed.

#[using="Type"] Lemma art_annU_tail_a : forall regs (M rom : word -> option byte) (b u' : Z),
  getr regs 9 = Z_to_bv 64 (b + RD u') -> getr regs 18 = Z_to_bv 64 (b + RU u') -> u' mod 8 = 0 ->
  msteps ASEGS (mkst regs (0x7ce70 : word) M rom) (mkst regs (0x7ce90 : word) M rom).
Proof.
  intros regs M rom b u' H9 H18 H8. rewrite (RU_RD_full u' H8) in H18.
  zbtk F_7ce20 D_7ce20. apply mst_refl.
Qed.

Lemma art_annU_ret_7ce3c : ret_ok (Z_to_bv 64 0x7ce8c).
Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma art_annU_tail_u : forall regs (M rom : word -> option byte) (b c u' : Z),
  getr regs 9 = Z_to_bv 64 (b + RD u') -> getr regs 18 = Z_to_bv 64 (b + RU u') -> getr regs 21 = Z_to_bv 64 (b + u') ->
  0 <= b -> b + c < 2 ^ 47 -> 0 <= u' <= c -> b mod 8 = 0 -> u' mod 8 <> 0 ->
  rt_layout_globs M -> in_app (b + RD u') -> wrA M (SB + (b + RD u') / 8) 1 ->
  exists regs', msteps ASEGS (mkst regs (0x7ce70 : word) M rom) (mkst regs' (0x7ce90 : word) (Wn 1 M (SB + (b + RD u') / 8) (u' mod 8)) rom)
    /\ getr regs' 2 = getr regs 2
    /\ (forall r : reg, In r callee_saved -> r <> 1%bv -> r <> 18%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom b c u' H9 H18 H21 Hb Hbc Hu' Hb8 H8 GL HA W.
  pose proof (RD_range u' ltac:(lia)) as (Q1 & Q2 & Q3). pose proof (RU_RD_partial u' ltac:(lia) H8) as E. pose proof (Z.mod_pos_bound u' 8 ltac:(lia)) as R.
  assert (D0 : 0 <= (b + RD u') / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]).
  assert (RUN1 : exists r1, msteps ASEGS (mkst regs (0x7ce70 : word) M rom) (mkst r1 (0x7c1e0 : word) M rom)
            /\ getr r1 1 = Z_to_bv 64 0x7ce8c /\ getr r1 10 = Z_to_bv 64 (b + RD u') /\ getr r1 18 = Z_to_bv 64 (u' mod 8)
            /\ (forall r : reg, r <> 1%bv -> r <> 10%bv -> r <> 13%bv -> r <> 18%bv -> getr r1 r = getr regs r)).
  { eexists. split.
    { zbft F_7ce20 D_7ce20.
      zstep F_7ce24 D_7ce24. zstep F_7ce28 D_7ce28.
      zbft F_7ce2c D_7ce2c.
      stepn F_7ce30 D_7ce30. rwH. rewrite art_annU_and7 by lia. rewrite (mod8_add b u' Hb8).
      zstep F_7ce34 D_7ce34.
      stepn F_7ce38 D_7ce38.
      apply mst_refl. }
    split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
    intros r N1 N10 N13 N18. gres. rewrite !getr_other by assumption. reflexivity. }
  destruct RUN1 as (r1 & RUN1 & A1 & A10 & A18 & K1).
  destruct (memtoshadow_run r1 M rom (Z_to_bv 64 0x7ce8c) (b + RD u') GL HA A10 A1 art_annU_ret_7ce3c) as (r2 & RUN2 & B10 & K2).
  assert (B18 : getr r2 18 = Z_to_bv 64 (u' mod 8)) by (rewrite (K2 18%bv) by (cbv; tauto); exact A18).
  eexists. split.
  { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
    replace (Z_to_bv 64 0x7ce8c) with (0x7ce8c%bv : word) by (apply bv_eq; vm_compute; reflexivity).
    unfold Eb0RegionPoisoned.SB in B10. unfold EbtPoison.SB in *.
    zsb F_7ce3c D_7ce3c (2147450880 + (b + RD u') / 8) (u' mod 8) ltac:(first [rewok W | zwok]).
    replace ((b + RD u') / 8 + 2147450880) with (2147450880 + (b + RD u') / 8) by lia.
    apply mst_refl. }
  split. { rewrite (K2 2%bv) by (cbv; tauto). apply K1; intros X; discriminate X. }
  intros r Hr N1 N18. rewrite (K2 r Hr). apply K1; [exact N1| intros X | intros X |exact N18]; subst r; exfalso; clear - Hr; cbv [callee_saved In] in Hr;
    repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] | H : False |- _ => destruct H
                           | H : @eq _ _ _ |- _ => apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H end.
Qed.

End FPX.
