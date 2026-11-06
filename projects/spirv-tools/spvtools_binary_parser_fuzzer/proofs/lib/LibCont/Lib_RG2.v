(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib LibIface LibEff MmapSim LibMaskBits S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts S1Facts Lib_RG. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_RG.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_RG.S1_code_6c160_6c3e0. Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_RG.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_RG.S1_code_6b914_6b92c.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Plain.M.loaded_segments.

Ltac rdn_fix H :=
  first [ exact H
        | lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
            lazymatch type of H with rdn _ _ (Z_to_bv 64 ?a') _ = _ =>
              replace a with a' by lia; exact H end end ].
Ltac b2z8 := apply bytes_le_to_Z_8.
Ltac slotv SL k H :=
  pose proof (SL k ltac:(lia)) as H;
  lazymatch type of H with rdn _ _ _ _ = Some (word_to_le_bytes 8 ?v) =>
    let v' := eval simpl in v in change v with v' in H end.
Ltac close_pc := lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end; f_equal; apply bv_eq; vm_compute; reflexivity.
Ltac wl := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ => wlit v | |- _ => idtac end.
Ltac snl F D := stepn F D; pin; wl.

Ltac zval := gres; pin; imm_norm; apply bv_eq; unfold v_add, v_addi, v_sub, v_slli;
  rewrite ?Z_to_bv_unsigned, ?bv_wrap64_mod; imm_norm;
  rewrite ?Z.add_0_r, ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r, ?Z.mod_mod by lia;
  first [ reflexivity | f_equal; lia | rewrite !Z.mod_small by lia; lia ].

Definition X1 : Z := 13057201162865595358.
Definition X156 : Z := 2619718836853156863.
Definition NX0 : Z := 2619718836730839568.
Definition OUT0 : Z := 14514284786278117030.
Lemma mt_init_1 : Znth 1 mt_init = X1. Proof. vm_compute. reflexivity. Qed.
Lemma mt_init_156 : Znth 156 mt_init = X156. Proof. vm_compute. reflexivity. Qed.

Definition K_DIV : Z := 0x14948.  Definition K_A : Z := 0x14a10.  Definition K_B : Z := 0x14980.
Lemma img_K_DIV : rdn SEGS (fun _ => None) (Z_to_bv 64 K_DIV) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 945986875574848801)).
Proof. vm_refl_bv. Qed.
Lemma img_K_A : rdn SEGS (fun _ => None) (Z_to_bv 64 K_A) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 13043109905998158313)).
Proof. vm_refl_bv. Qed.
Lemma img_K_B : rdn SEGS (fun _ => None) (Z_to_bv 64 K_B) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 8202884508482404352)).
Proof. vm_refl_bv. Qed.

Section GTE.
  Context {fx : FPState}.
Context {AC : AllocCeiling}.

  Lemma ENGINE : forall R M (obj ret : Z),
    0 <= obj -> obj + 2504 <= 2 ^ 63 -> alloc_ceiling <= obj -> ro_clear Ly.L M -> mdef M obj 2504 ->
    fld SEGS M (obj + 2496) 8 0 -> fld SEGS M obj 8 5489 -> fld SEGS M (obj + 8) 8 X1 -> fld SEGS M (obj + 1248) 8 X156 ->
    getr R 10%bv = Z_to_bv 64 obj -> getr R 1%bv = Z_to_bv 64 ret -> ret_ok (Z_to_bv 64 ret) ->
    exists R',
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6c31c) M (seg_rom SEGS))
                  (@mkst fx R' (Z_to_bv 64 ret)
                     (wbytes (wbytes M (Z_to_bv 64 obj) (word_to_le_bytes 8 (Z_to_bv 64 NX0))) (Z_to_bv 64 (obj + 2496)) (word_to_le_bytes 8 (Z_to_bv 64 1)))
                     (seg_rom SEGS))
      /\ getr R' 10%bv = Z_to_bv 64 OUT0
      /\ (forall r, ~ In r [5; 6; 10; 11; 12; 13; 14; 15; 16; 17]%bv -> getr R' r = getr R r).
  Proof using fx AC.
    intros R M obj ret Ho0 Ho1 Hoc ROC HD F2496 F0 F1 F156 Ha0 Hra Hret. pose proof ac_bounds_lit as Hcv.
    assert (RO : forall K v, rdn SEGS (fun _ => None) (Z_to_bv 64 K) 8 = Some v -> 0x10000 <= K -> K + 8 <= 0xe6000 ->
                  rdn SEGS M (Z_to_bv 64 K) 8 = Some v).
    { intros K v HK H1 H2. rewrite (ro_rdn M K 8 ROC); [exact HK | lia | cbn; lia]. }
    unfold fld in F2496, F0, F1, F156.
    eexists. split.
    - norm_pc.
      stepiv F_6c2dc D_6c2dc (Z_to_bv 64 (obj + 2047)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; reflexivity).
      snl F_6c2e0 D_6c2e0.
      ld_step F_6c2e4 D_6c2e4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix F2496) ltac:(b2z8).
      snl F_6c2e8 D_6c2e8.
      snl F_6c2ec D_6c2ec.
      ld_step F_6c2f0 D_6c2f0 (word_to_le_bytes 8 (Z_to_bv 64 945986875574848801)) (Z_to_bv 64 945986875574848801)
        ltac:(apply (RO K_DIV); [exact img_K_DIV | unfold K_DIV; lia | unfold K_DIV; lia]) ltac:(b2z8).
      snl F_6c2f4 D_6c2f4.
      snl F_6c2f8 D_6c2f8.
      snl F_6c2fc D_6c2fc. snl F_6c300 D_6c300. snl F_6c304 D_6c304. snl F_6c308 D_6c308.
      snl F_6c30c D_6c30c. snl F_6c310 D_6c310. snl F_6c314 D_6c314. snl F_6c318 D_6c318. snl F_6c31c D_6c31c.
      snl F_6c320 D_6c320. snl F_6c324 D_6c324.
      stepiv F_6c328 D_6c328 (Z_to_bv 64 obj) ltac:(zval).
      snl F_6c32c D_6c32c. snl F_6c330 D_6c330. snl F_6c334 D_6c334. snl F_6c338 D_6c338.
      stepiv F_6c33c D_6c33c (Z_to_bv 64 (obj + 8)) ltac:(zval).
      ld_step F_6c340 D_6c340 (word_to_le_bytes 8 (Z_to_bv 64 5489)) (Z_to_bv 64 5489) ltac:(rdn_fix F0) ltac:(b2z8).
      stepiv F_6c344 D_6c344 (Z_to_bv 64 (obj + 1248)) ltac:(zval).
      ld_step F_6c348 D_6c348 (word_to_le_bytes 8 (Z_to_bv 64 X1)) (Z_to_bv 64 X1) ltac:(rdn_fix F1) ltac:(b2z8).
      ld_step F_6c34c D_6c34c (word_to_le_bytes 8 (Z_to_bv 64 X156)) (Z_to_bv 64 X156) ltac:(rdn_fix F156) ltac:(b2z8).
      unfold X1, X156.
      snl F_6c350 D_6c350. snl F_6c354 D_6c354.
      ld_step F_6c358 D_6c358 (word_to_le_bytes 8 (Z_to_bv 64 13043109905998158313)) (Z_to_bv 64 13043109905998158313)
        ltac:(apply (RO K_A); [exact img_K_A | unfold K_A; lia | unfold K_A; lia]) ltac:(b2z8).
      snl F_6c35c D_6c35c. snl F_6c360 D_6c360. snl F_6c364 D_6c364. snl F_6c368 D_6c368. snl F_6c36c D_6c36c.
      snl F_6c370 D_6c370. snl F_6c374 D_6c374. snl F_6c378 D_6c378.
      stw F_6c37c D_6c37c (Z_to_bv 64 obj) (Z_to_bv 64 NX0) ltac:(ok_mdef HD).
      ld_step F_6c380 D_6c380 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(peel; rdn_fix F2496) ltac:(b2z8).
      snl F_6c384 D_6c384. snl F_6c388 D_6c388. snl F_6c38c D_6c38c. snl F_6c390 D_6c390.
      stepiv F_6c394 D_6c394 (Z_to_bv 64 obj) ltac:(zval).
      ld_step F_6c398 D_6c398 (word_to_le_bytes 8 (Z_to_bv 64 NX0)) (Z_to_bv 64 NX0) ltac:(apply rdn_wbytes_hit8; rewrite u64_of_Z by lia; lia) ltac:(b2z8).
      ld_step F_6c39c D_6c39c (word_to_le_bytes 8 (Z_to_bv 64 8202884508482404352)) (Z_to_bv 64 8202884508482404352)
        ltac:(peel; apply (RO K_B); [exact img_K_B | unfold K_B; lia | unfold K_B; lia]) ltac:(b2z8).
      unfold NX0.
      snl F_6c3a0 D_6c3a0. snl F_6c3a4 D_6c3a4. snl F_6c3a8 D_6c3a8. snl F_6c3ac D_6c3ac. snl F_6c3b0 D_6c3b0.
      snl F_6c3b4 D_6c3b4. snl F_6c3b8 D_6c3b8. snl F_6c3bc D_6c3bc. snl F_6c3c0 D_6c3c0. snl F_6c3c4 D_6c3c4.
      snl F_6c3c8 D_6c3c8. snl F_6c3cc D_6c3cc. snl F_6c3d0 D_6c3d0. snl F_6c3d4 D_6c3d4.
      stw F_6c3d8 D_6c3d8 (Z_to_bv 64 (obj + 2496)) (Z_to_bv 64 1) ltac:(ok_mdef HD).
      stepjr F_6c3dc D_6c3dc (Z_to_bv 64 ret) ltac:(gres; exact Hra).
      lazymatch goal with |- msteps _ (mkst ?r ?pc ?m _) (mkst ?r' ?pc' ?m' _) =>
        unify r' r; replace pc with pc' by (symmetry; imm_norm; exact Hret);
        replace m with m' by (repeat f_equal; apply bv_eq; vm_compute; reflexivity) end.
      apply mst_refl.
    - split.
      + gres. apply bv_eq. vm_compute. reflexivity.
      + intros r Hr. rewrite !getr_other by (intros ->; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto])). reflexivity.
  Qed.

  Lemma UNIF : forall R M (obj P sp ret : Z),
    0 <= obj -> obj + 2504 <= 2 ^ 63 -> alloc_ceiling <= obj -> ro_clear Ly.L M -> mdef M obj 2504 ->
    fld SEGS M (obj + 2496) 8 0 -> fld SEGS M obj 8 5489 -> fld SEGS M (obj + 8) 8 X1 -> fld SEGS M (obj + 1248) 8 X156 ->
    fld SEGS M P 4 0 -> fld SEGS M (P + 4) 4 26 -> 0 <= P -> P + 8 <= 2 ^ 63 ->
    mdef M (sp - 48) 48 -> alloc_ceiling <= sp - 48 -> sp <= 2 ^ 47 ->
    (sp <= P) -> (obj + 2504 <= sp - 48 \/ sp <= obj) -> (P + 8 <= obj \/ obj + 2504 <= P) ->
    getr R 12%bv = Z_to_bv 64 P -> getr R 11%bv = Z_to_bv 64 obj -> getr R 1%bv = Z_to_bv 64 ret -> getr R 2%bv = Z_to_bv 64 sp ->
    ret_ok (Z_to_bv 64 ret) ->
    exists R',
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6c1fc) M (seg_rom SEGS))
                  (@mkst fx R' (Z_to_bv 64 ret)
                     (wbytes (wbytes (wslots M sp [getr R 19%bv; getr R 18%bv; getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret])
                               (Z_to_bv 64 obj) (word_to_le_bytes 8 (Z_to_bv 64 NX0))) (Z_to_bv 64 (obj + 2496)) (word_to_le_bytes 8 (Z_to_bv 64 1)))
                     (seg_rom SEGS))
      /\ getr R' 10%bv = Z_to_bv 64 6 /\ getr R' 2%bv = Z_to_bv 64 sp
      /\ (forall r, ~ In r [5; 6; 10; 11; 12; 13; 14; 15; 16; 17]%bv -> getr R' r = getr R r).
  Proof using fx AC.
    intros R M obj P sp ret Ho0 Ho1 Hoc ROC HD F2496 F0 F1 F156 FP0 FP4 HP0 HP1 HDW Hspc Hsp47 HPsp DJo DJP Ha2 Ha1 Hra Hsp Hret.
    pose proof ac_bounds_lit as Hcv.
    set (M1 := wslots M sp [getr R 19%bv; getr R 18%bv; getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret]).
    assert (SI1 : stores_in (zwin (sp - 40) sp) M M1).
    { unfold M1. eapply stores_in_weaken; [apply wslots_stores_in; unfold Zlen; cbn; lia|]. intros a Ha. unfold zwin, Zlen in *. cbn in *. lia. }
    assert (WSO : forall a (k : nat) v, (a + Z.of_nat k <= sp - 40 \/ sp <= a) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
              rdn SEGS M (Z_to_bv 64 a) k = Some v -> rdn SEGS M1 (Z_to_bv 64 a) k = Some v).
    { intros a k v H1 H2 H3 H4. unfold M1. rewrite wslots_out; [exact H4 | unfold Zlen; cbn; lia | lia | lia | lia | unfold Zlen; cbn; lia]. }
    unfold fld in F2496, F0, F1, F156, FP0, FP4.
    assert (SL : forall k, 1 <= k <= 5 -> rdn SEGS M1 (Z_to_bv 64 (sp - 8 * k)) 8
              = Some (word_to_le_bytes 8 (nth (Z.to_nat (5 - k)) [getr R 19%bv; getr R 18%bv; getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret] (Z_to_bv 64 0)))).
    { intros k Hk. unfold M1. apply wslots_read; unfold Zlen; cbn; lia. }
    slotv SL 1 SL1. slotv SL 2 SL2. slotv SL 3 SL3. slotv SL 4 SL4. slotv SL 5 SL5. clear SL.

    assert (B1 : exists R1, msteps SEGS (@mkst fx R (Z_to_bv 64 0x6c1fc) M (seg_rom SEGS)) (@mkst fx R1 (Z_to_bv 64 0x6c31c) M1 (seg_rom SEGS))
      /\ getr R1 10%bv = Z_to_bv 64 obj /\ getr R1 1%bv = Z_to_bv 64 0x6c2dc /\ getr R1 2%bv = Z_to_bv 64 (sp - 48)
      /\ getr R1 8%bv = Z_to_bv 64 P /\ getr R1 9%bv = Z_to_bv 64 obj /\ getr R1 18%bv = Z_to_bv 64 27 /\ getr R1 19%bv = Z_to_bv 64 31
      /\ (forall r, ~ In r [1; 2; 8; 9; 10; 11; 12; 18; 19]%bv -> getr R1 r = getr R r)).
    { eexists. split.
      - norm_pc.
        sv F_6c1bc D_6c1bc (Z_to_bv 64 (sp - 48)).
        stw F_6c1c0 D_6c1c0 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_mdef HDW).
        stw F_6c1c4 D_6c1c4 (Z_to_bv 64 (sp - 16)) (getr R 8%bv) ltac:(ok_mdef HDW).
        stw F_6c1c8 D_6c1c8 (Z_to_bv 64 (sp - 24)) (getr R 9%bv) ltac:(ok_mdef HDW).
        stw F_6c1cc D_6c1cc (Z_to_bv 64 (sp - 32)) (getr R 18%bv) ltac:(ok_mdef HDW).
        stw F_6c1d0 D_6c1d0 (Z_to_bv 64 (sp - 40)) (getr R 19%bv) ltac:(ok_mdef HDW).
        sv F_6c1d4 D_6c1d4 (Z_to_bv 64 P).
        ld_step F_6c1d8 D_6c1d8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
          ltac:(apply (WSO P 4%nat); [cbn; lia | lia | cbn; lia | rdn_fix FP0]) ltac:(apply lwu_val; lia). wl.
        ld_step F_6c1dc D_6c1dc (word_to_le_bytes 4 (Z_to_bv 64 26)) (Z_to_bv 64 26)
          ltac:(apply (WSO (P + 4) 4%nat); [cbn; lia | lia | cbn; lia | rdn_fix FP4]) ltac:(apply lwu_val; lia). wl.
        stepb F_6c1e0 D_6c1e0.
        sv F_6c1e4 D_6c1e4 (Z_to_bv 64 obj).
        snl F_6c1e8 D_6c1e8. snl F_6c1ec D_6c1ec.
        stepb F_6c1f0 D_6c1f0.
        snl F_6c1f4 D_6c1f4. snl F_6c1f8 D_6c1f8. snl F_6c1fc D_6c1fc. snl F_6c200 D_6c200.
        snl F_6c204 D_6c204. snl F_6c208 D_6c208. snl F_6c20c D_6c20c. snl F_6c210 D_6c210.
        snl F_6c214 D_6c214. snl F_6c218 D_6c218. snl F_6c21c D_6c21c. snl F_6c220 D_6c220.
        snl F_6c224 D_6c224. snl F_6c228 D_6c228. snl F_6c22c D_6c22c. snl F_6c230 D_6c230.
        snl F_6c234 D_6c234. snl F_6c238 D_6c238. snl F_6c23c D_6c23c. snl F_6c240 D_6c240.
        snl F_6c244 D_6c244. snl F_6c248 D_6c248. snl F_6c24c D_6c24c. snl F_6c250 D_6c250.
        snl F_6c254 D_6c254. snl F_6c258 D_6c258. snl F_6c25c D_6c25c. snl F_6c260 D_6c260.
        snl F_6c264 D_6c264. snl F_6c268 D_6c268. snl F_6c26c D_6c26c. snl F_6c270 D_6c270.
        snl F_6c274 D_6c274. snl F_6c278 D_6c278. snl F_6c27c D_6c27c. snl F_6c280 D_6c280.
        snl F_6c284 D_6c284. snl F_6c288 D_6c288. snl F_6c28c D_6c28c. snl F_6c290 D_6c290.
        sv F_6c294 D_6c294 (Z_to_bv 64 obj).
        stepj F_6c298 D_6c298.
        fold M1. close_pc.
      - gres. repeat split; try reflexivity; try assumption; try (apply bv_eq; vm_compute; reflexivity).
        intros r Hr. rewrite !getr_other by (intros ->; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto])). reflexivity. }
    destruct B1 as (R1 & RUN1 & G10 & G1 & G2 & G8 & G9 & G18 & G19 & GS1).
    assert (HD1 : mdef M1 obj 2504) by (eapply stores_in_mdef; [exact SI1 | exact HD]).
    assert (ROC1 : ro_clear Ly.L M1) by (eapply ro_clear_stores; [exact ROC | exact SI1 | intros a Ha; unfold zwin in Ha; lia]).
    destruct (ENGINE R1 M1 obj 0x6c2dc Ho0 Ho1 Hoc ROC1 HD1
                ltac:(apply (WSO (obj + 2496) 8%nat); [cbn; lia | lia | cbn; lia | exact F2496])
                ltac:(apply (WSO obj 8%nat); [cbn; lia | lia | cbn; lia | exact F0])
                ltac:(apply (WSO (obj + 8) 8%nat); [cbn; lia | lia | cbn; lia | exact F1])
                ltac:(apply (WSO (obj + 1248) 8%nat); [cbn; lia | lia | cbn; lia | exact F156])
                G10 G1 ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity)) as (R2 & RUN2 & G2_10 & GS2).
    set (M3 := wbytes (wbytes M1 (Z_to_bv 64 obj) (word_to_le_bytes 8 (Z_to_bv 64 NX0))) (Z_to_bv 64 (obj + 2496)) (word_to_le_bytes 8 (Z_to_bv 64 1))) in *.
    assert (G2_18 : getr R2 18%bv = Z_to_bv 64 27) by (rewrite GS2 by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact G18).
    assert (G2_19 : getr R2 19%bv = Z_to_bv 64 31) by (rewrite GS2 by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact G19).
    assert (G2_8 : getr R2 8%bv = Z_to_bv 64 P) by (rewrite GS2 by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact G8).
    assert (G2_2 : getr R2 2%bv = Z_to_bv 64 (sp - 48)) by (rewrite GS2 by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact G2).
    assert (SLT : forall a vv, (a + 8 <= obj \/ obj + 2504 <= a) -> 0 <= a -> a + 8 < 2 ^ 64 ->
              rdn SEGS M1 (Z_to_bv 64 a) 8 = Some vv -> rdn SEGS M3 (Z_to_bv 64 a) 8 = Some vv).
    { intros a vv H1 H2 H3 H4. unfold M3. rewrite !rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia). exact H4. }
    assert (FP0' : rdn SEGS M3 (Z_to_bv 64 P) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))).
    { unfold M3. rewrite !rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia). apply (WSO P 4%nat); [cbn; lia | lia | cbn; lia | exact FP0]. }
    eexists. split; [|split; [|split]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. norm_pc.
      snl F_6c29c D_6c29c. snl F_6c2a0 D_6c2a0.
      stepb_ft F_6c2a4 D_6c2a4 ltac:(rewrite G2_18; vm_compute; reflexivity).
      ld_step F_6c2a8 D_6c2a8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix FP0') ltac:(apply lwu_val; lia). wl.
      snl F_6c2ac D_6c2ac.
      stepj F_6c2b0 D_6c2b0.
      snl F_6c2bc D_6c2bc.
      ld_step F_6c2c0 D_6c2c0 (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret) ltac:(apply SLT; [lia|lia|lia| rdn_fix SL1]) ltac:(b2z8).
      ld_step F_6c2c4 D_6c2c4 (word_to_le_bytes 8 (getr R 8%bv)) (getr R 8%bv) ltac:(apply SLT; [lia|lia|lia| rdn_fix SL2]) ltac:(b2z8).
      ld_step F_6c2c8 D_6c2c8 (word_to_le_bytes 8 (getr R 9%bv)) (getr R 9%bv) ltac:(apply SLT; [lia|lia|lia| rdn_fix SL3]) ltac:(b2z8).
      ld_step F_6c2cc D_6c2cc (word_to_le_bytes 8 (getr R 18%bv)) (getr R 18%bv) ltac:(apply SLT; [lia|lia|lia| rdn_fix SL4]) ltac:(b2z8).
      ld_step F_6c2d0 D_6c2d0 (word_to_le_bytes 8 (getr R 19%bv)) (getr R 19%bv) ltac:(apply SLT; [lia|lia|lia| rdn_fix SL5]) ltac:(b2z8).
      sv F_6c2d4 D_6c2d4 (Z_to_bv 64 sp).
      stepjr F_6c2d8 D_6c2d8 (Z_to_bv 64 ret) ltac:(gres; reflexivity).
      lazymatch goal with |- msteps _ (mkst ?r ?pc ?m _) (mkst ?r' ?pc' ?m' _) =>
        unify r' r; replace pc with pc' by (symmetry; imm_norm; exact Hret) end.
      apply mst_refl.
    - gres. apply bv_eq. vm_compute. reflexivity.
    - gres. reflexivity.
    - intros r Hr.
      destruct (bv_eq_dec _ r 2%bv) as [->|N2]; [gres; symmetry; exact Hsp|].
      destruct (bv_eq_dec _ r 1%bv) as [->|N1]; [gres; symmetry; exact Hra|].
      destruct (bv_eq_dec _ r 8%bv) as [->|N8]; [gres; reflexivity|].
      destruct (bv_eq_dec _ r 9%bv) as [->|N9]; [gres; reflexivity|].
      destruct (bv_eq_dec _ r 18%bv) as [->|N18]; [gres; reflexivity|].
      destruct (bv_eq_dec _ r 19%bv) as [->|N19]; [gres; reflexivity|].
      repeat (rewrite getr_other; [| first [assumption | intros ->; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto])]]).
      rewrite GS2 by (intros HH; apply Hr; revert HH; (first [solve [clear; cbv; tauto] | cbv; tauto])). apply GS1.
      cbv. intros HH; decompose [or] HH; clear HH; subst; try contradiction; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto]).
  Qed.
End GTE.

Theorem rg_gettargetenv_6c0fc_spec {AC : AllocCeiling} : rg_gettargetenv_stmt SEGS Ly.L cRG.
Proof.
  intros fx M R sp ret obj. cbn [rc_gettargetenv rc_gte_stack cRG]. lazy zeta.
  intros ROC Ho0 Ho1 SEEDED DJ HROOM Hspc Hsp47 Hsp16 Hoc Ho8 Hret Hra Hsp Ha0.
  pose proof ac_bounds_lit as Hcv. unfold RG_SZ in *.
  destruct SEEDED as (HD & FJ & FI). unfold MT_N in FJ, FI.
  assert (DJo : obj + 2504 <= sp - 96 \/ sp <= obj).
  { destruct (Z.lt_ge_cases obj sp); [left|right; lia].
    destruct (Z.lt_ge_cases (obj + 2504) (sp - 96 + 1)); [lia|]. exfalso.
    destruct (Z.lt_ge_cases obj (sp - 96)).
    - apply (DJ (sp - 96)); unfold zwin; lia.
    - apply (DJ obj); unfold zwin; lia. }
  clear DJ.
  assert (HDW : mdef M (sp - 96) 96).
  { unfold stack_room in HROOM. eapply store_ok_mdef_offimg; [exact HROOM | lia | lia | lia |]. intros w Hw. apply ly_noseg. lia. }
  set (Mg0 := wslots M sp [getr R 18%bv; getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret]).
  set (Mg := wbytes (wbytes Mg0 (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (sp - 36)) (word_to_le_bytes 4 (Z_to_bv 64 26))).
  assert (SIg : stores_in (zwin (sp - 40) sp) M Mg).
  { unfold Mg, Mg0. eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_weaken; [apply wslots_stores_in; unfold Zlen; cbn; lia|] | | |] | | |];
      rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; unfold Zlen; cbn; try lia; intros a Ha; unfold zwin in *; lia. }
  assert (AGg : forall a (k : nat) v, (a + Z.of_nat k <= sp - 40 \/ sp <= a) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
            rdn SEGS M (Z_to_bv 64 a) k = Some v -> rdn SEGS Mg (Z_to_bv 64 a) k = Some v).
  { intros a k v H1 H2 H3 H4. rewrite <- H4. apply rdn_agree_win; [lia|lia|]. eapply stores_in_agree; [exact SIg|].
    intros x Hx. unfold zwin in *. lia. }
  assert (SL : forall k, 1 <= k <= 4 -> rdn SEGS Mg0 (Z_to_bv 64 (sp - 8 * k)) 8
            = Some (word_to_le_bytes 8 (nth (Z.to_nat (4 - k)) [getr R 18%bv; getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret] (Z_to_bv 64 0)))).
  { intros k Hk. unfold Mg0. apply wslots_read; unfold Zlen; cbn; lia. }
  slotv SL 1 SL1. slotv SL 2 SL2. slotv SL 3 SL3. slotv SL 4 SL4. clear SL.

  set (R1 := regupd (regupd (regupd (regupd (regupd (regupd (regupd R
              2%bv (Z_to_bv 64 (sp - 48))) 8%bv (Z_to_bv 64 obj)) 18%bv (Z_to_bv 64 26))
              10%bv (Z_to_bv 64 (sp - 40))) 12%bv (Z_to_bv 64 (sp - 40))) 11%bv (Z_to_bv 64 obj)) 1%bv (Z_to_bv 64 0x6c1d4)).
  assert (RUN1 : msteps SEGS (@mkst fx R (Z_to_bv 64 0x6c1a0) M (seg_rom SEGS)) (@mkst fx R1 (Z_to_bv 64 0x6c1fc) Mg (seg_rom SEGS))).
  { unfold R1. norm_pc.
    sv F_6c160 D_6c160 (Z_to_bv 64 (sp - 48)).
    stw F_6c164 D_6c164 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_mdef HDW).
    stw F_6c168 D_6c168 (Z_to_bv 64 (sp - 16)) (getr R 8%bv) ltac:(ok_mdef HDW).
    stw F_6c16c D_6c16c (Z_to_bv 64 (sp - 24)) (getr R 9%bv) ltac:(ok_mdef HDW).
    stw F_6c170 D_6c170 (Z_to_bv 64 (sp - 32)) (getr R 18%bv) ltac:(ok_mdef HDW).
    sv F_6c174 D_6c174 (Z_to_bv 64 obj).
    sv F_6c178 D_6c178 (Z_to_bv 64 26).
    stw F_6c17c D_6c17c (Z_to_bv 64 (sp - 40)) (Z_to_bv 64 0) ltac:(ok_mdef HDW).
    stw F_6c180 D_6c180 (Z_to_bv 64 (sp - 36)) (Z_to_bv 64 26) ltac:(ok_mdef HDW).
    sv F_6c184 D_6c184 (Z_to_bv 64 (sp - 40)).
    sv F_6c188 D_6c188 (Z_to_bv 64 (sp - 40)).
    sv F_6c18c D_6c18c (Z_to_bv 64 obj).
    stepj F_6c190 D_6c190.
    lazymatch goal with |- msteps _ (mkst ?r ?pc ?m _) (mkst ?r' ?pc' ?m' _) =>
      change m with m'; replace pc with pc' by (apply bv_eq; vm_compute; reflexivity) end. apply mst_refl. }
  destruct (UNIF R1 Mg obj (sp - 40) (sp - 48) 0x6c1d4 Ho0 ltac:(lia) Hoc
              ltac:(eapply ro_clear_stores; [exact ROC | exact SIg | intros a Ha; unfold zwin in Ha; lia])
              ltac:(eapply stores_in_mdef; [exact SIg | exact HD])
              ltac:(apply (AGg (obj + 2496) 8%nat); [cbn; lia | lia | cbn; lia | exact FI])
              ltac:(apply (AGg obj 8%nat); [cbn; lia | lia | cbn; lia | pose proof (FJ 0 ltac:(lia)) as X; rewrite mt_init_0, Z.mul_0_r, Z.add_0_r in X; exact X])
              ltac:(apply (AGg (obj + 8) 8%nat); [cbn; lia | lia | cbn; lia | pose proof (FJ 1 ltac:(lia)) as X; rewrite mt_init_1 in X; exact X])
              ltac:(apply (AGg (obj + 1248) 8%nat); [cbn; lia | lia | cbn; lia | pose proof (FJ 156 ltac:(lia)) as X; rewrite mt_init_156 in X; exact X])
              ltac:(unfold fld, Mg; rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia); apply rdn_wbytes_hit4; rewrite u64_of_Z by lia; lia)
              ltac:(unfold fld, Mg; replace (sp - 40 + 4) with (sp - 36) by lia; apply rdn_wbytes_hit4; rewrite u64_of_Z by lia; lia)
              ltac:(lia) ltac:(lia)
              ltac:(replace (sp - 48 - 48) with (sp - 96) by lia; eapply stores_in_mdef; [exact SIg|]; eapply mdef_sub; [exact HDW | lia | lia])
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold R1; gres; reflexivity) ltac:(unfold R1; gres; reflexivity) ltac:(unfold R1; gres; reflexivity) ltac:(unfold R1; gres; reflexivity)
              ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity))
    as (R3 & RUN3 & G3_10 & G3_2 & GS3).
  set (Mu := wbytes (wbytes (wslots Mg (sp - 48) [getr R1 19%bv; getr R1 18%bv; getr R1 9%bv; getr R1 8%bv; Z_to_bv 64 0x6c1d4])
                     (Z_to_bv 64 obj) (word_to_le_bytes 8 (Z_to_bv 64 NX0))) (Z_to_bv 64 (obj + 2496)) (word_to_le_bytes 8 (Z_to_bv 64 1))) in *.
  assert (SIu : stores_in (fun a => zwin (sp - 88) (sp - 48) a \/ zwin obj (obj + 2504) a) Mg Mu).
  { unfold Mu. eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_weaken; [apply wslots_stores_in; unfold Zlen; cbn; lia|] | | |] | | |];
      rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; unfold Zlen; cbn; try lia; intros a Ha; unfold zwin in *; lia. }
  assert (SLT : forall a vv, sp - 32 <= a -> a + 8 <= sp -> rdn SEGS Mg0 (Z_to_bv 64 a) 8 = Some vv -> rdn SEGS Mu (Z_to_bv 64 a) 8 = Some vv).
  { intros a vv H1 H2 H3. rewrite <- H3.
    transitivity (rdn SEGS Mg (Z_to_bv 64 a) 8).
    - apply rdn_agree_win; [lia | cbn; lia |]. eapply stores_in_agree; [exact SIu|]. intros x Hx. unfold zwin in *. cbn in Hx. lia.
    - unfold Mg. rewrite !rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia). reflexivity. }
  assert (G3_8 : getr R3 8%bv = Z_to_bv 64 obj) by (rewrite GS3 by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); unfold R1; gres; reflexivity).
  assert (SI : stores_in (fun a => zwin obj (obj + 2504) a \/ zwin (sp - 96) sp a) M Mu).
  { eapply stores_in_trans; [eapply stores_in_weaken; [exact SIg|]; intros a Ha; right; unfold zwin in *; lia |].
    eapply stores_in_weaken; [exact SIu|]. intros a [Ha|Ha]; [right; unfold zwin in *; lia | left; exact Ha]. }
  eexists. exists Mu. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN3|]. norm_pc.
    snl F_6c194 D_6c194.
    stepj F_6c198 D_6c198.
    snl F_6b914 D_6b914. snl F_6b918 D_6b918. snl F_6b91c D_6b91c. snl F_6b920 D_6b920. snl F_6b924 D_6b924.
    stepjr F_6b928 D_6b928 (Z_to_bv 64 0x6c1dc) ltac:(gres; reflexivity).
    stepb_ft F_6c19c D_6c19c ltac:(vm_compute; reflexivity).
    snl F_6c1a0 D_6c1a0.
    ld_step F_6c1a4 D_6c1a4 (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret) ltac:(apply SLT; [lia|lia|rdn_fix SL1]) ltac:(b2z8).
    ld_step F_6c1a8 D_6c1a8 (word_to_le_bytes 8 (getr R 8%bv)) (getr R 8%bv) ltac:(apply SLT; [lia|lia|rdn_fix SL2]) ltac:(b2z8).
    ld_step F_6c1ac D_6c1ac (word_to_le_bytes 8 (getr R 9%bv)) (getr R 9%bv) ltac:(apply SLT; [lia|lia|rdn_fix SL3]) ltac:(b2z8).
    ld_step F_6c1b0 D_6c1b0 (word_to_le_bytes 8 (getr R 18%bv)) (getr R 18%bv) ltac:(apply SLT; [lia|lia|rdn_fix SL4]) ltac:(b2z8).
    sv F_6c1b4 D_6c1b4 (Z_to_bv 64 sp).
    stepjr F_6c1b8 D_6c1b8 (Z_to_bv 64 ret) ltac:(gres; reflexivity).
    lazymatch goal with |- msteps _ (mkst ?r ?pc ?m _) (mkst ?r' ?pc' ?m' _) =>
      unify r' r; replace pc with pc' by (symmetry; imm_norm; exact Hret) end. apply mst_refl.
  - intros r Hr. unfold callee_saved in Hr.
    destruct (bv_eq_dec _ r 1%bv) as [->|N1]; [gres; symmetry; exact Hra|].
    destruct (bv_eq_dec _ r 2%bv) as [->|N2]; [gres; symmetry; exact Hsp|].
    destruct (bv_eq_dec _ r 8%bv) as [->|N8]; [gres; reflexivity|].
    destruct (bv_eq_dec _ r 9%bv) as [->|N9]; [gres; reflexivity|].
    destruct (bv_eq_dec _ r 18%bv) as [->|N18]; [gres; reflexivity|].
    repeat (rewrite getr_other; [| first [assumption | intros ->; cbv in Hr; intuition discriminate]]).
    rewrite GS3 by (cbv; intros HH; decompose [or] HH; clear HH; subst; cbv in Hr; intuition discriminate).
    unfold R1. repeat (rewrite getr_other; [| first [assumption | intros ->; cbv in Hr; intuition discriminate]]). reflexivity.
  - gres. apply bv_eq. vm_compute. reflexivity.
  - eapply stores_in_mdef; [exact SI | exact HD].
  - eapply stores_in_frame_eq; [exact SI|]. intros a Ha; exact Ha.
  - exact (proj2 SI).
  - eapply ro_clear_stores; [exact ROC | exact SI |]. intros a [Ha|Ha]; unfold zwin in Ha; lia.
Qed.
