(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom LeptSlots LeptExec LeptExecW LeptExecFP LeptExecX DitherLib DitherLoop LeptCmapArr LeptExecB LeptArithB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptUb V2_code_pixBilateralGrayExact V2_code_pixGetDepth V2_code_pixRasterop V2_code_kernelGetParameters.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
(* [comment removed for export] *)
#[local] Opaque RiscvSemantics.store_ok.

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Ltac rinv_tac :=
  repeat (eapply rinv_wbytes;
          [ | rewrite ?length_N_to_le_bytes, ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; reflexivity | lia | lia
          | first [ (eexists; split; [ left; reflexivity | cbn [fst snd]; lia ])
                  | (eexists; split; [ right; left; reflexivity | cbn [fst snd]; lia ]) ] ]);
  apply rinv_refl.
Ltac rdn_solve4 :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
      tryif constr_eq a b then (apply rdn_wbytes_hit4; rewrite ?u_Z2bv by lia; lia)
      else (rdn_peel1; rdn_solve4)
  | |- _ => rdn_hyp
  end.
Ltac post1 :=
  lazymatch goal with
  | |- rinv _ _ _ => rinv_tac
  | |- regs_agree _ _ _ => solve_regs_agree
  | |- rdn _ _ _ _ = Some (word_to_le_bytes 8 _) => gres; rdn_solve
  | |- rdn _ _ _ 8 = Some (Z_to_le_bytes 8 ?z) => rewrite <- (w2b_Z 8 z) by lia; rdn_solve
  | |- rdn _ _ _ 4 = Some (Z_to_le_bytes 4 ?z) => rewrite <- (w2b_Z 4 z) by lia; rdn_solve4
  | |- getr _ _ = _ => gres; pin; first [ reflexivity | apply bv_eq; rewrite ?u_Z2bv by lia; lia ]
  | |- _ = _ => first [ reflexivity | assumption ]
  end.
Ltac fin E :=
  lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ => replace pc with (Z_to_bv 64 E) by (apply bv_eq; reflexivity) end;
  apply mst_refl.
Ltac post := repeat (lazymatch goal with |- _ /\ _ => split end); post1.
Ltac zlitv F D v := stepat F D v ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).
Ltac fixl v := fixv v ltac:(gres; pin; apply bv_eq; vm_compute; reflexivity).
Ltac ldw F D z :=
  stepLD F D (word_to_le_bytes 4 (Z_to_bv 64 z)) (Z_to_bv 64 z) ltac:(addr_norm; rewrite ?Z.add_0_r; rdn_solve4) ltac:(apply bytes_le_to_Z_4; unorm; lia);
  rewrite ?(v_lw_small z) by lia.
Ltac ldz F D z :=
  stepLD F D (Z_to_le_bytes 4 z) (Z_to_bv 64 z) ltac:(addr_norm; rewrite ?Z.add_0_r; rdn_solve4) ltac:(apply lez4; lia);
  rewrite ?(v_lw_small z) by lia.
Ltac lit_addr A :=
  lazymatch goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 A) by (apply bv_eq; vm_compute; reflexivity) end.
Ltac imgrd := apply (bool_decide_eq_true_1 _); vm_compute; reflexivity.
Ltac pgd_walk wc hc dc w h d Rw Rh Rd SOK Ap Awc Ahc Adc :=
  stepiv F_19b38 D_19b38 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_3; unorm; rewrite Awc; reflexivity);
  stepb_ft F_19b3c D_19b3c ltac:(condZ);
  stepb_ft F_19b40 D_19b40 ltac:(condZ);
  stepST F_19b44 D_19b44 (Z_to_bv 64 wc) (Z_to_bv 64 0) ltac:(sok_in SOK);
  stepiv F_19b48 D_19b48 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_3; unorm; rewrite Ahc; reflexivity);
  stepb_ft F_19b4c D_19b4c ltac:(condZ);
  stepb_ft F_19b50 D_19b50 ltac:(condZ);
  stepST F_19b54 D_19b54 (Z_to_bv 64 hc) (Z_to_bv 64 0) ltac:(sok_in SOK);
  stepiv F_19b58 D_19b58 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_3; unorm; rewrite Adc; reflexivity);
  stepb_ft F_19b5c D_19b5c ltac:(condZ);
  stepb_ft F_19b60 D_19b60 ltac:(condZ);
  stepST F_19b64 D_19b64 (Z_to_bv 64 dc) (Z_to_bv 64 0) ltac:(sok_in SOK);
  stepb_ft F_19b68 D_19b68 ltac:(condZ);
  stepiv F_19b6c D_19b6c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite Ap; reflexivity);
  stepb_ft F_19b70 D_19b70 ltac:(condZ);
  stepat F_19b74 D_19b74 (Z_to_bv 64 0) ltac:(gres; first [reflexivity | bveq]);
  stepb_ft F_19b78 D_19b78 ltac:(condZ);
  stepLD F_19b7c D_19b7c (Z_to_le_bytes 4 w) (Z_to_bv 64 w) ltac:(addr_norm; rdn_by Rw) ltac:(apply lez4; lia);
  rewrite ?(v_lw_small w) by lia;
  stepST F_19b80 D_19b80 (Z_to_bv 64 wc) (Z_to_bv 64 w) ltac:(sok_in SOK);
  stepb_ft F_19b84 D_19b84 ltac:(condZ);
  stepat F_19b88 D_19b88 (Z_to_bv 64 0) ltac:(gres; first [reflexivity | bveq]);
  stepb_ft F_19b8c D_19b8c ltac:(condZ);
  stepLD F_19b90 D_19b90 (Z_to_le_bytes 4 h) (Z_to_bv 64 h) ltac:(addr_norm; rdn_by Rh) ltac:(apply lez4; lia);
  rewrite ?(v_lw_small h) by lia;
  stepST F_19b94 D_19b94 (Z_to_bv 64 hc) (Z_to_bv 64 h) ltac:(sok_in SOK);
  stepb_ft F_19b98 D_19b98 ltac:(condZ);
  stepat F_19b9c D_19b9c (Z_to_bv 64 0) ltac:(gres; first [reflexivity | bveq]);
  stepb_ft F_19ba0 D_19ba0 ltac:(condZ);
  stepLD F_19ba4 D_19ba4 (Z_to_le_bytes 4 d) (Z_to_bv 64 d) ltac:(addr_norm; rdn_by Rd) ltac:(apply lez4; lia);
  rewrite ?(v_lw_small d) by lia;
  stepST F_19ba8 D_19ba8 (Z_to_bv 64 dc) (Z_to_bv 64 d) ltac:(sok_in SOK);
  sn F_19bac D_19bac.

Section Segs.
Variable rom : word -> option byte.
#[local] Existing Instance exf_fxd | 100.

Lemma ge_A : forall (fx : FPState) regs (m : word -> option byte) (s pixs skel rkel w h : Z),
  (4096 + 176 <= s <= 2 ^ 47)%Z ->
  (4096 <= pixs)%Z ->
  (pixs + 64 <= s - 176 \/ s <= pixs)%Z ->
  (pixs + 64 <= 2 ^ 47)%Z ->
  rdn SEGS m (Z_to_bv 64 pixs) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 8) ->
  (4096 <= skel)%Z ->
  (skel + 24 <= s - 176 \/ s <= skel)%Z ->
  (skel + 24 <= 2 ^ 47)%Z ->
  rdn SEGS m (Z_to_bv 64 skel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 41)) ->
  rdn SEGS m (Z_to_bv 64 (skel + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 41)) ->
  rdn SEGS m (Z_to_bv 64 (skel + 8)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 20)) ->
  rdn SEGS m (Z_to_bv 64 (skel + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 20)) ->
  (4096 <= rkel)%Z ->
  (rkel + 24 <= s - 176 \/ s <= rkel)%Z ->
  (rkel + 24 <= 2 ^ 47)%Z ->
  rdn SEGS m (Z_to_bv 64 rkel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn SEGS m (Z_to_bv 64 (rkel + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 256)) ->
  (83 <= w < 2 ^ 31)%Z ->
  (83 <= h < 2 ^ 31)%Z ->
  (0x45f0c <= s - 176)%Z ->
  (forall j, (0x44e98 <= j < 0x44ea0)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (0x45f08 <= j < 0x45f0c)%Z -> m (Z_to_bv 64 j) = None) ->
  (s mod 16 = 0)%Z ->
  (pixs mod 8 = 0)%Z ->
  (skel mod 8 = 0)%Z ->
  (rkel mod 8 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 176)) 176 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 pixs ->
  getr regs 11 = Z_to_bv 64 skel ->
  getr regs 12 = Z_to_bv 64 rkel ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3ad78) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x38e54) M' rom /\
      rinv [((s - 176)%Z, 176%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 21)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 22)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (getr regs 23)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 (getr regs 24)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 (getr regs 25)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (getr regs 26)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 (getr regs 27)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) /\ rdn SEGS M' (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) /\ rdn SEGS M' (Z_to_bv 64 (s - 116)) 4 = Some (Z_to_le_bytes 4 8) /\
      rdn SEGS M' (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 41) /\ rdn SEGS M' (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 41) /\
      getr regs' 1 = Z_to_bv 64 0x3ae60 /\ getr regs' 2 = Z_to_bv 64 (s - 176) /\ getr regs' 9 = Z_to_bv 64 pixs /\ getr regs' 18 = Z_to_bv 64 skel /\ getr regs' 8 = Z_to_bv 64 rkel /\
      getr regs' 10 = Z_to_bv 64 skel /\
      regs_agree (fun r => In r [1; 2; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs').
Proof.
  intros fx regs m s pixs skel rkel w h Hs Hp Hps Hp47 Rw Rh Rd Hk Hks Hk47 Rk0 Rk4 Rk8 Rk12 Hr Hrs Hr47 Rr0 Rr4 Hw Hh Hb NG NS ALs ALp ALk ALr SOK H2 H10 H11 H12.
  assert (A108 : ((s - 108) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact ALs | reflexivity]).
  assert (A112 : ((s - 112) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact ALs | reflexivity]).
  assert (A116 : ((s - 116) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact ALs | reflexivity]).
  assert (A120 : ((s - 120) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact ALs | reflexivity]).
  assert (A124 : ((s - 124) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact ALs | reflexivity]).
  unfold reach. eexists. split.
  - norm_pc.
    zv F_3ad78 D_3ad78 (Z_to_bv 64 (s - 176)).
    stepST F_3ad7c D_3ad7c (Z_to_bv 64 (s - 8)) (getr regs 1) ltac:(sok_in SOK).
    stepST F_3ad80 D_3ad80 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_3ad84 D_3ad84 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_3ad88 D_3ad88 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_3ad8c D_3ad8c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepST F_3ad90 D_3ad90 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
    stepST F_3ad94 D_3ad94 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
    stepST F_3ad98 D_3ad98 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
    stepST F_3ad9c D_3ad9c (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
    stepST F_3ada0 D_3ada0 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
    stepST F_3ada4 D_3ada4 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
    stepST F_3ada8 D_3ada8 (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
    stepST F_3adac D_3adac (Z_to_bv 64 (s - 104)) (getr regs 27) ltac:(sok_in SOK).
    stepb_ft F_3adb0 D_3adb0 ltac:(condZ).
    zv F_3adb4 D_3adb4 (Z_to_bv 64 rkel).
    zv F_3adb8 D_3adb8 (Z_to_bv 64 skel).
    zv F_3adbc D_3adbc (Z_to_bv 64 pixs).
    sn F_3adc0 D_3adc0.
    stepb_ft F_1a8cc D_1a8cc ltac:(condZ).
    guard8 F_1a8d0 D_1a8d0 ALp.
    stepb_ft F_1a8d4 D_1a8d4 ltac:(condZ).
    stepLD F_1a8d8 D_1a8d8 (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; rdn_by Rd) ltac:(apply lez4; lia).
    rewrite ?(v_lw_small 8) by lia.
    stepret F_1a8dc D_1a8dc (Z_to_bv 64 0x3adc4) ltac:(bveq).
    zv F_3adc4 D_3adc4 (Z_to_bv 64 8).
    stepb_ft F_3adc8 D_3adc8 ltac:(condZ).
    zv F_3adcc D_3adcc (Z_to_bv 64 (s - 108)).
    zv F_3add0 D_3add0 (Z_to_bv 64 (s - 112)).
    zv F_3add4 D_3add4 (Z_to_bv 64 (s - 116)).
    zv F_3add8 D_3add8 (Z_to_bv 64 pixs).
    sn F_3addc D_3addc.
    pgd_walk (s - 108)%Z (s - 112)%Z (s - 116)%Z w h 8%Z Rw Rh Rd SOK ALp A108 A112 A116.
    stepret F_19bb0 D_19bb0 (Z_to_bv 64 0x3ade0) ltac:(bveq).
    stepb_ft F_3ade0 D_3ade0 ltac:(condZ).
    zv F_3ade4 D_3ade4 (Z_to_bv 64 (s - 124)).
    zv F_3ade8 D_3ade8 (Z_to_bv 64 (s - 120)).
    zv F_3adec D_3adec (Z_to_bv 64 skel).
    zv F_3adf0 D_3adf0 (Z_to_bv 64 0).
    zv F_3adf4 D_3adf4 (Z_to_bv 64 0).
    sn F_3adf8 D_3adf8.
    guard4 F_38860 D_38860 A124.
    stepb_ft F_38864 D_38864 ltac:(condZ).
    stepb_ft F_38868 D_38868 ltac:(condZ).
    stepST F_3886c D_3886c (Z_to_bv 64 (s - 124)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    guard4 F_38870 D_38870 A120.
    stepb_ft F_38874 D_38874 ltac:(condZ).
    stepb_ft F_38878 D_38878 ltac:(condZ).
    stepST F_3887c D_3887c (Z_to_bv 64 (s - 120)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    zlitv F_38880 D_38880 (Z_to_bv 64 0).
    stepb_tk F_38884 D_38884 ltac:(condZ).
    zlitv F_38890 D_38890 (Z_to_bv 64 0).
    stepb_tk F_38894 D_38894 ltac:(condZ).
    stepb_ft F_388a0 D_388a0 ltac:(condZ).
    guard8 F_388a4 D_388a4 ALk.
    stepb_ft F_388a8 D_388a8 ltac:(condZ).
    stepat F_388ac D_388ac (Z_to_bv 64 0) ltac:(gres; first [reflexivity | bveq]).
    stepb_ft F_388b0 D_388b0 ltac:(condZ).
    ldw F_388b4 D_388b4 41%Z.
    stepST F_388b8 D_388b8 (Z_to_bv 64 (s - 124)) (Z_to_bv 64 41) ltac:(sok_in SOK).
    stepb_ft F_388bc D_388bc ltac:(condZ).
    stepat F_388c0 D_388c0 (Z_to_bv 64 0) ltac:(gres; first [reflexivity | bveq]).
    stepb_ft F_388c4 D_388c4 ltac:(condZ).
    ldw F_388c8 D_388c8 41%Z.
    stepST F_388cc D_388cc (Z_to_bv 64 (s - 120)) (Z_to_bv 64 41) ltac:(sok_in SOK).
    stepb_tk F_388d0 D_388d0 ltac:(condZ).
    stepb_tk F_388e4 D_388e4 ltac:(condZ).
    zv F_3892c D_3892c (Z_to_bv 64 0).
    stepret F_38930 D_38930 (Z_to_bv 64 0x3adfc) ltac:(bveq).
    ldw F_3adfc D_3adfc 41%Z.
    zlitv F_3ae00 D_3ae00 (Z_to_bv 64 0x40000000).
    sn F_3ae04 D_3ae04. fixl (Z_to_bv 64 0x40000029).
    stepb_ft F_3ae08 D_3ae08 ltac:(condZ).
    ldw F_3ae0c D_3ae0c w.
    sn F_3ae10 D_3ae10. fixl (Z_to_bv 64 82).
    stepb_ft F_3ae14 D_3ae14 ltac:(condZ).
    ldw F_3ae18 D_3ae18 41%Z.
    zlitv F_3ae1c D_3ae1c (Z_to_bv 64 0x40000000).
    sn F_3ae20 D_3ae20. fixl (Z_to_bv 64 0x40000029).
    stepb_ft F_3ae24 D_3ae24 ltac:(condZ).
    ldw F_3ae28 D_3ae28 h.
    sn F_3ae2c D_3ae2c. fixl (Z_to_bv 64 82).
    stepb_ft F_3ae30 D_3ae30 ltac:(condZ).
    stepb_ft F_3ae34 D_3ae34 ltac:(condZ).
    guard8 F_3ae38 D_3ae38 ALr.
    stepb_ft F_3ae3c D_3ae3c ltac:(condZ).
    ldw F_3ae40 D_3ae40 256%Z.
    zv F_3ae44 D_3ae44 (Z_to_bv 64 256).
    stepb_ft F_3ae48 D_3ae48 ltac:(condZ).
    ldw F_3ae4c D_3ae4c 1%Z.
    zv F_3ae50 D_3ae50 (Z_to_bv 64 1).
    stepb_ft F_3ae54 D_3ae54 ltac:(condZ).
    zv F_3ae58 D_3ae58 (Z_to_bv 64 skel).
    sn F_3ae5c D_3ae5c.
    fin 0x38e54%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma ge_Aw : forall (fx : FPState) regs (m : word -> option byte) (s pixs skel rkel w h : Z),
  (4096 + 176 <= s <= 2 ^ 47)%Z ->
  (4096 <= pixs)%Z ->
  (pixs + 64 <= s - 176 \/ s <= pixs)%Z ->
  (pixs + 64 <= 2 ^ 47)%Z ->
  rdn SEGS m (Z_to_bv 64 pixs) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 8) ->
  (4096 <= skel)%Z ->
  (skel + 24 <= s - 176 \/ s <= skel)%Z ->
  (skel + 24 <= 2 ^ 47)%Z ->
  rdn SEGS m (Z_to_bv 64 skel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 41)) ->
  rdn SEGS m (Z_to_bv 64 (skel + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 41)) ->
  (4096 <= rkel)%Z ->
  (1 <= w < 2 ^ 31)%Z ->
  (1 <= h < 2 ^ 31)%Z ->
  (w <= 82)%Z ->
  (0x45f0c <= s - 176)%Z ->
  (forall j, (0x44e98 <= j < 0x44ea0)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (0x45f08 <= j < 0x45f0c)%Z -> m (Z_to_bv 64 j) = None) ->
  (s mod 16 = 0)%Z ->
  (pixs mod 8 = 0)%Z ->
  (skel mod 8 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 176)) 176 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 pixs ->
  getr regs 11 = Z_to_bv 64 skel ->
  getr regs 12 = Z_to_bv 64 rkel ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3ad78) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x17e28) M' rom /\
      rinv [((s - 176)%Z, 176%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 21)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 22)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (getr regs 23)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 (getr regs 24)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 (getr regs 25)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (getr regs 26)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 (getr regs 27)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) /\ rdn SEGS M' (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) /\
      getr regs' 1 = Z_to_bv 64 0x3aff4 /\ getr regs' 2 = Z_to_bv 64 (s - 176) /\ getr regs' 9 = Z_to_bv 64 pixs /\
      getr regs' 10 = Z_to_bv 64 0x10f60 /\ getr regs' 11 = Z_to_bv 64 0x11f9c /\
      regs_agree (fun r => In r [1; 2; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs').
Proof.
  intros fx regs m s pixs skel rkel w h Hs Hp Hps Hp47 Rw Rh Rd Hk Hks Hk47 Rk0 Rk4 Hr Hw Hh Hw82 Hb NG NS ALs ALp ALk SOK H2 H10 H11 H12.
  assert (Rg : rdn SEGS m (Z_to_bv 64 0x44e98) 8 = Some (Z_to_le_bytes 8 0x45f08)).
  { rewrite (SumWalkTac.rdn_img _ _ _ _ 0x44e98%Z 0x44ea0%Z NG) by lia. imgrd. }
  assert (Rs : rdn SEGS m (Z_to_bv 64 0x45f08) 4 = Some (Z_to_le_bytes 4 3)).
  { rewrite (SumWalkTac.rdn_img _ _ _ _ 0x45f08%Z 0x45f0c%Z NS) by lia. imgrd. }
  assert (A108 : ((s - 108) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact ALs | reflexivity]).
  assert (A112 : ((s - 112) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact ALs | reflexivity]).
  assert (A116 : ((s - 116) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact ALs | reflexivity]).
  assert (A120 : ((s - 120) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact ALs | reflexivity]).
  assert (A124 : ((s - 124) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact ALs | reflexivity]).
  unfold reach. eexists. split.
  - norm_pc.
    zv F_3ad78 D_3ad78 (Z_to_bv 64 (s - 176)).
    stepST F_3ad7c D_3ad7c (Z_to_bv 64 (s - 8)) (getr regs 1) ltac:(sok_in SOK).
    stepST F_3ad80 D_3ad80 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_3ad84 D_3ad84 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_3ad88 D_3ad88 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_3ad8c D_3ad8c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepST F_3ad90 D_3ad90 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
    stepST F_3ad94 D_3ad94 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
    stepST F_3ad98 D_3ad98 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
    stepST F_3ad9c D_3ad9c (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
    stepST F_3ada0 D_3ada0 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
    stepST F_3ada4 D_3ada4 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
    stepST F_3ada8 D_3ada8 (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
    stepST F_3adac D_3adac (Z_to_bv 64 (s - 104)) (getr regs 27) ltac:(sok_in SOK).
    stepb_ft F_3adb0 D_3adb0 ltac:(condZ).
    zv F_3adb4 D_3adb4 (Z_to_bv 64 rkel).
    zv F_3adb8 D_3adb8 (Z_to_bv 64 skel).
    zv F_3adbc D_3adbc (Z_to_bv 64 pixs).
    sn F_3adc0 D_3adc0.
    stepb_ft F_1a8cc D_1a8cc ltac:(condZ).
    guard8 F_1a8d0 D_1a8d0 ALp.
    stepb_ft F_1a8d4 D_1a8d4 ltac:(condZ).
    stepLD F_1a8d8 D_1a8d8 (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; rdn_by Rd) ltac:(apply lez4; lia).
    rewrite ?(v_lw_small 8) by lia.
    stepret F_1a8dc D_1a8dc (Z_to_bv 64 0x3adc4) ltac:(bveq).
    zv F_3adc4 D_3adc4 (Z_to_bv 64 8).
    stepb_ft F_3adc8 D_3adc8 ltac:(condZ).
    zv F_3adcc D_3adcc (Z_to_bv 64 (s - 108)).
    zv F_3add0 D_3add0 (Z_to_bv 64 (s - 112)).
    zv F_3add4 D_3add4 (Z_to_bv 64 (s - 116)).
    zv F_3add8 D_3add8 (Z_to_bv 64 pixs).
    sn F_3addc D_3addc.
    pgd_walk (s - 108)%Z (s - 112)%Z (s - 116)%Z w h 8%Z Rw Rh Rd SOK ALp A108 A112 A116.
    stepret F_19bb0 D_19bb0 (Z_to_bv 64 0x3ade0) ltac:(bveq).
    stepb_ft F_3ade0 D_3ade0 ltac:(condZ).
    zv F_3ade4 D_3ade4 (Z_to_bv 64 (s - 124)).
    zv F_3ade8 D_3ade8 (Z_to_bv 64 (s - 120)).
    zv F_3adec D_3adec (Z_to_bv 64 skel).
    zv F_3adf0 D_3adf0 (Z_to_bv 64 0).
    zv F_3adf4 D_3adf4 (Z_to_bv 64 0).
    sn F_3adf8 D_3adf8.
    guard4 F_38860 D_38860 A124.
    stepb_ft F_38864 D_38864 ltac:(condZ).
    stepb_ft F_38868 D_38868 ltac:(condZ).
    stepST F_3886c D_3886c (Z_to_bv 64 (s - 124)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    guard4 F_38870 D_38870 A120.
    stepb_ft F_38874 D_38874 ltac:(condZ).
    stepb_ft F_38878 D_38878 ltac:(condZ).
    stepST F_3887c D_3887c (Z_to_bv 64 (s - 120)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    zlitv F_38880 D_38880 (Z_to_bv 64 0).
    stepb_tk F_38884 D_38884 ltac:(condZ).
    zlitv F_38890 D_38890 (Z_to_bv 64 0).
    stepb_tk F_38894 D_38894 ltac:(condZ).
    stepb_ft F_388a0 D_388a0 ltac:(condZ).
    guard8 F_388a4 D_388a4 ALk.
    stepb_ft F_388a8 D_388a8 ltac:(condZ).
    stepat F_388ac D_388ac (Z_to_bv 64 0) ltac:(gres; first [reflexivity | bveq]).
    stepb_ft F_388b0 D_388b0 ltac:(condZ).
    ldw F_388b4 D_388b4 41%Z.
    stepST F_388b8 D_388b8 (Z_to_bv 64 (s - 124)) (Z_to_bv 64 41) ltac:(sok_in SOK).
    stepb_ft F_388bc D_388bc ltac:(condZ).
    stepat F_388c0 D_388c0 (Z_to_bv 64 0) ltac:(gres; first [reflexivity | bveq]).
    stepb_ft F_388c4 D_388c4 ltac:(condZ).
    ldw F_388c8 D_388c8 41%Z.
    stepST F_388cc D_388cc (Z_to_bv 64 (s - 120)) (Z_to_bv 64 41) ltac:(sok_in SOK).
    stepb_tk F_388d0 D_388d0 ltac:(condZ).
    stepb_tk F_388e4 D_388e4 ltac:(condZ).
    zv F_3892c D_3892c (Z_to_bv 64 0).
    stepret F_38930 D_38930 (Z_to_bv 64 0x3adfc) ltac:(bveq).
    ldw F_3adfc D_3adfc 41%Z.
    zlitv F_3ae00 D_3ae00 (Z_to_bv 64 0x40000000).
    sn F_3ae04 D_3ae04. fixl (Z_to_bv 64 0x40000029).
    stepb_ft F_3ae08 D_3ae08 ltac:(condZ).
    ldw F_3ae0c D_3ae0c w.
    sn F_3ae10 D_3ae10. fixl (Z_to_bv 64 82).
    stepb_tk F_3ae14 D_3ae14 ltac:(condZ).
    zlitv F_3afac D_3afac (Z_to_bv 64 0x44fac).
    stepLD F_3afb0 D_3afb0 (Z_to_le_bytes 8 0x45f08) (Z_to_bv 64 0x45f08) ltac:(lit_addr 0x44e98%Z; rdn_by Rg) ltac:(apply lez8; lia).
    stepLD F_3afb4 D_3afb4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(lit_addr 0x45f08%Z; rdn_by Rs) ltac:(apply lez4; lia).
    rewrite ?(v_lw_small 3) by lia.
    zv F_3afb8 D_3afb8 (Z_to_bv 64 4).
    stepb_ft F_3afbc D_3afbc ltac:(condZ).
    ldw F_3afc0 D_3afc0 41%Z.
    zlitv F_3afc4 D_3afc4 (Z_to_bv 64 0x40000000).
    sn F_3afc8 D_3afc8. fixl (Z_to_bv 64 0x40000029).
    stepb_ft F_3afcc D_3afcc ltac:(condZ).
    ldw F_3afd0 D_3afd0 h.
    sn F_3afd4 D_3afd4.
    sn F_3afd8 D_3afd8.
    sn F_3afdc D_3afdc.
    zlitv F_3afe0 D_3afe0 (Z_to_bv 64 0x10fe0).
    zlitv F_3afe4 D_3afe4 (Z_to_bv 64 0x11fe4).
    zlitv F_3afe8 D_3afe8 (Z_to_bv 64 0x10f60).
    zlitv F_3afec D_3afec (Z_to_bv 64 0x11f9c).
    sn F_3aff0 D_3aff0.
    fin 0x17e28%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma ge_Ah : forall (fx : FPState) regs (m : word -> option byte) (s pixs skel rkel w h : Z),
  (4096 + 176 <= s <= 2 ^ 47)%Z ->
  (4096 <= pixs)%Z ->
  (pixs + 64 <= s - 176 \/ s <= pixs)%Z ->
  (pixs + 64 <= 2 ^ 47)%Z ->
  rdn SEGS m (Z_to_bv 64 pixs) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 8) ->
  (4096 <= skel)%Z ->
  (skel + 24 <= s - 176 \/ s <= skel)%Z ->
  (skel + 24 <= 2 ^ 47)%Z ->
  rdn SEGS m (Z_to_bv 64 skel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 41)) ->
  rdn SEGS m (Z_to_bv 64 (skel + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 41)) ->
  (4096 <= rkel)%Z ->
  (1 <= w < 2 ^ 31)%Z ->
  (1 <= h < 2 ^ 31)%Z ->
  (83 <= w)%Z ->
  (h <= 82)%Z ->
  (0x45f0c <= s - 176)%Z ->
  (forall j, (0x44e98 <= j < 0x44ea0)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (0x45f08 <= j < 0x45f0c)%Z -> m (Z_to_bv 64 j) = None) ->
  (s mod 16 = 0)%Z ->
  (pixs mod 8 = 0)%Z ->
  (skel mod 8 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 176)) 176 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 pixs ->
  getr regs 11 = Z_to_bv 64 skel ->
  getr regs 12 = Z_to_bv 64 rkel ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3ad78) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x17e28) M' rom /\
      rinv [((s - 176)%Z, 176%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 21)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 22)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (getr regs 23)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 (getr regs 24)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 (getr regs 25)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (getr regs 26)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 (getr regs 27)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) /\ rdn SEGS M' (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) /\
      getr regs' 1 = Z_to_bv 64 0x3aff4 /\ getr regs' 2 = Z_to_bv 64 (s - 176) /\ getr regs' 9 = Z_to_bv 64 pixs /\
      getr regs' 10 = Z_to_bv 64 0x10f60 /\ getr regs' 11 = Z_to_bv 64 0x11f9c /\
      regs_agree (fun r => In r [1; 2; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs').
Proof.
  intros fx regs m s pixs skel rkel w h Hs Hp Hps Hp47 Rw Rh Rd Hk Hks Hk47 Rk0 Rk4 Hr Hw Hh Hw83 Hh82 Hb NG NS ALs ALp ALk SOK H2 H10 H11 H12.
  assert (Rg : rdn SEGS m (Z_to_bv 64 0x44e98) 8 = Some (Z_to_le_bytes 8 0x45f08)).
  { rewrite (SumWalkTac.rdn_img _ _ _ _ 0x44e98%Z 0x44ea0%Z NG) by lia. imgrd. }
  assert (Rs : rdn SEGS m (Z_to_bv 64 0x45f08) 4 = Some (Z_to_le_bytes 4 3)).
  { rewrite (SumWalkTac.rdn_img _ _ _ _ 0x45f08%Z 0x45f0c%Z NS) by lia. imgrd. }
  assert (A108 : ((s - 108) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact ALs | reflexivity]).
  assert (A112 : ((s - 112) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact ALs | reflexivity]).
  assert (A116 : ((s - 116) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact ALs | reflexivity]).
  assert (A120 : ((s - 120) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact ALs | reflexivity]).
  assert (A124 : ((s - 124) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact ALs | reflexivity]).
  unfold reach. eexists. split.
  - norm_pc.
    zv F_3ad78 D_3ad78 (Z_to_bv 64 (s - 176)).
    stepST F_3ad7c D_3ad7c (Z_to_bv 64 (s - 8)) (getr regs 1) ltac:(sok_in SOK).
    stepST F_3ad80 D_3ad80 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_3ad84 D_3ad84 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_3ad88 D_3ad88 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_3ad8c D_3ad8c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepST F_3ad90 D_3ad90 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
    stepST F_3ad94 D_3ad94 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
    stepST F_3ad98 D_3ad98 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
    stepST F_3ad9c D_3ad9c (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
    stepST F_3ada0 D_3ada0 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
    stepST F_3ada4 D_3ada4 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
    stepST F_3ada8 D_3ada8 (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
    stepST F_3adac D_3adac (Z_to_bv 64 (s - 104)) (getr regs 27) ltac:(sok_in SOK).
    stepb_ft F_3adb0 D_3adb0 ltac:(condZ).
    zv F_3adb4 D_3adb4 (Z_to_bv 64 rkel).
    zv F_3adb8 D_3adb8 (Z_to_bv 64 skel).
    zv F_3adbc D_3adbc (Z_to_bv 64 pixs).
    sn F_3adc0 D_3adc0.
    stepb_ft F_1a8cc D_1a8cc ltac:(condZ).
    guard8 F_1a8d0 D_1a8d0 ALp.
    stepb_ft F_1a8d4 D_1a8d4 ltac:(condZ).
    stepLD F_1a8d8 D_1a8d8 (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; rdn_by Rd) ltac:(apply lez4; lia).
    rewrite ?(v_lw_small 8) by lia.
    stepret F_1a8dc D_1a8dc (Z_to_bv 64 0x3adc4) ltac:(bveq).
    zv F_3adc4 D_3adc4 (Z_to_bv 64 8).
    stepb_ft F_3adc8 D_3adc8 ltac:(condZ).
    zv F_3adcc D_3adcc (Z_to_bv 64 (s - 108)).
    zv F_3add0 D_3add0 (Z_to_bv 64 (s - 112)).
    zv F_3add4 D_3add4 (Z_to_bv 64 (s - 116)).
    zv F_3add8 D_3add8 (Z_to_bv 64 pixs).
    sn F_3addc D_3addc.
    pgd_walk (s - 108)%Z (s - 112)%Z (s - 116)%Z w h 8%Z Rw Rh Rd SOK ALp A108 A112 A116.
    stepret F_19bb0 D_19bb0 (Z_to_bv 64 0x3ade0) ltac:(bveq).
    stepb_ft F_3ade0 D_3ade0 ltac:(condZ).
    zv F_3ade4 D_3ade4 (Z_to_bv 64 (s - 124)).
    zv F_3ade8 D_3ade8 (Z_to_bv 64 (s - 120)).
    zv F_3adec D_3adec (Z_to_bv 64 skel).
    zv F_3adf0 D_3adf0 (Z_to_bv 64 0).
    zv F_3adf4 D_3adf4 (Z_to_bv 64 0).
    sn F_3adf8 D_3adf8.
    guard4 F_38860 D_38860 A124.
    stepb_ft F_38864 D_38864 ltac:(condZ).
    stepb_ft F_38868 D_38868 ltac:(condZ).
    stepST F_3886c D_3886c (Z_to_bv 64 (s - 124)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    guard4 F_38870 D_38870 A120.
    stepb_ft F_38874 D_38874 ltac:(condZ).
    stepb_ft F_38878 D_38878 ltac:(condZ).
    stepST F_3887c D_3887c (Z_to_bv 64 (s - 120)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    zlitv F_38880 D_38880 (Z_to_bv 64 0).
    stepb_tk F_38884 D_38884 ltac:(condZ).
    zlitv F_38890 D_38890 (Z_to_bv 64 0).
    stepb_tk F_38894 D_38894 ltac:(condZ).
    stepb_ft F_388a0 D_388a0 ltac:(condZ).
    guard8 F_388a4 D_388a4 ALk.
    stepb_ft F_388a8 D_388a8 ltac:(condZ).
    stepat F_388ac D_388ac (Z_to_bv 64 0) ltac:(gres; first [reflexivity | bveq]).
    stepb_ft F_388b0 D_388b0 ltac:(condZ).
    ldw F_388b4 D_388b4 41%Z.
    stepST F_388b8 D_388b8 (Z_to_bv 64 (s - 124)) (Z_to_bv 64 41) ltac:(sok_in SOK).
    stepb_ft F_388bc D_388bc ltac:(condZ).
    stepat F_388c0 D_388c0 (Z_to_bv 64 0) ltac:(gres; first [reflexivity | bveq]).
    stepb_ft F_388c4 D_388c4 ltac:(condZ).
    ldw F_388c8 D_388c8 41%Z.
    stepST F_388cc D_388cc (Z_to_bv 64 (s - 120)) (Z_to_bv 64 41) ltac:(sok_in SOK).
    stepb_tk F_388d0 D_388d0 ltac:(condZ).
    stepb_tk F_388e4 D_388e4 ltac:(condZ).
    zv F_3892c D_3892c (Z_to_bv 64 0).
    stepret F_38930 D_38930 (Z_to_bv 64 0x3adfc) ltac:(bveq).
    ldw F_3adfc D_3adfc 41%Z.
    zlitv F_3ae00 D_3ae00 (Z_to_bv 64 0x40000000).
    sn F_3ae04 D_3ae04. fixl (Z_to_bv 64 0x40000029).
    stepb_ft F_3ae08 D_3ae08 ltac:(condZ).
    ldw F_3ae0c D_3ae0c w.
    sn F_3ae10 D_3ae10. fixl (Z_to_bv 64 82).
    stepb_ft F_3ae14 D_3ae14 ltac:(condZ).
    ldw F_3ae18 D_3ae18 41%Z.
    zlitv F_3ae1c D_3ae1c (Z_to_bv 64 0x40000000).
    sn F_3ae20 D_3ae20. fixl (Z_to_bv 64 0x40000029).
    stepb_ft F_3ae24 D_3ae24 ltac:(condZ).
    ldw F_3ae28 D_3ae28 h.
    sn F_3ae2c D_3ae2c. fixl (Z_to_bv 64 82).
    stepb_tk F_3ae30 D_3ae30 ltac:(condZ).
    zlitv F_3afac D_3afac (Z_to_bv 64 0x44fac).
    stepLD F_3afb0 D_3afb0 (Z_to_le_bytes 8 0x45f08) (Z_to_bv 64 0x45f08) ltac:(lit_addr 0x44e98%Z; rdn_by Rg) ltac:(apply lez8; lia).
    stepLD F_3afb4 D_3afb4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(lit_addr 0x45f08%Z; rdn_by Rs) ltac:(apply lez4; lia).
    rewrite ?(v_lw_small 3) by lia.
    zv F_3afb8 D_3afb8 (Z_to_bv 64 4).
    stepb_ft F_3afbc D_3afbc ltac:(condZ).
    ldw F_3afc0 D_3afc0 41%Z.
    zlitv F_3afc4 D_3afc4 (Z_to_bv 64 0x40000000).
    sn F_3afc8 D_3afc8. fixl (Z_to_bv 64 0x40000029).
    stepb_ft F_3afcc D_3afcc ltac:(condZ).
    ldw F_3afd0 D_3afd0 h.
    sn F_3afd4 D_3afd4.
    sn F_3afd8 D_3afd8.
    sn F_3afdc D_3afdc.
    zlitv F_3afe0 D_3afe0 (Z_to_bv 64 0x10fe0).
    zlitv F_3afe4 D_3afe4 (Z_to_bv 64 0x11fe4).
    zlitv F_3afe8 D_3afe8 (Z_to_bv 64 0x10f60).
    zlitv F_3afec D_3afec (Z_to_bv 64 0x11f9c).
    sn F_3aff0 D_3aff0.
    fin 0x17e28%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma ge_W2 : forall (fx : FPState) regs (m : word -> option byte) (s pixs : Z),
  (4096 + 176 <= s <= 2 ^ 47)%Z ->
  (0 <= pixs < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 176) ->
  getr regs 9 = Z_to_bv 64 pixs ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3aff4) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x1a314) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 0x3b000 /\ getr regs' 2 = Z_to_bv 64 (s - 176) /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 pixs /\
      regs_agree (fun r => In r [1; 10; 11]%list) regs regs').
Proof.
  intros fx regs m s pixs Hs Hp H2 H9.
  unfold reach. eexists. split.
  - norm_pc.
    zv F_3aff4 D_3aff4 (Z_to_bv 64 0).
    zv F_3aff8 D_3aff8 (Z_to_bv 64 pixs).
    sn F_3affc D_3affc.
    fin 0x1a314%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

(* [comment removed for export] *)
Lemma ge_Xcp : forall (fx : FPState) regs (m : word -> option byte) (s a0v : Z) (ret : word) (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word),
  (4096 + 176 <= s <= 2 ^ 47)%Z ->
  (0 <= a0v < 2 ^ 64)%Z ->
  ret_ok ret ->
  v1 = ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v22) ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v23) ->
  rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v24) ->
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v25) ->
  rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 v26) ->
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 v27) ->
  getr regs 2 = Z_to_bv 64 (s - 176) ->
  getr regs 10 = Z_to_bv 64 a0v ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3b000) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' ret M' rom /\
      M' = m /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 a0v /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\ getr regs' 21 = v21 /\ getr regs' 22 = v22 /\ getr regs' 23 = v23 /\ getr regs' 24 = v24 /\ getr regs' 25 = v25 /\ getr regs' 26 = v26 /\ getr regs' 27 = v27 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs').
Proof.
  intros fx regs m s a0v ret v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 Hs Ha Hret E1 R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 H2 H10. subst v1.
  unfold reach. eexists. split.
  - norm_pc.
    sn F_3b000 D_3b000.
    stepLD8 F_3b38c D_3b38c ret.
    stepLD8 F_3b390 D_3b390 v8.
    stepLD8 F_3b394 D_3b394 v9.
    stepLD8 F_3b398 D_3b398 v18.
    stepLD8 F_3b39c D_3b39c v19.
    stepLD8 F_3b3a0 D_3b3a0 v20.
    stepLD8 F_3b3a4 D_3b3a4 v21.
    stepLD8 F_3b3a8 D_3b3a8 v22.
    stepLD8 F_3b3ac D_3b3ac v23.
    stepLD8 F_3b3b0 D_3b3b0 v24.
    stepLD8 F_3b3b4 D_3b3b4 v25.
    stepLD8 F_3b3b8 D_3b3b8 v26.
    stepLD8 F_3b3bc D_3b3bc v27.
    zv F_3b3c0 D_3b3c0 (Z_to_bv 64 s).
    stepret F_3b3c4 D_3b3c4 ret ltac:(bveq).
    apply mst_refl.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

(* [comment removed for export] *)
Lemma ge_Xerr : forall (fx : FPState) regs (m : word -> option byte) (s a0v : Z) (ret : word) (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word),
  (4096 + 176 <= s <= 2 ^ 47)%Z ->
  (0 <= a0v < 2 ^ 64)%Z ->
  ret_ok ret ->
  v1 = ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v22) ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v23) ->
  rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v24) ->
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v25) ->
  rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 v26) ->
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 v27) ->
  getr regs 2 = Z_to_bv 64 (s - 176) ->
  getr regs 10 = Z_to_bv 64 a0v ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3b030) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' ret M' rom /\
      M' = m /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 a0v /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\ getr regs' 21 = v21 /\ getr regs' 22 = v22 /\ getr regs' 23 = v23 /\ getr regs' 24 = v24 /\ getr regs' 25 = v25 /\ getr regs' 26 = v26 /\ getr regs' 27 = v27 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs').
Proof.
  intros fx regs m s a0v ret v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 Hs Ha Hret E1 R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 H2 H10. subst v1.
  unfold reach. eexists. split.
  - norm_pc.
    sn F_3b030 D_3b030.
    stepLD8 F_3b38c D_3b38c ret.
    stepLD8 F_3b390 D_3b390 v8.
    stepLD8 F_3b394 D_3b394 v9.
    stepLD8 F_3b398 D_3b398 v18.
    stepLD8 F_3b39c D_3b39c v19.
    stepLD8 F_3b3a0 D_3b3a0 v20.
    stepLD8 F_3b3a4 D_3b3a4 v21.
    stepLD8 F_3b3a8 D_3b3a8 v22.
    stepLD8 F_3b3ac D_3b3ac v23.
    stepLD8 F_3b3b0 D_3b3b0 v24.
    stepLD8 F_3b3b4 D_3b3b4 v25.
    stepLD8 F_3b3b8 D_3b3b8 v26.
    stepLD8 F_3b3bc D_3b3bc v27.
    zv F_3b3c0 D_3b3c0 (Z_to_bv 64 s).
    stepret F_3b3c4 D_3b3c4 ret ltac:(bveq).
    apply mst_refl.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

(* [comment removed for export] *)
Lemma ge_G : forall (fx : FPState) regs (m : word -> option byte) (s a0v : Z) (ret : word) (v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word),
  (4096 + 176 <= s <= 2 ^ 47)%Z ->
  (0 <= a0v < 2 ^ 64)%Z ->
  ret_ok ret ->
  v1 = ret ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v22) ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v23) ->
  rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v24) ->
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v25) ->
  rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 v26) ->
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 v27) ->
  getr regs 2 = Z_to_bv 64 (s - 176) ->
  rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 a0v) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3b3dc) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' ret M' rom /\
      M' = m /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 a0v /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\ getr regs' 21 = v21 /\ getr regs' 22 = v22 /\ getr regs' 23 = v23 /\ getr regs' 24 = v24 /\ getr regs' 25 = v25 /\ getr regs' 26 = v26 /\ getr regs' 27 = v27 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs').
Proof.
  intros fx regs m s a0v ret v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 Hs Ha Hret E1 R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 H2 Rp. subst v1.
  unfold reach. eexists. split.
  - norm_pc.
    stepLD F_3b3dc D_3b3dc (Z_to_le_bytes 8 a0v) (Z_to_bv 64 a0v) ltac:(addr_norm; exact Rp) ltac:(apply lez8; lia).
    sn F_3b3e0 D_3b3e0.
    stepLD8 F_3b38c D_3b38c ret.
    stepLD8 F_3b390 D_3b390 v8.
    stepLD8 F_3b394 D_3b394 v9.
    stepLD8 F_3b398 D_3b398 v18.
    stepLD8 F_3b39c D_3b39c v19.
    stepLD8 F_3b3a0 D_3b3a0 v20.
    stepLD8 F_3b3a4 D_3b3a4 v21.
    stepLD8 F_3b3a8 D_3b3a8 v22.
    stepLD8 F_3b3ac D_3b3ac v23.
    stepLD8 F_3b3b0 D_3b3b0 v24.
    stepLD8 F_3b3b4 D_3b3b4 v25.
    stepLD8 F_3b3b8 D_3b3b8 v26.
    stepLD8 F_3b3bc D_3b3bc v27.
    zv F_3b3c0 D_3b3c0 (Z_to_bv 64 s).
    stepret F_3b3c4 D_3b3c4 ret ltac:(bveq).
    apply mst_refl.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma ge_B : forall (fx : FPState) regs (m : word -> option byte) (s pixs keli : Z),
  (4096 + 176 <= s <= 2 ^ 47)%Z ->
  (0 <= pixs < 2 ^ 64)%Z ->
  (4096 <= keli)%Z ->
  (keli + 24 <= s - 176 \/ s <= keli)%Z ->
  (keli + 24 <= 2 ^ 47)%Z ->
  rdn SEGS m (Z_to_bv 64 keli) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 41)) ->
  rdn SEGS m (Z_to_bv 64 (keli + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 41)) ->
  rdn SEGS m (Z_to_bv 64 (keli + 8)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 20)) ->
  rdn SEGS m (Z_to_bv 64 (keli + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 20)) ->
  (s mod 16 = 0)%Z ->
  (keli mod 8 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 176)) 176 = true ->
  getr regs 2 = Z_to_bv 64 (s - 176) ->
  getr regs 9 = Z_to_bv 64 pixs ->
  getr regs 10 = Z_to_bv 64 keli ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3ae60) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x1c440) M' rom /\
      rinv [((s - 144)%Z, 8%Z); ((s - 132)%Z, 16%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 keli) /\
      rdn SEGS M' (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 41) /\ rdn SEGS M' (Z_to_bv 64 (s - 124)) 4 = Some (Z_to_le_bytes 4 41) /\
      rdn SEGS M' (Z_to_bv 64 (s - 128)) 4 = Some (Z_to_le_bytes 4 20) /\ rdn SEGS M' (Z_to_bv 64 (s - 132)) 4 = Some (Z_to_le_bytes 4 20) /\
      getr regs' 1 = Z_to_bv 64 0x3aeac /\ getr regs' 2 = Z_to_bv 64 (s - 176) /\ getr regs' 10 = Z_to_bv 64 pixs /\
      getr regs' 11 = Z_to_bv 64 20 /\ getr regs' 12 = Z_to_bv 64 21 /\ getr regs' 13 = Z_to_bv 64 20 /\ getr regs' 14 = Z_to_bv 64 21 /\
      regs_agree (fun r => In r [1; 5; 6; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs').
Proof.
  intros fx regs m s pixs keli Hs Hp Hk Hks Hk47 R0 R4 R8 R12 ALs ALk SOK H2 H9 H10.
  assert (A120 : ((s - 120) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact ALs | reflexivity]).
  assert (A124 : ((s - 124) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact ALs | reflexivity]).
  assert (A128 : ((s - 128) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact ALs | reflexivity]).
  assert (A132 : ((s - 132) mod 4 = 0)%Z) by (apply sp_slot_al4'; [exact ALs | reflexivity]).
  unfold reach. eexists. split.
  - norm_pc.
    stepST F_3ae60 D_3ae60 (Z_to_bv 64 (s - 144)) (Z_to_bv 64 keli) ltac:(sok_in SOK).
    zv F_3ae64 D_3ae64 (Z_to_bv 64 (s - 124)).
    zv F_3ae68 D_3ae68 (Z_to_bv 64 (s - 120)).
    zv F_3ae6c D_3ae6c (Z_to_bv 64 (s - 132)).
    zv F_3ae70 D_3ae70 (Z_to_bv 64 (s - 128)).
    sn F_3ae74 D_3ae74.
    guard4 F_38860 D_38860 A124.
    stepb_ft F_38864 D_38864 ltac:(condZ).
    stepb_ft F_38868 D_38868 ltac:(condZ).
    stepST F_3886c D_3886c (Z_to_bv 64 (s - 124)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    guard4 F_38870 D_38870 A120.
    stepb_ft F_38874 D_38874 ltac:(condZ).
    stepb_ft F_38878 D_38878 ltac:(condZ).
    stepST F_3887c D_3887c (Z_to_bv 64 (s - 120)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    guard4 F_38880 D_38880 A132.
    stepb_ft F_38884 D_38884 ltac:(condZ).
    stepb_ft F_38888 D_38888 ltac:(condZ).
    stepST F_3888c D_3888c (Z_to_bv 64 (s - 132)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    guard4 F_38890 D_38890 A128.
    stepb_ft F_38894 D_38894 ltac:(condZ).
    stepb_ft F_38898 D_38898 ltac:(condZ).
    stepST F_3889c D_3889c (Z_to_bv 64 (s - 128)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    stepb_ft F_388a0 D_388a0 ltac:(condZ).
    guard8 F_388a4 D_388a4 ALk.
    stepb_ft F_388a8 D_388a8 ltac:(condZ).
    stepat F_388ac D_388ac (Z_to_bv 64 0) ltac:(gres; first [reflexivity | bveq]).
    stepb_ft F_388b0 D_388b0 ltac:(condZ).
    ldw F_388b4 D_388b4 41%Z.
    stepST F_388b8 D_388b8 (Z_to_bv 64 (s - 124)) (Z_to_bv 64 41) ltac:(sok_in SOK).
    stepb_ft F_388bc D_388bc ltac:(condZ).
    stepat F_388c0 D_388c0 (Z_to_bv 64 0) ltac:(gres; first [reflexivity | bveq]).
    stepb_ft F_388c4 D_388c4 ltac:(condZ).
    ldw F_388c8 D_388c8 41%Z.
    stepST F_388cc D_388cc (Z_to_bv 64 (s - 120)) (Z_to_bv 64 41) ltac:(sok_in SOK).
    stepb_ft F_388d0 D_388d0 ltac:(condZ).
    stepat F_388d4 D_388d4 (Z_to_bv 64 0) ltac:(gres; first [reflexivity | bveq]).
    stepb_ft F_388d8 D_388d8 ltac:(condZ).
    ldw F_388dc D_388dc 20%Z.
    stepST F_388e0 D_388e0 (Z_to_bv 64 (s - 132)) (Z_to_bv 64 20) ltac:(sok_in SOK).
    stepb_ft F_388e4 D_388e4 ltac:(condZ).
    stepat F_388e8 D_388e8 (Z_to_bv 64 0) ltac:(gres; first [reflexivity | bveq]).
    stepb_ft F_388ec D_388ec ltac:(condZ).
    ldw F_388f0 D_388f0 20%Z.
    stepST F_388f4 D_388f4 (Z_to_bv 64 (s - 128)) (Z_to_bv 64 20) ltac:(sok_in SOK).
    zv F_388f8 D_388f8 (Z_to_bv 64 0).
    stepret F_388fc D_388fc (Z_to_bv 64 0x3ae78) ltac:(bveq).
    ldw F_3ae78 D_3ae78 20%Z.
    ldw F_3ae7c D_3ae7c 41%Z.
    sn F_3ae80 D_3ae80. fixl (Z_to_bv 64 21).
    zv F_3ae84 D_3ae84 (Z_to_bv 64 21).
    stepb_ft F_3ae88 D_3ae88 ltac:(condZ).
    ldw F_3ae8c D_3ae8c 20%Z.
    ldw F_3ae90 D_3ae90 41%Z.
    zv F_3ae94 D_3ae94 (Z_to_bv 64 21).
    sn F_3ae98 D_3ae98. fixl (Z_to_bv 64 21).
    stepb_ft F_3ae9c D_3ae9c ltac:(condZ).
    zlitv F_3aea0 D_3aea0 (Z_to_bv 64 21).
    zv F_3aea4 D_3aea4 (Z_to_bv 64 pixs).
    sn F_3aea8 D_3aea8.
    fin 0x1c440%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma ge_C : forall (fx : FPState) regs (m : word -> option byte) (s pixt w h : Z),
  (4096 + 176 <= s <= 2 ^ 47)%Z ->
  (4096 <= pixt < 2 ^ 47)%Z ->
  (0 <= w < 2 ^ 31)%Z ->
  (0 <= h < 2 ^ 31)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) ->
  store_ok SEGS m (Z_to_bv 64 (s - 176)) 176 = true ->
  getr regs 2 = Z_to_bv 64 (s - 176) ->
  getr regs 10 = Z_to_bv 64 pixt ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3aeac) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x192d0) M' rom /\
      rinv [((s - 152)%Z, 8%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 pixt) /\
      getr regs' 1 = Z_to_bv 64 0x3aec8 /\ getr regs' 2 = Z_to_bv 64 (s - 176) /\ getr regs' 19 = Z_to_bv 64 pixt /\
      getr regs' 10 = Z_to_bv 64 w /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 8 /\
      regs_agree (fun r => In r [1; 10; 11; 12; 19]%list) regs regs').
Proof.
  intros fx regs m s pixt w h Hs Hp Hw Hh Rw Rh SOK H2 H10.
  unfold reach. eexists. split.
  - norm_pc.
    stepST F_3aeac D_3aeac (Z_to_bv 64 (s - 152)) (Z_to_bv 64 pixt) ltac:(sok_in SOK).
    stepb_ft F_3aeb0 D_3aeb0 ltac:(condZ).
    zv F_3aeb4 D_3aeb4 (Z_to_bv 64 pixt).
    ldz F_3aeb8 D_3aeb8 w.
    ldz F_3aebc D_3aebc h.
    zv F_3aec0 D_3aec0 (Z_to_bv 64 8).
    sn F_3aec4 D_3aec4.
    fin 0x192d0%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma ge_Cn : forall (fx : FPState) regs (m : word -> option byte) (s : Z),
  (4096 + 176 <= s <= 2 ^ 47)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 176)) 176 = true ->
  getr regs 2 = Z_to_bv 64 (s - 176) ->
  getr regs 10 = Z_to_bv 64 0 ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3aeac) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x38570) M' rom /\
      rinv [((s - 152)%Z, 8%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 0) /\
      getr regs' 1 = Z_to_bv 64 0x3b360 /\ getr regs' 2 = Z_to_bv 64 (s - 176) /\ getr regs' 10 = Z_to_bv 64 (s - 144) /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s Hs SOK H2 H10.
  unfold reach. eexists. split.
  - norm_pc.
    stepST F_3aeac D_3aeac (Z_to_bv 64 (s - 152)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    stepb_tk F_3aeb0 D_3aeb0 ltac:(condZ).
    zv F_3b358 D_3b358 (Z_to_bv 64 (s - 144)).
    sn F_3b35c D_3b35c.
    fin 0x38570%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma ge_Cn2 : forall (fx : FPState) regs (m : word -> option byte) (s : Z),
  (4096 + 176 <= s <= 2 ^ 47)%Z ->
  (0x45f0c <= s - 176)%Z ->
  (forall j, (0x44e98 <= j < 0x44ea0)%Z -> m (Z_to_bv 64 j) = None) ->
  (forall j, (0x45f08 <= j < 0x45f0c)%Z -> m (Z_to_bv 64 j) = None) ->
  getr regs 2 = Z_to_bv 64 (s - 176) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3b360) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x17ec4) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 0x3b030 /\ getr regs' 2 = Z_to_bv 64 (s - 176) /\
      getr regs' 10 = Z_to_bv 64 0x11a85 /\ getr regs' 11 = Z_to_bv 64 0x11f9c /\ getr regs' 12 = Z_to_bv 64 0 /\
      regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs').
Proof.
  intros fx regs m s Hs Hb NG NS H2.
  assert (Rg : rdn SEGS m (Z_to_bv 64 0x44e98) 8 = Some (Z_to_le_bytes 8 0x45f08)).
  { rewrite (SumWalkTac.rdn_img _ _ _ _ 0x44e98%Z 0x44ea0%Z NG) by lia. imgrd. }
  assert (Rs : rdn SEGS m (Z_to_bv 64 0x45f08) 4 = Some (Z_to_le_bytes 4 3)).
  { rewrite (SumWalkTac.rdn_img _ _ _ _ 0x45f08%Z 0x45f0c%Z NS) by lia. imgrd. }
  unfold reach. eexists. split.
  - norm_pc.
    zlitv F_3b360 D_3b360 (Z_to_bv 64 0x45360).
    stepLD F_3b364 D_3b364 (Z_to_le_bytes 8 0x45f08) (Z_to_bv 64 0x45f08) ltac:(lit_addr 0x44e98%Z; exact Rg) ltac:(apply lez8; lia).
    stepLD F_3b368 D_3b368 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(lit_addr 0x45f08%Z; exact Rs) ltac:(apply lez4; lia).
    rewrite ?(v_lw_small 3) by lia.
    zv F_3b36c D_3b36c (Z_to_bv 64 5).
    stepb_ft F_3b370 D_3b370 ltac:(condZ).
    zlitv F_3b374 D_3b374 (Z_to_bv 64 0x11374).
    zlitv F_3b378 D_3b378 (Z_to_bv 64 0x12378).
    zlitv F_3b37c D_3b37c (Z_to_bv 64 0x11a85).
    zlitv F_3b380 D_3b380 (Z_to_bv 64 0x11f9c).
    sn F_3b384 D_3b384.
    zv F_3b028 D_3b028 (Z_to_bv 64 0).
    sn F_3b02c D_3b02c.
    fin 0x17ec4%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma ge_D : forall (fx : FPState) regs (m : word -> option byte) (s pixt pixd rkel datat datad wplt wpld : Z),
  (4096 + 176 <= s <= 2 ^ 47)%Z ->
  (4096 <= pixt)%Z ->
  (pixt + 64 <= 2 ^ 47)%Z ->
  (4096 <= pixd)%Z ->
  (pixd + 64 <= 2 ^ 47)%Z ->
  (0 <= datat < 2 ^ 64)%Z ->
  (0 <= datad < 2 ^ 64)%Z ->
  (0 <= wplt < 2 ^ 31)%Z ->
  (0 <= wpld < 2 ^ 31)%Z ->
  (0 <= rkel < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (pixt + 56)) 8 = Some (Z_to_le_bytes 8 datat) ->
  rdn SEGS m (Z_to_bv 64 (pixt + 16)) 4 = Some (Z_to_le_bytes 4 wplt) ->
  rdn SEGS m (Z_to_bv 64 (pixd + 56)) 8 = Some (Z_to_le_bytes 8 datad) ->
  rdn SEGS m (Z_to_bv 64 (pixd + 16)) 4 = Some (Z_to_le_bytes 4 wpld) ->
  (pixt + 64 <= s - 176 \/ s <= pixt)%Z ->
  (pixd + 64 <= s - 176 \/ s <= pixd)%Z ->
  (pixt mod 8 = 0)%Z ->
  (pixd mod 8 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 176)) 176 = true ->
  getr regs 2 = Z_to_bv 64 (s - 176) ->
  getr regs 10 = Z_to_bv 64 pixd ->
  getr regs 19 = Z_to_bv 64 pixt ->
  getr regs 8 = Z_to_bv 64 rkel ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3aec8) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x3aefc) M' rom /\
      rinv [((s - 168)%Z, 16%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 datad) /\ rdn SEGS M' (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 pixd) /\
      getr regs' 2 = Z_to_bv 64 (s - 176) /\ getr regs' 9 = Z_to_bv 64 datat /\ getr regs' 19 = Z_to_bv 64 wplt /\
      getr regs' 20 = Z_to_bv 64 pixd /\ getr regs' 8 = Z_to_bv 64 rkel /\ getr regs' 10 = Z_to_bv 64 wpld /\
      regs_agree (fun r => In r [1; 9; 10; 11; 19; 20]%list) regs regs').
Proof.
  intros fx regs m s pixt pixd rkel datat datad wplt wpld Hs Ht Ht47 Hd Hd47 Hdt Hdd Hwt Hwd Hrk Rdt Rwt Rdd Rwd Hts Hds ALt ALd SOK H2 H10 H19 H8.
  unfold reach. eexists. split.
  - norm_pc.
    zv F_3aec8 D_3aec8 (Z_to_bv 64 pixd).
    zv F_3aecc D_3aecc (Z_to_bv 64 pixt).
    sn F_3aed0 D_3aed0.
    stepb_ft F_1a9a4 D_1a9a4 ltac:(condZ).
    guard8 F_1a9a8 D_1a9a8 ALt.
    stepb_ft F_1a9ac D_1a9ac ltac:(condZ).
    stepLD F_1a9b0 D_1a9b0 (Z_to_le_bytes 8 datat) (Z_to_bv 64 datat) ltac:(addr_norm; exact Rdt) ltac:(apply lez8; lia).
    stepret F_1a9b4 D_1a9b4 (Z_to_bv 64 0x3aed4) ltac:(bveq).
    zv F_3aed4 D_3aed4 (Z_to_bv 64 datat).
    zv F_3aed8 D_3aed8 (Z_to_bv 64 pixd).
    sn F_3aedc D_3aedc.
    stepb_ft F_1a9a4 D_1a9a4 ltac:(condZ).
    guard8 F_1a9a8 D_1a9a8 ALd.
    stepb_ft F_1a9ac D_1a9ac ltac:(condZ).
    stepLD F_1a9b0 D_1a9b0 (Z_to_le_bytes 8 datad) (Z_to_bv 64 datad) ltac:(addr_norm; exact Rdd) ltac:(apply lez8; lia).
    stepret F_1a9b4 D_1a9b4 (Z_to_bv 64 0x3aee0) ltac:(bveq).
    stepST F_3aee0 D_3aee0 (Z_to_bv 64 (s - 160)) (Z_to_bv 64 datad) ltac:(sok_in SOK).
    zv F_3aee4 D_3aee4 (Z_to_bv 64 pixt).
    sn F_3aee8 D_3aee8.
    stepb_ft F_197e0 D_197e0 ltac:(condZ).
    guard8 F_197e4 D_197e4 ALt.
    stepb_ft F_197e8 D_197e8 ltac:(condZ).
    ldz F_197ec D_197ec wplt.
    stepret F_197f0 D_197f0 (Z_to_bv 64 0x3aeec) ltac:(bveq).
    zv F_3aeec D_3aeec (Z_to_bv 64 wplt).
    stepST F_3aef0 D_3aef0 (Z_to_bv 64 (s - 168)) (Z_to_bv 64 pixd) ltac:(sok_in SOK).
    zv F_3aef4 D_3aef4 (Z_to_bv 64 pixd).
    sn F_3aef8 D_3aef8.
    stepb_ft F_197e0 D_197e0 ltac:(condZ).
    guard8 F_197e4 D_197e4 ALd.
    stepb_ft F_197e8 D_197e8 ltac:(condZ).
    ldz F_197ec D_197ec wpld.
    stepret F_197f0 D_197f0 (Z_to_bv 64 0x3aefc) ltac:(bveq).
    fin 0x3aefc%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma ge_E : forall (fx : FPState) regs (m : word -> option byte) (s : Z),
  (4096 + 176 <= s <= 2 ^ 47)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 176) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3b3cc) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x38570) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 0x3b3d4 /\ getr regs' 2 = Z_to_bv 64 (s - 176) /\ getr regs' 10 = Z_to_bv 64 (s - 144) /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s Hs H2.
  unfold reach. eexists. split.
  - norm_pc.
    zv F_3b3cc D_3b3cc (Z_to_bv 64 (s - 144)).
    sn F_3b3d0 D_3b3d0.
    fin 0x38570%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma ge_F : forall (fx : FPState) regs (m : word -> option byte) (s : Z),
  (4096 + 176 <= s <= 2 ^ 47)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 176) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 0x3b3d4) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 0x1982c) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 0x3b3dc /\ getr regs' 2 = Z_to_bv 64 (s - 176) /\ getr regs' 10 = Z_to_bv 64 (s - 152) /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s Hs H2.
  unfold reach. eexists. split.
  - norm_pc.
    zv F_3b3d4 D_3b3d4 (Z_to_bv 64 (s - 152)).
    sn F_3b3d8 D_3b3d8.
    fin 0x1982c%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.
End Segs.
