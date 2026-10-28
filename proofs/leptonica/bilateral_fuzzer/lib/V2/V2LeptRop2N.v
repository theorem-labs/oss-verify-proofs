(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr V2LeptRop_iface V2LeptRop V2LeptRop2_iface V2_code_pixRasterop.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma str_pixd_not_defined : str16 0x11930 16.
Proof. unfold str16. str16_tac. Qed.
Lemma str_pixRasterop : str16 0x11778 11.
Proof. unfold str16. str16_tac. Qed.

Section SegsN.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma pr_NA : forall regs m (s : Z) (ret : word),
  (224 <= s)%Z -> (s + 8 < 2 ^ 64)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 224)) 224 = true ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (mkst regs (0x273f0 : word) m rom) (mkst regs' (0x274d8 : word) (RLF m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 224)
    /\ regs_agree (fun r => In r [2]%list) regs regs'.
Proof.
  intros regs m s ret Hs Hs64 SOK H2 H1 H10.
  eexists. split.
  - zv F_273f0 D_273f0 (Z_to_bv 64 (s - 224)).
    stepST F_273f4 D_273f4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
    stepST F_273f8 D_273f8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_273fc D_273fc (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_27400 D_27400 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_27404 D_27404 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    stepST F_27408 D_27408 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
    stepST F_2740c D_2740c (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
    stepST F_27410 D_27410 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
    stepST F_27414 D_27414 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
    stepST F_27418 D_27418 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
    stepST F_2741c D_2741c (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
    stepST F_27420 D_27420 (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
    stepST F_27424 D_27424 (Z_to_bv 64 (s - 104)) (getr regs 27) ltac:(sok_in SOK).
    stepb_tk F_27428 D_27428 ltac:(condZ).
    unfold RLF. apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma pr_NB : forall regs m (s : Z) (ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word),
  (224 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 0x44e98) 8 = Some (Z_to_le_bytes 8 0x45f08) -> rdn SEGS m (Z_to_bv 64 0x45f08) 4 = Some (Z_to_le_bytes 4 3) ->
  rlcells m s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ->
  getr regs 2 = Z_to_bv 64 (s - 224) ->
  exists regs',
    msteps SEGS (mkst regs (0x274d8 : word) m rom) (mkst regs' (0x17df4 : word) m rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
    /\ getr regs' 10 = Z_to_bv 64 0x11930 /\ getr regs' 11 = Z_to_bv 64 0x11778 /\ getr regs' 12 = Z_to_bv 64 1
    /\ getr regs' 8 = v0 /\ getr regs' 9 = v1 /\ getr regs' 18 = v2 /\ getr regs' 19 = v3 /\ getr regs' 20 = v4 /\ getr regs' 21 = v5 /\ getr regs' 22 = v6 /\ getr regs' 23 = v7 /\ getr regs' 24 = v8 /\ getr regs' 25 = v9 /\ getr regs' 26 = v10 /\ getr regs' 27 = v11
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
Proof.
  intros regs m s ret v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 Hs Hs64 Rg Rs (C & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11) R2.
  eexists. split.
  - sn F_274d8 D_274d8.
    stepLD F_274dc D_274dc (Z_to_le_bytes 8 0x45f08) (Z_to_bv 64 0x45f08) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
    stepLD F_274e0 D_274e0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
    sn F_274e4 D_274e4.
    stepb_ft F_274e8 D_274e8 ltac:(condZ).
    sn F_274ec D_274ec. sn F_274f0 D_274f0. sn F_274f4 D_274f4. sn F_274f8 D_274f8. sn F_274fc D_274fc.
    stepLD8 F_27500 D_27500 ret. stepLD8 F_27504 D_27504 v0. stepLD8 F_27508 D_27508 v1. stepLD8 F_2750c D_2750c v2.
    stepLD8 F_27510 D_27510 v3. stepLD8 F_27514 D_27514 v4. stepLD8 F_27518 D_27518 v5. stepLD8 F_2751c D_2751c v6.
    stepLD8 F_27520 D_27520 v7. stepLD8 F_27524 D_27524 v8. stepLD8 F_27528 D_27528 v9. stepLD8 F_2752c D_2752c v10.
    stepLD8 F_27530 D_27530 v11.
    zv F_27534 D_27534 (Z_to_bv 64 s).
    sn F_27538 D_27538.
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

End SegsN.

(* [comment removed for export] *)
Section RopNullW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Ltac grows_chain := repeat (eapply mem_grows_trans; [| apply wbytes_grows]); apply mem_grows_refl.

Theorem pixRasterop_null_W : pixRasterop_null_contract.
Proof.
  unfold pixRasterop_null_contract.
  intros C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 HK.
  unfold PC_pixRasterop. replace (Z_to_bv 64 0x273f0) with (0x273f0 : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ROPN_STACK, LSF in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  destruct (pr_NA al_rom regs m s ret ltac:(lia) ltac:(lia) (W_sok_win C A m md (s - 224) 224 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := RLF m s ret regs).
  assert (OUT1 : forall a : word, ~ (s - 224 <= u a < s)%Z -> M1 a = m a) by (intros a Ha; subst M1; apply RLF_outside; lia).
  assert (GR1 : mem_grows m M1) by (subst M1; unfold RLF; grows_chain).
  assert (HW1 : W C A M1 md).
  { apply (W_local C A m md M1 s CK HW Hhi); [| exact GR1].
    intros a NE. left. unfold scratch.
    destruct (Z_lt_ge_dec (u a) (s - 224)) as [B|B]; [exfalso; apply NE; apply OUT1; lia|].
    destruct (Z_lt_ge_dec (u a) s) as [B2|B2]; [lia | exfalso; apply NE; apply OUT1; lia]. }
  pose proof (rlcells_RLF m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  destruct (pr_NB al_rom r1 M1 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
              (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) ltac:(lia) ltac:(lia)
              (W_sev_got C A M1 md HW1) (W_sev C A M1 md HW1) CE1 Q2)
    as (r2 & RUN2 & P2 & P1 & P10 & P11 & P12 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  apply (returnErrorInt_W C A M1 md r2 s 0x11930 0x11778 16 11 ret (Z_to_bv 64 1) S CK HW1 P2 Hs16 ltac:(unfold LSF; lia) Hhi P1 Hret
           P10 P11 P12 str_pixd_not_defined str_pixRasterop).
  intros m' regs' HW' FR' GR' CS' R10'.
  apply (HK m' regs' HW').
  - apply (cs_kept_trans regs r2 regs'); [| exact CS'].
    apply cs_kept_intro; first [ rewrite P2; symmetry; exact H2 | assumption | csr; reflexivity ].
  - intros a Ha. unfold scratch in Ha. rewrite FR' by (unfold LSF; lia). apply OUT1. lia.
  - eapply mem_grows_trans; [exact GR1 | exact GR'].
  - exact R10'.
Qed.

End RopNullW.
