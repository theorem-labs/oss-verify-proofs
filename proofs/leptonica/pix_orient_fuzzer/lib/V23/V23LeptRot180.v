(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptExec LeptExecW LeptExecFP LeptExecB LeptExecX.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23_code_r90a_rot180.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma r180_and_0 : forall p k : Z, (0 <= p < 2 ^ 64)%Z -> (0 <= k)%Z -> (p mod (k + 1) = 0)%Z -> (k = 3 \/ k = 7)%Z ->
  alu64 ALU_AND (Z_to_bv 64 p) (Z_to_bv 64 k) = Z_to_bv 64 0.
Proof.
  intros p k Hp Hk Hm Hk37. rewrite alu_and. unfold v_and. rewrite !u_Z2bv by lia.
  destruct Hk37 as [-> | ->].
  - change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2)%Z with 4%Z. change (3 + 1)%Z with 4%Z in Hm. rewrite Hm. reflexivity.
  - change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3)%Z with 8%Z. change (7 + 1)%Z with 8%Z in Hm. rewrite Hm. reflexivity.
Qed.

Ltac r180_and0 := first [ rewrite (r180_and_0 _ 3) by (first [lia | assumption]) | rewrite (r180_and_0 _ 7) by (first [lia | assumption]) ].
Ltac r180_sc_hook :=
  lazymatch goal with
  | |- branch_taken _ _ _ = _ => repeat r180_and0; vm_compute; reflexivity
  end.
#[local] Ltac exB_sc_hook ::= r180_sc_hook.

Definition PC_pixRotate180 : Z := 0x98a70.

(* [comment removed for export] *)
Definition FR180 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).

Section Rot180.
Context {fx : FPState}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
  Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma r180_A : forall regs m (s pixs : Z) (v : pixv) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (pixs mod 8 = 0)%Z -> PIXat m pixs v -> (pixs + 64 <= s - 32 \/ s <= pixs)%Z -> p_d v = 1%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x98a70 : word) m rom) (mkst regs' (0x6eb5c : word) (FR180 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x98ac0
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 pixs /\ getr regs' 8 = Z_to_bv 64 pixs /\ getr regs' 9 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s pixs v ret Hs Hs64 Hp ALp PX DJ Hd SOK H2 H1 H10 H11.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    pose proof (PIX_rd_d SEGS _ _ _ PX) as Cd. rewrite Hd in Cd.
    unfold FR180. subst ret.
    replace (0x98a70 : word) with (Z_to_bv 64 0x98a70) by (apply bv_eq; reflexivity).
    replace (0x6eb5c : word) with (Z_to_bv 64 0x6eb5c) by (apply bv_eq; reflexivity).
    ex_entry regs [s; pixs] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; pixs]) m
      [KWr (SA (EVar 32) (-32)) 32; KRange (EVar 32) 32 (2 ^ 64 - 1); KRange (EVar 33) 1 (2 ^ 64 - 65);
       KWord (SA (EVar 33) 8) 4 (ELit 1);
       KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-32)) 32]%Z) by (ex_know regs).
    ex_open HR HK Hms Hlf.
    ex_cont 400%nat [0x6eb5c%Z] (SCR [false] [] []) HR Hlf HK Hms.
    exists R. split; [ex_mem regs Hms | repeat split; try (ex_reg regs HR); ex_agree HRo HR].
  Qed.

  (* [comment removed for export] *)
  Lemma r180_B : forall regs m (pixd : Z), (1 <= pixd < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x98ac0 : word) m rom) (mkst regs' (0x98b88 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x98ad0 /\ getr regs' 8 = Z_to_bv 64 pixd /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 8; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixd Hp H10.
    replace (0x98ac0 : word) with (Z_to_bv 64 0x98ac0) by (apply bv_eq; reflexivity).
    replace (0x98b88 : word) with (Z_to_bv 64 0x98b88) by (apply bv_eq; reflexivity).
    ex_entry regs [pixd] HR.
    assert (HK : know_ok SEGS (ex_env regs [pixd]) m [KRange (EVar 32) 1 (2 ^ 64 - 1)]%Z) by (ex_know regs).
    ex_run 40%nat [0x98b88%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split.
    - ex_mem regs Hms.
    - repeat split; try (ex_reg regs HR'). ex_agree HR HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma r180_C : forall regs m,
    exists regs',
      msteps SEGS (mkst regs (0x98ad0 : word) m rom) (mkst regs' (0x997e0 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x98adc /\ getr regs' 10 = getr regs 8 /\ getr regs' 11 = getr regs 8
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m. eexists. split.
    - sn F_98ad0 D_98ad0. sn F_98ad4 D_98ad4. sn F_98ad8 D_98ad8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma r180_D : forall regs m (s : Z) (ret v8 v9 : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    cellsZ m [(s - 8, ret); (s - 16, v8); (s - 24, v9)]%Z ->
    getr regs 2 = Z_to_bv 64 (s - 32) ->
    exists regs',
      msteps SEGS (mkst regs (0x98adc : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = getr regs 8
      /\ getr regs' 8 = v8 /\ getr regs' 9 = v9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ret v8 v9 Hs Hs64 Hret CE H2. cbn [cellsZ] in CE. destruct CE as (R8 & R16 & R24 & _).
    eexists. split.
    - sn F_98adc D_98adc.
      sn F_98b70 D_98b70.
      stepLD8 F_98b74 D_98b74 ret. stepLD8 F_98b78 D_98b78 v8. stepLD8 F_98b7c D_98b7c v9.
      zv F_98b80 D_98b80 (Z_to_bv 64 s). stepret F_98b84 D_98b84 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.
End Rot180.
