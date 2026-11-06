(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs LeptRecs LeptArith LeptArith2 GrayACELib LeptNuma LeptEdgeFP.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require Import O9_code_edC O9LeptEdgeSegs.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Plain.M.loaded_segments.

Section Segs2.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition PMESF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
      (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
      (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
      (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
      (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)).
  (* [comment removed for export] *)
  Definition PMESM (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (PMESF m s ret regs) (Z_to_bv 64 (s + 12)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (s + 8)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s + 4)) (word_to_le_bytes 4 (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Definition pm_R (regs : bvmap 5 word) (s : Z) : Prop :=
    getr regs 2 = Z_to_bv 64 (s - 112) /\ getr regs 8 = Z_to_bv 64 (s + 4) /\ getr regs 9 = Z_to_bv 64 1 /\
    getr regs 18 = Z_to_bv 64 (s + 8) /\ getr regs 19 = Z_to_bv 64 (s + 12) /\ getr regs 20 = Z_to_bv 64 1.

  (* [comment removed for export] *)
  Lemma pm_A0 : forall (fx : FPState) regs m (s pixs d : Z) (ret : word),
    (112 <= s)%Z -> (s + 16 < 2 ^ 63)%Z -> (1 <= pixs)%Z -> (pixs + 64 <= s - 112)%Z -> (0 <= d < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 d) ->
    store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true -> store_ok SEGS m (Z_to_bv 64 (s + 4)) 12 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 1 ->
    getr regs 12 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 (s + 12) -> getr regs 15 = Z_to_bv 64 (s + 8) ->
    getr regs 16 = Z_to_bv 64 (s + 4) -> getr regs 17 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x77a8c : word) m rom) (@mkst fx regs' (0x77b04 : word) (PMESM m s ret regs) rom)
      /\ pm_R regs' s /\ getr regs' 21 = Z_to_bv 64 0 /\ getr regs' 22 = Z_to_bv 64 1 /\ getr regs' 23 = Z_to_bv 64 pixs
      /\ getr regs' 24 = Z_to_bv 64 1 /\ getr regs' 10 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros fx regs m s pixs d ret Hs Hs64 Hp Hp2 Hd Cd SOK SOKC H2 H1 H10 H11 H12 H13 H14 H15 H16 H17. unfold PMESM, PMESF, pm_R.
    eexists. split.
    - zv F_77a34 D_77a34 (Z_to_bv 64 (s - 112)).   (* [comment removed for export] *)
      stepST F_77a38 D_77a38 (Z_to_bv 64 (s - 8)) (ret) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_77a3c D_77a3c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_77a40 D_77a40 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_77a44 D_77a44 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_77a48 D_77a48 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_77a4c D_77a4c (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_77a50 D_77a50 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_77a54 D_77a54 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_77a58 D_77a58 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_77a5c D_77a5c (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).   (* [comment removed for export] *)
      sn F_77a60 D_77a60.   (* [comment removed for export] *)
      sn F_77a64 D_77a64.   (* [comment removed for export] *)
      sn F_77a68 D_77a68.   (* [comment removed for export] *)
      sn F_77a6c D_77a6c.   (* [comment removed for export] *)
      sn F_77a70 D_77a70.   (* [comment removed for export] *)
      sn F_77a74 D_77a74.   (* [comment removed for export] *)
      sn F_77a78 D_77a78.   (* [comment removed for export] *)
      sn F_77a7c D_77a7c.   (* [comment removed for export] *)
      stepb_ft F_77a80 D_77a80 ltac:(condZ).   (* [comment removed for export] *)
      stepST F_77a84 D_77a84 (Z_to_bv 64 (s + 12)) (Z_to_bv 64 0) ltac:(sok_in SOKC).   (* [comment removed for export] *)
      stepb_ft F_77a88 D_77a88 ltac:(condZ).   (* [comment removed for export] *)
      stepST F_77a8c D_77a8c (Z_to_bv 64 (s + 8)) (Z_to_bv 64 0) ltac:(sok_in SOKC).   (* [comment removed for export] *)
      stepat F_77a90 D_77a90 (Z_to_bv 64 (Z.lor (s + 12) (s + 8))) ltac:(gres; pin; rewrite v_or_Z by lia; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_77a94 D_77a94 ltac:(condZ).   (* [comment removed for export] *)
      stepST F_77a98 D_77a98 (Z_to_bv 64 (s + 4)) (Z_to_bv 64 0) ltac:(sok_in SOKC).   (* [comment removed for export] *)
      stepat F_77a9c D_77a9c (Z_to_bv 64 1) ltac:(gres; pin; apply zbv_snez; pose proof (fp_Z_lor_range 63 (s + 12) (s + 8) ltac:(lia) ltac:(lia) ltac:(lia)) as HL; assert (Z.lor (s + 12) (s + 8) <> 0)%Z by (intro E; apply Z.lor_eq_0_iff in E; lia); lia).   (* [comment removed for export] *)
      stepb_ft F_77aa0 D_77aa0 ltac:(condZ).   (* [comment removed for export] *)
      sn F_77aa4 D_77aa4.   (* [comment removed for export] *)
      sn F_77aa8 D_77aa8.   (* [comment removed for export] *)
      stepb_ft F_63264 D_63264 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_63268 D_63268 (Z_to_le_bytes 4 d) (Z_to_bv 64 d) ltac:(addr_norm; repeat rdn_peel1; exact Cd) ltac:(apply lez4; lia).
      rewrite (v_lw_small d) by lia.   (* [comment removed for export] *)
      stepret F_6326c D_6326c (Z_to_bv 64 0x77b04) ltac:(reflexivity).   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_A1 : forall (fx : FPState) regs m (s pixs : Z),
    pm_R regs s -> getr regs 21 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 1 -> getr regs 23 = Z_to_bv 64 pixs -> getr regs 10 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x77b04 : word) m rom) (@mkst fx regs' (0x77d90 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x77bb0 /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros fx regs m s pixs (H2 & H8 & H9 & H18 & H19 & H20) H21 H22 H23 H10.
    eexists. split.
    - sn F_77aac D_77aac.   (* [comment removed for export] *)
      stepb_ft F_77ab0 D_77ab0 ltac:(condZ).   (* [comment removed for export] *)
      sn F_77ab4 D_77ab4.   (* [comment removed for export] *)
      stepb_tk F_77ab8 D_77ab8 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_77b40 D_77b40 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_77b44 D_77b44 ltac:(condZ).   (* [comment removed for export] *)
      sn F_77b48 D_77b48.   (* [comment removed for export] *)
      sn F_77b4c D_77b4c.   (* [comment removed for export] *)
      sn F_77b50 D_77b50.   (* [comment removed for export] *)
      sn F_77b54 D_77b54.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_Ae : forall (fx : FPState) regs m (s d : Z) (ret v8 v9 v18 v19 v20 v21 v22 v23 v24 : word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= d < 2 ^ 31)%Z -> d <> 1%Z ->
    rdn SEGS m (Z_to_bv 64 0xee570) 8 = Some (Z_to_le_bytes 8 0xef750) -> rdn SEGS m (Z_to_bv 64 0xef750) 4 = Some (Z_to_le_bytes 4 3) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) -> rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) -> rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) -> rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
    rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v22) -> rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v23) ->
    rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v24) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 d ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x77b04 : word) m rom) (@mkst fx regs' (0x5cdd4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x115d7 /\ getr regs' 11 = Z_to_bv 64 0x152d1
      /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\ getr regs' 21 = v21
      /\ getr regs' 22 = v22 /\ getr regs' 23 = v23 /\ getr regs' 24 = v24
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros fx regs m s d ret v8 v9 v18 v19 v20 v21 v22 v23 v24 Hs Hs64 Hd Hd1 Rg Rs C1 C8 C9 C18 C19 C20 C21 C22 C23 C24 H2 H10.
    eexists. split.
    - sn F_77aac D_77aac.   (* [comment removed for export] *)
      stepb_tk F_77ab0 D_77ab0 ltac:(condZ).   (* [comment removed for export] *)
      sn F_77ae4 D_77ae4.   (* [comment removed for export] *)
      stepLD F_77ae8 D_77ae8 (Z_to_le_bytes 8 0xef750) (Z_to_bv 64 0xef750) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).   (* [comment removed for export] *)
      stepLD F_77aec D_77aec (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).   (* [comment removed for export] *)
      sn F_77af0 D_77af0.   (* [comment removed for export] *)
      stepb_ft F_77af4 D_77af4 ltac:(condZ).   (* [comment removed for export] *)
      sn F_77af8 D_77af8.   (* [comment removed for export] *)
      sn F_77afc D_77afc.   (* [comment removed for export] *)
      sn F_77b00 D_77b00.   (* [comment removed for export] *)
      sn F_77b04 D_77b04.   (* [comment removed for export] *)
      sn F_77b08 D_77b08.   (* [comment removed for export] *)
      sn F_77cd0 D_77cd0.   (* [comment removed for export] *)
      stepLD8 F_77cd4 D_77cd4 ret.
      stepLD8 F_77cd8 D_77cd8 v8.
      stepLD8 F_77cdc D_77cdc v9.
      stepLD8 F_77ce0 D_77ce0 v18.
      stepLD8 F_77ce4 D_77ce4 v19.
      stepLD8 F_77ce8 D_77ce8 v20.
      stepLD8 F_77cec D_77cec v21.
      stepLD8 F_77cf0 D_77cf0 v22.
      stepLD8 F_77cf4 D_77cf4 v23.
      stepLD8 F_77cf8 D_77cf8 v24.
      zv F_77cfc D_77cfc (Z_to_bv 64 s).   (* [comment removed for export] *)
      sn F_77d00 D_77d00.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_B : forall (fx : FPState) regs m (s na n : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= na)%Z -> (na + 32 <= s - 112)%Z -> (2 <= n < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (na + 4)) 4 = Some (Z_to_le_bytes 4 n) ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 8 = true ->
    pm_R regs s -> getr regs 24 = Z_to_bv 64 1 -> getr regs 10 = Z_to_bv 64 na ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x77bb0 : word) m rom)
                  (@mkst fx regs' (0x60e78 : word) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 na))) rom)
      /\ pm_R regs' s /\ getr regs' 21 = Z_to_bv 64 n /\ getr regs' 1 = Z_to_bv 64 0x77be0
      /\ getr regs' 10 = Z_to_bv 64 na /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (s - 84)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 21; 22]%list) regs regs'.
  Proof.
    intros fx regs m s na n Hs Hs64 Hna Hna2 Hn Cn SOK (H2 & H8 & H9 & H18 & H19 & H20) H24 H10. unfold pm_R.
    eexists. split.
    - stepST F_77b58 D_77b58 (Z_to_bv 64 (s - 96)) (Z_to_bv 64 na) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepb_ft F_77b5c D_77b5c ltac:(condZ).   (* [comment removed for export] *)
      sn F_77b60 D_77b60.   (* [comment removed for export] *)
      sn F_77b64 D_77b64.   (* [comment removed for export] *)
      stepb_ft F_60c24 D_60c24 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_60c28 D_60c28 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; repeat rdn_peel1; exact Cn) ltac:(apply lez4; lia).
      rewrite (v_lw_small n) by lia.   (* [comment removed for export] *)
      stepret F_60c2c D_60c2c (Z_to_bv 64 0x77bc0) ltac:(reflexivity).   (* [comment removed for export] *)
      sn F_77b68 D_77b68.   (* [comment removed for export] *)
      stepb_ft F_77b6c D_77b6c ltac:(condZ).   (* [comment removed for export] *)
      sn F_77b70 D_77b70.   (* [comment removed for export] *)
      stepb_ft F_77b74 D_77b74 ltac:(condZ).   (* [comment removed for export] *)
      zv F_77b78 D_77b78 (Z_to_bv 64 (s - 84)).   (* [comment removed for export] *)
      sn F_77b7c D_77b7c.   (* [comment removed for export] *)
      sn F_77b80 D_77b80.   (* [comment removed for export] *)
      sn F_77b84 D_77b84.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_B0 : forall (fx : FPState) regs m (s na n : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= na)%Z -> (na + 32 <= s - 112)%Z -> (0 <= n < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (na + 4)) 4 = Some (Z_to_le_bytes 4 n) ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 8 = true ->
    pm_R regs s -> getr regs 10 = Z_to_bv 64 na ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x77bb0 : word) m rom)
                  (@mkst fx regs' (0x77bc0 : word) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 na))) rom)
      /\ pm_R regs' s /\ getr regs' 10 = Z_to_bv 64 n
      /\ regs_agree (fun r => In r [1; 10; 22]%list) regs regs'.
  Proof.
    intros fx regs m s na n Hs Hs64 Hna Hna2 Hn Cn SOK (H2 & H8 & H9 & H18 & H19 & H20) H10. unfold pm_R.
    eexists. split.
    - stepST F_77b58 D_77b58 (Z_to_bv 64 (s - 96)) (Z_to_bv 64 na) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepb_ft F_77b5c D_77b5c ltac:(condZ).   (* [comment removed for export] *)
      sn F_77b60 D_77b60.   (* [comment removed for export] *)
      sn F_77b64 D_77b64.   (* [comment removed for export] *)
      stepb_ft F_60c24 D_60c24 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_60c28 D_60c28 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; repeat rdn_peel1; exact Cn) ltac:(apply lez4; lia).
      rewrite (v_lw_small n) by lia.
      stepret F_60c2c D_60c2c (Z_to_bv 64 0x77bc0) ltac:(reflexivity).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_B1 : forall (fx : FPState) regs m (s n : Z),
    (0 <= n <= 1)%Z -> pm_R regs s -> getr regs 10 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x77bc0 : word) m rom) (@mkst fx regs' (0x77ca4 : word) m rom)
      /\ pm_R regs' s
      /\ regs_agree (fun r => In r [11]%list) regs regs'.
  Proof.
    intros fx regs m s n Hn (H2 & H8 & H9 & H18 & H19 & H20) H10. unfold pm_R.
    eexists. split.
    - sn F_77b68 D_77b68.   (* [comment removed for export] *)
      stepb_tk F_77b6c D_77b6c ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_C : forall (fx : FPState) regs m (s : Z),
    pm_R regs s ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x77be0 : word) m rom) (@mkst fx regs' (0x77bec : word) m rom)
      /\ pm_R regs' s /\ getr regs' 22 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [22; 23; 24]%list) regs regs'.
  Proof.
    intros fx regs m s (H2 & H8 & H9 & H18 & H19 & H20). unfold pm_R.
    eexists. split.
    - sn F_77b88 D_77b88.   (* [comment removed for export] *)
      sn F_77b8c D_77b8c.   (* [comment removed for export] *)
      sn F_77b90 D_77b90.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_L : forall (fx : FPState) regs m (s na i : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= na < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (Z_to_le_bytes 8 na) ->
    pm_R regs s -> getr regs 22 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x77bec : word) m rom) (@mkst fx regs' (0x60e78 : word) m rom)
      /\ pm_R regs' s /\ getr regs' 22 = Z_to_bv 64 i /\ getr regs' 1 = Z_to_bv 64 0x77bfc
      /\ getr regs' 10 = Z_to_bv 64 na /\ getr regs' 11 = Z_to_bv 64 i /\ getr regs' 12 = Z_to_bv 64 (s - 88)
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros fx regs m s na i Hs Hs64 Hna Cna (H2 & H8 & H9 & H18 & H19 & H20) H22. unfold pm_R.
    eexists. split.
    - stepLD F_77b94 D_77b94 (Z_to_le_bytes 8 na) (Z_to_bv 64 na) ltac:(addr_norm; exact Cna) ltac:(apply lez8; lia).   (* [comment removed for export] *)
      zv F_77b98 D_77b98 (Z_to_bv 64 (s - 88)).   (* [comment removed for export] *)
      sn F_77b9c D_77b9c.   (* [comment removed for export] *)
      sn F_77ba0 D_77ba0.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_L2n : forall (fx : FPState) regs m (s n i : Z) (b24 b28 : list byte),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= i)%Z -> (i + 1 < n)%Z -> (n < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 88)) 4 = Some b24 -> length b24 = 4%nat -> rdn SEGS m (Z_to_bv 64 (s - 84)) 4 = Some b28 -> length b28 = 4%nat ->
    store_ok SEGS m (Z_to_bv 64 (s - 84)) 4 = true ->
    pm_R regs s -> getr regs 21 = Z_to_bv 64 n -> getr regs 22 = Z_to_bv 64 i ->
    exists regs' (bs : list byte),
      msteps SEGS (@mkst fx regs (0x77bfc : word) m rom) (@mkst fx regs' (0x77bec : word) (wbytes m (Z_to_bv 64 (s - 84)) bs) rom)
      /\ length bs = 4%nat /\ pm_R regs' s /\ getr regs' 21 = Z_to_bv 64 n /\ getr regs' 22 = Z_to_bv 64 (i + 1)
      /\ regs_agree (fun r => In r [10; 11; 12; 13; 22; 23; 24]%list) regs regs'.
  Proof.
    intros fx regs m s n i b24 b28 Hs Hs64 Hi Hin Hn R24 L24 R28 L28 SOK (H2 & H8 & H9 & H18 & H19 & H20) H21 H22. unfold pm_R.
    eexists _, _. split.
    - stepLD F_77ba4 D_77ba4 b24 (Z_to_bv 64 (lez b24)) ltac:(addr_norm; exact R24) ltac:(symmetry; apply u_lez4; exact L24).   (* [comment removed for export] *)
      stepLD F_77ba8 D_77ba8 b28 (Z_to_bv 64 (lez b28)) ltac:(addr_norm; exact R28) ltac:(symmetry; apply u_lez4; exact L28).   (* [comment removed for export] *)
      stepat F_77bac D_77bac (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).   (* [comment removed for export] *)
      sn F_77bb0 D_77bb0.   (* [comment removed for export] *)
      sn F_77bb4 D_77bb4.   (* [comment removed for export] *)
      sn F_77bb8 D_77bb8.   (* [comment removed for export] *)
      sn F_77bbc D_77bbc.   (* [comment removed for export] *)
      sn F_77bc0 D_77bc0.   (* [comment removed for export] *)
      sn F_77bc4 D_77bc4.   (* [comment removed for export] *)
      sn F_77bc8 D_77bc8.   (* [comment removed for export] *)
      sn F_77bcc D_77bcc.   (* [comment removed for export] *)
      sn F_77bd0 D_77bd0.   (* [comment removed for export] *)
      sn F_77bd4 D_77bd4.   (* [comment removed for export] *)
      stepST F_77bd8 D_77bd8 (Z_to_bv 64 (s - 84)) (v_lw (Z_to_bv 64 (lez b24))) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepb_tk F_77bdc D_77bdc ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - split; [apply length_N_to_le_bytes|]. repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  Lemma pm_L2x : forall (fx : FPState) regs m (s n i : Z) (b24 b28 : list byte),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= i)%Z -> (i + 1 = n)%Z -> (n < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 88)) 4 = Some b24 -> length b24 = 4%nat -> rdn SEGS m (Z_to_bv 64 (s - 84)) 4 = Some b28 -> length b28 = 4%nat ->
    store_ok SEGS m (Z_to_bv 64 (s - 84)) 4 = true ->
    pm_R regs s -> getr regs 21 = Z_to_bv 64 n -> getr regs 22 = Z_to_bv 64 i ->
    exists regs' (bs : list byte),
      msteps SEGS (@mkst fx regs (0x77bfc : word) m rom) (@mkst fx regs' (0x77c38 : word) (wbytes m (Z_to_bv 64 (s - 84)) bs) rom)
      /\ length bs = 4%nat /\ pm_R regs' s /\ getr regs' 21 = Z_to_bv 64 n
      /\ regs_agree (fun r => In r [10; 11; 12; 13; 22; 23; 24]%list) regs regs'.
  Proof.
    intros fx regs m s n i b24 b28 Hs Hs64 Hi Hin Hn R24 L24 R28 L28 SOK (H2 & H8 & H9 & H18 & H19 & H20) H21 H22. unfold pm_R.
    eexists _, _. split.
    - stepLD F_77ba4 D_77ba4 b24 (Z_to_bv 64 (lez b24)) ltac:(addr_norm; exact R24) ltac:(symmetry; apply u_lez4; exact L24).   (* [comment removed for export] *)
      stepLD F_77ba8 D_77ba8 b28 (Z_to_bv 64 (lez b28)) ltac:(addr_norm; exact R28) ltac:(symmetry; apply u_lez4; exact L28).   (* [comment removed for export] *)
      stepat F_77bac D_77bac (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).   (* [comment removed for export] *)
      sn F_77bb0 D_77bb0.   (* [comment removed for export] *)
      sn F_77bb4 D_77bb4.   (* [comment removed for export] *)
      sn F_77bb8 D_77bb8.   (* [comment removed for export] *)
      sn F_77bbc D_77bbc.   (* [comment removed for export] *)
      sn F_77bc0 D_77bc0.   (* [comment removed for export] *)
      sn F_77bc4 D_77bc4.   (* [comment removed for export] *)
      sn F_77bc8 D_77bc8.   (* [comment removed for export] *)
      sn F_77bcc D_77bcc.   (* [comment removed for export] *)
      sn F_77bd0 D_77bd0.   (* [comment removed for export] *)
      sn F_77bd4 D_77bd4.   (* [comment removed for export] *)
      stepST F_77bd8 D_77bd8 (Z_to_bv 64 (s - 84)) (v_lw (Z_to_bv 64 (lez b24))) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepb_ft F_77bdc D_77bdc ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - split; [apply length_N_to_le_bytes|]. repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_D : forall (fx : FPState) regs m (s na : Z) (w21 w23 w24 : word),
    frm_zero (@fp_csr fx) -> (112 <= s)%Z -> (s + 16 < 2 ^ 63)%Z -> (0 <= na < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (Z_to_le_bytes 8 na) ->
    store_ok SEGS m (Z_to_bv 64 (s + 4)) 12 = true ->
    pm_R regs s -> getr regs 21 = w21 -> getr regs 23 = w23 -> getr regs 24 = w24 ->
    exists fr' cs' regs' (bs1 bs2 : list byte),
      msteps SEGS (@mkst fx regs (0x77c38 : word) m rom)
                  (@mkst (mkFP fr' cs') regs' (0x60738 : word) (wbytes (wbytes m (Z_to_bv 64 (s + 12)) bs1) (Z_to_bv 64 (s + 8)) bs2) rom)
      /\ frm_zero cs' /\ length bs1 = 4%nat /\ length bs2 = 4%nat
      /\ pm_R regs' s /\ getr regs' 1 = Z_to_bv 64 0x77c7c /\ getr regs' 10 = Z_to_bv 64 na /\ getr regs' 11 = Z_to_bv 64 0
      /\ reg_get fr' 10 = nan_box (Z_to_bv 32 0x3f800000)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros fx regs m s na w21 w23 w24 Hz Hs Hs64 Hna Cna SOKC (H2 & H8 & H9 & H18 & H19 & H20) H21 H23 H24. unfold pm_R.
    eexists _, _, _, _, _. split.
    - stepb_ft F_77be0 D_77be0 ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_77be4 | reflexivity | exact D_77be4 | left; split; reflexivity | right; left; repeat split; reflexivity | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_77be8 D_77be8.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_77bec | reflexivity | exact D_77bec | left; split; reflexivity | right; left; repeat split; reflexivity | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fari; [exact F_77bf0 | reflexivity | exact D_77bf0 | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_fsw with (a := Z_to_bv 64 (s + 12)); [exact F_77bf4 | reflexivity | exact D_77bf4 | gres; imm_norm; addr_tac | sok_in SOKC] | step_simpl ]; fpn.   (* [comment removed for export] *)
      stepb_ft F_77bf8 D_77bf8 ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_77bfc | reflexivity | exact D_77bfc | left; split; reflexivity | right; left; repeat split; reflexivity | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_77c00 D_77c00.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_77c04 | reflexivity | exact D_77c04 | left; split; reflexivity | right; left; repeat split; reflexivity | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fari; [exact F_77c08 | reflexivity | exact D_77c08 | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_fsw with (a := Z_to_bv 64 (s + 8)); [exact F_77c0c | reflexivity | exact D_77c0c | gres; imm_norm; addr_tac | sok_in SOKC] | step_simpl ]; fpn.   (* [comment removed for export] *)
      stepb_ft F_77c10 D_77c10 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_77c14 D_77c14 (Z_to_le_bytes 8 na) (Z_to_bv 64 na) ltac:(replace (v_addi (Z_to_bv 64 (s - 112)) 16) with (Z_to_bv 64 (s - 96)) by (unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia); repeat (rewrite rdn_wbytes_out_Z by (rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)); exact Cna) ltac:(apply lez8; lia).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_77c18 | reflexivity | exact D_77c18 | left; split; reflexivity | right; left; repeat split; reflexivity | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_77c1c D_77c1c.   (* [comment removed for export] *)
      sn F_77c20 D_77c20.   (* [comment removed for export] *)
      apply mst_refl.
    - split; [fz Hz|]. split; [apply length_Z_to_le_bytes|]. split; [apply length_Z_to_le_bytes|].
      repeat split; gres; pin; try reflexivity; try solve_regs_agree.
      rewrite fpv_get_same. cbn [fp_format]. rewrite u_Z2bv by lia. rewrite f32u_one. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_E : forall (fx : FPState) regs m (s nae c : Z) (w21 : word),
    frm_zero (@fp_csr fx) -> (112 <= s)%Z -> (s + 16 < 2 ^ 63)%Z -> (1 <= nae)%Z -> (nae + 32 <= s - 112)%Z -> (0 <= c < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (nae + 4)) 4 = Some (Z_to_le_bytes 4 c) ->
    store_ok SEGS m (Z_to_bv 64 (s - 104)) 8 = true -> store_ok SEGS m (Z_to_bv 64 (s + 4)) 12 = true ->
    pm_R regs s -> getr regs 10 = Z_to_bv 64 nae -> getr regs 21 = w21 ->
    exists fr' cs' regs' (bs : list byte),
      msteps SEGS (@mkst fx regs (0x77c7c : word) m rom)
                  (@mkst (mkFP fr' cs') regs' (0x60af0 : word) (wbytes (wbytes m (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (Z_to_bv 64 nae))) (Z_to_bv 64 (s + 4)) bs) rom)
      /\ frm_zero cs' /\ length bs = 4%nat
      /\ pm_R regs' s /\ getr regs' 1 = Z_to_bv 64 0x77ca4 /\ getr regs' 10 = Z_to_bv 64 (s - 104)
      /\ regs_agree (fun r => In r [1; 10; 21]%list) regs regs'.
  Proof.
    intros fx regs m s nae c w21 Hz Hs Hs64 Hnae Hnae2 Hc Cc SOK SOKC (H2 & H8 & H9 & H18 & H19 & H20) H10 H21. unfold pm_R.
    eexists _, _, _, _. split.
    - stepST F_77c24 D_77c24 (Z_to_bv 64 (s - 104)) (Z_to_bv 64 nae) ltac:(sok_in SOK).   (* [comment removed for export] *)
      sn F_77c28 D_77c28.   (* [comment removed for export] *)
      stepb_ft F_60c24 D_60c24 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_60c28 D_60c28 (Z_to_le_bytes 4 c) (Z_to_bv 64 c) ltac:(addr_norm; repeat rdn_peel1; exact Cc) ltac:(apply lez4; lia).
      rewrite (v_lw_small c) by lia.   (* [comment removed for export] *)
      stepret F_60c2c D_60c2c (Z_to_bv 64 0x77c84) ltac:(reflexivity).   (* [comment removed for export] *)
      sn F_77c2c D_77c2c.   (* [comment removed for export] *)
      sn F_77c30 D_77c30.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_77c34 | reflexivity | exact D_77c34 | left; split; reflexivity | left; repeat split; reflexivity | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_77c38 | reflexivity | exact D_77c38 | left; split; reflexivity | right; left; repeat split; reflexivity | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fari; [exact F_77c3c | reflexivity | exact D_77c3c | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_fsw with (a := Z_to_bv 64 (s + 4)); [exact F_77c40 | reflexivity | exact D_77c40 | gres; imm_norm; addr_tac | sok_in SOKC] | step_simpl ]; fpn.   (* [comment removed for export] *)
      zv F_77c44 D_77c44 (Z_to_bv 64 (s - 104)).   (* [comment removed for export] *)
      sn F_77c48 D_77c48.   (* [comment removed for export] *)
      apply mst_refl.
    - split; [fz Hz|]. split; [apply length_Z_to_le_bytes|]. repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_F : forall (fx : FPState) regs m (s : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> pm_R regs s ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x77ca4 : word) m rom) (@mkst fx regs' (0x60af0 : word) m rom)
      /\ pm_R regs' s /\ getr regs' 1 = Z_to_bv 64 0x77cac /\ getr regs' 10 = Z_to_bv 64 (s - 96)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros fx regs m s Hs Hs64 (H2 & H8 & H9 & H18 & H19 & H20). unfold pm_R.
    eexists. split.
    - zv F_77c4c D_77c4c (Z_to_bv 64 (s - 96)).   (* [comment removed for export] *)
      sn F_77c50 D_77c50.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_G : forall (fx : FPState) regs m (s : Z) (ret v8 v9 v18 v19 v20 v21 v22 v23 v24 : word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) -> rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) -> rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) -> rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
    rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v22) -> rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v23) ->
    rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v24) ->
    getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x77cac : word) m rom) (@mkst fx regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\ getr regs' 21 = v21
      /\ getr regs' 22 = v22 /\ getr regs' 23 = v23 /\ getr regs' 24 = v24
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros fx regs m s ret v8 v9 v18 v19 v20 v21 v22 v23 v24 Hs Hs64 Hret C1 C8 C9 C18 C19 C20 C21 C22 C23 C24 H2.
    eexists. split.
    - sn F_77c54 D_77c54.   (* [comment removed for export] *)
      sn F_77c58 D_77c58.   (* [comment removed for export] *)
      stepLD8 F_77d08 D_77d08 ret.
      stepLD8 F_77d0c D_77d0c v8.
      stepLD8 F_77d10 D_77d10 v9.
      stepLD8 F_77d14 D_77d14 v18.
      stepLD8 F_77d18 D_77d18 v19.
      stepLD8 F_77d1c D_77d1c v20.
      stepLD8 F_77d20 D_77d20 v21.
      stepLD8 F_77d24 D_77d24 v22.
      stepLD8 F_77d28 D_77d28 v23.
      stepLD8 F_77d2c D_77d2c v24.
      zv F_77d30 D_77d30 (Z_to_bv 64 s).   (* [comment removed for export] *)
      stepret F_77d34 D_77d34 ret ltac:(reflexivity).   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition FR3 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
           (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).

  (* [comment removed for export] *)
  Lemma fz_small : forall (fx : FPState) regs m (s sz : Z) (dptr ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sz < 3)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = dptr -> getr regs 11 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (@mkst fx regs (0x5cd50 : word) m rom) (@mkst fx regs' ret (FR3 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros fx regs m s sz dptr ret Hs Hs64 Hsz Hret SOK H2 H1 H10 H11. unfold FR3. eexists. split.
    - zv F_5ccf8 D_5ccf8 (Z_to_bv 64 (s - 48)).
      stepST F_5ccfc D_5ccfc (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_5cd00 D_5cd00 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_5cd04 D_5cd04 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_5cd08 D_5cd08. sn F_5cd0c D_5cd0c. stepb_tk F_5cd10 D_5cd10 ltac:(condZ).
      sn F_5cd60 D_5cd60.
      stepLD8 F_5cd64 D_5cd64 ret. stepLD8 F_5cd68 D_5cd68 (getr regs 8). stepLD8 F_5cd6c D_5cd6c (getr regs 9).
      zv F_5cd70 D_5cd70 (Z_to_bv 64 s). stepret F_5cd74 D_5cd74 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_big : forall (fx : FPState) regs m (s sz : Z) (dptr ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (3 <= sz < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    store_ok SEGS m (Z_to_bv 64 0xef758) 8 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = dptr -> getr regs 11 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (@mkst fx regs (0x5cd50 : word) m rom)
                              (@mkst fx regs' (0x72a30 : word) (wbytes (FR3 m s ret regs) (Z_to_bv 64 0xef758) (word_to_le_bytes 8 (Z_to_bv 64 0x5cdd0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x5cd88 /\ getr regs' 10 = dptr /\ getr regs' 11 = Z_to_bv 64 sz
      /\ getr regs' 8 = Z_to_bv 64 sz /\ getr regs' 9 = dptr
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros fx regs m s sz dptr ret Hs Hs64 Hsz SOK SOKh H2 H1 H10 H11. unfold FR3. eexists. split.
    - zv F_5ccf8 D_5ccf8 (Z_to_bv 64 (s - 48)).
      stepST F_5ccfc D_5ccfc (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_5cd00 D_5cd00 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_5cd04 D_5cd04 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_5cd08 D_5cd08. sn F_5cd0c D_5cd0c. stepb_ft F_5cd10 D_5cd10 ltac:(condZ).
      sn F_5cd14 D_5cd14. sn F_5cd18 D_5cd18. sn F_5cd1c D_5cd1c. sn F_5cd20 D_5cd20.
      stepb_tk F_5cf18 D_5cf18 ltac:(condZ).
      sn F_5cf24 D_5cf24.
      stepST F_5cf28 D_5cf28 (Z_to_bv 64 0xef758) (Z_to_bv 64 0x5cdd0) ltac:(store_ok_peel; exact SOKh).
      stepret F_5cf2c D_5cf2c (0x5cd7c : word) ltac:(bveq).
      sn F_5cd24 D_5cd24. sn F_5cd28 D_5cd28. sn F_5cd2c D_5cd2c. sn F_728dc D_728dc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_B0 : forall (fx : FPState) regs m (s : Z) (ret s0v s1v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (@mkst fx regs (0x5cd88 : word) m rom) (@mkst fx regs' ret (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros fx regs m s ret s0v s1v Hs Hs64 Hret SOK R1 R2 R3 H2 H10. eexists. split.
    - stepST F_5cd30 D_5cd30 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_5cd34 D_5cd34 ltac:(condZ).
      sn F_5cd60 D_5cd60.
      stepLD8 F_5cd64 D_5cd64 ret. stepLD8 F_5cd68 D_5cd68 s0v. stepLD8 F_5cd6c D_5cd6c s1v.
      zv F_5cd70 D_5cd70 (Z_to_bv 64 s). stepret F_5cd74 D_5cd74 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_B1 : forall (fx : FPState) regs m (s pix : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 pix ->
    exists regs', msteps SEGS (@mkst fx regs (0x5cd88 : word) m rom)
       (@mkst fx regs' (0x77a8c : word) (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 pix))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x5cdb0 /\ getr regs' 10 = Z_to_bv 64 pix
      /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1
      /\ getr regs' 14 = Z_to_bv 64 (s - 48 + 12) /\ getr regs' 15 = Z_to_bv 64 (s - 48 + 8) /\ getr regs' 16 = Z_to_bv 64 (s - 48 + 4)
      /\ getr regs' 17 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros fx regs m s pix Hs Hs64 Hp SOK H2 H10. eexists. split.
    - stepST F_5cd30 D_5cd30 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 pix) ltac:(sok_in SOK).
      stepb_ft F_5cd34 D_5cd34 ltac:(condZ).
      sn F_5cd38 D_5cd38. sn F_5cd3c D_5cd3c. sn F_5cd40 D_5cd40.
      zv F_5cd44 D_5cd44 (Z_to_bv 64 (s - 48 + 12)). zv F_5cd48 D_5cd48 (Z_to_bv 64 (s - 48 + 8)). zv F_5cd4c D_5cd4c (Z_to_bv 64 (s - 48 + 4)).
      sn F_5cd50 D_5cd50. sn F_5cd54 D_5cd54. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_C : forall (fx : FPState) regs m (s : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs', msteps SEGS (@mkst fx regs (0x5cdb0 : word) m rom) (@mkst fx regs' (0x62654 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x5cdb8 /\ getr regs' 10 = Z_to_bv 64 (s - 32)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros fx regs m s Hs Hs64 H2. eexists. split.
    - zv F_5cd58 D_5cd58 (Z_to_bv 64 (s - 32)). sn F_5cd5c D_5cd5c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_E : forall (fx : FPState) regs m (s : Z) (ret s0v s1v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs', msteps SEGS (@mkst fx regs (0x5cdb8 : word) m rom) (@mkst fx regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros fx regs m s ret s0v s1v Hs Hs64 Hret R1 R2 R3 H2. eexists. split.
    - sn F_5cd60 D_5cd60.
      stepLD8 F_5cd64 D_5cd64 ret. stepLD8 F_5cd68 D_5cd68 s0v. stepLD8 F_5cd6c D_5cd6c s1v.
      zv F_5cd70 D_5cd70 (Z_to_bv 64 s). stepret F_5cd74 D_5cd74 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End Segs2.
