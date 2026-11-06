(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs LeptRecs LeptArith LeptArith2 GrayLib GrayACELib LeptNuma LeptEdgeFP.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9_code_edA V9LeptNfeSegs.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Section Segs2.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition PMESF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
      (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
      (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
      (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
      (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)))
      (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (getr regs 25)).
  (* [comment removed for export] *)
  Definition PMESM (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (PMESF m s ret regs) (Z_to_bv 64 (s + 12)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (s + 8)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s + 4)) (word_to_le_bytes 4 (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Definition pm_R (regs : bvmap 5 word) (s : Z) : Prop :=
    getr regs 2 = Z_to_bv 64 (s - 112) /\ getr regs 8 = Z_to_bv 64 (s + 4) /\ getr regs 9 = Z_to_bv 64 1 /\
    getr regs 18 = Z_to_bv 64 (s + 8) /\ getr regs 19 = Z_to_bv 64 (s + 12) /\ getr regs 20 = Z_to_bv 64 1.
  (* [comment removed for export] *)
  Definition IMIN : Z := 18446744071562067968.

  Lemma al4_of16 : forall s k : Z, (s mod 16 = 0)%Z -> (k mod 4 = 0)%Z -> ((s + k) mod 4 = 0)%Z.
  Proof.
    intros s k Hs Hk. pose proof (Z.div_mod s 16 ltac:(lia)) as E. rewrite Hs, Z.add_0_r in E.
    pose proof (Z.div_mod k 4 ltac:(lia)) as Ek. rewrite Hk, Z.add_0_r in Ek.
    replace (s + k)%Z with ((4 * (s / 16) + k / 4) * 4)%Z by lia. apply Z_mod_mult.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_A0 : forall (fx : FPState) regs m (s pixs d : Z) (ret : word),
    (112 <= s)%Z -> (s + 16 < 2 ^ 63)%Z -> (1 <= pixs)%Z -> (pixs + 64 <= s - 112)%Z -> (0 <= d < 2 ^ 31)%Z ->
    (s mod 16 = 0)%Z -> (pixs mod 8 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 d) ->
    store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true -> store_ok SEGS m (Z_to_bv 64 (s + 4)) 12 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 1 ->
    getr regs 12 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 (s + 12) -> getr regs 15 = Z_to_bv 64 (s + 8) ->
    getr regs 16 = Z_to_bv 64 (s + 4) -> getr regs 17 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x82400 : word) m rom) (@mkst fx regs' (0x82494 : word) (PMESM m s ret regs) rom)
      /\ pm_R regs' s /\ getr regs' 21 = Z_to_bv 64 0 /\ getr regs' 22 = Z_to_bv 64 1 /\ getr regs' 23 = Z_to_bv 64 pixs
      /\ getr regs' 24 = Z_to_bv 64 1 /\ getr regs' 10 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros fx regs m s pixs d ret Hs Hs64 Hp Hp2 Hd Hs16 ALp Cd SOK SOKC H2 H1 H10 H11 H12 H13 H14 H15 H16 H17. unfold PMESM, PMESF, pm_R.
    pose proof (al4_of16 s 12 Hs16 eq_refl) as AL12. pose proof (al4_of16 s 8 Hs16 eq_refl) as AL8. pose proof (al4_of16 s 4 Hs16 eq_refl) as AL4.
    eexists. split.
    - zv F_823a8 D_823a8 (Z_to_bv 64 (s - 112)).   (* [comment removed for export] *)
      stepST F_823ac D_823ac (Z_to_bv 64 (s - 8)) (ret) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_823b0 D_823b0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_823b4 D_823b4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_823b8 D_823b8 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_823bc D_823bc (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_823c0 D_823c0 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_823c4 D_823c4 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_823c8 D_823c8 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_823cc D_823cc (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_823d0 D_823d0 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepST F_823d4 D_823d4 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).   (* [comment removed for export] *)
      sn F_823d8 D_823d8.   (* [comment removed for export] *)
      sn F_823dc D_823dc.   (* [comment removed for export] *)
      sn F_823e0 D_823e0.   (* [comment removed for export] *)
      sn F_823e4 D_823e4.   (* [comment removed for export] *)
      sn F_823e8 D_823e8.   (* [comment removed for export] *)
      sn F_823ec D_823ec.   (* [comment removed for export] *)
      sn F_823f0 D_823f0.   (* [comment removed for export] *)
      sn F_823f4 D_823f4.   (* [comment removed for export] *)
      stepb_ft F_823f8 D_823f8 ltac:(condZ).   (* [comment removed for export] *)
      zand F_823fc D_823fc andi_3 AL12. stepb_ft F_82400 D_82400 ltac:(condZ).   (* [comment removed for export] *)
      stepST F_82404 D_82404 (Z_to_bv 64 (s + 12)) (Z_to_bv 64 0) ltac:(sok_in SOKC).   (* [comment removed for export] *)
      stepb_ft F_82408 D_82408 ltac:(condZ).   (* [comment removed for export] *)
      zand F_8240c D_8240c andi_3 AL8. stepb_ft F_82410 D_82410 ltac:(condZ).   (* [comment removed for export] *)
      stepST F_82414 D_82414 (Z_to_bv 64 (s + 8)) (Z_to_bv 64 0) ltac:(sok_in SOKC).   (* [comment removed for export] *)
      stepb_ft F_82418 D_82418 ltac:(condZ).   (* [comment removed for export] *)
      zand F_8241c D_8241c andi_3 AL4. stepb_ft F_82420 D_82420 ltac:(condZ).   (* [comment removed for export] *)
      stepat F_82424 D_82424 (Z_to_bv 64 (Z.lor (s + 12) (s + 8))) ltac:(gres; pin; rewrite v_or_Z by lia; reflexivity).   (* [comment removed for export] *)
      stepST F_82428 D_82428 (Z_to_bv 64 (s + 4)) (Z_to_bv 64 0) ltac:(sok_in SOKC).   (* [comment removed for export] *)
      stepat F_8242c D_8242c (Z_to_bv 64 1) ltac:(gres; pin; apply zbv_snez; pose proof (fp_Z_lor_range 63 (s + 12) (s + 8) ltac:(lia) ltac:(lia) ltac:(lia)) as HL; assert (Z.lor (s + 12) (s + 8) <> 0)%Z by (intro E; apply Z.lor_eq_0_iff in E; lia); lia).   (* [comment removed for export] *)
      stepb_ft F_82430 D_82430 ltac:(condZ).   (* [comment removed for export] *)
      sn F_82434 D_82434.   (* [comment removed for export] *)
      sn F_82438 D_82438.   (* [comment removed for export] *)
      stepb_ft F_645dc D_645dc ltac:(condZ).   (* [comment removed for export] *)
      zand F_645e0 D_645e0 andi_7 ALp. stepb_ft F_645e4 D_645e4 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_645e8 D_645e8 (Z_to_le_bytes 4 d) (Z_to_bv 64 d) ltac:(addr_norm; repeat rdn_peel1; exact Cd) ltac:(apply lez4; lia).
      rewrite (v_lw_small d) by lia.   (* [comment removed for export] *)
      stepret F_645ec D_645ec (Z_to_bv 64 0x82494) ltac:(reflexivity).   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_A1 : forall (fx : FPState) regs m (s pixs : Z),
    pm_R regs s -> getr regs 21 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 1 -> getr regs 23 = Z_to_bv 64 pixs -> getr regs 10 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x82494 : word) m rom) (@mkst fx regs' (0x82768 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x82544 /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros fx regs m s pixs (H2 & H8 & H9 & H18 & H19 & H20) H21 H22 H23 H10.
    eexists. split.
    - sn F_8243c D_8243c.   (* [comment removed for export] *)
      stepb_ft F_82440 D_82440 ltac:(condZ).   (* [comment removed for export] *)
      sn F_82444 D_82444.   (* [comment removed for export] *)
      stepb_tk F_82448 D_82448 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_824d4 D_824d4 ltac:(condZ).   (* [comment removed for export] *)
      stepb_ft F_824d8 D_824d8 ltac:(condZ).   (* [comment removed for export] *)
      sn F_824dc D_824dc.   (* [comment removed for export] *)
      sn F_824e0 D_824e0.   (* [comment removed for export] *)
      sn F_824e4 D_824e4.   (* [comment removed for export] *)
      sn F_824e8 D_824e8.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_Ae : forall (fx : FPState) regs m (s d : Z) (ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 : word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= d < 2 ^ 31)%Z -> d <> 1%Z ->
    rdn SEGS m (Z_to_bv 64 0xf9120) 8 = Some (Z_to_le_bytes 8 0xfa300) -> rdn SEGS m (Z_to_bv 64 0xfa300) 4 = Some (Z_to_le_bytes 4 3) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) -> rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) -> rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) -> rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
    rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v22) -> rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v23) ->
    rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v24) -> rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v25) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 10 = Z_to_bv 64 d ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x82494 : word) m rom) (@mkst fx regs' (0x5d1c4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x115d7 /\ getr regs' 11 = Z_to_bv 64 0x152ed
      /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\ getr regs' 21 = v21
      /\ getr regs' 22 = v22 /\ getr regs' 23 = v23 /\ getr regs' 24 = v24 /\ getr regs' 25 = v25
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
  Proof.
    intros fx regs m s d ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 Hs Hs64 Hd Hd1 Rg Rs C1 C8 C9 C18 C19 C20 C21 C22 C23 C24 C25 H2 H10.
    eexists. split.
    - sn F_8243c D_8243c.   (* [comment removed for export] *)
      stepb_tk F_82440 D_82440 ltac:(condZ).   (* [comment removed for export] *)
      sn F_82474 D_82474.   (* [comment removed for export] *)
      stepLD F_82478 D_82478 (Z_to_le_bytes 8 0xfa300) (Z_to_bv 64 0xfa300) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).   (* [comment removed for export] *)
      stepLD F_8247c D_8247c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).   (* [comment removed for export] *)
      sn F_82480 D_82480.   (* [comment removed for export] *)
      stepb_ft F_82484 D_82484 ltac:(condZ).   (* [comment removed for export] *)
      sn F_82488 D_82488.   (* [comment removed for export] *)
      sn F_8248c D_8248c.   (* [comment removed for export] *)
      sn F_82490 D_82490.   (* [comment removed for export] *)
      sn F_82494 D_82494.   (* [comment removed for export] *)
      sn F_82498 D_82498.   (* [comment removed for export] *)
      sn F_82604 D_82604.   (* [comment removed for export] *)
      stepLD8 F_82608 D_82608 ret.
      stepLD8 F_8260c D_8260c v8.
      stepLD8 F_82610 D_82610 v9.
      stepLD8 F_82614 D_82614 v18.
      stepLD8 F_82618 D_82618 v19.
      stepLD8 F_8261c D_8261c v20.
      stepLD8 F_82620 D_82620 v21.
      stepLD8 F_82624 D_82624 v22.
      stepLD8 F_82628 D_82628 v23.
      stepLD8 F_8262c D_8262c v24.
      stepLD8 F_82630 D_82630 v25.
      zv F_82634 D_82634 (Z_to_bv 64 s).   (* [comment removed for export] *)
      sn F_82638 D_82638.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_B : forall (fx : FPState) regs m (s na n : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= na)%Z -> (na + 32 <= s - 112)%Z -> (2 <= n < 2 ^ 31)%Z -> (na mod 8 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 (na + 4)) 4 = Some (Z_to_le_bytes 4 n) ->
    store_ok SEGS m (Z_to_bv 64 (s - 104)) 8 = true ->
    pm_R regs s -> getr regs 24 = Z_to_bv 64 1 -> getr regs 10 = Z_to_bv 64 na ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x82544 : word) m rom)
                  (@mkst fx regs' (0x61bc0 : word) (wbytes m (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (Z_to_bv 64 na))) rom)
      /\ pm_R regs' s /\ getr regs' 21 = Z_to_bv 64 n /\ getr regs' 1 = Z_to_bv 64 0x82574
      /\ getr regs' 10 = Z_to_bv 64 na /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (s - 92)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 21; 22]%list) regs regs'.
  Proof.
    intros fx regs m s na n Hs Hs64 Hna Hna2 Hn ALna Cn SOK (H2 & H8 & H9 & H18 & H19 & H20) H24 H10. unfold pm_R.
    eexists. split.
    - stepST F_824ec D_824ec (Z_to_bv 64 (s - 104)) (Z_to_bv 64 na) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepb_ft F_824f0 D_824f0 ltac:(condZ).   (* [comment removed for export] *)
      sn F_824f4 D_824f4.   (* [comment removed for export] *)
      sn F_824f8 D_824f8.   (* [comment removed for export] *)
      stepb_ft F_61918 D_61918 ltac:(condZ).   (* [comment removed for export] *)
      zand F_6191c D_6191c andi_7 ALna. stepb_ft F_61920 D_61920 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_61924 D_61924 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; repeat rdn_peel1; exact Cn) ltac:(apply lez4; lia).
      rewrite (v_lw_small n) by lia.   (* [comment removed for export] *)
      stepret F_61928 D_61928 (Z_to_bv 64 0x82554) ltac:(reflexivity).   (* [comment removed for export] *)
      sn F_824fc D_824fc.   (* [comment removed for export] *)
      stepb_ft F_82500 D_82500 ltac:(condZ).   (* [comment removed for export] *)
      sn F_82504 D_82504.   (* [comment removed for export] *)
      stepb_ft F_82508 D_82508 ltac:(condZ).   (* [comment removed for export] *)
      zv F_8250c D_8250c (Z_to_bv 64 (s - 92)).   (* [comment removed for export] *)
      sn F_82510 D_82510.   (* [comment removed for export] *)
      sn F_82514 D_82514.   (* [comment removed for export] *)
      sn F_82518 D_82518.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_B0 : forall (fx : FPState) regs m (s na n : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= na)%Z -> (na + 32 <= s - 112)%Z -> (0 <= n < 2 ^ 31)%Z -> (na mod 8 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 (na + 4)) 4 = Some (Z_to_le_bytes 4 n) ->
    store_ok SEGS m (Z_to_bv 64 (s - 104)) 8 = true ->
    pm_R regs s -> getr regs 10 = Z_to_bv 64 na ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x82544 : word) m rom)
                  (@mkst fx regs' (0x82554 : word) (wbytes m (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (Z_to_bv 64 na))) rom)
      /\ pm_R regs' s /\ getr regs' 10 = Z_to_bv 64 n
      /\ regs_agree (fun r => In r [1; 10; 11; 22]%list) regs regs'.
  Proof.
    intros fx regs m s na n Hs Hs64 Hna Hna2 Hn ALna Cn SOK (H2 & H8 & H9 & H18 & H19 & H20) H10. unfold pm_R.
    eexists. split.
    - stepST F_824ec D_824ec (Z_to_bv 64 (s - 104)) (Z_to_bv 64 na) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepb_ft F_824f0 D_824f0 ltac:(condZ).   (* [comment removed for export] *)
      sn F_824f4 D_824f4.   (* [comment removed for export] *)
      sn F_824f8 D_824f8.   (* [comment removed for export] *)
      stepb_ft F_61918 D_61918 ltac:(condZ).   (* [comment removed for export] *)
      zand F_6191c D_6191c andi_7 ALna. stepb_ft F_61920 D_61920 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_61924 D_61924 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; repeat rdn_peel1; exact Cn) ltac:(apply lez4; lia).
      rewrite (v_lw_small n) by lia.
      stepret F_61928 D_61928 (Z_to_bv 64 0x82554) ltac:(reflexivity).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_B1 : forall (fx : FPState) regs m (s n : Z),
    (0 <= n <= 1)%Z -> pm_R regs s -> getr regs 10 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x82554 : word) m rom) (@mkst fx regs' (0x82754 : word) m rom)
      /\ pm_R regs' s
      /\ regs_agree (fun r => In r [11]%list) regs regs'.
  Proof.
    intros fx regs m s n Hn (H2 & H8 & H9 & H18 & H19 & H20) H10. unfold pm_R.
    eexists. split.
    - sn F_824fc D_824fc.   (* [comment removed for export] *)
      stepb_tk F_82500 D_82500 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_C : forall (fx : FPState) regs m (s : Z),
    pm_R regs s ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x82574 : word) m rom) (@mkst fx regs' (0x82594 : word) m rom)
      /\ pm_R regs' s /\ getr regs' 22 = Z_to_bv 64 1 /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 24 = Z_to_bv 64 0 /\ getr regs' 25 = Z_to_bv 64 IMIN
      /\ regs_agree (fun r => In r [22; 23; 24; 25]%list) regs regs'.
  Proof.
    intros fx regs m s (H2 & H8 & H9 & H18 & H19 & H20). unfold pm_R, IMIN.
    eexists. split.
    - sn F_8251c D_8251c.   (* [comment removed for export] *)
      sn F_82520 D_82520.   (* [comment removed for export] *)
      sn F_82524 D_82524.   (* [comment removed for export] *)
      sn F_82528 D_82528.   (* [comment removed for export] *)
      sn F_8252c D_8252c.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_L : forall (fx : FPState) regs m (s na i : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= na < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (Z_to_le_bytes 8 na) ->
    pm_R regs s -> getr regs 22 = Z_to_bv 64 i ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x82594 : word) m rom) (@mkst fx regs' (0x61bc0 : word) m rom)
      /\ pm_R regs' s /\ getr regs' 22 = Z_to_bv 64 i /\ getr regs' 1 = Z_to_bv 64 0x825a4
      /\ getr regs' 10 = Z_to_bv 64 na /\ getr regs' 11 = Z_to_bv 64 i /\ getr regs' 12 = Z_to_bv 64 (s - 96)
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros fx regs m s na i Hs Hs64 Hna Cna (H2 & H8 & H9 & H18 & H19 & H20) H22. unfold pm_R.
    eexists. split.
    - stepLD F_8253c D_8253c (Z_to_le_bytes 8 na) (Z_to_bv 64 na) ltac:(addr_norm; exact Cna) ltac:(apply lez8; lia).   (* [comment removed for export] *)
      zv F_82540 D_82540 (Z_to_bv 64 (s - 96)).   (* [comment removed for export] *)
      sn F_82544 D_82544.   (* [comment removed for export] *)
      sn F_82548 D_82548.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma imin_eq : Z_to_bv 64 IMIN = Z_to_bv 64 (- 2 ^ 31).
  Proof. apply bv_eq. reflexivity. Qed.
  Lemma c_eq_Zs_ne : forall a b : Z, (- 2 ^ 63 <= a < 2 ^ 63)%Z -> (- 2 ^ 63 <= b < 2 ^ 63)%Z -> a <> b -> c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
  Proof.
    intros a b Ha Hb Hne. unfold c_eq, bv_eqb. apply Z.eqb_neq. intro E. apply bv_eq in E. apply (f_equal bv_signed) in E.
    rewrite !bv_signed_Zs in E by lia. contradiction.
  Qed.
  Ltac condS := pin; rewrite ?c_lts_Zs by lia; first [ apply Z.ltb_lt | apply Z.ltb_ge | reflexivity ]; lia.

  (* [comment removed for export] *)
  Lemma pm_L2body : forall (fx : FPState) regs m (s nv pv nj js : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 4 = Some (Z_to_le_bytes 4 nv) -> rdn SEGS m (Z_to_bv 64 (s - 92)) 4 = Some (Z_to_le_bytes 4 pv) ->
    (0 <= nv <= 19999)%Z -> (0 <= pv <= 19999)%Z -> (0 <= nj <= 19999)%Z -> (0 <= js <= 19999 * 19999)%Z ->
    pm_R regs s -> getr regs 23 = Z_to_bv 64 js -> getr regs 24 = Z_to_bv 64 nj -> getr regs 25 = Z_to_bv 64 IMIN ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x825a4 : word) m rom) (@mkst fx regs' (0x82588 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 nv /\ getr regs' 23 = Z_to_bv 64 (js + Z.abs (nv - pv))
      /\ getr regs' 24 = Z_to_bv 64 (nj + (if (nv =? pv)%Z then 0 else 1))
      /\ regs_agree (fun r => In r [10; 11; 12; 13; 23; 24]%list) regs regs'.
  Proof.
    intros fx regs m s nv pv nj js Hs Hs64 Rn Rp Hnv Hpv Hnj Hjs (H2 & H8 & H9 & H18 & H19 & H20) H23 H24 H25.
    rewrite imin_eq in H25.
    destruct (Z_dec nv pv) as [[Hlt|Hgt]|Heq].
    - (* [comment removed for export] *)
      replace (Z.abs (nv - pv)) with (pv - nv)%Z by lia. replace (nv =? pv)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      eexists. split.
      + stepLD F_8254c D_8254c (Z_to_le_bytes 4 nv) (Z_to_bv 64 nv) ltac:(addr_norm; exact Rn) ltac:(apply lez4; lia).
        rewrite (v_lw_small nv) by lia.   (* [comment removed for export] *)
        stepLD F_82550 D_82550 (Z_to_le_bytes 4 pv) (Z_to_bv 64 pv) ltac:(addr_norm; exact Rp) ltac:(apply lez4; lia).
        rewrite (v_lw_small pv) by lia.   (* [comment removed for export] *)
        sn F_82554 D_82554. fixv (Z_to_bv 64 (nv - pv)) ltac:(pin; rewrite LeptArith2.v_subw_Z, sw32_small by lia; reflexivity).   (* [comment removed for export] *)
        sn F_82558 D_82558. fixv (Z_to_bv 64 (nv - pv)) ltac:(pin; rewrite zbv_sub; reflexivity).   (* [comment removed for export] *)
        stepb_ft F_8255c D_8255c ltac:(condR).   (* [comment removed for export] *)
        stepb_ft F_82560 D_82560 ltac:(condS).   (* [comment removed for export] *)
        stepb_ft F_82564 D_82564 ltac:(pin; apply c_eq_Zs_ne; lia).   (* [comment removed for export] *)
        sn F_82568 D_82568. fixv (Z_to_bv 64 (pv - nv)) ltac:(pin; rewrite LeptArith2.v_subw_Z, sw32_small by lia; f_equal; lia).   (* [comment removed for export] *)
        stepb_ft F_8256c D_8256c ltac:(condZ).   (* [comment removed for export] *)
        sn F_82570 D_82570. fixv (Z_to_bv 64 (nj + 1)) ltac:(pin; rewrite zbv_addiw_small by lia; reflexivity).   (* [comment removed for export] *)
        stepb_ft F_82574 D_82574 ltac:(condZ).   (* [comment removed for export] *)
        sn F_82578 D_82578. fixv (Z_to_bv 64 js) ltac:(pin; rewrite zbv_addiw_small by lia; f_equal; lia).   (* [comment removed for export] *)
        sn F_8257c D_8257c. fixv (Z_to_bv 64 (js + (pv - nv))) ltac:(pin; rewrite zbv_add; reflexivity).   (* [comment removed for export] *)
        sn F_82580 D_82580. fixv (Z_to_bv 64 (js + (pv - nv))) ltac:(pin; rewrite zbv_addw_small by lia; reflexivity).   (* [comment removed for export] *)
        stepb_ft F_82584 D_82584 ltac:(condR).   (* [comment removed for export] *)
        sn F_82588 D_82588.   (* [comment removed for export] *)
        sn F_8258c D_8258c.   (* [comment removed for export] *)
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity; try solve_regs_agree.
    - (* [comment removed for export] *)
      replace (Z.abs (nv - pv)) with (nv - pv)%Z by lia. replace (nv =? pv)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      eexists. split.
      + stepLD F_8254c D_8254c (Z_to_le_bytes 4 nv) (Z_to_bv 64 nv) ltac:(addr_norm; exact Rn) ltac:(apply lez4; lia).
        rewrite (v_lw_small nv) by lia.
        stepLD F_82550 D_82550 (Z_to_le_bytes 4 pv) (Z_to_bv 64 pv) ltac:(addr_norm; exact Rp) ltac:(apply lez4; lia).
        rewrite (v_lw_small pv) by lia.
        sn F_82554 D_82554. fixv (Z_to_bv 64 (nv - pv)) ltac:(pin; rewrite LeptArith2.v_subw_Z, sw32_small by lia; reflexivity).
        sn F_82558 D_82558. fixv (Z_to_bv 64 (nv - pv)) ltac:(pin; rewrite zbv_sub; reflexivity).
        stepb_ft F_8255c D_8255c ltac:(condR).
        stepb_tk F_82560 D_82560 ltac:(condZ).   (* [comment removed for export] *)
        stepb_ft F_8256c D_8256c ltac:(condZ).   (* [comment removed for export] *)
        sn F_82570 D_82570. fixv (Z_to_bv 64 (nj + 1)) ltac:(pin; rewrite zbv_addiw_small by lia; reflexivity).
        stepb_ft F_82574 D_82574 ltac:(condZ).
        sn F_82578 D_82578. fixv (Z_to_bv 64 js) ltac:(pin; rewrite zbv_addiw_small by lia; f_equal; lia).
        sn F_8257c D_8257c. fixv (Z_to_bv 64 (js + (nv - pv))) ltac:(pin; rewrite zbv_add; reflexivity).
        sn F_82580 D_82580. fixv (Z_to_bv 64 (js + (nv - pv))) ltac:(pin; rewrite zbv_addw_small by lia; reflexivity).
        stepb_ft F_82584 D_82584 ltac:(condR).
        sn F_82588 D_82588.
        sn F_8258c D_8258c.
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity; try solve_regs_agree.
    - (* [comment removed for export] *)
      subst pv. replace (Z.abs (nv - nv)) with 0%Z by lia. rewrite Z.eqb_refl, !Z.add_0_r.
      eexists. split.
      + stepLD F_8254c D_8254c (Z_to_le_bytes 4 nv) (Z_to_bv 64 nv) ltac:(addr_norm; exact Rn) ltac:(apply lez4; lia).
        rewrite (v_lw_small nv) by lia.
        stepLD F_82550 D_82550 (Z_to_le_bytes 4 nv) (Z_to_bv 64 nv) ltac:(addr_norm; exact Rp) ltac:(apply lez4; lia).
        rewrite (v_lw_small nv) by lia.
        sn F_82554 D_82554. fixv (Z_to_bv 64 0) ltac:(pin; rewrite LeptArith2.v_subw_Z, sw32_small by lia; f_equal; lia).
        sn F_82558 D_82558. fixv (Z_to_bv 64 0) ltac:(pin; rewrite zbv_sub; f_equal; lia).
        stepb_ft F_8255c D_8255c ltac:(condR).
        stepb_tk F_82560 D_82560 ltac:(condZ).   (* [comment removed for export] *)
        stepb_tk F_8256c D_8256c ltac:(condZ).   (* [comment removed for export] *)
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_LATn : forall (fx : FPState) regs m (s n i nv : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= i)%Z -> (i + 1 < n)%Z -> (n < 2 ^ 31)%Z -> (0 <= nv < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 92)) 4 = true ->
    pm_R regs s -> getr regs 21 = Z_to_bv 64 n -> getr regs 22 = Z_to_bv 64 i -> getr regs 10 = Z_to_bv 64 nv ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x82588 : word) m rom) (@mkst fx regs' (0x82594 : word) (wbytes m (Z_to_bv 64 (s - 92)) (Z_to_le_bytes 4 nv)) rom)
      /\ pm_R regs' s /\ getr regs' 21 = Z_to_bv 64 n /\ getr regs' 22 = Z_to_bv 64 (i + 1)
      /\ regs_agree (fun r => In r [22]%list) regs regs'.
  Proof.
    intros fx regs m s n i nv Hs Hs64 Hi Hin Hn Hnv SOK (H2 & H8 & H9 & H18 & H19 & H20) H21 H22 H10. unfold pm_R.
    rewrite <- (w2b_Z 4 nv Hnv).
    eexists. split.
    - stepat F_82530 D_82530 (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).   (* [comment removed for export] *)
      stepST F_82534 D_82534 (Z_to_bv 64 (s - 92)) (Z_to_bv 64 nv) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepb_ft F_82538 D_82538 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  Lemma pm_LATx : forall (fx : FPState) regs m (s n i nv : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= i)%Z -> (i + 1 = n)%Z -> (n < 2 ^ 31)%Z -> (0 <= nv < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 92)) 4 = true ->
    pm_R regs s -> getr regs 21 = Z_to_bv 64 n -> getr regs 22 = Z_to_bv 64 i -> getr regs 10 = Z_to_bv 64 nv ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x82588 : word) m rom) (@mkst fx regs' (0x826cc : word) (wbytes m (Z_to_bv 64 (s - 92)) (Z_to_le_bytes 4 nv)) rom)
      /\ pm_R regs' s /\ getr regs' 21 = Z_to_bv 64 n
      /\ regs_agree (fun r => In r [22]%list) regs regs'.
  Proof.
    intros fx regs m s n i nv Hs Hs64 Hi Hin Hn Hnv SOK (H2 & H8 & H9 & H18 & H19 & H20) H21 H22 H10. unfold pm_R.
    rewrite <- (w2b_Z 4 nv Hnv).
    eexists. split.
    - stepat F_82530 D_82530 (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).   (* [comment removed for export] *)
      stepST F_82534 D_82534 (Z_to_bv 64 (s - 92)) (Z_to_bv 64 nv) ltac:(sok_in SOK).   (* [comment removed for export] *)
      stepb_tk F_82538 D_82538 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_L2n : forall (fx : FPState) regs m (s n i nv pv nj js : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= i)%Z -> (i + 1 < n)%Z -> (n < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 4 = Some (Z_to_le_bytes 4 nv) -> rdn SEGS m (Z_to_bv 64 (s - 92)) 4 = Some (Z_to_le_bytes 4 pv) ->
    (0 <= nv <= 19999)%Z -> (0 <= pv <= 19999)%Z -> (0 <= nj <= 19999)%Z -> (0 <= js <= 19999 * 19999)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 92)) 4 = true ->
    pm_R regs s -> getr regs 21 = Z_to_bv 64 n -> getr regs 22 = Z_to_bv 64 i -> getr regs 23 = Z_to_bv 64 js -> getr regs 24 = Z_to_bv 64 nj ->
    getr regs 25 = Z_to_bv 64 IMIN ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x825a4 : word) m rom) (@mkst fx regs' (0x82594 : word) (wbytes m (Z_to_bv 64 (s - 92)) (Z_to_le_bytes 4 nv)) rom)
      /\ pm_R regs' s /\ getr regs' 21 = Z_to_bv 64 n /\ getr regs' 22 = Z_to_bv 64 (i + 1)
      /\ getr regs' 23 = Z_to_bv 64 (js + Z.abs (nv - pv)) /\ getr regs' 24 = Z_to_bv 64 (nj + (if (nv =? pv)%Z then 0 else 1))
      /\ getr regs' 25 = Z_to_bv 64 IMIN
      /\ regs_agree (fun r => In r [10; 11; 12; 13; 22; 23; 24]%list) regs regs'.
  Proof.
    intros fx regs m s n i nv pv nj js Hs Hs64 Hi Hin Hn Rn Rp Hnv Hpv Hnj Hjs SOK HR H21 H22 H23 H24 H25.
    destruct (pm_L2body fx regs m s nv pv nj js Hs Hs64 Rn Rp Hnv Hpv Hnj Hjs HR H23 H24 H25) as (r1 & RUN1 & E10 & E23 & E24 & AG1).
    pose proof HR as (H2 & H8 & H9 & H18 & H19 & H20).
    assert (HR1 : pm_R r1 s) by (unfold pm_R; repeat split; rewrite (AG1 _) by notin_lit; assumption).
    destruct (pm_LATn fx r1 m s n i nv Hs Hs64 Hi Hin Hn ltac:(lia) SOK HR1 ltac:(rewrite (AG1 21) by notin_lit; exact H21)
                ltac:(rewrite (AG1 22) by notin_lit; exact H22) E10) as (r2 & RUN2 & HR2 & F21 & F22 & AG2).
    exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
    split; [exact HR2|]. split; [exact F21|]. split; [exact F22|].
    split; [rewrite (AG2 23) by notin_lit; exact E23|]. split; [rewrite (AG2 24) by notin_lit; exact E24|].
    split; [rewrite (AG2 25) by notin_lit; rewrite (AG1 25) by notin_lit; exact H25|].
    intros r Hr. rewrite (AG2 r), (AG1 r); [reflexivity | |]; intro X; apply Hr; cbn [In] in X |- *; tauto.
  Qed.

  Lemma pm_L2x : forall (fx : FPState) regs m (s n i nv pv nj js : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= i)%Z -> (i + 1 = n)%Z -> (n < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 4 = Some (Z_to_le_bytes 4 nv) -> rdn SEGS m (Z_to_bv 64 (s - 92)) 4 = Some (Z_to_le_bytes 4 pv) ->
    (0 <= nv <= 19999)%Z -> (0 <= pv <= 19999)%Z -> (0 <= nj <= 19999)%Z -> (0 <= js <= 19999 * 19999)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 92)) 4 = true ->
    pm_R regs s -> getr regs 21 = Z_to_bv 64 n -> getr regs 22 = Z_to_bv 64 i -> getr regs 23 = Z_to_bv 64 js -> getr regs 24 = Z_to_bv 64 nj ->
    getr regs 25 = Z_to_bv 64 IMIN ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x825a4 : word) m rom) (@mkst fx regs' (0x826cc : word) (wbytes m (Z_to_bv 64 (s - 92)) (Z_to_le_bytes 4 nv)) rom)
      /\ pm_R regs' s /\ getr regs' 21 = Z_to_bv 64 n
      /\ getr regs' 23 = Z_to_bv 64 (js + Z.abs (nv - pv)) /\ getr regs' 24 = Z_to_bv 64 (nj + (if (nv =? pv)%Z then 0 else 1))
      /\ regs_agree (fun r => In r [10; 11; 12; 13; 22; 23; 24]%list) regs regs'.
  Proof.
    intros fx regs m s n i nv pv nj js Hs Hs64 Hi Hin Hn Rn Rp Hnv Hpv Hnj Hjs SOK HR H21 H22 H23 H24 H25.
    destruct (pm_L2body fx regs m s nv pv nj js Hs Hs64 Rn Rp Hnv Hpv Hnj Hjs HR H23 H24 H25) as (r1 & RUN1 & E10 & E23 & E24 & AG1).
    pose proof HR as (H2 & H8 & H9 & H18 & H19 & H20).
    assert (HR1 : pm_R r1 s) by (unfold pm_R; repeat split; rewrite (AG1 _) by notin_lit; assumption).
    destruct (pm_LATx fx r1 m s n i nv Hs Hs64 Hi Hin Hn ltac:(lia) SOK HR1 ltac:(rewrite (AG1 21) by notin_lit; exact H21)
                ltac:(rewrite (AG1 22) by notin_lit; exact H22) E10) as (r2 & RUN2 & HR2 & F21 & AG2).
    exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
    split; [exact HR2|]. split; [exact F21|].
    split; [rewrite (AG2 23) by notin_lit; exact E23|]. split; [rewrite (AG2 24) by notin_lit; exact E24|].
    intros r Hr. rewrite (AG2 r), (AG1 r); [reflexivity | |]; intro X; apply Hr; cbn [In] in X |- *; tauto.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_D : forall (fx : FPState) regs m (s na : Z) (w21 w23 w24 : word),
    frm_zero (@fp_csr fx) -> (112 <= s)%Z -> (s + 16 < 2 ^ 63)%Z -> (0 <= na < 2 ^ 64)%Z -> (s mod 16 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (Z_to_le_bytes 8 na) ->
    store_ok SEGS m (Z_to_bv 64 (s + 4)) 12 = true ->
    pm_R regs s -> getr regs 21 = w21 -> getr regs 23 = w23 -> getr regs 24 = w24 ->
    exists fr' cs' regs' (bs1 bs2 : list byte),
      msteps SEGS (@mkst fx regs (0x826cc : word) m rom)
                  (@mkst (mkFP fr' cs') regs' (0x613c0 : word) (wbytes (wbytes m (Z_to_bv 64 (s + 12)) bs1) (Z_to_bv 64 (s + 8)) bs2) rom)
      /\ frm_zero cs' /\ length bs1 = 4%nat /\ length bs2 = 4%nat
      /\ pm_R regs' s /\ getr regs' 1 = Z_to_bv 64 0x82720 /\ getr regs' 10 = Z_to_bv 64 na /\ getr regs' 11 = Z_to_bv 64 0
      /\ reg_get fr' 10 = nan_box (Z_to_bv 32 0x3f800000)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros fx regs m s na w21 w23 w24 Hz Hs Hs64 Hna Hs16 Cna SOKC (H2 & H8 & H9 & H18 & H19 & H20) H21 H23 H24. unfold pm_R.
    pose proof (al4_of16 s 12 Hs16 eq_refl) as AL12. pose proof (al4_of16 s 8 Hs16 eq_refl) as AL8.
    eexists _, _, _, _, _. split.
    - stepb_ft F_82674 D_82674 ltac:(condZ).   (* [comment removed for export] *)
      zand F_82678 D_82678 andi_3 AL12. stepb_ft F_8267c D_8267c ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_82680 | reflexivity | exact D_82680 | left; split; reflexivity | left; repeat split; reflexivity | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_82684 D_82684.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_82688 | reflexivity | exact D_82688 | left; split; reflexivity | right; left; repeat split; reflexivity | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fari; [exact F_8268c | reflexivity | exact D_8268c | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_fsw with (a := Z_to_bv 64 (s + 12)); [exact F_82690 | reflexivity | exact D_82690 | gres; imm_norm; addr_tac | sok_in SOKC] | step_simpl ]; fpn.   (* [comment removed for export] *)
      stepb_ft F_82694 D_82694 ltac:(condZ).   (* [comment removed for export] *)
      zand F_82698 D_82698 andi_3 AL8. stepb_ft F_8269c D_8269c ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_826a0 | reflexivity | exact D_826a0 | left; split; reflexivity | left; repeat split; reflexivity | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_826a4 D_826a4.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_826a8 | reflexivity | exact D_826a8 | left; split; reflexivity | right; left; repeat split; reflexivity | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fari; [exact F_826ac | reflexivity | exact D_826ac | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_fsw with (a := Z_to_bv 64 (s + 8)); [exact F_826b0 | reflexivity | exact D_826b0 | gres; imm_norm; addr_tac | sok_in SOKC] | step_simpl ]; fpn.   (* [comment removed for export] *)
      stepb_ft F_826b4 D_826b4 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_826b8 D_826b8 (Z_to_le_bytes 8 na) (Z_to_bv 64 na) ltac:(replace (v_addi (Z_to_bv 64 (s - 112)) 8) with (Z_to_bv 64 (s - 104)) by (unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia); repeat (rewrite rdn_wbytes_out_Z by (rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)); exact Cna) ltac:(apply lez8; lia).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_826bc | reflexivity | exact D_826bc | left; split; reflexivity | right; left; repeat split; reflexivity | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_826c0 D_826c0.   (* [comment removed for export] *)
      sn F_826c4 D_826c4.   (* [comment removed for export] *)
      apply mst_refl.
    - split; [fz Hz|]. split; [apply length_Z_to_le_bytes|]. split; [apply length_Z_to_le_bytes|].
      repeat split; gres; pin; try reflexivity; try solve_regs_agree.
      rewrite fpv_get_same. cbn [fp_format]. rewrite u_Z2bv by lia. rewrite f32u_one. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_E : forall (fx : FPState) regs m (s nae c : Z) (w21 : word),
    frm_zero (@fp_csr fx) -> (112 <= s)%Z -> (s + 16 < 2 ^ 63)%Z -> (1 <= nae)%Z -> (nae + 32 <= s - 112)%Z -> (0 <= c < 2 ^ 31)%Z ->
    (s mod 16 = 0)%Z -> (nae mod 8 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 (nae + 4)) 4 = Some (Z_to_le_bytes 4 c) ->
    store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true -> store_ok SEGS m (Z_to_bv 64 (s + 4)) 12 = true ->
    pm_R regs s -> getr regs 10 = Z_to_bv 64 nae -> getr regs 21 = w21 ->
    exists fr' cs' regs' (bs : list byte),
      msteps SEGS (@mkst fx regs (0x82720 : word) m rom)
                  (@mkst (mkFP fr' cs') regs' (0x61794 : word) (wbytes (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 nae))) (Z_to_bv 64 (s + 4)) bs) rom)
      /\ frm_zero cs' /\ length bs = 4%nat
      /\ pm_R regs' s /\ getr regs' 1 = Z_to_bv 64 0x82754 /\ getr regs' 10 = Z_to_bv 64 (s - 112)
      /\ regs_agree (fun r => In r [1; 10; 11; 21]%list) regs regs'.
  Proof.
    intros fx regs m s nae c w21 Hz Hs Hs64 Hnae Hnae2 Hc Hs16 ALnae Cc SOK SOKC (H2 & H8 & H9 & H18 & H19 & H20) H10 H21. unfold pm_R.
    pose proof (al4_of16 s 4 Hs16 eq_refl) as AL4.
    eexists _, _, _, _. split.
    - stepST F_826c8 D_826c8 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 nae) ltac:(sok_in SOK).   (* [comment removed for export] *)
      sn F_826cc D_826cc.   (* [comment removed for export] *)
      stepb_ft F_61918 D_61918 ltac:(condZ).   (* [comment removed for export] *)
      zand F_6191c D_6191c andi_7 ALnae. stepb_ft F_61920 D_61920 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_61924 D_61924 (Z_to_le_bytes 4 c) (Z_to_bv 64 c) ltac:(addr_norm; repeat rdn_peel1; exact Cc) ltac:(apply lez4; lia).
      rewrite (v_lw_small c) by lia.   (* [comment removed for export] *)
      stepret F_61928 D_61928 (Z_to_bv 64 0x82728) ltac:(reflexivity).   (* [comment removed for export] *)
      sn F_826d0 D_826d0. fixv (Z_to_bv 64 (c - 1)) ltac:(pin; rewrite zbv_addiw_small by lia; f_equal; lia).   (* [comment removed for export] *)
      stepb_ft F_826d4 D_826d4 ltac:(condS).   (* [comment removed for export] *)
      zand F_826d8 D_826d8 andi_3 AL4. stepb_ft F_826dc D_826dc ltac:(condZ).   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_826e0 | reflexivity | exact D_826e0 | left; split; reflexivity | left; repeat split; reflexivity | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_826e4 D_826e4.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_826e8 | reflexivity | exact D_826e8 | left; split; reflexivity | right; left; repeat split; reflexivity | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fpv_step_fari; [exact F_826ec | reflexivity | exact D_826ec | cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
      chain_step; [ reflexivity | eapply fp_step_fsw with (a := Z_to_bv 64 (s + 4)); [exact F_826f0 | reflexivity | exact D_826f0 | gres; imm_norm; addr_tac | sok_in SOKC] | step_simpl ]; fpn.   (* [comment removed for export] *)
      sn F_826f4 D_826f4.   (* [comment removed for export] *)
      sn F_826f8 D_826f8.   (* [comment removed for export] *)
      apply mst_refl.
    - split; [fz Hz|]. split; [apply length_Z_to_le_bytes|]. repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_F : forall (fx : FPState) regs m (s : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> pm_R regs s ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x82754 : word) m rom) (@mkst fx regs' (0x61794 : word) m rom)
      /\ pm_R regs' s /\ getr regs' 1 = Z_to_bv 64 0x8275c /\ getr regs' 10 = Z_to_bv 64 (s - 104)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros fx regs m s Hs Hs64 (H2 & H8 & H9 & H18 & H19 & H20). unfold pm_R.
    eexists. split.
    - zv F_826fc D_826fc (Z_to_bv 64 (s - 104)).   (* [comment removed for export] *)
      sn F_82700 D_82700.   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pm_G : forall (fx : FPState) regs m (s : Z) (ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 : word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) -> rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) -> rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) -> rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
    rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v22) -> rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v23) ->
    rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 v24) -> rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 v25) ->
    getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs',
      msteps SEGS (@mkst fx regs (0x8275c : word) m rom) (@mkst fx regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\ getr regs' 20 = v20 /\ getr regs' 21 = v21
      /\ getr regs' 22 = v22 /\ getr regs' 23 = v23 /\ getr regs' 24 = v24 /\ getr regs' 25 = v25
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
  Proof.
    intros fx regs m s ret v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 Hs Hs64 Hret C1 C8 C9 C18 C19 C20 C21 C22 C23 C24 C25 H2.
    eexists. split.
    - sn F_82704 D_82704.   (* [comment removed for export] *)
      sn F_82708 D_82708.   (* [comment removed for export] *)
      stepLD8 F_82640 D_82640 ret.
      stepLD8 F_82644 D_82644 v8.
      stepLD8 F_82648 D_82648 v9.
      stepLD8 F_8264c D_8264c v18.
      stepLD8 F_82650 D_82650 v19.
      stepLD8 F_82654 D_82654 v20.
      stepLD8 F_82658 D_82658 v21.
      stepLD8 F_8265c D_8265c v22.
      stepLD8 F_82660 D_82660 v23.
      stepLD8 F_82664 D_82664 v24.
      stepLD8 F_82668 D_82668 v25.
      zv F_8266c D_8266c (Z_to_bv 64 s).   (* [comment removed for export] *)
      stepret F_82670 D_82670 ret ltac:(reflexivity).   (* [comment removed for export] *)
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
    exists regs', msteps SEGS (@mkst fx regs (0x5d140 : word) m rom) (@mkst fx regs' ret (FR3 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros fx regs m s sz dptr ret Hs Hs64 Hsz Hret SOK H2 H1 H10 H11. unfold FR3. eexists. split.
    - zv F_5d0e8 D_5d0e8 (Z_to_bv 64 (s - 48)).
      stepST F_5d0ec D_5d0ec (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_5d0f0 D_5d0f0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_5d0f4 D_5d0f4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_5d0f8 D_5d0f8. sn F_5d0fc D_5d0fc. stepb_tk F_5d100 D_5d100 ltac:(condZ).
      sn F_5d150 D_5d150.
      stepLD8 F_5d154 D_5d154 ret. stepLD8 F_5d158 D_5d158 (getr regs 8). stepLD8 F_5d15c D_5d15c (getr regs 9).
      zv F_5d160 D_5d160 (Z_to_bv 64 s). stepret F_5d164 D_5d164 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_big : forall (fx : FPState) regs m (s sz : Z) (dptr ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (3 <= sz < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    store_ok SEGS m (Z_to_bv 64 0xfa308) 8 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = dptr -> getr regs 11 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (@mkst fx regs (0x5d140 : word) m rom)
                              (@mkst fx regs' (0x7c5c0 : word) (wbytes (FR3 m s ret regs) (Z_to_bv 64 0xfa308) (word_to_le_bytes 8 (Z_to_bv 64 0x5d1c0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x5d178 /\ getr regs' 10 = dptr /\ getr regs' 11 = Z_to_bv 64 sz
      /\ getr regs' 8 = Z_to_bv 64 sz /\ getr regs' 9 = dptr
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros fx regs m s sz dptr ret Hs Hs64 Hsz SOK SOKh H2 H1 H10 H11. unfold FR3. eexists. split.
    - zv F_5d0e8 D_5d0e8 (Z_to_bv 64 (s - 48)).
      stepST F_5d0ec D_5d0ec (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_5d0f0 D_5d0f0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_5d0f4 D_5d0f4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_5d0f8 D_5d0f8. sn F_5d0fc D_5d0fc. stepb_ft F_5d100 D_5d100 ltac:(condZ).
      sn F_5d104 D_5d104. sn F_5d108 D_5d108. sn F_5d10c D_5d10c. sn F_5d110 D_5d110.
      stepb_tk F_5d308 D_5d308 ltac:(condZ).
      sn F_5d314 D_5d314.
      stepST F_5d318 D_5d318 (Z_to_bv 64 0xfa308) (Z_to_bv 64 0x5d1c0) ltac:(store_ok_peel; exact SOKh).
      stepret F_5d31c D_5d31c (0x5d16c : word) ltac:(bveq).
      sn F_5d114 D_5d114. sn F_5d118 D_5d118. sn F_5d11c D_5d11c. sn F_7c46c D_7c46c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_B0 : forall (fx : FPState) regs m (s : Z) (ret s0v s1v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (@mkst fx regs (0x5d178 : word) m rom) (@mkst fx regs' ret (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros fx regs m s ret s0v s1v Hs Hs64 Hret SOK R1 R2 R3 H2 H10. eexists. split.
    - stepST F_5d120 D_5d120 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_5d124 D_5d124 ltac:(condZ).
      sn F_5d150 D_5d150.
      stepLD8 F_5d154 D_5d154 ret. stepLD8 F_5d158 D_5d158 s0v. stepLD8 F_5d15c D_5d15c s1v.
      zv F_5d160 D_5d160 (Z_to_bv 64 s). stepret F_5d164 D_5d164 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_B1 : forall (fx : FPState) regs m (s pix : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 pix ->
    exists regs', msteps SEGS (@mkst fx regs (0x5d178 : word) m rom)
       (@mkst fx regs' (0x82400 : word) (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 pix))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x5d1a0 /\ getr regs' 10 = Z_to_bv 64 pix
      /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1 /\ getr regs' 13 = Z_to_bv 64 1
      /\ getr regs' 14 = Z_to_bv 64 (s - 48 + 12) /\ getr regs' 15 = Z_to_bv 64 (s - 48 + 8) /\ getr regs' 16 = Z_to_bv 64 (s - 48 + 4)
      /\ getr regs' 17 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros fx regs m s pix Hs Hs64 Hp SOK H2 H10. eexists. split.
    - stepST F_5d120 D_5d120 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 pix) ltac:(sok_in SOK).
      stepb_ft F_5d124 D_5d124 ltac:(condZ).
      sn F_5d128 D_5d128. sn F_5d12c D_5d12c. sn F_5d130 D_5d130.
      zv F_5d134 D_5d134 (Z_to_bv 64 (s - 48 + 12)). zv F_5d138 D_5d138 (Z_to_bv 64 (s - 48 + 8)). zv F_5d13c D_5d13c (Z_to_bv 64 (s - 48 + 4)).
      sn F_5d140 D_5d140. sn F_5d144 D_5d144. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_C : forall (fx : FPState) regs m (s : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs', msteps SEGS (@mkst fx regs (0x5d1a0 : word) m rom) (@mkst fx regs' (0x636c8 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x5d1a8 /\ getr regs' 10 = Z_to_bv 64 (s - 32)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros fx regs m s Hs Hs64 H2. eexists. split.
    - zv F_5d148 D_5d148 (Z_to_bv 64 (s - 32)). sn F_5d14c D_5d14c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_E : forall (fx : FPState) regs m (s : Z) (ret s0v s1v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs', msteps SEGS (@mkst fx regs (0x5d1a8 : word) m rom) (@mkst fx regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros fx regs m s ret s0v s1v Hs Hs64 Hret R1 R2 R3 H2. eexists. split.
    - sn F_5d150 D_5d150.
      stepLD8 F_5d154 D_5d154 ret. stepLD8 F_5d158 D_5d158 s0v. stepLD8 F_5d15c D_5d15c s1v.
      zv F_5d160 D_5d160 (Z_to_bv 64 s). stepret F_5d164 D_5d164 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End Segs2.
