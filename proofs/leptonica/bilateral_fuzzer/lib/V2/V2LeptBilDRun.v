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
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptUb V2_code_bilateralDestroy.
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
Ltac snez1 F D := stepat F D (Z_to_bv 64 1) ltac:(gres; pin; imm_norm; apply zbv_snez; lia).
Ltac seqz0 F D := stepat F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
Ltac rinv_tac :=
  repeat (eapply rinv_wbytes;
          [ | rewrite ?length_N_to_le_bytes, ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; reflexivity | lia | lia
          | first [ (eexists; split; [ left; reflexivity | cbn [fst snd]; lia ])
                  | (eexists; split; [ right; left; reflexivity | cbn [fst snd]; lia ]) ] ]);
  apply rinv_refl.
Ltac post1 :=
  lazymatch goal with
  | |- rinv _ _ _ => rinv_tac
  | |- regs_agree _ _ _ => solve_regs_agree
  | |- rdn _ _ _ _ = Some (word_to_le_bytes 8 _) => gres; rdn_solve
  | |- rdn _ (wbytes _ _ (word_to_le_bytes 8 _)) _ 8 = Some (Z_to_le_bytes 8 0) =>
      rewrite <- (w2b_Z 8 0) by lia; apply rdn_wbytes_hit8; rewrite u_Z2bv by lia; lia
  | |- getr _ _ = _ => gres; pin; first [ reflexivity | apply bv_eq; rewrite ?u_Z2bv by lia; lia ]
  | |- _ = _ => first [ reflexivity | assumption ]
  end.
Ltac fin E :=
  lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ => replace pc with (Z_to_bv 64 E) by (apply bv_eq; reflexivity) end;
  apply mst_refl.
Ltac post := repeat (lazymatch goal with |- _ /\ _ => split end); post1.

Section Segs.
Variable rom : word -> option byte.
#[local] Existing Instance exf_fxd | 100.

Lemma bl_A : forall (fx : FPState) regs (m : word -> option byte) (s pp bil : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (s <= pp)%Z ->
  (pp + 8 <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 48)%Z ->
  (pp mod 8 = 0)%Z ->
  (bil mod 8 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 bil) ->
  store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 pp ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 240220) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 104492) M' rom /\
      rinv [((s - 40)%Z, 40%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
      getr regs' 1 = Z_to_bv 64 240280 /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 8 = Z_to_bv 64 pp /\ getr regs' 9 = Z_to_bv 64 bil /\ getr regs' 10 = Z_to_bv 64 bil /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs').
Proof.
  intros fx regs m s pp bil Hs Hpp Hpp47 Hbil Hbils ALpp ALbil Rpp SOK H2 H10.
  unfold reach. eexists. split.
  - norm_pc.
    zv F_3aa5c D_3aa5c (Z_to_bv 64 (s - 48)).
    stepST F_3aa60 D_3aa60 (Z_to_bv 64 (s - 8)) (getr regs 1) ltac:(sok_in SOK).
    stepST F_3aa64 D_3aa64 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
    stepST F_3aa68 D_3aa68 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
    stepST F_3aa6c D_3aa6c (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
    stepST F_3aa70 D_3aa70 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
    sn F_3aa74 D_3aa74.
    guard8 F_3aa78 D_3aa78 ALpp.
    stepb_ft F_3aa7c D_3aa7c ltac:(condZ).
    stepLD F_3aa80 D_3aa80 (Z_to_le_bytes 8 bil) (Z_to_bv 64 bil) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
    stepb_ft F_3aa84 D_3aa84 ltac:(condZ).
    guard8 F_3aa88 D_3aa88 ALbil.
    stepb_ft F_3aa8c D_3aa8c ltac:(condZ).
    sn F_3aa90 D_3aa90.
    sn F_3aa94 D_3aa94.
    fin 0x1982c%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma bl_B : forall (fx : FPState) regs (m : word -> option byte) (s bil : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 48)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 9 = Z_to_bv 64 bil ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 240280) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 104492) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 240288 /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 9 = Z_to_bv 64 bil /\ getr regs' 10 = Z_to_bv 64 (bil + 8) /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s bil Hs Hbil Hbils H2 H9.
  unfold reach. eexists. split.
  - norm_pc.
    zv F_3aa98 D_3aa98 (Z_to_bv 64 (bil + 8)).
    sn F_3aa9c D_3aa9c.
    fin 0x1982c%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma bl_C : forall (fx : FPState) regs (m : word -> option byte) (s bil : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 48)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 9 = Z_to_bv 64 bil ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 240288) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 99136) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 240296 /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 9 = Z_to_bv 64 bil /\ getr regs' 10 = Z_to_bv 64 (bil + 88) /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s bil Hs Hbil Hbils H2 H9.
  unfold reach. eexists. split.
  - norm_pc.
    zv F_3aaa0 D_3aaa0 (Z_to_bv 64 (bil + 88)).
    sn F_3aaa4 D_3aaa4.
    fin 0x18340%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma bl_F0 : forall (fx : FPState) regs (m : word -> option byte) (s bil v : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 48)%Z ->
  (0 <= v < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (bil + 32)) 8 = Some (Z_to_le_bytes 8 v) ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 9 = Z_to_bv 64 bil ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 240296) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 246320) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 240304 /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 9 = Z_to_bv 64 bil /\ getr regs' 10 = Z_to_bv 64 v /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s bil v Hs Hbil Hbils Hv Rv H2 H9.
  unfold reach. eexists. split.
  - norm_pc.
    stepLD F_3aaa8 D_3aaa8 (Z_to_le_bytes 8 v) (Z_to_bv 64 v) ltac:(addr_norm; exact Rv) ltac:(apply lez8; lia).
    sn F_3aaac D_3aaac.
    fin 0x3c230%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma bl_F1 : forall (fx : FPState) regs (m : word -> option byte) (s bil v : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 48)%Z ->
  (0 <= v < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (bil + 40)) 8 = Some (Z_to_le_bytes 8 v) ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 9 = Z_to_bv 64 bil ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 240304) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 246320) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 240312 /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 9 = Z_to_bv 64 bil /\ getr regs' 10 = Z_to_bv 64 v /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s bil v Hs Hbil Hbils Hv Rv H2 H9.
  unfold reach. eexists. split.
  - norm_pc.
    stepLD F_3aab0 D_3aab0 (Z_to_le_bytes 8 v) (Z_to_bv 64 v) ltac:(addr_norm; exact Rv) ltac:(apply lez8; lia).
    sn F_3aab4 D_3aab4.
    fin 0x3c230%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma bl_F2 : forall (fx : FPState) regs (m : word -> option byte) (s bil v : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 48)%Z ->
  (0 <= v < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (bil + 64)) 8 = Some (Z_to_le_bytes 8 v) ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 9 = Z_to_bv 64 bil ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 240312) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 246320) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 240320 /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 9 = Z_to_bv 64 bil /\ getr regs' 10 = Z_to_bv 64 v /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s bil v Hs Hbil Hbils Hv Rv H2 H9.
  unfold reach. eexists. split.
  - norm_pc.
    stepLD F_3aab8 D_3aab8 (Z_to_le_bytes 8 v) (Z_to_bv 64 v) ltac:(addr_norm; exact Rv) ltac:(apply lez8; lia).
    sn F_3aabc D_3aabc.
    fin 0x3c230%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma bl_F3 : forall (fx : FPState) regs (m : word -> option byte) (s bil v : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 48)%Z ->
  (0 <= v < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (bil + 72)) 8 = Some (Z_to_le_bytes 8 v) ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 9 = Z_to_bv 64 bil ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 240320) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 246320) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 240328 /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 9 = Z_to_bv 64 bil /\ getr regs' 10 = Z_to_bv 64 v /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s bil v Hs Hbil Hbils Hv Rv H2 H9.
  unfold reach. eexists. split.
  - norm_pc.
    stepLD F_3aac0 D_3aac0 (Z_to_le_bytes 8 v) (Z_to_bv 64 v) ltac:(addr_norm; exact Rv) ltac:(apply lez8; lia).
    sn F_3aac4 D_3aac4.
    fin 0x3c230%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma bl_F4 : forall (fx : FPState) regs (m : word -> option byte) (s bil v : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 48)%Z ->
  (0 <= v < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (bil + 80)) 8 = Some (Z_to_le_bytes 8 v) ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 9 = Z_to_bv 64 bil ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 240328) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 246320) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 240336 /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 9 = Z_to_bv 64 bil /\ getr regs' 10 = Z_to_bv 64 v /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s bil v Hs Hbil Hbils Hv Rv H2 H9.
  unfold reach. eexists. split.
  - norm_pc.
    stepLD F_3aac8 D_3aac8 (Z_to_le_bytes 8 v) (Z_to_bv 64 v) ltac:(addr_norm; exact Rv) ltac:(apply lez8; lia).
    sn F_3aacc D_3aacc.
    fin 0x3c230%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma bl_G : forall (fx : FPState) regs (m : word -> option byte) (s bil : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 48)%Z ->
  rdn SEGS m (Z_to_bv 64 (bil + 56)) 4 = Some (Z_to_le_bytes 4 10) ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 9 = Z_to_bv 64 bil ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 240336) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 240352) M' rom /\
      M' = m /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 9 = Z_to_bv 64 bil /\ getr regs' 18 = Z_to_bv 64 (8 * 0) /\ getr regs' 19 = Z_to_bv 64 0 /\
      regs_agree (fun r => In r [10; 18; 19]%list) regs regs').
Proof.
  intros fx regs m s bil Hs Hbil Hbils R56 H2 H9.
  unfold reach. eexists. split.
  - norm_pc.
    stepLD F_3aad0 D_3aad0 (Z_to_le_bytes 4 10) (Z_to_bv 64 10) ltac:(addr_norm; exact R56) ltac:(apply lez4; lia).
    stepb_ft F_3aad4 D_3aad4 ltac:(condZ).
    zv F_3aad8 D_3aad8 (Z_to_bv 64 0).
    zv F_3aadc D_3aadc (Z_to_bv 64 0).
    fin 0x3aae0%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma bl_Lb : forall (fx : FPState) regs (m : word -> option byte) (s bil ls i lf : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 48)%Z ->
  (4096 <= ls)%Z ->
  (ls + 80 <= 2 ^ 47)%Z ->
  (ls mod 8 = 0)%Z ->
  (0 <= i <= 9)%Z ->
  (0 <= lf < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (bil + 96)) 8 = Some (Z_to_le_bytes 8 ls) ->
  rdn SEGS m (Z_to_bv 64 (ls + 8 * i)) 8 = Some (Z_to_le_bytes 8 lf) ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 9 = Z_to_bv 64 bil ->
  getr regs 18 = Z_to_bv 64 (8 * i) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 240352) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 246320) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 240404 /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 9 = Z_to_bv 64 bil /\ getr regs' 10 = Z_to_bv 64 lf /\
      regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs').
Proof.
  intros fx regs m s bil ls i lf Hs Hbil Hbils Hls Hls47 ALls Hi Hlf Rls Rlf H2 H9 H18.
  assert (ALx : ((ls + 8 * i) mod 8 = 0)%Z) by (replace (ls + 8 * i)%Z with (ls + i * 8)%Z by lia; rewrite Z_mod_plus_full; exact ALls).
  unfold reach. eexists. split.
  - norm_pc.
    stepLD F_3aae0 D_3aae0 (Z_to_le_bytes 8 ls) (Z_to_bv 64 ls) ltac:(addr_norm; exact Rls) ltac:(apply lez8; lia).
    zv F_3aae4 D_3aae4 (Z_to_bv 64 (ls + 8 * i)).
    stepb_ft F_3aae8 D_3aae8 ltac:(condZ).
    snez1 F_3aaec D_3aaec.
    seqz0 F_3aaf0 D_3aaf0.
    sn F_3aaf4 D_3aaf4.
    stepb_ft F_3aaf8 D_3aaf8 ltac:(condZ).
    stepb_ft F_3aafc D_3aafc ltac:(condZ).
    zv F_3ab00 D_3ab00 (Z_to_bv 64 (ls + 8 * i)).
    guard8 F_3ab04 D_3ab04 ALx.
    stepb_ft F_3ab08 D_3ab08 ltac:(condZ).
    stepLD F_3ab0c D_3ab0c (Z_to_le_bytes 8 lf) (Z_to_bv 64 lf) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rlf) ltac:(apply lez8; lia).
    sn F_3ab10 D_3ab10.
    fin 0x3c230%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma bl_Hm : forall (fx : FPState) regs (m : word -> option byte) (s bil i : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 48)%Z ->
  (0 <= i <= 8)%Z ->
  rdn SEGS m (Z_to_bv 64 (bil + 56)) 4 = Some (Z_to_le_bytes 4 10) ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 9 = Z_to_bv 64 bil ->
  getr regs 18 = Z_to_bv 64 (8 * i) ->
  getr regs 19 = Z_to_bv 64 i ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 240404) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 240352) M' rom /\
      M' = m /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 9 = Z_to_bv 64 bil /\ getr regs' 18 = Z_to_bv 64 (8 * (i + 1)) /\ getr regs' 19 = Z_to_bv 64 (i + 1) /\
      regs_agree (fun r => In r [10; 18; 19]%list) regs regs').
Proof.
  intros fx regs m s bil i Hs Hbil Hbils Hi R56 H2 H9 H18 H19.
  unfold reach. eexists. split.
  - norm_pc.
    stepLD F_3ab14 D_3ab14 (Z_to_le_bytes 4 10) (Z_to_bv 64 10) ltac:(addr_norm; exact R56) ltac:(apply lez4; lia).
    zv F_3ab18 D_3ab18 (Z_to_bv 64 (i + 1)).
    zv F_3ab1c D_3ab1c (Z_to_bv 64 (8 * (i + 1))).
    stepb_tk F_3ab20 D_3ab20 ltac:(condZ).
    fin 0x3aae0%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma bl_Hl : forall (fx : FPState) regs (m : word -> option byte) (s bil : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 48)%Z ->
  rdn SEGS m (Z_to_bv 64 (bil + 56)) 4 = Some (Z_to_le_bytes 4 10) ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 9 = Z_to_bv 64 bil ->
  getr regs 18 = Z_to_bv 64 72 ->
  getr regs 19 = Z_to_bv 64 9 ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 240404) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 240420) M' rom /\
      M' = m /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 9 = Z_to_bv 64 bil /\
      regs_agree (fun r => In r [10; 18; 19]%list) regs regs').
Proof.
  intros fx regs m s bil Hs Hbil Hbils R56 H2 H9 H18 H19.
  unfold reach. eexists. split.
  - norm_pc.
    stepLD F_3ab14 D_3ab14 (Z_to_le_bytes 4 10) (Z_to_bv 64 10) ltac:(addr_norm; exact R56) ltac:(apply lez4; lia).
    sn F_3ab18 D_3ab18.
    sn F_3ab1c D_3ab1c.
    stepb_ft F_3ab20 D_3ab20 ltac:(condZ).
    fin 0x3ab24%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma bl_I : forall (fx : FPState) regs (m : word -> option byte) (s bil ls : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 48)%Z ->
  (0 <= ls < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (bil + 96)) 8 = Some (Z_to_le_bytes 8 ls) ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 9 = Z_to_bv 64 bil ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 240420) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 246320) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 240428 /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 9 = Z_to_bv 64 bil /\ getr regs' 10 = Z_to_bv 64 ls /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s bil ls Hs Hbil Hbils Hls Rls H2 H9.
  unfold reach. eexists. split.
  - norm_pc.
    stepLD F_3ab24 D_3ab24 (Z_to_le_bytes 8 ls) (Z_to_bv 64 ls) ltac:(addr_norm; exact Rls) ltac:(apply lez8; lia).
    sn F_3ab28 D_3ab28.
    fin 0x3c230%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma bl_J : forall (fx : FPState) regs (m : word -> option byte) (s bil : Z),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (4096 <= bil)%Z ->
  (bil + 104 <= s - 48)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 9 = Z_to_bv 64 bil ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 240428) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 246320) M' rom /\
      M' = m /\ getr regs' 1 = Z_to_bv 64 240436 /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 10 = Z_to_bv 64 bil /\
      regs_agree (fun r => In r [1; 10]%list) regs regs').
Proof.
  intros fx regs m s bil Hs Hbil Hbils H2 H9.
  unfold reach. eexists. split.
  - norm_pc.
    sn F_3ab2c D_3ab2c.
    sn F_3ab30 D_3ab30.
    fin 0x3c230%Z.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

Lemma bl_K : forall (fx : FPState) regs (m : word -> option byte) (s pp : Z) (ret : word) (v1 v8 v9 v18 v19 : word),
  (4096 + 48 <= s <= 2 ^ 47)%Z ->
  (s <= pp)%Z ->
  (pp + 8 <= 2 ^ 47)%Z ->
  ret_ok ret ->
  v1 = ret ->
  store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 v1) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
  getr regs 2 = Z_to_bv 64 (s - 48) ->
  getr regs 8 = Z_to_bv 64 pp ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 240436) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' ret M' rom /\
      rinv [(pp, 8%Z)] m M' /\ rdn SEGS M' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) /\
      getr regs' 2 = Z_to_bv 64 s /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19 /\
      regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs').
Proof.
  intros fx regs m s pp ret v1 v8 v9 v18 v19 Hs Hpp Hpp47 Hret E1 SOK R1 R8 R9 R18 R19 H2 H8. subst v1.
  unfold reach. eexists. split.
  - norm_pc.
    stepST F_3ab34 D_3ab34 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(sok_in SOK).
    stepLD8 F_3ab38 D_3ab38 ret.
    stepLD8 F_3ab3c D_3ab3c v8.
    stepLD8 F_3ab40 D_3ab40 v9.
    stepLD8 F_3ab44 D_3ab44 v18.
    stepLD8 F_3ab48 D_3ab48 v19.
    zv F_3ab4c D_3ab4c (Z_to_bv 64 s).
    stepret F_3ab50 D_3ab50 ret ltac:(bveq).
    apply mst_refl.
  - do 2 eexists. split; [reflexivity|]. post.
Qed.

End Segs.
