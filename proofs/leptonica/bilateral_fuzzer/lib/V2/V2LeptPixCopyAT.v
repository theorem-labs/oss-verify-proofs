(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptUb.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptErr.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptCmapValid V2LeptCmap2 V2_code_pixSetColormap.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoomBL.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section PixCopyA.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

  (* [comment removed for export] *)
  Definition FR4c (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes m
       (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
       (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
       (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
       (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

  Definition cells3 (m : word -> option byte) (s : Z) (ret s0v s1v : word) : Prop :=
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v).

  Lemma cells3_FR4c : forall m s ret regs, (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    cells3 (FR4c m s ret regs) s ret (getr regs 8) (getr regs 9).
  Proof. intros m s ret regs Hs Hs64. unfold cells3, FR4c. repeat split; rdn_solve. Qed.

  Lemma cells3_frm : forall C s' m m' s ret s0v s1v, Cok C -> FRM C s' m m' ->
    (s' <= s - 24)%Z -> (c_top C - LSTK <= s')%Z -> (s < 2 ^ 64)%Z ->
    cells3 m s ret s0v s1v -> cells3 m' s ret s0v s1v.
  Proof.
    intros C s' m m' s ret s0v s1v CK F Hs' Hlo Hs64 (R1 & R2 & R3). unfold cells3.
    rewrite !(FRM_rdn16 C s' m m' _ 8 CK F) by (cbn; lia). repeat split; assumption.
  Qed.

  Lemma cells3_out : forall m m' (lo hi s : Z) ret s0v s1v,
    (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) -> (hi <= s - 24 \/ s <= lo)%Z -> (24 <= s)%Z -> (s < 2 ^ 64)%Z ->
    cells3 m s ret s0v s1v -> cells3 m' s ret s0v s1v.
  Proof.
    intros m m' lo hi s ret s0v s1v OUT Hhi Hs Hs64 (R1 & R2 & R3). unfold cells3.
    repeat split; (eapply (rdn_after m m' lo hi); [exact OUT | lia | cbn; lia | cbn; lia | assumption]).
  Qed.

Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma pcm_A : forall regs m (s pixd pixs : Z) (vd vs : pixv) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixd)%Z -> (1 <= pixs)%Z -> pixd <> pixs -> (pixd mod 16 = 0)%Z -> (pixs mod 16 = 0)%Z ->
    PIXat m pixd vd -> PIXat m pixs vs -> p_d vd = p_d vs -> p_cmap vd = 0%Z ->
    (pixd + 64 <= s - 48 \/ s <= pixd)%Z -> (pixs + 64 <= s - 48 \/ s <= pixs)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x19c84 : word) m rom) (mkst regs' (0x19ce8 : word) (FR4c m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = ret
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs /\ getr regs' 8 = Z_to_bv 64 (p_cmap vs) /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [2; 8; 12; 13]%list) regs regs'.
  Proof.
    intros regs m s pixd pixs vd vs ret Hs Hs64 Hpd Hps NE ALd ALs PXd PXs Ed Ecm DJd DJs SOK H2 H1 H10 H11.
    assert (ALd8 : (pixd mod 8 = 0)%Z) by (apply al16_mod8; exact ALd). assert (ALs8 : (pixs mod 8 = 0)%Z) by (apply al16_mod8; exact ALs).
    pose proof PXd as (Hd0 & Hd64 & WFd & _). pose proof PXs as (Hs0 & Hs64' & WFs & _).
    pose proof (wf_d _ WFs) as Rd. pose proof (wf_cmap _ WFs) as Rcm.
    pose proof (PIX_rd_d SEGS m pixd vd PXd) as Cdd. rewrite Ed in Cdd. pose proof (PIX_rd_d SEGS m pixs vs PXs) as Cds.
    pose proof (PIX_rd_cmap SEGS m pixd vd PXd) as Ccd. rewrite Ecm in Ccd. pose proof (PIX_rd_cmap SEGS m pixs vs PXs) as Ccs.
    unfold FR4c. eexists. split.
    - zv F_19c84 D_19c84 (Z_to_bv 64 (s - 48)).
      stepST F_19c88 D_19c88 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_19c8c D_19c8c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_19c90 D_19c90 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_19c94 D_19c94 ltac:(condZ).
      stepb_ft F_19c98 D_19c98 ltac:(condZ).
      stepb_ft F_19c9c D_19c9c ltac:(condZ).
      guard8 F_19ca0 D_19ca0 ALs8. stepb_ft F_19ca4 D_19ca4 ltac:(condZ). (* [comment removed for export] *)
      guard8 F_19ca8 D_19ca8 ALd8. stepb_ft F_19cac D_19cac ltac:(condZ). (* [comment removed for export] *)
      stepLD F_19cb0 D_19cb0 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; repeat rdn_peel1; exact Cds) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepLD F_19cb4 D_19cb4 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; repeat rdn_peel1; exact Cdd) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepb_ft F_19cb8 D_19cb8 ltac:(condZ).
      stepLD F_19cbc D_19cbc (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; repeat rdn_peel1; exact Ccd) ltac:(apply lez8; lia).
      stepST F_19cc0 D_19cc0 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_19cc4 D_19cc4 ltac:(condZ).
      stepLD F_19ce4 D_19ce4 (Z_to_le_bytes 8 (p_cmap vs)) (Z_to_bv 64 (p_cmap vs)) ltac:(addr_norm; repeat rdn_peel1; exact Ccs) ltac:(apply lez8; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcm_RET : forall regs m (s : Z) (ret s0v s1v a0v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cells3 m s ret s0v s1v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = a0v ->
    exists regs',
      msteps SEGS (mkst regs (0x19e6c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = a0v /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v a0v Hs Hs64 Hret (R8 & R16 & R24) H2 H10. eexists. split.
    - stepLD8 F_19e6c D_19e6c ret. stepLD8 F_19e70 D_19e70 s0v. stepLD8 F_19e74 D_19e74 s1v.
      zv F_19e78 D_19e78 (Z_to_bv 64 s). stepret F_19e7c D_19e7c ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcm_A0 : forall regs m (s : Z) (ret s0v s1v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cells3 m s ret s0v s1v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x19ce8 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v Hs Hs64 Hret CE H2 H8.
    assert (RUN1 : exists r1, msteps SEGS (mkst regs (0x19ce8 : word) m rom) (mkst r1 (0x19e6c : word) m rom)
                              /\ getr r1 2 = Z_to_bv 64 (s - 48) /\ getr r1 10 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [10]%list) regs r1).
    { eexists. split.
      - stepb_tk F_19ce8 D_19ce8 ltac:(condZ). sn F_19d7c D_19d7c. sn F_19d80 D_19d80. apply mst_refl.
      - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
    destruct RUN1 as (r1 & RUN1 & Q2 & Q10 & AG1).
    destruct (pcm_RET r1 m s ret s0v s1v (Z_to_bv 64 0) Hs Hs64 Hret CE Q2 Q10) as (r2 & RUN2 & P2 & P1 & P10 & P8 & P9 & AG2).
    exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] |].
    repeat split; try assumption. eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  Qed.

  (* [comment removed for export] *)
  Lemma pcm_A1 : forall regs m (s cm pixd : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= cm)%Z -> (cm < 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 cm -> getr regs 10 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x19ce8 : word) m rom) (mkst regs' (0x1d734 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x19d00
      /\ getr regs' 10 = Z_to_bv 64 cm /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (s - 36)
      /\ getr regs' 8 = Z_to_bv 64 cm /\ getr regs' 9 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s cm pixd Hs Hs64 Hcm Hcm64 H2 H8 H10. eexists. split.
    - stepb_ft F_19ce8 D_19ce8 ltac:(condZ).
      sn F_19cec D_19cec. zv F_19cf0 D_19cf0 (Z_to_bv 64 (s - 36)). sn F_19cf4 D_19cf4. sn F_19cf8 D_19cf8. sn F_19cfc D_19cfc.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcm_B : forall regs m (s cm : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 36)) 4 = Some (Z_to_le_bytes 4 1) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 cm ->
    exists regs',
      msteps SEGS (mkst regs (0x19d00 : word) m rom) (mkst regs' (0x1d61c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x19d10 /\ getr regs' 10 = Z_to_bv 64 cm
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s cm Hs Hs64 Rv H2 H8. eexists. split.
    - stepLD F_19d00 D_19d00 (Z_to_le_bytes 4 1) (Z_to_bv 64 1) ltac:(addr_norm; exact Rv) ltac:(apply lez4; lia).
      stepb_ft F_19d04 D_19d04 ltac:(condZ).
      sn F_19d08 D_19d08. sn F_19d0c D_19d0c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcm_C : forall regs m (s cd pixd : Z) (vd : pixv),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= cd)%Z -> (cd < 2 ^ 64)%Z -> PIXat m pixd vd -> p_cmap vd = 0%Z ->
    (pixd + 64 <= s - 48 \/ s <= pixd)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true -> store_ok SEGS m (Z_to_bv 64 pixd) 64 = true ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 cd -> getr regs 9 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x19d10 : word) m rom)
                  (mkst regs' (0x1d734 : word)
                     (wbytes (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                             (Z_to_bv 64 (pixd + 48)) (word_to_le_bytes 8 (Z_to_bv 64 cd))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x19d48
      /\ getr regs' 10 = Z_to_bv 64 cd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (s - 32)
      /\ getr regs' 9 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s cd pixd vd Hs Hs64 Hcd Hcd64 PXd Ecm DJ SOK SOKp H2 H10 H9.
    pose proof PXd as (Hd0 & Hd64 & WFd & _).
    pose proof (PIX_rd_cmap SEGS m pixd vd PXd) as Ccd. rewrite Ecm in Ccd.
    eexists. split.
    - stepb_ft F_19d10 D_19d10 ltac:(condZ).
      sn F_19d14 D_19d14.
      stepLD F_19d18 D_19d18 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Ccd) ltac:(apply lez8; lia).
      stepST F_19d1c D_19d1c (Z_to_bv 64 (s - 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_19d20 D_19d20 ltac:(condZ).
      stepST F_19d38 D_19d38 (Z_to_bv 64 (pixd + 48)) (Z_to_bv 64 cd) ltac:(sok_in SOKp).
      zv F_19d3c D_19d3c (Z_to_bv 64 (s - 32)). sn F_19d40 D_19d40. sn F_19d44 D_19d44.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcm_D : forall regs m (s : Z) (ret s0v s1v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cells3 m s ret s0v s1v ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 4 = Some (Z_to_le_bytes 4 1) ->
    getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs',
      msteps SEGS (mkst regs (0x19d48 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v Hs Hs64 Hret CE Rv H2.
    assert (RUN1 : exists r1, msteps SEGS (mkst regs (0x19d48 : word) m rom) (mkst r1 (0x19e6c : word) m rom)
                              /\ getr r1 2 = Z_to_bv 64 (s - 48) /\ getr r1 10 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [10]%list) regs r1).
    { eexists. split.
      - stepLD F_19d48 D_19d48 (Z_to_le_bytes 4 1) (Z_to_bv 64 1) ltac:(addr_norm; exact Rv) ltac:(apply lez4; lia).
        stepb_tk F_19d4c D_19d4c ltac:(condZ). sn F_19d7c D_19d7c. sn F_19d80 D_19d80. apply mst_refl.
      - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
    destruct RUN1 as (r1 & RUN1 & Q2 & Q10 & AG1).
    destruct (pcm_RET r1 m s ret s0v s1v (Z_to_bv 64 0) Hs Hs64 Hret CE Q2 Q10) as (r2 & RUN2 & P2 & P1 & P10 & P8 & P9 & AG2).
    exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] |].
    repeat split; try assumption. eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  Qed.

  (* [comment removed for export] *)
  Lemma pcm_C0 : forall regs m (s : Z),
    rdn SEGS m (Z_to_bv 64 0x44e98) 8 = Some (Z_to_le_bytes 8 0x45f08) -> rdn SEGS m (Z_to_bv 64 0x45f08) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x19d10 : word) m rom) (mkst regs' (0x17df4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x19e64
      /\ getr regs' 10 = Z_to_bv 64 0x10773 /\ getr regs' 11 = Z_to_bv 64 0x108e0 /\ getr regs' 12 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s Rg Rs H2 H10. eexists. split.
    - stepb_tk F_19d10 D_19d10 ltac:(condZ).
      sn F_19e38 D_19e38.
      stepLD F_19e3c D_19e3c (Z_to_le_bytes 8 0x45f08) (Z_to_bv 64 0x45f08) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_19e40 D_19e40 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_19e44 D_19e44. stepb_ft F_19e48 D_19e48 ltac:(condZ).
      sn F_19e4c D_19e4c. sn F_19e50 D_19e50. sn F_19e54 D_19e54. sn F_19e58 D_19e58.
      sn F_19e5c D_19e5c. sn F_19e60 D_19e60.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcm_E : forall regs m (s : Z) (ret s0v s1v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cells3 m s ret s0v s1v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (mkst regs (0x19e64 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v Hs Hs64 Hret (R8 & R16 & R24) H2 H10. eexists. split.
    - sn F_19e64 D_19e64.
      stepLD8 F_19e6c D_19e6c ret. stepLD8 F_19e70 D_19e70 s0v. stepLD8 F_19e74 D_19e74 s1v.
      zv F_19e78 D_19e78 (Z_to_bv 64 s). stepret F_19e7c D_19e7c ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

Lemma str_cmapd_not_made' : str16 0x10773 14. Proof. str16_tac. Qed.
Lemma str_pixCopyColormap : str16 0x108e0 15. Proof. str16_tac. Qed.

(* [comment removed for export] *)
Lemma cmap_ok_copy : forall cv ad, cmap_ok cv -> (1 <= ad)%Z -> cmap_ok (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0).
Proof. intros cv ad (Hd & Hna & Hn & Harr) Had. unfold cmap_ok. cbn [c_d c_nalloc c_n c_arr]. repeat split; try assumption; lia. Qed.

Theorem pixCopyColormap_szT_W : forall C Ar A m md regs (s pixd pixs : Z) (vd vs : pixv) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 ->
  getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs ->
  PIXat m pixd vd -> PIXat m pixs vs -> p_d vd = p_d vs -> p_cmap vd = 0%Z -> pixd <> pixs ->
  live A (Z_to_bv 64 pixd) = Some 64%Z -> live Ar (Z_to_bv 64 pixd) = None -> live (c_A0 C) (Z_to_bv 64 pixd) = None ->
  live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (p_cmap vs = 0%Z \/ (CMAPat m (p_cmap vs) cv /\ cmap_ok cv /\ live A (Z_to_bv 64 (p_cmap vs)) = Some 24%Z /\
                        live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_cmapcopy <= kR)%Z -> (RB_cmapT (p_cmap vs) <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C Ar s m m' ->
     ( ((forall q, live A' q = live A q) /\ PIXat m' pixd vd)
       \/ (exists cd ad : Z, cmap_copy C A A' m' cd ad cv /\ PIXat m' pixd (set_cmap vd cd)) ) ->
     aroom A' vm' (kR - RK_cmapcopy) (bR - RB_cmapT (p_cmap vs)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x19c84 : word) m al_rom) md) S.
Proof.
  intros C Ar A m md regs s pixd pixs vd vs cv ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 PXd PXs Ed Ecm NEds Lpd Lpd0 Lpd00 Lps HCM kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PXd as (Hd0 & Hd64 & WFd & _). pose proof PXs as (Hs0 & Hs64' & WFs & _). pose proof (wf_cmap _ WFs) as Rcm.
  destruct (blk_range C A m md (Z_to_bv 64 pixd) 64 CK HW Lpd ltac:(lia)) as [Gpd TOPpd]. rewrite u_Z2bv in Gpd, TOPpd by lia.
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lpd) as (_ & ALpd & _). rewrite u_Z2bv in ALpd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  (* [comment removed for export] *)
  destruct (pcm_A al_rom regs m s pixd pixs vd vs ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) NEds ALpd ALps PXd PXs Ed Ecm ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR4c m s ret regs) md /\ POSTM C A s m (FR4c m s ret regs)) by (unfold FR4c; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR4c m s ret regs) in *.
  pose proof (cells3_FR4c m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 48 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold FR4c. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PXd1 : PIXat M1 pixd vd) by (apply (PIXat_frame m M1 _ _ PXd); intros x Hx; apply OUT1; lia).
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x56270) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)].
  - (* [comment removed for export] *)
    rewrite CM0 in Q8.
    destruct (pcm_A0 al_rom r1 M1 s ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) Hret CE1 Q2 Q8) as (r2 & RUN2 & P2 & P1 & P10 & P8 & P9 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    rewrite <- (with_vmmaps_same md). apply (HK A M1 (m_vmmaps md) r2).
    + rewrite with_vmmaps_same. exact HW1.
    + apply cs_kept_intro; csr; try reflexivity. all: rewrite ?P8, ?P9, ?Q9; reflexivity.
    + apply (POSTM_sub C Ar A); [exact SUB | exact PM1].
    + left. split; [intros q; reflexivity | exact PXd1].
    + pose proof (RB_cmapT_le (p_cmap vs)). apply (aroom_mono A (m_vmmaps md) kR bR _ _ Hrm); room_consts; lia.
  - (* [comment removed for export] *)
    pose proof CM as (Hc0 & Hc64 & CWF & _). set (cm := p_cmap vs) in *.
    destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
    assert (Ecm' : RB_cmapT cm = RB_cmapcopy) by (apply RB_cmapT_pos; lia). rewrite Ecm' in Hrb, HK.
    assert (CM1 : CMAPat M1 cm cv) by (apply (CMAPat_frame m M1 _ _ CM); intros x Hx; apply OUT1; lia).
    destruct (pcm_A1 al_rom r1 M1 s cm pixd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Q2 Q8 Q10) as (r2 & RUN2 & P2 & P1 & P10 & P11 & P12 & P8 & P9 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    apply (pixcmapIsValid_null_W C A M1 md r2 (s - 48) cm (s - 36) cv (Z_to_bv 64 0x19d00) S CK HW1 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply sp_slot_al4'; [exact Hs16 | reflexivity]) P1 ltac:(red; apply bv_eq; reflexivity) P10 P11 P12 CM1 CMOK Lcm).
    intros m2 r3 HW2 CS2 PV2 A10.
    replace (Z_to_bv 64 0x19d00) with (0x19d00 : word) by (apply bv_eq; reflexivity).
    pose proof PV2 as [F2 L2].
    assert (PM2 : POSTM C A s m m2).
    { eapply POSTM_trans; [exact PM1|].
      unshelve (eapply (POSTM_absorb C A A M1 _ m2 s (s - 48) _ _ CK HW1 (sub_live_refl A) ltac:(lia) _ _ Hhi PV2)); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (Rv2 : rdn SEGS m2 (Z_to_bv 64 (s - 36)) 4 = Some (Z_to_le_bytes 4 1)).
    { rewrite (FRM_rdn16 C (s - 48) _ m2 (s - 36) 4 CK F2) by (cbn; lia). rewrite <- (w2l_Z4 1) by lia. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
    assert (CE2 : cells3 m2 s ret (getr regs 8) (getr regs 9)).
    { apply (cells3_frm C (s - 48) (wbytes M1 (Z_to_bv 64 (s - 36)) (word_to_le_bytes 4 (Z_to_bv 64 1))) m2 s _ _ _ CK F2 ltac:(lia) ltac:(lia) ltac:(lia)).
      eapply (cells3_out M1 _ (s - 36) (s - 32)); [intros x Hx; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia | lia | lia | exact CE1]. }
    assert (HW1v : W C A (wbytes M1 (Z_to_bv 64 (s - 36)) (word_to_le_bytes 4 (Z_to_bv 64 1))) md).
    { apply (W_store_win C A M1 md _ _ CK HW1); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (EQ2 : forall (p k : Z) (x : word), live A (Z_to_bv 64 p) = Some k -> (0 <= p)%Z -> (p + k <= alloc_top (c_vm C))%Z -> (p <= u x < p + k)%Z -> m2 x = M1 x).
    { intros p k x L G0 TP Hx. rewrite (LIVK_byte C A _ m2 md p k x CK HW1v L2 L G0 TP Hx). apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (PXd2 : PIXat m2 pixd vd) by (apply (PIXat_frame M1); [exact PXd1 | intros x Hx; exact (EQ2 pixd 64%Z x Lpd ltac:(lia) TOPpd Hx)]).
    assert (CM2 : CMAPat m2 cm cv) by (apply (CMAPat_frame M1); [exact CM1 | intros x Hx; exact (EQ2 cm 24%Z x Lcm ltac:(lia) TOPcm Hx)]).
    assert (Y2 : getr r3 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (Y8 : getr r3 8 = Z_to_bv 64 cm) by (csr; reflexivity).
    (* [comment removed for export] *)
    destruct (pcm_B al_rom r3 m2 s cm ltac:(lia) ltac:(lia) Rv2 Y2 Y8) as (r4 & RUN4 & X2 & X1 & X10 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN4 |].
    assert (X4 : getr r4 4 = Z_to_bv 64 0x56270) by (rewrite (AG4 4) by (cbv; intuition discriminate); csr; reflexivity).
    apply (pixcmapCopy_W C A m2 md r4 (s - 48) cm cv (Z_to_bv 64 0x19d10) S CK HW2 X2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold LSF; lia) ltac:(lia) X1 ltac:(red; apply bv_eq; reflexivity) X4 X10 CM2 CMOK Lcm Larr kR bR Hrm Hrk Hrb).
    intros A1 m3 vm1 r5 HWa CSa PMa OUTa Hrm1.
    replace (Z_to_bv 64 0x19d10) with (0x19d10 : word) by (apply bv_eq; reflexivity).
    pose proof (cells3_frm C (s - 48) m2 m3 s _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE2) as CE3.
    assert (PMa' : POSTM C A s m m3) by (eapply POSTM_trans; [exact PM2 | eapply POSTM_mono; [|exact PMa]; lia]).
    assert (PXd3 : PIXat m3 pixd vd) by (apply (PIXat_frame m2); [exact PXd2 | intros x Hx; exact (LIVK_byte C A m2 m3 md pixd 64 x CK HW2 (proj2 PMa) Lpd ltac:(lia) TOPpd Hx)]).
    assert (E2a : getr r5 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (E9a : getr r5 9 = Z_to_bv 64 pixd) by (csr; reflexivity).
    destruct OUTa as [[Hres0 LIVEQ] | (cd & ad & Hres & CC)].
    + (* [comment removed for export] *)
      destruct (pcm_C0 al_rom r5 m3 s (W_sev_got C A1 m3 _ HWa) (W_sev C A1 m3 _ HWa) E2a Hres0) as (r6 & RUN6 & V2 & V1 & V10 & V11 & V12 & AG6).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN6 |].
      apply (returnErrorInt_W C A1 m3 _ r6 (s - 48) 0x10773 0x108e0 14 15 (Z_to_bv 64 0x19e64) (Z_to_bv 64 1) S CK HWa V2
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity)
               V10 V11 V12 str_cmapd_not_made' str_pixCopyColormap).
      intros m4 r7 HW4 OUT4 GR4 CS4 B10. unfold LSF in OUT4.
      replace (Z_to_bv 64 0x19e64) with (0x19e64 : word) by (apply bv_eq; reflexivity).
      pose proof (cells3_out m3 m4 _ _ s _ _ _ OUT4 ltac:(lia) ltac:(lia) ltac:(lia) CE3) as CE4.
      destruct (pcm_E al_rom r7 m4 s ret _ _ ltac:(lia) ltac:(lia) Hret CE4 ltac:(csr; reflexivity) B10) as (r8 & RUN8 & Z2 & Z1 & Z10 & Z8 & Z9 & AG8).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN8 |].
      apply (HK A1 m4 vm1 r8).
      * exact HW4.
      * apply cs_kept_intro; csr; try reflexivity. all: rewrite ?Z8, ?Z9, ?Q9; reflexivity.
      * apply (POSTM_sub C Ar A); [exact SUB|]. eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ|].
        eapply (POSTM_range C A1 m3 _ m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
      * left. split; [exact LIVEQ|]. apply (PIXat_frame m3); [exact PXd3|]. intros x Hx. apply OUT4. lia.
      * exact Hrm1.
    + (* [comment removed for export] *)
      pose proof CC as (CMOKc & Gcd & TOPcd & ALcd & Gad & TOPad & ALad & NEcdad & L0 & LA0 & L00 & LA00 & L1 & K1 & LEQ & CD3).
      assert (NEpdcd : Z_to_bv 64 pixd <> Z_to_bv 64 cd) by (intros E; rewrite E in Lpd; rewrite Lpd in L0; discriminate).
      assert (NEpdad : Z_to_bv 64 pixd <> Z_to_bv 64 ad) by (intros E; rewrite E in Lpd; rewrite Lpd in LA0; discriminate).
      assert (Lpd1 : live A1 (Z_to_bv 64 pixd) = Some 64%Z) by (rewrite (LEQ _ NEpdcd NEpdad); exact Lpd).
      assert (SUBa : sub_live A A1) by (eapply sub_live_new2; [exact L0 | exact LA0 | exact L1 | exact K1 | exact LEQ]).
      assert (SUBr : sub_live Ar A1) by (eapply sub_live_trans; [exact SUB | exact SUBa]).
      pose proof (blk_apart C A1 m3 _ _ _ _ _ CK HWa Lpd1 L1 NEpdcd ltac:(lia) ltac:(lia)) as APpdcd. rewrite !u_Z2bv in APpdcd by lia. apply box_i in APpdcd.
      destruct (pcm_C al_rom r5 m3 s cd pixd vd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PXd3 Ecm ltac:(lia)
                  (W_sok_win C A1 m3 _ (s - 48) 48 CK HWa ltac:(lia) ltac:(cbn; lia)) (blk_sok C A1 m3 _ pixd 64 CK HWa Lpd1 ltac:(lia) ltac:(lia) ltac:(lia)) E2a Hres E9a)
        as (r6 & RUN6 & V2 & V1 & V10 & V11 & V12 & V9 & AG6).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN6 |].
      set (M5 := wbytes m3 (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
      set (M6 := wbytes M5 (Z_to_bv 64 (pixd + 48)) (word_to_le_bytes 8 (Z_to_bv 64 cd))).
      assert (WP5 : W C A1 M5 (with_vmmaps vm1 md) /\ POSTM C Ar s m M5).
      { subst M5. apply (WP_win C A1 Ar m m3 _ _ _ s CK); [| exact SUBr | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia].
        split; [exact HWa | apply (POSTM_sub C Ar A); [exact SUB | exact PMa']]. }
      assert (WP6 : W C A1 M6 (with_vmmaps vm1 md) /\ POSTM C Ar s m M6).
      { subst M6. apply (WP_blk C Ar A1 m M5 _ (Z_to_bv 64 pixd) _ 64); [exact CK | exact WP5 | exact Lpd1 | exact Lpd0 | exact Lpd00 | exact SUBr | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
      destruct WP6 as [HW6 PM6].
      assert (OUT5 : forall x : word, ~ (s - 32 <= u x < s - 24)%Z -> M5 x = m3 x).
      { intros x Hx. subst M5. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
      assert (OUT6 : forall x : word, ~ (pixd + 48 <= u x < pixd + 56)%Z -> M6 x = M5 x).
      { intros x Hx. subst M6. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
      assert (PXd6 : PIXat M6 pixd (set_cmap vd cd)).
      { subst M6. apply PIX_wr_cmap; [|lia]. apply (PIXat_frame m3); [exact PXd3|]. intros x Hx. apply OUT5. lia. }
      set (cv' := CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0) in *.
      assert (CD6 : CMAPat M6 cd cv').
      { pose proof (box_e _ APpdcd) as U1. apply (CMAPat_frame m3); [exact CD3|]. intros x Hx. rewrite OUT6 by lia. apply OUT5. lia. }
      assert (CE6 : cells3 M6 s ret (getr regs 8) (getr regs 9)).
      { eapply (cells3_out M5 _ (pixd + 48) (pixd + 56)); [exact OUT6 | lia | lia | lia |].
        eapply (cells3_out m3 _ (s - 32) (s - 24)); [exact OUT5 | lia | lia | lia | exact CE3]. }
      pose proof (cmap_ok_copy cv ad CMOK ltac:(lia)) as CMOK'.
      apply (pixcmapIsValid_null_W C A1 M6 _ r6 (s - 48) cd (s - 32) cv' (Z_to_bv 64 0x19d48) S CK HW6 V2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply sp_slot_al4'; [exact Hs16 | reflexivity]) V1 ltac:(red; apply bv_eq; reflexivity) V10 V11 V12 CD6 CMOK' L1).
      intros m7 r7 HW7 CS7 PV7 B10.
      replace (Z_to_bv 64 0x19d48) with (0x19d48 : word) by (apply bv_eq; reflexivity).
      pose proof PV7 as [F7 L7].
      assert (PM7 : POSTM C Ar s m m7).
      { eapply POSTM_trans; [exact PM6|].
        unshelve (eapply (POSTM_absorb C Ar A1 M6 _ m7 s (s - 48) _ _ CK HW6 SUBr ltac:(lia) _ _ Hhi PV7)); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
      assert (Rv7 : rdn SEGS m7 (Z_to_bv 64 (s - 32)) 4 = Some (Z_to_le_bytes 4 1)).
      { rewrite (FRM_rdn16 C (s - 48) _ m7 (s - 32) 4 CK F7) by (cbn; lia). rewrite <- (w2l_Z4 1) by lia. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
      assert (CE7 : cells3 m7 s ret (getr regs 8) (getr regs 9)).
      { apply (cells3_frm C (s - 48) (wbytes M6 (Z_to_bv 64 (s - 32)) (word_to_le_bytes 4 (Z_to_bv 64 1))) m7 s _ _ _ CK F7 ltac:(lia) ltac:(lia) ltac:(lia)).
        eapply (cells3_out M6 _ (s - 32) (s - 28)); [intros x Hx; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia | lia | lia | exact CE6]. }
      assert (HW6v : W C A1 (wbytes M6 (Z_to_bv 64 (s - 32)) (word_to_le_bytes 4 (Z_to_bv 64 1))) (with_vmmaps vm1 md)).
      { apply (W_store_win C A1 M6 _ _ _ CK HW6); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
      assert (EQ7 : forall (p k : Z) (x : word), live A1 (Z_to_bv 64 p) = Some k -> (0 <= p)%Z -> (p + k <= alloc_top (c_vm C))%Z -> (p <= u x < p + k)%Z -> m7 x = M6 x).
      { intros p k x L G0 TP Hx. rewrite (LIVK_byte C A1 _ m7 _ p k x CK HW6v L7 L G0 TP Hx). apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
      assert (Y2' : getr r7 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
      destruct (pcm_D al_rom r7 m7 s ret _ _ ltac:(lia) ltac:(lia) Hret CE7 Rv7 Y2') as (r8 & RUN8 & Z2 & Z1 & Z10 & Z8 & Z9 & AG8).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN8 |].
      apply (HK A1 m7 vm1 r8).
      * exact HW7.
      * apply cs_kept_intro; csr; try reflexivity. all: rewrite ?Z8, ?Z9, ?Q9; reflexivity.
      * exact PM7.
      * right. exists cd, ad. split.
        -- unfold cmap_copy. do 15 (split; [assumption|]). apply (CMAPat_frame M6); [exact CD6|]. intros x Hx. exact (EQ7 cd 24%Z x L1 ltac:(lia) ltac:(lia) Hx).
        -- apply (PIXat_frame M6); [exact PXd6|]. intros x Hx. exact (EQ7 pixd 64%Z x Lpd1 ltac:(lia) TOPpd Hx).
      * exact Hrm1.
Qed.

End PixCopyA.
