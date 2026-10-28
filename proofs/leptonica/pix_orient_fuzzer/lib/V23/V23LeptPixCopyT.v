(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptUb.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptErr.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptPixCreate V23LeptPixCreateT2 V23LeptPadBitsW V23LeptCmapValid V23LeptCmap2 V23LeptPixCopyA V23LeptPixCopyAT.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MemcpyBase V23Memcpy V23Memset.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23_code_frontA_strrep V23_code_6e000_6f000.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixHdr O23LeptCmapValid O23LeptCmap2 O23LeptPixCopyT.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom14 LeptRoomBL.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].




Section PixCopy.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

  (* [comment removed for export] *)
  Definition FR4 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes m
       (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
       (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
       (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
       (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)).

  Definition cells4 (m : word -> option byte) (s : Z) (ret s0v s1v s2v : word) : Prop :=
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v).

  Lemma cells4_FR4 : forall m s ret regs, (32 <= s)%Z -> (s < 2 ^ 64)%Z -> cells4 (FR4 m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18).
  Proof. intros m s ret regs Hs Hs64. unfold cells4, FR4. repeat split; rdn_solve. Qed.

  Lemma cells4_frm : forall C s' m m' s ret s0v s1v s2v, Cok C -> FRM C s' m m' ->
    (s' <= s - 32)%Z -> (c_top C - LSTK <= s')%Z -> (s < 2 ^ 64)%Z ->
    cells4 m s ret s0v s1v s2v -> cells4 m' s ret s0v s1v s2v.
  Proof.
    intros C s' m m' s ret s0v s1v s2v CK F Hs' Hlo Hs64 (R1 & R2 & R3 & R4). unfold cells4.
    rewrite !(FRM_rdn16 C s' m m' _ 8 CK F) by (cbn; lia). repeat split; assumption.
  Qed.

  Lemma cells4_out : forall m m' (lo hi s : Z) ret s0v s1v s2v,
    (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) -> (hi <= s - 32 \/ s <= lo)%Z -> (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
    cells4 m s ret s0v s1v s2v -> cells4 m' s ret s0v s1v s2v.
  Proof.
    intros m m' lo hi s ret s0v s1v s2v OUT Hhi Hs Hs64 (R1 & R2 & R3 & R4). unfold cells4.
    repeat split; (eapply (rdn_after m m' lo hi); [exact OUT | lia | cbn; lia | cbn; lia | assumption]).
  Qed.

Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma ptn_A : forall regs m (s pixs : Z) (vs : pixv) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (pixs mod 16 = 0)%Z -> PIXat m pixs vs -> (pixs + 64 <= s - 32 \/ s <= pixs)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x6e148 : word) m rom) (mkst regs' (0x6dae0 : word) (FR4 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x6e17c
      /\ getr regs' 10 = Z_to_bv 64 (p_w vs) /\ getr regs' 11 = Z_to_bv 64 (p_h vs) /\ getr regs' 12 = Z_to_bv 64 (p_d vs)
      /\ getr regs' 9 = Z_to_bv 64 pixs /\ getr regs' 8 = getr regs 8
      /\ regs_agree (fun r => In r [1; 2; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pixs vs ret Hs Hs64 Hp ALp PX DJ SOK H2 H1 H10. pose proof PX as (Hp0 & Hp64 & WF & _).
    pose proof (wf_w _ WF) as Rw. pose proof (wf_h _ WF) as Rh. pose proof (wf_d _ WF) as Rd.
    assert (ALp8 : (pixs mod 8 = 0)%Z) by (apply al16_mod8; exact ALp).
    assert (PX1 : PIXat (FR4 m s ret regs) pixs vs).
    { unfold FR4. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
    pose proof (PIX_rd_w SEGS _ _ _ PX1) as Cw. pose proof (PIX_rd_h SEGS _ _ _ PX1) as Ch. pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd.
    unfold FR4 in *. eexists. split.
    - zv F_6e148 D_6e148 (Z_to_bv 64 (s - 32)).
      stepST F_6e14c D_6e14c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_6e150 D_6e150 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_6e154 D_6e154 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_6e158 D_6e158 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepb_ft F_6e15c D_6e15c ltac:(condZ).
      sn F_6e160 D_6e160.
      guard8 F_6e164 D_6e164 ALp8. stepb_ft F_6e168 D_6e168 ltac:(condZ).
      stepLD F_6e16c D_6e16c (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Cw) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w vs)) by lia.
      stepLD F_6e170 D_6e170 (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs)) ltac:(addr_norm; exact Ch) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      stepLD F_6e174 D_6e174 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; exact Cd) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      sn F_6e178 D_6e178.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ptn_F : forall regs m (s : Z) (ret s0v s1v s2v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x6e17c : word) m rom) (mkst regs' (0x63740 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x126da /\ getr regs' 11 = Z_to_bv 64 0x1b9b0
      /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v Hs Hs64 Rg Rs R8 R16 R24 R32 H2 H10. eexists. split.
    - stepb_tk F_6e17c D_6e17c ltac:(condZ).
      sn F_6e1c8 D_6e1c8.
      stepLD F_6e1cc D_6e1cc (Z_to_le_bytes 8 0x127c60) (Z_to_bv 64 0x127c60) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_6e1d0 D_6e1d0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_6e1d4 D_6e1d4. stepb_ft F_6e1d8 D_6e1d8 ltac:(condZ).
      sn F_6e1dc D_6e1dc. sn F_6e1e0 D_6e1e0. sn F_6e1e4 D_6e1e4. sn F_6e1e8 D_6e1e8.
      sn F_6e1ec D_6e1ec.
      stepLD8 F_6e1f0 D_6e1f0 ret. stepLD8 F_6e1f4 D_6e1f4 s0v. stepLD8 F_6e1f8 D_6e1f8 s1v. stepLD8 F_6e1fc D_6e1fc s2v.
      zv F_6e200 D_6e200 (Z_to_bv 64 s). sn F_6e204 D_6e204.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ptn_B : forall regs m (s pixs pixd : Z) (vs vd : pixv),
    (1 <= pixs)%Z -> (1 <= pixd)%Z -> pixs <> pixd -> (pixd mod 16 = 0)%Z -> PIXat m pixs vs -> PIXat m pixd vd ->
    (1 <= p_spp vs)%Z -> p_spp vd = p_spp vs -> p_xres vs = 0%Z -> p_yres vs = 0%Z ->
    (pixs + 64 <= pixd \/ pixd + 64 <= pixs)%Z -> store_ok SEGS m (Z_to_bv 64 pixd) 64 = true ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x6e17c : word) m rom)
                  (mkst regs' (0x6e4cc : word)
                     (wbytes (wbytes m (Z_to_bv 64 (pixd + 12)) (word_to_le_bytes 4 (Z_to_bv 64 (p_spp vs))))
                             (Z_to_bv 64 (pixd + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x6e264
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs /\ getr regs' 8 = Z_to_bv 64 pixd /\ getr regs' 9 = Z_to_bv 64 pixs
      /\ getr regs' 18 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 18]%list) regs regs'.
  Proof.
    intros regs m s pixs pixd vs vd Hps Hpd NE ALd PXs PXd Hspp Espp Hx Hy DJ SOKd H2 H10 H9.
    pose proof PXs as (Hs0 & Hs64 & WFs & _). pose proof PXd as (Hd0 & Hd64 & WFd & _). pose proof (wf_spp _ WFs) as Rspp.
    assert (ALd8 : (pixd mod 8 = 0)%Z) by (apply al16_mod8; exact ALd).
    pose proof (PIX_rd_spp SEGS _ _ _ PXs) as Cspp.
    assert (Cres : rdn SEGS (wbytes m (Z_to_bv 64 (pixd + 12)) (word_to_le_bytes 4 (Z_to_bv 64 (p_spp vs)))) (Z_to_bv 64 (pixs + 24)) 8 = Some (Z_to_le_bytes 8 0)).
    { rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact (O23LeptPixCopyT.PIX_rd_res0 SEGS m pixs vs PXs Hx Hy). }
    eexists. split.
    - stepb_ft F_6e17c D_6e17c ltac:(condZ).
      sn F_6e180 D_6e180.
      stepb_ft F_6e184 D_6e184 ltac:(condZ).
      stepLD F_6e188 D_6e188 (Z_to_le_bytes 4 (p_spp vs)) (Z_to_bv 64 (p_spp vs)) ltac:(addr_norm; exact Cspp) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_spp vs)) by lia.
      guard8 F_6e18c D_6e18c ALd8.
      stepb_ft F_6e190 D_6e190 ltac:(condZ).
      stepb_ft F_6e194 D_6e194 ltac:(condZ).
      stepST F_6e198 D_6e198 (Z_to_bv 64 (pixd + 12)) (Z_to_bv 64 (p_spp vs)) ltac:(sok_in SOKd).
      sn F_6e19c D_6e19c.
      stepb_ft F_6e24c D_6e24c ltac:(condZ).
      stepLD F_6e250 D_6e250 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Cres) ltac:(apply lez8; lia).
      stepST F_6e254 D_6e254 (Z_to_bv 64 (pixd + 24)) (Z_to_bv 64 0) ltac:(sok_in SOKd).
      sn F_6e258 D_6e258. sn F_6e25c D_6e25c. sn F_6e260 D_6e260.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ptn_C : forall regs m (s pixs pixd : Z) (vs vd : pixv),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (1 <= pixd)%Z -> (pixd mod 16 = 0)%Z -> PIXat m pixs vs -> PIXat m pixd vd ->
    p_text vs = 0%Z -> p_text vd = 0%Z -> p_fmt vs = 0%Z ->
    (pixs + 64 <= pixd \/ pixd + 64 <= pixs)%Z -> (pixd + 64 <= s - 64 \/ s <= pixd)%Z -> (pixs + 64 <= s - 64 \/ s <= pixs)%Z ->
    store_ok SEGS m (Z_to_bv 64 pixd) 64 = true -> store_ok SEGS m (Z_to_bv 64 (s - 64)) 32 = true ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x6e264 : word) m rom)
                  (mkst regs' (0x70a54 : word)
                     (wbytes (wbytes (wbytes (wbytes (wbytes m
                        (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x6e270)))
                        (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 pixd)))
                        (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 pixs)))
                        (Z_to_bv 64 (pixd + 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                        (Z_to_bv 64 (pixd + 32)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x6e284
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 8 = Z_to_bv 64 pixd /\ getr regs' 9 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s pixs pixd vs vd Hs Hs64 Hps Hpd ALd PXs PXd Hts Htd Hfs DJ DJd DJs SOKd SOK H2 H8 H9.
    pose proof PXs as (Hs0 & Hs64' & WFs & _). pose proof PXd as (Hd0 & Hd64 & WFd & _).
    assert (ALt : ((pixd + 40) mod 8 = 0)%Z) by (apply al16_plus_mod8; [exact ALd | reflexivity]).
    pose proof (PIX_rd_text SEGS _ _ _ PXs) as Cts. rewrite Hts in Cts. pose proof (PIX_rd_text SEGS _ _ _ PXd) as Ctd. rewrite Htd in Ctd.
    pose proof (PIX_rd_fmt SEGS _ _ _ PXs) as Cfs. rewrite Hfs in Cfs.
    eexists. split.
    - stepLD F_6e264 D_6e264 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Cts) ltac:(apply lez8; lia).
      zv F_6e268 D_6e268 (Z_to_bv 64 (pixd + 40)).
      sn F_6e26c D_6e26c.
      zv F_63db4 D_63db4 (Z_to_bv 64 (s - 64)).
      stepST F_63db8 D_63db8 (Z_to_bv 64 (s - 40)) (Z_to_bv 64 0x6e270) ltac:(sok_in SOK).
      stepST F_63dbc D_63dbc (Z_to_bv 64 (s - 48)) (Z_to_bv 64 pixd) ltac:(sok_in SOK).
      stepST F_63dc0 D_63dc0 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 pixs) ltac:(sok_in SOK).
      stepb_ft F_63dc4 D_63dc4 ltac:(condZ).
      sn F_63dc8 D_63dc8.
      guard8 F_63dcc D_63dcc ALt. stepb_ft F_63dd0 D_63dd0 ltac:(condZ).
      sn F_63dd4 D_63dd4.
      stepLD F_63dd8 D_63dd8 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; rewrite ?Z.add_0_r; repeat rdn_peel1; exact Ctd) ltac:(apply lez8; lia).
      stepb_tk F_63ddc D_63ddc ltac:(condZ).
      stepb_tk F_63de4 D_63de4 ltac:(condZ).
      sn F_63e34 D_63e34. sn F_63e38 D_63e38.
      stepST F_63e3c D_63e3c (Z_to_bv 64 (pixd + 40)) (Z_to_bv 64 0) ltac:(sok_in SOKd).
      sn F_63e40 D_63e40.
      stepLD8 F_63e48 D_63e48 (Z_to_bv 64 0x6e270). stepLD8 F_63e4c D_63e4c (Z_to_bv 64 pixd). stepLD8 F_63e50 D_63e50 (Z_to_bv 64 pixs).
      zv F_63e54 D_63e54 (Z_to_bv 64 (s - 32)).
      stepret F_63e58 D_63e58 (0x6e270 : word) ltac:(bveq).
      stepLD F_6e270 D_6e270 (Z_to_le_bytes 4 0) (Z_to_bv 64 0) ltac:(addr_norm; repeat rdn_peel1; exact Cfs) ltac:(apply lez4; lia).
      stepST F_6e274 D_6e274 (Z_to_bv 64 (pixd + 32)) (Z_to_bv 64 0) ltac:(sok_in SOKd).
      sn F_6e278 D_6e278. sn F_6e27c D_6e27c. sn F_6e280 D_6e280.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ptn_D : forall regs m (s pixd : Z) (ret s0v s1v s2v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x6e284 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18]%list) regs regs'.
  Proof.
    intros regs m s pixd ret s0v s1v s2v Hs Hs64 Hret R8 R16 R24 R32 H2 H8. eexists. split.
    - sn F_6e284 D_6e284.
      stepLD8 F_6e288 D_6e288 ret. stepLD8 F_6e28c D_6e28c s0v. stepLD8 F_6e290 D_6e290 s1v. stepLD8 F_6e294 D_6e294 s2v.
      zv F_6e298 D_6e298 (Z_to_bv 64 s). stepret F_6e29c D_6e29c ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcp_A : forall regs m (s pixs : Z) (vs : pixv) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (pixs mod 16 = 0)%Z -> PIXat m pixs vs -> (pixs + 64 <= s - 48 \/ s <= pixs)%Z ->
    (0 < 4 * (p_wpl vs * p_h vs) < 2 ^ 31)%Z -> (0 <= p_wpl vs * p_h vs)%Z -> (p_wpl vs < 2 ^ 24)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x6eb5c : word) m rom) (mkst regs' (0x6e148 : word) (O23LeptCmap2.FR5 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x6ec44 /\ getr regs' 10 = Z_to_bv 64 pixs
      /\ getr regs' 9 = Z_to_bv 64 pixs /\ getr regs' 18 = Z_to_bv 64 (4 * (p_wpl vs * p_h vs)) /\ getr regs' 8 = Z_to_bv 64 0 /\ getr regs' 19 = getr regs 19
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18]%list) regs regs'.
  Proof.
    intros regs m s pixs vs ret Hs Hs64 Hp ALp PX DJ Hsz Hwh Hwpl SOK H2 H1 H10 H11. pose proof PX as (Hp0 & Hp64 & WF & _).
    pose proof (wf_h _ WF) as Rh. pose proof (wf_wpl _ WF) as Rwpl.
    assert (ALp8 : (pixs mod 8 = 0)%Z) by (apply al16_mod8; exact ALp).
    assert (PX1 : PIXat (O23LeptCmap2.FR5 m s ret regs) pixs vs).
    { unfold O23LeptCmap2.FR5. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
    pose proof (PIX_rd_h SEGS _ _ _ PX1) as Ch. pose proof (PIX_rd_wpl SEGS _ _ _ PX1) as Cwpl.
    assert (Hm4 : (0 <= 4 * p_wpl vs * p_h vs < 2 ^ 31)%Z) by nia.
    unfold O23LeptCmap2.FR5 in *. eexists. split.
    - zv F_6eb5c D_6eb5c (Z_to_bv 64 (s - 48)).
      stepST F_6eb60 D_6eb60 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_6eb64 D_6eb64 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_6eb68 D_6eb68 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_6eb6c D_6eb6c (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_6eb70 D_6eb70 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      sn F_6eb74 D_6eb74.
      stepb_ft F_6eb78 D_6eb78 ltac:(condZ).
      sn F_6eb7c D_6eb7c.
      stepb_ft F_6eb80 D_6eb80 ltac:(condZ).
      guard8 F_6eb84 D_6eb84 ALp8. stepb_ft F_6eb88 D_6eb88 ltac:(condZ).
      stepLD F_6eb8c D_6eb8c (Z_to_le_bytes 4 (p_wpl vs)) (Z_to_bv 64 (p_wpl vs)) ltac:(addr_norm; exact Cwpl) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_wpl vs)) by lia.
      sn F_6eb90 D_6eb90.
      zv F_6eb94 D_6eb94 (Z_to_bv 64 (p_wpl vs + 536870912)).
      sn F_6eb98 D_6eb98. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srliw_small by lia; f_equal; apply Z.div_small; lia).
      stepb_ft F_6eb9c D_6eb9c ltac:(condZ).
      stepLD F_6eba0 D_6eba0 (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs)) ltac:(addr_norm; exact Ch) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      sn F_6eba4 D_6eba4. fixv (Z_to_bv 64 (4 * p_wpl vs)) ltac:(rewrite v_slliw_2, sw32_small by lia; f_equal; lia).
      zv F_6eba8 D_6eba8 (Z_to_bv 64 (4 * (p_wpl vs * p_h vs))).
      sn F_6ebac D_6ebac. fixv (Z_to_bv 64 (4 * (p_wpl vs * p_h vs))) ltac:(rewrite zbv_mulw_small by lia; f_equal; lia).
      stepb_ft F_6ebb0 D_6ebb0 ltac:(condZ).
      stepb_tk F_6ebb4 D_6ebb4 ltac:(condZ).
      sn F_6ec3c D_6ec3c. sn F_6ec40 D_6ec40.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcp_F1 : forall regs m (s : Z),
    rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x6ec44 : word) m rom) (mkst regs' (0x63740 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x6ecd8
      /\ getr regs' 10 = Z_to_bv 64 0x126da /\ getr regs' 11 = Z_to_bv 64 0x192a9 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 0x127c60
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 19]%list) regs regs'.
  Proof.
    intros regs m s Rg Rs H2 H10. eexists. split.
    - stepb_tk F_6ec44 D_6ec44 ltac:(condZ).
      sn F_6ecac D_6ecac.
      stepLD F_6ecb0 D_6ecb0 (Z_to_le_bytes 8 0x127c60) (Z_to_bv 64 0x127c60) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_6ecb4 D_6ecb4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rs) ltac:(apply lez4; lia).
      sn F_6ecb8 D_6ecb8. stepb_ft F_6ecbc D_6ecbc ltac:(condZ).
      sn F_6ecc0 D_6ecc0. sn F_6ecc4 D_6ecc4. sn F_6ecc8 D_6ecc8. sn F_6eccc D_6eccc. sn F_6ecd0 D_6ecd0. sn F_6ecd4 D_6ecd4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcp_F2 : forall regs m (s : Z) (ret s0v s1v s2v s3v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) -> cells5 m s ret s0v s1v s2v s3v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 0x127c60 ->
    exists regs',
      msteps SEGS (mkst regs (0x6ecd8 : word) m rom) (mkst regs' (0x63740 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 10 = Z_to_bv 64 0x126da /\ getr regs' 11 = Z_to_bv 64 0x18bc4 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v s3v Hs Hs64 Rs (R8 & R16 & R24 & R32 & R40) H2 H10 H19. eexists. split.
    - stepb_tk F_6ecd8 D_6ecd8 ltac:(condZ).
      stepLD F_6ed58 D_6ed58 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rs) ltac:(apply lez4; lia).
      sn F_6ed5c D_6ed5c. stepb_ft F_6ed60 D_6ed60 ltac:(condZ).
      sn F_6ed64 D_6ed64. sn F_6ed68 D_6ed68. sn F_6ed6c D_6ed6c. sn F_6ed70 D_6ed70. sn F_6ed74 D_6ed74.
      sn F_6ebf0 D_6ebf0. sn F_6ebf4 D_6ebf4.
      stepLD8 F_6ec20 D_6ec20 ret. stepLD8 F_6ec24 D_6ec24 s0v. stepLD8 F_6ec28 D_6ec28 s1v.
      stepLD8 F_6ec2c D_6ec2c s2v. stepLD8 F_6ec30 D_6ec30 s3v.
      zv F_6ec34 D_6ec34 (Z_to_bv 64 s). sn F_6ec38 D_6ec38.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcp_B : forall regs m (s pixd : Z) (vd : pixv),
    (1 <= pixd)%Z -> (pixd mod 16 = 0)%Z -> PIXat m pixd vd -> (0 <= p_wpl vd * p_h vd)%Z -> (4 * (p_wpl vd * p_h vd) < 2 ^ 31)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x6ec44 : word) m rom) (mkst regs' (0x11e6d4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x6ec7c
      /\ getr regs' 10 = Z_to_bv 64 (p_data vd) /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (4 * (p_wpl vd * p_h vd))
      /\ getr regs' 8 = Z_to_bv 64 pixd /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m s pixd vd Hp ALd PX Hwh Hsz H2 H10. pose proof PX as (Hp0 & Hp64 & WF & _).
    pose proof (wf_h _ WF) as Rh. pose proof (wf_wpl _ WF) as Rwpl. pose proof (wf_data _ WF) as Rdata.
    assert (ALd8 : (pixd mod 8 = 0)%Z) by (apply al16_mod8; exact ALd).
    assert (Hm4 : (0 <= 4 * p_wpl vd * p_h vd < 2 ^ 31)%Z) by nia.
    pose proof (PIX_rd_h SEGS _ _ _ PX) as Ch. pose proof (PIX_rd_wpl SEGS _ _ _ PX) as Cwpl. pose proof (PIX_rd_data SEGS _ _ _ PX) as Cdata.
    eexists. split.
    - stepb_ft F_6ec44 D_6ec44 ltac:(condZ).
      sn F_6ec48 D_6ec48.
      guard8 F_6ec4c D_6ec4c ALd8. stepb_ft F_6ec50 D_6ec50 ltac:(condZ).
      stepLD F_6ec54 D_6ec54 (Z_to_le_bytes 4 (p_wpl vd)) (Z_to_bv 64 (p_wpl vd)) ltac:(addr_norm; exact Cwpl) ltac:(apply lez4; lia).
      stepLD F_6ec58 D_6ec58 (Z_to_le_bytes 4 (p_h vd)) (Z_to_bv 64 (p_h vd)) ltac:(addr_norm; exact Ch) ltac:(apply lez4; lia).
      stepiv F_6ec5c D_6ec5c (Z_to_bv 64 (4 * p_wpl vd)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_6ec60 D_6ec60. fixv (Z_to_bv 64 0) ltac:(apply v_mulh_small; lia).
      zv F_6ec64 D_6ec64 (Z_to_bv 64 (4 * (p_wpl vd * p_h vd))).
      sn F_6ec68 D_6ec68. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srai_small by lia; f_equal; apply Z.div_small; lia).
      stepb_ft F_6ec6c D_6ec6c ltac:(condZ).
      stepLD F_6ec70 D_6ec70 (Z_to_le_bytes 8 (p_data vd)) (Z_to_bv 64 (p_data vd)) ltac:(addr_norm; exact Cdata) ltac:(apply lez8; lia).
      sn F_6ec74 D_6ec74. sn F_6ec78 D_6ec78.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcp_C : forall regs m (s pixd pixs : Z) (vd vs : pixv) (nb : Z),
    (1 <= pixd)%Z -> (1 <= pixs)%Z -> (pixd mod 16 = 0)%Z -> PIXat m pixd vd -> PIXat m pixs vs ->
    (p_data vd mod 16 = 0)%Z -> (p_data vs mod 16 = 0)%Z -> (0 <= nb < 2 ^ 31)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 pixs -> getr regs 18 = Z_to_bv 64 nb ->
    exists regs',
      msteps SEGS (mkst regs (0x6ec7c : word) m rom) (mkst regs' (0x11e154 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x6ed54
      /\ getr regs' 10 = Z_to_bv 64 (p_data vd) /\ getr regs' 11 = Z_to_bv 64 (p_data vs) /\ getr regs' 12 = Z_to_bv 64 nb
      /\ getr regs' 8 = Z_to_bv 64 pixd /\ getr regs' 9 = Z_to_bv 64 pixs /\ getr regs' 18 = Z_to_bv 64 nb
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pixd pixs vd vs nb Hpd Hps ALd PXd PXs ALdd ALds Hnb H2 H8 H9 H18.
    pose proof PXd as (Hd0 & Hd64 & WFd & _). pose proof PXs as (Hs0 & Hs64 & WFs & _). pose proof (wf_data _ WFd) as Rdd. pose proof (wf_data _ WFs) as Rds.
    assert (ALd8 : (pixd mod 8 = 0)%Z) by (apply al16_mod8; exact ALd).
    pose proof (Z_lor_range64 (p_data vd) (p_data vs) ltac:(lia) ltac:(lia)) as ORr.
    pose proof (lor_mod4_0 (p_data vd) (p_data vs) ltac:(lia) ltac:(lia) ltac:(apply al16_mod4; exact ALdd) ltac:(apply al16_mod4; exact ALds)) as OR4.
    pose proof (PIX_rd_data SEGS _ _ _ PXd) as Cdd. pose proof (PIX_rd_data SEGS _ _ _ PXs) as Cds.
    eexists. split.
    - guard8 F_6ec7c D_6ec7c ALd8. stepb_tk F_6ec80 D_6ec80 ltac:(condZ).
      stepLD F_6ed38 D_6ed38 (Z_to_le_bytes 8 (p_data vd)) (Z_to_bv 64 (p_data vd)) ltac:(addr_norm; exact Cdd) ltac:(apply lez8; lia).
      stepLD F_6ed3c D_6ed3c (Z_to_le_bytes 8 (p_data vs)) (Z_to_bv 64 (p_data vs)) ltac:(addr_norm; exact Cds) ltac:(apply lez8; lia).
      orv F_6ed40 D_6ed40 (p_data vd) (p_data vs). guard4 F_6ed44 D_6ed44 OR4. stepb_ft F_6ed48 D_6ed48 ltac:(condZ).
      sn F_6ed4c D_6ed4c. fixv (Z_to_bv 64 nb) ltac:(rewrite v_addiw_Z; f_equal; rewrite sw32_small by lia; lia).
      sn F_6ed50 D_6ed50.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcp_D : forall regs m (s pixd : Z) (ret s0v s1v s2v s3v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cells5 m s ret s0v s1v s2v s3v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x6ed54 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pixd
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pixd ret s0v s1v s2v s3v Hs Hs64 Hret (R8 & R16 & R24 & R32 & R40) H2 H8. eexists. split.
    - sn F_6ed54 D_6ed54. sn F_6ed7c D_6ed7c.
      stepLD8 F_6ed80 D_6ed80 ret. stepLD8 F_6ed84 D_6ed84 s0v. stepLD8 F_6ed88 D_6ed88 s1v.
      stepLD8 F_6ed8c D_6ed8c s2v. stepLD8 F_6ed90 D_6ed90 s3v.
      zv F_6ed94 D_6ed94 (Z_to_bv 64 s). stepret F_6ed98 D_6ed98 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.


Lemma str_pixCreateTemplateNoInit : str16 0x1b9b0 23. Proof. str16_tac. Qed.

#[local] Definition tn_rest : list (bv 5) := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.



(* [comment removed for export] *)
Definition TK (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s w h d cm : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z) : Prop :=
  forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ O23LeptPixCopyT.pixt_new C A A' m' pixd w h d cd data cv) ) ->
     aroom A' vm' (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w d * h)) + RB_cmapT cm)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S.

(* [comment removed for export] *)
Lemma ptn_tail_W : forall C A A2 m md m4 vm2 regs r4 (s pixs pixd w h d cm datas cd data : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z),
  Cok C -> TK C A m md regs s w h d cm cv ret S kR bR ->
  aroom A2 vm2 (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w d * h)) + RB_cmapT cm)) ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 128 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  W C A2 m4 (with_vmmaps vm2 md) -> POSTM C A s m m4 -> sub_live A A2 ->
  cells4 m4 s ret (getr regs 8) (getr regs 9) (getr regs 18) ->
  getr r4 2 = Z_to_bv 64 (s - 32) -> getr r4 8 = Z_to_bv 64 pixd -> getr r4 9 = Z_to_bv 64 pixs ->
  (forall x, In x tn_rest -> getr r4 x = getr regs x) -> getr regs 2 = Z_to_bv 64 s ->
  PIXat m4 pixs (O23LeptPixCopyT.hdv w h d cm datas) -> live A (Z_to_bv 64 pixs) = Some 64%Z ->
  O23LeptPixHdr.hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  (4096 <= pixd)%Z -> (pixd + 64 <= alloc_top (c_vm C))%Z -> (pixd mod 16 = 0)%Z ->
  (4096 <= data)%Z -> (data + 4 * (wpl_of w d * h) <= alloc_top (c_vm C))%Z -> (data mod 16 = 0)%Z -> pixd <> data ->
  live A (Z_to_bv 64 pixd) = None -> live A (Z_to_bv 64 data) = None ->
  live (c_A0 C) (Z_to_bv 64 pixd) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  live A2 (Z_to_bv 64 pixd) = Some 64%Z -> live A2 (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z ->
  PIXat m4 pixd (O23LeptPixCopyT.hdv w h d cd data) -> O23LeptPixCopyT.cmres C A A2 m4 pixd data cd cv ->
  realizes SEGS (mkCfg (mkst r4 (0x6e264 : word) m4 al_rom) (with_vmmaps vm2 md)) S.
Proof.
  intros C A A2 m md m4 vm2 regs r4 s pixs pixd w h d cm datas cd data cv ret S kR bR CK HK Hrm2 Hs16 Hlo Hhi Hret HW4 PM4 SUB CE4 R2 R8 R9 RR H2 PXs Lps HOK Hw Hh
         Gp TOPp ALp Gd TOPd ALd NEpd LAp LAd L00p L00d L2p L2d PXd CMR.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  pose proof (SUB _ _ Lps) as Lps2.
  destruct (blk_range C A2 m4 _ (Z_to_bv 64 pixs) 64 CK HW4 Lps2 ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  assert (NEsp : Z_to_bv 64 pixs <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lps; rewrite Lps in LAp; discriminate).
  pose proof (blk_apart C A2 m4 _ _ _ _ _ CK HW4 Lps2 L2p NEsp ltac:(lia) ltac:(lia)) as APsp. rewrite !u_Z2bv in APsp by lia.
  destruct (ptn_C al_rom r4 m4 s pixs pixd (O23LeptPixCopyT.hdv w h d cm datas) (O23LeptPixCopyT.hdv w h d cd data) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALp PXs PXd
              eq_refl eq_refl eq_refl APsp ltac:(lia) ltac:(lia) (blk_sok C A2 m4 _ pixd 64 CK HW4 L2p ltac:(lia) ltac:(lia) ltac:(lia))
              (W_sok_win C A2 m4 _ (s - 64) 32 CK HW4 ltac:(lia) ltac:(cbn; lia)) R2 R8 R9)
    as (r5 & RUN5 & Y2 & Y1 & Y10 & Y11 & Y8 & Y9 & AG5).
  apply O23LeptCmap2.box_i in APsp.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN5 |].
  set (Mw := wbytes (wbytes (wbytes m4 (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x6e270)))
                            (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 pixd)))
                            (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 pixs))).
  set (M5 := wbytes (wbytes Mw (Z_to_bv 64 (pixd + 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (pixd + 32)) (word_to_le_bytes 4 (Z_to_bv 64 0))).
  assert (WPw : W C A2 Mw (with_vmmaps vm2 md) /\ POSTM C A s m Mw) by (subst Mw; wp_win CK).
  assert (WP5 : W C A2 M5 (with_vmmaps vm2 md) /\ POSTM C A s m M5).
  { subst M5. do 2 (apply (WP_blk C A A2 m _ _ (Z_to_bv 64 pixd) _ 64); [exact CK | | exact L2p | exact LAp | exact L00p | exact SUB | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
    exact WPw. }
  destruct WP5 as [HW5 PM5].
  assert (OUTw : forall x : word, ~ (s - 56 <= u x < s - 32)%Z -> Mw x = m4 x).
  { intros x Hx. subst Mw. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (OUT5 : forall x : word, ~ (pixd + 32 <= u x < pixd + 48)%Z -> M5 x = Mw x).
  { intros x Hx. subst M5. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PXd5 : PIXat M5 pixd (O23LeptPixCopyT.hdv w h d cd data)).
  { subst M5. apply O23LeptPixCopyT.PIX_wr_fmt0; [|reflexivity]. apply O23LeptPixCopyT.PIX_wr_text0; [|reflexivity]. apply (PIXat_frame m4); [exact PXd|]. intros x Hx. apply OUTw. lia. }
  assert (CE5 : cells4 M5 s ret (getr regs 8) (getr regs 9) (getr regs 18)).
  { eapply (cells4_out Mw _ (pixd + 32) (pixd + 48)); [exact OUT5 | lia | lia | lia |].
    eapply (cells4_out m4 _ (s - 56) (s - 32)); [exact OUTw | lia | lia | lia | exact CE4]. }
  assert (NEpdw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply O23LeptPixCopyT.zbv_ne2; lia).
  apply (padbits_W C A A2 M5 _ r5 (s - 32) pixd (O23LeptPixCopyT.hdv w h d cd data) (Z_to_bv 64 0x6e284) S CK HW5 SUB Y2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Y1 ltac:(red; apply bv_eq; reflexivity) Y10 Y11 PXd5 DV ltac:(cbn; lia) ltac:(cbn; lia) eq_refl L2p).
  { cbn. exact L2d. } { cbn. exact LAd. } { cbn. exact L00d. } { cbn. exact NEpdw. }
  intros m6 r6 HW6 CS6 PM6 PX6 OUT6 A10. cbn [p_data p_wpl p_h O23LeptPixCopyT.hdv] in OUT6. unfold LSF in OUT6.
  replace (Z_to_bv 64 0x6e284) with (0x6e284 : word) by (apply bv_eq; reflexivity).
  pose proof (cells4_frm C (s - 32) M5 m6 s _ _ _ _ CK (proj1 PM6) ltac:(lia) ltac:(lia) ltac:(lia) CE5) as (C1 & C2 & C3 & C4).
  destruct (ptn_D al_rom r6 m6 s pixd ret _ _ _ ltac:(lia) ltac:(lia) Hret C1 C2 C3 C4 ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r7 & RUN7 & Z2 & Z1 & Z10 & Z8 & Z9 & Z18 & AG7).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN7 |].
  apply (HK A2 m6 vm2 r7 HW6).
  - apply cs_kept_intro; csr; try reflexivity. all: rewrite ?Z8, ?Z9, ?Z18; try reflexivity. all: unfold tn_rest in RR; csr; reflexivity.
  - eapply POSTM_trans; [exact PM5 | eapply POSTM_mono; [|exact PM6]; lia].
  - right. exists pixd, cd, data. split; [exact Z10|].
    unfold O23LeptPixCopyT.pixt_new. do 13 (split; [assumption|]). split; [exact PX6|].
    destruct CMR as [[CD0 LEQ] | (ad & CMOKc & Gcd & TOPcd & Gad & TOPad & NEcdad & NEcdp & NEcdd & NEadp & NEadd & LAcd & LAad & L00cd & L00ad & L2cd & L2ad & CM4 & LEQ)]; [left; split; [exact CD0 | exact LEQ] | right].
    exists ad. do 16 (split; [assumption|]). split; [| exact LEQ].
    assert (NEw1 : Z_to_bv 64 cd <> Z_to_bv 64 data) by (apply O23LeptPixCopyT.zbv_ne2; lia).
    pose proof (blk_apart C A2 m4 _ _ _ _ _ CK HW4 L2cd L2d NEw1 ltac:(lia) ltac:(lia)) as APcdd. rewrite !u_Z2bv in APcdd by lia.
    assert (NEw2 : Z_to_bv 64 cd <> Z_to_bv 64 pixd) by (apply O23LeptPixCopyT.zbv_ne2; lia).
    pose proof (blk_apart C A2 m4 _ _ _ _ _ CK HW4 L2cd L2p NEw2 ltac:(lia) ltac:(lia)) as APcdp. rewrite !u_Z2bv in APcdp by lia.
    apply (CMAPat_frame m4); [exact CM4|]. intros x Hx. rewrite OUT6 by lia. rewrite OUT5 by lia. apply OUTw. lia.
  - exact Hrm2.
Qed.

Theorem pixCreateTemplateNoInit_szT_W : forall C A m md regs (s pixs w h d cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 128 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pixs ->
  PIXat m pixs (O23LeptPixCopyT.hdv w h d cm datas) -> O23LeptPixHdr.hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ O23LeptCmapValid.cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> ((RB_pixT (4 * (wpl_of w d * h)) + RB_cmapT cm) <= bR)%Z ->
  TK C A m md regs s w h d cm cv ret S kR bR ->
  realizes SEGS (mkCfg (mkst regs (0x6e148 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs w h d cm datas cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 PXs HOK Hw Hh Lps HCM kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  (* [comment removed for export] *)
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  destruct (ptn_A al_rom regs m s pixs (O23LeptPixCopyT.hdv w h d cm datas) ret ltac:(lia) ltac:(lia) ltac:(lia) ALps PXs ltac:(lia)
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q9 & Q8 & AG1). cbn [p_w p_h p_d O23LeptPixCopyT.hdv] in Q10, Q11, Q12.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR4 m s ret regs) md /\ POSTM C A s m (FR4 m s ret regs)) by (unfold FR4; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR4 m s ret regs) in *.
  pose proof (cells4_FR4 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 32 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold FR4. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x1381d0) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  assert (Hwh : (w * h <= 400000000)%Z) by (clear - Hw Hh Hw2 Hh2; nia).
  apply (pixCreateNoInit_szT2_W C A M1 md r1 (s - 32) w h d (Z_to_bv 64 0x6e17c) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 ltac:(lia) ltac:(lia) Hwh ltac:(lia)).
  intros A1 m2 vm1 r2 HWa CSa PMa OUTa HRTa.
  replace (Z_to_bv 64 0x6e17c) with (0x6e17c : word) by (apply bv_eq; reflexivity).
  pose proof (cells4_frm C (s - 32) M1 m2 s _ _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (PMa' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (PXs2 : PIXat m2 pixs (O23LeptPixCopyT.hdv w h d cm datas)).
  { apply (PIXat_frame m); [exact PXs|]. intros x Hx. rewrite (LIVK_byte C A M1 m2 md pixs 64 x CK HW1 (proj2 PMa) Lps ltac:(lia) TOPps Hx). apply OUT1. lia. }
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 pixs) by (csr; reflexivity).
  assert (E4 : getr r2 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
  destruct OUTa as [[Hres0 LIVEQ] | (pixd & data & Hres & _ & PN)].
  - (* [comment removed for export] *)
    destruct CE2 as (C1 & C2 & C3 & C4).
    destruct (ptn_F al_rom r2 m2 s ret _ _ _ ltac:(lia) ltac:(lia) (W_sev_got C A1 m2 _ HWa) (W_sev C A1 m2 _ HWa) C1 C2 C3 C4 E2 Hres0)
      as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & V9 & V18 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    apply (returnErrorPtr_W C A1 m2 _ r3 s 0x126da 0x1b9b0 13 23 ret (Z_to_bv 64 0) S CK HWa V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
             V10 V11 V12 str_msg_pixd str_pixCreateTemplateNoInit).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    apply (HK A1 m4 vm1 r5).
    + exact HW4.
    + apply cs_kept_intro; csr; try reflexivity. all: rewrite ?V8, ?V9, ?V18, ?Q8; reflexivity.
    + eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ|].
      eapply (POSTM_range C A1 m2 _ m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
    + left. split; [exact A10 | exact LIVEQ].
    + pose proof (RB_cmapT_le cm). room_tac.
  - (* [comment removed for export] *)
    destruct PN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & LEQ & PXd & _).
    cbn [p_wpl p_h set_data O23LeptPixHdr.pix_hdr] in TOPd, L1d.
    change (PIXat m2 pixd (O23LeptPixCopyT.hdv w h d 0 data)) in PXd.
    assert (NEsp : Z_to_bv 64 pixs <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lps; rewrite Lps in L0p; discriminate).
    assert (SUBa : sub_live A A1) by (eapply sub_live_new2; [exact L0p | exact L0d | exact L1p | exact L1d | exact LEQ]).
    pose proof (SUBa _ _ Lps) as Lps1.
    pose proof (blk_apart C A1 m2 _ _ _ _ _ CK HWa Lps1 L1p NEsp ltac:(lia) ltac:(lia)) as APsp. rewrite !u_Z2bv in APsp by lia.
    destruct (ptn_B al_rom r2 m2 s pixs pixd (O23LeptPixCopyT.hdv w h d cm datas) (O23LeptPixCopyT.hdv w h d 0 data) ltac:(lia) ltac:(lia) ltac:(lia) ALp PXs2 PXd
                (proj1 (spp_of_range d)) eq_refl eq_refl eq_refl APsp (blk_sok C A1 m2 _ pixd 64 CK HWa L1p ltac:(lia) ltac:(lia) ltac:(lia)) E2 Hres E9)
      as (r3 & RUN3 & X2 & X1 & X10 & X11 & X8 & X9 & X18 & AG3).
    apply O23LeptCmap2.box_i in APsp.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    cbn [p_spp O23LeptPixCopyT.hdv] in *.
    set (M3 := wbytes (wbytes m2 (Z_to_bv 64 (pixd + 12)) (word_to_le_bytes 4 (Z_to_bv 64 (spp_of d)))) (Z_to_bv 64 (pixd + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A s m M3).
    { subst M3. do 2 (apply (WP_blk C A A1 m _ _ (Z_to_bv 64 pixd) _ 64); [exact CK | | exact L1p | exact L0p | exact L00p | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
      split; [exact HWa | exact PMa']. }
    destruct WP3 as [HW3 PM3].
    assert (OUT3 : forall x : word, ~ (pixd + 12 <= u x < pixd + 32)%Z -> M3 x = m2 x).
    { intros x Hx. subst M3. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    assert (PXd3 : PIXat M3 pixd (O23LeptPixCopyT.hdv w h d 0 data)).
    { subst M3. apply (O23LeptPixCopyT.PIX_wr_res0 _ pixd (O23LeptPixCopyT.hdv w h d 0 data)); [| reflexivity | reflexivity].
      exact (O23LeptPixCopyT.PIX_wr_spp_same m2 pixd (O23LeptPixCopyT.hdv w h d 0 data) PXd). }
    assert (PXs3 : PIXat M3 pixs (O23LeptPixCopyT.hdv w h d cm datas)).
    { pose proof (O23LeptCmap2.box_e _ APsp) as U. apply (PIXat_frame m2); [exact PXs2|]. intros x Hx. apply OUT3. lia. }
    assert (CE3 : cells4 M3 s ret (getr regs 8) (getr regs 9) (getr regs 18)) by (eapply (cells4_out m2 _ (pixd + 12) (pixd + 32)); [exact OUT3 | lia | lia | lia | exact CE2]).
    assert (X4 : getr r3 4 = Z_to_bv 64 0x1381d0) by (rewrite (AG3 4) by (cbv; intuition discriminate); exact E4).
    assert (HCM3 : cm = 0%Z \/ (CMAPat M3 cm cv /\ O23LeptCmapValid.cmap_ok cv /\ live A1 (Z_to_bv 64 cm) = Some 24%Z /\ live A1 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
    { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right].
      pose proof CM as (Hc0 & Hc64 & _).
      destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
      pose proof (SUBa _ _ Lcm) as Lcm1.
      assert (NEcp : Z_to_bv 64 cm <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lcm; rewrite Lcm in L0p; discriminate).
      pose proof (blk_apart C A1 m2 _ _ _ _ _ CK HWa Lcm1 L1p NEcp ltac:(lia) ltac:(lia)) as APcp. rewrite !u_Z2bv in APcp by lia.
      split; [| split; [exact CMOK | split; [exact Lcm1 | exact (SUBa _ _ Larr)]]].
      apply (CMAPat_frame m); [exact CM|]. intros x Hx. rewrite OUT3 by lia.
      rewrite (LIVK_byte C A M1 m2 md cm 24 x CK HW1 (proj2 PMa) Lcm ltac:(lia) TOPcm Hx). apply OUT1. lia. }
    apply (pixCopyColormap_szT_W C A A1 M3 _ r3 (s - 32) pixd pixs (O23LeptPixCopyT.hdv w h d 0 data) (O23LeptPixCopyT.hdv w h d cm datas) cv (Z_to_bv 64 0x6e264) S CK HW3 SUBa X2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) X1 ltac:(red; apply bv_eq; reflexivity) X4 X10 X11
             PXd3 PXs3 eq_refl eq_refl ltac:(pose proof (O23LeptCmap2.box_e _ APsp); lia) L1p L0p L00p Lps1 HCM3
             (kR - RK_pix) (bR - RB_pixT (4 * (wpl_of w d * h))) ltac:(pose proof (RB_cmapT_le cm); room_tac) ltac:(room_consts; lia) ltac:(cbn [p_cmap O23LeptPixCopyT.hdv]; lia)).
    intros A2 m4 vm2 r4 HWb CSb PMb OUTb Hrm2. rewrite with_vmmaps_twice in HWb |- *. cbn [p_cmap O23LeptPixCopyT.hdv] in Hrm2.
    replace (Z_to_bv 64 0x6e264) with (0x6e264 : word) by (apply bv_eq; reflexivity).
    pose proof (cells4_frm C (s - 32) M3 m4 s _ _ _ _ CK (proj1 PMb) ltac:(lia) ltac:(lia) ltac:(lia) CE3) as CE4.
    assert (PMb' : POSTM C A s m m4) by (eapply POSTM_trans; [exact PM3 | eapply POSTM_mono; [|exact PMb]; lia]).
    assert (PXs4 : PIXat m4 pixs (O23LeptPixCopyT.hdv w h d cm datas)).
    { apply (PIXat_frame M3); [exact PXs3|]. intros x Hx. exact (O23LeptCmap2.LIVK_at A M3 m4 pixs 64 x (proj2 PMb) Lps ltac:(lia) ltac:(lia) Hx). }
    assert (Y2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (Y8 : getr r4 8 = Z_to_bv 64 pixd) by (csr; reflexivity).
    assert (Y9 : getr r4 9 = Z_to_bv 64 pixs) by (csr; reflexivity).
    assert (RR : forall x, In x tn_rest -> getr r4 x = getr regs x) by (unfold tn_rest; rest_solve).
    destruct OUTb as [[LIVEQ PXd4] | (cd & ad & CC & PXd4)].
    + apply (ptn_tail_W C A A2 m md m4 vm2 regs r4 s pixs pixd w h d cm datas 0 data cv ret S kR bR CK HK ltac:(room_tac) Hs16 ltac:(unfold LSF; lia) Hhi Hret HWb PMb'
               (sub_live_trans _ _ _ SUBa (sub_live_eq _ _ LIVEQ)) CE4 Y2 Y8 Y9 RR H2 PXs4 Lps HOK Hw Hh Gp TOPp ALp Gd TOPd ALd NEpd L0p L0d L00p L00d
               ltac:(rewrite LIVEQ; exact L1p) ltac:(rewrite LIVEQ; exact L1d) PXd4).
      left. split; [reflexivity|]. intros q N1 N2. rewrite LIVEQ. apply LEQ; assumption.
    + pose proof CC as (CMOKc & Gcd & TOPcd & ALcd & Gad & TOPad & ALad & NEcdad & LA1cd & LA1ad & L00cd & L00ad & L2cd & L2ad & LEQ2 & CM4).
      assert (NEcdp : Z_to_bv 64 cd <> Z_to_bv 64 pixd) by (intros E; rewrite E in LA1cd; rewrite L1p in LA1cd; discriminate).
      assert (NEadp : Z_to_bv 64 ad <> Z_to_bv 64 pixd) by (intros E; rewrite E in LA1ad; rewrite L1p in LA1ad; discriminate).
      assert (NEcdd : Z_to_bv 64 cd <> Z_to_bv 64 data) by (intros E; rewrite E in LA1cd; rewrite L1d in LA1cd; discriminate).
      assert (NEadd : Z_to_bv 64 ad <> Z_to_bv 64 data) by (intros E; rewrite E in LA1ad; rewrite L1d in LA1ad; discriminate).
      assert (SUBb : sub_live A1 A2) by (eapply sub_live_new2; [exact LA1cd | exact LA1ad | exact L2cd | exact L2ad | exact LEQ2]).
      apply (ptn_tail_W C A A2 m md m4 vm2 regs r4 s pixs pixd w h d cm datas cd data cv ret S kR bR CK HK ltac:(room_tac) Hs16 ltac:(unfold LSF; lia) Hhi Hret HWb PMb'
               (sub_live_trans _ _ _ SUBa SUBb) CE4 Y2 Y8 Y9 RR H2 PXs4 Lps HOK Hw Hh Gp TOPp ALp Gd TOPd ALd NEpd L0p L0d L00p L00d
               (SUBb _ _ L1p) (SUBb _ _ L1d) PXd4).
      right. exists ad.
      split; [exact CMOKc|]. split; [exact Gcd|]. split; [exact TOPcd|]. split; [exact Gad|]. split; [exact TOPad|]. split; [exact NEcdad|].
      split; [intros E; apply NEcdp; rewrite E; reflexivity|]. split; [intros E; apply NEcdd; rewrite E; reflexivity|].
      split; [intros E; apply NEadp; rewrite E; reflexivity|]. split; [intros E; apply NEadd; rewrite E; reflexivity|].
      split; [rewrite <- (LEQ _ NEcdp NEcdd); exact LA1cd|]. split; [rewrite <- (LEQ _ NEadp NEadd); exact LA1ad|].
      split; [exact L00cd|]. split; [exact L00ad|]. split; [exact L2cd|]. split; [exact L2ad|]. split; [exact CM4|].
      intros q N1 N2 N3 N4. rewrite (LEQ2 q N3 N4). apply LEQ; assumption.
Qed.


Lemma str_pixCreateTemplate : str16 0x192a9 17. Proof. str16_tac. Qed.
Lemma str_pixCopy : str16 0x18bc4 7. Proof. str16_tac. Qed.

Ltac in_kept := unfold callee_kept; cbn [In]; repeat (first [left; reflexivity | right]).

(* [comment removed for export] *)
Theorem pixCopy_szT_W : forall C A m md regs (s pixs w h d cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 176 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 pixs ->
  PIXat m pixs (O23LeptPixCopyT.hdv w h d cm datas) -> O23LeptPixHdr.hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ O23LeptCmapValid.cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> ((RB_pixT (4 * (wpl_of w d * h)) + RB_cmapT cm) <= bR)%Z ->
  TK C A m md regs s w h d cm cv ret S kR bR ->
  realizes SEGS (mkCfg (mkst regs (0x6eb5c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs w h d cm datas cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 PXs HOK Hw Hh Lps Lds HCM kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  pose proof PXs as (Hs0 & Hs64' & WFs & _). pose proof (wf_data _ WFs) as Rds. cbn [p_data O23LeptPixCopyT.hdv] in Rds.
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  destruct (blk_range C A m md (Z_to_bv 64 datas) _ CK HW Lds ltac:(lia)) as [Gds TOPds]. rewrite u_Z2bv in Gds, TOPds by lia.
  set (n := (4 * (wpl_of w d * h))%Z) in *. assert (En : n = (4 * (wpl_of w d * h))%Z) by reflexivity.
  (* [comment removed for export] *)
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lds) as (_ & ALds & _). rewrite u_Z2bv in ALds by lia.
  destruct (pcp_A al_rom regs m s pixs (O23LeptPixCopyT.hdv w h d cm datas) ret ltac:(lia) ltac:(lia) ltac:(lia) ALps PXs ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q9 & Q18 & Q8 & Q19 & AG1). cbn [p_wpl p_h O23LeptPixCopyT.hdv] in Q18. rewrite <- En in Q18.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (O23LeptCmap2.FR5 m s ret regs) md /\ POSTM C A s m (O23LeptCmap2.FR5 m s ret regs)) by (unfold O23LeptCmap2.FR5; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := O23LeptCmap2.FR5 m s ret regs) in *.
  pose proof (cells5_FR5 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 48 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold O23LeptCmap2.FR5. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PXs1 : PIXat M1 pixs (O23LeptPixCopyT.hdv w h d cm datas)) by (apply (PIXat_frame m); [exact PXs | intros x Hx; apply OUT1; lia]).
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x1381d0) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  assert (HCM1 : cm = 0%Z \/ (CMAPat M1 cm cv /\ O23LeptCmapValid.cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right]. split; [| split; [exact CMOK | split; [exact Lcm | exact Larr]]].
    pose proof CM as (Hc0 & Hc64 & _). destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
    apply (CMAPat_frame m); [exact CM|]. intros x Hx. apply OUT1. lia. }
  apply (pixCreateTemplateNoInit_szT_W C A M1 md r1 (s - 48) pixs w h d cm datas cv (Z_to_bv 64 0x6ec44) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 PXs1 HOK Hw Hh Lps HCM1 kR bR Hrm Hrk Hrb).
  unfold TK. intros A1 m2 vm1 r2 HWa CSa PMa OUTa Hrm1.
  replace (Z_to_bv 64 0x6ec44) with (0x6ec44 : word) by (apply bv_eq; reflexivity).
  pose proof (cells5_frm C (s - 48) M1 m2 s _ _ _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (PMa' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (PXs2 : PIXat m2 pixs (O23LeptPixCopyT.hdv w h d cm datas)).
  { apply (PIXat_frame M1); [exact PXs1|]. intros x Hx. exact (O23LeptCmap2.LIVK_at A M1 m2 pixs 64 x (proj2 PMa) Lps ltac:(lia) ltac:(lia) Hx). }
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 pixs) by (csr; reflexivity).
  assert (E18 : getr r2 18 = Z_to_bv 64 n) by (csr; reflexivity).
  destruct OUTa as [[Hres0 LIVEQ] | (pixd & cd & data & Hres & PT)].
  - (* [comment removed for export] *)
    destruct (pcp_F1 al_rom r2 m2 s (W_sev_got C A1 m2 _ HWa) (W_sev C A1 m2 _ HWa) E2 Hres0) as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V19 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    apply (returnErrorPtr_W C A1 m2 _ r3 (s - 48) 0x126da 0x192a9 13 17 (Z_to_bv 64 0x6ecd8) (Z_to_bv 64 0) S CK HWa V2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity)
             V10 V11 V12 str_msg_pixd str_pixCreateTemplate).
    intros m3 r4 HW3 OUT3 GR3 CS3 B10. unfold LSF in OUT3.
    replace (Z_to_bv 64 0x6ecd8) with (0x6ecd8 : word) by (apply bv_eq; reflexivity).
    pose proof (cells5_out m2 m3 _ _ s _ _ _ _ _ OUT3 ltac:(lia) ltac:(lia) ltac:(lia) CE2) as CE3.
    assert (Y19 : getr r4 19 = Z_to_bv 64 0x127c60) by (csr; reflexivity).
    destruct (pcp_F2 al_rom r4 m3 s ret _ _ _ _ ltac:(lia) ltac:(lia) (W_sev C A1 m3 _ HW3) CE3 ltac:(csr; reflexivity) B10 Y19)
      as (r5 & RUN5 & X2 & X1 & X10 & X11 & X12 & X8 & X9 & X18 & X19 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
    apply (returnErrorPtr_W C A1 m3 _ r5 s 0x126da 0x18bc4 13 7 ret (Z_to_bv 64 0) S CK HW3 X2 Hs16 ltac:(unfold LSF; lia) Hhi X1 Hret
             X10 X11 X12 str_msg_pixd str_pixCopy).
    intros m4 r6 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    apply (HK A1 m4 vm1 r6).
    + exact HW4.
    + apply cs_kept_intro; csr; try reflexivity. all: rewrite ?X8, ?X9, ?X18, ?X19, ?Q19; reflexivity.
    + eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ|].
      eapply POSTM_trans; [eapply (POSTM_range C A1 m2 _ m3); [exact CK | exact HWa | exact OUT3 | lia | lia | lia] |].
      eapply (POSTM_range C A1 m3 _ m4); [exact CK | exact HW3 | exact OUT4 | lia | lia | lia].
    + left. split; [exact A10 | exact LIVEQ].
    + exact Hrm1.
  - (* [comment removed for export] *)
    pose proof PT as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & PXd & CMR). rewrite <- En in TOPd, L1d.
    assert (NEsp : Z_to_bv 64 pixs <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lps; rewrite Lps in L0p; discriminate).
    assert (NEsd : Z_to_bv 64 datas <> Z_to_bv 64 data) by (intros E; rewrite E in Lds; rewrite Lds in L0d; discriminate).
    assert (SUBa : sub_live A A1).
    { intros q k Lq. destruct CMR as [[_ LEQ] | (ad & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LAcd & LAad & _ & _ & _ & _ & _ & LEQ)].
      - rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence].
      - rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence | intros ->; congruence | intros ->; congruence]. }
    pose proof (SUBa _ _ Lps) as Lps1. pose proof (SUBa _ _ Lds) as Lds1.
    destruct (pcp_B al_rom r2 m2 s pixd (O23LeptPixCopyT.hdv w h d cd data) ltac:(lia) ALp PXd ltac:(cbn; lia) ltac:(cbn; lia) E2 Hres)
      as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & V9 & V18 & AG3). cbn [p_data p_wpl p_h O23LeptPixCopyT.hdv] in V10, V12. rewrite <- En in V12.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    (* [comment removed for export] *)
    pose proof (blk_sok C A1 m2 _ data n CK HWa L1d ltac:(lia) ltac:(lia) ltac:(lia)) as SOKd.
    destruct (memset_spec r3 m2 al_rom data n (Z_to_bv 64 0x6ec7c) ltac:(lia) ltac:(lia) ltac:(lia) SOKd ltac:(red; apply bv_eq; reflexivity) V1 V10 V11 V12)
      as (r4 & RUN4 & W10 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN4 |].
    replace (Z_to_bv 64 0x6ec7c) with (0x6ec7c : word) by (apply bv_eq; reflexivity).
    set (M5 := zf m2 data [(0, n)]%Z).
    assert (OUT5 : forall x : word, (u x < data \/ data + n <= u x)%Z -> M5 x = m2 x).
    { intros x Hx. subst M5. apply zf_outside. apply inzr_falseP. cbn [inzrP]. lia. }
    assert (CH : forall a, M5 a <> m2 a -> scratch C s a \/ (exists p k, live A1 p = Some k /\ live A p = None /\ (u p <= u a < u p + k)%Z)).
    { intros a NE. right. exists (Z_to_bv 64 data), n. rewrite u_Z2bv by lia. split; [exact L1d | split; [exact L0d|]].
      destruct (Z_lt_ge_dec (u a) data); [exfalso; apply NE; apply OUT5; lia|].
      destruct (Z_lt_ge_dec (u a) (data + n)); [lia | exfalso; apply NE; apply OUT5; lia]. }
    assert (HW5 : W C A1 M5 (with_vmmaps vm1 md)).
    { apply (W_local C A1 m2 _ M5 s CK HWa Hhi); [| subst M5; apply zf_grows].
      intros a NE. destruct (CH a NE) as [X|(p & k & L & _ & R)]; [left; exact X | right; exists p, k]. split; [exact L | split; [| exact R]].
      destruct (bv_eq_dec _ p (Z_to_bv 64 data)) as [->|NE']; [exact L00d|].
      exfalso. apply NE. apply OUT5.
      pose proof (ai_live_disjoint A1 m2 _ _ _ _ _ (w_inv _ _ _ _ HWa) L L1d NE') as D. rewrite u_Z2bv in D by lia.
      pose proof (ai_live_hull A1 m2 _ _ _ (w_inv _ _ _ _ HWa) L) as (Hn0 & _). pose proof (round16_ge k Hn0).
      pose proof (round16_ge n ltac:(lia)). lia. }
    assert (PM5 : POSTM C A s m M5) by (eapply POSTM_trans; [exact PMa' | exact (POSTM_local C A A1 m2 _ M5 s CK HWa SUBa CH)]).
    assert (EQ5 : forall (p k : Z) (x : word), live A1 (Z_to_bv 64 p) = Some k -> Z_to_bv 64 p <> Z_to_bv 64 data -> (0 <= p < 2 ^ 64)%Z -> (0 <= k)%Z -> (p <= u x < p + k)%Z -> M5 x = m2 x).
    { intros p k x L NE' G0 K0 Hx. apply OUT5.
      pose proof (blk_apart C A1 m2 _ _ _ _ _ CK HWa L L1d NE' K0 ltac:(lia)) as D. rewrite !u_Z2bv in D by lia. lia. }
    assert (NEpdw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply O23LeptPixCopyT.zbv_ne2; lia).
    assert (NEspd : Z_to_bv 64 pixs <> Z_to_bv 64 data) by (intros E; rewrite E in Lps; rewrite Lps in L0d; discriminate).
    assert (PXd5 : PIXat M5 pixd (O23LeptPixCopyT.hdv w h d cd data)) by (apply (PIXat_frame m2); [exact PXd | intros x Hx; exact (EQ5 pixd 64%Z x L1p NEpdw ltac:(lia) ltac:(lia) Hx)]).
    assert (PXs5 : PIXat M5 pixs (O23LeptPixCopyT.hdv w h d cm datas)) by (apply (PIXat_frame m2); [exact PXs2 | intros x Hx; exact (EQ5 pixs 64%Z x Lps1 NEspd ltac:(lia) ltac:(lia) Hx)]).
    assert (CE5 : cells5 M5 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
    { destruct CE2 as (C1 & C2 & C3 & C4 & C5). unfold cells5.
      repeat split; (etransitivity; [apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia | intros x Hx; apply OUT5; rewrite u_Z2bv in Hx by lia; cbn in Hx; lia] | eassumption]). }
    assert (X2 : getr r4 2 = Z_to_bv 64 (s - 48)) by (rewrite (AG4 2) by (cbv; intuition discriminate); exact V2).
    assert (X8 : getr r4 8 = Z_to_bv 64 pixd) by (rewrite (AG4 8) by (cbv; intuition discriminate); exact V8).
    assert (X9 : getr r4 9 = Z_to_bv 64 pixs) by (rewrite (AG4 9) by (cbv; intuition discriminate); rewrite V9; exact E9).
    assert (X18 : getr r4 18 = Z_to_bv 64 n) by (rewrite (AG4 18) by (cbv; intuition discriminate); rewrite V18; exact E18).
    destruct (pcp_C al_rom r4 M5 s pixd pixs (O23LeptPixCopyT.hdv w h d cd data) (O23LeptPixCopyT.hdv w h d cm datas) n ltac:(lia) ltac:(lia) ALp PXd5 PXs5
                ltac:(cbn; exact ALd) ltac:(cbn; exact ALds) ltac:(lia) X2 X8 X9 X18)
      as (r5 & RUN5 & Y2 & Y1 & Y10 & Y11 & Y12 & Y8 & Y9 & Y18 & AG5). cbn [p_data O23LeptPixCopyT.hdv] in Y10, Y11.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN5 |].
    (* [comment removed for export] *)
    destruct (blk_rdn C A1 M5 _ datas n (Z.to_nat n) CK HW5 Lds1 ltac:(lia) ltac:(lia) ltac:(lia)) as (bs & Hsrc & Hlen).
    pose proof (blk_apart C A1 M5 _ _ _ _ _ CK HW5 Lds1 L1d NEsd ltac:(lia) ltac:(lia)) as APsd. rewrite !u_Z2bv in APsd by lia.
    assert (HOKm : mcH M5 (Z_to_bv 64 data) (Z_to_bv 64 datas) n bs).
    { constructor; rewrite ?u_Z2bv by lia; [lia | exact Hlen | rewrite Hlen; exact Hsrc | rewrite Hlen; exact (blk_sok C A1 M5 _ data n CK HW5 L1d ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | lia]. }
    apply O23LeptCmap2.box_i in APsd.
    destruct (ref_memcpy M5 _ _ n bs al_rom HOKm r5 (Z_to_bv 64 0x6ed54) ltac:(red; apply bv_eq; reflexivity) Y1 Y10 Y11 Y12) as (r6 & RUN6 & KP6).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN6 |].
    replace (Z_to_bv 64 0x6ed54) with (0x6ed54 : word) by (apply bv_eq; reflexivity).
    set (M6 := wbytes M5 (Z_to_bv 64 data) bs) in *.
    assert (HW6 : W C A1 M6 (with_vmmaps vm1 md)).
    { subst M6. apply (W_store_blk C A1 M5 _ (Z_to_bv 64 data) (Z_to_bv 64 data) n bs CK HW5 L1d L00d); rewrite ?u_Z2bv by lia; [lia | rewrite Hlen; lia]. }
    assert (PM6 : POSTM C A s m M6).
    { eapply POSTM_trans; [exact PM5|]. subst M6. apply (POSTM_blk C A A1 M5 _ (Z_to_bv 64 data) (Z_to_bv 64 data) n bs s CK HW5 L1d L0d SUBa); rewrite ?u_Z2bv by lia; [lia | rewrite Hlen; lia]. }
    assert (OUT6 : forall x : word, ~ (data <= u x < data + n)%Z -> M6 x = M5 x).
    { intros x Hx. subst M6. apply wbytes_outside; rewrite Hlen, u_Z2bv by lia; lia. }
    assert (EQ6 : forall (p k : Z) (x : word), live A1 (Z_to_bv 64 p) = Some k -> Z_to_bv 64 p <> Z_to_bv 64 data -> (0 <= p < 2 ^ 64)%Z -> (0 <= k)%Z -> (p <= u x < p + k)%Z -> M6 x = M5 x).
    { intros p k x L NE' G0 K0 Hx. apply OUT6.
      pose proof (blk_apart C A1 m2 _ _ _ _ _ CK HWa L L1d NE' K0 ltac:(lia)) as D. rewrite !u_Z2bv in D by lia. lia. }
    assert (PXd6 : PIXat M6 pixd (O23LeptPixCopyT.hdv w h d cd data)) by (apply (PIXat_frame M5); [exact PXd5 | intros x Hx; exact (EQ6 pixd 64%Z x L1p NEpdw ltac:(lia) ltac:(lia) Hx)]).
    assert (CE6 : cells5 M6 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
    { eapply (cells5_out M5 _ data (data + n)); [exact OUT6 | lia | lia | lia | exact CE5]. }
    assert (K2 : getr r6 2 = getr r5 2) by (apply KP6; in_kept). assert (K8 : getr r6 8 = getr r5 8) by (apply KP6; in_kept).
    assert (K3 : getr r6 3 = getr r5 3) by (apply KP6; in_kept). assert (K4 : getr r6 4 = getr r5 4) by (apply KP6; in_kept).
    assert (K20 : getr r6 20 = getr r5 20) by (apply KP6; in_kept). assert (K21 : getr r6 21 = getr r5 21) by (apply KP6; in_kept).
    assert (K22 : getr r6 22 = getr r5 22) by (apply KP6; in_kept). assert (K23 : getr r6 23 = getr r5 23) by (apply KP6; in_kept).
    assert (K24 : getr r6 24 = getr r5 24) by (apply KP6; in_kept). assert (K25 : getr r6 25 = getr r5 25) by (apply KP6; in_kept).
    assert (K26 : getr r6 26 = getr r5 26) by (apply KP6; in_kept). assert (K27 : getr r6 27 = getr r5 27) by (apply KP6; in_kept).
    destruct (pcp_D al_rom r6 M6 s pixd ret _ _ _ _ ltac:(lia) ltac:(lia) Hret CE6 ltac:(rewrite K2; exact Y2) ltac:(rewrite K8; exact Y8))
      as (r7 & RUN7 & Z2 & Z1 & Z10 & Z8 & Z9 & Z18 & Z19 & AG7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN7 |].
    apply (HK A1 M6 vm1 r7 HW6).
    + apply cs_kept_intro; csr; try reflexivity. all: rewrite ?Z8, ?Z9, ?Z18, ?Z19; try reflexivity.
      all: rewrite ?K3, ?K4, ?K20, ?K21, ?K22, ?K23, ?K24, ?K25, ?K26, ?K27; csr; reflexivity.
    + exact PM6.
    + right. exists pixd, cd, data. split; [exact Z10|].
      unfold O23LeptPixCopyT.pixt_new. rewrite <- En. do 13 (split; [assumption|]). split; [exact PXd6|].
      destruct CMR as [[CD0 LEQ] | (ad & CMOKc & Gcd & TOPcd & Gad & TOPad & NEcdad & NEcdp & NEcdd & NEadp & NEadd & LAcd & LAad & L00cd & L00ad & L2cd & L2ad & CM4 & LEQ)]; [left; split; [exact CD0 | exact LEQ] | right].
      exists ad. do 16 (split; [assumption|]). split; [| exact LEQ].
      assert (NEw1 : Z_to_bv 64 cd <> Z_to_bv 64 data) by (apply O23LeptPixCopyT.zbv_ne2; lia).
      apply (CMAPat_frame m2); [exact CM4|]. intros x Hx. rewrite (EQ6 cd 24%Z x L2cd NEw1 ltac:(lia) ltac:(lia) Hx). exact (EQ5 cd 24%Z x L2cd NEw1 ltac:(lia) ltac:(lia) Hx).
    + exact Hrm1.
Qed.

End PixCopy.
