(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptStderr V10LeptBase V10LeptUb.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL7a.
Import V10CL7a.V10LeptErr.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL8a.
Import V10CL8a.V10LeptPixHdr. Import V10CL8a.V10LeptCmap.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptPixCreate.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL9a.
Import V10CL9a.V10LeptPixDestroy.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptCmapValid V10LeptCmap2 V10LeptPixCopyA V10LeptPixCopy V10LeptPixT V10LeptPixCopyT.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10Kit.
Import V10Kit.V10MemcpyBase. Import V10Kit.V10Memcpy. Import V10Kit.V10Memset.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10_code_fhH.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoom10.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Definition PC_pixAddBorderGeneral : Z := 0x17fb8.
Definition PC_pixRemoveBorderGeneral : Z := 0x18304.
Definition PC_pixDestroy : Z := 0x1615c.
Definition ABG_STACK : Z := 128 + 112 + LSF.      (* [comment removed for export] *)
Definition RBG_STACK : Z := 96 + 112 + LSF.       (* [comment removed for export] *)

Definition PCT_STACK : Z := 16 + 128 + 16 + LSF.     (* [comment removed for export] *)

(* [comment removed for export] *)
Module PxdSegs.
Section PxdS.
Context {fx : FPState}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma pxd_A : forall regs m (s pp pix : Z) (v : pixv) (ret : word),
    (32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (pix mod 16 = 0)%Z -> (pp mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> store_ok SEGS m (Z_to_bv 64 pix) 64 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
    PIXat m pix v -> p_rc v = 1%Z -> (pix + 64 <= s - 32 \/ s <= pix)%Z -> (4096 <= pix)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x1615c : word) m rom)
                  (mkst regs' (0x161a4 : word)
                        (wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                                (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                                (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
                                (Z_to_bv 64 (pix + 20)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 8 = Z_to_bv 64 pix /\ getr regs' 9 = Z_to_bv 64 pp
      /\ getr regs' 10 = Z_to_bv 64 (p_data v)
      /\ regs_agree (fun r => In r [2; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pp pix v ret Hs Hpp Hpp64 Hal ALp SOK SOKp Rpp PX RC DJ Hpix H2 H1 H10.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rd.
    assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact Hal | reflexivity]).
    eexists. split.
    - zv F_16060 D_16060 (Z_to_bv 64 (s - 32)).
      stepST F_16064 D_16064 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_16068 D_16068 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_1606c D_1606c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_16070 D_16070 ltac:(condZ).
      stepiv F_16074 D_16074 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite ALp; reflexivity).
      stepb_ft F_16078 D_16078 ltac:(condZ).
      stepLD F_1607c D_1607c (Z_to_le_bytes 8 pix) (Z_to_bv 64 pix) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
      stepb_ft F_16080 D_16080 ltac:(condZ).
      stepiv F_16084 D_16084 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite AL8; reflexivity).
      stepb_ft F_16088 D_16088 ltac:(condZ).
      zv F_1608c D_1608c (Z_to_bv 64 (pix + 20)).
      sn F_16090 D_16090.
      chain_step;
        [ reflexivity
        | eapply (step_amoadd_w SEGS _ _ _ rom _ _ _ _ _ _ (Z_to_le_bytes 4 1) (Z_to_bv 64 1) F_16094 eq_refl D_16094);
          [ gres; rewrite u_Z2bv by lia; apply mod16_plus_mod4; [exact Hal | reflexivity]
          | gres; repeat rdn_peel1; rewrite <- RC; exact (PIX_rd_rc SEGS _ _ _ PX)
          | apply lez4; lia
          | gres; sok_in SOKp ]
        | step_simpl ].
      gres. rewrite zbv_add. replace (Z_to_bv 64 (1 + 18446744073709551615)%Z) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite (v_lw_small 1) by lia.
      sn F_16098 D_16098.
      stepb_ft F_1609c D_1609c ltac:(condZ).
      sn F_160a0 D_160a0.
      stepLD F_160a4 D_160a4 (Z_to_le_bytes 8 (p_data v)) (Z_to_bv 64 (p_data v))
        ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Lemma pxd_B1 : forall regs m (data : Z),
    (1 <= data)%Z -> (data < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x34e18) 8 = Some (Z_to_le_bytes 8 0x2b208) ->
    getr regs 10 = Z_to_bv 64 data ->
    exists regs',
      msteps SEGS (mkst regs (0x161a4 : word) m rom) (mkst regs' (0x2b208 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 data /\ getr regs' 1 = Z_to_bv 64 0x161b4
      /\ regs_agree (fun r => In r [1; 11]%list) regs regs'.
  Proof.
    intros regs m data Hd Hd64 Rpmm H10.
    eexists. split.
    - stepb_ft F_160a8 D_160a8 ltac:(condZ).
      sn F_160ac D_160ac.
      stepLD F_160b0 D_160b0 (Z_to_le_bytes 8 0x2b208) (Z_to_bv 64 0x2b208) ltac:(addr_norm; exact Rpmm) ltac:(apply lez8; lia).
      stepjr F_160b4 D_160b4 (Z_to_bv 64 0x2b208) ltac:(gres; reflexivity).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pxd_B0 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    msteps SEGS (mkst regs (0x161a4 : word) m rom) (mkst regs (0x161b4 : word) m rom).
  Proof.
    intros regs m H10. stepb_tk F_160a8 D_160a8 ltac:(condZ). apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma pxd_C1 : forall regs m (s pix cm : Z) (v : pixv),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> PIXat m pix v -> p_text v = 0%Z -> p_cmap v = cm -> (1 <= cm)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> (pix + 64 <= s - 32 \/ s <= pix)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x161b4 : word) m rom)
                  (mkst regs' (0x19848 : word) (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 cm))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 10 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x161d4
      /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s pix cm v Hs Hs64 PX Ht Hc Hcm SOK DJ H2 H8.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_cmap _ WF) as Rc.
    eexists. split.
    - stepLD F_160b8 D_160b8 (Z_to_le_bytes 8 0) (Z_to_bv 64 0)
        ltac:(addr_norm; rewrite <- Ht; exact (PIX_rd_text SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepb_tk F_160bc D_160bc ltac:(condZ).
      stepLD F_160c4 D_160c4 (Z_to_le_bytes 8 cm) (Z_to_bv 64 cm)
        ltac:(addr_norm; rewrite <- Hc; exact (PIX_rd_cmap SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepST F_160c8 D_160c8 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 cm) ltac:(sok_in SOK).
      stepb_ft F_160cc D_160cc ltac:(condZ).
      sn F_160d0 D_160d0.
      sn F_160d4 D_160d4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pxd_C2 : forall regs m (pix : Z),
    (0 <= pix)%Z -> (pix + 64 < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 pix) 64 = true ->
    getr regs 8 = Z_to_bv 64 pix ->
    msteps SEGS (mkst regs (0x161d4 : word) m rom)
                (mkst regs (0x161d8 : word) (wbytes m (Z_to_bv 64 (pix + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom).
  Proof.
    intros regs m pix Hp0 Hp64 SOK H8.
    stepST F_160d8 D_160d8 (Z_to_bv 64 (pix + 48)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma pxd_C0 : forall regs m (s pix : Z) (v : pixv),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> PIXat m pix v -> p_text v = 0%Z -> p_cmap v = 0%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> (pix + 64 <= s - 32 \/ s <= pix)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x161b4 : word) m rom)
                  (mkst regs' (0x161d8 : word) (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m s pix v Hs Hs64 PX Ht Hc SOK DJ H2 H8.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    eexists. split.
    - stepLD F_160b8 D_160b8 (Z_to_le_bytes 8 0) (Z_to_bv 64 0)
        ltac:(addr_norm; rewrite <- Ht; exact (PIX_rd_text SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepb_tk F_160bc D_160bc ltac:(condZ).
      stepLD F_160c4 D_160c4 (Z_to_le_bytes 8 0) (Z_to_bv 64 0)
        ltac:(addr_norm; rewrite <- Hc; exact (PIX_rd_cmap SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepST F_160c8 D_160c8 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_160cc D_160cc ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pxd_D : forall regs m (pix : Z),
    getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x161d8 : word) m rom) (mkst regs' (0x2b208 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 1 = Z_to_bv 64 0x161e0
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m pix H8.
    eexists. split.
    - sn F_160dc D_160dc. sn F_160e0 D_160e0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pxd_E : forall regs m (s pp : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 9 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x161e0 : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s pp ret s0v s1v Hs Hpp Hpp64 Hret SOK R8 R16 R24 H2 H9.
    eexists. split.
    - sn F_160e4 D_160e4.
      stepST F_160e8 D_160e8 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_160ec D_160ec.
      stepLD8 F_16128 D_16128 ret.
      stepLD8 F_1612c D_1612c s0v.
      stepLD8 F_16130 D_16130 s1v.
      zv F_16134 D_16134 (Z_to_bv 64 s).
      stepret F_16138 D_16138 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End Segs.
End PxdS.
End PxdSegs.

Section GrayA.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma pixCopyResolution_run : forall regs m (pixd pixs : Z) (vs vd : pixv) (ret : word),
    (1 <= pixs)%Z -> (1 <= pixd)%Z -> pixs <> pixd -> (pixs mod 8 = 0)%Z -> (pixd mod 8 = 0)%Z ->
    PIXat m pixs vs -> PIXat m pixd vd -> p_xres vs = 0%Z -> p_yres vs = 0%Z ->
    store_ok SEGS m (Z_to_bv 64 pixd) 64 = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x16600 : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (pixd + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m pixd pixs vs vd ret Hps Hpd NE ALs ALd PXs PXd Hx Hy SOKd Hret H1 H10 H11.
    pose proof PXs as (Hs0 & Hs64 & WFs & _). pose proof PXd as (Hd0 & Hd64 & WFd & _).
    pose proof (PIX_rd_res0 SEGS m pixs vs PXs Hx Hy) as Cres.
    eexists. split.
    - stepb_ft F_16504 D_16504 ltac:(condZ).
      stepb_ft F_16508 D_16508 ltac:(condZ).
      stepb_ft F_1650c D_1650c ltac:(condZ).
      guard8 F_16510 D_16510 ALs. stepb_ft F_16514 D_16514 ltac:(condZ).
      guard8 F_16518 D_16518 ALd. stepb_ft F_1651c D_1651c ltac:(condZ).
      stepLD F_16520 D_16520 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Cres) ltac:(apply lez8; lia).
      stepST F_16524 D_16524 (Z_to_bv 64 (pixd + 24)) (Z_to_bv 64 0) ltac:(sok_in SOKd).
      sn F_16528 D_16528.
      stepret F_1652c D_1652c ret ltac:(exact H1).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pixCopySpp_run : forall regs m (pixd pixs : Z) (vs vd : pixv) (ret : word),
    (1 <= pixs)%Z -> (1 <= pixd)%Z -> pixs <> pixd -> (pixs mod 8 = 0)%Z -> (pixd mod 8 = 0)%Z ->
    PIXat m pixs vs -> PIXat m pixd vd -> (1 <= p_spp vs)%Z ->
    store_ok SEGS m (Z_to_bv 64 pixd) 64 = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x16524 : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (pixd + 12)) (word_to_le_bytes 4 (Z_to_bv 64 (p_spp vs)))) rom)
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m pixd pixs vs vd ret Hps Hpd NE ALs ALd PXs PXd Hspp SOKd Hret H1 H10 H11.
    pose proof PXs as (Hs0 & Hs64 & WFs & _). pose proof PXd as (Hd0 & Hd64 & WFd & _). pose proof (wf_spp _ WFs) as Rspp.
    pose proof (PIX_rd_spp SEGS _ _ _ PXs) as Cspp.
    eexists. split.
    - stepb_ft F_16428 D_16428 ltac:(condZ).
      stepb_ft F_1642c D_1642c ltac:(condZ).
      stepb_ft F_16430 D_16430 ltac:(condZ).
      guard8 F_16434 D_16434 ALs. stepb_ft F_16438 D_16438 ltac:(condZ).
      stepLD F_1643c D_1643c (Z_to_le_bytes 4 (p_spp vs)) (Z_to_bv 64 (p_spp vs)) ltac:(addr_norm; exact Cspp) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_spp vs)) by lia.
      stepb_ft F_16440 D_16440 ltac:(condZ).
      guard8 F_16444 D_16444 ALd. stepb_ft F_16448 D_16448 ltac:(condZ).
      stepST F_1644c D_1644c (Z_to_bv 64 (pixd + 12)) (Z_to_bv 64 (p_spp vs)) ltac:(sok_in SOKd).
      sn F_16450 D_16450. sn F_164f8 D_164f8.
      stepret F_164fc D_164fc ret ltac:(exact H1).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Definition FR2 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)).

  (* [comment removed for export] *)
  Lemma pct_A : forall regs m (s pixs : Z) (ret : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 16)) 16 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x1623c : word) m rom) (mkst regs' (0x1630c : word) (FR2 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x16250 /\ getr regs' 10 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 2]%list) regs regs'.
  Proof.
    intros regs m s pixs ret Hs Hs64 Hp SOK H2 H1 H10. unfold FR2. eexists. split.
    - zv F_16140 D_16140 (Z_to_bv 64 (s - 16)).
      stepST F_16144 D_16144 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_16148 D_16148 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepb_ft F_1614c D_1614c ltac:(condZ).
      sn F_16150 D_16150.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pct_B : forall regs m (s pixd : Z) (vd : pixv),
    (1 <= pixd)%Z -> (pixd mod 16 = 0)%Z -> PIXat m pixd vd -> (0 <= p_wpl vd * p_h vd)%Z -> (4 * (p_wpl vd * p_h vd) < 2 ^ 31)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 16) -> getr regs 10 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x16250 : word) m rom) (mkst regs' (0x32740 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x1628c
      /\ getr regs' 10 = Z_to_bv 64 (p_data vd) /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (4 * (p_wpl vd * p_h vd))
      /\ getr regs' 8 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m s pixd vd Hp ALd PX Hwh Hsz H2 H10. pose proof PX as (Hp0 & Hp64 & WF & _).
    pose proof (wf_h _ WF) as Rh. pose proof (wf_wpl _ WF) as Rwpl. pose proof (wf_data _ WF) as Rdata.
    assert (ALd8 : (pixd mod 8 = 0)%Z) by (apply al16_mod8; exact ALd).
    assert (Hm4 : (0 <= 4 * p_wpl vd * p_h vd < 2 ^ 31)%Z) by nia.
    pose proof (PIX_rd_h SEGS _ _ _ PX) as Ch. pose proof (PIX_rd_wpl SEGS _ _ _ PX) as Cwpl. pose proof (PIX_rd_data SEGS _ _ _ PX) as Cdata.
    eexists. split.
    - stepb_ft F_16154 D_16154 ltac:(condZ).
      guard8 F_16158 D_16158 ALd8. stepb_ft F_1615c D_1615c ltac:(condZ).
      stepLD F_16160 D_16160 (Z_to_le_bytes 4 (p_wpl vd)) (Z_to_bv 64 (p_wpl vd)) ltac:(addr_norm; exact Cwpl) ltac:(apply lez4; lia).
      stepLD F_16164 D_16164 (Z_to_le_bytes 4 (p_h vd)) (Z_to_bv 64 (p_h vd)) ltac:(addr_norm; exact Ch) ltac:(apply lez4; lia).
      stepiv F_16168 D_16168 (Z_to_bv 64 (4 * p_wpl vd)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_1616c D_1616c. fixv (Z_to_bv 64 0) ltac:(apply v_mulh_small; lia).
      zv F_16170 D_16170 (Z_to_bv 64 (4 * (p_wpl vd * p_h vd))).
      sn F_16174 D_16174. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srai_small by lia; f_equal; apply Z.div_small; lia).
      stepb_ft F_16178 D_16178 ltac:(condZ).
      stepLD F_1617c D_1617c (Z_to_le_bytes 8 (p_data vd)) (Z_to_bv 64 (p_data vd)) ltac:(addr_norm; exact Cdata) ltac:(apply lez8; lia).
      sn F_16180 D_16180. sn F_16184 D_16184. sn F_16188 D_16188. sn F_1618c D_1618c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pct_C : forall regs m (s pixd : Z) (ret s0v : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    getr regs 2 = Z_to_bv 64 (s - 16) -> getr regs 8 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x1628c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10]%list) regs regs'.
  Proof.
    intros regs m s pixd ret s0v Hs Hs64 Hret R8 R16 H2 H8. eexists. split.
    - sn F_16190 D_16190. sn F_16194 D_16194.
      stepLD8 F_161fc D_161fc ret. stepLD8 F_16200 D_16200 s0v.
      zv F_16204 D_16204 (Z_to_bv 64 s). stepret F_16208 D_16208 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pct_F : forall regs m (s : Z) (ret s0v : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x33d90) 8 = Some (Z_to_le_bytes 8 0x34e00) -> rdn SEGS m (Z_to_bv 64 0x34e00) 4 = Some (Z_to_le_bytes 4 3) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    getr regs 2 = Z_to_bv 64 (s - 16) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x16250 : word) m rom) (mkst regs' (0x1586c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x1054a /\ getr regs' 11 = Z_to_bv 64 0x10f2c
      /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s ret s0v Hs Hs64 Rg Rs R8 R16 H2 H10. eexists. split.
    - stepb_tk F_16154 D_16154 ltac:(condZ).
      sn F_161c0 D_161c0.
      stepLD F_161c4 D_161c4 (Z_to_le_bytes 8 0x34e00) (Z_to_bv 64 0x34e00) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_161c8 D_161c8 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_161cc D_161cc. stepb_ft F_161d0 D_161d0 ltac:(condZ).
      sn F_161d4 D_161d4. sn F_161d8 D_161d8. sn F_161dc D_161dc. sn F_161e0 D_161e0.
      sn F_161e4 D_161e4.
      stepLD8 F_161e8 D_161e8 ret. stepLD8 F_161ec D_161ec s0v.
      zv F_161f0 D_161f0 (Z_to_bv 64 s). sn F_161f4 D_161f4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End Segs.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cells2 (m : word -> option byte) (s : Z) (ret s0v : word) : Prop :=
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v).
Lemma cells2_FR2 : forall m s ret regs, (16 <= s)%Z -> (s < 2 ^ 64)%Z -> cells2 (FR2 m s ret regs) s ret (getr regs 8).
Proof. intros m s ret regs Hs Hs64. unfold cells2, FR2. repeat split; rdn_solve. Qed.
Lemma cells2_frm : forall C s' m m' s ret s0v, Cok C -> FRM C s' m m' ->
  (s' <= s - 16)%Z -> (c_top C - LSTK <= s')%Z -> (s < 2 ^ 64)%Z -> cells2 m s ret s0v -> cells2 m' s ret s0v.
Proof.
  intros C s' m m' s ret s0v CK F Hs' Hlo Hs64 (R1 & R2). unfold cells2.
  rewrite !(FRM_rdn16 C s' m m' _ 8 CK F) by (cbn; lia). repeat split; assumption.
Qed.
Lemma cells2_out : forall m m' (lo hi s : Z) ret s0v,
  (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) -> (hi <= s - 16 \/ s <= lo)%Z -> (16 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells2 m s ret s0v -> cells2 m' s ret s0v.
Proof.
  intros m m' lo hi s ret s0v OUT Hhi Hs Hs64 (R1 & R2). unfold cells2.
  repeat split; (eapply (rdn_after m m' lo hi); [exact OUT | lia | cbn; lia | cbn; lia | assumption]).
Qed.

#[local] Definition ct_rest : list (bv 5) := [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Definition TKr (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s w h d : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z) : Prop :=
  forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd w h d cd data cv) ->
     aroom A' vm' (kR - RK_pixcopy) (bR - RB10_pixcopy (4 * (wpl_of w d * h))) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S.

(* [comment removed for export] *)
Lemma pct_tail_W : forall C A A1 m md m2 vm1 regs r2 (s pixd w h d cd data : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z),
  Cok C -> TKr C A m md regs s w h d cv ret S kR bR ->
  aroom A1 vm1 (kR - RK_pixcopy) (bR - RB10_pixcopy (4 * (wpl_of w d * h))) ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 16 <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  W C A1 m2 (with_vmmaps vm1 md) -> POSTM C A s m m2 ->
  cells2 m2 s ret (getr regs 8) ->
  getr r2 2 = Z_to_bv 64 (s - 16) -> getr r2 10 = Z_to_bv 64 pixd ->
  (forall x, In x ct_rest -> getr r2 x = getr regs x) -> getr regs 2 = Z_to_bv 64 s ->
  hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  pixt_new C A A1 m2 pixd w h d cd data cv ->
  realizes SEGS (mkCfg (mkst r2 (0x16250 : word) m2 al_rom) (with_vmmaps vm1 md)) S.
Proof.
  intros C A A1 m md m2 vm1 regs r2 s pixd w h d cd data cv ret S kR bR CK HK Hrm1 Hs16 Hlo Hhi Hret HWa PMa' CE2 E2 Hres RR H2 HOK Hw Hh PT.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  set (n := (4 * (wpl_of w d * h))%Z) in *. assert (En : n = (4 * (wpl_of w d * h))%Z) by reflexivity.
  assert (Hn1 : (1 <= n)%Z) by (rewrite En; nia).
  pose proof PT as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & PXd & CMR). rewrite <- En in TOPd, L1d.
  assert (SUBa : sub_live A A1).
  { intros q k Lq. destruct CMR as [[_ LEQ] | (ad & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LAcd & LAad & _ & _ & _ & _ & _ & LEQ)].
    - rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence].
    - rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence | intros ->; congruence | intros ->; congruence]. }
  destruct (pct_B al_rom r2 m2 s pixd (hdv w h d cd data) ltac:(lia) ALp PXd ltac:(cbn; lia) ltac:(cbn; lia) E2 Hres)
    as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & AG3). cbn [p_data p_wpl p_h hdv] in V10, V12. rewrite <- En in V12.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  (* [comment removed for export] *)
  pose proof (blk_sok C A1 m2 _ data n CK HWa L1d ltac:(lia) ltac:(lia) ltac:(lia)) as SOKd.
  destruct (memset_spec r3 m2 al_rom data n (Z_to_bv 64 0x1628c) ltac:(lia) ltac:(lia) ltac:(lia) SOKd ltac:(red; apply bv_eq; reflexivity) V1 V10 V11 V12)
    as (r4 & RUN4 & W10 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN4 |].
  replace (Z_to_bv 64 0x1628c) with (0x1628c : word) by (apply bv_eq; reflexivity).
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
  assert (NEpdw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
  assert (PXd5 : PIXat M5 pixd (hdv w h d cd data)) by (apply (PIXat_frame m2); [exact PXd | intros x Hx; exact (EQ5 pixd 64%Z x L1p NEpdw ltac:(lia) ltac:(lia) Hx)]).
  assert (CE5 : cells2 M5 s ret (getr regs 8)).
  { destruct CE2 as (C1 & C2). unfold cells2.
    repeat split; (etransitivity; [apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia | intros x Hx; apply OUT5; rewrite u_Z2bv in Hx by lia; cbn in Hx; lia] | eassumption]). }
  destruct CE5 as (C1 & C2).
  destruct (pct_C al_rom r4 M5 s pixd ret _ ltac:(lia) ltac:(lia) Hret C1 C2 ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r5 & RUN5 & Z2 & Z1 & Z10 & Z8 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN5 |].
  apply (HK A1 M5 vm1 r5 HW5).
  - apply cs_kept_intro; csr; try reflexivity. all: unfold ct_rest in RR; csr; reflexivity.
  - exact PM5.
  - exists pixd, cd, data. split; [exact Z10|].
    unfold pixt_new. rewrite <- En. do 13 (split; [assumption|]). split; [exact PXd5|].
    destruct CMR as [[CD0 LEQ] | (ad & CMOKc & Gcd & TOPcd & Gad & TOPad & NEcdad & NEcdp & NEcdd & NEadp & NEadd & LAcd & LAad & L00cd & L00ad & L2cd & L2ad & CM4 & LEQ)]; [left; split; [exact CD0 | exact LEQ] | right].
    exists ad. do 16 (split; [assumption|]). split; [| exact LEQ].
    assert (NEw1 : Z_to_bv 64 cd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
    apply (CMAPat_frame m2); [exact CM4|]. intros x Hx. exact (EQ5 cd 24%Z x L2cd NEw1 ltac:(lia) ltac:(lia) Hx).
  - exact Hrm1.
Qed.

(* [comment removed for export] *)
Theorem pixCreateTemplate_W : forall C A m md regs (s pixs w h d cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PCT_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 ->
  getr regs 10 = Z_to_bv 64 pixs ->
  PIXat m pixs (hdv w h d cm datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> (RB10_pixcopy (4 * (wpl_of w d * h)) <= bR)%Z ->
  TKt C A m md regs s w h d cv ret S kR bR ->
  realizes SEGS (mkCfg (mkst regs (0x1623c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs w h d cm datas cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 PXs HOK Hw Hh Lps HCM kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold PCT_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  destruct (pct_A al_rom regs m s pixs ret ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR2 m s ret regs) md /\ POSTM C A s m (FR2 m s ret regs)) by (unfold FR2; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR2 m s ret regs) in *.
  pose proof (cells2_FR2 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 16 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold FR2. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PXs1 : PIXat M1 pixs (hdv w h d cm datas)) by (apply (PIXat_frame m); [exact PXs | intros x Hx; apply OUT1; lia]).
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x45480) by (csr; reflexivity).
  assert (HCM1 : cm = 0%Z \/ (CMAPat M1 cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right]. split; [| split; [exact CMOK | split; [exact Lcm | exact Larr]]].
    pose proof CM as (Hc0 & Hc64 & _). destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
    apply (CMAPat_frame m); [exact CM|]. intros x Hx. apply OUT1. lia. }
  apply (pixCreateTemplateNoInit_T C A M1 md r1 (s - 16) pixs w h d cm datas cv (Z_to_bv 64 0x16250) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 PXs1 HOK Hw Hh Lps HCM1 kR bR Hrm Hrk Hrb).
  unfold TKt. intros A1 m2 vm1 r2 HWa CSa PMa OUTa Hrm1.
  replace (Z_to_bv 64 0x16250) with (0x16250 : word) by (apply bv_eq; reflexivity).
  pose proof (cells2_frm C (s - 16) M1 m2 s _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (PMa' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  destruct OUTa as [[Hres0 LIVEQ] | (pixd & cd & data & Hres & PT)].
  - (* [comment removed for export] *)
    destruct CE2 as (C1 & C2).
    destruct (pct_F al_rom r2 m2 s ret _ ltac:(lia) ltac:(lia) (W_sev_got C A1 m2 _ HWa) (W_sev C A1 m2 _ HWa) C1 C2 ltac:(csr; reflexivity) Hres0)
      as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    apply (returnErrorPtr_W C A1 m2 _ r3 s 0x1054a 0x10f2c 13 17 ret (Z_to_bv 64 0) S CK HWa V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
             V10 V11 V12 str_msg_pixd str_pixCreateTemplate).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    apply (HK A1 m4 vm1 r5).
    + exact HW4.
    + apply cs_kept_intro; csr; try reflexivity.
    + eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ|].
      eapply (POSTM_range C A1 m2 _ m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
    + left. split; [exact A10 | exact LIVEQ].
    + exact Hrm1.
  - apply (pct_tail_W C A A1 m md m2 vm1 regs r2 s pixd w h d cd data cv ret S kR bR CK
             (fun A' m' vm' regs' X1 X2 X3 X4 X5 => HK A' m' vm' regs' X1 X2 X3 (or_intror X4) X5)
             Hrm1 Hs16 ltac:(lia) Hhi Hret HWa PMa' CE2 ltac:(csr; reflexivity) Hres ltac:(unfold ct_rest; rest_solve) H2 HOK Hw Hh PT).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem pixDestroy_keep_W : forall C A m md regs (s pp pix cm karr R : Z) (v : pixv) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 -> (pp mod 8 = 0)%Z ->
  getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
  PIXat m pix v -> p_rc v = 1%Z -> p_text v = 0%Z -> p_cmap v = cm ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  live A (Z_to_bv 64 (p_data v)) = Some R -> live (c_A0 C) (Z_to_bv 64 (p_data v)) = None -> (0 < R)%Z -> p_data v <> pix ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some karr /\
                live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
                cm <> c_arr cv /\ cm <> pix /\ c_arr cv <> pix /\ p_data v <> cm /\ p_data v <> c_arr cv /\ (0 < karr)%Z)) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     pixd_post A A' pix (p_data v) cm (c_arr cv) ->
     POSTM C A' (pp + 8) m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     (forall a : word, (s <= u a < pp)%Z -> m' a = m a) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x1615c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp pix cm karr R v cv ret S CK HW H2 Hs16 Hlo Hpp Hpphi H1 Hret H4 ALpp H10 Rpp PX Hrc Ht Hc Lp L0p LR LR0 HR NEdp HCM HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ALLOC_STACK in Hlo.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rd.
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A m md (Z_to_bv 64 (p_data v)) R CK HW LR HR) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (Hs32 : (32 <= s)%Z) by lia. assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  assert (SOKp : store_ok SEGS m (Z_to_bv 64 pix) 64 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m pix v x PX ltac:(lia) E). }
  destruct (PxdSegs.pxd_A al_rom regs m s pp pix v ret ltac:(lia) Hpp ltac:(lia) ALp ALpp (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia))
              SOKp Rpp PX Hrc ltac:(lia) Gp H2 H1 H10) as (r1 & RUN1 & Q2 & Q8 & Q9 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. clear RUN1.
  set (M0 := wbytes (wbytes (wbytes m _ _) _ _) _ _).
  set (M1 := wbytes M0 _ _).
  assert (WP0 : W C A M0 md /\ POSTM C A s m M0) by (subst M0; wp_win CK).
  destruct WP0 as [HW0 PM0].
  assert (HW1 : W C A M1 md).
  { subst M1. apply (W_store_blk C A M0 md (Z_to_bv 64 pix) _ 64 _ CK HW0 Lp L0p); [rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
  assert (F1 : FRM C s m M1).
  { eapply FRM_trans; [exact (proj1 PM0)|]. subst M1.
    refine (proj1 (POSTM_blk C (c_A0 C) A M0 md (Z_to_bv 64 pix) _ 64 _ s CK HW0 Lp L0p (W_sub0 _ _ _ _ HW0) _ _));
      [rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
  assert (K1 : forall q k i, live A q = Some k -> q <> Z_to_bv 64 pix -> (0 <= i < k)%Z -> M1 (at_ q i) = m (at_ q i)).
  { intros q k i Lq NEq Hi. rewrite <- (proj2 PM0 q k i Lq Hi). subst M1.
    pose proof (blk_apart C A m md _ _ _ _ CK HW Lq Lp NEq ltac:(lia) ltac:(lia)) as D. rewrite u_Z2bv in D by lia.
    destruct (blk_range C A m md q k CK HW Lq ltac:(lia)) as [Gq TOPq].
    apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; [cbn; lia|]. unfold at_. pose proof (u64_range q). rewrite u_Z2bv by lia. cbn. lia. }
  assert (PX1 : PIXat M1 pix (set_rc v 0)).
  { subst M1. apply PIX_wr_rc; [|lia]. subst M0.
    repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  assert (R8 : rdn SEGS M1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)) by (subst M1 M0; rdn_solve).
  assert (R16 : rdn SEGS M1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))) by (subst M1 M0; rdn_solve).
  assert (R24 : rdn SEGS M1 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))) by (subst M1 M0; rdn_solve).
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x45480) by (csr; reflexivity).
  assert (ER1 : forall r, In r cs_rest -> getr r1 r = getr regs r).
  { intros r Hr. apply AG1. cbn [In cs_rest] in Hr. repeat (destruct Hr as [<-|Hr]; [notin_lit|]). destruct Hr. }
  (* [comment removed for export] *)
  assert (FIN : forall Ax Mx vmx rx, W C Ax Mx (with_vmmaps vmx md) ->
            getr rx 2 = Z_to_bv 64 (s - 32) -> getr rx 8 = Z_to_bv 64 pix -> getr rx 9 = Z_to_bv 64 pp -> getr rx 4 = Z_to_bv 64 0x45480 ->
            (forall r, In r cs_rest -> getr rx r = getr regs r) ->
            live Ax (Z_to_bv 64 pix) = Some 64%Z -> live Ax (Z_to_bv 64 (p_data v)) = None ->
            (cm <> 0%Z -> live Ax (Z_to_bv 64 cm) = None /\ live Ax (Z_to_bv 64 (c_arr cv)) = None) ->
            (forall q, q <> Z_to_bv 64 (p_data v) -> (cm <> 0%Z -> q <> Z_to_bv 64 cm /\ q <> Z_to_bv 64 (c_arr cv)) -> live Ax q = live A q) ->
            FRM C s m Mx ->
            (forall q k i, live Ax q = Some k -> q <> Z_to_bv 64 pix -> (0 <= i < k)%Z -> Mx (at_ q i) = m (at_ q i)) ->
            rdn SEGS Mx (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
            rdn SEGS Mx (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) ->
            rdn SEGS Mx (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) ->
            roomtr A (m_vmmaps md) Ax vmx 0 0 ->
            realizes SEGS (mkCfg (mkst rx (0x161d8 : word) Mx al_rom) (with_vmmaps vmx md)) S).
  { intros Ax Mx vmx rx HWx X2 X8 X9 X4 XR Lpx Ldx Lcx LEQx Fx Kx C8 C16 C24 RTx.
    destruct (PxdSegs.pxd_D al_rom rx Mx pix X8) as (r5 & RUN5 & Y10 & Y1 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWx)) | exact (mp_lazy _ (w_pure _ _ _ _ HWx)) | exact RUN5 |]. clear RUN5.
    assert (Y4 : getr r5 4 = Z_to_bv 64 0x45480) by (csr; reflexivity).
    assert (Y2 : getr r5 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    replace (0x2b208 : word) with (Z_to_bv 64 0x2b208) by (apply bv_eq; reflexivity).
    apply (W_free16 C Ax Mx _ r5 (Z_to_bv 64 pix) (Z_to_bv 64 0x161e0) 64 (s - 32) S CK HWx Y10 Lpx L0p Y1
             ltac:(red; apply bv_eq; reflexivity) Y4 Y2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A2 m2 vm2 r6 HWb CSb Lb LEQb PMb HRTb. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWb.
    replace (Z_to_bv 64 0x161e0) with (0x161e0 : word) by (apply bv_eq; reflexivity).
    assert (Z2 : getr r6 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (Z9 : getr r6 9 = Z_to_bv 64 pp) by (csr; reflexivity).
    assert (FR12 : FRM C s m m2) by (eapply FRM_trans; [exact Fx | eapply FRM_mono; [exact (proj1 PMb) | lia]]).
    destruct (PxdSegs.pxd_E al_rom r6 m2 s pp ret (getr regs 8) (getr regs 9) ltac:(lia) Hpp ltac:(lia) Hret) as (r7 & RUN7 & V2 & V1 & V8 & V9 & AG7).
    { apply (W_sok_win C A2 m2 _ pp 8 CK HWb); [lia | cbn; lia]. }
    { rewrite (FRM_rdn16 C (s - 32) Mx m2 (s - 8) 8 CK (proj1 PMb)) by (cbn; lia). exact C8. }
    { rewrite (FRM_rdn16 C (s - 32) Mx m2 (s - 16) 8 CK (proj1 PMb)) by (cbn; lia). exact C16. }
    { rewrite (FRM_rdn16 C (s - 32) Mx m2 (s - 24) 8 CK (proj1 PMb)) by (cbn; lia). exact C24. }
    { exact Z2. } { exact Z9. }
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN7 |]. clear RUN7.
    set (M3 := wbytes m2 _ _).
    assert (WP3 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C A2 (pp + 8) m2 M3) by (subst M3; wp_win CK).
    destruct WP3 as [HW3 PM3].
    assert (NEpd : Z_to_bv 64 pix <> Z_to_bv 64 (p_data v)) by (apply zneq_w; lia).
    assert (NEdp' : Z_to_bv 64 (p_data v) <> Z_to_bv 64 pix) by (intros E; apply NEpd; rewrite E; reflexivity).
    apply (HK A2 M3 vm2 r7 HW3).
    - apply cs_kept_of_rest; [rewrite V2, H2; reflexivity | exact V8 | exact V9 |].
      intros r Hr. rewrite (AG7 r) by (cbn [In cs_rest] in Hr; repeat (destruct Hr as [<-|Hr]; [notin_lit|]); destruct Hr).
      rewrite (cs_rest_of_kept _ _ CSb r Hr). rewrite (AG5 r) by (cbn [In cs_rest] in Hr; repeat (destruct Hr as [<-|Hr]; [notin_lit|]); destruct Hr).
      exact (XR r Hr).
    - unfold pixd_post. split; [exact Lb|]. split; [intros _; rewrite (LEQb _ NEdp'); exact Ldx|]. split.
      + intros NC. destruct (Lcx NC) as [E1 E2]. destruct HCM as [X|(CM & _ & _ & _ & _ & _ & NE2 & NE3 & _)]; [exfalso; exact (NC X)|].
        pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_arr _ CWF).
        split; [rewrite (LEQb _ (zneq_w cm pix ltac:(lia) ltac:(lia) NE2)); exact E1 | rewrite (LEQb _ (zneq_w (c_arr cv) pix ltac:(lia) ltac:(lia) NE3)); exact E2].
      + intros q N1 N2 N3. rewrite (LEQb q N1). apply LEQx; [apply N2; lia | exact N3].
    - split; [eapply FRM_trans; [eapply FRM_mono; [exact FR12 | lia] | exact (proj1 PM3)]|].
      intros q k i Lq Hi.
      assert (N1 : q <> Z_to_bv 64 pix) by (intros ->; congruence).
      assert (Lqx : live Ax q = Some k) by (rewrite <- (LEQb q N1); exact Lq).
      rewrite (proj2 PM3 q k i Lq Hi). rewrite (proj2 PMb q k i Lq Hi). exact (Kx q k i Lqx N1 Hi).
    - subst M3. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
    - intros a Ha. subst M3. rewrite (wbytes_out_Z _ _ 8); [| rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia].
      destruct (win_facts C a CK ltac:(unfold win; lia)) as (_ & Ga & N2 & N3 & N4 & _).
      apply FR12; try assumption; [intros [_ X]; lia | unfold scratch; lia].
    - room_tac. }
  (* [comment removed for export] *)
  destruct (PxdSegs.pxd_B1 al_rom r1 M1 (p_data v) ltac:(lia) ltac:(lia) (W_pmm_free C A M1 md HW1) Q10) as (r2 & RUN2 & P10 & P1 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |]. clear RUN2.
  assert (P4 : getr r2 4 = Z_to_bv 64 0x45480) by (csr; reflexivity).
  assert (P2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  replace (0x2b208 : word) with (Z_to_bv 64 0x2b208) by (apply bv_eq; reflexivity).
  apply (W_free16 C A M1 md r2 (Z_to_bv 64 (p_data v)) (Z_to_bv 64 0x161b4) R (s - 32) S CK HW1 P10 LR LR0 P1
           ltac:(red; apply bv_eq; reflexivity) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r3 HWa CSa La LEQa PMa HRTa.
  replace (Z_to_bv 64 0x161b4) with (0x161b4 : word) by (apply bv_eq; reflexivity).
  assert (NEpd : Z_to_bv 64 pix <> Z_to_bv 64 (p_data v)) by (apply zneq_w; lia).
  assert (Lp1 : live A1 (Z_to_bv 64 pix) = Some 64%Z) by (rewrite (LEQa _ NEpd); exact Lp).
  assert (PXa : PIXat m1 pix (set_rc v 0)).
  { apply (PIXat_frame M1); [exact PX1|]. intros x Hx. pose proof (proj2 PMa (Z_to_bv 64 pix) 64%Z (u x - pix)%Z Lp1 ltac:(lia)) as E.
    unfold at_ in E. rewrite u_Z2bv in E by lia. replace (pix + (u x - pix))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E. }
  assert (E2 : getr r3 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E8 : getr r3 8 = Z_to_bv 64 pix) by (csr; reflexivity).
  assert (E9 : getr r3 9 = Z_to_bv 64 pp) by (csr; reflexivity).
  assert (E4 : getr r3 4 = Z_to_bv 64 0x45480) by (csr; reflexivity).
  assert (ER3 : forall r, In r cs_rest -> getr r3 r = getr regs r).
  { intros r Hr. rewrite (cs_rest_of_kept _ _ CSa r Hr). rewrite (AG2 r) by (cbn [In cs_rest] in Hr; repeat (destruct Hr as [<-|Hr]; [notin_lit|]); destruct Hr). exact (ER1 r Hr). }
  assert (K1a : forall q k i, live A1 q = Some k -> q <> Z_to_bv 64 pix -> (0 <= i < k)%Z -> m1 (at_ q i) = m (at_ q i)).
  { intros q k i Lq NEq Hi. rewrite (proj2 PMa q k i Lq Hi). apply (K1 q k i); [| exact NEq | exact Hi].
    rewrite <- (LEQa q); [exact Lq | intros ->; congruence]. }
  assert (F1a : FRM C s m m1) by (eapply FRM_trans; [exact F1 | eapply FRM_mono; [exact (proj1 PMa) | lia]]).
  destruct HCM as [Hcm0 | (CM & Lcm & Larr & L0cm & L0arr & NE1 & NE2 & NE3 & NEdc & NEda & Hk)].
  - (* [comment removed for export] *)
    destruct (PxdSegs.pxd_C0 al_rom r3 m1 s pix (set_rc v 0) ltac:(lia) ltac:(lia) PXa ltac:(cbn; exact Ht) ltac:(cbn; rewrite Hc; exact Hcm0)
                (W_sok_win C A1 m1 _ (s - 32) 32 CK HWa ltac:(lia) ltac:(cbn; lia)) ltac:(lia) E2 E8) as (r4 & RUN4 & X2 & X8 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN4 |]. clear RUN4.
    set (M2 := wbytes m1 _ _).
    assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A1 s m1 M2) by (subst M2; wp_win CK).
    destruct WP2 as [HW2 PM2].
    apply (FIN A1 M2 vm1 r4 HW2 X2 X8 ltac:(csr; reflexivity) ltac:(csr; reflexivity)).
    + intros r Hr. rewrite (AG4 r) by (cbn [In cs_rest] in Hr; repeat (destruct Hr as [<-|Hr]; [notin_lit|]); destruct Hr). exact (ER3 r Hr).
    + exact Lp1.
    + exact La.
    + intros NC. exfalso. exact (NC Hcm0).
    + intros q N1 _. exact (LEQa q N1).
    + eapply FRM_trans; [exact F1a | exact (proj1 PM2)].
    + intros q k i Lq NEq Hi. rewrite (proj2 PM2 q k i Lq Hi). exact (K1a q k i Lq NEq Hi).
    + subst M2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). exact R8.
    + subst M2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). exact R16.
    + subst M2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia). exact R24.
    + room_tac.
  - (* [comment removed for export] *)
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_arr _ CWF) as Rarr.
    destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia.
    assert (NEcd : Z_to_bv 64 cm <> Z_to_bv 64 (p_data v)) by (apply zneq_w; lia).
    assert (NEad : Z_to_bv 64 (c_arr cv) <> Z_to_bv 64 (p_data v)) by (apply zneq_w; lia).
    assert (NEcp : Z_to_bv 64 cm <> Z_to_bv 64 pix) by (apply zneq_w; lia).
    assert (NEap : Z_to_bv 64 (c_arr cv) <> Z_to_bv 64 pix) by (apply zneq_w; lia).
    assert (Lcm1 : live A1 (Z_to_bv 64 cm) = Some 24%Z) by (rewrite (LEQa _ NEcd); exact Lcm).
    assert (Larr1 : live A1 (Z_to_bv 64 (c_arr cv)) = Some karr) by (rewrite (LEQa _ NEad); exact Larr).
    assert (CMa : CMAPat m1 cm cv).
    { apply (CMAPat_frame m); [exact CM|]. intros x Hx.
      pose proof (K1a (Z_to_bv 64 cm) 24%Z (u x - cm)%Z Lcm1 NEcp ltac:(lia)) as E.
      unfold at_ in E. rewrite u_Z2bv in E by lia. replace (cm + (u x - cm))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E. }
    destruct (PxdSegs.pxd_C1 al_rom r3 m1 s pix cm (set_rc v 0) ltac:(lia) ltac:(lia) PXa ltac:(cbn; exact Ht) ltac:(cbn; exact Hc) ltac:(lia)
                (W_sok_win C A1 m1 _ (s - 32) 32 CK HWa ltac:(lia) ltac:(cbn; lia)) ltac:(lia) E2 E8) as (r4 & RUN4 & X2 & X10 & X1 & X8 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN4 |]. clear RUN4.
    set (M2 := wbytes m1 _ _).
    assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A1 s m1 M2) by (subst M2; wp_win CK).
    destruct WP2 as [HW2 PM2].
    assert (CM2 : CMAPat M2 cm cv).
    { subst M2. apply (CMAPat_out m1 cm cv); [exact CMa | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
    assert (X4 : getr r4 4 = Z_to_bv 64 0x45480) by (csr; reflexivity).
    apply (pixcmapDestroy_W C A1 M2 _ r4 (s - 32) (s - 32) cm cv karr (Z_to_bv 64 0x161d4) S CK HW2 X2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) X1
             ltac:(red; apply bv_eq; reflexivity) X4 ltac:(replace (s - 32)%Z with (s + (-32))%Z by lia; apply mod16_plus_mod8; [exact Hs16 | reflexivity]) X10).
    { subst M2. rewrite <- (w2b_Z 8 cm) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. }
    { exact CM2. } { exact Lcm1. } { exact Larr1. } { exact L0cm. } { exact L0arr. } { exact NE1. }
    intros A1c m1c vm1c r5 HWc CSc Lc1 Lc2 LEQc PMc _ HRTc. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWc.
    replace (Z_to_bv 64 0x161d4) with (0x161d4 : word) by (apply bv_eq; reflexivity).
    assert (Lp1c : live A1c (Z_to_bv 64 pix) = Some 64%Z).
    { rewrite (LEQc _ (fun E => NEcp (eq_sym E)) (fun E => NEap (eq_sym E))). exact Lp1. }
    assert (Y8 : getr r5 8 = Z_to_bv 64 pix) by (csr; reflexivity).
    assert (SOKp1 : store_ok SEGS m1c (Z_to_bv 64 pix) 64 = true).
    { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m1c x) eqn:E; [discriminate|]. exfalso.
      exact (proj1 (proj2 (blk_byte C A1c m1c _ (Z_to_bv 64 pix) 64 x CK HWc Lp1c ltac:(rewrite u_Z2bv by lia; lia))) E). }
    pose proof (PxdSegs.pxd_C2 al_rom r5 m1c pix ltac:(lia) ltac:(lia) SOKp1 Y8) as RUN6.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWc)) | exact (mp_lazy _ (w_pure _ _ _ _ HWc)) | exact RUN6 |]. clear RUN6.
    set (M2d := wbytes m1c _ _).
    assert (HW2d : W C A1c M2d (with_vmmaps vm1c md)).
    { subst M2d. apply (W_store_blk C A1c m1c _ (Z_to_bv 64 pix) _ 64 _ CK HWc Lp1c L0p); [rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
    assert (F2d : FRM C s m1c M2d).
    { subst M2d. refine (proj1 (POSTM_blk C (c_A0 C) A1c m1c _ (Z_to_bv 64 pix) _ 64 _ s CK HWc Lp1c L0p (W_sub0 _ _ _ _ HWc) _ _));
        [rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
    apply (FIN A1c M2d vm1c r5 HW2d ltac:(csr; reflexivity) Y8 ltac:(csr; reflexivity) ltac:(csr; reflexivity)).
    + intros r Hr. rewrite (cs_rest_of_kept _ _ CSc r Hr). rewrite (AG4 r) by (cbn [In cs_rest] in Hr; repeat (destruct Hr as [<-|Hr]; [notin_lit|]); destruct Hr). exact (ER3 r Hr).
    + exact Lp1c.
    + rewrite (LEQc _ (fun E => NEcd (eq_sym E)) (fun E => NEad (eq_sym E))). exact La.
    + intros _. split; [exact Lc1 | exact Lc2].
    + intros q N1 N2. destruct (N2 ltac:(lia)) as [N3 N4]. rewrite (LEQc q N3 N4). exact (LEQa q N1).
    + eapply FRM_trans; [exact F1a|]. eapply FRM_trans; [exact (proj1 PM2)|]. eapply FRM_trans; [eapply FRM_mono; [exact (proj1 PMc) | lia] | exact F2d].
    + intros q k i Lq NEq Hi.
      assert (N3 : q <> Z_to_bv 64 cm) by (intros ->; congruence). assert (N4 : q <> Z_to_bv 64 (c_arr cv)) by (intros ->; congruence).
      assert (Lq1 : live A1 q = Some k) by (rewrite <- (LEQc q N3 N4); exact Lq).
      transitivity (m1c (at_ q i)).
      { subst M2d. pose proof (blk_apart C A1c m1c _ _ _ _ _ CK HWc Lq Lp1c NEq ltac:(lia) ltac:(lia)) as D. rewrite u_Z2bv in D by lia.
        destruct (blk_range C A1c m1c _ q k CK HWc Lq ltac:(lia)) as [Gq TOPq].
        apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; [cbn; lia|]. unfold at_. pose proof (u64_range q). rewrite u_Z2bv by lia. cbn. lia. }
      rewrite (proj2 PMc q k i Lq Hi). rewrite (proj2 PM2 q k i Lq1 Hi). exact (K1a q k i Lq1 NEq Hi).
    + subst M2d. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 32 + 8) M2 m1c (s - 8) 8 CK (proj1 PMc)) by (cbn; lia). subst M2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). exact R8.
    + subst M2d. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 32 + 8) M2 m1c (s - 16) 8 CK (proj1 PMc)) by (cbn; lia). subst M2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). exact R16.
    + subst M2d. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 32 + 8) M2 m1c (s - 24) 8 CK (proj1 PMc)) by (cbn; lia). subst M2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia). exact R24.
    + room_tac.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pix_fresh (C : lctx) (A A' : AS) (m' : word -> option byte) (pixd w h d data : Z) : Prop :=
  (4096 <= pixd)%Z /\ (pixd + 64 <= alloc_top (c_vm C))%Z /\ (pixd mod 16 = 0)%Z /\
  (4096 <= data)%Z /\ (data + 4 * (wpl_of w d * h) <= alloc_top (c_vm C))%Z /\ (data mod 16 = 0)%Z /\ pixd <> data /\
  live A (Z_to_bv 64 pixd) = None /\ live A (Z_to_bv 64 data) = None /\
  live (c_A0 C) (Z_to_bv 64 pixd) = None /\ live (c_A0 C) (Z_to_bv 64 data) = None /\
  live A' (Z_to_bv 64 pixd) = Some 64%Z /\ live A' (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z /\
  (forall q, q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 data -> live A' q = live A q) /\
  PIXat m' pixd (hdv w h d 0 data).

Lemma pixt_new_fresh : forall C A A' m' pixd w h d data cv, pixt_new C A A' m' pixd w h d 0 data cv -> pix_fresh C A A' m' pixd w h d data.
Proof.
  intros C A A' m' pixd w h d data cv (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & PXd & CMR).
  unfold pix_fresh. repeat (split; [assumption|]). split; [| exact PXd].
  destruct CMR as [[_ LEQ] | (ad & _ & G & _)]; [exact LEQ | exfalso; lia].
Qed.

Lemma pix_fresh_sub : forall C A A' m' pixd w h d data, pix_fresh C A A' m' pixd w h d data -> sub_live A A'.
Proof.
  intros C A A' m' pixd w h d data (_ & _ & _ & _ & _ & _ & _ & L0p & L0d & _ & _ & L1p & L1d & LEQ & _).
  exact (sub_live_new2 A A' _ _ _ _ L0p L0d L1p L1d LEQ).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cm_facts (A : AS) (m : word -> option byte) (cm : Z) (cv : cmapv) : Prop :=
  cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z).

Definition pixAddBorderGeneral_contract : Prop :=
  forall C A m md regs (s pixs w h d cm datas left right top bot val : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ABG_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 left -> getr regs 12 = Z_to_bv 64 right ->
  getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot -> getr regs 15 = Z_to_bv 64 val ->
  PIXat m pixs (hdv w h d cm datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z -> (d = 1 \/ d = 8)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z -> cm_facts A m cm cv ->
  (1 <= left <= 64)%Z -> (1 <= right <= 64)%Z -> (1 <= top <= 64)%Z -> (1 <= bot <= 64)%Z -> ((left * d) mod 32 = 0)%Z ->
  (val = 0 \/ val = 2 ^ d - 1)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> (RB10_pixcopy (4 * (wpl_of (w + left + right) d * (h + top + bot))) <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ hdr_ok (w + left + right) (h + top + bot) d /\
                                pixt_new C A A' m' pixd (w + left + right) (h + top + bot) d cd data cv) ) ->
     aroom A' vm' (kR - RK_pixcopy) (bR - RB10_pixcopy (4 * (wpl_of (w + left + right) d * (h + top + bot)))) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixAddBorderGeneral) m al_rom) md) S.

Definition pixRemoveBorderGeneral_contract : Prop :=
  forall C A m md regs (s pixs w h d cm datas left right top bot : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + RBG_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 left -> getr regs 12 = Z_to_bv 64 right ->
  getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot ->
  PIXat m pixs (hdv w h d cm datas) -> hdr_ok w h d -> (d = 1 \/ d = 8)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z -> cm_facts A m cm cv ->
  (1 <= left <= 64)%Z -> (1 <= right <= 64)%Z -> (1 <= top <= 64)%Z -> (1 <= bot <= 64)%Z -> ((left * d) mod 32 = 0)%Z ->
  (1 <= w - left - right)%Z -> (1 <= h - top - bot)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> (RB10_pixcopy (4 * (wpl_of (w - left - right) d * (h - top - bot))) <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ hdr_ok (w - left - right) (h - top - bot) d /\
                                pixt_new C A A' m' pixd (w - left - right) (h - top - bot) d cd data cv) ) ->
     aroom A' vm' (kR - RK_pixcopy) (bR - RB10_pixcopy (4 * (wpl_of (w - left - right) d * (h - top - bot)))) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixRemoveBorderGeneral) m al_rom) md) S.

(* [comment removed for export] *)
Definition pixRemoveBorderGeneral_null_contract : Prop :=
  forall C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + RBG_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 0 ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixRemoveBorderGeneral) m al_rom) md) S.

End GrayA.
