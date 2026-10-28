(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import RelocKitVL RelocTacVL CanonImgVL RCodeVL_237d4_24000.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require Import MuslTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import RelocImg CanonImg.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require Import RelocRW RelocPF.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica.VL Require Import LeptStderr LeptBase LeptErr LeptCmap.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac zval ::= rl_zval.      (* [comment removed for export] *)
#[local] Ltac condZ ::= rl_condZ.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section PixDestroy.
Context {fx : FPState} {RLOC : Reloc} {RCODE : RelocCode RLOC} {RSITES : RelocSites RLOC} {RCODEF : RelocCodeVL RLOC} {RSITESF : RelocSitesVL RLOC} {RLEPT : RelocLept RLOC} {RIMGF : RelocImgVL RLOC} {RDATA : RelocData RLOC} {RIMG : RelocImg RLOC} {RRW : RelocRW RLOC RDATA} {RPF : RelocPF RLOC} {RENV : RelocLeptEnvVL RLOC} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLG} {P16 : PinsG}.
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
      msteps SEGS (mkst regs (rl dVL_23d30 0x23d30) m rom)
                  (mkst regs' (rl dVL_23d30 0x23d78)
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
    - zv F_23d30 D_23d30 (Z_to_bv 64 (s - 32)).
      stepST F_23d34 D_23d34 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_23d38 D_23d38 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_23d3c D_23d3c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_23d40 D_23d40 ltac:(condZ).
      stepiv F_23d44 D_23d44 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite ALp; reflexivity).
      stepb_ft F_23d48 D_23d48 ltac:(condZ).
      stepLD F_23d4c D_23d4c (Z_to_le_bytes 8 pix) (Z_to_bv 64 pix) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
      stepb_ft F_23d50 D_23d50 ltac:(condZ).
      stepiv F_23d54 D_23d54 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite AL8; reflexivity).
      stepb_ft F_23d58 D_23d58 ltac:(condZ).
      zv F_23d5c D_23d5c (Z_to_bv 64 (pix + 20)).
      sn F_23d60 D_23d60.
      chain_step;
        [ reflexivity
        | eapply (step_amoadd_w SEGS _ _ _ rom _ _ _ _ _ _ (Z_to_le_bytes 4 1) (Z_to_bv 64 1) F_23d64 eq_refl D_23d64);
          [ gres; rewrite u_Z2bv by lia; apply mod16_plus_mod4; [exact Hal | reflexivity]
          | gres; repeat rdn_peel1; rewrite <- RC; exact (PIX_rd_rc SEGS _ _ _ PX)
          | apply lez4; lia
          | gres; sok_in SOKp ]
        | step_simpl ].
      gres. rewrite zbv_add. replace (Z_to_bv 64 (1 + 18446744073709551615)%Z) with (Z_to_bv 64 0) by (apply bv_eq; rl_vmc_VL).
      rewrite (v_lw_small 1) by lia.
      sn F_23d68 D_23d68.
      stepb_ft F_23d6c D_23d6c ltac:(condZ).
      sn F_23d70 D_23d70.
      stepLD F_23d74 D_23d74 (Z_to_le_bytes 8 (p_data v)) (Z_to_bv 64 (p_data v))
        ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Lemma pxd_B1 : forall regs m (data : Z),
    (1 <= data)%Z -> (data < 2 ^ 64)%Z ->
    rdn SEGS m (rl dA_1f430 0x1f438) 8 = Some (Z_to_le_bytes 8 (0x15b38 + dF_15b38)) ->
    getr regs 10 = Z_to_bv 64 data ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_23d30 0x23d78) m rom) (mkst regs' (rl dF_15b38 0x15b38) m rom)
      /\ getr regs' 10 = Z_to_bv 64 data /\ getr regs' 1 = rl dVL_23d30 0x23d88
      /\ regs_agree (fun r => In r [1; 11]%list) regs regs'.
  Proof. rl_dbounds (dF_15b38 :: nil).
    intros regs m data Hd Hd64 Rpmm H10.
    eexists. split.
    - stepb_ft F_23d78 D_23d78 ltac:(condZ).
      sn F_23d7c D_23d7c.
      stepLD F_23d80 D_23d80 (Z_to_le_bytes 8 (0x15b38 + dF_15b38)) (rl dF_15b38 0x15b38) ltac:(addr_norm; exact Rpmm) ltac:(apply lez8; lia).
      assert (RLJR : ret_ok (rl dF_15b38 0x15b38)) by rl_ret_ok_VL. stepjr F_23d84 D_23d84 (rl dF_15b38 0x15b38) ltac:(gres; reflexivity). rl_jr_fix. rl_norm. clear RLJR.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pxd_B0 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    msteps SEGS (mkst regs (rl dVL_23d30 0x23d78) m rom) (mkst regs (rl dVL_23d30 0x23d88) m rom).
  Proof.
    intros regs m H10. stepb_tk F_23d78 D_23d78 ltac:(condZ). apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma pxd_C1 : forall regs m (s pix cm : Z) (v : pixv),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> PIXat m pix v -> p_text v = 0%Z -> p_cmap v = cm -> (1 <= cm)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> (pix + 64 <= s - 32 \/ s <= pix)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_23d30 0x23d88) m rom)
                  (mkst regs' (rl dVL_247d4 0x247d4) (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 cm))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 10 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = rl dVL_23d30 0x23da8
      /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s pix cm v Hs Hs64 PX Ht Hc Hcm SOK DJ H2 H8.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_cmap _ WF) as Rc.
    eexists. split.
    - stepLD F_23d88 D_23d88 (Z_to_le_bytes 8 0) (Z_to_bv 64 0)
        ltac:(addr_norm; rewrite <- Ht; exact (PIX_rd_text SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepb_tk F_23d8c D_23d8c ltac:(condZ).
      stepLD F_23d94 D_23d94 (Z_to_le_bytes 8 cm) (Z_to_bv 64 cm)
        ltac:(addr_norm; rewrite <- Hc; exact (PIX_rd_cmap SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepST F_23d98 D_23d98 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 cm) ltac:(sok_in SOK).
      stepb_ft F_23d9c D_23d9c ltac:(condZ).
      sn F_23da0 D_23da0.
      sn F_23da4 D_23da4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pxd_C2 : forall regs m (pix : Z),
    (0 <= pix)%Z -> (pix + 64 < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 pix) 64 = true ->
    getr regs 8 = Z_to_bv 64 pix ->
    msteps SEGS (mkst regs (rl dVL_23d30 0x23da8) m rom)
                (mkst regs (rl dVL_23d30 0x23dac) (wbytes m (Z_to_bv 64 (pix + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom).
  Proof.
    intros regs m pix Hp0 Hp64 SOK H8.
    stepST F_23da8 D_23da8 (Z_to_bv 64 (pix + 48)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma pxd_C0 : forall regs m (s pix : Z) (v : pixv),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> PIXat m pix v -> p_text v = 0%Z -> p_cmap v = 0%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> (pix + 64 <= s - 32 \/ s <= pix)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_23d30 0x23d88) m rom)
                  (mkst regs' (rl dVL_23d30 0x23dac) (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m s pix v Hs Hs64 PX Ht Hc SOK DJ H2 H8.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    eexists. split.
    - stepLD F_23d88 D_23d88 (Z_to_le_bytes 8 0) (Z_to_bv 64 0)
        ltac:(addr_norm; rewrite <- Ht; exact (PIX_rd_text SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepb_tk F_23d8c D_23d8c ltac:(condZ).
      stepLD F_23d94 D_23d94 (Z_to_le_bytes 8 0) (Z_to_bv 64 0)
        ltac:(addr_norm; rewrite <- Hc; exact (PIX_rd_cmap SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepST F_23d98 D_23d98 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_23d9c D_23d9c ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pxd_D : forall regs m (pix : Z),
    getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_23d30 0x23dac) m rom) (mkst regs' (rl dF_15b38 0x15b38) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 1 = rl dVL_23d30 0x23db4
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof. rl_dbounds (dF_15b38 :: nil).
    intros regs m pix H8.
    eexists. split.
    - sn F_23dac D_23dac. sn F_23db0 D_23db0. apply mst_refl.
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
      msteps SEGS (mkst regs (rl dVL_23d30 0x23db4) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s pp ret s0v s1v Hs Hpp Hpp64 Hret SOK R8 R16 R24 H2 H9.
    eexists. split.
    - sn F_23db4 D_23db4.
      stepST F_23db8 D_23db8 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_23dbc D_23dbc.
      stepLD8 F_23df8 D_23df8 ret.
      stepLD8 F_23dfc D_23dfc s0v.
      stepLD8 F_23e00 D_23e00 s1v.
      zv F_23e04 D_23e04 (Z_to_bv 64 s).
      stepret F_23e08 D_23e08 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End Segs.

(* [comment removed for export] *)
Definition pixd_post (A A' : AS) (pix data cm arr : Z) : Prop :=
  live A' (Z_to_bv 64 pix) = None /\
  (data <> 0%Z -> live A' (Z_to_bv 64 data) = None) /\
  (cm <> 0%Z -> live A' (Z_to_bv 64 cm) = None /\ live A' (Z_to_bv 64 arr) = None) /\
  (forall q, q <> Z_to_bv 64 pix -> (data <> 0%Z -> q <> Z_to_bv 64 data) -> (cm <> 0%Z -> q <> Z_to_bv 64 cm /\ q <> Z_to_bv 64 arr) ->
             live A' q = live A q).

(* [comment removed for export] *)
Lemma pixDestroy_fin : forall C A m md regs (s pp pix : Z) (ret s0v s1v : word) (S : TSet),
  Cok C -> W C A m md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> ret_ok ret ->
  getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pix -> getr regs 9 = Z_to_bv 64 pp -> getr regs 4 = rl dA_2f6b0 0x2f7b8 ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) ->
     getr regs' 2 = Z_to_bv 64 s -> getr regs' 8 = s0v -> getr regs' 9 = s1v ->
     (forall r, In r cs_rest -> getr regs' r = getr regs r) ->
     live A' (Z_to_bv 64 pix) = None -> (forall q, q <> Z_to_bv 64 pix -> live A' q = live A q) ->
     POSTM C (c_A0 C) (pp + 8) m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (rl dVL_23d30 0x23dac) m al_rom) md) S.
Proof.
  intros C A m md regs s pp pix ret s0v s1v S CK HW Hs16 Hlo Hpp Hpphi Hret H2 H8 H9 H4 R8 R16 R24 Lp L0p HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *. unfold ALLOC_STACK in Hlo.
  destruct (pxd_D al_rom regs m pix H8) as (r1 & RUN1 & Q10 & Q1 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (Q4 : getr r1 4 = rl dA_2f6b0 0x2f7b8) by (csr; reflexivity).
  assert (Q2 : getr r1 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  apply (W_free16 C A m md r1 (Z_to_bv 64 pix) (rl dVL_23d30 0x23db4) 64 (s - 32) S CK HW Q10 Lp L0p Q1
           ltac:(rl_ret_ok_VL) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 HWa CSa La LEQa PMa HRTa.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 pp) by (csr; reflexivity).
  destruct (pxd_E al_rom r2 m1 s pp ret s0v s1v ltac:(lia) Hpp ltac:(lia) Hret) as (r3 & RUN3 & V2 & V1 & V8 & V9 & AG3).
  { apply (W_sok_win C A1 m1 _ pp 8 CK HWa); [lia | cbn; lia]. }
  { rewrite (FRM_rdn16 C (s - 32) m m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). exact R8. }
  { rewrite (FRM_rdn16 C (s - 32) m m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). exact R16. }
  { rewrite (FRM_rdn16 C (s - 32) m m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia). exact R24. }
  { exact E2. } { exact E9. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  assert (WP : W C A1 (wbytes m1 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) (with_vmmaps vm1 md) /\
               POSTM C (c_A0 C) (pp + 8) m (wbytes m1 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0)))).
  { apply (WP_win C A1 (c_A0 C) m m1 _ _ _ (pp + 8) CK); [| exact (w_keep _ _ _ _ HWa) | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia].
    split; [exact HWa|]. apply (POSTM_sub C (c_A0 C) A1); [exact (w_keep _ _ _ _ HWa)|]. eapply POSTM_mono; [|exact PMa]. lia. }
  destruct WP as [HW3 PM3].
  apply (HK A1 _ vm1 r3); try assumption; try (solve [room_tac]).
  - intros r Hr. cbn [In cs_rest] in Hr.
    repeat (destruct Hr as [<-|Hr]; [csr; reflexivity|]). destruct Hr.
  - rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
Qed.


(* [comment removed for export] *)
Lemma pixDestroy_tail : forall C A m md regs (s pp pix cm karr : Z) (v : pixv) (cv : cmapv) (ret s0v s1v : word) (S : TSet),
  Cok C -> W C A m md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> ret_ok ret ->
  getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pix -> getr regs 9 = Z_to_bv 64 pp -> getr regs 4 = rl dA_2f6b0 0x2f7b8 ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
  PIXat m pix v -> p_text v = 0%Z -> p_cmap v = cm ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some karr /\
                live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
                cm <> c_arr cv /\ cm <> pix /\ c_arr cv <> pix /\ (0 < karr)%Z)) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) ->
     getr regs' 2 = Z_to_bv 64 s -> getr regs' 8 = s0v -> getr regs' 9 = s1v ->
     (forall r, In r cs_rest -> getr regs' r = getr regs r) ->
     live A' (Z_to_bv 64 pix) = None ->
     (cm <> 0%Z -> live A' (Z_to_bv 64 cm) = None /\ live A' (Z_to_bv 64 (c_arr cv)) = None) ->
     (forall q, q <> Z_to_bv 64 pix -> (cm <> 0%Z -> q <> Z_to_bv 64 cm /\ q <> Z_to_bv 64 (c_arr cv)) -> live A' q = live A q) ->
     POSTM C (c_A0 C) (pp + 8) m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (rl dVL_23d30 0x23d88) m al_rom) md) S.
Proof.
  intros C A m md regs s pp pix cm karr v cv ret s0v s1v S CK HW Hs16 Hlo Hpp Hpphi Hret H2 H8 H9 H4 R8 R16 R24 PX Ht Hc Lp L0p HCM HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *. unfold ALLOC_STACK in Hlo.
  pose proof PX as (Hp0 & Hp64 & WF & _).
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct HCM as [Hcm0 | (CM & Lcm & Larr & L0cm & L0arr & NE1 & NE2 & NE3 & Hk)].
  - (* [comment removed for export] *)
    rewrite Hcm0 in Hc.
    destruct (pxd_C0 al_rom regs m s pix v ltac:(lia) ltac:(lia) PX Ht Hc SOK ltac:(lia) H2 H8) as (r1 & RUN1 & Q2 & Q8 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    set (M1 := wbytes m _ _).
    assert (WP1 : W C A M1 md /\ POSTM C (c_A0 C) (pp + 8) m M1) by (subst M1; wp_win CK).
    destruct WP1 as [HW1 PM1].
    assert (Q9 : getr r1 9 = Z_to_bv 64 pp) by (csr; reflexivity).
    assert (Q4 : getr r1 4 = rl dA_2f6b0 0x2f7b8) by (csr; reflexivity).
    apply (pixDestroy_fin C A M1 md r1 s pp pix ret s0v s1v S CK HW1 Hs16 ltac:(unfold ALLOC_STACK; lia) Hpp Hpphi Hret Q2 Q8 Q9 Q4);
      [subst M1; rdn_solve | subst M1; rdn_solve | subst M1; rdn_solve | exact Lp | exact L0p |].
    intros A' m' vm' regs' HW' X2 X8 X9 XR L' LEQ' PM' Rpp' RT'.
    apply (HK A' m' vm' regs' HW' X2 X8 X9); try assumption; try (solve [room_tac]).
    + intros r Hr. rewrite (XR r Hr). apply AG1. cbn [In cs_rest] in Hr.
      repeat (destruct Hr as [<-|Hr]; [notin_lit|]). destruct Hr.
    + intros X. exfalso. apply X. exact Hcm0.
    + intros q N1 _. apply LEQ'. exact N1.
    + eapply POSTM_trans; [exact PM1 | exact PM'].
  - (* [comment removed for export] *)
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_arr _ CWF) as Rarr.
    destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia.
    destruct (pxd_C1 al_rom regs m s pix cm v ltac:(lia) ltac:(lia) PX Ht Hc ltac:(lia) SOK ltac:(lia) H2 H8) as (r1 & RUN1 & Q2 & Q10 & Q1 & Q8 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    set (M1 := wbytes m _ _).
    assert (WP1 : W C A M1 md /\ POSTM C (c_A0 C) (pp + 8) m M1) by (subst M1; wp_win CK).
    destruct WP1 as [HW1 PM1].
    assert (Q4 : getr r1 4 = rl dA_2f6b0 0x2f7b8) by (csr; reflexivity).
    assert (CM1 : CMAPat M1 cm cv).
    { subst M1. apply (CMAPat_out m cm cv); [exact CM | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
    apply (pixcmapDestroy_W C A M1 md r1 (s - 32) (s - 32) cm cv karr (rl dVL_23d30 0x23da8) S CK HW1 Q2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) Q1
             ltac:(rl_ret_ok_VL) Q4 ltac:(replace (s - 32)%Z with (s + (-32))%Z by lia; apply mod16_plus_mod8; [exact Hs16 | reflexivity]) Q10).
    { subst M1. rewrite <- (w2b_Z 8 cm) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. }
    { exact CM1. } { exact Lcm. } { exact Larr. } { exact L0cm. } { exact L0arr. } { exact NE1. }
    intros A1 m1 vm1 r2 HWa CSa La1 La2 LEQa PMa _ HRTa.
    assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (E8 : getr r2 8 = Z_to_bv 64 pix) by (csr; reflexivity).
    assert (E9 : getr r2 9 = Z_to_bv 64 pp) by (csr; reflexivity).
    assert (E4 : getr r2 4 = rl dA_2f6b0 0x2f7b8) by (csr; reflexivity).
    assert (Lp1 : live A1 (Z_to_bv 64 pix) = Some 64%Z).
    { rewrite (LEQa _ (zneq_w pix cm ltac:(lia) ltac:(lia) (not_eq_sym NE2)) (zneq_w pix (c_arr cv) ltac:(lia) ltac:(lia) (not_eq_sym NE3))). exact Lp. }
    (* [comment removed for export] *)
    assert (SOKp1 : store_ok SEGS m1 (Z_to_bv 64 pix) 64 = true).
    { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m1 x) eqn:E; [discriminate|]. exfalso.
      exact (proj1 (proj2 (blk_byte C A1 m1 _ (Z_to_bv 64 pix) 64 x CK HWa Lp1 ltac:(rewrite u_Z2bv by lia; lia))) E). }
    pose proof (pxd_C2 al_rom r2 m1 pix ltac:(lia) ltac:(lia) SOKp1 E8) as RUN2.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN2 |].
    set (M2 := wbytes m1 _ _).
    assert (PMm1 : POSTM C (c_A0 C) (pp + 8) m m1).
    { eapply POSTM_trans; [exact PM1|]. apply (POSTM_sub C (c_A0 C) A1); [exact (w_keep _ _ _ _ HWa) | eapply POSTM_mono; [|exact PMa]; lia]. }
    assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C (c_A0 C) (pp + 8) m M2).
    { subst M2. apply (WP_blk C (c_A0 C) A1 m m1 _ (Z_to_bv 64 pix) _ 64); [exact CK | split; [exact HWa | exact PMm1] | exact Lp1 | exact L0p | exact L0p | exact (w_keep _ _ _ _ HWa) | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
    destruct WP2 as [HW2 PM2].
    apply (pixDestroy_fin C A1 M2 _ r2 s pp pix ret s0v s1v S CK HW2 Hs16 ltac:(unfold ALLOC_STACK; lia) Hpp Hpphi Hret E2 E8 E9 E4).
    { subst M2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 32 + 8) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
    { subst M2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 32 + 8) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
    { subst M2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 32 + 8) M1 m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
    { exact Lp1. }
    { exact L0p. }
    intros A' m' vm' regs' HW' X2 X8 X9 XR L' LEQ' PM' Rpp' RT'. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HW'.
    apply (HK A' m' vm' regs' HW' X2 X8 X9); try assumption; try (solve [room_tac]).
    + intros r Hr. rewrite (XR r Hr). rewrite (cs_rest_of_kept _ _ CSa r Hr). apply AG1. cbn [In cs_rest] in Hr.
      repeat (destruct Hr as [<-|Hr]; [notin_lit|]). destruct Hr.
    + intros _. split; [| ]. 
      * rewrite (LEQ' _ (zneq_w cm pix ltac:(lia) ltac:(lia) NE2)). exact La1.
      * rewrite (LEQ' _ (zneq_w (c_arr cv) pix ltac:(lia) ltac:(lia) NE3)). exact La2.
    + intros q N1 N23. destruct (N23 ltac:(lia)) as [N2 N3]. rewrite (LEQ' q N1). apply LEQa; assumption.
    + eapply POSTM_trans; [exact PM2 | exact PM'].
Qed.

Theorem pixDestroy_W : forall C A m md regs (s pp pix cm karr R : Z) (v : pixv) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = rl dA_2f6b0 0x2f7b8 -> (pp mod 8 = 0)%Z ->
  getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
  PIXat m pix v -> p_rc v = 1%Z -> p_text v = 0%Z -> p_cmap v = cm ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  (p_data v = 0%Z \/ (live A (Z_to_bv 64 (p_data v)) = Some R /\ live (c_A0 C) (Z_to_bv 64 (p_data v)) = None /\ (0 < R)%Z /\
                      p_data v <> pix /\ (cm <> 0%Z -> p_data v <> cm /\ p_data v <> c_arr cv))) ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some karr /\
                live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
                cm <> c_arr cv /\ cm <> pix /\ c_arr cv <> pix /\ (0 < karr)%Z)) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     pixd_post A A' pix (p_data v) cm (c_arr cv) ->
     POSTM C (c_A0 C) (pp + 8) m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (rl dVL_23d30 0x23d30) m al_rom) md) S.
Proof.
  intros C A m md regs s pp pix cm karr R v cv ret S CK HW H2 Hs16 Hlo Hpp Hpphi H1 Hret H4 ALpp H10 Rpp PX Hrc Ht Hc Lp L0p HD HCM HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *. unfold ALLOC_STACK in Hlo.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rd.
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  assert (SOKp : store_ok SEGS m (Z_to_bv 64 pix) 64 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m pix v x PX ltac:(lia) E). }
  destruct (pxd_A al_rom regs m s pp pix v ret ltac:(lia) Hpp ltac:(lia) ALp ALpp (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia))
              SOKp Rpp PX Hrc ltac:(lia) Gp H2 H1 H10) as (r1 & RUN1 & Q2 & Q8 & Q9 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M0 := wbytes (wbytes (wbytes m _ _) _ _) _ _).
  set (M1 := wbytes M0 _ _).
  assert (WP0 : W C A M0 md /\ POSTM C (c_A0 C) (pp + 8) m M0) by (subst M0; wp_win CK).
  assert (WP1 : W C A M1 md /\ POSTM C (c_A0 C) (pp + 8) m M1).
  { subst M1. apply (WP_blk C (c_A0 C) A m M0 md (Z_to_bv 64 pix) _ 64); [exact CK | exact WP0 | exact Lp | exact L0p | exact L0p | exact (w_keep _ _ _ _ HW) | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
  destruct WP1 as [HW1 PM1]. clear WP0.
  assert (PX1 : PIXat M1 pix (set_rc v 0)).
  { subst M1. apply PIX_wr_rc; [|lia]. subst M0.
    repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  assert (R8 : rdn SEGS M1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)) by (subst M1 M0; rdn_solve).
  assert (R16 : rdn SEGS M1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))) by (subst M1 M0; rdn_solve).
  assert (R24 : rdn SEGS M1 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))) by (subst M1 M0; rdn_solve).
  assert (Q4 : getr r1 4 = rl dA_2f6b0 0x2f7b8) by (csr; reflexivity).
  assert (HCM1 : cm = 0%Z \/ (CMAPat M1 cm cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some karr /\
                live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
                cm <> c_arr cv /\ cm <> pix /\ c_arr cv <> pix /\ (0 < karr)%Z)).
  { destruct HCM as [X|(CM & X)]; [left; exact X | right; split; [|exact X]].
    pose proof CM as (Hc0 & Hc64 & _). destruct X as (Lcm & _ & _ & _ & _ & NE2 & _).
    destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia.
    pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lcm Lp (zneq_w cm pix ltac:(lia) ltac:(lia) NE2)) as D.
    rewrite !u_Z2bv in D by lia. unfold round16 in D. change ((24 + 15) / 16)%Z with 2%Z in D. change ((64 + 15) / 16)%Z with 4%Z in D.
    subst M1 M0. repeat (apply CMAPat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact CM. }
  (* [comment removed for export] *)
  assert (TAIL : forall A1 m1 vm1 r2, W C A1 m1 (with_vmmaps vm1 md) ->
            getr r2 2 = Z_to_bv 64 (s - 32) -> getr r2 8 = Z_to_bv 64 pix -> getr r2 9 = Z_to_bv 64 pp -> getr r2 4 = rl dA_2f6b0 0x2f7b8 ->
            (forall r, In r cs_rest -> getr r2 r = getr regs r) ->
            POSTM C (c_A0 C) (s - 32) M1 m1 -> PIXat m1 pix (set_rc v 0) ->
            live A1 (Z_to_bv 64 pix) = Some 64%Z ->
            (cm <> 0%Z -> live A1 (Z_to_bv 64 cm) = live A (Z_to_bv 64 cm) /\ live A1 (Z_to_bv 64 (c_arr cv)) = live A (Z_to_bv 64 (c_arr cv))) ->
            (p_data v <> 0%Z -> live A1 (Z_to_bv 64 (p_data v)) = None) ->
            (forall q, (p_data v <> 0%Z -> q <> Z_to_bv 64 (p_data v)) -> live A1 q = live A q) ->
            (cm <> 0%Z -> CMAPat m1 cm cv) ->
            roomtr A (m_vmmaps md) A1 vm1 0 0 ->
            realizes SEGS (mkCfg (mkst r2 (rl dVL_23d30 0x23d88) m1 al_rom) (with_vmmaps vm1 md)) S).
  { intros A1 m1 vm1 r2 HWa E2 E8 E9 E4 ER PMa PXa Lp1 Lcm1 LD1 LEQa CMa RTa.
    apply (pixDestroy_tail C A1 m1 _ r2 s pp pix cm karr (set_rc v 0) cv ret (getr regs 8) (getr regs 9) S CK HWa Hs16
             ltac:(unfold ALLOC_STACK; lia) Hpp Hpphi Hret E2 E8 E9 E4).
    - rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). exact R8.
    - rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). exact R16.
    - rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia). exact R24.
    - exact PXa.
    - cbn. exact Ht.
    - cbn. exact Hc.
    - exact Lp1.
    - exact L0p.
    - destruct HCM1 as [X|(CM & Lcm & Larr & X)]; [left; exact X | right].
      pose proof CM as (Hc0 & Hc64 & _).
      destruct (blk_range C A M1 md _ _ CK HW1 Lcm ltac:(lia)) as [G _]. rewrite u_Z2bv in G by lia.
      assert (NC : cm <> 0%Z) by lia.
      destruct (Lcm1 NC) as [E1 E2']. rewrite E1, E2'.
      split; [exact (CMa NC) | split; [exact Lcm | split; [exact Larr | exact X]]].
    - intros A' m' vm' regs' HW' X2 X8 X9 XR L' Lcm' LEQ' PM' Rpp' RT'. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HW'.
      apply (HK A' m' vm' regs' HW').
      + apply cs_kept_of_rest; [rewrite X2, H2; reflexivity | exact X8 | exact X9 |].
        intros r Hr. rewrite (XR r Hr). exact (ER r Hr).
      + split; [exact L'|]. split; [|split].
        * intros ND. destruct HD as [X|(LR & LR0 & HR & NEdp & NEdc)]; [exfalso; exact (ND X)|].
          rewrite (LEQ' (Z_to_bv 64 (p_data v))); [exact (LD1 ND) | apply zneq_w; lia |].
          intros NC. destruct (NEdc NC) as [N2 N3].
          destruct HCM as [X|(CM & _ & _ & _ & _ & _)]; [exfalso; exact (NC X)|]. pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_arr _ CWF).
          split; apply zneq_w; lia.
        * intros NC. exact (Lcm' NC).
        * intros q N1 N2 N3. rewrite (LEQ' q N1 N3). apply LEQa. exact N2.
      + eapply POSTM_trans; [eapply POSTM_mono; [|exact PM1]; lia|]. eapply POSTM_trans; [eapply POSTM_mono; [|exact PMa]; lia | exact PM'].
      + exact Rpp'.
      + room_tac. }
  assert (ER1 : forall r, In r cs_rest -> getr r1 r = getr regs r).
  { intros r Hr. apply AG1. cbn [In cs_rest] in Hr. repeat (destruct Hr as [<-|Hr]; [notin_lit|]). destruct Hr. }
  destruct HD as [D0 | (LR & LR0 & HR & NEdp & NEdc)].
  - (* [comment removed for export] *)
    rewrite D0 in Q10.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact (pxd_B0 al_rom r1 M1 Q10) |].
    rewrite <- (with_vmmaps_same md). rewrite <- (with_vmmaps_same md) in HW1.
    apply (TAIL A M1 (m_vmmaps md) r1 HW1 Q2 Q8 Q9 Q4 ER1).
    + apply POSTM_refl.
    + exact PX1.
    + exact Lp.
    + intros _. split; reflexivity.
    + intros ND. exfalso. exact (ND D0).
    + intros q _. reflexivity.
    + intros NC. destruct HCM1 as [X|(CM & _)]; [exfalso; exact (NC X) | exact CM].
    + room_tac.
  - (* [comment removed for export] *)
    rename R into Rn.
    destruct (blk_range C A m md (Z_to_bv 64 (p_data v)) Rn CK HW LR HR) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
    destruct (pxd_B1 al_rom r1 M1 (p_data v) ltac:(lia) ltac:(lia) (W_pmm_free C A M1 md HW1) Q10) as (r2 & RUN2 & P10 & P1 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    assert (P4 : getr r2 4 = rl dA_2f6b0 0x2f7b8) by (csr; reflexivity).
    assert (P2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    apply (W_free16 C A M1 md r2 (Z_to_bv 64 (p_data v)) (rl dVL_23d30 0x23d88) Rn (s - 32) S CK HW1 P10 LR LR0 P1
             ltac:(rl_ret_ok_VL) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A1 m1 vm1 r3 HWa CSa La LEQa PMa HRTa.
    assert (NEpd : Z_to_bv 64 pix <> Z_to_bv 64 (p_data v)) by (apply zneq_w; lia).
    assert (Lp1 : live A1 (Z_to_bv 64 pix) = Some 64%Z) by (rewrite (LEQa _ NEpd); exact Lp).
    apply (TAIL A1 m1 vm1 r3 HWa).
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + intros r Hr. rewrite (cs_rest_of_kept _ _ CSa r Hr). rewrite (AG2 r). exact (ER1 r Hr).
      cbn [In cs_rest] in Hr. repeat (destruct Hr as [<-|Hr]; [notin_lit|]). destruct Hr.
    + apply (POSTM_sub C (c_A0 C) A1); [exact (W_sub0 _ _ _ _ HWa) | exact PMa].
    + apply (PIXat_frame M1); [exact PX1|]. intros x Hx. pose proof (proj2 PMa (Z_to_bv 64 pix) 64%Z (u x - pix)%Z Lp1 ltac:(lia)) as E.
      unfold at_ in E. rewrite u_Z2bv in E by lia. replace (pix + (u x - pix))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E.
    + exact Lp1.
    + intros NC. destruct (NEdc NC) as [N2 N3].
      destruct HCM as [X|(CM & _)]; [exfalso; exact (NC X)|]. pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_arr _ CWF).
      split; apply LEQa; apply zneq_w; lia.
    + intros _. exact La.
    + intros q Hq. apply LEQa. apply Hq. lia.
    + intros NC. destruct HCM1 as [X|(CM & Lcm & X)]; [exfalso; exact (NC X)|]. pose proof CM as (Hc0 & Hc64 & CWF & _).
      destruct (NEdc NC) as [N2 N3].
      assert (Lcm1 : live A1 (Z_to_bv 64 cm) = Some 24%Z) by (rewrite (LEQa _ (zneq_w cm (p_data v) ltac:(lia) ltac:(lia) (not_eq_sym N2))); exact Lcm).
      apply (CMAPat_frame M1); [exact CM|]. intros x Hx. pose proof (proj2 PMa (Z_to_bv 64 cm) 24%Z (u x - cm)%Z Lcm1 ltac:(lia)) as E.
      unfold at_ in E. rewrite u_Z2bv in E by lia. replace (cm + (u x - cm))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E.
    + room_tac.
Qed.





End PixDestroy.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
