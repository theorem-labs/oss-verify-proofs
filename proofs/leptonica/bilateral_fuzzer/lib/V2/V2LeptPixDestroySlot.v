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

  Lemma pxdh_A : forall regs m (s pp pix : Z) (v : pixv) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (pp + 8 <= s - 32 \/ s <= pp)%Z -> (4096 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (pix mod 16 = 0)%Z -> (pp mod 8 = 0)%Z ->
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
    intros regs m s pp pix v ret Hs Hs64 Hpp Hpp4k Hpp64 Hal ALp SOK SOKp Rpp PX RC DJ Hpix H2 H1 H10.
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

  Lemma pxdh_E : forall regs m (s pp : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (pp + 8 <= s - 32 \/ s <= pp)%Z -> (4096 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> ret_ok ret ->
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
    intros regs m s pp ret s0v s1v Hs Hs64 Hpp Hpp4k Hpp64 Hret SOK R8 R16 R24 H2 H9.
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
End PixDestroy.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
