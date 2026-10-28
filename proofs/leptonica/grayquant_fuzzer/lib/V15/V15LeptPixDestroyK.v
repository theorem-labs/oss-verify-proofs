(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptStderr V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL7a.
Import V15CL7a.V15LeptErr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL8a.
Import V15CL8a.V15LeptCmap. Import V15CL8a.V15LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptPixCreate.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL9a.
Import V15CL9a.V15LeptPixDestroy.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL10a.
Import V15CL10a.V15LeptCmapValid.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptCmap2 V15LeptPixCopyA V15LeptPixCopy V15_code_gq.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

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
      msteps SEGS (mkst regs (0x170a4 : word) m rom)
                  (mkst regs' (0x170ec : word)
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
    - zv F_16fa0 D_16fa0 (Z_to_bv 64 (s - 32)).
      stepST F_16fa4 D_16fa4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_16fa8 D_16fa8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_16fac D_16fac (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_16fb0 D_16fb0 ltac:(condZ).
      stepiv F_16fb4 D_16fb4 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite ALp; reflexivity).
      stepb_ft F_16fb8 D_16fb8 ltac:(condZ).
      stepLD F_16fbc D_16fbc (Z_to_le_bytes 8 pix) (Z_to_bv 64 pix) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
      stepb_ft F_16fc0 D_16fc0 ltac:(condZ).
      stepiv F_16fc4 D_16fc4 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite AL8; reflexivity).
      stepb_ft F_16fc8 D_16fc8 ltac:(condZ).
      zv F_16fcc D_16fcc (Z_to_bv 64 (pix + 20)).
      sn F_16fd0 D_16fd0.
      chain_step;
        [ reflexivity
        | eapply (step_amoadd_w SEGS _ _ _ rom _ _ _ _ _ _ (Z_to_le_bytes 4 1) (Z_to_bv 64 1) F_16fd4 eq_refl D_16fd4);
          [ gres; rewrite u_Z2bv by lia; apply mod16_plus_mod4; [exact Hal | reflexivity]
          | gres; repeat rdn_peel1; rewrite <- RC; exact (PIX_rd_rc SEGS _ _ _ PX)
          | apply lez4; lia
          | gres; sok_in SOKp ]
        | step_simpl ].
      gres. rewrite zbv_add. replace (Z_to_bv 64 (1 + 18446744073709551615)%Z) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
      rewrite (v_lw_small 1) by lia.
      sn F_16fd8 D_16fd8.
      stepb_ft F_16fdc D_16fdc ltac:(condZ).
      sn F_16fe0 D_16fe0.
      stepLD F_16fe4 D_16fe4 (Z_to_le_bytes 8 (p_data v)) (Z_to_bv 64 (p_data v))
        ltac:(addr_norm; repeat rdn_peel1; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Lemma pxd_B1 : forall regs m (data : Z),
    (1 <= data)%Z -> (data < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x35280) 8 = Some (Z_to_le_bytes 8 0x28a54) ->
    getr regs 10 = Z_to_bv 64 data ->
    exists regs',
      msteps SEGS (mkst regs (0x170ec : word) m rom) (mkst regs' (0x28a54 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 data /\ getr regs' 1 = Z_to_bv 64 0x170fc
      /\ regs_agree (fun r => In r [1; 11]%list) regs regs'.
  Proof.
    intros regs m data Hd Hd64 Rpmm H10.
    eexists. split.
    - stepb_ft F_16fe8 D_16fe8 ltac:(condZ).
      sn F_16fec D_16fec.
      stepLD F_16ff0 D_16ff0 (Z_to_le_bytes 8 0x28a54) (Z_to_bv 64 0x28a54) ltac:(addr_norm; exact Rpmm) ltac:(apply lez8; lia).
      stepjr F_16ff4 D_16ff4 (Z_to_bv 64 0x28a54) ltac:(gres; reflexivity).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pxd_B0 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    msteps SEGS (mkst regs (0x170ec : word) m rom) (mkst regs (0x170fc : word) m rom).
  Proof.
    intros regs m H10. stepb_tk F_16fe8 D_16fe8 ltac:(condZ). apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma pxd_C1 : forall regs m (s pix cm : Z) (v : pixv),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> PIXat m pix v -> p_text v = 0%Z -> p_cmap v = cm -> (1 <= cm)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> (pix + 64 <= s - 32 \/ s <= pix)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x170fc : word) m rom)
                  (mkst regs' (0x18ba0 : word) (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 cm))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 10 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x1711c
      /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s pix cm v Hs Hs64 PX Ht Hc Hcm SOK DJ H2 H8.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_cmap _ WF) as Rc.
    eexists. split.
    - stepLD F_16ff8 D_16ff8 (Z_to_le_bytes 8 0) (Z_to_bv 64 0)
        ltac:(addr_norm; rewrite <- Ht; exact (PIX_rd_text SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepb_tk F_16ffc D_16ffc ltac:(condZ).
      stepLD F_17004 D_17004 (Z_to_le_bytes 8 cm) (Z_to_bv 64 cm)
        ltac:(addr_norm; rewrite <- Hc; exact (PIX_rd_cmap SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepST F_17008 D_17008 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 cm) ltac:(sok_in SOK).
      stepb_ft F_1700c D_1700c ltac:(condZ).
      sn F_17010 D_17010.
      sn F_17014 D_17014.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pxd_C2 : forall regs m (pix : Z),
    (0 <= pix)%Z -> (pix + 64 < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 pix) 64 = true ->
    getr regs 8 = Z_to_bv 64 pix ->
    msteps SEGS (mkst regs (0x1711c : word) m rom)
                (mkst regs (0x17120 : word) (wbytes m (Z_to_bv 64 (pix + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom).
  Proof.
    intros regs m pix Hp0 Hp64 SOK H8.
    stepST F_17018 D_17018 (Z_to_bv 64 (pix + 48)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma pxd_C0 : forall regs m (s pix : Z) (v : pixv),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> PIXat m pix v -> p_text v = 0%Z -> p_cmap v = 0%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> (pix + 64 <= s - 32 \/ s <= pix)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x170fc : word) m rom)
                  (mkst regs' (0x17120 : word) (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m s pix v Hs Hs64 PX Ht Hc SOK DJ H2 H8.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    eexists. split.
    - stepLD F_16ff8 D_16ff8 (Z_to_le_bytes 8 0) (Z_to_bv 64 0)
        ltac:(addr_norm; rewrite <- Ht; exact (PIX_rd_text SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepb_tk F_16ffc D_16ffc ltac:(condZ).
      stepLD F_17004 D_17004 (Z_to_le_bytes 8 0) (Z_to_bv 64 0)
        ltac:(addr_norm; rewrite <- Hc; exact (PIX_rd_cmap SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepST F_17008 D_17008 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_1700c D_1700c ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pxd_D : forall regs m (pix : Z),
    getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x17120 : word) m rom) (mkst regs' (0x28a54 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 1 = Z_to_bv 64 0x17128
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m pix H8.
    eexists. split.
    - sn F_1701c D_1701c. sn F_17020 D_17020. apply mst_refl.
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
      msteps SEGS (mkst regs (0x17128 : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s pp ret s0v s1v Hs Hpp Hpp64 Hret SOK R8 R16 R24 H2 H9.
    eexists. split.
    - sn F_17024 D_17024.
      stepST F_17028 D_17028 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_1702c D_1702c.
      stepLD8 F_17068 D_17068 ret.
      stepLD8 F_1706c D_1706c s0v.
      stepLD8 F_17070 D_17070 s1v.
      zv F_17074 D_17074 (Z_to_bv 64 s).
      stepret F_17078 D_17078 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End Segs.
End PxdS.
End PxdSegs.

Section DestroyK.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem pixDestroy_keep_W : forall C A m md regs (s pp pix cm karr R : Z) (v : pixv) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x455c0 -> (pp mod 8 = 0)%Z ->
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
  realizes SEGS (mkCfg (mkst regs (0x170a4 : word) m al_rom) md) S.
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
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
  assert (ER1 : forall r, In r cs_rest -> getr r1 r = getr regs r).
  { intros r Hr. apply AG1. cbn [In cs_rest] in Hr. repeat (destruct Hr as [<-|Hr]; [notin_lit|]). destruct Hr. }
  (* [comment removed for export] *)
  assert (FIN : forall Ax Mx vmx rx, W C Ax Mx (with_vmmaps vmx md) ->
            getr rx 2 = Z_to_bv 64 (s - 32) -> getr rx 8 = Z_to_bv 64 pix -> getr rx 9 = Z_to_bv 64 pp -> getr rx 4 = Z_to_bv 64 0x455c0 ->
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
            realizes SEGS (mkCfg (mkst rx (0x17120 : word) Mx al_rom) (with_vmmaps vmx md)) S).
  { intros Ax Mx vmx rx HWx X2 X8 X9 X4 XR Lpx Ldx Lcx LEQx Fx Kx C8 C16 C24 RTx.
    destruct (PxdSegs.pxd_D al_rom rx Mx pix X8) as (r5 & RUN5 & Y10 & Y1 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWx)) | exact (mp_lazy _ (w_pure _ _ _ _ HWx)) | exact RUN5 |]. clear RUN5.
    assert (Y4 : getr r5 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
    assert (Y2 : getr r5 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    replace (0x28a54 : word) with (Z_to_bv 64 0x28a54) by (apply bv_eq; reflexivity).
    apply (W_free16 C Ax Mx _ r5 (Z_to_bv 64 pix) (Z_to_bv 64 0x17128) 64 (s - 32) S CK HWx Y10 Lpx L0p Y1
             ltac:(red; apply bv_eq; reflexivity) Y4 Y2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A2 m2 vm2 r6 HWb CSb Lb LEQb PMb HRTb. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWb.
    replace (Z_to_bv 64 0x17128) with (0x17128 : word) by (apply bv_eq; reflexivity).
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
  assert (P4 : getr r2 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
  assert (P2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  replace (0x28a54 : word) with (Z_to_bv 64 0x28a54) by (apply bv_eq; reflexivity).
  apply (W_free16 C A M1 md r2 (Z_to_bv 64 (p_data v)) (Z_to_bv 64 0x170fc) R (s - 32) S CK HW1 P10 LR LR0 P1
           ltac:(red; apply bv_eq; reflexivity) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r3 HWa CSa La LEQa PMa HRTa.
  replace (Z_to_bv 64 0x170fc) with (0x170fc : word) by (apply bv_eq; reflexivity).
  assert (NEpd : Z_to_bv 64 pix <> Z_to_bv 64 (p_data v)) by (apply zneq_w; lia).
  assert (Lp1 : live A1 (Z_to_bv 64 pix) = Some 64%Z) by (rewrite (LEQa _ NEpd); exact Lp).
  assert (PXa : PIXat m1 pix (set_rc v 0)).
  { apply (PIXat_frame M1); [exact PX1|]. intros x Hx. pose proof (proj2 PMa (Z_to_bv 64 pix) 64%Z (u x - pix)%Z Lp1 ltac:(lia)) as E.
    unfold at_ in E. rewrite u_Z2bv in E by lia. replace (pix + (u x - pix))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E. }
  assert (E2 : getr r3 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E8 : getr r3 8 = Z_to_bv 64 pix) by (csr; reflexivity).
  assert (E9 : getr r3 9 = Z_to_bv 64 pp) by (csr; reflexivity).
  assert (E4 : getr r3 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
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
    assert (X4 : getr r4 4 = Z_to_bv 64 0x455c0) by (csr; reflexivity).
    apply (pixcmapDestroy_W C A1 M2 _ r4 (s - 32) (s - 32) cm cv karr (Z_to_bv 64 0x1711c) S CK HW2 X2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) X1
             ltac:(red; apply bv_eq; reflexivity) X4 ltac:(replace (s - 32)%Z with (s + (-32))%Z by lia; apply mod16_plus_mod8; [exact Hs16 | reflexivity]) X10).
    { subst M2. rewrite <- (w2b_Z 8 cm) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. }
    { exact CM2. } { exact Lcm1. } { exact Larr1. } { exact L0cm. } { exact L0arr. } { exact NE1. }
    intros A1c m1c vm1c r5 HWc CSc Lc1 Lc2 LEQc PMc _ HRTc. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWc.
    replace (Z_to_bv 64 0x1711c) with (0x1711c : word) by (apply bv_eq; reflexivity).
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

End DestroyK.
