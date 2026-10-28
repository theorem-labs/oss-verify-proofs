(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRop2Arith.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptRopClip.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptRop_iface V23LeptCmap2 V23LeptRop V23LeptRop2Segs V23LeptRopClip V23LeptRopGSpec.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section RopGenC.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition rasteropLow_arm_clip_contract (ARM : Z -> Z -> Z -> Z -> Prop) : Prop :=
  forall C Ar A m md regs (s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROPLOW_STACK <= s)%Z -> (s + 64 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw -> getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx -> getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 12)) ->
  rdn SEGS m (Z_to_bv 64 (s + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)) ->
  rdn SEGS m (Z_to_bv 64 (s + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixw)) ->
  rdn SEGS m (Z_to_bv 64 (s + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  rdn SEGS m (Z_to_bv 64 (s + 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sx)) ->
  rdn SEGS m (Z_to_bv 64 (s + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)) ->
  (0 <= datad < 2 ^ 64)%Z -> (0 <= datas < 2 ^ 64)%Z ->
  rop_shape dpixw dpixh 1 dwpl -> rop_shape spixw spixh 1 swpl ->
  (- 2 ^ 20 <= dx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= sx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= dy <= 2 ^ 20)%Z -> (- 2 ^ 20 <= sy <= 2 ^ 20)%Z ->
  (0 <= dw <= 2 ^ 20)%Z -> (0 <= dh <= 2 ^ 20)%Z ->
  ((1 <= clip_w dx sx dw dpixw spixw)%Z -> (1 <= clip_w dy sy dh dpixh spixh)%Z -> ARM (clip_d dx sx) (clip_s dx sx) (clip_w dx sx dw dpixw spixw) swpl) ->
  live A (Z_to_bv 64 datad) = Some (4 * (dwpl * dpixh))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (swpl * spixh))%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
      (forall a : word, ~ scratch C s a -> ~ (datad <= bv_unsigned a < datad + 4 * (dwpl * dpixh))%Z -> m' a = m a) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_rasteropLow) m al_rom) md) S.

Definition rasteropLow_armop_clip_contract (op : Z) (ARM : Z -> Z -> Z -> Z -> Prop) : Prop :=
  forall C Ar A m md regs (s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROPLOW_STACK <= s)%Z -> (s + 64 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw -> getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx -> getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 op)) ->
  rdn SEGS m (Z_to_bv 64 (s + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)) ->
  rdn SEGS m (Z_to_bv 64 (s + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixw)) ->
  rdn SEGS m (Z_to_bv 64 (s + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  rdn SEGS m (Z_to_bv 64 (s + 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sx)) ->
  rdn SEGS m (Z_to_bv 64 (s + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)) ->
  (0 <= datad < 2 ^ 64)%Z -> (0 <= datas < 2 ^ 64)%Z ->
  rop_shape dpixw dpixh 1 dwpl -> rop_shape spixw spixh 1 swpl ->
  (- 2 ^ 20 <= dx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= sx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= dy <= 2 ^ 20)%Z -> (- 2 ^ 20 <= sy <= 2 ^ 20)%Z ->
  (0 <= dw <= 2 ^ 20)%Z -> (0 <= dh <= 2 ^ 20)%Z ->
  ((1 <= clip_w dx sx dw dpixw spixw)%Z -> (1 <= clip_w dy sy dh dpixh spixh)%Z -> ARM (clip_d dx sx) (clip_s dx sx) (clip_w dx sx dw dpixw spixw) swpl) ->
  live A (Z_to_bv 64 datad) = Some (4 * (dwpl * dpixh))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (swpl * spixh))%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
      (forall a : word, ~ scratch C s a -> ~ (datad <= bv_unsigned a < datad + 4 * (dwpl * dpixh))%Z -> m' a = m a) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_rasteropLow) m al_rom) md) S.

Definition rasteropLow_gen_clip_contract : Prop :=
  rasteropLow_arm_clip_contract (fun DX SX DW swpl => DX mod 32 <> SX mod 32 /\ g_smax DX SX DW <= swpl - 1)%Z.

Definition rg_gen_pre : Prop :=
  forall C Ar A m md regs (s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy op tv : Z) (ret ENTRY : word),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROPLOW_STACK <= s)%Z -> (s + 64 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw -> getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx -> getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 op)) ->
  rdn SEGS m (Z_to_bv 64 (s + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)) ->
  rdn SEGS m (Z_to_bv 64 (s + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixw)) ->
  rdn SEGS m (Z_to_bv 64 (s + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  rdn SEGS m (Z_to_bv 64 (s + 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sx)) ->
  rdn SEGS m (Z_to_bv 64 (s + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)) ->
  (0 <= datad < 2 ^ 64)%Z -> (0 <= datas < 2 ^ 64)%Z ->
  rop_shape dpixw dpixh 1 dwpl -> rop_shape spixw spixh 1 swpl ->
  (- 2 ^ 20 <= dx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= sx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= dy <= 2 ^ 20)%Z -> (- 2 ^ 20 <= sy <= 2 ^ 20)%Z ->
  (0 <= dw <= 2 ^ 20)%Z -> (0 <= dh <= 2 ^ 20)%Z ->
  live A (Z_to_bv 64 datad) = Some (4 * (dwpl * dpixh))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (swpl * spixh))%Z ->
  (op = 2 \/ op = 3 \/ op = 8 \/ op = 12 \/ op = 14)%Z ->
  rdn SEGS (fun _ => None) (Z_to_bv 64 (RG_JT + 4 * (op - 1))) 4 = Some (Z_to_le_bytes 4 tv) ->
  Z_to_bv 64 (RG_JT + tv) = ENTRY -> (0 <= tv < 2 ^ 31)%Z -> (tv mod 2 = 0)%Z ->
  (1 <= clip_w dx sx dw dpixw spixw)%Z -> (1 <= clip_w dy sy dh dpixh spixh)%Z ->
  (clip_d dx sx mod 32 <> clip_s dx sx mod 32)%Z ->
  (g_smax (clip_d dx sx) (clip_s dx sx) (clip_w dx sx dw dpixw spixw) <= swpl - 1)%Z ->
  exists regs1 MB (dxb sls nfw psf pdf psF pdF psl pdl : Z) (fw f6 f7 nofull nolast f3 : bool),
    msteps SEGS (mkst regs (Z_to_bv 64 PC_rasteropLow) m al_rom) (mkst regs1 ENTRY MB al_rom)
    /\ (forall a : word, ~ (s - 240 <= u a < s)%Z -> MB a = m a) /\ mem_grows m MB
    /\ rlcells MB s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
         (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
    /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4
    /\ rg_geo datad (4 * (dwpl * dpixh)) datas (4 * (swpl * spixh)) (clip_w dy sy dh dpixh spixh) swpl dwpl dxb sls nfw
         psf pdf psF pdF psl pdl fw f6 f7 nofull nolast f3
    /\ rg_cells MB s (clip_w dy sy dh dpixh spixh) swpl nfw psl fw f6 nofull nolast f3
    /\ rg_regs regs1 s dxb dwpl sls psf pdf psF pdF pdl fw f7 nofull nolast.

Hypothesis GEN_PRE : rg_gen_pre.

Hypothesis RG_LOOPS12 : rg_loops_spec RG_S1.

Section GenOp.
Variables (op tv : Z) (ENTRY : word).
Hypothesis Hop : (op = 2 \/ op = 3 \/ op = 8 \/ op = 12 \/ op = 14)%Z.
Hypothesis JTv : rdn SEGS (fun _ => None) (Z_to_bv 64 (RG_JT + 4 * (op - 1))) 4 = Some (Z_to_le_bytes 4 tv).
Hypothesis Eent : Z_to_bv 64 (RG_JT + tv) = ENTRY.
Hypothesis Htv : (0 <= tv < 2 ^ 31 /\ tv mod 2 = 0)%Z.
Hypothesis LOOPS : rg_loops_spec ENTRY.

Theorem rasteropLow_genop_clip_W :
  rasteropLow_armop_clip_contract op (fun DX SX DW swpl => DX mod 32 <> SX mod 32 /\ g_smax DX SX DW <= swpl - 1)%Z.
Proof.
  unfold rasteropLow_armop_clip_contract.
  intros C Ar A m md regs s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy ret S
    CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
    Hdd Hds SHd SHs Bdx Bsx Bdy Bsy Bdw Bdh HARM Ld Ld0 Ld00 Ls HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *.
  assert (Hlo' : (c_top C - LSTK + 240 <= s)%Z) by exact Hlo.
  pose proof SHd as (_ & Hdpw & Hdph & Ewd & Hszd). pose proof SHs as (_ & Hspw & Hsph & Ews & Hszs).
  pose proof (wpl_bits dpixw 1 ltac:(lia) ltac:(lia)) as WBd. rewrite <- Ewd in WBd.
  pose proof (wpl_bits spixw 1 ltac:(lia) ltac:(lia)) as WBs. rewrite <- Ews in WBs.
  pose proof (wpl_of_range dpixw 1 ltac:(lia) ltac:(left; reflexivity)) as Hwd. rewrite <- Ewd in Hwd.
  pose proof (wpl_of_range spixw 1 ltac:(lia) ltac:(left; reflexivity)) as Hws. rewrite <- Ews in Hws.
  set (nd := (4 * (dwpl * dpixh))%Z) in *. set (ns := (4 * (swpl * spixh))%Z) in *.
  assert (Hnd : (0 < nd)%Z) by (subst nd; assert (1 * 1 <= dwpl * dpixh)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  assert (Hns : (0 < ns)%Z) by (subst ns; assert (1 * 1 <= swpl * spixh)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  destruct (blk_range C A m md (Z_to_bv 64 datad) nd CK HW Ld Hnd) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  destruct (blk_range C A m md (Z_to_bv 64 datas) ns CK HW Ls Hns) as [Gs TOPs]. rewrite u_Z2bv in Gs, TOPs by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & AL16d & _). rewrite u_Z2bv in AL16d by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ls) as (_ & AL16s & _). rewrite u_Z2bv in AL16s by lia.
  pose proof (mod16_mod4 _ AL16d) as AL4d. pose proof (mod16_mod4 _ AL16s) as AL4s.
  assert (EP : Z_to_bv 64 PC_rasteropLow = RLC_P) by (apply bv_eq; reflexivity).
  assert (SOKf : store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true)
    by (apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia]).
  assert (EMP : (clip_w dx sx dw dpixw spixw <= 0 \/ clip_w dy sy dh dpixh spixh <= 0)%Z ->
                realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_rasteropLow) m al_rom) md) S).
  { intros E.
    destruct (rl_clip_empty al_rom regs m s datad dpixw dpixh dwpl dx dy dw dh op datas spixw spixh swpl sx sy ret
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                SOKf Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy H2 H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 E)
      as (r1 & M1 & RUN1 & OUT1 & GR1 & CS1).
    assert (CH : forall a, M1 a <> m a -> scratch C s a).
    { intros a NE. unfold scratch.
      destruct (Z_lt_ge_dec (u a) (s - 240)); [exfalso; apply NE; apply OUT1; lia|].
      destruct (Z_lt_ge_dec (u a) s); [lia|]. exfalso; apply NE; apply OUT1; lia. }
    rewrite EP.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    apply HK.
    - apply (W_local C A m md M1 s CK HW ltac:(lia)); [|exact GR1]. intros a NE. left. exact (CH a NE).
    - exact CS1.
    - apply (POSTM_local C Ar A m md M1 s CK HW SUB). intros a NE. left. exact (CH a NE).
    - intros a Ha _. apply OUT1. unfold scratch in Ha. lia. }
  destruct (Z_lt_le_dec (clip_w dx sx dw dpixw spixw) 1) as [EW|NW]; [apply EMP; lia|].
  destruct (Z_lt_le_dec (clip_w dy sy dh dpixh spixh) 1) as [EH|NH]; [apply EMP; lia|].
  clear EMP.
  destruct (HARM NW NH) as [AR1 AR2].
  destruct (GEN_PRE C Ar A m md regs s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy op tv ret ENTRY
              CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
              Hdd Hds SHd SHs Bdx Bsx Bdy Bsy Bdw Bdh Ld Ld0 Ld00 Ls Hop JTv Eent (proj1 Htv) (proj2 Htv) NW NH AR1 AR2)
    as (r1 & MB & dxb & sls & nfw & psf & pdf & psF & pdF & psl & pdl & fw & f6 & f7 & nofull & nolast & f3 &
        RUN1 & OUT1 & GR1 & RC1 & K3 & K4 & GEO & CELLS & REGS).
  assert (FR : disj_apart datad nd (s - 240) 240) by (unfold disj_apart; lia).
  assert (BLK : rg_blk MB s datad nd datas ns).
  { unfold rg_blk. split; [lia |]. split; [lia |]. split; [lia |].
    split; [eapply store_ok_mono; [exact GR1 | exact (blk_sok C A m md datad nd CK HW Ld ltac:(lia) ltac:(lia) ltac:(lia))] |].
    split; [eapply store_ok_mono; [exact GR1 | exact (blk_sok C A m md datas ns CK HW Ls ltac:(lia) ltac:(lia) ltac:(lia))] |].
    split; [eapply store_ok_mono; [exact GR1 | apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia]] |].
    exact FR. }
  destruct (LOOPS MB al_rom s datad nd datas ns (clip_w dy sy dh dpixh spixh) swpl dwpl dxb sls nfw psf pdf psF pdF psl pdl
              fw f6 f7 nofull nolast f3 r1 BLK GEO CELLS REGS) as (r2 & M3 & RUN2 & INV2 & Q2 & AG2).
  destruct INV2 as [OUT2 GR2].
  assert (RC3 : rlcells M3 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                  (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
  { apply (rlcells_frame MB); [lia | lia | exact RC1 |].
    intros x Hx. apply OUT2; unfold disj_apart in FR; lia. }
  destruct (rl_Eg al_rom r2 M3 s ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) Hret Q2 RC3)
    as (r3 & RUN3 & G1 & G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) |
                     eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]] |].
  assert (OUTM : forall a : word, ~ (s - 240 <= u a < s)%Z -> ~ (datad <= u a < datad + nd)%Z -> M3 a = m a).
  { intros a Ha Hb. rewrite OUT2 by lia. apply OUT1. exact Ha. }
  assert (CH : forall a, M3 a <> m a -> scratch C s a \/ (datad <= u a < datad + nd)%Z).
  { intros a NE. destruct (Z_lt_ge_dec (u a) datad) as [B1|B1];
      [| destruct (Z_lt_ge_dec (u a) (datad + nd)) as [B2|B2]; [right; lia |]];
      (left; unfold scratch;
       destruct (Z_lt_ge_dec (u a) (s - 240)); [exfalso; apply NE; apply OUTM; lia|];
       destruct (Z_lt_ge_dec (u a) s); [lia|]; exfalso; apply NE; apply OUTM; lia). }
  assert (K3' : getr r3 3 = getr regs 3)
    by (rewrite (AG3 (3 : reg) ltac:(notin_list)), (AG2 (3 : reg) ltac:(notin_list)); exact K3).
  assert (K4' : getr r3 4 = getr regs 4)
    by (rewrite (AG3 (4 : reg) ltac:(notin_list)), (AG2 (4 : reg) ltac:(notin_list)); exact K4).
  apply HK.
  - apply (W_local C A m md M3 s CK HW ltac:(lia)).
    + intros a NE. destruct (CH a NE) as [X|R]; [left; exact X | right].
      exists (Z_to_bv 64 datad), nd. rewrite u_Z2bv by lia. split; [exact Ld | split; [exact Ld00 | lia]].
    + eapply mem_grows_trans; [exact GR1 | exact GR2].
  - apply cs_kept_intro; try assumption. rewrite G2, H2. reflexivity.
  - apply (POSTM_local C Ar A m md M3 s CK HW SUB). intros a NE. destruct (CH a NE) as [X|R]; [left; exact X | right].
    exists (Z_to_bv 64 datad), nd. rewrite u_Z2bv by lia. split; [exact Ld | split; [exact Ld0 | lia]].
  - intros a Ha Hb. apply OUTM; [|exact Hb]. unfold scratch in Ha. lia.
Qed.

End GenOp.

Lemma jt12g_rd : rdn SEGS (fun _ => None) (Z_to_bv 64 (RG_JT + 4 * (12 - 1))) 4 = Some (Z_to_le_bytes 4 RG_JT12V).
Proof. vm_refl_bv. Qed.

Lemma ent12 : Z_to_bv 64 (RG_JT + RG_JT12V) = RG_S1.
Proof. apply bv_eq. reflexivity. Qed.

Theorem rasteropLow_gen_clip_W : rasteropLow_gen_clip_contract.
Proof.
  exact (rasteropLow_genop_clip_W 12 RG_JT12V RG_S1 ltac:(lia) jt12g_rd ent12 ltac:(split; [unfold RG_JT12V; lia | reflexivity]) RG_LOOPS12).
Qed.

End RopGenC.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
