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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptRopClip.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptRop_iface V23LeptCmap2 V23LeptRopOp3.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma jt3_rd : rdn SEGS (fun _ => None) (Z_to_bv 64 a3_jt) 4 = Some (Z_to_le_bytes 4 a3_jtv).
Proof. vm_refl_bv. Qed.

Section RopOp3W.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Hypothesis RL_PRE : forall C Ar A m md regs (s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy op : Z) (ret : word),
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
  ((clip_d dx sx) mod 32 = 0)%Z -> ((clip_s dx sx) mod 32 = 0)%Z ->
  live A (Z_to_bv 64 datad) = Some (4 * (dwpl * dpixh))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (swpl * spixh))%Z -> Z_to_bv 64 datas <> Z_to_bv 64 datad ->
  (op = 2 \/ op = 3 \/ op = 8 \/ op = 12 \/ op = 14)%Z ->
  (1 <= clip_w dx sx dw dpixw spixw)%Z -> (1 <= clip_w dy sy dh dpixh spixh)%Z ->
  exists regs1 M2,
    msteps SEGS (mkst regs (Z_to_bv 64 PC_rasteropLow) m al_rom) (mkst regs1 a3_disp M2 al_rom)
    /\ (forall a : word, ~ (s - 240 <= u a < s)%Z -> M2 a = m a) /\ mem_grows m M2
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 21))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 22))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (getr regs 23))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 (getr regs 24))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 (getr regs 25))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (getr regs 26))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 (getr regs 27))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (clip_w dy sy dh dpixh spixh)))
    /\ rdn SEGS M2 (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl))
    /\ getr regs1 2 = Z_to_bv 64 (s - 240) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4
    /\ getr regs1 5 = Z_to_bv 64 1
    /\ getr regs1 7 = Z_to_bv 64 (datad + 4 * (clip_d dy sy * dwpl) + 4 * (clip_d dx sx / 32))
    /\ getr regs1 8 = Z_to_bv 64 (4 * (clip_s dy sy * swpl))
    /\ getr regs1 9 = Z_to_bv 64 (clip_w dx sx dw dpixw spixw)
    /\ getr regs1 10 = Z_to_bv 64 datad /\ getr regs1 11 = Z_to_bv 64 op
    /\ getr regs1 12 = Z_to_bv 64 (clip_w dx sx dw dpixw spixw mod 32)
    /\ getr regs1 14 = Z_to_bv 64 dwpl /\ getr regs1 16 = Z_to_bv 64 1
    /\ getr regs1 17 = Z_to_bv 64 (datas + 4 * (clip_s dy sy * swpl) + 4 * (clip_s dx sx / 32))
    /\ getr regs1 18 = Z_to_bv 64 (4 * (clip_s dx sx / 32)) /\ getr regs1 19 = Z_to_bv 64 datas
    /\ getr regs1 20 = Z_to_bv 64 sx /\ getr regs1 21 = Z_to_bv 64 dpixw
    /\ getr regs1 22 = Z_to_bv 64 (4 * (clip_d dy sy * dwpl)) /\ getr regs1 23 = Z_to_bv 64 (4 * (clip_d dx sx / 32))
    /\ getr regs1 27 = Z_to_bv 64 (clip_s dx sx) /\ getr regs1 29 = Z_to_bv 64 spixw /\ getr regs1 30 = Z_to_bv 64 dx
    /\ getr regs1 31 = Z_to_bv 64 (clip_d dx sx + clip_w2 dx sx dw - dpixw).

Hypothesis RL_EMPTY : forall C Ar A m md regs (s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy op : Z) (ret : word),
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
  live A (Z_to_bv 64 datas) = Some (4 * (swpl * spixh))%Z -> Z_to_bv 64 datas <> Z_to_bv 64 datad ->
  (op = 2 \/ op = 3 \/ op = 8 \/ op = 12 \/ op = 14)%Z ->
  (clip_w dx sx dw dpixw spixw <= 0 \/ clip_w dy sy dh dpixh spixh <= 0)%Z ->
  exists regs1 M1,
    msteps SEGS (mkst regs (Z_to_bv 64 PC_rasteropLow) m al_rom) (mkst regs1 ret M1 al_rom)
    /\ (forall a : word, ~ (s - 240 <= u a < s)%Z -> M1 a = m a) /\ mem_grows m M1 /\ cs_kept regs regs1.

(* [comment removed for export] *)
Definition rasteropLow_wa3_clip_contract : Prop :=
  forall C Ar A m md regs (s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROPLOW_STACK <= s)%Z -> (s + 64 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw -> getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx -> getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 3)) ->
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
  ((clip_d dx sx) mod 32 = 0)%Z -> ((clip_s dx sx) mod 32 = 0)%Z ->
  live A (Z_to_bv 64 datad) = Some (4 * (dwpl * dpixh))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (swpl * spixh))%Z -> Z_to_bv 64 datas <> Z_to_bv 64 datad ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
      (forall a : word, ~ scratch C s a -> ~ (datad <= bv_unsigned a < datad + 4 * (dwpl * dpixh))%Z -> m' a = m a) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_rasteropLow) m al_rom) md) S.

Theorem rasteropLow_wa3_clip_W : rasteropLow_wa3_clip_contract.
Proof.
  unfold rasteropLow_wa3_clip_contract.
  intros C Ar A m md regs s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy ret S
    CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
    Hdd Hds SHd SHs Bdx Bsx Bdy Bsy Bdw Bdh ALd ALs Ld Ld0 Ld00 Ls NEsd HK.
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
  assert (EMP : (clip_w dx sx dw dpixw spixw <= 0 \/ clip_w dy sy dh dpixh spixh <= 0)%Z ->
                realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_rasteropLow) m al_rom) md) S).
  { intros E.
    destruct (RL_EMPTY C Ar A m md regs s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy 3 ret
                CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
                Hdd Hds SHd SHs Bdx Bsx Bdy Bsy Bdw Bdh Ld Ld0 Ld00 Ls NEsd ltac:(lia) E)
      as (r1 & M1 & RUN1 & OUT1 & GR1 & CS1).
    assert (CH : forall a, M1 a <> m a -> scratch C s a).
    { intros a NE. unfold scratch.
      destruct (Z_lt_ge_dec (u a) (s - 240)); [exfalso; apply NE; apply OUT1; lia|].
      destruct (Z_lt_ge_dec (u a) s); [lia|]. exfalso; apply NE; apply OUT1; lia. }
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    apply HK.
    - apply (W_local C A m md M1 s CK HW ltac:(lia)); [|exact GR1]. intros a NE. left. exact (CH a NE).
    - exact CS1.
    - apply (POSTM_local C Ar A m md M1 s CK HW SUB). intros a NE. left. exact (CH a NE).
    - intros a Ha _. apply OUT1. unfold scratch in Ha. lia. }
  destruct (Z_lt_le_dec (clip_w dx sx dw dpixw spixw) 1) as [EW|NW]; [apply EMP; lia|].
  destruct (Z_lt_le_dec (clip_w dy sy dh dpixh spixh) 1) as [EH|NH]; [apply EMP; lia|].
  clear EMP.
  destruct (RL_PRE C Ar A m md regs s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy 3 ret
              CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
              Hdd Hds SHd SHs Bdx Bsx Bdy Bsy Bdw Bdh ALd ALs Ld Ld0 Ld00 Ls NEsd ltac:(lia) NW NH)
    as (r1 & M2 & RUN1 & OUT1 & GR1 & Cra & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & Cdh & Cswpl &
        Q2 & Q3 & Q4 & Q5 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q14 & Q16 & Q17 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q27 & Q29 & Q30 & Q31).
  pose proof (clip_facts dx sx dw dpixw spixw ltac:(lia) ltac:(lia) NW) as (CX1 & CX2 & CX3 & CX4 & CX5).
  pose proof (clip_facts dy sy dh dpixh spixh ltac:(lia) ltac:(lia) NH) as (CY1 & CY2 & CY3 & CY4 & CY5).
  assert (Hnf : (clip_w dx sx dw dpixw spixw = spixw - clip_s dx sx
                 + Z.min 0 (sx + dpixw - dx + Z.min 0 (clip_d dx sx + clip_w2 dx sx dw - dpixw) - spixw))%Z)
    by (unfold clip_w, clip_w3, clip_w2, clip_d, clip_s; lia).
  assert (Hraw : (- 2 ^ 28 <= sx <= 2 ^ 28 /\ - 2 ^ 28 <= dpixw <= 2 ^ 28 /\ - 2 ^ 28 <= dx <= 2 ^ 28 /\
                  - 2 ^ 28 <= clip_d dx sx + clip_w2 dx sx dw - dpixw <= 2 ^ 28 /\ - 2 ^ 28 <= spixw <= 2 ^ 28 /\
                  - 2 ^ 28 <= clip_s dx sx <= 2 ^ 28)%Z)
    by (unfold clip_w2, clip_d, clip_s; lia).
  set (DX := clip_d dx sx) in *. set (SX := clip_s dx sx) in *. set (DW := clip_w dx sx dw dpixw spixw) in *.
  set (DY := clip_d dy sy) in *. set (SY := clip_s dy sy) in *. set (DH := clip_w dy sy dh dpixh spixh) in *.
  set (nf := (DW / 32)%Z) in *. set (lw := (DW mod 32)%Z) in *. set (cdx := (DX / 32)%Z) in *. set (csx := (SX / 32)%Z) in *.
  pose proof (Z.div_mod DW 32 ltac:(lia)) as EDW. fold nf lw in EDW. pose proof (Z.mod_pos_bound DW 32 ltac:(lia)) as Hlw. fold lw in Hlw.
  pose proof (Z.div_mod DX 32 ltac:(lia)) as EDX. fold cdx in EDX. rewrite ALd in EDX.
  pose proof (Z.div_mod SX 32 ltac:(lia)) as ESX. fold csx in ESX. rewrite ALs in ESX.
  assert (WD : (cdx + nf + (if Z.eq_dec lw 0 then 0 else 1) <= dwpl)%Z) by (destruct (Z.eq_dec lw 0); lia).
  assert (WS : (csx + nf + (if Z.eq_dec lw 0 then 0 else 1) <= swpl)%Z) by (destruct (Z.eq_dec lw 0); lia).
  assert (HDY : (0 <= DY * dwpl)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (HSY : (0 <= SY * swpl)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hrowd : forall i, (0 <= i < DH)%Z ->
            (datad <= datad + 4 * (DY * dwpl) + 4 * cdx + 4 * (dwpl * i)
             /\ datad + 4 * (DY * dwpl) + 4 * cdx + 4 * (dwpl * i) + 4 * (nf + (if Z.eq_dec lw 0 then 0 else 1)) <= datad + nd)%Z).
  { intros i Hi.
    assert (dwpl * (DY + i + 1) <= dwpl * dpixh)%Z by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (0 <= dwpl * i)%Z by (apply Z.mul_nonneg_nonneg; lia).
    subst nd. split; lia. }
  assert (Hrows : forall i, (0 <= i < DH)%Z ->
            (datas <= datas + 4 * (SY * swpl) + 4 * csx + 4 * (swpl * i)
             /\ datas + 4 * (SY * swpl) + 4 * csx + 4 * (swpl * i) + 4 * (nf + (if Z.eq_dec lw 0 then 0 else 1)) <= datas + ns)%Z).
  { intros i Hi.
    assert (swpl * (SY + i + 1) <= swpl * spixh)%Z by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (0 <= swpl * i)%Z by (apply Z.mul_nonneg_nonneg; lia).
    subst ns. split; lia. }
  assert (HDIM : (1 <= DH < 2 ^ 24 /\ 0 <= dwpl /\ 0 <= swpl /\ dwpl * DH <= 2 ^ 30 /\ swpl * DH <= 2 ^ 30)%Z).
  { assert (dwpl * DH <= dwpl * dpixh)%Z by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (swpl * DH <= swpl * spixh)%Z by (apply Z.mul_le_mono_nonneg_l; lia).
    subst nd ns. lia. }
  assert (HAL : ((datad + 4 * (DY * dwpl) + 4 * cdx) mod 4 = 0 /\ (datas + 4 * (SY * swpl) + 4 * csx) mod 4 = 0)%Z).
  { split.
    - replace (datad + 4 * (DY * dwpl) + 4 * cdx)%Z with (datad + (DY * dwpl + cdx) * 4)%Z by ring.
      rewrite Z_mod_plus_full. exact AL4d.
    - replace (datas + 4 * (SY * swpl) + 4 * csx)%Z with (datas + (SY * swpl + csx) * 4)%Z by ring.
      rewrite Z_mod_plus_full. exact AL4s. }
  assert (SOKd : store_ok SEGS M2 (Z_to_bv 64 datad) (Z.to_nat nd) = true).
  { eapply store_ok_mono; [exact GR1 | exact (blk_sok C A m md datad nd CK HW Ld ltac:(lia) ltac:(lia) ltac:(lia))]. }
  assert (SOKs : store_ok SEGS M2 (Z_to_bv 64 datas) (Z.to_nat ns) = true).
  { eapply store_ok_mono; [exact GR1 | exact (blk_sok C A m md datas ns CK HW Ls ltac:(lia) ltac:(lia) ltac:(lia))]. }
  assert (JT : rdn SEGS M2 (Z_to_bv 64 a3_jt) 4 = Some (Z_to_le_bytes 4 a3_jtv)).
  { transitivity (rdn SEGS m (Z_to_bv 64 a3_jt) 4).
    - apply rdn_ext; unfold a3_jt; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply OUT1. lia.
    - rewrite <- p16_segs. rewrite (W_rdn_ro C A m md a3_jt 4 HW) by (unfold a3_jt; cbn; lia). rewrite p16_segs. exact jt3_rd. }
  destruct (rl3_run M2 al_rom s datad nd datas ns dwpl swpl DH
              (datad + 4 * (DY * dwpl) + 4 * cdx) (datas + 4 * (SY * swpl) + 4 * csx) DW nf lw
              (4 * (DY * dwpl)) (4 * cdx) (4 * (SY * swpl)) (4 * csx)
              sx dpixw dx (DX + clip_w2 dx sx dw - dpixw) spixw SX
              ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23)
              (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
              ltac:(lia) Hret ltac:(lia) ltac:(lia) ltac:(lia) HDIM ltac:(lia) Hrowd Hrows HAL SOKd SOKs
              ltac:(unfold disj_apart; lia) Cdh Cswpl Cra C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 JT eq_refl eq_refl Hraw Hnf
              r1 (getr r1 28) Q2 Q17 Q7 Q16 Q5 Q8 Q18 Q22 Q23 Q9 Q10 Q11 Q12 Q14 Q19 Q20 Q21 Q27 eq_refl Q29 Q30 Q31)
    as (r2 & M3 & RUN2 & INV2 & F2 & F1 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | eapply msteps_trans; [exact RUN1 | exact RUN2] |].
  destruct INV2 as [OUT2 GR2].
  assert (OUTM : forall a : word, ~ (s - 240 <= u a < s)%Z -> ~ (datad <= u a < datad + nd)%Z -> M3 a = m a).
  { intros a Ha Hb. rewrite OUT2 by lia. apply OUT1. exact Ha. }
  assert (CH : forall a, M3 a <> m a -> scratch C s a \/ (datad <= u a < datad + nd)%Z).
  { intros a NE. destruct (Z_lt_ge_dec (u a) datad) as [B1|B1];
      [| destruct (Z_lt_ge_dec (u a) (datad + nd)) as [B2|B2]; [right; lia |]];
      (left; unfold scratch;
       destruct (Z_lt_ge_dec (u a) (s - 240)); [exfalso; apply NE; apply OUTM; lia|];
       destruct (Z_lt_ge_dec (u a) s); [lia|]; exfalso; apply NE; apply OUTM; lia). }
  assert (K3 : getr r2 3 = getr regs 3) by (rewrite (AG2 3 ltac:(notin_list)); exact Q3).
  assert (K4 : getr r2 4 = getr regs 4) by (rewrite (AG2 4 ltac:(notin_list)); exact Q4).
  apply HK.
  - apply (W_local C A m md M3 s CK HW ltac:(lia)).
    + intros a NE. destruct (CH a NE) as [X|R]; [left; exact X | right].
      exists (Z_to_bv 64 datad), nd. rewrite u_Z2bv by lia. split; [exact Ld | split; [exact Ld00 | lia]].
    + eapply mem_grows_trans; [exact GR1 | exact GR2].
  - apply cs_kept_intro; csr; try reflexivity.
  - apply (POSTM_local C Ar A m md M3 s CK HW SUB). intros a NE. destruct (CH a NE) as [X|R]; [left; exact X | right].
    exists (Z_to_bv 64 datad), nd. rewrite u_Z2bv by lia. split; [exact Ld | split; [exact Ld0 | lia]].
  - intros a Ha Hb. apply OUTM; [|exact Hb]. unfold scratch in Ha. lia.
Qed.

End RopOp3W.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
