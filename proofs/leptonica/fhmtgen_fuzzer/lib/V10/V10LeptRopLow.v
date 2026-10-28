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
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRop.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptStderr V10LeptBase V10LeptCmap2.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL7a.
Import V10CL7a.V10LeptRop_iface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require V10RopLow.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma jt_src_rd : rdn SEGS (fun _ => None) (Z_to_bv 64 0x118c4) 4 = Some (Z_to_le_bytes 4 64680).
Proof. vm_refl_bv. Qed.

Section RopLowW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Theorem rasteropLow_W : rasteropLow_contract.
Proof.
  unfold rasteropLow_contract.
  intros C Ar A m md regs s datad dpixw dpixh d dwpl dx dy dw dh datas spixw spixh swpl sx sy ret S
    CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
    Hdd Hds SHd SHs RCd RCs ALd ALs Ld Ld0 Ld00 Ls NEsd HK.
  unfold PC_rasteropLow. replace (Z_to_bv 64 0x1efe8) with (0x1efe8 : word) by (apply bv_eq; reflexivity).
  destruct SHd as (Hd & Hdpw & Hdph & Ewd & Hszd). destruct SHs as (_ & Hspw & Hsph & Ews & Hszs).
  destruct RCd as (Hdx0 & Hdy0 & Hdw1 & Hdh1 & Hdxw & Hdyh). destruct RCs as (Hsx0 & Hsy0 & _ & _ & Hsxw & Hsyh).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. unfold ROPLOW_STACK in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  assert (DV : dval d) by (unfold dval; lia).
  pose proof (wpl_of_range dpixw d ltac:(lia) DV) as Hwd. rewrite <- Ewd in Hwd.
  pose proof (wpl_of_range spixw d ltac:(lia) DV) as Hws. rewrite <- Ews in Hws.
  pose proof (wpl_bits dpixw d ltac:(lia) ltac:(lia)) as WBd. rewrite <- Ewd in WBd.
  pose proof (wpl_bits spixw d ltac:(lia) ltac:(lia)) as WBs. rewrite <- Ews in WBs.
  set (nd := (4 * (dwpl * dpixh))%Z) in *. set (ns := (4 * (swpl * spixh))%Z) in *.
  assert (Hnd : (0 < nd)%Z) by (subst nd; assert (1 * 1 <= dwpl * dpixh)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  assert (Hns : (0 < ns)%Z) by (subst ns; assert (1 * 1 <= swpl * spixh)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  destruct (blk_range C A m md (Z_to_bv 64 datad) nd CK HW Ld Hnd) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  destruct (blk_range C A m md (Z_to_bv 64 datas) ns CK HW Ls Hns) as [Gs TOPs]. rewrite u_Z2bv in Gs, TOPs by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & AL16d & _). rewrite u_Z2bv in AL16d by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ls) as (_ & AL16s & _). rewrite u_Z2bv in AL16s by lia.
  (* [comment removed for export] *)
  set (DX := (dx * d)%Z). set (SX := (sx * d)%Z). set (DW := (dw * d)%Z).
  fold DX in ALd. fold SX in ALs.
  set (nfw := (DW / 32)%Z). set (k := (DW mod 32)%Z). set (cdx := (DX / 32)%Z). set (csx := (SX / 32)%Z).
  assert (HDW0 : (1 <= DW)%Z) by (subst DW; destruct Hd as [-> | ->]; lia).
  assert (HDX0 : (0 <= DX)%Z) by (subst DX; destruct Hd as [-> | ->]; lia).
  assert (HSX0 : (0 <= SX)%Z) by (subst SX; destruct Hd as [-> | ->]; lia).
  pose proof (Z.div_mod DW 32 ltac:(lia)) as EDW. fold nfw k in EDW. pose proof (Z.mod_pos_bound DW 32 ltac:(lia)) as Hk. fold k in Hk.
  pose proof (Z.div_mod DX 32 ltac:(lia)) as EDX. fold cdx in EDX. rewrite ALd in EDX.
  pose proof (Z.div_mod SX 32 ltac:(lia)) as ESX. fold csx in ESX. rewrite ALs in ESX.
  (* [comment removed for export] *)
  assert (JT : rdn SEGS m (Z_to_bv 64 0x118c4) 4 = Some (Z_to_le_bytes 4 64680)).
  { rewrite <- p16_segs. rewrite (W_rdn_ro C A m md 0x118c4 4 HW) by (cbn; lia). rewrite p16_segs. exact jt_src_rd. }
  (* [comment removed for export] *)
  pose proof (V10RopLow.rl_run m al_rom s datad dpixh dwpl dy dh datas spixh swpl sy d dpixw dx dw spixw sx (dpixw * d) DX DW (spixw * d) SX cdx csx nfw k
              ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23)
              (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
              ltac:(lia) Hret Hd eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
              (W_sok_win C A m md (s - 240) 240 CK HW ltac:(lia) ltac:(cbn; lia))
              ltac:(split; [lia | split; [lia | apply mod16_mod4; exact AL16d]]) ltac:(split; [lia | split; [lia | apply mod16_mod4; exact AL16s]])
              JT (blk_sok C A m md datad nd CK HW Ld ltac:(lia) ltac:(lia) ltac:(lia)) (blk_sok C A m md datas ns CK HW Ls ltac:(lia) ltac:(lia) ltac:(lia))
              ltac:(unfold disj_apart; lia)
              regs H1 H2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
              H10 H11 H12 H13 H14 H15 H16 H17) as RUN.
  destruct RUN as (r1 & m1 & RUN1 & INV1 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  destruct INV1 as [OUT1 GR1].
  assert (OUTM : forall a : word, ~ (s - 240 <= u a < s)%Z -> ~ (datad <= u a < datad + nd)%Z -> m1 a = m a).
  { intros a Ha Hb. rewrite OUT1 by lia. apply (V10RopLow.M2_outside m s datad dh datas swpl ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia)); lia. }
  assert (CH : forall a, m1 a <> m a -> scratch C s a \/ (datad <= u a < datad + nd)%Z).
  { intros a NE. destruct (Z_lt_ge_dec (u a) datad) as [B1|B1];
      [| destruct (Z_lt_ge_dec (u a) (datad + nd)) as [B2|B2]; [right; lia |]];
      (left; unfold scratch;
       destruct (Z_lt_ge_dec (u a) (s - 240)); [exfalso; apply NE; apply OUTM; lia|];
       destruct (Z_lt_ge_dec (u a) s); [lia|]; exfalso; apply NE; apply OUTM; lia). }
  apply HK.
  - apply (W_local C A m md m1 s CK HW ltac:(lia)).
    + intros a NE. destruct (CH a NE) as [X|R]; [left; exact X | right].
      exists (Z_to_bv 64 datad), nd. rewrite u_Z2bv by lia. split; [exact Ld | split; [exact Ld00 | lia]].
    + eapply mem_grows_trans; [apply V10RopLow.M2_grows | exact GR1].
  - apply cs_kept_intro; csr; try reflexivity.
  - apply (POSTM_local C Ar A m md m1 s CK HW SUB). intros a NE. destruct (CH a NE) as [X|R]; [left; exact X | right].
    exists (Z_to_bv 64 datad), nd. rewrite u_Z2bv by lia. split; [exact Ld | split; [exact Ld0 | lia]].
  - intros a Ha Hb. apply OUTM; [|exact Hb]. unfold scratch in Ha. lia.
Qed.

End RopLowW.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
