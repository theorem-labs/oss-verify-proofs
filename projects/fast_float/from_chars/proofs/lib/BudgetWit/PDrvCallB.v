(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: made from PDrvCall.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec CatSim SeqExec StepTac StoreOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Frame RefMemcpyLib DriverCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.Frame OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PDrvData RefMemchr RefStrnlen.
Import ListNotations.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import PDrvCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.BudgetWit Require Import Common_DriverCfgB Rzb.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope Z_scope.
Theorem fx_strnlen_b : forall E L ms model T (s sp ret : word) buf (K n : Z) (i : nat) (o : Z) (resl : lin),
  sden PSEGS E L ms -> s_pc L = 0x5ea30 -> s_resv L = RNone ->
  havoc_ok L [(i, o, 32)] (Some resl) = true -> PDrvCall.frame_in E L i o 32 (bv_unsigned sp - 32) ->
  getr (ms_regs ms) 1 = ret -> getr (ms_regs ms) 2 = sp -> getr (ms_regs ms) 10 = s -> getr (ms_regs ms) 11 = Z_to_bv 64 n ->
  mchrH (ms_mem ms) s buf K n -> 0 < bv_unsigned s + K -> 0x12fc0 <= bv_unsigned sp - 32 ->
  (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned s) ->
  bv_unsigned ret mod 2 = 0 -> lden E resl = Z_to_bv 64 K ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (forall E' ms', agree (s_next L) E E' -> sden PSEGS E' (havoc_call L (bv_unsigned ret) PDrvCall.KEEP [(i, o, 32)] (Some resl)) ms' ->
      frame_mod (ms_mem ms) (ms_mem ms') [(Z_to_bv 64 (bv_unsigned sp - 32), 32)] -> ms_rom ms' = ms_rom ms ->
      Rzb.rzb PSEGS DriverCfg.DCFG (mkCfg ms' model) T) ->
  Rzb.rzb PSEGS DriverCfg.DCFG (mkCfg ms model) T.
Proof.
  intros E L ms model T s sp ret buf K n i o resl Hd Hpc Hrv Hok Hfi H1 H2 H10 H11 HM Hs Hsp Hdj Hret Hres Hh Hl Hk.
  rewrite (sden_mkst PSEGS E L ms Hd Hrv). rewrite Hpc.
  set (fxs := mkFP (ms_fregs ms) (ms_fcsr ms)).
  pose proof (PDrvCall.frame_in_store_ok E L ms i o 32 _ Hd Hfi ltac:(lia)) as Hst.
  destruct (@ref_strnlen fxs (ms_mem ms) s sp buf K n (ms_rom ms) (ms_regs ms) ret HM Hs Hst Hsp Hdj
              (ret_ok_even ret Hret) H1 H2 H10 H11) as (regs' & mem' & Hrun & Hkc & Ha0 & Hfr).
  replace (Z_to_bv 64 0x5ea30) with (0x5ea30%bv : word) by (apply bv_eq; reflexivity).
  eapply Common_DriverCfgB.rz_msteps_b; [exact Hh | exact Hl | exact Hrun |].
  set (ms' := @mkst fxs regs' ret mem' (ms_rom ms)).
  destruct Hfi as (R & Hi & Ha & Hwk & Ho & Hn).
  assert (P1 : ms_pc_val ms' = Z_to_bv 64 (bv_unsigned ret)) by (cbn; symmetry; apply Z_to_bv_bv_unsigned).
  assert (P2 : forall r : reg, existsb (Pos.eqb (rkey r)) PDrvCall.KEEP = true -> rkey r <> 11%positive \/ Some resl = None ->
                 getr (ms_regs ms') r = getr (ms_regs ms) r).
  { intros r Hr _. cbn [ms_regs ms']. apply Hkc. apply PDrvCall.keep_cs. exact Hr. }
  assert (P3 : forall l, Some resl = Some l -> getr (ms_regs ms') (Z_to_bv 5 10) = lden E l).
  { intros l Hl0. injection Hl0 as <-. cbn [ms_regs ms']. transitivity (Z_to_bv 64 K); [exact Ha0 | rewrite Hres; reflexivity]. }
  assert (P4 : forall i' R' x, nth_error (s_rgs L) i' = Some R' -> in_rg E R' x -> ~ in_fp E (s_rgs L) [(i, o, 32)] x ->
                 ms_mem ms' x = ms_mem ms x).
  { intros i' R' x Hi' Hin Hnf. cbn [ms_mem ms']. destruct Hfr as [Hout _]. apply Hout.
    split; [|exact I]. unfold in_rng. intros Hx. apply Hnf. exists i, o, 32, R. split; [left; reflexivity|]. split; [exact Hi|].
    pose proof (u_range E (rg_base R)). pose proof (bv_unsigned_in_range _ sp). unfold bv_modulus in *.
    rewrite u_small64 in Hx by (unfold two64 in *; lia). lia. }
  assert (P5 : forall i' R' x, nth_error (s_rgs L) i' = Some R' -> in_rg E R' x -> ms_mem ms x <> None -> ms_mem ms' x <> None).
  { intros i' R' x Hi' Hin Hm. cbn [ms_mem ms']. destruct Hfr as [_ Hg]. exact (Hg x Hm). }
  destruct (havoc_call_sound PSEGS E L ms ms' (bv_unsigned ret) PDrvCall.KEEP [(i, o, 32)] (Some resl) Hok Hd P1 eq_refl eq_refl
              (sden_frm _ _ _ _ Hd) P2 P3 P4 P5) as (E' & Ha' & Hd').
  apply (Hk E' ms' Ha' Hd'); [exact Hfr | reflexivity].
Qed.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import Ref_code_5eb5c_5ee80.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import WalkTac SumWalkTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import P_memcpy_stmt P_memcpy.
Open Scope Z_scope.
Open Scope Z_scope.
Theorem fx_memcpy_b : forall E L ms model T (dst src : word) (n : Z) (bs old : list byte) (fp : list fpr) (resl : lin),
  sden PSEGS E L ms -> s_pc L = 0x5e2f0 -> s_resv L = RNone -> havoc_ok L fp (Some resl) = true -> ms_rom ms = seg_rom PSEGS ->
  getr (ms_regs ms) 10 = dst -> getr (ms_regs ms) 11 = src -> getr (ms_regs ms) 12 = Z_to_bv 64 n ->
  bv_unsigned (getr (ms_regs ms) 1) mod 2 = 0 ->
  bytes_at PSEGS (ms_mem ms) (bv_unsigned src) bs -> u8arr PSEGS (ms_mem ms) (bv_unsigned dst) old ->
  length old = length bs -> Z.of_nat (length bs) = n ->
  (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst) ->
  bv_unsigned dst + n < 2^64 -> bv_unsigned src + n < 2^64 ->
  lden E resl = dst ->
  (forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> bv_unsigned dst <= bv_unsigned x < bv_unsigned dst + n ->
     in_fp E (s_rgs L) fp x) ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (forall E' ms', agree (s_next L) E E' -> sden PSEGS E' (havoc_call L (bv_unsigned (getr (ms_regs ms) 1)) PDrvCall.KEEP fp (Some resl)) ms' ->
      (forall x, ~ (bv_unsigned dst <= bv_unsigned x < bv_unsigned dst + n) -> ms_mem ms' x = ms_mem ms x) ->
      (forall x, ms_mem ms x <> None -> ms_mem ms' x <> None) ->
      bytes_at PSEGS (ms_mem ms') (bv_unsigned dst) bs -> ms_rom ms' = ms_rom ms ->
      Rzb.rzb PSEGS DriverCfg.DCFG (mkCfg ms' model) T) ->
  Rzb.rzb PSEGS DriverCfg.DCFG (mkCfg ms model) T.
Proof.
  intros E L ms model T dst src n bs old fp resl Hd Hpc Hrv Hok Hrom H10 H11 H12 Hra Hb Hu Hlo Hln Hdj Hw1 Hw2 Hres Hfp Hh Hl Hk.
  rewrite (sden_mkst PSEGS E L ms Hd Hrv). rewrite Hpc, Hrom.
  set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *. set (rom := seg_rom PSEGS) in *.
  set (fxs := mkFP (ms_fregs ms) (ms_fcsr ms)).
  pose proof (memcpy_spec (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
                (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
                (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
                (getr regs 29) (getr regs 30) (getr regs 31) (ms_fregs ms) (ms_fcsr ms) mem bs old) as HS.
  assert (Hn0 : bv_unsigned (getr regs 12) = n).
  { rewrite H12, Z_to_bv_unsigned. apply bv_wrap_small. pose proof (bv_unsigned_in_range _ dst). unfold bv_modulus in *. lia. }
  specialize (HS ltac:(rewrite H11; exact Hb) ltac:(rewrite H10; exact Hu) Hlo ltac:(rewrite Hn0; exact Hln)
                 ltac:(rewrite Hn0, H10, H11; exact Hdj) ltac:(rewrite Hn0, H10; exact Hw1) ltac:(rewrite Hn0, H11; exact Hw2) Hra).
  change (mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
                (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
                (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
                (getr regs 29) (getr regs 30) (getr regs 31)) with (mkR_of regs) in HS.
  destruct (evt_bridge PSEGS fxs regs (Z_to_bv 64 0x5e2f0) mem rom _ HS) as (st & Hrun & s0 & HQ & Heqv).
  eapply Common_DriverCfgB.rz_msteps_b; [exact Hh | exact Hl | exact Hrun |].
  destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & Hmunch & Hwm & Hu8 & Hbs).
  destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ Heqv) as (fx' & regs' & -> & Hgr & _ & Hfc).
  assert (Hret : ret_pc (getr regs 1) = Z_to_bv 64 (bv_unsigned (getr regs 1))).
  { rewrite Z_to_bv_bv_unsigned. apply ret_pc_of_ret_ok. pose proof (ret_ok_even _ Hra) as R. unfold ret_ok, SeqExec.v_jalr, jalr_tgtZ in R. exact R. }
  set (ms' := @mkst fx' regs' (ret_pc (getr regs 1)) m' rom).
  assert (P1 : ms_pc_val ms' = Z_to_bv 64 (bv_unsigned (getr regs 1))) by exact Hret.
  assert (P2 : forall r : reg, existsb (Pos.eqb (rkey r)) PDrvCall.KEEP = true -> rkey r <> 11%positive \/ Some resl = None ->
                 getr (ms_regs ms') r = getr regs r).
  { intros r Hr _. cbn [ms_regs ms']. rewrite Hgr. apply PDrvCall.keep_mkR. apply PDrvCall.keep_cs. exact Hr. }
  assert (P3 : forall l, Some resl = Some l -> getr (ms_regs ms') (Z_to_bv 5 10) = lden E l).
  { intros l Hl0. injection Hl0 as <-. cbn [ms_regs ms']. rewrite Hgr, Hres. exact H10. }
  assert (Hout : forall x : word, ~ (bv_unsigned dst <= bv_unsigned x < bv_unsigned dst + n) -> m' x = mem x).
  { intros x Hx. apply Hmunch. cbn [Frame.outside]. split; [|exact I]. rewrite H10, Hn0. exact Hx. }
  assert (P4 : forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> ~ in_fp E (s_rgs L) fp x -> ms_mem ms' x = ms_mem ms x).
  { intros i R x Hi Hin Hnf. cbn [ms_mem ms']. apply Hout. intros Hc. exact (Hnf (Hfp i R x Hi Hin Hc)). }
  assert (P5 : forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> ms_mem ms x <> None -> ms_mem ms' x <> None).
  { intros i R x Hi Hin Hm. cbn [ms_mem ms']. exact (Hwm x Hm). }
  assert (P6 : frm_zero (ms_fcsr ms')) by (unfold ms', mkst; cbn [ms_fcsr]; rewrite Hfc; exact (sden_frm _ _ _ _ Hd)).
  destruct (havoc_call_sound PSEGS E L ms ms' (bv_unsigned (getr regs 1)) PDrvCall.KEEP fp (Some resl) Hok Hd P1 eq_refl eq_refl
              P6 P2 P3 P4 P5) as (E' & Ha' & Hd').
  apply (Hk E' ms' Ha' Hd'); [exact Hout | exact Hwm | | unfold ms', mkst; cbn [ms_rom]; symmetry; exact Hrom].
  cbn [ms_mem ms']. destruct Hu8 as [Hu8 _]. rewrite H10 in Hu8. exact Hu8.
Qed.
