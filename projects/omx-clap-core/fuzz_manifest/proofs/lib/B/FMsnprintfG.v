(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: a new walk of fm.asan's __interceptor_vsnprintf 0x458a0; the entry-state tactics
   (pairwise_disjoint_of_extents, facts_ok), the return-address step and the epilogue state built from the saved slots
   are adapted from A/AE35.v (tfib_vprintf_icpt_A / tfib_vprintf_icpt_E). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfGvsni.v, with its module paths changed; 396 of its 461 lines of code are new or changed and 705 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMsnprintfG.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* fm's snprintf: __wrap_snprintf 0x41374 (`j 0x45cf0`) and __interceptor_snprintf 0x45cf0 (frame 0x60; a3..a7 spilled
   at sp + 0x38, the va area P; TryAsanInitFromRtl; __interceptor_vsnprintf (str, size, format, ap = P)), and
   HarnessDesign's asnprintf_realizes (FMH_Rt.v) from the chain's contracts. Written new (no released proof names
   __interceptor_snprintf). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC20 YI00 YI16 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YE34 YF0l YF0m YF0x YE20 YE2y YE3h.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMsnprintfI FMsnprintfK.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMsnprintfGI FMsnprintfGk FMsnprintfGt.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require FMsnprintfGwrc.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMsnprintfGvf FMsnprintfGvfi FMsnprintfGvsn FMsnprintfGvsni.
Import ListNotations.
Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ---- the walk's symbolic states and runs (atom 2 = the entry sp; the stack region is the chain's frame
   [sp - 0xa30 - SNK_STK, sp)) ---- *)
Definition SN_K : Z := OSP_SNI + SNK_STK.
Definition sn_regs0 : smem := YP09.mkRegion (Some 2%nat) (- SN_K) 0 (- SN_K) 0 [] :: map ro_region icpt_rodata.
Definition sn_facts0 : facts := mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4) ] [] [].
Definition ss_sn : sstate := mkSS PC_snprintf sr_atoms sn_regs0 None sn_facts0.
Definition sn_e1 : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs tbl_g FUEL A_VSNI ss_sn).
Lemma r_sn1 : sym_run_toN tfibsegs tbl_g FUEL A_VSNI ss_sn = (sn_e1, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition sn_r0 : YP09.region := Eval vm_compute in hd (YP09.mkRegion None 0 0 0 0 []) (ss_mem sn_e1).
Lemma sn_e1_mem : ss_mem sn_e1 = sn_r0 :: map ro_region icpt_rodata.
Proof. vm_compute. reflexivity. Qed.
Definition sn_e1s : sstate := set_mem sn_e1 [sn_r0].
Definition sn_s2 : sstate := Eval vm_compute in kafter 32 sn_e1s RA_VSNI (-0x60) 0 0.
Lemma sn_s2_eq : kafter 32 sn_e1s RA_VSNI (-0x60) 0 0 = sn_s2.
Proof. vm_compute. reflexivity. Qed.
Definition sn_e2 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_g FUEL sn_s2).
Lemma r_sn2 : sym_runN tfibsegs tbl_g FUEL sn_s2 = (sn_e2, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
(* what the proof reads off the two runs *)
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 r)) v.
Definition slot_is (r : YP09.region) (off : Z) (v : sv) : bool :=
  existsb (fun c => (YP09.c_off c =? off) && match YP09.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end)
    (YP09.r_chunks r).
Definition KEPT : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Lemma sn_r0_eq : sn_r0 = YP09.mkRegion (Some 2%nat) (- SN_K) 0 (- SN_K) 0 (YP09.r_chunks sn_r0).
Proof. vm_compute. reflexivity. Qed.
Lemma sn_e1_pc : ss_pc sn_e1 = A_VSNI.
Proof. vm_compute. reflexivity. Qed.
Lemma sn_e1_resv : ss_resv sn_e1 = None.
Proof. vm_compute. reflexivity. Qed.
Lemma sn_e1_r : sr_get (ss_regs sn_e1) 1 = SLit RA_VSNI /\ sr_get (ss_regs sn_e1) 2 = SOff 2 (-0x60) /\
  sr_get (ss_regs sn_e1) 10 = SOff 10 0 /\ sr_get (ss_regs sn_e1) 11 = SOff 11 0 /\
  sr_get (ss_regs sn_e1) 12 = SOff 12 0 /\ sr_get (ss_regs sn_e1) 13 = SOff 2 (-0x28) /\
  sr_get (ss_regs sn_e1) 3 = SOff 3 0 /\ sr_get (ss_regs sn_e1) 4 = SOff 4 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma sn_e1_slots : forall i, (i < 5)%nat ->
  In (YP09.mkChunk (-0x28 + 8 * Z.of_nat i) (CVal 8 (SOff (13 + i) 0))) (YP09.r_chunks sn_r0).
Proof.
intros i Hi. do 5 (destruct i as [|i]; [vm_compute; tauto|]). lia.
Qed.
Lemma sn_e2_r : forall r, In r KEPT -> sr_get (ss_regs sn_e2) (Z_to_bv 5 r) = SOff (Z.to_nat r) 0.
Proof.
intros r Hr. assert (X : forallb (fun r => reg_is sn_e2 r (SOff (Z.to_nat r) 0)) KEPT = true) by (vm_compute; reflexivity).
rewrite forallb_forall in X. unfold reg_is in X. apply sv_eqb_eq. exact (X r Hr).
Qed.
Lemma sn_e2_ra_a0 : sr_get (ss_regs sn_e2) 1 = SOff 1 0 /\ sr_get (ss_regs sn_e2) 10 = SOff 36 0 /\
  ss_resv sn_e2 = None /\ clookup tbl_g (ss_pc sn_e2) = Some RET_WORD_r.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma sn_win0 : forallb (fun t => win_eqb t (Some 2%nat, - SN_K, 0) || (snd t <=? snd (fst t))) (windows (ss_mem ss_sn)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sn_win2 : forallb (fun t => win_eqb t (Some 2%nat, - SN_K, 0) || (snd t <=? snd (fst t))) (windows (ss_mem sn_s2)) = true.
Proof. vm_compute. reflexivity. Qed.
Definition sn_r2 : YP09.region := Eval vm_compute in hd (YP09.mkRegion None 0 0 0 0 []) (ss_mem sn_e2).
Lemma sn_e2_mem0 : nth_error (ss_mem sn_e2) 0 = Some sn_r2.
Proof. vm_compute. reflexivity. Qed.
Lemma sn_r2_eq : YP09.r_base sn_r2 = Some 2%nat /\ YP09.r_wlo sn_r2 = - SN_K /\ YP09.r_whi sn_r2 = 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma aview_range : forall (Hd : word -> bool) (m : word -> option byte) a v,
  aview tfibsegs Hd m a = Some v -> 0 <= v < 256.
Proof.
intros Hd m a v H. unfold aview in H. destruct (mbyte tfibsegs (mrestrict Hd m) a) as [b|]; [|discriminate].
injection H as <-. apply u8_range.
Qed.
End s.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.

(* the stack's shadow reads 0 (the head of ARm's zero_shadow_ranges), seen through the user-poisoned ranges *)
Lemma stack_zero_shadow : forall ly S U W mem md lo len,
  ARU tfibsegs B ly S U W mem md -> ly_stk_lo ly <= lo -> lo + len <= ly_stk_hi ly -> lo mod 8 = 0 -> len mod 8 = 0 ->
  0 <= len -> zero_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF lo len.
Proof.
intros ly S U W mem md lo len HA Hlo Hhi H8 Hl8 Hl0 i Hi.
pose proof (ARU_ARm tfibsegs B ly S U W mem md HA) as HM.
pose proof (am_zshadow B ly S _ HM) as ZS. unfold zshadow_ok, zero_shadow_ranges in ZS.
apply Forall_inv in ZS. cbn [fst snd] in ZS.
pose proof (lo_top ly (am_layout B ly S _ HM)) as (_ & _ & _ & K2 & PA & _ & K1).
unfold page_aligned in PA. unfold kHighMemBeg, kHighMemEnd in *.
assert (Hlq : ly_stk_lo ly mod 8 = 0).
{ pose proof (Z.div_mod (ly_stk_lo ly) 4096 ltac:(lia)) as Dm. rewrite PA, Z.add_0_r in Dm. rewrite Dm.
  replace (4096 * (ly_stk_lo ly / 4096)) with ((ly_stk_lo ly / 4096 * 512) * 8) by ring. apply Z_mod_mult. }
set (j := (lo - ly_stk_lo ly) / 8 + i).
assert (Ej : shadow_of_addr SHADOW_OFF lo + i = shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + j).
{ unfold j, shadow_of_addr.
  pose proof (Z.div_mod lo 8 ltac:(lia)). pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(lia)).
  pose proof (Z.div_mod (lo - ly_stk_lo ly) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (lo - ly_stk_lo ly) 8 ltac:(lia)).
  assert ((lo - ly_stk_lo ly) mod 8 = 0) by (rewrite Zminus_mod, H8, Hlq; reflexivity). lia. }
rewrite Ej.
assert (Hshz : shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + j = shadow_addr (lo + 8 * i)).
{ rewrite <- Ej. unfold shadow_of_addr, shadow_addr.
  replace (lo + 8 * i) with (i * 8 + lo) by lia. rewrite Z.div_add_l by lia. lia. }
rewrite Hshz.
rewrite (ARU_view_out tfibsegs B ly S U W mem md _ HA).
- rewrite <- Hshz. apply ZS. unfold j.
  pose proof (Z.div_le_mono (lo - ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly - len) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (lo - ly_stk_lo ly) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_mod len 8 ltac:(lia)). pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)).
  pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly - len) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly - len) 8 ltac:(lia)).
  lia.
- pose proof (Z.div_mod len 8 ltac:(lia)). pose proof (Z.mod_pos_bound len 8 ltac:(lia)).
  pose proof (Z.div_pos len 8 ltac:(lia) ltac:(lia)).
  apply (ARU_shadow_out_block tfibsegs B ly S U W mem md _ HA); [lia|].
  apply (ARU_stack_not_block tfibsegs B LAWS ly S U W mem md _ HA). lia.
Qed.

(* the chain's base at sp0 = the entry sp - 0xa30 *)
Lemma snk_base_entry : forall ly S U W regs mem md,
  ecall_preU_k tfibsegs B STK_RT_PRINTF ly S U W regs mem md ->
  snk_base B ly S U W mem md (spZ regs - OSP_SNI).
Proof.
intros ly S U W regs mem md (((HAR & Hra & H16 & Hes & Hhi & Hpe & Hgp & Htp) & Hok & Hpo) & Hac & Hstk & Hpres).
assert (HA : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; assumption]).
pose proof (stk_kHighMemBeg B ly S _ (ARU_ARm tfibsegs B ly S U W mem md HA)) as [K1 K2].
assert (HC : STK_RT_PRINTF = 12288 /\ SNK_STK = 9104 /\ OSP_SNI = 2608) by (repeat split; reflexivity).
unfold kHighMemBeg, kHighMemEnd in K1, K2.
split; [exact HA|]. split; [exact Hac|]. split; [unfold kHighMemBeg in *; lia|].
split; [replace (spZ regs - OSP_SNI) with (spZ regs + (-163) * 16) by lia; rewrite Z_mod_plus_full; exact H16|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold kHighMemBeg; lia|].
split; [intros a Ha; apply Hpres; unfold snk_band in Ha; lia|].
apply (stack_zero_shadow ly S U W mem md); [exact HA | lia | lia | | reflexivity | lia].
replace (spZ regs - OSP_SNI - SNK_STK) with (spZ regs + (- 1464) * 8) by lia. rewrite Z_mod_plus_full.
pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as Dm. rewrite H16, Z.add_0_r in Dm. rewrite Dm.
replace (16 * (spZ regs / 16)) with ((spZ regs / 16 * 2) * 8) by ring. apply Z_mod_mult.
Qed.

(* the destination of HarnessDesign's premises as FMsnprintfI's snk_dest *)
Lemma snk_dest_entry : forall ly S W regs mem d n,
  wdest_ok tfibsegs B STK_RT_PRINTF ly S W regs mem d n ->
  (d + n <= FM_canary \/ FM_canary + 8 <= d) -> 0 < d -> 1 <= n <= 2 ^ 30 ->
  (forall a, d <= a < d + n -> ~ in_rom tfibsegs a) ->
  snk_dest B ly S W mem d n.
Proof.
intros ly S W regs mem d n (Hd0 & Hdhi & Ham & Hw & Hra & Hhull) Hcan Hdp Hn Hnr.
split; [exact Hdp|]. split; [exact Hdhi|]. split; [exact Hn|]. split; [exact Hcan|].
split; [|split; [exact Ham | split; [exact Hra | exact (Hhull ltac:(lia))]]].
intros a Ha. destruct (Hw a Ha) as (Hwr & Ho & _). split; [exact Hwr|]. split; [exact Ho | exact (Hnr a Ha)].
Qed.

(* st_ok with the stack region only *)
Lemma st_ok_take1 : forall E ss ms r0 rest,
  st_ok tfibsegs E ss ms -> ss_mem ss = r0 :: rest -> st_ok tfibsegs E (set_mem ss [r0]) ms.
Proof.
intros E ss ms r0 rest (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hm.
rewrite Hm in Hwf, Hok, Hpd. unfold st_ok, set_mem. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
repeat (split; [assumption|]). split; [|exact H9]. split; [|split].
- cbn [regions_wf] in *. apply andb_prop in Hwf as [Ha _]. rewrite Ha. reflexivity.
- constructor; [exact (Forall_inv Hok) | constructor].
- cbn. tauto.
Qed.

(* a run of the walk's own code whose windows lie in the stack below top (above the band too) *)
Lemma g_frame_run2 : forall ly S U W mem0 md0 sp0 top XW mem md memB mat E rs,
  snk_base B ly S U W mem0 md0 sp0 -> top <= ly_stk_hi ly ->
  snk_frame B ly S U W mem0 md0 sp0 top XW mem md ->
  (forall a, in_wrange E rs a -> sp0 - SNK_STK <= a < top) ->
  frame_of E rs mem memB ->
  (forall a, in_wrange E rs a -> apresent (w_H W) memB a) ->
  (forall a, snk_band sp0 a -> apresent (w_H W) memB a) ->
  snk_frame B ly S U W mem0 md0 sp0 top XW memB (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros ly S U W mem0 md0 sp0 top XW mem md memB mat E rs Hbase Htop HF Hwin Hfo HpW HpB.
pose proof HF as (HA & Hsb & Hp & Hfr & Hpm).
destruct Hbase as (_ & Hac & H44 & H16 & Hlo & Hhi & H47 & Hkh & _ & _).
assert (HSS : SNK_STK = 9104) by reflexivity.
pose proof (stk_kHighMemBeg B ly S _ (ARU_ARm tfibsegs B ly S U W mem md HA)) as [K1 K2].
unfold kHighMemEnd in K2.
assert (OUT : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - SNK_STK <= a < top) -> memB (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha Hb. apply Hfo. rewrite unsigned_lit_small by lia. intros Hin. exact (Hb (Hwin a Hin)). }
assert (AVB : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - SNK_STK <= a < top) ->
  aview tfibsegs (w_H W) memB a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hb. apply aview_same. exact (OUT a Ha Hb). }
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat)) as MF.
apply (g_frame_step B ly S U W mem0 md0 sp0 top XW mem md memB _ HF).
- apply (ARU_frame tfibsegs B LAWS ly S U W mem md memB _ HA).
  + intros a Hr Hown. apply AVB; [exact Hr|]. intros Hb.
    exact (ARU_stack tfibsegs B LAWS ly S U W mem md a HA ltac:(lia) Hown).
  + intros a Hv. rewrite (FMupoison.aview_mod tfibsegs (w_H W) memB a).
    rewrite (FMupoison.aview_mod tfibsegs (w_H W) mem a) in Hv.
    assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    destruct (in_wrangeb_dec E rs (a mod 2 ^ 64)) as [Hin|Hin].
    * apply aview_some_of_apresent. exact (HpW _ Hin).
    * rewrite (aview_same (w_H W) mem memB); [exact Hv|]. apply Hfo. rewrite unsigned_lit_small by lia. exact Hin.
  + apply MF. + apply MF. + apply MF.
  + intros a Ha Hh. unfold YG0d.w64.
    assert (Har : 0 <= a < kHighMemBeg) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia).
    apply OUT; [unfold kHighMemBeg in *; lia | unfold kHighMemBeg in *; lia].
- apply with_vm_backing_same.
- exact HpB.
- intros a Hr H1 H2. apply AVB; assumption.
- intros a Hpa. rewrite (apresent_mod _ memB a). rewrite (apresent_mod _ mem a) in Hpa.
  assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  destruct (in_wrangeb_dec E rs (a mod 2 ^ 64)) as [Hin|Hin]; [exact (HpW _ Hin)|].
  apply (apresent_same (w_H W) mem memB _); [apply Hfo; rewrite unsigned_lit_small by lia; exact Hin | exact Hpa].
Qed.
(* a frame with a smaller XW *)
Lemma g_frame_mono : forall ly S U W mem0 md0 sp0 top (XW XW' : Z -> Prop) mem md,
  snk_frame B ly S U W mem0 md0 sp0 top XW mem md -> (forall a, XW a -> XW' a) ->
  snk_frame B ly S U W mem0 md0 sp0 top XW' mem md.
Proof.
intros ly S U W mem0 md0 sp0 top XW XW' mem md (HA & Hsb & Hp & Hfr & Hpm) Hx.
split; [exact HA|]. split; [exact Hsb|]. split; [exact Hp|]. split; [|exact Hpm].
intros a Hr H1 H2. apply Hfr; [exact Hr | exact H1 | intros X; exact (H2 (Hx a X))].
Qed.
End p.

(* ---- __wrap_snprintf / __interceptor_snprintf from the vsnprintf interceptor's contract ---- *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis AVSNI : avsni_realizes B A_VSNI.
Lemma snprintf_of_vsni : asnprintf_realizes tfibsegs B PC_snprintf.
Proof.
intros ly S U W regs mem md d sz f ps out HPRE Hrom Hcan G10 G11 G12 Hin Hfc Hfr Hsz Hwd Hdcan Hd0 Hnr.
pose proof HPRE as (((HAR & Hra & H16 & Hes & Hhi & Hpe & Hgp & Htp) & Hok & Hpo) & Hac & Hstk & Hpres).
assert (HA : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; assumption]).
pose proof (snk_base_entry B LAWS ly S U W regs mem md HPRE) as Hbase.
pose proof (stk_kHighMemBeg B ly S _ (ARU_ARm tfibsegs B ly S U W mem md HA)) as [K1 K2].
pose proof ac_bounds as ACB.
assert (HC : STK_RT_PRINTF = 12288 /\ SNK_STK = 9104 /\ OSP_SNI = 2608 /\ SN_K = 11712 /\ OSP_VSNI = 2512 /\
  kHighMemEnd = 2 ^ 47 /\ kHighMemBeg = 17594333495296 /\ TFIB_IMG_END = 0x5f7000) by (repeat split; reflexivity).
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
set (sp := spZ regs) in *.
set (sp0 := sp - OSP_SNI) in *.
set (M := Z.of_nat (length out) + 1).
set (P := sp - 0x28).
set (args := map (fun r : Z => bv_unsigned (getr regs (Z_to_bv 5 r))) [13; 14; 15; 16; 17]) in *.
assert (Hdst : snk_dest B ly S W mem d M).
{ eapply snk_dest_entry; [exact Hwd | unfold M; lia | exact Hd0 | unfold M; lia |]. intros a Ha. apply Hnr. unfold M in Ha. lia. }
pose proof Hdst as (_ & HDhi & _ & _ & _ & HDam & _ & _).
(* the entry state *)
set (E := Ereg regs []).
assert (E2 : bv_unsigned (ew E 2) = sp) by (unfold E; rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
assert (EREG : forall (r : bv 5), ew E (Z.to_nat (bv_unsigned r)) = getr regs r) by (intros r; apply ew_Ereg_reg).
assert (E2' : bv_unsigned (ew (Ereg regs []) 2) = sp) by exact E2.
assert (HS0 : st_ok tfibsegs E ss_sn (restrict (w_H W) (mkst regs (Z_to_bv 64 PC_snprintf) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_sn. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold sn_regs0. apply Forall_cons.
    + apply (region_ok_stack tfibsegs E _ 2 sp (- SN_K)); [exact E2 | lia | lia |].
      intros a Ha. apply YE2y.apresent_writable. apply Hpres. lia.
    + exact (FMsnprintfGwrc.icpt_rodata_okU B TB ly S U W mem md E HA).
  - apply pairwise_disjoint_of_extents. unfold sn_regs0, icpt_rodata, ro_region, extent_of_region.
    cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?E2, ?E2'.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. cbn [sn_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite ?E2, ?E2'.
    change (2 ^ 4) with 16. repeat split; lia. }
pose proof (g_frame_init B ly S U W mem md sp0 sp (fun _ => False) Hbase ltac:(lia)) as F0.
unfold cfg_at. change (w64 PC_snprintf) with (Z_to_bv 64 PC_snprintf).
(* run 1: to the vsnprintf interceptor *)
eapply SRr_bind; [exact (g_phase_to W E A_VSNI ss_sn sn_e1 RS_running _ md HS0 r_sn1)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md).
assert (WIN1 : forall a, in_wrange E (ss_mem ss_sn) a -> sp - SN_K <= a < sp).
{ intros a Hwi. pose proof (in_wrange_single_b E _ a 2 (- SN_K) 0 sp sn_win0 E2 Hwi). lia. }
assert (PW1 : forall a, sp - SN_K <= a < sp -> apresent (w_H W) (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent (w_H W) E sn_e1 ms1 0 sn_r0 a HS1); [rewrite sn_e1_mem; reflexivity | |].
  - rewrite sn_r0_eq. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]. rewrite E2. lia.
  - lia. }
assert (F1 : snk_frame B ly S U W mem md sp0 sp (fun _ => False) (ms_mem ms1) md1).
{ apply (g_frame_run2 B LAWS ly S U W mem md sp0 sp _ mem md (ms_mem ms1) mat1 E (ss_mem ss_sn) Hbase ltac:(lia) F0).
  - intros a Hwi. pose proof (WIN1 a Hwi). lia.
  - exact HF1.
  - intros a Hwi. apply PW1. exact (WIN1 a Hwi).
  - intros a Hb. apply PW1. unfold snk_band in Hb. lia. }
pose proof sn_e1_r as (R1 & R2 & R10 & R11 & R12 & R13 & R3 & R4).
assert (RD : forall (r : bv 5) v, sr_get (ss_regs sn_e1) r = v -> getr (ms_regs ms1) r = sv_denot E v).
{ intros r v Hr. exact (g_reg W E sn_e1 ms1 r v HS1 Hr). }
assert (OFF : forall (r : bv 5) z, sv_denot E (SOff (Z.to_nat (bv_unsigned r)) z) = Z_to_bv 64 (bv_unsigned (getr regs r) + z)).
{ intros r z. cbn [sv_denot]. rewrite EREG. reflexivity. }
assert (Q1 : getr (ms_regs ms1) 1 = w64 RA_VSNI) by (rewrite (RD _ _ R1); reflexivity).
assert (Q2 : getr (ms_regs ms1) 2 = w64 (sp - 0x60)) by (rewrite (RD _ _ R2); cbn [sv_denot]; rewrite E2; reflexivity).
assert (Q10 : getr (ms_regs ms1) 10 = w64 d).
{ rewrite (RD _ _ R10). rewrite (OFF 10%bv 0). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact G10. }
assert (Q11 : getr (ms_regs ms1) 11 = w64 sz).
{ rewrite (RD _ _ R11). rewrite (OFF 11%bv 0). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact G11. }
assert (Q12 : getr (ms_regs ms1) 12 = w64 f).
{ rewrite (RD _ _ R12). rewrite (OFF 12%bv 0). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact G12. }
assert (Q13 : getr (ms_regs ms1) 13 = w64 P) by (rewrite (RD _ _ R13); cbn [sv_denot]; rewrite E2; reflexivity).
assert (Q3 : getr (ms_regs ms1) 3 = w64 (as_gp B)).
{ rewrite (RD _ _ R3). rewrite (OFF 3%bv 0). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hgp. }
assert (Q4 : getr (ms_regs ms1) 4 = w64 (as_tp B)).
{ rewrite (RD _ _ R4). rewrite (OFF 4%bv 0). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Htp. }
(* the arguments' slots *)
assert (SL : slots_at W (ms_mem ms1) P args).
{ intros i Hi. unfold args in Hi. cbn [length map] in Hi.
  pose proof (g_slot W E sn_e1 ms1 0 sn_r0 _ 8%N _ (nth i args 0) HS1 ltac:(rewrite sn_e1_mem; reflexivity) (sn_e1_slots i Hi)) as X.
  rewrite sn_r0_eq in X. cbn [YP09.r_base base_val] in X. rewrite E2 in X.
  replace (sp + (-0x28 + 8 * Z.of_nat i)) with (P + 8 * Z.of_nat i) in X by (unfold P; lia).
  apply X; [| pose proof (u64_range (getr regs (Z_to_bv 5 (13 + Z.of_nat i)))) | lia].
  - unfold args. cbn [sv_denot].
    assert (EN : forall n, (n < 32)%nat -> ew E n = getr regs (Z_to_bv 5 (Z.of_nat n))).
    { intros n Hn. unfold E. apply ew_Ereg_nat. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
      rewrite Z.mod_small; lia. }
    do 5 (destruct i as [|i]; [cbn [nth map Nat.add]; rewrite EN by lia; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity|]). lia.
  - unfold args. do 5 (destruct i as [|i]; [cbn [nth map]; apply u64_range|]). lia. }
(* the chain's premises at the call *)
pose proof F1 as (HA1 & Hsb1 & Hp1 & Hfr1 & Hpm1).
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - SNK_STK <= a < sp) -> a <> d ->
  aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) mem a).
{ intros a Ha H1 _. apply Hfr1; [exact Ha | exact H1 | tauto]. }
assert (DV1 : aview tfibsegs (w_H W) (ms_mem ms1) d = aview tfibsegs (w_H W) mem d).
{ apply Hfr1; [unfold amem_range in HDam; lia | lia | tauto]. }
assert (GL : gl_pre B ly S U W (ms_mem ms1) md1 sp0 d sz M f ps P args out).
{ apply (gl_pre_mk B LAWS TB ly S U W mem md (ms_mem ms1) md1 sp0 d sz M f ps P args out sp Hbase Hrom Hcan Hin Hfc);
    try assumption; try (unfold M, P, args; cbn [length map]; lia).
  - left. exact DV1. }
(* the call: kcall with the vsnprintf interceptor's contract *)
assert (HS1s : st_ok tfibsegs E sn_e1s (restrict (w_H W) ms1)) by exact (st_ok_take1 E sn_e1 _ sn_r0 _ HS1 sn_e1_mem).
pose proof sn_r0_eq as R0.
eapply SRr_bind.
{ apply (kcall W E sn_e1s ms1 md1 sp SN_K sn_r0 [] 32 RA_VSNI (-0x60) 0 0 (SN_K - 0x60) (dst_xw d M)
    (fun regs2 mem2 md2 => getr regs2 10 = w64 (Z.of_nat (length out)) /\
       (forall i, 0 <= i <= Z.of_nat (length out) -> aview tfibsegs (w_H W) mem2 (d + i) = Some (nth (Z.to_nat i) (out ++ [0]) 0)) /\
       snk_frame B ly S U W (ms_mem ms1) md1 sp0 (sp0 + OSP_VSNI) (dst_xw d M) mem2 md2)
    HS1s ltac:(exact sn_e1_resv) E2 eq_refl).
  - rewrite R0. reflexivity.
  - rewrite R0. reflexivity.
  - rewrite R0. reflexivity.
  - rewrite R0. cbn. lia.
  - rewrite R0. cbn. lia.
  - exact R1.
  - exact R2.
  - vm_compute. reflexivity.
  - rewrite sn_s2_eq. vm_compute. reflexivity.
  - rewrite sn_s2_eq. vm_compute. reflexivity.
  - rewrite sn_s2_eq. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - intros a Hx Hr. exfalso. unfold dst_xw in Hx. lia.
  - intros r a Hr. destruct Hr.
  - intros r a Hr. destruct Hr.
  - intros a Ha. apply PW1. lia.
  - unfold cfg_at. change (ss_pc sn_e1s) with A_VSNI.
    eapply SRr_mono.
    + apply (AVSNI ly S U W (ms_regs ms1) (ms_mem ms1) md1 sp0 d sz M f ps P args out GL).
      * split; [rewrite Q1; apply ret_ok_lit; [unfold RA_VSNI; lia | reflexivity]|]. split; [rewrite Q2; f_equal; unfold sp0; lia|].
        split; [exact Q3 | exact Q4].
      * unfold sp0, P. lia.
      * unfold sp0. lia.
      * intros a Ha. apply PW1. unfold sp0 in Ha. lia.
      * exact Q10.
      * exact Q11.
      * exact Q12.
      * exact Q13.
    + intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HFR & Hap & G10' & HD').
      split; [reflexivity|]. exists regs2, mem2, md2.
      pose proof HFR as (_ & Hsb2 & _ & Hfr2 & Hpm2).
      split; [unfold raZ; rewrite Q1; unfold w64; rewrite unsigned_lit_small by (unfold RA_VSNI; lia); reflexivity|].
      split; [exact Hap|]. split; [exact Hsb2|]. split.
      * intros a Ha H1 H2. apply Hfr2; [exact Ha | unfold sp0 in *; lia | exact H2].
      * split; [exact Hpm2 | split; [exact G10' | split; [exact HD' | exact HFR]]]. }
intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & Hap2 & Hfr2 & Hpm2 & (G10b & HDb & FRb)).
rewrite sn_s2_eq in HS2.
set (md2 := with_vm_backing (m_vm_lazy md1) mat2 md1) in *.
set (E2v := havoc E 32 (map (getr (ms_regs ms2)) CLOB)) in *.
assert (E22 : bv_unsigned (ew E2v 2) = sp) by (unfold E2v; rewrite ew_havoc_old by lia; exact E2).
assert (F2 : snk_frame B ly S U W mem md sp0 sp (dst_xw d M) (ms_mem ms2) md2).
{ pose proof FRb as (HA2 & Hsb2 & Hp2 & Hfr2' & Hpm2').
  apply (g_frame_step B ly S U W mem md sp0 sp (dst_xw d M) (ms_mem ms1) md1 (ms_mem ms2) md2).
  - apply (g_frame_mono B ly S U W mem md sp0 sp (fun _ => False)); [exact F1 | tauto].
  - exact HA2.
  - exact Hsb2.
  - exact Hp2.
  - intros a Ha H1 H2. apply Hfr2'; [exact Ha | unfold sp0 in *; lia | exact H2].
  - exact Hpm2'. }
(* run 2: the epilogue *)
eapply SRr_bind; [exact (g_phase W E2v sn_s2 sn_e2 (RS_stopped (SR_jalr (SOff 1 0))) ms2 md2 HS2 r_sn2)|].
intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3).
set (md3 := with_vm_backing (m_vm_lazy md2) mat3 md2) in *.
assert (WIN2 : forall a, in_wrange E2v (ss_mem sn_s2) a -> sp - SN_K <= a < sp).
{ intros a Hwi. pose proof (in_wrange_single_b E2v _ a 2 (- SN_K) 0 sp sn_win2 E22 Hwi). lia. }
assert (PW3 : forall a, sp - SN_K <= a < sp -> apresent (w_H W) (ms_mem ms3) a).
{ intros a Ha. pose proof sn_r2_eq as (B2 & L2 & H2).
  apply (st_ok_window_apresent (w_H W) E2v sn_e2 ms3 0 sn_r2 a HS3 sn_e2_mem0); [|lia].
  rewrite B2, L2, H2. cbn [base_val]. rewrite E22. lia. }
assert (F3 : snk_frame B ly S U W mem md sp0 sp (dst_xw d M) (ms_mem ms3) md3).
{ apply (g_frame_run2 B LAWS ly S U W mem md sp0 sp _ (ms_mem ms2) md2 (ms_mem ms3) mat3 E2v (ss_mem sn_s2) Hbase ltac:(lia) F2).
  - intros a Hwi. pose proof (WIN2 a Hwi). lia.
  - exact HF3.
  - intros a Hwi. apply PW3. exact (WIN2 a Hwi).
  - intros a Hb. apply PW3. unfold snk_band in Hb. lia. }
pose proof sn_e2_ra_a0 as (S1 & S10 & Srv & Sret).
apply (g_ret W E2v sn_e2 ms3 md3 _ HS3 Srv Sret).
intros mat'. cbv beta. split; [reflexivity|].
set (md4 := with_vm_backing (m_vm_lazy md3) mat' md3).
pose proof F3 as (HA3 & Hsb3 & Hp3 & Hfr3 & Hpm3).
assert (RD3 : forall (r : bv 5) v, sr_get (ss_regs sn_e2) r = v -> getr (ms_regs ms3) r = sv_denot E2v v).
{ intros r v Hr. exact (g_reg W E2v sn_e2 ms3 r v HS3 Hr). }
assert (EOLD : forall (r : bv 5), (Z.to_nat (bv_unsigned r) < 32)%nat -> ew E2v (Z.to_nat (bv_unsigned r)) = getr regs r).
{ intros r Hr. unfold E2v. rewrite ew_havoc_old by exact Hr. apply EREG. }
assert (RA3 : getr (ms_regs ms3) 1 = getr regs 1).
{ rewrite (RD3 _ _ S1). cbn [sv_denot]. rewrite Z.add_0_r.
  change 1%nat with (Z.to_nat (bv_unsigned (1%bv : bv 5))). rewrite EOLD by (vm_compute; lia). apply Z_to_bv_bv_unsigned. }
exists (ms_regs ms3), (ms_mem ms3), md4.
split.
{ unfold cfg_at. rewrite RA3. unfold ret_ok in Hra. rewrite Hra. unfold raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (HA4 : ARU tfibsegs B ly S U W (ms_mem ms3) md4).
{ pose proof (same_but_materialized_frame md3 _ (with_vm_backing_same md3 mat')) as MF.
  apply (ARU_frame tfibsegs B LAWS ly S U W (ms_mem ms3) md3 (ms_mem ms3) md4 HA3);
    [intros; reflexivity | intros a Hv; exact Hv | apply MF | apply MF | apply MF | intros; reflexivity]. }
split; [exact (ARU_AR tfibsegs B ly S U W _ _ HA4)|].
split; [exact (ARU_poisoned tfibsegs B ly S U W _ _ HA4)|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hin2 : In r KEPT) by (unfold KEPT; cbn [In]; lia).
  rewrite (RD3 _ _ (sn_e2_r r Hin2)). cbn [sv_denot]. rewrite Z.add_0_r.
  assert (Hr5 : bv_unsigned (Z_to_bv 5 r) = r).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia. }
  replace (Z.to_nat r) with (Z.to_nat (bv_unsigned (Z_to_bv 5 r))) by (rewrite Hr5; reflexivity).
  rewrite EOLD by (rewrite Hr5; lia). apply Z_to_bv_bv_unsigned. }
split; [eapply same_but_materialized_trans; [exact Hsb3 | apply with_vm_backing_same]|].
split.
{ rewrite (RD3 _ _ S10). cbn [sv_denot]. rewrite Z.add_0_r.
  assert (X : ew E2v 36 = getr (ms_regs ms2) 10).
  { unfold E2v, havoc. cbn [ew]. reflexivity. }
  rewrite X, Z_to_bv_bv_unsigned. exact G10b. }
split.
{ intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  assert (Hav : aview tfibsegs (w_H W) (ms_mem ms3) (d + Z.of_nat j) = Some (nth j (out ++ [0]) 0)).
  { rewrite (aview_same (w_H W) (ms_mem ms2) (ms_mem ms3)).
    - rewrite (HDb (Z.of_nat j) ltac:(lia)). rewrite Nat2Z.id. reflexivity.
    - apply HF3. rewrite unsigned_lit_small by (unfold amem_range in HDam; lia). intros Hwi.
      pose proof (WIN2 _ Hwi). unfold M in *. lia. }
  split; [exact (val_mem1_of_aview (w_H W) (ms_mem ms3) _ _ Hav) | exact (aview_range _ _ _ _ Hav)]. }
split.
{ intros a Ha H1 H2. apply Hfr3; [exact Ha | lia | unfold dst_xw, M; lia]. }
exact Hpm3.
Qed.
End m.

(* ---- the chain: snprintf from the contracts of printf_common, printf_core (both passes), the flush, memset ---- *)
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis APCOMMON : apcommon_realizesU B A_PCOM.
Hypothesis APCORE : apcore_realizesU B A_PCORE.
Hypothesis APCORE0 : apcore0_realizesU B A_PCORE.
Hypothesis AFLUSH : asnflush_realizesU B A_SNW.
Hypothesis AMEMSET : aintrin_realizesU B OSet W_MEMSET.
Hypothesis AMEMCPY : aintrin_realizesU B OCpy W_MEMCPY.
Theorem snprintf_realizesU : asnprintf_realizes tfibsegs B PC_snprintf.
Proof.
pose proof (avfp_ok B LAWS TB APCORE0 APCORE AFLUSH) as AVFP.
pose proof (avfpi_ok B LAWS TB APCOMMON AVFP) as AVFPI.
pose proof (avsn_ok B LAWS TB AMEMSET AVFPI) as AVSN.
pose proof (avsni_ok B LAWS TB APCOMMON AVSN) as AVSNI.
exact (snprintf_of_vsni B LAWS TB AVSNI).
Qed.
End f.
