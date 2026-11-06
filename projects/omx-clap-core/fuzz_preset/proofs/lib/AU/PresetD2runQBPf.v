(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the proof of tfib_run_Q_cf_B of lib/AU/PresetD2runQB.v (fuzz_preset's asan-ubsan
   image), ported from proofs/cgif/cgif_file_fuzzer/lib/YD2d.v (relocated here as lib/Reusable/YD2d.v):
     YD2d.v:251-333 tfib_run_Q_empty -> tfib_run_Q_empty_cf
     YD2d.v:334-387 tfib_run_Q_at    -> tfib_run_Q_at_cf, tfib_run_Q -> tfib_run_Q_cf.
   The asan twin is lib/A/PresetD2runQAPf.v (lane CwRunqA, 345a4039cd2); this file is its text through port/a2b.py
   (sha256 b9c3f16342596f93d7e64903139a40399c87c0b7440f92e288113ad664f5a77c, --lib): 0 code lines differ. Lane
   CwPinvB's finv_run_pinv_B is PROVED (finv_run_pinv_B_holds, lib/AU/PresetPinvBPf.v at a working branch
   7ea213877203), cited as a Let, so the result takes no premise beyond its statement's.
   The changes are the statement files' (PresetD2runB.v header (1)-(6)): AR -> ARcf at Hp = [] with a8's proved
   laws AR_laws_ok_cf (lib/Reusable/YG0lawscf.v); the event bounds are dropped; the tail is CwSites' tail_at_pinv_B
   B NP (lib/AU/PresetD1sitesB.v), whose non-primary room NP S and xs_placed_cf pass unchanged along the symbolic
   runs (no allocator call between the header and the loop / the payload malloc); FINV -> PINV at 0 0, kept across
   a driver run by CwPinvB's PROVED finv_run_pinv_B_holds (lib/AU/PresetPinvBPf.v:117). The empty-payload arm enters
   CwLoopB's loop (PresetD1rB.loop_L_cf_B) at r = calls data,
   cnt = ran = 0; the nonempty arm hands CwRunqm's PresetD2eB.run_QM_tfa_cf its tail. The donors' AR-free lemmas
   are cited from the donor files; its two runs pe_run / pm_run are their memnorm twins (lib/Reusable/YD2mnSeg.v, at
   P := YAkMemnorm.memnorm tfibsegs with YSRrMemnorm.srr_inv_laws_memnorm_k), so the tail's memnorm of the full
   overlay reaches the loop head (LOOPL's memnorm premise) and RUNQM's tail (lane MnPrefix).
   Nothing in this file is a proof of a function (rule 24: the driver layer of a port). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0f YG0v YG0n YG0d YCe5.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB12 YF0l YB1h YB13 YF0m YD2j YD2i YD1t YD20 YD1v YD1y YD26 YD24.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD21 YD25 YD23 YD2h YD1w YD2f YD2b YD2g YD1s YD2c YD2d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01.
(* (YE2k / YD1u are not imported: no name of theirs is used, and YD1u is gated; the twin drops them too.) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcfRoomPre YGcfTok YG07cf YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD1sitesB PresetD2runB PresetD2runQB PresetD1rBx PresetPinvB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetPinvBPf.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetD2eB.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetD1rB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2mnSeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallStackUp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetStkUpB.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetCfnB.
Module PCB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetCfnB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section pf.
(* lane CwPinvB's proved finv_run_pinv_B (lib/AU/PresetPinvBPf.v) *)
Let Hfinv_run : finv_run_pinv_B := finv_run_pinv_B_holds.

(* ---------------------------------------------------------------------- *)
(* 2. RUNQ: YD2d.v:251 tfib_run_Q_empty, YD2d.v:334 tfib_run_Q_at, at CfParams_preset (the loop's instance).      *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {ci : CfImg}.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
Hypothesis Hfrm : YK0o.frm_zero (@YK11.fp_csr fx).
Section g.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Let ARL : AR_laws_cf tfibsegs B := AR_laws_ok_cf tfibsegs B.
Variable iface_room_np : astate -> Prop.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Variable NR : ProcInput -> Prop.
Variable sm : list Z -> Z * Z.
Hypothesis LOOPL : PresetD1rB.loop_L_cf_B (LS := LS) B xst NR sm iface_room_np.
Hypothesis HWMAX : (4 * YCbqGwild.K_LLVMF <= u_wmax (as_universe B))%nat.
Hypothesis RUNQM : PresetD2eB.run_QM_tfa_cf (LS := LS) B iface_room_np NR.
Variables (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
Hypothesis Hargv : in_argv inp = [a0; p].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; p].
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvfs : valid_fs (in_fs inp).
Hypothesis HNR : NR inp.
#[local] Notation EL := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation envp := (in_envp inp).

(* YD2d.v:251 *)
Theorem tfib_run_Q_empty_cf : forall ws (W : world tfibsegs) ms md ly S data (pb : sptr) cap,
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data -> payload_len data = 0 ->
let E3 := E_P (edset (havoc EL K_M1 ws) 2 data) data (sptr_addr B ly pb + 2 + config_len data) in
tail_at_pinv_B B iface_room_np (sQ (config_len data =? 0) (Z.of_nat (calls data))) E3 sp inp a0 p data W ms md ly S pb cap ->
YGcallStackUp.astack_up_x tfibsegs ly W usp (ms_mem ms) ->
bv_unsigned (ew E3 K_PP) = sptr_addr B ly pb + 2 + config_len data ->
srealizes tfibsegs (mkCfg ms md) (run_shape (LS := LS) (payload data) (calls data) (in_fs inp)).
Proof.
intros ws W ms md ly S data pb cap Hlk Hok Hpl0 E3 HT HUP0 E60.
pose proof (YSRrMemnorm.srr_inv_laws_memnorm_k tfibsegs) as PLAW.
destruct HT as (HS & E41 & E42 & HR & HAI & HAR & HRK & HTOP & Hbl & Hcap & HLc & HBLK & Hfs & Hfds & Hminv & HPI & HXS & HMN).
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
pose proof (top_ok_ceil _ _ HTOP) as HCT. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
set (buf := sptr_addr B ly pb) in *. set (c0 := config_len data =? 0) in *. set (k := Z.of_nat (calls data)) in *.
pose proof (config_len_bound data) as Hcl. pose proof (calls_bound data) as Hcb. unfold dlen in *.
assert (Hin : In (buf, cap) (ablocks B ly S)) by (unfold ablocks; rewrite Hbl; left; reflexivity).
pose proof (alc_blocks _ _ ARL ly S [] W (ms_mem ms) md _ _ HAR Hin) as (_ & Hb4096 & Hbce & _).
assert (Hcap' : cap <= req_size cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
assert (E3_0 : bv_unsigned (ew E3 0) = usp) by (subst E3; rewrite E_P_old by lia; cbn [ew edset]; rewrite ew_havoc_old by (unfold K_M1; lia); reflexivity).
assert (Ed2 : ed E3 2 = data) by (subst E3; rewrite E_P_ed by lia; reflexivity).
destruct (list_len3 data ltac:(lia)) as (d0 & d1 & d2 & rest & Ed).
assert (UPL : U E3 sv_pl00 = payload_len data).
{ apply (U_pl00 E3 data d0 d1 (d2 :: rest) Ed2 Ed); unfold dlen; [exact E42 | lia | lia]. }
assert (Hk : 1 <= k <= 4) by (subst k; lia).
assert (Hk1 : c0 = true -> k = 1).
{ subst c0 k. intros Hz. unfold calls, cfg_byte. rewrite Hz. reflexivity. }
assert (HS1 : st_ok tfibsegs E3 (add_cond (sQ c0 k) cond_PL0) (restrict (w_H W) ms)).
{ apply (st_ok_add_cond tfibsegs E3 (sQ c0 k) _ BC_EQ sv_pl00 (SLit 0) HS). rewrite branch_eq_U, UPL, U_SLit, Hpl0. reflexivity. }
apply (SRr_srealizes tfibsegs W (mkCfg ms md) _ _ (YD2mnSeg.pe_run_mn _ PLAW c0 k E3 W ms md HS1 HMN) HAI).
intros W0 c' _ HAI1 [(-> & ms1 & mat1 & -> & HS2 & HF1 & HFr1) (msA & mdA & EcA & HMN1)]. injection EcA as <- <-. cbn [cfg_model] in HAI1.
pose proof (pe_to_L c0 k E3 W ms1 (payload_len data) HS2 UPL ltac:(unfold payload_len, dlen, HDR_MIN; lia) Hk Hk1) as (HSL & V61 & V62 & V63 & V65).
set (E4 := E_L E3 (ms_regs ms1)) in *.
assert (E4old : forall j, (j < K_L)%nat -> ew E4 j = ew E3 j) by (intros j Hj; subst E4; unfold E_L; apply ew_havoc_old; exact Hj).
pose proof (st_ok_mem_ok tfibsegs E3 _ _ HS2) as HM2. cbn [restrict ms_mem] in HM2.
pose proof HM2 as HMB.
destruct (sPE_img_facts B HB c0 k E3 (w_H W) (ms_mem ms1) HMB) as [HIMG HRO].
assert (WOK : forallb drv_win_ok (ss_mem (sQ c0 k)) = true) by (subst c0; unfold sQ; destruct (config_len data =? 0); [exact (proj1 sQ_win_ok) | exact (proj2 sQ_win_ok k)]).
(* #102 (lane StackDrv): the live stack above usp across pe_run (its frame is below usp) *)
assert (HUP1 : YGcallStackUp.astack_up_x tfibsegs ly W usp (ms_mem ms1))
by exact (PresetStkUpB.stk_up_frame E3 _ ly W (ms_mem ms) (ms_mem ms1) usp WOK E3_0 ltac:(lia) HTOP HF1 HUP0).
assert (Hwin : forall a, usp - 65536 <= a < usp -> apresent (w_H W) (ms_mem ms1) a).
{ intros a Ha. destruct c0; destruct (Z.lt_ge_cases a (usp - 128)).
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms1) (ss_mem sPE0)); [exact HMB | left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms1) (ss_mem sPE0)); [exact HMB | right; left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms1) (ss_mem (sPE1 k))); [exact HMB | left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms1) (ss_mem (sPE1 k))); [exact HMB | right; left; reflexivity | exact E3_0 | lia | lia | cbn; lia]. }
change (run_shape (LS := LS) (payload data) (calls data) (in_fs inp)) with (loop_tgt (LS := LS) (payload data) (calls data) 0%nat (calls data) (in_fs inp)).
apply (LOOPL fx Hfrm sp inp xw xd E4 W ms1 (with_vm_backing (m_vm_lazy md) mat1 md) ly S a0 p data pb PNull cap 0 0%nat (calls data) (in_fs inp) 0 0
Hargv Hsp Hva Hve Hvfs HNR Hlk ltac:(unfold dlen; lia)).
- intros j Hj. rewrite E4old by (unfold K_L, K_M1 in *; lia). subst E3. rewrite E_P_old by (unfold K_M1 in Hj; lia). cbn [ew edset]. apply ew_havoc_old. exact Hj.
- change (ed E4 2) with (ed E3 2). exact Ed2.
- rewrite E4old by (unfold K_L, A_BUF; lia). exact E41.
- rewrite E4old by (unfold K_L, A_LEN; lia). exact E42.
- rewrite E4old by (unfold K_L; lia). exact E60.
- rewrite V61. reflexivity.
- rewrite V62, (proj2 (Z.eqb_eq _ _) Hpl0). reflexivity.
- exact V63.
- rewrite V65. subst k. reflexivity.
- exact HSL.
- lia.
- lia.
- left. split; [exact Hpl0|]. split; [reflexivity | exact Hbl].
-   intros Hp. exfalso. lia.
- exact (proj1 (proj2 (proj2 Hminv))).
- exact (proj1 (proj2 (proj2 (proj2 Hminv)))).
- exact HRK.
- apply (drv_wild_room_entry B S); [exact (proj1 (proj2 (proj2 (proj2 (proj2 Hminv))))) |
  apply (Nat.le_trans _ (4 * YCbqGwild.K_LLVMF)); [apply Nat.mul_le_mono_r; pose proof (calls_bound data); lia | exact HWMAX]].
- (* the interface's P8 premise at the loop entry, before any harness call: CwRunqm's iface_room_at_driver, with
     A18's driver base at the tail state (drv_rp_base_B, from drv_minv_cf's count) *)
exact (PresetD2eB.iface_room_at_driver sm _ (as_universe B) S (amc_wf _ _ _ _ _ (proj1 HAR))
(proj1 (proj2 (proj2 (proj2 Hminv)))) ltac:(rewrite Hbl; cbn; lia) (proj1 (drv_rp_base_B B S cap _ Hminv Hcap))).
- exact HXS.
- exact HAI1.
- apply (AR_after_run_cf B HB ARL ly S [] W E3 _ (ms_mem ms) (ms_mem ms1) md mat1 HAR WOK); [rewrite E3_0; exact Ulo | rewrite E3_0; exact HCT | exact HF1 |].
rewrite E3_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin a Ha)).
- exact HTOP.
- unfold PCB.LCNT, PCB.SIZE_MAX. lia.
- exact Hcap.
- unfold dlen. lia.
- left. split; [reflexivity | exact HIMG].
- exact HRO.
-   exact (Hfinv_run (w_H W) E3 _ (ms_mem ms) (ms_mem ms1) usp 0 0 HFr1 WOK E3_0 Ulo HPI).
- (* memnorm at the loop head: pe_run_mn's end memory; pe_to_L keeps the configuration *)
exact HMN1.
- (* #102: the loop's stack invariant *)
exact HUP1.
-   split; [intros k0; rewrite wvb_fds', Hfds; reflexivity|].
split; [rewrite wvb_fs'; exact Hfs | exact (proj1 Hvfs)].
Qed.

(* YD2d.v:334. The nonempty arm builds CwSites' tail_at_pinv_B at the payload-malloc state, as the donor builds
   tail_at, and hands it to CwRunqm's run_QM_tfa_cf (PresetD2eB.v), whose tail premise is that same tail. *)
Theorem tfib_run_Q_at_cf : forall ws (W : world tfibsegs) ms md ly S data (pb : sptr) cap,
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data ->
let E3 := E_P (edset (havoc EL K_M1 ws) 2 data) data (sptr_addr B ly pb + 2 + config_len data) in
tail_at_pinv_B B iface_room_np (sQ (config_len data =? 0) (Z.of_nat (calls data))) E3 sp inp a0 p data W ms md ly S pb cap ->
YGcallStackUp.astack_up_x tfibsegs ly W usp (ms_mem ms) ->
bv_unsigned (ew E3 K_PP) = sptr_addr B ly pb + 2 + config_len data ->
srealizes tfibsegs (mkCfg ms md) (run_shape (LS := LS) (payload data) (calls data) (in_fs inp)).
Proof.
intros ws W ms md ly S data pb cap Hlk Hok E3 HT HUP0 E60.
destruct (Z.eqb_spec (payload_len data) 0) as [Hpl0 | Hpl1]; [exact (tfib_run_Q_empty_cf ws W ms md ly S data pb cap Hlk Hok Hpl0 HT HUP0 E60)|].
pose proof (YSRrMemnorm.srr_inv_laws_memnorm_k tfibsegs) as PLAW.
destruct HT as (HS & E41 & E42 & HR & HAI & HAR & HRK & HTOP & Hbl & Hcap & HLc & HBLK & Hfs & Hfds & Hminv & HPI & HXS & HMN).
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
pose proof (top_ok_ceil _ _ HTOP) as HCT. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
set (buf := sptr_addr B ly pb) in *. set (c0 := config_len data =? 0) in *. set (k := Z.of_nat (calls data)) in *.
pose proof (config_len_bound data) as Hcl. unfold dlen in *.
assert (Hin : In (buf, cap) (ablocks B ly S)) by (unfold ablocks; rewrite Hbl; left; reflexivity).
pose proof (alc_blocks _ _ ARL ly S [] W (ms_mem ms) md _ _ HAR Hin) as (_ & Hb4096 & Hbce & _).
assert (Hcap' : cap <= req_size cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
assert (NIMG : forall a, buf <= a < buf + cap -> ~ in_img tfibsegs a).
{ intros a Ha. assert (Ha' : buf <= a < buf + req_size cap) by lia.
exact (proj2 (alc_client_img _ _ ARL ly S [] W (ms_mem ms) md a HAR (or_introl (ex_intro _ _ (ex_intro _ cap (conj Hin Ha')))))). }
assert (E3_0 : bv_unsigned (ew E3 0) = usp) by (subst E3; rewrite E_P_old by lia; cbn [ew edset]; rewrite ew_havoc_old by (unfold K_M1; lia); reflexivity).
assert (Ed2 : ed E3 2 = data) by (subst E3; rewrite E_P_ed by lia; reflexivity).
destruct (list_len3 data ltac:(lia)) as (d0 & d1 & d2 & rest & Ed).
assert (UPL : U E3 sv_pl00 = payload_len data).
{ apply (U_pl00 E3 data d0 d1 (d2 :: rest) Ed2 Ed); unfold dlen; [exact E42 | lia | lia]. }
assert (Hplpos : 0 < payload_len data) by (unfold payload_len, dlen, HDR_MIN in *; lia).
assert (HS1 : st_ok tfibsegs E3 (add_cond (sQ c0 k) cond_PL1) (restrict (w_H W) ms)).
{ apply (st_ok_add_cond tfibsegs E3 (sQ c0 k) _ BC_NE sv_pl00 (SLit 0) HS). rewrite branch_ne_U, UPL, U_SLit. change (zcanon 0) with 0.
apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
apply (SRr_srealizes tfibsegs W (mkCfg ms md) _ _ (YD2mnSeg.pm_run_mn _ PLAW c0 k E3 W ms md HS1 HMN) HAI).
intros W0 c' _ HAI1 [(-> & ms1 & mat1 & -> & HS2 & HF1 & HFr1) (msA & mdA & EcA & HMN1)]. injection EcA as <- <-. cbn [cfg_model] in HAI1.
pose proof (st_ok_mem_ok tfibsegs E3 _ _ HS2) as HM2. cbn [restrict ms_mem] in HM2.
assert (WOK : forallb drv_win_ok (ss_mem (sQ c0 k)) = true) by (subst c0; unfold sQ; destruct (config_len data =? 0); [exact (proj1 sQ_win_ok) | exact (proj2 sQ_win_ok k)]).
(* #102 (lane StackDrv): the live stack above usp across pm_run *)
assert (HUP1 : YGcallStackUp.astack_up_x tfibsegs ly W usp (ms_mem ms1))
by exact (PresetStkUpB.stk_up_frame E3 _ ly W (ms_mem ms) (ms_mem ms1) usp WOK E3_0 ltac:(lia) HTOP HF1 HUP0).
assert (Hwin : forall a, usp - 65536 <= a < usp -> apresent (w_H W) (ms_mem ms1) a).
{ intros a Ha. destruct c0; destruct (Z.lt_ge_cases a (usp - 128)).
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms1) (ss_mem sPM0)); [exact HM2 | left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms1) (ss_mem sPM0)); [exact HM2 | right; left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms1) (ss_mem (sPM1 k))); [exact HM2 | left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms1) (ss_mem (sPM1 k))); [exact HM2 | right; left; reflexivity | exact E3_0 | lia | lia | cbn; lia]. }
assert (HT1 : tail_at_pinv_B B iface_room_np (if c0 then sPM0 else sPM1 k) E3 sp inp a0 p data W ms1 (with_vm_backing (m_vm_lazy md) mat1 md) ly S pb cap).
{ split; [exact HS2|]. split; [exact E41|]. split; [exact E42|]. split.
{ eapply (runs_at_frame E3 (ss_facts (if c0 then sPM0 else sPM1 k)) (ss_mem (sQ c0 k)));
[exact (st_ok_facts_ok tfibsegs E3 _ _ HS2) | | exact HFr1 | rewrite E3_0; lia | exact HR].
subst c0. unfold sQ. pose proof wbs_PM as [WQ0 WQ1]. destruct (config_len data =? 0); [exact WQ0 | exact (WQ1 k)]. }
split; [exact HAI1|]. split.
{ apply (AR_after_run_cf B HB ARL ly S [] W E3 _ (ms_mem ms) (ms_mem ms1) md mat1 HAR WOK); [rewrite E3_0; exact Ulo | rewrite E3_0; exact HCT | exact HF1 |].
rewrite E3_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin a Ha)). }
split; [exact HRK|]. split; [exact HTOP|]. split; [exact Hbl|]. split; [exact Hcap|]. split; [unfold dlen; lia|]. split.
{ unfold dlen. apply (blk_of_frame_r _ _ _ _ _ buf (Z.of_nat (length data)) data usp HFr1 WOK E3_0 Ulo); [intros a Ha; apply NIMG; lia | lia | lia | exact HBLK]. }
split; [rewrite wvb_fs'; exact Hfs |]. split; [rewrite wvb_fds'; exact Hfds |]. split; [exact Hminv|]. split; [| split; [exact HXS | exact HMN1]].
exact (Hfinv_run (w_H W) E3 _ (ms_mem ms) (ms_mem ms1) usp 0 0 HFr1 WOK E3_0 Ulo HPI). }
apply (RUNQM sp inp xw xd ws W ms1 _ ly S a0 p data pb cap Hargv Hsp Hva Hve Hvfs HNR Hlk ltac:(unfold dlen; lia) Hplpos); [| exact HUP1 | exact E60].
fold buf E3. change (if config_len data =? 0 then sPM0 else sPM1 (Z.of_nat (calls data))) with (if c0 then sPM0 else sPM1 k).
exact HT1.
Qed.
End g.

(* YD2d.v:388 *)
Theorem tfib_run_Q_cf (B : asyms) (HB : TfibSyms B) (iface_room_np : astate -> Prop)
(xst : nat -> (word -> bool) -> (word -> option byte) -> Prop) (NR : ProcInput -> Prop) (sm : list Z -> Z * Z)
(LOOPL : PresetD1rB.loop_L_cf_B (LS := LS) B xst NR sm iface_room_np)
(HWMAX : (4 * YCbqGwild.K_LLVMF <= u_wmax (as_universe B))%nat)
(RUNQM : PresetD2eB.run_QM_tfa_cf (LS := LS) B iface_room_np NR) : run_Q_tfa_cf (LS := LS) B iface_room_np NR.
Proof.
intros sp inp xw xd ws W ms md ly S a0 p data pb cap Hargv Hsp Hva Hve Hvfs HNR Hlk Hok E3 HT HUP0 E60.
exact (tfib_run_Q_at_cf B HB iface_room_np xst NR sm LOOPL HWMAX RUNQM sp inp xw xd a0 p Hargv Hsp Hva Hve Hvfs HNR ws W ms md ly S data pb cap Hlk Hok HT HUP0 E60).
Qed.
End e.


Theorem tfib_run_Q_cf_B_holds : tfib_run_Q_cf_B.
Proof.
intros fx rc LS ci B iface_room_np xst NR sm Hfrm HB LOOPL HWMAX RUNQM.
exact (tfib_run_Q_cf (LS := LS) Hfrm B HB iface_room_np xst NR sm LOOPL HWMAX RUNQM).
Qed.
End pf.

Print Assumptions tfib_run_Q_cf_B_holds.
