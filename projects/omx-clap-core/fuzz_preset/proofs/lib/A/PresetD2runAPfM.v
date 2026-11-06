(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the proofs of tfib_file_arm_cf_A and tfib_dir_arm_cf_A of lib/A/PresetD2runA.v
   (fuzz_preset's asan image), ported from proofs/cgif/cgif_file_fuzzer/lib/A/AD26.v (relocated here as lib/A/AD26.v):
     AD26.v:156-291 m1_common       -> m1_common_cf
     AD26.v:293-318 tfib_file_arm_at / tfib_dir_arm_at -> tfib_file_arm_at_cf / tfib_dir_arm_at_cf
     AD26.v:320-331 tfib_file_arm / tfib_dir_arm       -> tfib_file_arm_cf / tfib_dir_arm_cf.
   The changes are the statement file's (PresetD2runA.v header (1)-(4)):
   (1) AR -> ARcf at Hp = [] with a8's proved laws AR_laws_ok_cf (lib/Reusable/YG0lawscf.v); cgif's model_laws ->
       a8's malloc_cf_apath_success (lib/Reusable/YGcfApath.v); AR_after_run / drv_after_call -> CwLoopB's
       AR_after_run_cf / drv_after_call_cf (lib/A/PresetD1rAx.v).
   (2) The malloc site is CwPreA's malloc_site_tfa_cf (lib/A/PresetD1preA.v), whose continuation covers every result
       of malloc_cf with `gflag tr = true`. Its PNull result is impossible here: the request (65536 bytes) is secondary
       (from_primary 65536 = false), so a8's room_cf holds at once and a8's malloc_cf_success_of_room
       (lib/Reusable/YGcfPath.v) refutes PNull; its shape premise comes from ARcf's Wf_cf (amc_wf).
       The leaf's frame exception also holds the errbuf extents (xs_cf, lib/Reusable/YG0ncf.v): xs_m1_cf places them
       below alloc_ceiling and off the image, from the leaf's xs_placed_cf and ARcf's ledger (alc_img).
   (3) The event bounds (st_nev S' <= 1, cgif's EV_MAX premise of the site) are DROPPED. In their place the room
       form of PresetD2runA.v header (2): the malloc site's pre carries NP init_state (the interface's
       PCA.iface_room_np_init), its allocator call premises use a8's ROOM_cf_init (lib/Reusable/YGcfNilInit.v), and
       the rd0 leaf's iface_room_np S' comes from the interface's PCA.iface_room_np_step (PROVISIONAL, owner
       a Theorem Labs lane) across the one malloc, from a well-formed (amc_wf), qtight (qtight_init) state with no live block.
       No headroom number. xs_placed_cf from xs_placed_cf_init and the leaf's own conjunct.
   (4) prim_pristine_except S' [] / quar_bytes S' = 0 -> prim_pristine_except S' [kBatchClass] only, from a8's
       malloc_cf_keeps_pristine_except (lib/Reusable/YGcfPristine.v, REAL since 404e3cabb354) at cs = [kBatchClass],
       with YG0k's pristine_init weakened by prim_pristine_mono. It is a theorem, not a premise.
   (5) FINV -> PresetCfnA.PINV at 0 0, kept by CwPinvA's PROVED finv_run_pinv_A_holds / finv_site_pinv_A_holds
       (lib/A/PresetPinvAPf.v:117 / :156).
   The donor's AR-free lemmas (m1c_run, at_m1c, rd0_run, win_present, EL0, EL6, usp_facts, apresent_some, the
   vm_compute facts, same_io_fs_fds, wvb_fs', wvb_fds') are cited from AD26.v.
   (6) memnorm (a Theorem Labs lane, lane MnPrefix, 2026-10-29): file_arm_tfa_cf takes `YAkMemnorm.memnorm tfibsegs (ms_mem ms)`
       and hands it to rd0_file_tfa_cf. m1_common_cf (shared with the dir arm, whose statement takes no memnorm) gives
       its continuation the keep `memnorm (ms_mem ms) -> memnorm (ms_mem ms1)`: the runs are AD2mnSeg's m1c_run_mn /
       rd0_run_mn at P := that keep (YSRrMemnorm.srr_inv_laws_imp of srr_inv_laws_memnorm_k), the malloc site's
       leaf (malloc_leaf_cf, YG0dcf.v) ends with the keep `memnorm mem -> memnorm mem'`, and the hand steps
       drv_after_call_cf / st_ok_add_cond keep the memory.
   Nothing in this file is a proof of a function (rule 24: the driver layer of a port). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK14 YK15 YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YN3q YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0k YG0f YG0n YG0d YCe5.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB12 AF0l AB1h AB13 AF0m AD2j AD2i AD1t AD20.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD2n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AD1v AD1y AD2a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AD26.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcfRoomPre YGcfTok YG07cf YGcfApath YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD1sitesA PresetD1preA PresetD2runA PresetD1rAx PresetPinvA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetPinvAPf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfPath YGcfPristine YGcfNilInit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2mnSeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetDrvSecsA PresetDrvAroA CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallStackUp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetStkUpA.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetCfnA.
Module PCA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetCfnA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section pf.
Let Hfinv_run : finv_run_pinv_A := finv_run_pinv_A_holds.     (* CwPinvA, lib/A/PresetPinvAPf.v:117 *)
Let Hfinv_site : finv_site_pinv_A := finv_site_pinv_A_holds.  (* CwPinvA, lib/A/PresetPinvAPf.v:156 *)

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {ci : CfImg} {cp : CfParams}.
Section M1.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Let ARL : AR_laws_cf tfibsegs B := AR_laws_ok_cf tfibsegs B.
(* the program interface's non-primary room and its two PROVISIONAL laws (lib/A/PresetCfnA.v section 3b) *)
Variable iface_room_np : astate -> Prop.
Hypothesis HNPi : PCA.iface_room_np_init iface_room_np.
Hypothesis HNPs : PCA.iface_room_np_step (cp := cp) iface_room_np.
Hypothesis MSITE : malloc_site_tfa_cf B iface_room_np.
Variable NR : ProcInput -> Prop.
(* a8's malloc_cf_keeps_pristine_except is a theorem (YGcfPristine.v), so no hypothesis of that name is taken. *)
Hypothesis RDF : rd0_file_tfa_cf (LS := LS) B iface_room_np NR.
Hypothesis RDD : rd0_dir_tfa_cf B iface_room_np.
Variables (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
Hypothesis Hargv : in_argv inp = [a0; p].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; p].
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hfit : entry_stack_fits sp [a0; p] (in_envp inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation EL := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).

(* NEW (no donor twin): the errbuf extents of the first malloc's frame exception (malloc_leaf_cf, YG0dcf.v) lie
   below alloc_ceiling and off the image: the leaf's xs_placed_cf keeps each extent disjoint from ly_img (one of
   static_extents) and ARcf's ledger keeps every image segment inside ly_img (alc_img). At init_state there is no
   errbuf (xs_cf ly init_state = []). *)
Lemma xs_m1_cf : forall ly ly' S' Hp (W' : world tfibsegs) mem' md' a,
ARcf tfibsegs B ly' S' Hp W' mem' md' -> xs_placed_cf ly' S' ->
Exists (in_zr a) (xs_cf ly init_state ++ xs_cf ly' S') -> a < alloc_ceiling /\ ~ YG0d.in_img tfibsegs a.
Proof.
intros ly ly' S' Hp W' mem' md' a HAR HX Hx.
change (xs_cf ly init_state) with (@nil (Z * Z)) in Hx. cbn [app] in Hx.
destruct (cfx_pick ly' S' a HX Hx) as (e & Hae & _ & Hce & Hdis).
assert (Himg : In (ly_img ly') (sec_extents ly' S' ++ static_extents ly' ++ ly_extra ly')).
{ apply in_or_app. right. apply in_or_app. left. unfold static_extents. apply in_or_app. right. right. left. reflexivity. }
pose proof (Hdis _ Himg) as Hd. unfold in_zr in Hae. split; [lia|].
intros (sg & Hsg & Ha). destruct HAR as (_ & L & _). pose proof (alc_img _ _ _ _ L sg Hsg) as [I1 I2].
unfold zdisjoint in Hd. lia.
Qed.

Section d.
Variables (W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (e : FdEntry).
Hypothesis HS1 : st_ok tfibsegs EL ss_m1 (restrict (w_H W) ms).
Hypothesis HR1 : runs_at usp (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] envp).
Hypothesis HAI1 : AI tfibsegs (w_H W) (w_A W) md.
Hypothesis HAR1 : ARcf tfibsegs B ly init_state [] W (ms_mem ms) md.
Hypothesis HTOP1 : top_ok usp ly.
Hypothesis HFI1 : PCA.PINV (aview tfibsegs (w_H W) (ms_mem ms)) 0 0.
Hypothesis Hfs1 : m_fs md = in_fs inp.
Hypothesis Hfds1 : m_fds md = APSG.fds3 e.
(* TEMPORARY (removed when the call contracts drop memnorm): memnorm of the full overlay at the
   first malloc's entry, as a fact for drv_pre_cf's memnorm conjunct; the file arm has it (its statement's premise),
   the dir arm takes it as the same TEMPORARY premise *)
Hypothesis HMN1 : YAkMemnorm.memnorm tfibsegs (ms_mem ms).

(* AD26.v:156 *)
Theorem m1_common_cf : forall KB : TSet,
(forall ws (W' : world tfibsegs) ms1 md1 ly' S' (pb : sptr),
st_ok tfibsegs (havoc EL K_M1 ws) ss_rd0 (restrict (w_H W') ms1) ->
runs_at usp (mrestrict (w_H W') (ms_mem ms1)) (runs_main_tfa true sp [a0; p] envp) ->
AI tfibsegs (w_H W') (w_A W') md1 -> ARcf tfibsegs B ly' S' [] W' (ms_mem ms1) md1 -> iface_room_np S' ->
xs_placed_cf ly' S' -> top_ok usp ly' ->
blocks S' = [(pb, 65536)] -> pb <> PNull -> sptr_addr B ly' pb = bv_unsigned (ew (havoc EL K_M1 ws) A_BUF) ->
frames S' = [] -> qtight S' -> prim_pristine_except S' [kBatchClass] ->
drv_depot_fixed B S' ->
PresetDrvSecsA.drv_secs_cf S' 65536 ->
PCA.PINV (aview tfibsegs (w_H W') (ms_mem ms1)) 0 0 ->
(YAkMemnorm.memnorm tfibsegs (ms_mem ms) -> YAkMemnorm.memnorm tfibsegs (ms_mem ms1)) ->
(* #102 (lane StackDrv): the keep of the live stack above usp (the dir arm's statement takes no stack premise) *)
(YGcallStackUp.astack_up_x tfibsegs ly W usp (ms_mem ms) -> YGcallStackUp.astack_up_x tfibsegs ly' W' usp (ms_mem ms1)) ->
m_fs md1 = in_fs inp -> m_fds md1 = APSG.fds3 e ->
srealizes tfibsegs (mkCfg ms1 md1) KB) ->
srealizes tfibsegs (mkCfg ms md) KB.
Proof.
intros KB CONT.
pose proof (AD26.EL0 sp inp xw xd a0 p) as EL0. pose proof (AD26.EL6 sp inp xw xd a0 p Hsp Hva Hve) as EL6.
pose proof (usp_facts sp Hsp) as [[Ulo Uhi] U16]. pose proof (u64_range sp) as Usp. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof m1_checks as (CK1 & CK2 & CK3 & CK4 & CK5). pose proof (top_ok_ceil _ _ HTOP1) as HCT.
pose proof (YSRrMemnorm.srr_inv_laws_imp tfibsegs (YAkMemnorm.memnorm tfibsegs) (ms_mem ms) (YSRrMemnorm.srr_inv_laws_memnorm_k tfibsegs)) as PLAW.
apply (SRr_srealizes tfibsegs W (mkCfg ms md) _ _ (AD2mnSeg.m1c_run_mn _ PLAW sp inp xw xd a0 p W ms md HS1 (fun h => h)) HAI1).
intros W0 c' _ HAI' [HAT (msk & mdk & Ec & HMK)]. destruct HAT as (-> & ms' & mat & -> & HS & HF & HFr). cbn [cfg_model] in HAI'.
injection Ec as <- <-.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) EL ss_m1c ms' HS eq_refl) as Hshape.
set (regs := ms_regs ms') in *. set (mem := ms_mem ms') in *.
set (md' := with_vm_backing (m_vm_lazy md) mat md) in *.
(* PROVISIONAL: 0x81194 = main's return address after its first malloc call (main+0x54), the same literal as the core's
   AD26.v:29 ss_m1r_eq / AF0m.v DRV_TRACES; no generated name yet (re-pin list). *)
assert (R1 : getr regs 1%bv = w64 0x81194) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) EL ss_m1c ms' 1%bv HS); reflexivity).
assert (R2 : getr regs 2%bv = Z_to_bv 64 (usp + -128)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) EL ss_m1c ms' 2%bv HS). eval_sr_get. cbn [sv_denot]. rewrite EL0. reflexivity. }
assert (R3 : getr regs 3%bv = w64 TFIB_GP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) EL ss_m1c ms' 3%bv HS); reflexivity).
assert (R4 : getr regs 4%bv = w64 TFIB_TP) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) EL ss_m1c ms' 4%bv HS); reflexivity).
assert (R8 : getr regs 8%bv = w64 2) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) EL ss_m1c ms' 8%bv HS); reflexivity).
assert (R10 : getr regs 10%bv = w64 65536) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) EL ss_m1c ms' 10%bv HS); reflexivity).
assert (Hsp' : spZ regs = usp + -128) by (unfold spZ; rewrite R2; apply u64_lit; unfold sp_window_lo in Ulo; lia).
assert (Hra : raZ regs = 0x81194) by (unfold raZ; rewrite R1; apply u64_lit; lia).
pose proof (st_ok_mem_ok tfibsegs EL ss_m1c _ HS) as HM. cbn [restrict ms_mem] in HM. fold mem in HM.
assert (Hwin : forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a).
{ intros a Ha. eapply (win_present sp Hsp EL (w_H W) mem (ss_mem ss_m1c)); [exact HM | left; reflexivity | exact EL0 | lia | lia | cbn; lia]. }
assert (HR : runs_at usp (mrestrict (w_H W) mem) (runs_main_tfa true sp [a0; p] envp)).
{ eapply (runs_at_frame EL (ss_facts ss_m1c) (ss_mem ss_m1)); [exact (st_ok_facts_ok tfibsegs EL ss_m1c _ HS) | exact wbs_m1c | exact HFr | rewrite EL0; lia | exact HR1]. }
assert (HAR : ARcf tfibsegs B ly init_state [] W mem md').
{ apply (AR_after_run_cf B HB ARL ly init_state [] W EL (ss_mem ss_m1) (ms_mem ms) mem md mat HAR1 ss_m1_win_ok); [rewrite EL0; exact Ulo | rewrite EL0; exact HCT | exact HF |].
rewrite EL0. intros a Ha. exact (apresent_some _ _ _ (Hwin a Ha)). }
pose proof (amc_wf _ _ _ _ _ (proj1 HAR)) as HWF0. pose proof HWF0 as HWP0. unfold Wf_cf in HWP0.
pose proof (amc_universe _ _ _ _ _ (proj1 HAR)) as HU.
pose proof (YGcfNilInit.ROOM_cf_init (cp := cp)) as HROOM0.
rewrite Hshape. change (Z_to_bv 64 (ss_pc ss_m1c)) with (w64 (pc_wrap_malloc Tfib_code)). rewrite <- (ts_code B HB).
fold regs mem. change (mkCfg (mkst regs (w64 (pc_wrap_malloc (as_code B))) mem (seg_rom tfibsegs)) md')
with (cfg_at tfibsegs (pc_wrap_malloc (as_code B)) regs mem md').
apply (MSITE ly init_state W regs mem md' 65536 KB).
-
split; [exact HAR|]. split; [unfold top_ok in *; tauto|].
split; [rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|]. split; [rewrite Hra; lia|].
split; [rewrite Hsp'; rewrite <- Zplus_mod_idemp_l, U16; reflexivity|].
split; [rewrite Hsp'; unfold sp_window_lo in *; lia|]. split; [rewrite Hsp'; unfold top_ok in HTOP1; lia|].
split; [rewrite Hsp'; intros a Ha; apply Hwin; unfold ASTACK in Ha; lia|].
split; [rewrite (ts_gp B HB); exact R3|]. split; [rewrite (ts_tp B HB); exact R4|].
split; [unfold s0Z; rewrite R8; unfold w64; rewrite u64_lit by lia; lia|].
split; [exact qtight_init|]. split; [exact HNPi|]. split; [exact (xs_placed_cf_init ly)|].
(* field round 3's three call facts (drv_pre_cf's last conjuncts): the hull at the start state (its meters are 0),
   memnorm across m1c_run, and the read-only bytes off ss_m1c's image cells *)
split; [exact (@cf_hull_ok_init CfParamsPreset.CfParams_preset)|]. split; [exact (HMK HMN1)|].
exact (PresetDrvAroA.drv_arodata_mem B HB (ss_mem ss_m1c) EL (w_H W) mem ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) HM).
- exact R10.
- pose proof cf_malloc_max_pos. lia.
- change (blocks_bytes init_state) with 0. unfold LIVE_MAX. lia.
- rewrite (ts_code B HB), Hra. apply (ts_universe_drv B HB). cbn. tauto.
- rewrite (ts_code B HB). apply (ts_universe_drv B HB). cbn. tauto.
- exact HAI'.
-
intros [pb S'] trc tr W' c' Htrc Hpath Hg HLEAF Hwle HAI2.
destruct HLEAF as ((ly' & regs' & mem' & md2 & Hc' & HPOST & Ha0 & HQT' & _ & HXS' & _ & _) & HMNK). subst c'.
cbn [fst snd] in HPOST, Ha0, HQT', HXS'. cbn [cfg_model] in HAI2.
unfold cfg_at. rewrite Hra.
pose proof HPOST as (HAR' & Hlyle & _ & HPres & Hio & _).
(* The PNull result is impossible: 65536 is a secondary request, so room_cf holds at once. *)
assert (Hnn : pb <> PNull).
{ exact (YGcfPath.malloc_cf_success_of_room 65536 trc init_state tr (pb, S') (YGcfPath.shape_cf_of_WfP_cf _ _ _ _ _ HWP0)
Hpath Hg ltac:(left; vm_compute; reflexivity)). }
pose proof HROOM0 as (HRm1 & HRm2 & HRm3).
destruct (malloc_cf_apath_success (as_universe B) init_state 65536 trc tr pb S' HU HWF0 ltac:(pose proof cf_malloc_max_pos; lia)
ltac:(change (blocks_bytes init_state) with 0; unfold LIVE_MAX; lia) (YG01.admits_fix _ _ init_state HU Htrc) HRm1 HRm2 HRm3 Hpath Hnn)
as (HWF' & _ & _ & Hfr0 & Hbl' & _ & _).
assert (Hblocks : blocks S' = [(pb, 65536)]) by (rewrite Hbl'; reflexivity).
assert (Hin : In (sptr_addr B ly' pb, 65536) (ablocks B ly' S')).
{ unfold ablocks. rewrite Hblocks. left. reflexivity. }
pose proof (alc_blocks _ _ ARL ly' S' [] W' mem' md2 _ _ HAR' Hin) as (_ & Hp4096 & Hpce & Hhigh & _).
(* the non-primary room after the first malloc: a8's PROVISIONAL step law from the well-formed, qtight initial state,
   which has no live block *)
assert (HRK' : iface_room_np S').
{ exact (proj1 HNPs (as_universe B) init_state 65536 trc tr pb S' HWF0 qtight_init HNPi
ltac:(change (length (blocks init_state)) with 0%nat; lia) Hpath). }
pose proof (drv_after_call_cf B HB ARL K_M1 EL ss_m1c ms' ly init_state [] W md' _ ly' S' W' regs' mem' md2 rs_m1
0x81194 usp (-128) HS eq_refl CK1 CK2 CK3 CK4 rs_m1_sub eq_refl HPOST HAR
ltac:(intros a [[_ Ha] | Hx]; [split; [unfold req_size in Ha, Hpce; cbn in Ha, Hpce; lia
| exact (proj2 (alc_client_img _ _ ARL ly' S' [] W' mem' md2 a HAR' (or_introl (ex_intro _ (sptr_addr B ly' pb) (ex_intro _ 65536 (conj Hin Ha))))))]
| exact (xs_m1_cf ly ly' S' [] W' mem' md2 a HAR' HXS' Hx)])
CK5 EL0 EL6 Hsp' ltac:(lia) Ulo HCT ltac:(intros a Ha; apply Hwin; lia)) as HS2.
rewrite ss_m1r_eq in HS2.
set (E2 := havoc EL K_M1 (map (getr regs') CLOB)) in HS2.
assert (A45 : ew E2 A_BUF = w64 (sptr_addr B ly' pb)).
{ subst E2. change A_BUF with (K_M1 + 4)%nat. rewrite (ew_havoc_new EL K_M1 _ 4 (w64 0)) by (cbn; lia). cbn. exact Ha0. }
assert (U45 : bv_unsigned (ew E2 A_BUF) = sptr_addr B ly' pb) by (rewrite A45; apply u64_lit; unfold req_size in Hpce; cbn in Hpce; lia).
apply (st_ok_add_cond tfibsegs _ _ _ Instr.BC_NE (SOff A_BUF 0) (SLit 0)) in HS2.
2:{ cbn [ac_c ac_a ac_b sv_denot Sem.branch_taken]. rewrite Z.add_0_r, U45. cbn [negb].
destruct (bv_eqb (Z_to_bv 64 (sptr_addr B ly' pb)) (Z_to_bv 64 0)) eqn:Eq; [|reflexivity].
exfalso. apply bv_eqb_eq in Eq. apply (f_equal bv_unsigned) in Eq. rewrite !u64_lit in Eq by (unfold req_size in Hpce; cbn in Hpce; lia). lia. }
apply (SRr_srealizes tfibsegs W' _ _ _ (AD2mnSeg.rd0_run_mn _ PLAW E2 W' regs' mem' md2 HS2
  (fun h => HMNK (raZ regs) regs' mem' md2 eq_refl (HMK h))) HAI2).
intros W1 c1 _ HAI3 [HAT3 (ms4 & md4 & Ec3 & HMK3)]. destruct HAT3 as (-> & ms3 & mat3 & -> & HS4 & HF3 & HFr3). cbn [cfg_model] in HAI3.
injection Ec3 as <- <-.
assert (E2_0 : bv_unsigned (ew E2 0) = usp) by (subst E2; rewrite ew_havoc_old by (unfold K_M1; lia); exact EL0).
pose proof (st_ok_mem_ok tfibsegs E2 ss_rd0 _ HS4) as HM3. cbn [restrict ms_mem] in HM3.
destruct (same_io_fs_fds _ _ Hio) as [Efs Efds].
subst E2. apply (CONT (map (getr regs') CLOB) W' ms3 _ ly' S' pb HS4).
+
eapply (runs_at_frame _ (ss_facts ss_rd0) (ss_mem ss_m1r));
[exact (st_ok_facts_ok tfibsegs _ ss_rd0 _ HS4) | exact wbs_rd0 | exact HFr3 | rewrite E2_0; lia |].
unfold runs_at in HR |- *. apply Forall_forall. intros [a bs] Hab. pose proof (proj1 (Forall_forall _ _) HR _ Hab) as (Q1 & Q2 & Q3).
cbn [fst snd] in *. split; [exact Q1|]. split; [exact Q2|].
intros j Hj. rewrite <- (Q3 j Hj). unfold mrestrict.
pose proof HPOST as (_ & _ & _ & _ & _ & Hfr & _).
assert (Hav : aview tfibsegs (w_H W') mem' (a + Z.of_nat j) = aview tfibsegs (w_H W) mem (a + Z.of_nat j)).
{ apply Hfr.
- unfold sp_window_lo in Ulo. lia.
- intros X. pose proof (alc_owned_low _ _ ARL _ _ _ _ _ _ _ HAR X). pose proof (YM05.ceil_le_top _ HCT). unfold stack_max_size in *. lia.
- intros X. pose proof (alc_owned_low _ _ ARL _ _ _ _ _ _ _ HAR' X). pose proof (YM05.ceil_le_top _ HCT). unfold stack_max_size in *. lia.
- unfold ascratch. rewrite Hsp', (ts_errno B HB). unfold TFIB_ERRNO. unfold sp_window_lo in Ulo. lia.
- intros [[_ [H1 H2]] | Hx].
* pose proof (YM05.ceil_le_top _ HCT). unfold stack_max_size in *. unfold req_size in H2, Hpce; cbn in H2, Hpce. lia.
* pose proof (proj1 (xs_m1_cf ly ly' S' [] W' mem' md2 _ HAR' HXS' Hx)). pose proof (YM05.ceil_le_top _ HCT). unfold stack_max_size in *. lia. }
pose proof (mbyte_of_aview tfibsegs _ _ _ _ _ Hav) as Hmb. unfold mbyte, mrestrict in Hmb.
pose proof (Q3 j Hj) as Q. unfold mrestrict in Q.
destruct (w_H W (Z_to_bv 64 (a + Z.of_nat j))) eqn:Hh.
{ exfalso. destruct (nth_error bs j) eqn:En; [discriminate Q | apply nth_error_None in En; lia]. }
assert (Hh' : w_H W' (Z_to_bv 64 (a + Z.of_nat j)) = false).
{ destruct (w_H W' (Z_to_bv 64 (a + Z.of_nat j))) eqn:E'; [| reflexivity]. pose proof (Hwle _ E') as X. rewrite Hh in X. discriminate X. }
rewrite Hh' in Hmb |- *. rewrite Q in Hmb.
destruct (mem' (Z_to_bv 64 (a + Z.of_nat j))) as [b'|] eqn:Em'.
* destruct (nth_error bs j) as [b|] eqn:En; [cbn in Hmb; congruence | apply nth_error_None in En; lia].
* exfalso. destruct (nth_error bs j) as [b|] eqn:En; [| apply nth_error_None in En; lia].
rewrite (seg_rom_none tfibsegs) in Hmb; [discriminate Hmb | lia | apply not_in_img_high; unfold sp_window_lo in Ulo; lia].
+ exact HAI3.
+ apply (AR_after_run_cf B HB ARL ly' S' [] W' (havoc EL K_M1 (map (getr regs') CLOB)) (ss_mem ss_m1r) mem' (ms_mem ms3) md2 mat3 HAR' ss_m1r_win_ok);
[rewrite E2_0; exact Ulo | rewrite E2_0; exact HCT | exact HF3 |].
rewrite E2_0. intros a Ha. destruct (Z.lt_ge_cases a (usp - 128)).
* apply (apresent_some (w_H W')). eapply (win_present sp Hsp _ (w_H W') (ms_mem ms3) (ss_mem ss_rd0)); [exact HM3 | left; reflexivity | exact E2_0 | lia | lia | cbn; lia].
* apply (apresent_some (w_H W')). eapply (win_present sp Hsp _ (w_H W') (ms_mem ms3) (ss_mem ss_rd0)); [exact HM3 | right; left; reflexivity | exact E2_0 | lia | lia | cbn; lia].
+ exact HRK'.
+ exact HXS'.
+ exact (top_ok_le _ _ _ _ Hlyle HTOP1).
+ exact Hblocks.
+ exact Hnn.
+ symmetry. exact U45.
+ rewrite Hfr0. reflexivity.
+ exact HQT'.
+ exact (YGcfPristine.malloc_cf_keeps_pristine_except 65536 trc init_state tr pb S' [kBatchClass]
ltac:(left; vm_compute; reflexivity) ltac:(left; reflexivity) Hpath
(prim_pristine_mono init_state [] [kBatchClass] ltac:(intros c []) pristine_init)).
+ (* the first malloc's trace is fixed and the start depot is empty (YGcfDepotStep.v) *)
  exact (drv_depot_fixed_malloc B 65536 trc init_state tr pb S' (drv_depot_fixed_init B) Htrc Hpath).
+ (* COUNT meter row A18: the first malloc from the start state, which has no secondary map entry *)
  exact (PresetDrvSecsA.drv_secs_first init_state trc tr pb S' eq_refl Hpath).
+
assert (HFIc : PCA.PINV (aview tfibsegs (w_H W) mem) 0 0)
by exact (Hfinv_run (w_H W) EL (ss_mem ss_m1) (ms_mem ms) mem usp 0 0 HFr ss_m1_win_ok EL0 Ulo HFI1).
assert (HFIp : PCA.PINV (aview tfibsegs (w_H W') mem') 0 0).
{ apply (Hfinv_site fx rc ci cp B HB ARL ASTACK ly init_state [] W regs mem md' _ ly' S' W' regs' mem' md2 usp 0 0 HAR HPOST);
[| exact HTOP1 | exact Ulo | exact Uhi | rewrite Hsp'; lia | unfold ASTACK; lia | exact HFIc].
intros a [[_ Ha] | Hx].
- right. left. exists (sptr_addr B ly' pb), 65536. exact (conj Hin Ha).
- right. right. exact (proj2 (xs_m1_cf ly ly' S' [] W' mem' md2 a HAR' HXS' Hx)). }
exact (Hfinv_run (w_H W') (havoc EL K_M1 (map (getr regs') CLOB)) (ss_mem ss_m1r) mem' (ms_mem ms3) usp 0 0 HFr3 ss_m1r_win_ok E2_0 Ulo HFIp).
+ exact HMK3.
+ (* #102 (lane StackDrv): the live stack above usp across m1c_run, the first malloc and rd0_run *)
intros HU0.
apply (PresetStkUpA.stk_up_frame _ (ss_mem ss_m1r) ly' W' mem' (ms_mem ms3) usp ss_m1r_win_ok E2_0 ltac:(lia)
  (top_ok_le _ _ _ _ Hlyle HTOP1) HF3).
apply (PresetStkUpA.stk_up_acall B ASTACK ly init_state [] W regs mem md' _ ly' S' W' regs' mem' md2 usp HB ARL HPOST HAR).
* intros a [[_ Ha] | Hx]; [unfold req_size in Ha, Hpce; cbn in Ha, Hpce; lia | exact (proj1 (xs_m1_cf ly ly' S' [] W' mem' md2 a HAR' HXS' Hx))].
* lia.
* exact HTOP1.
* exact (PresetStkUpA.stk_up_frame EL (ss_mem ss_m1) ly W (ms_mem ms) mem usp ss_m1_win_ok EL0 ltac:(lia) HTOP1 HF HU0).
+ rewrite wvb_fs', Efs. subst md'. rewrite wvb_fs', Hfs1. reflexivity.
+ rewrite wvb_fds', Efds. subst md'. rewrite wvb_fds', Hfds1. reflexivity.
Qed.
End d.

(* AD26.v:293 *)
Theorem tfib_file_arm_at_cf : forall (W : world tfibsegs) ms md ly data,
valid_fs (in_fs inp) -> NR inp -> (length p < 4096)%nat -> p <> [] -> p <> dot_path -> fs_lookup (in_fs inp) p = Some data ->
st_ok tfibsegs EL ss_m1 (restrict (w_H W) ms) ->
runs_at usp (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] envp) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly init_state [] W (ms_mem ms) md -> top_ok usp ly ->
PCA.PINV (aview tfibsegs (w_H W) (ms_mem ms)) 0 0 ->
YAkMemnorm.memnorm tfibsegs (ms_mem ms) ->
YGcallStackUp.astack_up_x tfibsegs ly W usp (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 (FdFile p (Z_to_bv 64 0)) ->
srealizes tfibsegs (mkCfg ms md) (CLOSEDX_loaded (LS := LS) data (in_fs inp)).
Proof.
intros W ms md ly data Hvfs HNR Hlen Hne Hnd Hlk HS HR HAI HAR HTOP HFI HMN HUP0 Hfs Hfds.
unfold CLOSEDX_loaded. apply (m1_common_cf W ms md ly _ HS HR HAI HAR HTOP HFI Hfs Hfds HMN).
intros ws W' ms1 md1 ly' S' pb HS1 HR1 HAI1 HAR1 HRK1 HXS1 HTOP1 Hbl Hnn Hpb HF1 HT1 HP1 HD1 HSC1 HFI1 HMK1 HSU1 Hfs1 Hfds1.
exact (RDF sp inp xw xd ws W' ms1 md1 ly' S' a0 p data pb Hargv Hsp Hva Hve Hvfs HNR Hlen Hne Hnd Hlk HS1 HR1 HAI1 HAR1 HRK1 HXS1
HTOP1 Hbl Hnn Hpb HF1 HT1 HP1 HD1 HSC1 HFI1 (HMK1 HMN) (HSU1 HUP0) Hfs1 Hfds1).
Qed.

(* AD26.v:306 *)
Theorem tfib_dir_arm_at_cf : forall (W : world tfibsegs) ms md ly,
p = dot_path ->
st_ok tfibsegs EL ss_m1 (restrict (w_H W) ms) ->
runs_at usp (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] envp) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly init_state [] W (ms_mem ms) md -> top_ok usp ly ->
PCA.PINV (aview tfibsegs (w_H W) (ms_mem ms)) 0 0 ->
(* TEMPORARY (removed when the call contracts drop memnorm): memnorm at the first malloc's entry, for drv_pre_cf's memnorm conjunct *)
YAkMemnorm.memnorm tfibsegs (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds3 FdDir ->
srealizes tfibsegs (mkCfg ms md) (CLOSEDX_dir p (in_fs inp)).
Proof.
intros W ms md ly Hdot HS HR HAI HAR HTOP HFI HMN Hfs Hfds. unfold CLOSEDX_dir.
apply (m1_common_cf W ms md ly _ HS HR HAI HAR HTOP HFI Hfs Hfds HMN).
intros ws W' ms1 md1 ly' S' pb HS1 HR1 HAI1 HAR1 HRK1 HXS1 HTOP1 Hbl Hnn Hpb _ HT1 _ _ _ _ _ _ Hfs1 Hfds1.
exact (RDD sp inp xw xd ws W' ms1 md1 ly' S' a0 p pb Hargv Hsp Hva Hve Hfit Hdot HS1 HR1 HAI1 HAR1 HRK1 HXS1 HTOP1 Hbl HT1 Hpb
Hfs1 Hfds1).
Qed.
End M1.

(* AD26.v:320 *)
Theorem tfib_file_arm_cf (B : asyms) (iface_room_np : astate -> Prop) (NR : ProcInput -> Prop) (HB : TfibSyms B)
(HNPi : PCA.iface_room_np_init iface_room_np) (HNPs : PCA.iface_room_np_step (cp := cp) iface_room_np)
(MSITE : malloc_site_tfa_cf B iface_room_np) (RDF : rd0_file_tfa_cf (LS := LS) B iface_room_np NR) : file_arm_tfa_cf (LS := LS) B NR.
Proof.
intros sp inp xw xd W ms md ly a0 p data Hargv Hsp Hva Hve Hvfs HNR Hlen Hne Hnd Hlk HS HR HAI HAR HTOP HFI HMN HUP0 Hfs Hfds.
exact (tfib_file_arm_at_cf B HB iface_room_np HNPi HNPs MSITE NR RDF sp inp xw xd a0 p Hargv Hsp Hva Hve
W ms md ly data Hvfs HNR Hlen Hne Hnd Hlk HS HR HAI HAR HTOP HFI HMN HUP0 Hfs Hfds).
Qed.

(* AD26.v:326 *)
Theorem tfib_dir_arm_cf (B : asyms) (iface_room_np : astate -> Prop) (HB : TfibSyms B)
(HNPi : PCA.iface_room_np_init iface_room_np) (HNPs : PCA.iface_room_np_step (cp := cp) iface_room_np)
(MSITE : malloc_site_tfa_cf B iface_room_np) (RDD : rd0_dir_tfa_cf B iface_room_np) : dir_arm_tfa_cf B.
Proof.
intros sp inp xw xd W ms md ly a0 p Hargv Hsp Hva Hve Hfit Hdot HS HR HAI HAR HTOP HFI HMN Hfs Hfds.
exact (tfib_dir_arm_at_cf B HB iface_room_np HNPi HNPs MSITE RDD sp inp xw xd a0 p Hargv Hsp Hva Hve Hfit
W ms md ly Hdot HS HR HAI HAR HTOP HFI HMN Hfs Hfds).
Qed.
End c.

Theorem tfib_file_arm_cf_A_holds : tfib_file_arm_cf_A.
Proof.
intros fx rc LS ci cp B iface_room_np NR HB HNPi HNPs MSITE RDF.
exact (tfib_file_arm_cf (LS := LS) B iface_room_np NR HB HNPi HNPs MSITE RDF).
Qed.

Theorem tfib_dir_arm_cf_A_holds : tfib_dir_arm_cf_A.
Proof.
intros fx rc LS ci cp B iface_room_np HB HNPi HNPs MSITE RDD.
exact (tfib_dir_arm_cf B iface_room_np HB HNPi HNPs MSITE RDD).
Qed.
End pf.

Print Assumptions tfib_file_arm_cf_A_holds.
Print Assumptions tfib_dir_arm_cf_A_holds.
