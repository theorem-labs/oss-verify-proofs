(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from tfib_drv_main of proofs/cgif/cgif_file_fuzzer/lib/A/AD1p.v:36-121
   (asan; its asan-ubsan twin is lib/YD1p.v:29-114), for fuzz_preset's ASan image. The statement only; the proof is
   lib/A/PresetD1pAPf.v. Nothing in this file is a proof of a function (rule 24: no function proved; composition /
   driver layer of a port).
   tfib_drv_main_A states the driver walk proper: from the certified state at `main`, the ASan build realizes
   CLOSEDX at preset's library shape, on every input on which the plain build is never refused memory at the
   agreement's plain budget. Changes from the donor (closedwalk-plan.md 1d, 1e, 2b, 2f; the parent's design change
   of 2026-10-28 22:44Z, which moves the AR -> ARcf switch to the allocator's initial state):
   (1) the no-refusal premise of preset's TFIB_T, `~ run_scfg_budget_refused Env.alloc_forced_only Images.plain
       Budgets.Asan.lim_source en_p inp`, with its entry en_p, is a premise. The conclusion is the text of
       drv_mainX_stmt_A rc HS_tfib (lib/A/PresetD1qA.v section 2, lane CwD1q), spelled out here;
   (2) the library shape is ZTraceSpec.checksum_shape, passed explicitly;
   (3) the program slot is the program interface preset_lib_contract_x (lib/A/PresetCfnA.v) in place of cgif's
       tfib_lib_contract_x, at its interface vocabulary ablocks_cf / afn_pre_cf / ajournal_cf, universally quantified
       here with PresetCfnA.v's types (PROVISIONAL: a8 / walkkit bodies pending), at CfParams_preset;
   (4) EVERY allocator-facing site is over a8's ARcf at Hp = [] (no hidden head is outstanding between harness
       calls, and none exists before the first): the realizers AMALLOC / AFREE / AICPY are a8's _cf forms, and
       ARDCHK, FWS, RFS, FPO, FPR, FPU, PF1, PFN, EXS are the core's site forms with cgif's AR replaced by ARcf. The
       switch from cgif's AR is made once, at the allocator's initial state, inside the proof (ARcf_nil_init);
   (5) cgif's event cap `st_nev S < EV_MAX` is dropped from the restated site forms: the cf instance has no event
       regime (YGcfNames.v: model_laws_cf has no st_nev premise).
   Dropped from the donor: nothing else of the Section's arguments; the Lets (AD1p.v:40-41, :50-55, :69-83) are the
   leaves, which the proof file takes from their lanes.
   Literals: the three fprintf format addresses are the core's relocated values (lib/A/AD1p.v:66-68) and are preset
   asan's strings (closedwalk-plan.md 2c: 0x1d83c / 0x1d851 / 0x158a1); the refused-site format 0x19746 and its
   numeral 67108864 are the core's (lib/A/AD1x.v:87). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetD1pA.v, with its module paths changed; 151 of its 206 lines of code are new or changed and 166 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: made from tfib_drv_main of proofs/cgif/cgif_file_fuzzer/lib/A/AD1p.v:36-121
   (asan; its asan-ubsan twin is lib/YD1p.v:29-114), for fuzz_preset's ASan image. The statement only; the proof is
   lib/A/PresetD1pAPf.v. Nothing in this file is a proof of a function (rule 24: no function proved; composition /
   driver layer of a port).
   tfib_drv_main_A states the driver walk proper: from the certified state at `main`, the ASan build realizes
   CLOSEDX at preset's library shape, on every input that satisfies the input predicate NR (at TFIB_T: the plain
   build is never refused memory at the agreement's plain budget). Changes from the donor (the internal file closedwalk-plan.md 1d,
   1e, 2b, 2f; the parent's design change
   of 2026-10-28 22:44Z, which moves the AR -> ARcf switch to the allocator's initial state):
   (1) the input premise is a predicate NR on the entry and the input (parent's decision 2026-10-29 06:02Z, for the
       halts tops' OBLIGATIONS row H_drv_main_halts_X), in place of the literal no-refusal premise of preset's
       TFIB_T; that premise, `~ run_scfg_budget_refused Env.alloc_forced_only Images.plain Budgets.Asan.lim_source
       en_p inp`, is the instance NR := fun en_p inp => ~ run_scfg_budget_refused .. en_p inp, at which CwD2 takes
       this statement. The conclusion is the text of drv_mainX_stmt_A rc HS_tfib (lib/A/PresetD1qA.v section 2,
       lane CwD1q), spelled out here;
   (2) the library shape is ZTraceSpec.checksum_shape, passed explicitly;
   (3) the program slot is the program interface preset_lib_contract_x_all (lib/A/PresetCfnA.v, 
       a working branch 3f83c075b61f) in place of cgif's tfib_lib_contract_x, at its Section variables: the
       build's strtod model sm, the PROVISIONAL non-primary room iface_room_np, B, MT, XM_LIB / XN_LIB and
       PAYLOAD_ROOM; its frame names (afn_pre_cf, ajournal_cf, apost_base_cf, ablocks_cf) are the interface's
       constants, so they are not quantified here; its listing class L / PA (RO_IN now reads PA's relro range in
       place of cgif's RLO / RHI). The slot, the free realizer and the post-call sites (PF1, PFN, EXS) are taken at
       every FP state, since a harness call returns at the callee's fx';
   (3a) the room, in the interface's form. The run-level start-up bound `4 * N_LLVMF + 24 <= K_INIT` of the
       earlier text (pushed 61da04ae7317) is DELETED with N_LLVMF: it made the run layer vacuous (K_INIT = 14,335
       against at least 9,696 allocator steps per harness call; a Theorem Labs lane's note, the internal file n-llvmf.md).
       The run's primary room is a Theorem Labs lane's P8 (a working branch 4ec915e66b6, lib/Spec/PresetP8.v
       preset_room), the interface's state conjunct iface_room_at, which the leaves derive at the first call and
       the slot's post carries; nothing about it is a premise here. A driver state carries only the interface's
       non-primary room iface_room_np, a PROVISIONAL Section variable of the interface (owner a Theorem Labs lane,
       room_live_cf), so its three laws, stated in PresetCfnA.v section 3b, are PROVISIONAL premises here, by the
       interface's names: NPI (iface_room_np_init: it holds at init_state), NPS (iface_room_np_step: one driver
       malloc_cf / free_cf keeps it, under Wf_cf, qtight and at most three driver blocks) and NPT
       (iface_room_np_tail: it gives a site's ROOM_cf_k S 2). They go when a8's lib/A/CfRoomLivePreset.v gives
       iface_room_np a body;
   (4) EVERY allocator-facing site is over a8's ARcf at Hp = [] (no hidden head is outstanding between harness
       calls, and none exists before the first): the realizers AMALLOC / AFREE / AICPY are a8's _cf forms, and
       ARDCHK, FWS, RFS, FPO, FPR, FPU, PF1, PFN, EXS are the core's site forms with cgif's AR replaced by ARcf. The
       switch from cgif's AR is made once, at the allocator's initial state, inside the proof (a Theorem Labs lane's
       ARcf_nil_init, lib/Reusable/YGcfNilInit.v:37, a working branch 5d91379f2041);
   (4a) the allocator rows AMALLOC / AFREE are in their keep forms, YGcfMallocComposeKeep.amalloc_realizes_cf_keep /
       afree_realizes_cf_rh_keep (the leaf's memnorm keep at its end configuration), AFREE the primed free contract
       under the re-hide;
   (5) cgif's event cap `st_nev S < EV_MAX` is dropped from the restated site forms: the cf instance has no event
       regime (YGcfNames.v: model_laws_cf has no st_nev premise);
   (6) NEW premise PROOM, the payload-room bridge of the internal file closedwalk-plan.md 2f (the interface's PAYLOAD_ROOM from the
       no-refusal premise; trivial at PAYLOAD_ROOM := fun _ => True);
   (7) the earlier premises ABL / AFL / AJL (CwLoopA's PROVISIONAL links of the then quantified interface
       vocabulary to ARcf) are DELETED: the interface's frame names are constants now (iface 3f83c075b61f);
   (8) memnorm (the interface's header item (8), a working branch 446222ec0601; lane MnPrefix): NO
       premise. The loop's named premise PresetD1rA.H_memnorm_drv_A (its three runner segments vp_run / br_run /
       l2_run keep YAkMemnorm.memnorm tfibsegs) is PROVED (lib/A/PresetD1rAmn.v H_memnorm_drv_A_holds, by the core
       twins of lib/A/AD2mnSeg.v), so the earlier premise HMND is deleted. Memnorm at the loop head comes from main:
       the start-up invariant SINV0 carries memnorm of FULL (core YA02.v SINV0_mn; YA0j.ho_memnorm at the hand-off),
       arm_argv2 takes it, and every prefix leaf keeps it across its runner segments (twins / in-place re-runs) and
       its call sites (the malloc / free leaves' keep, memcpy's AICPY in the keep form below, the read check's keep
       in ARDCHK : aread_check_stmt_cf).
   (9) the live real stack (#102; the interface's header item (13), the slot pre's last conjunct
       YGcallStackUp.astack_up_x at each harness call): the named premise H_stackup_main_A (section 3 below) states,
       at main's entry (the certified state this walk starts from) and the start-up world W1, that every byte of
       [usp - 64 KiB, ly_top ly) is present. It is the statement of the start-up lane's main-entry lemma
       stack_up_main_W1_A (StartupCert, lib/A/Prog/StackUpMainA.v, over the kit's widened argH0 in lib/Reusable/YA02.v:
       the argv NULL word and LPS's slack up to the entry page top). The walk carries the part above usp to each
       harness call (lib/A/PresetStkUpA.v; PresetD1rA.v header item (11)).
   Dropped from the donor: the LIB Let (AD1p.v:55; parent's ruling: the loop inlines the YD1m bridge and takes the
   interface directly) and every obligation on cgif's output file (A_WB, A_TRAILER, A_PATH: none is named here; the
   donor's AD1p.v:102 FINV handoff that carried them is PINV now, in the proof file). The other Lets (AD1p.v:40-41,
   :50-54, :69-83) are the leaves, which the proof file takes from their lanes.
   Literals: the three fprintf format addresses are the core's relocated values (lib/A/AD1p.v:66-68) and are preset
   asan's strings (the internal file closedwalk-plan.md 2c: 0x1d845 / 0x1d85a / 0x158b3); the refused-site format 0x1979c and its
   numeral 67108864 are the core's (lib/A/AD1x.v:87). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Images.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK15 YK18 YK0c YK0e YK09 YA0c YA0e YA01 YA02 YA00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB12 AB01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK00 YK0s YP0n YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YK04 YA0i YA0n YA0o YA0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0k YG0f YG0v YG0n YG0d YCe5 YL02 YG08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0l AF0m AD2j AD2i AD1t AD20 AD1v AD2h AD2f AD1w AD1x AD1i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0ncf YG0dcf YG0d2cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YP0b YPsym YC4aP YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfImgA CfParamsPreset PresetCfnA.
(* CITED, never copied (the parent's ruling: one definition per predicate):
   lane IfacePort (a working branch 3f83c075b61f, lib/A/PresetCfnA.v): preset_lib_contract_x_all,
   iface_room_np_init, iface_room_np_step, iface_room_np_tail;
   lane CwSites (a working branch 9f95abaab5bd: printf_post_cf with the memnorm keep): printf_first_cf,
   printf_next_cf, exit_site_cf;
   lane CwPreA (a working branch 3d2de00623dc): aread_check_stmt_cf, fwrite_site_tfa_cf,
   refused_site_tfa_cf, fprintf_s_site_tfa_cf.
   Each site form is the core's with cgif's AR replaced by ARcf; they take {fx rc ci cp}: tfib_drv_main_A passes
   cp := CfParams_preset by name, takes the sites a harness call can precede at every fx (after a call the FP state is
   the callee's fx'), and the image's CfImg_A (the only CfImg in scope, a local instance below) fills ci. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD1sitesA PresetD1preA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Base.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild YK0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfImgRows.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD1g.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.

#[local] Existing Instance YK11.fx0.
(* a8's CfImg_A (lib/A/CfImgA.v) is a Definition; it is made the local instance here so that the forms that take
   {ci} get the asan image's, and no other CfImg exists in this file's scope. *)
#[local] Existing Instance CfImg_A.

(* ---------------------------------------------------------------------- *)
(* 2. The driver walk proper. Donor: lib/A/AD1p.v:85-96, with the Section arguments of :37-69 as premises. *)
Definition tfib_drv_main_A : Prop :=
forall (rc : YM05.RunCeil)
(* the image's listing class (lib/Reusable/YC4aP.v PAImg), whose relro range the interface reads *)
(L : YP0b.ptable YPsym.asym) (PA : YC4aP.PAImg L)
(* the build's strtod model and the PROVISIONAL non-primary room: the interface's Section variables
   (lib/A/PresetCfnA.v section 5) *)
(sm : list Z -> Z * Z)
(iface_room_np : astate -> Prop)
(* the PROVISIONAL laws of iface_room_np (PresetCfnA.v section 3b; owner a Theorem Labs lane) *)
(NPI : iface_room_np_init iface_room_np)
(NPS : iface_room_np_step (ci := CfImg_A) (cp := CfParams_preset) iface_room_np)
(NPT : iface_room_np_tail (cp := CfParams_preset) iface_room_np)
(B : asyms) (HB : TfibSyms B)
(AMALLOC : YGcfMallocComposeKeep.amalloc_realizes_cf_keep (cp := CfParams_preset) tfibsegs B)
(* the post-loop frees run after a harness call, at the callee's FP state *)
(AFREE : forall fx : YK11.FPState, YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fx) (cp := CfParams_preset) tfibsegs B)
(* the payload / grow memcpy text in a Theorem Labs lane's keep form (lane MnPrefix: the read loop and RUNQM keep memnorm
   across their memcpy calls; YGcallMxmn.aintrin_realizes_xm is aintrin_realizes_cf with the keep as its last post
   conjunct) *)
(AICPY : YGcallMxmn.aintrin_realizes_xm tfibsegs B (ARcf (cp := CfParams_preset) tfibsegs B) OCpy (pc_wrap_memcpy (as_code B)))
(ARDCHK : aread_check_stmt_cf (cp := CfParams_preset) B)
(MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z)
(MT_FREE : forall S m, mo_ok MT S m)
(* the listing's relro range is read-only (the donor's RO_IN over RLO / RHI, now over PA's range) *)
(RO_IN : forall a, @YC4aP.pa_relro_lo rc L PA <= a < @YC4aP.pa_relro_hi rc L PA -> in_ro_tfa a)
(PAYLOAD_ROOM : list byte -> Prop)
(* the input predicate (change (1)): at TFIB_T it is the agreement's no-refusal premise *)
(NR : ExecEntry -> ProcInput -> Prop)
(* the payload-room bridge (the internal file closedwalk-plan.md 2f; NEW, no donor): the room the program interface asks of each
   call's payload follows from the input predicate. At NR en_p it is the bridge premise of CwLoopA's loop_L_x_A;
   at PAYLOAD_ROOM := fun _ => True (lib/A/PresetCfnA.v section 5) it holds trivially. *)
(PROOM : forall (en_p : ExecEntry) (inp : ProcInput) (a0 p data : list byte),
  NR en_p inp -> in_argv inp = [a0; p] -> fs_lookup (in_fs inp) p = Some data -> PAYLOAD_ROOM (payload data))
(* the program slot at every FP state (preset_lib_contract_x_all: each call returns at the callee's fx') *)
(LIBC : preset_lib_contract_x_all (rc := rc) (LS := ZTraceSpec.checksum_shape) (L := L) (PA := PA)
  sm iface_room_np B MT XM_LIB XN_LIB PAYLOAD_ROOM)
(* #102 (no-DW interface, PresetCfnA.v, first at commit 8259b94c42ee): the slot pre's universe closure at the slot's
   context set, state-free; the closed top takes it from the instance's universe *)
(UNIV : @PRH_Base.prh_univ_closure PresetCfnA.preset_prh_img B CfImg_A PresetCfnA.iface_ctx0)
(* the instance universe's wild room covers the loop's four calls (true by conversion at TfibB) *)
(HWMAX : (4 * YCbqGwild.K_LLVMF <= u_wmax (as_universe B))%nat)
(* the listing's entry is the driver's call target (PresetD1rA.v loop_L_x_A_at) *)
(HSIG : @YC4aP.pa_sigma rc L PA YPsym.AS_LLVMFuzzerTestOneInput = 0x815e0)
(xst : nat -> (word -> bool) -> (word -> option byte) -> Prop)
(XFR : xst_frame_tfa xst)
(PF1 : forall fx : YK11.FPState, printf_first_cf (fx := fx) (cp := CfParams_preset) B xst)
(PFN : forall fx : YK11.FPState, printf_next_cf (fx := fx) (cp := CfParams_preset) B xst)
(est : (word -> bool) -> (word -> option byte) -> Prop)
(ESTI : est_img_tfa est)
(ESTF : est_frame_tfa est)
(FWS : fwrite_site_tfa_cf (cp := CfParams_preset) B est)
(RFS : refused_site_tfa_cf (cp := CfParams_preset) B est)
(FPO : fprintf_s_site_tfa_cf (cp := CfParams_preset) B est 0x1d845 (strB "cli: cannot open "%string) nlB)
(FPR : fprintf_s_site_tfa_cf (cp := CfParams_preset) B est 0x1d85a (strB "cli: read error on "%string) nlB)
(FPU : fprintf_s_site_tfa_cf (cp := CfParams_preset) B est 0x158b3 (strB "usage: "%string) (strB " INPUT"%string ++ nlB))
(EXS : forall fx : YK11.FPState, exit_site_cf (fx := fx) (cp := CfParams_preset) B est xst),
forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (en_p : ExecEntry)
(h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
valid_sp sp -> valid_brk Asan.M.loaded_segments brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
NR en_p inp ->
@YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
HS_tfib h = Some ch ->
cs_ok Asan.M.loaded_segments TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 Asan.M.loaded_segments Asan.M.phdrs sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(YA02.argH0 Asan.M.phdrs sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 Asan.M.phdrs sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) n) ->
(forall a, YA02.argH0 Asan.M.phdrs sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a = true ->
FULL a = wrap_mem Asan.M.phdrs sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a) ->
srealizes Asan.M.loaded_segments (cfg_of Asan.M.loaded_segments R (pc ch) FULL model)
(CLOSEDX (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape) inp).

(* ---------------------------------------------------------------------- *)
(* 3. THE MAIN-ENTRY PRESENCE PREMISE (#102, header item (9)). At the certified state at main (the hand-off h of the
   start-up certificate, the binders of tfib_drv_main_A), at the start-up world W1 (the hidden set H1, with its band
   fact H1_8), for a layout whose top is page aligned and within top_ok of usp (AD1g.ly0: layout_ok and
   AD1f.tfib_top_ok), every byte of [usp - 64 KiB, ly_top) is present: not hidden by H1 and mapped in FULL. It is the
   statement of the start-up lane's stack_up_main_W1_A (lib/A/Prog/StackUpMainA.v, over the kit's argH0 change in
   lib/Reusable/YA02.v, a working branch 87cf0d0d06f6: the argv NULL word and LPS's slack up to the
   entry page top), which PROVES it: lib/A/PresetD1pAPfC.v H_stackup_main_A_holds. *)
Definition H_stackup_main_A : Prop :=
forall (rc : YM05.RunCeil) (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput)
(Hsp : valid_sp sp) (Hva : valid_argv (in_argv inp)) (Hve : valid_envp (in_envp inp))
(Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp))
(h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
HS_tfib h = Some ch ->
cs_ok Asan.M.loaded_segments TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 Asan.M.loaded_segments Asan.M.phdrs sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(YA02.argH0 Asan.M.phdrs sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
(forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 Asan.M.phdrs sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) n) ->
(forall a, YA02.argH0 Asan.M.phdrs sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E a = true ->
FULL a = wrap_mem Asan.M.phdrs sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a) ->
forall (H1_8 : forall a : Z, YG0f.in_band_rw a ->
  AD2i.H1 sp rdraw inp ch E model (Z_to_bv 64 a) = AD2i.H1 sp rdraw inp ch E model (Z_to_bv 64 (a - a mod 8))),
forall ly : alayout, ly_top ly mod 4096 = 0 -> AD1v.top_ok (rc := rc) (bv_unsigned sp) ly ->
forall a, bv_unsigned sp - 65536 <= a < ly_top ly -> apresent (w_H (AD2i.W1 sp rdraw inp Hsp Hva ch E model H1_8)) FULL a.

(* ---------------------------------------------------------------------- *)
(* 4. THE ALLOCATOR SWITCH'S START-UP PREMISES (cf layer field rounds 2-3): the named premises of
      YGcfNilInit.ARcf_nil_init at the driver's binders (the certified state at main, as section 3), one per premise.
      The driver walk (lib/A/PresetD1pAPf.v) takes them as Section hypotheses and its tops carry them by name. *)
(* the init model's lazy and noaccess maps lie in its maps (ARcf's alc_lazy_in_maps at the start);
   supplied by: start-up rows (the kit owner) *)
Definition H_start_lazy_A : Prop :=
forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput)
(h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
HS_tfib h = Some ch ->
cs_ok Asan.M.loaded_segments TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 Asan.M.loaded_segments Asan.M.phdrs sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(YA02.argH0 Asan.M.phdrs sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
forall x, YK0g.covered (vm_noaccess (m_vmmaps model) ++ m_vm_lazy model) x = true ->
YK0g.covered (vm_maps (m_vmmaps model)) x = true.
(* the start witness of the RegionInfo + 68 bytes and the errbuf object (YG0ncf.start_cells_cf) at the start-up
   world W1; supplied by: start-up rows (the kit owner) *)
Definition H_start_cells_A : Prop :=
forall (rc : YM05.RunCeil) (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput)
(Hsp : valid_sp sp) (Hva : valid_argv (in_argv inp))
(h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
HS_tfib h = Some ch ->
cs_ok Asan.M.loaded_segments TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 Asan.M.loaded_segments Asan.M.phdrs sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(YA02.argH0 Asan.M.phdrs sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
forall (H1_8 : forall a : Z, YG0f.in_band_rw a ->
  AD2i.H1 sp rdraw inp ch E model (Z_to_bv 64 a) = AD2i.H1 sp rdraw inp ch E model (Z_to_bv 64 (a - a mod 8))),
forall B : asyms, TfibSyms B ->
start_cells_cf tfibsegs B (AD1g.ly0 ch E model) init_state
  (AD2i.W1 sp rdraw inp Hsp Hva ch E model H1_8) FULL.
(* the start witness of Printf's two cells (YG0ncf.start_pf_cf) at W1; supplied by: start-up rows (the kit owner) *)
Definition H_start_pf_A : Prop :=
forall (rc : YM05.RunCeil) (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput)
(Hsp : valid_sp sp) (Hva : valid_argv (in_argv inp))
(h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
HS_tfib h = Some ch ->
cs_ok Asan.M.loaded_segments TFIB YA02.LIMIT (YA02.TOP sp)
(YA02.SINV0 Asan.M.loaded_segments Asan.M.phdrs sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
(YA02.argH0 Asan.M.phdrs sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
forall (H1_8 : forall a : Z, YG0f.in_band_rw a ->
  AD2i.H1 sp rdraw inp ch E model (Z_to_bv 64 a) = AD2i.H1 sp rdraw inp ch E model (Z_to_bv 64 (a - a mod 8))),
forall B : asyms, TfibSyms B ->
start_pf_cf tfibsegs B (AD1g.ly0 ch E model) (AD2i.W1 sp rdraw inp Hsp Hva ch E model H1_8) FULL.
(* the image rows of the errbuf object and of Printf's two cells at CfImg_A; supplied by: image rows (a Theorem Labs lane) *)
Definition H_errb_rows_A : Prop := forall B : asyms, TfibSyms B -> EXH_OFF_t /\ errb_obj_owned_t B /\ errb_ial_apart_t B.
Definition H_pf_rows_A : Prop := forall B : asyms, TfibSyms B -> pf_cells_owned_t B.
