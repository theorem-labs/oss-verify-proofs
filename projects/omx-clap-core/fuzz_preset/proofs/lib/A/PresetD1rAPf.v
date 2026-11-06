(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset (asan image A), the PROOF of loop_L_x_A (lib/A/PresetD1rA.v), the
   driver's per-call loop over preset's second allocator instance. Rule 24: no function is proved here (composition /
   driver layer of a port).
   Donor: proofs/cgif/cgif_file_fuzzer/lib/A/AD1r.v:160-1061 (journal_regions_kept, lib_reseat, calls_loop,
   tfib_loop_L_at, tfib_loop_L). The donor's image lemmas of the loop (the symbolic runs vp_run / br_run / l2_run /
   fq_run / xm_run, the re-seats l2_to_L / xm_to_CM / vp_reseat and the vm_compute facts of S_L .. S_XM) name no
   allocator invariant and are USED from lib/A/AD1r.v as they stand; the five donor lemmas that name AR, FINV or the
   lib site are restated here: journal_regions_kept_cf, lib_reseat_cf, calls_loop_cf, tfib_loop_L_at_cf,
   tfib_loop_L_cf. Changes in the proof, beyond the statement's (PresetD1rA.v header):
   - the harness call goes through PresetCfnA.preset_lib_contract_x: the donor's lib-site bridge (lib/A/AD1m.v) is
     inlined where calls_loop applied LIB;
   - after the call, the journal's image clause covers every image byte the driver keeps except the ledger cells
     (ledger_img, exempted through the journal's PST); the driver's kept image chunks avoid them (led_L, by
     vm_compute), and the stdout and read-only bytes avoid them too;
   - the donor's ofl_head special case (a sink-token exemption of its journal) is gone: preset's footprint is empty;
   - after the payload free, the model fact comes from a8's ml_free_cf (lib/Reusable/YG03dcf.v:428) through
     atok_cf_apath (YGcfTok.v:113), at the batch room ROOM_cf gives, in place of the donor's ml_free / atok_apath;
   - the float state: a harness call returns in a new float state fx' (the interface's continuation), so the loop
     is proved for every fx with frm_zero (fp_csr fx); after the call the machine state is carried over to fx' by
     st_ok_mkst_swap (st_ok's float conjuncts are the instance's own fields) and the old fx is cleared;
   - the room (statement change (2)): the interface's pre takes `iface_room_np S /\ iface_room_at sm x os H0 hist S`
     and its post gives it back one model call later (os ++ [o], hist'), so the loop carries it with no counter;
     after the last call the two driver frees take their sites' NP S' and the payload free's model fact takes its
     batch room from ROOM_cf S', which the interface's iface_room_np_tail gives (ROOM_cf_k S' 2, a8's RK_room);
   - memnorm (the interface's header item (8), a working branch 446222ec0601; PresetD1rA.v header item
     (10)): each harness call takes YAkMemnorm.memnorm tfibsegs over its FULL overlay, and its post keeps it. The
     first call takes it from the entry premise of loop_L_cf_A. Each later call gets it from the previous call's post
     (HMN'), then across the three runner segments vp_run / br_run / l2_run from the named premise H_memnorm_drv_A
     (the Section hypothesis HMND, a premise of the statement), and across the printf leaf (PF1 / PFN) from the keep
     `memnorm mem -> memnorm mem'`, the last premise of printf_post_cf's continuation (lane CwSites,
     a working branch 9f95abaab5bd, lib/A/PresetD1sitesA.v:174). The fq_run / free / xm_run / exit
     path after the last call needs no memnorm.
     The loop head is not reached from the composition directly: RUNQM (PresetD2eA.v:590; since the split
     PresetD2eAPf.v:462) and run_Q (PresetD2runQAPf.v:117), and their B twins, apply LOOPL deep inside their proofs,
     after start-up segments and
     library calls (malloc / memcpy / read); so the at-main FULL seed reaches the loop head only if every prefix leaf
     takes memnorm at entry and keeps it across its own runner segments and call sites.
   - the live real stack (the interface's header item (13); PresetD1rA.v header item (11)): each harness call's pre
     takes YGcallStackUp.astack_up_x at the call state as its last conjunct. calls_loop_cf carries the part above the
     entry sp, astack_up_x at usp (the statement's invariant HUPs), and loop_lib_pre gets the conjunct at the call's
     sp from it and the window of S_L (lib/A/PresetStkUpA.v stk_up_at). After the call the slot's journal keeps it
     (YGcallStackUp.astack_up_journal_xwR), the runner segments' frames keep it (stk_up_frame: they write below usp)
     and so does the printf leaf's presence keep.
   - the slot over the re-hiding relation (PresetD1rA.v header item (12)): each call's continuation steps the world by
     YA0nH.wle' tfibsegs RZ_cf, and the slot's post holds its journal at that relation (PCA.ajournal_cfwR). The loop
     never reads the journal's world conjunct: journal_regions_kept_cf and lib_reseat_cf take the journal at any R,
     its conjuncts are read by ajournal_cfwR_link (the link of lib/A/PresetD1rAl.v over R, the same projections), and
     the room and live-stack readers are the engine's R forms (YCbqGwild.ajournal_xw_roomR,
     YGcallStackUp.astack_up_journal_xwR).
   Other lanes' files, copied byte for byte from their pushed branches: lib/A/PresetD1sitesA.v (CwSites
   9f95abaab5bd: the free / printf / exit leaves over the non-primary room NP, the printf post with the memnorm keep),
   lib/A/PresetD1rAx.v and
   lib/A/PresetD1rAt.v and lib/A/PresetD1rAso.v (CwLoopB f881ab57213: the driver-run frame lemmas over ARcf,
   so_not_owned_cf and tfib_main_tail_cf, the donor's lib/A/AD29.v:105 over ARcf), lib/A/PresetPinvA.v and lib/A/PresetPinvAPf.v (CwPinvA
   093605f124c5: finv_run_pinv_A_holds and finv_printf_pinv_A_holds, the donor's lib/A/AD1v.v:31 and lib/A/AD1w.v:181
   over PINV), lib/A/PresetD1rAlPf.v (CwLoopB 81a3e8e75cf: the three links of lib/A/PresetD1rAl.v at the interface's frame
   constants, by unfolding). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK0k YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0k YG0f YG0v YG0n YG0d YCe5.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB12 AF0l AB1h AB13 AF0m AD2j AD2i AD1t AD20 AD1v AD1y AD26 AD24 AE22 ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AD21 AD25 AD23 AD2h AD1w AD2f AD2b AD2g AD1s AD2c AD2d AD29 AD2e AD1r.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01 YC5d YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG03cf YG03dcf YGcfTok YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Base CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD1sitesA PresetD1rAx PresetD1rAso PresetD1rAt PresetD1rAl PresetD1rA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetPinvA PresetPinvAPf PresetD1rAlPf PresetDrvHull PresetDrvAroA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomKeep YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallStackUp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetStkUpA.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetCfnA.
Module PCA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetCfnA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Notation ELV sp a0 p inp xw xd := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).

(* ---------------------------------------------------------------------- *)
(* 0. The ledger cells, as one interval list, and the checks that the driver's kept bytes avoid them. *)
Definition led_ivs : list (Z * Z) :=
[(PCA.G_RAN_OUT, PCA.G_RAN_OUT + 4); (PCA.G_LIVE, PCA.G_LIVE + 8); (PCA.G_PEAK, PCA.G_PEAK + 8);
(PCA.G_COUNT, PCA.G_COUNT + 8); (PCA.G_FAIL_AT, PCA.G_FAIL_AT + 8);
(* #102: the two new ledger cells (interface ledger_img) *)
(PCA.G_MOST, PCA.G_MOST + 8); (PCA.G_OWN_RAN_OUT, PCA.G_OWN_RAN_OUT + 4)].
Lemma ledger_img_ivs : forall a, PCA.ledger_img a -> exists lo hi, In (lo, hi) led_ivs /\ lo <= a < hi.
Proof.
intros a Ha. unfold PCA.ledger_img in Ha.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]];
[ exists PCA.G_RAN_OUT, (PCA.G_RAN_OUT + 4) | exists PCA.G_LIVE, (PCA.G_LIVE + 8) | exists PCA.G_PEAK, (PCA.G_PEAK + 8)
| exists PCA.G_COUNT, (PCA.G_COUNT + 8) | exists PCA.G_FAIL_AT, (PCA.G_FAIL_AT + 8)
| exists PCA.G_MOST, (PCA.G_MOST + 8) | exists PCA.G_OWN_RAN_OUT, (PCA.G_OWN_RAN_OUT + 4) ];
(split; [unfold led_ivs; cbn [In]; repeat (first [left; reflexivity | right]) | lia]).
Qed.
Definition led_avoid (lo hi : Z) : bool := forallb (fun iv => (hi <=? fst iv) || (snd iv <=? lo))%bool led_ivs.
Lemma led_avoid_sound : forall lo hi a, led_avoid lo hi = true -> lo <= a < hi -> ~ PCA.ledger_img a.
Proof.
intros lo hi a Hc Ha Hf. destruct (ledger_img_ivs a Hf) as (l & h & Hin & Hlh).
pose proof (proj1 (forallb_forall _ _) Hc (l, h) Hin) as X. cbn [fst snd] in X.
apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
Qed.
Definition led_region_ok (r : YP09.region) : bool :=
match r_base r with
| None => forallb (fun c => led_avoid (YP09.c_off c) (YP09.c_off c + c_len c)) (r_chunks r)
| Some _ => true
end.
Lemma led_L : forallb led_region_ok (tl L_mem) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma led_stdout : led_avoid STDOUT_LO STDOUT_HI = true /\ led_avoid SOBUF_LO SOBUF_HI = true.
Proof. vm_compute. split; reflexivity. Qed.
Lemma stdout_not_ledger : forall a, STDOUT_MUT a -> ~ PCA.ledger_img a.
Proof.
intros a [Ha|Ha]; [exact (led_avoid_sound _ _ a (proj1 led_stdout) Ha) | exact (led_avoid_sound _ _ a (proj2 led_stdout) Ha)].
Qed.
(* the two ranges of lib/A/AD1r.v in_ro_range, read from its statement *)
Lemma led_ro : forall a, in_ro_tfa a -> ~ PCA.ledger_img a.
Proof.
intros a Ha. pose proof (in_ro_range a Ha) as Hr.
lazymatch type of Hr with (?l1 <= _ < ?h1) \/ (?l2 <= _ < ?h2) =>
  assert (C : led_avoid l1 h1 = true /\ led_avoid l2 h2 = true) by (vm_compute; split; reflexivity) end.
destruct Hr as [Hr|Hr]; [exact (led_avoid_sound _ _ a (proj1 C) Hr) | exact (led_avoid_sound _ _ a (proj2 C) Hr)].
Qed.

(* ---------------------------------------------------------------------- *)
(* 1. st_ok of a machine state built by mkst does not depend on which float state built it: its two float conjuncts
      are that instance's own fields. *)
Lemma st_ok_mkst_swap : forall (fx fx' : YK11.FPState) segs E ss regs pc mem rom,
st_ok (fx := fx) segs E ss (mkst (fx := fx) regs pc mem rom) -> st_ok (fx := fx') segs E ss (mkst (fx := fx') regs pc mem rom).
Proof.
intros fx fx' segs E ss regs pc mem rom (_ & H2 & H3 & H4 & _ & H6 & H7 & H8 & H9).
unfold st_ok, mkst in *. cbn in *.
split; [reflexivity|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [reflexivity|].
split; [exact H6|]. split; [exact H7|]. split; [exact H8 | exact H9].
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The loop, at CwPinvA's two proved PINV frame theorems (lib/A/PresetPinvAPf.v). *)
Section P.
#[local] Notation HFRP := PresetPinvAPf.finv_run_pinv_A_holds (only parsing).
#[local] Notation HFPP := PresetPinvAPf.finv_printf_pinv_A_holds (only parsing).

Section e.
Context {rc : YM05.RunCeil} {LS : lib_shape} {ci : CfImg}.
Context {L : YP0b.ptable YPsym.asym} {PA : YC4aP.PAImg L}.
Section g.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws_cf tfibsegs B.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Variable NR : ProcInput -> Prop.
Variable sm : list Z -> Z * Z.
Variable iface_room_np : astate -> Prop.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable PAYLOAD_ROOM : list byte -> Prop.
(* the interface's frame names are its constants; the loop reads them through the three links of lib/A/PresetD1rAl.v,
   proved by unfolding in lib/A/PresetD1rAlPf.v *)
#[local] Notation ablocks_cf := PCA.ablocks_cf (only parsing).
#[local] Notation afn_pre_cf := PCA.afn_pre_cf (only parsing).
#[local] Notation ajournal_cf := PCA.ajournal_cf (only parsing).
#[local] Notation ABL := (PresetD1rAlPf.ablocks_link_A_holds B) (only parsing).
#[local] Notation AFN := (PresetD1rAlPf.afn_pre_link_A_holds B) (only parsing).
#[local] Notation AJ := (PresetD1rAlPf.ajournal_link_A_holds B) (only parsing).
Hypothesis MT_FREE : forall S m, mo_ok MT S m.
Hypothesis RO_IN : forall a, @YC4aP.pa_relro_lo rc L PA <= a < @YC4aP.pa_relro_hi rc L PA -> in_ro_tfa a.
Hypothesis NRB : forall inp a0 p data, NR inp -> in_argv inp = [a0; p] -> fs_lookup (in_fs inp) p = Some data -> PAYLOAD_ROOM (payload data).
Hypothesis LIBC : forall fx : YK11.FPState, @PCA.preset_lib_contract_xR rc LS L PA ci sm iface_room_np B MT XM_LIB XN_LIB PAYLOAD_ROOM fx
  (YA0nH.wle' tfibsegs (@YGcfRehidePost.RZ_cf rc)).
(* #102 (no-DW interface): the slot pre's universe closure at iface_ctx0 (PresetD1rA.v loop_L_x_A_at) *)
Hypothesis UNIV : @PRH_Base.prh_univ_closure PCA.preset_prh_img B ci PCA.iface_ctx0.
Hypothesis HSIG : @YC4aP.pa_sigma rc L PA YPsym.AS_LLVMFuzzerTestOneInput = A_LLVMF.
Hypothesis PF1 : forall fx : YK11.FPState, printf_first_cf (fx := fx) B xst.
Hypothesis PFN : forall fx : YK11.FPState, printf_next_cf (fx := fx) B xst.
(* the exit path's frees after the last harness call, over drv_pre_cf without memnorm (PresetD1sitesA.v
   free_site_nomn_cf / free_null_site_nomn_cf): the exit path does not carry memnorm *)
Hypothesis FREE : forall fx : YK11.FPState, free_site_nomn_cf (fx := fx) B iface_room_np.
Hypothesis FREEN : forall fx : YK11.FPState, free_null_site_nomn_cf (fx := fx) B iface_room_np.
Hypothesis EXITL : forall fx : YK11.FPState, exit_leaf_cf (fx := fx) B xst.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis NPT : PCA.iface_room_np_tail iface_room_np.
(* the named premise of the statement (PresetD1rA.v section 0): the three runner segments between two calls keep
   memnorm *)
Hypothesis HMND : H_memnorm_drv_A.
#[local] Notation AR_after_run_cf := (PresetD1rAx.AR_after_run_cf B HB ARL) (only parsing).
#[local] Notation drv_after_call_cf := (PresetD1rAx.drv_after_call_cf B HB ARL) (only parsing).
#[local] Notation so_not_owned_cf := (PresetD1rAso.so_not_owned_cf B HB ARL) (only parsing).
#[local] Notation canary_got_kept_cf := (PresetD1rAx.canary_got_kept_cf B HB) (only parsing).
Variables (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
Hypothesis Hargv : in_argv inp = [a0; p].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; p].
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvfs : valid_fs (in_fs inp).
Hypothesis HNR : NR inp.
#[local] Notation EL := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
Let EL6' : usp <= bv_unsigned (ew EL 6) := EL6 sp inp xw xd a0 p Hsp Hva Hve.

(* lib/A/PresetD1rAl.v's ajournal_link_A over a world relation R: the journal at R gives the same seven facts (none is
   the world conjunct; ajournal_cfw is ajournal_cfwR at wle, with the same conjuncts) *)
Lemma ajournal_cfwR_link : forall (R : world tfibsegs -> world tfibsegs -> Prop) (WS : list (list Z))
STK sp0 ly S Hp (W : world tfibsegs) mem md ly' S' Hp' W' mem' md' k,
PCA.ajournal_cfwR tfibsegs B R STK sp0 [] ly S Hp W mem md [] ly' S' Hp' W' mem' md' k WS ->
ARcf tfibsegs B ly' S' Hp' W' mem' md' /\
layout_le (length (st_secs S)) ly ly' /\
frames S' = frames S /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, in_img tfibsegs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
~ PCA.ledger_img a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a) /\
qtight S'.
Proof.
intros R WS STK sp0 ly S Hp W mem md ly' S' Hp' W' mem' md' k HJ.
unfold PCA.ajournal_cfwR in HJ.
destruct HJ as (HAR & Hle & _ & _ & _ & Hfr & _ & _ & Hout & _ & Himg & _ & _ & Hpres & _ & _ & HQ).
split; [exact HAR|]. split; [exact Hle|]. split; [rewrite Hfr; reflexivity|].
split; [exact Hout|]. split; [|split; [exact Hpres | exact (proj1 HQ)]].
intros a Hi Hns He Hl. apply Himg; [exact Hi | exact Hns | exact He | |].
- intros Hx. exact (Hl (PresetD1rAlPf.prh_pst_ledger_img_A a Hx)).
- apply YCbq.fp_spares_closed. exact YCbq.sink_closed_nil.
Qed.

(* lib/A/AD1r.v:226 journal_regions_kept over ARcf and the interface's journal (ajournal_link_A), at any world
   relation R of the journal *)
Lemma journal_regions_kept_cf : forall (R : world tfibsegs -> world tfibsegs -> Prop)
E rs ly S (W : world tfibsegs) mem md ly' S' W' mem' md' k sp0 (WS : list (list Z)),
PCA.ajournal_cfwR tfibsegs B R PCA.LLVMF_STK sp0 [] ly S [] W mem md [] ly' S' [] W' mem' md' k WS ->
ARcf tfibsegs B ly S [] W mem md ->
regions_wf rs = true ->
Forall (region_ok tfibsegs E (mrestrict (w_H W) mem)) rs ->
forallb (drv_keep_ok (-208)) rs = true -> forallb led_region_ok rs = true ->
bv_unsigned (ew E 0) = usp -> usp <= bv_unsigned (ew E 6) -> sp0 = usp - 208 -> YM05.ceil_of_top (usp - stack_max_size) ->
Forall (region_ok tfibsegs E (mrestrict (w_H W') mem')) rs.
Proof.
intros R E rs ly S W mem md ly' S' W' mem' md' k sp0 WS HJ HAR Hwf Hok Hchk Hled E0 E6 Hsp0 HCT.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. unfold sp_window_lo in Ulo.
pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
pose proof (ajournal_cfwR_link R WS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (HAR' & _ & _ & F1 & F3 & _ & _).
pose proof (ts_errno B HB) as Eerr.
apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) Hok r Hr) as HR. pose proof HR as (B1 & B2 & RW & _).
pose proof (chunk_inside_In r) as CI. specialize (CI) with (1 := regions_wf_In rs r Hwf Hr).
pose proof (proj1 (forallb_forall _ _) Hchk r Hr) as Hc. unfold drv_keep_ok in Hc.
pose proof (proj1 (forallb_forall _ _) Hled r Hr) as Hl. unfold led_region_ok in Hl.
assert (HIGH : forall a, usp - 208 <= a < 2 ^ 64 ->
mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a
/\ (writable_at tfibsegs (mrestrict (w_H W) mem) a -> writable_at tfibsegs (mrestrict (w_H W') mem') a)).
{ intros a Ha.
assert (EQA : aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
{ apply F1; [lia | unfold PCA.LLVMF_STK; lia]. }
assert (EQ : mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a) by (apply (mbyte_of_aview tfibsegs); exact EQA).
split; [exact EQ|]. intros Hw. apply (apresent_writable tfibsegs).
apply (apresent_transfer tfibsegs (w_H W) (w_H W') mem mem' a);
[lia | apply not_in_img_high; lia | exact EQA | apply apresent_of_writable; [lia | exact Hw]]. }
apply (region_ok_kept_chunks E (mrestrict (w_H W) mem) (mrestrict (w_H W') mem') r HR).
- intros c i Hcin Hi. pose proof (CI c Hcin) as [L1 L2].
destruct (r_base r) as [[|[|[|[|[|[|[|n]]]]]]]|] eqn:Hb; try discriminate Hc; cbn [base_val] in B1, B2, RW |- *.
+   apply andb_prop in Hc as [Hc Hcw]. apply Z.leb_le in Hc. rewrite E0 in *. apply (proj1 (HIGH (usp + YP09.c_off c + i) ltac:(lia))).
+   apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply (proj1 (HIGH (bv_unsigned (ew E 6) + YP09.c_off c + i) ltac:(lia))).
+   apply andb_prop in Hc as [Hc Hw]. apply andb_prop in Hc as [Hc Hav]. apply andb_prop in Hc as [Hilo Hihi].
apply Z.leb_le in Hilo. apply Z.leb_le in Hihi.
apply andb_prop in Hav as [Herr Hav]. unfold ext_avoids in Herr. cbn [fst snd] in Herr.
pose proof (proj1 (forallb_forall _ _) Hav c Hcin) as Havc. unfold chunk_avoids in Havc.
pose proof (proj1 (forallb_forall _ _) Hl c Hcin) as Hlc.
apply orb_prop in Havc as [Hsh|Havc].
{
destruct (shared_const_chunk_sound c Hsh) as [Hoff Hlen]. rewrite !Z.add_0_l, Hoff.
apply (canary_got_kept_cf _ _ _ _ _ _ _ _ _ _ _ _ i HAR HAR'). lia. }
pose proof (ext_avoids_sound _ _ _ (YP09.c_off c + i) Havc ltac:(lia)) as Hno.
assert (Hne : ~ (TFIB_ERRNO <= YP09.c_off c + i < TFIB_ERRNO + 4)) by (apply orb_prop in Herr as [Herr|Herr]; apply Z.leb_le in Herr; lia).
pose proof (in_img_hull (YP09.c_off c + i) ltac:(lia)) as Himg.
pose proof (led_avoid_sound _ _ (YP09.c_off c + i) Hlc ltac:(lia)) as Hnl.
rewrite !Z.add_0_l.
apply (mbyte_of_aview tfibsegs). apply F3; [exact Himg | rewrite (ts_owned B HB); exact Hno | rewrite Eerr; exact Hne | exact Hnl].
- intros o Ho.
destruct (r_base r) as [[|[|[|[|[|[|[|n]]]]]]]|] eqn:Hb; try discriminate Hc; cbn [base_val] in B1, B2, RW |- *.
+ apply andb_prop in Hc as [Hc Hcw]. apply Z.leb_le in Hc. rewrite E0 in *.
apply orb_prop in Hcw as [Hcw|Hcw]; [apply Z.leb_le in Hcw; lia|]. apply andb_prop in Hcw as [Hw1 Hw2].
apply Z.leb_le in Hw1. apply Z.leb_le in Hw2. apply (proj2 (HIGH (usp + o) ltac:(lia))). apply RW. exact Ho.
+ apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc2. lia.
+ apply andb_prop in Hc as [Hc Hw]. apply orb_prop in Hw as [Hw|Hw]; [apply Z.leb_le in Hw; lia|].
apply andb_prop in Hw as [Hw1 Hw2]. apply Z.leb_le in Hw1. apply Z.leb_le in Hw2.
unfold writable_at. rewrite Z.add_0_l. apply tfib_rw_window. rewrite u64_lit by lia. lia.
Qed.

(* lib/A/AD1r.v:291 lib_reseat over ARcf and the interface's journal, at any world relation R of the journal *)
Lemma lib_reseat_cf : forall (R : world tfibsegs -> world tfibsegs -> Prop)
(fx : YK11.FPState) E (W W' : world tfibsegs) regs mem regs' mem' ly S md ly' S' md' k (WS : list (list Z)),
st_ok tfibsegs E S_L (mkst regs (w64 A_LLVMF) (mrestrict (w_H W) mem) (seg_rom tfibsegs)) ->
bv_unsigned (ew E 0) = usp -> usp <= bv_unsigned (ew E 6) ->
PCA.ajournal_cfwR tfibsegs B R PCA.LLVMF_STK (usp - 208) [] ly S [] W mem md [] ly' S' [] W' mem' md' k WS ->
ARcf tfibsegs B ly S [] W mem md ->
aregs_preserved regs regs' -> getr regs' 10%bv = w64 0 -> YM05.ceil_of_top (usp - stack_max_size) ->
st_ok tfibsegs (havoc E K_LR (map (getr regs') CLOB')) S_LR (mkst regs' (Z_to_bv 64 RA_LLVMF) (mrestrict (w_H W') mem') (seg_rom tfibsegs)).
Proof.
intros R fx E W W' regs mem regs' mem' ly S md ly' S' md' k WS HS E0 E6 HJ HAR HP Ha0 HCT.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
pose proof calls_checks as (CKa & CKm & _).
rewrite S_LR_eq.
apply (st_ok_splice_havoc tfibsegs K_LR E S_L regs regs' (w64 A_LLVMF) RA_LLVMF (mrestrict (w_H W) mem) (mrestrict (w_H W') mem')
L_mem [(10%bv : bv 5, SLit 0)] CLOB' HS).
- exact CKa.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- exact CKm.
- exact (regs_kept_CLOB' regs regs' HP).
- constructor; [| constructor]. cbn [fst snd]. split; [reflexivity|]. rewrite Ha0. reflexivity.
-
pose proof (st_ok_mem_ok tfibsegs E S_L _ HS) as HM. cbn [ms_mem] in HM.
rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 rsFQ_eq)))))))))) in HM.
destruct HM as (Hwf & Hok & Hpd). split; [exact Hwf|]. split; [| exact Hpd].
pose proof (Forall_inv Hok) as Hr0. pose proof (Forall_inv_tail Hok) as Hrs0.
pose proof (ajournal_cfwR_link R WS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (_ & _ & _ & F1 & _ & Hpres & _).
change L_mem with (WIN208 :: tl L_mem). constructor.
+ apply (region_ok_transport_chunks E (mrestrict (w_H W) mem) (mrestrict (w_H W') mem')); [exact Hr0 | intros c i Hc; destruct Hc |].
cbn [r_wlo r_whi r_base base_val WIN208]. rewrite E0. intros o Ho. apply (apresent_writable tfibsegs).
destruct (Z.lt_ge_cases (usp + o) (usp - 208 - PCA.LLVMF_STK)) as [Hlow | Hhi].
* pose proof Hr0 as (_ & _ & RW & _). cbn [r_wlo r_whi r_base base_val WIN208] in RW. rewrite E0 in RW.
assert (EQA : aview tfibsegs (w_H W') mem' (usp + o) = aview tfibsegs (w_H W) mem (usp + o)).
{ apply F1; [unfold sp_window_lo in Ulo; lia | lia]. }
apply (apresent_transfer tfibsegs (w_H W) (w_H W') mem mem' (usp + o));
[unfold sp_window_lo in Ulo; lia | apply not_in_img_high; unfold sp_window_lo in Ulo; lia | exact EQA |].
apply apresent_of_writable; [unfold sp_window_lo in Ulo; lia | apply RW; lia].
* apply Hpres. lia.
+ exact (journal_regions_kept_cf R E (tl L_mem) ly S W mem md ly' S' W' mem' md' k (usp - 208) WS HJ HAR (proj2 (andb_prop _ _ Hwf)) Hrs0
ltac:(vm_compute; reflexivity) led_L E0 E6 eq_refl HCT).
Qed.

(* the interface's pre at the loop head: the donor's lib_pre (lib/A/AD1w.v:73) and the lib-site bridge (AD1m.v) *)
Lemma loop_lib_pre : forall (fx : YK11.FPState) ly S (W : world tfibsegs) regs mem md (data : list byte) q cnt ran os H0 hist,
YK0o.frm_zero (@YK11.fp_csr fx) ->
ARcf tfibsegs B ly S [] W mem md -> iface_room_np S -> PCA.iface_room_at sm (map (fun b : byte => bv_unsigned b) (payload data)) os H0 hist S ->
(* the hull closed set: the earlier calls' grant list of this call has at most 3 entries (the run's at most 4 calls) *)
(length os <= 3)%nat ->
xs_placed_cf ly S -> qtight S -> frames S = [] ->
getr regs 1%bv = w64 RA_LLVMF -> raZ regs = RA_LLVMF -> getr regs 3%bv = w64 (as_gp B) -> getr regs 4%bv = w64 (as_tp B) ->
spZ regs = usp - 208 -> top_ok usp ly -> (forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a) ->
s0Z regs = payload_len data -> 0 <= payload_len data < 2 ^ 26 ->
blocks_bytes S + PCA.LIVE_LIB <= LIVE_MAX ->
getr regs 10%bv = w64 (if payload_len data =? 0 then A_EMPTY_tfa else q) -> getr regs 11%bv = w64 (payload_len data) ->
((payload_len data = 0 /\ (if payload_len data =? 0 then A_EMPTY_tfa else q) = PCA.A_EMPTY)
\/ (0 < payload_len data < 2 ^ 26 /\ In ((if payload_len data =? 0 then A_EMPTY_tfa else q), payload_len data) (ablocks_cf tfibsegs B ly S))) ->
payload_len data = Z.of_nat (length (payload data)) ->
garr8 tfibsegs (mrestrict (w_H W) mem) (if payload_len data =? 0 then A_EMPTY_tfa else q) (map (fun b : byte => bv_unsigned b) (payload data)) ->
arodata_ok B (aview tfibsegs (w_H W) mem) ->
PCA.PINV (aview tfibsegs (w_H W) mem) cnt ran -> cnt + PCA.LCNT <= PCA.SIZE_MAX -> cnt + PCA.LCNT < 2 ^ 62 - 2 ^ 30 ->
PAYLOAD_ROOM (payload data) -> Fs.fs_sorted (m_fs md) = true ->
(* header item (8) of the interface: memnorm of the call's FULL overlay *)
YAkMemnorm.memnorm tfibsegs mem ->
(* the call's wild room (the pre's conjunct after the run room) *)
YCbqGwild.wild_room (as_universe B) [] YCbqGwild.K_LLVMF (st_depot S) ->
(* header item (13) of the interface: the live real stack from sp up to ly_top is present, the pre's last conjunct *)
YGcallStackUp.astack_up_x tfibsegs ly W (spZ regs) mem ->
PCA.preset_lib_pre_x (L := L) (PA := PA) (fx := fx) sm iface_room_np B MT XM_LIB PAYLOAD_ROOM
regs ly S [] W mem md (if payload_len data =? 0 then A_EMPTY_tfa else q) (payload_len data) (payload data) cnt ran os H0 hist.
Proof.
intros fx ly S W regs mem md data q cnt ran os H0 hist Hfz HAR HNP HRA HLOS HXS HQT Hfr R1 Hra R3 R4 Hsp' HTOP Hwin Hs0 Hpl Hlive R10 R11 Hpn Hlen Hgarr HRO HPI Hcnt Hcnt62 HPR Hsorted HMN HWR HUP.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (proj1 (@YM05.alloc_ceiling_value rc)) as CV.
pose proof (top_ok_ceil _ _ HTOP) as HCT. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
pose proof (amc_layout _ _ _ _ _ (proj1 HAR)) as LO. pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & _).
pose proof (lo_stk_ceil _ LO) as SC. unfold ASAN_CEIL in SC.
destruct HTOP as (Tt1 & Elo & Ehi & _).
assert (Hs0c : s0Z regs < alloc_ceiling) by (rewrite Hs0; lia).
assert (HAFN : afn_pre_cf tfibsegs B PCA.LLVMF_STK ly S [] W regs mem md []).
{ apply AFN; [exact HAR | rewrite R1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity | rewrite Hra; cbv; discriminate | exact R3 | exact R4 | | | apply achain_low; exact Hs0c | exact HQT].
- unfold astk_ok. rewrite Hsp', Ehi. rewrite Elo in SC.
unfold ly_bot, kHighMemEnd, PCA.LLVMF_STK, ASTACK, kStackSpan, sp_window_lo, sp_window_hi in *.
repeat split; try lia. all: replace (usp - 208) with (usp + (-13) * 16) by lia; rewrite Z.mod_add by lia; exact U16.
- rewrite Hsp'. intros a Ha. apply Hwin. unfold PCA.LLVMF_STK in Ha. lia. }
assert (HROP : PRH_Base.arodata_okP tfibsegs (@YC4aP.pa_relro_lo rc L PA) (@YC4aP.pa_relro_hi rc L PA) B (aview tfibsegs (w_H W) mem)).
{ intros a Ha Hno Hne. apply HRO; [| exact Hno | exact Hne]. destruct Ha as [Ha | Ha]; [left; exact Ha | exact (RO_IN a Ha)]. }
assert (HMO : mo_ok MT S (XM_LIB (payload_len data))) by apply MT_FREE.
assert (HHp : @nil Z = []) by reflexivity.
assert (HRM : iface_room_np S /\ PCA.iface_room_at sm (map (fun b : byte => bv_unsigned b) (payload data)) os H0 hist S /\
  (length os <= 3)%nat) by (split; [assumption | split; assumption]).
unfold PCA.preset_lib_pre_x.
repeat (split; [assumption|]); assumption.
Qed.

(* lib/A/AD1r.v:570 calls_loop over ARcf / PINV / the program interface. *)
Theorem calls_loop_cf : forall (r : nat) (fx : YK11.FPState), YK0o.frm_zero (@YK11.fp_csr fx) ->
forall (j : nat) E (W : world tfibsegs) ms md ly S data (buf cap q : Z) (fs : Fs) (N : nat) (cnt ran : Z),
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data ->
(forall k, (k < K_M1)%nat -> ew E k = ew EL k) -> ed E 2 = data ->
bv_unsigned (ew E A_BUF) = buf ->
bv_unsigned (ew E 162) = payload_len data -> bv_unsigned (ew E 163) = (if payload_len data =? 0 then A_EMPTY_tfa else q) ->
bv_unsigned (ew E 164) = q -> bv_unsigned (ew E 166) = Z.of_nat r ->
st_ok tfibsegs E S_L (restrict (w_H W) ms) ->
(1 <= r)%nat -> (j + r = N)%nat -> (N <= 4)%nat ->
((payload_len data = 0 /\ q = 0 /\ Permutation (ablocks B ly S) [(buf, cap)])
\/ (0 < payload_len data /\ Permutation (ablocks B ly S) [(buf, cap); (q, payload_len data)])) ->
(0 < payload_len data -> blk (w_H W) (ms_mem ms) q (payload_len data) (payload data)) ->
frames S = [] -> qtight S -> iface_room_np S ->
YCbqGwild.wild_room (as_universe B) [] (r * YCbqGwild.K_LLVMF) (st_depot S) ->
(exists os H0 hist, length os = j /\ PCA.iface_room_at sm (map (fun b : byte => bv_unsigned b) (payload data)) os H0 hist S) -> xs_placed_cf ly S ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S [] W (ms_mem ms) md -> top_ok usp ly ->
cnt + Z.of_nat r * PCA.LCNT < 2 ^ 62 - 2 ^ 30 -> 65536 <= cap <= 2 ^ 26 -> dlen data < cap -> (2 <= length data)%nat ->
so_state xst j (w_H W) (ms_mem ms) -> arodata_ok B (aview tfibsegs (w_H W) (ms_mem ms)) ->
PCA.PINV (aview tfibsegs (w_H W) (ms_mem ms)) cnt ran ->
YAkMemnorm.memnorm tfibsegs (ms_mem ms) ->
YGcallStackUp.astack_up_x tfibsegs ly W usp (ms_mem ms) ->
((forall k, fd_lookup (m_fds md) k = fd_lookup APSG.fds_std k) /\ m_fs md = fs /\ Fs.fs_sorted fs = true) ->
srealizes tfibsegs (mkCfg ms md) (loop_tgt (LS := LS) (payload data) N j r fs).
Proof.
induction r as [|r IH]; [intros; lia|].
intros fx Hfz j E W ms md ly S data buf cap q fs N cnt ran Hlk Hok HEE HEd E41 E61 E62 E63 E65 HS _ HjrN HN4 HBL HPL Hfr HQT HNP HWR HRA HXS HAI HAR HTOP Hcnt Hcap HLc Hlen HSO HRO HPI HMN HUPs HMD.
assert (Hjr : (j + Datatypes.S r <= 4)%nat) by lia.
pose proof HMD as (Hfdl0 & Hmfs & Hsorted0).
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (proj1 (@YM05.alloc_ceiling_value rc)) as CV.
pose proof (top_ok_ceil _ _ HTOP) as HCT. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
pose proof (config_len_bound data) as Hcl.
assert (Hpl : 0 <= payload_len data < cap) by (unfold payload_len, HDR_MIN in *; lia).
assert (E0 : bv_unsigned (ew E 0) = usp) by (rewrite HEE by (unfold K_M1; lia); reflexivity).
assert (E6 : usp <= bv_unsigned (ew E 6)) by (rewrite HEE by (unfold K_M1; lia); exact EL6').
pose proof calls_pcs as (PCV & PCB & PCL2 & PCF & PCX & PCLR & PCVr & PCFr & RVV & RVL2 & RVF & RVX & RVB & RVL).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E S_L ms HS RVL) as Hshape.
set (regs := ms_regs ms) in *. set (mem := ms_mem ms) in *.
pose proof S_L_regs as (Q1 & Q2 & Q3 & Q4 & Q8 & Q10 & Q11).
assert (R1 : getr regs 1%bv = w64 RA_LLVMF) by (subst regs; rewrite (st_ok_restrict_reg tfibsegs (w_H W) E S_L ms 1%bv HS), Q1; reflexivity).
assert (R2 : getr regs 2%bv = Z_to_bv 64 (usp + -208)) by (subst regs; rewrite (st_ok_restrict_reg tfibsegs (w_H W) E S_L ms 2%bv HS), Q2; cbn [sv_denot]; rewrite E0; reflexivity).
assert (R3 : getr regs 3%bv = w64 TFIB_GP) by (subst regs; rewrite (st_ok_restrict_reg tfibsegs (w_H W) E S_L ms 3%bv HS), Q3; reflexivity).
assert (R4 : getr regs 4%bv = w64 TFIB_TP) by (subst regs; rewrite (st_ok_restrict_reg tfibsegs (w_H W) E S_L ms 4%bv HS), Q4; reflexivity).
assert (R8 : getr regs 8%bv = w64 (payload_len data)).
{ subst regs. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E S_L ms 8%bv HS), Q8. cbn [sv_denot]. rewrite Z.add_0_r, <- E61. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (R10 : getr regs 10%bv = w64 (if payload_len data =? 0 then A_EMPTY_tfa else q)).
{ subst regs. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E S_L ms 10%bv HS), Q10. cbn [sv_denot]. rewrite Z.add_0_r, <- E62. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (R11 : getr regs 11%bv = w64 (payload_len data)).
{ subst regs. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E S_L ms 11%bv HS), Q11. cbn [sv_denot]. rewrite Z.add_0_r, <- E61. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (Hsp' : spZ regs = usp - 208) by (unfold spZ; rewrite R2; rewrite u64_lit by (unfold sp_window_lo in Ulo; lia); lia).
assert (Hra : raZ regs = RA_LLVMF) by (unfold raZ; rewrite R1; apply u64_lit; unfold RA_LLVMF; lia).
assert (Hs0 : s0Z regs = payload_len data) by (unfold s0Z; rewrite R8; apply u64_lit; lia).
pose proof (st_ok_mem_ok tfibsegs E S_L _ HS) as HM. cbn [restrict ms_mem] in HM. fold mem in HM.
assert (Hwin : forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E (w_H W) mem L_mem); [exact HM | left; reflexivity | exact E0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E (w_H W) mem L_mem); [exact HM | right; left; reflexivity | exact E0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E (w_H W) mem L_mem); [exact HM | right; right; left; reflexivity | exact E0 | lia | lia | cbn; lia]. }
assert (Hbb : blocks_bytes S <= cap + payload_len data).
{ rewrite (blocks_bytes_ablocks B ly S). destruct HBL as [(_ & _ & HP) | (_ & HP)]; rewrite (bsum_perm _ _ HP); cbn; lia. }
rewrite Hshape, PCL2 || rewrite Hshape. fold regs mem.
replace (Z_to_bv 64 (ss_pc S_L)) with (w64 A_LLVMF) by reflexivity.
change (mkCfg (mkst regs (w64 A_LLVMF) mem (seg_rom tfibsegs)) md) with (cfg_at tfibsegs A_LLVMF regs mem md).
destruct HRA as (os & H0 & hist & Hlos & HRA).
(* the slot pre's last conjunct at this call: the invariant above usp and the window of S_L below it *)
assert (HUP : YGcallStackUp.astack_up_x tfibsegs ly W (spZ regs) mem)
by (rewrite Hsp'; exact (PresetStkUpA.stk_up_at ly W mem usp (usp - 208) ltac:(lia) Hwin HUPs)).
(* the hull closed set at this call: j calls made, Datatypes.S r >= 1 left, j + S r = N <= 4 *)
assert (HLOS3 : (length os <= 3)%nat) by lia.
assert (PRE : PCA.preset_lib_pre_x (L := L) (PA := PA) (fx := fx) sm iface_room_np B MT XM_LIB PAYLOAD_ROOM
regs ly S [] W mem md (if payload_len data =? 0 then A_EMPTY_tfa else q) (payload_len data) (payload data) cnt ran os H0 hist).
{ apply (loop_lib_pre fx); try assumption.
- rewrite (ts_gp B HB); exact R3.
- rewrite (ts_tp B HB); exact R4.
- lia.
- unfold PCA.LIVE_LIB, LIVE_MAX. clear - Hbb Hcap Hpl. lia.
- rewrite ABL. destruct HBL as [(Hz & Hq & HP) | (Hp & HP)].
+ left. rewrite Hz. split; reflexivity.
+ right. replace (payload_len data =? 0) with false by (symmetry; apply Z.eqb_neq; lia). split; [lia|].
apply (Permutation_in _ (Permutation_sym HP)). right. left. reflexivity.
- symmetry. apply payload_length. exact Hok.
- destruct (Z.eqb_spec (payload_len data) 0) as [Hz|Hnz].
+ assert (Hpn : payload data = []) by (apply length_zero_iff_nil; pose proof (payload_length data Hok); lia). rewrite Hpn. apply YI00.garr8_nil.
+ apply garr8_of_blk. rewrite (payload_length data Hok). apply HPL. lia.
- unfold PCA.LCNT, PCA.SIZE_MAX in *. lia.
- unfold PCA.LCNT in *. lia.
- exact (NRB inp a0 p data HNR Hargv Hlk).
- rewrite Hmfs. exact Hsorted0.
- (* the call's room: K_LLVMF of the room for the r + 1 calls left *)
  refine (YCbqGwild.wild_room_le _ _ (Datatypes.S r * YCbqGwild.K_LLVMF) _ _ _ HWR). cbn [Nat.mul]. lia. }
rewrite (loop_tgt_step (payload data) N j r fs HjrN), <- Hmfs.
(* the call target: the driver's entry constant is the interface's A_LLVMF at this listing (HSIG) *)
assert (HLL : PCA.A_LLVMF (rc := rc) (L := L) (PA := PA) = A_LLVMF) by (unfold PCA.A_LLVMF; exact HSIG).
rewrite <- HLL.
apply (LIBC fx ly S [] W regs mem md (if payload_len data =? 0 then A_EMPTY_tfa else q) (payload_len data) (payload data) cnt ran
os H0 hist (Kstep (payload data) N j r) HAI PRE).
intros l W' c' _ HAI' (fx' & ly' & S' & regs' & mem' & md' & k & -> & Hfz' & _ & POST). cbn [cfg_model] in HAI'.
destruct POST as ((WS & HWB & HJ) & (HNP' & o & hist' & HRA') & HP & Ha0' & HPERM & Hfdl & Hmfs' & Hret & Hout & Hsorted & (cnt' & ran' & HPI' & Hcnt') & _ & Hplk & HXS' & HMN').
(* the room for the r calls still left after this one: the journal stored at most K_LLVMF fresh wild traces *)
assert (HWR' : YCbqGwild.wild_room (as_universe B) [] (r * YCbqGwild.K_LLVMF) (st_depot S')).
{ unfold YCbqGwild.wbudget in HWB. pose proof HJ as HJx. unfold PCA.ajournal_cfwR in HJx.
  assert (HW1 : YCbqGwild.wild_room (as_universe B) [] (Datatypes.S r * YCbqGwild.K_LLVMF - YCbqGwild.wfresh [] WS)
    (st_depot S')) by (eapply YCbqGwild.ajournal_xw_roomR; [exact HJx | exact HWR | cbn [Nat.mul]; lia]).
  refine (YCbqGwild.wild_room_le _ _ _ _ _ _ HW1). cbn [Nat.mul]. lia. }
rewrite !ABL in HPERM.
(* the rest of the driver runs in the float state fx' the call returned in *)
rewrite Hshape, restrict_mkst_fx in HS. fold regs mem in HS.
pose proof (st_ok_mkst_swap fx fx' tfibsegs E S_L regs (w64 A_LLVMF) (mrestrict (w_H W) mem) (seg_rom tfibsegs) HS) as HSx.
clear Hfz PRE.
pose proof (ajournal_cfwR_link _ WS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (HAR' & Hlyle & Hfrs & F1 & F3 & HpresJ & HQT').
(* the invariant after the call: the slot's journal keeps the live stack and extends it down over the callee's window *)
assert (HUP' : YGcallStackUp.astack_up_x tfibsegs ly' W' usp mem').
{ pose proof HJ as HJx. unfold PCA.ajournal_cfwR in HJx.
  pose proof (YGcallStackUp.astack_up_journal_xwR tfibsegs B _ _ tfib_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJx HUP) as HUPj.
  intros a Ha. apply HUPj. rewrite Hsp'. unfold PCA.LLVMF_STK. lia. }
rewrite Hfr in Hfrs.
assert (HTOP' : top_ok usp ly') by exact (top_ok_le _ _ _ _ Hlyle HTOP).
assert (HBL' : (payload_len data = 0 /\ q = 0 /\ Permutation (ablocks B ly' S') [(buf, cap)])
\/ (0 < payload_len data /\ Permutation (ablocks B ly' S') [(buf, cap); (q, payload_len data)])).
{ destruct HBL as [(Hz & Hq & HPm) | (Hp & HPm)]; [left | right]; repeat split; try assumption; exact (Permutation_trans HPERM HPm). }
assert (HSO' : so_state xst j (w_H W') mem').
{ apply (so_state_keep xst XFR j (w_H W) (w_H W') mem mem'); [| exact HSO]. intros a Ha. destruct (STDOUT_static B HB a Ha) as (H1 & H2 & H3).
exact (F3 a H1 H2 H3 (stdout_not_ledger a Ha)). }
assert (HRO' : arodata_ok B (aview tfibsegs (w_H W') mem')).
{ apply (arodata_keep B (w_H W) (w_H W') mem mem'); [| exact HRO]. intros a H1 H2 H3. apply F3; [| exact H2 | exact H3 | exact (led_ro a H1)].
apply in_img_hull. pose proof (in_ro_range a H1). lia. }
assert (HPL' : 0 < payload_len data -> blk (w_H W') mem' q (payload_len data) (payload data)).
{ intros Hp. replace (payload_len data =? 0) with false in Hplk by (symmetry; apply Z.eqb_neq; lia).
assert (Hinq : In (q, payload_len data) (ablocks B ly S)) by (destruct HBL as [(Hz & _) | (_ & HPm)]; [lia|]; apply (Permutation_in _ (Permutation_sym HPm)); right; left; reflexivity).
pose proof (alc_blocks _ _ ARL ly S [] W mem md _ _ HAR Hinq) as (_ & Hq4096 & Hqce & _).
assert (Hreqq : req_size (payload_len data) = payload_len data) by (unfold req_size; destruct (Z.eqb_spec (payload_len data) 0); lia). rewrite Hreqq in Hqce.
assert (NIMGQ : forall a, q <= a < q + payload_len data -> ~ in_img tfibsegs a).
{ intros a Ha. assert (Ha' : q <= a < q + req_size (payload_len data)) by (rewrite Hreqq; exact Ha).
exact (proj2 (alc_client_img _ _ ARL ly S [] W mem md a HAR (or_introl (ex_intro _ q (ex_intro _ (payload_len data) (conj Hinq Ha')))))). }
apply (blk_copy (w_H W) (w_H W') mem mem' q q (payload_len data) (payload data) Hplk (fun i Hi => NIMGQ (q + i) ltac:(lia)) ltac:(lia) ltac:(lia) (fun i Hi => NIMGQ (q + i) ltac:(lia)) ltac:(lia) ltac:(lia)).
exact (HPL Hp). }
pose proof (lib_reseat_cf _ fx' E W W' regs mem regs' mem' ly S md ly' S' md' k WS HSx E0 E6 ltac:(rewrite <- Hsp'; exact HJ) HAR HP Ha0' HCT) as HS2.
set (E2 := havoc E K_LR (map (getr regs') CLOB')) in HS2.
assert (E2old : forall i, (i < K_LR)%nat -> ew E2 i = ew E i) by (intros i Hi; subst E2; apply ew_havoc_old; exact Hi).
assert (E2_0 : bv_unsigned (ew E2 0) = usp) by (rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia); exact E0).
assert (E2_6 : usp <= bv_unsigned (ew E2 6)) by (rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia); exact E6).
rewrite <- restrict_mkst_fx in HS2.
(* vp_run, with memnorm on both ends (the first segment of H_memnorm_drv_A) *)
apply (SRr_srealizes tfibsegs W' _ _ _ (proj1 (HMND fx') E2 W' regs' mem' md' HS2 HMN') HAI').
intros W1 c1 _ HAI3 [HATV (msV1 & mdV1 & EcV & HMNV)]. destruct HATV as (-> & msV & matV & -> & HSV & HFV & HFrV). cbn [cfg_model] in HAI3.
(* the invariant across vp_run: its frame is below usp *)
assert (HUPV : YGcallStackUp.astack_up_x tfibsegs ly' W' usp (ms_mem msV))
by exact (PresetStkUpA.stk_up_frame E2 L_mem ly' W' mem' (ms_mem msV) usp (proj2 (proj2 (proj2 L_mem_wf))) E2_0
  ltac:(unfold sp_window_lo, sp_window_hi in *; lia) HTOP' HFV HUP').
injection EcV as <- <-.
set (mdV := with_vm_backing (m_vm_lazy md') matV md') in *.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W') E2 S_VP msV HSV RVV) as HshapeV.
set (regsV := ms_regs msV) in *. set (memV := ms_mem msV) in *.
pose proof S_VP_regs as (V1 & V2 & V3 & V4 & V10 & V11).
assert (RV1 : getr regsV 1%bv = w64 RA_EMIT) by (subst regsV; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 S_VP msV 1%bv HSV), V1; reflexivity).
assert (RV2 : getr regsV 2%bv = Z_to_bv 64 (usp + -288)) by (subst regsV; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 S_VP msV 2%bv HSV), V2; cbn [sv_denot]; rewrite E2_0; reflexivity).
assert (RV3 : getr regsV 3%bv = w64 TFIB_GP) by (subst regsV; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 S_VP msV 3%bv HSV), V3; reflexivity).
assert (RV4 : getr regsV 4%bv = w64 TFIB_TP) by (subst regsV; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 S_VP msV 4%bv HSV), V4; reflexivity).
assert (RV10 : getr regsV 10%bv = w64 A_FMT_D) by (subst regsV; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 S_VP msV 10%bv HSV), V10; reflexivity).
assert (RV11 : getr regsV 11%bv = Z_to_bv 64 (usp + -264)) by (subst regsV; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E2 S_VP msV 11%bv HSV), V11; cbn [sv_denot]; rewrite E2_0; reflexivity).
assert (HspV : spZ regsV = usp - 288) by (unfold spZ; rewrite RV2; rewrite u64_lit by (unfold sp_window_lo in Ulo; lia); lia).
assert (HraV : raZ regsV = RA_EMIT) by (unfold raZ; rewrite RV1; apply u64_lit; unfold RA_EMIT; lia).
pose proof (st_ok_mem_ok tfibsegs E2 S_VP _ HSV) as HMV. cbn [restrict ms_mem] in HMV. fold memV in HMV.
assert (HwinV : forall a, usp - 65536 <= a < usp -> apresent (w_H W') memV a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E2 (w_H W') memV (ss_mem S_VP)); [exact HMV | left; reflexivity | exact E2_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E2 (w_H W') memV (ss_mem S_VP)); [exact HMV | right; left; reflexivity | exact E2_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E2 (w_H W') memV (ss_mem S_VP)); [exact HMV | right; right; left; reflexivity | exact E2_0 | lia | lia | cbn; lia]. }
assert (HARV : ARcf tfibsegs B ly' S' [] W' memV mdV).
{ apply (AR_after_run_cf ly' S' [] W' E2 L_mem mem' memV md' matV HAR' (proj2 (proj2 (proj2 L_mem_wf)))); [rewrite E2_0; exact Ulo | rewrite E2_0; exact HCT | exact HFV |].
rewrite E2_0. intros a Ha. exact (apresent_some' _ _ _ (HwinV a Ha)). }
assert (HSOV : so_state xst j (w_H W') memV).
{ exact (so_state_frame xst XFR j (w_H W') E2 L_mem _ _ HFrV (proj2 (proj2 CM_so_ok)) ltac:(rewrite E2_0; exact Ulo) ltac:(rewrite E2_0; exact E2_6) HSO'). }
assert (HROV : arodata_ok B (aview tfibsegs (w_H W') memV)).
{ exact (arodata_frame B (w_H W') E2 L_mem _ _ HFrV (proj2 (proj2 (proj2 L_mem_wf))) ltac:(rewrite E2_0; exact Ulo) HRO'). }
assert (HRD : rdword (aview tfibsegs (w_H W') memV) (spZ regsV + 24) = Some 0) by (rewrite HspV; exact (rdword_vararg sp E2 (w_H W') memV HMV E2_0)).
assert (PREV : printf_pre_cf B ly' S' W' regsV memV mdV).
{ split; [exact HARV|]. split; [exact HraV|].
split; [rewrite HspV; replace (usp - 288) with (usp + (-18) * 16) by lia; rewrite Z.mod_add by lia; exact U16|].
split; [rewrite HspV; lia|]. split; [rewrite HspV; unfold top_ok in HTOP'; lia|].
split; [rewrite HspV; lia|]. split; [unfold top_ok in HTOP'; tauto|]. split; [unfold top_ok in HTOP'; tauto|]. split; [exact HROV|].
split; [rewrite HspV; intros a Ha; apply HwinV; unfold PF_STK in Ha; lia|].
split; [rewrite (ts_gp B HB); exact RV3|]. split; [rewrite (ts_tp B HB); exact RV4|].
split; [exact RV10|]. split; [rewrite RV11, HspV; unfold w64; f_equal; lia | exact HRD]. }
assert (HfdlV : forall fd, fd_lookup (m_fds mdV) fd = fd_lookup APSG.fds_std fd) by (intros fd; subst mdV; rewrite wvb_fds', Hfdl; apply Hfdl0).
assert (HPIV : PCA.PINV (aview tfibsegs (w_H W') memV) cnt' ran')
by exact (HFRP (w_H W') E2 L_mem mem' memV usp cnt' ran' HFrV (proj2 (proj2 (proj2 L_mem_wf))) E2_0 Ulo HPI').
assert (POST : printf_post_cf B xst ly' S' W' regsV memV mdV (Datatypes.S j) (lib_iter (payload data) r (run_tail (N - 1)) (ll_fs l))).
2:{ rewrite HshapeV, PCV. fold regsV memV.
change (mkCfg (mkst regsV (Z_to_bv 64 A_icpt_vprintf) memV (seg_rom tfibsegs)) mdV) with (cfg_at tfibsegs A_icpt_vprintf regsV memV mdV).
destruct j as [|j'].
-
cbn [Kstep]. replace (N - 1)%nat with r in POST by lia.
exact (PF1 fx' ly' S' W' regsV memV mdV _ PREV ltac:(destruct HSOV as [[_ X]|[X _]]; [exact X | exfalso; lia]) HfdlV HAI3 POST).
-
cbn [Kstep]. exact (PFN fx' ly' S' W' regsV memV mdV _ (Datatypes.S j') PREV ltac:(destruct HSOV as [[X _]|[_ X]]; [exfalso; lia | exact X]) ltac:(lia) HfdlV HAI3 POST). }
(* the printf leaf's continuation: its last premise is the memnorm keep (CwSites 9f95abaab5bd) *)
intros regs4 mem4 md4 HAR4 HP4 Hs4 Ha04 HX4 Hfr4 Hpres4 HAI4 HMK4. unfold cfg_at. rewrite HraV. rewrite HspV in Hfr4.
pose proof (HMK4 HMNV) as HMN4. clear HMK4.
pose proof (same_but_materialized_frame _ _ Hs4) as (_ & _ & _ & _ & _ & _ & _ & _ & Hfds4 & _ & _ & Hfs4 & _).
rewrite HshapeV, restrict_mkst_fx in HSV. fold regsV memV in HSV. rewrite PCV in HSV.
pose proof (vp_reseat sp Hsp E2 W' regsV memV regs4 mem4 HSV E2_0 E2_6 HP4 Ha04 Hfr4 Hpres4) as HS5.
set (E4 := havoc E2 K_VP (map (getr regs4) CLOB')) in HS5.
assert (E4old : forall i, (i < K_VP)%nat -> ew E4 i = ew E2 i) by (intros i Hi; subst E4; apply ew_havoc_old; exact Hi).
assert (E4_0 : bv_unsigned (ew E4 0) = usp) by (rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia); exact E2_0).
assert (E4_6 : usp <= bv_unsigned (ew E4 6)) by (rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia); exact E2_6).
assert (E4_65 : bv_unsigned (ew E4 166) = Z.of_nat (Datatypes.S r)) by (rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia); rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia); exact E65).
assert (HSO4 : so_state xst (Datatypes.S j) (w_H W') mem4) by (right; split; [lia | exact HX4]).
assert (HRO4 : arodata_ok B (aview tfibsegs (w_H W') mem4)).
{ apply (arodata_keep B (w_H W') (w_H W') memV mem4); [| exact HROV]. intros a H1 _ _. destruct (in_ro_static sp Hsp a H1) as [Y1 Y2]. pose proof (in_ro_range a H1).
apply Hfr4; [lia | unfold PF_STK; lia | exact Y2]. }
assert (Hwin4 : forall a, usp - 65536 <= a < usp -> apresent (w_H W') mem4 a)
by (intros a Ha; apply Hpres4; [unfold sp_window_lo, sp_window_hi in *; lia | unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI; unfold sp_window_lo in Ulo; lia | apply HwinV; exact Ha]).
(* the invariant across the printf leaf: its presence keep, off the stdout cells *)
assert (HUP4 : YGcallStackUp.astack_up_x tfibsegs ly' W' usp mem4).
{ intros a Ha. pose proof HTOP' as ((_ & T2) & _).
  apply Hpres4; [unfold sp_window_lo, sp_window_hi in *; lia | unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI; unfold sp_window_lo in Ulo; lia | apply HUPV; exact Ha]. }
rewrite <- restrict_mkst_fx in HS5.
(* br_run, with memnorm on both ends (the second segment of H_memnorm_drv_A) *)
apply (SRr_srealizes tfibsegs W' _ _ _ (proj1 (proj2 (HMND fx')) E4 W' regs4 mem4 md4 HS5 HMN4) HAI4).
intros W2 c2 _ HAI5 [HATB (msB1 & mdB1 & EcB & HMNB)]. destruct HATB as (-> & msB & matB & -> & HSB & HFB & HFrB). cbn [cfg_model] in HAI5.
injection EcB as <- <-.
set (mdB := with_vm_backing (m_vm_lazy md4) matB md4) in *.
pose proof (st_ok_mem_ok tfibsegs E4 S_BR _ HSB) as HMB. cbn [restrict ms_mem] in HMB.
rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 rsFQ_eq)))))))) in HMB.
assert (HwinB : forall a, usp - 65536 <= a < usp -> apresent (w_H W') (ms_mem msB) a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem msB) (ss_mem S_VP)); [exact HMB | left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem msB) (ss_mem S_VP)); [exact HMB | right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem msB) (ss_mem S_VP)); [exact HMB | right; right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia]. }
pose proof calls_checks as (_ & _ & _ & _ & CKF & WFF & NCF & MAF & KPF & WOKV & SOKV & WOKF & SOKF & _).
(* the invariant across br_run *)
assert (HUPB : YGcallStackUp.astack_up_x tfibsegs ly' W' usp (ms_mem msB))
by exact (PresetStkUpA.stk_up_frame E4 (ss_mem S_VP) ly' W' mem4 (ms_mem msB) usp WOKV E4_0
  ltac:(unfold sp_window_lo, sp_window_hi in *; lia) HTOP' HFB HUP4).
assert (HARB : ARcf tfibsegs B ly' S' [] W' (ms_mem msB) mdB).
{ apply (AR_after_run_cf ly' S' [] W' E4 (ss_mem S_VP) mem4 (ms_mem msB) md4 matB HAR4 WOKV); [rewrite E4_0; exact Ulo | rewrite E4_0; exact HCT | exact HFB |].
rewrite E4_0. intros a Ha. exact (apresent_some' _ _ _ (HwinB a Ha)). }
assert (HSOB : so_state xst (Datatypes.S j) (w_H W') (ms_mem msB)).
{ exact (so_state_frame xst XFR (Datatypes.S j) (w_H W') E4 (ss_mem S_VP) _ _ HFrB SOKV ltac:(rewrite E4_0; exact Ulo) ltac:(rewrite E4_0; exact E4_6) HSO4). }
assert (HROB : arodata_ok B (aview tfibsegs (w_H W') (ms_mem msB))).
{ exact (arodata_frame B (w_H W') E4 (ss_mem S_VP) _ _ HFrB WOKV ltac:(rewrite E4_0; exact Ulo) HRO4). }
assert (HfsB : m_fs mdB = ll_fs l) by (subst mdB; rewrite wvb_fs', Hfs4; subst mdV; rewrite wvb_fs'; exact Hmfs').
assert (HfdB : m_fds mdB = m_fds md') by (subst mdB; rewrite wvb_fds', Hfds4; subst mdV; rewrite wvb_fds'; reflexivity).
assert (HPIB : PCA.PINV (aview tfibsegs (w_H W') (ms_mem msB)) cnt' ran').
{ assert (HPI4 : PCA.PINV (aview tfibsegs (w_H W') mem4) cnt' ran') by exact (HFPP (w_H W') memV mem4 usp (usp - 288) cnt' ran' Ulo ltac:(lia) Hfr4 HPIV).
exact (HFRP (w_H W') E4 (ss_mem S_VP) mem4 (ms_mem msB) usp cnt' ran' HFrB WOKV E4_0 Ulo HPI4). }
assert (HPLB : 0 < payload_len data -> blk (w_H W') (ms_mem msB) q (payload_len data) (payload data)).
{ intros Hp. pose proof (HPL' Hp) as HPLm.
assert (Hinq : In (q, payload_len data) (ablocks B ly' S')) by (destruct HBL' as [(Hz & _) | (_ & HPm)]; [lia|]; apply (Permutation_in _ (Permutation_sym HPm)); right; left; reflexivity).
pose proof (alc_blocks _ _ ARL ly' S' [] W' mem' md' _ _ HAR' Hinq) as (_ & Hq4096 & Hqce & _).
assert (Hreqq : req_size (payload_len data) = payload_len data) by (unfold req_size; destruct (Z.eqb_spec (payload_len data) 0); lia). rewrite Hreqq in Hqce.
assert (NIMGQ : forall a, q <= a < q + payload_len data -> ~ in_img tfibsegs a).
{ intros a Ha. assert (Ha' : q <= a < q + req_size (payload_len data)) by (rewrite Hreqq; exact Ha).
exact (proj2 (alc_client_img _ _ ARL ly' S' [] W' mem' md' a HAR' (or_introl (ex_intro _ q (ex_intro _ (payload_len data) (conj Hinq Ha')))))). }
assert (HPLV : blk (w_H W') memV q (payload_len data) (payload data)).
{ apply (blk_of_frame_r _ E2 L_mem _ _ q (payload_len data) (payload data) usp HFrV (proj2 (proj2 (proj2 L_mem_wf))) E2_0 Ulo NIMGQ); [lia | lia | exact HPLm]. }
assert (HPL4 : blk (w_H W') mem4 q (payload_len data) (payload data)).
{ apply (blk_copy (w_H W') (w_H W') memV mem4 q q (payload_len data) (payload data)); [| exact (fun i Hi => NIMGQ (q + i) ltac:(lia)) | lia | lia | exact (fun i Hi => NIMGQ (q + i) ltac:(lia)) | lia | lia | exact HPLV].
intros i Hi. apply Hfr4; [lia | unfold PF_STK; lia |]. intros X. apply (NIMGQ (q + i) ltac:(lia)). apply in_img_rw. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in X. lia. }
apply (blk_of_frame_r _ E4 (ss_mem S_VP) _ _ q (payload_len data) (payload data) usp HFrB WOKV E4_0 Ulo NIMGQ); [lia | lia | exact HPL4]. }
destruct (Nat.eq_dec r 0) as [Hr0 | Hr1].
-
(* after the last call: the two frees' sites take NP S' and the driver's live bound; the payload free's model fact
   takes the batch room of ROOM_cf S', from the interface's iface_room_np_tail (ROOM_cf_k S' 2, a8's RK_room) *)
assert (HROOMc : ROOM_cf S') by exact (RK_room S' 2 (NPT S' HNP')).
assert (HL3 : (length (blocks S') <= 3)%nat).
{ destruct HBL' as [(_ & _ & HPm) | (_ & HPm)]; apply Permutation_length in HPm; unfold ablocks in HPm;
  rewrite length_map in HPm; cbn [length] in HPm; lia. }
assert (HSB' : st_ok tfibsegs E4 (add_cond S_BR cond_BRf) (restrict (w_H W') msB)).
{ apply (st_ok_add_cond tfibsegs E4 S_BR _ BC_EQ (SOff 166 (-1)) (SLit 0) HSB). cbn [ac_c ac_a ac_b sv_denot Sem.branch_taken].
rewrite E4_65, Hr0. reflexivity. }
apply (SRr_srealizes tfibsegs W' _ _ _ (fq_run E4 W' msB mdB HSB') HAI5).
intros W3 c3 _ HAI6 (-> & msF & matF & -> & HSF & HFF & HFrF). cbn [cfg_model] in HAI6.
set (mdF := with_vm_backing (m_vm_lazy mdB) matF mdB) in *.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W') E4 S_FQ msF HSF RVF) as HshapeF.
set (regsF := ms_regs msF) in *. set (memF := ms_mem msF) in *.
pose proof S_FQ_regs as (F1r & F2r & F3r & F4r & F8r & F10r).
assert (RF1 : getr regsF 1%bv = w64 RA_FQ) by (subst regsF; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E4 S_FQ msF 1%bv HSF), F1r; reflexivity).
assert (RF2 : getr regsF 2%bv = Z_to_bv 64 (usp + -208)) by (subst regsF; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E4 S_FQ msF 2%bv HSF), F2r; cbn [sv_denot]; rewrite E4_0; reflexivity).
assert (RF3 : getr regsF 3%bv = w64 TFIB_GP) by (subst regsF; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E4 S_FQ msF 3%bv HSF), F3r; reflexivity).
assert (RF4 : getr regsF 4%bv = w64 TFIB_TP) by (subst regsF; rewrite (st_ok_restrict_reg tfibsegs (w_H W') E4 S_FQ msF 4%bv HSF), F4r; reflexivity).
assert (RF8 : getr regsF 8%bv = w64 (payload_len data)).
{ subst regsF. rewrite (st_ok_restrict_reg tfibsegs (w_H W') E4 S_FQ msF 8%bv HSF), F8r. cbn [sv_denot].
rewrite Z.add_0_r, E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). rewrite <- E61. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (RF10 : getr regsF 10%bv = w64 q).
{ subst regsF. rewrite (st_ok_restrict_reg tfibsegs (w_H W') E4 S_FQ msF 10%bv HSF), F10r. cbn [sv_denot].
rewrite Z.add_0_r, E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). rewrite <- E63. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (HspF : spZ regsF = usp + -208) by (unfold spZ; rewrite RF2; apply u64_lit; unfold sp_window_lo in Ulo; lia).
assert (HraF : raZ regsF = RA_FQ) by (unfold raZ; rewrite RF1; apply u64_lit; unfold RA_FQ; lia).
pose proof (st_ok_mem_ok tfibsegs E4 S_FQ _ HSF) as HMF. cbn [restrict ms_mem] in HMF. fold memF in HMF.
rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 rsFQ_eq))))))))) in HMF.
assert (HwinF : forall a, usp - 65536 <= a < usp -> apresent (w_H W') memF a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E4 (w_H W') memF (ss_mem S_VP)); [exact HMF | left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') memF (ss_mem S_VP)); [exact HMF | right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') memF (ss_mem S_VP)); [exact HMF | right; right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia]. }
assert (HARF : ARcf tfibsegs B ly' S' [] W' memF mdF).
{ apply (AR_after_run_cf ly' S' [] W' E4 (ss_mem S_VP) (ms_mem msB) memF mdB matF HARB WOKV); [rewrite E4_0; exact Ulo | rewrite E4_0; exact HCT | exact HFF |].
rewrite E4_0. intros a Ha. exact (apresent_some' _ _ _ (HwinF a Ha)). }
(* the exit path's free call facts (field round 3): the hull at S' from the interface's count over the j + 1 calls
   made (A18 / A17: at most 4 calls), the read-only bytes across fq_run *)
assert (HHOF : @cf_hull_ok CfParamsPreset.CfParams_preset S').
{ apply (PresetDrvHull.drv_cf_hull_ok_of_run sm (map (fun b : byte => bv_unsigned b) (payload data)) (os ++ [o]) S');
    [rewrite length_app, Hlos; cbn [length]; lia | unfold PCA.iface_room_at in HRA'; tauto]. }
assert (HROF : arodata_ok B (aview tfibsegs (w_H W') memF)).
{ exact (arodata_frame B (w_H W') E4 (ss_mem S_VP) _ _ HFrF WOKV ltac:(rewrite E4_0; exact Ulo) HROB). }
assert (HSOF : so_state xst (Datatypes.S j) (w_H W') memF).
{ exact (so_state_frame xst XFR (Datatypes.S j) (w_H W') E4 (ss_mem S_VP) _ _ HFrF SOKV ltac:(rewrite E4_0; exact Ulo) ltac:(rewrite E4_0; exact E4_6) HSOB). }
assert (HWF' : Wf_cf (as_universe B) S') by exact (amc_wf _ _ _ _ _ (proj1 HARF)).
assert (HUB : universe_ok (as_universe B)) by exact (amc_universe _ _ _ _ _ (proj1 HARF)).
assert (PREF : drv_pre_nomn_cf B iface_room_np ly' S' W' regsF memF mdF).
{ split; [exact HARF|]. split; [unfold top_ok in *; tauto|].
split; [rewrite RF1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity|]. split; [rewrite HraF; unfold RA_FQ; lia|].
split; [rewrite HspF; rewrite <- Zplus_mod_idemp_l, U16; reflexivity|].
split; [rewrite HspF; unfold sp_window_lo in *; lia|]. split; [rewrite HspF; unfold top_ok in HTOP'; lia|].
split; [rewrite HspF; intros a Ha; apply HwinF; unfold ASTACK in Ha; lia|].
split; [rewrite (ts_gp B HB); exact RF3|]. split; [rewrite (ts_tp B HB); exact RF4|].
split; [unfold s0Z; rewrite RF8; unfold w64; rewrite u64_lit by lia; lia|].
split; [exact HQT'|]. split; [exact HNP'|]. split; [exact HXS'|]. split; [exact HHOF | exact HROF]. }
assert (Hinb : In (buf, cap) (ablocks B ly' S')) by (destruct HBL' as [(_ & _ & HPm) | (_ & HPm)]; apply (Permutation_in _ (Permutation_sym HPm)); left; reflexivity).
assert (Hbuf : 4096 <= buf).
{ pose proof (alc_blocks _ _ ARL ly' S' [] W' memF mdF _ _ HARF Hinb) as (_ & X & _). exact X. }
rewrite HshapeF, PCF. fold regsF memF. replace (Z_to_bv 64 A_wrap_free) with (w64 (pc_wrap_free (as_code B))) by (rewrite (ts_code B HB); reflexivity).
change (mkCfg (mkst regsF (w64 (pc_wrap_free (as_code B))) memF (seg_rom tfibsegs)) mdF) with (cfg_at tfibsegs (pc_wrap_free (as_code B)) regsF memF mdF).
assert (FSITE : exists (pf : sptr) (nf : Z) (Eb : Z -> Prop),
(pf = PNull \/ In (pf, nf) (blocks S')) /\ (forall a, Eb a -> a < alloc_ceiling /\ ~ in_img tfibsegs a) /\ (forall a, Eb a -> ~ STDOUT_MUT a) /\
(pf = PNull -> payload_len data = 0) /\ (pf <> PNull -> sptr_addr B ly' pf = q /\ nf = payload_len data /\ 0 < payload_len data) /\
YA0nH.SRr' tfibsegs YGcfRehidePost.RZ_cf W' (cfg_at tfibsegs (pc_wrap_free (as_code B)) regsF memF mdF)
(fun W'' c'' => exists ly6 S6 regs6 mem6 md6 trc tr,
In trc (as_universe B) /\ apath (free_cf pf trc S') tr (tt, S6) /\
c'' = cfg_at tfibsegs (raZ regsF) regs6 mem6 md6 /\
YGcfRehidePost.acall_post_cf_rh tfibsegs B ASTACK ly' S' [] W' regsF memF mdF Eb ly6 S6 W'' regs6 mem6 md6 /\
qtight S6 /\ iface_room_np S6 /\ xs_placed_cf ly6 S6)).
{ destruct HBL' as [(Hz & Hq & HPm) | (Hp & HPm)].
- exists PNull, 0, (fun _ => False). split; [left; reflexivity|]. split; [intros a []|]. split; [intros a []|].
split; [intros _; exact Hz|]. split; [intros X; exfalso; exact (X eq_refl)|].
apply (FREEN fx' ly' S' W' regsF memF mdF PREF HL3).
+ rewrite RF10, Hq. reflexivity.
+ rewrite (ts_code B HB), HraF. apply (ts_universe_drv B HB). cbn. tauto.
+ rewrite (ts_code B HB). apply (ts_universe_drv B HB). cbn. tauto.
- assert (Hinq : In (q, payload_len data) (ablocks B ly' S')) by (apply (Permutation_in _ (Permutation_sym HPm)); right; left; reflexivity).
pose proof (alc_blocks _ _ ARL ly' S' [] W' memF mdF _ _ HARF Hinq) as (_ & Hq4096 & Hqce & _).
assert (NIMGQ : forall a, q <= a < q + req_size (payload_len data) -> ~ in_img tfibsegs a).
{ intros a Ha. exact (proj2 (alc_client_img _ _ ARL ly' S' [] W' memF mdF a HARF (or_introl (ex_intro _ _ (ex_intro _ _ (conj Hinq Ha)))))). }
unfold ablocks in Hinq. apply in_map_iff in Hinq as ([pf nf] & Hpf & Hinbf). cbn [fst snd] in Hpf. injection Hpf as Hq Hn.
assert (Hreqq : req_size (payload_len data) = payload_len data) by (unfold req_size; destruct (Z.eqb_spec (payload_len data) 0); lia).
rewrite Hreqq in Hqce, NIMGQ.
exists pf, nf, (fun a => sptr_addr B ly' pf <= a < sptr_addr B ly' pf + req_size nf).
split; [right; exact Hinbf|]. split; [intros a Ha; rewrite Hq, Hn, Hreqq in Ha; split; [lia | exact (NIMGQ a Ha)]|].
split; [intros a Ha X; rewrite Hq, Hn, Hreqq in Ha; apply (NIMGQ a Ha); apply in_img_rw; unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in X; lia|].
split; [intros ->; exfalso; cbn in Hq; lia|]. split; [intros _; rewrite Hq, Hn; repeat split; [reflexivity .. | exact Hp]|].
unfold YA0nH.SRr'. eapply YA0nH.SRrG_mono; [apply (FREE fx' ly' S' W' regsF memF mdF pf nf PREF HL3 Hinbf) |].
+ rewrite RF10, Hq. reflexivity.
+ rewrite (ts_code B HB), HraF. apply (ts_universe_drv B HB). cbn. tauto.
+ rewrite (ts_code B HB). apply (ts_universe_drv B HB). cbn. tauto.
+ (* the exit path after the last call needs no memnorm: drop the free post's keep (its last conjunct) *)
cbv beta. intros W5 c5 _ (ly7 & S7 & regs7 & mem7 & md7 & trc7 & tr7 & X1 & X2 & X3 & X4 & X5 & X6 & X7 & _).
exists ly7, S7, regs7, mem7, md7, trc7, tr7. exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 X7)))))). }
destruct FSITE as (pf & nf & Eb & Hpfin & HEb & HEbso & HpfN & HpfB & FSITE).
eapply (YA0nH.SRrG_srealizes tfibsegs (YA0nH.wle' tfibsegs YGcfRehidePost.RZ_cf) W'
  (cfg_at tfibsegs (pc_wrap_free (as_code B)) regsF memF mdF)); [exact FSITE | exact HAI6 |].
cbv beta. intros W4 c4 Hwle4 HAI7 (ly6 & S6 & regs6 & mem6 & md6 & trc6 & tr6 & Htrc6 & Hpath6 & -> & HPOST6 & HQT6x & HNP6 & HXS6). cbn [cfg_model] in HAI7.
unfold cfg_at. rewrite HraF.
pose proof HPOST6 as (HAR6 & Hlyle6 & Hwle6 & HP6 & Hio6 & Hfr6 & Hsc6).
assert (Hbat : batch_room_cf S') by exact (proj2 (proj2 HROOMc)).
destruct (atok_cf_apath _ _ _ tr6 _ (ml_free_cf (as_universe B) HUB S' pf nf trc6 HWF' Hbat
ltac:(destruct Hpfin as [X|X]; [left; exact X | right; exact X]) (YG01.admits_fix _ _ S' HUB Htrc6)) Hpath6) as (ns6 & HFP).
cbn [free_post_ycf snd] in HFP. destruct HFP as (HWF6 & Hnev6 & _ & Hfr6' & (l1 & l2 & Hcase & Hbl6) & HQT6). cbn [snd] in HWF6, Hnev6, Hbl6, Hfr6', HQT6.
destruct (same_io_fs_fds _ _ Hio6) as [Efs6 Efds6].
pose proof (alc_layout _ _ ARL ly' S' [] W' memF mdF ly6 HARF Hlyle6) as (Habl6 & _ & _).
assert (EXT6 : forall b n, In (b, n) (blocks S') -> sptr_addr B ly6 b = sptr_addr B ly' b).
{ intros b n Hb. unfold ablocks in Habl6. pose proof (ext_in_map Habl6 (b, n) Hb) as X. cbn [fst snd] in X. injection X as X1. exact X1. }
assert (HBL6 : exists pb6, In (pb6, cap) (blocks S6) /\ sptr_addr B ly6 pb6 = buf).
{ unfold ablocks in Hinb. apply in_map_iff in Hinb as ([b0 n0] & Eb0 & HinS'). cbn [fst snd] in Eb0. injection Eb0 as Ea En. subst n0.
assert (GOAL : In (b0, cap) (blocks S6) \/ exists b1, In (b1, cap) (blocks S6) /\ sptr_addr B ly' b1 = buf).
{ destruct HBL' as [(Hz & Hq0 & HPm) | (Hp & HPm)].
- assert (Epf : pf = PNull).
{ destruct pf; [reflexivity | | |]; exfalso; (destruct (HpfB ltac:(discriminate)) as (_ & _ & X)); lia. }
subst pf. left. rewrite Hbl6. destruct Hcase as [[_ E12] | E12].
+ rewrite E12. exact HinS'.
+ rewrite E12 in HinS'. apply in_app_or in HinS' as [X|[X|X]]; apply in_or_app; [left; exact X | | right; exact X].
exfalso. injection X as Xb Xn. rewrite <- Xb in Ea. cbn in Ea. lia.
- assert (NE : pf <> PNull) by (intros ->; pose proof (HpfN eq_refl); lia).
destruct (HpfB NE) as (Hq & Hn & _).
destruct Hcase as [[Ez _] | E12]; [exfalso; exact (NE Ez)|].
right. unfold ablocks in HPm. rewrite E12, map_app in HPm. cbn [map fst snd] in HPm. rewrite Hq, Hn in HPm.
change [(buf, cap); (q, payload_len data)] with ([(buf, cap)] ++ (q, payload_len data) :: []) in HPm.
pose proof (Permutation_app_inv _ _ [(buf, cap)] [] (q, payload_len data) HPm) as HP2. rewrite app_nil_r, <- map_app in HP2.
assert (Hin2 : In (buf, cap) (map (fun b : sptr * Z => (sptr_addr B ly' (fst b), snd b)) (l1 ++ l2))).
{ apply (Permutation_in _ (Permutation_sym HP2)). left. reflexivity. }
apply in_map_iff in Hin2 as ([b1 n1] & Eb1 & Hin1). cbn [fst snd] in Eb1. injection Eb1 as Ea1 En1. subst n1.
exists b1. split; [rewrite Hbl6; exact Hin1 | exact Ea1]. }
destruct GOAL as [X | (b1 & X & Ea1)].
- exists b0. split; [exact X|]. rewrite (EXT6 b0 cap HinS'). exact Ea.
- exists b1. split; [exact X|].
assert (Hin1' : In (b1, cap) (blocks S')).
{ rewrite Hbl6 in X. destruct Hcase as [[_ E12] | E12]; rewrite E12 || rewrite <- E12; [exact X|]. apply in_app_or in X as [Y|Y]; apply in_or_app; [left; exact Y | right; right; exact Y]. }
rewrite (EXT6 b1 cap Hin1'). exact Ea1. }
destruct HBL6 as (pb6 & Hbl6S & Hpb6).
rewrite HshapeF, restrict_mkst_fx in HSF. fold regsF memF in HSF. rewrite <- restrict_mkst_fx, <- HshapeF in HSF.
pose proof (PresetD1rAx.drv_after_call_cf_rh B HB ARL K_FQ E4 S_FQ msF ly' S' [] W' mdF Eb ly6 S6 W4 regs6 mem6 md6 rsFQ RA_FQ usp (-208)
HSF RVF CKF WFF NCF MAF submem_FQ F1r HPOST6 HARF HEb KPF E4_0 E4_6 HspF ltac:(lia) Ulo HCT ltac:(intros a Ha; apply HwinF; lia)) as HS7.
rewrite S_FQr_eq in HS7. set (E8 := havoc E4 K_FQ (map (getr regs6) CLOB)) in HS7.
assert (E8old : forall i, (i < K_FQ)%nat -> ew E8 i = ew E4 i) by (intros i Hi; subst E8; apply ew_havoc_old; exact Hi).
assert (E8_0 : bv_unsigned (ew E8 0) = usp) by (rewrite E8old by (unfold K_FQ, A_BUF, A_LEN, K_PP; lia); exact E4_0).
assert (E8_6 : usp <= bv_unsigned (ew E8 6)) by (rewrite E8old by (unfold K_FQ, A_BUF, A_LEN, K_PP; lia); exact E4_6).
assert (HSO6 : so_state xst (Datatypes.S j) (w_H W4) mem6).
{ apply (so_state_keep xst XFR (Datatypes.S j) (w_H W') (w_H W4) memF mem6); [| exact HSOF]. intros a Ha. apply Hfr6.
- unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. lia.
- exact (so_not_owned_cf ly' S' [] W' memF mdF a HARF Ha).
- exact (so_not_owned_cf ly6 S6 [] W4 mem6 md6 a HAR6 Ha).
- unfold ascratch. rewrite HspF, (ts_errno B HB). unfold TFIB_ERRNO, ASTACK. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. unfold sp_window_lo in Ulo. lia.
- intros X. exact (HEbso a X Ha).
- apply dsn_not_img. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. lia. }
apply (SRr_srealizes tfibsegs W4 _ _ _ (xm_run E8 W4 regs6 mem6 md6 HS7) HAI7).
intros W5 c5 _ HAI8 (-> & msX & matX & -> & HSX & HFX & HFrX). cbn [cfg_model] in HAI8.
set (mdX := with_vm_backing (m_vm_lazy md6) matX md6) in *.
pose proof (st_ok_mem_ok tfibsegs E8 S_XM _ HSX) as HMX. cbn [restrict ms_mem] in HMX. rewrite (proj1 (proj2 rsFQ_eq)) in HMX.
assert (HwinX : forall a, usp - 65536 <= a < usp -> apresent (w_H W4) (ms_mem msX) a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E8 (w_H W4) (ms_mem msX) (WIN (-208) :: rsFQ)); [exact HMX | left; reflexivity | exact E8_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E8 (w_H W4) (ms_mem msX) (WIN (-208) :: rsFQ)); [exact HMX | right; left; reflexivity | exact E8_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E8 (w_H W4) (ms_mem msX) (WIN (-208) :: rsFQ)); [exact HMX | right; right; left; reflexivity | exact E8_0 | lia | lia | cbn; lia]. }
assert (HARX : ARcf tfibsegs B ly6 S6 [] W4 (ms_mem msX) mdX).
{ apply (AR_after_run_cf ly6 S6 [] W4 E8 (WIN (-208) :: rsFQ) mem6 (ms_mem msX) md6 matX HAR6 WOKF); [rewrite E8_0; exact Ulo | rewrite E8_0; exact HCT | exact HFX |].
rewrite E8_0. intros a Ha. exact (apresent_some' _ _ _ (HwinX a Ha)). }
assert (HSOX : so_state xst (Datatypes.S j) (w_H W4) (ms_mem msX)).
{ exact (so_state_frame xst XFR (Datatypes.S j) (w_H W4) E8 (WIN (-208) :: rsFQ) _ _ HFrX SOKF ltac:(rewrite E8_0; exact Ulo) ltac:(rewrite E8_0; exact E8_6) HSO6). }
pose proof (xm_to_CM E8 W4 msX HSX) as (HSCM & V79 & ECold).
set (E9 := E_CM E8 (ms_regs msX)) in *.
rewrite Hr0. cbn [lib_iter]. apply (srz_conseq tfibsegs _ (wr ch_stdout (concat (repeat line0 (N - 1))) (ex 0 (ll_fs l)))); [| apply run_tail_eq].
replace (N - 1)%nat with (Datatypes.S j - 1)%nat by lia.
replace (ex 0 (ll_fs l)) with (ex (if count_mode data then 0 else 0) (ll_fs l)) by (destruct (count_mode data); reflexivity).
assert (HL36 : (length (blocks S6) <= 3)%nat).
{ rewrite Hbl6. destruct Hcase as [[_ E12] | E12].
  - rewrite E12. exact HL3.
  - rewrite E12 in HL3. rewrite length_app in HL3 |- *. cbn [length] in HL3. lia. }
apply (PresetD1rAt.tfib_main_tail_cf B iface_room_np HB ARL xst (FREE fx') (EXITL fx') XFR sp inp xw xd a0 p Hsp Hva Hve
E9 W4 msX mdX ly6 S6 data pb6 cap 0 (Datatypes.S j) (ll_fs l)).
+ intros i Hi. rewrite ECold by (unfold K_CM, K_M1 in *; lia). rewrite E8old by (unfold K_FQ, K_M1 in *; lia). rewrite E4old by (unfold K_VP, K_M1 in *; lia).
rewrite E2old by (unfold K_LR, K_M1 in *; lia). apply HEE. exact Hi.
+ change (ed E9 2) with (ed E 2). exact HEd.
+ exact Hlen.
+ rewrite ECold by (unfold K_CM, A_BUF, A_LEN, K_PP; lia). rewrite E8old by (unfold K_FQ, A_BUF, A_LEN, K_PP; lia). rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). rewrite Hpb6. exact E41.
+ exact V79.
+ left. reflexivity.
+ exact HSCM.
+ exact HAI8.
+ exact HARX.
+ exact (top_ok_le _ _ _ _ Hlyle6 HTOP').
+ exact Hbl6S.
+ exact HL36.
+ exact (HQT6 HQT').
+ exact HNP6.
+ exact HXS6.
+ exact (PresetDrvHull.drv_cf_hull_ok_free pf trc6 S' tr6 S6 HHOF Hpath6).
+ exact (PresetDrvAroA.drv_arodata_mem B HB (WIN (-208) :: rsFQ) E8 (w_H W4) (ms_mem msX) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) HMX).
+ exact HSOX.
+ intros fd. subst mdX. rewrite wvb_fds', Efds6. subst mdF. rewrite wvb_fds', HfdB, Hfdl. apply Hfdl0.
+ subst mdX. rewrite wvb_fs', Efs6. subst mdF. rewrite wvb_fs'. exact HfsB.
-
assert (HSB' : st_ok tfibsegs E4 (add_cond S_BR cond_BRt) (restrict (w_H W') msB)).
{ apply (st_ok_add_cond tfibsegs E4 S_BR _ BC_NE (SOff 166 (-1)) (SLit 0) HSB). cbn [ac_c ac_a ac_b sv_denot Sem.branch_taken].
rewrite E4_65. cbn [negb].
destruct (bv_eqb (Z_to_bv 64 (Z.of_nat (Datatypes.S r) + -1)) (Z_to_bv 64 0)) eqn:Eq; [|reflexivity].
exfalso. apply bv_eqb_eq in Eq. apply (f_equal bv_unsigned) in Eq. rewrite !u64_lit in Eq by lia. lia. }
(* l2_run, with memnorm on both ends (the third segment of H_memnorm_drv_A) *)
apply (SRr_srealizes tfibsegs W' _ _ _ (proj2 (proj2 (HMND fx')) E4 W' msB mdB HSB' HMNB) HAI5).
intros W3 c3 _ HAI6 [HATL (msL1 & mdL1 & EcL & HMNL)]. destruct HATL as (-> & msL & matL & -> & HSL2 & HFL & HFrL). cbn [cfg_model] in HAI6.
injection EcL as <- <-.
set (mdL := with_vm_backing (m_vm_lazy mdB) matL mdB) in *.
pose proof (st_ok_mem_ok tfibsegs E4 S_L2 _ HSL2) as HML. cbn [restrict ms_mem] in HML.
assert (HwinL : forall a, usp - 65536 <= a < usp -> apresent (w_H W') (ms_mem msL) a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 208)); [| destruct (Z.lt_ge_cases a (usp - 128))].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem msL) (ss_mem S_L2)); [exact HML | left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem msL) (ss_mem S_L2)); [exact HML | right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E4 (w_H W') (ms_mem msL) (ss_mem S_L2)); [exact HML | right; right; left; reflexivity | exact E4_0 | lia | lia | cbn; lia]. }
(* the invariant across l2_run, to the next call *)
assert (HUPL : YGcallStackUp.astack_up_x tfibsegs ly' W' usp (ms_mem msL))
by exact (PresetStkUpA.stk_up_frame E4 (ss_mem S_VP) ly' W' (ms_mem msB) (ms_mem msL) usp WOKV E4_0
  ltac:(unfold sp_window_lo, sp_window_hi in *; lia) HTOP' HFL HUPB).
assert (HARL : ARcf tfibsegs B ly' S' [] W' (ms_mem msL) mdL).
{ apply (AR_after_run_cf ly' S' [] W' E4 (ss_mem S_VP) (ms_mem msB) (ms_mem msL) mdB matL HARB WOKV); [rewrite E4_0; exact Ulo | rewrite E4_0; exact HCT | exact HFL |].
rewrite E4_0. intros a Ha. exact (apresent_some' _ _ _ (HwinL a Ha)). }
assert (HSOL : so_state xst (Datatypes.S j) (w_H W') (ms_mem msL)).
{ exact (so_state_frame xst XFR (Datatypes.S j) (w_H W') E4 (ss_mem S_VP) _ _ HFrL SOKV ltac:(rewrite E4_0; exact Ulo) ltac:(rewrite E4_0; exact E4_6) HSOB). }
assert (HROL : arodata_ok B (aview tfibsegs (w_H W') (ms_mem msL))).
{ exact (arodata_frame B (w_H W') E4 (ss_mem S_VP) _ _ HFrL WOKV ltac:(rewrite E4_0; exact Ulo) HROB). }
pose proof (l2_to_L E4 W' msL (Z.of_nat (Datatypes.S r)) HSL2 E4_65 ltac:(lia)) as (HSLn & V65n & ELold).
set (E6n := E_L2 E4 (ms_regs msL)) in *.
apply (IH fx' Hfz' (Datatypes.S j) E6n W' msL mdL ly' S' data buf cap q (ll_fs l) N cnt' ran' Hlk Hok).
+ intros i Hi. rewrite ELold by (unfold K_M1 in Hi; lia). rewrite E4old by (unfold K_VP, K_M1 in *; lia). rewrite E2old by (unfold K_LR, K_M1 in *; lia). apply HEE. exact Hi.
+ change (ed E6n 2) with (ed E 2). exact HEd.
+ rewrite ELold by (unfold A_BUF, A_LEN, K_PP; lia). rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). exact E41.
+ rewrite ELold by (unfold A_BUF, A_LEN, K_PP; lia). rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). exact E61.
+ rewrite ELold by (unfold A_BUF, A_LEN, K_PP; lia). rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). exact E62.
+ rewrite ELold by (unfold A_BUF, A_LEN, K_PP; lia). rewrite E4old by (unfold K_VP, A_BUF, A_LEN, K_PP; lia). rewrite E2old by (unfold K_LR, A_BUF, A_LEN, K_PP; lia). exact E63.
+ rewrite V65n. lia.
+ exact HSLn.
+ lia.
+ lia.
+ lia.
+ exact HBL'.
+ intros Hp. assert (Hinq : In (q, payload_len data) (ablocks B ly' S')) by (destruct HBL' as [(Hz & _) | (_ & HPm)]; [lia|]; apply (Permutation_in _ (Permutation_sym HPm)); right; left; reflexivity).
pose proof (alc_blocks _ _ ARL ly' S' [] W' mem' md' _ _ HAR' Hinq) as (_ & Hq4096 & Hqce & _).
assert (Hreqq : req_size (payload_len data) = payload_len data) by (unfold req_size; destruct (Z.eqb_spec (payload_len data) 0); lia). rewrite Hreqq in Hqce.
apply (blk_of_frame_r _ E4 (ss_mem S_VP) _ _ q (payload_len data) (payload data) usp HFrL WOKV E4_0 Ulo); [| lia | lia | exact (HPLB Hp)].
intros a Ha. assert (Ha' : q <= a < q + req_size (payload_len data)) by (rewrite Hreqq; exact Ha).
exact (proj2 (alc_client_img _ _ ARL ly' S' [] W' mem' md' a HAR' (or_introl (ex_intro _ q (ex_intro _ (payload_len data) (conj Hinq Ha')))))).
+ exact Hfrs.
+ exact HQT'.
+ exact HNP'.
+ exact HWR'.
+ exists (os ++ [o]), H0, hist'. split; [rewrite length_app, Hlos; cbn [length]; lia | exact HRA'].
+ exact HXS'.
+ exact HAI6.
+ exact HARL.
+ exact HTOP'.
+ unfold PCA.LCNT, PCA.SIZE_MAX in *. lia.
+ exact Hcap.
+ exact HLc.
+ exact Hlen.
+ exact HSOL.
+ exact HROL.
+ exact (HFRP (w_H W') E4 (ss_mem S_VP) (ms_mem msB) (ms_mem msL) usp cnt' ran' HFrL WOKV E4_0 Ulo HPIB).
+ exact HMNL.
+ exact HUPL.
+ split; [intros fd; subst mdL; rewrite wvb_fds', HfdB, Hfdl; apply Hfdl0|].
split; [subst mdL; rewrite wvb_fs'; exact HfsB | exact Hsorted].
Qed.

(* lib/A/AD1r.v:1012 tfib_loop_L_at over ARcf / PINV. *)
Theorem tfib_loop_L_at_cf : forall (fx : YK11.FPState), YK0o.frm_zero (@YK11.fp_csr fx) ->
forall E (W : world tfibsegs) ms md ly S data (pb pq : sptr) (cap q : Z) (j r : nat) (fs : Fs) (cnt ran : Z),
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data ->
(forall k, (k < K_M1)%nat -> ew E k = ew EL k) -> ed E 2 = data ->
bv_unsigned (ew E A_BUF) = sptr_addr B ly pb -> bv_unsigned (ew E A_LEN) = dlen data ->
bv_unsigned (ew E 161) = sptr_addr B ly pb + 2 + config_len data ->
bv_unsigned (ew E 162) = payload_len data -> bv_unsigned (ew E 163) = (if payload_len data =? 0 then A_EMPTY_tfa else q) ->
bv_unsigned (ew E 164) = q -> bv_unsigned (ew E 166) = Z.of_nat r ->
st_ok tfibsegs E S_L (restrict (w_H W) ms) ->
(1 <= r)%nat -> (j + r = calls data)%nat ->
((payload_len data = 0 /\ q = 0 /\ blocks S = [(pb, cap)])
\/ (0 < payload_len data /\ blocks S = [(pb, cap); (pq, payload_len data)] /\ sptr_addr B ly pq = q)) ->
(0 < payload_len data -> blk (w_H W) (ms_mem ms) q (payload_len data) (payload data)) ->
frames S = [] -> qtight S -> iface_room_np S ->
YCbqGwild.wild_room (as_universe B) [] (r * YCbqGwild.K_LLVMF) (st_depot S) ->
(exists os H0 hist, length os = j /\ PCA.iface_room_at sm (map (fun b : byte => bv_unsigned b) (payload data)) os H0 hist S) -> xs_placed_cf ly S ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly S [] W (ms_mem ms) md -> top_ok usp ly ->
cnt + Z.of_nat r * PCA.LCNT < 2 ^ 62 - 2 ^ 30 -> 65536 <= cap <= 2 ^ 26 -> dlen data < cap ->
((j = 0%nat /\ stdout_img (w_H W) (ms_mem ms)) \/ ((1 <= j)%nat /\ xst j (w_H W) (ms_mem ms))) ->
arodata_ok B (aview tfibsegs (w_H W) (ms_mem ms)) ->
PCA.PINV (aview tfibsegs (w_H W) (ms_mem ms)) cnt ran ->
YAkMemnorm.memnorm tfibsegs (ms_mem ms) ->
YGcallStackUp.astack_up_x tfibsegs ly W usp (ms_mem ms) ->
((forall k, fd_lookup (m_fds md) k = fd_lookup APSG.fds_std k) /\ m_fs md = fs /\ Fs.fs_sorted fs = true) ->
srealizes tfibsegs (mkCfg ms md) (loop_tgt (LS := LS) (payload data) (calls data) j r fs).
Proof.
intros fx Hfz E W ms md ly S data pb pq cap q j r fs cnt ran Hlk Hok HEE HEd E41 E42 E60 E61 E62 E63 E65 HS Hr Hjr HBL HPL Hfr HQT HNP HWR HRA HXS HAI HAR HTOP Hcnt Hcap HLc HSO HRO HPI HMN HUP HMD.
pose proof (calls_bound data) as Hcb. pose proof (config_len_bound data) as Hcl.
apply (calls_loop_cf r fx Hfz j E W ms md ly S data (sptr_addr B ly pb) cap q fs (calls data) cnt ran Hlk Hok HEE HEd E41 E61 E62 E63 E65 HS Hr Hjr ltac:(lia)).
- destruct HBL as [(Hz & Hq & Hbl) | (Hp & Hbl & Hpq)]; [left | right]; unfold ablocks; rewrite Hbl; cbn [map fst snd app].
+ split; [exact Hz|]. split; [exact Hq | apply Permutation_refl].
+ split; [exact Hp|]. rewrite Hpq. apply Permutation_refl.
- exact HPL.
- exact Hfr.
- exact HQT.
- exact HNP.
- exact HWR.
- exact HRA.
- exact HXS.
- exact HAI.
- exact HAR.
- exact HTOP.
- exact Hcnt.
- exact Hcap.
- exact HLc.
- unfold dlen in Hok. lia.
- exact HSO.
- exact HRO.
- exact HPI.
- exact HMN.
- exact HUP.
- exact HMD.
Qed.
End g.

(* lib/A/AD1r.v:1053 tfib_loop_L over ARcf / PINV / the program interface. *)
Theorem tfib_loop_L_cf (B : asyms) (xst : nat -> (word -> bool) -> (word -> option byte) -> Prop) (NR : ProcInput -> Prop)
(sm : list Z -> Z * Z) (iface_room_np : astate -> Prop)
(MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (PAYLOAD_ROOM : list byte -> Prop) :
loop_L_x_A_at (rc := rc) (LS := LS) (L := L) (PA := PA)
B xst NR sm iface_room_np MT XM_LIB XN_LIB PAYLOAD_ROOM.
Proof.
intros HB ARL MT_FREE RO_IN NRB LIBC UNIV HSIG PF1 PFN FREE FREEN EXITL XFR NPT HMND.
intros fx Hfz sp inp xw xd E W ms md ly S a0 p data pb pq cap q j r fs cnt ran Hargv Hsp Hva Hve Hvfs HNR.
eapply tfib_loop_L_at_cf; eassumption.
Qed.
End e.

(* ---------------------------------------------------------------------- *)
(* THE THEOREM (PresetD1rA.v section 3), at CwPinvA's proved PINV frame theorems (lib/A/PresetPinvAPf.v). *)
Theorem loop_L_x_A_holds : loop_L_x_A.
Proof.
intros rc LS ci L PA B xst NR sm iface_room_np MT XM_LIB XN_LIB PAYLOAD_ROOM.
exact (tfib_loop_L_cf (rc := rc) (LS := LS) (ci := ci) (L := L) (PA := PA)
B xst NR sm iface_room_np MT XM_LIB XN_LIB PAYLOAD_ROOM).
Qed.
End P.
