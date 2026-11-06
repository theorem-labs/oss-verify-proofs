(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from tfib_run_QM of proofs/cgif/cgif_file_fuzzer/lib/YD2e.v:651-659
   (relocated here as lib/Reusable/YD2e.v; the proof follows tfib_run_QM_at, YD2e.v:379-650), for fuzz_preset's
   asan-ubsan image; lib/A/PresetD2eA.v is its asan twin, and this file is that file's port/a2b.py output (comments
   re-pointed at the B lanes and the B donor's line numbers). Nothing in this file is a proof of a function (rule 24: the composition
   / driver layer of a port).
   STATEMENT FILE since a working branch: section 3 (the proof of runqm_cf_B, runqm_cf_B_holds) is MOVED
   byte for byte to lib/AU/PresetD2eBPf.v (no proof change), so that the driver composition can cite runqm_cf_B
   while that proof waits for the prefix memnorm re-run (it does not build on the new interface).
   RUNQM is the driver's arm from the payload malloc to the loop head: `malloc(payload_len)`, the NULL check, the
   memcpy of the payload and the jump to the per-call loop. Changes from the donor's tfib_run_QM:
   (1) the allocator invariant is preset's second instance, ARcf at the ghost set Hp = [], throughout: the switch from
       cgif's AR is at the allocator's initial state (a Theorem Labs lane with a Theorem Labs lane, 2026-10-28 22:44Z), so RUNQM converts
       nothing. Its laws are a8's AR_laws_ok_cf (YG0lawscf.v), cited, not a premise;
   (2) the room carries NO headroom number any more (the sum form was unsatisfiable; section 0 below). The tail
       hands over the interface's non-primary room NP S (iface_room_np of lib/AU/PresetCfnB.v); the payload
       malloc site takes it as it is, and RUNQM reads the one-call ROOM_cf S a8's success lemma needs off it by
       the interface's iface_room_np_tail. The loop is handed NP S' by the interface's iface_room_np_step and
       P8's premise iface_room_at at S', which iface_room_at_driver below PROVES at this driver leaf;
   (3) malloc_cf may return PNull (CwPreB's malloc site hands every outcome to the continuation): RUNQM refutes PNull
       with a8's malloc_cf_success_of_room (YGcfPath.v), from tail_at's prim_pristine_except S [kBatchClass]
       (room_cf_of_pristine below); the donor's event regime is gone;
   (4) the error buffer's extents (malloc_leaf_cf's frame exceptions) are placed by xs_placed_cf, which tail_at and
       the malloc leaf carry and the loop takes; xs_cf_off_img below gives them below the ceiling and off the image;
   (5) cgif's FINV is the program interface's PINV (lib/AU/PresetCfnB.v) at the start-up ledger 0 0, carried by lane
       CwPinvB's frame results finv_site_pinv_B / finv_run_pinv_B / finv_icpt_pinv_B (statements in
       lib/AU/PresetPinvB.v), taken as premises of runqm_cf_B by the parallel rule, never by importing a proof file;
   (6) NEW premise NR inp (the agreement's no-refusal premise, the internal file closedwalk-plan.md 2f), passed to the loop;
   (7) the donor's unused leaves FREE, EXITL and XFR are dropped (tfib_run_QM_at never uses them, YD2e.v:657), and
       so are its ML / AR_laws premises (cited instead, (1) and (2)); the loop is entered at every float state with a
       zero rounding mode (lane CwLoopB's loop_L_cf_B), so the result takes frm_zero of the entry state.
   Statements cited, none copied: lane CwSites' tail_at_pinv_B / drv_pre_cf / drv_minv_cf (lib/AU/PresetD1sitesB.v),
   lane CwPreB's malloc_site_tfa_cf / memcpy_site_tfa_cf (lib/AU/PresetD1preB.v), lane CwLoopB's loop_L_cf_B
   (lib/AU/PresetD1rB.v) and its lemmas over ARcf (lib/AU/PresetD1rBx.v), lane CwPinvB's PINV frame theorems.
   The allocator parameters are preset's, CfParams_preset (lib/A/CfParamsPreset.v), as in the loop. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0k YG0f YG0v YG0n YG0d YCe5.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB12 YF0l YB1h YB13 YF0m YD2j YD2i YD1t YD20.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD2n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD1v YD1y YD26 YD24.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD21 YD25 YD23 YD2h YD1w YD2f YD2b YD2g YD1s YD2c YD2d YD29.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD2e.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfRoomPre YGcfApath.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomKeep YGcfPath YGcfXs YG0lawscf YK0o.
(* The run-level room is a Theorem Labs lane's P8 (a working branch 4ec915e66b6, lib/Spec/PresetP8.v): the state
   predicate room_at, not a sum over calls. a8's view of an astate (room_of_cf, q_fifo) is YGcfRoom.v, its free
   coupling YGcfFrees.v (a working branch 5d91379f2041); the model's run (hruns, hlive, hfrees) is
   lib/Spec. Names used qualified. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfFrees.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PresetRun PresetReqAt PresetRoomPos.
From Stdlib Require Import Sorting.Permutation.
(* The owners' statements and lemmas (a Theorem Labs lane's one-writer table). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD1sitesB PresetD1preB PresetD1rBx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetD1rB PresetPinvB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
(* Required, not imported: PresetCfnB defines A_LLVMF / RA_LLVMF / A_EMPTY / LIVE_LIB / LLVMF_STK at preset's values,
   which would shadow the driver's names; its names are written qualified. *)
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetCfnB.
Module PCB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetCfnB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallStackUp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 0. The run-level room, in P8's form (a Theorem Labs lane with two Theorem Labs lanes / IfacePort, 2026-10-29).
   The old run premise ROOM_cf_k S (4 * N_LLVMF + 3) is UNSATISFIABLE - K_INIT is 14,335 allocator steps and one
   harness call takes at least 9,696 (a Theorem Labs lane's note, the internal file n-llvmf.md) - so every headroom number
   of the RUN layer is deleted, here and in the statements this file consumes. A run of any length is carried
   instead by a Theorem Labs lane's P8 (a working branch 4ec915e66b6, lib/Spec/PresetP8.v preset_room): a
   PREDICATE ON THE STATE, which P8 turns into `room_at s c` at every consumer allocation.
   RUNQM's share of it (a Theorem Labs lane's division of 2026-10-29 04:5xZ) is the DRIVER LEAF: before the first harness
   call the model has run nothing, so P8's live premise is just `the state's own blocks are at most three`, and
   its free-history premise is read off the quarantine itself - no free has happened yet, so the accounted
   history IS the quarantine, in order. iface_room_at_driver below is that reading, PROVED; IfacePort's
   iface_room_at_entry turns it into room_at at each consumer allocation.
   The instance's one-call premise ROOM_cf (YGcfRoomPre.v) is unchanged; the interface's non-primary room
   iface_room_np gives it at every driver state (iface_room_np_tail, ROOM_cf_k S 2), and survives each driver
   allocator step (iface_room_np_step). No ROOM_cf_k number appears in any statement of this file. *)
Section R0.
Context {ci : CfImg} {cp : CfParams}.

(* The quarantine's two queues in the two orders: q_fifo walks the global batches then the thread's (a8's
   YGcfRoom.v:57), q_items the thread's then the global ones (YG01.v:209). Same members. *)
Lemma q_fifo_in_items : forall S k, In k (YGcfRoom.q_fifo S) -> In k (q_items S).
Proof.
intros S k. unfold YGcfRoom.q_fifo, q_items, all_batches. rewrite !flat_map_app.
intros H. apply in_app_or in H. apply in_or_app. tauto.
Qed.

(* Every chunk the quarantine holds is a chunk of the state, so its request is non-negative: a8's cf_hist_ok of
   the quarantine itself, from Wf_cf alone. This is what lets a driver leaf read its free history off the state
   instead of carrying it from the start. *)
Lemma hist_ok_of_wf : forall U S, Wf_cf U S -> YGcfFrees.cf_hist_ok (YGcfRoom.q_fifo S).
Proof.
intros U S W. apply Forall_forall. intros k Hk.
pose proof (wfc_quarantine _ _ _ _ _ W) as Q.
pose proof (proj1 (Forall_forall _ _) (wq_items _ Q) k (q_fifo_in_items S k Hk)) as HI.
exact (YGcfRoom.chunk_ok_cf_req S k
(proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ W) k (proj1 HI))).
Qed.

(* THE DRIVER LEAF, PROVED, not assumed: at a state the driver reached before the first harness call, the
   interface's P8 premise holds outright. With os = [] the model has run nothing - PresetRun.hruns sm x [] is []
   and so are PresetReqAt.hlive of it and PresetRun.hfrees of it - so P8's live premise is satisfied by the
   state's OWN blocks (at most three: the read buffer, the payload copy and one more), and its free history is
   the quarantine itself, with H0 its requests and no model free in the window.
   This is what a Theorem Labs lane assigned to RUNQM on 2026-10-29 04:5xZ; IfacePort's iface_room_at_entry turns it into
   room_at at each consumer allocation, and nothing here depends on the payload x.
   COUNT (A15, 2026-10-30): iface_room_at's count conjunct at os = [] is the
   driver's own base, so the leaf takes it as its one new premise PresetRoomPos.rp_base S (under the closed
   YGcfSecsStep.secs_steps_cf: nsec_cf S <= rp_NB = 64 and sec_T_cf S <= rp_TB = 2 ^ 30); A18's base (lane
   CountDrvB) supplies it at the loop entry from the driver's state invariant. *)
Lemma iface_room_at_driver : forall (sm : list Z -> Z * Z) (x : list Z) U S,
Wf_cf U S -> qtight S -> (length (blocks S) <= 3)%nat -> PresetRoomPos.rp_base S ->
exists os H0 hist, length os = 0%nat /\ PCB.iface_room_at sm x os H0 hist S.
Proof.
intros sm x U S HW HQ Hbl HB.
assert (Hml : forall (l : list (sptr * Z)), length (map snd l) = length l)
by (induction l as [|y t IH]; cbn [map length]; lia).
exists [], (map ck_req (YGcfRoom.q_fifo S)), (YGcfRoom.q_fifo S). split; [reflexivity|].
split; [|split; [exact HQ | split; [exists []; reflexivity |
split; [exact (hist_ok_of_wf U S HW) | split; [unfold YGcfFrees.cf_frees_follow |
  exact (PresetRoomPos.rp_count_of_base S HB)]]]]].
- exists (map snd (blocks S)). split; [rewrite Hml; exact Hbl|].
  cbn [PresetRoom.rs_live YGcfRoom.room_of_cf PresetReqAt.hlive PresetReqAt.hlive_from
       PresetRun.hruns concat map fold_left app].
  apply Permutation_refl.
- cbn [PresetRun.hfrees PresetRun.hruns concat map flat_map]. rewrite app_nil_r. reflexivity.
Qed.

End R0.

(* ---------------------------------------------------------------------- *)
(* 1. The leaf type: the donor's run_QM_tfa (YD2d.v:72-80) over CwSites' tail_at_pinv_B, with `NR inp ->` after
      valid_fs. Lane CwRunqA's run_Q result cites it. *)
Section s.
(* Every class argument is a Context variable; lib_shape is passed by name (run_shape's LS): this tree loads
   #[global] lib_shape instances of other builds. *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {ci : CfImg} {cp : CfParams}.
#[local] Notation ELV sp a0 p inp xw xd := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).
(* N_LLVMF is GONE from this layer: the interface's per-call step count went with the sum form of the room
   (2026-10-29). CwSites' tail_at_pinv_B takes B as its first explicit argument.
   NP is the interface's non-primary room: the Section Variable iface_room_np of lib/AU/PresetCfnB.v
   (a working branch 3f83c075b61f), whose body will be a Theorem Labs lane's room_live_cf
   (lib/A/CfRoomLivePreset.v, in progress). It is what a driver state carries in place of every deleted
   headroom number; its laws are the interface's own iface_room_np_tail / iface_room_np_step, taken as
   premises of runqm_cf_B. Section order B, NP, NR, as in CwSites' tail_at_pinv_B and CwPreB's sites. *)
Variable B : asyms.
Variable NP : astate -> Prop.
Variable NR : ProcInput -> Prop.

Definition run_QM_tfa_cf : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr) (cap : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
NR inp ->
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data -> 0 < payload_len data ->
let E3 := E_P (edset (havoc (ELV sp a0 p inp xw xd) K_M1 ws) 2 data) data (sptr_addr B ly pb + 2 + config_len data) in
tail_at_pinv_B B NP (if config_len data =? 0 then sPM0 else sPM1 (Z.of_nat (calls data))) E3 sp inp a0 p data W ms md ly S pb cap ->
(* #102 (lane StackDrv): the live real stack above the entry sp, carried from main to the loop head *)
YGcallStackUp.astack_up_x tfibsegs ly W (bv_unsigned sp) (ms_mem ms) ->
bv_unsigned (ew E3 K_PP) = sptr_addr B ly pb + 2 + config_len data ->
srealizes tfibsegs (mkCfg ms md) (run_shape (LS := LS) (payload data) (calls data) (in_fs inp)).
End s.

(* ---------------------------------------------------------------------- *)
(* 2. This lane's statement: RUNQM (the donor's tfib_run_QM, YD2e.v:651), closed. The loop it enters is CwLoopB's,
      stated at CfParams_preset for every float state with a zero rounding mode; so RUNQM is stated there. *)
#[local] Existing Instance CfParamsPreset.CfParams_preset.
Definition runqm_cf_B : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (LS : lib_shape) (ci : CfImg) (B : asyms)
(NR : ProcInput -> Prop) (xst : nat -> (word -> bool) -> (word -> option byte) -> Prop)
(NP : astate -> Prop) (sm : list Z -> Z * Z),
(* the interface's own laws for NP (lib/AU/PresetCfnB.v section 3b): the non-primary room gives one call's
   headroom, and it survives one allocator step of the driver. Their bodies come from a Theorem Labs lane. *)
PCB.iface_room_np_tail NP -> PCB.iface_room_np_step NP ->
(* lane CwPinvB's three PINV frame results, by statement (lib/AU/PresetPinvB.v) *)
PresetPinvB.finv_run_pinv_B -> PresetPinvB.finv_site_pinv_B -> PresetPinvB.finv_icpt_pinv_B ->
YK0o.frm_zero (@YK11.fp_csr fx) -> TfibSyms B ->
malloc_site_tfa_cf B NP -> memcpy_site_tfa_cf B ->
PresetD1rB.loop_L_cf_B (LS := LS) B xst NR sm NP ->
(* the instance universe's wild room covers the loop's four calls (true by conversion at TfibB) *)
(4 * YCbqGwild.K_LLVMF <= u_wmax (as_universe B))%nat ->
run_QM_tfa_cf (LS := LS) B NP NR.
