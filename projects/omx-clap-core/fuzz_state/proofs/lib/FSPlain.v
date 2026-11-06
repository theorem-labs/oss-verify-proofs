(* fuzz_state's plain side, closed: every run of fs.plain from a valid entry on a valid input, at the 16 GiB budget,
   realizes SPECX at ag_shape checksum_shape (cuts allowed). It is the plain realization that fs's released
   ubsan_agrees proof builds, assembled here from the same released, proved terms, used unchanged:
   - fs_plain_slot: lib/AgreeState.v:30-53 state_plain_slot (the plain slot contract lib_contract_g at
     ag_shape checksum_shape, from Prog/AG/LinkAg.v:36 slot_premise_plain_ag_holds, the frame facts of
     lib/FrameProof.v and lib/SlotTopG.v), restated because AgreeState.v also imports lib/U and lib/U/Prog/CF;
   - SBD_AG / driver_slots_AG / driver_RI_AG: lib/AgreeZlib.v:63-83, unchanged (byte-identical lines), copied as
     FsPlainSide.md section 3 measured: lib/AgreeFrame.v requires lib/AgreeZlib.v only for these, and the file's
     other requirements (lib/AllocCf.v, lib/AgreeWalk.v, 137 `_cf` / `_cfw` files) are not on the plain side;
   - fs_plain_rz: the HC construction of lib/AgreeFrame.v:37-45 (ubsan_agrees_of_slots) and its call of
     lib/AgreeTop.v:16 plain_rz_of_contracts_R (AgreeFrame.v:52-54), with driver_RI_AG over
     AgreeShape.ag_room_calls, omx_G_inside / omx_GI_local (Prog/StatementHalts.v:40, :51) and omx_GI_init
     (Prog/GIInit.v:20), as lib/AgreeState.v:93-99 instantiates them.
   Template: proofs/libreac/fuzz_grant/lib/A/AsanTop.v:29-89 grant_plain_rz (a working branch c2edc13c0fa).
   lead ruling 20:34Z: released slot-named plain-chain files used unchanged, each premise- and byte-checked by a Theorem Labs lane
   Imports: fs's plain lib only (no file of lib/U, no CF / _cf / _cfw / W6 file is named here). One transitive
   exception: lib/AgreeShape.v (ag_shape, ag_room_calls) requires lib/U/AgreeZlib.v for SBD_AG, a released, proved
   file of fs's ubsan chain, and with it 443 released lib/U files and the released `_cf` / `_cfw`-named files they
   require (lib/U/Reusable/*_cf.v, *_cfw.v and lib/Reusable/YM06_cf.v, YO03_cf.v, YO04_cfw.v, YO0d_cf.v, YO0j_cf.v,
   YO0l_cf.v, YO0m_cf.v, YO0n_cf.v). Without that one edge the closure holds 796 other files and no lib/U, CF, _cf
   or _cfw file.
   Every file of the closure except this one is in c8557374ad2e (none is an open lane's file) and in the closure of
   fs's released ubsan_agrees/Proof.v.
   The plain closure is fs's own: lib/Reusable/YH02.v:20-24 has ms_realloc = Some src0_A_realloc and
   mremap = Some src0_A_mremap, and Prog/AG/StatementHaltsAg.v:18 fixes ms_realloc B = Some 0x17e00; no file of
   the raw cgif_file copy (d579ce160e2) is in this closure. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_state Require Statements Images.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  Agree AgreeTop AgreeCap AgreeLim AgreeShape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require FrameProof SlotTopG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger GIInit LLVMFuzzerTestOneInput_c
  StatementHalts AG.StatementHaltsAg AG.LinkAg.
Import ListNotations.
Open Scope Z_scope.

(* lib/AgreeState.v:30-53 state_plain_slot, unchanged. *)
Lemma fs_plain_slot : forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
  @lib_contract_g fx rc (ag_shape checksum_shape) src0_msyms (@zlib_API rc) src0_sink_head src0_sink
    omx_G frame_RELRO (omx_GI src0_msyms) j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  intros rc fx j Hj.
  assert (FF : frame_facts_plain_ag src0_msyms (@zlib_API) (ag_shape checksum_shape) src0_sink_head src0_sink EMPTY).
  { unfold frame_facts_plain_ag.
    split; [exact lib.SlotTopG.ms_segs_rsegs|].
    do 4 (split; [reflexivity|]).
    split; [exact lib.FrameProof.errno_below_ceiling|].
    do 14 (split; [reflexivity|]).
    do 3 (split; [reflexivity|]).
    split; [reflexivity|].
    split; [split; vm_compute; reflexivity|].
    split; [exact lib.FrameProof.ctx_not_ro|].
    split; [exact lib.FrameProof.frame_G_facts|].
    split; [exact lib.FrameProof.frame_RELRO_facts|].
    split; [intros pl fs K; reflexivity|].
    split; [intros n b; reflexivity|].
    split; [intros b n H; exact H|].
    exact lib.FrameProof.zlib_frame_allocator. }
  exact (slot_premise_plain_ag_holds src0_msyms (@zlib_API) (ag_shape checksum_shape) src0_sink_head src0_sink EMPTY
    FF rc fx j RA_LIB Hj ltac:(vm_compute; reflexivity)).
Qed.

(* lib/AgreeZlib.v:63-83, unchanged. *)
Definition SBD_AG : sbound := SB 2 (2 ^ 28) CAP_AG.

Lemma driver_slots_AG data : leaves (run_slots SBD_AG) (driver_tree data).
Proof.
  eapply leaves_mono; [| exact (leaves_and _ _ _ (driver_res data) (driver_inv data))].
  intros [d s] [HR HI]. unfold run_slots, drv_inv in *. cbn [fst snd] in *.
  destruct d; try exact I. destruct HI as ((HW & HS & HG & HN & HNR & HM) & Hnb & Hub).
  destruct HR as (HII & _ & _ & Hh & _).
  unfold res_ok_slots, SBD_AG, HCAP, CAP_AG, DRB in *. cbn [sb_live sb_bytes sb_cap rb_hand] in *.
  repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
Qed.

Lemma driver_RI_AG : forall (LS : lib_shape), (forall data, @room_calls LS (payload_len data) (calls data) SBD_AG) ->
  forall data, leaves (run_RI (@RI_G LS) (payload data)) (driver_tree data).
Proof.
  intros LS HROOM data. eapply leaves_mono; [| exact (driver_slots_AG data)].
  intros [d A] H. unfold run_slots, run_RI in *. cbn [fst snd] in *. destruct d; cbv beta iota in H |- *; try exact I.
  exists SBD_AG. split; [exact H|].
  destruct (calls_witness (Z.of_nat (length (YO06.payload data))) (Nat2Z.is_nonneg _)) as (d' & Hd1 & Hd2).
  pose proof (HROOM d') as Hr. rewrite Hd1, Hd2 in Hr. exact Hr.
Qed.

(* lib/AgreeFrame.v:36-55 at LS := ag_shape checksum_shape, G := omx_G, GI := omx_GI src0_msyms (the arguments
   lib/AgreeState.v:93-99 gives it), stopped at its plain_rz_of_contracts_R call. *)
Theorem fs_plain_rz : forall en inp, valid_entry Images.plain en inp -> valid_input inp ->
  rz_run Images.plain Budgets.Standard.lim_source en inp (SPECX (LS:=ag_shape checksum_shape) inp).
Proof.
  assert (HROOMp : forall data, @room_calls (ag_shape checksum_shape) (payload_len data) (calls data) SBD_AG)
    by (intros data; exact (ag_room_calls checksum_shape (payload_len data) (calls data))).
  assert (GI0 : forall mem, G_img_c src0_msyms omx_G mem -> omx_GI src0_msyms 0%nat mem).
  { intros mem HI. apply omx_GI_init; [exact lib.SlotTopG.ms_segs_rsegs | exact HI]. }
  assert (HC : zlib_runtime_contracts_R (ag_shape checksum_shape) (@RI_G (ag_shape checksum_shape)) omx_G frame_RELRO
    (fun j T m => T = [] /\ omx_GI src0_msyms j m) (fun _ => [])).
  { intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
    apply (lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) (@RI_G (ag_shape checksum_shape)) omx_G frame_RELRO _
      (fun _ => []) LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step (ag_shape checksum_shape) (omx_GI src0_msyms))).
    intros fx j Hj.
    exact (lib_contract_x_T_of_G src0_msyms (@zlib_API rc) omx_G frame_RELRO (omx_GI src0_msyms) (fun _ => []) j
      LIBPC RA_LIB EMPTY LIB_STACK
      (lib_contract_x_G_of_g src0_msyms (@zlib_API rc) (zlib_tables rc) omx_G frame_RELRO (omx_GI src0_msyms) j
        LIBPC RA_LIB EMPTY LIB_STACK (fs_plain_slot rc fx j Hj))). }
  exact (plain_rz_of_contracts_R (ag_shape checksum_shape) (@RI_G (ag_shape checksum_shape)) omx_G frame_RELRO
    (fun j T m => T = [] /\ omx_GI src0_msyms j m) (fun _ => [])
    (driver_RI_AG (ag_shape checksum_shape) HROOMp) (fun a h => frame_G_src0 a (omx_G_inside a h)) frame_RELRO_src0
    (G_local_T_of_G src0segs omx_G (omx_GI src0_msyms) (omx_GI_local src0_msyms))
    (fun mem H => conj eq_refl (GI0 mem H)) HC).
Qed.
