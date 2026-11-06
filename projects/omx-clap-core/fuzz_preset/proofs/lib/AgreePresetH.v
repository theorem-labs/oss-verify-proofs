From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Statements Images.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  Agree AgreeTop AgreeLim SlotPack FrameSlotP Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require FrameProof.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger LLVMFuzzerTestOneInput_c Statement SlotGI
  PackSlot EntrySR LinkPlain.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require AgreePack AgreeZlib SlotAgreeV FrameAPI ZAllocator
  Contract SlotPack.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require YH02 YI5b YI5c YL0s YL0g.
Import ListNotations.
Open Scope Z_scope.

(* fuzz_preset's ubsan_agrees without the plain cut-free slot and without a 2^39 law (as fuzz_state's close):
   - plain run: the plain HALTS pack slot (lib_contract_pg) gives rz_run through RI_P (lib_contract_x_R_all_of_p,
     driver_RI_P), and the statement's own plain budget hypothesis is the plain budget (AgreeTop.ubsan_agrees_of_cut_free);
   - ubsan run: the ubsan cut-free pack slot at the 2^34 law (U.AgreePack.ubsan_crealizes_of_cgpg at LIM := SRC_LIM_MIN,
     the law being U.AgreeZlib.zlib_limit). *)

Theorem ubsan_agrees_of_halts_pg34 : forall (LS : lib_shape) (CS CSu : list byte -> list Z)
    (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop)
    (Gu : list (Z * Z)) (GIu : nat -> (word -> option byte) -> Prop),
  CS_ok CS ->
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_pg fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink CS G frame_RELRO GI j
       ENTRY RA_LIB EMPTY SLOT_STACK) ->
  U.SlotPack.CS_ok CSu ->
  (forall a, U.Reusable.YL0g.in_globals Gu a -> U.Reusable.YL0g.in_globals U.FrameAPI.frame_G a) ->
  U.Contract.G_local_c U.Reusable.YH02.src0_msyms Gu GIu ->
  (forall mem, U.Contract.G_img_c U.Reusable.YH02.src0_msyms Gu mem -> GIu 0%nat mem) ->
  (forall (rc : RunCeil), limlaw_at SRC_LIM_MIN U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc) ->
     forall (fx : FPState) (j : nat), (j < 4)%nat ->
     @U.SlotAgreeV.lib_contract_cgpg fx rc LS U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API rc)
       U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink
       CSu Gu U.FrameAPI.frame_RELRO GIu j U.FrameAPI.ENTRY U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY
       U.FrameAPI.SLOT_STACK) ->
  Statements.ubsan_agrees.
Proof.
  intros LS CS CSu G GI Gu GIu HCS HG GIL GI0 Hp HCSu HGu GILu GI0u Hu.
  assert (HUB : forall en inp, valid_entry Images.ubsan en inp -> valid_input inp ->
    rz_run Images.ubsan Budgets.Standard.lim_target en inp (SPECX (LS:=LS) inp) /\
    cf_run Images.ubsan Budgets.Standard.lim_target en inp).
  { intros en inp Hs Hin.
    exact (U.AgreePack.ubsan_crealizes_of_cgpg SRC_LIM_MIN LS CSu Gu GIu HCSu
      (fun rc => U.AgreeZlib.zlib_limit rc) HGu GILu GI0u Hu en inp Budgets.Standard.lim_target Hs Hin
      ltac:(apply Z.leb_le; vm_compute; reflexivity)). }
  apply (ubsan_agrees_of_cut_free LS (RI_P CS) G frame_RELRO (fun j T m => T = [] /\ GI j m) (fun _ => [])
    (driver_RI_P CS HCS) (fun a h => frame_G_src0 a (HG a h)) frame_RELRO_src0
    (G_local_T_of_G src0segs G GI GIL) (fun mem Hm => conj eq_refl (GI0 mem Hm))).
  - intros rc. exists (@zlib_API rc). split; [exact zlib_allocator_extra|].
    apply (lib_contract_x_R_all_of_p src0_msyms (@zlib_API rc) (zlib_tables rc) CS G frame_RELRO _ _ _ _ _ HCS).
    intros fx j Hj.
    exact (lib_contract_p_of_pg src0_msyms (@zlib_API rc) CS G frame_RELRO GI j _ _ _ _ (Hp rc fx j Hj)).
  - intros en inp Hs Hin. exact (proj1 (HUB en inp Hs Hin)).
  - intros en inp Hs Hin. exact (proj2 (HUB en inp Hs Hin)).
Qed.

(* The plain halts slot of fuzz_preset at the frame's allocator (src0_msyms, zlib_API), from the proved slot contract
   (Prog.PackSlot.slot_contract_of_entry over Prog.LinkPlain.lp_entry_sr). The three slot premises are those of
   h-hpreset's Prog/CF/PackSlotCf.v (psc_syms, psc_globals, psc_sinks). *)
Lemma ph_syms : Prog.LLVMFuzzerTestOneInput_c.slot_syms src0_msyms.
Proof. unfold Prog.LLVMFuzzerTestOneInput_c.slot_syms. repeat (split; [reflexivity|]). reflexivity. Qed.

Lemma ph_globals : Prog.LLVMFuzzerTestOneInput_c.slot_globals src0_msyms.
Proof. intros a Ha. exact (FrameProof.frame_G_facts a (Prog.Statement.slot_G_frame a Ha)). Qed.

(* #102: the numerals below are FrameAPI.frame_facts_plain's (rw102-ent bfd74483ce6c), each checked against the
   relocated src0_msyms / src0_sink by reflexivity; the frame's globals are LedgerCells.GL_runs, by name. *)
Lemma ph_sinks : @Prog.LLVMFuzzerTestOneInput_c.slot_sinks src0_msyms src0_sink_head src0_sink.
Proof.
  assert (HS : ms_segs src0_msyms = rsegs) by reflexivity.
  assert (Hne : ms_segs src0_msyms <> []).
  { (* frame_G's first run (LedgerCells.GL_runs), taken from the list itself: no cell name or numeral restated here *)
    assert (H0 : in_globals frame_G (fst (hd (0, 0) frame_G)))
      by (exists (fst (hd (0, 0) frame_G)), (snd (hd (0, 0) frame_G)); unfold frame_G; cbn; split; [left; reflexivity | lia]).
    exact (proj1 (proj1 (FrameProof.frame_G_facts _ H0))). }
  assert (Hoh : @sk_ofl_head src0_sink_head = 0x54f58) by reflexivity.
  assert (Hol : @sk_ofl_lock src0_sink = 0x54f50) by reflexivity.
  assert (Hth : @sk_threaded src0_sink = 0x54b28 + 1) by reflexivity.
  assert (Hg : ms_guard src0_msyms = 0x54b08) by reflexivity.
  assert (Hgg : ms_got_guard src0_msyms = 0x234e0) by reflexivity.
  assert (Hctx : ms_ctx src0_msyms = 0x54ba0) by reflexivity.
  assert (Hlk : ms_lock src0_msyms = 0x54b98) by reflexivity.
  assert (Hlc : ms_libc src0_msyms = 0x54b28) by reflexivity.
  assert (Hsc : ms_size_classes src0_msyms = 0x10570) by reflexivity.
  assert (Hsm : ms_small_cnt src0_msyms = 0x105d0) by reflexivity.
  assert (Hmd : ms_med_cnt src0_msyms = 0x105eb) by reflexivity.
  assert (Hdb : ms_debruijn src0_msyms = 0x10550) by reflexivity.
  assert (Htp : ms_tp src0_msyms = 0x34898) by reflexivity.
  assert (Heo : ms_errno_off src0_msyms = -164) by reflexivity.
  assert (Hvl : ms_vmlock src0_msyms = None) by reflexivity.
  assert (Hdl : ms_debruijn_len src0_msyms = 32) by reflexivity.
  intros a Ha. unfold Prog.LLVMFuzzerTestOneInput_c.slot_sink_cell in Ha. rewrite Hoh, Hol, Hth in Ha.
  unfold Prog.LLVMFuzzerTestOneInput_c.slot_apart, errno_addr. rewrite Hctx, Htp, Heo.
  split; [split; [|split; [|split]]|].
  - apply Prog.Statement.slot_img_data; [exact HS | exact Hne | lia].
  - unfold static_owned, vml_lo, vml_len. rewrite Hlk, Hlc, Hgg, Hg, Hdb, Hsc, Hsm, Hmd, Hvl, Hdl. cbv iota. lia.
  - unfold CTX_SIZE. lia.
  - lia.
  - intros (lo & len & Hin & Hl).
    unfold Prog.LLVMFuzzerTestOneInput_c.slot_G, lib.Prog.LedgerCells.GL_runs in Hin. cbn [In] in Hin.
    (* full path: lib.U.Prog.LedgerCells is loaded too, and the short `Prog.LedgerCells` does not name the plain one here *)
    destruct Hin as [E|[E|[]]]; injection E as E1 E2; subst lo len;
      unfold lib.Prog.LedgerCells.GL_FAIL, lib.Prog.LedgerCells.GL_OWN_RAN_OUT in Hl; lia.
Qed.

Lemma preset_plain_halts_slot : exists CS, CS_ok CS /\
  forall (rc : RunCeil) (fx : FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_pg fx rc checksum_shape src0_msyms (@zlib_API rc) src0_sink_head src0_sink CS
      Prog.LLVMFuzzerTestOneInput_c.slot_G frame_RELRO (Prog.Ledger.omx_GI src0_msyms) j ENTRY RA_LIB EMPTY SLOT_STACK.
Proof.
  assert (HE : forall (rc : RunCeil) (fx : FPState) (B : malloc_syms) (API : AllocAPI B) (SH : sink_head)
      (SK : sink_syms) (ra empty stk : Z),
      (forall fx' : FPState, @frame_allocator rc fx' B API) ->
      @Prog.EntrySR.entry_sr_contract fx rc B API SH SK pack_form ra empty stk).
  { intros rc fx B API SH SK ra empty stk FA.
    unfold Prog.EntrySR.entry_sr_contract. intros HS HG.
    pose proof (Prog.LinkPlain.lp_entry_sr (rc := rc) (fx := fx) (SH := SH) (SK := SK) B API HS HG FA ra empty stk) as H.
    unfold Prog.EntrySR.entry_sr_contract in H.
    exact (H HS HG). }
  destruct (Prog.PackSlot.slot_contract_of_entry HE) as (CS & HCS & HC).
  exists CS. split; [exact HCS|].
  intros rc fx j Hj.
  apply (HC rc fx checksum_shape src0_msyms (@zlib_API rc) src0_sink_head src0_sink RA_LIB EMPTY SLOT_STACK
    ph_syms ph_globals ph_sinks (FrameProof.zlib_frame_allocator rc)).
  - split; [intros pl fs K; reflexivity | intros n b; reflexivity].
  - vm_compute. reflexivity.
  - reflexivity.
  - split; apply Z.ltb_lt; vm_compute; reflexivity.
  - apply Z.leb_le. vm_compute. reflexivity.
  - exact Hj.
Qed.
