(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YD1q.v (tfib_srealizesX),
   lib/YB1n.v (tfib_startup_T1, HS_ok) and lib/YD2o.v (TFIB_TB_of_partsXF), in the form of fuzz_pcap's closing side
   (proofs/libreac/fuzz_pcap/lib/A/PcapClose.v, a working branch 86b0e893fe8), for libreac/fuzz_decode's
   ASan+UBSan image: one named Section hypothesis per remaining part, module paths and names changed. *)
(* The closing side of fuzz_decode's two ASan+UBSan statements (rule 24: no function proved; this file is assembly).

   TFIB_TB (lib/A/DecodeTFIB.v:28) is closed in the donor's two steps: cgif_file_fuzzer's lib/YD1q.v:79-98
   tfib_srealizesX joins the start-up certificate (lib/YB1n.v:52 tfib_startup_T1) and the driver's closed walk
   (lib/YD1q.v:77-78 DRV_MAINX, from lib/YD1p.v:84 tfib_drv_main) over the program contract
   (lib/YCfn.v:71 tfib_lib_contract_x_all, closed by lib/YCfi.v:139 tfib_lib_x_all) and the runtime walks.
   Every part is PROVED (step 5b): the parts proved on their lanes are applied as Lemmas, each of the name and
   statement of the Section Hypothesis it replaced, and carries the donor line it stands for and the lane that
   supplied it (proofs/libreac/fuzz_decode/provenance/OBLIGATIONS.md has the same rows with their status). No Section
   Variable or Hypothesis remains. From TFIB_TB, lib/A/AsanTop.v gives Statements.asan_ubsan_agrees and
   Statements.asan_ubsan_halts.

   Image B's relocated core (a working branch dfa268302f2, with a Theorem Labs lane's -decB files of
   7eb81ddb186) is on this unit, and every former Section variable is bound to its value (step 5b): B to lib/B/YD2l.v
   TfibB, HS_ok to lib/B/YB1n.v HS_ok, the sink names to the core's instance. The driver H_DRIVER concludes
   `srealizes segs c (SPECX inp)` at a hand-off state c, where the donor concludes CLOSEDX; the donor's own proof
   passes from one to the other in the two steps of YD1q.v:54-61 (HS_ok_open, YB1n.v:74, and specx_closedx_eq,
   Reusable/YO01.v), as lib/B/DecodeBDriver.v does.

   NO hypothesis here restates a top: TFIB_TB, Statements.asan_ubsan_agrees and Statements.asan_ubsan_halts occur only as the
   conclusions proved below. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_decode Require Statements.
From OSSVerify.libreac.fuzz_decode.images Require AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YM05 YK04 YA0i YA0n YG00 YG01 YG0f YG0n YG0d YG0q YCbq YC5d YGCalloc YCbp YCbpCalloc YI00 YO09
YO05 YO06.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeShape.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import DecodeCallocKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import
DecodeCalloc DecodeCallocRt DecodeCallocWrapB DecodeCallocEntryB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require DecodeCallocTopB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require AsanTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require DecodeBImg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LeafCgKit LLVMFuzzerTestOneInput_cg
check_round_trip_cg check_round_trip_cgpf reac_frame_is_reac_cg reac_frame_clean_len_cg reac_frame_counter_cg reac_frame_inspect_cg
reac_decode_cg reac_decode_plain_le_cg reac_upstream_channels_cg reac_upstream_decode_cg check_braid_cg
reac_braid_encode_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require reac_frame_clean_len_F reac_upstream_channels_F
reac_upstream_decode_F check_braid_F
reac_frame_is_reac_F_nosh reac_frame_counter_F_nosh reac_frame_inspect_F_nosh reac_decode_F_nosh
reac_decode_plain_le_F_nosh reac_braid_encode_F_nosh.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LLVMFuzzerTestOneInput_walk.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YE00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require PaBase.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require YD2l YB1n YCfn YCeg YE2k YE01.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require DecodeBStartupH DecodeBDriver DecodeBRtWalks
DecodeBRtMem DecodeBRtStackMalloc DecodeBCallocTp DecodeBPcs DecodeBCrtFacts DecodeBSinkRo DecodeBLaws
DecodeBAlloc DecodeBRows DecodeBRowsRt DecodeBRowsFill.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LeafCgClose.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Module YK11 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module YI16 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI16.
Module DSt := OSSVerify.libreac.fuzz_decode.Statements.
Module DAU := OSSVerify.libreac.fuzz_decode.images.AsanUbsan.
Module LK := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.LeafCgKit.
Module PL := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.LLVMFuzzerTestOneInput_cg.
Module PC := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.check_round_trip_cg.
Module PCpf := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.check_round_trip_cgpf.
Module PLW := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.LLVMFuzzerTestOneInput_walk.
Module DCTop := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.DecodeCallocTopB.
Module LIsReac := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_is_reac_cg.
Module LCleanLen := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_clean_len_cg.
Module LCounter := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_counter_cg.
Module LInspect := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_inspect_cg.
Module LDecode := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_decode_cg.
Module LPlainLe := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_decode_plain_le_cg.
Module LUpChannels := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_upstream_channels_cg.
Module LUpDecode := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_upstream_decode_cg.
Module LCheckBraid := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.check_braid_cg.
Module LBraid := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_braid_encode_cg.
Module FCleanLen := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_clean_len_F.
Module FUpChannels := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_upstream_channels_F.
Module FUpDecode := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_upstream_decode_F.
Module FCheckBraid := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.check_braid_F.
Module NIsReac := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_is_reac_F_nosh.
Module NCounter := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_counter_F_nosh.
Module NInspect := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_frame_inspect_F_nosh.
Module NDecode := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_decode_F_nosh.
Module NPlainLe := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_decode_plain_le_F_nosh.
Module NBraid := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_braid_encode_F_nosh.

(* Image B's relocated core's record and instances (a working branch dfa268302f2) and the
   step-5b row files that prove this file's former hypotheses at them. *)
Module YE00 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YE00.
Module PaBase := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.PaBase.
Module BD2l := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.YD2l.
Module BB1n := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.YB1n.
Module BCfn := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.YCfn.
Module BCeg := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.YCeg.
Module BE2k := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.YE2k.
Module BE01 := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.YE01.
Module DStart := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.DecodeBStartupH.
Module DDrv := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.DecodeBDriver.
Module DRtW := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.DecodeBRtWalks.
Module DRtM := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.DecodeBRtMem.
Module DRtS := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.DecodeBRtStackMalloc.
Module DTp := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.DecodeBCallocTp.
Module DPcs := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.DecodeBPcs.
Module DCrt := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.DecodeBCrtFacts.
Module DSink := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.DecodeBSinkRo.
Module DLaws := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.DecodeBLaws.
Module DAlloc := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.DecodeBAlloc.
Module DRows := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.DecodeBRows.
Module DRowsRt := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.DecodeBRowsRt.
Module DFill := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.DecodeBRowsFill.
Module DLeaf := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.LeafCgClose.

(* The plain build's six global sink instances are dropped from resolution by lib/A/DecodeCalloc.v
   (a working branch 92fd0236203), which this file imports: every ASan statement here names
   this image's own sink head dec_B_sink_head (musl's ofl_head of the image). *)

Local Notation segs := decodesegsB0.

(* SPECX holds of the empty trace, the `T []` premise of the start-up certificate (donor: Reusable/YO01.v:91
   CLOSEDX_has_nil, at SPECX instead of CLOSEDX). Every arm of SPECX_args (Reusable/YO06.v:30-39) is a t_emit. *)
Lemma specx_has_nil : forall inp, SPECX (LS:=decode_shape) inp [].
Proof.
  intros inp. unfold SPECX, SPECX_args.
  destruct (in_argv inp) as [|a0 [|p [|x r]]];
    try (unfold diag, wr; apply t_emit_has_nil).
  unfold t_alt2.
  destruct (classify_open p (in_fs inp));
    [unfold diag, wr; apply t_emit_has_nil | left; unfold diag, wr; apply t_emit_has_nil
    | left; unfold diag, wr; apply t_emit_has_nil].
Qed.

(* The stack-pointer window, from valid_sp (donor: fuzz_pcap lib/A/PcapClose.v:47 valid_sp_windowP). *)
Lemma valid_sp_windowD : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; [exact H1 | exact H2]. Qed.

Section asan_ubsan.

(* ===================================================================================================== *)
(* The image's data the parts are stated at. Owners in provenance/OBLIGATIONS.md.                         *)
(* ===================================================================================================== *)
(* Step 5b binds every Section variable of the earlier statement to image B's relocated core's value
   (a working branch dfa268302f2), as cgif's lib/YD2o.v:45-47 / :71 binds the donor's;
   none is free. The values are the ones the step-5b rows state their lemmas at. *)
(* B: the image's symbol and trace record, donor lib/YD2l.v:14 TfibB, bound to the core's lib/B/YD2l.v:12 TfibB
   (TfibB_ok :47, and TfibB_syms : TfibSyms TfibB at :68). *)
Local Notation B := BD2l.TfibB.
(* The meter and its bound, donor lib/YD1q.v:46 (MT XM_LIB XN_LIB), bound at lib/YD2o.v:45 to Reusable/YCbp.v:16
   ameter_triv and lib/YCfi.v:56 XL0 = fun _ => 0. Both are bound here as the donor binds them: MT to this unit's
   lib/Reusable/YCbp.v:17-18 ameter_triv (relocated from cgif's lib/YCbp.v), XL to lib/B/DecodeBLaws.v dec_XL0
   (fun _ => 0, row D-B-laws). *)
Local Notation MT := ameter_triv.
Local Notation XL := DLaws.dec_XL0.
(* The program's read-only range, donor lib/YD1q.v:46 (RLO RHI), bound at lib/YD2o.v:45 to cgif's 0x9da38 /
   0x9eca8, the second disjunct of cgif's in_ro_tfa. Bound here the same way: [0x98d88, 0x99ff8) is the second
   disjunct of the core's lib/B/YCeg.v:45-47 in_ro_tfa (the relro range), which gives the driver's premise RO_IN
   below; lib/B/DecodeBSinkRo.v states HB_RO_BELOW_OFL at the same pair. *)
Local Notation RLO := 0x98d88.
Local Notation RHI := 0x99ff8.
(* The sink's record, its vacuity and its invariants, in a Theorem Labs lane's sink form, as
   lib/B/Prog/LLVMFuzzerTestOneInput_cg.v takes them, bound to the core's instance: the record lib/B/YE2k.v tfib_K
   (type lib/Reusable/YE00.v asink_syms), Reusable/YE00.v asink_none, lib/B/YE01.v ameta_inv, arodata_okS and
   asink_img_laws at the image's sink head, and lib/A/Prog/PaBase.v:23 ro_below_ofl at the sink head: the instance
   lib/B/DecodeBDriver.v and lib/B/DecodeBSinkRo.v state their rows at. *)
Local Notation asink_syms := YE00.asink_syms.
Local Notation KS := BE2k.tfib_K.
Local Notation asink_none := YE00.asink_none.
Local Notation ameta_inv := BE01.ameta_inv.
Local Notation arodata_okS := BE01.arodata_okS.
Local Notation asink_img_laws := (@BE01.asink_img_laws dec_B_sink_head).
Local Notation ro_below_ofl := (fun s rlo rhi => @PaBase.ro_below_ofl s rlo rhi dec_B_sink_head).
(* The driver's two addresses, donor lib/YCfn.v:21-22 (Definitions), bound to the core's lib/B/YCfn.v:24-25
   RA_LLVMF = 0x7ffac and A_EMPTY = 0x5d39a0. *)
Local Notation RA_LLVMF := BCfn.RA_LLVMF.
Local Notation A_EMPTY := BCfn.A_EMPTY.
(* HS_ok: the start-up's hand-off states, bound to the core's lib/B/YB1n.v:45 HS_ok (donor lib/YB1n.v:44-51; its
   body is cs_ok at lib/B/YB01.v HS_tfib and lib/B/YB12.v TFIB). *)
Local Notation HS_ok := BB1n.HS_ok.

(* ===================================================================================================== *)
(* 1. The start-up certificate                                                                            *)
(* ===================================================================================================== *)
(* H_STARTUP: donor lib/YB1n.v:52-72 tfib_startup_T1, at HS_ok and fuzz_decode's ASan+UBSan image; the donor's
   YA02.LIMIT is target_alloc_limit (Reusable/YA02.v:19) and the donor's YA02.inp is its body
   (mkProcInput_full ... false Sv48 ...). PROVED as lib/B/DecodeBStartupH.v:41 dec_H_STARTUP (the core's
   lib/B/YB1n.v tfib_startup_T1 at these names; a Theorem Labs lane, -decB 7eb81ddb186 via -coreB dfa268302f2), applied
   unchanged. *)
Lemma H_STARTUP :
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs)
    (stdin : InputStream) (uid gid : word) (groups : list word) (net : NetQueue) (nofile sigmask hw : word)
    (urnd : InputStream) (tmp : Fs.Fs),
  valid_sp sp -> valid_brk segs brk0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  valid_id uid -> valid_hwcap hw ->
  forall T : TSet, T [] ->
  (forall h c, HS_ok h sp rdraw brk0 argv envp uid hw (fs_seed_tmp fs tmp) c -> srealizes segs c T) ->
  srealizes segs (init_config segs DAU.M.init_pc DAU.M.phdrs sp brk0 mbase rdraw target_alloc_limit
    (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp)) T.
Proof. exact DStart.dec_H_STARTUP. Qed.

(* ===================================================================================================== *)
(* 2. The relocated core's closed walk (the driver)                                                       *)
(* ===================================================================================================== *)
(* RO_IN: the driver's read-only premise (donor lib/YD2o.v:47 `fun a H => or_intror H`): [RLO, RHI) is the second
   disjunct of the core's lib/B/YCeg.v:45-47 in_ro_tfa. *)
Lemma RO_IN : forall a, RLO <= a < RHI -> BCeg.in_ro_tfa a.
Proof. intros a H. right. exact H. Qed.
(* H_DRIVER: donor lib/YD1p.v:84 tfib_drv_main, as lib/YD1q.v:64-78 states it (drv_mainX_stmt / DRV_MAINX),
   composed with lib/YB1n.v:74 HS_ok_open and Reusable/YO01.v specx_closedx_eq, so that its hand-off is HS_ok and its
   trace set is SPECX. PROVED as lib/B/DecodeBDriver.v:214 dec_H_DRIVER_TfibB (a working branch
   ba49323448a, over lib/B/DecodeBROPinned.v:129 dec_ro_owned_pinned), at its three left premises: dec_rom_no_errno
   TfibB (lib/B/DecodeBSinkRo.v:99 dec_HB_ROM_NO_ERRNO, the row HB_ROM_NO_ERRNO below), MT_FREE (mo_ok ameter_triv is
   True) and RO_IN above. The driver does not use universe_ok (as_universe B). The earlier premise arm_at_main rc and
   its Hypothesis H_ARM_AT_MAIN are DELETED: the driver does not use them (the core builds ARm at main itself,
   lib/B/YD1p.v tfib_AR), and H_DRIVER was their only consumer. *)
Lemma H_DRIVER : forall (rc : YM05.RunCeil),
  (forall fx : YK11.FPState, @amalloc_realizes fx rc segs B) ->
  (forall fx : YK11.FPState, @afree_realizes fx rc segs B) ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B))) ->
  @PL.dec_lib_contract_x_all rc decode_shape asink_syms KS asink_none ameta_inv arodata_okS
    RA_LLVMF A_EMPTY B MT XL XL RLO RHI ->
  universe_ok (as_universe B) ->
  forall (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput) (h : nat) (c : config),
  valid_sp sp -> valid_brk segs brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  @YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
  HS_ok h sp rdraw brk (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (in_fs inp) c ->
  srealizes segs c (SPECX (LS:=decode_shape) inp).
Proof.
  exact (fun rc AM AF AI LIB _ =>
    @DDrv.dec_H_DRIVER_TfibB MT XL RLO RHI rc DSink.dec_HB_ROM_NO_ERRNO (fun _ _ => I) RO_IN AM AF AI LIB).
Qed.

(* ===================================================================================================== *)
(* 3. The program walks (statement on a working branch, final e175e3e033a)                               *)
(* ===================================================================================================== *)
(* Both program walks of this image are PROVED and applied UNCHANGED here, so neither is a hypothesis.
   H_PROG_LLVMF keeps its name as a Lemma, whose statement is the hypothesis it replaces:
   lib/B/Prog/LLVMFuzzerTestOneInput_cg.v dec_llvmf_holds_stmt (cgif lib/YCfj.v:84-260 at fuzz_decode's callees,
   slot lib/YCfn.v:59-71), PROVED as lib/B/Prog/LLVMFuzzerTestOneInput_walk.v:33 dec_llvmf_holds
   (a working branch c4e3755d5a6, merged), with no premise beyond the statement's own. *)
Lemma H_PROG_LLVMF : forall (rc : YM05.RunCeil),
  @PL.dec_llvmf_holds_stmt rc asink_syms KS asink_none ameta_inv arodata_okS asink_img_laws ro_below_ofl
    RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
  intros rc.
  exact (@PLW.dec_llvmf_holds rc asink_syms KS asink_none ameta_inv arodata_okS asink_img_laws ro_below_ofl
    RA_LLVMF A_EMPTY B MT XL RLO RHI).
Qed.
(* check_round_trip's walk is PROVED for this image: lib/B/Prog/check_round_trip_cgpf.v:54
   dec_check_round_trip_cg_holds (a working branch beb498e78a3, the re-fit on the final
   statement e175e3e033a), with no premise beyond the statement's own; the composition applies it below
   (CRT_HOLDS), so it is not a hypothesis of this image. *)

(* ===================================================================================================== *)
(* 4. The runtime walks the program contract and the driver need                                          *)
(* ===================================================================================================== *)
(* Each refusal exit of these walks is placed at the error branch's TARGET, before the fatal trace, or the error
   block is proved unreachable; CheckFailed exits at its entry (a Theorem Labs lane R2 placement, 2026-10-29 00:27Z). *)
(* Every runtime walk of this section is PROVED at B := TfibB on a step-5b row and applied unchanged; each keeps its
   name as a Lemma whose statement is the hypothesis it replaces. *)
(* H_RT_MALLOC: donor lib/YF0w.v:44 tfib_amalloc_realizes. PROVED as lib/B/DecodeBRtWalks.v:42 dec_B_rt_malloc_at
   (the core's lib/B/YF0w.v at TfibB; a Theorem Labs lane 03981fe440b), at its premise as_dhash TfibB = tfib_dhash, true by
   definition (lib/B/YD2l.v:30). *)
Lemma H_RT_MALLOC : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @amalloc_realizes fx rc segs B.
Proof. exact (DRtW.dec_B_rt_malloc_at (fun _ => eq_refl)). Qed.
(* H_RT_FREE: donor lib/YF0q.v:12 afree_realizes_closed. PROVED as lib/B/DecodeBRtWalks.v:47 dec_B_rt_free_at. *)
Lemma H_RT_FREE : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @afree_realizes fx rc segs B.
Proof. exact (DRtW.dec_B_rt_free_at (fun _ => eq_refl)). Qed.
(* H_RT_MEMCPY_WRAP: the memcpy interceptor, donor lib/YD2m.v:16 tfib_AICPY (the driver's YD1q.v:45 AICPY). PROVED
   as lib/B/DecodeBRtMem.v:50 H_RT_MEMCPY_WRAP (a working branch d5d158b4f34). *)
Lemma H_RT_MEMCPY_WRAP : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (pc_wrap_memcpy (as_code B)).
Proof. exact DRtM.H_RT_MEMCPY_WRAP. Qed.
(* H_RT_ASAN_MEMSET / H_RT_ASAN_MEMCPY: donor lib/YCfi.v:92 link_AMEMSET (lib/YE2r.v:566 asan_memset_realizes)
   and lib/YCfi.v:97 link_AMEMCPY (lib/YE2q.v:143 asan_memcpy_realizes), at fuzz_decode's own entries. PROVED as
   lib/B/DecodeBRtMem.v:57 H_RT_ASAN_MEMSET and :67 H_RT_ASAN_MEMCPY. *)
Lemma H_RT_ASAN_MEMSET : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OSet (decodeb_sigma DB___asan_memset).
Proof. exact DRtM.H_RT_ASAN_MEMSET. Qed.
Lemma H_RT_ASAN_MEMCPY : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @aintrin_realizes fx rc segs B OCpy (decodeb_sigma DB___asan_memcpy).
Proof. exact DRtM.H_RT_ASAN_MEMCPY. Qed.
(* H_RT_BCMP: the bcmp interceptor (cgif's AsanAPI field aa_bcmp, Reusable/YG0d.v:353 abcmp_realizes). PROVED as
   lib/B/DecodeBRtMem.v:77 H_RT_BCMP. *)
Lemma H_RT_BCMP : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @abcmp_realizes fx rc segs B (decodeb_sigma DB___interceptor_trampoline_bcmp).
Proof. exact DRtM.H_RT_BCMP. Qed.
(* H_RT_STACK_MALLOC0: the class-0 side stack, a Theorem Labs lane's lib/A/Rt/StackMalloc0.v:513 stack_malloc0_contract
   (cgif's lib/YCfi.v:90 link_ASM2 is class 2; fuzz_decode calls class 0 once). PROVED as
   lib/B/DecodeBRtStackMalloc.v:35 dec_rt_stack_malloc0 (lib/B/Rt/StackMalloc0.v stack_malloc0_contract at TfibB;
   a working branch ce87b777d19). *)
Lemma H_RT_STACK_MALLOC0 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @astack_malloc_realizes fx rc segs B 0.
Proof. exact DRtS.dec_rt_stack_malloc0. Qed.
(* H_LINK_MALLOC04 / H_LINK_FREE04 are PROVED at MT = ameter_triv below (section 7b), from lib/Reusable/YCbp.v
   amalloc04_rule_triv / afree04_rule_triv; they are not hypotheses. *)

(* ===================================================================================================== *)
(* 5. The calloc walk over a Theorem Labs lane's AllocG (a working branch, lib/A/DecodeCalloc.v)               *)
(* ===================================================================================================== *)
(* Every calloc row of this section is PROVED at B := TfibB on image B's calloc tree of record
   (a working branch cf6a735494c, carrying a Theorem Labs lane b8678d241d2) and applied unchanged; each keeps its name
   as a Lemma whose statement is the hypothesis it replaces. *)
(* H_CALLOC_ALLOCATE: the Allocator::Allocate contract the calloc walk consumes, lib/A/DecodeCalloc.v
   decode_aalloc_B (Reusable/YGAlloc.v aalloc_realizes at DEC_B_allocate = 0x31298, AllocType FROM_MALLOC,
   can_fill = CF_CALLOC). The walk's size bound is DEC_CALLOC_MAX <= PRIM_MAX (Reusable/YGCalloc.v:144), proved by
   lib/A/DecodeCalloc.v DEC_CALLOC_MAX_prim: every request it covers is a primary one, so no secondary arm is needed.
   PROVED as lib/B/DecodeBAlloc.v:50 dec_b_aalloc_TfibB (a Theorem Labs lane's closed primary-size Allocate relocated onto image B,
   lib/B/AGtopcgifC.v, at TfibB). *)
Lemma H_CALLOC_ALLOCATE : forall (fx : YK11.FPState) (rc : YM05.RunCeil), @decode_aalloc_B fx rc B.
Proof. exact DAlloc.dec_b_aalloc_TfibB. Qed.
(* The premises of the calloc lane's CLOSED composition lib/A/DecodeCallocTopB.v decode_acalloc_of_allocate_B_holds:
   the thin caller walk over Allocate is no longer a hypothesis of this file, only these facts about the image are.
   H_CALLOC_IMG_COVER: PROVED as lib/B/DecodeBRows.v:60 dec_b_img_cover (the ledger covers the image, lib/B/YF0x.v
   img_cover_of_ledger). *)
Lemma H_CALLOC_IMG_COVER : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  forall ly S W regs mem md ch, acall_pre segs B ly S W regs mem md ch -> dec_img_cover ly.
Proof. exact (DRows.dec_b_img_cover B). Qed.
(* H_CALLOC_TP: PROVED as lib/B/DecodeBCallocTp.v:18 H_CALLOC_TP_TfibB (a working branch
   0c2b1b74143; ts_tp, TFIB_TP = DEC_B_TP). *)
Lemma H_CALLOC_TP : as_tp B = DEC_B_TP.
Proof. exact DTp.H_CALLOC_TP_TfibB. Qed.
(* H_CALLOC_INST: B's allocator instance is __asan::instance (DecodeCalloc.v DEC_B_instance = 0x9dcd8), the premise
   HINST of DecodeCallocEntryB.v / DecodeCallocTopB.v. PROVED as lib/B/DecodeBRows.v:159 dec_b_inst (TfibSyms's
   ts_inst) at TfibB_syms. *)
Lemma H_CALLOC_INST : as_inst B = DEC_B_instance.
Proof. exact (DRows.dec_b_inst B BD2l.TfibB_syms). Qed.
(* H_CALLOC_RT_TRY / H_CALLOC_RT_MCS / H_CALLOC_RT_GETPC: the walks of TryAsanInitFromRtl, GetMallocContextSize and
   StackTrace::GetCurrentPc, PROVED as lib/B/DecodeBRowsRt.v:128 dec_b_rt_try, :75 dec_b_rt_mcs, :40 dec_b_rt_getpc.
   H_CALLOC_RT_UNW: BufferedStackTrace::UnwindImpl, PROVED as lib/B/DecodeBRows.v:44 dec_b_rt_unw (the core's
   lib/B/YFl4.v unwind walk). *)
Lemma H_CALLOC_RT_TRY : forall (fx : YK11.FPState) (rc : YM05.RunCeil), decode_try_init_spec_B.
Proof. exact DRowsRt.dec_b_rt_try. Qed.
Lemma H_CALLOC_RT_MCS : forall (fx : YK11.FPState) (rc : YM05.RunCeil), decode_mcs_spec_B.
Proof. exact DRowsRt.dec_b_rt_mcs. Qed.
Lemma H_CALLOC_RT_GETPC : forall (fx : YK11.FPState) (rc : YM05.RunCeil), decode_getpc_spec_B.
Proof. exact DRowsRt.dec_b_rt_getpc. Qed.
Lemma H_CALLOC_RT_UNW : forall (fx : YK11.FPState) (rc : YM05.RunCeil), decode_unwind_spec_B.
Proof. exact DRows.dec_b_rt_unw. Qed.
(* H_CALLOC_FILL: the zero fill through __interception::real_memset, PROVED for every record as
   lib/B/DecodeBRowsFill.v:37 dec_b_fill. *)
Lemma H_CALLOC_FILL : forall (fx : YK11.FPState) (rc : YM05.RunCeil), decode_zero_fill_spec_B B.
Proof. intros fx rc. exact (DFill.dec_b_fill fx rc B). Qed.
(* H_CALLOC_CELLS: the sixteen start-up cells, PROVED as lib/B/DecodeBRows.v:77 dec_b_cells (ARm's const and thread
   cells) at TfibB_syms. *)
Lemma H_CALLOC_CELLS : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  forall ly S W regs mem md ch, acall_pre segs B ly S W regs mem md ch -> dec_cells_B ly W mem.
Proof. exact (DRows.dec_b_cells B BD2l.TfibB_syms). Qed.
(* H_CALLOC_IMG_CONST: its third conjunct is restated in the record's form `c8 (AInst o_space) (ASp 0)` (the form of
   lib/B/YF0m.v Tfib_const_sym, as DecodeCallocEntryB.v and DecodeCallocTopB.v state it; the cell's address follows
   from H_CALLOC_INST). PROVED as lib/B/DecodeBRows.v:146 dec_b_img_const (ts_const, cell_lookup) at TfibB_syms. *)
Lemma H_CALLOC_IMG_CONST : forall ly,
  In (z8 (ANum DEC_B_got_real_memset) DEC_B_real_memset) (as_const B ly) /\
  In (z8 (ANum DEC_B_real_memset) DEC_B_memset) (as_const B ly) /\
  In (c8 (AInst o_space) (ASp 0)) (as_const B ly).
Proof. exact (DRows.dec_b_img_const B BD2l.TfibB_syms). Qed.
(* H_CALLOC_ERRNO_LOW (the first conjunct of HB_API_ENV) and H_LINK_CALLOC04 (the calloc call rule at
   MT = ameter_triv, from lib/Reusable/YCbpCalloc.v acalloc04_rule_triv) are PROVED below (section 7b); they are not
   hypotheses. *)

(* ===================================================================================================== *)
(* 6. The 10 program leaves and the kit the leaf translations stand on                                    *)
(* ===================================================================================================== *)
(* The leaf statements are lib/B/Prog/<leaf>_cg.v dec_<leaf>_cg_of_F_stmt on the shared kit lib/B/Prog/LeafCgKit.v
   (a working branch fbea24d49f1); their footprint side <leaf>_contract_F is PROVED
   on that branch, so each leaf below is the TRANSLATION only, with the kit's generic translation as its premise.
   bridge_evtF is proved upstream (a working branch eea54967566, Reusable/YA0nR.v), ret_ok_stmt is proved
   (lib/B/Prog/LeafCgFacts.v ret_ok_stmt_YK0s) and AR_stack_img_stmt is dropped (fbea24d49f1). The four kit / glue
   rows below are PROVED, each a Lemma of its earlier hypothesis's name and statement. *)
(* H_KIT_AVIEW_EXT / H_KIT_AVIEW_SOME: the two kit premises about aview that the kit states (LeafCgKit.v
   aview_ext_stmt, aview_some_stmt), at this unit's aview. PROVED as lib/B/Prog/LeafCgClose.v:17 dec_b_kit_aview_ext
   and :20 dec_b_kit_aview_some (LeafCgFacts.v aview_ext_stmt_YG0n / aview_some_stmt_YG0n;
   a working branch 9436a8e5931). *)
Lemma H_KIT_AVIEW_EXT : @LK.aview_ext_stmt (aview segs).
Proof. exact DLeaf.dec_b_kit_aview_ext. Qed.
Lemma H_KIT_AVIEW_SOME : @LK.aview_some_stmt (aview segs).
Proof. exact DLeaf.dec_b_kit_aview_some. Qed.
(* H_LEAF_GLUE / H_LEAF_GLUE_FX: the ONE generic translation of the kit (LeafCgKit.v leaf_cg_of_evtF_stmt and its
   float-state twin leaf_cg_of_evtF_fx_stmt), from the two aview premises. PROVED as lib/B/Prog/LeafCgClose.v:26
   dec_b_leaf_glue and :42 dec_b_leaf_glue_fx (LeafCgGlue.v leaf_cg_of_evtF / leaf_cg_of_evtF_fx over the kit facts
   of LeafCgFacts.v, a working branch 585df3525ed), for every record B. *)
Lemma H_LEAF_GLUE : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @LK.aview_ext_stmt (aview segs) -> @LK.aview_some_stmt (aview segs) ->
  @PC.dec_leaf_wr_at rc B (@LK.leaf_cg_of_evtF_stmt) fx.
Proof. exact (DLeaf.dec_b_leaf_glue B). Qed.
Lemma H_LEAF_GLUE_FX : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @LK.aview_ext_stmt (aview segs) -> @LK.aview_some_stmt (aview segs) ->
  @PC.dec_leaf_wr_at rc B (@LK.leaf_cg_of_evtF_fx_stmt) fx.
Proof. exact (DLeaf.dec_b_leaf_glue_fx B). Qed.

(* ===================================================================================================== *)
(* 7. The facts about B the program walks take (donor lib/YCfi.v's links and lib/YCeh.v's record)      *)
(* ===================================================================================================== *)
(* Every fact of this section is PROVED at B := TfibB (and the sink instance, RLO / RHI and RA_LLVMF bound above) on
   a step-5b row, or by computation at TfibB here, and applied unchanged; each keeps its name as a Lemma whose
   statement is the hypothesis it replaces. *)
(* HB_PC_WRAP_MALLOC / HB_PC_WRAP_FREE / HB_PC_STACK_MALLOC0: the code addresses the call rules and the class-0
   side stack are stated at are the listing's, in cgif's PALib form (cgif lib/YC1f.v:309-310 pal_malloc / pal_free;
   Reusable/YG0d.v:290 pc_stack_malloc). They replace the TfibLib record the earlier statement took. PROVED by
   computation at TfibB: lib/B/DecodeBPcs.v:14 decB_pc_wrap_malloc, :17 decB_pc_wrap_free
   (a working branch 0f01e37f954) and lib/B/DecodeBRtStackMalloc.v:43 dec_pc_stack_malloc0. *)
Lemma HB_PC_WRAP_MALLOC : pc_wrap_malloc (as_code B) = decodeb_sigma DB___interceptor_trampoline_malloc.
Proof. exact DPcs.decB_pc_wrap_malloc. Qed.
Lemma HB_PC_WRAP_FREE : pc_wrap_free (as_code B) = decodeb_sigma DB___interceptor_trampoline_free.
Proof. exact DPcs.decB_pc_wrap_free. Qed.
Lemma HB_PC_STACK_MALLOC0 : pc_stack_malloc (as_code B) 0 = decodeb_sigma DB___asan_stack_malloc_0.
Proof. exact DRtS.dec_pc_stack_malloc0. Qed.
(* HB_CRT_CELLS: the ASan runtime cells the program leaves read are CONSTANT cells of B, and the value-0 shadow
   granules of the three REAC_MODE tables lie in as_zero_shadow B ranges (dec_tab_zshadow_at)
   (lib/B/Prog/check_round_trip_cg.v dec_crt_cells), which AR keeps at every state, as cgif keeps its own
   (lib/YF0m.v:28). PROVED by computation at TfibB: lib/B/DecodeBCrtFacts.v:54 dec_crt_cells_TfibB
   (a working branch 5f5e232261b). *)
Lemma HB_CRT_CELLS : @PC.dec_crt_cells B.
Proof. exact DCrt.dec_crt_cells_TfibB. Qed.
(* HB_RO_RD_UNOWNED / HB_ROM_NO_ERRNO: the two instance facts about B the read-only reads need
   (check_round_trip_cg.v dec_ro_rd_unowned / dec_rom_no_errno): no DEC_RO_RD byte is an owned static of B, and
   errno is not in the read-only image. PROVED by computation at TfibB: lib/B/DecodeBCrtFacts.v:71
   dec_ro_rd_unowned_TfibB and lib/B/DecodeBSinkRo.v:99 dec_HB_ROM_NO_ERRNO
   (a working branch 37b882978fec). *)
Lemma HB_RO_RD_UNOWNED : PC.dec_ro_rd_unowned B.
Proof. exact DCrt.dec_ro_rd_unowned_TfibB. Qed.
Lemma HB_ROM_NO_ERRNO : PC.dec_rom_no_errno B.
Proof. exact DSink.dec_HB_ROM_NO_ERRNO. Qed.
(* HB_SINK_KEPT / HB_META_KEPT: cgif's asink_none_kept / ameta_inv_kept (used at cgif lib/A/ACfj.v:193 / :199),
   specialised to one journal step, as the program walk's statement takes them. HB_SINK_KEPT carries the premise
   `~ YI16.sink_open_fp FP` of the amended statement (a working branch cb3945d8e0b,
   lib/B/Prog/LLVMFuzzerTestOneInput_cg.v:235); without it the fact is false at image B
   (lib/B/DecodeBSinkRoProbe.v HB_SINK_KEPT_false). PROVED from the core's sink record laws:
   lib/B/DecodeBSinkRo.v:48 dec_HB_SINK_KEPT (lib/B/YE01.v asink_none_kept) and :63 dec_HB_META_KEPT
   (lib/B/YE01.v ameta_inv_kept). *)
Lemma HB_SINK_KEPT : forall (rc : YM05.RunCeil),
  forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
    @ajournal rc dec_B_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
    ~ YI16.sink_open_fp FP ->
    asink_none segs KS (mrestrict (w_H W0) mem0) md0 -> asink_none segs KS (mrestrict (w_H W') mem') md'.
Proof. exact DSink.dec_HB_SINK_KEPT. Qed.
Lemma HB_META_KEPT : forall (rc : YM05.RunCeil),
  forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
    @ajournal rc dec_B_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
    ameta_inv segs KS ly (mrestrict (w_H W0) mem0) M -> ameta_inv segs KS ly' (mrestrict (w_H W') mem') M.
Proof. exact DSink.dec_HB_META_KEPT. Qed.
(* HB_UNIVERSE_OK: the trace universe is well formed (Reusable/YG01.v:142 universe_ok); cgif gets it from
   lib/YCej.v:153 Tfib_universe_ok. PROVED as lib/B/DecodeBLaws.v:32 HB_UNIVERSE_OK (TfibSyms's ts_universe at
   TfibB_syms; a working branch 5bce41888be, file taken by path). *)
Lemma HB_UNIVERSE_OK : universe_ok (as_universe B).
Proof. exact DLaws.HB_UNIVERSE_OK. Qed.
(* HB_MODEL_LAWS: donor lib/YCfi.v:72 link_ML (Reusable/YG05.v model_laws_ok). PROVED as lib/B/DecodeBLaws.v:36
   HB_MODEL_LAWS. *)
Lemma HB_MODEL_LAWS : model_laws (as_universe B).
Proof. exact DLaws.HB_MODEL_LAWS. Qed.
(* HB_METER_LAWS / HB_METER_FS_LAWS (donor Reusable/YCbp.v:21, :23 ameter_triv_laws, ameter_triv_fs_laws) are PROVED
   at MT = ameter_triv below (section 7b). *)
(* HB_SMP / HB_ASF / HB_FFL: donor lib/YCfi.v:74 link_SMP (Reusable/YG05.v stack_malloc_progress), :88 link_ASF
   (Reusable/YG0t.v astack_free_law_ok) and :76 link_FFL (AR_laws's al_flag and the image cover). PROVED at TfibB as
   lib/B/DecodeBRtStackMalloc.v:47 dec_smp, :51 dec_asf and :57 dec_ffl. *)
Lemma HB_SMP : stack_malloc_progressP B.
Proof. exact DRtS.dec_smp. Qed.
Lemma HB_ASF : forall (rc : YM05.RunCeil), astack_free_law segs B.
Proof. exact DRtS.dec_asf. Qed.
Lemma HB_FFL : forall (rc : YM05.RunCeil), frame_flag_lawP segs B.
Proof. exact DRtS.dec_ffl. Qed.
(* HB_SINK_IMG_LAWS: donor lib/YCfi.v:106 AIL (a Theorem Labs lane's lib/Reusable/YE01.v:28 asink_img_laws). PROVED as
   lib/B/DecodeBSinkRo.v:44 dec_HB_SINK_IMG_LAWS (the core's lib/B/YD1u.v tfib_AIL at TfibB). *)
Lemma HB_SINK_IMG_LAWS : asink_img_laws segs B KS.
Proof. exact DSink.dec_HB_SINK_IMG_LAWS. Qed.
(* HB_RO_BELOW_OFL: donor lib/YCfi.v:45 tfib_ROB (cgif lib/YC20.v:49 ro_tfa_below_ofl at the sink head). PROVED as
   lib/B/DecodeBSinkRo.v:81 dec_HB_RO_BELOW_OFL (every read-only loaded segment ends at or below the ofl head,
   vm_compute), at RHI = 0x99ff8 <= DEC_B_ofl_head = 0x5f49d0. *)
Lemma HB_RO_BELOW_OFL : ro_below_ofl segs RLO RHI.
Proof.
  exact (DSink.dec_HB_RO_BELOW_OFL RLO RHI ltac:(unfold DEC_B_ofl_head; apply Z.leb_le; reflexivity)).
Qed.
(* HB_LLVMF_UTRACES / HB_CRT_UCTX / HB_CRT_UFIX: the allocator traces of the two program walks are in B's trace
   universe (lib/B/Prog/LLVMFuzzerTestOneInput_cg.v dec_llvmf_utraces, lib/B/Prog/check_round_trip_cg.v
   dec_crt_uctx / dec_crt_ufix). PROVED by computation at TfibB and RA_LLVMF = 0x7ffac:
   lib/B/DecodeBCrtFacts.v:91 dec_llvmf_utraces_TfibB, :102 dec_crt_uctx_TfibB, :77 dec_crt_ufix_TfibB. *)
Lemma HB_LLVMF_UTRACES : @PL.dec_llvmf_utraces RA_LLVMF B.
Proof. exact DCrt.dec_llvmf_utraces_TfibB. Qed.
Lemma HB_CRT_UCTX : @PC.dec_crt_uctx B (@PL.CTX_check_round_trip RA_LLVMF).
Proof. exact DCrt.dec_crt_uctx_TfibB. Qed.
Lemma HB_CRT_UFIX : @PC.dec_crt_ufix B.
Proof. exact DCrt.dec_crt_ufix_TfibB. Qed.
(* HB_COST: the meter bound of one call of the entry function (donor lib/YCfi.v:61-66 XL0_HXL / XL0_HXL2, at
   XL0 = fun _ => 0 and ameter_triv). PROVED at MT = ameter_triv and XL = dec_XL0 as lib/B/DecodeBLaws.v:40
   HB_COST (every mo_malloc and mo_free of ameter_triv is 0). *)
Lemma HB_COST : forall n, 0 <= n -> @PL.dec_llvmf_cost MT n <= XL n.
Proof. exact DLaws.HB_COST. Qed.
(* HB_API_ENV: the walk layer's environment record of B (Reusable/YCbq.v:811-814 api_env, the Section hypothesis
   errno_low of YCbq.v:820 and Reusable/YCbp.v): errno lies in low memory and in the loaded image, and the
   one-element traces of the malloc and free interceptors are in B's trace universe. PROVED by computation at
   TfibB: errno (lib/B/YF0m.v TFIB_ERRNO = 0x5d4234) lies below kLowMemEnd and inside one loaded segment, and
   [0x52250] / [0x520f0] are in Tfib_universe (lib/B/YD2l.v:36 In_of_existsb). *)
Lemma HB_API_ENV : api_env segs B.
Proof.
  assert (E : ((0 <=? as_errno B) && (as_errno B + 4 <=? kLowMemEnd) &&
    existsb (fun s : Segment => (Z.of_N (seg_base s) <=? as_errno B) &&
      (as_errno B + 4 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs)%bool = true)
    by (vm_compute; reflexivity).
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.leb_le in E2.
  apply existsb_exists in E3 as (s & Hs & Hb). apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [split; [exact E1 | exact E2] | split].
  - intros a Ha. unfold in_img. exists s. split; [exact Hs | lia].
  - split; apply BD2l.In_of_existsb; vm_compute; reflexivity.
Qed.
(* HB_CALLOC_UNIV0: the one-element trace of the calloc interceptor (DecodeCalloc.v DEC_B_calloc_ra0 = 0x52484) is
   in B's trace universe, the calloc twin of api_env's malloc / free conjunct, which YCbpCalloc.v acalloc04_rule_triv
   takes. PROVED by computation at TfibB (Tfib_universe, lib/B/YD2l.v:36 In_of_existsb). *)
Lemma HB_CALLOC_UNIV0 : In [DEC_B_calloc_ra0] (as_universe B).
Proof. apply BD2l.In_of_existsb. vm_compute. reflexivity. Qed.

(* ===================================================================================================== *)
(* 7b. The parts proved at MT = ameter_triv (lib/Reusable/YCbp.v, lib/Reusable/YCbpCalloc.v)            *)
(* ===================================================================================================== *)
(* HB_METER_LAWS / HB_METER_FS_LAWS: Reusable/YCbp.v:22 ameter_triv_laws / :24 ameter_triv_fs_laws. *)
Lemma HB_METER_LAWS : ameter_laws MT.
Proof. exact ameter_triv_laws. Qed.
Lemma HB_METER_FS_LAWS : ameter_fs_laws MT.
Proof. exact ameter_triv_fs_laws. Qed.
(* H_CALLOC_ERRNO_LOW: the first conjunct of HB_API_ENV. *)
Lemma H_CALLOC_ERRNO_LOW : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd.
Proof. exact (proj1 HB_API_ENV). Qed.
(* H_LINK_MALLOC04 / H_LINK_FREE04: the call-rule form a program walk consumes, Reusable/YCbp.v:30 amalloc04_rule_triv /
   :39 afree04_rule_triv (cgif's lib/YCbp.v:29 / :38), at the image's segments (lib/B/Prog/DecodeBImg.v
   decodeb_segs_low), HB_API_ENV, AR_laws_ok and HB_MODEL_LAWS. *)
Lemma H_LINK_MALLOC04 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @amalloc_realizes fx rc segs B -> @amalloc04_rule fx rc dec_B_sink_head segs B MT.
Proof.
  intros rc fx AM. apply (amalloc04_rule_triv (SK := dec_B_sink_head) segs B).
  - exact DecodeBImg.decodeb_segs_low.
  - exact HB_API_ENV.
  - apply AR_laws_ok.
  - exact HB_MODEL_LAWS.
  - exact AM.
Qed.
Lemma H_LINK_FREE04 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @afree_realizes fx rc segs B -> @afree04_rule fx rc dec_B_sink_head segs B MT.
Proof.
  intros rc fx AF. apply (afree04_rule_triv (SK := dec_B_sink_head) segs B).
  - exact DecodeBImg.decodeb_segs_low.
  - exact HB_API_ENV.
  - apply AR_laws_ok.
  - exact HB_MODEL_LAWS.
  - exact AF.
Qed.
(* H_LINK_CALLOC04: the call-rule form the check_round_trip walk consumes (Reusable/YGCalloc.v acalloc04_rule at this
   unit's journal and meter), from the interceptor's contract: Reusable/YCbpCalloc.v:139 acalloc04_rule_triv, the calloc
   twin of amalloc04_rule_triv, with HB_CALLOC_UNIV0 for its one-element trace. The trampoline
   decodeb_sigma DB___interceptor_trampoline_calloc is DEC_B_wrap_calloc = 0x51fb4 by computation. *)
Lemma H_LINK_CALLOC04 : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  @decode_acalloc_B fx rc B ->
  @acalloc04_rule fx segs B (as_universe B) (@ajournal rc dec_B_sink_head segs B) (@acall_kept rc segs B)
    (mo_ok MT) (mo_le MT) (mo_malloc MT) (decodeb_sigma DB___interceptor_trampoline_calloc) DEC_B_calloc_ra0
    DEC_CALLOC_MAX DEC_CALLOC_DEPTH.
Proof.
  intros fx rc AC. apply (acalloc04_rule_triv (SK := dec_B_sink_head) segs B).
  - exact DecodeBImg.decodeb_segs_low.
  - exact HB_API_ENV.
  - apply AR_laws_ok.
  - exact HB_MODEL_LAWS.
  - exact HB_CALLOC_UNIV0.
  - exact AC.
Qed.

(* ===================================================================================================== *)
(* The composition                                                                                        *)
(* ===================================================================================================== *)
Section RC. Context {rc : YM05.RunCeil}.

(* The ten leaves, each from its PROVED translation dec_<leaf>_cg_of_F (lib/B/Prog/<leaf>_cg.v,
   a working branch d6060ccd6a6) over the kit's generic translation H_LEAF_GLUE /
   H_LEAF_GLUE_FX, applied to its PROVED footprint contract (<leaf>_F.v, or <leaf>_F_nosh.v for the six leaves
   whose statement dropped the shadow_rw premise, leaves 39c43113162). *)
Lemma LEAF_IS_REAC : forall fx : YK11.FPState, @PC.dec_leaf_at rc B (@LIsReac.dec_reac_frame_is_reac_cg) fx.
Proof.
  intros fx. exact (@LIsReac.dec_reac_frame_is_reac_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate (@AR rc segs B) (aview segs) same_but_materialized
      ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) NIsReac.reac_frame_is_reac_holds_F_nosh).
Qed.
Lemma LEAF_CLEAN_LEN : forall fx : YK11.FPState, @PC.dec_leaf_at rc B (@LCleanLen.dec_reac_frame_clean_len_cg) fx.
Proof.
  intros fx. exact (@LCleanLen.dec_reac_frame_clean_len_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate (@AR rc segs B) (aview segs) same_but_materialized
      ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) FCleanLen.reac_frame_clean_len_holds_F).
Qed.
Lemma LEAF_COUNTER : forall fx : YK11.FPState, @PC.dec_leaf_at rc B (@LCounter.dec_reac_frame_counter_cg) fx.
Proof.
  intros fx. exact (@LCounter.dec_reac_frame_counter_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate (@AR rc segs B) (aview segs) same_but_materialized
      ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) NCounter.reac_frame_counter_holds_F_nosh).
Qed.
Lemma LEAF_INSPECT : forall fx : YK11.FPState, @PC.dec_leaf_at rc B (@LInspect.dec_reac_frame_inspect_cg) fx.
Proof.
  intros fx. exact (@LInspect.dec_reac_frame_inspect_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate (@AR rc segs B) (aview segs) same_but_materialized
      ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) NInspect.reac_frame_inspect_holds_F_nosh).
Qed.
Lemma LEAF_UP_CHANNELS : forall fx : YK11.FPState,
  @PC.dec_leaf_at rc B (@LUpChannels.dec_reac_upstream_channels_cg) fx.
Proof.
  intros fx. exact (@LUpChannels.dec_reac_upstream_channels_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate (@AR rc segs B) (aview segs) same_but_materialized
      ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) FUpChannels.reac_upstream_channels_holds_F).
Qed.
Lemma LEAF_CHECK_BRAID : forall fx : YK11.FPState, @PC.dec_leaf_at rc B (@LCheckBraid.dec_check_braid_cg) fx.
Proof.
  intros fx. exact (@LCheckBraid.dec_check_braid_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate (@AR rc segs B) (aview segs) same_but_materialized
      ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) FCheckBraid.check_braid_holds_F).
Qed.
Lemma LEAF_DECODE : forall fx : YK11.FPState, @PC.dec_leaf_wr_at rc B (@LDecode.dec_reac_decode_cg) fx.
Proof.
  intros fx. exact (@LDecode.dec_reac_decode_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate (@AR rc segs B) (aview segs) same_but_materialized
      ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) (NDecode.reac_decode_holds_F_nosh NInspect.reac_frame_inspect_holds_F_nosh)).
Qed.
Lemma LEAF_PLAIN_LE : forall fx : YK11.FPState, @PC.dec_leaf_wr_at rc B (@LPlainLe.dec_reac_decode_plain_le_cg) fx.
Proof.
  intros fx. exact (@LPlainLe.dec_reac_decode_plain_le_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate (@AR rc segs B) (aview segs) same_but_materialized
      ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) (NPlainLe.reac_decode_plain_le_holds_F_nosh NInspect.reac_frame_inspect_holds_F_nosh)).
Qed.
Lemma LEAF_UP_DECODE : forall fx : YK11.FPState, @PC.dec_leaf_wr_at rc B (@LUpDecode.dec_reac_upstream_decode_cg) fx.
Proof.
  intros fx. exact (@LUpDecode.dec_reac_upstream_decode_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate (@AR rc segs B) (aview segs) same_but_materialized
      ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (H_LEAF_GLUE rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) FUpDecode.reac_upstream_decode_holds_F).
Qed.
Lemma LEAF_BRAID : forall fx : YK11.FPState, @PC.dec_leaf_wr_at rc B (@LBraid.dec_reac_braid_encode_cg) fx.
Proof.
  intros fx. exact (@LBraid.dec_reac_braid_encode_cg_of_F fx (world segs) (@w_H segs) (SRr segs) alayout astate (@AR rc segs B) (aview segs) same_but_materialized
      ly_stk_lo ly_stk_hi YK0s.ret_ok (as_gp B) (as_tp B) (aowned B)
    (H_LEAF_GLUE_FX rc fx H_KIT_AVIEW_EXT H_KIT_AVIEW_SOME) NBraid.reac_braid_encode_holds_F_nosh).
Qed.

(* The calloc interceptor's contract, from a Theorem Labs lane's Allocate and the calloc lane's CLOSED composition
   (lib/A/DecodeCallocTopB.v decode_acalloc_of_allocate_B_holds, Qed). *)
Lemma CALLOC_REALIZES : forall fx : YK11.FPState, @decode_acalloc_B fx rc B.
Proof.
  intros fx.
  apply (@DCTop.decode_acalloc_of_allocate_B_holds fx rc B).
  - exact (H_CALLOC_IMG_COVER fx rc).
  - exact H_CALLOC_TP.
  - exact H_CALLOC_INST.
  - exact (H_CALLOC_RT_TRY fx rc).
  - exact (H_CALLOC_RT_MCS fx rc).
  - exact (H_CALLOC_RT_GETPC fx rc).
  - exact (H_CALLOC_RT_UNW fx rc).
  - exact (H_CALLOC_FILL fx rc).
  - exact (H_CALLOC_CELLS fx rc).
  - apply AR_laws_ok.
  - exact H_CALLOC_IMG_CONST.
  - exact H_CALLOC_ERRNO_LOW.
  - exact DEC_CALLOC_MAX_prim.
  - exact (H_CALLOC_ALLOCATE fx rc).
Qed.

(* check_round_trip's walk: the PROVED dec_check_round_trip_cg_holds (check_round_trip_cgpf.v:54), over its own
   callee contracts. *)
Lemma CRT_HOLDS : forall fx : YK11.FPState,
  @PC.dec_check_round_trip_cg fx rc B MT (decodeb_sigma DB_check_round_trip) (@PL.CTX_check_round_trip RA_LLVMF).
Proof.
  intros fx. apply (@PCpf.dec_check_round_trip_cg_holds fx rc B MT (@PL.CTX_check_round_trip RA_LLVMF)).
  - exact HB_PC_WRAP_MALLOC.
  - exact HB_PC_WRAP_FREE.
  - exact HB_CRT_CELLS.
  - exact HB_RO_RD_UNOWNED.
  - exact HB_ROM_NO_ERRNO.
  - apply AR_laws_ok.
  - exact HB_METER_LAWS.
  - exact HB_CRT_UCTX.
  - exact HB_CRT_UFIX.
  - intros fx'. exact (H_LINK_MALLOC04 rc fx' (H_RT_MALLOC rc fx')).
  - intros fx'. exact (H_LINK_FREE04 rc fx' (H_RT_FREE rc fx')).
  - intros fx'. exact (H_LINK_CALLOC04 fx' rc (CALLOC_REALIZES fx')).
  - intros fx'. exact (H_RT_BCMP rc fx').
  - exact LEAF_BRAID.
Qed.

(* The program contract of the entry function, from the walk and every callee it names. *)
Lemma LIB_CONTRACT : @PL.dec_lib_contract_x_all rc decode_shape asink_syms KS asink_none ameta_inv arodata_okS
  RA_LLVMF A_EMPTY B MT XL XL RLO RHI.
Proof.
  apply (H_PROG_LLVMF rc).
  - exact HB_PC_WRAP_MALLOC.
  - exact HB_PC_WRAP_FREE.
  - exact HB_PC_STACK_MALLOC0.
  - exact HB_CRT_CELLS.
  - exact HB_RO_RD_UNOWNED.
  - exact HB_ROM_NO_ERRNO.
  - exact HB_LLVMF_UTRACES.
  - apply AR_laws_ok.
  - exact HB_MODEL_LAWS.
  - exact HB_METER_LAWS.
  - exact HB_METER_FS_LAWS.
  - exact HB_SMP.
  - exact (HB_ASF rc).
  - exact (HB_FFL rc).
  - exact HB_SINK_IMG_LAWS.
  - exact (HB_SINK_KEPT rc).
  - exact (HB_META_KEPT rc).
  - exact HB_RO_BELOW_OFL.
  - intros fx. exact (H_RT_STACK_MALLOC0 rc fx).
  - intros fx. exact (H_RT_ASAN_MEMSET rc fx).
  - intros fx. exact (H_RT_ASAN_MEMCPY rc fx).
  - intros fx. exact (H_LINK_MALLOC04 rc fx (H_RT_MALLOC rc fx)).
  - intros fx. exact (H_LINK_FREE04 rc fx (H_RT_FREE rc fx)).
  - intros fx. exact (H_RT_BCMP rc fx).
  - exact CRT_HOLDS.
  - exact LEAF_IS_REAC.
  - exact LEAF_CLEAN_LEN.
  - exact LEAF_COUNTER.
  - exact LEAF_INSPECT.
  - exact LEAF_DECODE.
  - exact LEAF_PLAIN_LE.
  - exact LEAF_UP_CHANNELS.
  - exact LEAF_UP_DECODE.
  - exact LEAF_CHECK_BRAID.
  - exact HB_COST.
Qed.

(* donor lib/YD1q.v:79-98 tfib_srealizesX, the same proof. *)
Lemma decode_srealizesX_rc : forall (sp : word) (rdraw : EntryDraw) (brk mb : word) (inp : ProcInput),
  valid_sp sp -> valid_brk segs brk -> valid_mmap_base mb ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  @YM05.ceil_of_top rc (bv_unsigned sp - stack_max_size) ->
  srealizes segs (init_config segs DAU.M.init_pc DAU.M.phdrs sp brk mb rdraw target_alloc_limit inp)
    (SPECX (LS:=decode_shape) inp).
Proof.
  intros sp rdraw brk mb inp Hsp Hbrk Hmb Hfit Hinp Hceil.
  destruct inp as [argv envp fs stdin uid gid groups net nofile sigmask hw ab mmu urnd tmp].
  pose proof Hinp as (Hva & Hve & _ & _ & [Huid Hgid] & _ & _ & Hhw & Hab & Hmmu & _).
  (* Only the input's projections are reduced: a bare `cbn in *` would also reduce the Section hypotheses in the
     context, whose statements name the listing's lookups (decode_sigma), and does not finish. *)
  cbn [in_argv in_envp in_uid in_hwcap in_abort_terminal in_va_size] in Hva, Hve, Huid, Hhw, Hab, Hmmu, Hfit.
  subst ab mmu.
  (* The trace set and the input are given explicitly: left as `_`, their unification problems
     (?T [] against SPECX ?inp [], in_argv ?inp against argv) did not finish in an hour of elaboration. *)
  apply (H_STARTUP sp rdraw brk mb argv envp fs stdin uid gid groups net nofile sigmask hw urnd tmp
    Hsp Hbrk Hva Hve Hfit Huid Hhw (SPECX (LS:=decode_shape) (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp)) (specx_has_nil _)).
  intros h c Hok.
  exact (H_DRIVER rc (H_RT_MALLOC rc) (H_RT_FREE rc) (H_RT_MEMCPY_WRAP rc) LIB_CONTRACT HB_UNIVERSE_OK
    sp rdraw brk (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp) h c Hsp Hbrk Hfit Hinp Hceil Hok).
Qed.
End RC.

(* donor lib/YD2o.v:75-84 tfib_srealizesX_top and TFIB_TB_of_partsXF. *)
Theorem decode_TFIB_TB_of_parts : TFIB_TB.
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
  exact (@decode_srealizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_windowD sp Hsp)) sp rnd brk mbase inp
    Hsp Hbrk Hmb Hfit Hinp (YM05.ceil_of_top_run _)).
Qed.

(* The two ASan+UBSan statements of record, given only the named parts above. *)
Theorem decode_asan_ubsan_agrees_of_parts : DSt.asan_ubsan_agrees.
Proof. exact (AsanTop.decode_asan_ubsan_agrees_of_tfib decode_TFIB_TB_of_parts). Qed.
Theorem decode_asan_ubsan_halts_of_parts : DSt.asan_ubsan_halts.
Proof. exact (AsanTop.decode_asan_ubsan_halts_of_tfib decode_TFIB_TB_of_parts). Qed.

(* Inside the Section, as fuzz_grant's lib/A/GrantTop.v does it (a working branch 7d31e8f3534): About lists every
   part a statement rests on (the Section variables and hypotheses above), and Print Assumptions lists those parts
   next to the axioms toolchain/allowed-axioms.txt allows (origin/ossv/recipes:toolchain/allowed-axioms.txt). *)
About decode_asan_ubsan_agrees_of_parts.
Print Assumptions decode_asan_ubsan_agrees_of_parts.
About decode_asan_ubsan_halts_of_parts.
Print Assumptions decode_asan_ubsan_halts_of_parts.
End asan_ubsan.
