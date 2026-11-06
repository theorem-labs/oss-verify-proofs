(* fuzz_state, image B (fs.asan-ubsan): the CLOSING SIDE of the two asan_ubsan statements of record,
   Statements.asan_ubsan_agrees and Statements.asan_ubsan_halts, from NAMED Section hypotheses (rule 24: no function
   proved; this file is assembly only, no walk is written here).

   The B twin of lib/A/FSClose.v (a working branch 1469f04666b), same
   decomposition (a Theorem Labs lane's lib/A/FMTfibParts.v, a working branch aeb12aaa12b):
     TFIB_T_B <-  lib/B/FSTfibPartsB.v TFIB_T_of_lib_B at LI := LI_fs: the start-up, HS_ok_open, the driver main, the
                  allocator, the driver's memcpy, the read checks and the stdio sites are PROVED lemmas of image B's
                  relocated core there (lib/B/YD1q.v tfib_srealizesX); its three premises are the program part LIBX
                  (the harness contract in the driver's INDEXED form) and the two library-invariant facts LIK / LI0.
     LIBX     <-  lib/B/FSTfibBridge.v fs_lib_xI_all applied to image B's program part fs_lib_x_B, and fs_lib_x_B <-
                  ENTRY's lib/B/FSW_entry.v fs_entry_proof (the walk of LLVMFuzzerTestOneInput on fs.asan-ubsan,
                  lib/B/FSH_Fn_entry.v fs_entry_goal) applied to its premises; the callee specs among them are S0's
                  proved image-B walks where S0 has one.
     LIK, LI0 <-  lib/B/FSTfibBridge.v LIK_fs and LI0_fs (a Theorem Labs lane, row F10).
   B := lib/B/YD2l.v TfibBU, its TfibSyms lib/B/YD2l.v TfibBU_syms; the sink head is lib/B/FSH_Base.v fsB_sink_head and
   the sink cells lib/B/YE2k.v tfib_K, both passed by position (`@`), never inferred.
   Rows of fs-OBLIGATIONS.md B0 .. B11 CLOSED here (each with its lemma below); the rows still named are listed at
   the Section's hypotheses. The row table is a Theorem Labs lane's fs-OBLIGATIONS record. *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_state Require Statements.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
  YK11 YK0s YK15 YK18 YK09 YK0c YK0e YA01 YA0c YA0e YA02 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
  YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YCbp YC5d YI00 YI04 YI16 YK06 YE00 YE01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import ZTraceSpec AgreeShape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoisonU SetShadowDefU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YF0m YCfn YD1w YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_Base FSH_Rt FSPstat FSH_Harness.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
  FSH_Fn_alloc FSH_Fn_checks FSH_Fn_cno FSH_Fn_crt FSH_Fn_writer FSH_Fn_entry FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSTfibBridge FSTfibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YE2k YCeg FSpoisonS FSTopB FSW_entry FSW_entry_link.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSTfibPartsB FSxM FSxU FSxSS FSImgFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSrtcells FSupoisonCmp FSupoisonAsanC FSW_preset_base64_encode FSxMset preset_base64_decode_ff_orch.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSReallocAGc.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Rt Require StrcmpU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSH_crt_chain FSW_pj_get FSW_pj_get_str FSW_pj_object
  FSW_pj_parse FSW_pj_string FSW_pj_write FSW_pj_free_top FSW_put_holds FSW_strdup FSW_write_value FSW_indent
  FSW_realloc_top FSRealloc_top ZZpsfinal FSW_reader_top FSW_parse_string.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require FSW_pj_set_holds FSW_grow_holds FSW_skip_ws.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require
  FSW_alloc_counters FSH_check_bounded_alloc FSH_check_as_written FSH_check_reject_clean
  FSH_check_reject_clean_starved FSW_fuzz_free FSW_fuzz_malloc FSpoisonW FSW_past_nul FSW_check_no_overread_top.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* SINK GUARD: no sink instance may resolve in this scope; every spec below names its head. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.

(* the library shape of TFIB_T_B (lib/B/FSTfibB.v:43) *)
Local Abbreviation LSB := (ag_shape checksum_shape).
Local Abbreviation SKB := FSH_Base.fsB_sink_head.

(* ===================================================================================================== *)
(* Facts about TfibBU proved by computation                                                                *)
(* ===================================================================================================== *)

(* the entry premise YCeg.TfibLib TfibBU (lib/B/YCeg.v:27). Port-from: cgif_file_fuzzer lib/YCed.v:29-48 tfibX_lib
   (c8557374ad2e), the B twin of lib/A/FSClose.v fs_tfib_lib, at image B's numbers: lib_const_addr is the constant
   word [0x10320, 0x10328) (lib/B/YCeg.v:26), errno is TFIB_ERRNO 0x5db38c (lib/B/YF0m.v:19) in the fourth load
   segment, the owned statics are lib/B/YF0m.v Tfib_owned_static, gp is TFIB_GP 0x10800 (lib/B/YF0m.v:18). *)
Lemma fsB_tfib_lib_consts_chk :
  forallb (fun r => (fst r + snd r <=? 0x10320) || (0x10328 <=? fst r))%bool Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

Theorem fsB_tfib_lib : YCeg.TfibLib TfibBU.
Proof.
constructor; try reflexivity.
- cbn [as_errno TfibBU]. unfold TFIB_ERRNO, kLowMemEnd. lia.
- intros a Ha. cbn [as_errno TfibBU] in Ha. unfold TFIB_ERRNO in Ha. unfold in_img.
  assert (Hb : match nth_error tfibsegs 3 with
               | Some s => ((Z.of_N (seg_base s) <=? 0x5db38c) && (0x5db390 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool
               | None => false end = true) by (vm_compute; reflexivity).
  revert Hb. destruct (nth_error tfibsegs 3) as [sg|] eqn:E; intros Hb; [| discriminate Hb].
  cbv beta iota in Hb. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact (nth_error_In _ 3 E) | lia].
- intros a Ha. cbn [as_owned_static as_errno TfibBU]. unfold TFIB_ERRNO. unfold YCeg.lib_const_addr in Ha. split; [|lia].
  intros HE. apply Exists_exists in HE as (r & Hr & [H1 H2]).
  pose proof (proj1 (forallb_forall _ _) fsB_tfib_lib_consts_chk r Hr) as Hb. cbn beta in Hb.
  apply Bool.orb_prop in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
- cbn [as_gp TfibBU]. unfold TFIB_GP. lia.
Qed.

(* the pcs FsRt / FsEntryRt pin (lib/B/FSH_Rt.v FsRt, lib/B/FSH_Fn_entry.v FsEntryRt), from S0's Tfib_code through
   ts_code of TfibBU_syms (B's class map {0, 1, 3}) *)
Lemma pc_stack_malloc_0_BU : pc_stack_malloc (as_code TfibBU) 0 = PC_stack_malloc_0.
Proof. rewrite (ts_code _ TfibBU_syms). reflexivity. Qed.
Lemma pc_stack_malloc_1_BU : pc_stack_malloc (as_code TfibBU) 1 = PC_stack_malloc_1.
Proof. rewrite (ts_code _ TfibBU_syms). reflexivity. Qed.
Lemma pc_stack_malloc_3_BU : pc_stack_malloc (as_code TfibBU) 3 = PC_stack_malloc_3.
Proof. rewrite (ts_code _ TfibBU_syms). reflexivity. Qed.
Lemma pc_wrap_malloc_BU : pc_wrap_malloc (as_code TfibBU) = PC_malloc.
Proof. rewrite (ts_code _ TfibBU_syms). reflexivity. Qed.
Lemma pc_wrap_free_BU : pc_wrap_free (as_code TfibBU) = PC_free.
Proof. rewrite (ts_code _ TfibBU_syms). reflexivity. Qed.
Lemma pc_asan_memcpy_BU : pc_asan_memcpy (as_code TfibBU) = PC_memcpy.
Proof. rewrite (ts_code _ TfibBU_syms). reflexivity. Qed.
(* lib/B/FSH_Base.v FsShadowSyms at TfibBU's two cells (lib/B/YD2l.v: as_got_shadow 0x9fc10, as_shadow_cell 0xa8438) *)
Lemma fsB_shadow_syms : FsShadowSyms TfibBU.
Proof. split; reflexivity. Qed.

(* ===================================================================================================== *)
(* The closing Section: one named hypothesis per remaining part                                            *)
(* ===================================================================================================== *)
(* the two premises of lib/B/FSRealloc_top.v fs_arealloc_BU at TfibBU, exactly as its statement has them (Allocate
   at tfib_A__ZN6__asan9Allocator8AllocateEmm..., RAW Deallocate at tfib_A__ZN6__asan9Allocator10DeallocateEPvmm...) *)
Definition FS_ALLOCATE_RAW_B (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  ltac:(let t := type of (@FSRealloc_top.fs_arealloc_BU fx rc TfibBU TfibBU_syms) in
        match t with ?A -> _ -> _ => exact A end).
Definition FS_DEALLOCATE_RAW_B (fx : YK11.FPState) (rc : YM05.RunCeil) : Prop :=
  ltac:(let t := type of (@FSRealloc_top.fs_arealloc_BU fx rc TfibBU TfibBU_syms) in
        match t with _ -> ?D -> _ => exact D end).

Section fs_close_B.

Local Abbreviation B := TfibBU (only parsing).

(* ---- RUNTIME, U forms at image B (lib/B/FSH_Rt.v FsRt and lib/B/FSH_Fn_entry.v:69 FsEntryRt) ---- *)
Local Abbreviation LAWS0 := (YG0q.AR_laws_ok tfibsegs TfibBU).
Local Abbreviation HD0 := (fun t => eq_refl).
(* strlen, memchr, bcmp, memcpy: a Theorem Labs lane's image-B interceptors (a working branch 26a456aaf33) *)
Lemma H_strlen : forall (rc : YM05.RunCeil) (fx : YK11.FPState), astrlen_realizesU tfibsegs B PC_strlen.
Proof. intros rc fx. exact (FSrtcells.fs_strlen_realizesU_s TfibBU LAWS0 TfibBU_syms fsB_tfib_lib). Qed.
(* strcmp: a Theorem Labs lane's lib/B/Rt/StrcmpU.v fs_strcmp_realizesU (in S0 8fee0cc526f) *)
Lemma H_strcmp : forall (rc : YM05.RunCeil) (fx : YK11.FPState), astrcmp_realizesU tfibsegs B PC_strcmp.
Proof. intros rc fx. exact (StrcmpU.fs_strcmp_realizesU TfibBU LAWS0 TfibBU_syms). Qed.
Lemma H_memchr : forall (rc : YM05.RunCeil) (fx : YK11.FPState), amemchr_realizesU tfibsegs B PC_memchr.
Proof. intros rc fx. exact (FSrtcells.fs_memchr_realizesU_s TfibBU LAWS0 TfibBU_syms fsB_tfib_lib). Qed.
Lemma H_bcmp : forall (rc : YM05.RunCeil) (fx : YK11.FPState), FSupoisonU.abcmp_realizesU tfibsegs B PC_bcmp.
Proof. intros rc fx. exact (FSupoisonCmp.tfib_abcmp_realizesU_PC TfibBU LAWS0 TfibBU_syms). Qed.
Lemma H_memcpy : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
Proof. intros rc fx. exact (FSupoisonAsanC.tfib_asan_memcpy_realizesU TfibBU LAWS0 TfibBU_syms). Qed.
(* memset: a Theorem Labs lane's lib/B/FSxMset.v tfib_asan_memset_realizesU (__asan_memset at B's PC_memset 0x5222c) *)
Lemma H_memset : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.
Proof. intros rc fx. exact (FSxMset.tfib_asan_memset_realizesU TfibBU LAWS0 TfibBU_syms). Qed.
(* set_shadow_f5, malloc, free, stack_malloc 0 / 1 / 3: a Theorem Labs lane's image-B runtime (lib/B/FSxSS.v, FSxM.v, FSxU.v) *)
Lemma H_set_shadow_f5 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  SetShadowDefU.aset_shadow_realizesU tfibsegs B PC_set_shadow_f5 0xf5.
Proof. intros rc fx. exact (FSxSS.set_shadow_f5_contractU_x TfibBU LAWS0 TfibBU_syms). Qed.
Lemma H_malloc : forall (rc : YM05.RunCeil) (fx : YK11.FPState), FSupoisonU.amalloc_realizesU tfibsegs B.
Proof. intros rc fx. exact (proj2 (FSxM.fr_malloc_U TfibBU TfibBU_syms HD0)). Qed.
Lemma H_free : forall (rc : YM05.RunCeil) (fx : YK11.FPState), FSupoisonU.afree_realizesU tfibsegs B.
Proof. intros rc fx. exact (proj2 (FSxM.fr_free_U TfibBU LAWS0 TfibBU_syms HD0)). Qed.
Lemma H_stack_malloc_0 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  FSupoisonU.astack_malloc_realizesU tfibsegs B 0.
Proof. intros rc fx. exact (FSxU.stack_malloc0_contractU_x TfibBU LAWS0 TfibBU_syms). Qed.
Lemma H_stack_malloc_1 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  FSupoisonU.astack_malloc_realizesU tfibsegs B 1.
Proof. intros rc fx. exact (FSxU.stack_malloc1_contractU_x TfibBU LAWS0 TfibBU_syms). Qed.
Lemma H_stack_malloc_3 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  FSupoisonU.astack_malloc_realizesU tfibsegs B 3.
Proof. intros rc fx. exact (FSxU.stack_malloc3_contractU_x TfibBU LAWS0 TfibBU_syms). Qed.

(* ---- PROGRAM PART: the image facts (a Theorem Labs lane's lib/B/FSImgFacts.v) and the callee specs with no image-B proof ---- *)
Lemma H_fs_img_facts : forall rc : YM05.RunCeil, @fs_img_facts rc tfibsegs B.
Proof. intros rc. exact (FSImgFacts.fs_img_facts_TfibBU rc). Qed.
(* realloc: lib/B/FSRealloc_top.v fs_arealloc_BU reduces FS_AREALLOC_BU to a Theorem Labs lane's Allocate contract and RAW
   Deallocate contract at fs B's pcs (route 1). Both are now PROVED by lib/B/FSReallocAGc.v (a Theorem Labs lane, route 1 B
   closing file), which closes lib/B/FSReallocAG.v Section g at the relocated image-B chain and the two ARU lifts. *)
Lemma H_alloc_raw : forall (rc : YM05.RunCeil) (fx : YK11.FPState), FS_ALLOCATE_RAW_B fx rc.
Proof. intros rc fx. exact (@FSReallocAGc.fs_aalloc_BU_TfibB fx rc). Qed.
Lemma H_dealloc_raw : forall (rc : YM05.RunCeil) (fx : YK11.FPState), FS_DEALLOCATE_RAW_B fx rc.
Proof. intros rc fx. exact (@FSReallocAGc.fs_adealloc_raw_BU_TfibB fx rc). Qed.

(* ---- the runtime record of the entry ---- *)
(* FsEntryRt: fe_stack_free is the Reusable law astack_free_law_ok (lib/Reusable/YG0t.v:474), every B *)
Lemma fsB_entry_rt : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @FsEntryRt fx rc tfibsegs B.
Proof.
  intros rc fx.
  refine {| fe_stack_malloc_0 := H_stack_malloc_0 rc fx; fe_stack_free := YG0t.astack_free_law_ok tfibsegs B;
            fe_malloc := H_malloc rc fx; fe_free := H_free rc fx; fe_memcpy := _; fe_memchr := H_memchr rc fx |}.
  rewrite pc_asan_memcpy_BU. exact (H_memcpy rc fx).
Qed.

(* ---- the callee proofs of S0 at TfibBU and fsB_sink_head; their own premises closed from fsB_tfib_lib ---- *)
Local Abbreviation ENV := (FSW_entry_link.fe_api_env TfibBU fsB_tfib_lib).
Local Abbreviation ML := (FSW_entry_link.fe_model_laws TfibBU fsB_tfib_lib).
Local Abbreviation GSH := (FSW_entry_link.fe_tl_got_shadow TfibBU fsB_tfib_lib).
Local Abbreviation CSH := (FSW_entry_link.fe_tl_shadow_cell TfibBU fsB_tfib_lib).
Local Abbreviation GUAR := (FSW_entry_link.fe_tl_got_uar TfibBU fsB_tfib_lib).
Local Abbreviation UCELL := (FSW_entry_link.fe_tl_uar_cell TfibBU fsB_tfib_lib).
Local Abbreviation SMP := (FSW_entry_link.fe_stack_malloc_progress TfibBU).
Local Abbreviation LAWS := (YG0q.AR_laws_ok tfibsegs TfibBU).

Lemma fsB_fuzz_alloc_live : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @fuzz_alloc_live_spec fx rc SKB tfibsegs B.
Proof. intros rc fx. exact (@FSW_alloc_counters.fuzz_alloc_live_ok fx rc SKB B). Qed.
Lemma fsB_fuzz_alloc_peak : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @fuzz_alloc_peak_spec fx rc SKB tfibsegs B.
Proof. intros rc fx. exact (@FSW_alloc_counters.fuzz_alloc_peak_ok fx rc SKB B). Qed.
Lemma fsB_fuzz_alloc_peak_reset : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @fuzz_alloc_peak_reset_spec fx rc SKB tfibsegs B.
Proof. intros rc fx. exact (@FSW_alloc_counters.fuzz_alloc_peak_reset_ok fx rc SKB B (H_fs_img_facts rc)). Qed.
Lemma fsB_fuzz_alloc_fail : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @fuzz_alloc_fail_spec fx rc SKB tfibsegs B.
Proof. intros rc fx. exact (@FSW_alloc_counters.fuzz_alloc_fail_ok fx rc SKB B (H_fs_img_facts rc)). Qed.
Lemma fsB_check_bounded_alloc : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @check_bounded_alloc_spec fx rc SKB tfibsegs B.
Proof. intros rc fx. exact (@FSH_check_bounded_alloc.check_bounded_alloc_proof fx rc SKB B). Qed.
Lemma fsB_check_reject_clean : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @check_reject_clean_spec fx rc SKB tfibsegs B.
Proof. intros rc fx. exact (@FSH_check_reject_clean.check_reject_clean_proof fx rc SKB B). Qed.
Lemma fsB_check_as_written : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @check_as_written_spec fx rc SKB tfibsegs B.
Proof.
  intros rc fx.
  exact (@FSH_check_as_written.check_as_written_proof fx rc SKB B
    (H_fs_img_facts rc) fsB_shadow_syms (H_strlen rc fx) (H_bcmp rc fx) (conj pc_wrap_malloc_BU (H_malloc rc fx))
    (conj pc_wrap_free_BU (H_free rc fx)) ENV ML).
Qed.
Lemma fsB_fuzz_free : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @fuzz_free_spec fx rc SKB tfibsegs B.
Proof.
  intros rc fx.
  exact (@FSW_fuzz_free.fuzz_free_holds fx rc SKB B
    (H_fs_img_facts rc) fsB_shadow_syms ENV ML (conj pc_wrap_free_BU (H_free rc fx))
    (@FSpoisonW.tfib_unpoison16 fx rc B LAWS TfibBU_syms)).
Qed.
(* fuzz_malloc (premise of encode_proof) and encode at image B (a Theorem Labs lane's lib/B/FSW_preset_base64_encode.v) *)
Lemma fsB_fuzz_malloc : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @fuzz_malloc_spec fx rc SKB tfibsegs B.
Proof.
  intros rc fx.
  exact (@FSW_fuzz_malloc.fuzz_malloc_holds fx rc SKB B (H_fs_img_facts rc) fsB_shadow_syms TfibBU_syms ENV
    (H_malloc rc fx) (@FSpoisonW.tfib_poison16 fx rc B LAWS TfibBU_syms)).
Qed.
(* decode at image B (a Theorem Labs lane's lib/B/preset_base64_decode_ff_orch.v decode_spec_ff_holds, a working branch
   856c422cb0b; from arm A's work): image facts, shadow cells, strlen, memchr, fuzz_malloc and fuzz_free *)
Lemma H_decode_ff : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @decode_spec_ff fx rc SKB B tfibsegs.
Proof.
  intros rc fx.
  exact (@preset_base64_decode_ff_orch.decode_spec_ff_holds fx rc SKB B (H_fs_img_facts rc) fsB_shadow_syms
    (H_strlen rc fx) (H_memchr rc fx) (fsB_fuzz_malloc rc fx) (fsB_fuzz_free rc fx)).
Qed.
Lemma H_encode : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @encode_spec fx rc SKB B tfibsegs.
Proof.
  intros rc fx.
  exact (@FSW_preset_base64_encode.encode_proof fx rc SKB B fsB_shadow_syms (H_fs_img_facts rc) (fsB_fuzz_malloc rc fx)).
Qed.
Lemma fsB_check_reject_clean_starved : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @check_reject_clean_starved_spec fx rc SKB tfibsegs B.
Proof.
  intros rc fx.
  exact (@FSH_check_reject_clean_starved.check_reject_clean_starved_proof fx rc SKB B
    (H_fs_img_facts rc) fsB_shadow_syms GUAR UCELL ENV ML (conj pc_stack_malloc_0_BU (H_stack_malloc_0 rc fx))
    (fsB_fuzz_alloc_live rc fx)
    (fsB_fuzz_alloc_fail rc fx) (fsB_check_reject_clean rc fx) (H_decode_ff rc fx) (H_encode rc fx)).
Qed.
Lemma fsB_past_nul : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @past_nul_spec fx rc SKB tfibsegs B.
Proof.
  intros rc fx.
  exact (@FSW_past_nul.past_nul_ok fx rc B (H_fs_img_facts rc) GSH CSH ENV ML
    (conj pc_wrap_malloc_BU (H_malloc rc fx)) (H_memcpy rc fx) (H_memset rc fx)).
Qed.
Lemma fsB_check_no_overread : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @check_no_overread_spec fx rc SKB tfibsegs B.
Proof.
  intros rc fx.
  exact (@FSW_check_no_overread_top.check_no_overread_ok fx rc B
    (fsB_past_nul rc fx) (H_decode_ff rc fx) (fsB_fuzz_free rc fx) (H_fs_img_facts rc) GSH CSH GUAR UCELL
    pc_stack_malloc_1_BU (H_stack_malloc_1 rc fx) SMP ENV ML (H_malloc rc fx) pc_wrap_malloc_BU
    (H_memcpy rc fx) (H_memset rc fx) (H_bcmp rc fx) (H_free rc fx) pc_wrap_free_BU).
Qed.

(* ---- check_round_trip at image B (lib/B/FSH_crt_chain.v check_round_trip_holds), from S0's image-B walks ---- *)
Local Abbreviation ASF := (YG0t.astack_free_law_ok tfibsegs TfibBU).
Lemma fsB_fuzz_realloc : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @fuzz_realloc_spec fx rc SKB tfibsegs B.
Proof.
  intros rc fx.
  exact (@FSW_realloc_top.fuzz_realloc_holds fx rc SKB B (H_fs_img_facts rc) fsB_shadow_syms ENV TfibBU_syms
    (@FSRealloc_top.fs_arealloc_BU fx rc TfibBU TfibBU_syms (H_alloc_raw rc fx) (H_dealloc_raw rc fx)) (H_malloc rc fx)).
Qed.
Lemma fsB_put : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @put_spec fx rc SKB B tfibsegs.
Proof. intros rc fx. exact (@FSW_put_holds.put_holds fx rc SKB B fsB_shadow_syms (H_memcpy rc fx) (H_fs_img_facts rc) (fsB_fuzz_realloc rc fx)). Qed.
Lemma fsB_strdup : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @fuzz_strdup_spec fx rc SKB tfibsegs B.
Proof. intros rc fx. exact (@FSW_strdup.fuzz_strdup_holds fx rc SKB B (H_fs_img_facts rc) (H_strlen rc fx) (H_memcpy rc fx) (fsB_fuzz_malloc rc fx)). Qed.
Lemma fsB_pj_get : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @pj_get_spec fx rc SKB tfibsegs B.
Proof. intros rc fx. exact (@FSW_pj_get.pj_get_holds fx rc SKB B (H_fs_img_facts rc) fsB_shadow_syms (H_strcmp rc fx)). Qed.
(* parse_value at nesting 0: a Theorem Labs lane's lib/B/FSW_reader_top.v reader_parse_value_0 (the descending-depth
   composition of S0's parse_value_holds / parse_items_holds), with parse_string (FSW_parse_string.parse_string_proof),
   grow (FSW_grow_holds) and skip_ws from S0 *)
Lemma H_parse_value : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @parse_value_spec fx rc SKB tfibsegs B 0%nat.
Proof.
  intros rc fx.
  exact (@FSW_reader_top.reader_parse_value_0 fx rc SKB TfibBU fsB_shadow_syms
    (@FSW_skip_ws.skip_ws_holds fx rc SKB B fsB_shadow_syms)
    (@FSW_grow_holds.grow_holds fx rc SKB B fsB_shadow_syms (fsB_fuzz_realloc rc fx))
    (@FSW_parse_string.parse_string_proof fx rc SKB B fsB_shadow_syms (fsB_fuzz_malloc rc fx))
    (H_memset rc fx) (H_fs_img_facts rc) GUAR UCELL (conj pc_stack_malloc_0_BU (H_stack_malloc_0 rc fx))
    ENV ML SMP ASF (@FSW_entry_link.fe_frame_flag_law fx rc TfibBU)).
Qed.
Lemma fsB_check_round_trip : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @check_round_trip_spec fx rc SKB tfibsegs B.
Proof.
  intros rc fx.
  pose proof (fsB_put rc fx) as HPUT.
  pose proof (@ZZpsfinal.ps_put_string_spec fx rc SKB B HPUT fsB_shadow_syms ENV ML SMP (H_stack_malloc_0 rc fx)
    pc_stack_malloc_0_BU ASF (@FSW_entry_link.fe_frame_flag_law fx rc TfibBU) GUAR UCELL (H_fs_img_facts rc)) as HPS.
  pose proof (@FSW_indent.indent_proof fx rc SKB B (H_fs_img_facts rc) HPUT) as HIND.
  pose proof (@FSW_write_value.write_value_holds fx rc SKB B fsB_shadow_syms (H_fs_img_facts rc) HPUT HPS HIND
    (H_strlen rc fx) 0%nat) as HWV.
  exact (@FSH_crt_chain.check_round_trip_holds fx rc SKB B (H_fs_img_facts rc)
    (@FSW_pj_write.pjw_pj_write_spec fx rc SKB B (H_memset rc fx) HWV HPUT (fsB_fuzz_free rc fx) (H_fs_img_facts rc))
    (@FSW_pj_parse.pj_parse_holds fx rc SKB B (H_memset rc fx) (H_parse_value rc fx)
       (@FSW_skip_ws.skip_ws_holds fx rc SKB B fsB_shadow_syms))
    (fsB_pj_get rc fx)
    (@FSW_pj_get_str.pj_get_str_holds fx rc SKB B fsB_shadow_syms (fsB_pj_get rc fx))
    (H_decode_ff rc fx) (fsB_fuzz_free rc fx) (H_strlen rc fx) (H_strcmp rc fx) (H_bcmp rc fx) (H_set_shadow_f5 rc fx)
    (conj pc_wrap_malloc_BU (H_malloc rc fx)) (conj pc_wrap_free_BU (H_free rc fx))
    (conj pc_stack_malloc_3_BU (H_stack_malloc_3 rc fx)) ENV
    (@FSW_pj_free_top.pj_free_holds fx rc SKB B fsB_shadow_syms (fsB_fuzz_free rc fx) (H_memset rc fx) 0%nat)
    (@FSW_pj_string.pj_string_holds fx rc SKB B (H_fs_img_facts rc) fsB_shadow_syms (H_memset rc fx) (fsB_strdup rc fx))
    (@FSW_pj_set_holds.pj_set_holds_s0 fx rc SKB B fsB_shadow_syms (H_fs_img_facts rc) (fsB_pj_get rc fx)
       (fsB_fuzz_realloc rc fx) (fsB_strdup rc fx) (H_memcpy rc fx) (H_memset rc fx))
    (@FSW_pj_object.pj_object_holds fx rc SKB B fsB_shadow_syms (H_memset rc fx))
    ML ASF (@FSW_entry_link.fe_frame_flag_law fx rc TfibBU) fsB_shadow_syms GUAR UCELL (H_encode rc fx)).
Qed.

(* ---- composition ---- *)
(* image B's program part: ENTRY's proof (lib/B/FSW_entry.v fs_entry_proof) applied to its premises at TFIB_T_B's
   library shape *)
Lemma fs_lib_x_B : forall rc : YM05.RunCeil,
  @fs_lib_contract_x_all rc LSB SKB B ameter_triv XL0 XL0 YE2k.tfib_K.
Proof.
  intros rc fx. apply (@FSW_entry.fs_entry_proof fx rc LSB B).
  - intros pl fs K. reflexivity.
  - exact fsB_tfib_lib.
  - exact TfibBU_syms.
  - exact (fsB_entry_rt rc fx).
  - exact (H_fs_img_facts rc).
  - exact {| en_no_overread := fsB_check_no_overread rc fx; en_alloc_live := fsB_fuzz_alloc_live rc fx;
             en_alloc_peak_reset := fsB_fuzz_alloc_peak_reset rc fx; en_decode := H_decode_ff rc fx;
             en_alloc_peak := fsB_fuzz_alloc_peak rc fx; en_bounded_alloc := fsB_check_bounded_alloc rc fx;
             en_as_written := fsB_check_as_written rc fx; en_round_trip := fsB_check_round_trip rc fx;
             en_reject_clean := fsB_check_reject_clean rc fx; en_starved := fsB_check_reject_clean_starved rc fx;
             en_free := fsB_fuzz_free rc fx |}.
Qed.

(* the driver's indexed form at LI_fs (lib/B/FSTfibBridge.v fs_lib_xI_all) *)
Lemma LIBX_ALL_B : forall rc : YM05.RunCeil,
  @tfib_lib_contract_xI_all rc LSB B ameter_triv XL0 XL0 FS_RLO FS_RHI LI_fs.
Proof. intros rc. exact (@fs_lib_xI_all rc LSB B ameter_triv XL0 XL0 (fs_lib_x_B rc)). Qed.

(* TFIB_T_B from the LI driver (a Theorem Labs lane's lib/B/FSTfibPartsB.v TFIB_T_of_lib_B) at LI := LI_fs, with
   LIBX := LIBX_ALL_B, LIK := LIK_fs, LI0 := LI0_fs (lib/B/FSTfibBridge.v, a Theorem Labs lane); FSTfibPartsB's restatement of
   TFIB_T_B is COMP-B's lib/B/FSTfibB.v:37 by conversion *)
Theorem fsB_TFIB_T : TFIB_T_B.
Proof. exact (FSTfibPartsB.TFIB_T_of_lib_B LI_fs LIBX_ALL_B LIK_fs LI0_fs). Qed.

(* the two asan_ubsan statements of record, through COMP-B's theorems (lib/B/FSTopB.v) *)
Theorem fs_asan_ubsan_agrees_closed : Statements.asan_ubsan_agrees.
Proof. exact (FSTopB.fs_asan_ubsan_agrees_of_tfib fsB_TFIB_T). Qed.
Theorem fs_asan_ubsan_halts_closed : Statements.asan_ubsan_halts.
Proof. exact (FSTopB.fs_asan_ubsan_halts_of_tfib fsB_TFIB_T). Qed.

End fs_close_B.

(* About / Print Assumptions of the two tops: lib/B/FSCloseB_assumptions.v (committed probe, built by the gates). *)
