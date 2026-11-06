(* fuzz_state, image A (fs.asan): the CLOSING SIDE of the two asan statements of record, Statements.asan_agrees and
   Statements.asan_halts, from NAMED Section hypotheses (rule 24: no function proved; this file is assembly only, no
   walk is written here).

   Templates: a Theorem Labs lane's lib/A/FMTfibParts.v (a working branch aeb12aaa12b; the decomposition and the row
   names) and fuzz_pcap's lib/A/PcapClose.v (a working branch 86b0e893fe8; the composition for parts whose
   proofs are not done yet). The decomposition is fm's:
     TFIB_T  <-  lib/A/FSTfibParts.v:123 TFIB_T_of_lib at LI := LI_fs: the start-up, HS_ok_open, the driver main, the
                 allocator, the driver's memcpy, the read checks and the stdio sites are PROVED lemmas of the relocated
                 core there; its three premises are the program part LIBX (the harness contract in the driver's INDEXED
                 form, call ci needs LI ci and gives LI (ci + 1)) and the two library-invariant facts LIK / LI0.
     LIBX    <-  lib/A/FSTfibBridge.v:125 fs_lib_xI_all applied to fs's program part fs_lib_x (S0's fs_lib_contract_x,
                 the live / cnt form), and fs_lib_x <- ENTRY's lib/A/FSW_entry.v:36 fs_entry_proof (the walk of
                 LLVMFuzzerTestOneInput, lib/A/FSH_Fn_entry.v:106 fs_entry_goal) applied to its premises; the callee specs
                 among them are S0's proved walks where S0 has one.
     LIK, LI0 <- lib/A/FSTfibBridge.v:103 LIK_fs and :114 LI0_fs.

   REBASED onto S0 a working branch 3ba29e4479d (the CTX drop, walk folds 1-5, the stack-budget candidate,
   image A's RUNTIME + ALLOCATOR set, strlen / memchr / strcmp / bcmp / memcpy / memset / set_shadow_f5, the narrowed
   crt walk, FSImgFacts, encode, the FsRt narrowings of pj_parse / pj_set and of a Theorem Labs lane, parse_value
   A, and this file at ee384876041) plus a working branch 1450ea6d4fa (A/FSW_reader_top.v
   reader_parse_value_0). Recorded before on S0 834df0ca5d9 (a97ae39683c), f0e2574c33c (1469f04666b, pushed as
   a working branch), 76fc4284839 (f3acbadcba3) and 1745d9d1573 + a Theorem Labs lane.
   What changed against the old file (a working branch cade049876a):
   - DELETED the local copies of S0 statements: tfib_lib_contract_xI / _all (now A/ACfn.v), lib_inv_stable /
     lib_inv_init (now A/AD1w.v), fs_LI and fs_lib_xI_of_x (now A/FSTfibBridge.v LI_fs / fs_lib_xI_all), drv_mainX_stmt,
     fs_drv_contract, HS_okA, startup_T1A, HS_ok_openA, DRV_MAINX, fs_srealizesX_rc and the local TFIB_T_of_lib (all
     inside A/FSTfibParts.v TFIB_T_of_lib now).
   - B is A/AD2l.v:15 TfibB (no Section variable; A/ACej.v and A/AD2l.v build on S0).
   - CTX drop: the callee specs take no CTX list (no site_ctx); fs_entry_goal has no FsEntryCtx / FsEntryTraces.
   - Rows CLOSED (fs-OBLIGATIONS.md):
       A0  B                     := TfibB (A/AD2l.v:15)
       A1  H_tfib_startup_T1     inside FSTfibParts.TFIB_T_of_lib (A/AD1q.v tfib_srealizesX over the start-up)
       A2  HB                    := TfibB_syms (A/AD2l.v:73)
       A3  H_strlen              lemma fs_strlen <- FSrtcells.fs_strlen_realizesU_s (A/FSrtcells.v:85, strfold)
       A4  H_strcmp              lemma fs_strcmp <- StrcmpU.fs_strcmp_realizesU (A/Rt/StrcmpU.v:581)
       A5  H_memchr              lemma fs_memchr <- FSrtcells.fs_memchr_realizesU_s (A/FSrtcells.v:92, strfold)
       A7  H_bcmp                FSrtA_fields.rtA_bcmp (A/FSrtA_fields.v:49)
       A8  H_memcpy              lemma fs_memcpy <- FSupoisonAsanC.tfib_asan_memcpy_realizesU (A/FSupoisonAsanC.v:5903)
       A9  H_memset              lemma fs_memset <- FSxMset.tfib_asan_memset_realizesU (A/FSxMset.v:2230)
       A10 H_set_shadow_f5       lemma fs_set_shadow_f5 <- FSxSS.set_shadow_f5_contractU_x (A/FSxSS.v:57)
       A11 H_malloc              lemma fs_malloc <- FSupoisonAllocM.tfib_amalloc_realizesU (A/FSupoisonAllocM.v:34)
       A12 H_free                lemma fs_free <- FSupoisonAllocF.afree_realizes_allU (A/FSupoisonAllocF.v:88)
       A13 H_stack_malloc_0      lemma fs_stack_malloc_0 <- FSxU.stack_malloc0_contractU_x (A/FSxU.v:21)
       A14 H_stack_malloc_1      lemma fs_stack_malloc_1 <- FSxU.stack_malloc1_contractU_x (A/FSxU.v:30)
       A15 H_stack_malloc_3      lemma fs_stack_malloc_3 <- FSxU.stack_malloc3_contractU_x (A/FSxU.v:39)
       A16 H_stack_free          lemma fs_stack_free <- YG0t.astack_free_law_ok (lib/Reusable/YG0t.v:474)
       A17 H_pc_stack_malloc_0   lemma pc_stack_malloc_0_B, by computation (S0's A/AF0l.v:12 is fs's class map {0,1,3})
       A18 H_pc_stack_malloc_3   lemma pc_stack_malloc_3_B, the same
       A19 AICPY                 inside FSTfibParts.TFIB_T_of_lib (A/AD2m.v tfib_AICPY)
       A20 H_fs_img_facts        FSImgFacts.fs_img_facts_TfibB (A/FSImgFacts.v:339, a working branch 67d03ac00ad)
       A21 H_check_no_overread   FSW_check_no_overread_top.check_no_overread_ok (A/FSW_check_no_overread_top.v:1499)
       A22 H_fuzz_alloc_live     FSW_alloc_counters.fuzz_alloc_live_ok (A/FSW_alloc_counters.v:199)
       A23 H_fuzz_alloc_peak_reset  FSW_alloc_counters.fuzz_alloc_peak_reset_ok (:620)
       A24 H_decode_ff           FSW_dec_fin.decode_ff_holds (A/FSW_dec_fin.v:43)
       A25 H_fuzz_alloc_peak     FSW_alloc_counters.fuzz_alloc_peak_ok (:225)
       A26 H_check_bounded_alloc FSH_check_bounded_alloc.check_bounded_alloc_proof (A/FSH_check_bounded_alloc.v:58)
       A27 H_check_as_written    FSH_check_as_written.check_as_written_proof (A/FSH_check_as_written.v:297)
       A28 H_check_round_trip    FSH_crt_chain.check_round_trip_holds (A/FSH_crt_chain.v:117, a working branch), with
                                 its callees pj_write / pj_parse / pj_get / pj_get_str / pj_free / pj_string / pj_set /
                                 pj_object, write_value, put, put_string, indent, fuzz_strdup and fuzz_realloc from
                                 their S0 proofs (lemmas fs_pj_* .. fs_check_round_trip)
       A29 H_check_reject_clean  FSH_check_reject_clean.check_reject_clean_proof (A/FSH_check_reject_clean.v:78)
       A30 H_check_reject_clean_starved  FSH_check_reject_clean_starved.check_reject_clean_starved_proof (:1265)
       A31 H_fuzz_free           FSW_fuzz_free.fuzz_free_holds (A/FSW_fuzz_free.v:798)
       A32 H_entry               FSW_entry.fs_entry_proof (A/FSW_entry.v:36)
       A33 LIK                   FSTfibBridge.LIK_fs (A/FSTfibBridge.v:103)
       A34 LI0                   FSTfibBridge.LI0_fs (A/FSTfibBridge.v:114)
       A35 H_tfib_drv_main       inside FSTfibParts.TFIB_T_of_lib (A/AD1q.v tfib_srealizesX, all driver parts proved)
     The callee proofs' own Section premises are discharged here, not assumed: past_nul_spec by FSW_past_nul.past_nul_ok
     (A/FSW_past_nul.v:820), fuzz_malloc_spec by FSW_fuzz_malloc.fuzz_malloc_holds (A/FSW_fuzz_malloc.v:975),
     fuzz_alloc_fail_spec by FSW_alloc_counters.fuzz_alloc_fail_ok (:635), __asan_unpoison_memory_region by
     FSpoisonW.tfib_unpoison16 (A/FSpoisonW.v:396), FsShadowSyms by FSrtcellsS0.fs_shadow_syms_of (A/FSrtcellsS0.v:41),
     api_env / model_laws / the shadow and use-after-return cells / the stack_malloc progress law by FSW_entry_link's
     fe_api_env / fe_model_laws / fe_tl_got_shadow / fe_tl_shadow_cell / fe_tl_got_uar / fe_tl_uar_cell /
     fe_stack_malloc_progress (A/FSW_entry_link.v:26-50), all at TfibB from fs_tfib_lib; AR_laws by YG0q.AR_laws_ok,
     the depot hash by eq_refl.
     The entry premise ACeg.TfibLib TfibB is the lemma fs_tfib_lib below (port of cgif_file_fuzzer lib/A/ACed.v:40-56
     tfibX_lib, c8557374ad2e, with fs's errno / segment / owned-static / lib_const numbers from S0's A/AF0m.v and
     A/ACeg.v).
   - FSTfibParts.FSTFIB_T is COMP-A's FSTfib.TFIB_T: lemma FSTFIB_T_eq (reflexivity).
   No named hypothesis left (every runtime premise and every callee spec has a theorem): H_arealloc
   (A/FSupoisonRealloc.v:27 FS_AREALLOC_AU tfibsegs TfibB (as_universe TfibB), route 1), the premise of
   fuzz_realloc_holds, is the lemma H_arealloc below, A/FSReallocAGfin.v fs_arealloc_AU_TfibB_final. parse_value at
   depth 0 (pj_parse_holds' premise) is FSW_reader_top.reader_parse_value_0 (lemma fs_parse_value); encode (starved's
   and crt's ENC) is FSW_preset_base64_encode.encode_proof (lemma fs_encode).

   Sink head: every spec hypothesis takes AE2k.tfib_sink_head by position (`@`); S0's A/FSH_Harness.v:32 removes it from
   instance search, and nothing here leaves SK to inference.
   Audit: About and Print Assumptions of the two tops and Print Statements.asan_halts are in lib/A/FSClose_assumptions.v
   (owner ruling 13:25Z), not here: Print Assumptions walks the whole proof cone and is the slow part of the build.
   The row table (statement location, owner lane, state, proof sha) is fuzz_state's obligations table, kept by its
   owner a Theorem Labs lane. *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_state Require Statements.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
  YK11 YK0s YK15 YK18 YK09 YK0c YK0e YA01 YA0c YA0e YA02 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
  YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YCbp YC5d YI00 YI04 YI16 YK06 YE00 YE01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import ZTraceSpec AgreeShape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AF0l AF0m ACfn AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AE2k SetShadowDefU ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
  FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Harness.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
  FSH_Fn_alloc FSH_Fn_checks FSH_Fn_cno FSH_Fn_crt FSH_Fn_writer FSH_Fn_entry.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSTfibBridge FSTfib.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSTfibParts FSTop FSW_entry FSW_entry_link FSrtcellsS0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require
  FSW_alloc_counters FSW_dec_fin FSH_check_bounded_alloc FSH_check_as_written FSH_check_reject_clean
  FSH_check_reject_clean_starved FSW_fuzz_free FSW_fuzz_malloc FSpoisonW FSW_past_nul FSW_check_no_overread_top.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require
  FSxSS FSxU FSupoisonAllocM FSupoisonAllocF FSrtA_fields FSImgFacts FSrtcells FSupoisonAsanC FSxMset.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require
  FSH_Fn_reader FSupoisonRealloc FSH_crt_chain FSW_pj_write FSW_pj_parse FSW_pj_get FSW_pj_get_str FSW_pj_free_top
  FSW_pj_string FSW_pj_object FSW_realloc_top FSW_strdup FSW_put_holds ZZpsfinal FSW_indent ZZwv_arm
  FSW_preset_base64_encode FSReallocAGfin.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSW_pj_set_holds FSW_grow_holds.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Rt Require StrcmpU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSW_parse_string FSW_reader_top.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the library shape of TFIB_T (lib/A/FSTfib.v:26) and of FSTfibParts.TFIB_T_of_lib (A/FSTfibParts.v:75) *)
Local Abbreviation LSA := (ag_shape checksum_shape).

(* ===================================================================================================== *)
(* Facts about TfibB proved by computation                                                                 *)
(* ===================================================================================================== *)

(* the entry premise ACeg.TfibLib TfibB (A/ACeg.v:28). Port-from: cgif_file_fuzzer lib/A/ACed.v:40-56 tfibX_lib
   (c8557374ad2e), at fs's numbers: lib_const_addr is fs's one constant word [0x10320, 0x10328) (A/ACeg.v:27), errno
   is TFIB_ERRNO 0x5dae8c (A/AF0m.v:21) in fs's fourth load segment (the .data / .bss segment from 0xa1400), the owned
   statics are A/AF0m.v:1147 Tfib_owned_static, gp is TFIB_GP 0x10800 (A/AF0m.v:20). *)
Lemma fs_tfib_lib_consts_chk :
  forallb (fun r => (fst r + snd r <=? 0x10320) || (0x10328 <=? fst r))%bool Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

Theorem fs_tfib_lib : ACeg.TfibLib TfibB.
Proof.
constructor; try reflexivity.
- cbn [as_errno TfibB]. unfold TFIB_ERRNO, kLowMemEnd. lia.
- intros a Ha. cbn [as_errno TfibB] in Ha. unfold TFIB_ERRNO in Ha. unfold in_img.
  assert (Hb : match nth_error tfibsegs 3 with
               | Some s => ((Z.of_N (seg_base s) <=? 0x5dae8c) && (0x5dae90 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool
               | None => false end = true) by (vm_compute; reflexivity).
  revert Hb. destruct (nth_error tfibsegs 3) as [sg|] eqn:E; intros Hb; [| discriminate Hb].
  cbv beta iota in Hb. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact (nth_error_In _ 3 E) | lia].
- intros a Ha. cbn [as_owned_static as_errno TfibB]. unfold TFIB_ERRNO. unfold ACeg.lib_const_addr in Ha. split; [|lia].
  intros HE. apply Exists_exists in HE as (r & Hr & [H1 H2]).
  pose proof (proj1 (forallb_forall _ _) fs_tfib_lib_consts_chk r Hr) as Hb. cbn beta in Hb.
  apply Bool.orb_prop in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
- cbn [as_gp TfibB]. unfold TFIB_GP. lia.
Qed.

(* rows A17 / A18 (FsRt's two class pcs, A/FSH_Rt.v:124, :126), and the other three pcs FsRt / FsEntryRt pin: S0's
   Tfib_code (A/AF0l.v:9-16) through ts_code of TfibB_syms *)
Lemma pc_stack_malloc_0_B : pc_stack_malloc (as_code TfibB) 0 = PC_stack_malloc_0.
Proof. rewrite (ts_code _ TfibB_syms). reflexivity. Qed.
Lemma pc_stack_malloc_3_B : pc_stack_malloc (as_code TfibB) 3 = PC_stack_malloc_3.
Proof. rewrite (ts_code _ TfibB_syms). reflexivity. Qed.
Lemma pc_stack_malloc_1_B : pc_stack_malloc (as_code TfibB) 1 = PC_stack_malloc_1.
Proof. rewrite (ts_code _ TfibB_syms). reflexivity. Qed.
Lemma pc_wrap_malloc_B : pc_wrap_malloc (as_code TfibB) = PC_malloc.
Proof. rewrite (ts_code _ TfibB_syms). reflexivity. Qed.
Lemma pc_wrap_free_B : pc_wrap_free (as_code TfibB) = PC_free.
Proof. rewrite (ts_code _ TfibB_syms). reflexivity. Qed.
Lemma pc_asan_memcpy_B : pc_asan_memcpy (as_code TfibB) = PC_memcpy.
Proof. rewrite (ts_code _ TfibB_syms). reflexivity. Qed.

(* FSTfibParts' restatement of TFIB_T (A/FSTfibParts.v:60) is COMP-A's (A/FSTfib.v:20): A/AB1h.v's TSEGS / TPH are
   Asan.M.loaded_segments / Asan.M.phdrs *)
Lemma FSTFIB_T_eq : FSTfibParts.FSTFIB_T = TFIB_T.
Proof. reflexivity. Qed.

(* ===================================================================================================== *)
(* The closing Section: one named hypothesis per remaining part                                            *)
(* ===================================================================================================== *)
Section fs_close_A.

(* rows A0 / A2: the image record is A/AD2l.v:15 TfibB, its TfibSyms is A/AD2l.v:73 TfibB_syms *)
Local Abbreviation B := TfibB (only parsing).

(* ---- RUNTIME, U forms (S0 A/FSH_Rt.v:113-127 FsRt and A/FSH_Fn_entry.v:60-67 FsEntryRt) ----
   A6 snprintf: no hypothesis. Its only consumer was the whole FsRt record; with pj_parse_holds / pj_set_holds_s0
   narrowed in S0 1745d9d1573 and check_as_written_proof / check_reject_clean_starved_proof narrowed by
   a Theorem Labs lane (59a68c6fea6), every callee takes the FsRt fields it uses by their types, and none uses fr_snprintf. A7
   is FSrtA_fields.rtA_bcmp; A3, A4, A5, A8, A9 are the lemmas below. *)

(* ---- RUNTIME rows with a theorem: A3, A4, A5, A8, A9 and A10-A16 (strings a Theorem Labs lane, memcpy a Theorem Labs lane, memset
   a Theorem Labs lane, image A's RUNTIME + ALLOCATOR set a Theorem Labs lane). Each lemma below states the old hypothesis verbatim;
   the theorems' own premises (AR_laws, TfibSyms, TfibLib, the depot hash) are closed from YG0q.AR_laws_ok,
   TfibB_syms, fs_tfib_lib and eq_refl ---- *)
Local Abbreviation LAWS := (YG0q.AR_laws_ok tfibsegs TfibB).
(* A3: A/FSrtcells.v:85 fs_strlen_realizesU_s *)
Lemma fs_strlen : forall (rc : YM05.RunCeil) (fx : YK11.FPState), astrlen_realizesU tfibsegs B PC_strlen.
Proof. intros rc fx. exact (FSrtcells.fs_strlen_realizesU_s TfibB LAWS TfibB_syms fs_tfib_lib). Qed.
(* A5: A/FSrtcells.v:92 fs_memchr_realizesU_s *)
Lemma fs_memchr : forall (rc : YM05.RunCeil) (fx : YK11.FPState), amemchr_realizesU tfibsegs B PC_memchr.
Proof. intros rc fx. exact (FSrtcells.fs_memchr_realizesU_s TfibB LAWS TfibB_syms fs_tfib_lib). Qed.
(* A8: A/FSupoisonAsanC.v:5903 tfib_asan_memcpy_realizesU *)
Lemma fs_memcpy : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
Proof. intros rc fx. exact (FSupoisonAsanC.tfib_asan_memcpy_realizesU TfibB LAWS TfibB_syms). Qed.
(* A4: A/Rt/StrcmpU.v:581 fs_strcmp_realizesU (a Theorem Labs lane, in S0 8fee0cc526f) *)
Lemma fs_strcmp : forall (rc : YM05.RunCeil) (fx : YK11.FPState), astrcmp_realizesU tfibsegs B PC_strcmp.
Proof. intros rc fx. exact (StrcmpU.fs_strcmp_realizesU TfibB LAWS TfibB_syms). Qed.
(* A9: A/FSxMset.v:2230 tfib_asan_memset_realizesU *)
Lemma fs_memset : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.
Proof. intros rc fx. exact (FSxMset.tfib_asan_memset_realizesU TfibB LAWS TfibB_syms). Qed.
(* A10: A/FSxSS.v:57 set_shadow_f5_contractU_x *)
Lemma fs_set_shadow_f5 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  SetShadowDefU.aset_shadow_realizesU tfibsegs B PC_set_shadow_f5 0xf5.
Proof. intros rc fx. exact (FSxSS.set_shadow_f5_contractU_x TfibB LAWS TfibB_syms). Qed.
(* A11: A/FSupoisonAllocM.v:34 tfib_amalloc_realizesU *)
Lemma fs_malloc : forall (rc : YM05.RunCeil) (fx : YK11.FPState), FSupoisonU.amalloc_realizesU tfibsegs B.
Proof. intros rc fx. exact (FSupoisonAllocM.tfib_amalloc_realizesU TfibB TfibB_syms (fun t => eq_refl)). Qed.
(* A12: A/FSupoisonAllocF.v:88 afree_realizes_allU *)
Lemma fs_free : forall (rc : YM05.RunCeil) (fx : YK11.FPState), FSupoisonU.afree_realizesU tfibsegs B.
Proof. intros rc fx. exact (FSupoisonAllocF.afree_realizes_allU TfibB LAWS TfibB_syms (fun t => eq_refl)). Qed.
(* A13: A/FSxU.v:21 stack_malloc0_contractU_x *)
Lemma fs_stack_malloc_0 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), FSupoisonU.astack_malloc_realizesU tfibsegs B 0.
Proof. intros rc fx. exact (FSxU.stack_malloc0_contractU_x TfibB LAWS TfibB_syms). Qed.
(* A14: A/FSxU.v:30 stack_malloc1_contractU_x *)
Lemma fs_stack_malloc_1 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), FSupoisonU.astack_malloc_realizesU tfibsegs B 1.
Proof. intros rc fx. exact (FSxU.stack_malloc1_contractU_x TfibB LAWS TfibB_syms). Qed.
(* A15: A/FSxU.v:39 stack_malloc3_contractU_x *)
Lemma fs_stack_malloc_3 : forall (rc : YM05.RunCeil) (fx : YK11.FPState), FSupoisonU.astack_malloc_realizesU tfibsegs B 3.
Proof. intros rc fx. exact (FSxU.stack_malloc3_contractU_x TfibB LAWS TfibB_syms). Qed.
(* A16: lib/Reusable/YG0t.v:474 astack_free_law_ok (every B) *)
Lemma fs_stack_free : forall (rc : YM05.RunCeil) (fx : YK11.FPState), astack_free_law tfibsegs B.
Proof. intros rc fx. exact (YG0t.astack_free_law_ok tfibsegs TfibB). Qed.

(* ---- PROGRAM PART: the callee specs with no proof on S0 ---- *)
(* A20 is proved: A/FSImgFacts.v:339 fs_img_facts_TfibB *)
Local Abbreviation IMG := FSImgFacts.fs_img_facts_TfibB.
(* H_arealloc: fs's realloc runtime contract (A/FSupoisonRealloc.v:27 FS_AREALLOC_AU), the premise of fuzz_realloc_holds
   (A/FSW_realloc_top.v:48); route 1's closed form A/FSReallocAGfin.v fs_arealloc_AU_TfibB_final *)
Lemma H_arealloc : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @FSupoisonRealloc.FS_AREALLOC_AU fx rc tfibsegs B (as_universe B).
Proof. intros rc fx. exact (@FSReallocAGfin.fs_arealloc_AU_TfibB_final fx rc). Qed.

(* ---- the entry's runtime record, from rows A5, A8, A11-A13, A16 ---- *)
(* A/FSH_Fn_entry.v:60 FsEntryRt: the entry's own runtime sites (fe_memcpy at __asan_memcpy's pc through TfibB_syms) *)
Lemma fs_entry_rt : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @FsEntryRt fx rc tfibsegs B.
Proof.
  intros rc fx.
  refine {| fe_stack_malloc_0 := fs_stack_malloc_0 rc fx; fe_stack_free := fs_stack_free rc fx;
            fe_malloc := fs_malloc rc fx; fe_free := fs_free rc fx; fe_memcpy := _; fe_memchr := fs_memchr rc fx |}.
  rewrite pc_asan_memcpy_B. exact (fs_memcpy rc fx).
Qed.

(* ---- the callee proofs of S0, at TfibB and AE2k.tfib_sink_head (signatures checked with About). Their own Section
   premises are closed here from fs_tfib_lib / TfibB_syms, never re-typed: ---- *)
(* FsShadowSyms (A/FSrtcellsS0.v:41) *)
Local Abbreviation SHS := (FSrtcellsS0.fs_shadow_syms_of TfibB fs_tfib_lib).
(* api_env, model_laws, the shadow / use-after-return cells and the stack_malloc progress law
   (A/FSW_entry_link.v:26-50) *)
Local Abbreviation ENV := (FSW_entry_link.fe_api_env TfibB fs_tfib_lib).
Local Abbreviation ML := (FSW_entry_link.fe_model_laws TfibB fs_tfib_lib).
Local Abbreviation GSH := (FSW_entry_link.fe_tl_got_shadow TfibB fs_tfib_lib).
Local Abbreviation CSH := (FSW_entry_link.fe_tl_shadow_cell TfibB fs_tfib_lib).
Local Abbreviation GUAR := (FSW_entry_link.fe_tl_got_uar TfibB fs_tfib_lib).
Local Abbreviation UCELL := (FSW_entry_link.fe_tl_uar_cell TfibB fs_tfib_lib).
Local Abbreviation SMP := (FSW_entry_link.fe_stack_malloc_progress TfibB).

(* A22 *)
Lemma fs_fuzz_alloc_live : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @fuzz_alloc_live_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof. intros rc fx. exact (@FSW_alloc_counters.fuzz_alloc_live_ok fx rc AE2k.tfib_sink_head B). Qed.
(* A25 *)
Lemma fs_fuzz_alloc_peak : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @fuzz_alloc_peak_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof. intros rc fx. exact (@FSW_alloc_counters.fuzz_alloc_peak_ok fx rc AE2k.tfib_sink_head B). Qed.
(* A23 *)
Lemma fs_fuzz_alloc_peak_reset : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @fuzz_alloc_peak_reset_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof.
  intros rc fx. exact (@FSW_alloc_counters.fuzz_alloc_peak_reset_ok fx rc AE2k.tfib_sink_head B (IMG rc)).
Qed.
(* fuzz_alloc_fail (premise FAIL of check_reject_clean_starved_proof) *)
Lemma fs_fuzz_alloc_fail : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @fuzz_alloc_fail_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof.
  intros rc fx. exact (@FSW_alloc_counters.fuzz_alloc_fail_ok fx rc AE2k.tfib_sink_head B (IMG rc)).
Qed.
(* A26 *)
Lemma fs_check_bounded_alloc : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @check_bounded_alloc_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof. intros rc fx. exact (@FSH_check_bounded_alloc.check_bounded_alloc_proof fx rc AE2k.tfib_sink_head B). Qed.
(* A29 *)
Lemma fs_check_reject_clean : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @check_reject_clean_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof. intros rc fx. exact (@FSH_check_reject_clean.check_reject_clean_proof fx rc AE2k.tfib_sink_head B). Qed.
(* A27 *)
Lemma fs_check_as_written : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @check_as_written_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof.
  intros rc fx.
  exact (@FSH_check_as_written.check_as_written_proof fx rc AE2k.tfib_sink_head B
    (IMG rc) SHS (fs_strlen rc fx) (FSrtA_fields.rtA_bcmp rc fx) (conj pc_wrap_malloc_B (fs_malloc rc fx))
    (conj pc_wrap_free_B (fs_free rc fx)) ENV ML).
Qed.
(* fuzz_malloc (premise of decode_ff_holds) *)
Lemma fs_fuzz_malloc : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @fuzz_malloc_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof.
  intros rc fx.
  exact (@FSW_fuzz_malloc.fuzz_malloc_holds fx rc AE2k.tfib_sink_head B
    (IMG rc) SHS TfibB_syms ENV (fs_malloc rc fx)).
Qed.
(* encode (Section premise ENC of check_reject_clean_starved_proof and check_round_trip_holds):
   A/FSW_preset_base64_encode.v:4551 encode_proof *)
Lemma fs_encode : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @encode_spec fx rc AE2k.tfib_sink_head B tfibsegs.
Proof.
  intros rc fx.
  exact (@FSW_preset_base64_encode.encode_proof fx rc AE2k.tfib_sink_head TfibB SHS (IMG rc) (fs_fuzz_malloc rc fx)).
Qed.
(* A31; its premise FS_AUNPOISON is FSpoisonW.tfib_unpoison16 (UP_ENTRY = FSH_Base.PC_unpoison, A/FSpoisonR.v:47) *)
Lemma fs_fuzz_free : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @fuzz_free_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof.
  intros rc fx.
  exact (@FSW_fuzz_free.fuzz_free_holds fx rc AE2k.tfib_sink_head B
    (IMG rc) SHS ENV ML (conj pc_wrap_free_B (fs_free rc fx))
    (@FSpoisonW.tfib_unpoison16 fx rc B LAWS TfibB_syms)).
Qed.
(* A24 *)
Lemma fs_decode_ff : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @decode_spec_ff fx rc AE2k.tfib_sink_head B tfibsegs.
Proof.
  intros rc fx.
  exact (@FSW_dec_fin.decode_ff_holds fx rc AE2k.tfib_sink_head B
    SHS (IMG rc) (fs_strlen rc fx) (fs_memchr rc fx) (fs_fuzz_malloc rc fx) (fs_fuzz_free rc fx)).
Qed.
(* A30 *)
Lemma fs_check_reject_clean_starved : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @check_reject_clean_starved_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof.
  intros rc fx.
  exact (@FSH_check_reject_clean_starved.check_reject_clean_starved_proof fx rc AE2k.tfib_sink_head B
    (IMG rc) SHS GUAR UCELL ENV ML (conj pc_stack_malloc_0_B (fs_stack_malloc_0 rc fx)) (fs_fuzz_alloc_live rc fx)
    (fs_fuzz_alloc_fail rc fx)
    (fs_check_reject_clean rc fx) (fs_decode_ff rc fx) (fs_encode rc fx)).
Qed.
(* past_nul (Section premise PN of check_no_overread_ok) *)
Lemma fs_past_nul : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @past_nul_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof.
  intros rc fx.
  exact (@FSW_past_nul.past_nul_ok fx rc B (IMG rc) GSH CSH ENV ML
    (conj pc_wrap_malloc_B (fs_malloc rc fx)) (fs_memcpy rc fx) (fs_memset rc fx)).
Qed.
(* A21 *)
Lemma fs_check_no_overread : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @check_no_overread_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof.
  intros rc fx.
  exact (@FSW_check_no_overread_top.check_no_overread_ok fx rc B
    (fs_past_nul rc fx) (fs_decode_ff rc fx) (fs_fuzz_free rc fx) (IMG rc) GSH CSH GUAR UCELL
    pc_stack_malloc_1_B (fs_stack_malloc_1 rc fx) SMP ENV ML (fs_malloc rc fx) pc_wrap_malloc_B
    (fs_memcpy rc fx) (fs_memset rc fx) (FSrtA_fields.rtA_bcmp rc fx) (fs_free rc fx) pc_wrap_free_B).
Qed.

(* ---- row A28: check_round_trip (A/FSH_crt_chain.v:117 check_round_trip_holds, a working branch) and
   the reader / writer / allocator callee proofs it takes, all of S0, at TfibB and AE2k.tfib_sink_head ---- *)
Lemma fs_fuzz_realloc : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @fuzz_realloc_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof.
  intros rc fx.
  exact (@FSW_realloc_top.fuzz_realloc_holds fx rc AE2k.tfib_sink_head B (IMG rc) SHS ENV TfibB_syms
    (H_arealloc rc fx) (fs_fuzz_malloc rc fx)).
Qed.
Lemma fs_fuzz_strdup : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @fuzz_strdup_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof.
  intros rc fx.
  exact (@FSW_strdup.fuzz_strdup_holds fx rc AE2k.tfib_sink_head B (IMG rc) (fs_strlen rc fx) (fs_memcpy rc fx)
    (fs_fuzz_malloc rc fx)).
Qed.
Lemma fs_put : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @put_spec fx rc AE2k.tfib_sink_head B tfibsegs.
Proof.
  intros rc fx.
  exact (@FSW_put_holds.put_holds fx rc AE2k.tfib_sink_head B SHS (fs_memcpy rc fx) (IMG rc) (fs_fuzz_realloc rc fx)).
Qed.
Lemma fs_indent : forall (rc : YM05.RunCeil) (fx : YK11.FPState), @indent_spec fx rc AE2k.tfib_sink_head B tfibsegs.
Proof. intros rc fx. exact (@FSW_indent.indent_proof fx rc AE2k.tfib_sink_head B (IMG rc) (fs_put rc fx)). Qed.
Lemma fs_put_string : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @put_string_spec fx rc AE2k.tfib_sink_head B tfibsegs.
Proof.
  intros rc fx.
  exact (@ZZpsfinal.ps_put_string_spec fx rc AE2k.tfib_sink_head B (fs_put rc fx) SHS ENV ML SMP
    (fs_stack_malloc_0 rc fx) pc_stack_malloc_0_B (fs_stack_free rc fx) (@FSW_entry_link.fe_frame_flag_law fx rc TfibB)
    GUAR UCELL (IMG rc)).
Qed.
Lemma fs_write_value0 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @write_value_spec_at fx rc AE2k.tfib_sink_head B tfibsegs 0.
Proof.
  intros rc fx.
  exact (@ZZwv_arm.write_value_spec_holds fx rc AE2k.tfib_sink_head B SHS (IMG rc) (fs_put rc fx) (fs_indent rc fx)
    (fs_put_string rc fx) (fs_strlen rc fx) 0%nat).
Qed.
Lemma fs_pj_write : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @pj_write_spec fx rc AE2k.tfib_sink_head B tfibsegs.
Proof.
  intros rc fx.
  exact (@FSW_pj_write.pjw_pj_write_spec fx rc AE2k.tfib_sink_head B (fs_memset rc fx) (fs_write_value0 rc fx)
    (fs_put rc fx) (fs_fuzz_free rc fx) (IMG rc)).
Qed.
(* parse_value at depth 0 (premise PV of pj_parse_holds): A/FSW_reader_top.v:71 reader_parse_value_0 (a Theorem Labs lane,
   a working branch 1450ea6d4fa), with its callees grow (Prog/FSW_grow_holds.v grow_holds) and parse_string
   (A/FSW_parse_string.v parse_string_proof) *)
Lemma fs_grow : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @FSH_Fn_reader.grow_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof. intros rc fx. exact (@FSW_grow_holds.grow_holds fx rc AE2k.tfib_sink_head B SHS (fs_fuzz_realloc rc fx)). Qed.
Lemma fs_parse_string : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @FSH_Fn_reader.parse_string_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof.
  intros rc fx. exact (@FSW_parse_string.parse_string_proof fx rc AE2k.tfib_sink_head B SHS (fs_fuzz_malloc rc fx)).
Qed.
Lemma fs_parse_value : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @FSH_Fn_reader.parse_value_spec fx rc AE2k.tfib_sink_head tfibsegs B 0.
Proof.
  intros rc fx.
  exact (@FSW_reader_top.reader_parse_value_0 fx rc AE2k.tfib_sink_head B GUAR UCELL
    (conj pc_stack_malloc_0_B (fs_stack_malloc_0 rc fx)) ENV ML SMP (IMG rc) (fs_stack_free rc fx)
    (@FSW_entry_link.fe_frame_flag_law fx rc TfibB) SHS (fs_grow rc fx) (fs_parse_string rc fx) (fs_memset rc fx)).
Qed.
Lemma fs_pj_parse : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @FSH_Fn_reader.pj_parse_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof.
  intros rc fx.
  exact (@FSW_pj_parse.pj_parse_holds fx rc AE2k.tfib_sink_head B SHS (fs_memset rc fx) (fs_parse_value rc fx)).
Qed.
Lemma fs_pj_get : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @FSH_Fn_reader.pj_get_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof. intros rc fx. exact (@FSW_pj_get.pj_get_holds fx rc B (IMG rc) SHS (fs_strcmp rc fx)). Qed.
Lemma fs_pj_get_str : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @FSH_Fn_reader.pj_get_str_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof. intros rc fx. exact (@FSW_pj_get_str.pj_get_str_holds fx rc B SHS (fs_pj_get rc fx)). Qed.
Lemma fs_pj_free0 : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @FSH_Fn_reader.pj_free_spec fx rc AE2k.tfib_sink_head tfibsegs B 0.
Proof.
  intros rc fx.
  exact (@FSW_pj_free_top.pj_free_holds fx rc AE2k.tfib_sink_head B SHS (fs_fuzz_free rc fx) (fs_memset rc fx) 0%nat).
Qed.
Lemma fs_pj_string : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @FSH_Fn_reader.pj_string_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof.
  intros rc fx.
  exact (@FSW_pj_string.pj_string_holds fx rc AE2k.tfib_sink_head B (IMG rc) SHS (fs_memset rc fx) (fs_fuzz_strdup rc fx)).
Qed.
Lemma fs_pj_set : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @FSH_Fn_reader.pj_set_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof.
  intros rc fx.
  exact (@FSW_pj_set_holds.pj_set_holds_s0 fx rc AE2k.tfib_sink_head B SHS (IMG rc) (fs_pj_get rc fx)
    (fs_fuzz_realloc rc fx) (fs_fuzz_strdup rc fx) (fs_memcpy rc fx) (fs_memset rc fx)).
Qed.
Lemma fs_pj_object : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @FSH_Fn_reader.pj_object_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof. intros rc fx. exact (@FSW_pj_object.pj_object_holds fx rc AE2k.tfib_sink_head B SHS (fs_memset rc fx)). Qed.
(* A28 *)
Lemma fs_check_round_trip : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @check_round_trip_spec fx rc AE2k.tfib_sink_head tfibsegs B.
Proof.
  intros rc fx.
  exact (@FSH_crt_chain.check_round_trip_holds fx rc AE2k.tfib_sink_head B (IMG rc) (fs_pj_write rc fx)
    (fs_pj_parse rc fx) (fs_pj_get rc fx) (fs_pj_get_str rc fx) (fs_decode_ff rc fx) (fs_fuzz_free rc fx)
    (fs_strlen rc fx) (fs_strcmp rc fx) (FSrtA_fields.rtA_bcmp rc fx) (fs_set_shadow_f5 rc fx)
    (conj pc_wrap_malloc_B (fs_malloc rc fx)) (conj pc_wrap_free_B (fs_free rc fx))
    (conj pc_stack_malloc_3_B (fs_stack_malloc_3 rc fx)) ENV (fs_pj_free0 rc fx) (fs_pj_string rc fx)
    (fs_pj_set rc fx) (fs_pj_object rc fx) ML (fs_stack_free rc fx) (@FSW_entry_link.fe_frame_flag_law fx rc TfibB)
    SHS GUAR UCELL (fs_encode rc fx)).
Qed.

(* ---- composition ---- *)
(* row A32: fs's program part in S0's form, ENTRY's proof (A/FSW_entry.v:36 fs_entry_proof) applied to its premises at
   TFIB_T's library shape *)
Lemma fs_lib_x : forall rc : YM05.RunCeil, @fs_lib_contract_x_all rc LSA B ameter_triv XL0 XL0.
Proof.
  intros rc fx. apply (@FSW_entry.fs_entry_proof fx rc LSA AE2k.tfib_sink_head B).
  - (* LIBK (ag_shape checksum_shape) is checksum_shape's (lib/AgreeShape.v:15 ag_LIBK, lib/ZTraceSpec.v:16) *)
    intros pl fs K. reflexivity.
  - exact fs_tfib_lib.
  - exact TfibB_syms.
  - exact (fs_entry_rt rc fx).
  - exact (IMG rc).
  - exact {| en_no_overread := fs_check_no_overread rc fx; en_alloc_live := fs_fuzz_alloc_live rc fx;
             en_alloc_peak_reset := fs_fuzz_alloc_peak_reset rc fx; en_decode := fs_decode_ff rc fx;
             en_alloc_peak := fs_fuzz_alloc_peak rc fx; en_bounded_alloc := fs_check_bounded_alloc rc fx;
             en_as_written := fs_check_as_written rc fx; en_round_trip := fs_check_round_trip rc fx;
             en_reject_clean := fs_check_reject_clean rc fx; en_starved := fs_check_reject_clean_starved rc fx;
             en_free := fs_fuzz_free rc fx |}.
Qed.

(* rows A1, A19, A33, A34, A35: TFIB_T from the LI driver (A/FSTfibParts.v:123 TFIB_T_of_lib) at LI := LI_fs, with
   LIBX := fs_lib_xI_all (A/FSTfibBridge.v:125) over fs_lib_x, LIK := LIK_fs (:103), LI0 := LI0_fs (:114) *)
Theorem fs_TFIB_T : TFIB_T.
Proof.
  rewrite <- FSTFIB_T_eq.
  exact (FSTfibParts.TFIB_T_of_lib LI_fs
    (fun rc => @fs_lib_xI_all rc LSA B ameter_triv XL0 XL0 (fs_lib_x rc)) LIK_fs LI0_fs).
Qed.

(* the two asan statements of record, through COMP-A's theorems (lib/A/FSTop.v:59, :75) *)
Theorem fs_asan_agrees_closed : Statements.asan_agrees.
Proof. exact (FSTop.fs_asan_agrees_of_tfib fs_TFIB_T). Qed.
Theorem fs_asan_halts_closed : Statements.asan_halts.
Proof. exact (FSTop.fs_asan_halts_of_tfib fs_TFIB_T). Qed.
End fs_close_A.
