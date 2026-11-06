(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AD2p.v (TFIB_T_closed),
   A/AD2o.v (TFIB_T_of_partsXF) and A/ACfi.v (link_FFL, tfib_ROB) of origin/ossv/recipes c8557374ad2 for
   libreac/fuzz_boxreg's ASan build (fuzz_boxreg.asan), with fuzz_boxreg's walk layer (lib/A/Prog) in place of cgif's
   program and module paths changed. *)
(* The closing composition of fuzz_boxreg's ASan side (rule 24: no function proved; this file is assembly): TFIB_T
   (lib/A/BoxTFIB.v) and the two ASan statements asan_agrees and asan_halts, from named parts. Every part that has not
   landed is ONE named Section variable or hypothesis (rows 1-22 below; one row each in
   proofs/libreac/fuzz_boxreg/provenance/OBLIGATIONS.md with its donor line and owner); each is replaced by its proof
   when that proof plugs in unchanged. The form is the pcap closing's (a working branch lib/A/PcapClose.v).

   cgif's closing lemma is TFIB_T_closed := TFIB_T_of_partsXF wfn (program contracts) (AD2p.v:11), where
   TFIB_T_of_partsXF (AD2o.v:83) feeds the whole-run library contract LIBX to the core's tfib_srealizesX (AD1q.v:79)
   and discharges every other premise of it with a core lemma (AD2o.v:42-62). Here the relocated core (lib/A, lib/Reusable)
   does the same in lib/A/Prog/BoxCore.v (box_TFIB_T_of_lib: LIBX -> TFIB_T, box_core_A's coreA_srz), and the rows
   below whose landed proofs fit their statements are Lemmas of the same name and type, each proved by applying the
   landed theorem; the rows still open stay Section hypotheses.

   The sink head is box_sink_head, built from fuzz_boxreg.asan's own `ofl_head` (.bss 0x5f4608, 8 bytes; pinned in
   lib/A/Prog/BoxSinkPin.v); it is a Definition, never an instance, and every statement below takes it explicitly. The
   Check / Fail Check guard after row 5 and the Ltac gate at the end of the file fail to build if the plain build's
   sink head (YI5b.src0_sink_head) or sink record (YI5c.src0_sink) appears in this image's closing. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK15 YK18 YM05 YO09 YO06.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YP09 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YG05 YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import BoxShape BoxTFIB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require AsanTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaRun BoxSyms BoxList BoxAddr BoxPa BoxImg BoxBase BoxPaLib BoxFrame BoxFrameImg BoxB BoxRo BoxLibX.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
Check ReadName RangeFree LowestFree LowestFreeBase
ReacBoxregInit ReacBoxregFind ReacBoxregDeclare ReacBoxregAdd ReacBoxregSetName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require SnprintfDef StrncmpDef MemchrDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Strncmp Memchr StackMalloc3 SetShadow StrncmpViewInst.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require SnprintfBridgeFmA.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YCbp YE00 YE01 YG0t SinkInert.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require AD2l AE2k AD1u AF0w AF0q AF0m ACed.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require BoxCore BoxGShadow BoxStartup BoxLxDefs.
From OSSVerify.libreac.fuzz_boxreg Require Statements.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Export BoxCloseDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module RSTR := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt.StrncmpDef.
Module RMCH := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt.MemchrDef.
Module RSSH := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt.SetShadowDef.
Module RSTRP := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt.Strncmp.
Module RMCHP := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt.Memchr.
Module RSM3P := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt.StackMalloc3.
Module RSSHP := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt.SetShadow.
(* lib/A/Prog/BoxSinkPin.v, a frozen walk-interface file (provenance/WALK-INTERFACE.md), pins BoxClose.box_sink_head:
   the name stays here as an abbreviation of the definition, which lib/A/Prog/BoxCloseDefs.v now holds. *)
Abbreviation box_sink_head := BoxCloseDefs.box_sink_head.

Section rl. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma box_rlo_eq : BOX_RLO = pa_relro_lo (PAImg := PI_box).
Proof. reflexivity. Qed.
Lemma box_rhi_eq : BOX_RHI = pa_relro_hi (PAImg := PI_box).
Proof. reflexivity. Qed.
End rl.

(* ---- the read-only range lies below the sink's list head (cgif A/ACfi.v tfib_ROB) -------------------------------- *)
Lemma box_ro_segs_chk :
  forallb (fun s : Segment => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? BOX_OFL_HEAD))%bool
    box_segs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma box_RO : @ro_below_ofl box_segs BOX_RLO BOX_RHI box_sink_head.
Proof.
intros a [(s & Hin & Hw & Hr) | Hr]; cbn [YI16.sk_ofl_head box_sink_head].
- pose proof (proj1 (forallb_forall _ _) box_ro_segs_chk s Hin) as Hb. cbn beta in Hb. rewrite Hw in Hb.
  cbn [orb] in Hb. apply Z.leb_le in Hb. lia.
- unfold BOX_RLO, BOX_RHI, BOX_OFL_HEAD in *. lia.
Qed.

(* ---- the frame-flag law, from the allocator laws and the image's cover (cgif A/ACfi.v link_FFL) ------------------ *)
Section ff. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma box_FFL : forall B : asyms, frame_flag_lawP box_segs B.
Proof.
intros B ly S W mem md cid pos HAR Hin.
pose proof (AR_laws_ok box_segs B) as LAWS.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (box_img_cover ly S md L) as [C1 C2].
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
End ff.

Section close.
(* Row 1. BA: the image's runtime symbol record, lib/A/AD2l.v:33 TfibB (cgif A/AD2l.v:14), with its BoxregSyms fact
   AD2l.v:95 TfibB_syms. Row 2. MT: the allocator meter, Reusable/YCbp.v:17 ameter_triv (cgif's, bound at
   A/AD2o.v:45). Rows 3-4. SINKN / METAI: Reusable/YE00.v:125 asink_none and YE01.v:141 ameta_inv at box_segs and the
   core's sink record lib/A/AE2k.v:55 tfib_K, the instance lib/A/ACfn.v:60-71 gives lib/A/Prog/BoxLibX.v's two
   variables. *)
Definition BA : asyms := AD2l.TfibB.
Definition MT : ameter_ops := YCbp.ameter_triv.
Definition SINKN : (word -> option byte) -> Model -> Prop := YE00.asink_none box_segs AE2k.tfib_K.
Definition METAI : alayout -> (word -> option byte) -> Z -> Prop := YE01.ameta_inv box_segs AE2k.tfib_K.
(* Row 5. H_CORE_A: the relocated core (owned by a Theorem Labs lane), field by field. coreA_srz: lib/A/Prog/BoxCore.v
   box_TFIB_T_of_lib (lib/A/AD1q.v:198 tfib_srealizesX at TfibB); it does not use the field's first two premises
   (rows 10 and 9): the relocated core's driver takes neither. coreA_mtl / coreA_mtf: YCbp.v:22 ameter_triv_laws /
   YCbp.v:24 ameter_triv_fs_laws. coreA_need: ameter_triv's zero costs. coreA_sinkn_kept / coreA_metai_kept: YE01.v:84
   asink_none_kept / YE01.v:155 ameta_inv_kept, with the sink record's image laws lib/A/AD1u.v:44 tfib_AIL.
   coreA_asf: YG0t.v:473 astack_free_law_ok. *)
Lemma H_CORE_A : box_core_A BA MT SINKN METAI.
Proof.
constructor.
- intros _ _ LIBX. exact (BoxCore.box_TFIB_T_of_lib LIBX).
- exact YCbp.ameter_triv_laws.
- exact YCbp.ameter_triv_fs_laws.
- exact (Z.le_refl 0).
- intros rc fx STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ Hcl HS.
  exact (YE01.asink_none_kept (SK := box_sink_head) box_segs BA AE2k.tfib_K (AD1u.tfib_AIL BA AD2l.TfibB_syms)
    STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ Hcl HS).
- intros rc fx STK sp0 FP ly S W mem md own ly' S' W' mem' md' k M HJ HM.
  exact (YE01.ameta_inv_kept (SK := box_sink_head) box_segs BA AE2k.tfib_K (AD1u.tfib_AIL BA AD2l.TfibB_syms)
    STK sp0 FP ly S W mem md own ly' S' W' mem' md' k M HJ HM).
- intros rc fx. exact (YG0t.astack_free_law_ok (rc := rc) box_segs BA).
Qed.
(* GUARD (the pcap closing's form): the core's library contract is at box_sink_head; at the plain build's global head
   the type is a different proposition. *)
Check (@coreA_srz _ _ _ _ H_CORE_A : (forall (FP : list (Z * Z)) (md md' : Model) (m : word -> option byte),
     ~ YI16.sink_open_fp FP -> aos_step FP md md' -> SINKN m md -> SINKN m md') ->
  (forall ly : alayout, In (z1 (ANum (BOX_COMMON_FLAGS + 0x4a)) 0) (as_const BA ly)) ->
  (forall rc : YM05.RunCeil,
  @tfib_lib_contract_x_all rc box_shape box_sink_head BA MT BXL0 BXL0 BOX_RLO BOX_RHI SINKN METAI) -> TFIB_T).
Fail Check (@coreA_srz _ _ _ _ H_CORE_A : (forall (FP : list (Z * Z)) (md md' : Model) (m : word -> option byte),
     ~ YI16.sink_open_fp FP -> aos_step FP md md' -> SINKN m md -> SINKN m md') ->
  (forall ly : alayout, In (z1 (ANum (BOX_COMMON_FLAGS + 0x4a)) 0) (as_const BA ly)) ->
  (forall rc : YM05.RunCeil,
  @tfib_lib_contract_x_all rc box_shape YI5b.src0_sink_head BA MT BXL0 BXL0 BOX_RLO BOX_RHI SINKN METAI) -> TFIB_T).
(* Row 6. H_ASYMS_A (owned by a Theorem Labs lane): TfibB's fields at their values (lib/A/AD2l.v:33-56), each by reflexivity. *)
Lemma H_ASYMS_A : box_asyms_A BA.
Proof. constructor; reflexivity. Qed.
(* Row 7. H_STARTUP_A (owned by a Theorem Labs lane): a Theorem Labs lane's lib/A/Prog/BoxStartup.v:144 box_startup_TfibB, every field
   from the generated start-up data (lib/A/AF0m.v, lib/A/ACej.v) and the image's segments
   (a working branch 59d8d48d44d). *)
Lemma H_STARTUP_A : box_startup_A BA.
Proof. exact BoxStartup.box_startup_TfibB. Qed.
(* Row 8. H_GSHADOW_A (owned by a Theorem Labs lane; the certificate gate records for A pass, collector/GATES-A.md:13 / :18):
   a Theorem Labs lane's lib/A/Prog/BoxGShadow.v:68 img_shadow_vis_box and :98 globs_marked_box, both proved from AR at TfibB
   (a working branch d2294f37ec7). *)
Lemma H_GSHADOW_A : box_gshadow_A BA.
Proof. exact (Build_box_gshadow_A BA BoxGShadow.img_shadow_vis_box BoxGShadow.globs_marked_box). Qed.
(* Row 9. H_NOLSAN_A: no leak-check exit handler (owned by a Theorem Labs lane, from the start-up certificate's state at main): the
   certificate fixes common_flags' byte +0x4a to 0 in every state, so InstallAtExitCheckLeaks registers no Atexit and
   the leak check is off the exit path. The core's driver (row 5, coreA_srz) takes it. The cell is a row of TfibB's
   constant table, lib/A/AF0m.v:270 `z1 (ANum 0x132af2) 0x0` (Tfib_const_abs, a working branch
   b40e3b9643cb), found by lib/A/AD2l.v:70 zcell_in (one vm_compute search). *)
Lemma H_NOLSAN_A : forall ly : alayout, In (z1 (ANum (BOX_COMMON_FLAGS + 0x4a)) 0) (as_const BA ly).
Proof.
intros ly. unfold BA. cbn [as_const AD2l.TfibB]. unfold AF0m.Tfib_const.
apply in_app_iff. right. apply in_app_iff. left.
cbv [z1 c1]. apply AD2l.zcell_in. vm_compute. reflexivity.
Qed.
(* Row 10. H_SINK_INERT_A: the sink's inertness, the shared image-generic inertness lemma (a Theorem Labs lane's SinkInert,
   lib/Reusable/SinkInert.v:54 asink_none_os_kept) at box_segs and tfib_K: no step whose footprint leaves the sink
   closed changes SINKN. The core's closed walk (row 5, coreA_srz) takes it. *)
Lemma H_SINK_INERT_A : forall (FP : list (Z * Z)) (md md' : Model) (m : word -> option byte),
  ~ YI16.sink_open_fp FP -> aos_step FP md md' -> SINKN m md -> SINKN m md'.
Proof. exact (SinkInert.asink_none_os_kept box_segs AE2k.tfib_K). Qed.
(* Row 11. H_RT_ALLOC_A: the malloc / free wrappers (owner: a working branch; cgif's released form):
   Reusable/YCbp.v:30 amalloc04_rule_triv / YCbp.v:39 afree04_rule_triv over the core's lib/A/AF0w.v:45
   tfib_amalloc_realizes / lib/A/AF0q.v:13 afree_realizes_closed at TfibB; their api_env premise is built from row 7's
   errno and allocator traces (stA_errno, stA_ra0), as TFIB_T_closed builds it, and the model laws from stA_uok. *)
Lemma H_RT_ALLOC_A : box_alloc_A BA MT.
Proof.
destruct H_STARTUP_A as [Herrno Huok Hra0 _ _ _].
constructor; intros rc fx;
  (assert (ENV : api_env box_segs BA)
    by (split; [exact (proj1 Herrno)|]; split; [exact (proj2 Herrno)|]; exact Hra0)).
- exact (YCbp.amalloc04_rule_triv (SK := box_sink_head) box_segs BA box_segs_low ENV (AR_laws_ok box_segs BA)
    (model_laws_ok (as_universe BA) Huok) (AF0w.tfib_amalloc_realizes BA AD2l.TfibB_syms (fun t => eq_refl))).
- exact (YCbp.afree04_rule_triv (SK := box_sink_head) box_segs BA box_segs_low ENV (AR_laws_ok box_segs BA)
    (model_laws_ok (as_universe BA) Huok) (AF0q.afree_realizes_closed BA AD2l.TfibB_syms (fun t => eq_refl))).
Qed.
(* Row 12. H_RT_MEMCPY_A: __asan_memcpy (cgif's released core A/AE2q.v:143, relocated by a Theorem Labs lane): a Theorem Labs lane's
   instance lib/A/ACed.v:40 boxX_AMEMCPY (lib/A/AE2q.v:144 asan_memcpy_realizes at TfibB, entry 0x51098). The form
   pb_read_name and the other walks consume. *)
Lemma H_RT_MEMCPY_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  aintrin_realizes box_segs BA OCpy (pa_sigma (PAImg := PI_box) BS___asan_memcpy).
Proof. exact ACed.boxX_AMEMCPY. Qed.
(* Row 13. H_RT_MEMSET_A: __asan_memset (cgif A/AE2r.v:566 relocated by a Theorem Labs lane): a Theorem Labs lane's instance
   lib/A/ACed.v:32 boxX_AMEMSET (lib/A/AE2r.v:567 asan_memset_realizes at TfibB in aintrin_realizes OSet's premise
   order, entry 0x51534). *)
Lemma H_RT_MEMSET_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  aintrin_realizes box_segs BA OSet (pa_sigma (PAImg := PI_box) BS___asan_memset).
Proof. exact ACed.boxX_AMEMSET. Qed.
(* Row 14. H_RT_BCMP_A: the bcmp wrapper (cgif A/ACed.v:158 tfibX_ABCMP, the released core's contract; relocated by
   a Theorem Labs lane with the core): a Theorem Labs lane's instance lib/A/ACed.v:46 boxX_ABCMP (lib/A/AE2s.v bc_icpt_realizes at
   TfibB, at the trampoline 0x41404). *)
Lemma H_RT_BCMP_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  abcmp_realizes box_segs BA (pa_sigma (PAImg := PI_box) BS___interceptor_trampoline_bcmp).
Proof. exact ACed.boxX_ABCMP. Qed.
(* Row 15. E1, H_RT_SM3_A: __asan_stack_malloc_3 (owned by a Theorem Labs lane, on a working branch at fc90d9018eb;
   relocated by a Theorem Labs lane; registry row 24): lib/A/Rt/StackMalloc3.v:517 stack_malloc3_contract at TfibB. *)
Lemma H_RT_SM3_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState), astack_malloc_realizes box_segs BA 3.
Proof. intros rc fx. exact (RSM3P.stack_malloc3_contract BA (AR_laws_ok box_segs BA) AD2l.TfibB_syms). Qed.
(* Row 16. E2, H_RT_SSF5_A: __asan_set_shadow_f5 (pg-core's released SetShadowDef + SetShadow, the cgif_rgb
   set_shadow_gen instance, with a Theorem Labs lane's apresent conjunct; relocated by a Theorem Labs lane): lib/A/Rt/SetShadow.v:185
   box_set_shadow_f5 at TfibB, at SSF5_ENTRY 0x54060 (__asan_set_shadow_f5, BoxAddr.v). *)
Lemma H_RT_SSF5_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  RSSH.aset_shadow_realizes box_segs BA (pa_sigma (PAImg := PI_box) BS___asan_set_shadow_f5) 0xf5.
Proof. intros rc fx. exact (RSSHP.box_set_shadow_f5 BA (AR_laws_ok box_segs BA) AD2l.TfibB_syms). Qed.
(* Row 17. E4, H_RT_STRNCMP_A: the strncmp wrapper (interceptor + musl strncmp): a Theorem Labs lane's FMstrncmp
   (a working branch 445e498a469) relocated, at boxreg's frozen text lib/A/Rt/StrncmpDef.v:
   lib/A/Rt/Strncmp.v:29 boxreg_astrncmp_A at TfibB, at STRNCMP_ENTRY, the trampoline 0x413f8. *)
Lemma H_RT_STRNCMP_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  RSTR.astrncmp_realizes box_segs BA (pa_sigma (PAImg := PI_box) BS___interceptor_trampoline_strncmp).
Proof. intros rc fx. exact (RSTRP.boxreg_astrncmp_A BA (AR_laws_ok box_segs BA) AD2l.TfibB_syms). Qed.
(* Row 18. E5, H_RT_MEMCHR_A: the memchr wrapper (a Theorem Labs lane's general memchr, relocated; lib/A/Rt/MemchrDef.v at
   musl memchr's constants [0x10350, 0x10370)): lib/A/Rt/Memchr.v:562 memchr_icpt_realizesM at TfibB, at the
   trampoline 0x41408. Registry row 12. *)
Lemma H_RT_MEMCHR_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  RMCH.amemchr_realizesM box_segs BA BOX_MCH_LO BOX_MCH_HI (pa_sigma (PAImg := PI_box) BS___interceptor_trampoline_memchr).
Proof. intros rc fx. exact (RMCHP.memchr_icpt_realizesM BA (AR_laws_ok box_segs BA) AD2l.TfibB_syms). Qed.
(* Row 19. H_RT_SNPRINTF_A: the whole snprintf chain as one contract, with the strnlen / memcpy / memset interceptors
   on its path: boxreg's own lib/A/Rt/SnprintfDef.v ('%s' with truncation; R2 text: format in [0x10000, 0x99b40), string
   readable to |s| + 8). Retired: lib/A/Rt/SnprintfBridgeFmA.v box_asnprintf_fm (a Theorem Labs lane, bridge 321cbf01609 in R2
   -pa 91ad3cb4145), a Theorem Labs lane's GXA route fm_snprintf_gxa_AR instanced at boxreg through the generic bridge
   snp_fm_of_shared, at BA = TfibB. *)
Lemma H_RT_SNPRINTF_A : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  RSNP.asnprintf_realizes box_segs BA (pa_sigma (PAImg := PI_box) BS___interceptor_trampoline_snprintf).
Proof. exact SnprintfBridgeFmA.box_asnprintf_fm. Qed.
(* Rows 20-22: the program walks, in the form of the proved ones (LAWS, TL, the runtime entries each calls, its
   callees' contracts). Row 20 (harness check 0x80ff0) is retired: pb_check (lib/A/Prog/Check.v:3713, a Theorem Labs lane,
   -pa ffe6ee97abc; LAWS, TL, AMEMCHR, ABCMP) plugs in. It also refutes check's fall-through into read_name at 0x812ac
   (check's last instruction, jal __asan_report_load4) inside a proved walk. *)
(* The read_name row (0x812b0) is retired: pb_read_name (lib/A/Prog/ReadName.v, 1d92330b7ad) plugs in unchanged. *)
(* Row 21 (reac_boxreg_add 0x81ba8) is retired: pb_reac_boxreg_add (lib/A/Prog/ReacBoxregAdd.v, a8925bf9f4d; LAWS, TL,
   memset, memcpy and its two callees' contracts, the row's premises) plugs in. *)
(* Row 22 (LLVMFuzzerTestOneInput 0x7ff4c) is retired: the walk BoxLibX.pb_llvmf_libx (lib/A/Prog/BoxLibX.v:365,
   a Theorem Labs lane, -pa 224543f649b) plugs into TFIB_T_closed directly, with every one of its 42 premises discharged below;
   W_ENTRY_A is gone. *)

(* cgif A/AD2p.v:11 TFIB_T_closed, at fuzz_boxreg.asan. Discharged here (no hypothesis): the allocator laws
   (Reusable/YG0q.v:803 AR_laws_ok), the model laws (Reusable/YG05.v:139 model_laws_ok), the side stack's progress
   (YG05.v:70 stack_malloc_progress), api_env, PALib / PALibF (BoxB.v), the GOT word HGOT, the frame-flag law (box_FFL),
   the read-only range below the sink's head (box_RO), rows 1-18 and 22 (the instances and lemmas above), and the proved
   walks pb_reac_boxreg_init, pb_reac_boxreg_find, pb_reac_boxreg_declare, pb_reac_boxreg_set_name, pb_lowest_free_base,
   pb_range_free, pb_lowest_free, pb_read_name, pb_reac_boxreg_add, pb_check and pb_llvmf_libx. pb_llvmf_libx's premises:
   each fx-bound one is the matching row or walk at that fx; the six ROM facts come from row 7 at YK11.fx0 (they name
   no FP state); HROP is lib/A/Rt/StrncmpViewInst.v:62 box_ro_owned_pinned; HRO and RO are the identity and box_RO at
   BOX_RLO / BOX_RHI = pa_relro_lo / hi (box_rlo_eq / box_rhi_eq); HRNTR and HGLOB are row 7's stA_rn and row 8's
   gsA_glob through BoxLibX.v's box_rn_malloc_ra_lit (A_read_name_mallocRA = 0x813a0) and box_bxg_lits (BX_G =
   BOX_GLOBS); HTR is stA_htr (GB_MSITES / GB_FSITES = BOX_MSITES / BOX_FSITES, box_msites_lits / box_fsites_lits);
   HXL at XM_LIB = XN_LIB = BXL0 is coreA_need (GB_NEED MT unfolds to its left side, box_need_sum), HXLN Z.le_refl. *)
Theorem TFIB_T_closed : TFIB_T.
Proof.
destruct H_CORE_A as [CORE MTL MTF NEED SKEPT MKEPT ASF].
destruct H_RT_ALLOC_A as [AMALLOC4 AFREE4].
pose proof H_RT_MEMCPY_A as AMEMCPY. pose proof H_RT_MEMSET_A as AMEMSET. pose proof H_RT_BCMP_A as ABCMP.
destruct H_ASYMS_A as [Hcode Hgsh Hshc Hguar Huarc].
destruct H_STARTUP_A as [Herrno Huok Hra0 Hrn HTR HROM].
destruct H_GSHADOW_A as [HISV HGLOB].
apply (CORE H_SINK_INERT_A H_NOLSAN_A). intros rc.
destruct (HROM rc YK11.fx0) as (R1 & R2 & R3 & R4 & R5 & R6).
pose proof (AR_laws_ok box_segs BA) as LAWS.
assert (ENV : api_env box_segs BA).
{ split; [exact (proj1 Herrno)|]. split; [exact (proj2 Herrno)|]. exact Hra0. }
pose proof (model_laws_ok (as_universe BA) Huok) as ML.
assert (SMP : stack_malloc_progressP BA)
  by (intros s cid Hw Hc Hn; exact (stack_malloc_progress (as_universe BA) s cid Hw Hc Hn)).
pose proof (box_PALib BA Hcode Hgsh Hshc ENV) as TL.
pose proof (box_PALibF BA Hcode Hguar Huarc) as TLF.
assert (HGOT : as_got_shadow BA = pa_val (PAImg := PI_box) (A_OBJ 1))
  by (rewrite Hgsh; exact (eq_sym box_val_obj1)).
assert (HRO : forall rd, arodata_okP box_segs BOX_RLO BOX_RHI BA rd ->
  arodata_okP box_segs (pa_relro_lo (PAImg := PI_box)) (pa_relro_hi (PAImg := PI_box)) BA rd).
{ intros rd H. rewrite <- box_rlo_eq, <- box_rhi_eq. exact H. }
assert (RO : @ro_below_ofl box_segs (pa_relro_lo (PAImg := PI_box)) (pa_relro_hi (PAImg := PI_box)) box_sink_head).
{ rewrite <- box_rlo_eq, <- box_rhi_eq. exact box_RO. }
assert (HRNTR : In [pc_malloc_ra0 (as_code BA); A_read_name_mallocRA (PI := PI_box)] (as_universe BA)).
{ rewrite BoxLibX.box_rn_malloc_ra_lit. exact Hrn. }
assert (HGLOBX : forall fx : YK11.FPState, globs_marked box_segs BA (BoxLxDefs.BX_G (PI := PI_box))).
{ intros fx. rewrite BoxLibX.box_bxg_lits. exact (HGLOB rc fx). }
pose proof (fun fx : YK11.FPState => pb_lowest_free_base (fx := fx) (SK := box_sink_head) (PI := PI_box) BA LAWS TL)
  as TLFB.
pose proof (fun fx : YK11.FPState => pb_range_free (fx := fx) (SK := box_sink_head) (PI := PI_box) BA LAWS TL)
  as TRANGEFREE.
pose proof (fun fx : YK11.FPState =>
  pb_reac_boxreg_find (fx := fx) (SK := box_sink_head) (PI := PI_box) BA LAWS TL (ABCMP rc fx)) as TFIND.
exact (BoxLibX.pb_llvmf_libx (rc := rc) (SK := box_sink_head) BA MT BXL0 BXL0 BOX_RLO BOX_RHI SINKN METAI
  MTL MTF (SKEPT rc YK11.fx0) (MKEPT rc YK11.fx0) HRO RO HTR HRNTR (fun n => NEED) (fun n => Z.le_refl (BXL0 n))
  (fun _ => LAWS) (fun _ => TL) (fun _ => TLF) (fun _ => ML) (fun fx => H_RT_SM3_A rc fx) SMP (fun fx => ASF rc fx)
  (fun _ => box_FFL BA) (fun fx => AMALLOC4 rc fx) (fun fx => AFREE4 rc fx) (fun fx => AMEMCPY rc fx)
  (fun fx => ABCMP rc fx) (fun fx => H_RT_STRNCMP_A rc fx) (fun fx => H_RT_SSF5_A rc fx)
  (fun fx => pb_reac_boxreg_init (fx := fx) (SK := box_sink_head) (PI := PI_box) BA LAWS (AMEMSET rc fx) HGOT)
  (fun fx => pb_check (fx := fx) (SK := box_sink_head) (PI := PI_box) BA LAWS TL (H_RT_MEMCHR_A rc fx) (ABCMP rc fx))
  (fun fx => pb_read_name (fx := fx) (SK := box_sink_head) (PI := PI_box) BA MT LAWS TL (AMALLOC4 rc fx)
     (AMEMCPY rc fx))
  TFIND
  (fun fx => pb_reac_boxreg_declare (fx := fx) (SK := box_sink_head) (PI := PI_box) BA LAWS TL (AMEMSET rc fx)
     (H_RT_SNPRINTF_A rc fx) (TLFB fx))
  (fun fx => pb_reac_boxreg_add (fx := fx) (SK := box_sink_head) (PI := PI_box) BA LAWS TL (AMEMSET rc fx)
     (AMEMCPY rc fx) (TFIND fx) (TLFB fx))
  (fun fx => pb_reac_boxreg_set_name (fx := fx) (SK := box_sink_head) (PI := PI_box) BA LAWS TL
     (H_RT_SNPRINTF_A rc fx))
  TRANGEFREE
  (fun fx => pb_lowest_free (fx := fx) (SK := box_sink_head) (PI := PI_box) BA LAWS (TRANGEFREE fx))
  (fun fx => HISV rc fx) HGLOBX R1 R2 R5 R3 R6 R4 StrncmpViewInst.box_ro_owned_pinned).
Defined.

(* The two ASan statements of fuzz_boxreg (lib/A/AsanTop.v, Section a). *)
Theorem box_asan_agrees : OSSVerify.libreac.fuzz_boxreg.Statements.asan_agrees.
Proof. exact (AsanTop.box_asan_agrees_of_tfib TFIB_T_closed). Defined.

Theorem box_asan_halts : OSSVerify.libreac.fuzz_boxreg.Statements.asan_halts.
Proof. exact (AsanTop.box_asan_halts_of_tfib TFIB_T_closed). Defined.
End close.
(* After the Section: About lists every part a statement rests on (the open row 19); Print Assumptions lists the axioms. *)
About box_asan_agrees.
Print Assumptions box_asan_agrees.
About box_asan_halts.
Print Assumptions box_asan_halts.

(* ---- gate: the ASan side of this image uses no sink head but box_sink_head -------------------------------------------
   Fails to compile if the statement of TFIB_T_closed, or its proof term, or the proof term of a top names the plain
   build's sink head YI5b.src0_sink_head or its sink record YI5c.src0_sink, or if TFIB_T_closed's proof term does not
   take box_sink_head. The proof terms are visible here because TFIB_T_closed and the tops end with Defined. (The plain
   side of the agreement tops, lib/A/AsanTop.v box_plain_rz, is about the plain image and uses that image's sink head.)
   Since row 22 is retired, no open row of the statement names a sink head (row 19's asnprintf_realizes takes none), so
   the box_sink_head check reads the proof term, which applies pb_llvmf_libx and the walks at SK := box_sink_head. *)
Ltac box_sink_gate T :=
  lazymatch T with
  | context [YI5b.src0_sink_head] => fail 0 "names the plain build's sink head YI5b.src0_sink_head"
  | context [YI5c.src0_sink] => fail 0 "names the plain build's sink record YI5c.src0_sink"
  | _ => idtac
  end.
Example box_sink_gate_ok : True.
Proof.
let T := type of TFIB_T_closed in box_sink_gate T.
let t := eval unfold TFIB_T_closed in TFIB_T_closed in box_sink_gate t;
  lazymatch t with context [box_sink_head] => idtac | _ => fail 0 "TFIB_T_closed does not take box_sink_head" end.
let t := eval unfold box_asan_agrees in box_asan_agrees in box_sink_gate t.
let t := eval unfold box_asan_halts in box_asan_halts in box_sink_gate t.
exact I.
Qed.
