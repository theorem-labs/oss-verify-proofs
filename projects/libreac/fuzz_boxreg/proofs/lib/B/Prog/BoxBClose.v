(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan twin of lib/A/Prog/BoxClose.v, made from
   proofs/cgif/cgif_file_fuzzer/lib/A/AD2p.v, A/AD2o.v and A/ACfi.v of origin/ossv/recipes c8557374ad2 for
   libreac/fuzz_boxreg's ASan+UBSan build (fuzz_boxreg.asan-ubsan) and its walk layer (lib/B/Prog); the image side is
   fuzz_decode's TFIB_TB form (a working branch 21b040f5808 DecodeTFIB.v) as lib/A/BoxTFIB.v states
   it; module paths changed. *)
(* The closing composition of fuzz_boxreg's ASan+UBSan side (rule 24: no function proved; this file is assembly):
   TFIB_TB (lib/A/BoxTFIB.v) and the two statements asan_ubsan_agrees and asan_ubsan_halts, from named parts, one row
   each (rows 1-26 below; proofs/libreac/fuzz_boxreg/provenance/OBLIGATIONS.md); lib/A/Prog/BoxClose.v explains the
   form of each part. The UBSan checks of this build are in trap mode: a failed check branches to the function's own
   `unimp`, which is an error under both statements. Each walk row therefore carries its function's trap guards: the
   walk's post is a normal return, so the walk refutes every trap branch it reaches (the proved walks here do; the open
   rows list their counts in OBLIGATIONS.md). Nothing in this file adds a trap exit.
   The sink head is boxb_sink_head, built from fuzz_boxreg.asan-ubsan's own `ofl_head` (.bss 0x5f4a48, 8 bytes; pinned
   in lib/B/Prog/BoxBSinkPin.v); it is a Definition, never an instance, and every statement below takes it explicitly.
   The Check / Fail Check guard after row 5 and the Ltac gate at the end fail to build if the plain build's sink head or
   sink record appears in this image's closing. *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym PaRun BoxBase BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import
BoxBSyms BoxBList BoxBAddr BoxBPa BoxBImg BoxBPaLib BoxBFrame BoxBB BoxBLibX.
(* Row 7's record boxb_startup_B and the values it names (BOXB_RN_MALLOC_RA, BOXB_MSITES, BOXB_FSITES), moved verbatim
   so that lib/B/Prog/BoxBStartup.v can prove the record without requiring this file. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Export BoxBCloseDefs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import
BoxBCheck BoxBReadName BoxBReadMac BoxBRangeFree BoxBRangeTaken BoxBLowestFreeBase BoxBMacIsZero
BoxBReacBoxregInit BoxBReacBoxregFind BoxBReacBoxregDeclare BoxBReacBoxregAdd BoxBReacBoxregSetName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require SnprintfDefB StrncmpDefB SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require MemchrDef.
From OSSVerify.libreac.fuzz_boxreg Require Statements.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YI5b YI5c.
(* The instances and dischargers of rows 1-18 (core 4b14024f7e8, -asyms AD2l, ACed, strncmp B, memchr B, SSF5 B,
   BoxBStartup, BoxBGShadow, SinkInert, BoxBCore) and row 26's PINNED (StrncmpViewBInst) and GCELLS list (BoxBLxDefs);
   the walks of rows 20 and 26 come with BoxBCheck and BoxBLibX above. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YCbp YE00 YE01 YG0t SinkInert.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require AD2l AE2k AD1u AE2q AE2s AF0w AF0q ACed.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require StackMalloc3 StrncmpB Memchr SetShadow StrncmpViewBInst.
(* Row 19's discharger: a Theorem Labs lane's bridge from a Theorem Labs lane's GXA route (R2, -pa 91ad3cb4145). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require SnprintfBridgeFmB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require BoxBStartup BoxBGShadow BoxBLxDefs BoxBCore.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module BRSNP := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt.SnprintfDefB.
Module BRSTR := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt.StrncmpDefB.
Module BRMCH := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt.MemchrDef.
Module BRSSH := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt.SetShadowDef.

(* ---- per-image values of fuzz_boxreg.asan-ubsan ------------------------------------------------------------------ *)
(* `ofl_head` (musl's open-file list head): .bss, 0x5f4a48, 8 bytes. *)
Definition BOXB_OFL_HEAD : Z := 0x5f4a48.
Definition boxb_sink_head : YI16.sink_head := YI16.mkSinkHead BOXB_OFL_HEAD.
(* The read-only range of the library contract: .data.rel.ro .. .got, [0x98d78, 0x99fd0), the range of PI_boxb
   (cgif's convention, lib/B/Prog/BoxBImg.v). *)
Definition BOXB_RLO : Z := 0x98d78.
Definition BOXB_RHI : Z := 0x99fd0.
(* The 5 registered globals (asan_globals, 0x9db90 .. 0x9dcd0, five 64-byte records): (beginning, size). *)
Definition BOXB_GLOBS : list (Z * Z) := [(0x20cc0, 6); (0x20ce0, 1); (0x20d00, 5); (0x20d40, 3); (0x20d60, 1)].
(* musl memchr's two read-only 8-byte constants (.rodata, not owned): 0x10350 and 0x10368; the memchr contract's
   constant range (lib/A/Rt/MemchrDef.v amemchr_realizesM, image-neutral, lib/A/Rt/ConstsViewDef.v consts_view) is [0x10350, 0x10370). *)
Definition BOXB_MCH_LO : Z := 0x10350.
Definition BOXB_MCH_HI : Z := 0x10370.
(* __sanitizer::common_flags_dont_use (.bss 0x132ee8, 0x120 bytes); its byte at +0x4a decides whether
   InstallAtExitCheckLeaks registers the leak check's Atexit handler. *)
Definition BOXB_COMMON_FLAGS : Z := 0x132ee8.
(* cgif's XL0 (A/ACfi.v:56). *)
Definition BBXL0 : Z -> Z := fun _ => 0.

Section rl. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma boxb_rlo_eq : BOXB_RLO = pa_relro_lo (PAImg := PI_boxb).
Proof. reflexivity. Qed.
Lemma boxb_rhi_eq : BOXB_RHI = pa_relro_hi (PAImg := PI_boxb).
Proof. reflexivity. Qed.
End rl.

(* ---- the read-only range lies below the sink's list head (cgif A/ACfi.v tfib_ROB) -------------------------------- *)
Lemma boxb_ro_segs_chk :
  forallb (fun s : Segment => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? BOXB_OFL_HEAD))%bool
    boxb_segs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma boxb_RO : @ro_below_ofl boxb_segs BOXB_RLO BOXB_RHI boxb_sink_head.
Proof.
intros a [(s & Hin & Hw & Hr) | Hr]; cbn [YI16.sk_ofl_head boxb_sink_head].
- pose proof (proj1 (forallb_forall _ _) boxb_ro_segs_chk s Hin) as Hb. cbn beta in Hb. rewrite Hw in Hb.
  cbn [orb] in Hb. apply Z.leb_le in Hb. lia.
- unfold BOXB_RLO, BOXB_RHI, BOXB_OFL_HEAD in *. lia.
Qed.

(* ---- the frame-flag law, from the allocator laws and the image's cover (cgif A/ACfi.v link_FFL) ------------------ *)
Section ff. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma boxb_FFL : forall B : asyms, frame_flag_lawP boxb_segs B.
Proof.
intros B ly S W mem md cid pos HAR Hin.
pose proof (AR_laws_ok boxb_segs B) as LAWS.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (boxb_img_cover ly S md L) as [C1 C2].
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
End ff.

(* ---- the parts the closing rests on, one record per owner's part (as lib/A/Prog/BoxClose.v; cgif's asan-ubsan core
   lib/YD2o.v, YD1q.v, YCfi.v, YCbp.v, YG0t.v and the YE2q / YE2r / YE2s twins) --------------------------------------- *)
Record boxb_core_B (BB : asyms) (MT : ameter_ops) (SINKN : (word -> option byte) -> Model -> Prop)
  (METAI : alayout -> (word -> option byte) -> Z -> Prop) : Prop := {
  coreB_srz : (forall (FP : list (Z * Z)) (md md' : Model) (m : word -> option byte),
       ~ YI16.sink_open_fp FP -> aos_step FP md md' -> SINKN m md -> SINKN m md') ->
    (forall ly : alayout, In (z1 (ANum (BOXB_COMMON_FLAGS + 0x4a)) 0) (as_const BB ly)) ->
    (forall rc : YM05.RunCeil,
      @tbfib_lib_contract_x_all rc box_shape boxb_sink_head BB MT BBXL0 BBXL0 BOXB_RLO BOXB_RHI SINKN METAI) -> TFIB_TB;
  coreB_mtl : ameter_laws MT;
  coreB_mtf : ameter_fs_laws MT;
  coreB_need : mo_malloc MT 288 + 64 * (mo_malloc MT 48 + mo_free MT) + mo_free MT <= 0;
  coreB_sinkn_kept : forall (rc : YM05.RunCeil) (fx : YK11.FPState) STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
    ajournal (SK := boxb_sink_head) boxb_segs BB STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
    ~ YI16.sink_open_fp FP -> SINKN (mrestrict (w_H W) mem) md -> SINKN (mrestrict (w_H W') mem') md';
  coreB_metai_kept : forall (rc : YM05.RunCeil) (fx : YK11.FPState) STK sp0 FP ly S W mem md own ly' S' W' mem' md' k M,
    ajournal (SK := boxb_sink_head) boxb_segs BB STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
    METAI ly (mrestrict (w_H W) mem) M -> METAI ly' (mrestrict (w_H W') mem') M;
  coreB_asf : forall (rc : YM05.RunCeil) (fx : YK11.FPState), astack_free_law boxb_segs BB }.
(* The allocator's two wrappers (cgif's released amalloc04_rule / afree04_rule; owner: a working branch). *)
Record boxb_alloc_B (BB : asyms) (MT : ameter_ops) : Prop := {
  alB_malloc : forall (rc : YM05.RunCeil) (fx : YK11.FPState), amalloc04_rule (SK := boxb_sink_head) boxb_segs BB MT;
  alB_free : forall (rc : YM05.RunCeil) (fx : YK11.FPState), afree04_rule (SK := boxb_sink_head) boxb_segs BB MT }.
(* The asyms record's fields (lib/B/Prog/BoxBB.v boxb_code, GOT words and cells as boxb_PALib / boxb_PALibF take them). *)
Record boxb_asyms_B (BB : asyms) : Prop := {
  asB_code : as_code BB = boxb_code;
  asB_got_shadow : as_got_shadow BB = 0x992d8;
  asB_shadow_cell : as_shadow_cell BB = 0xa13b8;
  asB_got_uar : as_got_uar BB = 0x99330;
  asB_uar_cell : as_uar_cell BB = 0xa13c0 }.
(* The start-up certificate's facts on the shadow of the image and of the registered globals (OPEN until boxreg's
   certificate gate, arrival + shadow step, passes for this image). *)
Record boxb_gshadow_B (BB : asyms) : Prop := {
  gsB_isv : forall (rc : YM05.RunCeil) (fx : YK11.FPState), img_shadow_vis boxb_segs BB;
  gsB_glob : forall (rc : YM05.RunCeil) (fx : YK11.FPState), globs_marked boxb_segs BB BOXB_GLOBS }.

Section close.
(* Rows 1-4 (instances). BB: cgif lib/YD2l.v TfibB, here lib/B/AD2l.v TfibB (767b2b2ca46). MT: ameter_triv
   (lib/Reusable/YCbp.v). SINKN / METAI: the core's invariants for BoxBLibX.v, lib/Reusable/YE00.v asink_none and
   lib/Reusable/YE01.v ameta_inv at boxb_segs and lib/B/AE2k.v tfib_K (core 4b14024f7e8). *)
Definition BB : asyms := AD2l.TfibB.
Definition MT : ameter_ops := YCbp.ameter_triv.
Definition SINKN : (word -> option byte) -> Model -> Prop := YE00.asink_none boxb_segs AE2k.tfib_K.
Definition METAI : alayout -> (word -> option byte) -> Z -> Prop := YE01.ameta_inv boxb_segs AE2k.tfib_K.
(* Row 5. H_CORE_B: the relocated asan-ubsan core, field by field. coreB_srz (H_CORE_SRZ_B): lib/B/Prog/BoxBCore.v
   boxb_TFIB_TB_of_lib (the B twin of cgif YD2o.v:78 TFIB_T_of_partsXF, over lib/B/AD1q.v:212 tfib_srealizesX at
   TfibB); it does not use the field's first two premises (rows 10 and 9): the relocated core's driver takes neither.
   The other fields come from the relocated core (4b14024f7e8): YCbp.v ameter_triv_laws / ameter_triv_fs_laws,
   ameter_triv's zero costs, YE01.v asink_none_kept / ameta_inv_kept over lib/B/AD1u.v tfib_AIL, and
   lib/Reusable/YG0t.v astack_free_law_ok. *)
Lemma H_CORE_SRZ_B : (forall (FP : list (Z * Z)) (md md' : Model) (m : word -> option byte),
     ~ YI16.sink_open_fp FP -> aos_step FP md md' -> SINKN m md -> SINKN m md') ->
  (forall ly : alayout, In (z1 (ANum (BOXB_COMMON_FLAGS + 0x4a)) 0) (as_const BB ly)) ->
  (forall rc : YM05.RunCeil,
    @tbfib_lib_contract_x_all rc box_shape boxb_sink_head BB MT BBXL0 BBXL0 BOXB_RLO BOXB_RHI SINKN METAI) -> TFIB_TB.
Proof. intros _ _ LIBX. exact (BoxBCore.boxb_TFIB_TB_of_lib LIBX). Qed.
Lemma H_CORE_B : boxb_core_B BB MT SINKN METAI.
Proof.
split.
- exact H_CORE_SRZ_B.
- exact YCbp.ameter_triv_laws.
- exact YCbp.ameter_triv_fs_laws.
- unfold MT, YCbp.ameter_triv. cbn. lia.
- exact (fun (rc : YM05.RunCeil) (fx : YK11.FPState) =>
    YE01.asink_none_kept (SK := boxb_sink_head) boxb_segs BB AE2k.tfib_K (AD1u.tfib_AIL BB AD2l.TfibB_syms)).
- exact (fun (rc : YM05.RunCeil) (fx : YK11.FPState) =>
    YE01.ameta_inv_kept (SK := boxb_sink_head) boxb_segs BB AE2k.tfib_K (AD1u.tfib_AIL BB AD2l.TfibB_syms)).
- exact (fun (rc : YM05.RunCeil) (fx : YK11.FPState) => YG0t.astack_free_law_ok boxb_segs BB).
Qed.
Check (@coreB_srz _ _ _ _ H_CORE_B : (forall (FP : list (Z * Z)) (md md' : Model) (m : word -> option byte),
     ~ YI16.sink_open_fp FP -> aos_step FP md md' -> SINKN m md -> SINKN m md') ->
  (forall ly : alayout, In (z1 (ANum (BOXB_COMMON_FLAGS + 0x4a)) 0) (as_const BB ly)) ->
  (forall rc : YM05.RunCeil,
  @tbfib_lib_contract_x_all rc box_shape boxb_sink_head BB MT BBXL0 BBXL0 BOXB_RLO BOXB_RHI SINKN METAI) -> TFIB_TB).
Fail Check (@coreB_srz _ _ _ _ H_CORE_B : (forall (FP : list (Z * Z)) (md md' : Model) (m : word -> option byte),
     ~ YI16.sink_open_fp FP -> aos_step FP md md' -> SINKN m md -> SINKN m md') ->
  (forall ly : alayout, In (z1 (ANum (BOXB_COMMON_FLAGS + 0x4a)) 0) (as_const BB ly)) ->
  (forall rc : YM05.RunCeil,
  @tbfib_lib_contract_x_all rc box_shape YI5b.src0_sink_head BB MT BBXL0 BBXL0 BOXB_RLO BOXB_RHI SINKN METAI) -> TFIB_TB).
(* Row 6. H_ASYMS_B: TfibB's fields, by reflexivity (lib/B/AD2l.v, 767b2b2ca46). Row 7. H_STARTUP_B:
   lib/B/Prog/BoxBStartup.v boxb_startup_TfibB (8df8ad627ea, a Theorem Labs lane). Row 8. H_GSHADOW_B: lib/B/Prog/BoxBGShadow.v
   img_shadow_vis_boxb / globs_marked_boxb (d2294f37ec7, a Theorem Labs lane), proved from AR at TfibB. *)
Lemma H_ASYMS_B : boxb_asyms_B BB.
Proof. exact (Build_boxb_asyms_B BB eq_refl eq_refl eq_refl eq_refl eq_refl). Qed.
Lemma H_STARTUP_B : boxb_startup_B BB.
Proof. exact BoxBStartup.boxb_startup_TfibB. Qed.
Lemma H_GSHADOW_B : boxb_gshadow_B BB.
Proof. exact (Build_boxb_gshadow_B BB BoxBGShadow.img_shadow_vis_boxb BoxBGShadow.globs_marked_boxb). Qed.
(* Row 9. H_NOLSAN_B: no leak-check exit handler; row 5's coreB_srz takes it. TfibB's Tfib_const_abs has the cell
   z1 (ANum 0x132f32) 0 (lib/B/AF0m.v, b40e3b9643c); membership by lib/B/AD2l.v zcell_in on a closed boolean. *)
Lemma H_NOLSAN_B : forall ly : alayout, In (z1 (ANum (BOXB_COMMON_FLAGS + 0x4a)) 0) (as_const BB ly).
Proof. intros ly. cbv [z1 c1]. apply AD2l.zcell_in. vm_compute. reflexivity. Qed.
(* Row 10. H_SINK_INERT_B: lib/Reusable/SinkInert.v asink_none_os_kept at boxb_segs and tfib_K (a Theorem Labs lane,
   add754d0ac8, relocated onto the train); row 5's coreB_srz takes it. *)
Lemma H_SINK_INERT_B : forall (FP : list (Z * Z)) (md md' : Model) (m : word -> option byte),
  ~ YI16.sink_open_fp FP -> aos_step FP md md' -> SINKN m md -> SINKN m md'.
Proof. exact (SinkInert.asink_none_os_kept boxb_segs AE2k.tfib_K). Qed.
(* Row 11. H_RT_ALLOC_B: YCbp.v amalloc04_rule_triv / afree04_rule_triv over lib/B/AF0w.v tfib_amalloc_realizes and
   lib/B/AF0q.v afree_realizes_closed (core 4b14024f7e8); api_env and the universe come from row 7 (H_STARTUP_B), as
   TFIB_TB_closed builds them. Row 12. H_RT_MEMCPY_B: lib/B/AE2q.v asan_memcpy_realizes (core). Row 13. H_RT_MEMSET_B:
   lib/B/ACed.v boxbX_AMEMSET (801de21e5ad; the premise reorder of lib/B/AE2r.v asan_memset_realizes). Row 14.
   H_RT_BCMP_B: lib/B/AE2s.v bcmp_icpt_contract (core). *)
Lemma H_RT_ALLOC_B : boxb_alloc_B BB MT.
Proof.
destruct H_STARTUP_B as [Herrno Huok Hra0 _ _ _].
assert (ENV : api_env boxb_segs BB).
{ split; [exact (proj1 Herrno)|]. split; [exact (proj2 Herrno)|]. exact Hra0. }
split.
- exact (fun (rc : YM05.RunCeil) (fx : YK11.FPState) =>
    YCbp.amalloc04_rule_triv (SK := boxb_sink_head) boxb_segs BB boxb_segs_low ENV (AR_laws_ok boxb_segs BB)
      (model_laws_ok _ Huok) (AF0w.tfib_amalloc_realizes BB AD2l.TfibB_syms (fun t => eq_refl))).
- exact (fun (rc : YM05.RunCeil) (fx : YK11.FPState) =>
    YCbp.afree04_rule_triv (SK := boxb_sink_head) boxb_segs BB boxb_segs_low ENV (AR_laws_ok boxb_segs BB)
      (model_laws_ok _ Huok) (AF0q.afree_realizes_closed BB AD2l.TfibB_syms (fun t => eq_refl))).
Qed.
Lemma H_RT_MEMCPY_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  aintrin_realizes boxb_segs BB OCpy (pa_sigma (PAImg := PI_boxb) BB___asan_memcpy).
Proof.
exact (fun (rc : YM05.RunCeil) (fx : YK11.FPState) =>
  AE2q.asan_memcpy_realizes BB (AR_laws_ok boxb_segs BB) AD2l.TfibB_syms).
Qed.
Lemma H_RT_MEMSET_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  aintrin_realizes boxb_segs BB OSet (pa_sigma (PAImg := PI_boxb) BB___asan_memset).
Proof.
exact ACed.boxbX_AMEMSET.
Qed.
Lemma H_RT_BCMP_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  abcmp_realizes boxb_segs BB (pa_sigma (PAImg := PI_boxb) BB___interceptor_trampoline_bcmp).
Proof.
exact (fun (rc : YM05.RunCeil) (fx : YK11.FPState) =>
  AE2s.bcmp_icpt_contract BB (AR_laws_ok boxb_segs BB) AD2l.TfibB_syms).
Qed.
(* Row 15. E1 H_RT_SM3_B: lib/B/Rt/StackMalloc3.v stack_malloc3_contract (core 4b14024f7e8).
   Row 16. E2 H_RT_SSF5_B: lib/B/Rt/SetShadow.v boxb_set_shadow_f5_row16 (47a33d051d2). *)
Lemma H_RT_SM3_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState), astack_malloc_realizes boxb_segs BB 3.
Proof.
exact (fun (rc : YM05.RunCeil) (fx : YK11.FPState) =>
  StackMalloc3.stack_malloc3_contract BB (AR_laws_ok boxb_segs BB) AD2l.TfibB_syms).
Qed.
Lemma H_RT_SSF5_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  BRSSH.aset_shadow_realizes boxb_segs BB (pa_sigma (PAImg := PI_boxb) BB___asan_set_shadow_f5) 0xf5.
Proof.
exact (fun (rc : YM05.RunCeil) (fx : YK11.FPState) =>
  SetShadow.boxb_set_shadow_f5_row16 rc fx BB (AR_laws_ok boxb_segs BB) AD2l.TfibB_syms).
Qed.
(* Row 17. E4 H_RT_STRNCMP_B: lib/B/Rt/StrncmpB.v boxreg_abstrncmp_B (fe7d65b1e2d). Row 18. E5 H_RT_MEMCHR_B:
   lib/B/Rt/Memchr.v memchr_icpt_realizesM (be509f896b3), at musl memchr's constants [0x10350, 0x10370)
   (lib/A/Rt/MemchrDef.v, image-neutral). *)
Lemma H_RT_STRNCMP_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  BRSTR.abstrncmp_realizes boxb_segs BB (pa_sigma (PAImg := PI_boxb) BB___interceptor_trampoline_strncmp).
Proof.
exact (fun (rc : YM05.RunCeil) (fx : YK11.FPState) =>
  StrncmpB.boxreg_abstrncmp_B BB (AR_laws_ok boxb_segs BB) AD2l.TfibB_syms).
Qed.
Lemma H_RT_MEMCHR_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  BRMCH.amemchr_realizesM boxb_segs BB BOXB_MCH_LO BOXB_MCH_HI (pa_sigma (PAImg := PI_boxb) BB___interceptor_trampoline_memchr).
Proof.
exact (fun (rc : YM05.RunCeil) (fx : YK11.FPState) =>
  Memchr.memchr_icpt_realizesM BB (AR_laws_ok boxb_segs BB) AD2l.TfibB_syms).
Qed.
(* Row 19 (H_RT_SNPRINTF_B, the whole snprintf chain as one contract) is retired: SnprintfBridgeFmB.boxb_absnprintf_fm (lib/B/Rt/SnprintfBridgeFmB.v, a Theorem Labs lane, -pa 91ad3cb4145: a Theorem Labs lane's fm_snprintf_gxa_AR at boxreg's instance through the generic bridge snp_fm_of_shared) plugs in unchanged. *)
Lemma H_RT_SNPRINTF_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  BRSNP.absnprintf_realizes boxb_segs BB (pa_sigma (PAImg := PI_boxb) BB___interceptor_trampoline_snprintf).
Proof. exact SnprintfBridgeFmB.boxb_absnprintf_fm. Qed.
(* Rows 20-26: the program walks (each with its function's UBSan trap guards). *)
(* Row 20. pb_bcheck (harness check 0x81034, 6 trap branches): lib/B/Prog/BoxBCheck.v:2617 pb_bcheck (a Theorem Labs lane,
   -pa b4f6a8019fa), whose Section hypotheses come in the order LAWS TL ABCMP AMEMCHR; the row keeps its frozen order
   (memchr before bcmp), so the lemma swaps the last two. *)
Lemma pb_bcheck : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  AR_laws boxb_segs BB -> PALib (PI := PI_boxb) BB ->
  BRMCH.amemchr_realizesM boxb_segs BB BOXB_MCH_LO BOXB_MCH_HI (pa_sigma (PAImg := PI_boxb) BB___interceptor_trampoline_memchr) ->
  abcmp_realizes boxb_segs BB (pa_sigma (PAImg := PI_boxb) BB___interceptor_trampoline_bcmp) ->
  tbcheck_spec (SK := boxb_sink_head) (PI := PI_boxb) BB.
Proof.
intros rc fx LAWS TL M C.
exact (BoxBCheck.pb_bcheck (SK := boxb_sink_head) (PI := PI_boxb) BB LAWS TL C M).
Qed.
(* Row 21 (harness read_name 0x81318) is retired: pb_bread_name (lib/B/Prog/BoxBReadName.v:1281, bc0f8b1c53d,
   a Theorem Labs lane; LAWS, TL, AMALLOC4, AMEMCPY, the row's premises) plugs in unchanged, with its implicit SK / PI given
   explicitly. *)
(* Row 22 (read_mac 0x81618) is retired: pb_bread_mac (lib/B/Prog/BoxBReadMac.v, bbe1fa659b9; LAWS, TL,
   aintrin_realizes OCpy at __asan_memcpy, the row's premises) plugs in unchanged. *)
(* Row 23 (range_free 0x814e8) is retired: pb_brange_free (lib/B/Prog/BoxBRangeFree.v:523, 147cefcfe4a; LAWS, TL)
   plugs in unchanged, with its implicit SK / PI given explicitly. *)
(* Row 24 (reac_boxreg_declare 0x81ad0) is retired: pbb_reac_boxreg_declare (lib/B/Prog/BoxBReacBoxregDeclare.v,
   83e3ebd3dd7) plugs in with the row's premises. *)
(* Row 25 (reac_boxreg_add 0x81f68) is retired: pbb_reac_boxreg_add (lib/B/Prog/BoxBReacBoxregAdd.v, 71ed52fe661; LAWS
   TL AMEMSET AMEMCPY MZ FIND LFB) plugs in unchanged. *)
(* Row 26 (LLVMFuzzerTestOneInput 0x7ffac, 25 trap branches) is retired: the walk BoxBLibX.pb_bllvmf_libx
   (lib/B/Prog/BoxBLibX.v:363, a Theorem Labs lane, -pa 1910380c310) plugs into TFIB_TB_closed directly, with every one of its
   40 premises discharged below; W_ENTRY_B is gone. Its state-free premise GCELLS (the start-up shadow cells of the
   five registered globals, BoxBLxDefs.v lx_glob_cells, are const cells of TfibB) is a closed decision over
   lib/B/AF0m.v's table (-start b40e3b9643c): boxb_cell_inb reflects membership of one z cell, vm_compute decides the
   whole list (a goal with no evar). *)
Definition boxb_cell_inb (l : list acell) (c : acell) : bool :=
  match c with ACell (ANum a) w (AV (ANum v)) => existsb (fun c' => AD2l.zcell_eqb c' a w v) l | _ => false end.
Lemma boxb_cell_inb_ok : forall l c, boxb_cell_inb l c = true -> In c l.
Proof.
intros l c H. destruct c as [e w av]. destruct e; cbn in H; try discriminate.
destruct av as [e'|]; cbn in H; try discriminate. destruct e'; cbn in H; try discriminate.
exact (AD2l.zcell_in l _ w _ H).
Qed.
Lemma boxb_gcells : forall (fx : YK11.FPState) (ly : alayout) (c : acell),
  In c (BoxBLxDefs.lx_glob_cells boxb_val) -> In c (as_const BB ly).
Proof.
intros fx ly c Hc. apply boxb_cell_inb_ok.
assert (CHK : forallb (boxb_cell_inb (as_const BB ly)) (BoxBLxDefs.lx_glob_cells boxb_val) = true)
  by (vm_compute; reflexivity).
exact (proj1 (forallb_forall _ _) CHK c Hc).
Qed.

(* cgif A/AD2p.v:11 TFIB_T_closed, at fuzz_boxreg.asan-ubsan. Discharged here (no hypothesis): AR_laws_ok,
   model_laws_ok, stack_malloc_progress, api_env, PALib / PALibF (BoxBB.v), the frame-flag law, rows 1-18, 20 and 26
   (the instances and lemmas above; row 5 with coreB_srz from BoxBCore.v), the proved walks pbb_mac_is_zero,
   pbb_reac_boxreg_init, pbb_reac_boxreg_find, pbb_reac_boxreg_set_name, pbb_range_taken, pbb_lowest_free_base,
   pbb_reac_boxreg_declare, pbb_reac_boxreg_add, pb_bread_mac, pb_brange_free, pb_bread_name, pb_bcheck and
   pb_bllvmf_libx (their 81 trap branches refuted inside them). pb_bllvmf_libx's premises: each fx-bound one is the
   matching row or walk at that fx; the six ROM facts come from row 7 at YK11.fx0 (they name no FP state); PINNED is
   lib/B/Rt/StrncmpViewBInst.v box_ro_owned_pinned; GCELLS is boxb_gcells; RNTRACE (AB_read_name_mallocRA = 0x81438
   = BOXB_RN_MALLOC_RA), HTR (LX_MSITES / LX_FSITES = BOXB_MSITES / BOXB_FSITES) and HRO (BOXB_RLO / BOXB_RHI =
   0x98d78 / 0x99fd0) hold by conversion; HXL at XM_LIB = XN_LIB = BBXL0 is coreB_need (LX_NEED MT unfolds to its
   left side). The walk takes no ro_below_ofl, so boxb_RO is no longer consumed. *)
Theorem TFIB_TB_closed : TFIB_TB.
Proof.
destruct H_CORE_B as [CORE MTL MTF NEED SKEPT MKEPT ASF].
destruct H_RT_ALLOC_B as [AMALLOC4 AFREE4].
pose proof H_RT_MEMCPY_B as AMEMCPY. pose proof H_RT_MEMSET_B as AMEMSET. pose proof H_RT_BCMP_B as ABCMP.
destruct H_ASYMS_B as [Hcode Hgsh Hshc Hguar Huarc].
destruct H_STARTUP_B as [Herrno Huok Hra0 Hrn HTR HROM].
destruct H_GSHADOW_B as [HISV _].
apply (CORE H_SINK_INERT_B H_NOLSAN_B). intros rc.
destruct (HROM rc YK11.fx0) as (R1 & R2 & R3 & R4 & R5 & R6).
pose proof (AR_laws_ok boxb_segs BB) as LAWS.
assert (ENV : api_env boxb_segs BB).
{ split; [exact (proj1 Herrno)|]. split; [exact (proj2 Herrno)|]. exact Hra0. }
pose proof (model_laws_ok (as_universe BB) Huok) as ML.
assert (SMP : stack_malloc_progressP BB)
  by (intros s cid Hw Hc Hn; exact (stack_malloc_progress (as_universe BB) s cid Hw Hc Hn)).
pose proof (boxb_PALib BB Hcode Hgsh Hshc ENV) as TL.
pose proof (boxb_PALibF BB Hcode Hguar Huarc) as TLF.
assert (HXL : forall n, BoxBLxDefs.LX_NEED MT <= BBXL0 n /\ BBXL0 n <= BBXL0 n).
{ intros n. split; [exact NEED | apply Z.le_refl]. }
pose proof (fun fx' : YK11.FPState => pbb_mac_is_zero (SK := boxb_sink_head) (PI := PI_boxb) BB LAWS TL) as TMZ.
pose proof (fun fx' : YK11.FPState => pbb_range_taken (SK := boxb_sink_head) (PI := PI_boxb) BB LAWS TL) as TRT.
pose proof (fun fx' : YK11.FPState =>
  pbb_lowest_free_base (SK := boxb_sink_head) (PI := PI_boxb) BB LAWS TL (TRT fx')) as TLFB.
pose proof (fun fx' : YK11.FPState =>
  pbb_reac_boxreg_find (SK := boxb_sink_head) (PI := PI_boxb) BB LAWS TL (ABCMP rc fx') (TMZ fx')) as TFIND.
exact (BoxBLibX.pb_bllvmf_libx (SK := boxb_sink_head) BB MT BBXL0 BBXL0 BOXB_RLO BOXB_RHI SINKN METAI
  (fun fx' => LAWS) (fun fx' => TL) (fun fx' => TLF) boxb_gcells R1 R2 R3 R4 R5 R6
  StrncmpViewBInst.box_ro_owned_pinned
  (fun fx' => HISV rc fx') (fun fx' => ML) (fun fx' => MTL) (fun fx' => MTF)
  (fun fx' => H_RT_SM3_B rc fx') (fun fx' => SMP) (fun fx' => ASF rc fx') (fun fx' => boxb_FFL BB)
  (fun fx' => AMALLOC4 rc fx') (fun fx' => AFREE4 rc fx') (fun fx' => AMEMCPY rc fx') (fun fx' => ABCMP rc fx')
  (fun fx' => H_RT_STRNCMP_B rc fx') (fun fx' => H_RT_SSF5_B rc fx')
  (fun fx' => pbb_reac_boxreg_init (SK := boxb_sink_head) (PI := PI_boxb) BB LAWS TL (AMEMSET rc fx'))
  (fun fx' => pb_bcheck rc fx' LAWS TL (H_RT_MEMCHR_B rc fx') (ABCMP rc fx'))
  (fun fx' => pb_bread_mac (SK := boxb_sink_head) (PI := PI_boxb) BB LAWS TL (AMEMCPY rc fx'))
  (fun fx' => pb_bread_name (SK := boxb_sink_head) (PI := PI_boxb) BB MT LAWS TL (AMALLOC4 rc fx') (AMEMCPY rc fx'))
  (fun fx' => @pb_brange_free fx' rc boxb_sink_head PI_boxb BB LAWS TL)
  TFIND
  (fun fx' => pbb_reac_boxreg_declare (SK := boxb_sink_head) (PI := PI_boxb) BB LAWS TL (AMEMSET rc fx')
     (H_RT_SNPRINTF_B rc fx') (TRT fx') (TLFB fx'))
  (fun fx' => pbb_reac_boxreg_add (SK := boxb_sink_head) (PI := PI_boxb) BB LAWS TL (AMEMSET rc fx')
     (AMEMCPY rc fx') (TMZ fx') (TFIND fx') (TLFB fx'))
  (fun fx' => pbb_reac_boxreg_set_name (SK := boxb_sink_head) (PI := PI_boxb) BB LAWS TL (H_RT_SNPRINTF_B rc fx'))
  Hrn (fun rd H => H) HTR HXL (fun fx' => SKEPT rc fx') (fun fx' => MKEPT rc fx')).
Defined.

(* The two ASan+UBSan statements of fuzz_boxreg (lib/A/AsanTop.v, Section b). *)
Theorem box_asan_ubsan_agrees : OSSVerify.libreac.fuzz_boxreg.Statements.asan_ubsan_agrees.
Proof. exact (AsanTop.box_asan_ubsan_agrees_of_tfib TFIB_TB_closed). Defined.

Theorem box_asan_ubsan_halts : OSSVerify.libreac.fuzz_boxreg.Statements.asan_ubsan_halts.
Proof. exact (AsanTop.box_asan_ubsan_halts_of_tfib TFIB_TB_closed). Defined.
End close.
(* After the Section: About lists every part a statement rests on (none open: rows 1-26 are all discharged); Print Assumptions lists the axioms. *)
About TFIB_TB_closed.
Print Assumptions TFIB_TB_closed.
About box_asan_ubsan_agrees.
Print Assumptions box_asan_ubsan_agrees.
About box_asan_ubsan_halts.
Print Assumptions box_asan_ubsan_halts.

(* ---- gate: the ASan side of this image uses no sink head but boxb_sink_head -------------------------------------------
   Fails to compile if the statement of TFIB_TB_closed, or its proof term, or the proof term of a top names the plain
   build's sink head YI5b.src0_sink_head or its sink record YI5c.src0_sink, or if TFIB_TB_closed's proof term does not take
   boxb_sink_head. The proof terms are visible here because TFIB_TB_closed and the tops end with Defined. (The plain side of the
   agreement tops, lib/A/AsanTop.v box_plain_rz, is about the plain image and uses that image's sink head.)
   The positive check reads the proof term, not the statement: since row 5 (coreB_srz) and rows 10 / 26 are discharged,
   the one open premise (row 19, the snprintf contract) names no sink head, so the statement names none; the proof term
   applies the walks (pb_bllvmf_libx and the callee walks) at SK := boxb_sink_head. *)
Ltac boxb_sink_gate T :=
  lazymatch T with
  | context [YI5b.src0_sink_head] => fail 0 "names the plain build's sink head YI5b.src0_sink_head"
  | context [YI5c.src0_sink] => fail 0 "names the plain build's sink record YI5c.src0_sink"
  | _ => idtac
  end.
Example boxb_sink_gate_ok : True.
Proof.
let T := type of TFIB_TB_closed in boxb_sink_gate T.
let t := eval unfold TFIB_TB_closed in TFIB_TB_closed in boxb_sink_gate t;
  lazymatch t with context [boxb_sink_head] => idtac | _ => fail 0 "TFIB_TB_closed does not take boxb_sink_head" end.
let t := eval unfold box_asan_ubsan_agrees in box_asan_ubsan_agrees in boxb_sink_gate t.
let t := eval unfold box_asan_ubsan_halts in box_asan_ubsan_halts in boxb_sink_gate t.
exact I.
Qed.
