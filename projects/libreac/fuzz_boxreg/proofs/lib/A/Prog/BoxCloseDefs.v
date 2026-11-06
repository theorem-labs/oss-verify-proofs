(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: moved verbatim from lib/A/Prog/BoxClose.v: its per-image values of
   fuzz_boxreg.asan and the five records of its named parts (box_core_A, box_alloc_A, box_asyms_A, box_startup_A,
   box_gshadow_A), with the Requires they need, so that a discharger of a row can Require them without requiring the
   closing. lib/A/Prog/BoxClose.v Require Exports this file; same text, same names. *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaRun BoxSyms BoxList BoxAddr BoxPa BoxImg BoxBase BoxPaLib BoxFrame BoxFrameImg BoxB BoxRo BoxLibX.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
Check ReadName RangeFree LowestFree LowestFreeBase
ReacBoxregInit ReacBoxregFind ReacBoxregDeclare ReacBoxregAdd ReacBoxregSetName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module RSNP := OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt.SnprintfDef.

(* ---- per-image values of fuzz_boxreg.asan ------------------------------------------------------------------------ *)
(* `ofl_head` (musl's open-file list head): .bss, 0x5f4608, 8 bytes. *)
Definition BOX_OFL_HEAD : Z := 0x5f4608.
Definition box_sink_head : YI16.sink_head := YI16.mkSinkHead BOX_OFL_HEAD.
(* The read-only range of the library contract: .data.rel.ro .. .got, [0x98958, 0x99bb0), the range of PI_box
   (cgif's convention, lib/A/Prog/BoxImg.v). *)
Definition BOX_RLO : Z := 0x98958.
Definition BOX_RHI : Z := 0x99bb0.
(* The 5 registered globals (asan_globals, 0x9d770 .. 0x9d8b0, five 64-byte records): (beginning, size). *)
Definition BOX_GLOBS : list (Z * Z) := [(0x20cc0, 6); (0x20ce0, 1); (0x20d00, 5); (0x20d40, 3); (0x20d60, 1)].
(* read_name's call of the malloc wrapper (jal at 0x8139c to 0x523ec) returns to 0x813a0. *)
Definition BOX_RN_MALLOC_RA : Z := 0x813a0.
(* musl memchr's two read-only 8-byte constants (.rodata, not owned): 0x10350 and 0x10368; the memchr contract's
   constant range (lib/A/Rt/MemchrDef.v amemchr_realizesM, lib/A/Rt/ConstsViewDef.v consts_view) is [0x10350, 0x10370). *)
Definition BOX_MCH_LO : Z := 0x10350.
Definition BOX_MCH_HI : Z := 0x10370.
(* LLVMFuzzerTestOneInput's own allocator calls, as offsets from box_text (0x7ff4c): the malloc wrapper call returns
   to 0x8011c (jal at 0x80118), the free wrapper calls to 0x80600, 0x80aac and 0x80e1c (jal at 0x805fc, 0x80aa8,
   0x80e18); grant's GE_MSITES / GE_FSITES form (a working branch GrantLibX.v:95). *)
Definition BOX_MSITES : list Z := [0x1d0].
Definition BOX_FSITES : list Z := [0x6b4; 0xb60; 0xed0].
(* __sanitizer::common_flags_dont_use (.bss 0x132aa8, 0x120 bytes); its byte at +0x4a decides whether
   InstallAtExitCheckLeaks registers the leak check's Atexit handler (a Theorem Labs lane 00:51Z). *)
Definition BOX_COMMON_FLAGS : Z := 0x132aa8.
(* cgif's XL0 (A/ACfi.v:56): the library contract's metering bounds. *)
Definition BXL0 : Z -> Z := fun _ => 0.

(* ---- the parts the closing rests on, one record per owner's part (lib/../provenance/OBLIGATIONS.md) ------------- *)
(* The relocated core's closed walk and its kit (owned by a Theorem Labs lane): cgif A/AD2o.v:42-84 (TFIB_T_of_partsXF over
   AD1q.v:79 tfib_srealizesX: LIBX -> TFIB_T, with the sink's inertness, row 9, as the driver's premise) and the core
   lemmas cgif's A/ACfi.v:85-100 / AD2o.v:43-46 / A/ACee.v:88 feed the program with: YCbp.v:21 ameter_triv_laws,
   YCbp.v:23 ameter_triv_fs_laws, the meter's zero costs at ameter_triv (cgif's XL0_HXL, A/ACfi.v:60-66; grant's
   grant_need), YE01.v:82 asink_none_kept and YE01.v:153 ameta_inv_kept (the sink and meta invariants kept over a
   journal), YG0t.v:472 astack_free_law_ok; the driver's exit (coreA_srz) also takes row 9, no LSan exit handler. *)
Record box_core_A (BA : asyms) (MT : ameter_ops) (SINKN : (word -> option byte) -> Model -> Prop)
  (METAI : alayout -> (word -> option byte) -> Z -> Prop) : Prop := {
  coreA_srz : (forall (FP : list (Z * Z)) (md md' : Model) (m : word -> option byte),
       ~ YI16.sink_open_fp FP -> aos_step FP md md' -> SINKN m md -> SINKN m md') ->
    (forall ly : alayout, In (z1 (ANum (BOX_COMMON_FLAGS + 0x4a)) 0) (as_const BA ly)) ->
    (forall rc : YM05.RunCeil,
      @tfib_lib_contract_x_all rc box_shape box_sink_head BA MT BXL0 BXL0 BOX_RLO BOX_RHI SINKN METAI) -> TFIB_T;
  coreA_mtl : ameter_laws MT;
  coreA_mtf : ameter_fs_laws MT;
  coreA_need : mo_malloc MT 288 + 64 * (mo_malloc MT 48 + mo_free MT) + mo_free MT <= 0;
  coreA_sinkn_kept : forall (rc : YM05.RunCeil) (fx : YK11.FPState) STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
    ajournal (SK := box_sink_head) box_segs BA STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
    ~ YI16.sink_open_fp FP -> SINKN (mrestrict (w_H W) mem) md -> SINKN (mrestrict (w_H W') mem') md';
  coreA_metai_kept : forall (rc : YM05.RunCeil) (fx : YK11.FPState) STK sp0 FP ly S W mem md own ly' S' W' mem' md' k M,
    ajournal (SK := box_sink_head) box_segs BA STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
    METAI ly (mrestrict (w_H W) mem) M -> METAI ly' (mrestrict (w_H W') mem') M;
  coreA_asf : forall (rc : YM05.RunCeil) (fx : YK11.FPState), astack_free_law box_segs BA }.
(* The allocator's two wrappers as the walks call them (cgif's released Reusable/YC5d.v:57 / :76 amalloc04_rule /
   afree04_rule over YG0d.v amalloc_realizes / afree_realizes; owner of the runtime's Allocate / Deallocate:
   a working branch). *)
Record box_alloc_A (BA : asyms) (MT : ameter_ops) : Prop := {
  alA_malloc : forall (rc : YM05.RunCeil) (fx : YK11.FPState), amalloc04_rule (SK := box_sink_head) box_segs BA MT;
  alA_free : forall (rc : YM05.RunCeil) (fx : YK11.FPState), afree04_rule (SK := box_sink_head) box_segs BA MT }.
(* The asyms record's fields the walk layer reads (owned by a Theorem Labs lane): cgif A/AD2l.v:14-37 TfibB, at fuzz_boxreg.asan's
   values (lib/A/Prog/BoxB.v box_code; GOT words and cells as BoxB.v box_PALib / box_PALibF take them). Each holds by
   reflexivity once boxreg's record is defined. *)
Record box_asyms_A (BA : asyms) : Prop := {
  asA_code : as_code BA = box_code;
  asA_got_shadow : as_got_shadow BA = 0x98eb8;
  asA_shadow_cell : as_shadow_cell BA = 0xa0f78;
  asA_got_uar : as_got_uar BA = 0x98f10;
  asA_uar_cell : as_uar_cell BA = 0xa0f80 }.
(* The start-up certificate's facts other than the globals' shadow, and the trace universe (owner: a Theorem Labs lane's
   generator run): the errno cell (cgif A/AF0m.v TFIB_ERRNO; A/ACfi.v:27-38 TfibB_libS) and the allocation-trace
   universe (cgif A/ACej.v:585 Tfib_universe_ok, A/AF0m.v:313-314 ts_universe / ts_universe_drv), with
   LLVMFuzzerTestOneInput's own allocator call traces (stA_htr, grant's HTR form, a working branch GrantLibX.v:95) and
   the state-free image bytes its callees read (stA_rom: ZERO 0x20cc0, read_mac.base 0x20d00, "%s" 0x20d40, musl
   memchr's constants 0x10350, the empty strings 0x20ce0 / 0x20d60; read-only bytes that are no owned static and no
   errno byte, so they hold once the record's owned statics and errno cell are fixed). *)
Record box_startup_A (BA : asyms) : Prop := {
  stA_errno : (0 <= as_errno BA /\ as_errno BA + 4 <= kLowMemEnd) /\
    (forall a, as_errno BA <= a < as_errno BA + 4 -> YG0d.in_img box_segs a);
  stA_uok : universe_ok (as_universe BA);
  stA_ra0 : In [pc_malloc_ra0 (as_code BA)] (as_universe BA) /\ In [pc_free_ra0 (as_code BA)] (as_universe BA);
  stA_rn : In [pc_malloc_ra0 (as_code BA); BOX_RN_MALLOC_RA] (as_universe BA);
  stA_htr : forall (ly : alayout) (regs regsT : bvmap 5 word) (pcf : Z),
    raZ regs = RA_LLVMF ->
    (pcf = pc_malloc_ra0 (as_code BA) /\ In (raZ regsT - box_text) BOX_MSITES) \/
    (pcf = pc_free_ra0 (as_code BA) /\ In (raZ regsT - box_text) BOX_FSITES) ->
    In (call_trace0 pcf regsT (if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []))
      (as_universe BA);
  stA_rom : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
    RSNP.asn_rom_bytes box_segs BA 0x20cc0 (map (fun b : byte => bv_unsigned b) Boxreg.zero6) /\
    RSNP.asn_rom_bytes box_segs BA 0x20d00 [0; 0x40; 0xab; 0; 0] /\
    RSNP.asn_rom_bytes box_segs BA 0x20d40 RSNP.ASN_FMT /\
    RSNP.asn_rom_bytes box_segs BA MCH_LO MCH_CONSTS /\
    RSNP.asn_rom_str box_segs BA 0x20ce0 [] /\ RSNP.asn_rom_str box_segs BA 0x20d60 [] }.
(* The start-up certificate's facts on the shadow of the image and of the registered globals (owned by a Theorem Labs lane; OPEN
   until boxreg's certificate gate, arrival + shadow step, passes for this image): cgif's form of GrantClose.v
   grant_img_shadow_vis / grant_globs_marked over the certificate's zero-shadow ranges and constant shadow cells. *)
Record box_gshadow_A (BA : asyms) : Prop := {
  gsA_isv : forall (rc : YM05.RunCeil) (fx : YK11.FPState), img_shadow_vis box_segs BA;
  gsA_glob : forall (rc : YM05.RunCeil) (fx : YK11.FPState), globs_marked box_segs BA BOX_GLOBS }.
