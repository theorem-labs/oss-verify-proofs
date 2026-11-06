(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/ProgWorld.v (a working branch 26edf006f53,
   re-synced to a working branch a48c4068c6e: SK as a Section variable of Fsteps / FsOfAstack / FstepsProofs,
   sections 14-18; then to 1d23ced37fd: ctl_gshadow_of_AR_stmt amended, ctl_global_shadow_of_AR_stmt added,
   ctl_frame_above_img_stmt premise-free with its proof moved to ProgWorld_Fs.v): the same definition / lemma names,
   Sections and proofs; lib.A.<X> -> lib.B.<X>, the core files
   A.AB1v / AE2k / ACfn / AF0m -> lib.Reusable.YB1v / YE2k / YCfn / YF0m; Section 0 restated with image B's
   (fuzz_ctrl.asan-ubsan) constants (REAL_USED from the B symtab), as_tsd_TSD's TSD restated (0x5fd9f8, B symtab);
   comments that cite image addresses cite image B's; the doubled lib/Lib modules named lib.Lib.X.  No statement
   differs from A's except by these module paths and those two constants.  Then to a working branch fec8db0a380
   (names only, no proof step changed): Z_to_bv_bv_unsigned (12 uses) and length_Z_to_le_bytes (1) written
   stdpp.bitvector.definitions.Z_to_bv_bv_unsigned / LinuxProcessSemantics.LinuxProcessSem.BvBase.length_Z_to_le_bytes,
   as A writes them -- in each case the constant `About` names at that use in this file (Locate / About probe, a Theorem Labs
   lane), so the doubled lib/Reusable/YK0h.v and lib/B/Reusable/YK0h.v copies of length_Z_to_le_bytes and the
   MState copies of Z_to_bv_bv_unsigned cannot be read in; Lib.ExecF Required as `From ...lib.Lib Require ExecF MState`,
   as A.  Then to a working branch 45b254caa11: the ANNOUNCED STATEMENT CHANGE of ctl_kept_cls (its high-memory
   class reads the run ceiling lib.Reusable.YM05.alloc_ceiling, not YK06's constant; Section 13) and the announced
   addition 19, ctl_const_vis_of_AR_stmt in Section ConstVis (statement only), with image B's row in its comment.
   Written by a Theorem Labs lane (a Theorem Labs lane; the 45b254caa11 mirror by a Theorem Labs lane); one writer. *)
(* lib/B/ProgWorld.v -- fuzz_ctrl image B (libreac v1.9.0, asan-ubsan): the cgif-world side of the callee lifts and of
   the runtime-cell hand-over.  Twin of a Theorem Labs lane's lib/A/ProgWorld.v: only Section 0 (image constants), the module paths, as_tsd_TSD's TSD constant
   and the image-specific comments differ.

   ITERATION-ONLY.  Statements are `Definition <name>_stmt : Prop`; no Axiom, no Parameter, no Admitted.  PROVED here
   (each cheap, type-check evidence on the planning core only, never acceptance): every Lemma below (the same set as
   image A's file).  Everything else is rule 24: no function proved.

   STATEMENT LIST (list owner a Theorem Labs lane, llvmf-cgif-walk-plan.md 2.4 and 4 (a working note, not in this delivery); requests two Theorem Labs lanes
   22:18Z..00:43Z, rt_of_core text a Theorem Labs lane 22:41Z (ctl_rt without mem_inv_at, 00:34Z), rulings three Theorem Labs lanes
   23:04Z..00:48Z).  Donor lemmas, premise sources, open questions:
   progworld-stmts.md (a working note, not in this delivery).
     Section ShadowGap   AR_states_vis0_shadow   (the one piece of ctl_rt's shadow_rw the core's AR does not state)
     Section RoView      ro_agree_of_view, AR_states_owned_ro          (read-only facts in the view form)
     Section RtOfCore    RT_used, ctl_RT (top level), rt_of_core          (only ctl_RT is named outside this file)
     Section CtlRt       ctlrt_of_AR                                      (M4: ACtlCut.ctl_rt at the entry and every cut)
     Section Fsteps      AR_of_fsteps, ajournal_of_fsteps                 (M3: across a lifted silent run)
     Section Visible     win_vis, win_sh_vis, heap_vis, heap_sh_vis,      (M5: the ProgLift range_visible premises;
                         frame_vis, glob_sh_vis                           PROVED by a Theorem Labs lane in ProgWorldVis*.v)
     Section ArodataP    arodata_okP_of_S                                 (ctl_base's arodata_okS -> the PA form)
     Section FsOfAstack  ctl_fs_geom, stack_malloc_classes (G4 gap), ctl_fs_of_astack (cid),
                         ctl_release_of_free_law (cid)                    (fake-stack call and inline release)
     Section RtPost      munch_vis, wmono_vis, rt_post_frame, ctl_post_{memset,memcpy,memchr,bcmp,strcmp,set_shadow}

   CLOSURE (porter 22:44Z, 23:38Z): every unit module is Required QUALIFIED, never Imported or Exported; no
   lib/AZ/AsanW, no W6, no SegCF / *_cfw / Cf* file, no frame-route file (lib/Lib/ExecF.v, shared with ProgBridge, pulls
   lib/AZ/LibA/AcctCore.v); neither AsanRTInv nor Contract is needed (RT narrowed to RT_used, APIf dropped).  Core names
   are written lib.Reusable.<file> / B.<file>.

   RT_used (two Theorem Labs lanes 23:05Z: the union of RT conjuncts the lifted runs' proofs CONSUME, directly or through a
   callee contract's premise; widened 02:10Z on the auditor a Theorem Labs lane's finding: F30F.v (a version not in this delivery; from a working branch e0a98c6447f),
   lib/A/Prog/Seg/R6F.v (at head lib/A/Prog/Seg/R6F.v:98-100) and lib/A/Prog/Seg/R9F.v (at head lib/A/Prog/Seg/R9F.v:178) (both written on a working branch b31dc485b96) pass a callee the fp premise (RcAsanFP.v:48-56), which expands through
   asan_tls_cells (asan_stack_malloc_c.v:38-51) and the TP word to opt / uw / fs cells; measurement rt-reads.md:22 (a working note, not in this delivery)).
   Sources in the core's world (cgif line numbers; the planning core keeps them) and, for image A, its v1.9 bytes (85
   cells, 54 image-initialised MATCH, 31 runtime-written MATCH by their init stores: rt-cells-v190.md (a working note, not in this delivery), a Theorem Labs lane;
   image B's cells are the same families over lib/B/AsanRT.v, not re-measured here).  The AF0m.v line numbers in the
   table are image A's file (lib/A/AF0m.v); image B's rows are the same rows of lib/Reusable/YF0m.v (a Theorem Labs lane's
   generated file of record, 8db247c6f3e), whose line numbers are not restated here:
     family / cells       consumed by the runs                      source in the core's world
     asan_cells (17)      yes (premise of every run; CELL_K,        am_const YG0n.v:210 over AF0m.v:79-85,87,95,96,111,
                          GOT_CELL_K, UAR, GOT_UAR by value)        174-178,185; AR_const_law YG0d.v:463-466
     shadow_rw            yes (premise; only own frame / block /   ahs_pres YG0n.v:441-445 EXCLUDES in_vis0, am_client :220;
                          global shadow loaded)                     vis0 shadow = hypothesis AR_states_vis0_shadow. OBLIGATION
                                                                    (two Theorem Labs lanes): start-up = a Theorem Labs lane's presence rows (KRWLAZY = present, a Theorem Labs lane 04:21Z; one extra interval open in 10/50 states, certificate side); step = Reusable/ShadowPresent.v (amalloc04 / afree04 / astack posts lack a presence clause, a Theorem Labs lane)
     asan_opt_cells (4)   yes (GOT_VERBOSITY, VERBOSITY via fp)     am_const AF0m.v:71,100,173,184
     asan_cf_cells (8)    yes (GOT_CF, CF+137 / +254 / +255)        am_const AF0m.v:34,38,40,45,47,60-62,67,172
     asan_uw_cells (5)    yes (TSD_KEY_INITED, TSD_KEY, TP-88,      am_const AF0m.v:88,89,92,132; symbolic :25
                          TSDMAIN via fp)                           (`c8 (ATp (-88)) (ATsd 0)`, `c8 (ATsd 0) (AC 0)`) +
                                                                    am_tsd YG0n.v:222
     asan_fs_cells (6)    yes (TLS_INDEX, DTLS_TPOFF, TP-8, TP+40,  am_const AF0m.v:101,115,116,133,135; symbolic :25-26;
                          TP word, TP+8 via fp)                     am_layout YG0n.v:208 for the FS / DB side conditions
     REAL_USED (4 slots)  yes (BCMP, MEMCMP, MEMCHR, TLS_GET_ADDR)  am_const AF0m.v:102-105 (stated REAL rows)
     asan_im_cells, asan_exit_cells, the other 35 REAL slots: consumed by no run nor callee premise (rt-reads.md (a working note, not in this delivery):
     no address literal nor name in 177 blobs; F34F, a stopped twin, only transports), so no as_const row is needed.
   CONSUMERS: the lifts' premises are produced from AR directly: asan_cells / shadow_rw / ro_agree by ctlrt_of_AR (as
   ACtlCut.ctl_rt), asan_tls_cells by ctl_tls_of_AR, the fp premise by ctl_fp_of_AR, asan_cf_cells / REAL_USED (the bcmp
   wrapper's aCL cells) by am_const as in rt_of_core.  ctl_RT / rt_of_core keep a Theorem Labs lane's 22:41Z glue text; its
   pilot (ACtlG/A5.v:70 (written on a working branch 8d0116e86e0)) does not use it yet.
   am_const states ctrl's rows only under the bundle law CtrlTSyms B (lib/Reusable/YF0m.v:2985, ts_const :3001; image
   A: A/AF0m.v:293, :308); the donor walk assumes only TfibLib B (A/ACfj.v:98), and no donor lemma links them for a
   generic B (the composition fixes B := CtrlB, CtrlB_syms AD2l.v:72), so rt_of_core and ctlrt_of_AR take CtrlTSyms B. *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YK04 YK04R YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YE01 YP09 YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.asan_stack_malloc_c B.Prog.RcAsanFP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v Reusable.YE2k Reusable.YCfn Reusable.YF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtlK B.ACtlCut B.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.rng_asan B.Prog.CtrlBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.AsanRT B.Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem Frame.
Local Open Scope Z_scope.
(* The journal's sink_head is the core's own instance, as lib.Reusable.YCfn resolves it (Reusable/YE2k.v:45);
   lib.Reusable.YE2k is only Required here, so its export instance is named explicitly. *)
#[local] Existing Instance lib.Reusable.YE2k.tfib_sink_head.

(* ---------------------------------------------------------------------------------------------------------
   0. Image constants (image B, fuzz_ctrl.asan-ubsan).  The twin changes only this section and the table above. *)
Notation segs := lib.Reusable.YB1v.tfibsegs (only parsing).    (* = B.Img0.rsegs = images.AsanUbsan.M.loaded_segments *)
(* the image hull [ImgBounds.IMG_LO, ImgBounds.IMG_HI) = [0x10000, 0x5fe000) (lib/B/Prog/ImgBounds.v:8-9):
   ProgBridge.img_vis_W *)
(* The REAL slots the runs read, from the B symtab (libreac-v190/asan-ubsan/fuzz_ctrl.nm.txt, each symbol + 0, an
   8-byte .data slot): REAL_BCMP 0xa2610 = __interception::real_bcmp, REAL_MEMCMP 0xa2608 = __interception::real_memcmp,
   REAL_MEMCHR 0xa2618 = __interception::real_memchr, REAL_TLS_GET_ADDR 0xa2690 = __interception::real___tls_get_addr.
   The same values are lib/B/Prog/bcmp_wrap_c.v:13-14, memchr_wrap_c.v:12 and asan_stack_malloc_c.v:17; their values
   are B.AsanRT.RT_REALS'. *)
Definition REAL_USED : list Z := [0xa2610; 0xa2608; 0xa2618; 0xa2690].

(* ---------------------------------------------------------------------------------------------------------
   1. The piece of ctl_rt's shadow_rw the core's AR does not state (named, a Theorem Labs lane 23:04Z): the presence of the
   visible vis0 shadow bytes (shadow of the allocator's T, C, D blocks, the region-info page, ly_extra zones).  No
   lifted run LOADS such a byte (rt-reads.md P4), but the runs state shadow_rw universally. *)
Section ShadowGap.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

Definition AR_states_vis0_shadow : Prop :=
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md,
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    forall a, B.AsanRT.in_shadow a -> lib.Reusable.YG0n.in_vis0 ly a ->
      lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false -> m (Z_to_bv 64 a) <> None.
End ShadowGap.

(* ---------------------------------------------------------------------------------------------------------
   1b. ctrl's read-only facts in the VIEW form (a Theorem Labs lane 23:56Z, via a Theorem Labs lane: no core change for rom_clean /
   store_clean).  ctrl's mem_inv (no byte of a read-only segment is present in mem) has no source in the core's
   world, and NO lifted run needs it at a cut: every mem_inv consumer is a callee contract premise, reached from
   `ro_agree m` (mrd m a = seg_rom a at read-only a) by MemNorm(F).evt(F)_normalize(_ro) + mem_inv_normalize, the
   route every v1.9 run already takes (R8F, F18F, F30F, R9F, R10BF, R18F, R19F, X12F, YTailF; rt-reads.md (a working note, not in this delivery));
   a callee post's `mem_inv m -> mem_inv m'` is dropped by every caller.  ro_agree IS the view form:
   ro_agree_of_view (PROVED) gets it from the core's aview.  The view facts come from (a) the kept read-only view
   arodata_okS / arodata_okP for non-owned read-only bytes (ctl_base, YCfn.v:41, kept by the journal:
   APostBase.arodata_ok_journalP), and (b) for OWNED read-only bytes, constant cells in the bundle's const table
   (a Theorem Labs lane generates them from the image), named here as AR_states_owned_ro until they land. *)
Section RoView.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

Lemma ro_agree_of_view : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte),
  (forall a : word, lib.Lib.Mem.ro_addr B.Img0.rsegs a = true ->
     lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m (bv_unsigned a) =
     option_map (fun b : byte => bv_unsigned b) (lib.Reusable.YK11.seg_rom segs a)) ->
  B.ACtlK.ro_agree_at m.
Proof.
  intros W m Hv a Ha. specialize (Hv a Ha).
  assert (Hh : lib.Reusable.YA0n.w_H W a = false).
  { destruct (lib.Reusable.YA0n.w_H W a) eqn:Hh; [|reflexivity]. exfalso.
    pose proof (lib.Reusable.YA0n.w_Hoff W a Hh) as Hoff. change lib.Reusable.YB1v.tfibsegs with B.Img0.rsegs in Hoff.
    unfold lib.Lib.Mem.ro_addr in Ha. rewrite Hoff in Ha. discriminate Ha. }
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in Hv.
  rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned, Hh in Hv.
  unfold lib.Lib.Mem.mrd. change (lib.Lib.PropExec.seg_rom B.Img0.rsegs a) with (lib.Reusable.YK11.seg_rom segs a).
  destruct (m a) as [b|] eqn:Em; [|reflexivity].
  destruct (lib.Reusable.YK11.seg_rom segs a) as [b'|] eqn:Er; cbn [option_map] in Hv; [|discriminate Hv].
  injection Hv as Hb. f_equal. apply bv_eq. exact Hb.
Qed.

(* (b) NAMED HYPOTHESIS (carried by ctlrt_of_AR and so by the top statement): every owned read-only byte reads its image
   byte through the view.  DISCHARGE (a Theorem Labs lane 23:56Z route (a); owners a Theorem Labs lane = rows, a Theorem Labs lane = lemma): pin image
   A's 54 read-only global redzones (all 0; owned-ro-redzones-A.md (a working note, not in this delivery)) as const rows, then am_const gives it. *)
Definition AR_states_owned_ro : Prop :=
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md,
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    forall a : word, lib.Lib.Mem.ro_addr B.Img0.rsegs a = true ->
      Exists (lib.Reusable.YG0n.in_zr (bv_unsigned a)) (lib.Reusable.YG0f.as_owned_static B) ->
      lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m (bv_unsigned a) =
      option_map (fun b : byte => bv_unsigned b) (lib.Reusable.YK11.seg_rom segs a).

(* The walk's carried runtime fact is ACtlCut.ctl_rt = asan_cells_at /\ shadow_rw_at /\ ro_agree_at (a Theorem Labs lane
   00:34Z: mem_inv_at dropped, on this file's measurement; the consumers take ro_agree, as above). *)
End RoView.

(* ---------------------------------------------------------------------------------------------------------
   2. The runtime-cell hand-over (a Theorem Labs lane 22:41Z; its glue cites ctl_RT and rt_of_core).  ctl_RT is RT_used, the
   narrowed RT (header table); its argument shape (sp, m, md) is kept for the glue.  Deltas from the 22:41Z text,
   forced by the type-check: ctlcx, ctl_base and c_sp take no segs and ctl_base takes no XN_LIB (ACtlCut with segs
   fixed to tfibsegs, as lib.Reusable.YCfn fixes it, ACfn.v:31); the closed form names the premises the proof needs.
   api_of_core / ctl_API: DROPPED (23:05Z; no machine-run lemma uses an AsanAllocAPI field, apif-measure.md). *)
Definition RT_used (m : word -> option byte) : Prop :=
  B.AsanRT.asan_cells m /\ B.AsanRT.shadow_rw m /\ B.AsanRT.asan_opt_cells m /\ B.AsanRT.asan_cf_cells m /\
  B.AsanRT.asan_uw_cells m /\ B.AsanRT.asan_fs_cells m /\
  Forall (fun p => In (fst p) REAL_USED ->
                   lib.Lib.Mem.bytes_at B.Img0.rsegs m (fst p) (lib.Lib.Mem.le8 (lib.Lib.Mem.wa (snd p)))) B.AsanRT.RT_REALS.
Definition ctl_RT (sp : Z) (m : word -> option byte) (md : Model) : Prop := RT_used m.

Section RtOfCore.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.
Variable MT : lib.Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable FP : list (Z * Z).

(* Proof plan: AR at the cut is ajournal's first conjunct (YCbq.v:352); asan_cf_cells and the REAL_USED slots from
   am_const (YG0n.v:210) under CtrlTSyms (YF0m.v:3001 ts_const) through the aview -> mrd bridge (w_Hoff); asan_cells and
   shadow_rw from ctl_rt. *)
Definition rt_of_core_stmt : Prop :=
  lib.Reusable.YF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B ->
  forall (cx : B.ACtlCut.ctlcx) (own : list (Z * Z)) (k : Z) ly3 S3 W3 (ms3 : machine_state) md3,
    B.ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
    lib.Reusable.YCbq.ajournal segs B lib.Reusable.YCfn.LLVMF_STK (B.ACtlCut.c_sp cx) FP
      (B.ACtlCut.c_ly cx) (B.ACtlCut.c_S cx) (B.ACtlCut.c_W cx) (B.ACtlCut.c_mem cx) (B.ACtlCut.c_md cx)
      own ly3 S3 W3 (ms_mem ms3) md3 k ->
    B.ACtlCut.ctl_rt (ms_mem ms3) ->
    ctl_RT (lib.Reusable.YG0d.spZ (ms_regs ms3)) (ms_mem ms3) md3.

(* The thread cells the stretches take as `asan_tls_cells m TP DT TS C T DB k` (asan_stack_malloc_c.v:38-51; a Theorem Labs lane
   02:05Z).  Every cell is an am_const row (YG0n.v:210) of the planning core's AF0m.v: absolute rows :117-118
   (TLS_INDEX), :112 (REAL_TLS_GET_ADDR), :90-91 (TSD_KEY_INITED, TSD_KEY = 0, so k = 0), :174 / :101 (GOT_CF, CF+137),
   :186 / :102 (GOT_VERBOSITY, VERBOSITY), :103 (DTLS_TPOFF), :135 (TP-8 = DT = TP+32), :137 (DT+8 = TP+2048), :134
   (TP-88 = TS); symbolic rows :26-28 (TS+0 -> C = ly_C, C+152 -> T = ly_T, T+48 / T+56, TP+8 -> DB = ly_D, DB+24 -> TP).
   AR restates them at EVERY state (after a fake-stack malloc: astack_malloc_realizes' AR at S'; after the release:
   ctl_release_of_free_law's journal; after malloc / free: the next ajournal), so no frame condition and no carried
   `fl_tls_same` is needed across those calls: the stretch after the call takes them at its own base memory from this. *)
Definition ctl_tls_of_AR_stmt : Prop :=
  lib.Reusable.YF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md,
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    exists DT TS C T DB : word, B.Prog.asan_stack_malloc_c.asan_tls_cells m B.AsanRT.RT_TP DT TS C T DB 0.

(* The fp premise of every callee that calls __asan_stack_malloc_c (RcAsanFP.v:48-56; consumers F30F.v:247 / :350,
   R6F.v:97-99, R9F.v:174, and the lifts of the fake-stack callees), from AR: asan_tls_cells by ctl_tls_of_AR's rows
   with DT = TP+32, TS = ly_tsd, C = ly_C, T = ly_T, DB = ly_D, k = 0; the TP word = ly_F (symbolic row `c8 (ATp 0)
   (AF 0)`, YF0m.v:25); fs_place from am_areas (AF 0, kFakeStackSize) (YG0n.v:136); FS+88 = kStackSizeLog = 20 and
   FS+96 = 0 from am_cells over fs_cells (YG0n.v:100-102); fp_cls (the hint word and flags of each class) from am_cells
   and am_flags (YG0n.v:152-154).  The window and disjointness premises are the caller's. *)
Definition ctl_fp_of_AR_stmt : Prop :=
  lib.Reusable.YF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md (cs : list nat) (lo hi : Z)
         (Wr D : list lib.Lib.Frame.ivl),
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    Forall (fun c => (c <= 6)%nat) cs ->
    lib.Reusable.YG0f.ly_F ly + B.Prog.asan_stack_malloc_c.FS_SIZE <= lo ->
    (forall a, lo <= a < hi -> B.AsanRT.app_mem a) ->
    B.Prog.RcAsanFP.fp_dj Wr
      (B.Prog.RcAsanFP.fp_tls B.AsanRT.RT_TP (Z_to_bv 64 (B.AsanRT.RT_TP + 32)) (Z_to_bv 64 (lib.Reusable.YG0f.ly_tsd ly))
         (Z_to_bv 64 (lib.Reusable.YG0f.ly_C ly)) (Z_to_bv 64 (lib.Reusable.YG0f.ly_T ly))
         (Z_to_bv 64 (lib.Reusable.YG0f.ly_D ly)) 0 ++
       (lib.Reusable.YG0f.ly_F ly, B.Prog.asan_stack_malloc_c.fs_frame (lib.Reusable.YG0f.ly_F ly) 0 0) :: nil) ->
    B.Prog.RcAsanFP.fp_dj D (B.Prog.RcAsanFP.fp_w cs (lib.Reusable.YG0f.ly_F ly)) ->
    B.Prog.RcAsanFP.fp cs m B.AsanRT.RT_TP (lib.Reusable.YG0f.ly_F ly) lo hi Wr D.
End RtOfCore.

(* ---------------------------------------------------------------------------------------------------------
   3. M4: the walk's runtime fact ACtlCut.ctl_rt (asan_cells_at /\ shadow_rw_at /\ ro_agree_at) from AR, one statement.
   Instances: at the entry AR is the first conjunct of afn_pre in ctl_base (YCfn.v:32-44, YCbq.v:336) and the
   read-only view is ctl_base's arodata_okS (YCfn.v:40); after each of the six world steps of image B's LLVMF
   (asan-ubsan objdump: malloc 0x81760 / 0x81f4c, free 0x81a9c / 0x82d18, __asan_stack_malloc_6 at 0x8108c, the
   class-6 frame release __asan_stack_free_6 at 0x82f48) AR is the
   first conjunct of the next cut's ajournal (YCbq.v:352) and the view is kept by APostBase.arodata_ok_journalP.  No
   earlier ctl_rt is used.  ro_agree_at comes through ro_agree_of_view; the errno word (as_errno, excluded by
   arodata_okP) lies in a writable segment, a CtrlTSyms fact (ts_errno) checked by computation in the proof. *)
Section CtlRt.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

Definition ctlrt_of_AR_stmt : Prop :=
  lib.Reusable.YF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B -> AR_states_vis0_shadow B -> AR_states_owned_ro B ->
  forall (RLO RHI : Z) ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md,
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    B.Prog.CtrlBase.arodata_okP segs RLO RHI B (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m) ->
    B.ACtlCut.ctl_rt m.
End CtlRt.

(* ---------------------------------------------------------------------------------------------------------
   4. M3 (a Theorem Labs lane 23:53Z: ajournal_of_fsteps): AR and the caller's journal across a lifted silent run, a YK04R.fsteps
   run whose footprint avoids w_H (the run SRr_fevt lifts), with its writes confined to the interval list WR of the
   callee post's `munch WR m m'` (lib/Lib/Frame.v:71).  Donor lemmas followed: A/AD1y.v:99 AR_after_run (through
   AR_frame_law YG0d.v:438-445, then A/AD1y.v:139 AR_same_but_materialized) and YCbq.v:515 ajournal_after_write; the
   hidden bytes are kept by YK04R.fsteps_restrict (second conjunct), and no step removes a byte. *)
Section Fsteps.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.

Definition AR_of_fsteps_stmt : Prop :=
  lib.Reusable.YG0d.AR_laws segs B -> lib.Reusable.YK04.wx_segs_nowrap segs ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (ms ms' : machine_state) md md' RNG (WR : list lib.Lib.Frame.ivl),
    lib.Reusable.YG0n.AR segs B ly S W (ms_mem ms) md ->
    lib.Reusable.YK04R.fsteps segs RNG ms ms' ->
    lib.Reusable.YK04R.fp_avoids (lib.Reusable.YA0n.w_H W) RNG ->
    lib.Lib.Frame.munch WR (ms_mem ms) (ms_mem ms') ->
    lib.Reusable.YK04.same_but_materialized md md' ->
    (forall a, 0 <= a < 2 ^ 64 -> lib.Reusable.YG0n.aowned B ly S a -> lib.Lib.Frame.outside WR a) ->
    lib.Reusable.YG0n.AR segs B ly S W (ms_mem ms') md'.

Definition ajournal_of_fsteps_stmt : Prop :=
  lib.Reusable.YG0d.AR_laws segs B -> lib.Reusable.YK04.wx_segs_nowrap segs ->
  forall STK sp0 (FPj : list (Z * Z)) ly S (W : lib.Reusable.YA0n.world segs) mem md own lyc Sc
         (Wc : lib.Reusable.YA0n.world segs) (ms ms' : machine_state) mdc mdc' k RNG (WR : list lib.Lib.Frame.ivl),
    lib.Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FPj ly S W mem md own lyc Sc Wc (ms_mem ms) mdc k ->
    lib.Reusable.YK04R.fsteps segs RNG ms ms' ->
    lib.Reusable.YK04R.fp_avoids (lib.Reusable.YA0n.w_H Wc) RNG ->
    lib.Lib.Frame.munch WR (ms_mem ms) (ms_mem ms') ->
    lib.Reusable.YK04.same_but_materialized mdc mdc' ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ lib.Lib.Frame.outside WR a ->
       lib.Reusable.YCbq.awr_byte STK sp0 FPj (lib.Reusable.YG0d.ablocks B ly S)
         (lib.Reusable.YG0d.ablocks B lyc Sc) lyc own a) ->
    lib.Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FPj ly S W mem md own lyc Sc Wc (ms_mem ms') mdc' k.
End Fsteps.

(* ---------------------------------------------------------------------------------------------------------
   5. M5: the visibility premises of the lifts (a working branch lib/A/ProgLift/<f>.v): each
   conclusion has exactly the ProgLift shape `range_visible (w_H W) lo len`, and for a shadow word cover
   `n = 0 \/ range_visible (w_H W) (sh_al8_lo p) (sh_al8_hi p n - sh_al8_lo p)` (rng_asan.v:80-81).  The other
   premise forms of the lifts (RT_LO..RT_HI, CELL_K 8, GOT_CELL_K 8, an exact shadow range `(p / 8 + ASAN_K)
   ((p + n - 1) / 8 - p / 8 + 1)`) are sub-ranges of these, by ProgBridge.range_visible_sub (4034df3a2b8); image and RT
   visibility are ProgBridge.img_vis_W / rt_vis_W, discharged inside the lifts.  So only the run-dependent ranges are
   stated here: win_vis / win_sh_vis (V1), heap_vis (V3), heap_sh_vis (V4), frame_vis (V5), glob_sh_vis (V6), all PROVED by
   a Theorem Labs lane (a working branch 25e7c792306, ProgWorldVis{Win,Heap,Frame}.v; Required by consumers, not here). *)
Section Visible.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

(* img_vis (V2, a Theorem Labs lane's image condition): NOT stated here.  It is a Theorem Labs lane's ProgBridge.img_vis_W
   (a working branch 7b850582d6a): `forall W : world rsegs, range_visible (w_H W) ImgBounds.IMG_LO
   (ImgBounds.IMG_HI - ImgBounds.IMG_LO)`, from w_Hoff and rsegs tiling the hull [0x10000, 0x5fe000); no top-pre
   conjunct and no wle argument are needed.  Consumers cite img_vis_W directly. *)

(* win_vis: the callee's stack window, from the cut's journal (YCbq.v:368; bounds astk_ok :333-335).  a Theorem Labs lane's
   window condition `range_visible (w_H W) (sp - K) K` is the instance lo = sp - K, len = K. *)
Definition win_vis_stmt : Prop :=
  forall STK sp0 (FPj : list (Z * Z)) ly S (W : lib.Reusable.YA0n.world segs) mem md own lyc Sc
         (Wc : lib.Reusable.YA0n.world segs) memc mdc k lo len,
    lib.Reusable.YCbq.ajournal segs B STK sp0 FPj ly S W mem md own lyc Sc Wc memc mdc k ->
    sp0 - STK <= lo -> lo + len <= sp0 ->
    B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H Wc) lo len.

(* win_sh_vis: the window's shadow word cover, from the stack entry of zero_shadow_ranges (YG0n.v:187-188) through
   AR_zshadow_law (YG0d.v:434-437); the stack bounds are page-aligned (layout_ok YG0f.v:321-323). *)
Definition win_sh_vis_stmt : Prop :=
  lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) mem md lo len,
    lib.Reusable.YG0n.AR segs B ly S W mem md ->
    lib.Reusable.YG0f.ly_stk_lo ly <= lo -> lo + len <= lib.Reusable.YG0f.ly_stk_hi ly -> 0 <= len ->
    len = 0 \/ B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W)
                 (B.Prog.rng_asan.sh_al8_lo lo)
                 (B.Prog.rng_asan.sh_al8_hi lo len - B.Prog.rng_asan.sh_al8_lo lo).

(* heap_vis: bytes of a live heap block, from AR_blocks_law (YG0d.v:422-428). *)
Definition heap_vis_stmt : Prop :=
  lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) mem md p n lo len,
    lib.Reusable.YG0n.AR segs B ly S W mem md ->
    In (p, n) (lib.Reusable.YG0d.ablocks B ly S) ->
    p <= lo -> lo + len <= p + lib.Reusable.YG00.req_size n ->
    B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) lo len.

(* heap_sh_vis: the shadow word cover of a sub-range of a live heap block, from AR_shadow_law's shadow_hull_vis
   (YG0d.v:429-433, :309-310). *)
Definition heap_sh_vis_stmt : Prop :=
  lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) mem md p n lo len,
    lib.Reusable.YG0n.AR segs B ly S W mem md ->
    In (p, n) (lib.Reusable.YG0d.ablocks B ly S) ->
    p <= lo -> lo + len <= p + lib.Reusable.YG00.req_size n -> 0 <= len ->
    len = 0 \/ B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W)
                 (B.Prog.rng_asan.sh_al8_lo lo)
                 (B.Prog.rng_asan.sh_al8_hi lo len - B.Prog.rng_asan.sh_al8_lo lo).

(* frame_vis: bytes of a live fake frame, and the shadow word cover of a sub-range whose 64-byte hull lies in the
   frame, from AR_frames_law (YG0d.v:446-454; the law gives only frame_addr mod 32 = 0). *)
Definition frame_vis_stmt : Prop :=
  lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) mem md cid pos lo len,
    lib.Reusable.YG0n.AR segs B ly S W mem md ->
    In (cid, pos) (lib.Reusable.YG01.frames S) ->
    lib.Reusable.YG0f.frame_addr ly cid pos <= lo ->
    lo + len <= lib.Reusable.YG0f.frame_addr ly cid pos + lib.Reusable.YG00.fs_frame_bytes cid ->
    B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) lo len /\
    (0 <= len -> lib.Reusable.YG0f.frame_addr ly cid pos <= 64 * (lo / 64) ->
     64 * ((lo + len - 1) / 64) + 64 <= lib.Reusable.YG0f.frame_addr ly cid pos + lib.Reusable.YG00.fs_frame_bytes cid ->
     len = 0 \/ B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W)
                  (B.Prog.rng_asan.sh_al8_lo lo)
                  (B.Prog.rng_asan.sh_al8_hi lo len - B.Prog.rng_asan.sh_al8_lo lo)).

(* glob_sh_vis: the shadow word cover of an image global listed in the bundle's as_zero_shadow (YG0n.v:188), from
   AR_zshadow_law (YG0d.v:434-437), when the 64-byte hull of [lo, lo + len) lies in the zero-shadow range. *)
Definition glob_sh_vis_stmt : Prop :=
  lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) mem md r lo len,
    lib.Reusable.YG0n.AR segs B ly S W mem md ->
    In r (lib.Reusable.YG0f.as_zero_shadow B) ->
    0 <= len -> fst r <= 64 * (lo / 64) -> 64 * ((lo + len - 1) / 64) + 64 <= fst r + 8 * (snd r / 8) ->
    len = 0 \/ B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W)
                 (B.Prog.rng_asan.sh_al8_lo lo)
                 (B.Prog.rng_asan.sh_al8_hi lo len - B.Prog.rng_asan.sh_al8_lo lo).
End Visible.

(* ---------------------------------------------------------------------------------------------------------
   6. The read-only data fact, from the cut shell's form to the PA layer's (two Theorem Labs lanes, 23:37Z).  Donor: the
   walk's Section hypothesis HRO (A/ACfj.v:119) and its instance tfib_HRO (A/ACfi.v:52-53, proof `exact (H a Ha)`).
   ctl_base carries `arodata_okS segs B RLO RHI` (YCfn.v:41); the PA layer reads `arodata_okP SEGS rlo rhi B`
   (APostBase, aliased in lib/B/Prog/CtrlBase.v).  The bodies are the same; the PA range must lie inside [RLO, RHI).
   NOTE (image B): the PA layer sets [pa_relro_lo, pa_relro_hi) := [0x9f168, 0xa15e8) (lib/B/Prog/CtrlImg.v:100-101,
   the GNU_RELRO span) while the core's [RLO, RHI) is [0x9f1a0, 0xa15e8) (lib/B/ACtlK.v:17: .data.rel.ro's start to
   the GNU_RELRO filesz end), so the instance at (pa_relro_lo, pa_relro_hi) does NOT follow: RLO <= pa_relro_lo fails,
   [0x9f168, 0x9f1a0) (.init_array / .fini_array / .preinit_array) lies below RLO. *)
Section ArodataP.
Variable B : lib.Reusable.YG0f.asyms.

Lemma arodata_okP_of_S : forall (RLO RHI rlo rhi : Z) (rd : lib.Reusable.YG0f.reader),
  lib.Reusable.YE01.arodata_okS segs B RLO RHI rd -> RLO <= rlo -> rhi <= RHI ->
  B.Prog.CtrlBase.arodata_okP segs rlo rhi B rd.
Proof.
  intros RLO RHI rlo rhi rd H Hl Hh a Ha. apply H.
  destruct Ha as [Ha|Ha]; [left; exact Ha | right; lia].
Qed.
End ArodataP.

(* ---------------------------------------------------------------------------------------------------------
   7. The fake-stack call and its release (a Theorem Labs lane 23:22Z; names a Theorem Labs lane 23:28Z: ctl_fs_of_astack with the
   size class as an argument).  The core's world speaks of frame_addr / flag_addr / ly_F; ctrl's stretches speak of
   fs_frame / fs_flag / fs_hint over the side stack FS (asan_stack_malloc_c.v:26-31).  FS := ly_F ly (the TLS word at
   as_tp B holds it: YF0m.v:25 `c8 (ATp 0) (AF 0)`), j := pos.  Draft and gaps: fs-of-astack.md (a working note, not in this delivery) (G1: the
   stretch after the call is re-based at the return memory, since the core's posts are view-level; G2 / G3: two
   stretches must be restated; G4: aa_stack_malloc covers only classes 1 and 2, cgif lib/YG0d.v:535).  Image A has one such
   stretch (reac_ctrl_parseF.v, class 1); the split points a Theorem Labs lane found are image B's. *)
Section FsOfAstack.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.

(* The class geometry, ctrl's numerals against the core's (a Theorem Labs lane's M9: no such lemma on that lane's refs;
   closed arithmetic). *)
Definition ctl_fs_geom_stmt : Prop :=
  forall (FS cid pos : Z), 0 <= cid <= 10 ->
    B.Prog.asan_stack_malloc_c.fs_M (Z.to_nat cid) = lib.Reusable.YG00.fs_frames cid /\
    B.Prog.asan_stack_malloc_c.fs_B (Z.to_nat cid) = lib.Reusable.YG00.fs_frame_bytes cid /\
    B.Prog.asan_stack_malloc_c.fs_frame FS (Z.to_nat cid) pos = FS + lib.Reusable.YG0f.fs_frame_off cid pos /\
    B.Prog.asan_stack_malloc_c.fs_flag FS (Z.to_nat cid) pos = FS + lib.Reusable.YG0f.fs_flag_off cid pos /\
    B.Prog.asan_stack_malloc_c.fs_hint FS (Z.to_nat cid) = FS + 8 * cid /\
    B.Prog.asan_stack_malloc_c.FS_SIZE = lib.Reusable.YG0f.kFakeStackSize /\
    (forall a, B.AsanRT.shadow_addr a = lib.Reusable.YG0f.shadow_addr a).

(* G4, named gap (a Theorem Labs lane 00:48Z): the stack-malloc contract for ctrl's four classes.  The planning core's API record
   covers only classes 1 and 2 (cgif lib/YG0d.v:535, cgif's form); a Theorem Labs lane's core post-pass takes, from a working branch f7bc5928423, the
   YG0d.v:536 line (`pc_stack_malloc (as_code B) cid <> 0 -> astack_malloc_realizes segs B cid`) with ctrl's image-B
   map 0 / 1 / 2 / 6 = 0x3d6f4 / 0x3d868 / 0x3d9f8 / 0x3db94 (lib/B/Prog/asan_stack_malloc_c.v (at head lib/B/Prog/asan_stack_malloc_c.v:8-11),
   ASAN_STACK_MALLOC_<cid>); then this follows from aa_stack_malloc. *)
Definition stack_malloc_classes : Prop :=
  forall cid, cid = 0 \/ cid = 1 \/ cid = 2 \/ cid = 6 -> lib.Reusable.YG0d.astack_malloc_realizes segs B cid.

(* PROVED (cheap, type-check evidence on the planning core only): case split over the 11 classes. *)
Lemma ctl_fs_geom : ctl_fs_geom_stmt.
Proof.
  intros FS cid pos Hc.
  unfold B.Prog.asan_stack_malloc_c.fs_M, B.Prog.asan_stack_malloc_c.fs_B, B.Prog.asan_stack_malloc_c.fs_frame,
    B.Prog.asan_stack_malloc_c.fs_flag, B.Prog.asan_stack_malloc_c.fs_hint, B.Prog.asan_stack_malloc_c.FS_SIZE,
    lib.Reusable.YG00.fs_frames, lib.Reusable.YG00.fs_frame_bytes, lib.Reusable.YG0f.fs_frame_off,
    lib.Reusable.YG0f.fs_flag_off, lib.Reusable.YG0f.kFakeFramesOff,
    lib.Reusable.YG0f.kFakeFlagsOff, lib.Reusable.YG0f.kFakeStackSize, lib.Reusable.YG00.kStackSizeLog,
    B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
  unfold B.Prog.asan_stack_malloc_c.fs_B, lib.Reusable.YG00.fs_frame_bytes.
  assert (Hfl : 2 ^ 15 - 2 ^ (15 - cid) = lib.Reusable.YG0f.fs_flags_off cid).
  { assert (H : cid = 0 \/ cid = 1 \/ cid = 2 \/ cid = 3 \/ cid = 4 \/ cid = 5 \/ cid = 6 \/ cid = 7 \/ cid = 8 \/
                cid = 9 \/ cid = 10) by lia.
    destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]];
      vm_compute; reflexivity. }
  rewrite !Z2Nat.id by lia.
  repeat rewrite Z.shiftl_mul_pow2 by lia.
  split; [replace (20 - 6 - cid) with (14 - cid) by lia; ring|].
  split; [ring|]. split; [ring|]. split; [lia|]. split; [ring|]. split; [reflexivity|].
  intros a; ring.
Qed.

(* After __asan_stack_malloc_<cid>: the frame facts the stretch after the call takes, at the return memory mem'.
   Premises: the cut before the call (ecall_pre), the model step (the new frame (cid, pos)), and the pieces of
   astack_malloc_realizes' post (YG0d.v:284-299).  L is the call's request size. *)
Definition ctl_fs_of_astack_stmt (cid : Z) : Prop :=
  ctl_fs_geom_stmt -> lib.Reusable.YG0d.AR_laws segs B -> 0 <= cid <= 6 ->
  forall ly S S' (W : lib.Reusable.YA0n.world segs) (regs regs' : bvmap 5 word)
         (mem mem' : word -> option byte) md md' (pos lo L : Z),
    lib.Reusable.YG0d.ecall_pre segs B ly S W regs mem md ->
    lib.Reusable.YG0f.ly_stk_lo ly <= lo -> lo <= lib.Reusable.YG0d.spZ regs - lib.Reusable.YG0d.ESTACK ->
    (forall a, lo <= a < lib.Reusable.YG0d.spZ regs - lib.Reusable.YG0d.ESTACK ->
       lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem a) ->
    lib.Reusable.YG01.frames S' = (cid, pos) :: lib.Reusable.YG01.frames S ->
    ~ In (cid, pos) (lib.Reusable.YG01.frames S) ->
    lib.Reusable.YG0n.AR segs B ly S' W mem' md' ->
    lib.Reusable.YK11.getr regs' 10 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.frame_addr ly cid pos) ->
    lib.Reusable.YG0v.zero_shadow (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem')
      lib.Reusable.YG0f.SHADOW_OFF (lib.Reusable.YG0f.frame_addr ly cid pos) (lib.Reusable.YG00.fs_frame_bytes cid) ->
    lib.Reusable.YG0d.rdword (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem')
      (lib.Reusable.YG0f.frame_addr ly cid pos + lib.Reusable.YG00.fs_frame_bytes cid - 8) =
      Some (lib.Reusable.YG0f.flag_addr ly cid pos) ->
    (forall a, lib.Reusable.YG0d.spZ regs - lib.Reusable.YG0d.ESTACK <= a < lib.Reusable.YG0d.spZ regs ->
       lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem' a) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ lib.Reusable.YG0n.aowned B ly S a -> ~ lib.Reusable.YG0n.aowned B ly S' a ->
       ~ (lib.Reusable.YG0d.spZ regs - lib.Reusable.YG0d.ESTACK <= a < lib.Reusable.YG0d.spZ regs) ->
       lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem' a = lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem a) ->
    1 <= L <= lib.Reusable.YG00.fs_frame_bytes cid ->
    let c := Z.to_nat cid in
    let FS := lib.Reusable.YG0f.ly_F ly in
    let fr := B.Prog.asan_stack_malloc_c.fs_frame FS c pos in
    let n := B.Prog.asan_stack_malloc_c.fs_B c in
    0 <= pos < B.Prog.asan_stack_malloc_c.fs_M c /\
    lib.Reusable.YK11.getr regs' 10 = Z_to_bv 64 fr /\
    lib.Lib.Mem.bytes_at B.Img0.rsegs mem' (B.Prog.asan_stack_malloc_c.fs_flag FS c pos) (Z_to_bv 8 1 :: nil) /\
    lib.Lib.Mem.bytes_at B.Img0.rsegs mem' (fr + n - 8)
      (lib.Lib.Mem.le8 (Z_to_bv 64 (B.Prog.asan_stack_malloc_c.fs_flag FS c pos))) /\
    lib.Lib.Mem.bytes_at B.Img0.rsegs mem' (B.AsanRT.shadow_addr fr) (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8))) /\
    B.AsanRT.addressable mem' fr L /\
    lib.Lib.Frame.stk B.Img0.rsegs mem' fr (fr + n) /\
    (forall a, fr <= a < fr + n -> B.AsanRT.app_mem a) /\
    fr mod 64 = 0 /\ FS <= fr /\ fr + n <= FS + B.Prog.asan_stack_malloc_c.FS_SIZE /\
    B.Prog.asan_stack_malloc_c.ASAN_GT <= fr /\
    lib.Lib.Frame.stk B.Img0.rsegs mem' lo (lib.Reusable.YG0d.spZ regs).

(* The inline release, as a JOURNAL step usable mid-run inside a lifted stretch (a Theorem Labs lane 00:39Z): the fsteps twin
   of the core's aj_flag_store (YCbq.v:2362-2378).  A footprint run over the cut's memory whose writes are the cut's
   awr bytes or the frame's flag byte, ending with the flag byte 0, switches the journal to stack_free_state at the
   store (own drops (cid, pos)).  ctrl's stretch stores at fs_flag FS c pos; ctl_fs_geom_stmt turns that into the
   core's flag_addr.  Sites (B): model_block bodyF.v:352, catalogue_match cm_exit:1272, identity_reply E3, lay_block
   ly_epi_side:1429, and image B's class-6 release in LLVMF (__asan_stack_free_6 at 0x82f48). *)
Definition ctl_release_of_free_law_stmt (cid : Z) : Prop :=
  lib.Reusable.YG0d.AR_laws segs B -> lib.Reusable.YG0d.astack_free_law segs B ->
  lib.Reusable.YK04.wx_segs_nowrap segs -> 0 <= cid ->
  forall STK sp0 (FPj : list (Z * Z)) ly S (W0 : lib.Reusable.YA0n.world segs) mem md own' lyc Sc
         (W : lib.Reusable.YA0n.world segs) (ms ms' : machine_state) mdc mdc' k pos RNG (WR : list lib.Lib.Frame.ivl),
    lib.Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FPj ly S W0 mem md ((cid, pos) :: own') lyc Sc W (ms_mem ms) mdc k ->
    lib.Reusable.YK04R.fsteps segs RNG ms ms' ->
    lib.Reusable.YK04R.fp_avoids (lib.Reusable.YA0n.w_H W) RNG ->
    lib.Lib.Frame.munch WR (ms_mem ms) (ms_mem ms') ->
    lib.Reusable.YK04.same_but_materialized mdc mdc' ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ lib.Lib.Frame.outside WR a ->
       lib.Reusable.YCbq.awr_byte STK sp0 FPj (lib.Reusable.YG0d.ablocks B ly S) (lib.Reusable.YG0d.ablocks B lyc Sc)
         lyc ((cid, pos) :: own') a \/ a = lib.Reusable.YG0f.flag_addr lyc cid pos) ->
    lib.Reusable.YP09.mbyte segs (ms_mem ms') (lib.Reusable.YG0f.flag_addr lyc cid pos) = Some (Z_to_bv 8 0) ->
    lib.Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FPj ly S W0 mem md own' lyc
      (lib.Reusable.YG01.stack_free_state cid pos Sc) W (ms_mem ms') mdc' k.

(* The side-stack facts at ANY state with AR (a Theorem Labs lane 01:36Z): the flag bytes, the hint words and the whole side
   stack's stk are allocator-OWNED bytes (owned_extents YG0f.v:294-297 contains (ly_F, kFakeStackSize)), so no frame
   condition keeps them across a fake-stack malloc (astack_malloc_realizes' keeps only non-owned bytes, YG0d.v:298-299)
   nor across an allocator call (acall_kept).  AR restates them at every state instead: am_flags / fs_flags_ok
   (YG0n.v:152-154, :215: every flag reads 1 iff live), am_cells over fs_cells (:99-102: the 11 hint words), am_areas
   over (AF 0, kFakeStackSize) (:136: every side-stack byte visible and present; above the image, so off the segments
   and writable).  A stretch takes them at its own base memory from this lemma, never by raw munch from an earlier
   memory. *)
Definition ctl_fs_of_AR_stmt : Prop :=
  ctl_fs_geom_stmt -> lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md,
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    B.Prog.asan_stack_malloc_c.ASAN_GT <= lib.Reusable.YG0f.ly_F ly ->
    let FS := lib.Reusable.YG0f.ly_F ly in
    lib.Lib.Frame.stk B.Img0.rsegs m FS (FS + B.Prog.asan_stack_malloc_c.FS_SIZE) /\
    (forall (c : nat) (j : Z), (c <= 10)%nat -> 0 <= j < B.Prog.asan_stack_malloc_c.fs_M c ->
       lib.Lib.Mem.bytes_at B.Img0.rsegs m (B.Prog.asan_stack_malloc_c.fs_flag FS c j)
         (Z_to_bv 8 (if lib.Reusable.YG00.mem_pos (lib.Reusable.YG01.frames S) (Z.of_nat c) j then 1 else 0) :: nil)) /\
    (forall c : nat, (c <= 10)%nat ->
       exists h : word, lib.Lib.Mem.bytes_at B.Img0.rsegs m (B.Prog.asan_stack_malloc_c.fs_hint FS c) (lib.Lib.Mem.le8 h)).
End FsOfAstack.

(* ---------------------------------------------------------------------------------------------------------
   8. Runtime-call posts -> the premises of the next _F run (two Theorem Labs lanes 00:33Z-00:36Z; names
   ctl_post_<runtime callee>; call sites callsite-premises-B.md (a working note, not in this delivery)).
   Each premise list is the core contract's post, piece by piece: aintrin_realizes OSet / OCpy (YG0d.v:318-336),
   amemchr0_realizes (:384-401), abcmp_realizes (:353-372), aset_shadow_realizes (
   lib/Reusable/SetShadowDef.v (at head lib/Reusable/SetShadowDef.v:20-31; from a working branch cb6eddd4032); also in this unit's core).  The posts are VIEW-level (aview),
   so the raw `munch WR m1 m2` / `wmono m1 m2` the stretches state today are NOT derivable (a hidden byte, or a byte
   equal to the rom byte, may change): the conclusions are their visible forms munch_vis / wmono_vis, and the
   stretch after the call is re-based to read them (a Theorem Labs lane 23:53Z allows re-based copies; G1 (fs-of-astack.md (a working note, not in this delivery))).
   strcmp: astrcmp_realizes (a working branch 04d425a4ce3 lib/Reusable/AStrcmpDef.v; also in the
   core) has abcmp_realizes' post shape (2 * ESTACK window, apresent clause), so ctl_post_strcmp needs no Require. *)
Section RtPost.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.

Definition munch_vis (H : word -> bool) (WR : list lib.Lib.Frame.ivl) (m m' : word -> option byte) : Prop :=
  forall x : word, H x = false -> lib.Lib.Frame.outside WR (bv_unsigned x) ->
    lib.Lib.Mem.mrd B.Img0.rsegs m' x = lib.Lib.Mem.mrd B.Img0.rsegs m x.
Definition wmono_vis (H : word -> bool) (m m' : word -> option byte) : Prop :=
  forall x : word, H x = false -> wview B.Img0.rsegs m x <> None -> wview B.Img0.rsegs m' x <> None.

(* the frame condition and the presence clause every runtime post states, outside a window [lo, hi) *)
Definition rt_post_frame (W : lib.Reusable.YA0n.world segs) (mem mem' : word -> option byte) (WR : list lib.Lib.Frame.ivl)
    : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> lib.Lib.Frame.outside WR a ->
     lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem' a =
     lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem a) /\
  (forall a, lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem a ->
     lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem' a).


(* The one primitive (two Theorem Labs lanes 01:22Z): at a visible address the core's view IS ctrl's mrd.  PROVED.
   Every ctl_post_* conclusion about bytes and the frame condition below follows from it. *)
Lemma aview_vis_mrd : forall (W : lib.Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem a =
  option_map (fun b : byte => bv_unsigned b) (lib.Lib.Mem.mrd B.Img0.rsegs mem (Z_to_bv 64 a)).
Proof.
  intros W mem a Hh.
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict, lib.Lib.Mem.mrd.
  rewrite Hh. reflexivity.
Qed.

(* A runtime post's frame condition and presence clause give munch_vis and wmono_vis.  PROVED. *)
Lemma rt_post_frame_vis : forall (W : lib.Reusable.YA0n.world segs) (mem mem' : word -> option byte)
    (WR : list lib.Lib.Frame.ivl),
  rt_post_frame W mem mem' WR ->
  munch_vis (lib.Reusable.YA0n.w_H W) WR mem mem' /\ wmono_vis (lib.Reusable.YA0n.w_H W) mem mem'.
Proof.
  intros W mem mem' WR [Hf Hp]. split.
  - intros x Hx Ho.
    pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
    specialize (Hf (bv_unsigned x) Rx Ho).
    rewrite (aview_vis_mrd W mem' (bv_unsigned x)), (aview_vis_mrd W mem (bv_unsigned x)) in Hf
      by (rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned; exact Hx).
    rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hf.
    destruct (lib.Lib.Mem.mrd B.Img0.rsegs mem' x) as [b'|], (lib.Lib.Mem.mrd B.Img0.rsegs mem x) as [b|];
      cbn [option_map] in Hf; try discriminate Hf; [|reflexivity].
    injection Hf as Hb. f_equal. apply bv_eq. exact Hb.
  - intros x Hx Hw. destruct (mem x) as [b|] eqn:Em.
    + assert (Hpr : lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem (bv_unsigned x)).
      { unfold lib.Reusable.YG0n.apresent. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. split; [exact Hx | exists b; exact Em]. }
      destruct (Hp _ Hpr) as [_ [b' Hb']]. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hb'.
      unfold wview. rewrite Hb'. discriminate.
    + unfold wview in *. rewrite Em in Hw. destruct (mem' x); [discriminate | exact Hw].
Qed.
(* memset (aintrin_realizes OSet): destination d, value x, length n; window = the callee's ESTACK. *)
Definition ctl_post_memset_stmt : Prop :=
  forall (W : lib.Reusable.YA0n.world segs) (mem mem' : word -> option byte) (sp d x n : Z),
    0 <= d -> d + n <= 2 ^ 63 -> 0 <= n < 2 ^ 32 ->
    (forall a, d <= a < d + n -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem a) ->
    (forall i, 0 <= i < n -> lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem' (d + i) = Some (x mod 256)) ->
    rt_post_frame W mem mem' ((d, d + n) :: (sp - lib.Reusable.YG0d.ESTACK, sp) :: nil) ->
    munch_vis (lib.Reusable.YA0n.w_H W) ((d, d + n) :: (sp - lib.Reusable.YG0d.ESTACK, sp) :: nil) mem mem' /\
    wmono_vis (lib.Reusable.YA0n.w_H W) mem mem' /\
    lib.Lib.Step.rw_cells B.Img0.rsegs mem' d
      (lib.Lib.Cells.CB (Z.to_nat n) (repeat (Z_to_bv 8 (x mod 256)) (Z.to_nat n)) :: nil).

(* memcpy (aintrin_realizes OCpy): source x with its bytes src (visible: src_ok), destination d. *)
Definition ctl_post_memcpy_stmt : Prop :=
  forall (W : lib.Reusable.YA0n.world segs) (mem mem' : word -> option byte) (sp d x n : Z) (src : list byte),
    0 <= d -> d + n <= 2 ^ 63 -> 0 <= n < 2 ^ 32 -> Z.of_nat (length src) = n ->
    (forall a, d <= a < d + n -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem a) ->
    lib.Lib.Mem.bytes_at B.Img0.rsegs mem x src ->
    (forall i, 0 <= i < n -> lib.Reusable.YA0n.w_H W (Z_to_bv 64 (x + i)) = false) ->
    (forall i, 0 <= i < n -> lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem' (d + i) =
                             lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem (x + i)) ->
    rt_post_frame W mem mem' ((d, d + n) :: (sp - lib.Reusable.YG0d.ESTACK, sp) :: nil) ->
    munch_vis (lib.Reusable.YA0n.w_H W) ((d, d + n) :: (sp - lib.Reusable.YG0d.ESTACK, sp) :: nil) mem mem' /\
    wmono_vis (lib.Reusable.YA0n.w_H W) mem mem' /\
    lib.Lib.Step.rw_cells B.Img0.rsegs mem' d (lib.Lib.Cells.CB (Z.to_nat n) src :: nil).

(* a call that writes nothing outside its own window [sp - K, sp): memchr (amemchr0_realizes, K = ESTACK) and bcmp
   (abcmp_realizes, K = 2 * ESTACK); its a0 fact passes through from the post unchanged. *)
Definition ctl_post_window_stmt (K : Z) : Prop :=
  forall (W : lib.Reusable.YA0n.world segs) (mem mem' : word -> option byte) (sp : Z),
    rt_post_frame W mem mem' ((sp - K, sp) :: nil) ->
    munch_vis (lib.Reusable.YA0n.w_H W) ((sp - K, sp) :: nil) mem mem' /\ wmono_vis (lib.Reusable.YA0n.w_H W) mem mem'.
Definition ctl_post_memchr_stmt : Prop := ctl_post_window_stmt lib.Reusable.YG0d.ESTACK.
Definition ctl_post_bcmp_stmt : Prop := ctl_post_window_stmt (2 * lib.Reusable.YG0d.ESTACK).
Definition ctl_post_strcmp_stmt : Prop := ctl_post_window_stmt (2 * lib.Reusable.YG0d.ESTACK).

(* The window corollaries.  PROVED. *)
Lemma ctl_post_window : forall K, ctl_post_window_stmt K.
Proof. intros K W mem mem' sp H. exact (rt_post_frame_vis W mem mem' _ H). Qed.
Lemma ctl_post_memchr : ctl_post_memchr_stmt. Proof. apply ctl_post_window. Qed.
Lemma ctl_post_bcmp : ctl_post_bcmp_stmt. Proof. apply ctl_post_window. Qed.
Lemma ctl_post_strcmp : ctl_post_strcmp_stmt. Proof. apply ctl_post_window. Qed.

(* ctl_post_malloc / ctl_post_free (a Theorem Labs lane 01:22Z): amalloc04_rule / afree04_rule (YC5d.v:57-97) end in
   YCbq.acall_kept (YCbq.v:824-835), which keeps the view only on four classes of addresses (high memory outside the
   window, live blocks off E, non-owned non-errno image bytes, live frames off E); owned (allocator) bytes change.
   So the conclusion is mrd equality at a visible address of a kept class, not munch_vis over all addresses.  E is
   the new block [res, res + req_size n) (malloc) or the freed block (free); [slo, shi) = [sp0 + o - ASTACK, sp0 + o).
   PROVED (one lemma serves both rules). *)
Definition kept_class (B : lib.Reusable.YG0f.asyms) (lyc : lib.Reusable.YG0f.alayout) (Sc : lib.Reusable.YG00.astate)
    (slo shi : Z) (E : Z -> Prop) (a : Z) : Prop :=
  (lib.Reusable.YM05.alloc_ceiling <= a < 2 ^ 64 /\ ~ (slo <= a < shi)) \/
  (exists b m i, In (b, m) (lib.Reusable.YG0d.ablocks B lyc Sc) /\ 0 <= i < lib.Reusable.YG00.req_size m /\
     a = b + i /\ ~ E (b + i)) \/
  (lib.Reusable.YG0d.in_img segs a /\ ~ Exists (lib.Reusable.YG0n.in_zr a) (lib.Reusable.YG0f.as_owned_static B) /\
     ~ (lib.Reusable.YG0f.as_errno B <= a < lib.Reusable.YG0f.as_errno B + 4)) \/
  (exists cid pos, In (cid, pos) (lib.Reusable.YG01.frames Sc) /\
     (lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng lyc (cid, pos)) \/
      lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr lyc cid pos),
                                 lib.Reusable.YG00.fs_frame_bytes cid / 8)) /\ ~ E a).

Lemma ctl_post_acall_kept : forall (B : lib.Reusable.YG0f.asyms) lyc Sc (W W2 : lib.Reusable.YA0n.world segs)
    (memc mem2 : word -> option byte) (slo shi : Z) (E : Z -> Prop),
  lib.Reusable.YCbq.acall_kept segs B lyc Sc W memc W2 mem2 slo shi E ->
  lib.Reusable.YA0n.wle W W2 ->
  forall x : word, lib.Reusable.YA0n.w_H W x = false -> kept_class B lyc Sc slo shi E (bv_unsigned x) ->
    lib.Lib.Mem.mrd B.Img0.rsegs mem2 x = lib.Lib.Mem.mrd B.Img0.rsegs memc x.
Proof.
  intros B lyc Sc W W2 memc mem2 slo shi E (K1 & K2 & K3 & K4 & _ & _) Hle x Hx Hk.
  assert (Hx2 : lib.Reusable.YA0n.w_H W2 x = false).
  { destruct (lib.Reusable.YA0n.w_H W2 x) eqn:E2; [|reflexivity]. rewrite (Hle _ E2) in Hx. discriminate Hx. }
  assert (Hv : lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W2) mem2 (bv_unsigned x) =
               lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) memc (bv_unsigned x)).
  { destruct Hk as [[H1 H2] | [(b & m & i & Hin & Hi & Ha & HE) | [(H1 & H2 & H3) | (cid & pos & Hin & Hr & HE)]]].
    - exact (K1 _ H1 H2).
    - rewrite Ha. exact (K2 b m i Hin Hi HE).
    - exact (K3 _ H1 H2 H3).
    - exact (K4 cid pos _ Hin Hr HE). }
  rewrite (aview_vis_mrd W2 mem2 (bv_unsigned x)), (aview_vis_mrd W memc (bv_unsigned x)) in Hv
    by (rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned; assumption).
  rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hv.
  destruct (lib.Lib.Mem.mrd B.Img0.rsegs mem2 x) as [b'|], (lib.Lib.Mem.mrd B.Img0.rsegs memc x) as [b|];
    cbn [option_map] in Hv; try discriminate Hv; [|reflexivity].
  injection Hv as Hb. f_equal. apply bv_eq. exact Hb.
Qed.

(* __asan_set_shadow_<v> (aset_shadow_realizes): the range [q, q + n) inside a live frame's shadow.  The presence
   clause is NOT in SetShadowDef.v's post (only the window's apresent): it is a premise here, to be added to that
   post by its owner. *)
Definition ctl_post_set_shadow_stmt : Prop :=
  forall (W : lib.Reusable.YA0n.world segs) (mem mem' : word -> option byte) (q n v : Z),
    0 <= q -> q + n <= 2 ^ 64 -> 0 < n ->
    (forall a, q <= a < q + n -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem a) ->
    (forall i, 0 <= i < n -> lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem' (q + i) = Some v) ->
    rt_post_frame W mem mem' ((q, q + n) :: nil) ->
    munch_vis (lib.Reusable.YA0n.w_H W) ((q, q + n) :: nil) mem mem' /\
    wmono_vis (lib.Reusable.YA0n.w_H W) mem mem' /\
    lib.Lib.Step.rw_cells B.Img0.rsegs mem' q (lib.Lib.Cells.CB (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n)) :: nil).

(* Proofs of the three statements above (group post, a Theorem Labs lane, commit 2fef5c2d5c2; type-check only). *)
Lemma rw_cells_CB_of_present : forall (m : word -> option byte) (d : Z) (k : nat) (bs : list byte),
  length bs = k -> 0 <= d -> d + Z.of_nat k <= 2 ^ 64 ->
  (forall i : nat, (i < k)%nat -> lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (d + Z.of_nat i)) = nth_error bs i) ->
  (forall i, 0 <= i < Z.of_nat k -> m (Z_to_bv 64 (d + i)) <> None) ->
  lib.Lib.Step.rw_cells B.Img0.rsegs m d (lib.Lib.Cells.CB k bs :: nil).
Proof.
  intros m d k bs Hl Hd Hk Hr Hp.
  unfold lib.Lib.Step.rw_cells, lib.Lib.Cells.cells_at, lib.Lib.Mem.bytes_at, lib.Lib.Mem.wr_at, lib.Lib.Mem.wa.
  cbn [lib.Lib.Cells.cells_wf lib.Lib.Cells.cell_wf lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes lib.Lib.Cells.cells_size
       lib.Lib.Cells.csize].
  rewrite app_nil_r, Nat.add_0_r.
  split; [split; [split; [exact Hl | exact I] | rewrite Hl; split; [exact Hd | split; [exact Hk | exact Hr]]] |].
  split; [exact Hd | split; [exact Hk |]].
  intros i Hi. unfold wview. destruct (m (Z_to_bv 64 (d + i))) as [b|] eqn:E; [discriminate |].
  exfalso. exact (Hp i Hi E).
Qed.

Lemma mrd_of_aview_some : forall (W : lib.Reusable.YA0n.world segs) (mem : word -> option byte) (a v : Z),
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem a = Some v ->
  lib.Lib.Mem.mrd B.Img0.rsegs mem (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof.
  intros W mem a v Hh E.
  rewrite (aview_vis_mrd W mem a Hh) in E.
  destruct (lib.Lib.Mem.mrd B.Img0.rsegs mem (Z_to_bv 64 a)) as [b|]; cbn [option_map] in E; [|discriminate E].
  injection E as Eb. rewrite <- Eb, stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma ctl_post_memset : ctl_post_memset_stmt.
Proof.
  intros W mem mem' sp d x n Hd Hdn Hn Hpres Hv Hf.
  destruct (rt_post_frame_vis W mem mem' _ Hf) as [Hm Hw].
  split; [exact Hm | split; [exact Hw |]].
  destruct Hf as [_ Hp].
  apply rw_cells_CB_of_present.
  - apply repeat_length.
  - exact Hd.
  - lia.
  - intros i Hi. rewrite nth_error_repeat by exact Hi.
    destruct (Hp _ (Hpres (d + Z.of_nat i) ltac:(lia))) as [Hh _].
    exact (mrd_of_aview_some W mem' _ _ Hh (Hv (Z.of_nat i) ltac:(lia))).
  - intros i Hi. destruct (Hp _ (Hpres (d + i) ltac:(lia))) as [_ [b Eb]].
    rewrite Eb. discriminate.
Qed.

Lemma ctl_post_memcpy : ctl_post_memcpy_stmt.
Proof.
  intros W mem mem' sp d x n src Hd Hdn Hn Hlen Hpres Hsrc HxH Hv Hf.
  destruct (rt_post_frame_vis W mem mem' _ Hf) as [Hm Hw].
  split; [exact Hm | split; [exact Hw |]].
  destruct Hf as [_ Hp].
  destruct Hsrc as (_ & _ & Hs).
  apply rw_cells_CB_of_present.
  - lia.
  - exact Hd.
  - lia.
  - intros i Hi.
    assert (Hi' : (i < length src)%nat) by lia.
    destruct (Hp _ (Hpres (d + Z.of_nat i) ltac:(lia))) as [Hh _].
    pose proof (Hv (Z.of_nat i) ltac:(lia)) as E.
    rewrite (aview_vis_mrd W mem' _ Hh), (aview_vis_mrd W mem _ (HxH (Z.of_nat i) ltac:(lia))) in E.
    specialize (Hs i Hi'). unfold lib.Lib.Mem.wa in Hs. rewrite Hs in E.
    destruct (lib.Lib.Mem.mrd B.Img0.rsegs mem' (Z_to_bv 64 (d + Z.of_nat i))) as [b'|], (nth_error src i) as [b|];
      cbn [option_map] in E; try discriminate E; [|reflexivity].
    injection E as Eb. f_equal. apply bv_eq. exact Eb.
  - intros i Hi. destruct (Hp _ (Hpres (d + i) ltac:(lia))) as [_ [b Eb]].
    rewrite Eb. discriminate.
Qed.

Lemma ctl_post_set_shadow : ctl_post_set_shadow_stmt.
Proof.
  intros W mem mem' q n v Hq Hqn Hn Hpres Hv Hf.
  destruct (rt_post_frame_vis W mem mem' _ Hf) as [Hm Hw].
  split; [exact Hm | split; [exact Hw |]].
  destruct Hf as [_ Hp].
  apply rw_cells_CB_of_present.
  - apply repeat_length.
  - exact Hq.
  - lia.
  - intros i Hi. rewrite nth_error_repeat by exact Hi.
    destruct (Hp _ (Hpres (q + Z.of_nat i) ltac:(lia))) as [Hh _].
    exact (mrd_of_aview_some W mem' _ _ Hh (Hv (Z.of_nat i) ltac:(lia))).
  - intros i Hi. destruct (Hp _ (Hpres (q + i) ltac:(lia))) as [_ [b Eb]].
    rewrite Eb. discriminate.
Qed.
End RtPost.

(* ---------------------------------------------------------------------------------------------------------
   ADDITIONS after the interface freeze at c03ce1627b6 (announced by two Theorem Labs lanes 02:36Z; earlier lines unchanged). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK1b YI04.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.MemNormF.

(* 9. Re-based stretches (a Theorem Labs lane 02:41Z-02:45Z): one normalization per stretch, at its base memory m.  The stretch
   runs on normalize m (where MemNorm.mem_inv_normalize gives mem_inv, so _F / plain contracts keep mem_inv in their
   premises and posts, and Q may state mem_inv of the normalized final memory); this wrapper carries the result back
   to the real memory: ms_rel (registers, pc, ...), bytes / wr / munch / wmono facts, and ro_agree of the real final
   memory (never mem_inv).  Glue-level only.  Proof: MemNormF.evtF_normalize_ro (from a working branch 5dbd293c250) (
   MemNormF.v (at head lib/B/MemNormF.v:148-152)) + MemNorm.bytes_at_rel :369, wr_at_rel :380, munch_rel :394, wmono_rel :402,
   ro_agree_of_mem_rel :73, mem_rel_normalize :67. *)
Definition rebase_ro_normalize_stmt : Prop :=
  forall (RNG : Lib.ExecF.footprint) (Q : machine_state -> Prop) R F pc fc rv (m : word -> option byte) ro,
    B.MemNorm.ro_agree B.Img0.rsegs m ->
    Lib.ExecF.evtF B.Img0.rsegs RNG Q (lib.Lib.MState.MS R F pc fc rv (B.MemNorm.normalize B.Img0.rsegs m) ro) ->
    Lib.ExecF.evtF B.Img0.rsegs RNG
      (fun s => exists s0, Q s0 /\ B.MemNorm.ms_rel B.Img0.rsegs s s0 /\
         B.MemNorm.ro_agree B.Img0.rsegs (ms_mem s) /\
         B.MemNorm.ro_same B.Img0.rsegs m (ms_mem s) /\
         (forall a, lib.Lib.Mem.mrd B.Img0.rsegs (ms_mem s) a = lib.Lib.Mem.mrd B.Img0.rsegs (ms_mem s0) a) /\
         (forall a bs, lib.Lib.Mem.bytes_at B.Img0.rsegs (ms_mem s) a bs <->
                       lib.Lib.Mem.bytes_at B.Img0.rsegs (ms_mem s0) a bs) /\
         (forall a n, lib.Lib.Mem.wr_at B.Img0.rsegs (ms_mem s0) a n -> lib.Lib.Mem.wr_at B.Img0.rsegs (ms_mem s) a n) /\
         (forall WR, lib.Lib.Frame.munch WR (B.MemNorm.normalize B.Img0.rsegs m) (ms_mem s0) ->
                     lib.Lib.Frame.munch WR m (ms_mem s)) /\
         (lib.Lib.Frame.wmono B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs m) (ms_mem s0) ->
          lib.Lib.Frame.wmono B.Img0.rsegs m (ms_mem s)) /\
         (* rd_mono (lib/A/Prog/MemMono.v:13-14 and the lanes' copies), written out to keep MemMono out of the closure *)
         ((forall x : word, (exists b, lib.Lib.Mem.mrd B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs m) x = Some b) ->
                            exists b, lib.Lib.Mem.mrd B.Img0.rsegs (ms_mem s0) x = Some b) ->
          forall x : word, (exists b, lib.Lib.Mem.mrd B.Img0.rsegs m x = Some b) ->
                           exists b, lib.Lib.Mem.mrd B.Img0.rsegs (ms_mem s) x = Some b))
      (lib.Lib.MState.MS R F pc fc rv m ro).

Lemma rebase_ro_normalize : rebase_ro_normalize_stmt.
Proof.
  intros RNG Q R F pc fc rv m ro Hro H.
  pose proof (B.MemNorm.mem_rel_normalize B.Img0.rsegs m Hro) as REL0.
  destruct (B.MemNormF.evtF_normalize_ro RNG Q R F pc fc rv m ro Hro H) as (s & Hs & s0 & HQ & Hrel & Hsame).
  exists s. split; [exact Hs|]. exists s0. split; [exact HQ|]. split; [exact Hrel|].
  pose proof Hrel as (_ & _ & _ & _ & _ & _ & _ & REL).
  split; [exact (B.MemNorm.ro_agree_of_mem_rel B.Img0.rsegs _ _ REL)|].
  split; [exact Hsame|].
  split; [intros a; exact (B.MemNorm.mrd_rel B.Img0.rsegs _ _ a REL)|].
  split; [intros a bs; exact (B.MemNorm.bytes_at_rel B.Img0.rsegs _ _ a bs REL)|].
  split; [intros a n Hw; exact (B.MemNorm.wr_at_rel B.Img0.rsegs _ _ a n REL Hw)|].
  split; [intros WR Hm; exact (B.MemNorm.munch_rel B.Img0.rsegs WR _ _ _ _ REL0 REL Hsame Hm)|].
  split; [intros Hw; exact (B.MemNorm.wmono_rel B.Img0.rsegs _ _ _ _ REL0 REL Hsame Hw)|].
  intros Hrd x (b & Hb). rewrite (B.MemNorm.mrd_rel B.Img0.rsegs _ _ x REL0) in Hb.
  destruct (Hrd x (ex_intro _ b Hb)) as (b' & Hb'). exists b'.
  rewrite (B.MemNorm.mrd_rel B.Img0.rsegs _ _ x REL). exact Hb'.
Qed.

(* 10. Shadow BYTE VALUES (a Theorem Labs lane 02:50Z: the announced block-shadow addition, two lemmas).  a Theorem Labs lane's heap_sh_vis /
   glob_sh_vis give visibility only.  ctl_block_shadow_of_AR: every byte of a sub-range of a live malloc block is
   addressable in ctrl's sense (checked loads, bcmp's `addressable m L N`), from AR's am_shadow (shadow_ok over ashadow:
   chunk granules, YG0n.v:181-187, :217) + AR_shadow_law's visibility (YG0d.v:430-434), through aview_vis_mrd.
   ctl_zshadow_of_AR: every byte of a sub-range of a zero-shadow global range of the bundle (as_zero_shadow, YG0n.v:188,
   e.g. the catalogue table) is addressable, from am_zshadow / AR_zshadow_law (YG0d.v:435-438). *)
Section BlkShadow.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

Definition ctl_block_shadow_of_AR_stmt : Prop :=
  lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md p n lo len,
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    In (p, n) (lib.Reusable.YG0d.ablocks B ly S) ->
    p <= lo -> 0 <= len -> lo + len <= p + lib.Reusable.YG00.req_size n ->
    B.AsanRT.addressable m lo len.

Definition ctl_zshadow_of_AR_stmt : Prop :=
  lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md r lo len,
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    In r (lib.Reusable.YG0f.as_zero_shadow B) ->
    fst r <= lo -> 0 <= len -> lo + len <= fst r + 8 * (snd r / 8) ->
    B.AsanRT.addressable m lo len.

(* The stack twin (announced 03:3xZ, a Theorem Labs lane): the first entry of zero_shadow_ranges (YG0n.v:188-189) is the whole
   stack (ly_stk_lo, ly_stk_hi - ly_stk_lo), so am_zshadow / AR_zshadow_law (YG0d.v:435-438) give its shadow values. *)
Definition ctl_stack_shadow_of_AR_stmt : Prop :=
  lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md lo len,
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    lib.Reusable.YG0f.ly_stk_lo ly <= lo -> 0 <= len -> lo + len <= lib.Reusable.YG0f.ly_stk_hi ly ->
    B.AsanRT.addressable m lo len.
End BlkShadow.
(* 11. The thread pointer of the bundle is ctrl's TP (announced addition, a Theorem Labs lane 03:2xZ): turns afn_pre's
   `getr regs 4 = w64 (as_tp B)` into fp's TP = AsanRT.RT_TP.  CtrlTSyms' ts_tp (YF0m.v:2987) gives TFIB_TP =
   0x5dc650 (YF0m.v:12; = B.AsanRT.RT_TP = builtin_tls 0x5dc588 + 0xc8, the B symtab). *)
Lemma as_tp_RT_TP : forall B : lib.Reusable.YG0f.asyms,
  lib.Reusable.YF0m.CtrlTSyms B -> lib.Reusable.YG0f.as_tp B = B.AsanRT.RT_TP.
Proof. intros B HTS. rewrite (lib.Reusable.YF0m.ts_tp _ HTS). reflexivity. Qed.
(* 12. RT_used from AR at any state (announced 03:0xZ): callee-internal re-based stretches (a Theorem Labs lane's aCL row, the
   bcmp wrapper's cells, a Theorem Labs lane's glue) take RT_used at their own base memory.  rt_of_core is this plus the cut's
   ajournal (AR = its first conjunct) and ctl_rt.  Proof: the am_const rows under CtrlTSyms (as rt_of_core). *)
Section RtUsed.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.
Definition RT_used_of_AR_stmt : Prop :=
  lib.Reusable.YF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B -> AR_states_vis0_shadow B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md,
    lib.Reusable.YG0n.AR segs B ly S W m md -> RT_used m.
End RtUsed.
(* 13. Shared helpers of the ctl_post_<callee> conversions (K0-K3; decision a Theorem Labs lane 03:3xZ: shared interface, several
   lanes need them; texts = a Theorem Labs lane's lib/B/Prog/C_reac_ctrl_identity_replyPost.v (not in this delivery) (1df58ed9045), image B's own
   names; that file came from ctl-post-callees.md section 0.3 (a working note, not in this delivery)).  The A twin lib/A/ProgWorld.v states the same.
   K0 is the class set acall_kept / tcj_kept / ajournal keep (kept_class of Section RtPost is the earlier malloc / free
   form, without the global ~ E).  The hint word and flag bytes of the side stack are NOT kept classes: they come from AR
   at the stretch base (ctl_fs_of_AR / ctl_fp_of_AR).
   ANNOUNCED STATEMENT CHANGE (two Theorem Labs lanes 08:21Z): the high-memory class of ctl_kept_cls used the constant
   lib.Reusable.YK06.alloc_ceiling (= CEIL_MIN 0x7fff7f800000), while acall_kept's clause 1 (YCbq.v:826, which Imports
   YM05) and kept_class (:671) use the run's ceiling lib.Reusable.YM05.alloc_ceiling (a RunCeil field, CEIL_MIN <= it,
   YM05.v:18-19).  On [CEIL_MIN, run ceiling) the old text claimed a byte kept that acall_kept does not keep, so it was
   not derivable from acall_kept there.  The class now reads YM05.alloc_ceiling, the Section's own `rc`. *)
Section CtlPostCallees.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

Definition ctl_kept_cls (bl frs : list (Z * Z)) (fra : Z -> Z -> Z) (slo shi : Z) (E : Z -> Prop) (a : Z) : Prop :=
  ~ E a /\
  ( (lib.Reusable.YM05.alloc_ceiling <= a < 2 ^ 64 /\ ~ (slo <= a < shi))
  \/ (exists p n i, In (p, n) bl /\ 0 <= i < lib.Reusable.YG00.req_size n /\ a = p + i)
  \/ (lib.Reusable.YG0d.in_img segs a /\
      ~ Exists (lib.Reusable.YG0n.in_zr a) (lib.Reusable.YG0f.as_owned_static B) /\
      ~ (lib.Reusable.YG0f.as_errno B <= a < lib.Reusable.YG0f.as_errno B + 4))
  \/ (exists cid pos, In (cid, pos) frs /\
        (lib.Reusable.YG0n.in_zr a (fra cid pos, lib.Reusable.YG00.fs_frame_bytes cid) \/
         lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.shadow_addr (fra cid pos),
                                    lib.Reusable.YG00.fs_frame_bytes cid / 8)))).

Definition ctl_kept_vis (H : word -> bool) (m m' : word -> option byte) (C : Z -> Prop) : Prop :=
  forall x : word, H x = false -> C (bv_unsigned x) ->
    lib.Lib.Mem.mrd B.Img0.rsegs m' x = lib.Lib.Mem.mrd B.Img0.rsegs m x.

Definition ctl_wmono_vis_off_img (H : word -> bool) (m m' : word -> option byte) (C : Z -> Prop) : Prop :=
  forall x : word, H x = false -> C (bv_unsigned x) -> ~ lib.Reusable.YG0d.in_img segs (bv_unsigned x) ->
    wview B.Img0.rsegs m x <> None -> wview B.Img0.rsegs m' x <> None.

Definition ctl_out_bytes_stmt : Prop :=
  forall (W2 : lib.Reusable.YA0n.world segs) (mem2 : word -> option byte) (o : Z) (bs : list byte),
    0 <= o -> o + Z.of_nat (length bs) <= 2 ^ 64 ->
    (forall i, (i < length bs)%nat -> ~ lib.Reusable.YG0d.in_img segs (o + Z.of_nat i)) ->
    lib.Reusable.YI00.garr8 segs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W2) mem2) o
      (map (fun b : byte => bv_unsigned b) bs) ->
    lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 o bs /\
    lib.Lib.Step.rw_cells B.Img0.rsegs mem2 o (lib.Lib.Cells.CB (length bs) bs :: nil).

(* K3 PROVED: off the image, garr8 over the restricted memory pins each byte as present, visible and equal. *)
Lemma ctl_out_bytes : ctl_out_bytes_stmt.
Proof.
  intros W2 mem2 o bs Ho Hb Hni Hg.
  assert (E : forall j, (j < length bs)%nat -> exists b, nth_error bs j = Some b /\
                mem2 (Z_to_bv 64 (o + Z.of_nat j)) = Some b).
  { intros j Hj. destruct (nth_error bs j) as [b|] eqn:En; [|apply nth_error_None in En; lia].
    exists b. split; [reflexivity|].
    assert (Hj' : (j < length (map (fun b : byte => bv_unsigned b) bs))%nat) by (rewrite length_map; exact Hj).
    pose proof (lib.Reusable.YI00.garr8_mbyte segs _ _ _ j Hg Hj') as Hv.
    assert (Hnth : nth j (map (fun b : byte => bv_unsigned b) bs) 0 = bv_unsigned b)
      by (apply nth_error_nth; rewrite nth_error_map, En; reflexivity).
    rewrite Hnth, stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hv.
    pose proof (lib.Reusable.YCbq.seg_rom_none segs (o + Z.of_nat j) ltac:(lia) (Hni j Hj)) as Hnone.
    unfold lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in Hv.
    destruct (lib.Reusable.YA0n.w_H W2 (Z_to_bv 64 (o + Z.of_nat j))).
    - rewrite Hnone in Hv. discriminate Hv.
    - destruct (mem2 (Z_to_bv 64 (o + Z.of_nat j))) as [b0|] eqn:Em.
      + injection Hv as Hv. rewrite Hv. reflexivity.
      + rewrite Hnone in Hv. discriminate Hv. }
  assert (HB : lib.Lib.Mem.bytes_at B.Img0.rsegs mem2 o bs).
  { split; [exact Ho|]. split; [exact Hb|]. intros i Hi. destruct (E i Hi) as (b & Hn & Hm).
    rewrite Hn. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hm. reflexivity. }
  split; [exact HB|].
  apply rw_cells_CB_of_present; [reflexivity | exact Ho | exact Hb | |].
  - intros i Hi. destruct (E i Hi) as (b & Hn & Hm). rewrite Hn. unfold lib.Lib.Mem.mrd. rewrite Hm. reflexivity.
  - intros i Hi. destruct (E (Z.to_nat i) ltac:(lia)) as (b & _ & Hm).
    rewrite Z2Nat.id in Hm by lia. rewrite Hm. discriminate.
Qed.
End CtlPostCallees.

(* Proofs of Section Fsteps (group steps, a Theorem Labs lane, commit bf110153c56; type-check only).
   Machine side without functional_extensionality (YK04R.fsteps_restrict depends on it). *)
(* ---- machine side: a footprint run whose footprint avoids H grows memory and keeps every H byte ---- *)
Section StepKeeps.
Local Open Scope bv_scope.
Variable sg : list Segment.
Variable H : word -> bool.

Lemma pws_interp_keeps : forall t m c mf' rs,
  interp_eff_accesses sg t m = MachineOk (@mkAccessReport _ (c, mf') rs) ->
  lib.Reusable.YK04.ranges_avoid H rs -> forall x, H x = true -> mf' x = m x.
Proof.
  induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH];
    intros m c mf' rs Hi Hrs x Hx; cbn [interp_eff_accesses] in Hi; try discriminate.
  - injection Hi as <- <- <-. reflexivity.
  - destruct (ov_read_bytes sg m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses sg (k (bv_extract 0 n (le_bytes_to_word bs))) m)
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    exact (IH _ m c1 m1 rs1 Hk (lib.Reusable.YK04R.ranges_avoid_tl H _ rs1 Hrs) x Hx).
  - destruct (store_ok sg m a (width_bytes n)); [|discriminate].
    destruct (interp_eff_accesses sg k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v))))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    rewrite (IH _ c1 m1 rs1 Hk (lib.Reusable.YK04R.ranges_avoid_tl H _ rs1 Hrs) x Hx).
    apply (lib.Reusable.YK04.write_to_mem_hidden H); [|exact Hx].
    rewrite LinuxProcessSemantics.LinuxProcessSem.BvBase.length_Z_to_le_bytes.
    exact (lib.Reusable.YK04R.ranges_avoid_hd H a (width_bytes n) rs1 Hrs).
Qed.

Lemma pws_decode_keeps : forall ms w ms' rs,
  decode_exec_accesses sg ms w = MachineOk (@mkAccessReport _ ms' rs) ->
  lib.Reusable.YK04.ranges_avoid H rs -> forall x, H x = true -> ms_mem ms' x = ms_mem ms x.
Proof.
  intros ms w ms' rs Hd Hrs x Hx. unfold decode_exec_accesses in Hd.
  destruct (is_ecall w) eqn:Hec.
  - injection Hd as <- <-. reflexivity.
  - destruct (LinuxProcessSemantics.Riscv.DecodeC.decode_any w) as [[i isz]|];
      [|destruct (LinuxProcessSemantics.Riscv.DecodeC.is_defined_illegal w); discriminate].
    lazymatch type of Hd with context [interp_eff_accesses sg ?t ?m] =>
      destruct (interp_eff_accesses sg t m) as [[[c1 m1] rs1]| |] eqn:Hint; try discriminate end.
    cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-.
    exact (pws_interp_keeps _ _ _ _ _ Hint Hrs x Hx).
Qed.

Lemma pws_step_keeps : forall ms ms' rs,
  step_accesses sg ms = MachineOk (@mkAccessReport _ ms' rs) ->
  lib.Reusable.YK04.ranges_avoid H rs -> forall x, H x = true -> ms_mem ms' x = ms_mem ms x.
Proof.
  intros ms ms' rs Hs Hrs. unfold step_accesses in Hs.
  destruct (fetch_word sg (ms_pc ms)) as [w|].
  { exact (pws_decode_keeps ms w ms' rs Hs Hrs). }
  destruct (fetch_word_ov sg (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (pws_decode_keeps ms w ms' rs Hs Hrs). }
  destruct (fetch_tail_any sg (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (pws_decode_keeps ms w ms' rs Hs Hrs). }
  exfalso. unfold fetch_failure in Hs.
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps sg (ms_pc ms) || fetch_byte_traps sg (ms_pc ms + 1)
    || match fetch_half_any sg (ms_mem ms) (ms_pc ms) with
       | Some _ => fetch_byte_traps sg (ms_pc ms + 2) || fetch_byte_traps sg (ms_pc ms + 3)
       | None => false end); discriminate.
Qed.

Lemma pws_fsteps_mem : forall RNG ms ms',
  lib.Reusable.YK04R.fsteps sg RNG ms ms' -> lib.Reusable.YK04R.fp_avoids H RNG ->
  lib.Reusable.YK1b.mem_grows (ms_mem ms) (ms_mem ms') /\ (forall x, H x = true -> ms_mem ms' x = ms_mem ms x).
Proof.
  intros RNG ms ms' Hrun Hfp. induction Hrun as [ms | ms ms1 ms2 [Hsvc (accs & Hs & HF)] _ IH].
  - split; [apply lib.Reusable.YK1b.mem_grows_refl | intros x _; reflexivity].
  - assert (Hrs : lib.Reusable.YK04.ranges_avoid H accs).
    { intros a n Hin. apply Hfp. exact (proj1 (Forall_forall _ accs) HF (a, n) Hin). }
    destruct IH as [G K]. split.
    + eapply lib.Reusable.YK1b.mem_grows_trans; [|exact G].
      apply (lib.Reusable.YI04.step_mem_grows sg). unfold RiscvSemantics.step, drop_access_report.
      rewrite Hs. reflexivity.
    + intros x Hx. rewrite (K x Hx). exact (pws_step_keeps ms ms1 accs Hs Hrs x Hx).
Qed.
End StepKeeps.

Lemma pws_grows_mrestrict : forall (H : word -> bool) m m',
  lib.Reusable.YK1b.mem_grows m m' ->
  lib.Reusable.YK1b.mem_grows (lib.Reusable.YK04.mrestrict H m) (lib.Reusable.YK04.mrestrict H m').
Proof. intros H m m' G x Hx. unfold lib.Reusable.YK04.mrestrict in *. destruct (H x); [exact Hx | exact (G x Hx)]. Qed.

Lemma pws_u64 : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros a Ha. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

Lemma pws_outside_dec : forall (WR : list lib.Lib.Frame.ivl) x, lib.Lib.Frame.outside WR x \/ ~ lib.Lib.Frame.outside WR x.
Proof.
  induction WR as [|[lo hi] WR IH]; cbn [lib.Lib.Frame.outside]; intros x; [left; exact I|].
  assert (D : (lo <= x < hi) \/ ~ (lo <= x < hi)) by lia.
  destruct D as [D|D]; [right; tauto|]. destruct (IH x) as [H|H]; [left; tauto | right; tauto].
Qed.

(* the image segments lie below kLowMemEnd: the segs_low premise of YCbq's Section a0 (donor A/ACeg.v:63) *)
Lemma pws_segs_low : forall a, lib.Reusable.YG0d.in_img segs a -> 0 <= a < lib.Reusable.YG0f.kLowMemEnd.
Proof.
  intros a (sg & Hin & Hr). unfold lib.Reusable.YG0f.kLowMemEnd.
  assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
    (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs)).
  { exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs sg Hin). }
  remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
  vm_compute in H.
  destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.

(* ---- the two statements ---- *)
Section FstepsProofs.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.

Lemma AR_of_fsteps : AR_of_fsteps_stmt B.
Proof.
  intros ARL _ ly S W ms ms' md md' RNG WR HAR Hrun Hfp Hm Hs Hown.
  destruct (pws_fsteps_mem segs (lib.Reusable.YA0n.w_H W) RNG ms ms' Hrun Hfp) as [Hgr Hhid].
  apply (lib.Reusable.YG0d.al_frame _ _ ARL ly S W (ms_mem ms) md (ms_mem ms') md' HAR).
  - intros a Ha Ho. apply lib.Reusable.YCbq.aview_eq_of. unfold lib.Reusable.YK04.mrestrict.
    rewrite (Hm (Z_to_bv 64 a)); [reflexivity|]. rewrite (pws_u64 a Ha). exact (Hown a Ha Ho).
  - intros a Hv. exact (lib.Reusable.YCbq.aview_keeps_vis segs _ _ _ a (pws_grows_mrestrict _ _ _ Hgr) Hv).
  - rewrite Hs. reflexivity.
  - rewrite Hs. reflexivity.
  - rewrite Hs. unfold lib.Reusable.YK04.eager_used. reflexivity.
  - intros a _ Hh. exact (Hhid _ Hh).
Qed.

Lemma ajournal_of_fsteps : ajournal_of_fsteps_stmt (SK := SK) B.
Proof.
  intros ARL _ STK sp0 FPj ly S W mem md own lyc Sc Wc ms ms' mdc mdc' k RNG WR HJ Hrun Hfp Hm Hs Hwr.
  destruct (pws_fsteps_mem segs (lib.Reusable.YA0n.w_H Wc) RNG ms ms' Hrun Hfp) as [Hgr Hhid].
  apply (lib.Reusable.YCbq.ajournal_exec (SK := SK) segs B ARL pws_segs_low STK sp0 FPj ly S W mem md own lyc Sc Wc
    (ms_mem ms) mdc k (ms_mem ms') mdc' (fun a => 0 <= a < 2 ^ 64 /\ ~ lib.Lib.Frame.outside WR a) HJ).
  - intros x Hx. unfold lib.Reusable.YK04.mrestrict. rewrite (Hm x); [reflexivity|].
    destruct (pws_outside_dec WR (bv_unsigned x)) as [Ho|Ho]; [exact Ho|].
    exfalso. apply Hx. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    split; [exact R | exact Ho].
  - exact (pws_grows_mrestrict _ _ _ Hgr).
  - exact Hhid.
  - exact Hs.
  - intros a [Ha Ho]. exact (Hwr a Ha Ho).
Qed.
End FstepsProofs.
(* ---------------------------------------------------------------------------------------------------------
   14. Announced additions (a Theorem Labs lane 04:2xZ, from a Theorem Labs lane's three base facts). *)
Section CtlBase3.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

(* (i) a global's PARTIAL granule: a shadow const row of value k (0 < k < 8) at shadow_addr g makes the first k bytes
   of the granule at g addressable.  Image B's rows of record are a Theorem Labs lane's generated Tfib_const_shadow
   (e56483f863b, lib/Reusable/YF0m.v:2166-2952; image A: lib/A/AF0m.v 2167-2953, = global-shadow-rows-A.v.txt (a working note, not in this delivery)). *)
Definition ctl_gshadow_of_AR_stmt : Prop :=
  lib.Reusable.YF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md g k lo len,
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    In (lib.Reusable.YG0f.z1 (lib.Reusable.YG0f.ANum (lib.Reusable.YG0f.shadow_addr g)) k) (lib.Reusable.YF0m.Tfib_const ly) ->
    g mod 8 = 0 -> lib.Reusable.YG0f.kImgLo <= g -> g + k <= lib.Reusable.YG0f.kImgEnd ->
    0 < k < 8 -> g <= lo -> 0 <= len -> lo + len <= g + k ->
    B.AsanRT.addressable m lo len.

(* (iii) every cell asan_tls_cells / fp_tls names (at the values ctl_fp_of_AR uses) is owned, so it is apart from any
   byte a caller writes (YCbq.awr_byte_present: an awr byte is not owned). *)
Definition fp_tls_owned_stmt : Prop :=
  lib.Reusable.YF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md a,
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    Exists (fun r => fst r <= a < snd r)
      (B.Prog.RcAsanFP.fp_tls B.AsanRT.RT_TP (Z_to_bv 64 (B.AsanRT.RT_TP + 32))
         (Z_to_bv 64 (lib.Reusable.YG0f.ly_tsd ly)) (Z_to_bv 64 (lib.Reusable.YG0f.ly_C ly))
         (Z_to_bv 64 (lib.Reusable.YG0f.ly_T ly)) (Z_to_bv 64 (lib.Reusable.YG0f.ly_D ly)) 0) ->
    lib.Reusable.YG0n.aowned B ly S a.

(* (i') a WHOLE global body [g, g + n) (announced addition, a Theorem Labs lane 05:4xZ for a Theorem Labs lane's KIND_NAME / QMARK glues): the full
   granules from a zero-shadow range of the bundle (a Theorem Labs lane's record Tfib_zero_shadow, image B: e56483f863b
   lib/Reusable/YF0m.v:2954, is the fine list: it keeps each global's full granules and excludes its partial granule and
   redzone, e.g. image B's KIND_NAME [0x9f580, 0x9f5f0) (asan-ubsan symtab: KIND_NAME at 0x9f580, 0xa0 bytes with its
   redzone; the redzone (0x9f5f0, 0x30) is owned static, YF0m.v:2978) lies in (0x21aa0, 0x9f5f0 - 0x21aa0), YF0m.v:2962),
   the partial last granule from its shadow const row (a Theorem Labs lane's Tfib_const_shadow, YF0m.v:2166+).  Proof =
   ctl_zshadow_of_AR on [g, g + 8 * (n / 8)) + ctl_gshadow_of_AR on the last granule. *)
Definition ctl_global_shadow_of_AR_stmt : Prop :=
  lib.Reusable.YF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md g n r,
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    g mod 8 = 0 -> 0 <= n ->
    In r (lib.Reusable.YG0f.as_zero_shadow B) -> fst r <= g ->
    g + 8 * (n / 8) <= fst r + 8 * (snd r / 8) ->
    (n mod 8 <> 0 ->
       In (lib.Reusable.YG0f.z1 (lib.Reusable.YG0f.ANum (lib.Reusable.YG0f.shadow_addr (g + 8 * (n / 8)))) (n mod 8))
          (lib.Reusable.YF0m.Tfib_const ly)) ->
    g + n <= lib.Reusable.YG0f.kImgEnd ->
    B.AsanRT.addressable m g n.
End CtlBase3.

(* (ii) a view equality at the visible addresses of a class keeps mrd there (K1), and off the image also writability
   (K2): a visible byte's view is its mrd byte (aview = mbyte over the restricted memory), and off the image the rom
   is None, so the view equality is a raw byte equality.  PROVED.  Gives a Theorem Labs lane's stk over [CA, Sp) after a
   fake-stack request from ctl_fs_of_astack's frame condition (stack bytes are above alloc_ceiling and never owned). *)
Lemma ctl_kept_of_view_eq : forall (H : word -> bool) (m m' : word -> option byte) (C : Z -> Prop),
  (forall x : word, H x = false -> C (bv_unsigned x) ->
     lib.Reusable.YG0n.aview segs H m' (bv_unsigned x) = lib.Reusable.YG0n.aview segs H m (bv_unsigned x)) ->
  ctl_kept_vis H m m' C /\ ctl_wmono_vis_off_img H m m' C.
Proof.
  intros H m m' C Hv. split.
  - intros x Hx Hc. specialize (Hv x Hx Hc).
    unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in Hv.
    rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned, Hx in Hv. unfold lib.Lib.Mem.mrd.
    change (lib.Lib.PropExec.seg_rom B.Img0.rsegs x) with (lib.Reusable.YK11.seg_rom segs x).
    destruct (m' x) as [b'|], (m x) as [b|];
      destruct (lib.Reusable.YK11.seg_rom segs x) as [r|]; cbn [option_map] in Hv |- *;
      try discriminate Hv; try reflexivity;
      injection Hv as Hb; f_equal; apply bv_eq; exact Hb.
  - intros x Hx Hc Hni Hw. specialize (Hv x Hx Hc).
    pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    pose proof (lib.Reusable.YCbq.seg_rom_none segs (bv_unsigned x) R Hni) as Hnone.
    rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hnone.
    pose proof (lib.Reusable.YCbq.find_segment_none segs (bv_unsigned x) Hni) as Hfs.
    unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in Hv.
    rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned, Hx, Hnone in Hv.
    unfold wview in Hw |- *. change B.Img0.rsegs with segs in Hw |- *.
    destruct (m x) as [b|]; [|rewrite Hfs in Hw; exfalso; exact (Hw eq_refl)].
    destruct (m' x) as [b'|]; [discriminate | cbn [option_map] in Hv; discriminate Hv].
Qed.

(* 15. Announced additions (a Theorem Labs lane 04:31Z).  as_tsd_TSD PROVED; fp_tls_apart: the thread cells are apart from the side
   stack's class bytes and from any stack window's shadow (a Theorem Labs lane's reac_box_catalogue_match_tls is the instance cs = [0;1;2]).
   Source: the AR values of the cells (two le8 reads at one address agree), the image cells below ASAN_GT <= ly_F
   (ProgWorld_Fs.pw_F_above) and below the shadow bands, C+152 / T+48 / DB+24 in the owned extents ly_C / ly_T / ly_D,
   apart from (ly_F, kFakeStackSize) by layout_ok lo_disj and in application memory.
   Image B's TSD: 0x5fd9f8 = __pthread_tsd_main + 0 (libreac-v190/asan-ubsan/fuzz_ctrl.nm.txt, a 0x400-byte .bss
   object) = lib/Reusable/YF0m.v:12 TFIB_TSD = B.AsanRT.RT_TSDMAIN (image A: 0x5fcbb8, the same symbol in fuzz_ctrl.asan). *)
Lemma as_tsd_TSD : forall B : lib.Reusable.YG0f.asyms,
  lib.Reusable.YF0m.CtrlTSyms B -> lib.Reusable.YG0f.as_tsd B = 0x5fd9f8.
Proof. intros B HTS. rewrite (lib.Reusable.YF0m.ts_tsd _ HTS). reflexivity. Qed.

Section TlsApart.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.
Definition fp_tls_apart_stmt : Prop :=
  lib.Reusable.YF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md (cs : list nat) (lo hi : Z),
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    Forall (fun c => (c <= 6)%nat) cs ->
    lib.Reusable.YG0f.ly_stk_lo ly <= lo -> hi <= lib.Reusable.YG0f.ly_stk_hi ly ->
    forall (DT TS C T DB : word) (k : Z),
      B.Prog.asan_stack_malloc_c.asan_tls_cells m B.AsanRT.RT_TP DT TS C T DB k ->
      B.Prog.RcAsanFP.fp_dj (B.Prog.RcAsanFP.fp_tls B.AsanRT.RT_TP DT TS C T DB k)
        (B.Prog.RcAsanFP.fp_w cs (lib.Reusable.YG0f.ly_F ly) ++
         (B.AsanRT.shadow_addr lo, B.AsanRT.shadow_addr hi) :: nil).
End TlsApart.

(* 16. hid_kept (announced addition, DEFINITION only; a Theorem Labs lane 04:4xZ for a Theorem Labs lane's LLVMF walk): the raw hidden-byte
   clause YCbq.ajournal_exec takes after a call, restricted to the bytes not owned in the post-call state (an
   allocator / fake-stack event may write a byte that was hidden before).  No cgif-form callee post states it today
   (astack_malloc_realizes' post gives view facts only; a core clause is proposed to a Theorem Labs lane). *)
Definition hid_kept {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}
    (B : lib.Reusable.YG0f.asyms) (ly' : lib.Reusable.YG0f.alayout) (S' : lib.Reusable.YG00.astate)
    (W : lib.Reusable.YA0n.world segs) (memc mem2 : word -> option byte) : Prop :=
  forall x : word, lib.Reusable.YA0n.w_H W x = true -> ~ lib.Reusable.YG0n.aowned B ly' S' (bv_unsigned x) ->
    mem2 x = memc x.

(* 17. A live heap block is apart from the fake-stack region (announced addition, a Theorem Labs lane 04:54Z, catalogue_match glue).
   Source (proof pending): chunk placement (Wf chunk_ok, PPrim / PSec: the primary space or a section) and layout_ok's
   lo_disj / sec_placed, which keep those apart from (ly_F, kFakeStackSize). *)
Section BlockApartFs.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.
Definition ctl_block_apart_fs_stmt : Prop :=
  lib.Reusable.YG0d.AR_laws segs B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md p n,
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    In (p, n) (lib.Reusable.YG0d.ablocks B ly S) ->
    p + lib.Reusable.YG00.req_size n <= lib.Reusable.YG0f.ly_F ly \/
    lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeStackSize <= p.
End BlockApartFs.

(* 18. A live fake frame lies above the image (announced addition; final form three Theorem Labs lanes 05:39Z: ONE
   premise-free statement for every class, the `6 <= cid` premise of a48c4068c6e dropped).  frame_addr ly cid pos =
   ly_F ly + kFakeFramesOff + cid * 2^20 + pos * fs_frame_bytes cid (YG0f.v:39-40, :340) >= ly_F ly, because
   0 <= cid <= 10 and 0 <= pos (AR's Wf: wf_fakestack / wfs_live, YG01.v:313); and ASAN_GT = 0x5fe000 <= ly_F ly from AR
   (lib/B/ProgWorld_Fs.v pw_F_above: lo_disj keeps (ly_F, kFakeStackSize) apart from ly_img, and ALedger's al_img puts
   every segment of image B, the last ending at 0x5fdf30 (0xa25e8 + 0x55b948, readelf) below 0x5fe000, inside ly_img).
   0x5fe000 is image B's hull end, lib/B/Prog/ImgBounds.v:9 IMG_HI (the same value as image A's).  As in image A, the
   proof is in lib/B/ProgWorld_Fs.v (ctl_frame_above_img), which can use pw_F_above. *)
Section FrameAbove.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

Definition ctl_frame_above_img_stmt : Prop :=
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md cid pos,
    lib.Reusable.YG0n.AR segs B ly S W m md ->
    In (cid, pos) (lib.Reusable.YG01.frames S) ->
    0x5fe000 <= lib.Reusable.YG0f.frame_addr ly cid pos.
End FrameAbove.

(* 19. A byte of a const row is visible and readable with its value (announced addition, two Theorem Labs lanes 08:05Z /
   08:1xZ; consumers: seg_R18's shadow-word cover of the box catalogue's last row, whose redzone shadow byte 0x8000c05b
   is the const row `z1 (ANum 0x8000c05b) 0xf9` (YF0m.v:2385; image B's BOX_CATALOGUE 0x9f620 + 0xcb8, B symtab),
   a Theorem Labs lane's P12, and any shadow-word cover crossing a
   global redzone).  The core gives it: AR's am_const at as_const B ly = Tfib_const ly (CtrlTSyms' ts_const, YF0m.v:3001)
   makes every row hold over the view (lib/B/ProgWorld_Fs.v pw_row); a byte the view reads is visible (a hidden byte
   lies in no segment, w_Hoff: lib/B/ProgWorldVisFrame.v vis_of_aview); and pw_z1_row gives the byte in mrd form.
   Proof: a Theorem Labs lane, in lib/A/ProgWorldShadow.v (image A), from pw_z1_row + vis_of_aview. *)
Section ConstVis.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

Definition ctl_const_vis_of_AR_stmt : Prop :=
  lib.Reusable.YF0m.CtrlTSyms B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md (e : lib.Reusable.YG0f.aexp) (v a : Z),
    lib.Reusable.YG0n.AR segs B ly S W m md -> In (lib.Reusable.YG0f.z1 e v) (lib.Reusable.YF0m.Tfib_const ly) ->
    lib.Reusable.YG0f.aeval B ly e = a -> 0 <= a < 2 ^ 64 -> 0 <= v < 256 ->
    lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false /\ lib.Lib.Mem.bytes_at B.Img0.rsegs m a (Z_to_bv 8 v :: nil).
End ConstVis.
