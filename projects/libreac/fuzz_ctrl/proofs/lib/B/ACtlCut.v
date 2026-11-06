(* lib/B/ACtlCut.v -- the cut layer of fuzz_ctrl image B's (asan-ubsan) walk of LLVMFuzzerTestOneInput, in the
   released cgif_file_fuzzer form.  Written by a Theorem Labs lane as the image-B twin of a Theorem Labs lane's lib/A/ACtlCut.v
   (a working branch e76ced8e847 with a Theorem Labs lane's frame-law fix b535733d786): same definition names, only module
   paths and image constants differ (check: diff <(sed 's/\bA\./B./g' lib/A/ACtlCut.v) lib/B/ACtlCut.v); section 1b
   (ctl_chain, ctl_trace_in) is written here first and mirrored by image A.  Single writer.  The
   stage files lib/B/ACtlW*.v prove the walk between these cuts and must not edit this file; lib/B/ACtlCutP.v holds
   the 90 cut records (91 table rows; B82f58 is a note); lib/B/ACtlK.v holds the walk-internal names; lib/B/ACtl.v
   holds the top and the composition.

   PROVENANCE
   - translation of record: llvmf-B-walk-plan.md sections 2-5 (a working note, not in this delivery) and its rulings,
     the image-B twin of llvmf-cgif-walk-plan.md (a working note, not in this delivery); cut table
     cut-table-B.tsv (a working note, not in this delivery) (91 rows, every Inv_* verified at its cited line of
     image B's lib/B/Prog/SlotInv.v at 23a791566db).
   - donor, RELEASED: origin/ossv/recipes c8557374ad2e, proofs/cgif/cgif_file_fuzzer/lib.  The cut shell below is
     the donor's rt_from (A/ACf5.v:70-80) and its context record rtcx (:45-48), restated for ctrl.  The ENTRY
     and the EXIT are NOT restated: they are the donor's own lib contract, its image-B twin root YCfn.v
     (tfib_lib_pre_x :31-44, tfib_lib_post_x :45-56, tfib_lib_contract_x :57-67), which the relocated core carries
     as lib.Reusable.YCfn with ctrl's values (porter a Theorem Labs lane 21:37Z / 21:46Z, override table from
     v190/constants-B.md (a working note, not in this delivery)).  One constant, one source: A_LLVMF / RA_LLVMF /
     A_EMPTY / EV_LIB / LIVE_LIB / LLVMF_STK / RLO / RHI are the core's; lib/B/ACtlK.v holds only walk-internal
     names.
   - route (lead via a Theorem Labs lane 21:00Z, porter a Theorem Labs lane 21:01Z): the walk is NEW in the donor's form, reusing
     ctrl's cut plan, cut invariants and loop structure.  It consumes no segment _F and no runtime _F.

   WHY THE CUT BODIES ARE RESTATED INSTEAD OF IMPORTED
   The porter's landing rule (21:18Z, amended 21:29Z / 21:33Z) and a Theorem Labs lane's collision ruling (21:19Z): a port
   file never Imports or Exports a collided ctrl module, and the frame route (SlotInv.v, lib/AZ/**,
   AsanRTInv.v, Contract / FrameAPI, AZ/AS/SpinAlg, A/W6) is outside the port's closure.  ctrl's cut text and
   its helpers (rg / q64 / spill / Sfr / CUTST, the ghost record) live in lib/B/Prog/SlotInv.v, so the bodies
   are transcribed verbatim into lib/B/ACtlCutP.v against the vocabulary below and the allowed pure modules
   (SlotModel.v, lib/Prog/Rc*, lib/Lib/* memory predicates, AsanRT.v), each Required, never Imported.

   NAME COLLISIONS MEASURED IN THIS UNIT (cgif-vocab-in-ctrl.md (a working note, not in this delivery))
   - srealizes: the donor's (lib/Reusable/YK18.v:19-33) is an Inductive with no cut constructor -- that is what
     "cut-free by construction" means, and it is cited BY PATH.  ctrl's lib/AZ/AS/SpinAlg.v:26 defines
     srealizes := YK15.realizes segs, whose YK15.v:208-212 has an rz_cut constructor, i.e. a DIFFERENT relation
     under the same name.  Never Import SpinAlg in a port file.
   - rt_E: donor A/ACf5.v:66 against ctrl lib/B/Prog/SlotModel.v:79, both two-argument.  Not used here.
   - also collided, qualified use only: astate, alayout, ablocks, frames, layout_le, AR, env / st_ok.
   - AIw is a Local Notation (donor YA0n.v:33) and never leaves that file.

   SHADOWED NAMES (a Theorem Labs lane via the porter, 21:37Z): getr, mkst, seg_rom exist in BOTH lib/Lib and the core's
   YK11 and DIFFER (lib/Lib's mkst empties the FP registers; the core's cfg_at uses YK11's mkst over fx).  A file
   that takes mkst from lib/Lib while stating against cfg_at builds GREEN and is wrong.  So this file names them
   lib.Reusable.YK11.* / Reusable.YG0d.cfg_at only and never Imports lib/Lib.  Check, run before every commit:
     grep -nE '(^|[^.A-Za-z_])(mkst|getr|seg_rom|cfg_at)\b' lib/B/ACtlCut.v   -- nothing outside comments

   MODULE PATHS (porter 21:39Z / 21:46Z, port_core's flat layout): the donor's root (image-B) files land in
   lib/Reusable and are named Reusable.<file>: its YCfn.v is ...fuzz_ctrl.lib.Reusable.YCfn (image A's twin is
   lib.A.ACfn).  Reusable.YK11 is one of the 106 files ctrl shares with the donor, kept as ctrl's version.

   BUILD STATE (honest): the core's files arrive with a Theorem Labs lane's relocated core; at 6f430a7d2fa this unit
   carries none of those the walk needs (YA0n YA0i YK18 YG00 YG01 YG0f YG0n YG0d YC5d YCbp YCbq YC85 YE00 and
   the root YCfn).  So this file does NOT compile yet; it is a labelled stand-in, it contains no Axiom, no
   Parameter and no Admitted, and it is scratch-typechecked (zfactsbuild on FACTS ed6b6b7b0ab + PAU
   pau-libreac-v190; there is no cb base, a Theorem Labs lane 21:22Z) the hour the core lands. *)

From Coq Require Import ZArith List Permutation.
(* LPS's machine vocabulary (word, byte, bvmap, config, machine_state, Model, ms_mem, mkCfg, ...) is taken from
   LPS directly, as the donor's A/ACfn.v does: YK11.v only Imports it (YK11.v:9), so `lib.Reusable.YK11.word` does not
   resolve (composition lane, 22:37Z).  The shadowed names getr / mkst / seg_rom / cfg_at stay YK11 / YG0d-
   qualified below, and lib/Lib is never Imported. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YA0n Reusable.YK18.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YG0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0n Reusable.YG0d Reusable.YC5d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v Reusable.YCfn B.ACtlK.
(* route (C) (a Theorem Labs lane 09:20Z / 11:03Z): the cut carries ctl_rt_C (a Theorem Labs lane's B twin of a Theorem Labs lane's A.ACtlRtC). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ACtlRtC.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list.  The lib contract is stated over it (the donor's `Local Notation segs := tfibsegs`,
   root YCfn.v:29, tfibsegs at root YB1v.v:11), so the cut layer must use the SAME list: a free Variable here would
   make `world segs` a different type from the pre's.  The name `Reusable.YB1v.tfibsegs` is the porter's (22:45Z). *)
Local Notation segs := Reusable.YB1v.tfibsegs.

Section CtlCut.

(* The lib contract's own parameters (Reusable.YCfn, Section a): the floating-point state, the run ceiling and the lib
   shape as contexts, plus the journal's sink head (ajournal takes `{SK : YI16.sink_head}`, YCbq.v:121; which
   instance the core supplies is asked of the porter); the symbol bundle, the meter, the two meter bounds and the
   read-only span as variables.  The meter is trivial for ctrl (XM_LIB = XN_LIB = XL0, donor A/ACfi.v:56), so
   mo_le / mo_ok are True and no stage reasons about them.  FP is the freed-block list the journal keeps: the
   walk runs with FP = [] and the last stage reaches the post's [sink_token] through the donor's ajournal_fp_nil
   (A/ACfh.v:29), as the donor's ACfj.v:208-228 does. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : Reusable.YG0f.asyms.          (* Record asyms is donor YG0f.v:154, not YG00 (a Theorem Labs lane, measured) *)
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable FP : list (Z * Z).

(* ---------------------------------------------------------------------------------------------------------
   1. The entry context: the arguments of the donor's tfib_lib_pre_x (root YCfn.v:31-44) as one record, plus the
   engine's anchored sp (donor rt_base, A/ACf5.v:59) and the fake frame's position in class 6 (ctrl's own frame
   class; the donor's is 2).  c_in is the donor's pl, the input bytes, which ctrl's cut bodies read as g_in.
   Dropped from ctrl's ENT, per the translation section 2.1: the kept-block ghost T (the donor keeps no block;
   its post states a Permutation of ablocks), frm_zero, and the entry class bound. *)
Record ctlcx := mkCtlCx {
  c_ly    : Reusable.YG0f.alayout;
  c_S     : Reusable.YG00.astate;
  c_W     : Reusable.YA0n.world segs;
  c_regs  : bvmap 5 word;
  c_mem   : word -> option byte;
  c_md    : Model;
  c_p     : Z;
  c_n     : Z;
  c_in    : list byte;
  c_M     : Z;                      (* the meta measure of the donor's pre (ameta_inv) *)
  c_fpos  : Z;
  c_sp1   : Z
}.

Definition c_sp (cx : ctlcx) : Z := Reusable.YG0d.spZ (c_regs cx).

(* The entry facts are the core's own lib pre at this context, plus the engine's sp anchor.  Nothing about the
   entry is restated, so the walk proves exactly the statement the core composes. *)
(* The donor's pre takes only the section variables it uses (B MT XM_LIB RLO RHI, as ACfj.v:233 applies it),
   its post only B MT XN_LIB (ACfj.v:238); the contexts fx / rc / LS / SK are implicit. *)
Definition ctl_base (cx : ctlcx) : Prop :=
  Reusable.YCfn.tfib_lib_pre_x B MT XM_LIB RLO RHI
    (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx) (c_in cx) (c_M cx) /\
  c_sp1 cx = 32 * ((c_sp cx + -128) / 32).

(* ---------------------------------------------------------------------------------------------------------
   1b. The frame-pointer chain and the call trace at an allocator call: SHELL definitions, NOT ctl_from premises
   (a Theorem Labs lane 23:17Z, agreed with a Theorem Labs lane: image B writes them first, image A mirrors).  The donor's allocator rules
   (amalloc04_rule / afree04_rule, YC5d.v:56-96) take a chain_pre of the caller's frame-pointer chain and its call
   trace in the core's trace universe; the donor builds them per call site (rt_chain, A/ACf5.v:170-185, and
   rt_trace_in, A/ACf5.v:155-163, applied as A/ACf2.v:133-136 does).  Here they are stated once.  Source of the
   statements: a Theorem Labs lane's HCHAIN (lib/B/ACtlW2a.v section 2, ffb9cb21497), split at its two conjuncts: the chain is
   ctl_chain, the trace is ctl_trace_in, and HCHAIN's premises are those of CHAIN_OF_CUT, the named Section
   hypothesis of lib/B/ACtl.v that gives both at every owning cut (a Theorem Labs lane 23:53Z: no Aborted lemma in a shell file,
   so it is a hypothesis where Print Assumptions shows it, not a lemma here).  The reader is the core's
   aview (donor YG0n.v:17), chain_pre is YG0d.v:217, call_trace0 YCbq.v:315, pc_malloc_ra0 / pc_free_ra0 are fields
   of YG0f's acode, as_code / as_universe of YG0f's asyms. *)
Definition ctl_chain (ly : Reusable.YG0f.alayout) (W : Reusable.YA0n.world segs) (mem : word -> option byte)
    (regsT : bvmap 5 word) (ch : list (Z * Z * Z)) : Prop :=
  Reusable.YG0d.chain_pre ly (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem) regsT ch.

Definition ctl_trace_in (pc0 : Z) (regsT : bvmap 5 word) (ch : list (Z * Z * Z)) : Prop :=
  In (Reusable.YCbq.call_trace0 pc0 regsT ch) (Reusable.YG0f.as_universe B).

(* ---------------------------------------------------------------------------------------------------------
   2. Register vocabulary, restated (ctrl's SlotInv.v:82, :351, :367-368), YK11-qualified.  The byte-level
   readers (bytes_at / rw_cells / addressable and ctrl's q64 / u32 / u16 / b8 over them) are lib/Lib's memory
   predicates, allowed by the porter's 21:33Z ruling for exactly this use; lib/B/ACtlCutP.v names them
   qualified, and its header carries the closure scan of what that pulls in. *)
Definition rgv (regs : bvmap 5 word) (r : bv 5) (v : Z) : Prop :=
  lib.Reusable.YK11.getr regs r = Z_to_bv 64 v.
Definition a0v (regs : bvmap 5 word) (v : Z) : Prop := rgv regs 10 v.

(* ---------------------------------------------------------------------------------------------------------
   3. A cut.  The record is the table of cut-table-B.tsv (a working note, not in this delivery): the pc,
   the frame list the cut owns, the event bound, and the cut's own predicate, which is ctrl's cut body
   transcribed verbatim in lib/B/ACtlCutP.v.

   THE BODY STATES THE LIVE-BLOCK LIST ITSELF, as the donor's INV does (A/ACf5.v:84-86, INV_0), and is handed
   the current list bl = ablocks B ly3 S3.  Reason (the transcription lane, 21:31Z): 56 of ctrl's 91 cuts
   carry a live list `entry ++ [(phi, n)]` whose phi is the malloc'd address, existential INSIDE ctrl's body,
   which a field seeing only the context and the index cannot name.

   THE INDEX IS A LIST: [] for a straight cut, [b] for the round trip, [j] for the frame loop, [j; i] for the
   three row cuts, so one field carries every loop shape.  The event bound is stated with the walk's measured
   need B.ACtlK.EV_LLVMF (526), never with the core's EV_LIB, and meets it through EV_LLVMF <= EV_LIB.

   ONE FAKE-STACK ARM.  The body takes the frame base fr and the selector sel, and the shell passes sel = fr.
   The class-full arm, where __asan_stack_malloc_6 would return 0, is NOT a live case in the model: at the entry
   frames S = [] (the core's pre states it), so the donor's room premise count_cid 6 (frames S) < fs_frames 6
   holds, astack_malloc_realizes has only the frame_addr outcome (YG0d.v:284-299), stack_malloc_progress rules
   the null result out (YG05.v:69-84), and a real-stack frame's shadow would be the machine stack's owned zero
   shadow, which no ajournal allows (two Theorem Labs lanes, 21:29Z-21:30Z).  The stage at the fake-stack
   call discharges the machine's s8 = 0 branch from that law, so every cut from the frame's allocation to its
   release owns the class-6 frame.  (The UAR measurement, a Theorem Labs lane's P6, settles only that the fake arm is
   ENTERED; this law is what makes the other one unreachable.) *)
Record ctlcut := mkCtlCut {
  cut_pc   : Z;
  cut_own  : ctlcx -> list (Z * Z);
  cut_kmax : ctlcx -> list Z -> Z;
  cut_body : ctlcx -> list Z -> list (Z * Z) -> Z -> Z ->
             bvmap 5 word -> (word -> option byte) -> Prop
                                                (* cx, idx, bl, fr, sel, regs, mem *)
}.

Definition own6 (cx : ctlcx) : list (Z * Z) := [(6, c_fpos cx)].
Definition own0 (_ : ctlcx) : list (Z * Z) := [].

(* The entry segment picks the fake frame's position: the allocator at 0x8108c chooses pos (aj_stack_malloc_at's
   post is `exists ... pos`), and every own6 cut after it is entered at the context with c_fpos := pos.  So the
   ENTRY stage (seg_A1) can only conclude for posts that do not read c_fpos; the donor states the same thing by an
   `exists fpos` in its entry segment (cgif A/ACfj.v:252).  Added 06:31Z (found by a Theorem Labs lane); name and form are
   image A's twin (a Theorem Labs lane 06:31Z, batch 4). *)
Definition cx_set_fpos (cx : ctlcx) (p : Z) : ctlcx :=
  mkCtlCx (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx) (c_in cx) (c_M cx)
    p (c_sp1 cx).

(* ---------------------------------------------------------------------------------------------------------
   4. The carried ctrl-runtime conjunct (translation section 2.0, design difference 2).  ctrl's inline shadow
   checks read the runtime cells at nearly every cut, so the cut carries three facts and ONE lemma under the vis0 / owned-ro premises (a Theorem Labs lane's
   ctlrt_of_AR, lib/B/ProgWorldCtlRt.v) produces them from AR at entry and after each of the six world-changing steps
   (4 allocator, 2 fake-stack).  One source per byte: where the core's AR / YF0m rows state a cell, that lemma takes
   the core's fact.  mem_inv is NOT carried (a Theorem Labs lane 00:35Z, agreed with a Theorem Labs lane, both images): it has no source in
   the core's world at the entry or after a world step (a Theorem Labs lane, progworld-stmts.md section 0 (a working note, not in this delivery)), so no lemma
   could produce it. *)
Definition ctl_rt (m : word -> option byte) : Prop :=
  B.ACtlK.asan_cells_at m /\ B.ACtlK.shadow_rw_at m /\ B.ACtlK.ro_agree_at m.

(* ---------------------------------------------------------------------------------------------------------
   5. The cut, in the donor's rt_from shape (A/ACf5.v:70-80), with three differences forced by reusing ctrl's
   cut plan (translation section 2.0): no symbolic state (ctrl's cuts are over concrete registers and memory, so
   the body replaces st_ok / rt_E), the carried ctl_rt, and the trivial meter.  POST is the top's continuation;
   for the walk it is ctl_post below.

   THE CUT STATE IS PINNED BY cfg_at (a Theorem Labs lane's finding, 22:44Z): the configuration at a cut is
   `cfg_at segs pc regs mem md` (donor YG0d.v:212, = mkCfg (mkst regs (w64 pc) mem (seg_rom segs)) md over
   YK11's mkst and fx), not an arbitrary machine_state with only its pc fixed.  That gives every stage what the
   donor gets from st_ok (A/ACf5.v:79) - ms_svc_pending = None, the fp registers and fcsr from fx, the rom
   segments - which a footprint run's start state and YK04R.fstep need; it is the form ctl_post's return
   configuration already has; and the entry meets it as `cfg_at segs A_LLVMF regs mem md`, the contract's start. *)
Definition ctl_from (POST : ctlcx -> Reusable.YA0n.world segs -> config -> Prop)
    (X : ctlcut) : Prop :=
  forall (cx : ctlcx) (idx : list Z) (fr k : Z) ly3 S3 W3
         (regs3 : bvmap 5 word) (mem3 : word -> option byte) md3,
    ctl_base cx ->
    Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (c_sp cx) FP
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      (cut_own X cx) ly3 S3 W3 mem3 md3 k ->
    Reusable.YG01.frames S3 = cut_own X cx ->
    (* the frame base IS the journal's owned frame: the donor's rt_F cx = frame_addr (c_ly cx) 2 (c_fpos cx)
       (A/ACf5.v:64), stated once here for every owning cut, vacuous for own0 (a Theorem Labs lane's finding:
       the free_6 call, the `beqz s8` not-taken step and every frame-byte footprint need it) *)
    (forall cid pos, In (cid, pos) (cut_own X cx) -> fr = Reusable.YG0f.frame_addr (c_ly cx) cid pos) ->
    k <= cut_kmax X cx idx ->
    cut_body X cx idx (Reusable.YG0d.ablocks B ly3 S3) fr fr regs3 mem3 ->
    (* route (C), 11:15Z: the NARROWED runtime conjunct (shadow_rw only on the cut's own shadow and the image's),
       which the core's AR gives at every state without AR_states_vis0_shadow (B.ProgWorldCtlRtC.ctl_rt_C_of_AR);
       the full ctl_rt above is not a world fact (a Theorem Labs lane truth audit 11:04Z).  ctl_rt -> ctl_rt_C is
       B.ACtlCutC.ctl_rt_C_of_ctl_rt. *)
    B.ACtlRtC.ctl_rt_C B ly3 S3 mem3 ->
    Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs (cut_pc X) regs3 mem3 md3) (POST cx).

(* One loop turn of a cut.  ctl_from quantifies the index inside, so a loop latch - whose premise is the next
   turn's cut at ONE index - cannot be composed from it directly; the donor's rt_G_allX is measure-indexed for
   the same reason.  ix_cut restricts a cut to one index, and ctl_from_ix says a cut holds iff it holds at every
   index, so a loop stage reads
     forall POST j, ctl_from POST (ix_cut C_latch [Z.of_nat (S j)]) -> ctl_from POST C_exit ->
                    ctl_from POST (ix_cut C_head [Z.of_nat j]).
   (Same name and statement as image A's, a Theorem Labs lane's lib/A/ACtlCut.v.) *)
Definition ix_cut (X : ctlcut) (i0 : list Z) : ctlcut :=
  mkCtlCut (cut_pc X) (cut_own X) (cut_kmax X)
    (fun cx idx bl fr sel regs m => idx = i0 /\ cut_body X cx idx bl fr sel regs m).

Lemma ctl_from_ix : forall POST X, (forall i0, ctl_from POST (ix_cut X i0)) <-> ctl_from POST X.
Proof.
  intros POST X; split.
  - intros H cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL HK HP HR.
    exact (H idx cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL HK (conj eq_refl HP) HR).
  - intros H i0 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL HK HP HR.
    destruct HP as [_ HP].
    exact (H cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL HK HP HR).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   6. The exit.  Not restated: the return configuration at the core's RA_LLVMF together with the core's own lib
   post (root YCfn.v:45-56) for some leaf, which is what the continuation of tfib_lib_contract_x (root YCfn.v:61-66)
   consumes.  The walk's last cut (B82f5c, own0) reaches this with k <= EV_LLVMF. *)
Definition ctl_post (cx : ctlcx) : Reusable.YA0n.world segs -> config -> Prop :=
  fun W' c' => exists (l : lib.Reusable.YO09.lleaf) ly' S' regs' mem' md' k,
    c' = Reusable.YG0d.cfg_at segs Reusable.YCfn.RA_LLVMF regs' mem' md' /\
    Reusable.YCfn.tfib_lib_post_x B MT XN_LIB
      (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx) (c_M cx) l
      ly' S' W' regs' mem' md' k.

End CtlCut.

(* ---------------------------------------------------------------------------------------------------------
   HOW A STAGE FILE USES THIS (lib/B/ACtlW*.v, one writer per file)

   A stage lemma is "the successor cuts hold -> this cut holds", exactly as the donor's rt_A2 (A/ACf0.v:173),
   rt_B (A/ACf1.v:499), rt_C (A/ACf2.v:402) and rt_D (A/ACf3.v:311) are shaped:

     Lemma ctl_W5_B82eac : forall POST,
       ctl_from B MT XM_LIB RLO RHI FP POST C_B82ecc ->
       ctl_from B MT XM_LIB RLO RHI FP POST C_Jrel ->
       ctl_from B MT XM_LIB RLO RHI FP POST C_B82eac.

   (after End CtlCut a definition takes only the section variables it uses, in declaration order: ctl_from
   takes B MT XM_LIB RLO RHI FP; ctl_post takes B MT XN_LIB; ctlcx and the cut records take none; the contexts
   fx / rc / LS / SK stay implicit.  The TOP instantiates SK EXPLICITLY with the core's
   `Reusable.YE2k.tfib_sink_head` (root YE2k.v:44, ofl_head 0x5fcd48 = ctrl's B ofl_head; porter 22:45Z) and never
   lets instance search find YL0j's global src0_sink_head.)

   with the cut records C_* from lib/B/ACtlCutP.v.  Standing rules for those files: one local lemma per
   allocator site and nothing else in the file touching the allocator (a Theorem Labs lane's measured rule); no Axiom,
   no Parameter, no Admitted -- a premise that cannot be discharged becomes a named Section hypothesis with its
   exact text; and at each callee call site the stage proves the callee spec's caller obligations as its owner
   lists them (e.g. a Theorem Labs lane's treac_ctrl_parse_spec, P1-P13,
   spec-draft.md section 4 (a working note, not in this delivery)).  The top (lib/B/ACtl.v) composes the stages into Reusable.YCfn.tfib_lib_contract_x,
   as the donor's ACfj.v:230-258 does. *)

(* ajournal_fp_nil, COPIED VERBATIM from the donor, proofs/cgif/cgif_file_fuzzer/lib/A/ACfh.v:29-43 at
   origin/ossv/recipes c8557374ad2e (its sections: d with {fx} {rc} {SK} :24-25, e with segs / B :26-28); only the
   module paths change, and the Section's sink head is passed BY NAME, `(SK := SK)`, to ajournal and
   fp_spares_closed (porter 00:59Z: an implicit sink head can elaborate to a global instance such as YI5b's
   src0_sink_head).  A/ACfh.v does not join the core (porter 22:43Z: its closure pulls 26 non-core files),
   but this proof uses only the core's ajournal and four helpers, each named through the core:
     Reusable.YCbq.aos_step_mono     donor YCbq.v:65
     Reusable.YCbq.sink_closed_nil   donor YCbq.v:99
     Reusable.YCbq.fp_spares_closed  donor YCbq.v:87 (Section e, implicit {SK})
     lib.Reusable.YI04.inFP_nil          donor YI04.v:390 (YCbq Requires YI04; ctrl's kept copy, lib/Reusable/YI04.v:393)
   The walk runs with FP = [] (section 1 of Section Ctl); the exit stage seg_Y3 lifts its journal to the post's
   [sink_token] with this lemma, as the donor's lx_leaf_fail does (ACfj.v:194). *)
Section FpNil. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variable B : Reusable.YG0f.asyms.
Lemma ajournal_fp_nil : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply Reusable.YCbq.aos_step_mono; [|exact Hio]; intros Ho; exfalso; exact (Reusable.YCbq.sink_closed_nil Ho)|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
split; [intros p n i H1 H2 Hi _; apply (F2 p n i H1 H2 Hi); apply lib.Reusable.YI04.inFP_nil|].
split; [intros a Hi Hns He _; apply (F3 a Hi Hns He); apply (Reusable.YCbq.fp_spares_closed (SK := SK)); intros Ho; exact (Reusable.YCbq.sink_closed_nil Ho)|].
split; [intros cid pos a H1 H2 _; apply (F4 cid pos a H1 H2); apply lib.Reusable.YI04.inFP_nil|].
split; [intros p n i H1 H2 Hi; exfalso; exact (lib.Reusable.YI04.inFP_nil _ (Hgone p n i H1 H2 Hi))|].
split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5 | exact HQT].
Qed.
End e.
End FpNil.
