(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 2422 of its 2466 lines of code are new or changed and 984 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW3a.v, with its module names and addresses changed; 898 of its 975 lines of code are new or changed and 2389 lines of the source are left out. *)
(* lib/B/ACtlW5.v -- piece W5 (the tail: S_X1, S_X2, S_Jrel, S_Y1, S_Y3) of fuzz_ctrl image B's (asan-ubsan) walk
   of LLVMFuzzerTestOneInput in the released cgif_file_fuzzer form.  One writer: a Theorem Labs lane (proof pass).
   rule 24: no function proved (stage glue of a walk).

   WHAT THIS FILE PROVES: one stage lemma per walked cut of W5, in the donor's continuation shape
   (rt_A2 A/ACf0.v:173 .. rt_D A/ACf3.v:311 at c8557374ad2e), over lib/B/ACtlCut.v's ctl_from and
   lib/B/ACtlCutP.v's records.  No index, no loop.  All five are closed by Qed over the named Section hypotheses below.
     B82eac (0x82eac, own6) --S_X1--> B82ecc (memchr arm) | Jrel (byte 20 of the identity record = 0)
     B82ecc (0x82ecc, own6) --S_X2--> Jrel
     Jrel   (0x82f2c, own6) --S_Jrel--> B82f48            (sel = fr: the fake-frame release arm only)
     B82f48 (0x82f48, own6) --S_Y1--> B82f5c              (__asan_stack_free_6 @0x82f48 releases the frame)
     B82f5c (0x82f5c, own0) --S_Y3--> exit at RA_LLVMF 0x80f14 (post_leaf: lib/B/ACtl.v's ctl_post_leaf, the core's
                                      tfib_lib_post_x at fuzz_ctrl's one leaf)
   B82f58 (0x82f58) has NO RECORD (ACtlCutP.v: the class-full real-stack release join; with sel = fr no stage
   reaches it) and so NO stage lemma here; S_Y2 (its __asan_set_shadow_00 unpoison of the real-stack frame) is not
   walked.  Every k bound of the piece is B.ACtlK.EV_LLVMF = 526 (<= EV_LIB = 2000).

   ROUTE (lib/A/ACtlG/A5.v's glue pattern at a working branch): each footprint run starts at the cut's
   cfg_at (= lib/Lib's MS), the walk is moved to the run's canonical register map (Reusable.YA0nR.SRr_xregs_eqv),
   lifted by B.ProgBridge.fevt_of_evtF and Reusable.YA0nR.SRr_fevt_hid at the footprint B.ProgBridge.RNG_W (w_H W);
   the journal crosses a writing run by Reusable.YCbq.ajournal_exec (writes = bytes of the owned class-6 frame or
   its shadow, w5_journal_munch), the memchr call by Reusable.StackFreeJournal.ajournal_after_write_win (writes =
   the callee window) and the release by Reusable.StackFreeJournal.aj_stack_free_at.  Route (C): every cut carries
   the narrowed ctl_rt_C (B.ACtlRtC); the only conjunct a W5 stage READS at its entry cut is ro_agree (seg_X1's
   memchr call: rom_view, w5_rom_view); no W5 run or callee contract reads shadow_rw (X12F / YTailF take the frame's
   shadow from AR's frame law; amemchr_realizes and astack_free_realizes have no shadow_rw premise).  ctl_rt_C of
   every successor cut is a Theorem Labs lane's proved B.ProgWorldCtlRtC.ctl_rt_C_of_AR on the journal's AR and the kept
   read-only view (w5_ctlrt).  The frame base is the journal's frame (shell gap (G1), ACtlCut.v's
   frame law): fr = frame_addr ly3 6 pos, with frames_bounds / al_frames / al_client_img / al_flag from AR_laws.

   SECTION HYPOTHESES OF THIS FILE (sources; per stage, Check of each lemma lists exactly the ones it uses):
   - LAWS, Hwx: the core's AR laws and the kit's wx_segs_nowrap, the walk's shared named hypotheses (top discharges).
   - TFIB_SYMS, RELRO_IMG, RO_OFL (Context): the premises of B.ProgWorldCtlRtC.ctl_rt_C_of_AR and of
     Reusable.APostBase.arodata_ok_journalP, exact names and texts given by a Theorem Labs lane (06:40Z / 06:46Z).
     (VIS0 / OWNED_RO are gone: route (C), AR_states_vis0_shadow is false at an AR state.)
   - AIL: Reusable.YE01.asink_img_laws at the core's sink head and tfib_K (seg_Y3's asink_none / ameta_inv); the
     core proves it as Reusable.YD1u.tfib_AIL, not cited because YD1u's closure has lib/Reusable/YE2y.v, which does
     not compile on the walk line adc9b58a03c (YE2y.v:75).
   - HMOLE: the trivial meter's mo_le (the top's MT is Reusable.YCbp.ameter_triv, mo_le True).
   - ML: the core's model_laws over B's universe (aj_stack_free_at's Section hypothesis; AsanAPI aa_model).
   - HMEMCHR_ENTRY: B_memchr_tramp_entry = 0x42ab0 (where X12F.x12_a_pre_F runs to).
   - AMEMCHR (with Variable B_memchr_tramp_entry, intended 0x42ab0): `__interceptor_trampoline_memchr` @0x82ec8, ctrl's
     call fuzz_ctrl.c:711 memchr(id.model_name, 0, 17).  The shared text is a Theorem Labs lane's `amemchr_realizes`
     (MemchrDef.v:21, a Theorem Labs lane's 23:53Z ruling; moving to lib/Reusable/MemchrDef.v on a working branch), by that exact name and
     argument order (segs B pc): any byte c, n < 2^32, a found or not-found result, the whole [x, x + n) addressable.
     It is PROVED for disco (a Theorem Labs lane 23:56Z: a working branch 3b8a77d146c
     proofs/libreac/fuzz_disco/lib/Y/Rt/Memchr.v:566 `memchr_icpt_realizes`, no Admitted, no Axiom; disco's trampoline
     is 0x42a54) and reaches ctrl by relocation; until the relocated instance lands it is this Section hypothesis, with
     the entry a Variable, never the literal (the porter's trampoline rule, 23:17Z).  ctrl's copy of the definition
     is lib/Reusable/MemchrDef.v.
   - stack_free6_contract: `__asan_stack_free_6` @0x82f48 (callee 0x3dd30), a Theorem Labs lane's name for the shared core's
     class-6 release (a Theorem Labs lane 22:53Z, a Theorem Labs lane's final word): `astack_free_realizes tfibsegs B 0x3dd30 6`, a Theorem Labs lane's
     lib/Reusable/StackFreeDef.v form (explicit pc; premises include a1 = n with 8 <= n <= fs_frame_bytes 6 = 4096 and
     n mod 8 = 0, so a1 = 3136 fits; its 0xf5 pattern cell is 0x10338, a core constant, a Theorem Labs lane 23:07Z), by path in
     lib/Reusable/StackFreeDef.v from a working branch fa349ffc195.  Its premise on the frame's trailer word
     comes from the shell's FRAHC trailer conjunct (a218ac85be5).
   - ITEM 23 (the final ProgWorld form), the two conversions this piece uses, pasted below from the walk's shared
     RtPost text (lib/B/RTPOST-SHARED-B.txt) as named Section hypotheses.  Both are PROVED in this tree in
     lib/B/ProgWorld.v (owner a Theorem Labs lane): aview_vis_mrd as B.ProgWorld.aview_vis_mrd (ProgWorld.v:587) and
     ctl_post_memchr as B.ProgWorld.ctl_post_memchr (ProgWorld.v:659).  They stay here as RTPOST NOTE rows until the
     owner swap.  SOURCE of that block: a Theorem Labs lane's lib/A/ProgWorld.v
     (at head lib/A/ProgWorld.v:546-559, :564-567 and :625-629; written on a working branch c03ce1627b6), twinned for image B.
     ctl_post_memchr is a Theorem Labs lane's window statement at K := ESTACK: munch_vis / wmono_vis in the mrd vocabulary at
     visible addresses outside the CALLEE WINDOW [sp - ESTACK, sp), the whole written range of the memchr call; its
     premise rt_post_frame (aview clause + apresent clause) is exactly amemchr_realizes' post (seg_X1).
     aview_vis_mrd is item 23's one primitive: at a VISIBLE address the core's aview is lib/Lib's mrd read (seg_X1's
     shadow and model_name reads, seg_Y1's trailer word and its saved bytes after the release).  A raw `mem x`
     equality is claimed nowhere in this file: it is not derivable from a view post.
   `_F` LEMMAS (a working branch 4d6ca903c00; texts in
   (internal path){X12F,YTailF}.md; module
   OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.<File>F, Required qualified, never Imported, a Theorem Labs lane 23:38Z;
   split at EVERY call, and a call whose return pc is the next cut has no `_post_F`):
   - X12F.x12_store_evt_F  (Seg/X12.v:303; the shared shadow-fill block 0x82ed0-0x82f2c, 20 `sb` of 0xf8 into the
                            frame shadow [S(fr) + 328, S(fr) + 365), then the reloads s8 = [A+48], s9 = [A+40])
   - X12F.x12_b_evt_F      (Seg/X12.v:360; the byte-20 = 0 arm 0x82eac -> 0x82ed0)
   - X12F.x12_a_pre_F      (Seg/X12.v:393; 0x82eac -> the memchr wrapper 0x42ab0 with ra = 0x82ecc = the cut; no post)
   - X12F.x12_x2_evt_F     (Seg/X12.v:503; 0x82ecc -> 0x82ed0, `beqz a0,0x82fa4` not taken)
   - YTailF.jrel_evt_side_F (Seg/YTail.v:1133; 0x82f2c -> 0x82f48, the sel = fr arm)
     (YTailF.jrel_evt_real_F, :1102, the sel = 0 arm to 0x82f58, and YTailF.y2_pre_F, 0x82f58 -> set_shadow_00
     0x55024, are NOT used: that arm is the discharged class-full arm, no record, and ACtl.v's seg_Jrel has no B82f58
     premise; so this file needs no set_shadow_00 contract)
   - YTailF.y1_pre_F (0x82f48 -> stack_free_6 0x3dd30, ra = 0x82f4c) and YTailF.y1_post_F (0x82f4c `j 0x82f5c`)
   - YTailF.y3_evt_F       (Seg/YTail.v:66; 0x82f5c -> ret: `li a0,0`, the 13 reloads from [S - 104, S), sp = S,
                            `ret` to ra = RA_LLVMF)
   PROVENANCE: cut table rows 86-91; plan 2.3 rows 85-90, 2.6 (Y1 row), 6.2 (no trap on W5 paths); ctrl's runs at
   a working branch 3803efccea0 (Seg/X12.v, Seg/YTail.v); objdump L85730-L85812.

   ABORT-SINK / TRAP OBLIGATIONS ON W5 (objdump 0x82eac-0x82fa0, all 164 branches into 0x82fa4 / 0x82fa0 listed by
   one awk over the listing): exactly ONE, 0x82ecc `beqz a0,0x82fa4` (L85760), in S_X2's run (seg_X2). No UBSan
   branch (plan 6.2). *)

From Coq Require Import ZArith List Permutation Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04R Reusable.YA0nR Lib.ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCfn.
(* the core's sink / meta kept lemmas (asink_none_kept, ameta_inv_kept) and the walk's sink head and syms, for the
   exit stage seg_Y3 *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YE00 Reusable.YE01 Reusable.YE2k Reusable.YF0m.
(* ctl_rt_C at every successor cut (route (C)): a Theorem Labs lane's proved B.ProgWorldCtlRtC.ctl_rt_C_of_AR, fed with the
   kept read-only view (Reusable.APostBase.arodata_ok_journalP, B.ProgWorld.arodata_okP_of_S). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.APostBase B.ProgWorld.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ACtlRtC ProgWorldCtlRtC.
(* a Theorem Labs lane's StackFreeDef (text of record, by path from a working branch fa349ffc195) and its journal rule
   StackFreeJournal (aj_stack_free_at, ajournal_after_write_win), a Theorem Labs lane's MemchrDef. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.StackFreeDef Reusable.StackFreeJournal.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.MemchrDef.
(* lib/Lib's raw-memory vocabulary of the call-post fact below and of the `_F` runs (Required only, never Imported). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Lib.Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Frame Mem PropExec MState Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Img0 B.ACtlK B.ACtlCut B.ACtlCutP B.AsanRT.
(* a Theorem Labs lane's frozen image-B bridge (RNG_W, fp_avoids_RNG_W, rng_of_visible, rsegs_spans, fevt_of_evtF, cfg_at_MS). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgBridge.
(* The top, for its exit post ctl_post_leaf only (ACtl.v Requires no stage file, so this is no cycle). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ACtl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require X12F YTailF.
Import ListNotations.
Local Open Scope Z_scope.

Section W5.

Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable FP : list (Z * Z).

Local Notation segs := Reusable.YB1v.tfibsegs.

(* ---- SHELL BINDING: the only lines that name ACtlCut's / ACtlCutP's argument lists.  At the re-twin, fix the
   argument lists here and nowhere else.  a Theorem Labs lane 22:4xZ (d): ctl_base / ctl_post take only the variables they use
   (tfib_lib_pre_x B MT XM_LIB RLO RHI, tfib_lib_post_x B MT XN_LIB); ctl_from adds the journal's FP. ---- *)
Local Notation ctl_from := (ACtlCut.ctl_from B MT XM_LIB RLO RHI FP).
(* lib/B/ACtl.v's ctl_post_leaf (ACtl.v:285-292), the exit post the top consumes, by name (gate note on c80d46e98f9:
   ACtl.v Requires no stage file, so Requiring it here is no cycle). *)
Local Notation post_leaf := (B.ACtl.ctl_post_leaf B MT XN_LIB).
Local Notation C_B82eac := (ACtlCutP.C_B82eac B).
Local Notation C_B82ecc := (ACtlCutP.C_B82ecc B).
Local Notation C_Jrel := (ACtlCutP.C_Jrel B).
Local Notation C_B82f48 := (ACtlCutP.C_B82f48 B).
Local Notation C_B82f5c := (ACtlCutP.C_B82f5c B).

(* ---- Section hypotheses (sources in the header) ---- *)
(* The core's AR laws (YG0d.v:496 AR_laws; the donor walk takes them the same way, A/ACf2.v:47), the same text as
   lib/B/ACtlW2a.v, ACtlW3a.v, ACtlW4e1.v, ACtlW4g.v: ajournal_exec, frames_bounds, al_frames and al_client_img are
   stated under it.  Supplied by the core's api_of_core (aa_laws). *)
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.

(* The kit's once-per-unit premise of Reusable.YA0nR.SRr_fevt_hid (a Theorem Labs lane bridge-stmt.md:114 (a working note, not in this delivery)), the walk's shared
   named hypothesis (a Theorem Labs lane 05:31Z: the top discharges it). *)
Hypothesis Hwx : Reusable.YK04.wx_segs_nowrap segs.

(* Route (C) (brief routeC-refit.md): the successor cuts' ctl_rt_C is B.ProgWorldCtlRtC.ctl_rt_C_of_AR (PROVED;
   CtrlTSyms + AR_laws + AR + arodata_okP, no AR_states_vis0_shadow, no AR_states_owned_ro), whose premise the next
   line carries, exact name and text; the top discharges it.  RELRO_IMG and RO_OFL are the premises of
   Reusable.APostBase.arodata_ok_journalP, which keeps the entry's read-only view (ctl_base's arodata_okS, through
   B.ProgWorld.arodata_okP_of_S) along the journal to each successor state (w5_ctlrt below). *)
Hypothesis TFIB_SYMS : Reusable.YF0m.CtrlTSyms B.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Context {RO_OFL : Reusable.APostBase.ro_below_ofl segs RLO RHI}.

(* The sink's image laws at the walk's sink head and syms (Reusable.YE01.asink_img_laws, the premise of
   YE01.asink_none_kept / ameta_inv_kept, which seg_Y3 uses for the exit post's asink_none / ameta_inv).  The core
   proves it as Reusable.YD1u.tfib_AIL from CtrlTSyms B and AR_laws (YD1u.v:42); the top discharges this hypothesis
   with `Reusable.YD1u.tfib_AIL B TFIB_SYMS LAWS`.  Not cited here because YD1u's closure has
   lib/Reusable/YE2y.v, which does not compile on the walk line adc9b58a03c (YE2y.v:75, `Unable to unify "true" with
   "false"`; build (internal path) 20261029T054547Z). *)
Hypothesis AIL : Reusable.YE01.asink_img_laws (SK := Reusable.YE2k.tfib_sink_head) segs B Reusable.YE2k.tfib_K.

(* The trivial meter: the top instantiates MT := Reusable.YCbp.ameter_triv (lib/B/ACtl.v:917), whose mo_le is True
   (YCbp.v:16).  The exit post's mo_le conjunct is this fact; no cut carries a meter relation (ACtlCut.v section 5). *)
Hypothesis HMOLE : forall (S S' : Reusable.YG00.astate) (m : Z), Reusable.YC5d.mo_le MT S S' m.

(* __interceptor_trampoline_memchr @0x82ec8: a Theorem Labs lane's amemchr_realizes (a Theorem Labs lane 23:3xZ), at B's trampoline entry. *)
Variable B_memchr_tramp_entry : Z.
(* Image-B instance (a Theorem Labs lane 00:58Z): B.Rt.Memchr.memchr_icpt_realizes (0x42ab0), text after B's core lands; the top
   discharges this hypothesis with it (and B_memchr_tramp_entry := 0x42ab0). *)
Hypothesis AMEMCHR : Reusable.MemchrDef.amemchr_realizes segs B B_memchr_tramp_entry.
(* The trampoline entry is the address x12_a_pre_F (lib/B/Prog/Seg/X12F.v) runs to: the relocated instance's 0x42ab0.
   The top discharges it by eq_refl when it instantiates B_memchr_tramp_entry := 0x42ab0. *)
Hypothesis HMEMCHR_ENTRY : B_memchr_tramp_entry = 0x42ab0.

(* __asan_stack_free_6 @0x82f48 (callee 0x3dd30): a Theorem Labs lane's name, a Theorem Labs lane's form. *)
Hypothesis stack_free6_contract : Reusable.StackFreeDef.astack_free_realizes segs B 0x3dd30 6.

(* The core's allocator-model laws over B's trace universe (YG0d.v:514 model_laws; the AsanAPI field aa_model,
   YG0d.v:533), the premise of the free-6 journal rule StackFreeJournal.aj_stack_free_at (its Section hypothesis ML,
   StackFreeJournal.v:164).  Supplied by the core's api_of_core. *)
Hypothesis ML : Reusable.YG0d.model_laws (Reusable.YG0f.as_universe B).

(* The freed-block list is the empty one: the top runs the walk with FP := [] (lib/B/ACtl.v's CF notation) and
   discharges this by eq_refl; the sibling lib/B/ACtlW4g.v's name and text.  Only seg_Y3 takes it: its exit post
   needs the journal at FP = [] (w5_journal_sk at [], YI04.inFP_nil). *)
Hypothesis FP_nil : FP = [].

(* ---- RtPost, image B: the shared text of record of this walk (RTPOST-SHARED-B.txt (not in this delivery), author a Theorem Labs lane for
   a Theorem Labs lane), pasted token for token; only the members this file uses are here.  SOURCE: a Theorem Labs lane's
   lib/A/ProgWorld.v (at head lib/A/ProgWorld.v:546-559, :564-567 and :625-629; written on a working branch c03ce1627b6), with
   lib.Reusable -> Reusable, Lib. -> lib.Lib. and A.Img0 -> B.Img0 and nothing else; a Theorem Labs lane's Definitions are Local Notations here and
   its PROVED lemmas named Section hypotheses, as RTPOST-SHARED-B.txt (a working note, not in this delivery) states them.  lib/B/ProgWorld.v (owner
   a Theorem Labs lane) is in this tree and proves both members over its own Definitions munch_vis / wmono_vis /
   rt_post_frame (ProgWorld.v:569-582): aview_vis_mrd at ProgWorld.v:587, ctl_post_memchr at ProgWorld.v:659.  They
   stay here as RTPOST NOTE rows until the owner swap.  The earlier placeholder, which concluded wmono_vis from an
   aview clause with no apresent premise, is gone.
   SITE: the memchr trampoline 0x82ec8 (return 0x82ecc = the cut B82ecc); rt_post_frame's two clauses are
   amemchr_realizes' post (MemchrDef.v:20: the view outside the callee window and the presence clause; seg_X1).
   The stack-free release at 0x82f48 is a world-form call too: its view post reaches the cut body through
   aview_vis_mrd (seg_Y1). ---- *)
Local Notation munch_vis H WR m m' :=
  (forall x : word, H x = false -> lib.Lib.Frame.outside WR (bv_unsigned x) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' x = lib.Lib.Mem.mrd B.Img0.rsegs m x).
Local Notation wmono_vis H m m' :=
  (forall x : word, H x = false -> wview B.Img0.rsegs m x <> None -> wview B.Img0.rsegs m' x <> None).
Local Notation rt_post_frame W mem mem' WR :=
  ((forall a, 0 <= a < 2 ^ 64 -> lib.Lib.Frame.outside WR a ->
      Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem' a =
      Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a) /\
   (forall a, Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem a ->
      Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem' a)).

(* aview_vis_mrd: lib/A/ProgWorld.v (at head lib/A/ProgWorld.v:564-567; written on a working branch c03ce1627b6); PROVED in this tree as B.ProgWorld.aview_vis_mrd (ProgWorld.v:587). *)
Hypothesis aview_vis_mrd : forall (W : Reusable.YA0n.world segs) (mem : word -> option byte) (a : Z),
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a =
  option_map (fun b : byte => bv_unsigned b) (lib.Lib.Mem.mrd B.Img0.rsegs mem (Z_to_bv 64 a)).

(* ctl_post_memchr: lib/A/ProgWorld.v (at head lib/A/ProgWorld.v:625-629; written on a working branch c03ce1627b6), ctl_post_window_stmt at K = ESTACK; PROVED in this tree as B.ProgWorld.ctl_post_memchr
   (ProgWorld.v:659). *)
Hypothesis ctl_post_memchr :
  forall (W : Reusable.YA0n.world segs) (mem mem' : word -> option byte) (sp : Z),
    rt_post_frame W mem mem' ((sp - Reusable.YG0d.ESTACK, sp) :: nil) ->
    munch_vis (Reusable.YA0n.w_H W) ((sp - Reusable.YG0d.ESTACK, sp) :: nil) mem mem' /\
    wmono_vis (Reusable.YA0n.w_H W) mem mem'.

(* ---------------------------------------------------------------------------------------------------------
   Stage helpers.  The image facts (segment hull, wx_segs_nowrap) are computed from lib/B/ProgBridge.v's rsegs_spans;
   the lift is lib/A/ACtlG/A5.v's G3/G4 (cfg_at = lib/Lib's MS, the walk moved to the run's canonical register map
   by Reusable.YA0nR.SRr_xregs_eqv, ProgBridge.fevt_of_evtF, Reusable.YA0nR.SRr_fevt_hid); the frame facts come from
   the journal's AR (frames_bounds, al_frames, al_client_img); the journal across a writing footprint run is the
   core's ajournal_exec. *)
Local Notation AJ cx own ly3 S3 W3 mem3 md3 k :=
  (Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
     (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
     own ly3 S3 W3 mem3 md3 k).
Local Notation FX5 :=
  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.mkFP lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr).

Lemma w5_img : forall a, Reusable.YG0d.in_img segs a -> 0x10000 <= a < 0x5fe000.
Proof.
  intros a (sg & Hin & Ha).
  pose proof (in_map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) _ _ Hin) as Hm.
  change Reusable.YB1v.tfibsegs with B.Img0.rsegs in Hm. rewrite B.ProgBridge.rsegs_spans in Hm.
  cbn [In] in Hm. destruct Hm as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; lia.
Qed.

Lemma w5_segs_low : forall a, Reusable.YG0d.in_img segs a -> 0 <= a < Reusable.YG0f.kLowMemEnd.
Proof. intros a H. apply w5_img in H. unfold Reusable.YG0f.kLowMemEnd. lia. Qed.

Lemma w5_lift : forall (W : Reusable.YA0n.world segs) (regs : bvmap 5 word) (mem : word -> option byte) md (pc : Z)
    (RNG : Lib.ExecF.footprint) (P : machine_state -> Prop) (Q : Reusable.YA0n.world segs -> config -> Prop),
  Lib.ExecF.evtF B.Img0.rsegs RNG P
    (lib.Lib.MState.MS (Lib.Regs6ss.mkR_of regs) lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None
       mem (lib.Lib.PropExec.seg_rom B.Img0.rsegs)) ->
  Reusable.YK04R.fp_avoids (Reusable.YA0n.w_H W) RNG ->
  (forall ms' md', P ms' -> (forall x : word, Reusable.YA0n.w_H W x = true -> ms_mem ms' x = mem x) ->
     Reusable.YK04.same_but_materialized md md' -> Reusable.YA0n.SRr segs W (mkCfg ms' md') Q) ->
  Reusable.YA0n.SRr segs W (Reusable.YG0d.cfg_at segs pc regs mem md) Q.
Proof.
  intros W regs mem md pc RNG P Q Hrun Hav K.
  change (Reusable.YG0d.cfg_at segs pc regs mem md) with
    (mkCfg (lib.Lib.MState.MS regs lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None mem
              (lib.Lib.PropExec.seg_rom B.Img0.rsegs)) md).
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W (Lib.Regs6ss.mkR_of regs) regs).
  2: exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs)).
  apply (Reusable.YA0nR.SRr_fevt_hid segs Hwx W _ md RNG P Q (B.ProgBridge.fevt_of_evtF RNG P _ Hrun) Hav).
  intros ms' md' HP Hhid Hsbm. apply (K ms' md' HP); [| exact Hsbm].
  intros x Hx. rewrite (Hhid x Hx). reflexivity.
Qed.

(* The owned class-6 frame of an own6 cut, from the journal's AR (frames_bounds, al_frames, al_client_img). *)
Lemma w5_frame : forall (cx : ACtlCut.ctlcx) ly3 S3 W3 mem3 md3 k,
  AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3) /\
  Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) /\
  4096 <= Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) /\
  Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) + 4096 <= lib.Reusable.YM05.alloc_ceiling /\
  Reusable.YG0f.in_app (Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)) 4096 /\
  (forall a, Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) <= a <
             Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx) + 4096 ->
     Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a /\ ~ Reusable.YG0d.in_img segs a) /\
  (forall i, 0 <= i < 512 ->
     Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3
       (Reusable.YG0f.shadow_addr (Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)) + i)).
Proof.
  intros cx ly3 S3 W3 mem3 md3 k HJ Hfr.
  pose proof HJ as (HAR & Hly & _).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfr; left; reflexivity).
  assert (Efa : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) =
                Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)).
  { unfold Reusable.YG0f.frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  assert (E64 : Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (Hb0 & Hb1 & Happ).
  destruct (Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as (_ & _ & Hfb & Hfsh).
  rewrite Efa, E64 in *.
  split; [exact Hin|]. split; [reflexivity|]. split; [exact Hb0|]. split; [exact Hb1|]. split; [exact Happ|].
  split.
  - intros a Ha. split; [exact (proj1 (Hfb a Ha))|].
    refine (proj2 (Reusable.YG0d.al_client_img _ _ LAWS ly3 S3 W3 mem3 md3 a HAR _)).
    right. left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin|]. rewrite Efa, E64. exact Ha.
  - intros i Hi. exact (proj1 (Hfsh i ltac:(change (4096 / 8) with 512; lia))).
Qed.

(* The journal's stack facts: the window [c_sp - LLVMF_STK, c_sp) lies above the allocator ceiling and below 2^47,
   and every byte of it is present (astk_ok and the presence clause of ajournal). *)
Lemma w5_stack : forall (cx : ACtlCut.ctlcx) own ly3 S3 W3 mem3 md3 k,
  AJ cx own ly3 S3 W3 mem3 md3 k ->
  lib.Reusable.YM05.alloc_ceiling + 32768 <= ACtlCut.c_sp cx /\ ACtlCut.c_sp cx <= 2 ^ 47 /\
  ACtlCut.c_sp cx mod 16 = 0 /\
  (forall a, ACtlCut.c_sp cx - 32768 <= a < ACtlCut.c_sp cx -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HJ.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & Hstk & _).
  destruct Hstk as (H16 & _ & Hceil & Hlo & Hhi & H47 & _).
  unfold Reusable.YCfn.LLVMF_STK in *.
  split; [lia|]. split; [lia|]. split; [exact H16|]. exact Hwin.
Qed.

(* ctl_rt_C at a successor cut: the journal's AR, and the entry's read-only view (ctl_base's arodata_okS) kept along
   the journal (Reusable.APostBase.arodata_ok_journalP), into a Theorem Labs lane's proved B.ProgWorldCtlRtC.ctl_rt_C_of_AR. *)
Lemma w5_ctlrt : forall (cx : ACtlCut.ctlcx) own ly3 S3 W3 mem3 md3 k,
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  AJ cx own ly3 S3 W3 mem3 md3 k -> B.ACtlRtC.ctl_rt_C B ly3 S3 mem3.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro0 & _) & _).
  apply (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly3 S3 W3 mem3 md3 (proj1 HJ)).
  eapply (Reusable.APostBase.arodata_ok_journalP segs RLO RHI RELRO_IMG B); [exact HJ|].
  apply (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ Hro0); lia.
Qed.

(* bytes outside a run's write set keep their mrd read. *)
Lemma w5_bytes_munch : forall WR (m m' : word -> option byte) a bs,
  lib.Lib.Frame.munch WR m m' ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> lib.Lib.Frame.outside WR (a + i)) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs.
Proof.
  intros WR m m' a bs Hmu Hout (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H2 i Hi). unfold lib.Lib.Mem.mrd. rewrite (Hmu (lib.Lib.Mem.wa (a + Z.of_nat i))); [reflexivity|].
  rewrite lib.Lib.Mem.wa_unsigned by lia. apply Hout. lia.
Qed.

(* The journal across a footprint run whose writes are bytes of the owned frames (in_frames) outside the image. *)
Lemma w5_journal_munch : forall (cx : ACtlCut.ctlcx) own ly3 S3 W3 mem3 md3 k (m' : word -> option byte) md' (lo hi : Z),
  AJ cx own ly3 S3 W3 mem3 md3 k ->
  lib.Lib.Frame.munch [(lo, hi)] mem3 m' -> lib.Lib.Frame.wmono B.Img0.rsegs mem3 m' ->
  (forall x : word, Reusable.YA0n.w_H W3 x = true -> m' x = mem3 x) ->
  Reusable.YK04.same_but_materialized md3 md' ->
  (forall a, lo <= a < hi -> Reusable.YCbq.in_frames ly3 own a /\ ~ Reusable.YG0d.in_img segs a) ->
  AJ cx own ly3 S3 W3 m' md' k.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k m' md' lo hi HJ Hmu Hwm Hhid Hsbm HW.
  apply (Reusable.YCbq.ajournal_exec segs B LAWS w5_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' md'
           (fun a => lo <= a < hi) HJ).
  - intros x Hx. unfold Reusable.YK04.mrestrict. rewrite (Hmu x); [reflexivity|]. cbn. split; [exact Hx | exact I].
  - intros x Hx. unfold Reusable.YK04.mrestrict in *. destruct (Reusable.YA0n.w_H W3 x) eqn:Eh; [exact Hx|].
    destruct (Z.leb lo (bv_unsigned x) && Z.ltb (bv_unsigned x) hi)%bool eqn:E.
    + apply Bool.andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      destruct (HW (bv_unsigned x) ltac:(lia)) as [_ Hni].
      assert (Hv : wview B.Img0.rsegs mem3 x <> None).
      { unfold wview. destruct (mem3 x); [discriminate | exfalso; exact (Hx eq_refl)]. }
      apply Hwm in Hv. unfold wview in Hv. destruct (m' x) as [b|]; [discriminate|].
      exfalso. apply Hv.
      replace (find_segment B.Img0.rsegs (bv_unsigned x) 1) with (@None Segment)
        by (symmetry; exact (Reusable.YCbq.find_segment_none segs _ Hni)).
      reflexivity.
    + rewrite (Hmu x); [exact Hx|]. cbn. split; [|exact I].
      apply Bool.andb_false_iff in E as [E|E]; [apply Z.leb_gt in E | apply Z.ltb_ge in E]; lia.
  - exact Hhid.
  - exact Hsbm.
  - intros a Ha. right. right. right. exact (proj1 (HW a Ha)).
Qed.


(* ACtlCut.ajournal_fp_nil (the donor's A/ACfh.v:29-43) with the sink head changed as well: a journal with no freed
   block reads no sink head (fp_spares [] holds at any head), so it is a journal at any head and any freed-block
   list.  The exit stage takes the walk's journal (generic SK, FP = []) to the post's (the core's head, [sink_token]). *)
Lemma w5_journal_sk : forall (SK1 SK2 : lib.Reusable.YI16.sink_head) STK sp0 FP' ly S W mem md own ly' S' W' mem' md' k,
  Reusable.YCbq.ajournal (SK := SK1) segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  Reusable.YCbq.ajournal (SK := SK2) segs B STK sp0 FP' ly S W mem md own ly' S' W' mem' md' k.
Proof.
  intros SK1 SK2 STK sp0 FP' ly S W mem md own ly' S' W' mem' md' k
    (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
  split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
  split; [eapply Reusable.YCbq.aos_step_mono; [|exact Hio]; intros Ho; exfalso; exact (Reusable.YCbq.sink_closed_nil Ho)|].
  split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
  split; [intros p n i H1 H2 Hi _; apply (F2 p n i H1 H2 Hi); apply lib.Reusable.YI04.inFP_nil|].
  split; [intros a Hi Hns He _; apply (F3 a Hi Hns He); apply (Reusable.YCbq.fp_spares_closed (SK := SK1));
          intros Ho; exact (Reusable.YCbq.sink_closed_nil Ho)|].
  split; [intros cid pos a H1 H2 _; apply (F4 cid pos a H1 H2); apply lib.Reusable.YI04.inFP_nil|].
  split; [intros p n i H1 H2 Hi; exfalso; exact (lib.Reusable.YI04.inFP_nil _ (Hgone p n i H1 H2 Hi))|].
  split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5 | exact HQT].
Qed.

(* A run that leaves every byte of [lo, lo + N) readable (mrd Some) leaves some N bytes there. *)
Lemma w5_bytes_of_mrd : forall (m : word -> option byte) (N : nat) lo,
  0 <= lo -> lo + Z.of_nat N <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat N -> exists b, lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa (lo + i)) = Some b) ->
  exists bs, lib.Lib.Mem.bytes_at B.Img0.rsegs m lo bs /\ length bs = N.
Proof.
  intros m N. induction N as [|N IH]; intros lo H0 H1 Hb.
  - exists []. split; [|reflexivity]. split; [lia|]. split; [cbn [length Z.of_nat]; lia|].
    intros i Hi. cbn [length] in Hi. lia.
  - destruct (Hb 0 ltac:(lia)) as (b & Eb). rewrite Z.add_0_r in Eb.
    destruct (IH (lo + 1) ltac:(lia) ltac:(lia)) as (bs & (_ & _ & Hbs) & Hl).
    { intros i Hi. destruct (Hb (i + 1) ltac:(lia)) as (c & Ec). exists c. rewrite <- Ec. f_equal. f_equal. lia. }
    exists (b :: bs). split; [|cbn [length]; rewrite Hl; reflexivity].
    split; [lia|]. split; [cbn [length]; lia|].
    intros [|i] Hi; cbn [nth_error].
    + rewrite Z.add_0_r. exact Eb.
    + rewrite <- (Hbs i ltac:(cbn [length] in Hi; lia)). f_equal. f_equal. lia.
Qed.


Lemma w5_byte_at : forall (m : word -> option byte) a bs (i : nat) b,
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> nth_error bs i = Some b ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m (a + Z.of_nat i) [b].
Proof.
  intros m a bs i b (H0 & H1 & H2) Hn.
  assert (Hi : (i < length bs)%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
  split; [lia|]. split; [cbn [length]; lia|].
  intros j Hj. cbn [length] in Hj. destruct j as [|j]; [|lia]. cbn [nth_error].
  rewrite <- Hn, <- (H2 i Hi). f_equal. f_equal. lia.
Qed.

Lemma w5_find_byte : forall c l i, ACtlCutP.SFA.find_byte c l = Some i ->
  (i < length l)%nat /\ exists b, nth_error l i = Some b /\ bv_unsigned b = c.
Proof.
  intros c l. induction l as [|b l IH]; intros i H; cbn in H; [discriminate|].
  destruct (bv_unsigned b =? c) eqn:E.
  - injection H as <-. apply Z.eqb_eq in E. split; [cbn; lia|]. exists b. split; [reflexivity | exact E].
  - destruct (ACtlCutP.SFA.find_byte c l) as [j|] eqn:Ej; [|discriminate]. injection H as <-.
    destruct (IH j eq_refl) as (Hj & b' & Hb' & Eb'). split; [cbn; lia|]. exists b'. split; [exact Hb' | exact Eb'].
Qed.



(* The journal's layout keeps the stack bounds of the entry layout. *)
Lemma w5_stk_ly : forall (cx : ACtlCut.ctlcx) own ly3 S3 W3 mem3 md3 k,
  AJ cx own ly3 S3 W3 mem3 md3 k ->
  Reusable.YG0f.ly_stk_lo ly3 + 32768 <= ACtlCut.c_sp cx /\ ACtlCut.c_sp cx <= Reusable.YG0f.ly_stk_hi ly3.
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HJ.
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  destruct Hstk as (_ & _ & _ & Hlo & Hhi & _). rewrite Elo, Ehi. unfold Reusable.YCfn.LLVMF_STK in Hlo. lia.
Qed.

(* find_segment of the image at an address of a segment is that segment (the four spans are disjoint). *)
Lemma w5_find_seg : forall a sg, In sg segs ->
  Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg) -> find_segment segs a 1 = Some sg.
Proof.
  pose proof B.ProgBridge.rsegs_spans as Hs. change B.Img0.rsegs with Reusable.YB1v.tfibsegs in Hs.
  revert Hs. generalize Reusable.YB1v.tfibsegs as l. intros l Hs.
  destruct l as [|s0 [|s1 [|s2 [|s3 [|s4 l]]]]]; cbn [map] in Hs; try discriminate Hs.
  injection Hs as E0 E0' E1 E1' E2 E2' E3 E3'.
  intros a sg Hin Ha. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [find_segment];
    rewrite ?E0, ?E0', ?E1, ?E1', ?E2, ?E2', ?E3, ?E3' in *;
    repeat (match goal with |- context [(?x <=? ?y)%Z] =>
              first [rewrite (proj2 (Z.leb_le x y)) by lia | rewrite (proj2 (Z.leb_gt x y)) by lia] end);
    cbn [andb]; reflexivity.
Qed.

(* rom_view from the cut's ctl_rt_C (its ro_agree conjunct): a present byte of a read-only segment is its rom byte. *)
Lemma w5_rom_view : forall (W : Reusable.YA0n.world segs) ly S (mem : word -> option byte),
  B.ACtlRtC.ctl_rt_C B ly S mem -> Reusable.YG0d.rom_view segs W mem.
Proof.
  intros W ly S mem (_ & _ & _ & Hro) a (sg & Hin & Hw & Ha).
  assert (Himg : 0x10000 <= a < 0x5fe000) by (apply w5_img; exists sg; split; [exact Hin | exact Ha]).
  unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict. cbv beta.
  destruct (Reusable.YA0n.w_H W (Z_to_bv 64 a)); [reflexivity|].
  destruct (mem (Z_to_bv 64 a)) as [b|] eqn:E; [|reflexivity].
  assert (Hra : lib.Lib.Mem.ro_addr B.Img0.rsegs (Z_to_bv 64 a) = true).
  { unfold lib.Lib.Mem.ro_addr. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_small by lia.
    replace (find_segment B.Img0.rsegs a 1) with (Some sg) by (symmetry; exact (w5_find_seg a sg Hin Ha)).
    rewrite Hw. reflexivity. }
  pose proof (Hro _ Hra) as Hr. unfold lib.Lib.Mem.mrd in Hr. rewrite E in Hr.
  exact (f_equal (option_map (fun b0 : byte => bv_unsigned b0)) Hr).
Qed.


Lemma w5_rgv_mod : forall (regs : bvmap 5 word) (r : bv 5) (x y : Z),
  ACtlCut.rgv regs r x -> ACtlCut.rgv regs r y -> x mod 2 ^ 64 = y mod 2 ^ 64.
Proof.
  intros regs r x y Hx Hy. unfold ACtlCut.rgv in *. rewrite Hx in Hy.
  apply (f_equal (@bv_unsigned 64)) in Hy. rewrite !Z_to_bv_unsigned in Hy. unfold bv_wrap in Hy.
  change (bv_modulus 64) with (2 ^ 64) in Hy. exact Hy.
Qed.

(* A runtime callee's munch_vis keeps lib/Lib's mrd reads of visible bytes outside its write set. *)
Lemma w5_bytes_mvis : forall (H : word -> bool) WR (m m' : word -> option byte) a bs,
  (forall x : word, H x = false -> lib.Lib.Frame.outside WR (bv_unsigned x) ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' x = lib.Lib.Mem.mrd B.Img0.rsegs m x) ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> H (Z_to_bv 64 (a + i)) = false /\ lib.Lib.Frame.outside WR (a + i)) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs.
Proof.
  intros H WR m m' a bs Hmv Hv (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H2 i Hi). destruct (Hv (Z.of_nat i) ltac:(lia)) as [Hh Ho].
  apply Hmv; [exact Hh|]. rewrite lib.Lib.Mem.wa_unsigned by lia. exact Ho.
Qed.

Lemma w5_u8 : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof. intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap. reflexivity. Qed.

(* Byte k of the little-endian bytes of a 64-bit value. *)
Lemma w5_le8_byte : forall v (k : nat), 0 <= v < 2 ^ 64 -> (k < 8)%nat ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (lib.Lib.Mem.le8 (Z_to_bv 64 v)) k) =
  Some ((v / 2 ^ (8 * Z.of_nat k)) mod 256).
Proof.
  intros v k Hv Hk.
  assert (Ev : bv_unsigned (Z_to_bv 64 v) = v).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  change (lib.Lib.Mem.le8 (Z_to_bv 64 v)) with (Z_to_le_bytes 8 (bv_unsigned (Z_to_bv 64 v))).
  rewrite Ev.
  destruct k as [|k].
  { cbn [Z_to_le_bytes nth_error option_map]. rewrite w5_u8. change (2 ^ (8 * Z.of_nat 0)) with 1.
    rewrite Z.div_1_r. reflexivity. }
  do 7 (destruct k as [|k]; [cbn [Z_to_le_bytes nth_error option_map]; rewrite w5_u8;
         rewrite ?Z.shiftr_shiftr by lia; rewrite Z.shiftr_div_pow2 by lia; reflexivity|]).
  lia.
Qed.

(* An 8-byte little-endian word of visible bytes reads back through the core's view (rdword over aview). *)
Lemma w5_rdword : forall (W : Reusable.YA0n.world segs) (m : word -> option byte) a v,
  0 <= v < 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> Reusable.YA0n.w_H W (Z_to_bv 64 (a + i)) = false) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a (lib.Lib.Mem.le8 (Z_to_bv 64 v)) ->
  Reusable.YG0d.rdword (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m) a = Some v.
Proof.
  intros W m a v Hv Hh (_ & _ & Hb).
  assert (Hrd : forall i : Z, 0 <= i < 8 ->
            Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + i) = Some ((v / 2 ^ (8 * i)) mod 256)).
  { intros i Hi. rewrite (aview_vis_mrd W m (a + i) (Hh i Hi)).
    replace (Z_to_bv 64 (a + i)) with (lib.Lib.Mem.wa (a + Z.of_nat (Z.to_nat i)))
      by (unfold lib.Lib.Mem.wa; rewrite Z2Nat.id by lia; reflexivity).
    rewrite (Hb (Z.to_nat i)) by (rewrite lib.Lib.Mem.length_le8; lia).
    rewrite (w5_le8_byte v (Z.to_nat i) Hv ltac:(lia)). rewrite Z2Nat.id by lia. reflexivity. }
  pose proof (Hrd 0 ltac:(lia)) as R0. rewrite Z.add_0_r in R0. change (2 ^ (8 * 0)) with 1 in R0.
  rewrite Z.div_1_r in R0.
  pose proof (Hrd 1 ltac:(lia)) as R1. change (2 ^ (8 * 1)) with 256 in R1.
  pose proof (Hrd 2 ltac:(lia)) as R2. change (2 ^ (8 * 2)) with 65536 in R2.
  pose proof (Hrd 3 ltac:(lia)) as R3. change (2 ^ (8 * 3)) with 16777216 in R3.
  pose proof (Hrd 4 ltac:(lia)) as R4. change (2 ^ (8 * 4)) with 4294967296 in R4.
  pose proof (Hrd 5 ltac:(lia)) as R5. change (2 ^ (8 * 5)) with 1099511627776 in R5.
  pose proof (Hrd 6 ltac:(lia)) as R6. change (2 ^ (8 * 6)) with 281474976710656 in R6.
  pose proof (Hrd 7 ltac:(lia)) as R7. change (2 ^ (8 * 7)) with 72057594037927936 in R7.
  unfold Reusable.YG0d.rdword. rewrite R0, R1, R2, R3, R4, R5, R6, R7. cbv beta iota. f_equal.
  assert (D0 : v = v mod 256 + 256 * (v / 256)) by (pose proof (Z.div_mod v 256); lia).
  assert (Dk : forall c, 0 < c -> v / c = (v / c) mod 256 + 256 * (v / (c * 256))).
  { intros c Hc. rewrite <- Z.div_div by lia. pose proof (Z.div_mod (v / c) 256). lia. }
  pose proof (Dk 256 ltac:(lia)) as D1. pose proof (Dk 65536 ltac:(lia)) as D2.
  pose proof (Dk 16777216 ltac:(lia)) as D3. pose proof (Dk 4294967296 ltac:(lia)) as D4.
  pose proof (Dk 1099511627776 ltac:(lia)) as D5. pose proof (Dk 281474976710656 ltac:(lia)) as D6.
  pose proof (Dk 72057594037927936 ltac:(lia)) as D7.
  cbn [Z.mul] in D1, D2, D3, D4, D5, D6, D7.
  assert (D8 : v / 18446744073709551616 = 0) by (apply Z.div_small; lia).
  lia.
Qed.

(* A view-form post (equal views at visible addresses) keeps lib/Lib's mrd reads there. *)
Lemma w5_bytes_aview : forall (W : Reusable.YA0n.world segs) (m m' : word -> option byte) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) ->
     Reusable.YA0n.w_H W (Z_to_bv 64 (a + i)) = false /\
     Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m' (a + i) = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + i)) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs.
Proof.
  intros W m m' a bs Hv (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H2 i Hi). destruct (Hv (Z.of_nat i) ltac:(lia)) as [Hh E].
  rewrite (aview_vis_mrd W m' _ Hh), (aview_vis_mrd W m _ Hh) in E. unfold lib.Lib.Mem.wa.
  destruct (lib.Lib.Mem.mrd B.Img0.rsegs m' (Z_to_bv 64 (a + Z.of_nat i))) as [b'|],
           (lib.Lib.Mem.mrd B.Img0.rsegs m (Z_to_bv 64 (a + Z.of_nat i))) as [b|]; cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82eac (0x82eac, own6, k <= 526) --S_X1--> B82ecc | Jrel.
   S_X1 (Seg/X12.v seg_X1 :858): `ld a0,176(s1); lbu a0,20(a0); beqz a0,0x82ed0`.  Byte 20 of the identity record
   (at [A+176] = fr + 2688, so the byte at fr + 2708) = 0: the shadow-fill block and on to Jrel.  Otherwise
   a0 = fr + 2691, a2 = 17, a1 = 0 and the memchr trampoline @0x82ec8, returning at 0x82ecc = B82ecc. *)
Lemma seg_X1 : forall POST,
  ctl_from POST C_B82ecc ->
  ctl_from POST C_Jrel ->
  ctl_from POST C_B82eac.
Proof.
  intros POST Hcc Hjr cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  unfold ACtlCutP.C_B82eac in HJ, Hfr, HFA, Hk, HBODY |- *.
  cbn [ACtlCut.cut_own ACtlCut.cut_kmax ACtlCut.cut_body ACtlCut.cut_pc] in HJ, Hfr, HFA, Hk, HBODY |- *.
  pose proof (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)) as Efr.
  destruct (w5_frame cx ly3 S3 W3 mem3 md3 k HJ Hfr) as (Hin & Efa & Hf0 & Hf1 & Happ & Hfb & Hfsh).
  rewrite <- Efr in Efa, Hf0, Hf1, Happ, Hfb, Hfsh.
  destruct (w5_stack cx _ ly3 S3 W3 mem3 md3 k HJ) as (Hs0 & Hs47 & Hs16 & Hwin).
  destruct (w5_stk_ly cx _ ly3 S3 W3 mem3 md3 k HJ) as (Hly0 & Hly1).
  pose proof (lib.Reusable.YM05.alloc_ceiling_val (RunCeil := rc)) as [[Hc0 Hc1] _].
  destruct HBODY as (Hperm & HFRAC & Hn & HOUR & (A1 & HA1 & Q176) & (nm & Hnm & Hlen & Hfind) & Hadd).
  pose proof HFRAC as (A & sp & Esp & Hsp16 & EspZ & Etp & E8 & E9 & E3 & E19 & E26 & Hfr32 & HA32 & HAS & HspA &
                     HfrA & HA448 & HSsp & HSapp & Q336 & Q48 & Q40 & Qhdr & Q16 & Hsh & Hsav & Qtr).
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Happ.
  unfold ACtlCutP.q64 in Q176. pose proof (lib.Lib.Mem.bytes_at_bound _ _ _ _ Q176) as HQb.
  rewrite lib.Lib.Mem.length_le8 in HQb. change (Z.of_nat 8) with 8 in HQb.
  assert (EA1 : A1 = A).
  { pose proof (w5_rgv_mod regs3 _ A1 A HA1 E9) as HM. destruct HQb as [HQ1 HQ2]. lia. } subst A1.
  assert (ESh : ACtlCutP.Sfr fr = Reusable.YG0f.shadow_addr fr).
  { unfold ACtlCutP.Sfr, ACtlCutP.ART.shadow_addr, Reusable.YG0f.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.SHADOW_OFF.
    lia. }
  assert (HShv : ACtlCutP.Sfr fr = fr / 8 + 2147450880).
  { unfold ACtlCutP.Sfr, ACtlCutP.ART.shadow_addr, B.AsanRT.ASAN_K. lia. }
  assert (Hshp : forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 ->
                 Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
  { intros a Ha. pose proof (Hfsh (a - ACtlCutP.Sfr fr) ltac:(lia)) as Hp. rewrite <- ESh in Hp.
    replace (ACtlCutP.Sfr fr + (a - ACtlCutP.Sfr fr)) with a in Hp by lia. exact Hp. }
  destruct (nth_error nm 20) as [b20|] eqn:Eb20; [| apply nth_error_None in Eb20; lia].
  pose proof (w5_byte_at _ _ _ _ _ Hnm Eb20) as Hb20.
  replace (fr + 2688 + Z.of_nat 20) with (fr + 2708) in Hb20 by lia.
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  destruct (Z.eq_dec (bv_unsigned b20) 0) as [Hz|Hnz].
  - (* byte 20 = 0: 0x82eac -> 0x82ed0 -> the shadow-fill block -> Jrel *)
    eapply (w5_lift W3 regs3 mem3 md3 0x82eac RNG).
    { eapply (Lib.ExecF.evtF_cut B.Img0.rsegs RNG).
      { eapply (X12F.x12_b_evt_F RNG).
        - exact E9.
        - exact Q176.
        - exact Hb20.
        - exact Hz.
        - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
          intros a Ha. exact (proj1 (Hwin a ltac:(lia))).
        - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
          intros a Ha. exact (proj1 (proj1 (Hfb a ltac:(lia)))). }
      intros ms1 E1. cbv beta in E1. subst ms1.
      unfold ACtlCutP.q64 in Q48, Q40.
      eapply (X12F.x12_store_evt_F RNG).
      - exact E9.
      - exact E19.
      - split; [lia|]. split; [lia|]. intros a Ha. destruct (Hshp a ltac:(lia)) as (_ & b & Hb).
        unfold wview, lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. split; [discriminate | exists b; reflexivity].
      - exact Q48.
      - exact Q40.
      - lia.
      - lia.
      - lia.
      - lia.
      - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
        intros a Ha. exact (proj1 (Hshp a ltac:(lia))).
      - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
        intros a Ha. exact (proj1 (Hwin a ltac:(lia))). }
    { apply B.ProgBridge.fp_avoids_RNG_W. }
    intros ms' md' (m' & -> & Hmu & Hwm & Hstk') Hhid Hsbm.
    assert (HJ' : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
    { apply (w5_journal_munch cx _ ly3 S3 W3 mem3 md3 k m' md' _ _ HJ Hmu Hwm Hhid Hsbm).
      intros a Ha. split.
      - exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. right.
        unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efa, <- ESh.
        change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512. lia.
      - intros Hi. apply w5_img in Hi. lia. }
    match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ =>
      apply (Hjr cx idx fr k ly3 S3 W3 R m' md' HB HJ' Hfr HFA Hk) end.
    + unfold ACtlCutP.C_Jrel. cbn [ACtlCut.cut_body].
      split; [exact Hperm|]. split; [|split; reflexivity].
      exists A, sp.
      split; [exact Esp|]. split; [exact Hsp16|]. split; [exact EspZ|]. split; [exact Etp|].
      split; [exact E8|]. split; [exact E9|]. split; [exact E3|]. split; [exact E19|]. split; [exact E26|].
      do 8 (split; [assumption|]).
      unfold ACtlCutP.q64 in *.
      split.
      { apply (w5_bytes_munch _ mem3 m' _ _ Hmu); [|exact Q336].
        intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. cbn. split; [lia | exact I]. }
      split.
      { apply (w5_bytes_munch _ mem3 m' _ _ Hmu); [|exact Qhdr].
        intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. cbn. split; [lia | exact I]. }
      split.
      { apply (w5_bytes_munch _ mem3 m' _ _ Hmu); [|exact Q16].
        intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. cbn. split; [lia | exact I]. }
      split.
      { destruct Hstk' as (_ & _ & Hstk').
        destruct (w5_bytes_of_mrd m' 392 (ACtlCutP.Sfr fr) ltac:(lia) ltac:(lia)) as (sh & Hsh' & Hl).
        { intros i Hi. exact (proj2 (Hstk' (ACtlCutP.Sfr fr + i) ltac:(lia))). }
        exists sh. split; [exact Hsh'|]. rewrite Hl. reflexivity. }
      split.
      { apply (w5_bytes_munch _ mem3 m' _ _ Hmu); [|exact Hsav].
        intros i Hi. unfold ACtlCutP.saved_bytes in Hi. rewrite !length_app, !lib.Lib.Mem.length_le8 in Hi.
        cbn. split; [lia | exact I]. }
      { apply (w5_bytes_munch _ mem3 m' _ _ Hmu); [|exact Qtr].
        intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. cbn. split; [lia | exact I]. }
    + exact (w5_ctlrt cx _ _ _ _ _ _ _ HB HJ').
  - (* byte 20 <> 0: 0x82eac -> the memchr trampoline 0x42ab0 with ra = 0x82ecc, then the call *)
    eapply (w5_lift W3 regs3 mem3 md3 0x82eac RNG).
    { eapply (X12F.x12_a_pre_F RNG).
      - exact E9.
      - exact Q176.
      - lia.
      - match goal with |- _ + ?F <= ?E => change F with 3136; change E with 140737488355328 end.
        unfold B.AsanRT.APPMEM_END in HSapp. lia.
      - exact Hb20.
      - exact Hnz.
      - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
        intros a Ha. exact (proj1 (Hwin a ltac:(lia))).
      - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
        intros a Ha. exact (proj1 (proj1 (Hfb a ltac:(lia)))). }
    { apply B.ProgBridge.fp_avoids_RNG_W. }
    intros ms' md' Hpost Hhid Hsbm. cbv beta in Hpost. subst ms'.
    assert (HJm : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md' k).
    { apply (w5_journal_munch cx _ ly3 S3 W3 mem3 md3 k mem3 md' 0 0 HJ (lib.Lib.Frame.munch_refl _ _)
               (lib.Lib.Frame.wmono_refl _ _) Hhid Hsbm).
      intros a Ha. lia. }
    match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ => set (R1 := R) end.
    assert (EspR : Reusable.YG0d.spZ R1 = sp) by exact EspZ.
    change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x42ab0 R1 mem3 md') (POST cx)).
    rewrite <- HMEMCHR_ENTRY.
    pose proof HB as ((HAFN & _) & _). pose proof HAFN as (_ & _ & _ & Hgp & _).
    eapply Reusable.YA0n.SRr_bind.
    { apply (AMEMCHR ly3 S3 W3 R1 mem3 md' (fr + 2691) 0 17).
      - split; [exact (proj1 HJm)|]. split; [apply lib.Reusable.YK0s.ret_ok_even; reflexivity|].
        rewrite EspR. split; [exact Hsp16|]. split; [unfold Reusable.YG0d.ESTACK; lia|]. split; [lia|].
        split; [intros a Ha; apply Hwin; unfold Reusable.YG0d.ESTACK in Ha; lia|].
        split; [rewrite <- Hgp; exact E3 | exact Etp].
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - lia.
      - intros a Ha. split.
        + destruct (proj1 (Hfb a ltac:(lia))) as (Hh & b & Hb). rewrite (aview_vis_mrd W3 _ _ Hh).
          unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. discriminate.
        + rewrite EspR. unfold Reusable.YG0d.ESTACK. lia.
      - unfold Reusable.YG0d.amem_range, Reusable.YG0f.kLowMemEnd, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.kHighMemEnd.
        lia.
      - destruct Hadd as (_ & _ & _ & Hab). intros x Hx.
        destruct (Hab (x - (fr + 2691)) ltac:(lia)) as (_ & b & Hb & Hok).
        replace (fr + 2691 + (x - (fr + 2691))) with x in Hb, Hok by lia.
        assert (Ex : ACtlCutP.ART.shadow_addr x = Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF x).
        { unfold ACtlCutP.ART.shadow_addr, Reusable.YG0v.shadow_of_addr, B.AsanRT.ASAN_K, Reusable.YG0f.SHADOW_OFF.
          lia. }
        assert (Hx8 : ACtlCutP.Sfr fr + 336 <= Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF x <= ACtlCutP.Sfr fr + 338).
        { rewrite <- Ex. unfold ACtlCutP.ART.shadow_addr, B.AsanRT.ASAN_K. lia. }
        exists (bv_unsigned b). split.
        + destruct (Hshp (Reusable.YG0v.shadow_of_addr Reusable.YG0f.SHADOW_OFF x) ltac:(lia)) as (Hh & _). rewrite (aview_vis_mrd W3 _ _ Hh), <- Ex. unfold lib.Lib.Mem.wa in Hb. rewrite Hb. reflexivity.
        + unfold Reusable.YG0v.saddr_ok. unfold ACtlCutP.ART.shadow_ok in Hok.
          unfold bv_signed, bv_swrap, bv_half_modulus, bv_wrap in Hok. change (bv_modulus 8) with 256 in Hok.
          pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr. lia.
      - intros _ s Hs. destruct (Hshp s) as (Hh & b & Hb).
        { unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF in Hs. lia. }
        rewrite (aview_vis_mrd W3 _ _ Hh). unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. discriminate.
      - exact (w5_rom_view W3 ly3 S3 mem3 HRT). }
    cbv beta. intros W2 c2 _ (-> & regs' & mem' & md'' & -> & HAR' & Hpres & Hsbm' & (kk & Hfb1 & Ha0) & Hview & Hapres).
    rewrite EspR in Hview.
    assert (HJ' : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem' md'' k).
    { pose proof HJm as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
      apply (Reusable.StackFreeJournal.ajournal_after_write_win segs B LAWS w5_segs_low
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem' md'' (fun a => sp - 4096 <= a < sp) S3 (ACtlCut.own6 cx) HJm).
      - intros a Ha Hn'. apply Hview; [exact Ha|]. unfold Reusable.YG0d.ESTACK. exact Hn'.
      - intros a _ Hp. exact (Hapres a Hp).
      - exact Hsbm'.
      - intros a Ha. left. left. unfold Reusable.YCfn.LLVMF_STK. lia.
      - exact HAR'.
      - reflexivity.
      - reflexivity.
      - lia.
      - exact Hfrs.
      - exact HQT. }
    (* kk < 17: the 17 model_name bytes hold a 0 (the body's find_byte) *)
    destruct Hfb1 as (Hk0 & Hne & Hat).
    destruct (ACtlCutP.SFA.find_byte 0 (firstn 17 (skipn 3 nm))) as [j|] eqn:Ej; [|exfalso; exact (Hfind eq_refl)].
    destruct (w5_find_byte _ _ _ Ej) as (Hj & bj & Hbj & Ebj).
    rewrite length_firstn, length_skipn, Hlen in Hj. cbn in Hj.
    rewrite nth_error_firstn in Hbj. destruct (Nat.ltb j 17) eqn:Ejl; [|discriminate].
    rewrite nth_error_skipn in Hbj.
    assert (Hkk : kk < 17).
    { destruct (Z_lt_le_dec kk 17) as [h|h]; [exact h|]. exfalso.
      destruct (Hne (Z.of_nat j) ltac:(lia)) as (b & Hb & Hb0).
      destruct (proj1 (Hfb (fr + 2691 + Z.of_nat j) ltac:(lia))) as (Hh & _).
      rewrite (aview_vis_mrd W3 _ _ Hh) in Hb.
      destruct Hnm as (_ & _ & Hnm).
      pose proof (Hnm (3 + j)%nat ltac:(lia)) as Hm. rewrite Hbj in Hm.
      replace (fr + 2688 + Z.of_nat (3 + j)) with (fr + 2691 + Z.of_nat j) in Hm by lia.
      replace (lib.Lib.Mem.mrd B.Img0.rsegs mem3 (Z_to_bv 64 (fr + 2691 + Z.of_nat j))) with (Some bj) in Hb
        by (symmetry; exact Hm).
      cbn in Hb. injection Hb as Hb. lia. }
    rewrite (proj2 (Z.ltb_lt kk 17) Hkk) in Ha0.
    apply (Hcc cx idx fr k ly3 S3 W3 regs' mem' md'' HB HJ' Hfr HFA Hk).
    + unfold ACtlCutP.C_B82ecc. cbn [ACtlCut.cut_body].
      assert (Hcs : forall r, r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 19 \/ r = 26 ->
                    Reusable.YG0d.acallee_saved r) by (intros r Hr; unfold Reusable.YG0d.acallee_saved; lia).
      assert (P2 : lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs3 2) by exact (Hpres 2 (Hcs 2 ltac:(lia))).
      assert (P3 : lib.Reusable.YK11.getr regs' 3 = lib.Reusable.YK11.getr regs3 3) by exact (Hpres 3 (Hcs 3 ltac:(lia))).
      assert (P4 : lib.Reusable.YK11.getr regs' 4 = lib.Reusable.YK11.getr regs3 4) by exact (Hpres 4 (Hcs 4 ltac:(lia))).
      assert (P8 : lib.Reusable.YK11.getr regs' 8 = lib.Reusable.YK11.getr regs3 8) by exact (Hpres 8 (Hcs 8 ltac:(lia))).
      assert (P9 : lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs3 9) by exact (Hpres 9 (Hcs 9 ltac:(lia))).
      assert (P19 : lib.Reusable.YK11.getr regs' 19 = lib.Reusable.YK11.getr regs3 19) by exact (Hpres 19 (Hcs 19 ltac:(lia))).
      assert (P26 : lib.Reusable.YK11.getr regs' 26 = lib.Reusable.YK11.getr regs3 26) by exact (Hpres 26 (Hcs 26 ltac:(lia))).
      assert (Hkeep : forall (a : Z) (bs : list byte), (forall i : Z, 0 <= i < Z.of_nat (length bs) ->
                         (0 <= a + i < 2 ^ 64) /\ (~ (sp - 4096 <= a + i < sp)) /\
                         (Reusable.YA0n.w_H W3 (Z_to_bv 64 (a + i)) = false)) ->
                      lib.Lib.Mem.bytes_at B.Img0.rsegs mem3 a bs -> lib.Lib.Mem.bytes_at B.Img0.rsegs mem' a bs).
      { destruct (ctl_post_memchr W3 mem3 mem' sp) as [Hmv _].
        { split; [|exact Hapres]. intros a Ha Hout. apply Hview; [exact Ha|]. cbn in Hout. exact (proj1 Hout). }
        intros a bs Hv. apply (w5_bytes_mvis (Reusable.YA0n.w_H W3) _ mem3 mem' a bs Hmv). intros i Hi.
        destruct (Hv i Hi) as (H0 & H1 & H2). split; [exact H2|]. cbn.
        split; [unfold Reusable.YG0d.ESTACK; exact H1 | exact I]. }
      split; [exact Hperm|].
      split.
      { exists A, sp.
        split; [rewrite P2; exact Esp|]. split; [exact Hsp16|].
        split; [unfold Reusable.YG0d.spZ; rewrite P2; exact EspZ|].
        split; [rewrite P4; exact Etp|]. split; [unfold ACtlCut.rgv; rewrite P8; exact E8|].
        split; [unfold ACtlCut.rgv; rewrite P9; exact E9|]. split; [rewrite P3; exact E3|].
        split; [unfold ACtlCut.rgv; rewrite P19; exact E19|]. split; [unfold ACtlCut.rgv; rewrite P26; exact E26|].
        do 8 (split; [assumption|]).
        unfold ACtlCutP.q64 in *.
        split.
        { apply Hkeep; [|exact Q336]. intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. simpl in Hi.
          split; [lia|]. split; [lia|]. match goal with |- _ (Z_to_bv 64 ?a) = false => exact (proj1 (Hwin a ltac:(lia))) end. }
        split.
        { apply Hkeep; [|exact Q48]. intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. simpl in Hi.
          split; [lia|]. split; [lia|]. match goal with |- _ (Z_to_bv 64 ?a) = false => exact (proj1 (Hwin a ltac:(lia))) end. }
        split.
        { apply Hkeep; [|exact Q40]. intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. simpl in Hi.
          split; [lia|]. split; [lia|]. match goal with |- _ (Z_to_bv 64 ?a) = false => exact (proj1 (Hwin a ltac:(lia))) end. }
        split.
        { apply Hkeep; [|exact Qhdr]. intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. simpl in Hi.
          split; [lia|]. split; [lia|]. match goal with |- _ (Z_to_bv 64 ?a) = false => exact (proj1 (proj1 (Hfb a ltac:(lia)))) end. }
        split.
        { apply Hkeep; [|exact Q16]. intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. simpl in Hi.
          split; [lia|]. split; [lia|]. match goal with |- _ (Z_to_bv 64 ?a) = false => exact (proj1 (proj1 (Hfb a ltac:(lia)))) end. }
        split.
        { destruct Hsh as (sh & Hsh & Hl). exists sh. split; [|exact Hl].
          apply Hkeep; [|exact Hsh]. intros i Hi. rewrite Hl in Hi.
          change (Z.of_nat (Z.to_nat ACtlCutP.FRAME_SHADOW)) with 392 in Hi.
          split; [lia|]. split; [lia|]. match goal with |- _ (Z_to_bv 64 ?a) = false => exact (proj1 (Hshp a ltac:(lia))) end. }
        split.
        { apply Hkeep; [|exact Hsav]. intros i Hi. unfold ACtlCutP.saved_bytes in Hi.
          rewrite !length_app, !lib.Lib.Mem.length_le8 in Hi. simpl in Hi.
          split; [lia|]. split; [lia|]. match goal with |- _ (Z_to_bv 64 ?a) = false => exact (proj1 (Hwin a ltac:(lia))) end. }
        { apply Hkeep; [|exact Qtr]. intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. simpl in Hi.
          split; [lia|]. split; [lia|]. match goal with |- _ (Z_to_bv 64 ?a) = false => exact (proj1 (proj1 (Hfb a ltac:(lia)))) end. } }
      split; [exact Hn|].
      split.
      { unfold ACtlCutP.OURb in *. apply Hkeep; [|exact HOUR]. intros i Hi.
        rewrite ACtlCutP.SM.OUR_length in Hi. simpl in Hi.
        split; [lia|]. split; [lia|]. match goal with |- _ (Z_to_bv 64 ?a) = false => exact (proj1 (proj1 (Hfb a ltac:(lia)))) end. }
      { exists (fr + 2691 + kk). split; [exact Ha0|]. lia. }
    + exact (w5_ctlrt cx _ _ _ _ _ _ _ HB HJ').
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82ecc (0x82ecc, own6, k <= 526) --S_X2--> Jrel.
   S_X2 (Seg/X12.v seg_X2 :821): `beqz a0,0x82fa4` (the abort pair __asan_handle_no_return; abort) NOT taken, then
   the shared shadow-fill block 0x82ed0-0x82f2c to the release join. *)
Lemma seg_X2 : forall POST,
  ctl_from POST C_Jrel ->
  ctl_from POST C_B82ecc.
Proof.
  intros POST Hjr cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  unfold ACtlCutP.C_B82ecc in HJ, Hfr, HFA, Hk, HBODY |- *.
  cbn [ACtlCut.cut_own ACtlCut.cut_kmax ACtlCut.cut_body ACtlCut.cut_pc] in HJ, Hfr, HFA, Hk, HBODY |- *.
  pose proof (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)) as Efr.
  destruct (w5_frame cx ly3 S3 W3 mem3 md3 k HJ Hfr) as (Hin & Efa & Hf0 & Hf1 & Happ & Hfb & Hfsh).
  rewrite <- Efr in Efa, Hf0, Hf1, Happ, Hfb, Hfsh.
  destruct (w5_stack cx _ ly3 S3 W3 mem3 md3 k HJ) as (Hs0 & Hs47 & Hs16 & Hwin).
  pose proof (lib.Reusable.YM05.alloc_ceiling_val (RunCeil := rc)) as [[Hc0 Hc1] _].
  destruct HBODY as (Hperm & HFRAC & Hn & HOUR & (q & Hq & Hq64)).
  pose proof HFRAC as (A & sp & Esp & Hsp16 & EspZ & Etp & E8 & E9 & E3 & E19 & E26 & Hfr32 & HA32 & HAS & HspA &
                     HfrA & HA448 & HSsp & HSapp & Q336 & Q48 & Q40 & Qhdr & Q16 & Hsh & Hsav & Qtr).
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Happ.
  assert (ESh : ACtlCutP.Sfr fr = Reusable.YG0f.shadow_addr fr).
  { unfold ACtlCutP.Sfr, ACtlCutP.ART.shadow_addr, Reusable.YG0f.shadow_addr, B.AsanRT.ASAN_K, Reusable.YG0f.SHADOW_OFF.
    lia. }
  assert (HShv : ACtlCutP.Sfr fr = fr / 8 + 2147450880).
  { unfold ACtlCutP.Sfr, ACtlCutP.ART.shadow_addr, B.AsanRT.ASAN_K. lia. }
  assert (Hshp : forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 ->
                 Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
  { intros a Ha. pose proof (Hfsh (a - ACtlCutP.Sfr fr) ltac:(lia)) as Hp. rewrite <- ESh in Hp.
    replace (ACtlCutP.Sfr fr + (a - ACtlCutP.Sfr fr)) with a in Hp by lia. exact Hp. }
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  eapply (w5_lift W3 regs3 mem3 md3 0x82ecc RNG).
  { eapply (Lib.ExecF.evtF_cut B.Img0.rsegs RNG).
    { eapply (X12F.x12_x2_evt_F RNG); [exact Hq | lia]. }
    intros ms1 E1. cbv beta in E1. subst ms1.
    unfold ACtlCutP.q64 in Q48, Q40.
    eapply (X12F.x12_store_evt_F RNG).
    - exact E9.
    - exact E19.
    - split; [lia|]. split; [lia|]. intros a Ha. destruct (Hshp a ltac:(lia)) as (_ & b & Hb).
      unfold wview, lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Hb. split; [discriminate | exists b; reflexivity].
    - exact Q48.
    - exact Q40.
    - lia.
    - lia.
    - lia.
    - lia.
    - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (Hshp a ltac:(lia))).
    - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (Hwin a ltac:(lia))). }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' (m' & -> & Hmu & Hwm & Hstk') Hhid Hsbm.
  assert (HJ' : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { apply (w5_journal_munch cx _ ly3 S3 W3 mem3 md3 k m' md' _ _ HJ Hmu Hwm Hhid Hsbm).
    intros a Ha. split.
    - exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. right.
      unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efa, <- ESh. change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
      lia.
    - intros Hi. apply w5_img in Hi. lia. }
  match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ =>
    apply (Hjr cx idx fr k ly3 S3 W3 R m' md' HB HJ' Hfr HFA Hk) end.
  - unfold ACtlCutP.C_Jrel. cbn [ACtlCut.cut_body].
    split; [exact Hperm|]. split; [|split; reflexivity].
    exists A, sp.
    split; [exact Esp|]. split; [exact Hsp16|]. split; [exact EspZ|]. split; [exact Etp|].
    split; [exact E8|]. split; [exact E9|]. split; [exact E3|]. split; [exact E19|]. split; [exact E26|].
    do 8 (split; [assumption|]).
    unfold ACtlCutP.q64 in *.
    split.
    { apply (w5_bytes_munch _ mem3 m' _ _ Hmu); [|exact Q336].
      intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. cbn. split; [lia | exact I]. }
    split.
    { apply (w5_bytes_munch _ mem3 m' _ _ Hmu); [|exact Qhdr].
      intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. cbn. split; [lia | exact I]. }
    split.
    { apply (w5_bytes_munch _ mem3 m' _ _ Hmu); [|exact Q16].
      intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. cbn. split; [lia | exact I]. }
    split.
    { destruct Hstk' as (_ & _ & Hstk').
      destruct (w5_bytes_of_mrd m' 392 (ACtlCutP.Sfr fr) ltac:(lia) ltac:(lia)) as (sh & Hsh' & Hl).
      { intros i Hi. exact (proj2 (Hstk' (ACtlCutP.Sfr fr + i) ltac:(lia))). }
      exists sh. split; [exact Hsh'|]. rewrite Hl. reflexivity. }
    split.
    { apply (w5_bytes_munch _ mem3 m' _ _ Hmu); [|exact Hsav].
      intros i Hi. unfold ACtlCutP.saved_bytes in Hi. rewrite !length_app, !lib.Lib.Mem.length_le8 in Hi.
      cbn. split; [lia | exact I]. }
    { apply (w5_bytes_munch _ mem3 m' _ _ Hmu); [|exact Qtr].
      intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. cbn. split; [lia | exact I]. }
  - exact (w5_ctlrt cx _ _ _ _ _ _ _ HB HJ').
Qed.

(* ---------------------------------------------------------------------------------------------------------
   Jrel (0x82f2c, own6, k <= 526) --S_Jrel--> B82f48.
   S_Jrel (Seg/YTail.v seg_Jrel :1406): `beqz s8,0x82f58` at 0x82f38 splits the release.  The shell passes sel = fr
   and C_Jrel pins rgv regs 24 sel, so s8 = fr; fr <> 0 by (G1) (fr = frame_addr (c_ly cx) 6 (c_fpos cx) and AR's
   frame law puts the class-6 frame in the fake stack above 4096).  So only the fake-frame arm runs: a0 = fr,
   a1 = 3136 = FRAME_BYTES, to the call at 0x82f48.  The sel = 0 exit to B82f58 (no record) is not taken. *)
Lemma seg_Jrel : forall POST,
  ctl_from POST C_B82f48 ->
  ctl_from POST C_Jrel.
Proof.
  intros POST H48 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  unfold ACtlCutP.C_Jrel in HJ, Hfr, HFA, Hk, HBODY |- *.
  cbn [ACtlCut.cut_own ACtlCut.cut_kmax ACtlCut.cut_body ACtlCut.cut_pc] in HJ, Hfr, HFA, Hk, HBODY |- *.
  pose proof (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)) as Efr.
  destruct (w5_frame cx ly3 S3 W3 mem3 md3 k HJ Hfr) as (Hin & Efa & Hf0 & Hf1 & Happ & Hfb & Hfsh).
  rewrite <- Efr in Efa, Hf0, Hf1, Happ, Hfb, Hfsh.
  destruct (w5_stack cx _ ly3 S3 W3 mem3 md3 k HJ) as (Hs0 & Hs47 & Hs16 & Hwin).
  pose proof (lib.Reusable.YM05.alloc_ceiling_val (RunCeil := rc)) as [[Hc0 Hc1] _].
  destruct HBODY as (Hperm & HFH & H24 & H25).
  pose proof HFH as (A & sp & Esp & Hsp16 & EspZ & Etp & E8 & E9 & E3 & E19 & E26 & Hfr32 & HA32 & HAS & HspA &
                     HfrA & HA448 & HSsp & HSapp & Q336 & Qhdr & Q16 & Hsh & Hsav & Qtr).
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  eapply (w5_lift W3 regs3 mem3 md3 0x82f2c (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { eapply (YTailF.jrel_evt_side_F (fx := FX5) (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
    - exact H24.
    - exact H25.
    - lia.
    - unfold ACtlCutP.q64 in Qhdr. split; [split|].
      + cbn. split; exact I.
      + cbn [lib.Lib.Cells.cells_bytes lib.Lib.Cells.cbytes]. rewrite app_nil_r. exact Qhdr.
      + cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize]. split; [lia|]. split; [lia|].
        intros i Hi. destruct (proj1 (Hfb (fr + i) ltac:(lia))) as (_ & b & Hb).
        unfold wview, lib.Lib.Mem.wa. rewrite Hb. discriminate.
    - unfold lib.Lib.Frame.stk. refine (conj (Z.le_refl 0) (conj (_ : 0 <= 2 ^ 64) _)); [lia|]. intros a Ha. lia.
    - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (proj1 (Hfb a ltac:(lia)))). }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' (m' & -> & Hmu & Hwm & Hhdr & _) Hhid Hsbm.
  assert (HJ' : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 m' md' k).
  { apply (w5_journal_munch cx _ ly3 S3 W3 mem3 md3 k m' md' fr (fr + 8) HJ Hmu Hwm Hhid Hsbm).
    intros a Ha. split; [|exact (proj2 (Hfb a ltac:(lia)))].
    exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. left.
    unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efa. change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia. }
  match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ =>
    apply (H48 cx idx fr k ly3 S3 W3 R m' md' HB HJ' Hfr HFA Hk) end.
  - unfold ACtlCutP.C_B82f48. cbn [ACtlCut.cut_body].
    split; [exact Hperm|]. split; [|split; [reflexivity|split; reflexivity]].
    exists A, sp.
    assert (Hsh' : forall i, 0 <= i -> lib.Lib.Frame.outside [(fr, fr + 8)] (A + i)).
    { intros i Hi. cbn. split; [lia | exact I]. }
    split; [exact Esp|]. split; [exact Hsp16|]. split; [exact EspZ|]. split; [exact Etp|].
    split; [exact E8|]. split; [exact E9|]. split; [exact E3|]. split; [exact E19|]. split; [exact E26|].
    do 8 (split; [assumption|]).
    split.
    { unfold ACtlCutP.q64 in *. apply (w5_bytes_munch _ mem3 m' _ _ Hmu); [|exact Q336].
      intros i Hi. cbn. split; [lia | exact I]. }
    split; [unfold ACtlCutP.q64; exact Hhdr|].
    split.
    { unfold ACtlCutP.q64 in *. apply (w5_bytes_munch _ mem3 m' _ _ Hmu); [|exact Q16].
      intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. cbn. split; [lia | exact I]. }
    split.
    { destruct Hsh as (sh & Hsh & Hlen). exists sh. split; [|exact Hlen].
      apply (w5_bytes_munch _ mem3 m' _ _ Hmu); [|exact Hsh].
      intros i Hi. rewrite Hlen in Hi. unfold ACtlCutP.FRAME_SHADOW, ACtlCutP.FRAME_BYTES in Hi.
      unfold ACtlCutP.Sfr, ACtlCutP.ART.shadow_addr, ACtlCutP.ART.ASAN_K, B.AsanRT.ASAN_K.
      unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL in Happ.
      cbn. split; [|exact I]. lia. }
    split.
    { apply (w5_bytes_munch _ mem3 m' _ _ Hmu); [|exact Hsav].
      intros i Hi. unfold ACtlCutP.saved_bytes in Hi. rewrite !length_app, !lib.Lib.Mem.length_le8 in Hi.
      cbn. split; [lia | exact I]. }
    { unfold ACtlCutP.q64 in *. apply (w5_bytes_munch _ mem3 m' _ _ Hmu); [|exact Qtr].
      intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi. cbn. split; [lia | exact I]. }
  - exact (w5_ctlrt cx _ _ _ _ _ _ _ HB HJ').
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82f48 (0x82f48, own6, k <= 526) --S_Y1--> B82f5c (own0).
   S_Y1 (Seg/YTail.v seg_Y1 :854): `jal __asan_stack_free_6` at 0x82f48 (a0 = fr, a1 = 3136), returning at 0x82f4c,
   then `j 0x82f5c`.  The frame (6, c_fpos cx) is released: own goes [(6, c_fpos cx)] -> []. *)
Lemma seg_Y1 : forall POST,
  ctl_from POST C_B82f5c ->
  ctl_from POST C_B82f48.
Proof.
  intros POST H5c cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  unfold ACtlCutP.C_B82f48 in HJ, Hfr, HFA, Hk, HBODY |- *.
  cbn [ACtlCut.cut_own ACtlCut.cut_kmax ACtlCut.cut_body ACtlCut.cut_pc] in HJ, Hfr, HFA, Hk, HBODY |- *.
  pose proof (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)) as Efr.
  destruct (w5_frame cx ly3 S3 W3 mem3 md3 k HJ Hfr) as (Hin & Efa & Hf0 & Hf1 & Happ & Hfb & Hfsh).
  rewrite <- Efr in Efa, Hf0, Hf1, Happ, Hfb, Hfsh.
  destruct (w5_stack cx _ ly3 S3 W3 mem3 md3 k HJ) as (Hs0 & Hs47 & Hs16 & Hwin).
  pose proof (lib.Reusable.YM05.alloc_ceiling_val (RunCeil := rc)) as [[Hc0 Hc1] _].
  destruct HBODY as (Hperm & HFH & _ & Ha0 & Ha1).
  pose proof HFH as (A & sp & Esp & Hsp16 & EspZ & Etp & E8 & E9 & E3 & E19 & E26 & Hfr32 & HA32 & HAS & HspA &
                     HfrA & HA448 & HSsp & HSapp & Q336 & Qhdr & Q16 & Hsh & Hsav & Qtr).
  unfold ACtlCutP.FRAME_BYTES in HfrA.
  pose proof HB as ((HAFN & _ & _ & _ & _ & _ & _ & Hfr0 & _) & _).
  pose proof HAFN as (_ & _ & _ & Hgp & Htp & _).
  pose proof HJ as (HAR & Hly & _).
  assert (Efl : Reusable.YG0f.flag_addr ly3 6 (ACtlCut.c_fpos cx) =
                Reusable.YG0f.flag_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)).
  { unfold Reusable.YG0f.flag_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  destruct (Reusable.YG0d.al_flag _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as (_ & _ & Hfl1 & Hfl2).
  rewrite Efl in Hfl1, Hfl2. unfold Reusable.YG0f.in_app in Hfl1.
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  (* 0x82f48 `jal 3dd30`: to the release entry with ra = 0x82f4c *)
  eapply (w5_lift W3 regs3 mem3 md3 0x82f48 RNG).
  { eapply (YTailF.y1_pre_F (fx := FX5) RNG). }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' Hpost Hhid Hsbm. cbv beta in Hpost. subst ms'.
  assert (HJm : AJ cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md' k).
  { apply (w5_journal_munch cx _ ly3 S3 W3 mem3 md3 k mem3 md' 0 0 HJ (lib.Lib.Frame.munch_refl _ _)
             (lib.Lib.Frame.wmono_refl _ _) Hhid Hsbm).
    intros a Ha. lia. }
  unfold ACtlCut.own6 in HJm.
  match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ => set (R1 := R) end.
  assert (EspR : Reusable.YG0d.spZ R1 = sp) by exact EspZ.
  change (Reusable.YA0n.SRr segs W3
            (mkCfg (lib.Reusable.YK11.mkst R1 (Z_to_bv 64 0x3dd30) mem3 (lib.Reusable.YK11.seg_rom segs)) md') (POST cx)).
  eapply Reusable.YA0n.SRr_bind.
  { apply (Reusable.StackFreeJournal.aj_stack_free_at segs B LAWS w5_segs_low ML 0x3dd30 6 stack_free6_contract
             ltac:(lia) W3 R1 mem3 Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP (ACtlCut.c_ly cx) (ACtlCut.c_S cx)
             (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) [] ly3 S3 md' k (ACtlCut.c_fpos cx) 3136
             (sp - ACtlCut.c_sp cx) (Z_to_bv 64 0x82f4c) HJm).
    - rewrite Efa. exact Ha0.
    - exact Ha1.
    - change (Reusable.YG00.fs_frame_bytes 6) with 4096. lia.
    - reflexivity.
    - rewrite Efa, Efl. change (Reusable.YG00.fs_frame_bytes 6) with 4096.
      replace (fr + 4096 - 8) with (fr + 4088) by lia.
      apply (w5_rdword W3 mem3); [lia | |].
      + intros i Hi. exact (proj1 (proj1 (Hfb (fr + 4088 + i) ltac:(lia)))).
      + unfold ACtlCutP.q64 in Qtr. exact Qtr.
    - rewrite EspR. lia.
    - lia.
    - lia.
    - unfold Reusable.YG0d.ESTACK, Reusable.YCfn.LLVMF_STK. lia.
    - rewrite <- Hgp. exact E3.
    - exact Etp.
    - reflexivity.
    - apply lib.Reusable.YK0s.ret_ok_even. reflexivity. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hpres & _ & Hview & _).
  (* 0x82f4c `j 0x82f5c` *)
  change (Reusable.YA0n.SRr segs W3 (Reusable.YG0d.cfg_at segs 0x82f4c regs2 mem2 md2) (POST cx)).
  eapply (w5_lift W3 regs2 mem2 md2 0x82f4c RNG).
  { eapply (YTailF.y1_post_F (fx := FX5) RNG). }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md3' Hpost Hhid' Hsbm'. cbv beta in Hpost. subst ms'.
  assert (HJ3 : AJ cx (ACtlCut.own0 cx) ly3
                  (Reusable.YG01.stack_free_state 6 (ACtlCut.c_fpos cx) S3) W3 mem2 md3' k).
  { apply (w5_journal_munch cx _ ly3 _ W3 mem2 md2 k mem2 md3' 0 0 HJ2 (lib.Lib.Frame.munch_refl _ _)
             (lib.Lib.Frame.wmono_refl _ _) Hhid' Hsbm').
    intros a Ha. lia. }
  assert (Hcs : forall r, r = 3 \/ r = 4 \/ r = 8 -> Reusable.YG0d.acallee_saved r)
    by (intros r Hr; unfold Reusable.YG0d.acallee_saved; lia).
  assert (P3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs3 3) by exact (Hpres 3 (Hcs 3 ltac:(lia))).
  assert (P4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs3 4) by exact (Hpres 4 (Hcs 4 ltac:(lia))).
  assert (P8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr regs3 8) by exact (Hpres 8 (Hcs 8 ltac:(lia))).
  match goal with |- Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ =>
    apply (H5c cx idx fr k ly3 (Reusable.YG01.stack_free_state 6 (ACtlCut.c_fpos cx) S3) W3 R mem2 md3' HB HJ3) end.
  - pose proof HJ3 as (_ & _ & _ & _ & _ & Hfrs3 & _). rewrite Hfrs3, Hfr0. reflexivity.
  - intros cid pos Hc. destruct Hc.
  - exact Hk.
  - unfold ACtlCutP.C_B82f5c. cbn [ACtlCut.cut_body].
    split; [exact Hperm|].
    split; [unfold ACtlCut.rgv; transitivity (lib.Reusable.YK11.getr regs2 8); [reflexivity|]; rewrite P8; exact E8|].
    split; [transitivity (lib.Reusable.YK11.getr regs2 3); [reflexivity|]; rewrite P3; exact E3|].
    split; [transitivity (lib.Reusable.YK11.getr regs2 4); [reflexivity|]; rewrite P4; exact (eq_trans Etp (eq_sym Htp))|].
    apply (w5_bytes_aview W3 mem3 mem2); [|exact Hsav].
    intros i Hi. unfold ACtlCutP.saved_bytes in Hi. rewrite !length_app, !lib.Lib.Mem.length_le8 in Hi. simpl in Hi.
    split; [exact (proj1 (Hwin (ACtlCut.c_sp cx - 104 + i) ltac:(lia)))|].
    apply Hview.
    + lia.
    + rewrite Efa. unfold Reusable.StackFreeDef.sf_span. cbn -[Reusable.YG0f.shadow_addr].
      unfold Reusable.YG0f.shadow_addr, Reusable.YG0f.SHADOW_OFF. change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
      lia.
    + rewrite Efl. lia.
    + lia.
  - exact (w5_ctlrt cx _ _ _ _ _ _ _ HB HJ3).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B82f5c (0x82f5c, own0, k <= 526) --S_Y3--> return to RA_LLVMF = 0x80f14 with the core's lib post.
   S_Y3 (Seg/YTail.v seg_Y3 :241): `li a0,0`, the 13 callee-saved reloads from [S - 104, S), sp = S, `ret`.
   The donor's exit is rt_postP (A/ACf5.v:99-107), built as rt_XP_aux does (A/ACf4.v:89-116, SRr_ret_at
   YA0o.v:334); here the exit predicate is post_leaf (ACtl.v's ctl_post_leaf).  ACtl.v states seg_Y3 at the walk's
   FP := [] (its section 1); this file keeps FP a Variable and takes FP = [] as the Section hypothesis FP_nil, which
   the top discharges by eq_refl. *)
Lemma seg_Y3 :
  ctl_from post_leaf C_B82f5c.
Proof.
  intros cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  unfold ACtlCutP.C_B82f5c in HJ, Hfr, HFA, Hk, HBODY |- *.
  cbn [ACtlCut.cut_own ACtlCut.cut_kmax ACtlCut.cut_body ACtlCut.cut_pc] in HJ, Hfr, HFA, Hk, HBODY |- *.
  destruct HBODY as (Hperm & E8 & E3 & E4 & Hsav).
  destruct (w5_stack cx _ ly3 S3 W3 mem3 md3 k HJ) as (Hs0 & Hs47 & Hs16 & Hwin).
  pose proof (lib.Reusable.YM05.alloc_ceiling_val (RunCeil := rc)) as [[Hc0 Hc1] _].
  pose proof HB as ((HAFN & Hra & Ha0 & Ha1 & Hpn & Hlen & Hgarr & Hfr0 & Hnev0 & Hlive0 & Hro0 & Hsink0 & Hfd0 &
                     Hsorted0 & Hmeta0 & Hmok0) & Hsp1).
  unfold ACtlCutP.saved_bytes in Hsav.
  eapply (w5_lift W3 regs3 mem3 md3 0x82f5c (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))).
  { eapply (YTailF.y3_evt_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3))) with (Sv := ACtlCut.c_sp cx)
      (Rv := Reusable.YCfn.RA_LLVMF).
    - exact E8.
    - lia.
    - reflexivity.
    - unfold Reusable.YCfn.RA_LLVMF. lia.
    - reflexivity.
    - exact Hsav.
    - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (Hwin a ltac:(lia))). }
  { apply B.ProgBridge.fp_avoids_RNG_W. }
  intros ms' md' Hpost Hhid Hsbm.
  destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
  assert (HJm : AJ cx (ACtlCut.own0 cx) ly3 S3 W3 mem3 md' k).
  { apply (w5_journal_munch cx _ ly3 S3 W3 mem3 md3 k mem3 md' 0 0 HJ (lib.Lib.Frame.munch_refl _ _)
             (lib.Lib.Frame.wmono_refl _ _) Hhid Hsbm).
    intros a Ha. lia. }
  rewrite FP_nil in HJm. unfold ACtlCut.own0 in HJm.
  pose proof (w5_journal_sk SK Reusable.YE2k.tfib_sink_head _ _ [] _ _ _ _ _ _ _ _ _ _ _ _ HJm) as HJ0.
  pose proof HJ0 as (_ & _ & _ & _ & Hio & _ & _ & _ & _ & HF2 & _).
  destruct Hio as (_ & _ & _ & _ & _ & _ & Hclosed).
  destruct (Hclosed Reusable.YCbq.sink_closed_nil) as (Efd & Efsys & _).
  pose proof AIL as HAIL.
  apply Reusable.YA0n.SRr_ret.
  unfold B.ACtl.ctl_post_leaf.
  match goal with |- context [mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _] =>
    exists ly3, S3, R, mem3, md', k end.
  split; [reflexivity|].
  split; [exact (w5_journal_sk SK Reusable.YE2k.tfib_sink_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJm)|].
  split; [unfold Reusable.YCfn.EV_LIB; unfold B.ACtlK.EV_LLVMF in Hk; lia|].
  split.
  { intros r Hr. unfold Reusable.YG0d.acallee_saved in Hr.
    assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                 r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]].
    - transitivity (Z_to_bv 64 (ACtlCut.c_sp cx)); [reflexivity|].
      unfold ACtlCut.c_sp, Reusable.YG0d.spZ. apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned.
    - transitivity (lib.Reusable.YK11.getr regs3 3); [reflexivity | exact E3].
    - transitivity (lib.Reusable.YK11.getr regs3 4); [reflexivity | exact E4].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity. }
  split; [reflexivity|].
  split; [exact Hperm|].
  split; [intros fd; unfold m_fds; rewrite Efd; reflexivity|].
  split; [unfold m_fs; rewrite Efsys; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hsorted0|].
  split; [exact (Reusable.YE01.asink_none_kept (SK := Reusable.YE2k.tfib_sink_head) segs B Reusable.YE2k.tfib_K HAIL
                   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 Reusable.YCbq.sink_closed_nil Hsink0)|].
  split; [exact (Reusable.YE01.ameta_inv_kept (SK := Reusable.YE2k.tfib_sink_head) segs B Reusable.YE2k.tfib_K HAIL
                   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 Hmeta0)|].
  split; [apply HMOLE|].
  intros i Hi. destruct Hpn as [[Hn0 _] | [Hn Hin0]]; [lia|].
  apply (HF2 _ _ i Hin0).
  - exact (Permutation_in _ (Permutation_sym Hperm) Hin0).
  - pose proof (Reusable.YCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)) as Hrq. lia.
  - apply lib.Reusable.YI04.inFP_nil.
Qed.

End W5.

(* Stage lemmas of this file, all closed by Qed; each is named and stated exactly as ACtl.v's Hypothesis of the same
   name, generic in SK; FP enters seg_Y3 only through the named Section hypothesis FP_nil (FP = [], the top's
   instance):
     seg_X1   (B82eac) : forall POST, ctl_from POST C_B82ecc -> ctl_from POST C_Jrel -> ctl_from POST C_B82eac
     seg_X2   (B82ecc) : forall POST, ctl_from POST C_Jrel -> ctl_from POST C_B82ecc
     seg_Jrel (Jrel)   : forall POST, ctl_from POST C_B82f48 -> ctl_from POST C_Jrel
     seg_Y1   (B82f48) : forall POST, ctl_from POST C_B82f5c -> ctl_from POST C_B82f48
     seg_Y3   (B82f5c) : ctl_from post_leaf C_B82f5c   (ACtl.v: CF ctl_post_leaf C_B82f5c)
   B82f58: no record, no lemma (class-full arm).
   Sink / trap obligations: 0x82ecc -> 0x82fa4 (`beqz a0`), refuted in seg_X2 inside X12F.x12_x2_evt_F (a0 = q, 0 < q),
   and on S_X1's memchr arm the cut's a0 is the memchr result fr + 2691 + k with k < 17 (the body's find_byte).
   Dead edge discharged: S_Jrel -> B82f58 (sel = fr <> 0: jrel_evt_side_F's premise 0 < fr, from frames_bounds). *)
