(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v, with its module paths and module names changed; 3018 of its 3112 lines of code are new or changed and 934 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/ACtlW4e1.v, with its module names changed; 841 of its 922 lines of code are new or changed and 3031 lines of the source are left out. *)
(* lib/B/ACtlW0.v -- piece W0 (the prologue: S_A1, S_A2, S_A3) of fuzz_ctrl image B's (asan-ubsan) walk of
   LLVMFuzzerTestOneInput in the released cgif_file_fuzzer form.  Writer: a Theorem Labs lane for a Theorem Labs lane.
   rule 24: no function proved (stage glue of a walk).

   WHAT THIS FILE PROVES: one stage lemma per cut of W0, in the donor's continuation shape (rt_A2 A/ACf0.v:173 at
   c8557374ad2e): "the successor cuts hold -> this cut holds", over lib/B/ACtlCut.v's ctl_from and
   lib/B/ACtlCutP.v's cut records.  Each statement is token-equal to lib/B/ACtl.v's Hypothesis of the same name,
   generic in SK and FP (the top instantiates SK := tfib_sink_head, FP := []).
     ENTRY  (0x81018) --S_A1--> B81090   the prologue run, then __asan_stack_malloc_6 @0x8108c (seg_A1)
     B81090 (0x81090) --S_A2--> B810c4   the arm split on a0; only the fake-frame arm is live (seg_A2)
     B810c4 (0x810c4) --S_A3--> B81220   frame header + 68 shadow stores, then __asan_set_shadow_f8 @0x8121c (seg_A3)
   No piece-internal loop; no allocator site; no UBSan trap branch (plan 6.2) and no branch into the ASan abort sink
   0x82fa4 / 0x82fa0 in 0x81018-0x81220 (objdump L83794-L83924).  Dead edges: S_A1 -> B810c4 (UAR = 1 from
   asan_cells, read by the run) and S_A2's real-stack arm (the allocation post has only the frame_addr outcome).

   ROUTE: each stage lifts a footprint run of the cut's raw memory with Reusable.YA0nR.SRr_fsteps (footprint
   ProgBridge.RNG_W (w_H W), which avoids the hidden set by construction), keeps the journal across the run with
   B.ProgWorld.ajournal_of_fsteps, steps each runtime call through its owner's contract in SRr form, and rebuilds the
   successor's body, journal and runtime conjunct.  Route (C): the cut carries B.ACtlRtC.ctl_rt_C (asan cells,
   shadow_rw_on over the cut's own shadow and over the image's shadow, ro_agree); an exit gets it from the post AR by
   B.ProgWorldCtlRtC.ctl_rt_C_of_AR (w0_ctl_rt).  Runs used: A2F.a2_side_evt_F, W0A1N.a1_pro_Fs (below, the narrowed
   form of A1F.a1_pro_F, with a pin back to it) and the owner's narrowed run A3F.a3_evt_pre_F_on (Seg/A3F.v:267).

   SECTION HYPOTHESES (each is discharged by the top; owner in brackets):
   - Hwx : wx_segs_nowrap segs                                        [the top; the kit's once-per-unit fact]
   - LAWS : AR_laws segs B                                            [the top; core YG0q.AR_laws_ok]
   - UnitSyms / USYMS / stack_malloc6_contract                       [a Theorem Labs lane; ctrl B's <Unit>Syms name pending]
   - set_shadow_f8 : aset_shadow_realizes segs B 0x55144 0xf8         [a Theorem Labs lane; B.Rt.SetShadow.ctrl_set_shadow_f8]
   - TFIB_SYMS : CtrlTSyms B                                          [the top; CtrlB_syms]
   - RELRO_IMG, RO_OFL                                                [the top; ACtl.v / RTPOST texts]
   No other open fact: mem_inv, the 1 MiB slot window and sp < 2^47 of A1F.a1_pro_F are narrowed away (W0A1N); the
   frame-shadow writability that A3F.a3_evt_pre_F_on takes comes from ctl_rt_C's cut_shadow conjunct; set_shadow_f8's
   missing presence clause is not needed (w0_journal_view: its writes are shadow bytes, every stack byte lies above
   the image, where the core's view sees only mem).

   PROVENANCE: cut table cut-table-B.tsv rows 1-3 (a working note, not in this delivery); plan
   llvmf-B-walk-plan.md 2.3 rows 1-3, 2.6, 6.2 (a working note, not in this delivery); ctrl's runs at
   a working branch 3803efccea0 (Seg/A1.v, A2.v, A3.v); objdump
   fuzz_ctrl.objdump.txt L83794-L83924 (a working note, not in this delivery). *)

From Stdlib Require Import ZArith List Permutation Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04 Reusable.YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11.
(* the kit bridge (a Theorem Labs lane, bridge-stmt.md (a working note, not in this delivery)) and ctrl's footprint engine lib/Lib/ExecF.v (Required, never
   Imported: the SHADOWED NAMES rule) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04R Reusable.YA0nR Lib.ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YC5d Reusable.YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YO09 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YCfn.
(* expected path of a Theorem Labs lane's relocated SetShadowDef (pending; see header) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.SetShadowDef.
(* lib/Lib's raw-memory vocabulary of the call-post facts below (Required only, never Imported). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Frame Cells Step Mem.
(* lib/Lib's register-map bridge (the run's canonical start registers) and the MS constructor of the footprint runs *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss MState.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Img0 B.ACtlK B.ACtlCut B.ACtlCutP.
(* image B's frozen bridge (a Theorem Labs lane): fevt_of_evtF, RNG_W, fp_avoids_RNG_W, cfg_at_MS, rsegs_spans *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgBridge.
(* image B's ProgWorld (a Theorem Labs lane, writer a Theorem Labs lane): aview_vis_mrd, ajournal_of_fsteps, arodata_okP_of_S; the byte
   lemmas of ProgWorldCtlRt; route (C): ctl_rt_C (ACtlRtC), shadow_rw_on (ShadowRwOn), ctl_rt_C_of_AR (ProgWorldCtlRtC) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld B.ProgWorldCtlRt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ShadowRwOn ACtlRtC ProgWorldCtlRtC.
(* the core's CtrlTSyms record, the read-only journal lemma, the frame placement facts *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YF0m Reusable.APostBase Reusable.YG0s Reusable.YG0p.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG00 Reusable.YG01 Reusable.YE01 Reusable.YG05.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require A1F A2F A3F.
(* Closure only (porter 23:38Z / 23:40Z: a stage file may Require a Theorem Labs lane's `_F` files and their closure, which includes
   lib/B/Contract.v; no STATEMENT names it except the one bridging lemma below).  Reusable.YImgTop arrives with the
   next planning-core sha (IMG_LO 0x10000, IMG_TOP 0x5fe000). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Contract Reusable.YImgTop.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------
   NARROWED PROLOGUE RUN (the glue owner's narrowing of a source run, as image A's lane did for its A1F.v:
   a working branch lib/A/Prog/Seg/A1Fs.v).  a Theorem Labs lane's A1F.a1_pro_F (Seg/A1.v:397 a1_pro) states a
   1 MiB slot stack window `stk rsegs m lo sp` with `lo + 1048576 <= sp`, `sp < 2 ^ 47` and `mem_inv rsegs m` (with
   mem_inv in its post).  The walk's journal gives presence only for [c_sp - LLVMF_STK, c_sp) (LLVMF_STK = 32768),
   the core's pre gives sp <= 2 ^ 47 only (astk_ok), and no core fact gives mem_inv (a Theorem Labs lane).  The run writes only
   [sp - 448, sp), so a1_pro_Fs takes the window [lo, sp) with lo + 448 <= sp, sp <= 2 ^ 47, and drops mem_inv from
   its premises and its post.  Its script is A1F.v's (:58-85), unchanged; the pin a1_pro_F_of_Fs re-derives A1F's
   statement (its type taken from the term A1F.a1_pro_F) from it.  The module is closed: its Imports (A1F.v's list)
   do not reach the Section below. *)
Module W0A1N.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs
  LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode
  LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YM05
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK0o OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK0s
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK15 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YP09
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YO0f OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YO0d
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YO09 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YL00
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YL0g OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YL0i
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YI14 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YI16
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YL01 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YM06.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Tac
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Bytes OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ZBridge.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Img0 OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.AsanRT
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.AsanRTInv OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.AsanRTFacts
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.PContract OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.MemNorm
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.AsanLift OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.KindBGlue.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.SlotModel OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.SlotInv
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.RcAsanFPLib
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_stack_malloc_c.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.Tac_slot OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.Tac_fs.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Lemma a1_pro_Fs :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo + 448 <= bv_unsigned sp ->
  bv_unsigned sp <= 2 ^ 47 -> asan_cells m ->
  rng RNG (bv_unsigned sp - 448) 8 -> rng RNG (bv_unsigned sp - 104) 104 ->
  rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 -> rng RNG GOT_UAR 8 -> rng RNG UAR 4 ->
  evtF rsegs RNG
    (fun ms' => exists (ra' sp' a0' a1' a2' s10' : word) (m' : word -> option byte),
       ms' = MS (mkR ra' sp' gp tp t0 t1 t2 sp sp' a0' a1' a2' a3 a4 a5 a6 a7 a1 s3 s4 s5 a0 s7 s8 s9 s10' s11
                     t3 t4 t5 t6) F (Z_to_bv 64 0x3db94) fc None m' (seg_rom rsegs) /\
       ra' = Z_to_bv 64 0x81090 /\
       bv_unsigned sp' = (bv_unsigned sp - 448) - (bv_unsigned sp - 448) mod 32 /\
       bv_unsigned a0' = 3136 /\ s10' = Z_to_bv 64 ASAN_K /\
       munch [(bv_unsigned sp - 448, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
       stk rsegs m' lo (bv_unsigned sp) /\
       bytes_at rsegs m' (bv_unsigned sp - 104)
         (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++
          le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81018) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST HLO LO HSP HAC RZ RSTK RGCK RCK RGUAR RUAR.
  destruct HAC as (HCK & HGCK & _ & _ & _ & HUAR & HGUAR & _).
  unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR, ASAN_K in *.
  apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.A1.ro8l in HCK, HGCK, HGUAR.
  apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.A1.ro4l in HUAR.
  pose proof (munch_refl [(bv_unsigned sp - 448, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  carve_frame 448%nat ST.
  do 27 step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with false by (vm_compute; reflexivity) end.
  cbv iota.
  do 3 step.
  pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.A1.a1_tail2 _ _ _ _ _ _ FR) as SB.
  cbn [cells_bytes cbytes] in SB. rewrite app_nil_r in SB.
  replace (bv_unsigned sp + -448 + 8 + Z.of_nat 336) with (bv_unsigned sp - 104) in SB by lia.
  release_frame FR ST (bv_unsigned sp).
  finish.
  all: try reflexivity.
  all: try assumption.
  rewrite (unsigned_lit (bv_unsigned sp + -448)) by lia.
  rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.A1.a1_land32 by lia.
  rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned sp + -448) 32 ltac:(lia)); lia).
  reflexivity.
Qed.

(* The PIN: A1F.a1_pro_F's statement (its type, taken from the term itself), re-derived from a1_pro_Fs.  The 1 MiB
   window and sp < 2 ^ 47 imply the narrowed premises; mem_inv of the end memory follows from mem_inv of the start
   memory: outside [sp - 448, sp) the run leaves memory unchanged (munch), and inside it every byte is writable in
   the start memory (stk), hence not read-only (Mem.wview_not_ro). *)
Lemma a1_pro_F_of_Fs :
  ltac:(let T := type of OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.A1F.a1_pro_F in exact T).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST HLO LO MI HSP HAC RZ RSTK RGCK RCK RGUAR RUAR.
  eapply evtF_mono;
    [exact (a1_pro_Fs RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6 F fc m lo ST HLO ltac:(lia) ltac:(lia) HAC RZ RSTK RGCK RCK RGUAR RUAR)|].
  intros ms' (ra' & sp' & a0' & a1' & a2' & s10' & m' & E & Era & Esp & Ea0 & Es10 & MU & WM & ST' & SB).
  exists ra', sp', a0', a1', a2', s10', m'.
  split; [exact E|]. split; [exact Era|]. split; [exact Esp|]. split; [exact Ea0|]. split; [exact Es10|].
  split; [exact MU|]. split; [exact WM|]. split; [|split; [exact ST' | exact SB]].
  intros x b Hx.
  destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp - 448)) as [D1|D1];
    [rewrite (MU x ltac:(cbn; split; [lia | exact I])) in Hx; exact (MI x b Hx)|].
  destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned sp)) as [D2|D2];
    [|rewrite (MU x ltac:(cbn; split; [lia | exact I])) in Hx; exact (MI x b Hx)].
  destruct (m x) as [b0|] eqn:Em; [exact (MI x b0 Em)|].
  apply (wview_not_ro rsegs m x); [|exact Em].
  destruct ST as (_ & _ & STa). destruct (STa (bv_unsigned x) ltac:(lia)) as (Hw & _).
  unfold wa in Hw. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hw. exact Hw.
Qed.

End W0A1N.


Section W0.

(* The shell's contexts and variables, in its order (lib/B/ACtlCut.v section CtlCut after the 22:47Z re-twin).
   SK is the core's sink head; the top instantiates it EXPLICITLY with Reusable.YE2k.tfib_sink_head (a Theorem Labs lane
   22:39Z / 22:45Z); nothing here relies on instance resolution. *)
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib.Reusable.YO09.lib_shape}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : Reusable.YG0f.asyms.
Variable MT : Reusable.YC5d.ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable FP : list (Z * Z).

Local Notation segs := Reusable.YB1v.tfibsegs.

(* ---- SHELL BINDING: the only lines that name ACtlCut's / ACtlCutP's argument lists.  At the re-twin, fix the
   argument list here and nowhere else.  ctl_from takes the variables its ctl_base / ajournal use (a Theorem Labs lane 22:4xZ (d):
   tfib_lib_pre_x B MT XM_LIB RLO RHI; the journal's FP), as the sibling W2a draft does. ---- *)
Local Notation ctl_from := (ACtlCut.ctl_from B MT XM_LIB RLO RHI FP).
Local Notation C_ENTRY := (ACtlCutP.C_ENTRY B).
Local Notation C_B81090 := (ACtlCutP.C_B81090 B).
Local Notation C_B810c4 := (ACtlCutP.C_B810c4 B).
Local Notation C_B81220 := (ACtlCutP.C_B81220 B).

(* ---- Section hypotheses (sources in the header) ---- *)
Hypothesis Hwx : Reusable.YK04.wx_segs_nowrap segs.

(* __asan_stack_malloc_6 @0x8108c (callee 0x3db94): a Theorem Labs lane's stack_malloc6_contract at this Section's fx rc B.
   UnitSyms = ctrl B's <Unit>Syms record (name pending, TfibSyms's role in the donor). *)
Variable UnitSyms : Reusable.YG0f.asyms -> Prop.
Hypothesis LAWS : Reusable.YG0d.AR_laws segs B.
Hypothesis USYMS : UnitSyms B.
Hypothesis stack_malloc6_contract :
  Reusable.YG0d.AR_laws segs B -> UnitSyms B -> Reusable.YG0d.astack_malloc_realizes segs B 6.

(* __asan_set_shadow_f8 @0x8121c (callee 0x55144 = the relocated file's SSF8_ENTRY): a Theorem Labs lane's Theorem Labs contract,
   value 0xf8, in grant_set_shadow_f8's statement form at this Section's B. *)
(* Image-B instance (a Theorem Labs lane 00:58Z): B.Rt.SetShadow.ctrl_set_shadow_f8 (0x55144), text after B's core lands; the
   top discharges this hypothesis with it. *)
Hypothesis set_shadow_f8 :
  Reusable.YG0d.AR_laws segs B -> UnitSyms B -> Reusable.SetShadowDef.aset_shadow_realizes segs B 0x55144 0xf8.

(* The core's symbol record of ctrl B (ACtl.v's TFIB_SYMS, same text; the top supplies CtrlB_syms). *)
Hypothesis TFIB_SYMS : Reusable.YF0m.CtrlTSyms B.

(* ctl_rt_C after a world-changing step: B.ProgWorldCtlRtC.ctl_rt_C_of_AR (proved; CtrlTSyms, AR_laws, AR and the
   read-only fact of the state, which the journal carries from ctl_base's arodata_okS by
   APostBase.arodata_ok_journalP: the span lies in the image and below the sink head). *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> Reusable.YG0d.in_img segs a.
Context {RO_OFL : Reusable.APostBase.ro_below_ofl segs RLO RHI}.

(* A3F's a3_evt_pre_F_on re-runs a3_evt, whose premise is `AC.GT <= fr` (Seg/A3.v:428-433).  Porter 23:40Z: a stage file that
   applies an `_F` naming AC.GT states ONE lemma AC.GT = IMG_TOP and rewrites with it, so its statements say IMG_TOP
   only.  lib/B/Contract.v:73 `Definition GT : Z := 0x5fe000`. *)
Lemma w0_gt_img_top : B.Contract.GT = Reusable.YImgTop.IMG_TOP.
Proof. reflexivity. Qed.

(* ---- Local glue lemmas (generic in the cut; used by every stage below) ---- *)

(* The core's segments lie below kLowMemEnd: the side condition `segs_low` of the journal lemmas
   (Reusable.YCbq Section a0), from ProgBridge.rsegs_spans (tfibsegs = rsegs by conversion). *)
Lemma w0_segs_low : forall a, Reusable.YG0d.in_img segs a -> 0 <= a < Reusable.YG0f.kLowMemEnd.
Proof.
  intros a (sg & Hin & Hr).
  pose proof (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs sg Hin) as H.
  change segs with B.Img0.rsegs in H. rewrite B.ProgBridge.rsegs_spans in H.
  unfold Reusable.YG0f.kLowMemEnd.
  remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
  destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.

(* The journal does not see a materialized model (a footprint run's only effect on the model). *)
Lemma w0_journal_mat : forall STK sp0 ly S W mem md own lyc Sc Wc memc mdc k mdc',
  Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  Reusable.YK04.same_but_materialized mdc mdc' ->
  Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc' k.
Proof.
  intros STK sp0 ly S W mem md own lyc Sc Wc memc mdc k mdc' HJ Hs.
  eapply (Reusable.YCbq.ajournal_exec (SK := SK) segs B LAWS w0_segs_low STK sp0 FP ly S W mem md own lyc Sc Wc
            memc mdc k memc mdc' (fun _ => False) HJ).
  - intros x _. reflexivity.
  - apply lib.Reusable.YK1b.mem_grows_refl.
  - intros x _. reflexivity.
  - exact Hs.
  - intros a [].
Qed.

(* An own6 cut's frame base (gap G1 of the shell): the journal's frame (6, c_fpos cx) is live, fr is its address in the
   current layout, and the frame lies in the fake-stack area [4096, alloc_ceiling), 32-aligned. *)
Lemma w0_own6_frame : forall cx fr ly3 S3 W3 mem3 md3 k,
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3) /\
  fr = Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) /\
  4096 <= fr /\ fr + 4096 <= lib.Reusable.YM05.alloc_ceiling /\ fr mod 32 = 0.
Proof.
  intros cx fr ly3 S3 W3 mem3 md3 k HJ Hfr HFA.
  assert (Hin : In (6, ACtlCut.c_fpos cx) (Reusable.YG01.frames S3)) by (rewrite Hfr; left; reflexivity).
  pose proof (HFA 6 (ACtlCut.c_fpos cx) (or_introl eq_refl)) as Efr.
  destruct HJ as (HAR & Hly & _).
  assert (EF : Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) =
               Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 (ACtlCut.c_fpos cx)).
  { unfold Reusable.YG0f.frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  pose proof (Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (H1 & H2 & _).
  pose proof (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as (H3 & _).
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in H2.
  rewrite <- EF in Efr. subst fr.
  split; [exact Hin|]. split; [reflexivity|]. split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

(* ---- raw-memory facts from the core's presence (apresent is H a = false and a byte in mem) ---- *)
Lemma w0_pres_raw : forall H mem a, Reusable.YG0n.apresent H mem a ->
  wview B.Img0.rsegs mem (lib.Lib.Mem.wa a) <> None /\
  exists b, lib.Lib.Mem.mrd B.Img0.rsegs mem (lib.Lib.Mem.wa a) = Some b.
Proof.
  intros H mem a (_ & b & Hb). unfold lib.Lib.Mem.wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd. rewrite Hb. reflexivity.
Qed.

Lemma w0_stk_pres : forall H mem lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> Reusable.YG0n.apresent H mem a) -> lib.Lib.Frame.stk B.Img0.rsegs mem lo hi.
Proof.
  intros H mem lo hi H0 H1 HP. split; [exact H0|]. split; [exact H1|].
  intros a Ha. exact (w0_pres_raw H mem a (HP a Ha)).
Qed.

(* a footprint range inside B's loaded image [0x10000, 0x5fe000), visible in every world (ProgBridge.img_vis_W) *)
Lemma w0_rng_img : forall (W : Reusable.YA0n.world segs) lo len, 0x10000 <= lo -> 0 <= len ->
  lo + len <= 0x5fe000 -> Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) lo len.
Proof.
  intros W lo len H0 H1 H2. apply B.ProgBridge.rng_of_visible.
  apply (B.ProgBridge.range_visible_sub _ B.Prog.ImgBounds.IMG_LO
           (B.Prog.ImgBounds.IMG_HI - B.Prog.ImgBounds.IMG_LO)); [exact (B.ProgBridge.img_vis_W W) | | |];
    unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI; lia.
Qed.

(* the byte arithmetic of a little-endian word read *)
Lemma w0_div256 : forall b X, 0 <= b < 256 -> (b + 256 * X) / 256 = X.
Proof. intros b X Hb. rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia. Qed.

Lemma w0_mod256 : forall b X, 0 <= b < 256 -> (b + 256 * X) mod 256 = b.
Proof. intros b X Hb. rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. exact Hb. Qed.

(* a word the core's view reads (rdword over aview) is a q64 over mrd *)
Lemma w0_q64_of_rdword : forall (W : Reusable.YA0n.world segs) m a v,
  0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  Reusable.YG0d.rdword (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m) a = Some v ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a (lib.Lib.Mem.le8 (Z_to_bv 64 v)).
Proof.
  intros W m a v Ha0 Ha8 Hv Hr. unfold Reusable.YG0d.rdword in Hr.
  destruct (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m a) as [b0|] eqn:E0; [|discriminate Hr].
  destruct (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + 1)) as [b1|] eqn:E1; [|discriminate Hr].
  destruct (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + 2)) as [b2|] eqn:E2; [|discriminate Hr].
  destruct (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + 3)) as [b3|] eqn:E3; [|discriminate Hr].
  destruct (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + 4)) as [b4|] eqn:E4; [|discriminate Hr].
  destruct (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + 5)) as [b5|] eqn:E5; [|discriminate Hr].
  destruct (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + 6)) as [b6|] eqn:E6; [|discriminate Hr].
  destruct (Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) m (a + 7)) as [b7|] eqn:E7; [|discriminate Hr].
  injection Hr as Hr.
  destruct (Reusable.YCbq.aview_byte _ _ _ _ _ E0) as (_ & _ & _ & B0).
  destruct (Reusable.YCbq.aview_byte _ _ _ _ _ E1) as (_ & _ & _ & B1).
  destruct (Reusable.YCbq.aview_byte _ _ _ _ _ E2) as (_ & _ & _ & B2).
  destruct (Reusable.YCbq.aview_byte _ _ _ _ _ E3) as (_ & _ & _ & B3).
  destruct (Reusable.YCbq.aview_byte _ _ _ _ _ E4) as (_ & _ & _ & B4).
  destruct (Reusable.YCbq.aview_byte _ _ _ _ _ E5) as (_ & _ & _ & B5).
  destruct (Reusable.YCbq.aview_byte _ _ _ _ _ E6) as (_ & _ & _ & B6).
  destruct (Reusable.YCbq.aview_byte _ _ _ _ _ E7) as (_ & _ & _ & B7).
  assert (Uv : bv_unsigned (Z_to_bv 64 v) = v).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact Hv. }
  split; [exact Ha0|]. rewrite lib.Lib.Mem.length_le8. split; [lia|].
  intros i Hi. unfold lib.Lib.Mem.le8, word_to_le_bytes.
  rewrite (B.ProgWorldCtlRt.nth_Z_to_le_bytes 8 _ i Hi), Uv, <- Hr.
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; [| | | | | | | | lia];
    repeat match goal with |- context [Z.of_nat ?n] =>
      let e := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with e end;
    rewrite ?Z.add_0_r;
    [ rewrite (B.ProgWorldCtlRt.mrd_of_aview W m _ _ E0)
    | rewrite (B.ProgWorldCtlRt.mrd_of_aview W m _ _ E1)
    | rewrite (B.ProgWorldCtlRt.mrd_of_aview W m _ _ E2)
    | rewrite (B.ProgWorldCtlRt.mrd_of_aview W m _ _ E3)
    | rewrite (B.ProgWorldCtlRt.mrd_of_aview W m _ _ E4)
    | rewrite (B.ProgWorldCtlRt.mrd_of_aview W m _ _ E5)
    | rewrite (B.ProgWorldCtlRt.mrd_of_aview W m _ _ E6)
    | rewrite (B.ProgWorldCtlRt.mrd_of_aview W m _ _ E7) ];
    f_equal; apply lib.Lib.Mem.Z_to_bv8_mod; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 8) with 256;
    repeat match goal with |- context [2 ^ ?k] =>
      let e := eval vm_compute in (2 ^ k) in change (2 ^ k) with e end.
  - rewrite Z.div_1_r, w0_mod256 by lia. apply Z.mod_small. lia.
  - rewrite (w0_div256 b0) by lia. rewrite w0_mod256 by lia. apply Z.mod_small. lia.
  - change 65536 with (256 * 256). rewrite <- Z.div_div by lia.
    rewrite (w0_div256 b0) by lia. rewrite (w0_div256 b1) by lia. rewrite w0_mod256 by lia. apply Z.mod_small. lia.
  - change 16777216 with (256 * 256 * 256). rewrite <- !Z.div_div by lia.
    rewrite (w0_div256 b0), (w0_div256 b1), (w0_div256 b2) by lia. rewrite w0_mod256 by lia.
    apply Z.mod_small. lia.
  - change 4294967296 with (256 * 256 * 256 * 256). rewrite <- !Z.div_div by lia.
    rewrite (w0_div256 b0), (w0_div256 b1), (w0_div256 b2), (w0_div256 b3) by lia. rewrite w0_mod256 by lia.
    apply Z.mod_small. lia.
  - change 1099511627776 with (256 * 256 * 256 * 256 * 256). rewrite <- !Z.div_div by lia.
    rewrite (w0_div256 b0), (w0_div256 b1), (w0_div256 b2), (w0_div256 b3), (w0_div256 b4) by lia.
    rewrite w0_mod256 by lia. apply Z.mod_small. lia.
  - change 281474976710656 with (256 * 256 * 256 * 256 * 256 * 256). rewrite <- !Z.div_div by lia.
    rewrite (w0_div256 b0), (w0_div256 b1), (w0_div256 b2), (w0_div256 b3), (w0_div256 b4), (w0_div256 b5)
      by lia.
    rewrite w0_mod256 by lia. apply Z.mod_small. lia.
  - change 72057594037927936 with (256 * 256 * 256 * 256 * 256 * 256 * 256). rewrite <- !Z.div_div by lia.
    rewrite (w0_div256 b0), (w0_div256 b1), (w0_div256 b2), (w0_div256 b3), (w0_div256 b4), (w0_div256 b5),
      (w0_div256 b6) by lia.
    rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma w0_wr_at_pres : forall H mem a n, 0 <= a -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> Reusable.YG0n.apresent H mem (a + i)) -> lib.Lib.Mem.wr_at B.Img0.rsegs mem a n.
Proof.
  intros H mem a n H0 H1 HP. split; [exact H0|]. split; [exact H1|].
  intros i Hi. exact (proj1 (w0_pres_raw H mem (a + i) (HP i Hi))).
Qed.

Lemma w0_rng_pres : forall (W : Reusable.YA0n.world segs) mem lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W) mem a) ->
  Lib.ExecF.rng (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W)) lo len.
Proof.
  intros W mem lo len H0 H1 HP. apply B.ProgBridge.rng_RNG_W; [exact H0 | exact H1 |].
  intros a Ha. exact (proj1 (HP a Ha)).
Qed.

(* ---- moving byte facts between memories ---- *)
Lemma w0_bytes_at_eq : forall m m' a bs,
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a bs ->
  (forall i, (i < length bs)%nat ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa (a + Z.of_nat i)) =
     lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa (a + Z.of_nat i))) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H2) HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (HE i Hi). exact (H2 i Hi).
Qed.

Lemma w0_q64_keep : forall m m' a v,
  lib.Lib.Mem.bytes_at B.Img0.rsegs m a (lib.Lib.Mem.le8 (Z_to_bv 64 v)) ->
  (forall i, 0 <= i < 8 ->
     lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa (a + i)) = lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa (a + i))) ->
  lib.Lib.Mem.bytes_at B.Img0.rsegs m' a (lib.Lib.Mem.le8 (Z_to_bv 64 v)).
Proof.
  intros m m' a v H HE. apply (w0_bytes_at_eq m m' a _ H). intros i Hi.
  rewrite lib.Lib.Mem.length_le8 in Hi. apply HE. split; lia.
Qed.

(* a callee-saved register number (YG0d.acallee_saved: 2, 3, 4, 8, 9, 18 .. 27) *)
Local Ltac w0_cs :=
  unfold Reusable.YG0d.acallee_saved;
  first [ left; reflexivity | right; left; reflexivity | do 2 right; left; reflexivity
        | do 3 right; left; reflexivity | do 4 right; left; reflexivity | do 5 right; split; lia ].

Lemma w0_mrd_munch : forall WR m m' a, lib.Lib.Frame.munch WR m m' -> 0 <= a < 2 ^ 64 ->
  lib.Lib.Frame.outside WR a ->
  lib.Lib.Mem.mrd B.Img0.rsegs m' (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa a).
Proof.
  intros WR m m' a HM Ha Ho. unfold lib.Lib.Mem.mrd.
  rewrite (HM (lib.Lib.Mem.wa a)); [reflexivity|]. rewrite lib.Lib.Mem.wa_unsigned by exact Ha. exact Ho.
Qed.

Lemma w0_mrd_view : forall (W : Reusable.YA0n.world segs) mem mem' a,
  Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem' a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H W) mem a ->
  lib.Lib.Mem.mrd B.Img0.rsegs mem' (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd B.Img0.rsegs mem (lib.Lib.Mem.wa a).
Proof.
  intros W mem mem' a Hv E.
  rewrite (B.ProgWorld.aview_vis_mrd W mem' a Hv), (B.ProgWorld.aview_vis_mrd W mem a Hv) in E.
  unfold lib.Lib.Mem.wa.
  destruct (lib.Lib.Mem.mrd B.Img0.rsegs mem' (Z_to_bv 64 a)) as [b'|];
    destruct (lib.Lib.Mem.mrd B.Img0.rsegs mem (Z_to_bv 64 a)) as [b|]; cbn in E; try discriminate E;
    [| reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* a range every byte of which mrd reads holds some byte list of its length *)
Lemma w0_bytes_exist : forall m a n, 0 <= a -> 0 <= n -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> exists b, lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa (a + i)) = Some b) ->
  exists sh, lib.Lib.Mem.bytes_at B.Img0.rsegs m a sh /\ length sh = Z.to_nat n.
Proof.
  intros m a n H0 Hn H1 HR.
  exists (map (fun i : nat => match lib.Lib.Mem.mrd B.Img0.rsegs m (lib.Lib.Mem.wa (a + Z.of_nat i)) with
                              | Some b => b | None => Z_to_bv 8 0 end) (seq 0 (Z.to_nat n))).
  rewrite length_map, length_seq. split; [|reflexivity].
  split; [exact H0|]. rewrite length_map, length_seq. split; [lia|].
  intros i Hi.
  rewrite nth_error_map, nth_error_seq, (proj2 (Nat.ltb_lt i (Z.to_nat n)) Hi). cbn [option_map].
  rewrite Nat.add_0_l. destruct (HR (Z.of_nat i) ltac:(lia)) as (b & Hb). rewrite Hb. reflexivity.
Qed.

(* ---- a live fake frame lies above the image: ProgWorld's ctl_frame_above_img_stmt, from frame_facts (the fake-stack
   area is apart from ly_img) and al_img (ly_img covers B's last segment [0xa2000, 0x5fe000)) ---- *)
Lemma w0_frame_high : forall ly S (W : Reusable.YA0n.world segs) mem md cid pos,
  Reusable.YG0n.AR segs B ly S W mem md -> In (cid, pos) (Reusable.YG01.frames S) ->
  0x5fe000 <= Reusable.YG0f.frame_addr ly cid pos.
Proof.
  intros ly S W mem md cid pos (HM & HL & _) Hin.
  destruct (Reusable.YG0s.frame_facts B ly S _ cid pos HM Hin)
    as (Hcid & _ & HFapp & HFsep & _ & HFoff & _).
  assert (Hsg : exists sg, In sg segs /\ Z.of_N (seg_base sg) = 0xa2000 /\ Z.of_N (seg_size sg) = 0x55c000).
  { assert (Hm : In (0xa2000, 0x55c000) (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs)).
    { change segs with B.Img0.rsegs. rewrite B.ProgBridge.rsegs_spans. right; right; right; left; reflexivity. }
    apply in_map_iff in Hm as (sg & Esg & Hsg). injection Esg as E1 E2. exists sg. auto. }
  destruct Hsg as (sg & Hsg & Eb & Es).
  destruct (Reusable.YG0n.al_img _ _ _ _ HL sg Hsg) as [I1 I2]. rewrite Eb in I1, I2. rewrite Es in I2.
  destruct HFapp as [HF0 _].
  unfold Reusable.YG0f.frame_addr.
  destruct (Z_lt_ge_dec (Reusable.YG0f.ly_F ly) 0x5fe000) as [Hlt|Hge].
  - exfalso. apply HFsep. exists (Z.max (Reusable.YG0f.ly_F ly) 0xa2000).
    unfold Reusable.YG0n.in_zr, Reusable.YG0f.kFakeStackSize. cbn [fst snd]. split; [lia|]. left. lia.
  - pose proof (Z.pow_pos_nonneg 2 20 ltac:(lia) ltac:(lia)) as P20.
    assert (KF : 0 <= Reusable.YG0f.kFakeFramesOff) by (cbv; discriminate).
    assert (KC : 0 <= cid * 2 ^ 20) by (apply Z.mul_nonneg_nonneg; lia).
    lia.
Qed.

(* ---- ctl_rt_C at any state the cut journal reaches (B.ProgWorldCtlRtC.ctl_rt_C_of_AR; the read-only fact carried
   from ctl_base's arodata_okS by APostBase.arodata_ok_journalP) ---- *)
Lemma w0_ctl_rt : forall cx own ly' S' W' m' md' k,
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    own ly' S' W' m' md' k ->
  B.ACtlRtC.ctl_rt_C B ly' S' m'.
Proof.
  intros cx own ly' S' W' m' md' k HB HJ.
  destruct HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROS & _) & _).
  pose proof (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HROS (Z.le_refl _) (Z.le_refl _)) as HRO0.
  pose proof (Reusable.APostBase.arodata_ok_journalP segs RLO RHI RELRO_IMG B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HRO0)
    as HRO.
  exact (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TFIB_SYMS LAWS RLO RHI ly' S' W' m' md' (proj1 HJ) HRO).
Qed.

(* ---- the journal across a call whose post keeps the core's view outside a write set lying in the shadow region (no
   application byte, no image byte), for a journal from an entry without frames (the walk's entry: frames S = [], the
   lib pre).  The stack window stays present because a stack byte is above the image, where the view sees only mem. *)
Lemma w0_journal_view : forall STK sp0 ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wr : Z -> Prop),
  Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  Reusable.YG01.frames S = [] ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a ->
     Reusable.YG0n.aview segs (Reusable.YA0n.w_H Wc) memc' a = Reusable.YG0n.aview segs (Reusable.YA0n.w_H Wc) memc a) ->
  (forall a, Wr a -> Reusable.YG0f.kLowMemEnd <= a < Reusable.YG0f.kHighMemBeg) ->
  Reusable.YG0n.AR segs B lyc Sc Wc memc' mdc' ->
  Reusable.YK04.same_but_materialized mdc mdc' ->
  Reusable.YCbq.ajournal (SK := SK) segs B STK sp0 FP ly S W mem md own lyc Sc Wc memc' mdc' k.
Proof.
  intros STK sp0 ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wr HJ HF0 Heqw HWr HAR' Hsame.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres &
                    Hstatic & F5 & HQT).
  pose proof Hstatic as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop2 & Htop).
  pose proof Reusable.YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (NW : forall a, ~ (Reusable.YG0f.kLowMemEnd <= a < Reusable.YG0f.kHighMemBeg) -> ~ Wr a)
    by (intros a Ha HW; exact (Ha (HWr a HW))).
  split; [exact HAR'|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
  split; [eapply Reusable.YCbq.aos_step_same_io; [exact Hio | apply Reusable.YCbq.same_io_materialized, Hsame]|].
  split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|].
  split.
  { intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply Heqw; [lia|]. apply NW. lia. }
  split.
  { intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
    destruct (Reusable.YG0d.al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2) as (_ & H4096 & Hceilp & Happ & _).
    unfold Reusable.YG0f.in_app in Happ.
    apply Heqw; [lia|]. apply NW. unfold Reusable.YG0f.kLowShadowBeg in Happ. lia. }
  split.
  { intros a Hi Hns He Hsp. rewrite <- (F3 a Hi Hns He Hsp). pose proof (w0_segs_low a Hi) as Hal'.
    apply Heqw; [lia|]. apply NW. lia. }
  split.
  { intros cid pos a Hin. rewrite HF0 in Hin. destruct Hin. }
  split; [exact Hgone|].
  split.
  { intros a Ha. destruct (Hpres a Ha) as (Hh & b & Hb). split; [exact Hh|].
    assert (Ev : Reusable.YG0n.aview segs (Reusable.YA0n.w_H Wc) memc' a =
                 Reusable.YG0n.aview segs (Reusable.YA0n.w_H Wc) memc a) by (apply Heqw; [lia | apply NW; lia]).
    assert (Hm : memc' (Z_to_bv 64 a) <> None).
    { apply (B.ProgWorldCtlRt.mem_some_of_aview_high Wc memc' a); [unfold B.Prog.ImgBounds.IMG_HI; lia|].
      rewrite Ev. unfold Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, Reusable.YK04.mrestrict.
      rewrite Hh, Hb. discriminate. }
    destruct (memc' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; exact (Hm eq_refl)]. }
  split; [exact Hstatic|]. split; [|exact HQT].
  { intros a HXa He. rewrite <- (F5 a HXa He).
    pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
    assert (HXc : Exists (Reusable.YG0n.in_zr a) (Reusable.YG0f.ly_extra lyc)) by (rewrite Eextra; exact HXa).
    pose proof (Reusable.YG0p.AR_extra_law_ok segs B lyc Sc Wc memc mdc a HAR HXc) as (_ & _ & _ & _ & _ & _ & Xapp).
    unfold Reusable.YG0f.app_addr, Reusable.YG0f.kLowShadowBeg in Xapp.
    pose proof (@Reusable.YG0f.ASAN_CEIL_range rc) as [CR _].
    apply Heqw; [unfold Reusable.YG0f.ASAN_CEIL in *; lia|]. apply NW. lia. }
Qed.

(* ---------------------------------------------------------------------------------------------------------
   ENTRY (0x81018, own0, k <= 0) --S_A1--> B81090 (0x81090, own6, k <= 0).
   The exit B810c4 of S_A1 (the D = 0 edge `beqz a2,0x81098` at 0x81080, use-after-return word 0) is dead:
   ctl_rt's asan_cells states UAR 0xa96c0 = 1 (lib/B/AsanRT.v:81; BM4 CLOSED, measured), so a1_pro's run takes
   D = 1 (Seg/A1.v:685-690 drops that premise the same way). *)
Lemma seg_A1 : forall POST, (forall cx p, POST (ACtlCut.cx_set_fpos cx p) = POST cx) ->
  ctl_from POST C_B81090 ->
  ctl_from POST C_B810c4 ->
  ctl_from POST C_ENTRY.
Proof.
  (* 1. The prologue 0x81018 -> 0x3db94 is the narrowed run W0A1N.a1_pro_Fs over the cut's raw memory (the stack
        window [c_sp - LLVMF_STK, c_sp) is present: the journal's stack clause), footprint RNG_W (w_H W3); lifted by
        SRr_fsteps, the journal kept by B.ProgWorld.ajournal_of_fsteps (the writes [sp - 448, sp) are stack bytes).
     2. __asan_stack_malloc_6 at 0x3db94 = pc_stack_malloc (as_code B) 6 (CtrlTSyms' ts_code): the core's
        aj_stack_malloc_at with a Theorem Labs lane's stack_malloc6_contract; the allocator picks the position pos.
     3. The B81090 premise at cx_set_fpos cx pos; the post is moved back to cx by the premise on POST.  Body: the
        prologue's pins kept across the call (aregs_preserved), the saved bytes kept by acall_kept's stack clause, the
        trailer word from the allocation's rdword post (w0_q64_of_rdword); ctl_rt_C by w0_ctl_rt.
     The B810c4 premise (the UAR = 0 edge) is not used: the run reads UAR = 1 from asan_cells. *)
  intros POST HPF H90 _ cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  cbn [ACtlCut.cut_body ACtlCut.cut_own ACtlCut.cut_pc ACtlCut.cut_kmax ACtlCutP.C_ENTRY] in *.
  destruct HBODY as (HPERM & _ & ->).
  pose proof HB as ((HPRE & Hra & H10 & H11 & Hpn & _ & _ & Hfr0 & _) & _).
  destruct HPRE as (_ & _ & _ & Hgp & Htp & _).
  pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & Hk0 & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
  pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof Reusable.YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold Reusable.YCfn.LLVMF_STK in Hpres, Hslo, Hbot.
  assert (HSTP : forall a, ACtlCut.c_sp cx - 32768 <= a < ACtlCut.c_sp cx ->
                           Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a) by exact Hpres.
  destruct HRT as (HAC & _ & _ & _).
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  assert (ST : lib.Lib.Frame.stk B.Img0.rsegs mem3 (ACtlCut.c_sp cx - 32768) (ACtlCut.c_sp cx)).
  { apply (w0_stk_pres (Reusable.YA0n.w_H W3)); [lia | lia | exact HSTP]. }
  assert (R1 : Lib.ExecF.rng RNG (ACtlCut.c_sp cx - 448) 8).
  { apply (w0_rng_pres W3 mem3); [lia | lia |]. intros a Ha. apply HSTP. split; lia. }
  assert (R2 : Lib.ExecF.rng RNG (ACtlCut.c_sp cx - 104) 104).
  { apply (w0_rng_pres W3 mem3); [lia | lia |]. intros a Ha. apply HSTP. split; lia. }
  assert (R3 : Lib.ExecF.rng RNG B.AsanRT.GOT_CELL_K 8)
    by (apply w0_rng_img; unfold B.AsanRT.GOT_CELL_K; lia).
  assert (R4 : Lib.ExecF.rng RNG B.AsanRT.CELL_K 8) by (apply w0_rng_img; unfold B.AsanRT.CELL_K; lia).
  assert (R5 : Lib.ExecF.rng RNG B.AsanRT.GOT_UAR 8) by (apply w0_rng_img; unfold B.AsanRT.GOT_UAR; lia).
  assert (R6 : Lib.ExecF.rng RNG B.AsanRT.UAR 4) by (apply w0_rng_img; unfold B.AsanRT.UAR; lia).
  assert (HLO : 0x10007fff8000 <= ACtlCut.c_sp cx - 32768) by lia.
  assert (HLO2 : ACtlCut.c_sp cx - 32768 + 448 <= ACtlCut.c_sp cx) by lia.
  assert (HSP : ACtlCut.c_sp cx <= 2 ^ 47) by lia.
  pose proof (W0A1N.a1_pro_Fs RNG
     (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 1) (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 2)
     (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 3) (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 4)
     (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 5) (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 6)
     (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 7) (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 8)
     (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 9) (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 10)
     (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 11) (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 12)
     (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 13) (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 14)
     (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 15) (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 16)
     (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 17) (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 18)
     (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 19) (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 20)
     (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 21) (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 22)
     (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 23) (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 24)
     (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 25) (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 26)
     (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 27) (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 28)
     (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 29) (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 30)
     (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 31) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3
     (ACtlCut.c_sp cx - 32768) ST HLO HLO2 HSP HAC R1 R2 R3 R4 R5 R6) as RUN.
  destruct (B.ProgBridge.fevt_of_evtF _ _ _ RUN) as (ms1 & Hrun & HP). clear RUN.
  rewrite B.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of (ACtlCut.c_regs cx)) (ACtlCut.c_regs cx));
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv (ACtlCut.c_regs cx)))].
  apply (Reusable.YA0nR.SRr_fsteps segs Hwx W3 _ ms1 md3 RNG (POST cx) Hrun (B.ProgBridge.fp_avoids_RNG_W _)).
  intros md1 Hsame1.
  destruct HP as (ra' & sp' & a0' & a1' & a2' & s10' & m1 & -> & Era & Esp & Ea0 & Es10 & MU & WM & ST1 & SB).
  set (S := ACtlCut.c_sp cx) in *.
  change (bv_unsigned (lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 2)) with S in *.
  (* the journal across the prologue: its writes [S - 448, S) are stack-window bytes *)
  assert (Hawr : forall a, 0 <= a < 2 ^ 64 -> ~ lib.Lib.Frame.outside [(S - 448, S)] a ->
            Reusable.YCbq.awr_byte Reusable.YCfn.LLVMF_STK S FP
              (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3) ly3
              (ACtlCut.own0 cx) a).
  { intros a Ha Ho. cbn [lib.Lib.Frame.outside] in Ho. left. unfold Reusable.YCfn.LLVMF_STK.
    destruct (Z_lt_ge_dec a (S - 448)) as [D1|D1]; [exfalso; apply Ho; split; [lia | exact I]|].
    destruct (Z_lt_ge_dec a S) as [D2|D2]; [split; lia | exfalso; apply Ho; split; [lia | exact I]]. }
  lazymatch type of Hrun with Reusable.YK04R.fsteps _ _ ?m0 _ =>
    pose proof (B.ProgWorld.ajournal_of_fsteps (SK := SK) B LAWS Hwx _ _ FP _ _ _ _ _ _ _ _ _ m0 _ _ md1 k RNG
                  [(S - 448, S)] HJ Hrun (B.ProgBridge.fp_avoids_RNG_W _) MU Hsame1 Hawr) as HJ1 end.
  cbn [ms_mem lib.Lib.MState.MS] in HJ1.
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
  unfold Reusable.YCfn.LLVMF_STK in Hpres1.
  (* the fake-stack request: the core's aj_stack_malloc_at with a Theorem Labs lane's contract *)
  assert (PC6 : Reusable.YG0f.pc_stack_malloc (Reusable.YG0f.as_code B) 6 = 0x3db94)
    by (rewrite (Reusable.YF0m.ts_code B TFIB_SYMS); vm_compute; reflexivity).
  assert (ENV : Reusable.YCbq.api_env segs B).
  { unfold Reusable.YCbq.api_env. rewrite (Reusable.YF0m.ts_errno B TFIB_SYMS), (Reusable.YF0m.ts_code B TFIB_SYMS).
    unfold Reusable.YF0m.TFIB_ERRNO, Reusable.YG0f.kLowMemEnd.
    split; [split; lia|]. split.
    { intros a Ha. assert (Hm : In (0xa2000, 0x55c000)
        (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs)).
      { change segs with B.Img0.rsegs. rewrite B.ProgBridge.rsegs_spans. right; right; right; left; reflexivity. }
      apply in_map_iff in Hm as (sg & Esg & Hsg). injection Esg as E1 E2.
      exists sg. split; [exact Hsg | lia]. }
    split; apply (Reusable.YF0m.ts_universe_drv B TFIB_SYMS); vm_compute; tauto. }
  pose proof (Reusable.YG05.model_laws_ok _ (Reusable.YF0m.ts_universe B TFIB_SYMS)) as ML.
  assert (SMP : Reusable.YCbq.stack_malloc_progressP B)
    by (intros s cid; exact (Reusable.YG05.stack_malloc_progress (Reusable.YG0f.as_universe B) s cid)).
  lazymatch goal with |- context [lib.Lib.MState.MS ?R _ _ _ _ _ _] => set (RT := R) end.
  assert (ESR : Reusable.YG0d.spZ RT = bv_unsigned sp') by reflexivity.
  pose proof (Z.div_mod (S - 448) 32 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound (S - 448) 32 ltac:(lia)) as Dr.
  rewrite <- PC6.
  eapply Reusable.YA0n.SRr_bind.
  { exact (Reusable.YCbq.aj_stack_malloc_at (SK := SK) segs B LAWS w0_segs_low ENV ML SMP 6
             (stack_malloc6_contract LAWS USYMS) ltac:(split; lia) W3 RT m1 Reusable.YCfn.LLVMF_STK S FP
             (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) []
             ly3 S3 md1 k (bv_unsigned sp' - S) (Z_to_bv 64 0x81090) HJ1
             ltac:(rewrite ESR; lia) ltac:(rewrite Esp; Z.div_mod_to_equations; lia) ltac:(lia)
             ltac:(unfold Reusable.YG0d.ESTACK, Reusable.YCfn.LLVMF_STK; lia)
             Hgp Htp Era ltac:(unfold lib.Reusable.YK0s.ret_ok; vm_compute; reflexivity)
             ltac:(rewrite Hfr; vm_compute; reflexivity)). }
  intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & Hpr & H10' & Eab & Efr2 & Hnin & Hnev & Hbb &
                  Hzs & Htrl & Hkept).
  (* the B81090 premise at the allocated position; the post does not read the position *)
  rewrite <- (HPF cx pos).
  pose proof HJ2 as (HAR2 & _).
  assert (Hin2 : In (6, pos) (Reusable.YG01.frames S2)) by (rewrite Efr2; left; reflexivity).
  pose proof Hly as (_ & _ & _ & _ & _ & ElyF & _).
  assert (EF : Reusable.YG0f.frame_addr ly3 6 pos = Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) 6 pos)
    by (unfold Reusable.YG0f.frame_addr; rewrite ElyF; reflexivity).
  assert (EFL : Reusable.YG0f.flag_addr ly3 6 pos = Reusable.YG0f.flag_addr (ACtlCut.c_ly cx) 6 pos)
    by (unfold Reusable.YG0f.flag_addr; rewrite ElyF; reflexivity).
  pose proof (Reusable.YCbq.frames_bounds segs B LAWS ly3 S2 W3 mem2 md2 6 pos HAR2 Hin2) as (FB1 & FB2 & _).
  pose proof (Reusable.YG0d.al_flag segs B LAWS ly3 S2 W3 mem2 md2 6 pos HAR2 Hin2) as (_ & _ & FL1 & FL2).
  unfold Reusable.YG0f.in_app in FL1.
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in FB2, Htrl.
  set (fr' := Reusable.YG0f.frame_addr ly3 6 pos) in *.
  apply (H90 (ACtlCut.cx_set_fpos cx pos) [] fr' k ly3 S2 W3 regs2 mem2 md2 HB HJ2);
    [ rewrite Efr2, Hfr; reflexivity
    | intros cid p' [E|[]]; injection E as <- <-; exact EF
    | exact Hk
    |
    | exact (w0_ctl_rt (ACtlCut.cx_set_fpos cx pos) _ ly3 S2 W3 mem2 md2 k HB HJ2) ].
  cbn [ACtlCut.cut_body ACtlCutP.C_B81090 ACtlCut.cx_set_fpos ACtlCut.c_ly ACtlCut.c_S ACtlCut.c_p ACtlCut.c_n
       ACtlCut.c_fpos ACtlCut.c_regs].
  change (ACtlCut.c_sp (ACtlCut.mkCtlCx (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_regs cx)
            (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.c_p cx) (ACtlCut.c_n cx) (ACtlCut.c_in cx)
            (ACtlCut.c_M cx) pos (ACtlCut.c_sp1 cx))) with S.
  (* registers across the call *)
  assert (Hpr' : forall r, Reusable.YG0d.acallee_saved r ->
                   lib.Reusable.YK11.getr regs2 (Z_to_bv 5 r) = lib.Reusable.YK11.getr RT (Z_to_bv 5 r))
    by exact Hpr.
  assert (E2 : lib.Reusable.YK11.getr regs2 2 = sp')
    by (transitivity (lib.Reusable.YK11.getr RT 2); [exact (Hpr' 2 ltac:(w0_cs)) | reflexivity]).
  assert (E3 : lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 3)
    by (transitivity (lib.Reusable.YK11.getr RT 3); [exact (Hpr' 3 ltac:(w0_cs)) | reflexivity]).
  assert (E4 : lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 4)
    by (transitivity (lib.Reusable.YK11.getr RT 4); [exact (Hpr' 4 ltac:(w0_cs)) | reflexivity]).
  assert (E8 : lib.Reusable.YK11.getr regs2 8 = lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 2)
    by (transitivity (lib.Reusable.YK11.getr RT 8); [exact (Hpr' 8 ltac:(w0_cs)) | reflexivity]).
  assert (E9 : lib.Reusable.YK11.getr regs2 9 = sp')
    by (transitivity (lib.Reusable.YK11.getr RT 9); [exact (Hpr' 9 ltac:(w0_cs)) | reflexivity]).
  assert (E18 : lib.Reusable.YK11.getr regs2 18 = lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 11)
    by (transitivity (lib.Reusable.YK11.getr RT 18); [exact (Hpr' 18 ltac:(w0_cs)) | reflexivity]).
  assert (E22 : lib.Reusable.YK11.getr regs2 22 = lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 10)
    by (transitivity (lib.Reusable.YK11.getr RT 22); [exact (Hpr' 22 ltac:(w0_cs)) | reflexivity]).
  assert (E26 : lib.Reusable.YK11.getr regs2 26 = s10')
    by (transitivity (lib.Reusable.YK11.getr RT 26); [exact (Hpr' 26 ltac:(w0_cs)) | reflexivity]).
  assert (EA : bv_unsigned sp' = 32 * ((S - 448) / 32)) by lia.
  pose proof (Z.div_mod S 16 ltac:(lia)) as DS.
  assert (ERA : lib.Reusable.YK11.getr (ACtlCut.c_regs cx) 1 = Z_to_bv 64 Reusable.YCfn.RA_LLVMF).
  { rewrite <- Hra. unfold Reusable.YG0d.raZ. symmetry. apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. }
  rewrite ERA in SB.
  unfold ACtlCut.a0v, ACtlCut.rgv.
  split; [rewrite Eab; exact HPERM|]. split.
  { exists (bv_unsigned sp'), (bv_unsigned sp'). unfold ACtlCut.rgv, Reusable.YG0d.spZ.
    rewrite E2, E3, E4, E8, E9, E26.
    split; [symmetry; apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned|].
    split; [rewrite EA; replace (32 * ((S - 448) / 32)) with (2 * ((S - 448) / 32) * 16) by lia;
            apply Z_mod_mult|].
    split; [reflexivity|]. split; [exact Htp|].
    split; [symmetry; apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned|].
    split; [symmetry; apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned|].
    split; [reflexivity|]. split; [exact Es10|].
    split; [rewrite EA; rewrite Z.mul_comm; apply Z_mod_mult|].
    change (ACtlCut.c_sp (ACtlCut.cx_set_fpos cx pos)) with S.
    change (ACtlCut.c_n (ACtlCut.cx_set_fpos cx pos)) with (ACtlCut.c_n cx).
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [unfold ACtlCutP.ART.APPMEM_END, B.AsanRT.APPMEM_END; lia|].
    split.
    { refine (w0_bytes_at_eq m1 mem2 (S - 104) _ SB _).
      intros i Hi. rewrite !length_app, !lib.Lib.Mem.length_le8 in Hi. cbn in Hi.
      apply (w0_mrd_view W3 m1 mem2); [exact (proj1 (Hpres1 (S - 104 + Z.of_nat i) ltac:(split; lia)))|].
      destruct Hkept as (HK1 & _). apply HK1; [split; lia | unfold Reusable.YG0d.ESTACK; lia]. }
    unfold ACtlK.ANMAX. destruct Hpn as [[-> _] | [[H1 H2] _]]; lia. }
  split; [exact H10'|]. split; [split; lia|].
  split; [rewrite E22; exact H10|]. split; [rewrite E18; exact H11|].
  rewrite <- EFL. apply (w0_q64_of_rdword W3 mem2); [lia | lia | split; lia |].
  replace (fr' + 4088) with (fr' + 4096 - 8) by lia. exact Htrl.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B81090 (0x81090, own6, k <= 0) --S_A2--> B810c4 (0x810c4, own6, k <= 0).
   With G2, a0 = sel = fr = frame_addr (c_ly cx) 6 (c_fpos cx) (G1) and fr <> 0, so `bnez s8,0x810c4` (0x810a0)
   is taken: only the fake-frame arm a2_side_evt runs.  The real-stack arm (a2_real_evt, probe loop
   0x810b4-0x810bc) is the class-full arm, discharged at ENTRY's fake-stack call (ACtlCutP header, section 3). *)
Lemma seg_A2 : forall POST,
  ctl_from POST C_B810c4 ->
  ctl_from POST C_B81090.
Proof.
  (* The run 0x81090 -> 0x810c4 is A2F.a2_side_evt_F (Seg/A2.v:112): register moves only, so the footprint is
     RNG_W (w_H W3), which avoids the hidden set by construction.  fr <> 0 because the frame lies above 4096
     (w0_own6_frame).  Memory is unchanged, so the journal, the trailer word and ctl_rt carry over; the model is
     only materialized (w0_journal_mat). *)
  intros POST HC4 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  cbn [ACtlCut.cut_body ACtlCut.cut_own ACtlCut.cut_pc ACtlCut.cut_kmax ACtlCutP.C_B81090] in *.
  destruct HBODY as (HPERM & HPREF & Ha0 & Hfr64 & H22 & H18 & HTRL).
  destruct (w0_own6_frame cx fr ly3 S3 W3 mem3 md3 k HJ Hfr HFA) as (_ & _ & Hlo & _ & Hal).
  assert (Hnz : fr mod 2 ^ 64 <> 0) by (rewrite Z.mod_small by lia; lia).
  rewrite B.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3);
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  apply (Reusable.YA0nR.SRr_fevt segs Hwx W3 _ md3 (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) _ (POST cx)
           (B.ProgBridge.fevt_of_evtF _ _ _
              (A2F.a2_side_evt_F (B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)) regs3
                 lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3 fr Ha0 Hnz))
           (B.ProgBridge.fp_avoids_RNG_W _)).
  intros ms' md' (R & -> & E25 & E24 & E2 & E3 & E4 & E8 & E9 & E26 & E22 & E18) Hsame.
  pose proof (HC4 cx [] fr k ly3 S3 W3 R mem3 md' HB (w0_journal_mat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hsame)
                Hfr HFA Hk) as HC.
  rewrite B.ProgBridge.cfg_at_MS in HC.
  apply HC; [| exact HRT]. clear HC.
  cbn [ACtlCut.cut_body ACtlCutP.C_B810c4].
  assert (E2' : lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2) by exact E2.
  assert (E3' : lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3) by exact E3.
  assert (E4' : lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4) by exact E4.
  assert (E8' : lib.Reusable.YK11.getr R 8 = lib.Reusable.YK11.getr regs3 8) by exact E8.
  assert (E9' : lib.Reusable.YK11.getr R 9 = lib.Reusable.YK11.getr regs3 9) by exact E9.
  assert (E26' : lib.Reusable.YK11.getr R 26 = lib.Reusable.YK11.getr regs3 26) by exact E26.
  assert (E22' : lib.Reusable.YK11.getr R 22 = lib.Reusable.YK11.getr regs3 22) by exact E22.
  assert (E18' : lib.Reusable.YK11.getr R 18 = lib.Reusable.YK11.getr regs3 18) by exact E18.
  split; [exact HPERM|]. split.
  - destruct HPREF as (A & sp & HP). exists A, sp.
    unfold ACtlCut.rgv, Reusable.YG0d.spZ in HP |- *.
    rewrite E2', E3', E4', E8', E9', E26'. exact HP.
  - exists (fr + ACtlCutP.FRAME_BYTES). unfold ACtlCut.rgv in *.
    split; [exact E25|]. split; [exact Hal|]. split; [exact E24|]. split; [exact Hfr64|].
    split; [lia|]. split; [rewrite E22'; exact H22|]. split; [rewrite E18'; exact H18|]. exact HTRL.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   B810c4 (0x810c4, own6, k <= 0) --S_A3--> B81220 (0x81220, own6, k <= 0).
   The frame header writes ([A + 336] := fr, [fr] := 0x41b58ab3, [fr + 8] := 0x17e9c, [fr + 16] := 0x81018), the 68
   one-byte shadow stores into S(fr) .. S(fr) + 67, then __asan_set_shadow_f8 (S(fr) + 68, 187) @0x8121c
   (callee 0x55144), returning at 0x81220.  The early edge to Jrel (n >= 2^26) belongs to S_A4, not here. *)
Lemma seg_A3 : forall POST,
  ctl_from POST C_B81220 ->
  ctl_from POST C_B810c4.
Proof.
  (* 1. The run 0x810c4 -> 0x55144 is the owner's narrowed run A3F.a3_evt_pre_F_on (Seg/A3F.v:267) over the cut's
        raw memory, footprint RNG_W (w_H W3).  Its premises: s1 = A, s9 = fr, s10 = ASAN_K from PREFC / the body;
        GT <= fr because a live fake frame lies above the image (w0_frame_high); fr + 3136 <= A because the frame ends
        below alloc_ceiling <= ly_stk_lo and A is in the stack window; the frame and its shadow are present by AR's
        frame law, the spill slot by the journal's stack clause (raw bytes: w0_pres_raw); asan_cells / ro_agree from
        ctl_rt_C, and shadow_rw_on over the stored frame shadow [S(fr), S(fr) + 68) (A3F.a3_evt_pre_F_shadow_R fr)
        from ctl_rt_C's cut_shadow conjunct (the frame (6, c_fpos cx) is in frames S3).  Its post carries
        shadow_rw_on transport (forall P, shadow_rw_on P m -> shadow_rw_on P m'); the exit does not need it
        (w0_ctl_rt rebuilds ctl_rt_C from AR).
     2. SRr_fsteps lifts the run; B.ProgWorld.ajournal_of_fsteps keeps the journal (writes: the spill slot, in the
        stack window, and the owned frame and its shadow, in_frames).
     3. The call to __asan_set_shadow_f8 (q = S(fr) + 68, n = 187) through a Theorem Labs lane's contract set_shadow_f8; its
        post keeps the view outside [q, q + n), so w0_journal_view rebuilds the journal (no presence clause is
        needed: the written bytes are shadow bytes, every stack byte lies above the image).
     4. C_B81220's body: registers by aregs_preserved and the run's post; the byte facts by munch (run) and the view
        frame clause read through B.ProgWorld.aview_vis_mrd (call); the 392 shadow bytes are present in the post
        state by AR's frame law; ctl_rt_C by w0_ctl_rt. *)
  intros POST H220 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ Hfr HFA Hk HBODY HRT.
  cbn [ACtlCut.cut_body ACtlCut.cut_own ACtlCut.cut_pc ACtlCut.cut_kmax ACtlCutP.C_B810c4] in *.
  destruct HBODY as (HPERM & HPREF & A' & H25 & Hal' & H24 & Hfr64 & HA' & H22 & H18 & HTRL).
  destruct HPREF as (A & sp & P2 & P16 & Psp & P4 & P8 & P9 & P3 & P26 & PA32 & PAS & PAlo & PspA & PA448 &
                     Psplo & PSapp & PSAV & PN).
  destruct (w0_own6_frame cx fr ly3 S3 W3 mem3 md3 k HJ Hfr HFA) as (Hin & Efr & Hlo & Hhi & Hal).
  pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
  pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof Reusable.YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (w0_frame_high ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin) as Hgt. rewrite <- Efr in Hgt.
  pose proof (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (_ & Happ & HFP & HFSP).
  change (Reusable.YG00.fs_frame_bytes 6) with 4096 in Happ, HFP, HFSP. rewrite <- Efr in Happ, HFP, HFSP.
  unfold Reusable.YCfn.LLVMF_STK in Hpres, Hslo, Hbot.
  pose proof (@Reusable.YG0f.ASAN_CEIL_range rc) as [CR _].
  unfold Reusable.YG0f.in_app, Reusable.YG0f.kLowShadowBeg, Reusable.YG0f.kHighMemBeg, Reusable.YG0f.ASAN_CEIL
    in Happ.
  assert (ESh : Reusable.YG0f.shadow_addr fr = ACtlCutP.Sfr fr)
    by (unfold Reusable.YG0f.shadow_addr, ACtlCutP.Sfr, B.AsanRT.shadow_addr, Reusable.YG0f.SHADOW_OFF,
          B.AsanRT.ASAN_K; lia).
  rewrite ESh in HFSP. change (4096 / 8) with 512 in HFSP.
  assert (HSb : (B.AsanRT.LOWMEM_END <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 512 <= B.AsanRT.LOWSHADOW_END /\
                 fr + 4096 <= ACtlCutP.Sfr fr) \/
                (B.AsanRT.HIGHSHADOW_BEG <= ACtlCutP.Sfr fr /\ ACtlCutP.Sfr fr + 512 <= B.AsanRT.HIGHMEM_BEG /\
                 ACtlCutP.Sfr fr + 512 <= fr)).
  { unfold ACtlCutP.Sfr, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END,
           B.AsanRT.HIGHSHADOW_BEG, B.AsanRT.HIGHMEM_BEG.
    pose proof (Z.div_mod fr 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound fr 8 ltac:(lia)) as Dr.
    destruct Happ as [_ [Hl | [Hh1 Hh2]]]; [left | right].
    - split; [lia|]. split; lia.
    - split; [lia|]. split; lia. }
  (* the spill base A lies on the stack, above the fake frame and the shadow *)
  assert (HfrA : fr + 3136 <= A) by lia.
  set (RNG := B.ProgBridge.RNG_W (Reusable.YA0n.w_H W3)).
  destruct HRT as (HAC & HSWC & _ & HRO).
  assert (HSh : forall i, 0 <= i < 392 -> B.AsanRT.in_shadow (ACtlCutP.Sfr fr + i)).
  { intros i Hi. unfold B.AsanRT.in_shadow.
    destruct HSb as [HSb|HSb]; [left | right]; split; lia. }
  assert (HSHP : forall a, ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 512 ->
                           Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a).
  { intros a Ha. replace a with (ACtlCutP.Sfr fr + (a - ACtlCutP.Sfr fr)) by lia.
    apply (HFSP (a - ACtlCutP.Sfr fr)). split; lia. }
  assert (HFRP : forall a, fr <= a < fr + 4096 -> Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a)
    by (intros a Ha; exact (proj1 (HFP a Ha))).
  assert (HSTP : forall a, ACtlCut.c_sp cx - 32768 <= a < ACtlCut.c_sp cx ->
                           Reusable.YG0n.apresent (Reusable.YA0n.w_H W3) mem3 a) by exact Hpres.
  assert (WF : lib.Lib.Mem.wr_at B.Img0.rsegs mem3 fr 24).
  { apply (w0_wr_at_pres (Reusable.YA0n.w_H W3) mem3 fr 24); [lia | lia |]. intros i Hi. apply HFRP. split; lia. }
  assert (WA : lib.Lib.Mem.wr_at B.Img0.rsegs mem3 (A + 336) 8).
  { apply (w0_wr_at_pres (Reusable.YA0n.w_H W3) mem3 (A + 336) 8); [lia | lia |].
    intros i Hi. apply HSTP. split; lia. }
  assert (RA : Lib.ExecF.rng RNG (A + 336) 8).
  { apply (w0_rng_pres W3 mem3); [lia | lia |]. intros a Ha. apply HSTP. split; lia. }
  assert (RF : Lib.ExecF.rng RNG fr 24).
  { apply (w0_rng_pres W3 mem3); [lia | lia |]. intros a Ha. apply HFRP. split; lia. }
  assert (RS : Lib.ExecF.rng RNG (ACtlCutP.Sfr fr) 68).
  { apply (w0_rng_pres W3 mem3);
      [| | intros a Ha; apply HSHP; split; lia];
      destruct HSb as [X|X];
      cbv [B.AsanRT.LOWMEM_END B.AsanRT.LOWSHADOW_END B.AsanRT.HIGHSHADOW_BEG B.AsanRT.HIGHMEM_BEG] in X; lia. }
  assert (HGT : B.Contract.GT <= fr) by (unfold B.Contract.GT; lia).
  assert (HAhi : B.AsanRT.HIGHMEM_BEG <= A) by (unfold B.AsanRT.HIGHMEM_BEG; lia).
  assert (HA64 : A + 344 <= 2 ^ 64) by lia.
  assert (Hsep : fr + 3136 <= B.AsanRT.LOWMEM_END \/ B.AsanRT.HIGHMEM_BEG <= fr).
  { unfold B.AsanRT.LOWMEM_END, B.AsanRT.HIGHMEM_BEG. destruct Happ as [_ [Hl | [Hh1 Hh2]]]; [left | right]; lia. }
  (* route (C): the run stores only into the frame shadow [S(fr), S(fr) + 68) (A3F.a3_evt_pre_F_shadow_R fr); the
     cut's ctl_rt_C gives shadow_rw_on over the shadow of every frame in frames S3, and (6, c_fpos cx) is one of them
     with base fr *)
  assert (HSWP : B.ShadowRwOn.shadow_rw_on (B.Prog.Seg.A3F.a3_evt_pre_F_shadow_R fr) mem3).
  { apply (B.ShadowRwOn.shadow_rw_on_mono (B.ACtlRtC.cut_shadow B ly3 S3) _ mem3); [|exact HSWC].
    intros a Ha. change (ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 68) in Ha.
    left. exists 6, (ACtlCut.c_fpos cx). split; [exact Hin|].
    rewrite <- Efr, ESh. change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512. lia. }
  pose proof (B.Prog.Seg.A3F.a3_evt_pre_F_on RNG
     (lib.Reusable.YK11.getr regs3 1) (lib.Reusable.YK11.getr regs3 2) (lib.Reusable.YK11.getr regs3 3)
     (lib.Reusable.YK11.getr regs3 4) (lib.Reusable.YK11.getr regs3 5) (lib.Reusable.YK11.getr regs3 6)
     (lib.Reusable.YK11.getr regs3 7) (lib.Reusable.YK11.getr regs3 8) (lib.Reusable.YK11.getr regs3 9)
     (lib.Reusable.YK11.getr regs3 10) (lib.Reusable.YK11.getr regs3 11) (lib.Reusable.YK11.getr regs3 12)
     (lib.Reusable.YK11.getr regs3 13) (lib.Reusable.YK11.getr regs3 14) (lib.Reusable.YK11.getr regs3 15)
     (lib.Reusable.YK11.getr regs3 16) (lib.Reusable.YK11.getr regs3 17) (lib.Reusable.YK11.getr regs3 18)
     (lib.Reusable.YK11.getr regs3 19) (lib.Reusable.YK11.getr regs3 20) (lib.Reusable.YK11.getr regs3 21)
     (lib.Reusable.YK11.getr regs3 22) (lib.Reusable.YK11.getr regs3 23) (lib.Reusable.YK11.getr regs3 24)
     (lib.Reusable.YK11.getr regs3 25) (lib.Reusable.YK11.getr regs3 26) (lib.Reusable.YK11.getr regs3 27)
     (lib.Reusable.YK11.getr regs3 28) (lib.Reusable.YK11.getr regs3 29) (lib.Reusable.YK11.getr regs3 30)
     (lib.Reusable.YK11.getr regs3 31) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem3 A fr
     P9 H25 P26 HGT HfrA HAhi HA64 Hsep HSh WF WA HSWP HRO HAC RA RF RS) as RUN.
  (* the lift: SRr_fsteps over the run, the journal across it by ProgWorld.ajournal_of_fsteps *)
  destruct (B.ProgBridge.fevt_of_evtF _ _ _ RUN) as (ms1 & Hrun & HP). clear RUN.
  rewrite B.ProgBridge.cfg_at_MS.
  apply (Reusable.YA0nR.SRr_xregs_eqv segs W3 (lib.Lib.Regs6ss.mkR_of regs3) regs3);
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs3))].
  apply (Reusable.YA0nR.SRr_fsteps segs Hwx W3 _ ms1 md3 RNG (POST cx) Hrun (B.ProgBridge.fp_avoids_RNG_W _)).
  intros md1 Hsame1.
  destruct HP as (R & m1 & -> & G1 & G10 & G11 & G2 & G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G24 &
                  G25 & G26 & G27 & MU & WM & RO1 & SWT1 & AC1 & Q336 & Qhdr & Q8 & Q16).
  set (WR := [(A + 336, A + 344); (fr, fr + 24); (ACtlCutP.Sfr fr, ACtlCutP.Sfr fr + 392)]).
  assert (Hawr : forall a, 0 <= a < 2 ^ 64 -> ~ lib.Lib.Frame.outside WR a ->
            Reusable.YCbq.awr_byte Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
              (Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) (Reusable.YG0d.ablocks B ly3 S3) ly3
              (ACtlCut.own6 cx) a).
  { intros a Ha Ho. unfold WR in Ho. cbn [lib.Lib.Frame.outside] in Ho.
    assert (HD : (A + 336 <= a < A + 344) \/ (fr <= a < fr + 24) \/
                 (ACtlCutP.Sfr fr <= a < ACtlCutP.Sfr fr + 392)).
    { destruct (Z_lt_ge_dec a (A + 336)) as [D1|D1]; [|destruct (Z_lt_ge_dec a (A + 344)) as [D2|D2];
        [left; split; lia|]];
      (destruct (Z_lt_ge_dec a fr) as [D3|D3]; [|destruct (Z_lt_ge_dec a (fr + 24)) as [D4|D4];
        [right; left; split; lia|]]);
      (destruct (Z_lt_ge_dec a (ACtlCutP.Sfr fr)) as [D5|D5]; [|destruct (Z_lt_ge_dec a (ACtlCutP.Sfr fr + 392))
        as [D6|D6]; [right; right; split; lia|]]);
      exfalso; apply Ho; repeat split; try exact I; lia. }
    unfold Reusable.YCbq.awr_byte, Reusable.YCbq.in_frames, Reusable.YCfn.LLVMF_STK.
    destruct HD as [HD|[HD|HD]].
    - left. split; lia.
    - right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. left.
      unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr. change (Reusable.YG00.fs_frame_bytes 6) with 4096.
      split; lia.
    - right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. right.
      unfold Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr, ESh.
      change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512. split; lia. }
  lazymatch type of Hrun with Reusable.YK04R.fsteps _ _ ?m0 _ =>
    pose proof (B.ProgWorld.ajournal_of_fsteps (SK := SK) B LAWS Hwx _ _ FP _ _ _ _ _ _ _ _ _ m0 _ _ md1 k RNG WR
                  HJ Hrun (B.ProgBridge.fp_avoids_RNG_W _) MU Hsame1 Hawr) as HJ1 end.
  cbn [ms_mem lib.Lib.MState.MS] in HJ1.
  (* core register facts of the run's end state *)
  assert (G1' : lib.Reusable.YK11.getr R 1 = Z_to_bv 64 0x81220) by exact G1.
  assert (G2' : lib.Reusable.YK11.getr R 2 = lib.Reusable.YK11.getr regs3 2) by exact G2.
  assert (G3' : lib.Reusable.YK11.getr R 3 = lib.Reusable.YK11.getr regs3 3) by exact G3.
  assert (G4' : lib.Reusable.YK11.getr R 4 = lib.Reusable.YK11.getr regs3 4) by exact G4.
  assert (ESR : Reusable.YG0d.spZ R = sp) by (unfold Reusable.YG0d.spZ in *; rewrite G2'; exact Psp).
  pose proof HB as ((HPRE & _ & _ & _ & _ & _ & _ & Hfr0 & _) & _).
  destruct HPRE as (_ & _ & _ & Hgp & Htp & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
  unfold Reusable.YCfn.LLVMF_STK in Hpres1.
  assert (EC : Reusable.YG0d.ecall_pre segs B ly3 S3 W3 R m1 md1).
  { split; [exact (proj1 HJ1)|]. split.
    { unfold lib.Reusable.YK0s.ret_ok. rewrite G1'. vm_compute. reflexivity. }
    rewrite ESR, Eslo, Eshi. unfold Reusable.YG0d.ESTACK.
    split; [exact P16|]. split; [lia|]. split; [lia|].
    split; [intros a Ha; apply Hpres1; split; lia|].
    split; [rewrite G3', P3; exact Hgp | rewrite G4'; exact P4]. }
  assert (Hq1 : Reusable.YG0f.shadow_addr (Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)) <=
                ACtlCutP.Sfr fr + 68) by (rewrite <- Efr, ESh; lia).
  assert (Hq2 : ACtlCutP.Sfr fr + 68 + 187 <=
                Reusable.YG0f.shadow_addr (Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx)) +
                Reusable.YG00.fs_frame_bytes 6 / 8)
    by (rewrite <- Efr, ESh; change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512; lia).
  pose proof (set_shadow_f8 LAWS USYMS ly3 S3 W3 R m1 md1 6 (ACtlCut.c_fpos cx) (ACtlCutP.Sfr fr + 68) 187
                EC Hin G10 G11 ltac:(lia) Hq1 Hq2) as HSS.
  eapply Reusable.YA0n.SRr_bind; [exact HSS|].
  intros W' c' _ (-> & regs' & mem2 & md2 & -> & HAR2 & Hpr & Hsame2 & Hval & Hfrm & Hwin).
  replace (Reusable.YG0d.raZ R) with 0x81220
    by (unfold Reusable.YG0d.raZ; rewrite G1'; reflexivity).
  (* the journal across the call: its writes are frame-shadow bytes only *)
  assert (HJ2 : Reusable.YCbq.ajournal (SK := SK) segs B Reusable.YCfn.LLVMF_STK (ACtlCut.c_sp cx) FP
                  (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
                  (ACtlCut.own6 cx) ly3 S3 W3 mem2 md2 k).
  { apply (w0_journal_view _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             (fun a => ACtlCutP.Sfr fr + 68 <= a < ACtlCutP.Sfr fr + 68 + 187) HJ1 Hfr0 Hfrm);
      [| exact HAR2 | exact Hsame2].
    intros a Ha. rewrite C3, C5.
    destruct HSb as [X|X];
      cbv [B.AsanRT.LOWMEM_END B.AsanRT.LOWSHADOW_END B.AsanRT.HIGHSHADOW_BEG B.AsanRT.HIGHMEM_BEG] in X;
      split; lia. }
  apply (H220 cx [] fr k ly3 S3 W3 regs' mem2 md2 HB HJ2 Hfr HFA Hk);
    [| exact (w0_ctl_rt cx _ ly3 S3 W3 mem2 md2 k HB HJ2)].
  cbn [ACtlCut.cut_body ACtlCutP.C_B81220].
  (* registers across the call (callee-saved, aregs_preserved) *)
  assert (Hpr' : forall r, Reusable.YG0d.acallee_saved r ->
                   lib.Reusable.YK11.getr regs' (Z_to_bv 5 r) = lib.Reusable.YK11.getr R (Z_to_bv 5 r))
    by exact Hpr.
  assert (E2 : lib.Reusable.YK11.getr regs' 2 = lib.Reusable.YK11.getr regs3 2)
    by (rewrite <- G2'; exact (Hpr' 2 ltac:(w0_cs))).
  assert (E3 : lib.Reusable.YK11.getr regs' 3 = lib.Reusable.YK11.getr regs3 3)
    by (rewrite <- G3'; exact (Hpr' 3 ltac:(w0_cs))).
  assert (E4 : lib.Reusable.YK11.getr regs' 4 = lib.Reusable.YK11.getr regs3 4)
    by (rewrite <- G4'; exact (Hpr' 4 ltac:(w0_cs))).
  assert (E8 : lib.Reusable.YK11.getr regs' 8 = lib.Reusable.YK11.getr regs3 8)
    by (transitivity (lib.Reusable.YK11.getr R 8); [exact (Hpr' 8 ltac:(w0_cs)) | exact G8]).
  assert (E9 : lib.Reusable.YK11.getr regs' 9 = lib.Reusable.YK11.getr regs3 9)
    by (transitivity (lib.Reusable.YK11.getr R 9); [exact (Hpr' 9 ltac:(w0_cs)) | exact G9]).
  assert (E18 : lib.Reusable.YK11.getr regs' 18 = lib.Reusable.YK11.getr regs3 18)
    by (transitivity (lib.Reusable.YK11.getr R 18); [exact (Hpr' 18 ltac:(w0_cs)) | exact G18]).
  assert (E19 : lib.Reusable.YK11.getr regs' 19 = Z_to_bv 64 (ACtlCutP.Sfr fr))
    by (transitivity (lib.Reusable.YK11.getr R 19); [exact (Hpr' 19 ltac:(w0_cs)) | exact G19]).
  assert (E20 : lib.Reusable.YK11.getr regs' 20 = Z_to_bv 64 (-8))
    by (transitivity (lib.Reusable.YK11.getr R 20); [exact (Hpr' 20 ltac:(w0_cs)) | exact G20]).
  assert (E21 : lib.Reusable.YK11.getr regs' 21 = Z_to_bv 64 (-14))
    by (transitivity (lib.Reusable.YK11.getr R 21); [exact (Hpr' 21 ltac:(w0_cs)) | exact G21]).
  assert (E22 : lib.Reusable.YK11.getr regs' 22 = lib.Reusable.YK11.getr regs3 22)
    by (transitivity (lib.Reusable.YK11.getr R 22); [exact (Hpr' 22 ltac:(w0_cs)) | exact G22]).
  assert (E24 : lib.Reusable.YK11.getr regs' 24 = lib.Reusable.YK11.getr regs3 24)
    by (transitivity (lib.Reusable.YK11.getr R 24); [exact (Hpr' 24 ltac:(w0_cs)) | exact G24]).
  assert (E25 : lib.Reusable.YK11.getr regs' 25 = lib.Reusable.YK11.getr regs3 25)
    by (transitivity (lib.Reusable.YK11.getr R 25); [exact (Hpr' 25 ltac:(w0_cs)) | exact G25]).
  assert (E26 : lib.Reusable.YK11.getr regs' 26 = lib.Reusable.YK11.getr regs3 26)
    by (transitivity (lib.Reusable.YK11.getr R 26); [exact (Hpr' 26 ltac:(w0_cs)) | exact G26]).
  assert (E27 : lib.Reusable.YK11.getr regs' 27 = Z_to_bv 64 (ACtlCutP.Sfr fr + 68))
    by (transitivity (lib.Reusable.YK11.getr R 27); [exact (Hpr' 27 ltac:(w0_cs)) | exact G27]).
  (* bytes across the run (munch) and the call (the view outside the shadow fill) *)
  assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (ACtlCutP.Sfr fr + 68 <= a < ACtlCutP.Sfr fr + 68 + 187) ->
            Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false ->
            lib.Lib.Mem.mrd B.Img0.rsegs mem2 (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd B.Img0.rsegs m1 (lib.Lib.Mem.wa a))
    by (intros a Ha Hq Hv; exact (w0_mrd_view W3 m1 mem2 a Hv (Hfrm a Ha Hq))).
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> lib.Lib.Frame.outside WR a ->
            ~ (ACtlCutP.Sfr fr + 68 <= a < ACtlCutP.Sfr fr + 68 + 187) ->
            Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false ->
            lib.Lib.Mem.mrd B.Img0.rsegs mem2 (lib.Lib.Mem.wa a) = lib.Lib.Mem.mrd B.Img0.rsegs mem3 (lib.Lib.Mem.wa a)).
  { intros a Ha Ho Hq Hv. rewrite (KEEP1 a Ha Hq Hv). exact (w0_mrd_munch WR mem3 m1 a MU Ha Ho). }
  assert (LSV : length (ACtlCutP.saved_bytes cx) = 104%nat)
    by (unfold ACtlCutP.saved_bytes; rewrite !length_app, !lib.Lib.Mem.length_le8; reflexivity).
  pose proof (Reusable.YG0d.al_frames segs B LAWS ly3 S3 W3 mem2 md2 6 (ACtlCut.c_fpos cx) HAR2 Hin)
    as (_ & _ & _ & HFSP2).
  change (Reusable.YG00.fs_frame_bytes 6 / 8) with 512 in HFSP2. rewrite <- Efr, ESh in HFSP2.
  unfold ACtlCut.rgv in *.
  split; [exact HPERM|]. split.
  { exists A, sp. unfold ACtlCut.rgv. unfold Reusable.YG0d.spZ in Psp |- *.
    rewrite E2, E4, E8, E9, E3, E19, E26.
    split; [exact P2|]. split; [exact P16|]. split; [exact Psp|]. split; [exact P4|]. split; [exact P8|].
    split; [exact P9|]. split; [exact P3|]. split; [reflexivity|]. split; [exact P26|]. split; [exact Hal|].
    split; [exact PA32|]. split; [exact PAS|]. split; [exact PspA|].
    split; [unfold ACtlCutP.FRAME_BYTES; lia|]. split; [exact PA448|]. split; [exact Psplo|].
    split; [exact PSapp|].
    split.
    { apply (w0_q64_keep m1 mem2 (A + 336) fr); [exact Q336|]. intros i Hi. apply KEEP1.
      - split; lia.
      - destruct HSb as [X|X]; cbv [B.AsanRT.LOWSHADOW_END B.AsanRT.HIGHMEM_BEG] in X, HAhi; lia.
      - apply (HSTP (A + 336 + i)). split; lia. }
    split.
    { apply (w0_q64_keep m1 mem2 fr 0x41b58ab3); [exact Qhdr|]. intros i Hi. apply KEEP1.
      - split; lia.
      - destruct HSb as [X|X]; lia.
      - apply (HFRP (fr + i)). split; lia. }
    split.
    { apply (w0_q64_keep m1 mem2 (fr + 16) Reusable.YCfn.A_LLVMF); [exact Q16|]. intros i Hi. apply KEEP1.
      - split; lia.
      - destruct HSb as [X|X]; lia.
      - apply (HFRP (fr + 16 + i)). split; lia. }
    split.
    { unfold ACtlCutP.FRAME_SHADOW.
      apply (w0_bytes_exist mem2 (ACtlCutP.Sfr fr) 392); [destruct HSb as [X|X];
        cbv [B.AsanRT.LOWMEM_END B.AsanRT.HIGHSHADOW_BEG] in X; lia | lia |
        destruct HSb as [X|X]; cbv [B.AsanRT.LOWSHADOW_END B.AsanRT.HIGHMEM_BEG] in X; lia |].
      intros i Hi. exact (proj2 (w0_pres_raw _ mem2 _ (proj1 (HFSP2 i ltac:(split; lia))))). }
    split.
    { apply (w0_bytes_at_eq mem3 mem2 _ _ PSAV). intros i Hi. rewrite LSV in Hi. apply KEEP.
      - split; lia.
      - unfold WR. cbn [lib.Lib.Frame.outside]. destruct HSb as [X|X];
          cbv [B.AsanRT.LOWSHADOW_END B.AsanRT.HIGHMEM_BEG] in X, HAhi; repeat split; try exact I; lia.
      - destruct HSb as [X|X]; cbv [B.AsanRT.LOWSHADOW_END B.AsanRT.HIGHMEM_BEG] in X, HAhi; lia.
      - apply (HSTP (ACtlCut.c_sp cx - 104 + Z.of_nat i)). split; lia. }
    { apply (w0_q64_keep mem3 mem2 (fr + 4088)); [exact HTRL|]. intros i Hi. apply KEEP.
      - split; lia.
      - unfold WR. cbn [lib.Lib.Frame.outside]. destruct HSb as [X|X]; repeat split; try exact I; lia.
      - destruct HSb as [X|X]; lia.
      - apply (HFRP (fr + 4088 + i)). split; lia. } }
  split; [exact PN|]. split; [exact E20|]. split; [exact E21|].
  split; [rewrite E24; exact H24|]. split; [rewrite E25; exact H25|].
  split; [rewrite E22; exact H22|]. split; [rewrite E18; exact H18 | exact E27].
Qed.

End W0.

(* Stage lemmas of this file, all closed by Qed; each is named and stated exactly as ACtl.v's Hypothesis of the same
   name, generic in SK and FP (ACtl.v's CF instantiates SK := tfib_sink_head, FP := []):
     seg_A1 (ENTRY)  : forall POST, (forall cx p, POST (ACtlCut.cx_set_fpos cx p) = POST cx) ->
                       ctl_from POST C_B81090 -> ctl_from POST C_B810c4 -> ctl_from POST C_ENTRY
                       (the B810c4 premise is the dead UAR = 0 edge)
     seg_A2 (B81090) : forall POST, ctl_from POST C_B810c4 -> ctl_from POST C_B81090
     seg_A3 (B810c4) : forall POST, ctl_from POST C_B81220 -> ctl_from POST C_B810c4
   FRAC / FRAHC re-established: seg_A1 builds PREFC at B81090 (the trailer word q64 (fr + 4088) (flag_addr ..) from the
   allocation's rdword post, w0_q64_of_rdword); seg_A2 carries PREFC to B810c4; seg_A3 builds FRAHC at B81220 (the
   trailer word kept across the header stores and the shadow fill, w0_q64_keep).
   Trap / sink obligations: none (plan 6.2; no branch to 0x82fa0 / 0x82fa4 in 0x81018-0x81220).  Dead edges
   discharged: S_A1 -> B810c4 (UAR = 1 via ctl_rt's asan_cells, read by the prologue run),
   S_A2's real-stack arm (class-full; astack_malloc_realizes has only the frame_addr outcome). *)
