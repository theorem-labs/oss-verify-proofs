(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 823 of its 864 lines of code are new or changed and 970 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F3F.v, with its addresses changed; 244 of its 469 lines of code are new or changed and 639 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F3.v 7267394c6d6f (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7 (the same blob the
   glue base carries), Seg/F3F.v at a working branch e1ece7d93f27.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: f3_call_of_pre_post / f3_calln_of_pre_post re-derive F3.f3_call / F3.f3_calln from the two stretches and
   the PLAIN callee contract; the two _verbatim pins check by constr_eq that their types are the types of F3.f3_call
   and F3.f3_calln. Mechanical re-cut, route (a) (lead 22:15Z); input to the ported walk only.
   rule 24: no function proved (segment lemma). *)

(* SPLIT STRETCHES of F3's two call runs, at the `jal reac_ctrl_parse` of 0x81df8 (callee entry
   REAC_CTRL_PARSE = 0x83578, return point 0x81dfc).  Shape of record: segF-v19-spec.md (a working note, not in this delivery)
   (a Theorem Labs lane ruling 00:45Z; shape fixed by a Theorem Labs lane 00:48Z; a Theorem Labs lane's yes to this file
   04:01Z, relayed by a Theorem Labs lane).  Model of record: Seg/R10AF.v's r10a_call34_pre_F / _post_F / _of_pre_post.
   Writer: a Theorem Labs lane.  NEITHER lib/A/Prog/Seg/F3.v NOR lib/A/Prog/Seg/F3F.v is edited by this file;
   both are Required.

   WHY THE WALK NEEDS THE SPLIT.  The walk of LLVMFuzzerTestOneInput (lib/A/ACtl.v, stage seg_F3) applies
   a Theorem Labs lane's cgif-form parse spec `treac_ctrl_parse_spec` (lib/A/Prog/C_reac_ctrl_parse.v) at the jal, not
   `reac_ctrl_parse_contract(_F)`: the cgif spec is journal-form and asks the caller for journal facts
   (ajournal, afobj, awr_byte ...), never for the machine-level ASan invariants (mem_inv, asan_cells, fp, the
   side-stack tls package) that the machine-level contract asks for.  So the glue needs the segment's run cut in
   two at the call, with the callee contract out of the pre stretch entirely.

   THE FOUR LEMMAS
   - f3_call_pre_Fs / f3_calln_pre_Fs (NARROWED) and f3_call_pre_F / f3_calln_pre_F (a Theorem Labs lane's full-premise shape
     of record, proved from the narrowed ones): the four instructions 0x81dec mv a0,s7 ; 0x81df0 mv a1,s2 ;
     0x81df4 ld a2,248(s1) ; 0x81df8 jal reac_ctrl_parse, ending in the CALLEE ENTRY state (pc =
     Z_to_bv 64 REAC_CTRL_PARSE, x1 = Z_to_bv 64 0x81dfc, a0 = f, a1 = N, a2 = o).  This is the source's
     `step. step. step. step.` prefix (F3.v:1063 / F3F.v:f3_call_F), with the one access it makes -- the 8-byte
     prologue spill read [A + 248, A + 256) -- as its single rng premise.
     THE NARROWED PREMISES (narrowed-stretch rule, a Theorem Labs lane 04:23Z via a Theorem Labs lane 04:34Z, relayed by
     a Theorem Labs lane): ONLY the ones that prefix uses (0 <= A, A + 256 <= 2 ^ 64 for the address form of the load, and
     the source's own read premise `ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o))`).  The
     source's other premises -- mem_inv / ro_agree, the record and output-cell packages, asan_cells, shadow_rw,
     the window, the GOT and CF cells, fp and reac_ctrl_parse_tls -- are premises OF THE CALLEE CONTRACT at this
     call, not of these four instructions: F3.v's script uses none of them before `eapply evt_cut`, and they have
     no source at the walk's cut (the cgif route has no machine-level ASan invariant to offer).  The walk's glue
     consumes the narrowed form; the full form keeps the source's list for the premise table, and
     f3_call_of_pre_post / f3_calln_of_pre_post carry the whole list, pinned against F3's types.
     The two pre stretches have the SAME statement: the prefix reads one spill cell and no invariant of the
     memory, so normalizing the memory (which is what separates F3.f3_calln from F3.f3_call) changes nothing in
     it; f3_calln_pre_Fs is therefore f3_call_pre_Fs, stated under its own name for the premise table.
   - f3_call_post_F / f3_calln_post_F: the zero-step stretch from the RETURN pc 0x81dfc at a universally
     quantified canonical register map (Regs6ss.mkR_of regs), with exactly the machine-level facts the source
     script holds right after it applies the callee contract: the seventeen register equalities the source's post
     pins (x1 x2 x3 x4 x8 x9 x10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27; the scratch registers x5-x7, x11-x17 and
     x28-x31 are existential in that post and are instantiated with their own values) and the memory facts the
     post states (munch, wmono, [ro_same,] stk, the 36 output cells, shadow_rw, addressable, and fp / the two
     side-stack conjuncts).  The callee post's mem_inv / asan_cells / tls clauses are not in the source's
     conclusion, so they are not premises.  No access, so no rng premise.
     The start keeps the source's Fr (float registers) and fc (fcsr) binders rather than fp_regs / fp_csr, because
     the of_pre_post lemmas have to rebuild F3's runs for the source's own Fr and fc (the no-weakening pin), as
     R10AF.v's r10a_call34_post_F does for the same reason.
   - f3_call_of_pre_post: pre_F at ExecF.RNG_all, then the PLAIN contract (the Section hypothesis HPARSE, in
     F3.v's own position), then post_F, re-deriving F3.f3_call; pinned by constr_eq.
   - f3_calln_of_pre_post: F3.f3_calln's own script with `f3_call` replaced by `f3_call_of_pre_post` and its tail
     replaced by f3_calln_post_F; pinned by constr_eq.  THE CUT IS STILL THE ONE AT THE JAL: F3.f3_calln reaches
     the contract on the NORMALIZED memory (MemNorm.evt_normalize from ro_agree, F3.v:1137-1140), because the
     machine-level contract's mem_inv premise is false on the caller's own memory; so the only place the plain
     contract can be applied in a re-derivation of f3_calln is where the source applies it, inside the normalized
     run.  The normalization is the source's own two script lines, copied, and no reasoning is added.  (The walk
     never takes this route: it uses f3_calln_pre_F on the caller's own memory and the cgif spec, which has no
     mem_inv premise.)

   NO new proof obligation: every tactic below is F3.v's or F3F.v's at the same point of the same script.
   No Axiom, no Parameter, no Admitted, no admit.

   TWIN MODULES (porter a Theorem Labs lane, 04:03Z; relayed by a Theorem Labs lane): the six modules that exist twice
   (YI04 YI16 YK11 YK1b YM05 YO09) are named FULLY QUALIFIED in every statement of this file
   (A.Reusable.<X>, ctrl's copy, which is the one F3.v and F3F.v are stated over); the Require block below is
   F3F.v's, so the bodies are the same constants. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcParse RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c
  RcAsanFP reac_ctrl_parse_c reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs F1 F2 F3 F3F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Tac Bytes.
(* Last but YK11: StepF's step / finish (evtF goals) shadow the evt engine's. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

(* F3.v's Section S starts at its line 43, so its Ltac definitions are section-local and not exported: this is
   the same body under the same name, for this file (F3F.v copies it for the same reason). *)
Ltac f3_ba_rel R :=
  first [ apply (proj1 (bytes_at_rel rsegs _ _ _ _ R)); assumption
        | apply (proj2 (bytes_at_rel rsegs _ _ _ _ R)); assumption ].

(* An 8-byte spill cell, in the form the load engine reads.  Cut from R10A.v:704's r10a_q64_ro use
   (bytes_at -> the engine's read) with lib/Lib/Mem.v's bytes_at_ov_read; the walk's glue builds the source's
   read premise with it from the cut body's q64 conjunct.  Every name here is Lib.Mem-qualified: lib/A/Tk/UL/Mem.v
   defines le8 / length_le8 too, and the unqualified length_le8 is that other copy in this environment (the first
   build's error). *)
Lemma f3s_q64_ov : forall (m : word -> option byte) (a v : Z),
  Lib.Mem.bytes_at rsegs m a (Lib.Mem.le8 (Z_to_bv 64 v)) ->
  ov_read_bytes rsegs m (Lib.Mem.wa a) 8 = Some (Lib.Mem.le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H.
  pose proof (Lib.Mem.length_le8 (Z_to_bv 64 v)) as L8.
  pose proof (Lib.Mem.bytes_at_ov_read rsegs m a (Lib.Mem.le8 (Z_to_bv 64 v)) 0
                (length (Lib.Mem.le8 (Z_to_bv 64 v))) H ltac:(lia)) as E.
  rewrite skipn_O, firstn_all, L8 in E.
  replace (a + Z.of_nat 0) with a in E by lia. exact E.
Qed.

(* F3.v's Section S (F3.v:42-51), declaration for declaration, so every lemma below discharges over the same
   variables in the same order and the two _verbatim pins can compare whole types. *)
Section S.
Context {fx : A.Reusable.YK11.FPState} {LS : A.Reusable.YO09.lib_shape} {rc : A.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : A.Reusable.YM05.RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : A.Reusable.YI16.sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee contract, PLAIN, in F3.v's own position (F3.v:51). *)
Hypothesis HPARSE : reac_ctrl_parse_contract.

(* ---- The pre stretch: 0x81dec .. the jal, ending at the callee entry with x1 = the return point.
   NARROWED form (a Theorem Labs lane 04:23Z via a Theorem Labs lane 04:34Z, relayed by a Theorem Labs lane): only the premises these four
   instructions use.  The full-premise form of record, f3_call_pre_F / f3_calln_pre_F, is below and is proved
   from this one; the walk's glue consumes the narrowed one, because the dropped premises (mem_inv / ro_agree,
   fp, reac_ctrl_parse_tls, the GOT and CF cells, the record and output-cell packages) are premises OF THE
   CALLEE CONTRACT and have no source at the walk's cut. ---- *)
Lemma f3_call_pre_Fs :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f N o S : Z),
    0 <= A -> A + 256 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    ExecF.rng RNG (A + 248) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                                (Z_to_bv 64 f) (Z_to_bv 64 N) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                                (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81dec) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f N o S HA0 HAhi HRDcur R248.
  (* the same region as R248, in the address form the code computes it (ld a2,248(s1)) -- F3F.v's line *)
  assert (R248' : ExecF.rng RNG (bv_unsigned (Z_to_bv 64 A) + 248) 8)
    by (rewrite MState.unsigned_lit by lia; exact R248).
  (* 0x81dec mv a0,s7 ; 0x81df0 mv a1,s2 ; 0x81df4 ld a2,248(s1) ; 0x81df8 jal reac_ctrl_parse *)
  step. step. step. step.
  apply ExecF.evtF_done. reflexivity.
Qed.

(* The same four instructions on the caller's own memory: the prefix reads one spill cell and no invariant of
   the memory, so F3.f3_calln's stretch up to the jal is F3.f3_call's. *)
Lemma f3_calln_pre_Fs :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f N o S : Z),
    0 <= A -> A + 256 <= 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    ExecF.rng RNG (A + 248) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                                (Z_to_bv 64 f) (Z_to_bv 64 N) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                                (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81dec) fc None m (seg_rom rsegs)).
Proof. exact f3_call_pre_Fs. Qed.

(* ---- The pre stretch in a Theorem Labs lane's FULL-PREMISE shape of record: F3.f3_call's own binders and premises, RNG
   first, the one rng premise appended, concluding at the callee entry.  Proved from the narrowed form; the
   dropped premises are not used by any of the four instructions. ---- *)
Lemma f3_call_pre_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f N o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= N -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd N bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o <> 0 -> o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= N -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= N -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f N o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    ExecF.rng RNG (A + 248) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                                (Z_to_bv 64 f) (Z_to_bv 64 N) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                                (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81dec) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f N o S FS bs junk Hf HN Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr HBC H1 H2 H3 H4 H5 HFP HTLS R248.
  exact (f3_call_pre_Fs RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fc m A f N o S HA0 HAhi HRDcur R248).
Qed.

(* The same, for F3.f3_calln's premise list (ro_agree in place of mem_inv, the output-cell package split). *)
Lemma f3_calln_pre_F :
  forall (RNG : ExecF.footprint)
         (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f N o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= N -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd N bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    (50 <= N -> o + 36 <= f \/ f + 50 <= o) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= N -> addressable m f 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f N o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    ExecF.rng RNG (A + 248) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A)
                                (Z_to_bv 64 f) (Z_to_bv 64 N) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                                (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
                           Fr (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81dec) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f N o S FS bs junk Hf HN Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Hbig HRD Ho4 Hocell
    Howin Howf HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS R248.
  exact (f3_call_pre_Fs RNG ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11
           t3 t4 t5 t6 Fr fc m A f N o S HA0 HAhi HRDcur R248).
Qed.

(* ---- The post stretch: no instruction, F3.f3_call's post rebuilt from the callee post's facts. ---- *)
Lemma f3_call_post_F :
  forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (gp tp s0 s3i s4 s5 s6 s8 s9 s10 s11 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f N o S FS : Z) (bs : list byte),
    A.Reusable.YK11.getr regs 1 = Z_to_bv 64 0x81dfc ->
    A.Reusable.YK11.getr regs 2 = Z_to_bv 64 S ->
    A.Reusable.YK11.getr regs 3 = gp ->
    A.Reusable.YK11.getr regs 4 = tp ->
    A.Reusable.YK11.getr regs 8 = s0 ->
    A.Reusable.YK11.getr regs 9 = Z_to_bv 64 A ->
    A.Reusable.YK11.getr regs 10 = Z_to_bv 64 (fst (ctrlparse N bs)) ->
    A.Reusable.YK11.getr regs 18 = Z_to_bv 64 N ->
    A.Reusable.YK11.getr regs 19 = s3i ->
    A.Reusable.YK11.getr regs 20 = s4 ->
    A.Reusable.YK11.getr regs 21 = s5 ->
    A.Reusable.YK11.getr regs 22 = s6 ->
    A.Reusable.YK11.getr regs 23 = Z_to_bv 64 f ->
    A.Reusable.YK11.getr regs 24 = s8 ->
    A.Reusable.YK11.getr regs 25 = s9 ->
    A.Reusable.YK11.getr regs 26 = s10 ->
    A.Reusable.YK11.getr regs 27 = s11 ->
    munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
           [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m mem ->
    wmono rsegs m mem ->
    stk rsegs mem (S - REAC_CTRL_PARSE_K) S ->
    rw_cells rsegs mem o [CB 36 (snd (ctrlparse N bs))] ->
    shadow_rw mem ->
    addressable mem (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    fp [1%nat] mem (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
       (reac_ctrl_parse_D f N o) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse N bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81dfc) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse N bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f N o))
      (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x81dfc) fc None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem gp tp s0 s3i s4 s5 s6 s8 s9 s10 s11 Fr fc m A f N o S FS bs
    K1 K2 K3 K4 K8 K9 K10 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 MU WM ST RW SW AD FPo.
  assert (EM : Regs6ss.mkR_of regs =
               mkR (A.Reusable.YK11.getr regs 1) (A.Reusable.YK11.getr regs 2) (A.Reusable.YK11.getr regs 3)
                   (A.Reusable.YK11.getr regs 4) (A.Reusable.YK11.getr regs 5) (A.Reusable.YK11.getr regs 6)
                   (A.Reusable.YK11.getr regs 7) (A.Reusable.YK11.getr regs 8) (A.Reusable.YK11.getr regs 9)
                   (A.Reusable.YK11.getr regs 10) (A.Reusable.YK11.getr regs 11) (A.Reusable.YK11.getr regs 12)
                   (A.Reusable.YK11.getr regs 13) (A.Reusable.YK11.getr regs 14) (A.Reusable.YK11.getr regs 15)
                   (A.Reusable.YK11.getr regs 16) (A.Reusable.YK11.getr regs 17) (A.Reusable.YK11.getr regs 18)
                   (A.Reusable.YK11.getr regs 19) (A.Reusable.YK11.getr regs 20) (A.Reusable.YK11.getr regs 21)
                   (A.Reusable.YK11.getr regs 22) (A.Reusable.YK11.getr regs 23) (A.Reusable.YK11.getr regs 24)
                   (A.Reusable.YK11.getr regs 25) (A.Reusable.YK11.getr regs 26) (A.Reusable.YK11.getr regs 27)
                   (A.Reusable.YK11.getr regs 28) (A.Reusable.YK11.getr regs 29) (A.Reusable.YK11.getr regs 30)
                   (A.Reusable.YK11.getr regs 31)) by reflexivity.
  apply ExecF.evtF_done.
  exists (A.Reusable.YK11.getr regs 5), (A.Reusable.YK11.getr regs 6), (A.Reusable.YK11.getr regs 7),
         (A.Reusable.YK11.getr regs 11), (A.Reusable.YK11.getr regs 12), (A.Reusable.YK11.getr regs 13),
         (A.Reusable.YK11.getr regs 14), (A.Reusable.YK11.getr regs 15), (A.Reusable.YK11.getr regs 16),
         (A.Reusable.YK11.getr regs 17), (A.Reusable.YK11.getr regs 28), (A.Reusable.YK11.getr regs 29),
         (A.Reusable.YK11.getr regs 30), (A.Reusable.YK11.getr regs 31), mem.
  split.
  { rewrite EM, K1, K2, K3, K4, K8, K9, K10, K18, K19, K20, K21, K22, K23, K24, K25, K26, K27. reflexivity. }
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. split; [exact RW|].
  split; [exact SW|]. split; [exact AD | exact FPo].
Qed.

(* The same stretch for the run on the caller's own memory: F3.f3_calln's post (ro_same, and the two side-stack
   conjuncts in place of fp). *)
Lemma f3_calln_post_F :
  forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte)
         (gp tp s0 s3i s4 s5 s6 s8 s9 s10 s11 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f N o S FS : Z) (bs : list byte),
    A.Reusable.YK11.getr regs 1 = Z_to_bv 64 0x81dfc ->
    A.Reusable.YK11.getr regs 2 = Z_to_bv 64 S ->
    A.Reusable.YK11.getr regs 3 = gp ->
    A.Reusable.YK11.getr regs 4 = tp ->
    A.Reusable.YK11.getr regs 8 = s0 ->
    A.Reusable.YK11.getr regs 9 = Z_to_bv 64 A ->
    A.Reusable.YK11.getr regs 10 = Z_to_bv 64 (fst (ctrlparse N bs)) ->
    A.Reusable.YK11.getr regs 18 = Z_to_bv 64 N ->
    A.Reusable.YK11.getr regs 19 = s3i ->
    A.Reusable.YK11.getr regs 20 = s4 ->
    A.Reusable.YK11.getr regs 21 = s5 ->
    A.Reusable.YK11.getr regs 22 = s6 ->
    A.Reusable.YK11.getr regs 23 = Z_to_bv 64 f ->
    A.Reusable.YK11.getr regs 24 = s8 ->
    A.Reusable.YK11.getr regs 25 = s9 ->
    A.Reusable.YK11.getr regs 26 = s10 ->
    A.Reusable.YK11.getr regs 27 = s11 ->
    munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
           [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m mem ->
    wmono rsegs m mem ->
    ro_same rsegs m mem ->
    stk rsegs mem (S - REAC_CTRL_PARSE_K) S ->
    rw_cells rsegs mem o [CB 36 (snd (ctrlparse N bs))] ->
    shadow_rw mem ->
    addressable mem (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    stk rsegs mem FS (FS + FS_SIZE) ->
    fp_cls mem FS 1 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse N bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81dfc) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_same rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse N bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 1)
      (MS (Regs6ss.mkR_of regs) Fr (Z_to_bv 64 0x81dfc) fc None mem (seg_rom rsegs)).
Proof.
  intros RNG regs mem gp tp s0 s3i s4 s5 s6 s8 s9 s10 s11 Fr fc m A f N o S FS bs
    K1 K2 K3 K4 K8 K9 K10 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 MU WM RO ST RW SW AD STF CLS.
  assert (EM : Regs6ss.mkR_of regs =
               mkR (A.Reusable.YK11.getr regs 1) (A.Reusable.YK11.getr regs 2) (A.Reusable.YK11.getr regs 3)
                   (A.Reusable.YK11.getr regs 4) (A.Reusable.YK11.getr regs 5) (A.Reusable.YK11.getr regs 6)
                   (A.Reusable.YK11.getr regs 7) (A.Reusable.YK11.getr regs 8) (A.Reusable.YK11.getr regs 9)
                   (A.Reusable.YK11.getr regs 10) (A.Reusable.YK11.getr regs 11) (A.Reusable.YK11.getr regs 12)
                   (A.Reusable.YK11.getr regs 13) (A.Reusable.YK11.getr regs 14) (A.Reusable.YK11.getr regs 15)
                   (A.Reusable.YK11.getr regs 16) (A.Reusable.YK11.getr regs 17) (A.Reusable.YK11.getr regs 18)
                   (A.Reusable.YK11.getr regs 19) (A.Reusable.YK11.getr regs 20) (A.Reusable.YK11.getr regs 21)
                   (A.Reusable.YK11.getr regs 22) (A.Reusable.YK11.getr regs 23) (A.Reusable.YK11.getr regs 24)
                   (A.Reusable.YK11.getr regs 25) (A.Reusable.YK11.getr regs 26) (A.Reusable.YK11.getr regs 27)
                   (A.Reusable.YK11.getr regs 28) (A.Reusable.YK11.getr regs 29) (A.Reusable.YK11.getr regs 30)
                   (A.Reusable.YK11.getr regs 31)) by reflexivity.
  apply ExecF.evtF_done.
  exists (A.Reusable.YK11.getr regs 5), (A.Reusable.YK11.getr regs 6), (A.Reusable.YK11.getr regs 7),
         (A.Reusable.YK11.getr regs 11), (A.Reusable.YK11.getr regs 12), (A.Reusable.YK11.getr regs 13),
         (A.Reusable.YK11.getr regs 14), (A.Reusable.YK11.getr regs 15), (A.Reusable.YK11.getr regs 16),
         (A.Reusable.YK11.getr regs 17), (A.Reusable.YK11.getr regs 28), (A.Reusable.YK11.getr regs 29),
         (A.Reusable.YK11.getr regs 30), (A.Reusable.YK11.getr regs 31), mem.
  split.
  { rewrite EM, K1, K2, K3, K4, K8, K9, K10, K18, K19, K20, K21, K22, K23, K24, K25, K26, K27. reflexivity. }
  split; [exact MU|]. split; [exact WM|]. split; [exact RO|]. split; [exact ST|]. split; [exact RW|].
  split; [exact SW|]. split; [exact AD|]. split; [exact STF | exact CLS].
Qed.

(* ---- The two stretches and the PLAIN contract rebuild F3.f3_call. ---- *)
Lemma f3_call_of_pre_post :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f N o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= N -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd N bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o <> 0 -> o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= N -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= N -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f N o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse N bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81dfc) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse N bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f N o))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81dec) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f N o S FS bs junk Hf HN Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr HBC H1 H2 H3 H4 H5 HFP HTLS.
  (* the pre stretch, 0x81dec .. the jal *)
  eapply evt_cut.
  { apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
    apply (f3_call_pre_Fs ExecF.RNG_all ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11
             t3 t4 t5 t6 Fr fc m A f N o S HA0 HAhi HRDcur).
    apply ExecF.rng_all; lia. }
  intros ms' ->.
  (* the callee, on the PLAIN contract, exactly as F3.v:1066-1070 applies it *)
  pose proof HPARSE as HP. unfold reac_ctrl_parse_contract, REAC_CTRL_PARSE in HP.
  eapply evt_cut.
  { eapply HP with (f := f) (n := N) (o := o) (S := S) (FS := FS) (fr := bs) (junk := junk);
      try reflexivity; try assumption; try lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m' &
    E & MU & WM & MI & ST & Hrw & Hac & HSW' & Hadr & FPo & Htls).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x81dfc)) with (Z_to_bv 64 0x81dfc)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  (* the post stretch, at the return point *)
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f3_call_post_F ExecF.RNG_all
           (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                (Z_to_bv 64 (fst (ctrlparse N bs))) a1' a2' a3' a4' a5' a6' a7'
                (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 tt3 tt4 tt5 tt6)
           m' gp tp s0 s3i s4 s5 s6 s8 s9 s10 s11 Fr fc m A f N o S FS bs);
    try reflexivity.
  - exact MU.
  - exact WM.
  - exact ST.
  - exact (Hrw Honz).
  - exact HSW'.
  - exact Hadr.
  - exact FPo.
Qed.


(* ---- F3.f3_calln, re-derived: its own script over f3_call_of_pre_post, closing with f3_calln_post_F. ---- *)
Lemma f3_calln_of_pre_post :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f N o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= N -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd N bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    (50 <= N -> o + 36 <= f \/ f + 50 <= o) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= N -> addressable m f 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f N o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse N bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81dfc) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_same rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse N bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 1)
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81dec) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f N o S FS bs junk Hf HN Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Hbig HRD Ho4 Hocell
    Howin Howf HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  set (m0 := normalize rsegs m) in REL.
  assert (HC := f3_call_of_pre_post ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11
                  t3 t4 t5 t6 Fr fc m0 A f N o S FS bs junk Hf HN ltac:(lia) ltac:(lia) HS HS16 HSK HA0 HAhi).
  pose proof (f3_stk_rel m m0 (S - REAC_CTRL_PARSE_K) S REL ltac:(unfold REAC_CTRL_PARSE_K, HIGHMEM_BEG in *; lia) HST)
    as HST0.
  specialize (HC HST0 (mem_inv_normalize rsegs m) Hlen).
  specialize (HC ltac:(rewrite <- (ov_read_rel rsegs m m0 _ _ REL); exact HRDcur)).
  specialize (HC Hbig).
  specialize (HC ltac:(intros i Hi; rewrite <- (mrd_rel rsegs m m0 _ REL); exact (HRD i Hi))).
  specialize (HC ltac:(intros _; split; [exact Ho4|]; split; [lia|]; split;
    [ destruct Hocell as ((Hwf & Hb) & Hw); split; [split; [exact Hwf | f3_ba_rel REL]|];
      apply (wr_at_norm rsegs m m0 o _ REL Hw); intros i Hi; apply f3_ro_gt; cbn in Hi; lia
    | split; [exact Howin | exact Howf]])).
  specialize (HC (f3_cells_rel m m0 REL HAC) (f3_shrw_rel m m0 REL HSW) HHI HAPP (f3_addr_rel m m0 _ _ REL HWA)).
  specialize (HC ltac:(intros Hb; exact (f3_addr_rel m m0 _ _ REL (HFA Hb)))).
  specialize (HC ltac:(intros _; split; [exact (f3_addr_rel m m0 _ _ REL Hoaddr) | split; [exact Hoapp | exact HoCF]])).
  specialize (HC (f3_addr_rel m m0 _ _ REL HBC)).
  specialize (HC ltac:(f3_ba_rel REL) ltac:(f3_ba_rel REL) ltac:(f3_ba_rel REL) ltac:(f3_ba_rel REL)
                 ltac:(f3_ba_rel REL)).
  specialize (HC (f3_fp_rel _ m m0 _ _ _ _ _ _ REL HFP)).
  specialize (HC ltac:(intros DT TS C T DB k HT0; apply HTLS; exact (proj2 (f3_tls_rel m m0 _ DT TS C T DB k REL) HT0))).
  pose proof (evt_normalize rsegs _ _ Fr _ fc None m (seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO HC) as HN0.
  eapply evt_cut; [exact HN0|].
  intros ms' (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m0' &
    E0 & MU0 & WM0 & ST0 & RW0 & SW0 & AD0 & FP0) & Hrel & Hro').
  subst s0'.
  destruct Hrel as (ER & EF & EP & ESv & ERes & EFc & ERom & HR').
  destruct ms' as [r' f' p' sv' rv' fc' m' ro'].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ER, EF, EP, ESv, ERes, EFc,
    ERom, HR', Hro'.
  subst r' f' p' sv' rv' fc' ro'.
  (* the post stretch on the caller's own memory, at the return point *)
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f3_calln_post_F ExecF.RNG_all
           (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                (Z_to_bv 64 (fst (ctrlparse N bs))) a1' a2' a3' a4' a5' a6' a7'
                (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 tt3 tt4 tt5 tt6)
           m' gp tp s0 s3i s4 s5 s6 s8 s9 s10 s11 Fr fc m A f N o S FS bs);
    try reflexivity.
  - exact (munch_rel rsegs _ m m0 m' m0' REL HR' Hro' MU0).
  - exact (wmono_rel rsegs m m0 m' m0' REL HR' Hro' WM0).
  - exact Hro'.
  - exact (f3_stk_back m' m0' _ _ HR' ST0).
  - destruct RW0 as ((Hwf & Hb) & Hw). split; [split; [exact Hwf | f3_ba_rel HR']|].
    exact (wr_at_rel rsegs m' m0' o _ HR' Hw).
  - exact (f3_shrw_back m' m0' HR' SW0).
  - exact (f3_addr_back m' m0' _ _ HR' AD0).
  - destruct FP0 as (DT & TS & C & T & DB & k & _ & _ & Hpl & _ & _ & Hcls & _).
    destruct Hpl as (_ & _ & _ & _ & P5). exact (f3_stk_back m' m0' _ _ HR' P5).
  - destruct FP0 as (DT & TS & C & T & DB & k & _ & _ & _ & _ & _ & Hcls & _).
    exact (proj2 (f3_cls_rel m' m0' FS 1 HR') (Forall_inv Hcls)).
Qed.

End S.

(* ---- The pins.  Both of_pre_post lemmas are F3's own statements, term for term: the callee contract is the
   PLAIN one in F3.v's own Section position, so no context swap is needed (unlike F3F.v's two call pins, which
   replace reac_ctrl_parse_contract_F).  The comparison is of the whole discharged type, section binders
   included. ---- *)

Example f3_call_of_pre_post_verbatim : True.
Proof. let a := type of F3.f3_call in let b := type of f3_call_of_pre_post in constr_eq a b. exact I. Qed.

Example f3_calln_of_pre_post_verbatim : True.
Proof. let a := type of F3.f3_calln in let b := type of f3_calln_of_pre_post in constr_eq a b. exact I. Qed.
