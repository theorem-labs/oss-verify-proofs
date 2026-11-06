(* reac_box_model_block (0x865d8) of fuzz_ctrl's ASan+UBSan build (image B, libreac v1.9.0): its contract in cgif's
   CALLER-JOURNAL form (cgif lib/YC20.v:311-365 on origin/ossv/recipes c8557374ad2e), STATEMENT ONLY (no Admitted;
   the proof is pb_reac_box_model_block, lib/B/Prog/C_reac_box_model_blockPb.v, plan of record
   analyses/libreac/fuzz_ctrl/glue-B/model_block/pb_reac_box_model_block.plan.md).  rule 24: no function is proved here.

   The image-B twin of image A's spec of record, a Theorem Labs lane's lib/A/Prog/C_reac_box_model_block.v
   (a working branch c592a980fe0), in B's copies of its vocabulary:
   - the segments are the CONCRETE list SEGS := YB1v.tfibsegs, the pa_segs of image B's PA instance
     CtrlImg.PI_ctrl_B (lib/B/Prog/CtrlImg.v:86), so CtrlCallerJ's shapes stated over pa_segs PI apply by
     conversion (A: AB1v.tfibsegs / CtrlImg.PI_ctrl);
   - the post keeps the caller's bytes by CtrlCallerJ.tcj_kept (lib/B/Prog/CtrlCallerJ.v:42), which exempts the
     bytes the call writes in EVERY clause, high memory included (the core's acall_kept, a malloc-post shape, does
     not exempt them in its high-memory clause, so the output block o, which lies in high memory, could not be
     written under it);
   - the row and the name are registered read-only image globals (GLOBS; IMG_LO / IMG_HI of lib/B/Prog/CtrlRo.v; the
     core's in_roP), not owned-static, not errno: so the class-0 request keeps their bytes (acall_kept's image
     clause) and their shadow is marked in every AR state (CtrlRo.globs_marked, the proof's hypothesis);
   - o lies in a side-stack frame of the caller's of class 1 or more, or on the machine stack (tbmb_o_home), and the
     caller lets the call write it (twr_ok) and read it (tsrc_ok).
   Kept from this file's earlier form, differing from A's on purpose:
   - the entry is the constant REAC_BOX_MODEL_BLOCK = 0x865d8 (decisions.md item 3), not a parameter;
   - REAC_BOX_MODEL_BLOCK_STK = 4272, the window of the proved B run, because the proof lifts __asan_memset,
     __asan_memcpy, build_dt1_single, name_field and dt1_head INSIDE that run (their own footprint contracts),
     where A walks memset / memcpy as cgif events and needs 176 + 48 + ESTACK = 4320;
   - the read-only window RLO / RHI are Section variables with RELRO_IMG (decisions.md item 17).

   Provenance (lead's route-(a) condition): the run this contract is glued from is the proved B footprint run
   reac_box_model_block_holds_F (a working branch; statement lib/B/Prog/reac_box_model_block_c.v
   reac_box_model_block_contract_F), re-based in C_reac_box_model_blockRB*.v / C_reac_box_model_blockRBLib.v. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* YI04, YI16, YK11, YK1b, YM05 and YO09 exist twice (core lib/Reusable and ctrl's lib/{A,B}/Reusable): they are
   Required by their core path and named `lib.Reusable.X.n` (a Theorem Labs lane 04:24Z / 04:33Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require APostBase.
(* image B's PA layer (as lib/B/Prog/CtrlCallerJ.v Requires it), the caller-journal shapes and the read-only image
   facts; the segments and the concrete instance qualified only *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import PaTable PaSym PaShadow PaStep PaRun PaJournal.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import CtrlSyms CtrlList CtrlAddr CtrlPa CtrlPaLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require CtrlCallerJ CtrlRo CtrlImg.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v.
(* ctrl's address-free model, Required without Import, every name qualified *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcBox RcSynth.
#[local] Existing Instance CtrlImg.PI_ctrl_B.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* The entry: a constant (decisions.md item 3), = lib/B/Prog/reac_box_model_block_c.v:10 REAC_BOX_MODEL_BLOCK
   (v1.9 asan-ubsan image; A twin 0x85b44). *)
Definition REAC_BOX_MODEL_BLOCK : Z := 0x865d8.

(* The machine stack the call needs = the window of the proved B run (decisions.md item 4):
   REAC_BOX_MODEL_BLOCK_K = 4272 (lib/B/Prog/reac_box_model_block_c.v:16) = max(4272, 176 + 208, 240 + max(2208,
   2224, 2272, 2240, 16)): the 160-byte frame realigned down to 32 (A >= S - 176), the callees at A - 64 >= S - 240 or
   at A, the class-0 request's ESTACK below A (A - 4096 >= S - 4272).  ctrl_lay_block counts it once inside its own
   CTRL_LAY_BLOCK_STK = 4512 (240 + 4272). *)
Definition REAC_BOX_MODEL_BLOCK_STK : Z := 4272.

(* The journal events this call adds: the class-0 request (__asan_stack_malloc_0 at 0x86644) and the inline flag
   release (the `sb zero` at 0x86e4c) keep st_nev and blocks_bytes; no callee allocates.  So 0 (A twin EV_BMB). *)
Definition EV_BMB : Z := 0.

(* The caller's bytes the call writes: the 32-byte output block. *)
Definition treac_box_model_block_out (o a : Z) : Prop := o <= a < o + 32.

(* the byte lists of the model, as the image holds them (A twin bmb_z) *)
Definition bmb_z (l : list byte) : list Z := map (fun x : byte => bv_unsigned x) l.

Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.   (* := Reusable.YE2k.tfib_sink_head once B's core twin lands *)

Section d.
(* the concrete segments of image B (CtrlImg.v:22-24, 86-87) *)
#[local] Notation SEGS := YB1v.tfibsegs.
(* The read-only span of the RO premise (decisions.md item 17, cgif lib/YC20.v:56); the composer instantiates it
   with PI_ctrl_B's pa_relro = [0x9f168, 0xa15e8) and discharges RELRO_IMG by CtrlImg.ctrl_relro_img. *)
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.

Section e.
Variable B : asyms.              (* the composer instantiates B := Reusable.YD2l.CtrlB *)
(* the registered globals, as the callers' specs carry them (the row's table and the name strings) *)
Variable GLOBS : list (Z * Z).

(* o lies in a side-stack frame of the caller's of class 1 or more, or on the machine stack (A twin tbmb_o_home).
   Class 0 is excluded: the call takes a class-0 frame. *)
Definition tbmb_o_home (lyc : alayout) (Sc : astate) (o : Z) : Prop :=
  (exists cid pos, In (cid, pos) (frames Sc) /\ cid <> 0 /\
     forall x, o <= x < o + 32 -> in_zr x (frame_rng lyc (cid, pos))) \/
  (ly_stk_lo lyc <= o /\ o + 32 <= ly_stk_hi lyc).

(* What the call leaves (A twin): the same journal, callee-saved registers, the caller's frames and blocks, a0 and
   the output block as the proved run's post says (a0 = -1 and nothing written outside the window when p = 0 or
   o = 0; else a0 = rc row b and o holds synth row b nb), and tcj_kept: every byte outside the call's own window
   [sp - REAC_BOX_MODEL_BLOCK_STK, sp) and outside what it writes is kept. *)
Definition treac_box_model_block_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (p b o : Z) (row nb : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (lib.Reusable.YK11.mkst regs2 (lib.Reusable.YK11.getr regs 1) mem2
                  (lib.Reusable.YK11.seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_BMB) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
    (if (p =? 0) || (o =? 0)
     then lib.Reusable.YK11.getr regs2 10 = w64 (-1) /\
          CtrlCallerJ.tcj_kept B REAC_BOX_MODEL_BLOCK_STK lyc Sc W memc W2 mem2 (spZ regs) (fun _ => False)
     else lib.Reusable.YK11.getr regs2 10 = w64 (RcSynth.rc row b) /\
          garr8 SEGS (mrestrict (w_H W2) mem2) o (bmb_z (RcSynth.synth row b nb)) /\
          CtrlCallerJ.tcj_kept B REAC_BOX_MODEL_BLOCK_STK lyc Sc W memc W2 mem2 (spZ regs)
            (treac_box_model_block_out o)).

(* The contract (A twin, premise for premise, but the entry constant and the window). *)
Definition treac_box_model_block_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (p b o : Z) (row nb : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (lib.Reusable.YK11.getr regs 1) -> 4096 <= raZ regs ->
  lib.Reusable.YK11.getr regs 3 = w64 (as_gp B) -> lib.Reusable.YK11.getr regs 4 = w64 (as_tp B) ->
  (* a0 = p (the 296-byte model row), a1 = b (the case), a2 = o (the output block); no achain premise
     (decisions.md item 5, exception 00:05Z) *)
  lib.Reusable.YK11.getr regs 10 = w64 p -> lib.Reusable.YK11.getr regs 11 = w64 b ->
  lib.Reusable.YK11.getr regs 12 = w64 o ->
  0 <= p < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_BOX_MODEL_BLOCK_STK -> spZ regs <= sp0 ->
  (* room for the class-0 frame __asan_stack_malloc_0 takes at 0x86644 (YG0d.v:287, astack_malloc_realizes) *)
  count_cid 0 (frames Sc) < fs_frames 0 ->
  (* the 296-byte row at p: a row of a registered, read-only image table (the box catalogue, in PT_GNU_RELRO);
     arodata_okS carries its bytes *)
  (p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\
             garr8 SEGS (mrestrict (w_H W) memc) p (bmb_z row) /\
             (exists q sz, In (q, sz) GLOBS /\ q <= p /\ p + 296 <= q + sz) /\
             CtrlRo.IMG_LO + 64 <= p /\ p + 296 + 64 <= CtrlRo.IMG_HI /\
             (forall x, p <= x < p + 296 -> APostBase.in_roP SEGS RLO RHI x /\
                ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) /\
             (o = 0 \/ o + 32 <= p \/ p + 296 <= o)) ->
  (* the name the row points to (a read-only image string), read byte by byte for b = 5 and b = 6 *)
  (p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
             RcBox.name_ok nb /\
             garr8 SEGS (mrestrict (w_H W) memc) (RcSynth.rname row) (bmb_z nb) /\
             (exists q sz, In (q, sz) GLOBS /\ q <= RcSynth.rname row /\
                RcSynth.rname row + Z.of_nat (length nb) <= q + sz) /\
             CtrlRo.IMG_LO + 64 <= RcSynth.rname row /\
             RcSynth.rname row + Z.of_nat (length nb) + 64 <= CtrlRo.IMG_HI /\
             (forall x, RcSynth.rname row <= x < RcSynth.rname row + Z.of_nat (length nb) ->
                APostBase.in_roP SEGS RLO RHI x /\
                ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) /\
             (o = 0 \/ o + 32 <= RcSynth.rname row \/ RcSynth.rname row + Z.of_nat (length nb) <= o)) ->
  (* the 32 bytes at o: the caller's, which it lets this call write *)
  (o <> 0 -> tbmb_o_home lyc Sc o /\
             (forall x, o <= x < o + 32 -> ~ in_img SEGS x) /\
             CtrlCallerJ.twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) o 32 /\
             CtrlCallerJ.tsrc_ok W memc (spZ regs) o 32 /\
             (spZ regs <= o \/ o + 32 <= spZ regs - REAC_BOX_MODEL_BLOCK_STK)) ->
  lib.Reusable.YA0n.SRr SEGS W (cfg_at SEGS REAC_BOX_MODEL_BLOCK regs memc mdc)
    (treac_box_model_block_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p b o row nb).

(* ---- Discharge lemmas for the callers (ctrl_lay_block: its class-1 frame + 32; reac_box_catalogue_match: its
   class-2 frame + 112; the row and the name: sub-ranges of registered read-only image globals). ---- *)

(* An output block inside a live caller frame of class <> 0 satisfies o's home. *)
Lemma tbmb_o_home_frame : forall lyc Sc cid pos off,
  In (cid, pos) (frames Sc) -> cid <> 0 -> 0 <= off -> off + 32 <= fs_frame_bytes cid ->
  tbmb_o_home lyc Sc (frame_addr lyc cid pos + off).
Proof.
  intros lyc Sc cid pos off Hin Hc H0 H1. left. exists cid, pos. split; [exact Hin|]. split; [exact Hc|].
  intros x Hx. unfold in_zr, frame_rng. cbn [fst snd]. lia.
Qed.

(* An output block on the machine stack satisfies o's home. *)
Lemma tbmb_o_home_stack : forall lyc Sc o,
  ly_stk_lo lyc <= o -> o + 32 <= ly_stk_hi lyc -> tbmb_o_home lyc Sc o.
Proof. intros lyc Sc o H0 H1. right. split; assumption. Qed.

(* The per-byte read-only facts of a registered global pass to every sub-range of it (the row, the name). *)
Lemma ro_global_sub : forall (q sz a n : Z),
  (forall x, q <= x < q + sz -> APostBase.in_roP SEGS RLO RHI x /\
     ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) ->
  q <= a -> a + n <= q + sz ->
  forall x, a <= x < a + n -> APostBase.in_roP SEGS RLO RHI x /\
     ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4).
Proof. intros q sz a n H Hq Hn x Hx. apply H. lia. Qed.

End e.
End d.
End b.
