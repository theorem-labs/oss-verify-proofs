(* The live-state clauses of fuzz_reply's program contract fr_lib_contract_cf (W_LLVMFuzzerTestOneInput_cut.v:234),
   which W8's segments take as the opaque Variables fr_live_pre, fr_live_post, fr_surv and fr_FP.  The text is
   W8Entry-2's (2026-10-29), agreed before this file was written; no W8 segment destructures any of them, so their
   cost lands on SEG_PRO, SEG_EXIT and the driver.

   READ THIS BEFORE CHANGING A DEFINITION.  DRIVER_CF is FALSE over free Variables - take fr_live_pre := fun _ => False.
   With that choice the W8 contract fr_lib_contract_cf holds trivially and TFIB_T does not follow, so these
   definitions ARE the content of the step from fr_lib_contract_cf to TFIB_T (ReplyATop.v's DRIVER_CF), not
   bookkeeping.  A "simplification" that weakens fr_live_pre / fr_surv or strengthens fr_live_post / fr_FP can make
   the W8 contract easier to prove while making the driver's step unprovable, or make the contract vacuous with a
   green build.  Change them only with the agreement of both W8 (which proves the contract) and the driver lane
   (which consumes it).

   - fr_live_pre: the room the call may use, on top of everything live (input block included): CALL_ROOM = 2^33
     bytes (a Theorem Labs lane's ruling, 2026-10-29, with the structural LS): the call's model bytes at any cut point are at
     most about 65 * 2^26 + 3e6 = 4.4e9 < 2^33, and the measured peak of live request bytes is 603,927,919.  The
     driver supplies it from blocks_bytes S <= 2^27 + 3 * (ATABLE + OUT_MAX) (AD1r_heap_cf.v H_bytes).  The earlier
     ATABLE + OUT_MAX room left the call's own model no room under LIVE_MAX.
   - fr_live_post: live bytes grow by at most ATABLE + OUT_MAX (the table and the g_out buffer the entry keeps; every
     other model block is freed by the return).  k is deliberately NOT bounded: fuzz_reply makes about two
     allocator calls per input byte, so cgif's st_nev S + EV_LIB <= EV_MAX (EV_MAX = 8192) is false for it, and the
     cf allocator carries a budget (Reusable/YGcfNames.v LIB_ROOM) in place of an event bound.
   - fr_surv (agreed with W8Entry-2, 2026-10-29, NAMED THROUGH MEMORY): a block alive at the entry that is not one of
     the entry's harness blocks (fr_hblks: g_src's table and g_out's buffer as the globals name them) is alive at the
     return; a block alive at the return was alive at the entry or is one of the return's harness blocks; and the
     return's harness blocks are fresh or were harness blocks at the entry.  By induction the driver's buf and q are
     never harness blocks, so they survive every call; the count form (fr_surv_v0) could not show that, since its one
     dropped block was unnamed.
   - fr_FP: the journal footprint from the entry: g_src's table and g_out's buffer AS THE ENTRY MEMORY HOLDS THEM,
     read through the globals (rdword, Reusable/YG0d.v:34; rg_src / rg_out / rg_capout of fr_globals, W_rep.v).  FP
     entries are (lo, hi) ranges (YI04.v:392 inFP).  There is no sink_token: the entry writes no output (checksum_shape);
     the driver consumes sink_token :: fr_FP, reached from this footprint by footprint weakening. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YP09 YI04 YI00 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
(* Required, not Imported: ra_rel and xcnt_ok, cited by their qualified names in fr_xcnt_ok *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_contract ReplyCnt.
Import ListNotations.
Open Scope Z_scope.

(* g_out's largest buffer, from the source (projects/plugin-hostd/fuzz_reply/source/fuzz_reply.c at the pin
   c8557374ad2e): g_nout restarts at 0 for every op (:692, :749) while g_capout persists and never shrinks, and each
   growth of send_line sets cap = (g_nout + len) * 2 (:299-308; Prog/RelayCap.v send_line_cap_le), so
   g_capout <= 2 * (the most bytes the controller reads in one op).  Every byte the relay sends comes from what its
   source received in the call, R_s <= MASS = 511 * 65,535 (the 511 op-1 pushes :705 of at most 65,535 bytes,
   fuzz_u16).  A drain (op 2) sends each received line once at its received length: <= R_s.  relay_remove DRAINS
   FIRST and then ends the source's held gestures in the SAME op (ReplyRINV.v:380-391 rm_rr_ok: dr_rel .. sl_sends ..
   ge_bytes; relay.c:464-465): each held key x costs |x| + 5 bytes to end (W_contract.v END5) against the |x| + 7 of
   the begin line received in this call that made it, and the held set has no duplicate keys, so the op sends at most
   2 * R_s - 2; gone (op 5) is the same summed over sources; an event sends one line <= 65,536 bytes; relay_finish
   ends keys only.  So g_capout <= 2 * (2 * MASS - 2) = 133,953,536 <= OUT_MAX = 4 * 511 * 65,535 = 133,953,540
   (a Theorem Labs lane's ruling 2026-10-30 01:39Z on a Theorem Labs lane's B1cOutMax; fresh reviewer OutMax4Review, 01:5xZ).
   Witnesses: r1d's model (the implicit open :684, 511 op-1 pushes to slot 0 of 65,535 bytes of
   `param_gesture XYZ begin\0` lines = 1,395,349 begin lines, then op 4: the op sends 64,186,054 bytes and the caps run
   25,165,776, 50,331,600, 100,663,230), and a Theorem Labs lane's MEASUREMENTS on the pinned fuzz_reply.asan (qemu-riscv64
   -strace; b1-RECHECK.md (sha256 2d07c55f9e3f; internal record)): gest511_rm g_nout 66,962,805 and g_capout 98,303,538
   (= 2 * 49,151,769; above 66,976,770, the value this replaces), gest188_rm g_out 49,141,066, and the smallest
   exceeding shape K = 129 writes (g_capout 33,777,208).  The power-of-two sequence 2, 6, 14, .., 2^m - 2 holds only
   for 1-byte sends from cap 0: 511 NUL writes and a drain give exactly 33,554,430 (the older 2^25 - 2,
   REPLY-INSTANCE-REQUIREMENTS.md (sha256 f19868a5803c; internal record) s.3), so the REMOVE op is what exceeds the old bounds. *)
Definition OUT_MAX : Z := 133953540.
(* OPS_MAX is the cut's (W_LLVMFuzzerTestOneInput_cut.v:104, the source's fuzz_reply.c:115) *)
Lemma OUT_MAX_src : OUT_MAX = 2 * (2 * ((OPS_MAX - 1) * 65535)).
Proof. reflexivity. Qed.

(* the room the call's model may use on top of the entry's live bytes *)
Definition CALL_ROOM : Z := 2 ^ 33.

Definition fr_live_pre (S : astate) : Prop := blocks_bytes S + CALL_ROOM <= LIVE_MAX.

Definition fr_live_post (S S' : astate) (k : Z) : Prop := blocks_bytes S' <= blocks_bytes S + ATABLE + OUT_MAX /\ 0 <= k.

(* WITNESS (VERIFY's rule 10): b1's measured gest511_rm call (a new relay table and a g_out buffer of 98,303,538
   bytes) meets fr_live_post, and so does any growth up to the bound; the driver meets fr_live_pre at every call after
   up to three such growths (AD1r_heap_cf.v H_live).  Inputs are under FUZZ_INPUT_MAX = 2^26 (fuzz.h:38). *)
Lemma fr_live_post_remove_witness : forall S S' k, 0 <= k ->
  blocks_bytes S' = blocks_bytes S + ATABLE + 98303538 -> fr_live_post S S' k.
Proof. intros S S' k Hk H. unfold fr_live_post, OUT_MAX in *. lia. Qed.
Lemma fr_live_post_worst : forall S S' k, 0 <= k ->
  blocks_bytes S' = blocks_bytes S + ATABLE + 4 * (OPS_MAX - 1) * 65535 -> fr_live_post S S' k.
Proof. intros S S' k Hk H. unfold fr_live_post, OUT_MAX, OPS_MAX in *. lia. Qed.

(* The form W8's current _cut.v Variable takes (alayout -> astate -> alayout -> astate -> Prop), until its ARcf switch
   lands with fr_surv below; delete this definition then. *)
Definition fr_surv_v0 (B : asyms) (ly : alayout) (S : astate) (ly' : alayout) (S' : astate) : Prop :=
  exists drop new, (length drop <= 1)%nat /\ (length new <= 2)%nat /\
  (forall b, In b (ablocks B ly S) -> ~ In b drop -> In b (ablocks B ly' S')) /\
  (forall b, In b (ablocks B ly' S') -> In b new \/ In b (ablocks B ly S)).

Section fp. Context {rc : YM05.RunCeil}.
Definition fr_FP (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte)
  : list (Z * Z) :=
  let rd := aview tfibsegs (w_H W) mem in
  (match rdword rd (rg_src fr_globals) with Some G => if G =? 0 then [] else [(G, G + ATABLE)] | None => [] end) ++
  (match rdword rd (rg_out fr_globals), rdword rd (rg_capout fr_globals) with
   | Some o, Some c => if c =? 0 then [] else [(o, o + c)] | _, _ => [] end).
(* The entry's harness blocks (g_src's table and g_out's buffer as the globals name them) are
   W_LLVMFuzzerTestOneInput_cut.v's fr_hblks, THE ONE DEFINITION (W8Entry-2, integ 60c0b278422); this name is an
   abbreviation for that constant, so the driver files that import this file read the cut's definition. *)
Definition fr_surv (B : asyms) (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte)
  (ly' : alayout) (S' : astate) (W' : world tfibsegs) (mem' : word -> option byte) : Prop :=
  (forall b, In b (ablocks B ly S) -> ~ In b (W_LLVMFuzzerTestOneInput_cut.fr_hblks W mem) -> In b (ablocks B ly' S')) /\
  (forall b, In b (ablocks B ly' S') -> In b (W_LLVMFuzzerTestOneInput_cut.fr_hblks W' mem') \/ In b (ablocks B ly S)) /\
  (forall b, In b (W_LLVMFuzzerTestOneInput_cut.fr_hblks W' mem') -> ~ In b (ablocks B ly S) \/ In b (W_LLVMFuzzerTestOneInput_cut.fr_hblks W mem)).
End fp.
(* the cut's harness blocks under their driver-side name (see above) *)
Notation fr_hblks := W_LLVMFuzzerTestOneInput_cut.fr_hblks.
(* the cut's CAPOUT clause (W_LLVMFuzzerTestOneInput_cut.v fr_lib_pre_cf / fr_lib_post_cf, the last conjunct) at
   segs := tfibsegs: g_capout reads a c with 0 <= c <= CAPOUT_MAX (CAPOUT_MAX is OUT_MAX above; val_mem keeps only the
   low 64 bits, so the lower bound is needed).  The view is W_rep.arm's body
   (mrestrict (w_H W) mem): arm takes an image instance (W_kit.v PAImg, W_img.v PB_fr), which needs an FPState and a
   RunCeil in context; the cut's clause is this one by conversion. *)
Definition fr_capout_ok (W : world tfibsegs) (mem : word -> option byte) : Prop :=
  exists c, val_mem tfibsegs (mrestrict (w_H W) mem) (rg_capout W_LLVMFuzzerTestOneInput_cut.fr_RG) 8 c /\
    0 <= c <= W_LLVMFuzzerTestOneInput_cut.CAPOUT_MAX.
Lemma CAPOUT_MAX_OUT_MAX : W_LLVMFuzzerTestOneInput_cut.CAPOUT_MAX = OUT_MAX.
Proof. reflexivity. Qed.
(* the cut's XCNT clause (W_LLVMFuzzerTestOneInput_cut.v fr_lib_pre_cf / fr_lib_post_cf, the conjunct before CAPOUT)
   with the input block list inp for the cut's `if n =? 0 then [] else [(p, n)]`: the relay as the globals hold it
   (T0, as fr_gi's ra_rel names it), g_out's cells and block (cap, out, as aout_at names them), and few other live
   blocks (ReplyCnt.xcnt_ok).  ra_rel and aout_at take the image instance, so the definition is in a Section with an
   FPState and a RunCeil, as the cut's is. *)
Section xc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition fr_xcnt_ok (B : asyms) (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte)
  (inp : list (Z * Z)) : Prop :=
  exists T0 c O mx cap out, W_contract.ra_rel B fr_RG ly S W mem T0 [] /\
    aout_at B fr_RG ly S W mem c O mx (Z.of_nat (length O)) cap out /\
    ReplyCnt.xcnt_ok B S ly inp T0 cap out.
(* That this is the cut's text is checked where both meet: ReplyDriverCf.v's fr_pre_bridge passes it to
   fr_lib_pre_cf_x by position (fresh reviewer DrvTailReview, 05:5xZ: an iff_refl Goal here checked nothing). *)
End xc.
