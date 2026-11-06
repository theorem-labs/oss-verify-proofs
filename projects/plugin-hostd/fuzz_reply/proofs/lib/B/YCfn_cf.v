(* The live-state clauses of fuzz_reply.asan-ubsan's program contract fr_lib_contract_cf_x
   (lib/B/W_LLVMFuzzerTestOneInput_cut_x.v, the Section cf parameters fr_live_pre / fr_live_post / fr_surv / fr_FP; the
   B top lib/B/W_LLVMFuzzerTestOneInput_top_x.v and the B plug lib/B/ReplyDriverCfB.v fill them with this file's _b
   names; the non-x lib/B/W_LLVMFuzzerTestOneInput_cut.v takes a 4-argument fr_surv that fr_surv_b does not fill):
   lib/B's twin of lib/A/ACfn_cf.v (commit 2dc8b98f64d), at image B's globals fr_globals_b
   (lib/B/W_rep.v) and image B's segments tfibsegs (lib/B/YB1v.v).  The texts are the ones W8Entry-2 and ATopKeeper
   agreed for A; a Theorem Labs lane approved them for B (2026-10-29), with fr_surv in A's MEMORY-NAMED form from the start:
   the count form (A's fr_surv_v0) cannot carry the driver's own buf and q across a call, because its dropped block is
   unnamed, and B's driver loop frees the same two blocks.

   READ lib/A/ACfn_cf.v's warning before changing a definition: the B program contract is consumed by the image-B cf
   driver (lib/B/ReplyTFIBBcf.v, through lib/B/ReplyDriverCfB.v), and over free Variables that step is FALSE (take
   fr_live_pre := fun _ => False), so these definitions ARE the content of the step, not bookkeeping.  Change them only
   with the agreement of W8 (which proves the contract) and the driver lane (which consumes it).

   - fr_live_pre_b: the room the call may use on top of everything live (input block included): CALL_ROOM_B = 2^33
     (below; a Theorem Labs lane's ruling (B), 2026-10-29 23:47Z), as A's CALL_ROOM.
   - fr_live_post_b: live bytes grow by at most ATABLE + OUT_MAX (g_src's 896-byte table and g_out's largest buffer,
     OUT_MAX = 133,953,540, below); k is NOT bounded (one write of 65,535 NULs makes about 131,128 allocator calls:
     ENTRY-FINDING.txt (sha256 2fea03396e1e; internal record)).
   - fr_hblks_b: the harness blocks that survive a call, as the globals name them: g_src's table (g_src <> 0) and
     g_out's buffer (g_capout <> 0).
   - fr_surv_b: a block live at the entry that is not an entry harness block is live at the return; a block live at the
     return was live at the entry or is a return harness block; a return harness block is fresh or was an entry
     harness block.
   - fr_FP_b: the journal footprint from the entry: the same two blocks as ranges, as the entry memory holds them.
     No sink_token: the entry writes no output (checksum_shape). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YP09 YI04 YI00 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_LLVMFuzzerTestOneInput_cut.
(* Required, not Imported: ra_rel and xcnt_ok, cited by their qualified names in fr_xcnt_ok_b *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_contract ReplyCnt.
Import ListNotations.
Open Scope Z_scope.

(* g_out's largest buffer, from the source (projects/plugin-hostd/fuzz_reply/source/fuzz_reply.c at the pin
   c8557374ad2e, the same source as image A's): g_capout <= 2 * (the most bytes the controller reads in one op), and the
   remove op (a drain, then the held gestures ended in the same op) sends at most 2 * R_s - 2 with
   R_s <= 511 * 65,535, so g_capout <= 133,953,536 <= OUT_MAX = 4 * 511 * 65,535 = 133,953,540.  The B twin of
   lib/A/ACfn_cf.v's OUT_MAX (a Theorem Labs lane, commit 15e5eb0c405 / d36b6f2c3b1; a Theorem Labs lane's ruling
   2026-10-30 01:39Z on a Theorem Labs lane's B1cOutMax, fresh reviewer OutMax4Review), whose comment gives the full
   derivation and the witnesses: the bound is a fact of the source, so it holds for image B without change.  The
   older 2^25 - 2 holds only for 1-byte sends from cap 0; the REMOVE op exceeds it. *)
Definition OUT_MAX : Z := 133953540.
(* OPS_MAX is the B cut's (W_LLVMFuzzerTestOneInput_cut.v, the source's fuzz_reply.c:115) *)
Lemma OUT_MAX_src : OUT_MAX = 2 * (2 * ((W_LLVMFuzzerTestOneInput_cut.OPS_MAX - 1) * 65535)).
Proof. reflexivity. Qed.

(* The room one call may use on top of everything live: 2^33, as A (lib/A/ACfn_cf.v CALL_ROOM, a Theorem Labs lane
   78ca01c6153). A Theorem Labs lane's ruling (B) 2026-10-29 23:47Z: ATABLE + OUT_MAX was too small for the arms' room
   premises (LS_write_room, LS_event_malloc, LS_rm_rr_pre, HLSRIG, LS_rf_room, LS_pro_oa, LS_add_room), which need
   CALL_ROOM_B >= ~6.58e9; the driver's H_live still holds (blocks_bytes stays below 2^30 over the <= 4 calls:
   2^27 + 3 * (ATABLE + OUT_MAX) < 2^30, and 2^30 + 2^33 <= LIVE_MAX = 2^34). fr_live_post_b keeps ATABLE + OUT_MAX. *)
Definition CALL_ROOM_B : Z := 2 ^ 33.

Definition fr_live_pre_b (S : astate) : Prop := blocks_bytes S + CALL_ROOM_B <= LIVE_MAX.

Definition fr_live_post_b (S S' : astate) (k : Z) : Prop :=
  blocks_bytes S' <= blocks_bytes S + ATABLE + OUT_MAX /\ 0 <= k.

(* WITNESS (VERIFY's satisfiability rule), as A's: a call that adds a relay table and a g_out buffer of 98,303,538
   bytes (a Theorem Labs lane's measured gest511_rm call on fuzz_reply.asan, the same source) meets fr_live_post_b, and so does
   any growth up to the bound; the driver meets fr_live_pre_b at every call after up to three such growths
   (YD1r_heap_cf.v H_live). *)
Lemma fr_live_post_b_remove_witness : forall S S' k, 0 <= k ->
  blocks_bytes S' = blocks_bytes S + ATABLE + 98303538 -> fr_live_post_b S S' k.
Proof. intros S S' k Hk H. unfold fr_live_post_b, OUT_MAX in *. lia. Qed.
Lemma fr_live_post_b_worst : forall S S' k, 0 <= k ->
  blocks_bytes S' = blocks_bytes S + ATABLE + 4 * (W_LLVMFuzzerTestOneInput_cut.OPS_MAX - 1) * 65535 ->
  fr_live_post_b S S' k.
Proof. intros S S' k Hk H. unfold fr_live_post_b, OUT_MAX, W_LLVMFuzzerTestOneInput_cut.OPS_MAX in *. lia. Qed.

Section fp. Context {rc : YM05.RunCeil}.
Definition fr_FP_b (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte)
  : list (Z * Z) :=
  let rd := aview tfibsegs (w_H W) mem in
  (match rdword rd (rg_src fr_globals_b) with Some G => if G =? 0 then [] else [(G, G + ATABLE)] | None => [] end) ++
  (match rdword rd (rg_out fr_globals_b), rdword rd (rg_capout fr_globals_b) with
   | Some o, Some c => if c =? 0 then [] else [(o, o + c)] | _, _ => [] end).
(* The harness blocks as (p, n) pairs, matching ablocks: g_src's table and g_out's buffer as the globals name them
   (the cut's model blocks (lm_G m, ATABLE) and aout_blks (lm_cap m) (lm_out m), tied to rg_src / rg_out / rg_capout by
   amodel_at). *)
Definition fr_hblks_b (W : world tfibsegs) (mem : word -> option byte) : list (Z * Z) :=
  let rd := aview tfibsegs (w_H W) mem in
  (match rdword rd (rg_src fr_globals_b) with Some G => if G =? 0 then [] else [(G, ATABLE)] | None => [] end) ++
  (match rdword rd (rg_out fr_globals_b), rdword rd (rg_capout fr_globals_b) with
   | Some o, Some c => if c =? 0 then [] else [(o, c)] | _, _ => [] end).
Definition fr_surv_b (B : asyms) (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte)
  (ly' : alayout) (S' : astate) (W' : world tfibsegs) (mem' : word -> option byte) : Prop :=
  (forall b, In b (ablocks B ly S) -> ~ In b (fr_hblks_b W mem) -> In b (ablocks B ly' S')) /\
  (forall b, In b (ablocks B ly' S') -> In b (fr_hblks_b W' mem') \/ In b (ablocks B ly S)) /\
  (forall b, In b (fr_hblks_b W' mem') -> ~ In b (ablocks B ly S) \/ In b (fr_hblks_b W mem)).
End fp.
(* the cut's CAPOUT clause (W_LLVMFuzzerTestOneInput_cut.v fr_lib_pre_cf / fr_lib_post_cf, the last conjunct) at
   segs := tfibsegs: g_capout reads a c with 0 <= c <= CAPOUT_MAX (CAPOUT_MAX is OUT_MAX above; val_mem keeps only the
   low 64 bits, so the lower bound is needed).  The view is W_rep.arm's body
   (mrestrict (w_H W) mem): arm takes an image instance (W_kit.v PAImg, W_img.v PB_fr), which needs an FPState and a
   RunCeil in context; the cut's clause is this one by conversion. *)
Definition fr_capout_ok_b (W : world tfibsegs) (mem : word -> option byte) : Prop :=
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
Definition fr_xcnt_ok_b (B : asyms) (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte)
  (inp : list (Z * Z)) : Prop :=
  exists T0 c O mx cap out, W_contract.ra_rel B W_LLVMFuzzerTestOneInput_cut.fr_RG ly S W mem T0 [] /\
    aout_at B W_LLVMFuzzerTestOneInput_cut.fr_RG ly S W mem c O mx (Z.of_nat (length O)) cap out /\
    ReplyCnt.xcnt_ok B S ly inp T0 cap out.
(* That this is the cut's text is checked where both meet: ReplyDriverCfB.v's fr_pre_bridge passes it to
   fr_lib_pre_cf_x by position (fresh reviewer DrvTailReview, 05:5xZ: an iff_refl Goal here checked nothing). *)
End xc.
