(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: group RI-gone of the image-A top (W_LLVMFuzzerTestOneInput_top_x.v, the rows
   RI_gone_pairs / RI_gone_read / RI_gone_step / RI_gone_end) at RINV := fr_RINV (ReplyRINV.v).  Proves no function
   walk (model-rule obligations only).
   Part 1 (over ReplyRINV.v's copies of the gone model, verbatim the same text as gone_base.v's):
   - RI_gone_pairs_holds: fr_RINV's pairing hj of the table with the open sources is a gn_pairs witness.  The size
     bounds gn_pair_ok asks come from fr_RINV's cost bound (fr_cost <= c_n < 2 ^ 26: a pending stream and a key count
     are parts of one entry's cost) and from fr_pair_ok's ecap_ok.
   - RI_gone_read_holds: a slot k that reads (gn_reads m k = 1) holds the source of an open entry j; that entry's
     gn_pair_ok source is at slot k (fr_RINV's distinct fds, RI_fds_holds), so after relay_instance_gone slot k holds
     rig_post's source for entry j, which rig_rel's dr_rel leaves drained (pending list empty, offset 0).
   - RI_gone_read_sat: one state meets all of RI_gone_read's premises (and RI_gone_pairs's).
   - Section collapse / collapse2: the records of rounds 1 and 2 of the gone rules' texts (bb9dae5d905, a1a3591c77c),
     which were false at the instance; machine-checked counter-instances, not proofs of the rows.
   Part 2 (over W_LLVMFuzzerTestOneInput_gone_base.v's own model): RI_gone_pairs_plug / RI_gone_read_plug restate
   part 1 at gone_base's GN_RI_pairs / GN_RI_read; then the step and end rows.
   - The table-order loop (gn_run) as an invariant (rg_inv): every entry's slot, once processed, holds what
     check_no_loss and check_shape_ends left of what relay_instance_gone left there; when gone = 0, `at` is the
     entry's position in the stream relay_instance_gone sent (rg_acc_pos), which is the entries' drained lines and
     then their ended keys' end lines (rg_rel_dec, rg_strm).
   - RI_gone_step_holds(_c): GN_RI_step of a working branch a39b599f92e (copied verbatim as
     GN_RI_step_d) at MT := ameter_triv, RINV := fr_RINV, MMAX := WR_MMAX, LS := fr_LS3 B / fr_LS3c B.  The LS-side
     conjunct cnl_room is a Theorem Labs lane's gx6_step_room(_c) (ReplyLS3cTopxGoneF.v at b25d82fcf04); mo_ok is True at
     ameter_triv; the rest is RINV-side (rg_step_rinv_side).
   - RI_gone_end_holds_q5(_c): GN_RI_end of a39b599f92e (copied as GN_RI_end_q5) with REQ5 (no held list's capacity
     shrinks from m to mc) as one more, last, premise: s5-r1d's gx6_end_LS3(_c) needs it, and a39b599f92e's gn_cnl_ok
     does not carry `hl_cap (hs_held h) <= hl_cap H'` from which ReplyLS3cTopxGoneH.v's gxh_req5 derives it.
   - GN_RI_step_r3 (Section rg3): the record of round 3 (aa34c06e82c): without re_U NUL-free the step row is false.
   Local helpers rg_lines_nz / rg_upds_in / rg_W_read_lines_nz state what a Theorem Labs lane's ReplyRINV_a12.v
   (lines_nul_free / upds_nul_free) states; they stay local. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyRINV_gone.v, with its module paths and module names changed; 362 of its 481 lines of code are new or changed and 2804 lines of the source are left out. *)
(* proves no function (rule 24; kind: segment lemma): the SATISFIABILITY witnesses of the premises that the gone
   arm's re-fitted text (REQ1-REQ5, C1, C2) added to lib/B/W_LLVMFuzzerTestOneInput_gone_base.v's GN_RI_step,
   GN_RI_end, gn_cnl_ok and GN_CNT_step, at image B's real instance. *)
(* VERIFY's rule (2026-10-29 21:38Z): before a statement text fans out to several provers, its owner shows it
   satisfiable AT THE REAL INSTANCE, not at a trivial one.  The B text re-fitted to A's gone arm
   (lib/B/W_LLVMFuzzerTestOneInput_gone_base.v, sha256 6e72185dcc4d; internal record, as the room branch
   a working branch 85038211e65 carries it: cand13 commit 2 63bca49e574 + the arms base
   6fbfc8c80e3b + this text, merged here)
   fans out to the phase walks (gone_base_x, p0..p6, gone_tk, gone) and to the two RI rows, so every premise it added
   needs a state where all of them hold TOGETHER.  This file gives that state and fires each statement at it:
   GN_RI_step, GN_RI_end, GN_CNT_step, GN_CNT_rig (the count rule of the relay_instance_gone call, which a Theorem Labs lane
   consumes at CNTRIG, gone_p3_x :147 and gone_x :168) and GN_LS_rig; then it names each at image B's own TfibB
   (Section inst).  The three fires lemmas that read an LS take it as a parameter with its fact at this state as a
   hypothesis, so the v2 instance below and B's v3, when it can be loaded, plug into the same proof.
   Relocated from the proved image-A twin ReplyRINV_gone.v (sha256 af44c72ef1b9; internal record)
   ("A" below): Section nsat (A :3038-3200) rn_* / rn_common / RI_gone_step_new_sat /
   RI_gone_end_new_sat, and the held-list growth of A's Section rg3 (A :2876-2995 rg3_h1 / rg3_E / rg3_H / rg3_cnl)
   as the NON-TRIVIAL gn_cnl_ok witness (C1 and REQ5(b) at a capacity that really grows, 0 -> 8).

   THE INSTANCE.  B := TfibB (lib/B/YD2l.v, the image-B start-up instance); RINV := ReplyRINVB.fr_RINV;
   LS := ReplyLSB.fr_LS TfibB CR, the LS the B top names at its own check (lib/B/W_LLVMFuzzerTestOneInput_top_x.v
   :819 `Local Notation LSx := (ReplyLSB.fr_LS TfibB CR)`), at every call room CR the driver's room fits in
   (rn_LS_room: the B driver's 2 ^ 33, YCfn_cf.CALL_ROOM_B at a Theorem Labs lane's 6dd1d8ad0dfe, is one); MT := ANY
   LAWFUL METER (ameter_laws, YC5d.v), not ameter_triv: the witness needs only mo_le_refl; MMAX := ANY (no premise
   of the four statements reads it).  The state is A's, at B's records: one operation done (t = 1), the gone op
   (byte 5) next at lm_k = 1 of a 2-byte input, one relay entry whose line buffer is allocated (an earlier drain),
   its source open at slot 0 with nothing pending; the live blocks are the input, the table, the entry's buffer and
   the source's partial buffer, each a chunk of the allocator state.

   NOT v3.  A's witness states its LS fact at A's v3 (ReplyLS3.fr_LS3).  B's v3 twin lib/B/ReplyB3LS3.v
   (6dd1d8ad0dfe, sha256 50eb7bb8b605; internal record) STILL CANNOT BE LOADED on cand13: it Requires
   lib/B/W_op_add.v, and its helper ReplyB3Base.v Requires lib/B/W_LLVMFuzzerTestOneInput_arm_event.v; both are on
   a Theorem Labs lane's own list of files that fail in the whole-B build of the kit tree (cand13 3b4d6e514910,
   whole-B-breaks.txt (sha256 207433003b15; internal record): W_op_add.v:302 and W_list_push.v:339 "has type list (list Z) while it
   is expected to have type roomp", arm_event.v:2880), and a build of ReplyB3LS3.vo on this tree reproduces all
   three.  They are B-walk consumers of the room round, not files this file reads.  So the LS fact below is the v2
   instance the B top names.  WHEN THOSE LAND, restate rn_LS at ReplyB3LS3.fr_LS3 TfibB YCfn_cf.CALL_ROOM_B (the
   same state: its PHI3 adds E_ENT + K0 over PHI, both far under the bound) and pass it to the two fires lemmas,
   which take the LS as a parameter; nothing else in this file changes, every other premise being RINV- or
   model-side.

   NOT DUPLICATED.  RI_gone_read_sat (GN_RI_read's premises) and the old text's rn_common already exist at B in
   lib/B/ReplyRINVB_gone.v (a working branch 40b5ea53c631, Module RG); this file does not copy them.
   A's rg2 / rgc counter-instances (A :444-570, :580-704) belong to the FINDINGS of the old rows, not to the new
   premises, and are not relocated either.

   A -> B swaps: lib/A's modules -> lib/B's of the same name (W_rep, W_contract, W_sites, W_frame, _cut,
   _gone_base); lib/A/ReplyRINV -> lib/B/ReplyRINVB; A's oa_new_src (lib/A/W_op_add.v) -> ReplyRINVB.pro_new_src (a
   verbatim copy of lib/B/W_op_add.v oa_new_src, which this file cannot load either, see above); A's ReplyLS3.ls3_*
   state (its layout, chunks, world and model) -> the rs_* copies below, written out here because ReplyB3LS3.v
   cannot be loaded (they are plain definitions, no proof is borrowed); ACfn_cf.CALL_ROOM -> the Section-free
   parameter CR with its room premise.  No image numeral is read by any proof here: the constants are the model's
   (4 slots, FIRST_FD 100, CLIENT_FD 3, ATABLE, APARTIAL, 8192, 2 ^ 26, LIVE_MAX), which ReplyRINVB.v and W_rep.v
   check against image B's binary.

   BUILD INPUTS: none.  This file builds from git, with nothing untracked in the worktree. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
drain_b_c gestures_end_b_c relay_remove_b_c relay_instance_gone_b_c SlotInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
(* The sink-instance guard (MERGE.md (sha256 0694aca87ccd; internal record) rule 3), as lib/B's segment files Require it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_head.
(* the statements under test, the model invariant, the LS and the image instance *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_gone_base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyRINVB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyLSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YD2l.
(* Required, not Imported: the live counts GN_CNT_step names, cited by their qualified names (as gone_base does) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section nsat.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable Bx : asyms.

(* ================================================================== the state (A :3038-3057, at B's records)
   A's ReplyLS3.ls3_* layout / chunks / world / model, written out (ReplyB3LS3.v cannot be loaded here, see the
   header): the four live chunks are the 2-byte input, the relay's 896-byte table, the entry's 8192-byte line
   buffer and the source's 6000-byte partial buffer. *)
Definition rs_ly : alayout := ALayout 0 0 0 0 0 0 0 0 0 0 0 0 [] [] 0 [] (0, 0) (fun _ => 0).
Definition rs_k0 : YG00.chunk := YG00.mkChunk (YG00.PPrim 0) 2 YG00.CAllocated.
Definition rs_k1 : YG00.chunk := YG00.mkChunk (YG00.PPrim 4096) ATABLE YG00.CAllocated.
Definition rs_k3 : YG00.chunk := YG00.mkChunk (YG00.PPrim 32768) 8192 YG00.CAllocated.
Definition rs_k2 : YG00.chunk := YG00.mkChunk (YG00.PPrim 16384) APARTIAL YG00.CAllocated.
Definition rs_S : astate := YG00.set_chunks [rs_k0; rs_k1; rs_k3; rs_k2] YG00.init_state.
Lemma rs_Hoff : H_off_segments segs (fun _ => false).
Proof. intros a Ha. discriminate. Qed.
Definition rs_W : world segs := mkW segs (fun _ => false) [] rs_Hoff (Forall_nil _) (fun _ _ => eq_refl).
Definition rs_vm : VmMaps :=
  mkVmMapsFull [] [] [] (Z_to_bv 64 0) (Z_to_bv 64 0) 0 (Z_to_bv 64 0) (Z_to_bv 64 0).
Definition rs_md : Model := mkModel [] rs_vm IEof [] None None None.
Definition rs_p : Z := sptr_addr Bx rs_ly (YG00.ck_user rs_k0).
Definition rs_G : Z := sptr_addr Bx rs_ly (YG00.ck_user rs_k1).
Definition rs_b : Z := sptr_addr Bx rs_ly (YG00.ck_user rs_k3).
Definition rs_q : Z := sptr_addr Bx rs_ly (YG00.ck_user rs_k2).
(* the entry's two bytes: operation 4 done, operation 5 (the gone op) next at lm_k = 1.  The entry's memory reads 0
   everywhere (it is read by one premise only, GN_LS_rig's CAPOUT clause: g_capout is 0 at the first call, a .bss
   word); every other premise reads the input list, the layout and the allocator state. *)
Definition rn_cx : lfcx (rc := rc) :=
  LFCX rs_ly rs_S rs_W bvmap_empty (fun _ => Some (Z_to_bv 8 0)) rs_md rs_p 2
    [Z_to_bv 8 4; Z_to_bv 8 5] 0.
Definition rn_c0 : ctl := CTL 3 0 0 0 0.
Definition rn_e : rentry := RE 100 0 0 (repeat (Z_to_bv 8 0) 4) rs_b 0 8192 0 0 (repeat (Z_to_bv 8 0) 4) [] [] [].
Definition rn_h : hsrc := pro_new_src 100 rs_q [].
Definition rn_m : lmod := LM 1 [Some rn_h; None; None; None] rs_G [rn_e] rn_c0 [] 0 0 0 0 1.
Definition rn_c2 : ctl := dr_ctl rn_c0 rn_h 0.
Definition rn_m1 : lmod := LM (gn_kq rn_cx rn_m) (lm_hs rn_m) rs_G [rn_e] rn_c2 [] 0 0 0 0 1.
Definition rn_h' : hsrc := set_exp_held rn_h (hs_expected rn_h) (hs_held rn_h).
Definition rn_h'' : hsrc := set_held rn_h' (hs_held rn_h').
Definition rn_mc : lmod := gn_set rn_m1 0 rn_h''.

(* relay_instance_gone's drain of the entry: nothing pending, nothing relayed (A :3059-3065) *)
Lemma rn_dr_rel : dr_rel rn_c0 0 0 0 rn_e rn_h rn_e rn_h [].
Proof.
  unfold dr_rel. vm_compute.
  repeat match goal with |- _ /\ _ => split end;
    first [ reflexivity | (intros Hx; discriminate Hx) | (apply NoDup_ListNoDup; constructor)
          | (intros y; split; intros []) | (intros _; reflexivity) ].
Qed.

(* ================================================================== the premises the four statements share
   (A :3068-3155 rn_common, with REQ1 (0 <= lm_cap), REQ2 (the entry clause) and REQ3 (the pending clause) of the
   re-fitted text; the LS conjunct is rn_LS below, the only one that names a call room) *)
Lemma rn_common :
  fr_RINV rn_cx 1 rn_m /\ gn_op rn_cx 1 rn_m /\
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es rn_m) /\
  0 <= lm_cap rn_m /\
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL /\ (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
    ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))) (lm_es rn_m) /\
  Forall (fun o => match o with
    | Some h0 => ((hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
                  (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) /\
                 Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h0))
    | None => True end) (lm_hs rn_m) /\
  gn_pairs rn_m [(rn_h, 0%nat)] /\ gn_after_rig rn_cx rn_m [(rn_h, 0%nat)] [(rn_e, rn_h)] rn_c2 [] 0 0 rn_m1 /\
  gn_rig_ok rn_cx rn_m [(rn_h, 0%nat)] [(rn_e, rn_h)] rn_c2 [] 0.
Proof.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - (* fr_RINV after one operation, as RI_pro_holds_b proves it at the first head *)
    split; [|split; [|split]].
    + unfold fr_count, rn_m, nopen, OPS_MAX. cbn. lia.
    + unfold fr_relay, rn_m. cbn [lm_hs lm_es lm_nfd lm_k].
      split; [reflexivity|].
      split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
      split; [constructor; [cbn; lia | constructor]|].
      split.
      { constructor; [|constructor]. unfold fr_entry_ok. cbn.
        split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [apply NoDup_ListNoDup; constructor | left; reflexivity]. }
      exists [(rn_h, 0%nat)].
      split.
      { constructor; [|constructor]. unfold fr_pair_ok, rn_h. cbn.
        split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
        split; [intros _; split; [reflexivity | intros _; reflexivity]|].
        split; [intros y; split; intros []|]. split; [apply NoDup_ListNoDup; constructor|]. split; [reflexivity|].
        split; [left; reflexivity|]. split; [lia|]. split; [unfold SlotInv.WRITE_MAX; lia | lia]. }
      split; [apply NoDup_ListNoDup; repeat constructor; intros []|].
      split.
      { intros i Hi Ho. destruct i as [|[|[|[|i]]]]; cbn in Ho |- *;
          first [discriminate Ho | reflexivity | lia]. }
      unfold fr_cost, fr_pair_cost. cbn. lia.
    + cbn. lia.
    + unfold fr_gone, rn_m, rn_c0. cbn [lm_gn lm_c ct_cl ct_br ct_dd]. split; intros H; [auto | discriminate H].
  - (* the gone op is next: in_byte at lm_k = 1 is 5, the stream is empty, t < OPS_MAX *)
    unfold gn_op, rn_m, rn_cx, in_byte. cbn. split; [reflexivity|]. split; [reflexivity|]. unfold OPS_MAX. lia.
  - (* no 0 byte in the entry's unfinished line, no key held *)
    constructor; [|constructor]. cbn. split; [intros []|constructor].
  - (* REQ1: g_capout is 0 *)
    cbn. lia.
  - (* REQ2: the entry's line is empty, its buffer is one of the three sizes, it holds no key *)
    constructor; [|constructor]. cbn. split; [unfold APARTIAL; lia|].
    split; [right; left; reflexivity | left; split; reflexivity].
  - (* REQ3: slot 0 has nothing pending; the other three are closed *)
    constructor; [|constructor; [exact I | constructor; [exact I | constructor; [exact I | constructor]]]].
    cbn. split; [left; split; reflexivity | constructor].
  - (* gn_pairs: the one open entry with slot 0's source *)
    unfold gn_pairs, rn_m. cbn [lm_es]. split; [reflexivity|]. split.
    + constructor; [|constructor]. intros _. unfold gn_pair_ok, rn_h, pro_new_src. cbn [fst snd lm_hs nth].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros _; reflexivity|].
      unfold pending_stream, re_nheld. vm_compute. repeat match goal with |- _ /\ _ => split end; reflexivity.
    + apply NoDup_ListNoDup. cbn. constructor; [intros [] | constructor].
  - (* gn_after_rig: the table and slot 0 are what the drain left *)
    unfold gn_after_rig, rn_m1.
    do 11 (split; [reflexivity|]). split.
    + intros j _ _. reflexivity.
    + intros [|i] Hi _; [reflexivity | cbn in Hi; lia].
  - (* gn_rig_ok: rig_rel is the one drain (rn_dr_rel) and no key ended *)
    unfold gn_rig_ok. split; [|split; [reflexivity | split]].
    + generalize (relay_instance_gone_b_c.instance_prefix (gn_id rn_cx rn_m)). intros pre.
      unfold rn_m. cbn [rig_rel combine lm_es lm_mx lm_c lm_O lm_cap].
      exists rn_e, 0, []. cbv zeta. cbn [re_eof rn_e Z.eqb Pos.eqb].
      split; [exact rn_dr_rel|]. split; [reflexivity|].
      vm_compute. split; [reflexivity | split; reflexivity].
    + constructor; [|constructor]. unfold gn_entry_model, rn_e, re_nheld. vm_compute.
      repeat match goal with |- _ /\ _ => split end;
        first [ (left; reflexivity) | reflexivity | (intros Hx; discriminate Hx) | (apply NoDup_ListNoDup; constructor) ].
    + apply NoDup_ListNoDup. cbn. constructor; [intros [] | constructor].
Qed.

(* ================================================================== the LS premise, at the LS the B top names
   (ReplyLSB.fr_LS Bx CR; the base's top_x :819).  Every call room the state leaves under LIVE_MAX will do; the B
   driver's own room (2 ^ 33) is one (rn_LS_room). *)
Lemma rn_LS : forall CR, 2 + ATABLE + 8192 + APARTIAL + CR <= LIVE_MAX ->
  ReplyLSB.fr_LS Bx CR rn_cx 1 rn_m rs_ly rs_S.
Proof.
  intros CR HCR. exists [], 0.
  assert (EA : ablocks Bx rs_ly rs_S = input_blks rn_cx ++ model_blks rn_m ++ []) by reflexivity.
  assert (Hbb : blocks_bytes rs_S = 2 + ATABLE + 8192 + APARTIAL) by (vm_compute; reflexivity).
  assert (Hin : bsum (input_blks rn_cx) = 2) by reflexivity.
  assert (Hrest : bsum (@nil (Z * Z)) = 0) by reflexivity.
  assert (HS : c_S rn_cx = rs_S) by reflexivity.
  assert (Hn : c_n rn_cx = 2) by reflexivity.
  assert (HL : LIVE_MAX = 17179869184) by reflexivity.
  assert (En : ReplyLSB.npend rn_m = 0) by reflexivity.
  assert (Ek : ReplyLSB.kk rn_cx rn_m = 1) by reflexivity.
  assert (Eo : nopen (lm_hs rn_m) = 1) by reflexivity.
  assert (Ep : ReplyLSB.PHI rn_m <= 100000) by (vm_compute; intros Hx; discriminate Hx).
  unfold APARTIAL, ATABLE in HCR.
  rewrite EA, HS, Hbb, Hn, Hin, Hrest, En, Ek, Eo.
  split; [apply Permutation_refl|].
  unfold ReplyLSB.MB_K, ReplyLSB.MB_C, ATABLE, APARTIAL in *.
  refine (conj _ (conj _ (conj _ (conj eq_refl (conj _ _))))); lia.
Qed.
Lemma rn_LS_room : 2 + ATABLE + 8192 + APARTIAL + 2 ^ 33 <= LIVE_MAX.
Proof. unfold ATABLE, APARTIAL, LIVE_MAX. lia. Qed.

(* ================================================================== KF-COUNT (gone_base 187cede058c): gn_cst's bound
   cst <= r + q at this state needs relay_instance_gone's meter cost r to be non-negative.  A trace whose requests all
   have a non-negative size costs at least 0 at a lawful meter (mo_malloc_nonneg / mo_free_nonneg, Reusable/YC5d.v
   :32 / :34), and relay_instance_gone's trace at this state is such a trace. *)
Lemma rn_tr_cost_nonneg : forall (MT : ameter_ops), ameter_laws MT -> forall (P : Type) (tr : list (RelayRunT.rev P)),
  Forall (fun ev => 0 <= match ev with RelayRunT.RMalloc n => n | RelayRunT.RFree _ _ => 0
                                       | RelayRunT.RRealloc _ n _ => n end) tr ->
  0 <= tr_cost MT tr.
Proof.
  intros MT ML P tr H. pose proof (mo_free_nonneg MT ML) as Hf.
  induction H as [|ev tr Hev _ IH]; [unfold tr_cost; cbn; lia|].
  change (tr_cost MT (ev :: tr)) with
    ((match ev with RelayRunT.RMalloc n => mo_malloc MT n + mo_free MT | RelayRunT.RFree _ _ => mo_free MT
      | RelayRunT.RRealloc _ n _ => mo_malloc MT n + mo_free MT end) + tr_cost MT tr).
  destruct ev as [n|n a|k n a]; cbn iota beta in Hev |- *;
    [pose proof (mo_malloc_nonneg MT ML n Hev) | | pose proof (mo_malloc_nonneg MT ML n Hev)]; lia.
Qed.
Lemma rn_rig_cost_nonneg : forall (MT : ameter_ops), ameter_laws MT ->
  0 <= tr_cost MT (rig_tr (lm_c rn_m) (lm_mx rn_m) (Z.of_nat (length (lm_O rn_m))) (lm_cap rn_m) (gn_id rn_cx rn_m)
         (lm_es rn_m) [(rn_h, 0%nat)]).
Proof.
  intros MT ML. apply (rn_tr_cost_nonneg MT ML). vm_compute.
  repeat (apply Forall_cons; [vm_compute; intros Hx; discriminate Hx|]). apply Forall_nil.
Qed.
(* gn_cst at this state, for every loop cost q >= 0 and cst := 0: relay_instance_gone's pairing is rn_common's *)
Lemma rn_cst : forall (MT : ameter_ops), ameter_laws MT -> forall q, 0 <= q -> gn_cst MT rn_cx rn_m rn_m1 q 0.
Proof.
  intros MT ML q Hq.
  destruct rn_common as (_ & _ & _ & _ & _ & _ & HPR & HAR & _).
  unfold gn_cst, gn_rigc.
  exists (tr_cost MT (rig_tr (lm_c rn_m) (lm_mx rn_m) (Z.of_nat (length (lm_O rn_m))) (lm_cap rn_m) (gn_id rn_cx rn_m)
    (lm_es rn_m) [(rn_h, 0%nat)])).
  split; [exists [(rn_h, 0%nat)], [(rn_e, rn_h)], rn_c2, [], 0, 0; split; [exact HPR|];
    split; [exact HAR | reflexivity]|].
  pose proof (rn_rig_cost_nonneg MT ML). lia.
Qed.

(* ================================================================== GN_RI_step's own premises at the loop's first
   call (gn_run0 / gn_runc0: slot 0, entry 0, at = 0, loop cost q = 0; cst = 0), REQ4 last (A :3157-3170) *)
Lemma RI_gone_step_new_sat : forall (MT : ameter_ops), ameter_laws MT ->
  gn_run (gn_pre rn_cx rn_m) rn_m1 rn_m1 0 0%nat 0%nat /\ gn_runc MT (gn_pre rn_cx rn_m) rn_m1 rn_m1 0 0%nat 0%nat 0 /\
  mo_le MT rs_S rs_S 0 /\ gn_cst MT rn_cx rn_m rn_m1 0 0 /\
  (forall rest, Permutation (ablocks Bx rs_ly rs_S) (input_blks rn_cx ++ model_blks rn_m ++ rest) ->
     Permutation (ablocks Bx rs_ly rs_S) (input_blks rn_cx ++ model_blks rn_m1 ++ rest)) /\
  (0 < length (lm_es rn_m1))%nat /\ (0 < 4)%nat /\
  nth 0 (lm_hs rn_m1) None = Some rn_h /\ hs_fd rn_h = re_fd (nth 0 (lm_es rn_m1) gn_e0) /\
  (forall j hj, nth j (lm_hs rn_m1) None = Some hj -> hl_n (hs_held hj) <= hl_cap (hs_held hj)).
Proof.
  intros MT ML.
  split; [exact (gn_run0 _ _)|]. split; [constructor|]. split; [exact (mo_le_refl MT ML rs_S)|].
  split; [exact (rn_cst MT ML 0 (Z.le_refl 0))|].
  split; [intros rest H; exact H|].
  split; [cbn; lia|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
  intros [|[|[|[|j]]]] hj Hj; cbn in Hj; try discriminate Hj; [|destruct j; discriminate Hj].
  injection Hj as <-. vm_compute. intros Hx; discriminate Hx.
Qed.

(* ================================================================== GN_RI_end's own premises after the loop: the
   call at slot 0, three slots passed, the next entry (A :3172-3199; B's REQ5 lives inside gn_cnl_ok, which the
   gn_run_call below discharges); gn_runc's loop cost is the one call's, gn_runc_call's sum at q = 0; cst = 0 *)
Lemma RI_gone_end_new_sat : forall (MT : ameter_ops), ameter_laws MT ->
  (lm_gn rn_m = 0 \/ lm_gn rn_m = 1) /\
  gn_run (gn_pre rn_cx rn_m) rn_m1 rn_mc 0 (length (lm_es rn_m1)) 0%nat /\
  gn_runc MT (gn_pre rn_cx rn_m) rn_m1 rn_mc 0 (length (lm_es rn_m1)) 0%nat
    (0 + cnl_cost MT (hs_expected rn_h) (hs_held rn_h) + cshe_cost MT (hs_held rn_h')) /\
  mo_le MT rs_S rs_S 0 /\
  gn_cst MT rn_cx rn_m rn_m1 (0 + cnl_cost MT (hs_expected rn_h) (hs_held rn_h) + cshe_cost MT (hs_held rn_h')) 0 /\
  (forall rest, Permutation (ablocks Bx rs_ly rs_S) (input_blks rn_cx ++ model_blks rn_m ++ rest) ->
     Permutation (ablocks Bx rs_ly rs_S) (input_blks rn_cx ++ model_blks rn_mc ++ rest)).
Proof.
  intros MT ML.
  assert (HCNL : gn_cnl_ok rn_h rn_h' (hs_expected rn_h) (hs_held rn_h)).
  { unfold gn_cnl_ok. vm_compute.
    repeat match goal with |- _ /\ _ => split end;
      first [ reflexivity | (intros Hx; discriminate Hx) | (apply NoDup_ListNoDup; constructor) ]. }
  assert (HCSHE : gn_cshe_ok (gn_pre rn_cx rn_m) (lm_gn rn_m1) (gn_at1 (lm_gn rn_m1) 0 rn_h) (lm_O rn_m1) rn_h' rn_h''
    [] 0).
  { unfold gn_cshe_ok. exists (hs_held rn_h').
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply NoDup_ListNoDup; constructor|]. split; [lia|].
    right. split; reflexivity. }
  split; [left; reflexivity|]. split.
  { change (length (lm_es rn_m1)) with 1%nat. apply gn_run_next.
    apply gn_run_skip; [|lia | left; reflexivity].
    apply gn_run_skip; [|lia | left; reflexivity].
    apply gn_run_skip; [|lia | left; reflexivity].
    unfold rn_mc.
    exact (gn_run_call _ _ rn_m1 0 0%nat 0%nat rn_h rn_h' rn_h'' (hs_expected rn_h) (hs_held rn_h)
      [] 0 (gn_run0 _ _) ltac:(lia) (Nat.lt_0_succ 0) eq_refl eq_refl HCNL HCSHE). }
  split.
  { change (length (lm_es rn_m1)) with 1%nat. apply gn_runc_next.
    apply gn_runc_skip; [|lia | left; reflexivity].
    apply gn_runc_skip; [|lia | left; reflexivity].
    apply gn_runc_skip; [|lia | left; reflexivity].
    unfold rn_mc.
    exact (gn_runc_call _ _ _ rn_m1 0 0%nat 0%nat 0 rn_h rn_h' rn_h'' (hs_expected rn_h) (hs_held rn_h)
      [] 0 (gn_runc0 _ _ _) ltac:(lia) (Nat.lt_0_succ 0) eq_refl eq_refl HCNL HCSHE). }
  split; [exact (mo_le_refl MT ML rs_S)|].
  split.
  { apply (rn_cst MT ML). assert (Eq : 0 + cnl_cost MT (hs_expected rn_h) (hs_held rn_h) + cshe_cost MT (hs_held rn_h')
      = 0) by reflexivity.
    rewrite Eq. lia. }
  intros rest H; exact H.
Qed.

(* ================================================================== GN_CNT_step's own premises (C2 and the block
   clause; the rest are GN_RI_step's, above).  C2 is `Forall (the key-array clause) (map fst qs)`: the table
   relay_instance_gone leaves holds no key, so its key array is the null one. *)
Lemma rn_blks_nonneg : forall b, In b (model_blks rn_m) -> 0 <= snd b.
Proof.
  intros b Hb. cbn in Hb.
  destruct Hb as [<- | [<- | [<- | []]]]; cbn [snd]; unfold ATABLE, APARTIAL; lia.
Qed.
Lemma rn_c2_entries :
  Forall (fun e => (re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))
    (map fst [(rn_e, rn_h)]).
Proof. constructor; [left; split; reflexivity | constructor]. Qed.

(* ================================================================== gn_cnl_ok's two new conjuncts (REQ5(b): the
   held list's capacity never shrinks; C1: it is EXACTLY cnl_cap) are met at a call that really grows the list.
   A :2876-2995 (Section rg3): the source's expected list holds one gesture line, so check_no_loss appends one key
   and the held list's capacity goes 0 -> 8 (list_push's first vector).  A NUL byte inside the line is what makes
   A's rg3 a counter-instance of the round-3 text; it plays no part here (gn_cnl_ok reads no NUL clause). *)
Definition cn_pre : list Z := relay_instance_gone_b_c.instance_prefix 0.
Definition cn_Wz : list Z := cn_pre ++ [97; 0; 98].
Definition cn_lz : list Z := cn_Wz ++ [32; 98; 101; 103; 105; 110].
Definition cn_W : list byte := map (Z_to_bv 8) cn_Wz.
(* the source after the drain: nothing pending, the line W ++ " begin" expected, nothing held (capacity 0) *)
Definition cn_h : hsrc :=
  HS 100 1 0 0 (HL 0 8 [] []) 0 0 cn_W 0 0 [] (HL 0 8 [(0, map (Z_to_bv 8) cn_lz)] []) empty_list.
Definition cn_E : hlist := HL 0 8 [] [].
Definition cn_H : hlist := HL 0 8 [(0, cn_W)] [].

Lemma cn_cnl : gn_cnl_ok cn_h (set_exp_held cn_h cn_E cn_H) cn_E cn_H.
Proof.
  unfold gn_cnl_ok. vm_compute.
  repeat match goal with |- _ /\ _ => split end;
    first [ reflexivity | (intros Hx; discriminate Hx) | (apply NoDup_ListNoDup; repeat constructor; intros [])
          | (apply NoDup_ListNoDup; constructor) ].
Qed.
(* the growth the witness exercises: the held list goes from no vector to a vector of 8 (REQ5(b) is 0 <= 8, not
   0 <= 0, and C1's cnl_cap is read at a record that appends) *)
Lemma cn_grows : hl_cap (hs_held cn_h) = 0 /\ hl_cap cn_H = 8 /\ hl_recs (hs_expected cn_h) <> [].
Proof. split; [reflexivity|]. split; [reflexivity | cbn; intros Hx; discriminate Hx]. Qed.

(* ================================================================== THE CHECK: each statement FIRED at the state.
   Applying the statement to the witness type-checks its WHOLE premise list, in its order, so none can be missed. *)
Lemma GN_RI_step_fires : forall (MT : ameter_ops) (MMAX : Z)
    (LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop), ameter_laws MT ->
  LS rn_cx 1 rn_m rs_ly rs_S ->
  GN_RI_step Bx MT LS fr_RINV MMAX ->
  NoDup (texts (hs_held rn_h)) /\
  hl_n (hs_expected rn_h) < 2 ^ 26 /\
  hl_n (hs_held rn_h) + Z.of_nat (count_begin (texts (hs_expected rn_h))) < 2 ^ 22 /\
  0 <= 0 <= Z.of_nat (length (lm_O rn_m1)) /\
  Z.of_nat (length (lm_O rn_m1)) < 2 ^ 32 /\
  (lm_gn rn_m1 = 0 -> exists rest, skipn (Z.to_nat 0) (lm_O rn_m1) = bstream (hs_expected rn_h) ++ rest) /\
  AREC * capb (hs_held rn_h) (hs_expected rn_h) < 2 ^ 32 /\
  cnl_room MMAX (blocks_bytes rs_S) (texts (hs_held rn_h)) (hl_cap (hs_held rn_h))
    (hl_recs (hs_expected rn_h)) /\
  mo_ok MT rs_S (cnl_cost MT (hs_expected rn_h) (hs_held rn_h)) /\
  (forall h' E' H' (Sy : astate), gn_cnl_ok rn_h h' E' H' ->
     mo_le MT rs_S Sy (cnl_cost MT (hs_expected rn_h) (hs_held rn_h)) ->
     hl_n (hs_held h') < 2 ^ 26 /\
     gn_at1 (lm_gn rn_m1) 0 rn_h <= Z.of_nat (length (lm_O rn_m1)) /\
     (lm_gn rn_m1 = 0 -> ends_run (gn_pre rn_cx rn_m) (hl_recs (hs_held h'))
        (skipn (Z.to_nat (gn_at1 (lm_gn rn_m1) 0 rn_h)) (lm_O rn_m1))
        (want_of (gn_pre rn_cx rn_m) (hl_recs (hs_held h'))) <> None) /\
     mo_ok MT Sy (hl_n (hs_held h') * mo_free MT)).
Proof.
  intros MT MMAX LS ML HLS HST.
  destruct rn_common as (HRI & HOP & HNZ & HCAP & HENT & HPEND & HPR & HAR & HOK).
  destruct (RI_gone_step_new_sat MT ML) as (HRUN & HRUNC & HMLE & HCST & HPERM & HI & HK & HNTH & HFD & HREQ4).
  exact (HST rn_cx 1 rn_m rs_ly rs_S [(rn_h, 0%nat)] [(rn_e, rn_h)] rn_c2 [] 0 0 rn_m1 rn_m1 0 0%nat 0%nat rn_h
    rs_ly rs_S 0 0 HRI HOP HNZ HCAP HENT HPEND HLS HPR HAR HOK HRUN HRUNC HMLE HCST HPERM HI HK HNTH HFD HREQ4).
Qed.

Lemma GN_RI_end_fires : forall (MT : ameter_ops)
    (LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop), ameter_laws MT ->
  LS rn_cx 1 rn_m rs_ly rs_S ->
  GN_RI_end Bx MT LS fr_RINV ->
  0 = Z.of_nat (length (lm_O rn_mc)) /\ fr_RINV rn_cx (1 + 1) rn_mc /\
  LS rn_cx (1 + 1) rn_mc rs_ly rs_S.
Proof.
  intros MT LS ML HLS HE.
  destruct rn_common as (HRI & HOP & HNZ & HCAP & HENT & HPEND & HPR & HAR & HOK).
  destruct (RI_gone_end_new_sat MT ML) as (HGN & HRUN & HRUNC & HMLE & HCST & HPERM).
  exact (HE rn_cx 1 rn_m rs_ly rs_S [(rn_h, 0%nat)] [(rn_e, rn_h)] rn_c2 [] 0 0 rn_m1 rn_mc 0
    rs_ly rs_S 0 _ HRI HOP HNZ HGN HCAP HENT HPEND HLS HPR HAR HOK HRUN HRUNC HMLE HCST HPERM).
Qed.

Lemma GN_CNT_step_fires : forall (gn_pk : lfcx -> lmod -> list (hsrc * nat) -> (Z -> bool) -> nat)
    (gn_cnl_pk : hsrc -> (Z -> bool) -> nat) (P : Z -> bool),
  GN_CNT_step fr_RINV gn_pk gn_cnl_pk ->
  (ReplyCnt.acnt P (model_blks rn_m1) + gn_cnl_pk rn_h P
     <= ReplyCnt.acnt P (model_blks rn_m) + gn_pk rn_cx rn_m [(rn_h, 0%nat)] P)%nat /\
  (forall h' E' H', gn_cnl_ok rn_h h' E' H' ->
     (ReplyCnt.acnt P (model_blks (gn_set rn_m1 0 h')) + 0
        <= ReplyCnt.acnt P (model_blks rn_m) + gn_pk rn_cx rn_m [(rn_h, 0%nat)] P)%nat).
Proof.
  intros gn_pk gn_cnl_pk P HC.
  destruct rn_common as (HRI & HOP & HNZ & HCAP & HENT & HPEND & HPR & HAR & HOK).
  destruct (RI_gone_step_new_sat ameter_triv ameter_triv_laws)
    as (HRUN & _ & _ & _ & _ & HI & HK & HNTH & HFD & HREQ4).
  exact (HC rn_cx 1 rn_m [(rn_h, 0%nat)] [(rn_e, rn_h)] rn_c2 [] 0 0 rn_m1 rn_m1 0 0%nat 0%nat rn_h P
    HRI HOP HNZ HCAP HENT HPEND rn_blks_nonneg HPR HAR HOK rn_c2_entries HRUN HI HK HNTH HFD HREQ4).
Qed.

(* GN_CNT_rig (the count rule of the relay_instance_gone call itself; a Theorem Labs lane consumes it at CNTRIG, gone_p3_x
   :147 and gone_x :168; A discharges it at its top as CNT_gone_rig, A top_x.v:841).  Its premise list is empty, so
   what a witness must show is that its UNIVERSALS are met at a REACHED state: the cx, m and hs it is used at are
   the arm's own (fr_RINV cx t m and gn_pairs m hs hold there, as GRG carries them), which is what the two
   conjuncts below say. *)
Lemma GN_CNT_rig_fires : forall (gn_pk gn_rig_pk : lfcx -> lmod -> list (hsrc * nat) -> (Z -> bool) -> nat)
    (P : Z -> bool),
  GN_CNT_rig gn_pk gn_rig_pk ->
  fr_RINV rn_cx 1 rn_m /\ gn_pairs rn_m [(rn_h, 0%nat)] /\
  (gn_rig_pk rn_cx rn_m [(rn_h, 0%nat)] P <= gn_pk rn_cx rn_m [(rn_h, 0%nat)] P)%nat.
Proof.
  intros gn_pk gn_rig_pk P HC.
  destruct rn_common as (HRI & _ & _ & _ & _ & _ & HPR & _ & _).
  split; [exact HRI|]. split; [exact HPR|].
  exact (HC rn_cx rn_m [(rn_h, 0%nat)] P).
Qed.

(* ================================================================== GN_LS_rig (the re-taken text, A 3d17f490d56's
   TX_GN_LS_rig: gn_op, the per-slot pending-offset premise and the entry's CAPOUT clause are new, and it concludes
   two more facts).  Its three premises beyond rn_common's: *)
Lemma rn_U_le : Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es rn_m).
Proof. constructor; [cbn; unfold APARTIAL; lia | constructor]. Qed.
(* the per-slot form of REQ3: slot 0 holds the open source with nothing pending, the other three are closed *)
Lemma rn_pend_slots : forall j h, nth j (lm_hs rn_m) None = Some h ->
  (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
  (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r))).
Proof.
  intros [|[|[|[|j]]]] h Hj; cbn in Hj; try discriminate Hj; [|destruct j; discriminate Hj].
  injection Hj as <-. left. split; reflexivity.
Qed.
(* the CAPOUT clause of the entry's pre (_cut.v:301-302), at the entry's own world and memory: g_capout reads 0,
   which is what the first call sees (a .bss word) and what the bound allows *)
Lemma rn_capout : exists c, val_mem segs (arm (c_W rn_cx) (c_mem rn_cx)) (rg_capout fr_RG) 8 c /\
  0 <= c <= CAPOUT_MAX.
Proof.
  exists 0. split; [|unfold CAPOUT_MAX, OPS_MAX; lia].
  intros k Hk. unfold arm, mrestrict, mbyte, rn_cx, rs_W.
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; cbn; first [reflexivity | lia].
Qed.

Lemma GN_LS_rig_fires : forall (MT : ameter_ops) (MMAX : Z)
    (LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop),
  LS rn_cx 1 rn_m rs_ly rs_S ->
  GN_LS_rig MT LS fr_RINV MMAX ->
  tr_max (rig_tr (lm_c rn_m) (lm_mx rn_m) (Z.of_nat (length (lm_O rn_m))) (lm_cap rn_m)
            (gn_id rn_cx rn_m) (lm_es rn_m) [(rn_h, 0%nat)]) < MMAX /\
  blocks_bytes rs_S + tr_peak (rig_tr (lm_c rn_m) (lm_mx rn_m) (Z.of_nat (length (lm_O rn_m))) (lm_cap rn_m)
            (gn_id rn_cx rn_m) (lm_es rn_m) [(rn_h, 0%nat)]) <= LIVE_MAX /\
  mo_ok MT rs_S (tr_cost MT (rig_tr (lm_c rn_m) (lm_mx rn_m) (Z.of_nat (length (lm_O rn_m))) (lm_cap rn_m)
            (gn_id rn_cx rn_m) (lm_es rn_m) [(rn_h, 0%nat)])) /\
  lm_cap rn_m < MMAX /\
  blocks_bytes rs_S + tr_peak (rig_tr (lm_c rn_m) (lm_mx rn_m) (Z.of_nat (length (lm_O rn_m))) (lm_cap rn_m)
            (gn_id rn_cx rn_m) (lm_es rn_m) [(rn_h, 0%nat)]) +
    4 * Z.max (lm_cap rn_m) (tr_max (rig_tr (lm_c rn_m) (lm_mx rn_m) (Z.of_nat (length (lm_O rn_m))) (lm_cap rn_m)
            (gn_id rn_cx rn_m) (lm_es rn_m) [(rn_h, 0%nat)])) <= LIVE_MAX.
Proof.
  intros MT MMAX LS HLS HR.
  destruct rn_common as (HRI & HOP & _ & _ & _ & _ & HPR & _ & _).
  exact (HR rn_cx 1 rn_m rs_ly rs_S [(rn_h, 0%nat)] HLS HRI HPR HOP rn_U_le rn_blks_nonneg rn_pend_slots
    rn_capout).
Qed.
End nsat.

(* ================================================================== THE WITNESSES AT THE IMAGE-B INSTANCE
   B := TfibB (lib/B/YD2l.v, the image-B start-up instance), with the B driver's own call room 2 ^ 33
   (YCfn_cf.CALL_ROOM_B at a Theorem Labs lane's 6dd1d8ad0dfe).  Each is one application of the Section's lemma: the
   Section proves them for EVERY asyms, so the image's own symbol table is one case.  (These lemmas waited for
   lib/B/YCej.v, which cand13 commit 2, a working branch 63bca49e574 on the room branch, fixed.) *)
Section inst.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma gone_B_LS_sat : ReplyLSB.fr_LS YD2l.TfibB (2 ^ 33) (rn_cx YD2l.TfibB) 1 (rn_m YD2l.TfibB) rs_ly rs_S.
Proof. exact (rn_LS YD2l.TfibB (2 ^ 33) rn_LS_room). Qed.
Lemma gone_B_step_sat : forall (MT : ameter_ops) (MMAX : Z), ameter_laws MT ->
  GN_RI_step YD2l.TfibB MT (ReplyLSB.fr_LS YD2l.TfibB (2 ^ 33)) fr_RINV MMAX ->
  NoDup (texts (hs_held (rn_h YD2l.TfibB))) /\
  mo_ok MT rs_S (cnl_cost MT (hs_expected (rn_h YD2l.TfibB)) (hs_held (rn_h YD2l.TfibB))).
Proof.
  intros MT MMAX ML HST.
  destruct (GN_RI_step_fires YD2l.TfibB MT MMAX (ReplyLSB.fr_LS YD2l.TfibB (2 ^ 33)) ML gone_B_LS_sat HST)
    as (H1 & _ & _ & _ & _ & _ & _ & _ & H9 & _).
  exact (conj H1 H9).
Qed.
Lemma gone_B_end_sat : forall (MT : ameter_ops), ameter_laws MT ->
  GN_RI_end YD2l.TfibB MT (ReplyLSB.fr_LS YD2l.TfibB (2 ^ 33)) fr_RINV ->
  fr_RINV (rn_cx YD2l.TfibB) (1 + 1) (rn_mc YD2l.TfibB) /\
  ReplyLSB.fr_LS YD2l.TfibB (2 ^ 33) (rn_cx YD2l.TfibB) (1 + 1) (rn_mc YD2l.TfibB) rs_ly rs_S.
Proof.
  intros MT ML HE.
  destruct (GN_RI_end_fires YD2l.TfibB MT (ReplyLSB.fr_LS YD2l.TfibB (2 ^ 33)) ML gone_B_LS_sat HE)
    as (_ & H2 & H3).
  exact (conj H2 H3).
Qed.
Lemma gone_B_cnt_step_sat : forall (gn_pk : lfcx -> lmod -> list (hsrc * nat) -> (Z -> bool) -> nat)
    (gn_cnl_pk : hsrc -> (Z -> bool) -> nat) (P : Z -> bool),
  GN_CNT_step fr_RINV gn_pk gn_cnl_pk ->
  (ReplyCnt.acnt P (model_blks (rn_m1 YD2l.TfibB)) + gn_cnl_pk (rn_h YD2l.TfibB) P
     <= ReplyCnt.acnt P (model_blks (rn_m YD2l.TfibB))
        + gn_pk (rn_cx YD2l.TfibB) (rn_m YD2l.TfibB) [(rn_h YD2l.TfibB, 0%nat)] P)%nat.
Proof. intros gn_pk gn_cnl_pk P HC. exact (proj1 (GN_CNT_step_fires YD2l.TfibB gn_pk gn_cnl_pk P HC)). Qed.
Lemma gone_B_cnt_rig_sat : forall (gn_pk gn_rig_pk : lfcx -> lmod -> list (hsrc * nat) -> (Z -> bool) -> nat)
    (P : Z -> bool),
  GN_CNT_rig gn_pk gn_rig_pk ->
  fr_RINV (rn_cx YD2l.TfibB) 1 (rn_m YD2l.TfibB) /\
  gn_pairs (rn_m YD2l.TfibB) [(rn_h YD2l.TfibB, 0%nat)] /\
  (gn_rig_pk (rn_cx YD2l.TfibB) (rn_m YD2l.TfibB) [(rn_h YD2l.TfibB, 0%nat)] P
     <= gn_pk (rn_cx YD2l.TfibB) (rn_m YD2l.TfibB) [(rn_h YD2l.TfibB, 0%nat)] P)%nat.
Proof. intros gn_pk gn_rig_pk P HC. exact (GN_CNT_rig_fires YD2l.TfibB gn_pk gn_rig_pk P HC). Qed.
Lemma gone_B_ls_rig_sat : forall (MT : ameter_ops) (MMAX : Z),
  GN_LS_rig MT (ReplyLSB.fr_LS YD2l.TfibB (2 ^ 33)) fr_RINV MMAX ->
  lm_cap (rn_m YD2l.TfibB) < MMAX.
Proof.
  intros MT MMAX HR.
  destruct (GN_LS_rig_fires YD2l.TfibB MT MMAX (ReplyLSB.fr_LS YD2l.TfibB (2 ^ 33)) gone_B_LS_sat HR)
    as (_ & _ & _ & H4 & _).
  exact H4.
Qed.
End inst.

(* ================================================================== the axiom audit (toolchain/allowed-axioms.txt) *)
Print Assumptions rn_common.
Print Assumptions rn_LS.
Print Assumptions rn_tr_cost_nonneg.
Print Assumptions rn_rig_cost_nonneg.
Print Assumptions rn_cst.
Print Assumptions RI_gone_step_new_sat.
Print Assumptions RI_gone_end_new_sat.
Print Assumptions cn_cnl.
Print Assumptions cn_grows.
Print Assumptions rn_blks_nonneg.
Print Assumptions rn_c2_entries.
Print Assumptions GN_RI_step_fires.
Print Assumptions GN_RI_end_fires.
Print Assumptions GN_CNT_step_fires.
Print Assumptions GN_CNT_rig_fires.
Print Assumptions rn_U_le.
Print Assumptions rn_pend_slots.
Print Assumptions rn_capout.
Print Assumptions GN_LS_rig_fires.
Print Assumptions gone_B_LS_sat.
Print Assumptions gone_B_step_sat.
Print Assumptions gone_B_end_sat.
Print Assumptions gone_B_cnt_step_sat.
Print Assumptions gone_B_cnt_rig_sat.
Print Assumptions gone_B_ls_rig_sat.
