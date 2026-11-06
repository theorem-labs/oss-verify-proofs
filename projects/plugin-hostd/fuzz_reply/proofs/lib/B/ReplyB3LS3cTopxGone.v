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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyRINV_gone.v, with its module paths and module names changed; 1094 of its 1264 lines of code are new or changed and 2753 lines of the source are left out. *)
(* proves no function (kind: segment lemma): the gone arm's LS / meter conjuncts of GN_RI_step and GN_RI_end at the v3
   LS layer of image B (LS := fr_LS3 B CALL_ROOM_B / fr_LS3c B CALL_ROOM_B, RINV := fr_RINV, MT := ameter_triv,
   MMAX := fr_MMAX) *)
(* The image-B (fuzz_reply.asan-ubsan) port of lib/A/ReplyLS3cTopxGone.v (sha256
   bd8dd3f0fe7d; internal record) at 1318828167d3, row G-BLS3-port (the gone half):
   A's definitions, names and proofs over lib/B's records.  Every lemma keeps A's name and A's statement but for the
   swaps below.
   A -> B SWAPS (as lib/B/ReplyB3LS3.v, ReplyB3LS3Arms.v and ReplyB3LS3c.v made them):
   - the Require header is ReplyB3LS3Arms.v's (lib/A AB1v -> lib/B YB1v; Reusable YE01 + lib/A AE2k -> lib/B YE01 YE2k;
     lib/A ACfn -> lib/B YCfn, Required only; lib/A W_* -> lib/B W_*, then ReplyGuardB; lib/A ACfn_cf -> lib/B
     YCfn_cf); lib/A ReplyLS / ReplyLSArms -> lib/B ReplyLSB, ReplyLSBArms, ReplyB3Base; ReplyRINV -> ReplyRINVB;
     ReplyLSDrainPre -> ReplyLSBDrainPre; ReplyLS3 -> ReplyB3LS3; ReplyLSDrain3 / ReplyLSRemove3 / ReplyLSEvent3 /
     ReplyLS3Arms -> ReplyB3LS3Arms (the dr3_ / ls3_ facts this file reads, A's names and statements); ReplyLSCntL ->
     ReplyB3LSCntL; ReplyLS3c -> ReplyB3LS3c; lib/A W_LLVMFuzzerTestOneInput_drain -> lib/B
     W_LLVMFuzzerTestOneInput_drain_defs; _event -> _arm_event; ReplyLS3cTopxDefs -> ReplyB3LS3cTopxDefs (which
     re-exports lib/B/W_LLVMFuzzerTestOneInput_gone_base.v: every gn_* name below is B's gone_base's, A's text);
   - A's Section gnrs (A :76-123) COPIES GN_RI_step / GN_RI_end from a working branch a1a3591c77c, and
     no lemma of A's file names them.  This file does not copy them: the texts are B's gone_base GN_RI_step (:559-596)
     and GN_RI_end (:597-617) at a2ff0ba990a4, applied as `GN_RI_step B MT LS RINV MMAX` and `GN_RI_end B MT LS RINV`.
     B's texts have A's copied premises plus `gn_op cx t m` and the relay entries' NUL-free / key-length Forall after
     `RINV cx t m` (GN_RI_end also `lm_gn m = 0 \/ lm_gn m = 1`) and REQ1-REQ4, and B writes `AREC * capb ..` where
     A's copy writes capb's body (lib/B/W_contract.v :1961).  Each lemma below keeps A's premises, so it reads none of
     those extras;
   - fr_LS3 B -> fr_LS3 B CALL_ROOM_B and fr_LS3c B -> fr_LS3c B CALL_ROOM_B: Sections acct and meter3 take the
     Variable CALL_ROOM_B after B (ReplyLSB.fr_LS's room), and {SK : YI16.sink_head} in their Context (ReplyLSB.v
     :144).  The two lemmas whose proofs read the room's value (A's `ACfn_cf.CALL_ROOM = 8589934592`, A :1331),
     gx_step_room and gx_step_room_c, take the premise `YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B` (the B driver's room,
     2 ^ 33 as A's) before their A text, as ReplyB3LS3.v's fr_LS3_room does.  gx_end_LS3 / gx_end_LS3c and the
     meter lemmas read no room value and take no premise;
   - MMAX: A's Local Notation MMAX := WR_MMAX -> fr_MMAX (lib/A/CfParamsReply.v; ReplyLSBArms.v fr_MMAX_val =
     1072693248, A's value), the MMAX the B top states its LS rules at; A's `WR_MMAX = 1072693248` (A :1355) ->
     `MMAX = 1072693248` by fr_MMAX_val.  gx_WR_MMAX_pin keeps A's statement over lib/B/_write.v's WR_MMAX (the
     write arm's request bound, 2 ^ 30 - 2 ^ 20).
   REQ1-REQ5 (A's gone_base edits after d3a30b1562c6; B's gone_base has them from a2ff0ba990a4, REQ5 and C1 as
   gn_cnl_ok's last two conjuncts, which gx_touch_cost's destruct skips): A's file states S1 and E1 at the gnrs texts
   and carries what they read beyond those texts as the named hypotheses gx_xstep / gx_xend (below), so no lemma here
   reads a REQ text and none needs a `_q` premise.
   A's header follows. *)
(* The gone arm's LS / meter conjuncts of GN_RI_step and GN_RI_end at LS := fr_LS3 B / fr_LS3c B, RINV := fr_RINV,
   MT := ameter_triv, MMAX := WR_MMAX, against the OFFICIAL restated texts of
   a working branch a1a3591c77c lib/A/W_LLVMFuzzerTestOneInput_gone_base.v (copied below):
   (S1) GN_RI_step's cnl_room on blocks_bytes Sx, (S2) its mo_ok MT Sx (cnl_cost ..), (S3) its inner
   mo_ok MT Sy (hl_n .. * mo_free MT), (E1) GN_RI_end's LS cx (t + 1) mc lyx Sx.
   proves no function (kind: invariant lemma).

   S2 and S3 hold at the official text (mo_ok is True at ameter_triv).  S1 and E1 do NOT follow from the official
   premises alone: they read model facts of the operation's start state (lm_O m = [] and 0 <= lm_cap m, and the
   relay entries' and drained sources' representation clauses at relay_instance_gone's call) that neither fr_LS3
   nor fr_RINV nor the official premises give, and S1 reads the held lists' count clause at the loop's state.
   E1 also needs the held vectors not to shrink over the operation: check_no_loss's post bounds the new held
   capacity from above only (W_contract.v:2028), and the held list's potential measure can rise by 64 at a call
   whose capacity drops (cap 8, 4 texts -> cap 4: 128 -> 192), four calls per operation, against MB_K = 65 per
   input byte (one or two bytes).  Each is carried as ONE named extra hypothesis (gx_xstep for S1, gx_xend for
   E1); see their definitions for the clauses and where the gone arm holds each.

   The accounting (Section acct): the potential PHX = PHI3 + RES, where RES credits each expected list with what
   check_no_loss will spend on it (the held keys and vector growth of its begin lines) less its texts' blocks.
   relay_instance_gone (rig_rel, induction over the table) costs at most 0 per entry: an open entry's drain is
   paid by the 64 per pending byte it releases and W_U per byte of the old unfinished line (as
   ReplyLS3Arms.v fr_LS3_drain_step_p), each key it ends releases 5 |key| + 1 >= 2 (|key| + 5) (the key has the
   15-byte instance prefix); the table-order loop (gn_run) touches each slot at most once (the table's fds are
   distinct) and each check_no_loss + check_shape_ends costs at most 64 (0 when the held vector does not
   shrink). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_drain_defs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  drain_b_c gestures_end_b_c gesture_end_c relay_remove_b_c relay_instance_gone_b_c RelayCap SlotReads SlotInv
  SlotDrain3Aux SlotPass2Aux relay_remove_b_aux send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSB ReplyRINVB ReplyLSBArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyLSBDrainPre.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
ReplyB3Base ReplyB3LS3 ReplyB3LS3Arms ReplyB3LSCntL ReplyB3LS3c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyB3LS3cTopxDefs.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================== the official texts *)
(* A :76-123 copies GN_RI_step / GN_RI_end here (Section gnrs).  On B they are
   lib/B/W_LLVMFuzzerTestOneInput_gone_base.v's GN_RI_step (:559-596) and GN_RI_end (:597-617), cited, not copied
   (see the header); no lemma below names them. *)

Local Notation MT := ameter_triv.
Local Notation MMAX := fr_MMAX.
Local Notation zsum l := (fold_right Z.add 0 l).

(* GN_RI_step names MMAX; top_x applies it at CfParamsReply.fr_MMAX, which is WR_MMAX by computation (B: MMAX is
   fr_MMAX; WR_MMAX is lib/B/W_LLVMFuzzerTestOneInput_write.v's) *)
Example gx_WR_MMAX_pin : WR_MMAX = CfParamsReply.fr_MMAX.
Proof. reflexivity. Qed.

(* ================================================================== the named extra hypotheses *)
(* What S1 and E1 read of the operation that the official premises do not give.  Where the gone arm holds each
   (integ bb9dae5d905; lib/B/W_LLVMFuzzerTestOneInput_gone_base.v / W_contract.v / W_rep.v line numbers):
   - lm_O m = [] : gn_op cx t m (gone_base.v:355-356), carried by gdone (:666-669) in every p5st (gone_p5.v:1145);
   - 0 <= lm_cap m : aout_at's capacity clause (W_rep.v:189-190) at relay_instance_gone's call (rig_spec :1444);
   - for every open pair (e, (h, j)) of gn_pairs: aentry_ok e's clauses (W_rep.v:126-141, from rig_spec's
     arelay_at :1443) as dr3_epre e and ls3_kh e (ReplyLSDrain3.v:80, ReplyLS3Arms.v:306), and asrc_at h's
     pending clauses (W_rep.v:93, :106-107, from rig_spec's dr_src_ok :1446 / :1239) as dr3_hpre h
     (ReplyLSDrain3.v:87). *)
Definition gx_xpre (m : lmod) (hs : list (hsrc * nat)) : Prop :=
  lm_O m = [] /\ 0 <= lm_cap m /\
  Forall (fun p => re_eof (fst p) = 0 -> dr3_epre (fst p) /\ ls3_kh (fst p) /\ dr3_hpre (fst (snd p)))
    (combine (lm_es m) hs).
(* S1's hypothesis: gx_xpre and alist_at's count clause (W_rep.v:83) of every open slot's held list at the loop's
   state (gst's amodel_at, gone_base.v:630, held at every p5st; asrc_at :112) *)
Definition gx_xstep (m : lmod) (hs : list (hsrc * nat)) (mc : lmod) : Prop :=
  gx_xpre m hs /\
  forall k h, nth k (lm_hs mc) None = Some h -> hl_n (hs_held h) <= hl_cap (hs_held h).
(* E1's hypothesis: gx_xpre and that no held vector shrinks over the operation.  The program keeps it (drain
   keeps the held list, dr_rel :1232; check_no_loss only appends through gesture_model's list_push, whose
   capstep never lowers the capacity, ReplyLSDrain3.v dr3_capstep_ge; check_shape_ends keeps hl_cap, :1812), but
   no callee post states it: cnl_post :1973 bounds hl_cap H' from above only. *)
Definition gx_xend (m : lmod) (hs : list (hsrc * nat)) (mc : lmod) : Prop :=
  gx_xpre m hs /\
  forall k h h', nth k (lm_hs m) None = Some h -> nth k (lm_hs mc) None = Some h' ->
    hl_cap (hs_held h) <= hl_cap (hs_held h').

(* ================================================================== the potential, split by component *)
Definition gx_EP (e : rentry) : Z := bsum (aentry_blks e) + W_H * entry_held e + ent_cred e.
Definition gx_SP (o : option hsrc) : Z :=
  bsum (slot_blks o) + W_P * slot_pend o + W_H * slot_held o + slot_vsl o + slot_cred o.
(* the expected list's reserve: what check_no_loss spends on its texts (the held keys, 5 |key| + 1 each, and 32 of
   held vector per begin line), less the texts' blocks it frees *)
Definition gx_RES (o : option hsrc) : Z :=
  match o with
  | Some h => zsum (map ls3_wk (dr3_nk (texts (hs_expected h)))) +
              32 * Z.of_nat (count_begin (texts (hs_expected h))) - dr3_tsz (hl_recs (hs_expected h))
  | None => 0
  end.
Definition gx_SQ (o : option hsrc) : Z := gx_SP o + gx_RES o.
Definition gx_PHX (m : lmod) : Z := PHI3 m + zsum (map gx_RES (lm_hs m)).

Lemma gx_zsum_add : forall {X : Type} (f g : X -> Z) l,
  zsum (map (fun x => f x + g x) l) = zsum (map f l) + zsum (map g l).
Proof. intros X f g l. induction l as [|x l IH]; cbn [map fold_right]; lia. Qed.
Lemma gx_EP_sum : forall es, zsum (map gx_EP es) =
  bsum (concat (map aentry_blks es)) + W_H * zsum (map entry_held es) + zsum (map ent_cred es).
Proof.
  induction es as [|e es IH]; cbn [map concat fold_right]; [rewrite bsum_nil; lia|].
  rewrite bsum_app, IH. unfold gx_EP, W_H. lia.
Qed.
Lemma gx_SP_sum : forall hs, zsum (map gx_SP hs) =
  bsum (concat (map slot_blks hs)) + W_P * zsum (map slot_pend hs) + W_H * zsum (map slot_held hs) +
  zsum (map slot_vsl hs) + zsum (map slot_cred hs).
Proof.
  induction hs as [|o hs IH]; cbn [map concat fold_right]; [rewrite bsum_nil; lia|].
  rewrite bsum_app, IH. unfold gx_SP, W_P, W_H. lia.
Qed.
Lemma gx_PHI3_split : forall m,
  PHI3 m = ATABLE + zsum (map gx_EP (lm_es m)) + zsum (map gx_SP (lm_hs m)) + dr3_bo (lm_cap m).
Proof.
  intros m. unfold PHI3, PHI, ECRED, pend_bytes, held_bytes, vslack, model_blks.
  rewrite bsum_cons, !bsum_app, gx_EP_sum, gx_SP_sum, dr3_bsum_aout. cbn [snd]. unfold W_P, W_H. lia.
Qed.
Lemma gx_PHX_split : forall m,
  gx_PHX m = ATABLE + zsum (map gx_EP (lm_es m)) + zsum (map gx_SQ (lm_hs m)) + dr3_bo (lm_cap m).
Proof. intros m. unfold gx_PHX, gx_SQ. rewrite gx_PHI3_split, (gx_zsum_add gx_SP gx_RES). lia. Qed.

(* ================================================================== sums over the four slots *)
Lemma gx_sum4 : forall (g : option hsrc -> Z) l, length l = 4%nat ->
  zsum (map g l) = g (nth 0 l None) + g (nth 1 l None) + g (nth 2 l None) + g (nth 3 l None).
Proof.
  intros g [|a [|b [|c [|d [|x l]]]]] H; cbn [length] in H; try lia. cbn [map fold_right nth]. lia.
Qed.
Lemma gx_sum_RS : forall (F : nat -> Z) RS, List.NoDup RS -> (forall j, In j RS -> (j < 4)%nat) ->
  (forall j, (j < 4)%nat -> ~ In j RS -> F j = 0) ->
  F 0%nat + F 1%nat + F 2%nat + F 3%nat = zsum (map F RS).
Proof.
  intros F RS Hnd Hlt H0.
  set (p := fun j => existsb (Nat.eqb j) RS).
  assert (Hp : forall j, p j = true <-> In j RS).
  { intros j. unfold p. rewrite existsb_exists. split.
    - intros (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
    - intros Hj. exists j. split; [exact Hj | apply Nat.eqb_refl]. }
  assert (Hperm : Permutation (List.filter p [0; 1; 2; 3]%nat) RS).
  { apply NoDup_Permutation.
    - apply NoDup_filter. repeat constructor; cbn; intuition lia.
    - exact Hnd.
    - intros x. rewrite filter_In, Hp. split; [tauto|]. intros Hx. split; [|exact Hx].
      specialize (Hlt x Hx). cbn. lia. }
  rewrite <- (fr_sum_perm _ F _ _ Hperm).
  assert (E : forall l, (forall j, In j l -> (j < 4)%nat) -> zsum (map F l) = zsum (map F (List.filter p l))).
  { induction l as [|a l IH]; intros Hl; [reflexivity|]. cbn [List.filter map fold_right].
    assert (Hl' : forall j, In j l -> (j < 4)%nat) by (intros j Hj; apply Hl; right; exact Hj).
    destruct (p a) eqn:Ea; cbn [map fold_right].
    - rewrite (IH Hl'). reflexivity.
    - assert (Ha : ~ In a RS) by (intros Hin; apply Hp in Hin; congruence).
      rewrite (H0 a (Hl a (or_introl eq_refl)) Ha), (IH Hl'). lia. }
  rewrite <- E; [cbn [map fold_right]; lia|]. intros j Hj. cbn in Hj. lia.
Qed.
Lemma gx_rs_sum : forall (F : nat -> Z) (ps : list (rentry * (hsrc * nat))),
  zsum (map F (rig_slots ps)) = zsum (map (fun p => if re_eof (fst p) =? 0 then F (snd (snd p)) else 0) ps).
Proof.
  intros F ps. induction ps as [|p ps IH]; [reflexivity|].
  unfold rig_slots in *. cbn [map concat]. rewrite map_app, zsum_app, IH. cbn [map fold_right].
  destruct (re_eof (fst p) =? 0); cbn [map fold_right]; lia.
Qed.
Lemma gx_sum_ext : forall {X : Type} (P : X -> Prop) (g g' : X -> Z) l, Forall P l ->
  (forall x, P x -> g x = g' x) -> zsum (map g l) = zsum (map g' l).
Proof.
  intros X P g g' l HF Hg. induction HF as [|x l Hx _ IH]; [reflexivity|].
  cbn [map fold_right]. rewrite (Hg x Hx), IH. reflexivity.
Qed.
Lemma gx_sum_cfst : forall {X Y : Type} (g : X -> Z) (l1 : list X) (l2 : list Y), length l1 = length l2 ->
  zsum (map g l1) = zsum (map (fun pq => g (fst pq)) (combine l1 l2)).
Proof.
  intros X Y g l1. induction l1 as [|x l1 IH]; intros [|y l2] Hl;
    cbn [length combine map fold_right fst] in Hl |- *; try (exfalso; lia); [reflexivity|].
  rewrite (IH l2) by lia. reflexivity.
Qed.
Lemma gx_sum_csnd : forall {X Y : Type} (g : Y -> Z) (l1 : list X) (l2 : list Y), length l1 = length l2 ->
  zsum (map g l2) = zsum (map (fun pq => g (snd pq)) (combine l1 l2)).
Proof.
  intros X Y g l1. induction l1 as [|x l1 IH]; intros [|y l2] Hl;
    cbn [length combine map fold_right snd] in Hl |- *; try (exfalso; lia); [reflexivity|].
  rewrite (IH l2) by lia. reflexivity.
Qed.
Lemma gx_zsum_sub : forall {X : Type} (f g : X -> Z) l,
  zsum (map (fun x => f x - g x) l) = zsum (map f l) - zsum (map g l).
Proof. intros X f g l. induction l as [|x l IH]; cbn [map fold_right]; lia. Qed.
Lemma gx_Forall_nth : forall {X Y : Type} (P : X * Y -> Prop) (l1 : list X) (l2 : list Y) dx dy,
  length l1 = length l2 -> (forall i, (i < length l1)%nat -> P (nth i l1 dx, nth i l2 dy)) -> Forall P (combine l1 l2).
Proof.
  intros X Y P l1. induction l1 as [|x l1 IH]; intros [|y l2] dx dy Hl HP; cbn [length] in Hl; try (exfalso; lia).
  - cbn [combine]. constructor.
  - cbn [combine]. constructor.
    + apply (HP 0%nat). cbn [length]. lia.
    + apply (IH l2 dx dy); [lia|]. intros i Hi. apply (HP (S i)). cbn [length]. lia.
Qed.
Lemma gx_nth_some_lt : forall {X : Type} (l : list (option X)) k x, nth k l None = Some x -> (k < length l)%nat.
Proof.
  intros X l k x H. destruct (Nat.lt_ge_cases k (length l)) as [L|L]; [exact L|].
  rewrite nth_overflow in H by exact L. discriminate.
Qed.
Lemma gx_nodup_nth : forall {X Y : Type} (f : X -> Y) (l : list X) d i j, List.NoDup (map f l) ->
  (i < length l)%nat -> (j < length l)%nat -> f (nth i l d) = f (nth j l d) -> i = j.
Proof.
  intros X Y f l d i j Hnd Hi Hj E. apply (proj1 (NoDup_nth (map f l) (f d)) Hnd); rewrite ?length_map; auto.
  rewrite !map_nth. exact E.
Qed.

(* ================================================================== the drain's run, from any g_nout *)
(* ReplyLS3Arms.v's ls3_seen / ls3_lines_run / ls3_dinv / ls3_drain_run with 21 * KA a free bound X (so the run may
   start at g_nout = NO), and the buffer's capacity, the unfinished line's length and the expected list's capacity
   carried along *)
Lemma gx_seen : forall H ka l j ha ks X no,
  168 * Z.of_nat (length H) <= X + 8 * no -> 21 * ka <= X + 8 * no ->
  168 * Z.of_nat (length (RelayKeys.seen_arr H l)) <= X + 8 * (no + (Z.of_nat (length l) + 1)) /\
  21 * snd (fst (drain_b_c.seen_tr H ka l j ha ks)) <= X + 8 * (no + (Z.of_nat (length l) + 1)).
Proof.
  intros H ka l j ha ks X no HH Hk.
  unfold RelayKeys.seen_arr, drain_b_c.seen_tr.
  destruct (RelayModel.gesture l) as [[kd x]|] eqn:G; [|cbn [fst snd]; lia].
  destruct kd; destruct (RelayKeys.index_of x H) as [n|] eqn:I; cbn [fst snd].
  - lia.
  - pose proof (SlotReads.gesture_begin_len l x G). rewrite length_app. cbn [length]. lia.
  - unfold RelayKeys.swap_remove. rewrite length_firstn. lia.
  - lia.
Qed.
Lemma gx_lines_run : forall ls live mx no cap H ka j o ha ks X,
  168 * Z.of_nat (length H) <= X + 8 * no -> 21 * ka <= X + 8 * no ->
  168 * Z.of_nat (length (snd (fst (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks)))))) <=
    X + 8 * (no + Z.of_nat (length (with_nul ls))) /\
  21 * snd (snd (fst (drain_b_c.lines_run live mx no cap H ka ls j o ha ks))) <=
    X + 8 * (no + Z.of_nat (length (with_nul ls))).
Proof.
  induction ls as [|l r IH]; intros live mx no cap H ka j o ha ks X HH Hk; cbn [drain_b_c.lines_run].
  - cbn [fst snd]. rewrite RelayCap.with_nul_nil_len. lia.
  - rewrite RelayCap.with_nul_cons_len.
    match goal with |- context [drain_b_c.lines_run live mx ?a1 ?a2 (RelayKeys.seen_arr H l)
                                  (snd (fst (drain_b_c.seen_tr H ka l ?jj ?hh ?kk))) r ?a5 ?a6 ?a7 ?a8] =>
      pose proof (gx_seen H ka l jj hh kk X no HH Hk) as [S1 S2];
      destruct (IH live mx a1 a2 (RelayKeys.seen_arr H l) (snd (fst (drain_b_c.seen_tr H ka l jj hh kk)))
                  a5 a6 a7 a8 X ltac:(lia) ltac:(lia)) as [I1 I2] end.
    cbn [fst snd]. lia.
Qed.
Definition gx_dinv (X A : Z) (s : drain_b_c.dstate) : Prop :=
  0 <= drain_b_c.ds_off s /\ 0 <= dpre_rem s /\
  drain_b_c.ds_no s + Z.of_nat (length (drain_b_c.ds_u s)) + dpre_rem s <= A /\
  21 * drain_b_c.ds_ka s <= X + 8 * drain_b_c.ds_no s /\
  168 * Z.of_nat (length (drain_b_c.ds_H s)) <= X + 8 * drain_b_c.ds_no s /\
  (drain_b_c.ds_cap s = 0 \/ drain_b_c.ds_cap s = 8192 \/ drain_b_c.ds_cap s = 16384) /\
  Z.of_nat (length (drain_b_c.ds_u s)) <= 6000 /\ 0 <= drain_b_c.ds_ecap s.
Lemma gx_grow : forall cap used j b, (cap = 0 \/ cap = 8192 \/ cap = 16384) -> 0 <= used <= 6000 ->
  fst (snd (drain_b_c.grow_tr cap used j b)) = 0 \/ fst (snd (drain_b_c.grow_tr cap used j b)) = 8192 \/
  fst (snd (drain_b_c.grow_tr cap used j b)) = 16384.
Proof.
  intros cap used j b Hc Hu. unfold drain_b_c.grow_tr.
  destruct (Z.ltb_spec (cap - used) 4096); cbn [fst snd]; [|lia].
  destruct (Z.eqb_spec cap 0); lia.
Qed.
Lemma gx_pushes_cap : forall ls n cap j v rs, 0 <= cap -> 0 <= snd (fst (drain_b_c.pushes_run n cap ls j v rs)).
Proof.
  induction ls as [|l ls IH]; intros n cap j v rs Hc; cbn [drain_b_c.pushes_run]; cbv zeta; cbn [fst snd];
    [exact Hc|].
  apply IH. unfold drain_b_c.push_cap. destruct (n =? cap), (cap =? 0); lia.
Qed.
Lemma gx_drain_run : forall f live mx s j a X A, gx_dinv X A s ->
  gx_dinv X A (fst (snd (drain_b_c.drain_run f live mx s j a))).
Proof.
  induction f as [|f IH]; intros live mx s j a X A HI; [exact HI|].
  pose proof HI as (Io & Ir & Ia & Ik & Ih & Ic & Iu & Ie).
  pose proof (gx_grow (drain_b_c.ds_cap s) (Z.of_nat (length (drain_b_c.ds_u s))) j (drain_b_c.da_buf a) Ic
                ltac:(lia)) as Hg.
  cbn [drain_b_c.drain_run].
  destruct (drain_b_c.ds_eintr s).
  - cbn [fst snd]. apply IH. unfold gx_dinv, dpre_rem in HI |- *.
    cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_pend
         drain_b_c.ds_cap drain_b_c.ds_ecap]. lia.
  - destruct (drain_b_c.ds_pend s) as [|r0 rs] eqn:EP.
    + cbn [fst snd]. unfold gx_dinv, dpre_rem in HI |- *. rewrite EP in HI.
      cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_pend
           drain_b_c.ds_cap drain_b_c.ds_ecap]. lia.
    + assert (Hrem : dpre_rem s = Z.of_nat (length r0) + Z.of_nat (length (concat rs)) - drain_b_c.ds_off s).
      { unfold dpre_rem. rewrite EP. cbn [concat]. rewrite length_app. lia. }
      match goal with |- context [Z.leb ?x 0] => destruct (Z.leb_spec x 0) as [Hn0|Hn0] end.
      * cbn [fst snd]. unfold gx_dinv, dpre_rem.
        cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_pend
             drain_b_c.ds_cap drain_b_c.ds_ecap concat].
        rewrite length_app. lia.
      * match type of Hn0 with 0 < ?x =>
          assert (Hn1 : x <= Z.of_nat (length r0) - drain_b_c.ds_off s) by lia;
          set (n := x) in * end.
        assert (Hd : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat (drain_b_c.ds_off s)) r0))) = n)
          by (rewrite length_firstn, length_skipn; lia).
        set (d := firstn (Z.to_nat n) (skipn (Z.to_nat (drain_b_c.ds_off s)) r0)) in *.
        destruct (RelayModel.chunk (drain_b_c.ds_u s) (drain_b_c.ds_skip s) d) as [[u' sk'] rl] eqn:EC.
        destruct (dpre_chunk _ _ _ _ _ _ EC) as (C1 & C2 & C3).
        cbv beta iota.
        match goal with |- context [drain_b_c.pushes_run ?p1 ?p2 ?p3 ?p4 ?p5 ?p6] =>
          pose proof (gx_pushes_cap p3 p1 p2 p4 p5 p6 Ie) as Hpu end.
        match goal with |- context [drain_b_c.lines_run ?l1 ?l2 ?l3 ?l4 ?l5 ?l6 ?l7 ?l8 ?l9 ?l10 ?l11] =>
          pose proof (gx_lines_run l7 l1 l2 l3 l4 l5 l6 l8 l9 l10 l11 X ltac:(lia) ltac:(lia)) as [L1 L2];
          revert L1 L2;
          destruct (drain_b_c.lines_run l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11) as [[tl [[oc' H'] ka']] [[o' ha'] ks']];
          intros L1 L2 end.
        cbn [fst snd] in L1, L2 |- *.
        destruct (Z.eqb_spec (drain_b_c.ds_off s + n) (Z.of_nat (length r0))) as [Ew|Ew].
        -- apply IH. unfold gx_dinv, dpre_rem.
           cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_pend
                drain_b_c.ds_cap drain_b_c.ds_ecap].
           lia.
        -- apply IH. unfold gx_dinv, dpre_rem.
           cbn [drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_pend
                drain_b_c.ds_cap drain_b_c.ds_ecap concat].
           rewrite length_app. lia.
Qed.
(* a drain from g_nout = NO: the bytes it sends and the new unfinished line are at most the old line and the
   pending bytes; the key array grows by at most 8 per 21 bytes sent; the buffer ends at 0, 8192 or 16384; the
   expected list's capacity stays >= 0 *)
Lemma gx_drain_fin : forall live mx NO CAP (e : rentry) h,
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  168 * Z.of_nat (length (re_keys e)) <= 21 * drain_b_c.ent_ka e ->
  (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) -> Z.of_nat (length (re_U e)) <= 6000 ->
  0 <= hl_cap (hs_expected h) ->
  drain_b_c.ds_no (drain_b_c.drain_fin live mx NO CAP e h) - NO +
    Z.of_nat (length (drain_b_c.ds_u (drain_b_c.drain_fin live mx NO CAP e h))) <=
    Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h)) /\
  21 * drain_b_c.ds_ka (drain_b_c.drain_fin live mx NO CAP e h) <=
    21 * drain_b_c.ent_ka e + 8 * (drain_b_c.ds_no (drain_b_c.drain_fin live mx NO CAP e h) - NO) /\
  (drain_b_c.ds_cap (drain_b_c.drain_fin live mx NO CAP e h) = 0 \/
   drain_b_c.ds_cap (drain_b_c.drain_fin live mx NO CAP e h) = 8192 \/
   drain_b_c.ds_cap (drain_b_c.drain_fin live mx NO CAP e h) = 16384) /\
  0 <= drain_b_c.ds_ecap (drain_b_c.drain_fin live mx NO CAP e h).
Proof.
  intros live mx NO CAP e h Hoffc Hk Hc HU He.
  destruct (ls3_rem_init NO CAP e h Hoffc) as (Ho & Hr0).
  assert (HI : gx_dinv (21 * drain_b_c.ent_ka e - 8 * NO)
                 (NO + Z.of_nat (length (re_U e)) + Z.of_nat (length (pending_stream h)))
                 (drain_b_c.drain_fin live mx NO CAP e h)).
  { unfold drain_b_c.drain_fin, drain_b_c.drain_go. apply gx_drain_run.
    pose proof (dpre_rem_init NO CAP e h Ho) as Hr.
    unfold gx_dinv.
    cbn [drain_b_c.drain_init drain_b_c.ds_u drain_b_c.ds_off drain_b_c.ds_no drain_b_c.ds_H drain_b_c.ds_ka
         drain_b_c.ds_cap drain_b_c.ds_ecap] in Hr, Hr0 |- *.
    rewrite SlotReads.bzs_length. unfold drain_b_c.keys_texts. rewrite length_map. lia. }
  destruct HI as (_ & Ir & Ia & Ik & _ & Ic & _ & Ie).
  split; [lia|]. split; [lia|]. split; [exact Ic | exact Ie].
Qed.

(* ================================================================== gestures_end_instance's keys, the sends *)
Lemma gx_swap_perm : forall {A : Type} (d : A) n (l : list A), (n < length l)%nat ->
  Permutation l (nth n l d :: RelayKeys.swap_remove d n l).
Proof.
  intros A d n l Hn. destruct (nth_split l d Hn) as (l1 & l2 & E & L).
  remember (nth n l d) as x eqn:Ex. clear Ex. subst l n. apply RelayKeys.swap_remove_perm.
Qed.
Lemma gx_geik_loop : forall f pre n ks,
  Permutation ks (fst (geik_loop f pre n ks) ++ snd (geik_loop f pre n ks)) /\
  Forall (fun k => RelayKeys.has_prefix pre (bzs (gestures_end_b_c.key_text k)) = true) (fst (geik_loop f pre n ks)).
Proof.
  induction f as [|f IH]; intros pre n ks; cbn [geik_loop].
  - cbn [fst snd app]. split; [apply Permutation_refl | constructor].
  - destruct (Nat.ltb_spec n (length ks)) as [Hl|Hl]; [|cbn [fst snd app]; split; [apply Permutation_refl | constructor]].
    destruct (RelayKeys.has_prefix pre (bzs (gestures_end_b_c.key_text (nth n ks (0, [], []))))) eqn:Hp.
    + pose proof (IH pre n (RelayKeys.swap_remove (0, [], []) n ks)) as HI. revert HI.
      destruct (geik_loop f pre n (RelayKeys.swap_remove (0, [], []) n ks)) as [E K]. intros [P1 F1].
      cbn [fst snd app] in P1, F1 |- *. split.
      * eapply Permutation_trans; [exact (gx_swap_perm (0, [], []) n ks Hl)|]. apply perm_skip. exact P1.
      * constructor; [exact Hp | exact F1].
    + apply IH.
Qed.
Lemma gx_has_prefix_len : forall pre x, RelayKeys.has_prefix pre x = true -> (length pre <= length x)%nat.
Proof.
  intros pre x H. unfold RelayKeys.has_prefix in H. apply RelayKeys.list_eqb_true in H.
  pose proof (f_equal (@length Z) H) as L. rewrite length_firstn in L. lia.
Qed.
Lemma gx_pre_len : forall id, (15 <= length (relay_instance_gone_b_c.instance_prefix id))%nat.
Proof.
  intros id. unfold relay_instance_gone_b_c.instance_prefix. rewrite !length_app. cbn [length].
  assert (E : length K_GESTURE = 13%nat) by reflexivity. lia.
Qed.
Lemma gx_ended_len : forall pre ks, (15 <= length pre)%nat ->
  Forall (fun k => 15 <= Z.of_nat (length (gestures_end_b_c.key_text k))) (fst (geik pre ks)).
Proof.
  intros pre ks Hp. destruct (gx_geik_loop (length ks) pre 0 ks) as [_ F]. unfold geik.
  eapply Forall_impl; [|exact F]. intros k Hk. cbv beta in Hk.
  apply gx_has_prefix_len in Hk. rewrite SlotReads.bzs_length in Hk. lia.
Qed.
(* the entry after gestures_end_instance: its kept keys, the rest of it the entry's *)
Lemma gx_geik_EP : forall pre e1,
  gx_EP (entry_keys e1 (snd (geik pre (re_keys e1)))) + dr3_ksz (fst (geik pre (re_keys e1))) +
  W_H * zsum (map (fun k => Z.of_nat (length (gestures_end_b_c.key_text k))) (fst (geik pre (re_keys e1)))) =
  gx_EP e1.
Proof.
  intros pre e1. destruct (gx_geik_loop (length (re_keys e1)) pre 0 (re_keys e1)) as [P _].
  change (geik_loop (length (re_keys e1)) pre 0 (re_keys e1)) with (geik pre (re_keys e1)) in P.
  set (E := fst (geik pre (re_keys e1))) in *. set (K := snd (geik pre (re_keys e1))) in *.
  assert (S1 : dr3_ksz (re_keys e1) = dr3_ksz E + dr3_ksz K).
  { unfold dr3_ksz. rewrite (fr_sum_perm _ _ _ _ P), map_app, zsum_app. reflexivity. }
  assert (S2 : entry_held e1 =
               zsum (map (fun k => Z.of_nat (length (gestures_end_b_c.key_text k))) E) + entry_held (entry_keys e1 K)).
  { unfold entry_held. cbn [entry_keys re_keys]. rewrite (fr_sum_perm _ _ _ _ P), map_app, zsum_app. reflexivity. }
  unfold gx_EP. rewrite !dr3_bsum_aentry, S2. unfold ent_cred, dr3_ce, dr3_ke.
  cbn [entry_keys re_keys re_cap re_hp re_kh re_U]. rewrite S1. unfold W_H. lia.
Qed.
(* an ended key releases 5 |key| + 1 and its two sends cost 2 (|key| + 5) of g_out: >= 0 for |key| >= 3 *)
Lemma gx_ended_pay : forall E, Forall (fun k => 15 <= Z.of_nat (length (gestures_end_b_c.key_text k))) E ->
  2 * gestures_end_b_c.keys_total E <=
  dr3_ksz E + W_H * zsum (map (fun k => Z.of_nat (length (gestures_end_b_c.key_text k))) E).
Proof.
  induction E as [|k E IH]; intros HF; [cbn; lia|]. apply Forall_cons_iff in HF as [H1 H2]. specialize (IH H2).
  unfold gestures_end_b_c.keys_total, dr3_ksz in *. cbn [map fold_right] in *. unfold W_H in *. lia.
Qed.
Lemma gx_closed_cost : forall pre e, (15 <= length pre)%nat ->
  gx_EP (entry_keys e (snd (geik pre (re_keys e)))) + 2 * gestures_end_b_c.keys_total (fst (geik pre (re_keys e)))
  <= gx_EP e.
Proof.
  intros pre e Hp. pose proof (gx_geik_EP pre e). pose proof (gx_ended_pay _ (gx_ended_len pre (re_keys e) Hp)). lia.
Qed.
Lemma gx_ge_bytes_len : forall E,
  zsum (map (fun Bl : list byte => Z.of_nat (length Bl)) (ge_bytes E)) = gestures_end_b_c.keys_total E.
Proof.
  induction E as [|k E IH]; [reflexivity|].
  unfold ge_bytes in *. cbn [map concat app fold_right]. rewrite IH.
  assert (E5 : Z.of_nat (length gesture_end_c.END5) = 5) by reflexivity.
  unfold gestures_end_b_c.keys_total. cbn [fold_right]. lia.
Qed.
(* send_line per byte string: g_out grows by the bytes sent, g_capout stays under max C0 (2 * g_nout) *)
Lemma gx_sends : forall mx Bs c O cap c' O' cap' C0, sl_sends mx c O cap Bs = (c', O', cap') ->
  cap <= Z.max C0 (2 * Z.of_nat (length O)) ->
  Z.of_nat (length O') <= Z.of_nat (length O) + zsum (map (fun Bl : list byte => Z.of_nat (length Bl)) Bs) /\
  (length O <= length O')%nat /\ cap' <= Z.max C0 (2 * Z.of_nat (length O')).
Proof.
  intros mx Bs. induction Bs as [|Bl r IH]; intros c O cap c' O' cap' C0 HS Hc; cbn [sl_sends] in HS.
  - injection HS as <- <- <-. cbn [map fold_right]. lia.
  - assert (Hc1 : sl_cap c mx (Z.of_nat (length O)) cap (Z.of_nat (length Bl)) <=
                  Z.max C0 (2 * Z.of_nat (length (sl_O c O Bl))) /\
                  Z.of_nat (length (sl_O c O Bl)) <= Z.of_nat (length O) + Z.of_nat (length Bl) /\
                  (length O <= length (sl_O c O Bl))%nat).
    { unfold sl_cap, sl_O. destruct (sl_live c (Z.of_nat (length Bl))).
      - pose proof (RelayCap.send_line_cap_le true mx (Z.of_nat (length O)) cap (Z.of_nat (length Bl))) as L.
        rewrite length_app. lia.
      - rewrite RelayCap.send_line_cap_dead. lia. }
    destruct Hc1 as (Hc1 & Hl1 & Hl2).
    destruct (IH _ _ _ _ _ _ C0 HS Hc1) as (I1 & I2 & I3). cbn [map fold_right]. lia.
Qed.

(* ================================================================== the held list's measure *)
Definition gx_f (c n : Z) : Z := dr3_vec c + AREC * Z.max 0 (2 * n - c) + AREC * Z.max 0 (8 - c).
(* check_no_loss then check_shape_ends on a held list (cap c, n texts) with cb begin lines: at most 32 per begin
   and 64 when the new list's count is within its capacity (cnl_post bounds the new capacity from above only) *)
Lemma gx_held_a : forall c n cb c' n', 0 <= n -> 0 <= cb -> 0 <= n' <= c' -> n' <= n + cb ->
  c' <= Z.max 8 (Z.max c (2 * (n + cb))) -> gx_f c' n' <= gx_f c n + 32 * cb + 64.
Proof. intros. unfold gx_f, dr3_vec, AREC. destruct (Z.eqb_spec c' 0), (Z.eqb_spec c 0); lia. Qed.
(* ... and 32 per begin when the capacity does not drop *)
Lemma gx_held_b : forall c n cb c' n', 0 <= n -> 0 <= cb -> 0 <= n' -> n' <= n + cb -> c <= c' ->
  c' <= Z.max 8 (Z.max c (2 * (n + cb))) -> gx_f c' n' <= gx_f c n + 32 * cb.
Proof. intros. unfold gx_f, dr3_vec, AREC. destruct (Z.eqb_spec c' 0), (Z.eqb_spec c 0); lia. Qed.
(* the expected list, empty before the drain, holding the drain's nl lines after it *)
Lemma gx_exp_mid : forall c0 c1 nl, 0 <= c0 -> 0 <= c1 -> 0 <= nl -> c1 <= Z.max 8 (Z.max c0 (2 * nl)) ->
  gx_f c1 nl <= gx_f c0 0 + 32 * nl.
Proof. intros. unfold gx_f, dr3_vec, AREC. destruct (Z.eqb_spec c1 0), (Z.eqb_spec c0 0); lia. Qed.

(* ================================================================== one entry of relay_instance_gone *)
(* dr_rel's clauses the accounting reads (W_contract.v at bb9dae5d905 :1215-1234) *)
Lemma gx_dr_rel : forall c mx no cap e h e1 h1 LB, dr_rel c mx no cap e h e1 h1 LB ->
  re_fd e1 = re_fd e /\ re_cap e1 = drain_b_c.ds_cap (dr_fin c mx no cap e h) /\
  bzs (re_U e1) = drain_b_c.ds_u (dr_fin c mx no cap e h) /\
  drain_b_c.ent_ka e1 = drain_b_c.ds_ka (dr_fin c mx no cap e h) /\
  NoDup (drain_b_c.keys_texts (re_keys e1)) /\
  same_set (drain_b_c.keys_texts (re_keys e1)) (upds (drain_b_c.keys_texts (re_keys e)) (dr_lines h)) /\
  hl_cap (hs_expected h1) = drain_b_c.ds_ecap (dr_fin c mx no cap e h) /\
  hl_cap (hs_expected h1) <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h1))) /\
  hs_fd h1 = hs_fd h /\ hl_recs (hs_pending h1) = [] /\ hs_off h1 = 0 /\
  hl_cap (hs_pending h1) = hl_cap (hs_pending h) /\
  map snd (hl_recs (hs_expected h1)) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) /\
  hs_held h1 = hs_held h /\ bzs LB = with_nul (dr_lines h).
Proof.
  intros c mx no cap e h e1 h1 LB Hd. unfold dr_rel in Hd. cbv zeta in Hd.
  destruct Hd as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 &
                  D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & D26 & D27).
  exact (conj D1 (conj D4 (conj D5 (conj D8 (conj D9 (conj D10 (conj D11 (conj D12 (conj D13 (conj D16 (conj D17
    (conj D19 (conj D22 (conj D24 D27)))))))))))))).
Qed.
(* an open pair's facts: RINV's slot clauses (fr_pair_ok), gn_pair_ok's, fr_entry_ok's skip flag, gx_xpre's *)
Definition gx_pf (p : rentry * (hsrc * nat)) : Prop :=
  hl_recs (hs_expected (fst (snd p))) = [] /\ 0 <= hl_cap (hs_expected (fst (snd p))) /\ 0 <= hs_off (fst (snd p)) /\
  re_skip (fst p) = hs_overlong (fst (snd p)) /\
  (re_skip (fst p) = 0 -> bzs (re_U (fst p)) = bzs (hs_W (fst (snd p)))) /\
  (re_skip (fst p) = 0 \/ re_skip (fst p) = 1) /\
  dr3_epre (fst p) /\ ls3_kh (fst p) /\ dr3_hpre (fst (snd p)) /\
  Z.of_nat (length (pending_stream (fst (snd p)))) < 2 ^ 26.
(* the drained lines in the expected list after the drain *)
Lemma gx_exp_lines : forall c mx no cap e h e1 h1 LB, dr_rel c mx no cap e h e1 h1 LB ->
  hl_recs (hs_expected h) = [] ->
  texts (hs_expected h1) = dr_lines h /\ hl_n (hs_expected h1) = Z.of_nat (length (dr_lines h)) /\
  dr3_tsz (hl_recs (hs_expected h1)) = Z.of_nat (length (with_nul (dr_lines h))) /\
  (forall r, In r (hl_recs (hs_expected h1)) ->
     Z.of_nat (length (snd r)) + 1 <= Z.of_nat (length (with_nul (dr_lines h)))).
Proof.
  intros c mx no cap e h e1 h1 LB Hd Hexp.
  destruct (gx_dr_rel c mx no cap e h e1 h1 LB Hd) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Dmap & _).
  pose proof (dr3_lines h) as (_ & _ & HZr & _).
  split; [|split; [|split]].
  - unfold texts. rewrite <- (map_map snd bzs). rewrite Dmap, Hexp. cbn [map app]. exact (fr_bzs_lines _ HZr).
  - unfold hl_n. rewrite <- (length_map snd (hl_recs (hs_expected h1))), Dmap, Hexp. cbn [map app].
    rewrite length_map. reflexivity.
  - assert (X : map (fun r : Z * list byte => Z.of_nat (length (snd r)) + 1) (hl_recs (hs_expected h1)) =
                map (fun x => Z.of_nat (length x) + 1) (map snd (hl_recs (hs_expected h1))))
      by (rewrite map_map; reflexivity).
    unfold dr3_tsz. rewrite X, Dmap, Hexp. cbn [map app]. rewrite map_map, dr3_wn_sum. f_equal.
    apply map_ext. intros x. rewrite length_map. reflexivity.
  - intros r Hr. assert (Hs : In (snd r) (map (map (Z_to_bv 8)) (dr_lines h))).
    { replace (map (map (Z_to_bv 8)) (dr_lines h)) with (map snd (hl_recs (hs_expected h1)))
        by (rewrite Dmap, Hexp; reflexivity).
      apply in_map. exact Hr. }
    apply in_map_iff in Hs as (l & El & Hl). rewrite <- El, length_map. exact (dr3_wn_in _ l Hl).
Qed.
(* an open entry: the drain, then gestures_end_instance; the bytes it sends (the lines, then each ended key and
   " end\0") counted twice for g_out's growth.  It costs nothing: ReplyLS3Arms.v fr_LS3_drain_step_p's accounting,
   check_no_loss's share moved into the reserve gx_RES, and each ended key pays its two sends. *)
Lemma gx_open_cost : forall pre c mx (O : list byte) cap e h j e1 h1 LB,
  gx_pf (e, (h, j)) -> (15 <= length pre)%nat ->
  dr_rel c mx (Z.of_nat (length O)) cap e h e1 h1 LB ->
  gx_EP (entry_keys e1 (snd (geik pre (re_keys e1)))) + gx_SQ (Some h1) +
  2 * Z.of_nat (length (with_nul (dr_lines h))) + 2 * gestures_end_b_c.keys_total (fst (geik pre (re_keys e1)))
  <= gx_EP e + gx_SP (Some h).
Proof.
  intros pre c mx O cap e h j e1 h1 LB Hpf Hpre Hd.
  destruct Hpf as (Hexp & Hec0 & Hoff & Hsk & HskU & Hsk01 & Hepre & Hkh & Hhpre & HP26). cbn [fst snd] in *.
  destruct (gx_exp_lines c mx (Z.of_nat (length O)) cap e h e1 h1 LB Hd Hexp) as (HT & HnE & De1 & _).
  destruct (gx_dr_rel c mx (Z.of_nat (length O)) cap e h e1 h1 LB Hd)
    as (_ & Dcap & DU & Dka & Dnd & Dss & Decap & Decb & _ & Dpend & Doff & Dpc & _ & Dheld & _).
  pose proof (gx_geik_EP pre e1) as GE.
  pose proof (gx_ended_pay _ (gx_ended_len pre (re_keys e1) Hpre)) as GP.
  pose proof Hepre as (Hce & HU & HUz & Hkh8 & H14).
  pose proof Hhpre as (Hoffc & _).
  unfold dr_fin in Dcap, DU, Dka, Decap.
  set (NO := Z.of_nat (length O)) in *.
  assert (HJ : J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h)) by exact (dr3_J1 e h Hsk HskU Hsk01 HU HUz).
  assert (Hce0 : re_cap e = 0 \/ 8192 <= re_cap e) by lia.
  pose proof (relay_remove_b_aux.rma_fin_no (dr_live c h) mx NO cap e h HJ (dr3_pok NO cap e h Hoff Hhpre) Hce0)
    as Hno.
  assert (Hkh168 : 168 * Z.of_nat (length (re_keys e)) <= 21 * drain_b_c.ent_ka e).
  { unfold drain_b_c.ent_ka. destruct Hkh as [(E1 & E2) | (E1 & E2)].
    - rewrite E1, E2. cbn [length Z.of_nat Z.eqb]. lia.
    - rewrite (proj2 (Z.eqb_neq _ _) E1). unfold re_nheld in E2. lia. }
  assert (HU6 : Z.of_nat (length (re_U e)) <= 6000) by (unfold APARTIAL in HU; lia).
  destruct (gx_drain_fin (dr_live c h) mx NO cap e h Hoffc Hkh168 Hce HU6 Hec0) as (RM & RK & RC & RE).
  set (fin := drain_b_c.drain_fin (dr_live c h) mx NO cap e h) in *.
  change (lines (hs_state h) (bzs (pending_stream h))) with (dr_lines h) in Hno.
  set (Ls := dr_lines h) in *.
  set (TOT := Z.of_nat (length (with_nul Ls))) in *.
  set (P := Z.of_nat (length (pending_stream h))) in *.
  set (U := Z.of_nat (length (re_U e))) in *.
  set (U' := Z.of_nat (length (re_U e1))).
  set (NL := Z.of_nat (length Ls)) in *.
  set (CB := Z.of_nat (count_begin Ls)).
  set (SNK := zsum (map ls3_wk (dr3_nk Ls))).
  assert (ESNK : SNK = zsum (map ls3_wk (dr3_nk Ls))) by reflexivity.
  assert (ECB : CB = Z.of_nat (count_begin Ls)) by reflexivity.
  pose proof (dr3_lines h) as (HLn & _ & HZr & HCB). fold Ls in HLn, HZr, HCB.
  assert (HNL : NL <= P) by (unfold NL, P; lia).
  assert (HCB' : 21 * CB <= TOT) by (unfold CB, TOT; lia).
  assert (HSNK : SNK <= 5 * TOT) by exact (ls3_nk_wk Ls).
  assert (HTOT0 : 0 <= TOT) by (unfold TOT; lia).
  assert (HP0 : 0 <= P) by (unfold P; lia).
  assert (HU' : U' = Z.of_nat (length (drain_b_c.ds_u fin)))
    by (unfold U'; rewrite <- DU, SlotReads.bzs_length; reflexivity).
  assert (HMASS : TOT + U' <= U + P) by lia.
  assert (HKA : 21 * (drain_b_c.ent_ka e1 - drain_b_c.ent_ka e) <= 8 * TOT) by (rewrite Dka; lia).
  (* the entry: drained, then its keys with the prefix ended *)
  assert (CE : gx_EP e1 <= gx_EP e + (drain_b_c.ent_ka e1 - drain_b_c.ent_ka e) + SNK + W_U * (U' - U)).
  { unfold gx_EP. rewrite !dr3_bsum_aentry.
    assert (G1 : E_ENT <= dr3_ce e + Z.max 0 (E_ENT - re_cap e)) by (unfold dr3_ce; apply ent_buf_ge).
    assert (G2 : dr3_ce e1 + Z.max 0 (E_ENT - re_cap e1) <= E_ENT)
      by (unfold dr3_ce; apply ent_buf_le; rewrite Dcap; unfold E_ENT; lia).
    assert (EK : dr3_ke e = drain_b_c.ent_ka e) by reflexivity.
    assert (EK' : dr3_ke e1 = drain_b_c.ent_ka e1) by reflexivity.
    pose proof (ls3_keys_wk (re_keys e)) as W1. pose proof (ls3_keys_wk (re_keys e1)) as W2.
    assert (KI : zsum (map ls3_wk (drain_b_c.keys_texts (re_keys e1))) <=
                 zsum (map ls3_wk (drain_b_c.keys_texts (re_keys e))) + SNK).
    { pose proof Dnd as Hnd2. apply NoDup_ListNoDup in Hnd2.
      pose proof (ls3_sum_incl (drain_b_c.keys_texts (re_keys e1))
                    (drain_b_c.keys_texts (re_keys e) ++ dr3_nk Ls) Hnd2) as X.
      rewrite map_app, zsum_app in X. rewrite ESNK. apply X. intros y Hy. apply in_or_app.
      destruct (dr3_upds_in Ls _ y (proj1 (Dss y) Hy)) as [Hy'|Hy']; [left | right]; exact Hy'. }
    unfold entry_held, ent_cred. fold U U'. unfold W_H, W_U in *. lia. }
  (* the source: pending released, expected holding the lines (and their reserve), held kept *)
  assert (CS : gx_SQ (Some h1) <= gx_SP (Some h) - W_P * P + 32 * NL + SNK + 32 * CB).
  { unfold gx_SQ, gx_SP, gx_RES. cbn [slot_blks slot_pend slot_held slot_vsl slot_cred].
    rewrite !dr3_bsum_asrc, !dr3_bsum_alist. rewrite HT, De1. rewrite <- ESNK, <- ECB.
    unfold vsl, lst_cred.
    pose proof (ls3_ps_sp h Hoffc) as EP. cbn [slot_pend] in EP. fold P in EP.
    assert (Ep1 : hl_bytes (hs_pending h1) = 0) by (unfold hl_bytes; rewrite Dpend; reflexivity).
    assert (Ep2 : hl_n (hs_pending h1) = 0) by (unfold hl_n; rewrite Dpend; reflexivity).
    assert (Ep3 : dr3_tsz (hl_recs (hs_pending h1)) = 0) by (rewrite Dpend; reflexivity).
    rewrite Ep1, Ep2, Ep3, Dpc, Doff, Dheld.
    pose proof (dr3_tsz_nonneg (hl_recs (hs_pending h))) as Tp.
    assert (Hnp0 : 0 <= hl_n (hs_pending h)) by (unfold hl_n; lia).
    assert (Ee3 : hl_n (hs_expected h) = 0) by (unfold hl_n; rewrite Hexp; reflexivity).
    assert (Ee4 : dr3_tsz (hl_recs (hs_expected h)) = 0) by (rewrite Hexp; reflexivity).
    rewrite Ee3, Ee4, HnE.
    assert (Hc1 : 0 <= hl_cap (hs_expected h1)) by (rewrite Decap; exact RE).
    rewrite HnE in Decb.
    pose proof (gx_exp_mid (hl_cap (hs_expected h)) (hl_cap (hs_expected h1)) NL Hec0 Hc1
                  ltac:(unfold NL; lia) Decb) as XE.
    unfold gx_f in XE. unfold W_P, W_H, AREC in *. lia. }
  clear - GE GP CE CS HMASS HKA HSNK HCB' HNL HTOT0 HP0.
  unfold W_P, W_U, W_H in *. lia.
Qed.
(* g_capout after the drain, against g_out's length after it *)
Lemma gx_drain_cap : forall c mx (O : list byte) cap e h j e1 h1 LB C0, gx_pf (e, (h, j)) ->
  dr_rel c mx (Z.of_nat (length O)) cap e h e1 h1 LB -> cap <= Z.max C0 (2 * Z.of_nat (length O)) ->
  drain_b_c.ds_ocap (dr_fin c mx (Z.of_nat (length O)) cap e h) <= Z.max C0 (2 * Z.of_nat (length (O ++ LB))) /\
  Z.of_nat (length LB) = Z.of_nat (length (with_nul (dr_lines h))).
Proof.
  intros c mx O cap e h j e1 h1 LB C0 Hpf Hd Hc.
  destruct Hpf as (_ & _ & Hoff & Hsk & HskU & Hsk01 & Hepre & _ & Hhpre & _). cbn [fst snd] in *.
  destruct Hepre as (Hce & HU & HUz & _ & _).
  destruct (gx_dr_rel c mx (Z.of_nat (length O)) cap e h e1 h1 LB Hd)
    as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DLB).
  assert (HLB : Z.of_nat (length LB) = Z.of_nat (length (with_nul (dr_lines h))))
    by (rewrite <- DLB, SlotReads.bzs_length; reflexivity).
  split; [|exact HLB].
  assert (HJ : J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h)) by exact (dr3_J1 e h Hsk HskU Hsk01 HU HUz).
  assert (Hce0 : re_cap e = 0 \/ 8192 <= re_cap e) by lia.
  pose proof (relay_remove_b_aux.rma_fin_no (dr_live c h) mx (Z.of_nat (length O)) cap e h HJ
                (dr3_pok (Z.of_nat (length O)) cap e h Hoff Hhpre) Hce0) as Hno.
  pose proof (RelayCap.drain_ocap_le (dr_live c h) mx (Z.of_nat (length O)) cap e h) as (_ & Ho).
  unfold dr_fin. change (lines (hs_state h) (bzs (pending_stream h))) with (dr_lines h) in Hno.
  rewrite length_app. lia.
Qed.

(* ================================================================== relay_instance_gone's table run *)
Lemma gx_rig : forall pre mx ps qs c O cap c2 O2 cap2 C0,
  rig_rel pre mx c O cap ps qs c2 O2 cap2 -> (15 <= length pre)%nat ->
  Forall (fun p => re_eof (fst p) = 0 -> gx_pf p) ps ->
  cap <= Z.max C0 (2 * Z.of_nat (length O)) ->
  zsum (map (fun pq => gx_EP (fst (snd pq))) (combine ps qs)) +
  zsum (map (fun pq => if re_eof (fst (fst pq)) =? 0 then gx_SQ (Some (snd (snd pq))) else 0) (combine ps qs)) +
  2 * (Z.of_nat (length O2) - Z.of_nat (length O)) <=
  zsum (map (fun pq => gx_EP (fst (fst pq))) (combine ps qs)) +
  zsum (map (fun pq => if re_eof (fst (fst pq)) =? 0 then gx_SP (Some (fst (snd (fst pq)))) else 0)
          (combine ps qs)) /\
  cap2 <= Z.max C0 (2 * Z.of_nat (length O2)).
Proof.
  intros pre mx ps. induction ps as [|[e [h j]] r IH]; intros qs c O cap c2 O2 cap2 C0 HR Hpre HF Hc.
  - destruct qs as [|q qs]; cbn [rig_rel] in HR; [|contradiction].
    destruct HR as (-> & -> & ->). cbn [combine map fold_right]. lia.
  - destruct qs as [|[e' h1] q]; cbn [rig_rel] in HR; [contradiction|].
    destruct HR as (e1 & ev & LB & HR). cbv zeta in HR. destruct HR as (Hd & He' & Hrest).
    apply Forall_cons_iff in HF as [Hp HF]. cbn [fst snd] in Hp.
    match type of Hrest with context [sl_sends ?a ?b ?d ?f ?g] =>
      destruct (sl_sends a b d f g) as [[c3 O3] cap3] eqn:ES end.
    cbn [combine map fold_right fst snd].
    subst e'.
    revert Hd ES. destruct (re_eof e =? 0) eqn:Eo; cbn [andb]; intros Hd ES.
    + apply Z.eqb_eq in Eo. specialize (Hp Eo).
      pose proof (gx_open_cost pre c mx O cap e h j e1 h1 LB Hp Hpre Hd) as Hcost.
      destruct (gx_drain_cap c mx O cap e h j e1 h1 LB C0 Hp Hd Hc) as (Hoc & HLB).
      destruct (dr_live c h) eqn:Lv.
      * destruct (gx_sends mx _ _ _ _ _ _ _ C0 ES Hoc) as (S1 & S2 & S3).
        rewrite gx_ge_bytes_len, length_app in S1.
        destruct (IH q c3 O3 cap3 c2 O2 cap2 C0 Hrest Hpre HF S3) as (I1 & I2).
        split; [|exact I2]. lia.
      * destruct (gx_sends mx _ _ _ _ _ _ _ C0 ES Hc) as (S1 & S2 & S3).
        rewrite gx_ge_bytes_len in S1.
        destruct (IH q c3 O3 cap3 c2 O2 cap2 C0 Hrest Hpre HF S3) as (I1 & I2).
        assert (HT0 : 0 <= Z.of_nat (length (with_nul (dr_lines h)))) by lia.
        split; [|exact I2]. lia.
    + destruct Hd as [-> ->].
      pose proof (gx_closed_cost pre e Hpre) as Hcost.
      destruct (gx_sends mx _ _ _ _ _ _ _ C0 ES Hc) as (S1 & S2 & S3).
      rewrite gx_ge_bytes_len in S1.
      destruct (IH q c3 O3 cap3 c2 O2 cap2 C0 Hrest Hpre HF S3) as (I1 & I2).
      split; [|exact I2]. lia.
Qed.
(* the run's pairs: the entry keeps its fd, an open pair is a drain *)
Lemma gx_rig_pairs : forall pre mx ps qs c O cap c2 O2 cap2, rig_rel pre mx c O cap ps qs c2 O2 cap2 ->
  Forall (fun pq => re_fd (fst (snd pq)) = re_fd (fst (fst pq)) /\
    (re_eof (fst (fst pq)) = 0 -> exists c' mx' no cap' e1 LB,
       dr_rel c' mx' no cap' (fst (fst pq)) (fst (snd (fst pq))) e1 (snd (snd pq)) LB)) (combine ps qs).
Proof.
  intros pre mx ps. induction ps as [|[e [h j]] r IH]; intros qs c O cap c2 O2 cap2 HR.
  - cbn [combine]. constructor.
  - destruct qs as [|[e' h1] q]; cbn [rig_rel] in HR; [contradiction|].
    destruct HR as (e1 & ev & LB & HR). cbv zeta in HR. destruct HR as (Hd & He' & Hrest).
    match type of Hrest with context [sl_sends ?a ?b ?d ?f ?g] =>
      destruct (sl_sends a b d f g) as [[c3 O3] cap3] end.
    cbn [combine]. constructor; [|exact (IH q c3 O3 cap3 c2 O2 cap2 Hrest)].
    cbn [fst snd]. subst e'. cbn [entry_keys re_fd].
    revert Hd. destruct (re_eof e =? 0) eqn:Eo; intros Hd.
    + split.
      * destruct (gx_dr_rel _ _ _ _ _ _ _ _ _ Hd) as (D1 & _). exact D1.
      * intros _. exists c, mx, (Z.of_nat (length O)), cap, e1, LB. exact Hd.
    + destruct Hd as [-> ->]. split; [reflexivity|]. intros Heof. apply Z.eqb_neq in Eo. contradiction.
Qed.

Section acct.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* ================================================================== what fr_RINV gives of an open slot *)
Lemma gx_rinv_slot : forall cx t m k h, fr_RINV cx t m -> (k < 4)%nat -> nth k (lm_hs m) None = Some h ->
  hl_recs (hs_expected h) = [] /\ 0 <= hl_cap (hs_expected h) /\ 0 <= hs_off h /\ hl_cap (hs_held h) < 2 ^ 24 /\
  NoDup (texts (hs_held h)) /\
  exists e2, same_set (drain_b_c.keys_texts (re_keys e2)) (texts (hs_held h)) /\
             gestures_end_b_c.keys_total (re_keys e2) < 2 ^ 26.
Proof.
  intros cx t m k h HRI Hk Hh. destruct HRI as (_ & HR & Hn & _).
  destruct HR as (_ & Hnd & _ & Hent & hj & HF & _ & Hcl & _ & Hcn).
  destruct (fr_pair_of_open m t hj k h HF Hcl Hk Hh) as (e2 & p & Hin & Hok & Hp2 & Hp1).
  destruct p as [h0 s0]. cbn [fst snd] in Hp1, Hp2. subst h0 s0.
  unfold fr_pair_ok in Hok. cbv zeta in Hok. cbn [fst snd] in Hok.
  destruct Hok as (_ & _ & _ & _ & Hss & Hnd2 & Hexp & Hec & Hhc & _ & Hoff).
  pose proof (SlotInv.ecap_ok_lt _ Hec) as Hec0.
  assert (Hc : fr_pair_cost e2 (h, k) <= fr_cost (lm_es m) hj).
  { unfold fr_cost. apply (dr3_sum_in (fun q => fr_pair_cost (fst q) (snd q)) _ (e2, (h, k))).
    - intros q. apply fr_pair_cost_nonneg.
    - exact Hin. }
  assert (Hkt : gestures_end_b_c.keys_total (re_keys e2) <= fr_pair_cost e2 (h, k)).
  { unfold fr_pair_cost. cbn [fst]. destruct (re_skip e2 =? 0); lia. }
  refine (conj Hexp (conj (proj1 Hec0) (conj Hoff (conj Hhc (conj Hnd2 (ex_intro _ e2 (conj Hss _))))))). lia.
Qed.
Lemma gx_RES_empty : forall h, hl_recs (hs_expected h) = [] -> gx_RES (Some h) = 0.
Proof. intros h H. unfold gx_RES, texts. rewrite H. reflexivity. Qed.
(* every open pair of gn_pairs, with what fr_RINV and gx_xpre say of it *)
Lemma gx_pf_all : forall cx t m hs, fr_RINV cx t m -> gn_pairs m hs -> gx_xpre m hs ->
  Forall (fun p => re_eof (fst p) = 0 -> gx_pf p) (combine (lm_es m) hs).
Proof.
  intros cx t m hs HRI (Hlh & HP & _) (_ & _ & HX).
  pose proof HRI as (_ & (_ & _ & _ & Hent & _) & _).
  rewrite Forall_forall in HP, HX |- *. intros [e [h j]] Hin Heof. cbn [fst snd] in *.
  destruct (HP _ Hin Heof) as (Hj & Hh & Hfd & Hsk & HskU & HP26 & _ & _). cbn [fst snd] in *.
  destruct (HX _ Hin Heof) as (He & Hk & Hhp).
  destruct (gx_rinv_slot cx t m j h HRI Hj Hh) as (Hexp & Hec & Hoff & _).
  assert (Hs01 : re_skip e = 0 \/ re_skip e = 1).
  { rewrite Forall_forall in Hent. destruct (Hent e (in_combine_l _ _ _ _ Hin)) as (_ & _ & _ & _ & S). exact S. }
  unfold gx_pf. cbn [fst snd].
  exact (conj Hexp (conj Hec (conj Hoff (conj Hsk (conj HskU (conj Hs01 (conj He (conj Hk (conj Hhp HP26))))))))).
Qed.
Lemma gx_rs_in : forall j ps, In j (rig_slots ps) -> exists p, In p ps /\ re_eof (fst p) = 0 /\ snd (snd p) = j.
Proof.
  intros j ps H. unfold rig_slots in H. apply in_concat in H as (l & Hl & Hj).
  apply in_map_iff in Hl as (p & <- & Hp).
  revert Hj. destruct (re_eof (fst p) =? 0) eqn:E; intros Hj; [|destruct Hj].
  apply Z.eqb_eq in E. destruct Hj as [<-|[]]. exists p. auto.
Qed.
(* the drained slots before and after relay_instance_gone, pair by pair *)
Lemma gx_pq_facts : forall cx m hs qs c2 O2 cap2 out2 m1,
  gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 -> gn_rig_ok cx m hs qs c2 O2 cap2 ->
  Forall (fun pq => re_eof (fst (fst pq)) = 0 ->
            (snd (snd (fst pq)) < 4)%nat /\
            nth (snd (snd (fst pq))) (lm_hs m) None = Some (fst (snd (fst pq))) /\
            nth (snd (snd (fst pq))) (lm_hs m1) None = Some (snd (snd pq)))
    (combine (combine (lm_es m) hs) qs).
Proof.
  intros cx m hs qs c2 O2 cap2 out2 m1 (Hlh & HP & _) Hafter (_ & Hlq & _).
  pose proof Hafter as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A13).
  apply (gx_Forall_nth _ _ _ (gn_e0, gn_hj0) gn_q0).
  - rewrite length_combine. lia.
  - intros i Hi. rewrite length_combine in Hi. cbv beta. rewrite combine_nth by lia. cbn [fst snd]. intros Heof.
    rewrite Forall_forall in HP.
    assert (Hin : In (nth i (lm_es m) gn_e0, nth i hs gn_hj0) (combine (lm_es m) hs)).
    { rewrite <- combine_nth by lia. apply nth_In. rewrite length_combine. lia. }
    destruct (HP _ Hin Heof) as (Hj & Hh & _). cbn [fst snd] in Hj, Hh.
    split; [exact Hj|]. split; [exact Hh|]. apply A13; [lia | exact Heof].
Qed.

(* ================================================================== the potential after relay_instance_gone *)
Lemma gx_rig_phase : forall cx t m hs qs c2 O2 cap2 out2 m1,
  fr_RINV cx t m -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 -> gx_xpre m hs -> gx_PHX m1 <= PHI3 m.
Proof.
  intros cx t m hs qs c2 O2 cap2 out2 m1 HRI Hpairs Hafter Hrok HX.
  pose proof (gx_pf_all cx t m hs HRI Hpairs HX) as HPF.
  pose proof (gx_pq_facts cx m hs qs c2 O2 cap2 out2 m1 Hpairs Hafter Hrok) as HPQ.
  pose proof HX as (HO & Hcap0 & _).
  pose proof Hpairs as (Hlh & HPok & HRS).
  pose proof Hafter as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
  pose proof Hrok as (Hrr & Hlq & _ & _).
  pose proof HRI as (_ & (Hl4 & _) & _).
  set (ps := combine (lm_es m) hs) in *.
  assert (Hlps : length ps = length qs) by (unfold ps; rewrite length_combine; lia).
  destruct (gx_rig _ (lm_mx m) ps qs (lm_c m) (lm_O m) (lm_cap m) c2 O2 cap2 (lm_cap m) Hrr (gx_pre_len _) HPF
              ltac:(lia)) as (R1 & R2).
  rewrite HO in R1. cbn [length Z.of_nat] in R1.
  rewrite gx_PHX_split, gx_PHI3_split, A3, A7.
  (* the entries *)
  assert (EA : zsum (map gx_EP (map fst qs)) = zsum (map (fun pq => gx_EP (fst (snd pq))) (combine ps qs))).
  { rewrite map_map, (gx_sum_csnd (fun q => gx_EP (fst q)) ps qs Hlps). reflexivity. }
  assert (EB : zsum (map gx_EP (lm_es m)) = zsum (map (fun pq => gx_EP (fst (fst pq))) (combine ps qs))).
  { rewrite (gx_sum_cfst gx_EP (lm_es m) hs ltac:(lia)). fold ps.
    rewrite (gx_sum_cfst (fun p => gx_EP (fst p)) ps qs Hlps). reflexivity. }
  (* the slots: only the drained ones change *)
  set (F := fun j => gx_SQ (nth j (lm_hs m1) None) - gx_SQ (nth j (lm_hs m) None)).
  assert (S1 : zsum (map gx_SQ (lm_hs m1)) - zsum (map gx_SP (lm_hs m)) = F 0%nat + F 1%nat + F 2%nat + F 3%nat).
  { rewrite (gx_sum4 gx_SQ (lm_hs m1) A11), (gx_sum4 gx_SP (lm_hs m) Hl4).
    assert (R0 : forall j, (j < 4)%nat -> gx_SQ (nth j (lm_hs m) None) = gx_SP (nth j (lm_hs m) None)).
    { intros j Hj. unfold gx_SQ. destruct (nth j (lm_hs m) None) as [h|] eqn:Eh; [|cbn [gx_RES]; lia].
      destruct (gx_rinv_slot cx t m j h HRI Hj Eh) as (Hexp & _). rewrite (gx_RES_empty h Hexp). lia. }
    unfold F. rewrite (R0 0%nat), (R0 1%nat), (R0 2%nat), (R0 3%nat) by lia. lia. }
  assert (S2 : F 0%nat + F 1%nat + F 2%nat + F 3%nat = zsum (map F (rig_slots ps))).
  { apply gx_sum_RS.
    - apply NoDup_ListNoDup. exact HRS.
    - intros j Hj. destruct (gx_rs_in j ps Hj) as (p & Hp & Heof & <-).
      rewrite Forall_forall in HPok. destruct (HPok p Hp Heof) as (Hj4 & _). exact Hj4.
    - intros j Hj Hn. unfold F. rewrite (A12 j Hj Hn). lia. }
  rewrite gx_rs_sum in S2.
  rewrite (gx_sum_cfst (fun p => if re_eof (fst p) =? 0 then F (snd (snd p)) else 0) ps qs Hlps) in S2.
  assert (S3 : zsum (map (fun pq => if re_eof (fst (fst pq)) =? 0 then F (snd (snd (fst pq))) else 0)
                     (combine ps qs)) =
     zsum (map (fun pq => if re_eof (fst (fst pq)) =? 0 then gx_SQ (Some (snd (snd pq))) else 0) (combine ps qs)) -
     zsum (map (fun pq => if re_eof (fst (fst pq)) =? 0 then gx_SP (Some (fst (snd (fst pq)))) else 0)
             (combine ps qs))).
  { rewrite <- gx_zsum_sub. apply (gx_sum_ext _ _ _ _ HPQ). intros [p q] Hpq. cbn [fst snd] in Hpq |- *.
    destruct (re_eof (fst p) =? 0) eqn:Eo; [|lia].
    apply Z.eqb_eq in Eo. destruct (Hpq Eo) as (Hj4 & Hm & Hm1).
    unfold F. rewrite Hm, Hm1.
    destruct (gx_rinv_slot cx t m _ _ HRI Hj4 Hm) as (Hexp & _).
    assert (Z0 : gx_SQ (Some (fst (snd p))) = gx_SP (Some (fst (snd p))))
      by (unfold gx_SQ; rewrite (gx_RES_empty _ Hexp); lia).
    lia. }
  assert (Hout : dr3_bo cap2 - dr3_bo (lm_cap m) <= 2 * Z.of_nat (length O2)).
  { unfold dr3_bo. destruct (Z.eqb_spec cap2 0), (Z.eqb_spec (lm_cap m) 0); lia. }
  clearbody F. lia.
Qed.

(* ================================================================== the table-order loop *)
Lemma gx_setn_len : forall k x (l : list (option hsrc)), length (gn_setn k x l) = length l.
Proof. induction k as [|k IH]; intros x [|y l]; cbn [gn_setn length]; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma gx_setn_same : forall k x (l : list (option hsrc)), (k < length l)%nat -> nth k (gn_setn k x l) None = x.
Proof.
  induction k as [|k IH]; intros x [|y l] Hk; cbn [gn_setn length nth] in *; try (exfalso; lia); [reflexivity|].
  apply IH. lia.
Qed.
Lemma gx_setn_other : forall k k' x (l : list (option hsrc)), k <> k' -> nth k' (gn_setn k x l) None = nth k' l None.
Proof.
  induction k as [|k IH]; intros [|k'] x [|y l] Hne; cbn [gn_setn nth]; try reflexivity; try (exfalso; lia).
  apply IH. lia.
Qed.
(* one check_no_loss then check_shape_ends on a slot *)
Definition gx_touch (h h'' : hsrc) : Prop :=
  exists h' E' H' P g A0 ob ds c, gn_cnl_ok h h' E' H' /\ gn_cshe_ok P g A0 ob h' h'' ds c.
Lemma gx_touch_fd : forall h h'', gx_touch h h'' -> hs_fd h'' = hs_fd h.
Proof.
  intros h h'' (h' & E' & H' & P & g & A0 & ob & ds & c & (E1 & _) & (H'' & E2 & _)). subst. reflexivity.
Qed.
(* the slots the loop has touched (each once: the table's fds are distinct) and, for every (entry, slot) it has
   passed, the slot with the entry's fd has an empty expected list *)
Definition gx_hist (es : list rentry) (m1 mc : lmod) (i k : nat) : Prop :=
  forall k', nth k' (lm_hs mc) None = nth k' (lm_hs m1) None \/
    exists h h'' i0, nth k' (lm_hs m1) None = Some h /\ nth k' (lm_hs mc) None = Some h'' /\ gx_touch h h'' /\
      (i0 < length es)%nat /\ hs_fd h'' = re_fd (nth i0 es gn_e0) /\ ((i0 < i)%nat \/ (i0 = i /\ (k' < k)%nat)).
Definition gx_cov (es : list rentry) (mc : lmod) (i k : nat) : Prop :=
  forall i' k' h, ((i' < i)%nat \/ (i' = i /\ (k' < k)%nat)) -> (i' < length es)%nat -> (k' < 4)%nat ->
    nth k' (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i' es gn_e0) -> hl_recs (hs_expected h) = [].
Lemma gx_run : forall P m1 mc A i k, gn_run P m1 mc A i k -> List.NoDup (map re_fd (lm_es m1)) ->
  lm_es mc = lm_es m1 /\ lm_cap mc = lm_cap m1 /\ lm_k mc = lm_k m1 /\ lm_G mc = lm_G m1 /\
  lm_out mc = lm_out m1 /\ length (lm_hs mc) = length (lm_hs m1) /\
  gx_hist (lm_es m1) m1 mc i k /\ gx_cov (lm_es m1) mc i k.
Proof.
  intros P m1 mc A i k HR Hnd.
  induction HR as [| mc A i k HR IH Hk Hc | mc A i k h h' h'' E' H' ds c HR IH Hk Hi Hh Hfd Hcnl Hcshe
                   | mc A i HR IH].
  - refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj _ _))))))).
    + intros k'. left. reflexivity.
    + intros i' k' h0 Hlt. exfalso. lia.
  - destruct IH as (E1 & E2 & E3 & E4 & E5 & E6 & Hhist & Hcov).
    refine (conj E1 (conj E2 (conj E3 (conj E4 (conj E5 (conj E6 (conj _ _))))))).
    + intros k'. destruct (Hhist k') as [L | (h0 & h1 & i0 & X1 & X2 & X3 & X4 & X5 & X6)]; [left; exact L | right].
      exists h0, h1, i0. refine (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 _))))). lia.
    + intros i' k' h0 Hlt Hi' Hk' Hh0 Hfd0.
      destruct (Nat.eq_dec k' k) as [->|Hne].
      * destruct (Nat.eq_dec i' i) as [->|Hne'].
        -- exfalso. destruct Hc as [Hc|Hc]; [congruence|]. exact (Hc h0 Hh0 Hfd0).
        -- apply (Hcov i' k h0); [lia | exact Hi' | exact Hk' | exact Hh0 | exact Hfd0].
      * apply (Hcov i' k' h0); [lia | exact Hi' | exact Hk' | exact Hh0 | exact Hfd0].
  - destruct IH as (E1 & E2 & E3 & E4 & E5 & E6 & Hhist & Hcov).
    pose proof (gx_nth_some_lt _ _ _ Hh) as Hkl.
    assert (Htouch : gx_touch h h'')
      by (exists h', E', H', P, (lm_gn m1), (gn_at1 (lm_gn m1) A h), (lm_O mc), ds, c; split; assumption).
    unfold gn_set, gx_hist, gx_cov. cbn [lm_es lm_cap lm_k lm_G lm_out lm_hs].
    refine (conj E1 (conj E2 (conj E3 (conj E4 (conj E5 (conj _ (conj _ _))))))).
    + rewrite gx_setn_len. exact E6.
    + intros k'. cbn [lm_hs]. destruct (Nat.eq_dec k k') as [<-|Hne].
      * rewrite (gx_setn_same k (Some h'') (lm_hs mc) Hkl). right.
        destruct (Hhist k) as [L | (h0 & h1 & i0 & X1 & X2 & X3 & X4 & X5 & X6)].
        -- exists h, h'', i. refine (conj _ (conj eq_refl (conj Htouch (conj Hi (conj _ _))))).
           ++ rewrite <- L. exact Hh.
           ++ rewrite (gx_touch_fd h h'' Htouch). exact Hfd.
           ++ right. split; [reflexivity | lia].
        -- exfalso. rewrite Hh in X2. injection X2 as X2. subst h1.
           assert (Hii : i0 = i).
           { apply (gx_nodup_nth re_fd (lm_es m1) gn_e0 i0 i Hnd X4 Hi). rewrite <- X5. exact Hfd. }
           subst i0. lia.
      * rewrite (gx_setn_other k k' (Some h'') (lm_hs mc) Hne).
        destruct (Hhist k') as [L | (h0 & h1 & i0 & X1 & X2 & X3 & X4 & X5 & X6)]; [left; exact L | right].
        exists h0, h1, i0. refine (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 _))))). lia.
    + intros i' k' h0 Hlt Hi' Hk' Hh0 Hfd0. cbn [lm_hs] in Hh0. destruct (Nat.eq_dec k k') as [<-|Hne].
      * rewrite (gx_setn_same k (Some h'') (lm_hs mc) Hkl) in Hh0. injection Hh0 as Hh0. subst h0.
        destruct Hcnl as (Eh' & HE' & _). destruct Hcshe as (H'' & Eh'' & _). subst h'' h'. exact HE'.
      * rewrite (gx_setn_other k k' (Some h'') (lm_hs mc) Hne) in Hh0.
        apply (Hcov i' k' h0); [lia | exact Hi' | exact Hk' | exact Hh0 | exact Hfd0].
  - destruct IH as (E1 & E2 & E3 & E4 & E5 & E6 & Hhist & Hcov).
    refine (conj E1 (conj E2 (conj E3 (conj E4 (conj E5 (conj E6 (conj _ _))))))).
    + intros k'. destruct (Hhist k') as [L | (h0 & h1 & i0 & X1 & X2 & X3 & X4 & X5 & X6)]; [left; exact L | right].
      exists h0, h1, i0. refine (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 _))))). lia.
    + intros i' k' h0 Hlt Hi' Hk' Hh0 Hfd0.
      apply (Hcov i' k' h0); [lia | exact Hi' | exact Hk' | exact Hh0 | exact Hfd0].
Qed.

(* ================================================================== one check_no_loss + check_shape_ends *)
(* check_shape_ends drops records: the gone <> 0 filter or the gone = 0 ends_run *)
Lemma gx_sfilter_perm : forall (f : Z * list byte -> bool) (l : list (Z * list byte)),
  Permutation l (filter (fun r => Is_true (negb (f r))) l ++ filter (fun r => Is_true (f r)) l).
Proof.
  intros f l. induction l as [|x l IH]; [constructor|].
  change (filter (fun r => Is_true (negb (f r))) (x :: l)) with
    (if decide (Is_true (negb (f x))) then x :: filter (fun r => Is_true (negb (f r))) l
     else filter (fun r => Is_true (negb (f r))) l).
  change (filter (fun r => Is_true (f r)) (x :: l)) with
    (if decide (Is_true (f x)) then x :: filter (fun r => Is_true (f r)) l else filter (fun r => Is_true (f r)) l).
  repeat match goal with |- context [@decide ?P ?d] => destruct (@decide P d) end;
  destruct (f x) eqn:Ef; try rewrite Ef in *; cbn [negb Is_true] in *; try (exfalso; tauto).
  all: first [ (cbn [app]; apply perm_skip; exact IH) | (apply Permutation_cons_app; exact IH) ].
Qed.
Lemma gx_find_text_lt : forall y rs i, find_text y rs = Some i -> (i < length rs)%nat.
Proof.
  intros y rs. induction rs as [|r rs IH]; intros i H; revert H; cbn [find_text]; [intros H; discriminate|].
  match goal with |- context [if ?b then _ else _] => destruct b end.
  - intros H. injection H as <-. cbn [length]. lia.
  - destruct (find_text y rs) as [j|] eqn:E; cbn [option_map]; intros H; [|discriminate].
    injection H as <-. specialize (IH j eq_refl). cbn [length]. lia.
Qed.
Lemma gx_drop_perm : forall i (rs : list (Z * list byte)) d, (i < length rs)%nat ->
  Permutation rs (nth i rs d :: drop_nth i rs).
Proof.
  induction i as [|i IH]; intros [|r rs] d Hi; cbn [length] in Hi; try (exfalso; lia).
  - unfold drop_nth. cbn [nth firstn skipn app]. apply Permutation_refl.
  - unfold drop_nth in *. cbn [nth firstn skipn app].
    eapply Permutation_trans; [apply perm_skip; exact (IH rs d ltac:(lia))|]. apply perm_swap.
Qed.
Lemma gx_ends_run_perm : forall P w rs d rs' ds c, ends_run P rs d w = Some (rs', ds, c) -> Permutation rs (rs' ++ ds).
Proof.
  intros P w. induction w as [|w IH]; intros rs d rs' ds c H; revert H; cbn [ends_run].
  - intros H. injection H as <- <- <-. rewrite app_nil_r. apply Permutation_refl.
  - destruct (split_nul d) as [[l d']|]; [|intros H; discriminate].
    match goal with |- context [if ?b then _ else None] => destruct b end; [|intros H; discriminate].
    match goal with |- context [find_text ?y rs] => destruct (find_text y rs) as [i|] eqn:Ef end;
      [|intros H; discriminate].
    destruct (ends_run P (drop_nth i rs) d' w) as [[[rs'' ds''] c'']|] eqn:Er; [|intros H; discriminate].
    intros H. injection H as <- <- <-.
    pose proof (gx_find_text_lt _ _ _ Ef) as Hi.
    pose proof (IH _ _ _ _ _ Er) as HP.
    eapply Permutation_trans; [exact (gx_drop_perm i rs (0, []) Hi)|].
    eapply Permutation_trans; [apply perm_skip; exact HP|]. apply Permutation_middle.
Qed.
Lemma gx_cshe_perm : forall P g A0 ob h' h'' ds c, gn_cshe_ok P g A0 ob h' h'' ds c ->
  exists H'', h'' = set_held h' H'' /\ hl_cap H'' = hl_cap (hs_held h') /\
    Permutation (hl_recs (hs_held h')) (hl_recs H'' ++ ds).
Proof.
  intros P g A0 ob h' h'' ds c (H'' & E & _ & Hc & _ & _ & Hr). exists H''. split; [exact E|]. split; [exact Hc|].
  destruct Hr as [(_ & E1 & E2 & _) | (_ & E1)].
  - rewrite E1, E2. apply (gx_sfilter_perm (fun r => prefixb P (snd r))).
  - exact (gx_ends_run_perm _ _ _ _ _ _ _ E1).
Qed.
(* a slot's potential with its reserve, by list: the pending list, the expected list with its reserve, the held
   list (its measure gx_f and its texts' weights) *)
Definition gx_E (E : hlist) : Z :=
  bsum (alist_blks E) + AREC * Z.max 0 (2 * hl_n E - hl_cap E) + AREC * Z.max 0 (8 - hl_cap E) +
  zsum (map ls3_wk (dr3_nk (texts E))) + 32 * Z.of_nat (count_begin (texts E)) - dr3_tsz (hl_recs E).
Lemma gx_SQ_split : forall h, gx_SQ (Some h) =
  APARTIAL + bsum (alist_blks (hs_pending h)) + W_P * slot_pend (Some h) +
  AREC * Z.max 0 (2 * hl_n (hs_pending h) - hl_cap (hs_pending h)) + gx_E (hs_expected h) +
  gx_f (hl_cap (hs_held h)) (hl_n (hs_held h)) + zsum (map ls3_wk (texts (hs_held h))).
Proof.
  intros h. pose proof (ls3_held_wk (hs_held h)) as W.
  unfold gx_SQ, gx_SP, gx_RES, gx_E, gx_f. cbn [slot_blks slot_held slot_vsl slot_cred].
  rewrite dr3_bsum_asrc, (dr3_bsum_alist (hs_held h)). unfold vsl, lst_cred. unfold W_H in *. lia.
Qed.
(* check_no_loss empties the expected list and spends its reserve *)
Lemma gx_E_touch : forall E E', hl_recs E' = [] -> hl_cap E' = hl_cap E ->
  gx_E E' + zsum (map ls3_wk (dr3_nk (texts E))) + 32 * Z.of_nat (count_begin (texts E)) <= gx_E E.
Proof.
  intros E E' Hr Hc. unfold gx_E. rewrite !dr3_bsum_alist.
  assert (T' : texts E' = []) by (unfold texts; rewrite Hr; reflexivity).
  assert (N' : hl_n E' = 0) by (unfold hl_n; rewrite Hr; reflexivity).
  assert (Z1 : zsum (map ls3_wk (dr3_nk [])) = 0) by reflexivity.
  assert (Z2 : Z.of_nat (count_begin []) = 0) by reflexivity.
  assert (Z3 : dr3_tsz [] = 0) by reflexivity.
  rewrite T', N', Hr, Hc, Z1, Z2, Z3.
  assert (N0 : 0 <= hl_n E) by (unfold hl_n; lia). unfold AREC. lia.
Qed.
(* the touch's cost: at most 64, and nothing when the held vector does not shrink *)
Lemma gx_touch_cost : forall h h'', gx_touch h h'' ->
  hs_pending h'' = hs_pending h /\ hs_off h'' = hs_off h /\ hl_recs (hs_expected h'') = [] /\
  (hl_n (hs_held h'') <= hl_cap (hs_held h'') -> gx_SQ (Some h'') <= gx_SQ (Some h) + 64) /\
  (hl_cap (hs_held h) <= hl_cap (hs_held h'') -> gx_SQ (Some h'') <= gx_SQ (Some h)).
Proof.
  intros h h'' (h' & E' & H' & P & g & A0 & ob & ds & c & Hcnl & Hcshe).
  destruct (gx_cshe_perm P g A0 ob h' h'' ds c Hcshe) as (H'' & E2 & Hc'' & Hperm).
  destruct Hcnl as (E1 & HrE & _ & HcE & HndH' & HtH' & HcH' & _ & _).
  assert (Q1 : hs_pending h'' = hs_pending h) by (rewrite E2, E1; reflexivity).
  assert (Q0 : hs_off h'' = hs_off h) by (rewrite E2, E1; reflexivity).
  assert (Q2 : hs_expected h'' = E') by (rewrite E2, E1; reflexivity).
  assert (Q3 : hs_held h'' = H'') by (rewrite E2; reflexivity).
  assert (Q4 : slot_pend (Some h'') = slot_pend (Some h)) by (cbn [slot_pend]; rewrite Q1, Q0; reflexivity).
  assert (Q5 : hs_held h' = H') by (rewrite E1; reflexivity).
  rewrite Q5 in Hc'', Hperm.
  split; [exact Q1|]. split; [exact Q0|]. split; [rewrite Q2; exact HrE|].
  rewrite !gx_SQ_split, Q1, Q2, Q3, Q4.
  pose proof (gx_E_touch (hs_expected h) E' HrE HcE) as XE.
  set (Ls := texts (hs_expected h)) in *.
  set (CB := Z.of_nat (count_begin Ls)) in *.
  set (SNK := zsum (map ls3_wk (dr3_nk Ls))) in *.
  assert (Hn : hl_n (hs_held h) = Z.of_nat (length (texts (hs_held h))))
    by (unfold hl_n, texts; rewrite length_map; reflexivity).
  assert (Hn' : hl_n H' = Z.of_nat (length (texts H'))) by (unfold hl_n, texts; rewrite length_map; reflexivity).
  assert (Hn'' : hl_n H'' <= hl_n H') by (unfold hl_n; rewrite (Permutation_length Hperm), length_app; lia).
  pose proof (ls3_upds_len Ls (texts (hs_held h))) as UL. rewrite <- HtH' in UL. fold CB in UL.
  assert (W1 : zsum (map ls3_wk (texts H'')) <= zsum (map ls3_wk (texts H'))).
  { assert (P1 : Permutation (texts H') (texts H'' ++ map (fun r => bzs (snd r)) ds))
      by (unfold texts; rewrite <- map_app; apply Permutation_map; exact Hperm).
    rewrite (ls3_sum_perm _ _ P1), map_app, zsum_app.
    pose proof (zsum_map_nonneg ls3_wk (map (fun r => bzs (snd r)) ds) ls3_wk_nonneg). lia. }
  assert (W2 : zsum (map ls3_wk (texts H')) <= zsum (map ls3_wk (texts (hs_held h))) + SNK).
  { pose proof HndH' as Hnd2. apply NoDup_ListNoDup in Hnd2.
    pose proof (ls3_sum_incl (texts H') (texts (hs_held h) ++ dr3_nk Ls) Hnd2) as X.
    rewrite map_app, zsum_app in X. apply X. intros y Hy. apply in_or_app. rewrite HtH' in Hy.
    destruct (dr3_upds_in Ls _ y Hy) as [Hy'|Hy']; [left | right]; exact Hy'. }
  assert (Hcb0 : 0 <= CB) by (unfold CB; lia).
  assert (Hn0 : 0 <= hl_n (hs_held h)) by (unfold hl_n; lia).
  assert (Hn0'' : 0 <= hl_n H'') by (unfold hl_n; lia).
  assert (Hnn : hl_n H'' <= hl_n (hs_held h) + CB) by lia.
  rewrite Hc''. split.
  - intros Hnc.
    pose proof (gx_held_a (hl_cap (hs_held h)) (hl_n (hs_held h)) CB (hl_cap H') (hl_n H'')
                  Hn0 Hcb0 ltac:(lia) Hnn HcH') as XH. lia.
  - intros Hcc.
    pose proof (gx_held_b (hl_cap (hs_held h)) (hl_n (hs_held h)) CB (hl_cap H') (hl_n H'')
                  Hn0 Hcb0 Hn0'' Hnn Hcc HcH') as XH. lia.
Qed.

(* ================================================================== the slots after relay_instance_gone *)
(* the drained lines' bytes: at most the unfinished line and the pending bytes *)
Lemma gx_tot_le : forall e h0 j, gx_pf (e, (h0, j)) ->
  Z.of_nat (length (with_nul (dr_lines h0))) <= 6000 + 2 ^ 26 - 1.
Proof.
  intros e h0 j (_ & _ & _ & Hsk & HskU & Hsk01 & Hepre & _ & _ & HP26). cbn [fst snd] in *.
  destruct Hepre as (_ & HU & _ & _ & _).
  pose proof (dr3_lines h0) as (_ & HTOT & _ & _).
  pose proof (dr3_wcost e h0 Hsk HskU Hsk01) as HW.
  unfold APARTIAL in HU. revert HW. destruct (re_skip e =? 0); intros HW; lia.
Qed.
Lemma gx_res_drained : forall e h0 j c mx no cap e1 h1 LB, gx_pf (e, (h0, j)) ->
  dr_rel c mx no cap e h0 e1 h1 LB -> - gx_RES (Some h1) <= 6000 + 2 ^ 26.
Proof.
  intros e h0 j c mx no cap e1 h1 LB Hpf Hd.
  pose proof (gx_tot_le e h0 j Hpf) as HT.
  pose proof Hpf as (Hexp & _). cbn [fst snd] in Hexp.
  destruct (gx_exp_lines c mx no cap e h0 e1 h1 LB Hd Hexp) as (HT' & _ & De1 & _).
  unfold gx_RES. rewrite HT', De1.
  pose proof (zsum_map_nonneg ls3_wk (dr3_nk (dr_lines h0)) ls3_wk_nonneg). lia.
Qed.
(* each slot of m1: m's, or drained by an open pair (whose entry's fd it keeps) *)
Lemma gx_rig_slot : forall cx t m hs qs c2 O2 cap2 out2 m1,
  fr_RINV cx t m -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 -> gx_xpre m hs ->
  forall k, (k < 4)%nat ->
  nth k (lm_hs m1) None = nth k (lm_hs m) None \/
  exists e h0 h1 c mx no cap e1 LB i,
    nth k (lm_hs m) None = Some h0 /\ nth k (lm_hs m1) None = Some h1 /\ gx_pf (e, (h0, k)) /\
    dr_rel c mx no cap e h0 e1 h1 LB /\ (i < length (lm_es m1))%nat /\ re_fd (nth i (lm_es m1) gn_e0) = hs_fd h1.
Proof.
  intros cx t m hs qs c2 O2 cap2 out2 m1 HRI Hpairs Hafter Hrok HX k Hk.
  pose proof Hafter as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
  pose proof Hpairs as (Hlh & HPok & _).
  pose proof Hrok as (Hrr & Hlq & _ & _).
  pose proof (gx_pq_facts cx m hs qs c2 O2 cap2 out2 m1 Hpairs Hafter Hrok) as HPQ.
  pose proof (gx_pf_all cx t m hs HRI Hpairs HX) as HPF.
  pose proof (gx_rig_pairs _ _ _ _ _ _ _ _ _ _ Hrr) as HRP.
  rewrite Forall_forall in HPQ, HPF, HRP, HPok.
  set (ps := combine (lm_es m) hs) in *.
  destruct (in_dec Nat.eq_dec k (rig_slots ps)) as [Hin|Hnin]; [right | left; exact (A12 k Hk Hnin)].
  destruct (gx_rs_in k ps Hin) as (p & Hp & Heof & Hpk).
  destruct (In_nth ps p (gn_e0, gn_hj0) Hp) as (i & Hi & Hpi).
  assert (Hlps : length ps = length qs) by (unfold ps; rewrite length_combine; lia).
  set (q := nth i qs gn_q0).
  assert (Hpq : In (p, q) (combine ps qs)).
  { rewrite <- Hpi. unfold q. rewrite <- combine_nth by exact Hlps. apply nth_In. rewrite length_combine. lia. }
  destruct (HRP _ Hpq) as (Hfdq & Hdr). cbn [fst snd] in Hfdq, Hdr.
  destruct (Hdr Heof) as (c & mx & no & cap & e1 & LB & Hd).
  destruct (HPQ _ Hpq Heof) as (_ & Hm & Hm1). cbn [fst snd] in Hm, Hm1.
  pose proof (HPF p Hp Heof) as Hpf.
  destruct (HPok p Hp Heof) as (_ & _ & Hfd0 & _).
  destruct p as [e [h0 j]]. cbn [fst snd] in *. subst j.
  destruct (gx_dr_rel _ _ _ _ _ _ _ _ _ Hd) as (_ & _ & _ & _ & _ & _ & _ & _ & Hfd1 & _).
  exists e, h0, (snd q), c, mx, no, cap, e1, LB, i.
  split; [exact Hm|]. split; [exact Hm1|]. split; [exact Hpf|]. split; [exact Hd|].
  split; [rewrite A3, length_map; lia|].
  rewrite A3. change gn_e0 with (fst gn_q0). rewrite map_nth. fold q. rewrite Hfdq, Hfd1. symmetry. exact Hfd0.
Qed.

(* ================================================================== E1: the model after the operation *)
(* the potential, the pending records, the open slots and the input consumed, m against mc *)
Lemma gx_end_core : forall cx t m hs qs c2 O2 cap2 out2 m1 mc A,
  fr_RINV cx t m -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 -> gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat ->
  gx_xend m hs mc ->
  PHI3 mc <= PHI3 m /\ npend mc <= npend m /\ nopen (lm_hs mc) = nopen (lm_hs m) /\
  length (lm_hs mc) = 4%nat /\ lm_k m + 1 <= lm_k mc.
Proof.
  intros cx t m hs qs c2 O2 cap2 out2 m1 mc A HRI Hpairs Hafter Hrok Hrun (HX & Hgrow).
  pose proof (gx_rig_phase cx t m hs qs c2 O2 cap2 out2 m1 HRI Hpairs Hafter Hrok HX) as HPH.
  pose proof Hafter as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
  pose proof Hrok as (_ & _ & _ & Hfds).
  assert (Hnd : List.NoDup (map re_fd (lm_es m1))) by (rewrite A3; apply NoDup_ListNoDup; exact Hfds).
  destruct (gx_run _ m1 mc A _ _ Hrun Hnd) as (R1 & R2 & R3 & R4 & R5 & R6 & Hhist & Hcov).
  pose proof HRI as (_ & (Hl4 & _) & _).
  assert (Hlc : length (lm_hs mc) = 4%nat) by lia.
  assert (Hslot : forall k', (k' < 4)%nat ->
            gx_RES (nth k' (lm_hs mc) None) = 0 /\
            slot_npend (nth k' (lm_hs mc) None) <= slot_npend (nth k' (lm_hs m) None) /\
            slot_open (nth k' (lm_hs mc) None) = slot_open (nth k' (lm_hs m) None) /\
            gx_SQ (nth k' (lm_hs mc) None) <= gx_SQ (nth k' (lm_hs m1) None)).
  { intros k' Hk'.
    destruct (gx_rig_slot cx t m hs qs c2 O2 cap2 out2 m1 HRI Hpairs Hafter Hrok HX k' Hk')
      as [L2 | (e & h0 & h1 & c & mx & no & cap & e1 & LB & i1 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6)].
    - destruct (Hhist k') as [L | (h & h'' & i0 & X1 & X2 & X3 & _)].
      + rewrite L, L2. split; [|split; [lia | split; [reflexivity | lia]]].
        destruct (nth k' (lm_hs m) None) as [h0|] eqn:Eh; [|reflexivity].
        destruct (gx_rinv_slot cx t m k' h0 HRI Hk' Eh) as (Hexp & _). exact (gx_RES_empty h0 Hexp).
      + rewrite X2, X1. rewrite X1 in L2.
        destruct (gx_touch_cost h h'' X3) as (T1 & _ & T3 & _ & T5).
        rewrite <- L2. split; [exact (gx_RES_empty h'' T3)|]. split; [cbn [slot_npend]; rewrite T1; lia|].
        split; [reflexivity|]. apply T5. exact (Hgrow k' h h'' (eq_sym L2) X2).
    - destruct (gx_dr_rel _ _ _ _ _ _ _ _ _ Y4) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Dpend & _ & _ & _ & Dheld & _).
      assert (Hn0 : slot_npend (Some h1) = 0) by (cbn [slot_npend]; unfold hl_n; rewrite Dpend; reflexivity).
      assert (Hn1 : 0 <= slot_npend (Some h0)) by apply slot_npend_nonneg.
      rewrite Y1. destruct (Hhist k') as [L | (h & h'' & i0 & X1 & X2 & X3 & _)].
      + rewrite L, Y2.
        assert (Hexp1 : hl_recs (hs_expected h1) = []).
        { apply (Hcov i1 k' h1); [lia | exact Y5 | exact Hk' | rewrite L; exact Y2 | symmetry; exact Y6]. }
        split; [exact (gx_RES_empty h1 Hexp1)|]. split; [lia|]. split; [reflexivity | lia].
      + rewrite X2, X1. rewrite X1 in Y2. injection Y2 as Y2. subst h1.
        destruct (gx_touch_cost h h'' X3) as (T1 & _ & T3 & _ & T5).
        split; [exact (gx_RES_empty h'' T3)|].
        split; [cbn [slot_npend] in Hn0, Hn1 |- *; rewrite T1; lia|]. split; [reflexivity|].
        apply T5. rewrite Dheld. exact (Hgrow k' h0 h'' Y1 X2). }
  destruct (Hslot 0%nat ltac:(lia)) as (a0 & b0 & c0 & d0). destruct (Hslot 1%nat ltac:(lia)) as (a1 & b1 & c1 & d1).
  destruct (Hslot 2%nat ltac:(lia)) as (a2 & b2 & c2' & d2). destruct (Hslot 3%nat ltac:(lia)) as (a3 & b3 & c3 & d3).
  assert (HP3 : PHI3 mc <= gx_PHX m1).
  { assert (Hres : zsum (map gx_RES (lm_hs mc)) = 0) by (rewrite (gx_sum4 gx_RES (lm_hs mc) Hlc); lia).
    assert (HSQ : zsum (map gx_SQ (lm_hs mc)) <= zsum (map gx_SQ (lm_hs m1)))
      by (rewrite (gx_sum4 gx_SQ (lm_hs mc) Hlc), (gx_sum4 gx_SQ (lm_hs m1) A11); lia).
    pose proof (gx_PHX_split mc) as P1. pose proof (gx_PHX_split m1) as P2. rewrite R1, R2 in P1.
    unfold gx_PHX in P1. lia. }
  split; [lia|]. split.
  { unfold npend. rewrite (gx_sum4 slot_npend (lm_hs mc) Hlc), (gx_sum4 slot_npend (lm_hs m) Hl4). lia. }
  split.
  { rewrite !nopen_zsum, (gx_sum4 slot_open (lm_hs mc) Hlc), (gx_sum4 slot_open (lm_hs m) Hl4). lia. }
  split; [exact Hlc|].
  rewrite R3, A1. unfold gn_kq. destruct (gn_more cx m); lia.
Qed.

Variable B : asyms.
(* the call room of fr_LS3 (ReplyB3LS3.v, as ReplyLSB.fr_LS takes it) *)
Variable CALL_ROOM_B : Z.
(* E1 at LS := fr_LS3 B: GN_RI_end's `LS cx (t + 1) mc lyx Sx` at the official premises (mo_le unused) and the
   named extra hypothesis gx_xend (gx_xpre, held vectors not shrinking) *)
Lemma gx_end_LS3 : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate) cst,
  fr_RINV cx t m -> fr_LS3 B CALL_ROOM_B cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  forall Hx : gx_xend m hs mc,
  fr_LS3 B CALL_ROOM_B cx (t + 1) mc lyx Sx.
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst HRI HLS Hpairs Hafter Hrok Hrun _ Hfr Hx.
  destruct (gx_end_core cx t m hs qs c2 O2 cap2 out2 m1 mc A HRI Hpairs Hafter Hrok Hrun Hx)
    as (C1 & C2 & C3 & C4 & C5).
  destruct HLS as (rest & e0 & HP & HR & HE & Hc & Hl & Hnp & HM).
  exists rest, e0. split; [exact (Hfr rest HP)|]. split; [exact HR|]. split; [exact HE|]. split; [exact Hc|].
  split; [exact C4|].
  assert (Hk : kk cx m <= kk cx mc) by (unfold kk; lia).
  split; [lia|]. rewrite C3. unfold MB_K in *. lia.
Qed.
(* E1 at LS := fr_LS3c B: fr_LS3's, and fr_CNT by fr_CNT_same_rest (the frame keeps fr_LS3's rest; npend only
   falls: the drained sources' pending lists are emptied, the loop keeps them) *)
Lemma gx_end_LS3c : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate) cst,
  fr_RINV cx t m -> fr_LS3c B CALL_ROOM_B cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  forall Hx : gx_xend m hs mc,
  fr_LS3c B CALL_ROOM_B cx (t + 1) mc lyx Sx.
Proof.
  intros cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst HRI (HLS & HCNT) Hpairs Hafter Hrok Hrun Hmle Hfr Hx.
  split; [exact (gx_end_LS3 cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A lyx Sx cst HRI HLS Hpairs Hafter Hrok Hrun
                   Hmle Hfr Hx)|].
  destruct (gx_end_core cx t m hs qs c2 O2 cap2 out2 m1 mc A HRI Hpairs Hafter Hrok Hrun Hx) as (_ & C2 & _).
  destruct HLS as (rest & e0 & HP & _).
  exact (fr_CNT_same_rest B cx t (t + 1) m mc ly S lyx Sx rest HP (Hfr rest HP) ltac:(lia) HCNT).
Qed.

(* ================================================================== S1: check_no_loss's room in the loop *)
(* GN_RI_step's `cnl_room MMAX (blocks_bytes Sx) ..` at LS := fr_LS3 B, at the official premises (mo_le unused)
   and the named extra hypothesis gx_xstep (gx_xpre, the held lists' count clause at the loop's state) *)
Lemma gx_step_room : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (lyx : alayout) (Sx : astate) cst,
  fr_RINV cx t m -> fr_LS3 B CALL_ROOM_B cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A i k -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  forall Hx : gx_xstep m hs mc,
  cnl_room MMAX (blocks_bytes Sx) (texts (hs_held h)) (hl_cap (hs_held h)) (hl_recs (hs_expected h)).
Proof.
  intros HCRB cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst HRI HLS Hpairs Hafter Hrok Hrun _ Hfr Hi Hk Hh
    Hfd (HX & Hcnt).
  pose proof (gx_rig_phase cx t m hs qs c2 O2 cap2 out2 m1 HRI Hpairs Hafter Hrok HX) as HPH.
  pose proof Hafter as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
  pose proof Hrok as (_ & _ & _ & Hfds).
  assert (Hnd : List.NoDup (map re_fd (lm_es m1))) by (rewrite A3; apply NoDup_ListNoDup; exact Hfds).
  destruct (gx_run _ m1 mc A _ _ Hrun Hnd) as (R1 & R2 & R3 & R4 & R5 & R6 & Hhist & _).
  pose proof HRI as (_ & (Hl4 & _) & _).
  assert (Hlc : length (lm_hs mc) = 4%nat) by lia.
  (* per slot: the loop's cost so far and the expected lists' blocks *)
  assert (Hslot : forall k', (k' < 4)%nat ->
            - gx_RES (nth k' (lm_hs mc) None) <= 6000 + 2 ^ 26 /\
            gx_SQ (nth k' (lm_hs mc) None) <= gx_SQ (nth k' (lm_hs m1) None) + 64).
  { intros k' Hk'.
    destruct (Hhist k') as [L | (h0 & h'' & i0 & X1 & X2 & X3 & _)].
    - rewrite L. split; [|lia].
      destruct (gx_rig_slot cx t m hs qs c2 O2 cap2 out2 m1 HRI Hpairs Hafter Hrok HX k' Hk')
        as [L2 | (e & h0 & h1 & c & mx & no & cap & e1 & LB & i1 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6)].
      + rewrite L2. destruct (nth k' (lm_hs m) None) as [h0|] eqn:Eh; [|cbn [gx_RES]; lia].
        destruct (gx_rinv_slot cx t m k' h0 HRI Hk' Eh) as (Hexp & _). rewrite (gx_RES_empty h0 Hexp). lia.
      + rewrite Y2. exact (gx_res_drained e h0 k' c mx no cap e1 h1 LB Y3 Y4).
    - rewrite X2, X1. destruct (gx_touch_cost h0 h'' X3) as (_ & _ & T3 & T4 & _).
      split; [rewrite (gx_RES_empty h'' T3); lia|]. apply T4. exact (Hcnt k' h'' X2). }
  (* the room at Sx: fr_LS3's bound at m, the frame's rest, the potential's step *)
  assert (Hroom : blocks_bytes Sx + 3892199361 <= LIVE_MAX).
  { destruct HLS as (rest & e0 & HP & HR & HE & Hc & Hl & Hnp & HM).
    pose proof (Hfr rest HP) as HP'.
    rewrite (blocks_bytes_bsum B lyx Sx), (bsum_perm _ _ HP'), !bsum_app.
    pose proof (PHI3_ge mc) as G1.
    destruct (Hslot 0%nat ltac:(lia)) as (a0 & b0). destruct (Hslot 1%nat ltac:(lia)) as (a1 & b1).
    destruct (Hslot 2%nat ltac:(lia)) as (a2 & b2). destruct (Hslot 3%nat ltac:(lia)) as (a3 & b3).
    assert (G2 : PHI3 mc <= gx_PHX mc + 4 * (6000 + 2 ^ 26)).
    { unfold gx_PHX. rewrite (gx_sum4 gx_RES (lm_hs mc) Hlc). lia. }
    assert (G3 : gx_PHX mc <= gx_PHX m1 + 256).
    { rewrite !gx_PHX_split, R1, R2, (gx_sum4 gx_SQ (lm_hs mc) Hlc), (gx_sum4 gx_SQ (lm_hs m1) A11). lia. }
    pose proof (nopen_le4 _ Hl) as Hno4. pose proof (npend_nonneg m) as Hnp0.
    assert (Hkk : kk cx m <= c_n cx) by (unfold kk; lia).
    assert (HC : YCfn_cf.CALL_ROOM_B = 8589934592) by reflexivity.
    clear - G1 G2 G3 HPH HM HR HE Hc Hno4 Hnp0 Hkk HC HCRB Hnp.
    unfold MB_K, MB_C, W_OPEN, E_ENT, K0, APARTIAL in *. lia. }
  (* the slot the loop calls check_no_loss on *)
  destruct (Hhist k) as [L | (h0 & h'' & i0 & X1 & X2 & X3 & _)].
  - destruct (gx_rig_slot cx t m hs qs c2 O2 cap2 out2 m1 HRI Hpairs Hafter Hrok HX k Hk)
      as [L2 | (e & h0 & h1 & c & mx & no & cap & e1 & LB & i1 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6)].
    + rewrite L, L2 in Hh. destruct (gx_rinv_slot cx t m k h HRI Hk Hh) as (Hexp & _). rewrite Hexp. exact I.
    + rewrite L, Y2 in Hh. injection Hh as Hh. subst h1.
      pose proof Y3 as (Hexp0 & _). cbn [fst snd] in Hexp0.
      destruct (gx_exp_lines c mx no cap e h0 e1 h LB Y4 Hexp0) as (HT & _ & _ & Hrec).
      destruct (gx_dr_rel _ _ _ _ _ _ _ _ _ Y4) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Dheld & _).
      pose proof (gx_tot_le e h0 k Y3) as HTOT.
      destruct (gx_rinv_slot cx t m k h0 HRI Hk Y1) as (_ & _ & _ & Hhc & Hndh & e2 & Hss & Hkt).
      apply (dr3_room MMAX (hl_recs (hs_expected h)) (texts (hs_held h)) (hl_cap (hs_held h)) (blocks_bytes Sx)
               33521663 (6000 + 2 ^ 26)).
      * unfold dr3_M. change (map (fun r => bzs (snd r)) (hl_recs (hs_expected h))) with (texts (hs_expected h)).
        rewrite HT, Dheld.
        pose proof (dr3_held_len (re_keys e2) (hs_held h0) Hndh Hss) as HHL.
        destruct (ls3_keys_parts (re_keys e2)) as (KP1 & _).
        assert (KP0 : 0 <= zsum (map (fun k0 => Z.of_nat (length (gestures_end_b_c.key_text k0))) (re_keys e2)))
          by (apply zsum_map_nonneg; intros; lia).
        pose proof (dr3_lines h0) as (_ & _ & _ & HCB).
        lia.
      * assert (HW : MMAX = 1072693248) by exact fr_MMAX_val. lia.
      * intros r Hr. pose proof (Hrec r Hr). lia.
      * pose proof (Z.le_max_l 0 (dr3_vec (hl_cap (hs_held h)))). lia.
  - rewrite X2 in Hh. injection Hh as Hh. subst h''.
    destruct (gx_touch_cost h0 h X3) as (_ & _ & T3 & _). rewrite T3. exact I.
Qed.
(* S1 at LS := fr_LS3c B CALL_ROOM_B *)
Lemma gx_step_room_c : YCfn_cf.CALL_ROOM_B <= CALL_ROOM_B ->
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (lyx : alayout) (Sx : astate) cst,
  fr_RINV cx t m -> fr_LS3c B CALL_ROOM_B cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A i k -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  forall Hx : gx_xstep m hs mc,
  cnl_room MMAX (blocks_bytes Sx) (texts (hs_held h)) (hl_cap (hs_held h)) (hl_recs (hs_expected h)).
Proof.
  intros HCRB cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst HRI (HLS & _).
  exact (gx_step_room HCRB cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h lyx Sx cst HRI HLS).
Qed.
End acct.

(* S2 / S3 at the two LS instances, at the official premises (gx_step_cnl_meter / gx_step_cshe_meter are the same
   at any LS) *)
Section meter3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the call room of fr_LS3 (ReplyB3LS3.v, as ReplyLSB.fr_LS takes it) *)
Variable CALL_ROOM_B : Z.
Lemma gx_step_cnl_meter_LS3 : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (lyx : alayout) (Sx : astate)
    cst,
  fr_RINV cx t m -> fr_LS3 B CALL_ROOM_B cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A i k -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  mo_ok MT Sx (cnl_cost MT (hs_expected h) (hs_held h)).
Proof. intros. exact I. Qed.
Lemma gx_step_cnl_meter_LS3c : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (lyx : alayout) (Sx : astate)
    cst,
  fr_RINV cx t m -> fr_LS3c B CALL_ROOM_B cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A i k -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  mo_ok MT Sx (cnl_cost MT (hs_expected h) (hs_held h)).
Proof. intros. exact I. Qed.
Lemma gx_step_cshe_meter_LS3 : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (lyx : alayout)
    (Sx : astate) cst,
  fr_RINV cx t m -> fr_LS3 B CALL_ROOM_B cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A i k -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  forall h' E' H' (Sy : astate) cst', gn_cnl_ok h h' E' H' -> mo_le MT Sx Sy cst' ->
  mo_ok MT Sy (hl_n (hs_held h') * mo_free MT).
Proof. intros. exact I. Qed.
Lemma gx_step_cshe_meter_LS3c : forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (lyx : alayout)
    (Sx : astate) cst,
  fr_RINV cx t m -> fr_LS3c B CALL_ROOM_B cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A i k -> mo_le MT S Sx cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  forall h' E' H' (Sy : astate) cst', gn_cnl_ok h h' E' H' -> mo_le MT Sx Sy cst' ->
  mo_ok MT Sy (hl_n (hs_held h') * mo_free MT).
Proof. intros. exact I. Qed.
End meter3.

Print Assumptions gx_WR_MMAX_pin.
Print Assumptions gx_end_LS3.
Print Assumptions gx_end_LS3c.
Print Assumptions gx_step_room.
Print Assumptions gx_step_room_c.
Print Assumptions gx_step_cnl_meter_LS3.
Print Assumptions gx_step_cnl_meter_LS3c.
Print Assumptions gx_step_cshe_meter_LS3.
Print Assumptions gx_step_cshe_meter_LS3c.
