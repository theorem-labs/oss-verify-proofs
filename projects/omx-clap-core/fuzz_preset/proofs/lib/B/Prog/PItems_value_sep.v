(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_head.v, with its module paths and module names changed; 2323 of its 2524 lines of code are new or changed and 1105 lines of the source are left out. *)
(* Theorem Labs, 2026-10: block SEP of parse_items' image-B walk (segment VALUE,
   file 4 of 4): B 0x87dbc .. 0x87e1c (PV_O_SEP .. PI_O_GROW2 + 4) and the closer test
   0x87f38 .. 0x87f54 (PI_O_CLS1, B's duplicate close block). Rule 24: proves no function (kind: segment lemma).
   PROVED (Qed): pv_sep_holds : forall N, (forall N', N' < N -> pi_body_spec B ARx SK d CTX0 CW N') ->
     pi_close2_spec B ARx SK d CTX0 CW -> pi_epi_spec B ARx SK d -> pv_sep_spec B ARx SK d CTX0 CW N,
   PItems_value_pres.v's pv_sep_spec at image B (B_prog_listing / PL_prog_B / PI_prog_B, prh_img_B), at the texts'
   current form: the cursor set CW, the BUDGETED journal (pi_ajR .. WS0 at
   wbudget CW 0; every run on the rebased empty-budget journal, YCbqGwild.ajournal_xw_rebaseR / unbase0R; grow, an
   unbudgeted callee, by YCbqGcallW.aj_call_xW_spR on the rebased journal, so the budget stays WS0), and the text's post:
   at the refusal exits the OUTCOME (PItems_ledk1.pik1_run_granted on the granted prefix pi_grant), the ledger move
   over the all-granted trace (pik1_move_regt) and the partial tree's free order (PItems_forder.pi_forder_at,
   pis_fo_open); at the closer pi_close_pre's free order at every nn >= depth of the closed tree and its capacities
   (pvs_ncap_mk); at the comma PItemsBody.Loop's batch-kit step with pi_fl_eq from pv_jfk's comma branch, the members'
   capacities and free order carried across the in->p++ store (PItems_value_model.v pvm_ncaps_frame /
   pvm_forder_frame). Earlier kit: form (b) (no rp_* binders, most / own after ran).
   THE TRAVELLING FACTS (pv_sep_pre's memnorm memc, and pi_posb S Sc tr0 / pi_live over tr0): the overlay's normality
   rides every run by the invariant runners YC1fPx.v paj_run_to_x_inv / paj_run_x_inv at YSRrMemnorm.v
   srr_inv_laws_memnorm_k (RUNTOI / RUNI, the in->p store included) and grow's fpostWm keep; pi_posb / pi_live go into
   PItems_body_loop.v's step at the grow call, which extends them over grow's events; the refusal and closer exits read
   them as they are (the state Sc is unchanged: pvs_refuse_post, pvs_close_data). grow's two live-count premises come
   from pi_ent's at the block's pi_live (PItems_value_model.v pvm_lc_call, PRH_FnReader.v prhPg_evs_model under
   PIL_HEAD); fpre's frm_zero from pi_fpok. Every prh_ledger fact is read through PRH_Base.v's ledger_proj projections
   (prh_ledger_nodup / _blocks / _bounds), never by its position.
   THE RUN (YC1fPx paj_run_to_tok_x_inv / paj_run_tok_x_inv and psrr_branch_tok from the symbolic state ss_pvs, realised by
   pvs_st_ok: q's 24 bytes as one region of atom 9 whose p field is writable in the comma arm, the cursor byte as its own
   region of atom 32 with a 1-byte shadow entry):
     0x87dbc .. 0x87dd4: the shadow checks of q and q + 8, end := q->end, p := q->p, `bgeu p, end` split by hand:
       p >= end refuses (pvs_run_refused) to PI_O_EPI;
     0x87dd8 .. 0x87df4: `beqz p`, the cursor byte's shadow and its partial-granule slow path, c := *p, `bne c, 44`
       split by hand;
     c <> 44, 0x87f38 .. 0x87f54: the shadow byte again, the closer 125 (object) / 93 (array) from s2, `bne closer, c`
       split by hand: not the closer refuses (pvs_refuse_post) to PI_O_EPI; the closer falls through to PI_O_CLOSE2 with
       the container's n + 1 members as the finished tree (pvs_close_data, pi_close2_spec);
     c = 44, 0x87df8 .. 0x87e14: `beq p, -1`, the shadow check of q, q->p := p + 1, a0 := s3 = v, `jal grow`: the call by
       YCbqGcallW.v aj_call_xW_spR with grow's text GROW (footprint pvs_FP1: v's kids / keys and cap fields and the slot
       blocks' allocator hulls), then at 0x87e18 (pvs_tail) `beqz a0`: a0 = 0 re-enters the loop body at PI_O_BODY with
       N' := length (rest after the comma) < N (pvs_grow_post, pi_body_spec), a0 = -1 goes to PI_O_EPI with the refusal
       post, both from the grow-post step (PItems_body_loop.v pil_grow_step, Qed) on grow's post.
   CHECKS NOT TAKEN, each with its fact (the runs of pvs_core):
     0x87dc0 / 0x87dc8 bnez on shadow (q) / shadow (q + 8), to errpath 0x88058 / 0x88060: the shadow entry (q, 0, 24)
       from pi_cur's range_addressable q 24 (pvs_core, first paj_run_to_tok_x of each arm);
     0x87dd8 beqz p, to PI_O_TRAP: the atom fact 4096 <= p (pi_cur's pj_in_okR: 0 < text <= p) (second run);
     0x87de8 -> 0x87e20 `andi a3, p, 7; bge a3, a2`, to errpath_load1 0x880d4: the cursor byte's shadow entry (p, 0, 1)
       from src_rd's range_addressable of the text (the byte p lies in it, p < text + len) (second run);
     0x87dfc beq p, -1, to PI_O_TRAP: the atom fact p <= 2 ^ 47 - 2 (comma arm's paj_run_tok_x);
     0x87e04 bnez on shadow (q) before the store, to errpath 0x88090: the shadow entry (q, 0, 24) (comma arm's run);
     0x87f3c bnez on the cursor byte's shadow, to 0x88010 / errpath 0x88018: the shadow entry (p, 0, 1) (closer arm's
       paj_run_to_tok_x).
   SECTION HYPOTHESES of pv_sep_holds (Section top):
     LAWS : AR_laws_x SEGS B ARx cf_head (the engine's laws at the instance's head length, as PItems_body.v /
       PItems_body_loop.v state them). OWNER: the instance (top);
     PIL_HEAD : cf_head = PresetReqAt.HEAD (the instance's head length is the model's; PItems_body_loop.v's PIL_HEAD,
       same text). OWNER: the instance (reflexivity at the preset's CfParams);
    GROW : forall fy, tgrow_specX (fx := fy) B ARx SK CTX0 (the text, lib/A/PRH_FnReader.v, verbatim: the two
      live-count premises, the hull budget, each post arm's live-request permutation and position implication, the
      refused arms' OUTCOME exclusion; it concludes YA0nH.SRr' segs RZ_cf with its post at wle');
    HKEPT : pi_cur_kept_callR_stmt B ARx (lib/B/Prog/PItems_kept.v, a statement there over a world relation R, the
      callee journal at a budget WS1 last - grow's at WS1 := []; proved there as pi_cur_kept_callR from HSH / HZS /
      HIMG / HPSTRO), taken at R := wle' segs RZ_cf.
  The cursor set CW is a Variable of the Sections main / top (the specs' parameter after CTX0).
  THE RE-HIDING MOVE: grow frees, so the walk runs at the world relation wle' segs RZ_cf (YA0nH): the journals pi_ajR,
    the goal pi_goalR, the runners PI_RUNTOR / PI_RUNR / paj_run_to_x_invR / paj_run_x_invR, the branch paj_branchR,
    the journal steps YCbqGwild.ajournal_xw_rebaseR / unbase0R and grow's call YCbqGcallW.aj_call_xW_spR, all at
    wle'; pvs_tail / pvs_epi / pvs_grow_post conclude YA0nH.SRr' segs RZ_cf with the text's fpostWFbm (at wle'). THE HULL
    (route (b)): grow's hull budget at the call from pi_ent's (PItems_defs.pi_ent_hull) by PItems_posb.pi_posb_budget
    over the split pvm_gt_pref / pil_gt_split; the refusal exit's hull use from pi_posb over tr0 (= the all-granted
    trace there). The texts' posts are read and built through their named layers (tpiP_R_of / tpiP_Q_of_R, tgrP_R_of and
    the arm records); the refusal exit's injected-reading conjunct by PItems_defs.pi_grant_granted.
   COPIED (their files bring image A's instances or are not on this base): pvs_rod_kept / pvs_rdword_of_val /
     pvs_zmaxl_in / pvs_zmaxl_nonneg (PItems_body_key.v pik_rod_kept / pik_rdword_of_val / pik_zmaxl_in /
     pik_zmaxl_nonneg), pvs_pst_allb / pvs_in_ro_b / pvs_pst_not_ro (lib/A/Prog/S1ImgA.v pst_allb / in_ro_b and
     lib/B/Prog/S1ImgB.v pst_not_ro_B, over SEGS), pvs_stk_nonneg (PItems_head.v pi_stk_nonneg).
   IMPORTED from PItemsB.PItemsBody.Loop (lib/B/Prog/PItems_body_loop.v): pil_grow_step (the grow-post step, the batch kit's form,
     applied as PVS_STEP := pil_grow_step B ARx LAWS PIL_HEAD), pil_gt_split, pil_lsum_perm, pil_gcap.
   Numerals: 0x384 (via PV_O_SEP) and PI_O_GROW2 + 4 (PVS_O_GROWR, the return offset) LENGTH, offsets inside the body;
   144 LENGTH (the frame), 56, 48, 40, 24, 16, 8 LENGTH (the node, its fields, the cursor struct, a word, alignment);
   4096 LENGTH (the page); 16560 DERIVED (LEAF_pv_pi, checked by vm_compute); 44, 125, 93 WORD (',', '}', ']');
   6, 5 WORD (pj_value type tags); 3 WORD (the shadow shift); 2 ^ 32 .. 2 ^ 64 DERIVED (address-space and shadow
   bounds); register, atom and region indices DERIVED (the engine's numbering). No ADDRESS: every pc is PI_AT PI_O_*,
   PIAT PV_O_SEP / PVS_O_GROWR or the engine's computed offset; the hexadecimal addresses above are comments only. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YC80x YC80xf YPsym YC4aP YImgTop YC1fP YC1fPx YCbqG YCbqGcall YCbqGcallW YP08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_defs PItems_pres
  PItems_value_pres PItems_value_model PItems_shape PItems_kept PItems_agr PItems_body_loop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetRun PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_posb.
(* The batch kit: the order-list layer, the granted-prefix tools, the ordered exit lemmas, the budgeted journal *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_ledk1 PItems_forder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
(* the walk's world relation wle' segs RZ_cf (the re-hiding move) and the hull (route (b)) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.


(* ================================================================================================== *)
(* 2. THE MODEL AT THE SEPARATOR (machine-free). pv_run_after's continuation pv_kont (PItems_value_pres.v)
   decides the member's tail on skip r: ',' runs the loop on at n + 1, the closer finishes the container,
   anything else (or nothing) refuses. *)
(* ================================================================================================== *)

Lemma pvs_rev_snoc : forall (acc : list (list Z * jv)) x, rev (acc ++ [x]) = x :: rev acc.
Proof. intros acc x. rewrite rev_app_distr. reflexivity. Qed.

Lemma pvs_rev_kont : forall (acc : list (list Z * jv)) nm t, rev ((nm, t) :: rev acc) = acc ++ [(nm, t)].
Proof. intros acc nm t. cbn [rev]. rewrite rev_involutive. reflexivity. Qed.

Lemma pvs_closer_44 : forall o, (closer o =? 44) = false.
Proof. intros [|]; reflexivity. Qed.

(* the byte after the white space is neither ',' nor the closer, or there is none: the whole call refuses, with
   no event after the value's *)
Lemma pvs_run_refused : forall d o x0 ok0 tr0 f n cap acc nm t r,
  pv_run_after d o x0 ok0 tr0 f n cap acc nm (Some (t, r)) ->
  match skip r with [] => True | c :: _ => c <> 44 /\ c <> closer o end ->
  forall ok1, jr_items prh_jr_strtod d o x0 (ok0 ++ ok1) = (None, tr0, ok1).
Proof.
intros d o x0 ok0 tr0 f n cap acc nm t r HR Hc ok1.
cbn [pv_run_after] in HR. rewrite <- (app_nil_r tr0). apply HR.
unfold pv_kont. destruct (skip r) as [|c r1]; [reflexivity|].
destruct Hc as [H44 Hcl].
rewrite (proj2 (Z.eqb_neq c 44) H44), (proj2 (Z.eqb_neq c (closer o)) Hcl). reflexivity.
Qed.

(* the byte is the closer: the container with its n + 1 members is the call's tree *)
Lemma pvs_run_closed : forall d o x0 ok0 tr0 f n cap acc nm t r r1,
  pv_run_after d o x0 ok0 tr0 f n cap acc nm (Some (t, r)) ->
  skip r = closer o :: r1 ->
  forall ok1, jr_items prh_jr_strtod d o x0 (ok0 ++ ok1) = (Some (mk o (acc ++ [(nm, t)]), r1), tr0, ok1).
Proof.
intros d o x0 ok0 tr0 f n cap acc nm t r r1 HR Hs ok1.
cbn [pv_run_after] in HR. rewrite <- (app_nil_r tr0). apply HR.
unfold pv_kont. rewrite Hs, pvs_closer_44, Z.eqb_refl, pvs_rev_kont. reflexivity.
Qed.

(* the byte is ',': the member loop runs on from the cursor after it, with n + 1 members *)
Lemma pvs_run_comma : forall d o x0 ok0 tr0 f n cap acc nm t r r1,
  pv_run_after d o x0 ok0 tr0 f n cap acc nm (Some (t, r)) ->
  skip r = 44 :: r1 ->
  pi_run_eq d o x0 ok0 tr0 f (S n) cap (acc ++ [(nm, t)]) r1.
Proof.
intros d o x0 ok0 tr0 f n cap acc nm t r r1 HR Hs ok1 r' t' ok2 Hj.
cbn [pv_run_after] in HR. apply HR.
unfold pv_kont. rewrite Hs, Z.eqb_refl. rewrite pvs_rev_snoc in Hj. exact Hj.
Qed.

(* ---- THE FREE-LIST MODEL AT THE SEPARATOR (the batch kit, PItems_value_pres.v pv_jfk): not ',' (or nothing) closes jfl's member
   with the arrays; ',' runs jfl on at n + 1 from the rest after it ---- *)
Lemma pvs_jfk_stop : forall f D o n cap af1 r ok, match skip r with [] => True | c :: _ => c <> 44 end ->
  pv_jfk f D o n cap af1 r ok = af1 ++ PresetReqAt.arrz o cap.
Proof.
intros f D o n cap af1 r ok Hc. unfold pv_jfk. destruct (skip r) as [|c r1]; [reflexivity|].
rewrite (proj2 (Z.eqb_neq c 44) Hc). reflexivity.
Qed.

Lemma pvs_jfk_comma : forall f D o n cap af1 r r1 ok, skip r = 44 :: r1 ->
  pv_jfk f D o n cap af1 r ok = PresetReqAt.jfl ReaderRes.jr_strtod f D o (S n) cap af1 r1 ok.
Proof. intros f D o n cap af1 r r1 ok Hs. unfold pv_jfk. rewrite Hs, Z.eqb_refl. reflexivity. Qed.

(* the model after ',' is pi_fl_eq at the next loop head (n + 1 members, the rest after the comma) *)
Lemma pvs_fl_comma : forall d o x0 ok0 f n cap af1 r r1, skip r = 44 :: r1 ->
  (forall ok1, prhPi_frees d o x0 (ok0 ++ ok1) = pv_jfk f (Nat.succ d) o n cap af1 r ok1) ->
  pi_fl_eq d o x0 ok0 f (S n) cap af1 r1.
Proof. intros d o x0 ok0 f n cap af1 r r1 Hs HF ok1. rewrite (HF ok1). exact (pvs_jfk_comma _ _ _ _ _ _ _ _ _ Hs). Qed.

(* the call's whole free list at the separator's stop (not ','): the completed slots' list, then the arrays *)
Lemma pvs_frees_stop : forall d o x0 ok0 f n cap af1 r,
  match skip r with [] => True | c :: _ => c <> 44 end ->
  (forall ok1, prhPi_frees d o x0 (ok0 ++ ok1) = pv_jfk f (Nat.succ d) o n cap af1 r ok1) ->
  prhPi_frees d o x0 ok0 = af1 ++ PresetReqAt.arrz o cap.
Proof.
intros d o x0 ok0 f n cap af1 r Hc HF. pose proof (HF []) as H0. rewrite app_nil_r in H0. rewrite H0.
exact (pvs_jfk_stop _ _ _ _ _ _ _ _ Hc).
Qed.

(* the depth of a closed container: n' = S nn with every member at most nn deep (PItems_forder.pi_forder_mk, whose
   container is mk o (rev acc), at acc := rev Lm) *)
Lemma pvs_depth_mk : forall (o : bool) (Lm : list (list Z * jv)) n', (depth (mk o Lm) <= n')%nat ->
  exists nn, n' = S nn /\ Forall (fun mb => (depth (snd mb) <= nn)%nat) Lm.
Proof.
intros o Lm n' H. rewrite <- (rev_involutive Lm) in H.
destruct (PItems_forder.pi_forder_mk o (rev Lm) n' H) as (nn & E & HF). exists nn. split; [exact E|].
rewrite <- (rev_involutive Lm). apply Forall_rev. exact HF.
Qed.

(* the cursor one byte further *)
Lemma pvs_rest_next : forall tb text pc c rest, text <= pc -> rest_atR tb text pc = c :: rest ->
  rest_atR tb text (pc + 1) = rest.
Proof.
intros tb text pc c rest Hle H. unfold rest_atR in *.
replace (Z.to_nat (pc + 1 - text)) with (S (Z.to_nat (pc - text))) by lia.
revert H. generalize (Z.to_nat (pc - text)) as k. revert c rest.
induction tb as [|x tb IH]; intros c rest k H; destruct k as [|k]; cbn [skipn] in *; try discriminate.
- injection H as _ <-. reflexivity.
- exact (IH c rest k H).
Qed.

(* the byte the cursor reads *)
Lemma pvs_nth_skipn : forall (l : list Z) kk b rest, skipn kk l = b :: rest -> nth kk l 0 = b.
Proof.
induction l as [|x l IH]; intros [|kk] b rest H; cbn in H; try discriminate.
- injection H as -> ->. reflexivity.
- cbn. exact (IH kk b rest H).
Qed.

(* ---- the ledger facts are invariant under a permutation of the block list D ---- *)
Lemma pvs_ledger_perm : forall Lam peak cnt fail ran most ok gt tr D D' Lam' peak' cnt' fail' ran',
  Permutation D D' -> rd_ledger_move Lam peak cnt fail ran most ok gt tr D Lam' peak' cnt' fail' ran' ->
  rd_ledger_move Lam peak cnt fail ran most ok gt tr D' Lam' peak' cnt' fail' ran'.
Proof.
intros Lam peak cnt fail ran most ok gt tr D D' Lam' peak' cnt' fail' ran' HP (O & C & F & P & Sz & N & K).
unfold rd_ledger_move.
split; [exact O|]. split; [exact C|]. split; [exact F|].
split; [eapply Permutation_trans; [exact P | apply Permutation_app_tail; exact HP]|].
split; [eapply Permutation_trans; [apply Permutation_map; apply Permutation_sym; exact HP | exact Sz]|].
split; [rewrite <- (Permutation_length HP); exact N | exact K].
Qed.

Section cpm. Context {cp : CfParams}.
Lemma pvs_blocks_perm : forall B ly S ly' S' D D' tr x d, Permutation D D' ->
  rd_blocks_move B ly S ly' S' D tr x d -> rd_blocks_move B ly S ly' S' D' tr x d.
Proof.
intros B ly S ly' S' D D' tr x d HP (A & P & F & K). unfold rd_blocks_move.
split; [intros a k Hin; apply A; eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hin]|].
split; [eapply Permutation_trans; [exact P | apply Permutation_app_tail; unfold prhReader_ab;
  apply Permutation_map; exact HP]|].
split; [exact F | exact K].
Qed.
End cpm.

(* the ledger's NoDup carries over to a permutation of the prefix's blocks *)
Lemma pvs_nodup_D0 : forall (Lam Lamc D0 X : list (Z * Z)), Permutation Lamc (D0 ++ Lam) -> NoDup (map fst Lamc) ->
  Permutation D0 X -> NoDup X.
Proof.
intros Lam Lamc D0 X HP HN HX.
try (apply NoDup_ListNoDup in HN).
assert (H1 : List.NoDup Lamc) by exact (List.NoDup_map_inv fst Lamc HN).
assert (H2 : List.NoDup (D0 ++ Lam)) by exact (Permutation_NoDup HP H1).
assert (H3 : NoDup D0) by (apply (pis_nodup_l _ D0 Lam); apply NoDup_ListNoDup; exact H2).
apply NoDup_ListNoDup. eapply Permutation_NoDup; [exact HX|]. apply NoDup_ListNoDup. exact H3.
Qed.

(* ---- the half-built container closed: PItems_value_model.v's pvm_cont_open, then PItems_shape.v's pis_close ---- *)
Section bridge. Context {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).

(* the closed container: the open one at n members IS the node of mk o acc *)
Lemma pvs_cont_node : forall m lblk (o : bool) v kids keys n cap acc Di,
  pi_cont (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) m lblk o v kids keys n cap acc Di ->
  NoDup (pi_sblk o kids keys cap ++ Di) -> pj_apartR (pi_sblk o kids keys cap) v ->
  pj_nodeR SEGS m lblk v (mk o acc) (pi_sblk o kids keys cap ++ Di).
Proof.
intros m lblk o v kids keys n cap acc Di HC HN HA.
pose proof (pvm_cont_open m lblk o v kids keys n cap acc Di HC HA HN) as HO.
pose proof HC as (_ & Hn & _).
rewrite pvm_sblk_slots. rewrite <- (rev_involutive acc).
apply (pis_close SEGS m lblk v o 0 kids keys (Z.of_nat cap) (rev acc) Di).
rewrite rev_involutive, length_rev, <- Hn. exact HO.
Qed.

(* ---- The batch kit: the closed (or refused) container's free order and capacities ---- *)
Lemma pvs_kids_impl : forall (A : Type) (P Q : Z -> A -> Prop) a (l : list A), (forall a x, P a x -> Q a x) ->
  pj_kidsR P a l -> pj_kidsR Q a l.
Proof.
intros A P Q a l HPQ. revert a. induction l as [|x l IH]; intros a H; cbn [pj_kidsR] in *; [exact I|].
destruct H as [H1 H2]. split; [exact (HPQ a x H1) | exact (IH (a + 56) H2)].
Qed.

Lemma pvs_kids_map : forall (A B0 : Type) (P : Z -> B0 -> Prop) (g : A -> B0) a (l : list A),
  pj_kidsR (fun a x => P a (g x)) a l -> pj_kidsR P a (map g l).
Proof.
intros A B0 P g a l. revert a. induction l as [|x l IH]; intros a H; cbn [pj_kidsR map] in *; [exact I|].
destruct H as [H1 H2]. split; [exact H1 | exact (IH (a + 56) H2)].
Qed.

(* the container's capacities (CAP): its header's cap word is ncap of its count, its kids' from pi_ncaps (whose
   predicate reads snd mb where pj_ncapR's object arm reads `let (_, u) := mb`) *)
Lemma pvs_ncap_mk : forall m (o : bool) v ty num str kids keys nz (cap : nat) (Lm : list (list Z * jv)),
  pj_hdrR SEGS m v ty num str kids keys nz (Z.of_nat cap) -> cap = PresetReqAt.ncap (length Lm) ->
  pi_ncaps (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) m kids Lm -> pj_ncapR SEGS m v (mk o Lm).
Proof.
intros m o v ty num str kids keys nz cap Lm (_ & _ & _ & _ & Hk & _ & _ & Hc) Ecap HN. unfold pi_ncaps in HN.
destruct o; unfold mk; cbn [pj_ncapR].
- split; [rewrite <- Ecap; exact Hc|]. exists kids. split; [exact Hk|].
  apply (pvs_kids_impl _ (fun a (mb : list Z * jv) => pj_ncapR SEGS m a (snd mb)) _ kids Lm); [|exact HN].
  intros a [nm u] H. exact H.
- split; [rewrite length_map, <- Ecap; exact Hc|]. exists kids. split; [exact Hk|].
  apply pvs_kids_map. exact HN.
Qed.

(* the open container closed with the arrays (PItems_forder.pis_fo_open at pi_cont's pis_open): its order list is
   the completed slots' Facc, then kids, then keys *)
Lemma pvs_fo_close : forall m lblk (o : bool) v kids keys n cap (Lm : list (list Z * jv)) Di nn Facc,
  pi_cont (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) m lblk o v kids keys n cap Lm Di ->
  pj_apartR (pi_sblk o kids keys cap) v -> NoDup (pi_sblk o kids keys cap ++ Di) ->
  PRH_PjOrder.pf_oitemsR SEGS m lblk (PRH_PjOrder.pj_foR SEGS m lblk nn) o kids keys n Di Facc ->
  PRH_PjOrder.pj_foR SEGS m lblk (S nn) v (pi_sblk o kids keys cap ++ Di) (Facc ++ pi_sblk o kids keys cap).
Proof.
intros m lblk o v kids keys n cap Lm Di nn Facc HC HA HN HPF.
pose proof (pvm_cont_open m lblk o v kids keys n cap Lm Di HC HA HN) as HO.
pose proof HC as (_ & En & _).
assert (EL : length (map snd Lm) = n) by (rewrite length_map; symmetry; exact En).
rewrite <- EL in HO, HPF. rewrite pvm_sblk_slots.
exact (PItems_forder.pis_fo_open SEGS m lblk v o 0 kids keys (Z.of_nat cap) (map snd Lm) (map fst Lm) Di nn Facc HO HPF).
Qed.
End bridge.

(* grow's granted trace on a full container (n = cap): the kids realloc, then for an object the keys realloc *)
Lemma pvs_gtrace_full : forall (o : bool) (cap : nat),
  PRH_Charge.prhPg_gtrace o (Z.of_nat cap) (Z.of_nat cap) =
  EGrow (56 * cap) (56 * (if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat)) ::
  (if o then [EGrow (8 * cap) (8 * (if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat))] else []).
Proof.
intros o cap. unfold PRH_Charge.prhPg_gtrace. rewrite Nat2Z.id. unfold PjGrammar.grow.
rewrite Nat.ltb_irrefl. cbv zeta. unfold jbind, jrealloc, jret, take. destruct o; reflexivity.
Qed.

(* grow's room on a full container: the largest request and the per-event live room of tgrow_specX's premise (the batch kit's tip:
   PRH_Base.prh_live_evs over grow's own events, which are rd_hevs of its granted trace) follow from the room of grow's
   own granted trace *)
Section groom. Context {cp : CfParams} {RL : PrhRoomLive}.
Lemma pvs_grow_room : forall Sc (o : bool) (cap : nat),
  rd_room Sc (PRH_Charge.prhPg_gtrace o (Z.of_nat cap) (Z.of_nat cap)) ->
  56 * cap2R (Z.of_nat cap) + cf_head < cf_malloc_max /\
  prh_live_evs Sc (PresetReqAt.rd_hevs (PRH_Charge.prhPg_gtrace o (Z.of_nat cap) (Z.of_nat cap))).
Proof.
intros Sc o cap (R1 & R2 & R3). pose proof (@cf_head_nonneg cp) as CH.
split; [|exact R3].
rewrite pvs_gtrace_full in R2. unfold cap2R. unfold PRH_Charge.prh_maxreq in R2.
destruct (Nat.eqb_spec cap 0) as [->|Hc].
- change (Z.of_nat 0) with 0 in *. cbn [Z.eqb] in *.
  destruct o; cbn in R2 |- *; lia.
- assert (E : (Z.of_nat cap =? 0) = false) by (apply Z.eqb_neq; lia). rewrite E.
  try rewrite (proj2 (Nat.eqb_neq cap 0) Hc) in R2.
  destruct o; cbn [map fold_right PjGrammar.esize hpeakR held_ev PjGrammar.calls PjGrammar.is_call Z.eqb Pos.eqb]
    in R2 |- *;
  rewrite ?Nat2Z.inj_mul in R2; lia.
Qed.
End groom.

(* ---- alloc.c's statics are not read-only at image B (lib/B/Prog/S1ImgB.v pst_not_ro_B, with lib/A/Prog/S1ImgA.v's
   image-free checkers pst_allb / in_ro_b, copied over SEGS: requiring S1ImgB loads image A's PAImg instance, which
   then wins the implicit instance search of this file's statements) ---- *)
Section ro. Context {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).
Definition pvs_pst_allb (f : Z -> bool) (P : list (Z * Z)) : bool :=
  forallb (fun r => zallb f (fst r) (Z.to_nat (snd r))) P.
Lemma pvs_pst_allb_sound : forall f P a, pvs_pst_allb f P = true -> Exists (in_zr a) P -> f a = true.
Proof.
intros f P a H Ha. apply Exists_exists in Ha as (r & Hr & Ha). unfold pvs_pst_allb in H.
rewrite forallb_forall in H. specialize (H r Hr). unfold in_zr in Ha.
apply (zallb_sound f (Z.to_nat (snd r)) (fst r) a H). rewrite Z2Nat.id by lia. lia.
Qed.
Definition pvs_in_ro_b (a : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
    SEGS || ((pa_relro_lo (PAImg := PI_prog_B) <=? a) && (a <? pa_relro_hi (PAImg := PI_prog_B))).
Lemma pvs_in_ro_b_complete : forall a,
  in_roP SEGS (pa_relro_lo (PAImg := PI_prog_B)) (pa_relro_hi (PAImg := PI_prog_B)) a -> pvs_in_ro_b a = true.
Proof.
intros a [(s & Hs & Hw & Hr) | Hr]; unfold pvs_in_ro_b; apply orb_true_intro; [left | right].
- apply existsb_exists. exists s. split; [exact Hs|]. rewrite Hw. cbn [negb andb].
  apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma pvs_pst_not_ro : forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
  ~ in_roP SEGS (pa_relro_lo (PAImg := PI_prog_B)) (pa_relro_hi (PAImg := PI_prog_B)) a.
Proof.
intros a Ha Hro.
assert (Hb : negb (pvs_in_ro_b a) = true)
  by (refine (pvs_pst_allb_sound (fun x => negb (pvs_in_ro_b x)) _ a _ Ha); vm_compute; reflexivity).
rewrite (pvs_in_ro_b_complete a Hro) in Hb. discriminate.
Qed.
End ro.

(* ================================================================================================== *)
(* 3. THE SYMBOLIC STATE AT PV_O_SEP: s1 = q (atom 9), s10 = SHADOW_OFF (atom 26), s0 / s4 / s7 / s9 / s11 pinned
   to q + 16, q + 8 and the three shadow addresses, s2 the literal (if o then 1 else 0) the closer test reads; the
   cursor's p field (atom 32) and end word (atom 33) as one region of q whose p field [0, 8) is WRITABLE when wr
   (the comma arm stores p + 1 there, a cell of FP = rd_fp q v in the caller's window; every other arm is seated
   read-only, so its run leaves the reader unchanged), and, when the cursor is on a byte,
   that byte (atom 34) as its own read-only region. PItems_head.v's hd_smem with the store window and s4 / s7. *)
(* ================================================================================================== *)
Definition pvs_sregs (o : bool) : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 8%bv (SOff 9 16)) 20%bv (SOff 9 8))
    23%bv (pi_shx (SOff 9 8))) 25%bv (pi_shx (SOff 9 16))) 27%bv (pi_shx (SOff 9 0)))
    18%bv (SLit (if o then 1 else 0)).
Definition pvs_smem (bt wr : bool) : smem :=
  (if bt then [YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))]] else []) ++
  [ YP09.mkRegion (Some 9%nat) 0 16 0 (if wr then 8 else 0)
      [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))] ].
Definition pvs_facts : list (nat * afact) :=
 [ (9%nat, mkAF 4096 (2 ^ 47 - 24) 3); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (32%nat, mkAF 4096 (2 ^ 47 - 2) 0); (33%nat, mkAF 4096 (2 ^ 47 - 1) 0); (34%nat, mkAF 0 255 0) ].
Definition ss_pvs (o bt wr : bool) (pc : Z) : sstate :=
  mkSS pc (pvs_sregs o) (pvs_smem bt wr) None (mkFacts pvs_facts [] []).
Definition pvs_SH (bt : bool) : list shent := (if bt then [mkSHE 32 0 1] else []) ++ [mkSHE 9 0 24].
Definition pvs_Bx : sv := SOff 26 0.

Section st. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation VAL := (@pa_val rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

Lemma pvs_st_ok : forall (W : world SEGS) memc (regs : bvmap 5 word) q p1 ed c (o bt wr : bool) off,
  getr regs 9 = w64 q -> getr regs 8 = w64 (q + 16) -> getr regs 20 = w64 (q + 8) -> getr regs 26 = w64 SHADOW_OFF ->
  getr regs 27 = w64 (pi_sh q) -> getr regs 25 = w64 (pi_sh (q + 16)) -> getr regs 23 = w64 (pi_sh (q + 8)) ->
  getr regs 18 = w64 (if o then 1 else 0) ->
  4096 <= q <= 2 ^ 47 - 24 -> q mod 8 = 0 -> 4096 <= p1 <= 2 ^ 47 - 2 -> 4096 <= ed <= 2 ^ 47 - 1 ->
  0 <= c < 256 -> (bt = true -> q + 16 <= p1 \/ p1 + 1 <= q) ->
  val_mem SEGS (rdW W memc) q 8 p1 -> val_mem SEGS (rdW W memc) (q + 8) 8 ed ->
  (wr = true -> forall x, q <= x < q + 8 -> writable_at SEGS (rdW W memc) x) ->
  (bt = true -> val_mem SEGS (rdW W memc) p1 1 c) ->
  st_ok_pi (fx := fx) SEGS VAL (Eimg (rc := rc) (L := B_prog_listing) (PI := PI_prog_B)
                      (Ereg regs [Z_to_bv 64 p1; Z_to_bv 64 ed; Z_to_bv 64 c])) (ss_pvs o bt wr off)
    (restrict (w_H W) (mkst (fx := fx) regs (Z_to_bv 64 (VAL A_TEXT + off)) memc (seg_rom SEGS))).
Proof.
intros W memc regs q p1 ed c o bt wr off H9 H8 H20 H26 H27 H25 H23 H18 Hq Hq8 Hp1 Hed Hc Hdj Vp Ve Hwr Vc.
set (E := Eimg (rc := rc) (L := B_prog_listing) (PI := PI_prog_B)
           (Ereg regs [Z_to_bv 64 p1; Z_to_bv 64 ed; Z_to_bv 64 c])).
assert (E9 : ew E 9 = Z_to_bv 64 q) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E32 : ew E 32 = Z_to_bv 64 p1) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 ed) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 c) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (U9 : bv_unsigned (ew E 9) = q) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF) by (rewrite E26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = p1) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = ed) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = c) by (rewrite E34; apply unsigned_lit_small; lia).
assert (D9 : forall x, 0 <= q + x < 2 ^ 64 -> sv_denot E (SOff 9 x) = Z_to_bv 64 (q + x)).
{ intros x Hx. rewrite denot_lit_U, U_SOff, U9, zcanon_id by (unfold M64; lia). reflexivity. }
rewrite (restrict_mkst_fx (fx := fx)). unfold ss_pvs. apply (pa_entry_st_ok_full (fx := fx) (L := B_prog_listing) (PI := PI_prog_B)).
- unfold pvs_sregs.
  apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
    [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg| |]| |]| |]| |]| |]| |];
  try (intros X; discriminate X).
  + rewrite H8, D9 by lia. reflexivity.
  + rewrite H20, D9 by lia. reflexivity.
  + rewrite H23, (pi_denot_shx E (SOff 9 8) SHADOW_OFF (q + 8) (D9 8 ltac:(lia)) E26) by (unfold SHADOW_OFF; lia).
    reflexivity.
  + rewrite H25, (pi_denot_shx E (SOff 9 16) SHADOW_OFF (q + 16) (D9 16 ltac:(lia)) E26) by (unfold SHADOW_OFF; lia).
    reflexivity.
  + rewrite H27, (pi_denot_shx E (SOff 9 0) SHADOW_OFF q ltac:(rewrite D9 by lia; f_equal; lia) E26)
      by (unfold SHADOW_OFF; lia).
    reflexivity.
  + rewrite H18. cbn [sv_denot]. unfold w64. destruct o; reflexivity.
- destruct bt; destruct wr; vm_compute; reflexivity.
- assert (RQ : region_ok SEGS E (rdW W memc) (YP09.mkRegion (Some 9%nat) 0 16 0 (if wr then 8 else 0)
      [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))])).
  { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [destruct wr; lia|].
    split; [intros oo Ho; destruct wr; [apply Hwr; [reflexivity | lia] | lia]|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ q 0 8 (SOff 32 0) p1);
      [rewrite denot_lit_U, U_SOff, U32, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside
      | rewrite Z.add_0_r; exact Vp].
    * apply (chunk_ok_val SEGS E _ q 8 8 (SOff 33 0) ed);
      [rewrite denot_lit_U, U_SOff, U33, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside | exact Ve]. }
  unfold pvs_smem. destruct bt; cbn [app]; repeat apply Forall_cons; try apply Forall_nil; try exact RQ.
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U32. split; [lia|]. split; [lia|]. split; [intros oo Ho; lia|]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ p1 0 1 (SOff 34 0) c);
  [rewrite denot_lit_U, U_SOff, U34, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity | cbn; lia | zside
  | rewrite Z.add_0_r; exact (Vc eq_refl)].
- apply pairwise_disjoint_of_extents. unfold pvs_smem. destruct bt;
  [pose proof (Hdj eq_refl) as Hdj'|]; cbn [app map]; unfold extent_of_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U9, ?U32;
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok pvs_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U26, U32, U33, U34. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SHADOW_OFF. repeat split; lia.
Qed.

(* a run whose regions write nothing leaves the reader pointwise unchanged (PItems_head.v's hd_meq_of) *)
Lemma pvs_meq_of : forall E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall r0, In r0 rs -> YP09.r_whi r0 <= YP09.r_wlo r0) ->
  mrestrict H m' = mrestrict H m.
Proof.
intros E rs H m m' HFr Hro. apply functional_extensionality. intros x. apply HFr.
intros (r0 & Hin & Hr). pose proof (Hro r0 Hin). lia.
Qed.
End st.

(* ================================================================================================== *)
(* 4. THE WALK of PV_O_SEP (0x87dbc .. 0x87e1c) and the closer test (0x87f38 .. 0x87f54).                 *)
(* ================================================================================================== *)
(* the return site of the grow call at PI_O_GROW2: the next instruction (a LENGTH offset inside the body) *)
Definition PVS_O_GROWR : Z := PI_O_GROW2 + 4.

(* split a right-nested conjunction into its conjuncts, syntactically (no definition is unfolded): pi_ent's and rd_pre's
   conjuncts after their fixed prefixes are read BY TYPE, robust to a conjunct the kit owner adds there (PItems_value_aftv.v's
   av_split, the same text under this file's name) *)
Ltac pvs_split H :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh "TLa" in let H2 := fresh "TLb" in destruct H as [H1 H2]; pvs_split H2
  | _ => idtac
  end.

Section main. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instance prh_img_B.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation VAL := (@pa_val rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation PIAT := (@PI_AT rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
(* the walk's world relation (the re-hiding move) *)
#[local] Notation WR := (wle' SEGS YGcfRehidePost.RZ_cf).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable d : nat.
Variable CTX0 : list (list Z).
(* the cursor set of the batch kit's texts (the specs' parameter after CTX0) *)
Variable CW : list (list Z).
(* the engine's laws at the instance's head length cf_head (as PItems_body.v / PItems_body_loop.v state them):
   PItems_body_loop.v's pil_grow_step, applied at the grow call, takes them there *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the head length the instance's event lists use (PRH_FnReader.v prhPg_evs: cf_head) is the model's
   (PresetReqAt.rd_hevs: HEAD), so grow's live-count premises over prhPg_evs .. [] are the counts over rd_hevs of its
   granted trace (PRH_FnReader.v prhPg_evs_model), and PItems_body_loop.v's step reads its post the same way. OWNER: the
   instance (reflexivity at the preset's CfParams); the same text as PItems_body_loop.v's PIL_HEAD *)
Hypothesis PIL_HEAD : cf_head = PresetReqAt.HEAD.

Lemma pvs_stk_nonneg : 0 <= STK_parse_items (PI := prh_img_B) d.
Proof.
unfold STK_parse_items. pose proof (Nat2Z.is_nonneg (PjGrammar.MAXD - d)).
assert (EL : LEAF_pv_pi (PI := prh_img_B) = 16560) by (vm_compute; reflexivity). rewrite EL.
cbn [PRH_Base.pi_frame prh_img_B]. lia.
Qed.

(* the text's post reads memory only through the reader (PItems_head.v's cl_post_stable); read through tpiP_R_of, built
   through tpiP_Q_of_R: only the ledger and the arm read memory *)
Lemma pvs_post_stable : forall ly0 S0 dd (o : bool) tb text len p q v Lam peak cnt fail ran most own kr,
  pi_Qstable (rc := rc) (L := B_prog_listing) (PA := PI_prog_B)
    (pi_post (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
       B ly0 S0 dd o tb text len p q v Lam peak cnt fail ran most own kr).
Proof.
intros ly0 S0 dd o tb text len p q v Lam peak cnt fail ran most own kr ly S Hp W regs m m' md md' Heq HQ.
assert (E : rdW W m' = rdW W m) by (apply functional_extensionality; exact Heq).
unfold pi_post in HQ |- *.
eapply tpiP_R_of in HQ.
destruct HQ as (ok & res & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & HR).
pose proof (tpiP_arm HR) as Hm.
eapply tpiP_Q_of_R.
refine {| tpiP_run := tpiP_run HR; tpiP_ledger := cl_ledger_rdeq B _ _ _ _ _ _ _ _ _ _ _ _ _ E (tpiP_ledger HR);
  tpiP_room := tpiP_room HR; tpiP_hull := tpiP_hull HR; tpiP_live := tpiP_live HR; tpiP_pos := tpiP_pos HR;
  tpiP_outcome := tpiP_outcome HR; tpiP_injected := tpiP_injected HR; tpiP_ledger_move := tpiP_ledger_move HR;
  tpiP_blocks_move := tpiP_blocks_move HR; tpiP_bytes := tpiP_bytes HR; tpiP_lsum := tpiP_lsum HR;
  tpiP_arm := _ |}.
unfold tpiP_ASome, tpiP_ANone in Hm |- *. rewrite E. exact Hm.
Qed.

(* ---- THE REFUSAL POST: the separator is neither ',' nor the closer (or there is none); nothing was written, so
   the batch kit's None arm holds of the prefix's run, ledger and blocks, with the container's n + 1 members freeable. The batch kit: every
   call so far was granted (pi_grant) and the refusal is the grammar's, so the all-granted run IS this run
   (PItems_ledk1.pik1_run_granted): the OUTCOME, the ledger over prhPi_gtrace = tr0 (pik1_move_regt), ran kept
   (pik1_move_ran); the partial tree's free order at every n' >= MAXD - d is the completed slots' (pi_forder at
   n' = S nn, PItems_forder.pi_forder_at) then the arrays (pvs_fo_close), against pv_jfk's stop (pvs_frees_stop) ---- *)
Lemma pvs_refuse_post : forall (fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem ch CTX (regs0 : bvmap 5 word) e q v
  (o : bool) text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc (Wc : world SEGS) memc
  (f n cap : nat) acc kids keys Di nm t r pc ok0 tr0 D0 Lamc peakc cntc failc ranc af1 memf mdf
  (regs' : bvmap 5 word),
  pi_ent (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o CTX0 CW ->
  PItems_posb.pi_posb S Sc tr0 ->
  PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) tr0 ->
  pi_cont (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) (rdW Wc memc) (prh_lin Lamc) o v kids keys (Nat.succ n) cap
    (acc ++ [(nm, t)]) Di ->
  Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - Nat.succ d)%nat) (acc ++ [(nm, t)]) ->
  pj_apartR (pi_sblk o kids keys cap) v ->
  Permutation D0 (pi_sblk o kids keys cap ++ Di) ->
  pv_run_after d o (rest_atR tb text p) ok0 tr0 f n cap acc nm (Some (t, r)) ->
  pi_led Lam peak cnt fail ran most ok0 tr0 D0 Lamc peakc cntc failc ranc ->
  rd_blocks_move (cp := cp) B ly S lyc Sc D0 tr0 (rest_atR tb text p) d ->
  blocks_bytes Sc <= blocks_bytes S + PRH_Charge.prh_held tr0 ->
  Ledger.lsum D0 = PjGrammar.held tr0 ->
  room_live_cf (PrhRoomLive := RL) Sc ->
  pi_cur (rc := rc) (cp := cp) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B)
    B regs0 e q v text len tb d lyc Sc Hpc Wc memc pc Lamc peakc cntc failc ranc most own ->
  match skip r with [] => True | c :: _ => c <> 44 /\ c <> closer o end ->
  rdW Wc memf = rdW Wc memc ->
  getr regs' 10 = w64 (-1) ->
  (* The batch kit's invariants of pv_sep_pre: the granted prefix, the completed slots' free order, the model *)
  pi_grant ok0 tr0 ->
  pi_forder (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) (rdW Wc memc) (prh_lin Lamc) o kids keys (Nat.succ n)
    Di (acc ++ [(nm, t)]) af1 ->
  (forall ok1, prhPi_frees d o (rest_atR tb text p) (ok0 ++ ok1) = pv_jfk f (Nat.succ d) o n cap af1 r ok1) ->
  pi_post (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    B ly S d o tb text len p q v Lam peak cnt fail ran most own kr lyc Sc Hpc Wc regs' memf mdf.
Proof.
intros fx0 ly S Hp W mem ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc
  f n cap acc kids keys Di nm t r pc ok0 tr0 D0 Lamc peakc cntc failc ranc af1 memf mdf regs'
  Hent HPOSB HLIVE HCONT HDEP HAP HPERM HRUN HLED HBM HBB HLS HROOM HCUR Hsep MEQ H10 HGR HFORD HFLE.
pose proof HCUR as (HIN & HRA & HSRC & HHOME & HPLAT & HRAV & HLG & HCNT).
pose proof HIN as (Vp & Ve & Vdp & Hrw & Hq8 & Ht0 & Htl & Hple & Hlen & HG & Hdqt & Hd032).
pose proof HLED as (_ & _ & _ & HPL & _).
pose proof HLG as HNDL. apply prh_ledger_nodup in HNDL.
unfold pi_grant in HGR.
assert (HdM : (d < PjGrammar.MAXD)%nat) by (unfold PjGrammar.MAXD; lia).
assert (HND0 : NoDup D0) by exact (pvs_nodup_D0 Lam Lamc D0 D0 HPL HNDL (Permutation_refl D0)).
assert (HNS : NoDup (pi_sblk o kids keys cap ++ Di)) by exact (pvs_nodup_D0 Lam Lamc D0 _ HPL HNDL HPERM).
(* THE GRANTED RUN: the prefix ate one grant per call and the separator is the grammar's refusal *)
assert (HR0 : jr_items prh_jr_strtod d o (rest_atR tb text p) ok0 = (None, tr0, [])).
{ pose proof (pvs_run_refused d o _ ok0 tr0 f n cap acc nm t r HRUN Hsep []) as H0. rewrite app_nil_r in H0. exact H0. }
assert (HGRUN : fst (jr_items prh_jr_strtod d o (rest_atR tb text p) []) = (None, tr0)).
{ pose proof HR0 as HR1. rewrite HGR in HR1.
  exact (PItems_ledk1.pik1_run_granted _ _ _ _ _ _ (PjGrammar.agrees_jr_items _ _ _ _) HR1). }
assert (HGT : PRH_Charge.prhPi_gtrace d o (rest_atR tb text p) = tr0)
  by (unfold PRH_Charge.prhPi_gtrace; rewrite HGRUN; reflexivity).
assert (HGNT : prh_granted ok0 cnt fail (PjGrammar.calls tr0)) by (rewrite HGR; apply PItems_ledk1.pik1_grant_granted).
assert (HRAN : ranc = ran) by exact (PItems_ledk1.pik1_move_ran _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGNT HLED).
(* the text's post, built through its named record. The hull use over the whole call's all-granted list, which is tr0 here
   (PItems_posb.pi_posb_hull); the OUTCOME: ran' = ran, the all-granted run's result is this one, and the position
   advances by its events; the injected-reading conjunct: the prefix granted every call (pi_grant_granted) *)
assert (HR0' : jr_items ReaderRes.jr_strtod d o (rest_atR tb text p) ok0 = (None, tr0, [])) by exact HR0.
assert (HHU : PresetHullBudget.hull_used S Sc (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))))
  by (rewrite HGT; exact (PItems_posb.pi_posb_hull S Sc tr0 HPOSB)).
assert (HOUT : forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))) ->
  PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) ->
  (fail < cnt \/ cnt + Z.of_nat (PjGrammar.calls (prhPi_gtrace d o (rest_atR tb text p))) <= fail) ->
  ranc = ran /\ fst (jr_items ReaderRes.jr_strtod d o (rest_atR tb text p) []) = (None, tr0) /\
  exists hist', PresetRoomPos.iface_room_pos sm x os
    (i + length (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p))))%nat H0 hist' Sc).
{ intros sm x os i H0 hist Hpos Hrun _ _. split; [exact HRAN|]. split; [exact HGRUN|].
  rewrite HGT in Hrun |- *. exact (PItems_posb.pi_posb_post S Sc tr0 HPOSB sm x os i H0 hist Hpos Hrun). }
unfold pi_post.
eapply tpiP_Q_of_R.
(* the live requests and the position: nothing ran since the block's state, so pi_live / pi_posb over tr0 are the
   post's permutation and position implication; the ledger over the WHOLE call's granted trace: a granted move is
   priced 0 at any granted trace *)
refine {| tpiP_run := HR0'; tpiP_ledger := cl_ledger_rdeq B _ _ _ _ _ _ _ _ _ _ _ _ _ MEQ HLG; tpiP_room := HROOM;
  tpiP_hull := HHU; tpiP_live := HLIVE; tpiP_pos := PItems_posb.pi_posb_post S Sc tr0 HPOSB; tpiP_outcome := HOUT;
  tpiP_injected := fun _ _ _ _ _ _ _ _ _ _ => pi_grant_granted ok0 tr0 cnt fail (PjGrammar.calls tr0) HGR;
  tpiP_ledger_move := PItems_ledk1.pik1_move_regt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGNT HLED;
  tpiP_blocks_move := HBM; tpiP_bytes := HBB; tpiP_lsum := HLS; tpiP_arm := _ |}.
split; [exact H10|]. rewrite MEQ.
(* THE PARTIAL TREE'S FREE ORDER (the None arm): at every n' >= MAXD - d *)
split.
{ intros Hhd n' Hn'.
  destruct (PItems_forder.pi_forder_at _ _ _ _ _ _ _ _ _ d HFORD Hhd HdM HDEP n' Hn') as (nn & Facc & -> & _ & HPF & HMF).
  exists (Facc ++ pi_sblk o kids keys cap). split.
  - apply (pvm_foR_perm _ _ _ _ _ _ _ _ (Permutation_sym HPERM)).
    exact (pvs_fo_close _ _ o v kids keys (Nat.succ n) cap (acc ++ [(nm, t)]) Di nn Facc HCONT HAP HNS HPF).
  - rewrite map_app, HMF, pvm_sblk_slots, (PItems_forder.pis_fo_slots_hb_nat _ o kids keys cap Hhd).
    symmetry. apply (pvs_frees_stop d o _ ok0 f n cap af1 r); [|exact HFLE].
    revert Hsep. destruct (skip r) as [|c r1]; [intros _; exact I | intros [Hc _]; exact Hc]. }
split.
- exists pc, (Z.of_nat d + 1). split; [lia|]. split; [lia|].
  split; [exact Vp|]. split; [exact Ve|]. split; [exact Vdp | exact Hrw].
- apply (pi_cont_fd _ Lamc o v kids keys (Nat.succ n) cap (acc ++ [(nm, t)]) Di D0 d HCONT HDEP HAP HPERM HND0).
  left. exact HdM.
Qed.

(* ---- THE CLOSER'S PRE: the separator is the closer; nothing was written, the container's n + 1 members are the
   finished tree, its node is pi_cont closed (pvs_cont_node), and the blocks list D is the slot blocks then the
   members' (a permutation of the prefix's D0). The batch kit: the ledger over prhPi_gtrace (pik1_move_regt on the granted
   prefix); the closed tree's free order at every nn >= its depth (nn = S nn', every member at most nn' deep:
   pvs_depth_mk; pi_forder at nn', then the arrays: pvs_fo_close) against pv_jfk's stop at the closer
   (pvs_frees_stop); its capacities from the header's cap = ncap (S n) and pi_ncaps (pvs_ncap_mk) ---- *)
Lemma pvs_close_data : forall (fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem md ch CTX (regs0 : bvmap 5 word)
  e q v (o : bool) text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc (Wc : world SEGS) memc
  (f n cap : nat) acc kids keys Di nm t r r1 pc ok0 tr0 D0 Lamc peakc cntc failc ranc af1 memf mdf k
  (regs regs' : bvmap 5 word),
  pi_fpok fx0 fx ->
  pi_ent (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o CTX0 CW ->
  YAkMemnorm.memnorm SEGS memf ->
  PItems_posb.pi_posb S Sc tr0 ->
  PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) tr0 ->
  pi_frame (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) regs0 regs W mem Wc memc e q v ->
  pi_cont (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) (rdW Wc memc) (prh_lin Lamc) o v kids keys (Nat.succ n) cap
    (acc ++ [(nm, t)]) Di ->
  pj_apartR (pi_sblk o kids keys cap) v ->
  Permutation D0 (pi_sblk o kids keys cap ++ Di) ->
  pv_run_after d o (rest_atR tb text p) ok0 tr0 f n cap acc nm (Some (t, r)) ->
  pi_led Lam peak cnt fail ran most ok0 tr0 D0 Lamc peakc cntc failc ranc ->
  rd_blocks_move (cp := cp) B ly S lyc Sc D0 tr0 (rest_atR tb text p) d ->
  blocks_bytes Sc <= blocks_bytes S + PRH_Charge.prh_held tr0 ->
  Ledger.lsum D0 = PjGrammar.held tr0 ->
  room_live_cf (PrhRoomLive := RL) Sc ->
  pi_cur (rc := rc) (cp := cp) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B)
    B regs0 e q v text len tb d lyc Sc Hpc Wc memc pc Lamc peakc cntc failc ranc most own ->
  rest_atR tb text pc = skip r -> skip r = closer o :: r1 ->
  rdW Wc memf = rdW Wc memc ->
  pi_regs regs' q v o -> getr regs' 10 = w64 pc ->
  spZ regs' = spZ regs -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  (* The batch kit's invariants of pv_sep_pre *)
  pi_grant ok0 tr0 -> cap = PresetReqAt.ncap (Nat.succ n) ->
  pi_ncaps (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) (rdW Wc memc) kids (acc ++ [(nm, t)]) ->
  pi_forder (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) (rdW Wc memc) (prh_lin Lamc) o kids keys (Nat.succ n)
    Di (acc ++ [(nm, t)]) af1 ->
  (forall ok1, prhPi_frees d o (rest_atR tb text p) (ok0 ++ ok1) = pv_jfk f (Nat.succ d) o n cap af1 r ok1) ->
  pi_close_pre (fx := fx) (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    B fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memf mdf
    k regs' CTX0 CW.
Proof.
intros fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc
  f n cap acc kids keys Di nm t r r1 pc ok0 tr0 D0 Lamc peakc cntc failc ranc af1 memf mdf k regs regs'
  Hfp Hent HMNf HPOSB HLIVE Hfr HCONT HAP HPERM HRUN HLED HBM HBB HLS HROOM HCUR HY Hcl MEQ Hrg' H10 Hsp H3 H4
  HGR Hcapn HNC HFORD HFLE.
pose proof HCUR as (HIN & HRA & HSRC & HHOME & HPLAT & HRAV & HLG & HCNT).
pose proof HLED as (_ & _ & _ & HPL & _).
pose proof HLG as HNDL. apply prh_ledger_nodup in HNDL.
pose proof Hent as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RDP & Eplt & _).
pose proof RDP as (_ & _ & _ & _ & IN0 & _).
pose proof IN0 as (_ & _ & _ & _ & _ & _ & _ & Hple0 & _).
pose proof HIN as (_ & _ & _ & _ & _ & Ht0 & _ & _ & Hlen & _).
assert (HN : NoDup (pi_sblk o kids keys cap ++ Di)) by exact (pvs_nodup_D0 Lam Lamc D0 _ HPL HNDL HPERM).
pose proof HCONT as (HHDR & En & _).
unfold pi_grant in HGR.
assert (HGNT : prh_granted ok0 cnt fail (PjGrammar.calls tr0)) by (rewrite HGR; apply PItems_ledk1.pik1_grant_granted).
assert (HJR : PjGrammar.jr_items prh_jr_strtod d o (rest_atR tb text p) ok0 =
              (Some (mk o (acc ++ [(nm, t)]), r1), tr0, [])).
{ rewrite <- (app_nil_r ok0). exact (pvs_run_closed d o _ ok0 tr0 f n cap acc nm t r r1 HRUN Hcl []). }
unfold pi_close_pre.
split; [exact Hfp|]. split; [exact Hent|]. split; [exact HMNf|].
split.
{ apply (pi_frame_kept (fun _ => True) regs0 regs regs' W mem Wc memc memf e q v Hfr Hsp H3 H4);
  [intros a _; rewrite MEQ; reflexivity | intros a _; exact I | intros a _ _; exact I]. }
split; [exact Hrg'|].
exists pc, ok0, tr0, [], (pi_sblk o kids keys cap ++ Di), Lamc, peakc, cntc, failc, ranc, (mk o (acc ++ [(nm, t)])), r1.
split; [exact H10|]. split; [exact HJR|]. split; [rewrite HY; exact Hcl|].
split; [exact (cl_ledger_rdeq B _ _ _ _ _ _ _ _ _ _ _ _ _ MEQ HLG)|].
split; [exact HROOM|].
split; [exact (pvs_ledger_perm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPERM
  (PItems_ledk1.pik1_move_regt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGNT HLED))|].
split; [exact (pvs_blocks_perm B _ _ _ _ _ _ _ _ _ HPERM HBM)|].
(* the travelling position and live requests over the whole trace tr0: the closer makes no call *)
split; [exact HPOSB|]. split; [exact HLIVE|].
split; [exact HBB|].
split; [rewrite <- (pil_lsum_perm _ _ HPERM); exact HLS|].
split; [rewrite MEQ; exact HIN|].
split; [rewrite MEQ; exact (pvs_cont_node _ _ o v kids keys (Nat.succ n) cap (acc ++ [(nm, t)]) Di HCONT HN HAP)|].
split; [exact HPLAT|].
split.
{ rewrite <- (pil_lsum_perm _ _ HPERM), HLS.
  destruct (rest_atR tb text p) as [|b y] eqn:Ex.
  - exfalso. unfold rest_atR in Ex. pose proof (length_skipn (Z.to_nat (p - text)) tb) as HL0.
    rewrite Ex in HL0. cbn [length] in HL0. lia.
  - try rewrite Ex in HJR. exact (G10_1_items prh_jr_strtod d o b y ok0 _ r1 tr0 [] HJR). }
split; [unfold aview; rewrite MEQ; exact HRA|].
(* THE CLOSED TREE'S FREE ORDER (the Some arm) at every nn >= its depth *)
split.
{ intros Hhd n' Hn'.
  destruct (pvs_depth_mk o (acc ++ [(nm, t)]) n' Hn') as (nn & -> & HA).
  destruct (HFORD Hhd nn HA) as (Facc & HPF & HMF).
  exists (Facc ++ pi_sblk o kids keys cap). split.
  - rewrite MEQ. exact (pvs_fo_close _ _ o v kids keys (Nat.succ n) cap (acc ++ [(nm, t)]) Di nn Facc HCONT HAP HN HPF).
  - rewrite map_app, HMF, pvm_sblk_slots, (PItems_forder.pis_fo_slots_hb_nat _ o kids keys cap Hhd).
    symmetry. apply (pvs_frees_stop d o _ ok0 f n cap af1 r); [|exact HFLE].
    rewrite Hcl. exact (proj1 (Z.eqb_neq _ _) (pvs_closer_44 o)). }
(* its capacities (CAP) *)
rewrite MEQ. apply (pvs_ncap_mk _ o v _ 0 0 kids keys _ cap (acc ++ [(nm, t)]) HHDR); [|exact HNC].
rewrite <- En. exact Hcapn.
Qed.

(* ---- THE GROW CALL'S SUPPORT (the comma arm): the store of p + 1 into q's p field, the call state, the call's
   footprint FP1 (v's kids / keys and cap fields, the slot blocks' allocator hulls), the old slot bytes, the room ---- *)
Definition pvs_FP1 (o : bool) (v kids keys : Z) (cap : nat) : list (Z * Z) :=
  [(v + 24, v + 40); (v + 48, v + 56)] ++
  ablocks_fp (prhReader_ab (kids_blkR kids (Z.of_nat cap) ++ keys_blkR (if o then 6 else 5) keys (Z.of_nat cap))).

(* the cells outside q's p field *)
Definition pvs_Fq (q : Z) (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ (q <= a < q + 8).

Lemma pvs_agr_trans : forall (F : Z -> Prop) (m0 m1 m2 : word -> option byte),
  pi_agr F m0 m1 -> pi_agr F m1 m2 -> pi_agr F m0 m2.
Proof. intros F m0 m1 m2 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

(* the half-built container across a write outside its footprint (PItems_value_model.v's pi_cont_frame) *)
Lemma pvs_cont_agr : forall (F : Z -> Prop) (m m' : word -> option byte) lblk (o : bool) v kids keys n cap acc Di,
  pi_cont (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) m lblk o v kids keys n cap acc Di ->
  pi_agr F m m' -> (forall x, v <= x < v + 56 -> F x) ->
  (forall x, (exists b, In b (pi_sblk o kids keys cap ++ Di) /\ pj_holdsR b x) -> F x) ->
  pi_cont (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) m' lblk o v kids keys n cap acc Di.
Proof.
intros F m m' lblk o v kids keys n cap acc Di HC HA Hv HB.
apply (pi_cont_frame m m' lblk o v kids keys n cap acc Di HC).
intros x Hx. assert (HF : F x) by (destruct Hx as [Hx | Hx]; [exact (Hv x Hx) | exact (HB x Hx)]).
split; [unfold mbyte; rewrite (HA x HF); reflexivity | exact (pi_wr_agr SEGS F m m' x HA HF)].
Qed.

(* the same write keeps pi_cont's read bytes (PItems_value_model.v pvm_cont_ufoot), the footprint the batch kit invariants'
   frames pvm_ncaps_frame / pvm_forder_frame ask *)
Lemma pvs_ufoot_agr : forall (F : Z -> Prop) (m m' : word -> option byte) (o : bool) v kids keys n cap Di,
  pi_agr F m m' -> (n <= cap)%nat -> (forall x, v <= x < v + 56 -> F x) ->
  (forall x, (exists b, In b (pi_sblk o kids keys cap ++ Di) /\ pj_holdsR b x) -> F x) ->
  pj_agreeR SEGS m m' (pvm_cont_ufoot o v kids keys n Di).
Proof.
intros F m m' o v kids keys n cap Di HA Hn Hv HB x Hx.
assert (HF : F x)
  by (destruct (pvm_ufoot_foot o v kids keys n cap Di x Hn Hx) as [Hf | Hf]; [exact (Hv x Hf) | exact (HB x Hf)]).
split; [unfold mbyte; rewrite (HA x HF); reflexivity | exact (pi_wr_agr SEGS F m m' x HA HF)].
Qed.

(* the cursor record after `sd p + 1, 0(s1)`: one byte further, everything else as before *)
Lemma pvs_cur_store : forall (regs0 : bvmap 5 word) e q v text len tb dd lyc Sc Hpc (Wc : world SEGS) memc memc' md
  pc Lamc peakc cntc failc ranc mostc ownc,
  ARx lyc Sc Hpc Wc memc md ->
  pi_cur (rc := rc) (cp := cp) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B)
    B regs0 e q v text len tb dd lyc Sc Hpc Wc memc pc Lamc peakc cntc failc ranc mostc ownc ->
  pi_agr (pvs_Fq q) (rdW Wc memc) (rdW Wc memc') ->
  val_mem SEGS (rdW Wc memc') q 8 (pc + 1) -> (forall x, q <= x < q + 8 -> writable_at SEGS (rdW Wc memc') x) ->
  pc < text + len -> YM05.alloc_ceiling <= q -> q + 24 <= 2 ^ 47 -> (q + 24 <= v \/ v + 56 <= q) ->
  4096 <= v -> v + 56 <= 2 ^ 47 ->
  cntc + 2 * Z.of_nat (length (rest_atR tb text (pc + 1))) + 2 < 2 ^ 64 - 1 ->
  pi_cur (rc := rc) (cp := cp) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B)
    B regs0 e q v text len tb dd lyc Sc Hpc Wc memc' (pc + 1) Lamc peakc cntc failc ranc mostc ownc.
Proof.
intros regs0 e q v text len tb dd lyc Sc Hpc Wc memc memc' md pc Lamc peakc cntc failc ranc mostc ownc
  HAR HCUR AGR VQ WRq Hlt Hq0 Hq47 Hqv Hv0 Hv1 HCNT'.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCUR as (HIN & HRA & HSRC & HHOME & HPLAT & HRAV & HLG & HCNT).
pose proof HIN as (Vp & Ve & Vdp & Hrw & Hq8 & Ht0 & Htl & Hple & Hlen & HG & Hdqt & Hd032).
pose proof HSRC as (HGt & Ht4 & Htc & Htam & Htra & Hhull).
rewrite Hlen in Htc.
assert (HSH : forall x, 0 <= x < 2 ^ 47 -> pvs_Fq q (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. unfold pvs_Fq, shadow_of_addr, SHADOW_OFF.
  assert (0 <= x / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia. }
unfold pi_cur. split.
- split; [exact VQ|].
  split; [apply (pi_val_agr SEGS (pvs_Fq q) _ _ _ _ _ AGR); [intros kk Hk; unfold pvs_Fq; lia | exact Ve]|].
  split; [apply (pi_val_agr SEGS (pvs_Fq q) _ _ _ _ _ AGR); [intros kk Hk; unfold pvs_Fq; lia | exact Vdp]|].
  split; [intros x Hx; destruct (Z_lt_dec x (q + 8)) as [Hx8|Hx8];
          [apply WRq; lia | apply (pi_wr_agr SEGS (pvs_Fq q) _ _ x AGR); [unfold pvs_Fq; lia | apply Hrw; lia]]|].
  split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Htl|]. split; [lia|]. split; [exact Hlen|].
  split; [apply (pi_garr8_agr SEGS (pvs_Fq q) _ _ _ _ AGR); [intros x Hx; unfold pvs_Fq; lia | exact HG]|].
  split; [exact Hdqt | exact Hd032].
- split; [apply (pi_ra_agr SEGS (pvs_Fq q) _ _ _ _ _ AGR); [intros x Hx; apply HSH; lia | exact HRA]|].
  split.
  { split; [apply (pi_garr8_agr SEGS (pvs_Fq q) _ _ _ _ AGR); [intros x Hx; unfold pvs_Fq; rewrite Hlen in Hx; lia | exact HGt]|].
    split; [exact Ht4|]. split; [rewrite Hlen; exact Htc|]. split; [exact Htam|].
    split; [apply (pi_ra_agr SEGS (pvs_Fq q) _ _ _ _ _ AGR); [intros x Hx; apply HSH; rewrite Hlen in Hx; lia | exact Htra]|].
    intros Hl0. pose proof (Hhull Hl0) as Hh. intros s Hs. specialize (Hh s Hs).
    rewrite (pi_aview_agr SEGS (pvs_Fq q) (w_H Wc) memc memc' s AGR); [exact Hh|].
    unfold pvs_Fq. unfold shadow_addr, SHADOW_OFF in Hs. rewrite Hlen in Hs.
    assert (0 <= text / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    assert (0 <= (text + len - 1) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    pose proof (Z.mul_div_le (2147450880 + (text + len - 1) / 8) 8 ltac:(lia)).
    assert (0 <= (2147450880 + text / 8) / 8) by (apply Z.div_pos; lia).
    lia. }
  split; [exact HHOME|]. split; [exact HPLAT|].
  split; [apply (pi_ra_agr SEGS (pvs_Fq q) _ _ _ _ _ AGR); [intros x Hx; apply HSH; lia | exact HRAV]|].
  split; [exact (cl_ledger_agr B ARx cf_head LAWS (pvs_Fq q) _ _ _ _ _ md memc' _ _ _ _ _ _ _ HAR
                  ltac:(intros a Ha; unfold pvs_Fq; lia) AGR HLG) | exact HCNT'].
Qed.

(* ---- where the node, the slot blocks and the text lie ---- *)
Lemma pvs_req_ge : forall k, 0 <= k -> k <= req_size k.
Proof. intros k Hk. unfold req_size. destruct (Z.eqb_spec k 0); lia. Qed.

Lemma pvs_req_id : forall k, 0 < k -> req_size k = k.
Proof. intros k Hk. unfold req_size. destruct (Z.eqb_spec k 0); lia. Qed.

(* the node is below the allocation ceiling: prhReader_at's window case is the one rd_pre excludes *)
Lemma pvs_v_low : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own (regs0 : bvmap 5 word) e v,
  ARx ly S Hp W mem md ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs0 e v 56 ->
  (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) ->
  v + 56 <= YM05.alloc_ceiling.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs0 e v HAR HLG HAT Hvw.
pose proof (@cf_head_nonneg cp) as CH0.
destruct HAT as [(a & k & Hin & H1 & H2) | [(b & m & Hin & _ & H1 & H2) | [(cid & pos & Hin & H1 & H2) | (H1 & H2)]]].
- destruct (cl_D_bounds B ARx cf_head LAWS ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HLG Hin). lia.
- destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & B2 & B3 & _).
  pose proof (pvs_req_ge m ltac:(lia)). lia.
- destruct (alx_sep _ _ _ LAWS ly S Hp W mem md HAR) as (_ & Hf).
  pose proof (proj1 (Forall_forall _ _) Hf (cid, pos) Hin) as [F1 F2]. cbn [fst snd] in F1, F2. lia.
- lia.
Qed.

(* the slot blocks are harness blocks of the ledger *)
Lemma pvs_sblk_in : forall m Lamc (o : bool) v kids keys n cap acc Di,
  pi_cont (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) m (prh_lin Lamc) o v kids keys n cap acc Di ->
  forall a k, In (a, k) (pi_sblk o kids keys cap) -> In (a, k) Lamc.
Proof.
intros m Lamc o v kids keys n cap acc Di (_ & _ & _ & _ & Hcs & _) a k Hin.
unfold pi_sblk, kids_blkR, keys_blkR in Hin.
destruct Hcs as [(E0 & _ & _) | (Hp & L0 & L1)].
- subst cap. cbn in Hin. destruct Hin.
- rewrite (proj2 (Z.eqb_neq (Z.of_nat cap) 0)) in Hin by lia. cbn [orb] in Hin.
  destruct o; cbn in Hin.
  + destruct Hin as [E | [E | []]]; injection E as <- <-; [exact L0 | exact (L1 eq_refl)].
  + destruct Hin as [E | []]. injection E as <- <-. exact L0.
Qed.

Lemma pvs_ab_in : forall (l : list (Z * Z)) b m, In (b, m) (prhReader_ab l) ->
  exists a k, b = a - cf_head /\ m = k + cf_head /\ In (a, k) l.
Proof.
intros l b m Hin. unfold prhReader_ab in Hin. apply in_map_iff in Hin. destruct Hin as ([a k] & E & Hin).
cbn [fst snd] in E. injection E as <- <-. exists a, k. auto.
Qed.


(* YG0f.pairwise over two distinct members, and over a permutation (symmetric relation) *)
Lemma pvs_pw_in2 : forall {X} (R : X -> X -> Prop) l x y, YG0f.pairwise R l -> In x l -> In y l -> x <> y ->
  R x y \/ R y x.
Proof.
intros X R l. induction l as [|z l IH]; intros x y HP Hx Hy Hne; cbn in *; [destruct Hx|].
destruct HP as [Hz HP]. rewrite Forall_forall in Hz.
destruct Hx as [<-|Hx], Hy as [<-|Hy].
- congruence.
- left. exact (Hz y Hy).
- right. exact (Hz x Hx).
- exact (IH x y HP Hx Hy Hne).
Qed.

Lemma pvs_pw_app_in : forall {X} (R : X -> X -> Prop) l1 l2 x y, YG0f.pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|z l1 IH]; intros l2 x y HP Hx Hy; cbn in *; [destruct Hx|].
destruct HP as [Hz HP]. rewrite Forall_forall in Hz.
destruct Hx as [<-|Hx]; [apply Hz; apply in_or_app; right; exact Hy | exact (IH l2 x y HP Hx Hy)].
Qed.

Lemma pvs_pw_perm : forall {X} (R : X -> X -> Prop), (forall x y, R x y -> R y x) ->
  forall l l', Permutation l l' -> YG0f.pairwise R l -> YG0f.pairwise R l'.
Proof.
intros X R Hs l l' HP. induction HP as [| x l l' HP IH | x y l | l l' l'' H1 IH1 H2 IH2]; intros H; cbn in *.
- exact I.
- destruct H as [Hx H]. split; [|exact (IH H)]. rewrite Forall_forall in Hx |- *. intros z Hz.
  apply Hx. exact (Permutation_in _ (Permutation_sym HP) Hz).
- destruct H as [Hy [Hx H]]. apply Forall_cons_iff in Hy. destruct Hy as [Hyx Hyl].
  split; [apply Forall_cons; [apply Hs; exact Hyx | exact Hx] | split; [exact Hyl | exact H]].
- exact (IH2 (IH1 H)).
Qed.

(* two live allocator blocks with different bases are disjoint *)
Lemma pvs_blk_disj : forall ly S Hp (W : world SEGS) mem md b1 n1 b2 n2,
  ARx ly S Hp W mem md -> In (b1, n1) (ablocks B ly S) -> In (b2, n2) (ablocks B ly S) -> b1 <> b2 ->
  b1 + req_size n1 <= b2 \/ b2 + req_size n2 <= b1.
Proof.
intros ly S Hp W mem md b1 n1 b2 n2 HAR H1 H2 Hne.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b1 n1 HAR H1) as (_ & _ & _ & _ & _ & HPW).
assert (I1 : In (b1, req_size n1) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (apply in_map_iff; exists (b1, n1); split; [reflexivity | exact H1]).
assert (I2 : In (b2, req_size n2) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (apply in_map_iff; exists (b2, n2); split; [reflexivity | exact H2]).
destruct (pvs_pw_in2 zdisjoint _ _ _ HPW I1 I2 ltac:(intros E; injection E; lia)) as [Hd|Hd];
  unfold zdisjoint in Hd; cbn [fst snd] in Hd; lia.
Qed.

(* two live allocator blocks with the same base and non-zero sizes are the same block *)
Lemma pvs_same_base : forall ly S Hp (W : world SEGS) mem md b n1 n2,
  ARx ly S Hp W mem md -> In (b, n1) (ablocks B ly S) -> In (b, n2) (ablocks B ly S) -> 0 < n1 -> 0 < n2 -> n1 = n2.
Proof.
intros ly S Hp W mem md b n1 n2 HAR H1 H2 Hn1 Hn2.
destruct (Z.eq_dec n1 n2) as [E|Hne]; [exact E|exfalso].
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b n1 HAR H1) as (_ & _ & _ & _ & _ & HPW).
assert (I1 : In (b, req_size n1) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (apply in_map_iff; exists (b, n1); split; [reflexivity | exact H1]).
assert (I2 : In (b, req_size n2) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (apply in_map_iff; exists (b, n2); split; [reflexivity | exact H2]).
rewrite !pvs_req_id in I1, I2 by lia.
destruct (pvs_pw_in2 zdisjoint _ _ _ HPW I1 I2 ltac:(intros E; injection E; lia)) as [Hd|Hd];
  unfold zdisjoint in Hd; cbn [fst snd] in Hd; lia.
Qed.

(* a harness block of the ledger as its allocator block *)
Lemma pvs_lam_ab : forall ly S Hp (W : world SEGS) mem Lam peak cnt fail ran most own a k,
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k) Lam -> 0 <= k /\ In (a - cf_head, k + cf_head) (ablocks B ly S) /\ In (a - cf_head) Hp.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own a k HLG Hin.
pose proof HLG as HB. apply prh_ledger_blocks in HB.
pose proof (proj1 (Forall_forall _ _) HB (a, k) Hin) as (Hk0 & Hab & Hhp & _ & _). cbn [fst snd] in *. auto.
Qed.

(* every byte of the grow call's footprint is a client byte below the allocation ceiling *)
Lemma pvs_fp1_low : forall lyc Sc Hpc (Wc : world SEGS) memc md Lamc peakc cntc failc ranc mostc ownc m (o : bool) v
  kids keys n cap acc Di,
  ARx lyc Sc Hpc Wc memc md ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc
    mostc ownc ->
  pi_cont (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) m (prh_lin Lamc) o v kids keys n cap acc Di ->
  4096 <= v -> v + 56 <= YM05.alloc_ceiling ->
  forall a, inFP (pvs_FP1 o v kids keys cap) a -> 4096 <= a < YM05.alloc_ceiling.
Proof.
intros lyc Sc Hpc Wc memc md Lamc peakc cntc failc ranc mostc ownc m o v kids keys n cap acc Di HAR HLG HC Hv0 Hv1 a
  (r & Hr & Ha).
pose proof (@cf_head_nonneg cp) as CH0.
unfold pvs_FP1 in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- cbn in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr. destruct Hr as ([b nb] & <- & Hin). cbn [fst snd] in Ha.
  destruct (pvs_ab_in _ _ _ Hin) as (a0 & k0 & -> & -> & Hin0).
  pose proof (pvs_sblk_in m Lamc o v kids keys n cap acc Di HC a0 k0 Hin0) as HL0.
  destruct (pvs_lam_ab _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLG HL0) as (Hk0 & Hab & _).
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc md _ _ HAR Hab) as (_ & B2 & B3 & _). lia.
Qed.

(* the grow call's footprint is the reader's FP (v's fields) or blocks the call allocated (the slot blocks) *)
Lemma pvs_fpsub : forall ly S lyc Sc Hpc (Wc : world SEGS) memc Lamc peakc cntc failc ranc mostc ownc m (o : bool) v
  kids keys n cap acc Di D0 tr x dd q e (regs0 : bvmap 5 word),
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc
    mostc ownc ->
  pi_cont (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) m (prh_lin Lamc) o v kids keys n cap acc Di ->
  Permutation D0 (pi_sblk o kids keys cap ++ Di) ->
  rd_blocks_move (cp := cp) B ly S lyc Sc D0 tr x dd ->
  fp_sub_x B (STK_parse_items (PI := prh_img_B) d + e) (spZ regs0 + e) (rd_fp q v) (pvs_FP1 o v kids keys cap)
    ly S [] lyc Sc.
Proof.
intros ly S lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc m o v kids keys n cap acc Di D0 tr x dd q e regs0
  HLG HC HPERM (HFR & _) a (r & Hr & Ha).
unfold pvs_FP1 in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- left. exists (v, v + 56). split; [cbn; tauto|]. cbn in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in *; lia.
- right. left. unfold ablocks_fp in Hr. apply in_map_iff in Hr. destruct Hr as ([b nb] & <- & Hin).
  cbn [fst snd] in Ha.
  destruct (pvs_ab_in _ _ _ Hin) as (a0 & k0 & -> & -> & Hin0).
  pose proof (pvs_sblk_in m Lamc o v kids keys n cap acc Di HC a0 k0 Hin0) as HL0.
  destruct (pvs_lam_ab _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLG HL0) as (_ & Hab & _).
  exists (a0 - cf_head), (k0 + cf_head). split; [exact Hab|]. split; [|exact Ha].
  apply HFR. apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. left. exact Hin0.
Qed.

(* a present byte range has a byte list *)
Lemma pvs_garr8_ex : forall (H : word -> bool) (m : word -> option byte) a (k : nat),
  (forall j, (j < k)%nat -> apresent H m (a + Z.of_nat j)) ->
  exists l, length l = k /\ garr8 SEGS (mrestrict H m) a l.
Proof.
intros H m a k. revert a. induction k as [|k IH]; intros a Hp.
- exists []. split; [reflexivity | apply garr8_nil].
- destruct (IH (a + 1) ltac:(intros j Hj; replace (a + 1 + Z.of_nat j) with (a + Z.of_nat (S j)) by lia; apply Hp; lia))
    as (l & Hl & HG).
  destruct (Hp 0%nat ltac:(lia)) as (Hh & b & Hb). rewrite Z.add_0_r in Hh, Hb.
  exists (bv_unsigned b :: l). split; [cbn; rewrite Hl; reflexivity|].
  intros j Hj. destruct j as [|j].
  + cbn [nth]. pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_modulus in Hr. cbn in Hr.
    split; [|lia]. intros kk Hk. assert (kk = 0%nat) by lia. subst kk.
    unfold mbyte, mrestrict. rewrite !Z.add_0_r, Hh, Hb. f_equal.
    unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
    rewrite (Z.mod_small (bv_unsigned b) (2 ^ 8)) by lia. rewrite Z.mod_small by lia.
    symmetry. apply Z_to_bv_bv_unsigned.
  + cbn [nth]. cbn [length] in Hj. destruct (HG j ltac:(lia)) as [Hv Hr].
    replace (a + Z.of_nat (S j)) with (a + 1 + Z.of_nat j) by lia. split; [exact Hv | exact Hr].
Qed.

(* the old slot bytes grow is called with: a live block's user bytes are present *)
Lemma pvs_kb : forall lyc Sc Hpc (Wc : world SEGS) memc md Lamc peakc cntc failc ranc mostc ownc m (o : bool) v kids
  keys n cap acc Di,
  ARx lyc Sc Hpc Wc memc md ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc
    mostc ownc ->
  pi_cont (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) m (prh_lin Lamc) o v kids keys n cap acc Di ->
  exists kb yb, Z.of_nat (length kb) = 56 * Z.of_nat cap /\ bytes_at Wc memc kids kb /\
    (o = true -> Z.of_nat (length yb) = 8 * Z.of_nat cap /\ bytes_at Wc memc keys yb).
Proof.
intros lyc Sc Hpc Wc memc md Lamc peakc cntc failc ranc mostc ownc m o v kids keys n cap acc Di HAR HLG HC.
pose proof (@cf_head_nonneg cp) as CH0.
assert (HP : forall a k, In (a, k) Lamc -> 0 <= k -> forall j, (j < Z.to_nat k)%nat ->
  apresent (w_H Wc) memc (a + Z.of_nat j)).
{ intros a k Hin Hk j Hj. destruct (pvs_lam_ab _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLG Hin) as (_ & Hab & _).
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc md _ _ HAR Hab) as (_ & _ & _ & _ & Hpr & _).
  assert (Hkc : 0 <= k + cf_head) by lia.
  pose proof (pvs_req_ge _ Hkc). apply (proj1 (Hpr (a + Z.of_nat j) ltac:(lia))). }
pose proof HC as (_ & _ & _ & _ & Hcs & _).
destruct Hcs as [(E0 & K0 & Y0) | (Hp & L0 & L1)].
- subst cap. exists [], []. split; [reflexivity|]. split; [apply garr8_nil|]. intros _. split; [reflexivity | apply garr8_nil].
- destruct (pvs_garr8_ex (w_H Wc) memc kids (Z.to_nat (56 * Z.of_nat cap)) (HP kids _ L0 ltac:(lia))) as (kb & Hkl & Hkb).
  destruct o.
  + destruct (pvs_garr8_ex (w_H Wc) memc keys (Z.to_nat (8 * Z.of_nat cap)) (HP keys _ (L1 eq_refl) ltac:(lia)))
      as (yb & Hyl & Hyb).
    exists kb, yb. split; [rewrite Hkl; lia|]. split; [exact Hkb|]. intros _. split; [rewrite Hyl; lia | exact Hyb].
  + exists kb, []. split; [rewrite Hkl; lia|]. split; [exact Hkb|]. intros H; discriminate H.
Qed.

(* grow's room premise on a full container, from the room of the loop's granted run *)
Lemma pvs_room_grow : forall Sc f dd (o : bool) (n cap : nat) accr y, (1 <= f)%nat ->
  rd_room (cp := cp) (RL := RL) Sc (snd (fst (jrl prh_jr_strtod f dd o n cap accr y []))) ->
  Z.of_nat n = Z.of_nat cap ->
  56 * cap2R (Z.of_nat cap) + cf_head < cf_malloc_max /\
  prh_live_evs Sc (PresetReqAt.rd_hevs (PRH_Charge.prhPg_gtrace o (Z.of_nat cap) (Z.of_nat cap))).
Proof.
intros Sc f dd o n cap accr y Hf HR Heq.
destruct f as [|f']; [lia|].
change (S f') with (Nat.succ f') in HR. rewrite (pil_gt_split f' dd o n cap accr y) in HR.
apply pvm_room_pre in HR. assert (n = cap) by lia. subst n. exact (pvs_grow_room Sc o cap HR).
Qed.

(* ---- the text and the node lie outside the slot blocks and the grow call's footprint ---- *)
Lemma pvs_ro_img : forall a, in_roP SEGS (pa_relro_lo (PAImg := PI_prog_B)) (pa_relro_hi (PAImg := PI_prog_B)) a ->
  in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (pa_relro_img (PAImg := PI_prog_B) a Hr)].
Qed.

Lemma pvs_nodup_fst : forall (l : list (Z * Z)) a k k', NoDup (map fst l) -> In (a, k) l -> In (a, k') l -> k = k'.
Proof.
intros l a k k' HN. try (apply NoDup_ListNoDup in HN). revert HN.
induction l as [|[a0 k0] l IH]; intros HN H1 H2; [destruct H1|].
cbn [map fst] in HN. inversion HN as [|x l' Hn HN' E]; subst.
destruct H1 as [E1|H1], H2 as [E2|H2].
- inversion E1; inversion E2; subst; reflexivity.
- inversion E1; subst. exfalso. apply Hn. apply in_map_iff. exists (a, k'). auto.
- inversion E2; subst. exfalso. apply Hn. apply in_map_iff. exists (a, k). auto.
- exact (IH HN' H1 H2).
Qed.

(* the text lies in a block of the ENTRY state or in the image, the prefix's blocks D0 are new: disjoint *)
Lemma pvs_text_fresh : forall ly S Hp Lam text len lyc Sc Hpc (Wc : world SEGS) memc md
  Lamc peakc cntc failc ranc mostc ownc D0 tr x dd,
  prhReader_home B ly S Hp Lam text len -> 0 < len ->
  ARx lyc Sc Hpc Wc memc md ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc
    mostc ownc ->
  Permutation Lamc (D0 ++ Lam) ->
  rd_blocks_move (cp := cp) B ly S lyc Sc D0 tr x dd ->
  forall a k y, In (a, k) D0 -> 0 < k -> a - cf_head <= y < a - cf_head + req_size (k + cf_head) ->
  ~ (text <= y < text + len).
Proof.
intros ly S Hp Lam text len lyc Sc Hpc Wc memc md Lamc peakc cntc failc ranc mostc ownc D0 tr x dd
  Hhome Hlen HAR HLG HPL (HFR & HPB & _) a k y HinD Hk Hy Ht.
pose proof (@cf_head_nonneg cp) as CH0.
pose proof HLG as HNDL. apply prh_ledger_nodup in HNDL.
assert (HinL : In (a, k) Lamc) by (apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact HinD).
destruct (pvs_lam_ab _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLG HinL) as (_ & HabA & _).
assert (HyI : ~ in_img SEGS y).
{ apply (alx_client_img _ _ _ LAWS lyc Sc Hpc Wc memc md y HAR). left. exists (a - cf_head), (k + cf_head). auto. }
destruct Hhome as [[(b0 & m0 & Hin0 & H1 & H2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b0 & m0 & Hin0 & _ & H1 & H2)].
- assert (HinL0 : In (b0, m0) Lamc) by (apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; right; exact Hin0).
  destruct (pvs_lam_ab _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLG HinL0) as (Hm0 & HabB & _).
  assert (Hne : a <> b0).
  { intros ->. pose proof (pvs_nodup_fst Lamc b0 k m0 HNDL HinL HinL0) as ->.
    assert (HND : NoDup (D0 ++ Lam)).
    { apply NoDup_ListNoDup. eapply Permutation_NoDup; [exact HPL|]. try (apply NoDup_ListNoDup in HNDL).
      exact (List.NoDup_map_inv fst Lamc HNDL). }
    exact (pis_nodup_app_disj _ D0 Lam (b0, m0) HND HinD Hin0). }
  assert (RA : k + cf_head <= req_size (k + cf_head)) by (apply pvs_req_ge; lia).
  assert (RB : m0 + cf_head <= req_size (m0 + cf_head)) by (apply pvs_req_ge; lia).
  destruct (pvs_blk_disj lyc Sc Hpc Wc memc md (a - cf_head) (k + cf_head) (b0 - cf_head) (m0 + cf_head) HAR HabA HabB
    ltac:(lia)) as [Hd|Hd]; lia.
- exact (HyI (pvs_ro_img y (proj1 (Hro y Ht)))).
- exact (HyI (pvs_ro_img y (proj1 (Hro y Ht)))).
- assert (HinB : In (b0, m0) (ablocks B lyc Sc))
    by (apply (Permutation_in _ (Permutation_sym HPB)); apply in_or_app; right; exact Hin0).
  assert (Hne : a - cf_head <> b0).
  { intros E. pose proof (pvs_same_base lyc Sc Hpc Wc memc md b0 (k + cf_head) m0 HAR ltac:(rewrite <- E; exact HabA)
      HinB ltac:(lia) ltac:(lia)) as Em.
    apply (HFR a k HinD). rewrite E, Em. exact Hin0. }
  assert (RA : k + cf_head <= req_size (k + cf_head)) by (apply pvs_req_ge; lia).
  assert (RB : m0 <= req_size m0) by (apply pvs_req_ge; lia).
  destruct (pvs_blk_disj lyc Sc Hpc Wc memc md (a - cf_head) (k + cf_head) b0 m0 HAR HabA HinB Hne) as [Hd|Hd]; lia.
Qed.

(* the node lies outside the slot blocks' allocator hulls: its home is another block or a frame *)
Lemma pvs_v_off_slots : forall lyc Sc Hpc (Wc : world SEGS) memc md Lamc peakc cntc failc ranc mostc ownc m (o : bool) v
  kids keys n cap acc Di (regs0 : bvmap 5 word) e,
  ARx lyc Sc Hpc Wc memc md ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc
    mostc ownc ->
  pi_cont (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) m (prh_lin Lamc) o v kids keys n cap acc Di ->
  pj_apartR (pi_sblk o kids keys cap) v ->
  prhReader_at B lyc Sc Lamc regs0 e v 56 -> (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) ->
  forall a k y, In (a, k) (pi_sblk o kids keys cap) -> a - cf_head <= y < a - cf_head + req_size (k + cf_head) ->
  ~ (v <= y < v + 56).
Proof.
intros lyc Sc Hpc Wc memc md Lamc peakc cntc failc ranc mostc ownc m o v kids keys n cap acc Di regs0 e HAR HLG HC HAP
  HAT Hvw a k y Hin Hy Hv.
pose proof (@cf_head_nonneg cp) as CH0.
pose proof HLG as HNDL. apply prh_ledger_nodup in HNDL.
assert (HinL : In (a, k) Lamc) by exact (pvs_sblk_in m Lamc o v kids keys n cap acc Di HC a k Hin).
destruct (pvs_lam_ab _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLG HinL) as (Hk0 & HabA & _).
assert (Hk : 0 < k).
{ unfold pi_sblk, kids_blkR, keys_blkR in Hin. destruct (Z.eqb_spec (Z.of_nat cap) 0) as [E0|E0];
  [destruct o; cbn in Hin; destruct Hin | destruct o; cbn in Hin;
   repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin]. }
(* the node's byte v itself is not in the slot's user range *)
assert (Hnu : ~ (a <= v < a + k)) by (intros Hu; exact (HAP (a, k) v Hin ltac:(unfold pj_holdsR; cbn; lia) ltac:(lia))).
destruct HAT as [(a' & k' & Hin' & H1 & H2) | [(b & m' & Hin' & Hnl & H1 & H2) | [(cid & pos & Hin' & H1 & H2) | (H1 & H2)]]].
- destruct (pvs_lam_ab _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLG Hin') as (Hk' & HabB & _).
  assert (Hne : a <> a').
  { intros <-. pose proof (pvs_nodup_fst Lamc a k k' HNDL HinL Hin') as <-. lia. }
  assert (RA : k + cf_head <= req_size (k + cf_head)) by (apply pvs_req_ge; lia).
  assert (RB : k' + cf_head <= req_size (k' + cf_head)) by (apply pvs_req_ge; lia).
  destruct (pvs_blk_disj lyc Sc Hpc Wc memc md (a - cf_head) (k + cf_head) (a' - cf_head) (k' + cf_head) HAR HabA HabB
    ltac:(lia)) as [Hd|Hd]; lia.
- assert (Hne : a - cf_head <> b).
  { intros E. assert (Hm' : 0 < m') by lia.
    pose proof (pvs_same_base lyc Sc Hpc Wc memc md b (k + cf_head) m' HAR ltac:(rewrite <- E; exact HabA) Hin'
      ltac:(lia) Hm') as Em.
    apply Hnl. replace (b + cf_head) with a by lia. replace (m' - cf_head) with k by lia. exact HinL. }
  assert (RA : k + cf_head <= req_size (k + cf_head)) by (apply pvs_req_ge; lia).
  assert (RB : m' <= req_size m') by (apply pvs_req_ge; lia).
  destruct (pvs_blk_disj lyc Sc Hpc Wc memc md (a - cf_head) (k + cf_head) b m' HAR HabA Hin' Hne) as [Hd|Hd]; lia.
- destruct (alx_sep _ _ _ LAWS lyc Sc Hpc Wc memc md HAR) as (HPW & _).
  pose proof (pvs_pw_app_in zdisjoint _ _ _ _ HPW
    ltac:(apply in_map_iff; exists (a - cf_head, k + cf_head); split; [reflexivity | exact HabA])
    ltac:(apply in_map_iff; exists (cid, pos); split; [reflexivity | exact Hin'])) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  assert (RA : k + cf_head <= req_size (k + cf_head)) by (apply pvs_req_ge; lia). lia.
- lia.
Qed.

(* ---- what the grow call keeps (its callee journal and post) ---- *)
Lemma pvs_pair_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Qed.

(* a block of the call state one of whose bytes is outside the callee's footprint is still live at the return (the
   callee journal over any world relation R: the conjunct read does not mention R) *)
Lemma pvs_blk_persist : forall {R : world SEGS -> world SEGS -> Prop} STK1 sp1 FP1 lyc Sc Hpc (Wc : world SEGS) memc mdc
  own ly2 S2 Hp2 W2 mem2 md2 k1 b m x,
  ajournal_xR (SK := SK) SEGS B prh_pst ARx R STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc own ly2 S2 Hp2 W2 mem2 md2 k1 ->
  In (b, m) (ablocks B lyc Sc) -> b <= x < b + req_size m -> ~ inFP FP1 x -> In (b, m) (ablocks B ly2 S2).
Proof.
intros R STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc own ly2 S2 Hp2 W2 mem2 md2 k1 b m x HJ Hin Hx Hn.
destruct (in_dec pvs_pair_dec (b, m) (ablocks B ly2 S2)) as [H|H]; [exact H|].
exfalso. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfree & _).
apply Hn. replace x with (b + (x - b)) by lia. apply (Hfree b m (x - b) Hin H). lia.
Qed.

(* and its bytes outside the footprint keep their values *)
Lemma pvs_blk_bytes : forall {R : world SEGS -> world SEGS -> Prop} STK1 sp1 FP1 lyc Sc Hpc (Wc : world SEGS) memc mdc
  own ly2 S2 Hp2 W2 mem2 md2 k1 b m x,
  ajournal_xR (SK := SK) SEGS B prh_pst ARx R STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc own ly2 S2 Hp2 W2 mem2 md2 k1 ->
  In (b, m) (ablocks B lyc Sc) -> b <= x < b + req_size m -> ~ inFP FP1 x ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H Wc) memc x.
Proof.
intros R STK1 sp1 FP1 lyc Sc Hpc Wc memc mdc own ly2 S2 Hp2 W2 mem2 md2 k1 b m x HJ Hin Hx Hn.
pose proof (pvs_blk_persist _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hin Hx Hn) as Hin2.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk & _).
replace x with (b + (x - b)) by lia. apply (Hblk b m (x - b) Hin Hin2); [lia|]. replace (b + (x - b)) with x by lia. exact Hn.
Qed.

(* the harness status of a block that is not one of the swapped ones is unchanged by a realloc swap *)
Lemma pvs_hp_swap : forall lyc Sc Hpc Lamc ly2 S2 Hp2 Lam2 Dold Dnew b m (Wc W2 : world SEGS) memc mem2 mdc md2,
  ARx lyc Sc Hpc Wc memc mdc -> ARx ly2 S2 Hp2 W2 mem2 md2 ->
  prhReader_swap B lyc Sc Hpc Lamc ly2 S2 Hp2 Lam2 Dold Dnew ->
  Forall (fun ak => 0 < snd ak + cf_head) Dold -> Forall (fun ak => 0 < snd ak + cf_head) Dnew ->
  In (b, m) (ablocks B lyc Sc) -> 0 < m -> ~ In (b, m) (prhReader_ab Dold) -> In (b, m) (ablocks B ly2 S2) ->
  (In b Hpc <-> In b Hp2).
Proof.
intros lyc Sc Hpc Lamc ly2 S2 Hp2 Lam2 Dold Dnew b m Wc W2 memc mem2 mdc md2 HAR HAR2
  ((bl & PB1 & PB2) & (hl & PH1 & PH2) & _) HFo HFn Hin Hm Hno Hin2.
pose proof (@cf_head_nonneg cp) as CH0.
assert (Hbl : In (b, m) bl).
{ pose proof (Permutation_in _ PB1 Hin) as H. apply in_app_or in H. destruct H as [H|H]; [contradiction | exact H]. }
assert (NO : ~ In b (prhReader_hd Dold)).
{ intros H. unfold prhReader_hd in H. apply in_map_iff in H. destruct H as ([a k] & E & Hak). cbn [fst] in E.
  rewrite Forall_forall in HFo. pose proof (HFo _ Hak) as Hk. cbn [snd] in Hk.
  assert (HabA : In (a - cf_head, k + cf_head) (ablocks B lyc Sc)).
  { apply (Permutation_in _ (Permutation_sym PB1)). apply in_or_app. left. unfold prhReader_ab. apply in_map_iff.
    exists (a, k). auto. }
  rewrite E in HabA. pose proof (pvs_same_base lyc Sc Hpc Wc memc mdc b (k + cf_head) m HAR HabA Hin Hk Hm) as Em.
  apply Hno. unfold prhReader_ab. apply in_map_iff. exists (a, k). cbn [fst snd]. rewrite E, Em. auto. }
assert (NN : ~ In b (prhReader_hd Dnew)).
{ intros H. unfold prhReader_hd in H. apply in_map_iff in H. destruct H as ([a k] & E & Hak). cbn [fst] in E.
  rewrite Forall_forall in HFn. pose proof (HFn _ Hak) as Hk. cbn [snd] in Hk.
  assert (HabA : In (a - cf_head, k + cf_head) (prhReader_ab Dnew)) by (unfold prhReader_ab; apply in_map_iff; exists (a, k); auto).
  assert (HabA2 : In (a - cf_head, k + cf_head) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym PB2)); apply in_or_app; left; exact HabA).
  rewrite E in HabA, HabA2. pose proof (pvs_same_base ly2 S2 Hp2 W2 mem2 md2 b (k + cf_head) m HAR2 HabA2 Hin2 Hk Hm) as Em.
  rewrite Em in HabA.
  destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 b m HAR2 Hin2) as (_ & _ & _ & _ & _ & HPW).
  pose proof (pvs_pw_perm zdisjoint ltac:(intros x y Hxy; unfold zdisjoint in *; lia) _ _
    (Permutation_map (fun b0 => (fst b0, req_size (snd b0))) PB2) HPW) as HPW2.
  rewrite map_app in HPW2.
  pose proof (pvs_pw_app_in zdisjoint _ _ _ _ HPW2
    ltac:(apply in_map_iff; exists (b, m); split; [reflexivity | exact HabA])
    ltac:(apply in_map_iff; exists (b, m); split; [reflexivity | exact Hbl])) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. pose proof (pvs_req_ge m ltac:(lia)). lia. }
split; intros H.
- pose proof (Permutation_in _ PH1 H) as H1. apply in_app_or in H1. destruct H1 as [H1|H1]; [contradiction|].
  apply (Permutation_in _ (Permutation_sym PH2)). apply in_or_app. right. exact H1.
- pose proof (Permutation_in _ PH2 H) as H1. apply in_app_or in H1. destruct H1 as [H1|H1]; [contradiction|].
  apply (Permutation_in _ (Permutation_sym PH1)). apply in_or_app. right. exact H1.
Qed.

Lemma pvs_ab_sub : forall (l1 l2 : list (Z * Z)) x, In x (prhReader_ab l1) -> In x (prhReader_ab (l1 ++ l2)).
Proof. intros l1 l2 x H. unfold prhReader_ab in *. rewrite map_app. apply in_or_app. left. exact H. Qed.

(* grow's post keeps the harness status of every block other than the slot blocks *)
Lemma pvs_hp_iff : forall (ty num str v kids keys n cap : Z) kb yb lyc Sc Hpc (Wc : world SEGS) memc Lamc
  peakc cntc failc ranc mostc ownc ly2 S2 Hp2 W2 regs2 mem2 md2 mdc b m,
  pil_gpost (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B) B
    ty num str v kids keys n cap kb yb lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc ly2 S2 Hp2 W2 regs2 mem2
    md2 ->
  ARx lyc Sc Hpc Wc memc mdc -> ARx ly2 S2 Hp2 W2 mem2 md2 -> 0 <= cap ->
  In (b, m) (ablocks B lyc Sc) -> 0 < m -> ~ In (b, m) (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap)) ->
  In (b, m) (ablocks B ly2 S2) ->
  (In b Hpc <-> In b Hp2).
Proof.
intros ty num str v kids keys n cap kb yb lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc mostc ownc
  ly2 S2 Hp2 W2 regs2 mem2 md2 mdc b m HK HAR HAR2 Hc0 Hin Hm Hno Hin2.
pose proof (@cf_head_nonneg cp) as CH0.
assert (Fk : Forall (fun ak => 0 < snd ak + cf_head) (kids_blkR kids cap)).
{ unfold kids_blkR. destruct (Z.eqb_spec cap 0); repeat constructor. cbn [snd]. lia. }
assert (Fy : Forall (fun ak => 0 < snd ak + cf_head) (kids_blkR kids cap ++ keys_blkR ty keys cap)).
{ apply Forall_app. split; [exact Fk|]. unfold keys_blkR. destruct ((cap =? 0) || negb (ty =? 6)) eqn:E; repeat constructor.
  cbn [snd]. apply orb_false_iff in E. destruct E as [E _]. apply Z.eqb_neq in E. lia. }
assert (Fn1 : forall k' : Z, Forall (fun ak : Z * Z => 0 < snd ak + cf_head) [(k', 56 * cap2R cap)]).
{ intros k'. repeat constructor. cbn [snd]. unfold cap2R. destruct (Z.eqb_spec cap 0); lia. }
assert (Fn2 : forall k' y' : Z, Forall (fun ak : Z * Z => 0 < snd ak + cf_head) [(y', 8 * cap2R cap); (k', 56 * cap2R cap)]).
{ intros k' y'. repeat constructor; cbn [snd]; unfold cap2R; destruct (Z.eqb_spec cap 0); lia. }
assert (Hno1 : ~ In (b, m) (prhReader_ab (kids_blkR kids cap))) by (intros H; apply Hno; apply pvs_ab_sub; exact H).
(* grow's post, read through the text's named layer: its arms, each arm's harness-list conjunct by name *)
unfold pil_gpost in HK. apply tgrP_R_of in HK. pose proof (tgrP_arms HK) as HKA. clear HK.
destruct HKA as [A1 | [A2 | [A3 | [A4 | [A5 | [A6 | A7]]]]]].
- apply tgrP_R1_of in A1. rewrite (tgrP1_hp A1). tauto.
- apply tgrP_R2_of in A2. rewrite (tgrP2_hp A2). tauto.
- apply tgrP_R3_of in A3. pose proof (tgrP3_hp A3) as HP.
  split; intros H; [exact (Permutation_in _ (Permutation_sym HP) H) | exact (Permutation_in _ HP H)].
- apply tgrP_R4_of in A4. destruct A4 as (k' & Lam' & A4).
  exact (pvs_hp_swap _ _ _ _ _ _ _ _ _ _ b m Wc W2 memc mem2 mdc md2 HAR HAR2 (tgrP4_swap A4) Fk (Fn1 k') Hin Hm Hno1
    Hin2).
- apply tgrP_R5_of in A5. destruct A5 as (k' & Lam' & A5).
  exact (pvs_hp_swap _ _ _ _ _ _ _ _ _ _ b m Wc W2 memc mem2 mdc md2 HAR HAR2 (tgrP5_swap A5) Fk (Fn1 k') Hin Hm Hno1
    Hin2).
- apply tgrP_R6_of in A6. destruct A6 as (k' & Lam' & A6).
  exact (pvs_hp_swap _ _ _ _ _ _ _ _ _ _ b m Wc W2 memc mem2 mdc md2 HAR HAR2 (tgrP6_swap A6) Fk (Fn1 k') Hin Hm Hno1
    Hin2).
- apply tgrP_R7_of in A7. destruct A7 as (k' & y' & Lam' & A7).
  exact (pvs_hp_swap _ _ _ _ _ _ _ _ _ _ b m Wc W2 memc mem2 mdc md2 HAR HAR2 (tgrP7_swap A7) Fy (Fn2 k' y') Hin Hm Hno
    Hin2).
Qed.

(* ---- the grow call's footprint, case by case, and what lies outside it ---- *)
Lemma pvs_sblk_pos : forall (o : bool) kids keys (cap : nat) a k, In (a, k) (pi_sblk o kids keys cap) -> 0 < k.
Proof.
intros o kids keys cap a k Hin. unfold pi_sblk, kids_blkR, keys_blkR in Hin.
destruct (Z.eqb_spec (Z.of_nat cap) 0) as [E0|E0]; [destruct o; cbn in Hin; destruct Hin|].
destruct o; cbn in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin.
Qed.

Lemma pvs_fp1_cases : forall (o : bool) v kids keys (cap : nat) y, inFP (pvs_FP1 o v kids keys cap) y ->
  (v + 24 <= y < v + 40) \/ (v + 48 <= y < v + 56) \/
  exists a k, In (a, k) (pi_sblk o kids keys cap) /\ a - cf_head <= y < a - cf_head + req_size (k + cf_head).
Proof.
intros o v kids keys cap y (r & Hr & Hy). unfold pvs_FP1 in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- cbn in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hy; [left | right; left]; lia.
- right. right. unfold ablocks_fp in Hr. apply in_map_iff in Hr. destruct Hr as ([b nb] & <- & Hin). cbn [fst snd] in Hy.
  destruct (pvs_ab_in _ _ _ Hin) as (a0 & k0 & -> & -> & Hin0). exists a0, k0. split; [exact Hin0 | exact Hy].
Qed.

(* the node's 56 bytes are below the low shadow or in high memory (PItems_value.v's pv_v_place, its last clause) *)
Lemma pvs_v_app : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own (regs0 : bvmap 5 word) e v,
  ARx ly S Hp W mem md ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs0 e v 56 -> (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) ->
  v + 56 <= SHADOW_OFF \/ kHighMemBeg <= v.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs0 e v HAR HLG Hat Hvw.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (@cf_head_nonneg cp) as Hh0.
assert (HB : forall b m, In (b, m) (ablocks B ly S) -> b <= v -> v + 56 <= b + req_size m ->
  v + 56 <= SHADOW_OFF \/ kHighMemBeg <= v).
{ intros b m Hin H1 H2. destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b m HAR Hin) as (_ & H4096 & Hc & Happ & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia. }
destruct Hat as [(a & k & Hin & H1 & H2) | [(b & m & Hin & _ & H1 & H2) | [(cid & pos & Hin & H1 & H2) | (H1 & H2)]]].
- destruct (pvs_lam_ab _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLG Hin) as (Hk & Hblk & _).
  apply (HB _ _ Hblk); [lia|]. assert (k + cf_head <= req_size (k + cf_head)) by (apply pvs_req_ge; lia). lia.
- apply (HB _ _ Hin); [lia|]. assert (m <= req_size m) by (apply pvs_req_ge; lia). lia.
- destruct (alx_frames _ _ _ LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & Happ & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
- lia.
Qed.

(* every byte of the grow call's footprint is below the low shadow or in high memory *)
Lemma pvs_fp1_app : forall lyc Sc Hpc (Wc : world SEGS) memc md Lamc peakc cntc failc ranc mostc ownc m (o : bool) v
  kids keys n cap acc Di,
  ARx lyc Sc Hpc Wc memc md ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B lyc Sc Hpc Wc memc Lamc peakc cntc failc ranc
    mostc ownc ->
  pi_cont (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) m (prh_lin Lamc) o v kids keys n cap acc Di ->
  (v + 56 <= SHADOW_OFF \/ kHighMemBeg <= v) ->
  forall y, inFP (pvs_FP1 o v kids keys cap) y -> y < SHADOW_OFF \/ kHighMemBeg <= y.
Proof.
intros lyc Sc Hpc Wc memc md Lamc peakc cntc failc ranc mostc ownc m o v kids keys n cap acc Di HAR HLG HC Hv y Hy.
pose proof (@cf_head_nonneg cp) as CH0.
destruct (pvs_fp1_cases o v kids keys cap y Hy) as [Hy1 | [Hy1 | (a & k & Hin & Hy1)]]; [lia | lia |].
pose proof (pvs_sblk_in m Lamc o v kids keys n cap acc Di HC a k Hin) as HL0.
destruct (pvs_lam_ab _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLG HL0) as (Hk0 & Hab & _).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc md _ _ HAR Hab) as (_ & _ & _ & Happ & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.

Lemma pvs_shadow_off : forall y x, (y < SHADOW_OFF \/ kHighMemBeg <= y) -> 0 <= x < 2 ^ 47 ->
  y <> shadow_of_addr SHADOW_OFF x.
Proof.
intros y x Hy Hx E. subst y. unfold shadow_of_addr, kHighMemBeg, SHADOW_OFF in *.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* ---- the blocks of the call state that hold the text or the node are not slot blocks ---- *)
Lemma pvs_hull_notslot : forall (o : bool) kids keys (cap : nat) b m (P : Z -> Prop),
  (forall a k y, In (a, k) (pi_sblk o kids keys cap) -> a - cf_head <= y < a - cf_head + req_size (k + cf_head) -> ~ P y) ->
  (exists y, P y /\ b <= y < b + m) ->
  ~ In (b, m) (prhReader_ab (kids_blkR kids (Z.of_nat cap) ++ keys_blkR (if o then 6 else 5) keys (Z.of_nat cap))).
Proof.
intros o kids keys cap b m P HP (y & Hy & Hyb) Hin.
destruct (pvs_ab_in _ _ _ Hin) as (a & k & -> & -> & Hin0).
apply (HP a k y Hin0); [| exact Hy].
assert (0 < k) by exact (pvs_sblk_pos o kids keys cap a k Hin0). pose proof (@cf_head_nonneg cp).
assert (k + cf_head <= req_size (k + cf_head)) by (apply pvs_req_ge; lia). lia.
Qed.

(* ---- WHAT THE GROW CALL KEEPS, from its widened journal (aj_call_xW_sp's conclusion) ---- *)

(* the members' blocks Di: their bytes are outside the footprint, so they keep their values and stay writable *)
Lemma pvs_di_kept : forall {R : world SEGS -> world SEGS -> Prop} lyc Sc Hpc (Wc : world SEGS) m1 mdc1 Lamc peakc cntc
  failc ranc mostc ownc m (o : bool) v kids keys n cap acc Di Lam D0 STK1 sp1 ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1,
  ARx lyc Sc Hpc Wc m1 mdc1 ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B lyc Sc Hpc Wc m1 Lamc peakc cntc failc ranc
    mostc ownc ->
  pi_cont (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) m (prh_lin Lamc) o v kids keys n cap acc Di ->
  Permutation Lamc (D0 ++ Lam) -> Permutation D0 (pi_sblk o kids keys cap ++ Di) ->
  ajournal_xR (SK := SK) SEGS B prh_pst ARx R STK1 sp1 (pvs_FP1 o v kids keys cap) lyc Sc Hpc Wc m1 mdc1 []
    ly2 S2 Hp2 W2 mem2 md2 k1 ->
  forall x, (exists b, In b Di /\ pj_holdsR b x) ->
    mbyte SEGS (rdW W2 mem2) x = mbyte SEGS (rdW Wc m1) x /\
    (writable_at SEGS (rdW Wc m1) x -> writable_at SEGS (rdW W2 mem2) x).
Proof.
intros R lyc Sc Hpc Wc m1 mdc1 Lamc peakc cntc failc ranc mostc ownc m o v kids keys n cap acc Di Lam D0 STK1 sp1 ly2 S2
  Hp2 W2 mem2 md2 k1 HAR HLG HC HPL HPERM HJ1 x ([a k] & Hb & Hx).
pose proof (@cf_head_nonneg cp) as CH0.
unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & HAPD & _).
pose proof HLG as HNDL. apply prh_ledger_nodup in HNDL.
assert (HinD0 : forall z, In z (pi_sblk o kids keys cap ++ Di) -> In z Lamc).
{ intros z Hz. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left.
  exact (Permutation_in _ (Permutation_sym HPERM) Hz). }
assert (HinL : In (a, k) Lamc) by (apply HinD0; apply in_or_app; right; exact Hb).
destruct (pvs_lam_ab _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLG HinL) as (Hk0 & HabA & _).
assert (RA : k + cf_head <= req_size (k + cf_head)) by (apply pvs_req_ge; lia).
assert (Hx' : a - cf_head <= x < a - cf_head + req_size (k + cf_head)) by lia.
assert (HN : NoDup (pi_sblk o kids keys cap ++ Di)) by exact (pvs_nodup_D0 Lam Lamc D0 _ HPL HNDL HPERM).
assert (HnFP : ~ inFP (pvs_FP1 o v kids keys cap) x).
{ intros Hfp. destruct (pvs_fp1_cases o v kids keys cap x Hfp) as [Hy | [Hy | (a' & k' & Hin' & Hy)]].
  - exact (HAPD (a, k) x Hb ltac:(unfold pj_holdsR; cbn; lia) ltac:(lia)).
  - exact (HAPD (a, k) x Hb ltac:(unfold pj_holdsR; cbn; lia) ltac:(lia)).
  - assert (HinL' : In (a', k') Lamc) by (apply HinD0; apply in_or_app; left; exact Hin').
    destruct (pvs_lam_ab _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLG HinL') as (Hk0' & HabB & _).
    assert (RB : k' + cf_head <= req_size (k' + cf_head)) by (apply pvs_req_ge; lia).
    destruct (Z.eq_dec a a') as [<- | Hne].
    + pose proof (pvs_nodup_fst Lamc a k k' HNDL HinL HinL') as <-.
      exact (pis_nodup_app_disj _ _ _ (a, k) HN Hin' Hb).
    + destruct (pvs_blk_disj lyc Sc Hpc Wc m1 mdc1 (a - cf_head) (k + cf_head) (a' - cf_head) (k' + cf_head) HAR HabA
        HabB ltac:(lia)) as [Hd|Hd]; lia. }
split.
- apply (mbyte_of_aview SEGS (w_H Wc) (w_H W2) m1 mem2 x).
  replace x with (a - cf_head + (x - (a - cf_head))) by lia.
  apply (pvs_blk_bytes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1 HabA); [lia|]. replace (a - cf_head + (x - (a - cf_head))) with x by lia.
  exact HnFP.
- intros _. pose proof (pvs_blk_persist _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1 HabA Hx' HnFP) as Hin2.
  pose proof HJ1 as (HAR2 & _).
  destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hin2) as (_ & _ & _ & _ & Hpr & _).
  apply apresent_writable. exact (proj1 (Hpr x Hx')).
Qed.

(* a block the call creates is apart from the node: the node's home is kept and live blocks are disjoint *)
Lemma pvs_new_apart : forall {R : world SEGS -> world SEGS -> Prop} lyc Sc Hpc (Wc : world SEGS) m1 mdc1 Lamc peakc cntc
  failc ranc mostc ownc (regs0 : bvmap 5 word) e v STK1 sp1 FP1 ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1,
  ARx lyc Sc Hpc Wc m1 mdc1 ->
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B lyc Sc Hpc Wc m1 Lamc peakc cntc failc ranc
    mostc ownc ->
  prhReader_at B lyc Sc Lamc regs0 e v 56 -> (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) ->
  ajournal_xR (SK := SK) SEGS B prh_pst ARx R STK1 sp1 FP1 lyc Sc Hpc Wc m1 mdc1 [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  ~ inFP FP1 v ->
  forall b m x, In (b, m) (ablocks B ly2 S2) -> ~ In (b, m) (ablocks B lyc Sc) -> b <= x < b + m -> ~ (v <= x < v + 56).
Proof.
intros R lyc Sc Hpc Wc m1 mdc1 Lamc peakc cntc failc ranc mostc ownc regs0 e v STK1 sp1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1
  HAR HLG HAT Hvw HJ1 HvFP b m x Hin2 Hno Hx Hv.
pose proof (@cf_head_nonneg cp) as CH0.
pose proof HJ1 as (HAR2 & HLYL & _ & _ & _ & HFRS & _).
assert (RM : m <= req_size m) by (apply pvs_req_ge; lia).
(* a kept home block (b0, m0) of the call state holding the node *)
assert (HOME : forall b0 m0, In (b0, m0) (ablocks B lyc Sc) -> b0 <= v -> v + 56 <= b0 + m0 -> False).
{ intros b0 m0 Hin0 H1 H2.
  assert (R0 : m0 <= req_size m0) by (apply pvs_req_ge; lia).
  pose proof (pvs_blk_persist _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ v HJ1 Hin0 ltac:(lia) HvFP) as Hin02.
  destruct (Z.eq_dec b b0) as [<- | Hne].
  - pose proof (pvs_same_base ly2 S2 Hp2 W2 mem2 md2 b m m0 HAR2 Hin2 Hin02 ltac:(lia) ltac:(lia)) as <-.
    exact (Hno Hin0).
  - destruct (pvs_blk_disj ly2 S2 Hp2 W2 mem2 md2 b m b0 m0 HAR2 Hin2 Hin02 Hne) as [Hd|Hd]; lia. }
destruct HAT as [(a & k & Hin & H1 & H2) | [(b0 & m0 & Hin & _ & H1 & H2) | [(cid & pos & Hin & H1 & H2) | (H1 & H2)]]].
- destruct (pvs_lam_ab _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLG Hin) as (Hk & Hab & _).
  apply (HOME _ _ Hab); lia.
- exact (HOME _ _ Hin H1 H2).
- assert (HinF : In (cid, pos) (frames S2)) by (rewrite HFRS; exact Hin).
  destruct (alx_layout _ _ _ LAWS lyc Sc Hpc Wc m1 mdc1 ly2 HAR HLYL) as (_ & HFA & _).
  rewrite <- (HFA cid pos) in H1, H2.
  destruct (alx_sep _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 HAR2) as (HPW & _).
  pose proof (pvs_pw_app_in zdisjoint _ _ _ _ HPW
    ltac:(apply in_map_iff; exists (b, m); split; [reflexivity | exact Hin2])
    ltac:(apply in_map_iff; exists (cid, pos); split; [reflexivity | exact HinF])) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- lia.
Qed.

(* the blocks holding the text or the node are kept, with their harness status (PItems_kept.v's pi_blk_kept) *)
Lemma pvs_blk_kept : forall {R : world SEGS -> world SEGS -> Prop} (ty num str v kids keys nZ capZ : Z) kb yb lyc Sc Hpc
  (Wc : world SEGS) m1 mdc1 Lamc peakc cntc failc ranc mostc ownc STK1 sp1 ly2 S2 Hp2 (W2 : world SEGS) regs2 mem2 md2 k1
  text len (o : bool)
  (cap : nat),
  ty = (if o then 6 else 5) -> capZ = Z.of_nat cap ->
  pil_gpost (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B) B
    ty num str v kids keys nZ capZ kb yb lyc Sc Hpc Wc m1 Lamc peakc cntc failc ranc mostc ownc ly2 S2 Hp2 W2 regs2 mem2
    md2 ->
  ARx lyc Sc Hpc Wc m1 mdc1 ->
  ajournal_xR (SK := SK) SEGS B prh_pst ARx R STK1 sp1 (pvs_FP1 o v kids keys cap) lyc Sc Hpc Wc m1 mdc1 []
    ly2 S2 Hp2 W2 mem2 md2 k1 ->
  0 < len ->
  (forall y, text <= y < text + len -> ~ inFP (pvs_FP1 o v kids keys cap) y) -> ~ inFP (pvs_FP1 o v kids keys cap) v ->
  (forall a k y, In (a, k) (pi_sblk o kids keys cap) -> a - cf_head <= y < a - cf_head + req_size (k + cf_head) ->
     ~ (text <= y < text + len)) ->
  (forall a k y, In (a, k) (pi_sblk o kids keys cap) -> a - cf_head <= y < a - cf_head + req_size (k + cf_head) ->
     ~ (v <= y < v + 56)) ->
  pi_blk_kept B lyc Sc Hpc ly2 S2 Hp2 text len v.
Proof.
intros R ty num str v kids keys nZ capZ kb yb lyc Sc Hpc Wc m1 mdc1 Lamc peakc cntc failc ranc mostc ownc STK1 sp1 ly2 S2
  Hp2 W2 regs2 mem2 md2 k1 text len o cap -> -> HK HAR HJ1 Hlen HtFP HvFP HtS HvS b m Hin Hh.
pose proof HJ1 as (HAR2 & _).
assert (RM : m <= req_size m) by (apply pvs_req_ge; destruct Hh; lia).
assert (Hin2 : In (b, m) (ablocks B ly2 S2)).
{ destruct Hh as [Hh|Hh].
  - exact (pvs_blk_persist _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ text HJ1 Hin ltac:(lia) (HtFP text ltac:(lia))).
  - exact (pvs_blk_persist _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ v HJ1 Hin ltac:(lia) HvFP). }
split; [exact Hin2|].
apply (pvs_hp_iff _ _ _ v kids keys nZ (Z.of_nat cap) kb yb lyc Sc Hpc Wc m1 Lamc peakc cntc failc ranc mostc ownc ly2
  S2 Hp2 W2 regs2 mem2 md2 mdc1 b m HK HAR HAR2 ltac:(lia) Hin ltac:(destruct Hh; lia)); [| exact Hin2].
destruct Hh as [Hh|Hh].
- apply (pvs_hull_notslot o kids keys cap b m (fun y => text <= y < text + len) HtS). exists text. split; lia.
- apply (pvs_hull_notslot o kids keys cap b m (fun y => v <= y < v + 56) HvS). exists v. split; lia.
Qed.

(* where the text lives, in the form PItems_kept.v's statement asks (pi_home_ro / kept_img / a live block) *)
Lemma pvs_home_call : forall lyc Sc Hpc (Wc : world SEGS) m1 Lamc peakc cntc failc ranc mostc ownc text len,
  prh_ledger (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B lyc Sc Hpc Wc m1 Lamc peakc cntc failc ranc
    mostc ownc ->
  prhReader_home B lyc Sc Hpc Lamc text len ->
  pi_home_ro (L := B_prog_listing) (PA := PI_prog_B) B text len \/ kept_img B text len \/
  exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= text /\ text + len <= b + m.
Proof.
intros lyc Sc Hpc Wc m1 Lamc peakc cntc failc ranc mostc ownc text len HLG
  [[(b0 & m0 & Hin0 & H1 & H2) | [Hro | Himg]] | (b0 & m0 & Hin0 & _ & H1 & H2)].
- right. right. destruct (pvs_lam_ab _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLG Hin0) as (Hk & Hab & _).
  pose proof (@cf_head_nonneg cp). exists (b0 - cf_head), (m0 + cf_head). split; [exact Hab | lia].
- left. exact Hro.
- right. left. exact Himg.
- right. right. exists b0, m0. auto.
Qed.

(* the callee-saved registers the body pins (pi_regs, pi_regs_body, s5) and the frame's sp / gp / tp *)
Definition pvs_CS : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma pvs_cs_preserved : forall (regs1 regs2 : bvmap 5 word), aregs_preserved regs1 regs2 ->
  forall r, In r pvs_CS -> getr regs2 r = getr regs1 r.
Proof.
intros regs1 regs2 HP r Hr.
rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP.
cbn [pvs_CS In] in Hr.
repeat (destruct Hr as [<- | Hr];
  [match goal with |- acallee_saved ?x => let y := eval vm_compute in x in change x with y end;
   unfold acallee_saved; lia|]).
destruct Hr.
Qed.

Lemma pvs_cs_regs : forall (regs regs' : bvmap 5 word) q v o, (forall r, In r pvs_CS -> getr regs' r = getr regs r) ->
  pi_regs regs q v o -> pi_regs regs' q v o.
Proof.
intros regs regs' q v o HK (R9 & R19 & R18 & R8 & R20 & R26 & R27 & R25 & R23).
unfold pi_regs. rewrite !HK by (cbn; tauto). auto 10.
Qed.

Section tail.
Let RUNTO := PI_RUNTOR (fx := fx) (rc := rc) (SK := SK) (L := B_prog_listing) (PL := PL_prog_B) (PI := PI_prog_B)
  B (@prh_pst prh_img_B) ARx LAWS.
Let BR := paj_branchR (rc := rc) (L := B_prog_listing) (PI := PI_prog_B) WR.

(* BACK FROM grow at 0x87e18: `beqz a0, PI_O_BODY` then `j PI_O_EPI`. Nothing is read or written; a fresh symbolic
   state of atoms only (PItemsBody.Loop's seating). The two exits get the registers of the return state. The batch kit: the
   journal at the budget WS; the run takes it rebased (YCbqGwild.ajournal_xw_rebaseR), each exit gets it back at WS
   (ajournal_xw_unbase0R: the run stores nothing). The walk's relation is wle' segs RZ_cf: the journals at it, the
   conclusions YA0nH.SRr' segs RZ_cf with the text's fpostWFbm (at wle') *)
Lemma pvs_tail : forall (P : list (list Z) -> Prop) (fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem md
  (regs0 : bvmap 5 word) e q v
  (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k2 (regs2 : bvmap 5 word) WS,
  pi_ajR (rc := rc) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK WR ly S Hp W mem md regs0 d e
    q v ly2 S2 Hp2 W2 mem2 md2 k2 WS ->
  (getr regs2 10 = w64 0 \/ getr regs2 10 = w64 (-1)) ->
  (getr regs2 10 = w64 0 -> forall (regs' : bvmap 5 word) md' k',
     pi_ajR (rc := rc) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK WR ly S Hp W mem md regs0 d
       e q v ly2 S2 Hp2 W2 mem2 md' k' WS ->
     (forall r, In r pvs_CS -> getr regs' r = getr regs2 r) ->
     SRr' SEGS YGcfRehidePost.RZ_cf W2 (cfg_at (fx := fx) SEGS (VAL A_TEXT + PIAT PI_O_BODY) regs' mem2 md')
       (fpostWFbm (fx := fx0) (rc := rc) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK P
         (STK_parse_items (PI := prh_img_B) d) e (rd_fp q v) regs0 ly S Hp W mem md Q)) ->
  (getr regs2 10 = w64 (-1) -> forall (regs' : bvmap 5 word) md' k',
     pi_ajR (rc := rc) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK WR ly S Hp W mem md regs0 d
       e q v ly2 S2 Hp2 W2 mem2 md' k' WS ->
     (forall r, In r pvs_CS -> getr regs' r = getr regs2 r) ->
     SRr' SEGS YGcfRehidePost.RZ_cf W2 (cfg_at (fx := fx) SEGS (VAL A_TEXT + PIAT PI_O_EPI) regs' mem2 md')
       (fpostWFbm (fx := fx0) (rc := rc) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK P
         (STK_parse_items (PI := prh_img_B) d) e (rd_fp q v) regs0 ly S Hp W mem md Q)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W2 (cfg_at (fx := fx) SEGS (VAL A_TEXT + PIAT PVS_O_GROWR) regs2 mem2 md2)
    (fpostWFbm (fx := fx0) (rc := rc) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK P
      (STK_parse_items (PI := prh_img_B) d) e (rd_fp q v) regs0 ly S Hp W mem md Q).
Proof.
intros P fx0 ly S Hp W mem md regs0 e q v Q ly2 S2 Hp2 W2 mem2 md2 k2 regs2 WS HJw Ha0 HB0 HE0.
unfold pi_ajR in HJw, HB0, HE0. unfold SRr' in HB0, HE0 |- *. unfold cfg_at.
pose proof (ajxR_wild HJw) as HWD.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARx WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw)
  as HJ.
clear HJw.
remember (Eimg (rc := rc) (L := B_prog_listing) (PI := PI_prog_B) (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HS : st_ok_pi (fx := fx) SEGS VAL E (mkSS (PIAT PVS_O_GROWR) sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (@YK11.mkst fx regs2 (Z_to_bv 64 (VAL A_TEXT + PIAT PVS_O_GROWR)) mem2 (seg_rom SEGS)))).
{ rewrite (restrict_mkst_fx (fx := fx)).
  apply (pa_entry_st_ok_full (fx := fx) (L := B_prog_listing) (PI := PI_prog_B)
           E (PIAT PVS_O_GROWR) sr_atoms regs2 [] (mkFacts [] [] []) (mrestrict (w_H W2) mem2)).
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute; reflexivity.
  - constructor.
  - cbn; exact I.
  - repeat split; exact I. }
assert (SHOK : sh_ok SEGS (SLit 0) [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (HAE : env_agree 32 (Ereg regs2 []) E)
  by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E10 : ew E 10 = getr regs2 10)
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 10 10%bv eq_refl)).
change (w64 (VAL A_TEXT + PIAT PVS_O_GROWR)) with (Z_to_bv 64 (VAL A_TEXT + PIAT PVS_O_GROWR)).
pi_run_to RUNTO HS HJ SHOK (PIAT PI_O_EPI).
{ apply awr_ok_nil. }
assert (HM0 : ms_mem ms = mem2).
{ apply functional_extensionality; intros x. apply HF. intros (r & Hin & _). exact (in_nil Hin). }
clear HF HFr HG.
assert (U10 : forall z, getr regs2 10 = w64 z -> 0 <= z < 2 ^ 64 -> U E (SOff 10 0) = z).
{ intros z Hz Hr. rewrite U_SOff, E10, Hz, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. apply zcanon_id.
  unfold M64. lia. }
psrr_branch_tok RUNTO BR HS SHOK BAND_SPAN.
- (* 0x87e18 `beqz a0, PI_O_BODY` taken: grow returned 0 *)
  rewrite branch_eq_U, U_lit in Hc by lia.
  assert (Ha0' : getr regs2 10 = w64 0).
  { destruct Ha0 as [Ha0 | Ha0]; [exact Ha0|]. exfalso. rewrite (U10 (2 ^ 64 - 1)) in Hc; [discriminate Hc | | lia].
    rewrite Ha0. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity. }
  clear Hc.
  pi_run_to RUNTO HS HJ SHOK (PIAT PI_O_BODY).
  { apply awr_ok_nil. }
  assert (HM1 : ms_mem ms0 = ms_mem ms).
  { apply functional_extensionality; intros x. apply HF. intros (r & Hin & _). exact (in_nil Hin). }
  clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi (rc := rc) (L := B_prog_listing) (PI := PI_prog_B) E _ _ regs2 [] pvs_CS HS HAE
    ltac:(vm_compute; reflexivity)) as HK.
  pmkst HS.
  lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
    replace pcw with (w64 (VAL A_TEXT + PIAT PI_O_BODY)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
  rewrite HM1, HM0 in HJ |- *.
  exact (HB0 Ha0' _ _ _
    (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWD) HK).
- (* not taken: `j PI_O_EPI`, grow returned -1 *)
  rewrite branch_eq_U, U_lit in Hc by lia.
  assert (Ha0' : getr regs2 10 = w64 (-1)).
  { destruct Ha0 as [Ha0 | Ha0]; [|exact Ha0]. exfalso. rewrite (U10 0 Ha0 ltac:(lia)) in Hc. discriminate Hc. }
  clear Hc.
  pi_run_to RUNTO HS HJ SHOK (PIAT PI_O_EPI).
  { apply awr_ok_nil. }
  assert (HM1 : ms_mem ms0 = ms_mem ms).
  { apply functional_extensionality; intros x. apply HF. intros (r & Hin & _). exact (in_nil Hin). }
  clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi (rc := rc) (L := B_prog_listing) (PI := PI_prog_B) E _ _ regs2 [] pvs_CS HS HAE
    ltac:(vm_compute; reflexivity)) as HK.
  pmkst HS.
  lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
    replace pcw with (w64 (VAL A_TEXT + PIAT PI_O_EPI)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
  rewrite HM1, HM0 in HJ |- *.
  exact (HE0 Ha0' _ _ _
    (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWD) HK).
Qed.
End tail.

(* a reader agreement through the aview, between two worlds (the window clause of a call) *)
Lemma pvs_val_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a n w,
  (forall kk, (kk < n)%nat -> aview SEGS H' m' (a + Z.of_nat kk) = aview SEGS H m (a + Z.of_nat kk)) ->
  val_mem SEGS (mrestrict H m) a n w -> val_mem SEGS (mrestrict H' m') a n w.
Proof.
intros H H' m m' a n w HE Hv kk Hk. rewrite (mbyte_of_aview SEGS H H' m m' _ (HE kk Hk)). exact (Hv kk Hk).
Qed.

(* the frame through a call whose footprint is below the frame: the window clause keeps it *)
Lemma pvs_frame_call : forall (regs0 regs1 regs2 : bvmap 5 word) (W : world SEGS) mem (Wc : world SEGS) m1
  (W2 : world SEGS) mem2 e q v (FP1 : list (Z * Z)),
  pi_frame (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) regs0 regs1 W mem Wc m1 e q v ->
  (forall r, In r pvs_CS -> getr regs2 r = getr regs1 r) ->
  (forall a, spZ regs1 <= a < spZ regs1 + (PI_FRAME + e) -> ~ inFP FP1 a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) m1 a) ->
  (forall a, inFP FP1 a -> a < spZ regs1) ->
  pi_frame (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) regs0 regs2 W mem W2 mem2 e q v.
Proof.
intros regs0 regs1 regs2 W mem Wc m1 W2 mem2 e q v FP1
  (Fsp & F3 & F4 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & Fw & Fra & Fe0 & Fe16)
  HK HX Hlow.
unfold PI_FRAME in *.
assert (Hsp : spZ regs2 = spZ regs1) by (unfold spZ; rewrite HK by (cbn; tauto); reflexivity).
assert (VK : forall o w, 40 <= o -> o + 8 <= 144 ->
  val_mem SEGS (mrestrict (w_H Wc) m1) (spZ regs1 + o) 8 w -> val_mem SEGS (mrestrict (w_H W2) mem2) (spZ regs2 + o) 8 w).
{ intros o w Ho1 Ho2 Hv. rewrite Hsp. apply (pvs_val_aview (w_H Wc) (w_H W2) m1 mem2); [|exact Hv].
  intros kk Hk. apply HX; [lia|]. intros Hin. specialize (Hlow _ Hin). lia. }
split; [unfold PI_FRAME; lia|]. split; [rewrite HK by (cbn; tauto); exact F3|]. split; [rewrite HK by (cbn; tauto); exact F4|].
split; [apply VK; [lia | lia | exact V1]|]. split; [apply VK; [lia | lia | exact V2]|].
split; [apply VK; [lia | lia | exact V3]|]. split; [apply VK; [lia | lia | exact V4]|].
split; [apply VK; [lia | lia | exact V5]|]. split; [apply VK; [lia | lia | exact V6]|].
split; [apply VK; [lia | lia | exact V7]|]. split; [apply VK; [lia | lia | exact V8]|].
split; [apply VK; [lia | lia | exact V9]|]. split; [apply VK; [lia | lia | exact V10]|].
split; [apply VK; [lia | lia | exact V11]|]. split; [apply VK; [lia | lia | exact V12]|].
split; [apply VK; [lia | lia | exact V13]|].
split; [|exact (conj Fra (conj Fe0 Fe16))].
intros a Ha Hn. rewrite HX; [exact (Fw a Ha Hn) | lia | intros Hin; specialize (Hlow _ Hin); lia].
Qed.

(* the frame cache of the loop body through the same call *)
Lemma pvs_rb_call : forall (regs1 regs2 : bvmap 5 word) (Wc : world SEGS) m1 (W2 : world SEGS) mem2 v e (FP1 : list (Z * Z)),
  pi_regs_body (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) regs1 Wc m1 v -> 0 <= e ->
  (forall r, In r pvs_CS -> getr regs2 r = getr regs1 r) ->
  (forall a, spZ regs1 <= a < spZ regs1 + (PI_FRAME + e) -> ~ inFP FP1 a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) m1 a) ->
  (forall a, inFP FP1 a -> a < spZ regs1) ->
  pi_regs_body (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) regs2 W2 mem2 v.
Proof.
intros regs1 regs2 Wc m1 W2 mem2 v e FP1 (G22 & G24 & V0 & V32 & V24 & V16 & V8) He HK HX Hlow.
unfold PI_FRAME in *.
assert (Hsp : spZ regs2 = spZ regs1) by (unfold spZ; rewrite HK by (cbn; tauto); reflexivity).
assert (VK : forall o w, 0 <= o -> o + 8 <= 40 ->
  val_mem SEGS (mrestrict (w_H Wc) m1) (spZ regs1 + o) 8 w -> val_mem SEGS (mrestrict (w_H W2) mem2) (spZ regs2 + o) 8 w).
{ intros o w Ho1 Ho2 Hv. rewrite Hsp. apply (pvs_val_aview (w_H Wc) (w_H W2) m1 mem2); [|exact Hv].
  intros kk Hk. apply HX; [lia|]. intros Hin. specialize (Hlow _ Hin). lia. }
unfold pi_regs_body. rewrite !HK by (cbn; tauto).
split; [exact G22|]. split; [exact G24|].
split; [rewrite <- (Z.add_0_r (spZ regs2)); apply VK; [lia | lia | rewrite Z.add_0_r; exact V0]|].
split; [apply VK; [lia | lia | exact V32]|]. split; [apply VK; [lia | lia | exact V24]|].
split; [apply VK; [lia | lia | exact V16] | apply VK; [lia | lia | exact V8]].
Qed.

(* the frame cache of the loop body through the store of q's p field *)
Lemma pvs_rb_store : forall (regs : bvmap 5 word) (Wc : world SEGS) memc m1 v q,
  pi_regs_body (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) regs Wc memc v ->
  pi_agr (pvs_Fq q) (rdW Wc memc) (rdW Wc m1) -> spZ regs + 40 <= q -> q < 2 ^ 64 ->
  pi_regs_body (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) regs Wc m1 v.
Proof.
intros regs Wc memc m1 v q (G22 & G24 & V0 & V32 & V24 & V16 & V8) AGR Hq Hq64.
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr. unfold bv_modulus in Hr. cbn in Hr.
assert (Hs : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; lia).
unfold pi_regs_body.
split; [exact G22|]. split; [exact G24|].
split; [apply (pi_val_agr SEGS (pvs_Fq q) _ _ _ _ _ AGR); [intros kk Hk; unfold pvs_Fq; lia | exact V0]|].
split; [apply (pi_val_agr SEGS (pvs_Fq q) _ _ _ _ _ AGR); [intros kk Hk; unfold pvs_Fq; lia | exact V32]|].
split; [apply (pi_val_agr SEGS (pvs_Fq q) _ _ _ _ _ AGR); [intros kk Hk; unfold pvs_Fq; lia | exact V24]|].
split; [apply (pi_val_agr SEGS (pvs_Fq q) _ _ _ _ _ AGR); [intros kk Hk; unfold pvs_Fq; lia | exact V16]|].
apply (pi_val_agr SEGS (pvs_Fq q) _ _ _ _ _ AGR); [intros kk Hk; unfold pvs_Fq; lia | exact V8].
Qed.

(* the comma arm's room: the rest of the member's run is the loop's run from the cursor after ',' *)
Lemma pvs_room_comma : forall Sc f dd (o : bool) n cap acc nm t r r1,
  skip r = 44 :: r1 ->
  rd_room (cp := cp) (RL := RL) Sc (snd (fst (pv_kont f (Nat.succ dd) o n cap (rev acc) nm (t, r) []))) ->
  rd_room (cp := cp) (RL := RL) Sc
    (snd (fst (jrl prh_jr_strtod f (Nat.succ dd) o (Nat.succ n) cap (rev (acc ++ [(nm, t)])) r1 []))).
Proof. intros Sc f dd o n cap acc nm t r r1 Hs H. unfold pv_kont in H. rewrite Hs, Z.eqb_refl in H. rewrite pvs_rev_snoc. exact H. Qed.

(* ---- THE NEIGHBOURS' STATEMENTS this walk uses, as Section hypotheses ---- *)
(* grow's text (the kit's, lib/A/PRH_FnReader.v tgrow_specX), at every float state the run can reach *)
Hypothesis GROW : forall (fy : YK11.FPState),
  tgrow_specX (fx := fy) (rc := rc) (ci := ci) (cp := cp) (PI := prh_img_B) (RL := RL) (L := B_prog_listing)
    (PA := PI_prog_B) B ARx SK CTX0.
(* the grow-post step, PROVED (lib/B/Prog/PItems_body_loop.v pil_grow_step, Qed) *)
Let PVS_STEP := pil_grow_step (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing)
  (PA := PI_prog_B) B ARx LAWS PIL_HEAD.

(* the cursor transport across a call over a world relation R (lib/B/Prog/PItems_kept.v pi_cur_kept_callR_stmt, a
   statement there; proved there as pi_cur_kept_callR), taken at the grow call's journal at wle' segs RZ_cf *)
Hypothesis HKEPT : pi_cur_kept_callR_stmt (rc := rc) (cp := cp) (PIi := prh_img_B) (L := B_prog_listing)
  (PA := PI_prog_B) (SKq := SK) B ARx.

(* the stack budget of the grow call: its frame and parse_items' own fit in parse_items' bound (PItems_body_key.v's
   pik_zmaxl_in / pik_stk_skw, the same argument) *)
Lemma pvs_zmaxl_in : forall x l, In x l -> x <= zmaxl l.
Proof.
intros x l. induction l as [|y l IH]; intros H; [destruct H|]. cbn [zmaxl fold_right].
destruct H as [<-|H]; [lia|]. specialize (IH H). fold (zmaxl l). lia.
Qed.

Lemma pvs_stk_grow : STK_grow + PI_FRAME <= STK_parse_items (PI := prh_img_B) d.
Proof.
unfold STK_parse_items, LEAF_pv_pi.
pose proof (pvs_zmaxl_in STK_grow [STK_RT_ECALL; STK_RT_STRTOD; STK_fuzz_malloc; STK_fuzz_free; STK_literal;
  STK_parse_string; STK_grow; STK_skip_ws] ltac:(cbn; tauto)) as H1.
pose proof (Nat2Z.is_nonneg (PjGrammar.MAXD - d)) as H4.
assert (EF : PRH_Base.pi_frame (PrhImg := prh_img_B) F_parse_items = PI_FRAME) by reflexivity.
assert (EV : 0 <= PRH_Base.pi_frame (PrhImg := prh_img_B) F_parse_value) by (vm_compute; discriminate).
assert (H5 : 0 <= Z.of_nat (PjGrammar.MAXD - d) *
  (PRH_Base.pi_frame (PrhImg := prh_img_B) F_parse_value + PRH_Base.pi_frame (PrhImg := prh_img_B) F_parse_items))
  by (rewrite EF; unfold PI_FRAME; nia).
lia.
Qed.

Lemma pvs_zmaxl_nonneg : forall l, 0 <= zmaxl l.
Proof. intros l. induction l as [|y l IH]; cbn [zmaxl fold_right]; [lia|]. fold (zmaxl l). lia. Qed.

Lemma pvs_stk_pi : PI_FRAME <= STK_parse_items (PI := prh_img_B) d.
Proof.
unfold STK_parse_items, LEAF_pv_pi.
pose proof (pvs_zmaxl_nonneg [STK_RT_ECALL; STK_RT_STRTOD; STK_fuzz_malloc; STK_fuzz_free; STK_literal;
  STK_parse_string; STK_grow; STK_skip_ws]) as H1.
pose proof (Nat2Z.is_nonneg (PjGrammar.MAXD - d)) as H4.
assert (EF : PRH_Base.pi_frame (PrhImg := prh_img_B) F_parse_items = PI_FRAME) by reflexivity.
assert (EV : 0 <= PRH_Base.pi_frame (PrhImg := prh_img_B) F_parse_value) by (vm_compute; discriminate).
assert (H5 : 0 <= Z.of_nat (PjGrammar.MAXD - d) *
  (PRH_Base.pi_frame (PrhImg := prh_img_B) F_parse_value + PRH_Base.pi_frame (PrhImg := prh_img_B) F_parse_items))
  by (rewrite EF; unfold PI_FRAME; nia).
lia.
Qed.

(* ---- THE CALL SITE's helpers ---- *)
(* fpre's read-only view rides through a journal whose footprint does not open the sink (PItems_body_key.v
   pik_rod_kept, with S1ImgB.v pst_not_ro_B for its preamble hypothesis PIK_PSTRO; PItems_value_aftv.v's av_rod_kept), over any
   world relation R (the image conjunct does not read R) *)
Lemma pvs_rod_kept : forall (R : world SEGS -> world SEGS -> Prop) STK sp0 FP ly S Hp (W : world SEGS) mem md own lyc
    Sc Hpc (W' : world SEGS) mem' md' k,
  ajournal_xR (SK := SK) SEGS B prh_pst ARx R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W' mem' md' k ->
  ~ YI16.sink_open_fp FP ->
  arodata_okP SEGS (pa_relro_lo (PAImg := PI_prog_B)) (pa_relro_hi (PAImg := PI_prog_B)) B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS (pa_relro_lo (PAImg := PI_prog_B)) (pa_relro_hi (PAImg := PI_prog_B)) B (aview SEGS (w_H W') mem').
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W' mem' md' k HJ Hsk Hrod a Hro Hos Her.
pose proof (ajxR_img HJ) as F3.
rewrite (F3 a); [exact (Hrod a Hro Hos Her) | | exact Hos | exact Her | | apply fp_spares_closed; exact Hsk].
- destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (pa_relro_img (PAImg := PI_prog_B) a Hr)].
- intros Hp'. exact (pvs_pst_not_ro a Hp' Hro).
Qed.

(* PItems_body_key.v pik_rdword_of_val, same proof *)
Lemma pvs_rdword_of_val : forall (H : word -> bool) (mem : word -> option byte) a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (Bb : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bb 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bb 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bb 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bb 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bb 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bb 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bb 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bb 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* a run whose only write window is q's p field leaves every other cell of the reader as it was *)
Lemma pvs_frame_q : forall E rs (m m' : word -> option byte) q, frame_of E rs m m' ->
  (forall a, in_wrange E rs a -> q <= a < q + 8) -> pi_agr (pvs_Fq q) m m'.
Proof.
intros E rs m m' q HF Hw a (Ha & Hn). apply HF. rewrite unsigned_lit_small by lia. intros Hi. exact (Hn (Hw a Hi)).
Qed.

(* the node's place does not depend on the window when the node is not in it *)
Lemma pvs_at_regs : forall ly S Lam (regs regs' : bvmap 5 word) e e' p n, prhReader_at B ly S Lam regs e p n ->
  (p + n <= spZ regs \/ spZ regs + e <= p) -> 0 < n -> prhReader_at B ly S Lam regs' e' p n.
Proof.
intros ly S Lam regs regs' e e' p n [H | [H | [H | (H1 & H2)]]] Hw Hn.
- left. exact H.
- right. left. exact H.
- right. right. left. exact H.
- lia.
Qed.

(* the frame cache of the loop body under another register file with the same sp, n pointer and its shadow *)
Lemma pvs_rb_regs : forall (regs regs' : bvmap 5 word) (W : world SEGS) m v,
  getr regs' 2 = getr regs 2 -> getr regs' 22 = getr regs 22 -> getr regs' 24 = getr regs 24 ->
  pi_regs_body (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) regs W m v ->
  pi_regs_body (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) regs' W m v.
Proof.
intros regs regs' W m v H2 H22 H24 (G22 & G24 & V0 & V32 & V24 & V16 & V8).
assert (Hs : spZ regs' = spZ regs) by (unfold spZ; rewrite H2; reflexivity).
unfold pi_regs_body. rewrite H22, H24, Hs. auto 10.
Qed.

Lemma pvs_stk_grow0 : 0 <= STK_grow (PI := prh_img_B).
Proof.
unfold STK_grow, STK_fuzz_realloc.
pose proof (pvs_zmaxl_nonneg [STK_RT_ALLOC; STK_RT_ECALL; STK_own; STK_fuzz_malloc]) as H1.
cbn [PRH_Base.pi_frame prh_img_B] in *. lia.
Qed.

Section core.
(* PItems_entry.v's epilogue and PItems_head.v's second closer copy, PItems_pres.v's texts *)
Hypothesis HEPI : pi_epi_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing)
  (PA := PI_prog_B) (PL := PL_prog_B) B ARx SK d.
Hypothesis HCL2 : pi_close2_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing)
  (PA := PI_prog_B) (PL := PL_prog_B) B ARx SK d CTX0 CW.
(* the induction measure and the loop body below it (this walk's cut) *)
Variable N : nat.
Hypothesis HBODY : forall N', (N' < N)%nat -> pi_body_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL)
  (L := B_prog_listing) (PA := PI_prog_B) (PL := PL_prog_B) B ARx SK d CTX0 CW N'.

Let RUNTO := PI_RUNTOR (fx := fx) (rc := rc) (SK := SK) (L := B_prog_listing) (PL := PL_prog_B) (PI := PI_prog_B)
  B (@prh_pst prh_img_B) ARx LAWS.
Let RUN := PI_RUNR (fx := fx) (rc := rc) (SK := SK) (L := B_prog_listing) (PL := PL_prog_B) (PI := PI_prog_B)
  B (@prh_pst prh_img_B) ARx LAWS.
Let BR := paj_branchR (rc := rc) (L := B_prog_listing) (PI := PI_prog_B) WR.
(* the same runners carrying the overlay's normality (YAkMemnorm.memnorm) from the run's start memory to its end, over
   the walk's relation *)
Let RUNTOI := paj_run_to_x_invR (fx := fx) (rc := rc) (SK := SK) (L := B_prog_listing) (PL := PL_prog_B)
  (PI := PI_prog_B) B (@prh_pst prh_img_B) ARx LAWS (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)
  WR (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).
Let RUNI := paj_run_x_invR (fx := fx) (rc := rc) (SK := SK) (L := B_prog_listing) (PL := PL_prog_B) (PI := PI_prog_B)
  B (@prh_pst prh_img_B) ARx LAWS (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)
  WR (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf).

(* AT PI_O_EPI with nothing written since the pre: the epilogue concludes any stable post Q that holds at a0 = -1,
   at the journal's budget WS and any budget predicate P that holds of it (pi_epi_spec's generic P) *)
Lemma pvs_epi : forall (P : list (list Z) -> Prop) (fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem md
  (regs0 : bvmap 5 word) e q v
  (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  lyc Sc Hpc (Wc : world SEGS) memc memf mdf k WS (regs regs' : bvmap 5 word),
  pi_ajR (rc := rc) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK WR ly S Hp W mem md regs0 d e
    q v lyc Sc Hpc Wc memf mdf k WS -> P WS ->
  pi_fpok fx0 fx -> pi_frame (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) regs0 regs W mem Wc memc e q v ->
  rdW Wc memf = rdW Wc memc -> YAkMemnorm.memnorm SEGS memf ->
  spZ regs' = spZ regs -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 -> getr regs' 21 = w64 (-1) ->
  pi_Qstable (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) Q ->
  (forall regs'', getr regs'' 10 = w64 (-1) -> Q lyc Sc Hpc Wc regs'' memf mdf) ->
  SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfg_at (fx := fx) SEGS (VAL A_TEXT + PIAT PI_O_EPI) regs' memf mdf)
    (fpostWFbm (fx := fx0) (rc := rc) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK P
      (STK_parse_items (PI := prh_img_B) d) e (rd_fp q v) regs0 ly S Hp W mem md Q).
Proof.
intros P fx0 ly S Hp W mem md regs0 e q v Q lyc Sc Hpc Wc memc memf mdf k WS regs regs' HJ HP Hfp Hfr MEQ HMNf Hsp H3
  H4 H21 HQs HQ.
apply (HEPI P fx fx0 ly S Hp W mem md regs0 e q v Q lyc Sc Hpc Wc memf mdf k regs' (-1) WS HJ HP).
unfold pi_epi_pre. split; [exact Hfp|]. split; [exact HMNf|]. split.
- apply (pi_frame_kept (fun _ => True) regs0 regs regs' W mem Wc memc memf e q v Hfr Hsp H3 H4);
  [intros a _; rewrite MEQ; reflexivity | intros a _; exact I | intros a _ _; exact I].
- split; [exact H21|]. split; [exact HQs | exact HQ].
Qed.


Lemma pvs_w64_ne : w64 0 <> w64 (-1).
Proof. unfold w64. intros E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. vm_compute in E. discriminate. Qed.

(* BACK FROM grow at 0x87e18: PItems_body_loop.v's step on grow's post, then a0 = 0 re-enters the loop body at PI_O_BODY
   with N' = |rest after the comma| < N (HBODY), a0 = -1 goes to the epilogue with the refusal post (HEPI). The batch kit: the
   step's loop invariants at n + 1 members (pi_grant, cap = ncap (n + 1), pi_ncaps, pi_forder at the call memory, and
   pi_fl_eq from pv_jfk's comma branch: pvs_fl_comma); the caller's journal at its budget WS0 (grow stores nothing) *)
Lemma pvs_grow_post : forall (fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem md ch CTX (regs0 : bvmap 5 word) e q v
  (o : bool) text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc (Wc : world SEGS) m1 mdc1 (regs1 : bvmap 5 word)
  (f n cap : nat) acc kids keys Di nm t r r0 pc ok0 tr0 D0 Lamc peakc cntc failc ranc af1 kb yb
  ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k k1 (regs2 : bvmap 5 word) WS0,
  pi_fpok fx0 fx ->
  pi_ent (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o CTX0 CW ->
  (* memnorm at the call state *)
  YAkMemnorm.memnorm SEGS m1 ->
  pi_frame (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) regs0 regs1 W mem Wc m1 e q v ->
  pi_regs regs1 q v o -> pi_regs_body (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) regs1 Wc m1 v ->
  getr regs1 21 = w64 (-1) ->
  pi_cont (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) (rdW Wc m1) (prh_lin Lamc) o v kids keys (Nat.succ n) cap
    (acc ++ [(nm, t)]) Di ->
  Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - Nat.succ d)%nat) (acc ++ [(nm, t)]) ->
  pj_apartR (pi_sblk o kids keys cap) v ->
  Permutation D0 (pi_sblk o kids keys cap ++ Di) ->
  pv_run_after d o (rest_atR tb text p) ok0 tr0 f n cap acc nm (Some (t, r)) ->
  pi_led Lam peak cnt fail ran most ok0 tr0 D0 Lamc peakc cntc failc ranc ->
  rd_blocks_move (cp := cp) B ly S lyc Sc D0 tr0 (rest_atR tb text p) d ->
  (* the prefix's two travelling facts at the call state (form (b)) *)
  PItems_posb.pi_posb S Sc tr0 ->
  PItems_posb.pi_live (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc)) tr0 ->
  blocks_bytes Sc <= blocks_bytes S + PRH_Charge.prh_held tr0 -> length ok0 = PjGrammar.calls tr0 ->
  Ledger.lsum D0 = PjGrammar.held tr0 ->
  pi_cur (rc := rc) (cp := cp) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B)
    B regs0 e q v text len tb d lyc Sc Hpc Wc m1 (pc + 1) Lamc peakc cntc failc ranc most own ->
  cntc + 2 * Z.of_nat (length (rest_atR tb text pc)) + 2 < 2 ^ 64 - 1 ->
  text <= pc < text + len -> rest_atR tb text pc = 44 :: r0 -> skip r = 44 :: r0 ->
  (Nat.succ (length r) <= N)%nat -> (2 * length r + 3 <= f)%nat ->
  rd_room (cp := cp) (RL := RL) Sc (snd (fst (pv_kont f (Nat.succ d) o n cap (rev acc) nm (t, r) []))) ->
  (* The batch kit's invariants of pv_sep_pre, at the call memory m1 *)
  pi_grant ok0 tr0 -> cap = PresetReqAt.ncap (Nat.succ n) ->
  pi_ncaps (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) (rdW Wc m1) kids (acc ++ [(nm, t)]) ->
  pi_forder (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) (rdW Wc m1) (prh_lin Lamc) o kids keys (Nat.succ n)
    Di (acc ++ [(nm, t)]) af1 ->
  (forall ok1, prhPi_frees d o (rest_atR tb text p) (ok0 ++ ok1) = pv_jfk f (Nat.succ d) o n cap af1 r ok1) ->
  ARx lyc Sc Hpc Wc m1 mdc1 ->
  pi_ajR (rc := rc) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK WR ly S Hp W mem md regs0 d e
    q v ly2 S2 Hp2 W2 mem2 md2 k WS0 ->
  YCbqGwild.wbudget CW 0 WS0 ->
  ajournal_xR (SK := SK) SEGS B prh_pst ARx WR (STK_grow + (PI_FRAME + e)) (spZ regs1 + (PI_FRAME + e))
    (pvs_FP1 o v kids keys cap) lyc Sc Hpc Wc m1 mdc1 [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, spZ regs1 <= a < spZ regs1 + (PI_FRAME + e) -> ~ inFP (pvs_FP1 o v kids keys cap) a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) m1 a) ->
  aregs_preserved regs1 regs2 ->
  pil_gpost (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B) B
    (if o then 6 else 5) 0 0 v kids keys (Z.of_nat (Nat.succ n)) (Z.of_nat cap) kb yb
    lyc Sc Hpc Wc m1 Lamc peakc cntc failc ranc most own ly2 S2 Hp2 W2 regs2 mem2 md2 ->
  (YAkMemnorm.memnorm SEGS m1 -> YAkMemnorm.memnorm SEGS mem2) ->
  (Nat.succ n = cap -> bytes_at Wc m1 kids kb /\ Z.of_nat (length kb) = 56 * Z.of_nat cap /\
     (o = true -> bytes_at Wc m1 keys yb /\ Z.of_nat (length yb) = 8 * Z.of_nat cap)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W2 (cfg_at (fx := fx) SEGS (VAL A_TEXT + PIAT PVS_O_GROWR) regs2 mem2 md2)
    (fpostWFbm (fx := fx0) (rc := rc) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK
      (YCbqGwild.wbudget CW 0) (STK_parse_items (PI := prh_img_B) d) e (rd_fp q v) regs0 ly S Hp W mem md
      (pi_post (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
         B ly S d o tb text len p q v Lam peak cnt fail ran most own kr)).
Proof.
intros fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc Wc m1 mdc1
  regs1 f n cap acc kids keys Di nm t r r0 pc ok0 tr0 D0 Lamc peakc cntc failc ranc af1 kb yb ly2 S2 Hp2 W2 mem2 md2 k
  k1 regs2 WS0 Hfp Hent HMN1 Hfr1 Hrg1 Hrb1 R21 HCONT1 HDEP HAP HPERM HRUN HLED HBM HPOSB HLIVE HBB HOK HLS HCUR1
  HCNTpc Hpcb Hyc HY HN HF HRM HGR Hcapn HNC1 HFORD1 HFLE HAR1 HJ2 HWS HJ1 HX HP HG HMK HKB.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as CH0.
pose proof pvs_stk_grow as HSTKG. pose proof pvs_stk_nonneg as HSTK. pose proof pvs_stk_pi as HSTKP.
assert (EPF : PI_FRAME = 144) by reflexivity.
pose proof HCUR1 as (HIN & HRA & HSRC & HHOME & HPLAT & HRAV & HLG & HCNT).
pose proof HIN as (Vp & Ve & Vdp & Hrw & Hq8 & Ht0 & Htl & Hple & Hlen & HG0 & Hdqt & Hd032).
pose proof Hent as (Emn & ELC1 & ELC2 & Ein & Ecl & Ecur & Echn & Epart & E10 & E11 & E12 & Egp & Etp & RDP & Eplt & Enth
  & Eroom & Ech0 & Efrm & Erod & EENT).
pvs_split EENT.
pose proof RDP as (_ & _ & _ & _ & IN0 & Hfwin & Hsq & Hqe & _ & _ & HHOME0 & RDT).
pvs_split RDT.
match goal with H : prhPv_node _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HPV end.
match goal with H : q + 24 <= v \/ v + 56 <= q |- _ => rename H into Hqv end.
match goal with H : 0 < len -> text + len <= v \/ v + 56 <= text |- _ => rename H into Htv end.
match goal with H : v + 56 <= spZ regs0 \/ spZ regs0 + e <= v |- _ => rename H into Hvw end.
match goal with H : prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own |- _ => rename H into HLG0 end.
match goal with H : (d <= PjGrammar.MAXD)%nat |- _ => rename H into Hdm end.
match goal with H : cnt + 2 * Z.of_nat (length (rest_atR tb text p)) + 2 < 2 ^ 64 - 1 |- _ => rename H into HCNT0 end.
pose proof IN0 as (_ & _ & _ & _ & _ & _ & _ & Hple0 & Hlen0 & _).
pose proof HPV as (Hv0 & Hv8 & _).
pose proof HSRC as (HGt & Ht4 & Htc & Htam & Htra & _).
pose proof Hfr1 as (Fsp & F3 & F4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fwin & Fret & He0 & He16).
pose proof HJ2 as HJ2'. unfold pi_ajR in HJ2'.
pose proof HJ2' as (HAR2 & HLY2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk2 & _ & _).
pose proof Hastk2 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
pose proof HLY2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
pose proof HJ1 as (_ & _ & _ & _ & _ & HFRS1 & _).
pose proof HLED as (_ & _ & _ & HPL & _).
pose proof HLG0 as Hcnt64. apply prh_ledger_bounds in Hcnt64. destruct Hcnt64 as (_ & _ & Hcnt64 & _).
rewrite Hlen in Htc.
assert (Hq0 : YM05.alloc_ceiling <= q) by lia.
assert (HK2 : forall r', In r' pvs_CS -> getr regs2 r' = getr regs1 r') by exact (pvs_cs_preserved regs1 regs2 HP).
assert (Hv56 : v + 56 <= YM05.alloc_ceiling)
  by exact (pvs_v_low lyc Sc Hpc Wc m1 mdc1 Lamc peakc cntc failc ranc most own regs0 e v HAR1 HLG HPLAT Hvw).
assert (Hvapp : v + 56 <= SHADOW_OFF \/ kHighMemBeg <= v)
  by exact (pvs_v_app lyc Sc Hpc Wc m1 mdc1 Lamc peakc cntc failc ranc most own regs0 e v HAR1 HLG HPLAT Hvw).
assert (Hrest1 : rest_atR tb text (pc + 1) = r0) by exact (pvs_rest_next tb text pc 44 r0 ltac:(lia) Hyc).
assert (Hr0r : (length r0 < length r)%nat).
{ pose proof (PjGrammar.skip_len r) as H. rewrite HY in H. cbn [length] in H. lia. }
assert (Hlenpos : 0 < len) by lia.
(* the slot blocks are apart from the text and from the node *)
assert (HtS : forall a k' y, In (a, k') (pi_sblk o kids keys cap) ->
  a - cf_head <= y < a - cf_head + req_size (k' + cf_head) -> ~ (text <= y < text + len)).
{ intros a k' y Hin Hy.
  apply (pvs_text_fresh ly S Hp Lam text len lyc Sc Hpc Wc m1 mdc1 Lamc peakc cntc failc ranc most own D0 tr0
    (rest_atR tb text p) d HHOME0 Hlenpos HAR1 HLG HPL HBM a k' y).
  - apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. left. exact Hin.
  - exact (pvs_sblk_pos o kids keys cap a k' Hin).
  - exact Hy. }
assert (HvS : forall a k' y, In (a, k') (pi_sblk o kids keys cap) ->
  a - cf_head <= y < a - cf_head + req_size (k' + cf_head) -> ~ (v <= y < v + 56))
  by exact (pvs_v_off_slots lyc Sc Hpc Wc m1 mdc1 Lamc peakc cntc failc ranc most own _ o v kids keys _ cap _ Di regs0 e
              HAR1 HLG HCONT1 HAP HPLAT Hvw).
set (FP1 := pvs_FP1 o v kids keys cap) in *.
assert (HvFP : ~ inFP FP1 v).
{ intros Hq1. destruct (pvs_fp1_cases o v kids keys cap v Hq1) as [Hy | [Hy | (a & k' & Hin & Hy)]]; [lia | lia |].
  exact (HvS a k' v Hin Hy ltac:(lia)). }
assert (HtFP : forall y, text <= y < text + len -> ~ inFP FP1 y).
{ intros y Hy Hq1. destruct (pvs_fp1_cases o v kids keys cap y Hq1) as [Hy1 | [Hy1 | (a & k' & Hin & Hy1)]];
  [lia | lia | exact (HtS a k' y Hin Hy1 Hy)]. }
assert (HFPapp : forall y, inFP FP1 y -> y < SHADOW_OFF \/ kHighMemBeg <= y)
  by exact (pvs_fp1_app lyc Sc Hpc Wc m1 mdc1 Lamc peakc cntc failc ranc most own _ o v kids keys _ cap _ Di HAR1 HLG
    HCONT1 Hvapp).
assert (HFPlow : forall y, inFP FP1 y -> 4096 <= y < YM05.alloc_ceiling)
  by exact (pvs_fp1_low lyc Sc Hpc Wc m1 mdc1 Lamc peakc cntc failc ranc most own _ o v kids keys _ cap _ Di HAR1 HLG
    HCONT1 ltac:(lia) Hv56).
assert (HFPbelow : forall a, inFP FP1 a -> a < spZ regs1).
{ intros a Ha. pose proof (HFPlow a Ha). rewrite Fsp, EPF. lia. }
(* the entry's text is not empty and its counter has headroom *)
assert (HX0 : rest_atR tb text p <> []).
{ unfold rest_atR. intros E0. pose proof (length_skipn (Z.to_nat (p - text)) tb) as HL0. rewrite E0 in HL0.
  cbn [length] in HL0. lia. }
(* PItemsBody.Loop's step, at n + 1 members (the batch kit: the loop invariants, pi_fl_eq from pv_jfk's comma branch) *)
pose proof (PVS_STEP ly S d o tb text len p q v e regs0 Lam peak cnt fail ran most own kr lyc Sc Hpc Wc m1 f (Nat.succ n)
  cap (acc ++ [(nm, t)]) kids keys Di (pc + 1) ok0 tr0 D0 Lamc peakc cntc failc ranc af1 kb yb ly2 S2 Hp2 W2 regs2 mem2
  md2 HMN1 HCUR1) as OUT.
rewrite Hrest1 in OUT. rewrite Hyc in HCNTpc. cbn [length] in HCNTpc.
specialize (OUT ltac:(lia) HCONT1 HDEP HAP HPERM ltac:(lia) (pvs_run_comma d o _ ok0 tr0 f n cap acc nm t r r0 HRUN HY)
  HX0 (conj Hcnt64 HCNT0) HLED HBM HPOSB HLIVE HBB HOK HLS (pvs_room_comma Sc f d o n cap acc nm t r r0 HY HRM)
  HGR Hcapn HNC1 HFORD1 (pvs_fl_comma d o _ ok0 f n cap af1 r r0 HY HFLE) HKB HG
  HMK
  (pvs_di_kept lyc Sc Hpc Wc m1 mdc1 Lamc peakc cntc failc ranc most own _ o v kids keys _ cap _ Di Lam D0 _ _ ly2 S2 Hp2
     W2 mem2 md2 k1 HAR1 HLG HCONT1 HPL HPERM HJ1)
  HAR2
  (pvs_new_apart lyc Sc Hpc Wc m1 mdc1 Lamc peakc cntc failc ranc most own regs0 e v _ _ _ ly2 S2 Hp2 W2 mem2 md2 k1
     HAR1 HLG HPLAT Hvw HJ1 HvFP)).
match type of OUT with ?A -> _ => assert (HKC : A) end.
{ intros Lam2 peak2 cnt2 fail2 ran2 HLG2 HKL HLAM2 HC2. rewrite <- Hrest1 in HC2.
  apply (HKEPT WR regs0 e q v text len tb d lyc Sc Hpc Wc m1 mdc1 (pc + 1) Lamc peakc cntc failc ranc most own STK_grow
    (spZ regs1) (PI_FRAME + e) FP1 [] ly2 S2 Hp2 W2 mem2 md2 k1 (pc + 1) Lam2 peak2 cnt2 fail2 ran2 most own [] HCUR1
    HJ1 HX).
  - rewrite EPF. lia.
  - rewrite Fsp. lia.
  - rewrite Fsp, EPF. lia.
  - rewrite Eslo. lia.
  - rewrite Eshi. lia.
  - exact (pvs_home_call lyc Sc Hpc Wc m1 Lamc peakc cntc failc ranc most own text len HLG HHOME).
  - exact (pvs_blk_kept _ 0 0 v kids keys _ _ kb yb lyc Sc Hpc Wc m1 mdc1 Lamc peakc cntc failc ranc most own _ _ ly2
      S2 Hp2 W2 regs2 mem2 md2 k1 text len o cap eq_refl eq_refl HG HAR1 HJ1 Hlenpos HtFP HvFP HtS HvS).
  - exact HtFP.
  - intros a Ha Hq1. exact (pvs_shadow_off _ a (HFPapp _ Hq1) ltac:(lia) eq_refl).
  - intros a Ha Hq1. exact (pvs_shadow_off _ a (HFPapp _ Hq1) ltac:(lia) eq_refl).
  - intros Hs. unfold YI16.sink_open_fp, YI16.in_fp in Hs. destruct Hs as (r1 & Hr1 & H0).
    pose proof (HFPlow 0 (ex_intro _ r1 (conj Hr1 H0))). lia.
  - right. split; [reflexivity|]. intros a Ha Hq1. pose proof (HFPlow a Hq1). lia.
  - exact HLG2.
  - exact HC2.
  - left. reflexivity.
  - intros a k' Hin Hh. apply (HKL a k' Hin). intros Hs.
    assert (Hk' : 0 < k') by exact (pvs_sblk_pos o kids keys cap a k' Hs).
    assert (RA : k' + cf_head <= req_size (k' + cf_head)) by (apply pvs_req_ge; lia).
    destruct Hh as [Hh|Hh].
    + exact (HtS a k' text Hs ltac:(lia) ltac:(lia)).
    + exact (HvS a k' v Hs ltac:(lia) ltac:(lia)).
  - exact Hsq.
  - exact Hqe.
  - exact HLAM2.
  - exact HAR1. }
specialize (OUT HKC ltac:(rewrite HFRS1; reflexivity)).
destruct OUT as [(Ha0 & HMN2 & f' & cap' & kids' & keys' & ok0' & tr0' & D0' & Lam' & peak' & cnt' & fail'
  & ran' & Ef & HCUR2 & Hncap' & HCONT2 & HDEP2 & HAP2 & HPERM2 & HFU2 & HEQ2 & HLED2 & HBM2 & HPOSB2 & HLIVE2 & HBB2
  & HOK2 & HLS2 & HROOM2 & HGR2 & Hcap2 & HNC2 & af' & HFORD2 & HFLE2) | (Ha0 & HMN2 & HPOST)].
- (* a0 = 0: 0x87e18 `beqz a0` taken, back to the loop body at PI_O_BODY with N' = length r0 < N *)
  apply (pvs_tail (YCbqGwild.wbudget CW 0) fx0 ly S Hp W mem md regs0 e q v _ ly2 S2 Hp2 W2 mem2 md2 k regs2 WS0 HJ2
    (or_introl Ha0)).
  + intros _ regs' md' k' HJ' HK'.
    assert (HK3 : forall r', In r' pvs_CS -> getr regs' r' = getr regs1 r')
      by (intros r' Hr'; rewrite (HK' r' Hr'); exact (HK2 r' Hr')).
    assert (HN' : (length r0 < N)%nat)
      by exact (Nat.lt_le_trans _ _ _ Hr0r (Nat.le_trans _ _ _ (Nat.le_succ_diag_r _) HN)).
    apply (HBODY (length r0) HN' fx fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most
      own kr ly2 S2 Hp2 W2 mem2 md' k' regs' WS0 HJ' HWS).
    unfold pi_body_pre.
    split; [exact Hfp|]. split; [exact Hent|]. split; [exact HMN2|].
    split; [exact (pvs_frame_call regs0 regs1 regs' W mem Wc m1 W2 mem2 e q v FP1 Hfr1 HK3 HX HFPbelow)|].
    split; [exact (pvs_cs_regs regs1 regs' q v o HK3 Hrg1)|].
    split; [exact (pvs_rb_call regs1 regs' Wc m1 W2 mem2 v e FP1 Hrb1 He0 HK3 HX HFPbelow)|].
    split; [rewrite (HK3 21%bv) by (cbn; tauto); exact R21|].
    exists f', (Nat.succ n), cap', (acc ++ [(nm, t)]), kids', keys', Di, (pc + 1), ok0', tr0', D0', Lam', peak', cnt',
      fail', ran'.
    rewrite Hrest1.
    split; [exact HCUR2|]. split; [lia|].
    exact (conj Hncap' (conj HCONT2 (conj HDEP2 (conj HAP2 (conj HPERM2 (conj HFU2 (conj HEQ2 (conj HLED2 (conj HBM2
      (conj HPOSB2 (conj HLIVE2 (conj HBB2 (conj HOK2 (conj HLS2 (conj HROOM2 (conj HGR2 (conj Hcap2 (conj HNC2
      (ex_intro _ af' (conj HFORD2 HFLE2)))))))))))))))))))).
  + intros Hm1. exfalso. rewrite Ha0 in Hm1. exact (pvs_w64_ne Hm1).
- (* a0 = -1: 0x87e18 `beqz a0` not taken, 0x87e1c `j PI_O_EPI` with the refusal post *)
  apply (pvs_tail (YCbqGwild.wbudget CW 0) fx0 ly S Hp W mem md regs0 e q v _ ly2 S2 Hp2 W2 mem2 md2 k regs2 WS0 HJ2
    (or_intror Ha0)).
  + intros Hm0. exfalso. rewrite Ha0 in Hm0. exact (pvs_w64_ne (eq_sym Hm0)).
  + intros _ regs' md' k' HJ' HK'.
    assert (HK3 : forall r', In r' pvs_CS -> getr regs' r' = getr regs1 r')
      by (intros r' Hr'; rewrite (HK' r' Hr'); exact (HK2 r' Hr')).
    apply (HEPI (YCbqGwild.wbudget CW 0) fx fx0 ly S Hp W mem md regs0 e q v _ ly2 S2 Hp2 W2 mem2 md' k' regs' (-1) WS0
      HJ' HWS).
    unfold pi_epi_pre.
    split; [exact Hfp|]. split; [exact HMN2|].
    split; [exact (pvs_frame_call regs0 regs1 regs' W mem Wc m1 W2 mem2 e q v FP1 Hfr1 HK3 HX HFPbelow)|].
    split; [rewrite (HK3 21%bv) by (cbn; tauto); exact R21|].
    split; [apply pvs_post_stable|].
    intros regs'' H10''. exact (HPOST regs'' md' H10'').
Qed.
Lemma pvs_core : forall (fx0 : YK11.FPState) ly S Hp (W : world SEGS) mem md ch CTX (regs0 : bvmap 5 word) e q v
  (o : bool) text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc (Wc : world SEGS) memc mdc k
  (regs : bvmap 5 word) WS0,
  pi_ajR (rc := rc) (PIi := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B) B ARx SK WR ly S Hp W mem md regs0 d e
    q v lyc Sc Hpc Wc memc mdc k WS0 -> YCbqGwild.wbudget CW 0 WS0 ->
  pv_sep_pre (fx := fx) (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing)
    (PA := PI_prog_B) B fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc k regs N CTX0 CW ->
  pi_goalR (fx := fx) (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing) (PA := PI_prog_B)
    B ARx SK WR fx0 ly S Hp W mem md regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr
    PV_O_SEP Wc memc mdc regs CW.
Proof.
intros fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc
  k regs WS0 HJw HWS HPRE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pvs_stk_nonneg as HSTK.
destruct HPRE as (Hfp & Hent & HMN & Hfr & Hrg & Hrb & R21 & f & n & cap & acc & kids & keys & Di & nm & t & r & pc & ok0
  & tr0 & D0 & Lamc & peakc & cntc & failc & ranc & Hncap & HCONT & HDEP & HAP & HPERM & HRUN & HLED & HBM & HPOSB
  & HLIVE & HBB & HOK & HLS & HROOM & HCUR & HY & HN & HFU & HRM & HGR & Hcapn & HNC & af1 & HFORD & HFLE).
(* THE BUDGETED JOURNAL, at the walk's relation wle' segs RZ_cf: the runs take the empty-budget journal rebased at
   this block's depot; every exit steps back to WS0 (YCbqGwild.ajournal_xw_unbase0R) over HWD: the runs store
   nothing, and grow (unbudgeted) neither *)
unfold pi_ajR in HJw.
pose proof (ajxR_wild HJw) as HWD.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARx WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw)
  as HJ.
pose proof Hrg as (R9 & R19 & R18 & R8 & R20 & R26 & R27 & R25 & R23).
pose proof HCUR as (HIN & HRA & HSRC & HHOME & HPLAT & HRAV & HLG & HCNT).
pose proof HIN as (Vp & Ve & Vdp & Hrw & Hq8 & Ht0 & Htl & Hple & Hlen & HG & Hdqt & Hd032).
pose proof Hent as (Emn & ELC1 & ELC2 & Ein & Ecl & Ecur & Echn & Epart & E10 & E11 & E12 & Egp & Etp & RDP & Eplt
  & Enth & Eroom & Ech0 & Efrm & Erod & EENT).
pvs_split EENT.
pose proof RDP as (_ & _ & _ & _ & IN0 & Hfwin & Hsq & Hqe & _ & _ & _ & RDT).
pvs_split RDT.
match goal with H : prhPv_node _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HPV end.
match goal with H : q + 24 <= v \/ v + 56 <= q |- _ => rename H into Hqv end.
match goal with H : 0 < len -> text + len <= v \/ v + 56 <= text |- _ => rename H into Htv end.
match goal with H : v + 56 <= spZ regs0 \/ spZ regs0 + e <= v |- _ => rename H into Hvw end.
match goal with H : (d <= PjGrammar.MAXD)%nat |- _ => rename H into Hdm end.
pose proof HSRC as (HGt & Ht4 & Htc & Htam & Htra & _). rewrite Hlen in Htc, Htam, Htra.
pose proof Hfr as (Fsp & F3 & F4 & _).
pose proof HJ as HJ0.
pose proof HJ0 as (HARc & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
assert (Hq0 : YM05.alloc_ceiling <= q) by lia.
assert (Hqb : 4096 <= q <= 2 ^ 47 - 24) by lia.
assert (Hp1b : 4096 <= pc <= 2 ^ 47 - 2) by lia.
assert (Hedb : 4096 <= text + len <= 2 ^ 47 - 1) by lia.
assert (HQ63 : 0 <= q < 2 ^ 63) by lia.
assert (HQ63a : 0 <= q + 8 < 2 ^ 63) by lia.
assert (HQ63b : 0 <= q + 16 < 2 ^ 63) by lia.
assert (HSB : 0 <= SHADOW_OFF < 2 ^ 32) by (unfold SHADOW_OFF; lia).
unfold pi_goalR, cfg_at. clear HJw.
destruct (Z_lt_dec pc (text + len)) as [Hlt | Hge].
- (* THE CURSOR IS ON A BYTE c *)
  destruct (skipn (Z.to_nat (pc - text)) tb) as [|c r0] eqn:HSK.
  { exfalso. pose proof (length_skipn (Z.to_nat (pc - text)) tb) as HLn0. rewrite HSK in HLn0. cbn [length] in HLn0. lia. }
  assert (Hck : nth (Z.to_nat (pc - text)) tb 0 = c) by (apply (pvs_nth_skipn tb _ c r0); exact HSK).
  destruct (HGt (Z.to_nat (pc - text)) ltac:(lia)) as [Vc0 Hc256].
  rewrite Hck in Vc0, Hc256.
  replace (text + Z.of_nat (Z.to_nat (pc - text))) with pc in Vc0 by lia.
  assert (Hyc : rest_atR tb text pc = c :: r0) by (unfold rest_atR; exact HSK).
  rewrite Hyc in HY. symmetry in HY.
  destruct (Z.eq_dec c 44) as [Hc44 | Hn44].
  + (* ',' : the comma arm and the grow call *)
    clear Hck. subst c.
    pose proof (pvs_st_ok (fx := fx) Wc memc regs q pc (text + len) 44 o true true (PIAT PV_O_SEP)
      R9 R8 R20 R26 R27 R25 R23 R18 Hqb Hq8 Hp1b Hedb Hc256 ltac:(intros _; lia) Vp Ve
      ltac:(intros _ x Hx; apply Hrw; lia) ltac:(intros _; exact Vc0)) as HS.
    remember (Eimg (rc := rc) (L := B_prog_listing) (PI := PI_prog_B)
               (Ereg regs [Z_to_bv 64 pc; Z_to_bv 64 (text + len); Z_to_bv 64 44])) as E eqn:HE in HS.
    assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
    assert (E9 : ew E 9 = Z_to_bv 64 q) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
    assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
    assert (E32 : ew E 32 = Z_to_bv 64 pc) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
    assert (E33 : ew E 33 = Z_to_bv 64 (text + len)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
    assert (E34 : ew E 34 = Z_to_bv 64 44) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
    assert (U9 : bv_unsigned (ew E 9) = q) by (rewrite E9; apply unsigned_lit_small; lia).
    assert (U32 : bv_unsigned (ew E 32) = pc) by (rewrite E32; apply unsigned_lit_small; lia).
    assert (U33 : bv_unsigned (ew E 33) = text + len) by (rewrite E33; apply unsigned_lit_small; lia).
    assert (U34 : bv_unsigned (ew E 34) = 44) by (rewrite E34; apply unsigned_lit_small; lia).
    assert (E2 : ew E 2 = getr regs 2) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
    assert (E3 : ew E 3 = getr regs 3) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
    assert (E4 : ew E 4 = getr regs 4) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
    assert (E19 : ew E 19 = Z_to_bv 64 v) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
    assert (E21 : ew E 21 = Z_to_bv 64 (-1)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
    assert (E22 : ew E 22 = getr regs 22) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 22 22%bv eq_refl)).
    assert (E24 : ew E 24 = getr regs 24) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 24 24%bv eq_refl)).
    assert (W16 : Z_to_bv 64 (bv_unsigned (ew E 9) + 16) = Z_to_bv 64 (q + 16)) by (rewrite U9; reflexivity).
    assert (W8 : Z_to_bv 64 (bv_unsigned (ew E 9) + 8) = Z_to_bv 64 (q + 8)) by (rewrite U9; reflexivity).
    clear HE.
    assert (SHOK : sh_ok SEGS pvs_Bx (pvs_SH true) E (rdW Wc memc)).
    { unfold pvs_SH. cbn [app]. constructor; [|constructor; [|constructor]].
      - apply (shent_ok_of_range SEGS (w_H Wc) memc E pvs_Bx 32 text len pc 0 1 Htra);
        [unfold pvs_Bx; rewrite (U_atom E 26 SHADOW_OFF E26) by (unfold SHADOW_OFF; lia); reflexivity
        | rewrite (U_atom E 32 pc E32) by lia; reflexivity | lia | lia
        | intros x Hx; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam; unfold SHADOW_OFF; lia].
      - apply (shent_ok_of_range SEGS (w_H Wc) memc E pvs_Bx 9 q 24 q 0 24 HRA);
        [unfold pvs_Bx; rewrite (U_atom E 26 SHADOW_OFF E26) by (unfold SHADOW_OFF; lia); reflexivity
        | rewrite (U_atom E 9 q E9) by lia; reflexivity | lia | lia | intros x Hx; unfold SHADOW_OFF; lia]. }
    change (w64 (VAL A_TEXT + PIAT PV_O_SEP)) with (Z_to_bv 64 (VAL A_TEXT + PIAT PV_O_SEP)).
    paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_EPI).
    { unfold ss_pvs; cbn [ss_mem]; unfold pvs_smem; cbn [app].
      apply awr_ok_cons_ro; [cbn; lia|].
      apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (q - (spZ regs0 + e)));
      [reflexivity | cbn [ew ewset extK Nat.eqb]; rewrite U9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
      apply awr_ok_nil. }
    clear HF HG.
    rename HFr into HFr1.
    psrr_branch_tok RUNTO BR HS SHOK BAND_SPAN.
    * (* 0x87dd4 `bgeu p, end` taken: impossible, the cursor is on a byte *)
      exfalso. rewrite branch_geu_U, !U_SOff in Hc. cbn [ew ewset extK Nat.eqb] in Hc.
      rewrite U32, U33, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
      destruct (Z.ltb_spec pc (text + len)); [discriminate Hc | lia].
    * clear Hc.
      paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_EPI).
      { unfold ss_pvs; cbn [ss_mem]; unfold pvs_smem; cbn [app].
        apply awr_ok_cons_ro; [cbn; lia|].
        apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (q - (spZ regs0 + e)));
        [reflexivity | cbn [ew ewset extK Nat.eqb]; rewrite U9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
        apply awr_ok_nil. }
      clear HF HG. rename HFr into HFr2.
      psrr_branch_tok RUNTO BR HS SHOK BAND_SPAN.
      -- (* 0x87df4 `bne c, 44` taken: impossible, c is ',' *)
         exfalso. rewrite branch_ne_U, U_lit, U_SOff in Hc by lia. cbn [ew ewset extK Nat.eqb] in Hc.
         rewrite U34, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia). discriminate Hc.
      -- clear Hc.
         paj_run_tok_x_inv RUNI HS HJ SHOK HMN BAND_SPAN.
         { unfold ss_pvs; cbn [ss_mem]; unfold pvs_smem; cbn [app].
           apply awr_ok_cons_ro; [cbn; lia|].
           apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (q - (spZ regs0 + e)));
           [reflexivity | cbn [ew ewset extK Nat.eqb]; rewrite U9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
           apply awr_ok_nil. }
         clear HF HG. rename HFr into HFr3.
         prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
         prreg HS (10%bv : bv 5) Q10. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
         prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
         prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
         prreg HS (27%bv : bv 5) Q27.
         (* AT THE grow CALL (0x87e14): `sd a0, 0(s1)` stored p + 1 into q's p field (region 9, chunk 0), a0 := s3 = v,
            ra := the return site; every other register is the block's *)
         pose proof Hfr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fwin & Fret & He0 & He16).
         pose proof pvs_stk_grow as HSTKG. pose proof pvs_stk_pi as HSTKP. pose proof pvs_stk_grow0 as HSTKG0.
         assert (EPF : PI_FRAME = 144) by reflexivity.
         assert (Rsp : spZ (ms_regs ms1) = spZ regs) by (unfold spZ; rewrite Q2, E2; reflexivity).
         assert (K3 : getr (ms_regs ms1) 3 = getr regs 3) by (rewrite Q3, E3; reflexivity).
         assert (K4 : getr (ms_regs ms1) 4 = getr regs 4) by (rewrite Q4, E4; reflexivity).
         assert (Ra0 : getr (ms_regs ms1) 10 = w64 v) by (rewrite Q10, E19; reflexivity).
         assert (R21' : getr (ms_regs ms1) 21 = w64 (-1)) by (rewrite Q21, E21; reflexivity).
         assert (Hrg1 : pi_regs (ms_regs ms1) q v o).
         { unfold pi_regs.
           split; [rewrite Q9, E9; reflexivity|]. split; [rewrite Q19, E19; reflexivity|].
           split; [rewrite Q18; reflexivity|]. split; [rewrite Q8, U9; reflexivity|].
           split; [rewrite Q20, U9; reflexivity|]. split; [rewrite Q26, E26; reflexivity|].
           split; [rewrite Q27, (hd_alu_shx _ _ q SHADOW_OFF E9 E26 HQ63 HSB); unfold pi_sh, w64; reflexivity|].
           split; [rewrite Q25, (hd_alu_shx _ _ (q + 16) SHADOW_OFF W16 E26 HQ63b HSB); unfold pi_sh, w64; reflexivity|].
           rewrite Q23, (hd_alu_shx _ _ (q + 8) SHADOW_OFF W8 E26 HQ63a HSB); unfold pi_sh, w64; reflexivity. }
         (* the three runs wrote only q's p field *)
         assert (AGR : pi_agr (pvs_Fq q) (rdW Wc memc) (rdW Wc (ms_mem ms1))).
         { assert (WQ : forall E0 rs m m', frame_of E0 rs m m' -> bv_unsigned (ew E0 9) = q ->
             rs = pvs_smem true true -> pi_agr (pvs_Fq q) m m').
           { intros E0 rs m m' HFx U0 ->. apply (pvs_frame_q E0 _ m m' q HFx). intros a (r1 & Hin & Hr).
             vm_compute in Hin. repeat (destruct Hin as [<- | Hin];
               [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U0 in Hr; lia|]). destruct Hin. }
           apply (pvs_agr_trans _ _ (rdW Wc (ms_mem ms0))).
           - apply (pvs_agr_trans _ _ (rdW Wc (ms_mem ms))).
             + exact (WQ _ _ _ _ HFr1 U9 eq_refl).
             + apply (WQ _ _ _ _ HFr2); [cbn [ew ewset extK Nat.eqb]; exact U9 | reflexivity].
           - apply (WQ _ _ _ _ HFr3); [cbn [ew ewset extK Nat.eqb]; exact U9 | reflexivity]. }
         (* the stored cursor: q's p field reads p + 1 and stays writable *)
         lazymatch type of HS with st_ok _ ?Ec _ _ =>
           assert (HQR : region_ok SEGS Ec (rdW Wc (ms_mem ms1))
             (YP09.mkRegion (Some 9%nat) 0 16 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 32 1)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))]))
         end.
         { pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & Hrs & _). cbn [ss_mem setpc] in Hrs.
           apply Forall_inv_tail in Hrs. apply Forall_inv in Hrs. exact Hrs. }
         assert (VQ : val_mem SEGS (rdW Wc (ms_mem ms1)) q 8 (pc + 1)).
         { replace q with (q + 0) by lia.
           apply (pi_field SEGS _ _ 9%nat q _ 0 16 0 8 0 8 (SOff 32 1) (pc + 1) HQR);
             [cbn [ew ewset extK Nat.eqb]; exact U9 | cbn; tauto | | lia | lia].
           rewrite denot_lit_U, U_SOff. cbn [ew ewset extK Nat.eqb]. rewrite U32, zcanon_id by (unfold M64; lia).
           reflexivity. }
         assert (WRq : forall x, q <= x < q + 8 -> writable_at SEGS (rdW Wc (ms_mem ms1)) x).
         { intros x Hx. destruct HQR as (_ & _ & Hwr & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hwr.
           cbn [ew ewset extK Nat.eqb] in Hwr. rewrite U9 in Hwr. replace x with (q + (x - q)) by lia. apply Hwr. lia. }
         pose proof HJ as (HAR1 & _).
         assert (HCNT1 : cntc + 2 * Z.of_nat (length (rest_atR tb text (pc + 1))) + 2 < 2 ^ 64 - 1).
         { rewrite (pvs_rest_next tb text pc 44 r0 ltac:(lia) Hyc). rewrite Hyc in HCNT. cbn [length] in HCNT. lia. }
         assert (Hv56c : v + 56 <= YM05.alloc_ceiling)
           by exact (pvs_v_low lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc most own regs0 e v HARc HLG HPLAT Hvw).
         assert (HCUR1 := pvs_cur_store regs0 e q v text len tb d lyc Sc Hpc Wc memc (ms_mem ms1) mdc pc Lamc peakc cntc
           failc ranc most own HARc HCUR AGR VQ WRq Hlt Hq0 ltac:(lia) Hqv ltac:(pose proof HPV as (Hv0 & _); lia)
           ltac:(lia) HCNT1).
         pose proof HLED as (_ & _ & _ & HPL & _).
         assert (HFDi : forall x, (exists b, In b (pi_sblk o kids keys cap ++ Di) /\ pj_holdsR b x) -> pvs_Fq q x).
         { intros x ([a0 k0] & Hb & Hx). unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
           assert (HinL : In (a0, k0) Lamc).
           { apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left.
             apply (Permutation_in _ (Permutation_sym HPERM)). exact Hb. }
           destruct (cl_D_bounds B ARx cf_head LAWS lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc most own a0 k0 HARc
             HLG HinL).
           unfold pvs_Fq. lia. }
         assert (HCONT1 := pvs_cont_agr (pvs_Fq q) _ _ _ o v kids keys _ cap _ Di HCONT AGR
           ltac:(intros x Hx; unfold pvs_Fq; pose proof HPV as (Hv0 & _); lia) HFDi).
         (* The batch kit's invariants across the store: it writes q's p field, outside pi_cont's read bytes *)
         assert (HAGU : pj_agreeR SEGS (rdW Wc memc) (rdW Wc (ms_mem ms1)) (pvm_cont_ufoot o v kids keys (Nat.succ n) Di))
           by exact (pvs_ufoot_agr (pvs_Fq q) _ _ o v kids keys (Nat.succ n) cap Di AGR Hncap
             ltac:(intros x Hx; unfold pvs_Fq; pose proof HPV as (Hv0 & _); lia) HFDi).
         assert (HNC1 := pvm_ncaps_frame (w_H Wc) memc (rdW Wc (ms_mem ms1)) _ o v kids keys _ cap _ Di HCONT HNC HAGU).
         assert (HFORD1 := pvm_forder_frame _ _ _ (prh_lin Lamc) o v kids keys _ Di _ af1 HFORD (fun x k0 H => H) HAGU).
         assert (Hfr1 : pi_frame (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) regs0 (ms_regs ms1) W mem Wc
           (ms_mem ms1) e q v).
         { apply (pi_frame_kept (pvs_Fq q) regs0 regs (ms_regs ms1) W mem Wc memc (ms_mem ms1) e q v Hfr Rsp K3 K4 AGR).
           - intros a Ha. unfold pvs_Fq. lia.
           - intros a Ha Hn. unfold pvs_Fq. split; [lia|]. intros Hq. apply Hn. exists (q, q + 8). cbn. split; [tauto | lia]. }
         assert (Hrb1 : pi_regs_body (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) (ms_regs ms1) Wc (ms_mem ms1) v).
         { apply (pvs_rb_regs regs); [rewrite Q2, E2; reflexivity | rewrite Q22, E22; reflexivity
                                     | rewrite Q24, E24; reflexivity |].
           apply (pvs_rb_store regs Wc memc (ms_mem ms1) v q Hrb AGR); [rewrite Fsp, EPF; lia | lia]. }
         pose proof HCUR1 as (_ & HRA1 & HSRC1 & HHOME1 & HPLAT1 & HRAV1 & HLG1 & _).
         destruct (pvs_kb lyc Sc Hpc Wc (ms_mem ms1) _ Lamc peakc cntc failc ranc most own _ o v kids keys _ cap _ Di HAR1
           HLG1 HCONT1) as (kb & yb & Hkl & Hkb & Hyb).
         (* the frame-pointer chain the call sees (PItems_body_key.v's skip_ws call, same construction): s0 = q + 16, whose
            two words below are the end and the stored cursor p + 1, below q, so the chain stops there *)
         assert (Us0 : s0Z (ms_regs ms1) = q + 16) by (unfold s0Z; rewrite Q8, U9; apply unsigned_lit_small; lia).
         assert (Ve1 : val_mem SEGS (rdW Wc (ms_mem ms1)) (q + 8) 8 (text + len))
           by (apply (pi_val_agr SEGS (pvs_Fq q) _ _ _ _ _ AGR); [intros kk Hk; unfold pvs_Fq; lia | exact Ve]).
         assert (HCH : exists ch1, achain lyc (aview SEGS (w_H Wc) (ms_mem ms1)) (spZ regs) (q + 16) ch1).
         { destruct (Z_lt_le_dec (q + 16) (ly_top lyc - 16)) as [Hlt16 | Hge16].
           - exists [(q + 16, text + len, pc + 1)]. right.
             split; [lia|]. split; [exact Hlt16|]. split; [rewrite Z.add_mod, Hq8 by lia; reflexivity|].
             split.
             + cbn [fpchain]. split; [reflexivity|]. split; [rewrite Z.add_mod, Hq8 by lia; reflexivity|].
               split; [replace (q + 16 - 8) with (q + 8) by lia; apply (pvs_rdword_of_val (w_H Wc) (ms_mem ms1) (q + 8) (text + len));
                 [exact Ve1 | lia]|].
               split; [replace (q + 16 - 16) with q by lia; apply (pvs_rdword_of_val (w_H Wc) (ms_mem ms1) q (pc + 1));
                 [exact VQ | lia]|].
               split; [lia|].
               unfold bad_next. replace (pc + 1 <=? q + 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
             + constructor; [cbn [fst]; lia | constructor].
           - exists []. left. split; [right; left; lia | reflexivity]. }
         destruct HCH as (ch1 & HCH).
         pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
         assert (Hv56 : v + 56 <= YM05.alloc_ceiling)
           by exact (pvs_v_low lyc Sc Hpc Wc (ms_mem ms1) _ Lamc peakc cntc failc ranc most own regs0 e v HAR1 HLG1 HPLAT1
             Hvw).
         (* THE LIVE COUNTS AT THE grow CALL (form (b)): grow's two peak premises are over its own granted events
            prhPg_evs .. [], which are rd_hevs of its granted trace (PIL_HEAD, PRH_FnReader.v prhPg_evs_model); they come
            from pi_ent's over the whole call's granted events at the block's pi_live (PItems_value_model.v pvm_lc_call),
            grow's granted trace being the head of the comma continuation's (PItems_body_loop.v pil_gt_split) *)
         assert (LCG : forall (f0 : Z -> bool) b,
           Z.of_nat (PresetRun.pkR f0 (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
             (PresetReqAt.rd_hevs (prhPi_gtrace d o (rest_atR tb text p)))) <= b ->
           Z.of_nat (PresetRun.pkR f0 (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc))
             (prhPg_evs ((if o then 6 else 5) =? 6) (Z.of_nat (Nat.succ n)) (Z.of_nat cap) [])) <= b).
         { intros f0 b Hb.
           replace ((if o then 6 else 5) =? 6) with o by (destruct o; reflexivity).
           rewrite (prhPg_evs_model o (Z.of_nat (Nat.succ n)) (Z.of_nat cap) [] ltac:(clear; lia) ltac:(clear; lia)
             PIL_HEAD).
           destruct f as [|f']; [clear - HFU; lia|].
           apply (pvm_lc_call f0 _ _ d o (rest_atR tb text p) ok0 tr0
             (jrl prh_jr_strtod (Nat.succ f') (Nat.succ d) o (Nat.succ n) cap (rev (acc ++ [(nm, t)])) r0) _ b
             (pvs_run_comma d o _ ok0 tr0 (Nat.succ f') n cap acc nm t r r0 HRUN HY) HOK HLIVE); [|exact Hb].
           exists (snd (fst (pi_jrb f' (Nat.succ d) o (Nat.succ n) (pil_gcap (Nat.succ n) cap) (rev (acc ++ [(nm, t)]))
             r0 []))).
           exact (pil_gt_split f' (Nat.succ d) o (Nat.succ n) cap (rev (acc ++ [(nm, t)])) r0). }
         (* THE HULL BUDGET AT THE grow CALL (route (b)): grow's all-granted events are the block's next ones after the
            prefix's (PItems_value_model.v pvm_gt_pref, PItems_body_loop.v pil_gt_split), so pi_ent's budget over the
            whole call's all-granted events pays it at the block (PItems_posb.pi_posb_budget) *)
         assert (HBG : PresetHullBudget.hull_budget Sc
           (prhPg_evs ((if o then 6 else 5) =? 6) (Z.of_nat (Nat.succ n)) (Z.of_nat cap) [])).
         { replace ((if o then 6 else 5) =? 6) with o by (destruct o; reflexivity).
           rewrite (prhPg_evs_model o (Z.of_nat (Nat.succ n)) (Z.of_nat cap) [] ltac:(clear; lia) ltac:(clear; lia)
             PIL_HEAD).
           destruct f as [|f']; [clear - HFU; lia|].
           destruct (pvm_gt_pref d o (rest_atR tb text p) ok0 tr0
             (jrl prh_jr_strtod (Nat.succ f') (Nat.succ d) o (Nat.succ n) cap (rev (acc ++ [(nm, t)])) r0)
             (pvs_run_comma d o _ ok0 tr0 (Nat.succ f') n cap acc nm t r r0 HRUN HY) HOK) as (Etl & EG).
           rewrite (pil_gt_split f' (Nat.succ d) o (Nat.succ n) cap (rev (acc ++ [(nm, t)])) r0),
             PresetReqAt.rd_hevs_app, <- app_assoc in EG.
           pose proof Hent as HB0. apply pi_ent_hull in HB0. rewrite EG in HB0.
           exact (PItems_posb.pi_posb_budget S Sc tr0 _ _ _ HB0 HPOSB eq_refl). }
         eapply (SRrG_bind SEGS WR (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
         { eapply (aj_call_xW_spR (SK := SK) SEGS B prh_pst ARx LAWS (pa_segs_low (PAImg := PI_prog_B)) WR
             (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc _ _ ms1
             (STK_parse_items (PI := prh_img_B) d + e) (spZ regs0 + e) (rd_fp q v) ly (set_depot (st_depot Sc) S) Hp W
             mem md [] lyc Sc Hpc _ k
             STK_grow (PI_FRAME + e) (pvs_FP1 o v kids keys cap) (- (PI_FRAME + e)) _ ch1
             (fQmn (rc := rc) (L := B_prog_listing) (PA := PI_prog_B) (ms_mem ms1)
               (pil_gpost (rc := rc) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing)
                (PA := PI_prog_B) B (if o then 6 else 5) 0 0 v kids keys (Z.of_nat (Nat.succ n))
                (Z.of_nat cap) kb yb lyc Sc Hpc Wc (ms_mem ms1) Lamc peakc cntc failc ranc most own))
             HS eq_refl HJ).
           - rewrite Rsp, Fsp. lia.
           - rewrite EPF. rewrite Z.mod_opp_l_z; [reflexivity | lia | rewrite Z.add_mod, He16 by lia; reflexivity].
           - rewrite EPF. lia.
           - exact HSTKG0.
           - lia.
           - rewrite EPF. lia.
           - rewrite EPF. rewrite Z.add_mod, He16 by lia; reflexivity.
           - lia.
           - rewrite K3, F3. exact Egp.
           - rewrite K4, F4. exact Etp.
           - exact Q1.
           - apply ret_ok_codeptr_v; [lia | reflexivity].
           - rewrite unsigned_lit_small by (vm_compute; split; [discriminate | reflexivity]). vm_compute. discriminate.
           - replace (spZ regs0 + e + - (PI_FRAME + e)) with (spZ regs) by (rewrite Fsp, EPF; lia). rewrite Us0. exact HCH.
           - intros HAF HWIN. cbn [ss_pc setpc].
             refine (GROW fx most own lyc Sc Hpc Wc (ms_regs ms1) (ms_mem ms1) _ ch1 (PI_FRAME + e)
               v (if o then 6 else 5) 0 0 kids keys (Z.of_nat (Nat.succ n)) (Z.of_nat cap) kb yb Lamc peakc cntc failc ranc
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
             + split; [exact HAF|]. split.
               { apply (pvs_rod_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); [|exact Erod].
                 intros Hs0. unfold YI16.sink_open_fp, YI16.in_fp in Hs0. destruct Hs0 as (r1 & Hr1 & H0).
                 pose proof HPV as (Hv0 & _).
                 cbn [rd_fp In] in Hr1. destruct Hr1 as [<- | [<- | [<- | []]]]; cbn [fst snd] in H0; lia. }
               split; [rewrite Rsp, Fsp, EPF, Eshi; lia|].
               (* fpre's frm_zero at the call (FRM0-ENTRY): the block's own float state, pi_fpok *)
               split; [|exact (proj1 Hfp)].
               (* fpre's return-address bound: the return site PVS_O_GROWR is a text address, below the ceiling *)
               assert (Hr0 : raZ (ms_regs ms1) = VAL A_TEXT + PIAT PVS_O_GROWR)
                 by (unfold raZ; rewrite Q1; vm_compute; reflexivity).
               assert (Hr0v : VAL A_TEXT + PIAT PVS_O_GROWR < 2 ^ 40) by (vm_compute; reflexivity). lia.
             + exact Ecl.
             + exists []. apply achain_low.
               assert (E48 : prh_s0 (PI := prh_img_B) F_grow v = v + 48) by reflexivity. rewrite E48. lia.
             + exact HROOM.
             + exact (LCG _ _ ELC1).
             + exact (LCG _ _ ELC2).
             + exact HBG.
             + exact Ra0.
             + pose proof HPV as (Hv0 & _). lia.
             + pose proof HPV as (_ & Hv8 & _). exact Hv8.
             + pose proof HCONT1 as (Hh & _). exact Hh.
             + pose proof (pvs_nodup_D0 Lam Lamc D0 _ HPL ltac:(pose proof HLG as HN0; apply prh_ledger_nodup in HN0; exact HN0) HPERM) as HND.
               pose proof (pvm_cont_open _ _ o v kids keys _ cap _ Di HCONT1 HAP HND) as (_ & _ & _ & Hsl & _).
               destruct o; exact Hsl.
             + exact HAP.
             + exact HWIN.
             + apply (pvs_at_regs lyc Sc Lamc regs0 (ms_regs ms1) e (PI_FRAME + e) v 56 HPLAT1 Hvw). lia.
             + exact HRAV1.
             + intros _. split; [exact Hkb|]. split; [exact Hkl|]. intros Ho. destruct o; [|discriminate Ho].
               destruct (Hyb eq_refl) as [Hyl Hyb']. split; [exact Hyb' | exact Hyl].
             + exact HLG1.
             + rewrite Hyc in HCNT. cbn [length] in HCNT. lia.
             + intros Heq.
               destruct (pvs_room_grow Sc f (Nat.succ d) o (Nat.succ n) cap (rev (acc ++ [(nm, t)])) r0
                 ltac:(clear -HFU; revert HFU; generalize (length r); intros lr Hlr; lia)
                 (pvs_room_comma Sc f d o n cap acc nm t r r0 HY HRM) Heq) as [Hmx Hlv].
               split; [exact Hmx|].
               (* grow's event list is the model's rd_hevs of its granted trace (PRH_FnReader.prhPg_evs_model) *)
               rewrite Heq. replace ((if o then 6 else 5) =? 6) with o by (destruct o; reflexivity).
               rewrite (prhPg_evs_model o (Z.of_nat cap) (Z.of_nat cap) [] ltac:(clear; lia) ltac:(clear; lia)
                 PIL_HEAD).
               exact Hlv.
           - exact (pvs_fpsub ly S lyc Sc Hpc Wc (ms_mem ms1) Lamc peakc cntc failc ranc most own _ o v kids keys _ cap _ Di
               D0 tr0 (rest_atR tb text p) d q e regs0 HLG1 HCONT1 HPERM HBM). }
         (* BACK FROM grow at the return site (0x87e18): the caller's journal back at its budget WS0 *)
         cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & HX & HP & HK & HMK).
         pose proof (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
           HJ2 HWD) as HJ2w.
         lazymatch goal with |- context [YK11.mkst regs2 ?raw mem2 _] =>
           replace raw with (w64 (VAL A_TEXT + PIAT PVS_O_GROWR)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
         replace (spZ regs0 + e + - (PI_FRAME + e) + (PI_FRAME + e)) with (spZ (ms_regs ms1) + (PI_FRAME + e)) in HJ1
           by (rewrite Rsp, Fsp; lia).
         apply (pvs_grow_post fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr lyc
           Sc Hpc Wc (ms_mem ms1) _ (ms_regs ms1) f n cap acc kids keys Di nm t r r0 pc ok0 tr0 D0 Lamc peakc cntc failc
           ranc af1 kb yb ly2 S2 Hp2 W2 mem2 md2 (k + k1) k1 regs2 WS0 Hfp Hent HMN Hfr1 Hrg1 Hrb1 R21' HCONT1 HDEP HAP
           HPERM HRUN HLED HBM HPOSB HLIVE HBB HOK HLS HCUR1 HCNT ltac:(lia) Hyc HY HN HFU HRM HGR Hcapn HNC1 HFORD1 HFLE
           HAR1 HJ2w HWS HJ1).
         { intros a Ha Hn. apply HX; [rewrite Rsp, Fsp in *; lia | exact Hn]. }
         { exact HP. }
         { exact HK. }
         { exact HMK. }
         { intros _. split; [exact Hkb|]. split; [exact Hkl|]. intros Ho. destruct (Hyb Ho) as [Hyl Hyb'].
           split; [exact Hyb' | exact Hyl]. }
  + (* not ',' : the closer test *)
    pose proof (pvs_st_ok (fx := fx) Wc memc regs q pc (text + len) c o true false (PIAT PV_O_SEP)
      R9 R8 R20 R26 R27 R25 R23 R18 Hqb Hq8 Hp1b Hedb Hc256 ltac:(intros _; lia) Vp Ve
      ltac:(intros X; discriminate X) ltac:(intros _; exact Vc0)) as HS.
    remember (Eimg (rc := rc) (L := B_prog_listing) (PI := PI_prog_B)
               (Ereg regs [Z_to_bv 64 pc; Z_to_bv 64 (text + len); Z_to_bv 64 c])) as E eqn:HE in HS.
    assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
    assert (E2 : ew E 2 = getr regs 2) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
    assert (E3 : ew E 3 = getr regs 3) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
    assert (E4 : ew E 4 = getr regs 4) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
    assert (E9 : ew E 9 = Z_to_bv 64 q) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
    assert (E19 : ew E 19 = Z_to_bv 64 v) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
    assert (E21 : ew E 21 = Z_to_bv 64 (-1)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
    assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
    assert (E32 : ew E 32 = Z_to_bv 64 pc) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
    assert (E33 : ew E 33 = Z_to_bv 64 (text + len)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
    assert (E34 : ew E 34 = Z_to_bv 64 c) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
    assert (U9 : bv_unsigned (ew E 9) = q) by (rewrite E9; apply unsigned_lit_small; lia).
    assert (U32 : bv_unsigned (ew E 32) = pc) by (rewrite E32; apply unsigned_lit_small; lia).
    assert (U33 : bv_unsigned (ew E 33) = text + len) by (rewrite E33; apply unsigned_lit_small; lia).
    assert (U34 : bv_unsigned (ew E 34) = c) by (rewrite E34; apply unsigned_lit_small; lia).
    assert (W16 : Z_to_bv 64 (bv_unsigned (ew E 9) + 16) = Z_to_bv 64 (q + 16)) by (rewrite U9; reflexivity).
    assert (W8 : Z_to_bv 64 (bv_unsigned (ew E 9) + 8) = Z_to_bv 64 (q + 8)) by (rewrite U9; reflexivity).
    clear HE.
    assert (SHOK : sh_ok SEGS pvs_Bx (pvs_SH true) E (rdW Wc memc)).
    { unfold pvs_SH. cbn [app]. constructor; [|constructor; [|constructor]].
      - apply (shent_ok_of_range SEGS (w_H Wc) memc E pvs_Bx 32 text len pc 0 1 Htra);
        [unfold pvs_Bx; rewrite (U_atom E 26 SHADOW_OFF E26) by (unfold SHADOW_OFF; lia); reflexivity
        | rewrite (U_atom E 32 pc E32) by lia; reflexivity | lia | lia
        | intros x Hx; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam; unfold SHADOW_OFF; lia].
      - apply (shent_ok_of_range SEGS (w_H Wc) memc E pvs_Bx 9 q 24 q 0 24 HRA);
        [unfold pvs_Bx; rewrite (U_atom E 26 SHADOW_OFF E26) by (unfold SHADOW_OFF; lia); reflexivity
        | rewrite (U_atom E 9 q E9) by lia; reflexivity | lia | lia | intros x Hx; unfold SHADOW_OFF; lia]. }
    change (w64 (VAL A_TEXT + PIAT PV_O_SEP)) with (Z_to_bv 64 (VAL A_TEXT + PIAT PV_O_SEP)).
    paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_EPI).
    { unfold ss_pvs; cbn [ss_mem]; unfold pvs_smem; cbn [app];
      repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
    assert (MEQ1 : rdW Wc (ms_mem ms) = rdW Wc memc).
    { apply (pvs_meq_of _ _ _ _ _ HFr). intros r1 Hin. vm_compute in Hin.
      repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
    clear HF HFr HG.
    psrr_branch_tok RUNTO BR HS SHOK BAND_SPAN.
    * (* 0x87dd4 `bgeu p, end` taken: impossible, the cursor is on a byte *)
      exfalso. rewrite branch_geu_U, !U_SOff in Hc. cbn [ew ewset extK Nat.eqb] in Hc.
      rewrite U32, U33, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
      destruct (Z.ltb_spec pc (text + len)); [discriminate Hc | lia].
    * clear Hc.
      paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_EPI).
      { unfold ss_pvs; cbn [ss_mem]; unfold pvs_smem; cbn [app];
        repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
      assert (MX2 : rdW Wc (ms_mem ms0) = rdW Wc (ms_mem ms)).
      { apply (pvs_meq_of _ _ _ _ _ HFr). intros r1 Hin. vm_compute in Hin.
        repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
      assert (MEQ2 : rdW Wc (ms_mem ms0) = rdW Wc memc) by (rewrite MX2; exact MEQ1).
      clear HF HFr HG.
      psrr_branch_tok RUNTO BR HS SHOK BAND_SPAN.
      -- (* 0x87df4 `bne c, 44` taken: to the closer test at PI_O_CLS1 *)
         rewrite branch_ne_U, U_lit, U_SOff in Hc by lia. cbn [ew ewset extK Nat.eqb] in Hc.
         rewrite U34, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia). clear Hc.
         destruct o.
         ++ paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_EPI).
            { unfold ss_pvs; cbn [ss_mem]; unfold pvs_smem; cbn [app];
              repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
            assert (MX3 : rdW Wc (ms_mem ms1) = rdW Wc (ms_mem ms0)).
            { apply (pvs_meq_of _ _ _ _ _ HFr). intros r1 Hin. vm_compute in Hin.
              repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
            assert (MEQ3 : rdW Wc (ms_mem ms1) = rdW Wc memc) by (rewrite MX3; exact MEQ2).
            clear HF HFr HG.
            psrr_branch_tok RUNTO BR HS SHOK BAND_SPAN.
            ** (* 0x87f54 `bne closer, c` taken: the byte is not the closer, the call refuses at PI_O_EPI *)
               rewrite branch_ne_U, U_lit, U_SOff in Hc by lia. cbn [ew ewset extK Nat.eqb] in Hc.
               rewrite U34, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia).
               assert (Hcl : c <> 125) by (destruct (Z.eqb_spec 125 c); [discriminate Hc | lia]). clear Hc.
               paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_EPI).
               { unfold ss_pvs; cbn [ss_mem]; unfold pvs_smem; cbn [app];
                 repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
               assert (MX4 : rdW Wc (ms_mem ms2) = rdW Wc (ms_mem ms1)).
               { apply (pvs_meq_of _ _ _ _ _ HFr). intros r1 Hin. vm_compute in Hin.
                 repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
               assert (MEQ4 : rdW Wc (ms_mem ms2) = rdW Wc memc) by (rewrite MX4; exact MEQ3).
               clear HF HFr HG.
               prreg HS (21%bv : bv 5) Q21. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
               prreg HS (4%bv : bv 5) Q4.
               pmkst HS.
               lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
                 replace pcw with (w64 (VAL A_TEXT + PIAT PI_O_EPI)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
               apply (pvs_epi (YCbqGwild.wbudget CW 0) fx0 ly S Hp W mem md regs0 e q v _ lyc Sc Hpc Wc memc _ _ k WS0
                 regs _ (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 _ _ HJ HWD) HWS Hfp Hfr MEQ4 HMN).
               --- cbn [ms_regs]; unfold spZ in *; rewrite Q2, E2; reflexivity.
               --- cbn [ms_regs]; rewrite Q3, E3; reflexivity.
               --- cbn [ms_regs]; rewrite Q4, E4; reflexivity.
               --- cbn [ms_regs]; rewrite Q21, E21; reflexivity.
               --- apply pvs_post_stable.
               --- intros regs'' H10''.
                   exact (pvs_refuse_post fx0 ly S Hp W mem ch CTX regs0 e q v true text len tb p Lam peak cnt fail ran
                     most own kr lyc Sc Hpc Wc memc f n cap acc kids keys Di nm t r pc ok0 tr0 D0 Lamc peakc cntc failc
                     ranc af1 _ _ regs'' Hent HPOSB HLIVE HCONT HDEP HAP HPERM HRUN HLED HBM HBB HLS HROOM HCUR
                     ltac:(rewrite HY; split; [exact Hn44 | cbn [closer]; exact Hcl]) MEQ4 H10'' HGR HFORD HFLE).
            ** (* 0x87f54 `bne closer, c` not taken: the byte is the closer, on to PI_O_CLOSE2 *)
               rewrite branch_ne_U, U_lit, U_SOff in Hc by lia. cbn [ew ewset extK Nat.eqb] in Hc.
               rewrite U34, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia).
               assert (Hcl : c = 125) by (destruct (Z.eqb_spec 125 c); [lia | discriminate Hc]). clear Hc.
               paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_CLOSE2).
               { unfold ss_pvs; cbn [ss_mem]; unfold pvs_smem; cbn [app];
                 repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
               assert (MX4 : rdW Wc (ms_mem ms2) = rdW Wc (ms_mem ms1)).
               { apply (pvs_meq_of _ _ _ _ _ HFr). intros r1 Hin. vm_compute in Hin.
                 repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
               assert (MEQ4 : rdW Wc (ms_mem ms2) = rdW Wc memc) by (rewrite MX4; exact MEQ3).
               clear HF HFr HG.
               prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19. prreg HS (18%bv : bv 5) Q18.
               prreg HS (8%bv : bv 5) Q8. prreg HS (20%bv : bv 5) Q20. prreg HS (26%bv : bv 5) Q26.
               prreg HS (27%bv : bv 5) Q27. prreg HS (25%bv : bv 5) Q25. prreg HS (23%bv : bv 5) Q23.
               prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
               prreg HS (10%bv : bv 5) Q10.
               pmkst HS.
               lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
                 replace pcw with (w64 (VAL A_TEXT + PIAT PI_O_CLOSE2)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
               apply (HCL2 fx fx0 ly S Hp W mem md ch CTX regs0 e q v true text len tb p Lam peak cnt fail ran most own
                 kr lyc Sc Hpc Wc _ _ k _ WS0 (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx WR _ _ _ _ _ _ _ _
                 _ _ _ _ _ _ _ _ _ _ _ HJ HWD) HWS).
               apply (pvs_close_data fx0 ly S Hp W mem md ch CTX regs0 e q v true text len tb p Lam peak cnt fail ran most
                 own kr lyc Sc Hpc Wc memc f n cap acc kids keys Di nm t r r0 pc ok0 tr0 D0 Lamc peakc cntc failc ranc af1 _
                 _ k regs _ Hfp Hent HMN HPOSB HLIVE Hfr HCONT HAP HPERM HRUN HLED HBM HBB HLS HROOM HCUR
                 ltac:(rewrite Hyc, HY; reflexivity) ltac:(rewrite HY, Hcl; reflexivity) MEQ4);
                 [ | | | | | exact HGR | exact Hcapn | exact HNC | exact HFORD | exact HFLE].
               --- unfold pi_regs.
                   split; [cbn [ms_regs]; rewrite Q9, E9; reflexivity|].
                   split; [cbn [ms_regs]; rewrite Q19, E19; reflexivity|].
                   split; [cbn [ms_regs]; rewrite Q18; reflexivity|].
                   split; [cbn [ms_regs]; rewrite Q8, U9; reflexivity|].
                   split; [cbn [ms_regs]; rewrite Q20, U9; reflexivity|].
                   split; [cbn [ms_regs]; rewrite Q26, E26; reflexivity|].
                   split; [cbn [ms_regs]; rewrite Q27, (hd_alu_shx _ _ q SHADOW_OFF E9 E26 HQ63 HSB); unfold pi_sh, w64; reflexivity|].
                   split; [cbn [ms_regs]; rewrite Q25, (hd_alu_shx _ _ (q + 16) SHADOW_OFF W16 E26 HQ63b HSB);
                     unfold pi_sh, w64; reflexivity|].
                   cbn [ms_regs]; rewrite Q23, (hd_alu_shx _ _ (q + 8) SHADOW_OFF W8 E26 HQ63a HSB); unfold pi_sh, w64; reflexivity.
               --- cbn [ms_regs]. rewrite Q10, E32. reflexivity.
               --- cbn [ms_regs]; unfold spZ in *; rewrite Q2, E2; reflexivity.
               --- cbn [ms_regs]; rewrite Q3, E3; reflexivity.
               --- cbn [ms_regs]; rewrite Q4, E4; reflexivity.
         ++ paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_EPI).
            { unfold ss_pvs; cbn [ss_mem]; unfold pvs_smem; cbn [app];
              repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
            assert (MX3 : rdW Wc (ms_mem ms1) = rdW Wc (ms_mem ms0)).
            { apply (pvs_meq_of _ _ _ _ _ HFr). intros r1 Hin. vm_compute in Hin.
              repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
            assert (MEQ3 : rdW Wc (ms_mem ms1) = rdW Wc memc) by (rewrite MX3; exact MEQ2).
            clear HF HFr HG.
            psrr_branch_tok RUNTO BR HS SHOK BAND_SPAN.
            ** (* 0x87f54 `bne closer, c` taken: the byte is not the closer, the call refuses at PI_O_EPI *)
               rewrite branch_ne_U, U_lit, U_SOff in Hc by lia. cbn [ew ewset extK Nat.eqb] in Hc.
               rewrite U34, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia).
               assert (Hcl : c <> 93) by (destruct (Z.eqb_spec 93 c); [discriminate Hc | lia]). clear Hc.
               paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_EPI).
               { unfold ss_pvs; cbn [ss_mem]; unfold pvs_smem; cbn [app];
                 repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
               assert (MX4 : rdW Wc (ms_mem ms2) = rdW Wc (ms_mem ms1)).
               { apply (pvs_meq_of _ _ _ _ _ HFr). intros r1 Hin. vm_compute in Hin.
                 repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
               assert (MEQ4 : rdW Wc (ms_mem ms2) = rdW Wc memc) by (rewrite MX4; exact MEQ3).
               clear HF HFr HG.
               prreg HS (21%bv : bv 5) Q21. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
               prreg HS (4%bv : bv 5) Q4.
               pmkst HS.
               lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
                 replace pcw with (w64 (VAL A_TEXT + PIAT PI_O_EPI)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
               apply (pvs_epi (YCbqGwild.wbudget CW 0) fx0 ly S Hp W mem md regs0 e q v _ lyc Sc Hpc Wc memc _ _ k WS0
                 regs _ (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 _ _ HJ HWD) HWS Hfp Hfr MEQ4 HMN).
               --- cbn [ms_regs]; unfold spZ in *; rewrite Q2, E2; reflexivity.
               --- cbn [ms_regs]; rewrite Q3, E3; reflexivity.
               --- cbn [ms_regs]; rewrite Q4, E4; reflexivity.
               --- cbn [ms_regs]; rewrite Q21, E21; reflexivity.
               --- apply pvs_post_stable.
               --- intros regs'' H10''.
                   exact (pvs_refuse_post fx0 ly S Hp W mem ch CTX regs0 e q v false text len tb p Lam peak cnt fail ran
                     most own kr lyc Sc Hpc Wc memc f n cap acc kids keys Di nm t r pc ok0 tr0 D0 Lamc peakc cntc failc
                     ranc af1 _ _ regs'' Hent HPOSB HLIVE HCONT HDEP HAP HPERM HRUN HLED HBM HBB HLS HROOM HCUR
                     ltac:(rewrite HY; split; [exact Hn44 | cbn [closer]; exact Hcl]) MEQ4 H10'' HGR HFORD HFLE).
            ** (* 0x87f54 `bne closer, c` not taken: the byte is the closer, on to PI_O_CLOSE2 *)
               rewrite branch_ne_U, U_lit, U_SOff in Hc by lia. cbn [ew ewset extK Nat.eqb] in Hc.
               rewrite U34, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia).
               assert (Hcl : c = 93) by (destruct (Z.eqb_spec 93 c); [lia | discriminate Hc]). clear Hc.
               paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_CLOSE2).
               { unfold ss_pvs; cbn [ss_mem]; unfold pvs_smem; cbn [app];
                 repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
               assert (MX4 : rdW Wc (ms_mem ms2) = rdW Wc (ms_mem ms1)).
               { apply (pvs_meq_of _ _ _ _ _ HFr). intros r1 Hin. vm_compute in Hin.
                 repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
               assert (MEQ4 : rdW Wc (ms_mem ms2) = rdW Wc memc) by (rewrite MX4; exact MEQ3).
               clear HF HFr HG.
               prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19. prreg HS (18%bv : bv 5) Q18.
               prreg HS (8%bv : bv 5) Q8. prreg HS (20%bv : bv 5) Q20. prreg HS (26%bv : bv 5) Q26.
               prreg HS (27%bv : bv 5) Q27. prreg HS (25%bv : bv 5) Q25. prreg HS (23%bv : bv 5) Q23.
               prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
               prreg HS (10%bv : bv 5) Q10.
               pmkst HS.
               lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
                 replace pcw with (w64 (VAL A_TEXT + PIAT PI_O_CLOSE2)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
               apply (HCL2 fx fx0 ly S Hp W mem md ch CTX regs0 e q v false text len tb p Lam peak cnt fail ran most own
                 kr lyc Sc Hpc Wc _ _ k _ WS0 (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx WR _ _ _ _ _ _ _ _
                 _ _ _ _ _ _ _ _ _ _ _ HJ HWD) HWS).
               apply (pvs_close_data fx0 ly S Hp W mem md ch CTX regs0 e q v false text len tb p Lam peak cnt fail ran
                 most own kr lyc Sc Hpc Wc memc f n cap acc kids keys Di nm t r r0 pc ok0 tr0 D0 Lamc peakc cntc failc ranc
                 af1 _ _ k regs _ Hfp Hent HMN HPOSB HLIVE Hfr HCONT HAP HPERM HRUN HLED HBM HBB HLS HROOM HCUR
                 ltac:(rewrite Hyc, HY; reflexivity) ltac:(rewrite HY, Hcl; reflexivity) MEQ4);
                 [ | | | | | exact HGR | exact Hcapn | exact HNC | exact HFORD | exact HFLE].
               --- unfold pi_regs.
                   split; [cbn [ms_regs]; rewrite Q9, E9; reflexivity|].
                   split; [cbn [ms_regs]; rewrite Q19, E19; reflexivity|].
                   split; [cbn [ms_regs]; rewrite Q18; reflexivity|].
                   split; [cbn [ms_regs]; rewrite Q8, U9; reflexivity|].
                   split; [cbn [ms_regs]; rewrite Q20, U9; reflexivity|].
                   split; [cbn [ms_regs]; rewrite Q26, E26; reflexivity|].
                   split; [cbn [ms_regs]; rewrite Q27, (hd_alu_shx _ _ q SHADOW_OFF E9 E26 HQ63 HSB); unfold pi_sh, w64; reflexivity|].
                   split; [cbn [ms_regs]; rewrite Q25, (hd_alu_shx _ _ (q + 16) SHADOW_OFF W16 E26 HQ63b HSB);
                     unfold pi_sh, w64; reflexivity|].
                   cbn [ms_regs]; rewrite Q23, (hd_alu_shx _ _ (q + 8) SHADOW_OFF W8 E26 HQ63a HSB); unfold pi_sh, w64; reflexivity.
               --- cbn [ms_regs]. rewrite Q10, E32. reflexivity.
               --- cbn [ms_regs]; unfold spZ in *; rewrite Q2, E2; reflexivity.
               --- cbn [ms_regs]; rewrite Q3, E3; reflexivity.
               --- cbn [ms_regs]; rewrite Q4, E4; reflexivity.
      -- (* 0x87df4 `bne c, 44` not taken: impossible, c is not ',' *)
         exfalso. rewrite branch_ne_U, U_lit, U_SOff in Hc by lia. cbn [ew ewset extK Nat.eqb] in Hc.
         rewrite U34, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia).
         destruct (Z.eqb_spec c 44); [exact (Hn44 e0) | discriminate Hc].
- (* THE CURSOR IS AT THE END OF THE TEXT: no byte, the call refuses at PI_O_EPI *)
  assert (Hpe : pc = text + len) by lia.
  assert (Hyn : rest_atR tb text pc = []) by (unfold rest_atR; apply skipn_all2; lia).
  rewrite Hyn in HY. symmetry in HY.
  pose proof (pvs_st_ok (fx := fx) Wc memc regs q pc (text + len) 0 o false false (PIAT PV_O_SEP)
    R9 R8 R20 R26 R27 R25 R23 R18 Hqb Hq8 Hp1b Hedb ltac:(lia) ltac:(intros X; discriminate X) Vp Ve
    ltac:(intros X; discriminate X) ltac:(intros X; discriminate X)) as HS.
  remember (Eimg (rc := rc) (L := B_prog_listing) (PI := PI_prog_B)
             (Ereg regs [Z_to_bv 64 pc; Z_to_bv 64 (text + len); Z_to_bv 64 0])) as E eqn:HE in HS.
  assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E3 : ew E 3 = getr regs 3) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
  assert (E4 : ew E 4 = getr regs 4) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
  assert (E9 : ew E 9 = Z_to_bv 64 q) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
  assert (E21 : ew E 21 = Z_to_bv 64 (-1)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
  assert (E26 : ew E 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 pc) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (text + len)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (U32 : bv_unsigned (ew E 32) = pc) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = text + len) by (rewrite E33; apply unsigned_lit_small; lia).
  clear HE.
  assert (SHOK : sh_ok SEGS pvs_Bx (pvs_SH false) E (rdW Wc memc)).
  { unfold pvs_SH. cbn [app]. constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H Wc) memc E pvs_Bx 9 q 24 q 0 24 HRA);
    [unfold pvs_Bx; rewrite (U_atom E 26 SHADOW_OFF E26) by (unfold SHADOW_OFF; lia); reflexivity
    | rewrite (U_atom E 9 q E9) by lia; reflexivity | lia | lia | intros x Hx; unfold SHADOW_OFF; lia]. }
  change (w64 (VAL A_TEXT + PIAT PV_O_SEP)) with (Z_to_bv 64 (VAL A_TEXT + PIAT PV_O_SEP)).
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_EPI).
  { unfold ss_pvs; cbn [ss_mem]; unfold pvs_smem; cbn [app];
    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
  assert (MEQ1 : rdW Wc (ms_mem ms) = rdW Wc memc).
  { apply (pvs_meq_of _ _ _ _ _ HFr). intros r1 Hin. vm_compute in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
  clear HF HFr HG.
  psrr_branch_tok RUNTO BR HS SHOK BAND_SPAN.
  + (* 0x87dd4 `bgeu p, end` taken: the cursor is at the end, refusal *)
    clear Hc.
    paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN BAND_SPAN (PIAT PI_O_EPI).
    { unfold ss_pvs; cbn [ss_mem]; unfold pvs_smem; cbn [app];
      repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil. }
    assert (MX2 : rdW Wc (ms_mem ms0) = rdW Wc (ms_mem ms)).
    { apply (pvs_meq_of _ _ _ _ _ HFr). intros r1 Hin. vm_compute in Hin.
      repeat (destruct Hin as [<-|Hin]; [cbn; lia|]). destruct Hin. }
    assert (MEQ2 : rdW Wc (ms_mem ms0) = rdW Wc memc) by (rewrite MX2; exact MEQ1).
    clear HF HFr HG.
    prreg HS (21%bv : bv 5) Q21. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    pmkst HS.
    lazymatch goal with |- context [{| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |}] =>
      replace pcw with (w64 (VAL A_TEXT + PIAT PI_O_EPI)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
    apply (pvs_epi (YCbqGwild.wbudget CW 0) fx0 ly S Hp W mem md regs0 e q v _ lyc Sc Hpc Wc memc _ _ k WS0 regs _
      (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWD) HWS
      Hfp Hfr MEQ2 HMN).
    * cbn [ms_regs]; unfold spZ in *; rewrite Q2, E2; reflexivity.
    * cbn [ms_regs]; rewrite Q3, E3; reflexivity.
    * cbn [ms_regs]; rewrite Q4, E4; reflexivity.
    * cbn [ms_regs]; rewrite Q21, E21; reflexivity.
    * apply pvs_post_stable.
    * intros regs'' H10''.
      exact (pvs_refuse_post fx0 ly S Hp W mem ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr
        lyc Sc Hpc Wc memc f n cap acc kids keys Di nm t r pc ok0 tr0 D0 Lamc peakc cntc failc ranc af1 _ _ regs''
        Hent HPOSB HLIVE HCONT HDEP HAP HPERM HRUN HLED HBM HBB HLS HROOM HCUR ltac:(rewrite HY; exact I) MEQ2 H10''
        HGR HFORD HFLE).
  + (* 0x87dd4 `bgeu p, end` not taken: impossible at the end of the text *)
    exfalso. rewrite branch_geu_U, !U_SOff in Hc. cbn [ew ewset extK Nat.eqb] in Hc.
    rewrite U32, U33, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
    destruct (Z.ltb_spec pc (text + len)); [lia | discriminate Hc].
Qed.

End core.
End main.

(* ================================================================================================== *)
(* 5. THE SEGMENT LEMMA, in PItems_top.v's form (d, CTX0, CW and N parameters; the float state at the block a binder)  *)
(* ================================================================================================== *)
Section top. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instance prh_img_B.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable d : nat.
Variable CTX0 : list (list Z).
(* the cursor set of the batch kit's texts (the specs' parameter after CTX0) *)
Variable CW : list (list Z).
(* the engine's laws at the instance's head length (PItems_body.v / PItems_body_loop.v's form) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the instance's head length is the model's (PItems_body_loop.v PIL_HEAD, same text). OWNER: the instance *)
Hypothesis PIL_HEAD : cf_head = PresetReqAt.HEAD.
(* grow's text, the kit's (lib/A/PRH_FnReader.v tgrow_specX), at every float state *)
Hypothesis GROW : forall (fy : YK11.FPState),
  tgrow_specX (fx := fy) (rc := rc) (ci := ci) (cp := cp) (PI := prh_img_B) (RL := RL) (L := B_prog_listing)
    (PA := PI_prog_B) B ARx SK CTX0.
(* the cursor transport across a call over a world relation R (lib/B/Prog/PItems_kept.v pi_cur_kept_callR_stmt;
   proved there as pi_cur_kept_callR) *)
Hypothesis HKEPT : pi_cur_kept_callR_stmt (rc := rc) (cp := cp) (PIi := prh_img_B) (L := B_prog_listing)
  (PA := PI_prog_B) (SKq := SK) B ARx.

Theorem pv_sep_holds : forall N,
  (forall N', (N' < N)%nat -> pi_body_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL)
     (L := B_prog_listing) (PA := PI_prog_B) (PL := PL_prog_B) B ARx SK d CTX0 CW N') ->
  pi_close2_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing)
    (PA := PI_prog_B) (PL := PL_prog_B) B ARx SK d CTX0 CW ->
  pi_epi_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing)
    (PA := PI_prog_B) (PL := PL_prog_B) B ARx SK d ->
  pv_sep_spec (rc := rc) (ci := ci) (cp := cp) (PIi := prh_img_B) (RL := RL) (L := B_prog_listing)
    (PA := PI_prog_B) (PL := PL_prog_B) B ARx SK d CTX0 CW N.
Proof.
intros N HBODY HCL2 HEPI fxc.
exact (pvs_core (fx := fxc) (rc := rc) (ci := ci) (cp := cp) (RL := RL) B ARx SK d CTX0 CW LAWS PIL_HEAD GROW HKEPT
  HEPI HCL2 N HBODY).
Qed.

End top.
