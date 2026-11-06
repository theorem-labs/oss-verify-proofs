(* fuzz_preset, slice S5b, the Ival walk's lane (a Theorem Labs lane), adapted by lane A'Step (a Theorem Labs lane, 2026-10-30): parse_items'
   ELEMENT STEP, image A - PROVED as `Theorem vrd_ival_okG : tvrd_ival_aG B ARx SK CTXv CTX0v CWv`, VrdIElem.v's
   generic Prop (A2Ipro's text): for every memory invariant Pm with srr_inv_laws / srr_inv_call / srr_inv_mn,
   VrdIElem.tvrd_ival_aP Pm - tvrd_ival_a's premises plus Pm (ip_mem P), and its post plus Pm on the reached memory
   and the PROGRESS conjunct ip_n P' = ip_n P + 1 at the comma (vrd_ival_holds_P inside Section VI, which holds
   exactly Pm and its three laws).
   A'STEP (the kit's #102 reader text, a working branch 3ac20a5c9e30: PRH_FnParse.v blob 94232293d483,
   PRH_FnReader.v fb7b12dfa169, PRH_Base.v ee2f5cd7ed35, PRH_FnAlloc.v 95e26ff95e63, taken once by lane A2Num as
   6b723d760c66): prh_ledger takes most own; rd_ledger_move takes most and the all-granted trace (parse_value's
   prhPv_gtrace at the call, the whole call's prhPi_gtrace at the position, split by vv_gt_val); parse_value's post
   is the POST-IMPLICATION form (no entry room position; the live requests, the position transfer and the OUTCOME
   are post conjuncts, composed by VrdCallPos's vc_xfer / vc_live / vc_outc); the refusal exit's OUTCOME is the
   callee's (vv_outc_callee), the text exits' is the granted prefix's (vc_outc_granted); fpre gains the return slot
   bound (vv_ret_slot_ceil) and frm_zero; the live counts at parse_value's inner calls come from vrd_ient_ok's along
   the call's granted events (VrdIStep.vi_pk_mid).
   The kit's CUT (lane RItems, a working branch 7cdbb61b5fa0: PRH_FnParse.v f0d92dcec7e9, PRH_Base.v
   ef7c8ca98529; RBase's VrdIElem / VrdIStep / VrdIFd at c1ae1218f628). DW is CW. rd_room's live room is per event
   (vv_room_prefix by VrdLedgerStep.vl_live_evs_prefix; vl_room_tail on the callee's live move). Every position's
   journal is at the budget ie_CW E (VrdIElem.vrd_ijrn): the runners run from it rebased (vrd_ijrn_base) and the
   transports take it back (vrd_ijrn_unbase), so the transport lemmas' journal premises are budgeted. Row 231 calls
   parse_value by the BUDGETED rule VrdArm.vrd_call_WFb_P (the text's post is fpostWFbm at wbudget CW 0) with the cut's
   new premises (prh_cw_entry from vrd_reader_call_pre, wild_room by vrd_wild_room_at, rd_pre's appended
   text + len < alloc_ceiling) and composes by vrd_pos_after_call at the callee's budget. THE BATCH KIT'S LAYER: vrd_islot_a's
   is carried across the memset (vv_k1_keep_w, vv_keyR_keep); after a granted value the callee's free order and
   pj_ncapR join the completed slots' (vv_k1_snoc, the model's list vrd_jfsep by vv_fl_some), carried by vv_sep's new
   last conjunct vv_k1sep to the comma (vrd_icomma_a's batch-kit conjunct) and to the exits (vv_exit_fo: the complete order list and
   caps); a refused value's exit takes the partial child's list (vv_fo_exit, vv_fl_none). The model's free-list
   determinism (vv_jf_det) and PresetFreeFo.jfv_fuel give jfv's value at the granted prefix.
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). One step of parse_items' element loop, from the value slot
   (vrd_islot_a, slot 6142) to the next comma (vrd_icomma_a, slot 6212) or the exit join (vrd_iexit_a, slot 6242).

   THE ROWS (slot k is at A_prog_base + 4 k of lib/A/Listing_prog.v; the words are those of the record image A' asan
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44 (pins102); parse_items at A 0x87298). STALE, kept
   as history: the objdump sha256 3d8143a4cdf95d11747ee1e0993fed9eccfe74df4919582b1c6e408c8d45abd1 was taken on the
   OLD image d83eb25d with the internal file neutral_dis.py; the A' objdump has not been re-derived (the owner's artifact; a
   re-run of the internal file neutral_dis.py on 1be0f53d is owed) - the addresses here were relocated by lane P102Reloc2 and audited.
   - PART A, rows 210..223 (A 0x875d8..0x8760c): the slot address kids + 56 n, `jal __asan_memset` zeroing it, by
     YGcallMxmn.aj_intrin_at_xm OSet (vv_partA, to vv_set at the return slot 6156);
   - PART B, rows 224..237 (A 0x87610..0x87644): the arguments, `jal parse_value` at nesting d + 1 (row 231) by
     VrdArm.vrd_call_WFb_P against tparse_value_specX (S d) (vv_partB; the text's post is the budgeted m-form
     fpostWFbm), then the count store v->n := n + 1 and the result test (vv_after_call), to vv_sep at slot 6170 or a
     refusal exit (res = -1) through slot 6241;
   - PART C, rows 238..264: the white-space scan after the value (vv_partC1, vv_partC2, SRr'_loopZ on end - p);
   - PART D, rows 265..279 and 326..346: the separator test - the comma to vrd_icomma_a (slot 6212), the closer to the
     exit with res = 0, anything else to the exit with res = -1 (vv_partD).
   The shared transports this step uses are written once elsewhere and cited: VrdCurStore.vk_cur_store_keep (the S3 walk,
   cursor stores), VrdCallKeep.vrd_call_keep / vrd_reader_call_pre / vrd_pos_after_call (journal across a call),
   VrdLedgerStep (ledger composition), VrdIStep.vrd_icur_after_call / vrd_node_ra_after_call / vrd_lam_shadow (IelemE,
   the facts no journal keeps), VrdIElem.vrd_chain_keep_w (IelemE).

   THE MEMORY INVARIANT (a Theorem Labs lane's generic-P ruling 12:18Z; srr_inv_call 12:22Z; srr_inv_mn 12:23Z): Pm is any
   memory predicate with srr_inv_laws SEGS Pm (the runner twins of YSRrMemnorm.v / YC80xf_inv.v carry it through every
   symbolic run), srr_inv_call SEGS Pm (it crosses the memset row and parse_value, whose posts keep memnorm) and
   srr_inv_mn SEGS Pm (parse_value's ENTRY premise memnorm at the call, PRH_FnParse.v:181). An SRr post is opaque once
   Qed, so the end-state invariant is in each part's statement. Pm is instantiated once, at parse_items' top, as
   `fun m => memnorm segs mem0 -> memnorm segs m` (srr_inv_laws_imp, srr_inv_call_imp, srr_inv_mn_imp with parse_items'
   own entry premise PRH_FnParse.v:252).
   NO Pm := True COROLLARY OF THE OLD STATEMENT: the premises moved because of a callee's TEXT, not for Pm's sake.
   parse_value's record text (PRH_FnParse.v blob 6ece0e8567fe, a working branch ee649e1b39d) takes
   `YAjMemnorm.memnorm segs mem` at entry (:181); vrd_ient_ok and vrd_islot_a (VrdIElem.v blob 5c5bb8aae5c5,
   a working branch 6372b90e841) give memnorm of no memory, and fpre / ajournal_x / ARx do not imply it.
   Counterexample to tvrd_ival_a (VrdIElem.v:446) from parse_value's text (then the Section hypothesis H_parse_value):
   take E, P, nm with vrd_ient_ok and vrd_islot_a and add one overlay byte at an address at or above TASK_SIZE outside
   every segment, in ie_mem E and every later memory. MemNorm.task_mem fails, so memnorm fails; no named fact changes
   (they read named addresses only); parse_value's text says nothing about the row-231 call. (The frames-count premise
   of the same text, :211, is not new: vrd_ient_ok's
   last conjunct gives it through vv_maxd_succ.)

   SECTION HYPOTHESES (each is carried by name; none is a stand-in for this step's own proof):
   - NO parse_value hypothesis: VrdIElem's tvrd_ival_aP (A2Ipro's b6d759e9b2b9) takes parse_value's text at the
     element's own nesting S (ie_d E) as its first premise, the one the parse_items / parse_value descending induction
     on d can supply (check 2's finding on this file, 2026-10-30; the earlier all-depths H_parse_value is deleted);
   - H_checked_memset: __asan_memset by the kit's intrinsic text in the m-form (YGcallMxmn.aintrin_realizes_xm OSet),
     as VrdNum carries __asan_memcpy; a row for it exists (lib/A/Prog/S6ImgWit.v s6w_aim, through
     PRowSet.prow_asan_memset_xm_A_lit), which the assembly can cite;
   - Pm with PLAW / PCALL / PMN: the generic invariant above (its laws are YSRrMemnorm.v's three definitions);
   - H_img (pi_frame F_parse_items = 144, pi_s0cur F_parse_items = Some 0, 0 <= pi_frame F_parse_value) and H_s0s
     (pi_s0cur F_parse_string = Some 0): image facts, true at prh_img_A by computation (PRH_Img.v);
   - H_head (8 <= cf_head /\ HL = cf_head): the kit's prh_head_wide (a Theorem Labs lane's preset_head_wide) and IelemE's H_HL;
   - H_pst (S1ImgA.pst_in_img_A), H_pst_ro (S1ImgA.pst_not_ro_A), H_zsal, H_imgvis: IelemE's VrdIStep.v image facts,
     same names and statements.
   SET: a working branch on the S3 walk's a9cece7b4d8 (ielem 6372b90e841: VrdIElem.v blob 5c5bb8aae5c5; VrdCallPos.v
   ec329a9d5256; VrdArm.v f1a084bbd44f), the record texts a working branch ee649e1b39d (PRH_FnParse.v blob
   6ece0e8567fe) on the kit's preview walkkit-next 2d523216ac5 (PRH_Base.v 54a99f16629c). Engine files by path:
   YSRrMemnorm.v a1c1ece77b14 and YAkMemnorm.v 96c72061b4d4 (a working branch 161f89a71b4d), YC80xf_inv.v
   082f0c430210 (a working branch 1941d76deca), YGcallMxmn.v 2b01e06e3fc4 (a working branch
   36d44407fa94; its header table's memset rule aj_intrin_at_xm). A-only: B sites not measured.
   Numerals: slots and row numbers (LISTING INDEX), 144 / 56 / 24 / 8 / 4096 (LENGTH: frame, node, cursor, word, page),
   2 ^ 64 / 2 ^ 47 (LENGTH: bounds); A 0x... in this comment only (ADDRESS, the image above). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80xf YGcallMx YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YC80xf_inv YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YAjMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetFreeFo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse VrdFrame VrdIElem VrdIStep
VrdIFd VrdCurStore VrdCallKeep VrdArm VrdLedgerStep VrdCallPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_StepKit.

(* the re-hiding move's SRr' / wle' (YA0nH, YSRrG) and preset's zone (YGcfRehidePost.RZ_cf); the threaded hull
   budget *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the listing slots this step passes ---- *)
Definition A_IMSET_RET : nat := 6156%nat.  (* row 224, the return site of `jal __asan_memset` (row 223) *)
Definition A_ISEP_SLOT : nat := 6170%nat.  (* row 238, after the count store: the white-space scan begins *)
Definition A_IWSL_SLOT : nat := 6178%nat.  (* row 246, the head of the white-space loop *)
Definition A_ITAIL_SLOT : nat := 6197%nat. (* row 265, the separator test *)

(* the shadow address of an atom plus an offset, as the code computes it: ((x + off) >> 3) + s10 *)
Definition vv_sh (a : nat) (off : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff a off) (SLit 3)) (SOff 26 0).

Lemma vv_sh_U : forall (E : env) a off x, bv_unsigned (ew E a) = x -> bv_unsigned (ew E 26) = SHADOW_OFF ->
  0 <= x + off < 2 ^ 47 -> U E (vv_sh a off) = shadow_addr (x + off).
Proof.
  intros E a off x Hx Hs Hr. unfold vv_sh. rewrite U_SAlu. cbn [zalu_raw].
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit, U_SOff, Hx, Hs, Z.add_0_r.
  rewrite (zcanon_id (x + off)) by (unfold M64; lia).
  change (zcanon 3) with 3. change (Z.land 3 63) with 3.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (Z.div_pos (x + off) 8 ltac:(lia) ltac:(lia)).
  assert ((x + off) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  rewrite (zcanon_id ((x + off) / 8)) by (unfold M64; lia).
  rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
  unfold shadow_addr. rewrite Z.add_comm. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

(* a register seated to an expression whose denotation is that register's value *)
Lemma vv_regs_ok_set : forall E sr regs (r : bv 5) e,
  regs_ok E sr regs -> getr regs r = sv_denot E e -> regs_ok E (sr_set sr r e) regs.
Proof.
  intros E sr regs r e Hr Hv r'.
  unfold sr_set. destruct (bv_eqb r 0) eqn:Hr0; [apply Hr|].
  specialize (Hr r'). unfold sr_get in *.
  destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
  rewrite nth_sr_upd.
  destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
  apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. exact Hv.
Qed.

Lemma vv_maxd_succ : forall d, (d < PjGrammar.MAXD)%nat ->
  Z.of_nat (Nat.succ (PjGrammar.MAXD - S d)%nat) = Z.of_nat (PjGrammar.MAXD - d)%nat.
Proof.
  intros d H. rewrite Nat2Z.inj_succ, (Nat2Z.inj_sub _ _ H), (Nat2Z.inj_sub _ _ (Nat.lt_le_incl _ _ H)), Nat2Z.inj_succ.
  lia.
Qed.

(* the visible shadow hull of a range covers the hull of every sub-range (YGcfHeadSh.v's shadow_hull_vis_sub_cf,
   restated here: that file is not in this unit's build graph) *)
Lemma vv_hull_sub : forall rd x n x' n',
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> shadow_hull_vis rd x' n'.
Proof.
  intros rd x n x' n' H H1 H2 s Hs. apply H. unfold shadow_addr in *.
  assert (A1 : (SHADOW_OFF + x / 8) / 8 * 8 <= (SHADOW_OFF + x' / 8) / 8 * 8).
  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
    pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1). lia. }
  assert (A2 : (SHADOW_OFF + (x' + n' - 1) / 8) / 8 * 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8 * 8).
  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
    pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)). lia. }
  lia.
Qed.

(* ---- the model lemmas of sub-lane IvalM (pure) ---- *)

(* ---- copied Qed lemmas: IvalL_led.v (ledger algebra) ---- *)


(* hpeakR is the largest prefix sum (and 0) *)





(* the ledger move of a granted prefix followed by one more call's move *)

(* ---- IvalG: the live-size multiset of a reader trace (pure; no Section variables) ---- *)

(* every removal of a trace finds its size among the sizes live at that point *)
Fixpoint vv_hits (t : list PjGrammar.ev) (s : list nat) : Prop :=
  match t with
  | [] => True
  | e :: r =>
      match e with
      | PjGrammar.EGrow (S m') _ => In (S m') s
      | PjGrammar.EFree n => In n s
      | _ => True
      end /\ vv_hits r (lsz_evR s e)
  end.

(* ---- multiset algebra of rm1nR / lsz_evR ---- *)

Lemma vv_lz_rm1_perm : forall k l l', Permutation l l' -> Permutation (rm1nR k l) (rm1nR k l').
Proof.
  intros k l l' H. induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2].
  - constructor.
  - cbn [rm1nR]. destruct (Nat.eqb x k); [exact H|]. apply perm_skip. exact IH.
  - cbn [rm1nR]. destruct (Nat.eqb y k) eqn:Ey, (Nat.eqb x k) eqn:Ex.
    + apply Nat.eqb_eq in Ey, Ex. subst. apply Permutation_refl.
    + apply Permutation_refl.
    + apply Permutation_refl.
    + apply perm_swap.
  - eapply perm_trans; eassumption.
Qed.

Lemma vv_lz_fold_perm : forall t l l', Permutation l l' ->
  Permutation (fold_left lsz_evR t l) (fold_left lsz_evR t l').
Proof.
  induction t as [|e r IH]; intros l l' H; cbn [fold_left]; [exact H|].
  apply IH. destruct e as [n|[|m] n|n|n]; cbn [lsz_evR].
  - apply perm_skip; exact H.
  - apply perm_skip; exact H.
  - apply perm_skip; apply vv_lz_rm1_perm; exact H.
  - exact H.
  - apply vv_lz_rm1_perm; exact H.
Qed.

Lemma vv_lz_rm1_in : forall k s, In k s -> Permutation s (k :: rm1nR k s).
Proof.
  intros k s. induction s as [|x r IH]; intros H; [destruct H|].
  cbn [rm1nR]. destruct (Nat.eqb x k) eqn:E.
  - apply Nat.eqb_eq in E. subst x. apply Permutation_refl.
  - apply Nat.eqb_neq in E. destruct H as [H|H]; [contradiction|].
    eapply perm_trans; [apply perm_skip; apply IH; exact H|]. apply perm_swap.
Qed.

Lemma vv_lz_rm1_app : forall k s0 s, In k s ->
  Permutation (rm1nR k (s0 ++ s)) (s0 ++ rm1nR k s).
Proof.
  intros k s0 s H. induction s0 as [|x s0 IH]; cbn [app rm1nR]; [apply Permutation_refl|].
  destruct (Nat.eqb x k) eqn:E.
  - apply Nat.eqb_eq in E. subst x.
    eapply perm_trans; [apply Permutation_app_head; apply vv_lz_rm1_in; exact H|].
    apply Permutation_sym, Permutation_middle.
  - apply perm_skip. exact IH.
Qed.

Lemma vv_lz_ev_app : forall e s0 s,
  match e with
  | PjGrammar.EGrow (S m') _ => In (S m') s
  | PjGrammar.EFree n => In n s
  | _ => True
  end ->
  Permutation (lsz_evR (s0 ++ s) e) (s0 ++ lsz_evR s e).
Proof.
  intros e s0 s H. destruct e as [n|[|m] n|n|n]; cbn [lsz_evR].
  - apply Permutation_middle.
  - apply Permutation_middle.
  - eapply perm_trans; [apply perm_skip; apply vv_lz_rm1_app; exact H|]. apply Permutation_middle.
  - apply Permutation_refl.
  - apply vv_lz_rm1_app; exact H.
Qed.

Lemma vv_lsz_app : forall t s0 s, vv_hits t s ->
  Permutation (fold_left lsz_evR t (s0 ++ s)) (s0 ++ fold_left lsz_evR t s).
Proof.
  induction t as [|e r IH]; intros s0 s H; cbn [fold_left]; [apply Permutation_refl|].
  cbn [vv_hits] in H. destruct H as [H1 H2].
  eapply perm_trans; [eapply vv_lz_fold_perm; eapply vv_lz_ev_app; exact H1|].
  apply IH. exact H2.
Qed.

Lemma vv_lz_frame : forall t a s, vv_hits t [] -> In a s -> In a (fold_left lsz_evR t s).
Proof.
  intros t a s H Ha. pose proof (vv_lsz_app t s [] H) as P. rewrite app_nil_r in P.
  eapply Permutation_in; [exact (Permutation_sym P)|]. apply in_or_app. left. exact Ha.
Qed.

Lemma vv_lz_hits_app : forall t1 t2 s,
  vv_hits (t1 ++ t2) s <-> vv_hits t1 s /\ vv_hits t2 (fold_left lsz_evR t1 s).
Proof.
  induction t1 as [|e r IH]; intros t2 s; cbn [app vv_hits fold_left].
  - tauto.
  - specialize (IH t2 (lsz_evR s e)). tauto.
Qed.

Lemma vv_lz_in_rm1 : forall x k s, In x s -> x <> k -> In x (rm1nR k s).
Proof.
  intros x k s. induction s as [|y r IH]; intros H Hx; [destruct H|].
  cbn [rm1nR]. destruct (Nat.eqb y k) eqn:E.
  - apply Nat.eqb_eq in E. destruct H as [H|H]; [congruence|exact H].
  - destruct H as [H|H]; [left; exact H|right; apply IH; assumption].
Qed.

Lemma vv_lz_in_grow_old : forall x m n s, In x s -> x <> m -> In x (lsz_evR s (PjGrammar.EGrow m n)).
Proof.
  intros x m n s H Hx. destruct m as [|m]; cbn [lsz_evR]; right; [exact H|apply vv_lz_in_rm1; assumption].
Qed.

Lemma vv_lz_in_grow_new : forall m n s, In n (lsz_evR s (PjGrammar.EGrow m n)).
Proof. intros m n s. destruct m; cbn [lsz_evR]; left; reflexivity. Qed.

(* ---- the reader monad ---- *)

Lemma vv_lz_bind : forall (A B : Type) (m : PjGrammar.M A) (k : A -> PjGrammar.M B) ok s,
  vv_hits (snd (fst (m ok))) s ->
  (forall a t ok1, m ok = (Some a, t, ok1) -> vv_hits (snd (fst (k a ok1))) (fold_left lsz_evR t s)) ->
  vv_hits (snd (fst (PjGrammar.jbind m k ok))) s.
Proof.
  intros A B m k ok s. unfold PjGrammar.jbind. cbv beta.
  destruct (m ok) as [[[a|] t] ok1]; cbv beta iota; cbn [fst snd]; intros H1 H2.
  - specialize (H2 a t ok1 eq_refl). revert H2.
    destruct (k a ok1) as [[r t'] ok2]; cbv beta iota; cbn [fst snd]; intros H2.
    apply (proj2 (vv_lz_hits_app _ _ _)). split; assumption.
  - exact H1.
Qed.

Lemma vv_lz_alloc_hits : forall n ok s, vv_hits (snd (fst (PjGrammar.jalloc n ok))) s.
Proof.
  intros n ok s. unfold PjGrammar.jalloc. cbv beta.
  destruct (PjGrammar.take ok) as [[|] ok1]; cbn; auto.
Qed.

Lemma vv_lz_alloc_tr : forall n ok a t ok1,
  PjGrammar.jalloc n ok = (Some a, t, ok1) -> t = [PjGrammar.EAlloc n].
Proof.
  intros n ok a t ok1. unfold PjGrammar.jalloc. cbv beta.
  destruct (PjGrammar.take ok) as [[|] ok2]; cbv beta iota; intros E; inversion E; subst; reflexivity.
Qed.

Lemma vv_lz_realloc_hits : forall m n ok s, (m <> 0%nat -> In m s) ->
  vv_hits (snd (fst (PjGrammar.jrealloc m n ok))) s.
Proof.
  intros m n ok s H. unfold PjGrammar.jrealloc. cbv beta.
  destruct (PjGrammar.take ok) as [[|] ok1]; cbv beta iota; cbn [fst snd vv_hits]; [|tauto].
  split; [|exact I]. destruct m as [|m]; [exact I|]. exact (H ltac:(discriminate)).
Qed.

Lemma vv_lz_realloc_tr : forall m n ok a t ok1,
  PjGrammar.jrealloc m n ok = (Some a, t, ok1) -> t = [PjGrammar.EGrow m n].
Proof.
  intros m n ok a t ok1. unfold PjGrammar.jrealloc. cbv beta.
  destruct (PjGrammar.take ok) as [[|] ok2]; cbv beta iota; intros E; inversion E; subst; reflexivity.
Qed.

Lemma vv_lz_lit : forall w v x ok s, vv_hits (snd (fst (PjGrammar.lit w v x ok))) s.
Proof. intros w v x ok s. unfold PjGrammar.lit. cbv beta. destruct (PjGrammar.prefixb w x); exact I. Qed.

Lemma vv_lz_jr_string : forall z ok s, vv_hits (snd (fst (PjGrammar.jr_string z ok))) s.
Proof.
  intros z ok s. unfold PjGrammar.jr_string.
  destruct (PjGrammar.scan z) as [q|]; cbv beta iota; [|exact I].
  apply vv_lz_bind; [apply vv_lz_alloc_hits|].
  intros u t ok1 E. apply vv_lz_alloc_tr in E. subst t. cbv beta.
  destruct (PjGrammar.decode z) as [sr|]; cbv beta iota; [exact I|].
  cbn. auto with datatypes.
Qed.

Lemma vv_lz_jr_name : forall o y ok s, vv_hits (snd (fst (PjGrammar.jr_name o y ok))) s.
Proof.
  intros o y ok s. unfold PjGrammar.jr_name. cbv beta.
  destruct o; cbv beta iota; [|exact I].
  destruct (PjGrammar.skip y) as [|b z]; cbv beta iota; [exact I|].
  destruct (b =? 34); cbv beta iota; [|exact I].
  apply vv_lz_bind; [apply vv_lz_jr_string|].
  intros [nm r] t ok1 E.
  pose proof (PjGrammar.jr_string_spec z ok) as Hs. rewrite E in Hs. cbv beta iota in Hs.
  destruct Hs as (q & Hq & _ & -> & _).
  assert (Hb : PjGrammar.sblock z = S q) by (unfold PjGrammar.sblock; rewrite Hq; reflexivity).
  cbv beta iota.
  destruct (PjGrammar.skip r) as [|c r1]; cbv beta iota.
  - rewrite Hb. cbn. auto with datatypes.
  - destruct (c =? 58); cbv beta iota; [exact I|]. rewrite Hb. cbn. auto with datatypes.
Qed.

Lemma vv_lz_number : forall (st : list Z -> Z * Z) x ok s,
  vv_hits (snd (fst (PjGrammar.jr_number st x ok))) s.
Proof.
  intros st x ok s. unfold PjGrammar.jr_number. cbv beta zeta.
  destruct (skipn _ x) as [|c z]; cbv beta iota; [exact I|].
  destruct (negb (PjGrammar.digit c)); cbv beta iota; [exact I|].
  destruct ((c =? 48) && _); cbv beta iota; [exact I|].
  destruct (PjGrammar.span PjGrammar.numch z) as [a r]; cbv beta iota.
  apply vv_lz_bind; [apply vv_lz_alloc_hits|].
  intros u t ok1 _. cbv beta. destruct (PjGrammar.whole _ _); exact I.
Qed.

Lemma vv_lz_cont : forall loop d o x ok s,
  (forall y ok' s', vv_hits (snd (fst (loop (S d) o 0%nat 0%nat [] y ok'))) s') ->
  vv_hits (snd (fst (PjGrammar.jr_cont loop d o x ok))) s.
Proof.
  intros loop d o x ok s H. unfold PjGrammar.jr_cont. cbv beta zeta.
  destruct (Nat.ltb PjGrammar.MAXD (S d)); cbv beta iota; [exact I|].
  destruct (PjGrammar.skip (tl x)) as [|c r]; cbv beta iota; [apply H|].
  destruct (c =? PjGrammar.closer o); cbv beta iota; [exact I|apply H].
Qed.

(* grow's step after the capacity test: one EGrow of the item array, and for an object one of the key array *)
Lemma vv_lz_grow_core : forall (o : bool) (cap c' : nat) ok s,
  c' <> 0%nat -> (cap = 0%nat \/ c' = (2 * cap)%nat) ->
  (cap <> 0%nat -> In (56 * cap)%nat s /\ (o = true -> In (8 * cap)%nat s)) ->
  vv_hits (snd (fst (PjGrammar.jbind (PjGrammar.jrealloc (56 * cap) (56 * c'))%nat (fun _ =>
      if o then PjGrammar.jbind (PjGrammar.jrealloc (8 * cap) (8 * c'))%nat (fun _ => PjGrammar.jret c')
      else PjGrammar.jret c') ok))) s /\
  (forall cap1 t ok1, PjGrammar.jbind (PjGrammar.jrealloc (56 * cap) (56 * c'))%nat (fun _ =>
      if o then PjGrammar.jbind (PjGrammar.jrealloc (8 * cap) (8 * c'))%nat (fun _ => PjGrammar.jret c')
      else PjGrammar.jret c') ok = (Some cap1, t, ok1) ->
     cap1 <> 0%nat /\ In (56 * cap1)%nat (fold_left lsz_evR t s) /\
     (o = true -> In (8 * cap1)%nat (fold_left lsz_evR t s))).
Proof.
  intros o cap c' ok s Hc0 Hc2 H. split.
  - apply vv_lz_bind.
    + apply vv_lz_realloc_hits. intros HA. apply (proj1 (H ltac:(lia))).
    + intros u t1 ok2 E1. apply vv_lz_realloc_tr in E1. subst t1. cbn [fold_left]. cbv beta.
      destruct o; cbv beta iota; [|exact I].
      apply vv_lz_bind; [|intros; exact I].
      apply vv_lz_realloc_hits. intros HB.
      apply vv_lz_in_grow_old; [apply (proj2 (H ltac:(lia)) eq_refl)|lia].
  - intros cap1 t ok1 E.
    apply PjGrammar.jbind_some in E. destruct E as (u & t1 & ok2 & t2 & E1 & E2 & ->).
    apply vv_lz_realloc_tr in E1. subst t1.
    destruct o; cbv beta iota in E2.
    + apply PjGrammar.jbind_some in E2. destruct E2 as (u' & t3 & ok3 & t4 & E3 & E4 & ->).
      apply vv_lz_realloc_tr in E3. subst t3. cbv beta delta [PjGrammar.jret] in E4.
      inversion E4; subst. cbn [app fold_left].
      split; [lia|]. split.
      * apply vv_lz_in_grow_old; [apply vv_lz_in_grow_new|lia].
      * intros _. apply vv_lz_in_grow_new.
    + cbv beta delta [PjGrammar.jret] in E2. inversion E2; subst. cbn [app fold_left].
      split; [lia|]. split; [apply vv_lz_in_grow_new|intros Hf; discriminate Hf].
Qed.

Lemma vv_lz_grow : forall o n cap ok s,
  (cap <> 0%nat -> In (56 * cap)%nat s /\ (o = true -> In (8 * cap)%nat s)) ->
  vv_hits (snd (fst (PjGrammar.grow o n cap ok))) s /\
  (forall cap1 t ok1, PjGrammar.grow o n cap ok = (Some cap1, t, ok1) ->
     cap1 <> 0%nat /\ In (56 * cap1)%nat (fold_left lsz_evR t s) /\
     (o = true -> In (8 * cap1)%nat (fold_left lsz_evR t s))).
Proof.
  intros o n cap ok s H. unfold PjGrammar.grow.
  destruct (Nat.ltb n cap) eqn:Hlt; cbv beta iota zeta.
  - apply Nat.ltb_lt in Hlt. split; [exact I|].
    intros cap1 t ok1 E. cbv beta delta [PjGrammar.jret] in E. inversion E; subst.
    cbn [fold_left]. split; [lia|]. apply H. lia.
  - destruct (Nat.eqb cap 0) eqn:Ec; cbv beta iota; apply vv_lz_grow_core; try exact H.
    + apply Nat.eqb_eq in Ec. lia.
    + apply Nat.eqb_eq in Ec. lia.
    + apply Nat.eqb_neq in Ec. lia.
    + apply Nat.eqb_neq in Ec. lia.
Qed.

(* the grammar, by fuel: a value's trace from any live set; a loop's trace from a live set holding its arrays *)
Lemma vv_lz_fuel : forall (st : list Z -> Z * Z) f,
  (forall d x ok s, vv_hits (snd (fst (PjGrammar.jrv st f d x ok))) s) /\
  (forall d o n cap acc y ok s,
     (cap <> 0%nat -> In (56 * cap)%nat s /\ (o = true -> In (8 * cap)%nat s)) ->
     vv_hits (snd (fst (PjGrammar.jrl st f d o n cap acc y ok))) s).
Proof.
  intros st f. induction f as [|f [IHv IHl]].
  - split; intros; exact I.
  - split.
    + intros d x ok s. cbn [PjGrammar.jrv].
      destruct (PjGrammar.skip x) as [|b y]; cbv beta iota; [exact I|].
      destruct (b =? 123); cbv beta iota.
      { apply vv_lz_cont. intros y' ok' s'. apply IHl. intros Hc. exfalso. exact (Hc eq_refl). }
      destruct (b =? 91); cbv beta iota.
      { apply vv_lz_cont. intros y' ok' s'. apply IHl. intros Hc. exfalso. exact (Hc eq_refl). }
      destruct (b =? 34); cbv beta iota.
      { apply vv_lz_bind; [apply vv_lz_jr_string|]. intros [s1 r1] t ok1 _. exact I. }
      destruct (b =? 116); cbv beta iota; [apply vv_lz_lit|].
      destruct (b =? 102); cbv beta iota; [apply vv_lz_lit|].
      destruct (b =? 110); cbv beta iota; [apply vv_lz_lit|].
      apply vv_lz_number.
    + intros d o n cap acc y ok s Hcap. cbn [PjGrammar.jrl].
      destruct (vv_lz_grow o n cap ok s Hcap) as [G1 G2].
      apply vv_lz_bind; [exact G1|].
      intros cap1 t1 ok1 E1. destruct (G2 cap1 t1 ok1 E1) as (C0 & C1 & C2). cbv beta.
      apply vv_lz_bind; [apply vv_lz_jr_name|].
      intros [nm y1] t2 ok2 E2. cbv beta iota.
      assert (T2 : vv_hits t2 []) by (pose proof (vv_lz_jr_name o y ok1 []) as Hn; rewrite E2 in Hn; exact Hn).
      apply vv_lz_bind; [apply IHv|].
      intros [v r] t3 ok3 E3. cbv beta iota.
      assert (T3 : vv_hits t3 []) by (pose proof (IHv d y1 ok2 []) as Hv; rewrite E3 in Hv; exact Hv).
      destruct (PjGrammar.skip r) as [|c r1]; cbv beta iota; [exact I|].
      destruct (c =? 44); cbv beta iota.
      * apply IHl. intros _. split.
        -- apply vv_lz_frame; [exact T3|]. apply vv_lz_frame; [exact T2|]. exact C1.
        -- intros Ho. apply vv_lz_frame; [exact T3|]. apply vv_lz_frame; [exact T2|]. exact (C2 Ho).
      * destruct (c =? PjGrammar.closer o); exact I.
Qed.

Lemma vv_jr_value_hits : forall (st : list Z -> Z * Z) d x ok,
  vv_hits (snd (fst (PjGrammar.jr_value st d x ok))) [].
Proof.
  intros st d x ok. unfold PjGrammar.jr_value. apply (proj1 (vv_lz_fuel st _)).
Qed.

Lemma vv_lszR_app : forall (st : list Z -> Z * Z) d x ok tr1,
  Permutation (lszR (tr1 ++ snd (fst (PjGrammar.jr_value st d x ok))))
              (lszR tr1 ++ lszR (snd (fst (PjGrammar.jr_value st d x ok)))).
Proof.
  intros st d x ok tr1. unfold lszR. rewrite fold_left_app.
  pose proof (vv_lsz_app (snd (fst (PjGrammar.jr_value st d x ok))) (fold_left lsz_evR tr1 []) []
                (vv_jr_value_hits st d x ok)) as H.
  rewrite app_nil_r in H. exact H.
Qed.


(* ==== IvalM: pure facts for the parse_value call of parse_items' element step (row 231) ==== *)



(* a granted run of an agreeing computation: the oracle run, the granted prefix, and every tail *)

(* the outcomes of a granted prefix are the plain `true`s *)

(* ---- the rest a reader returns is a suffix of the text it read ---- *)
Definition vv_sfx (r x : list Z) : Prop := exists k, r = skipn k x.

Lemma vv_skipn_skipn : forall (x : list Z) (a b : nat), skipn a (skipn b x) = skipn (b + a) x.
Proof.
  induction x as [|c x IH]; intros a b.
  - rewrite !skipn_nil. reflexivity.
  - destruct b as [|b]; [reflexivity|]. simpl. apply IH.
Qed.

Lemma vv_skipn_len_app : forall (a b : list Z), skipn (length a) (a ++ b) = b.
Proof. induction a as [|c a IH]; intros b; [reflexivity|]. simpl. apply IH. Qed.

Lemma vv_sfx_refl : forall x, vv_sfx x x.
Proof. intros x. unfold vv_sfx. exists 0%nat. reflexivity. Qed.

Lemma vv_sfx_trans : forall r y x, vv_sfx r y -> vv_sfx y x -> vv_sfx r x.
Proof. unfold vv_sfx. intros r y x [a ->] [b ->]. exists (b + a)%nat. apply vv_skipn_skipn. Qed.

Lemma vv_sfx_cons : forall b r x, vv_sfx (b :: r) x -> vv_sfx r x.
Proof.
  intros b r x H. apply (vv_sfx_trans r (b :: r) x); [|exact H].
  unfold vv_sfx. exists 1%nat. reflexivity.
Qed.

Lemma vv_sfx_skip : forall x, vv_sfx (PjGrammar.skip x) x.
Proof.
  induction x as [|b r IH]; cbn [PjGrammar.skip]; [apply vv_sfx_refl|].
  destruct (PjGrammar.ws b); [|apply vv_sfx_refl].
  apply (vv_sfx_trans _ r); [exact IH|]. unfold vv_sfx. exists 1%nat. reflexivity.
Qed.

Lemma vv_sfx_tl : forall x, vv_sfx (tl x) x.
Proof. unfold vv_sfx. intros [|b r]; [exists 0%nat | exists 1%nat]; reflexivity. Qed.

Lemma vv_sfx_string : forall z ok s r t ok', PjGrammar.jr_string z ok = (Some (s, r), t, ok') -> vv_sfx r z.
Proof.
  intros z ok s r t ok' H. pose proof (PjGrammar.jr_string_spec z ok) as Hs. rewrite H in Hs.
  destruct Hs as (q & _ & Hd & _). destruct (PjGrammar.decode_stop _ _ _ Hd) as (q' & _ & Hr & _).
  unfold vv_sfx. exists (S q'). exact Hr.
Qed.

Lemma vv_sfx_name : forall o y ok nm y1 t ok', PjGrammar.jr_name o y ok = (Some (nm, y1), t, ok') -> vv_sfx y1 y.
Proof.
  intros o y ok nm y1 t ok' H. unfold PjGrammar.jr_name in H. destruct o.
  - destruct (PjGrammar.skip y) as [|b z] eqn:Ey; [unfold PjGrammar.jrefuse in H; discriminate H|].
    destruct (b =? 34); [|unfold PjGrammar.jrefuse in H; discriminate H].
    apply PjGrammar.jbind_some in H as ([name r] & t1 & ok1 & t2 & Es & H & _).
    cbv beta iota in H.
    assert (Hz : vv_sfx z y) by (apply (vv_sfx_cons b); rewrite <- Ey; apply vv_sfx_skip).
    pose proof (vv_sfx_string _ _ _ _ _ _ Es) as Hr.
    destruct (PjGrammar.skip r) as [|c r1] eqn:Er.
    + unfold PjGrammar.jbind, PjGrammar.jfree, PjGrammar.jrefuse in H. cbv beta iota in H. discriminate H.
    + assert (Hr1 : vv_sfx r1 y).
      { apply (vv_sfx_trans _ r); [|exact (vv_sfx_trans _ _ _ Hr Hz)].
        apply (vv_sfx_cons c). rewrite <- Er. apply vv_sfx_skip. }
      destruct (c =? 58).
      * unfold PjGrammar.jret in H. cbv beta in H. inversion H; subst. exact Hr1.
      * unfold PjGrammar.jbind, PjGrammar.jfree, PjGrammar.jrefuse in H. cbv beta iota in H. discriminate H.
  - unfold PjGrammar.jret in H. cbv beta in H. inversion H; subst. apply vv_sfx_refl.
Qed.

Lemma vv_sfx_lit : forall w v x ok u r t ok', PjGrammar.lit w v x ok = (Some (u, r), t, ok') -> vv_sfx r x.
Proof.
  intros w v x ok u r t ok' H. unfold PjGrammar.lit in H.
  destruct (PjGrammar.prefixb w x); [|unfold PjGrammar.jrefuse in H; discriminate H].
  unfold PjGrammar.jret in H. cbv beta in H. inversion H; subst. unfold vv_sfx. exists (length w). reflexivity.
Qed.

Lemma vv_sfx_number : forall st x ok u r t ok', PjGrammar.jr_number st x ok = (Some (u, r), t, ok') -> vv_sfx r x.
Proof.
  intros st x ok u r t ok' H. unfold PjGrammar.jr_number in H. cbv zeta in H.
  destruct (skipn _ x) as [|c z] eqn:Ez; cbv beta iota in H; [unfold PjGrammar.jrefuse in H; discriminate H|].
  destruct (negb (PjGrammar.digit c)); cbv beta iota in H; [unfold PjGrammar.jrefuse in H; discriminate H|].
  destruct ((c =? 48) && _); cbv beta iota in H; [unfold PjGrammar.jrefuse in H; discriminate H|].
  destruct (PjGrammar.span PjGrammar.numch z) as [a r'] eqn:Es. cbv beta iota in H.
  assert (Hr : vv_sfx r' x).
  { apply (vv_sfx_trans _ z).
    - unfold vv_sfx. exists (length a). rewrite (PjGrammar.span_app _ _ _ _ Es). symmetry. apply vv_skipn_len_app.
    - apply (vv_sfx_cons c). rewrite <- Ez. unfold vv_sfx. eexists. reflexivity. }
  apply PjGrammar.jbind_some in H as (u0 & t1 & ok1 & t2 & _ & H & _). cbv beta in H.
  destruct (PjGrammar.whole _ _); [|unfold PjGrammar.jrefuse in H; discriminate H].
  unfold PjGrammar.jret in H. cbv beta in H. inversion H; subst. exact Hr.
Qed.

Lemma vv_sfx_cont :
  forall (loop : nat -> bool -> nat -> nat -> list (list Z * jv) -> list Z -> PjGrammar.M (jv * list Z))
         d o x ok t r tr ok',
  (forall o' n cap acc y ok1 t1 r1 tr1 ok2, loop (S d) o' n cap acc y ok1 = (Some (t1, r1), tr1, ok2) ->
     vv_sfx r1 y) ->
  PjGrammar.jr_cont loop d o x ok = (Some (t, r), tr, ok') -> vv_sfx r x.
Proof.
  intros loop d o x ok t r tr ok' HL H. unfold PjGrammar.jr_cont in H.
  destruct (Nat.ltb PjGrammar.MAXD (S d)); cbv beta iota in H; [unfold PjGrammar.jrefuse in H; discriminate H|].
  cbv zeta in H.
  pose proof (vv_sfx_trans _ _ _ (vv_sfx_skip (tl x)) (vv_sfx_tl x)) as Hy.
  destruct (PjGrammar.skip (tl x)) as [|c r0] eqn:Ey; cbv beta iota in H.
  - exact (vv_sfx_trans _ _ _ (HL _ _ _ _ _ _ _ _ _ _ H) Hy).
  - destruct (c =? PjGrammar.closer o); cbv beta iota in H.
    + unfold PjGrammar.jret in H. cbv beta in H. inversion H; subst. exact (vv_sfx_cons _ _ _ Hy).
    + exact (vv_sfx_trans _ _ _ (HL _ _ _ _ _ _ _ _ _ _ H) Hy).
Qed.

Lemma vv_sfx_fuel : forall st f,
  (forall d x ok t r tr ok', PjGrammar.jrv st f d x ok = (Some (t, r), tr, ok') -> vv_sfx r x) /\
  (forall d o n cap acc y ok t r tr ok', PjGrammar.jrl st f d o n cap acc y ok = (Some (t, r), tr, ok') ->
     vv_sfx r y).
Proof.
  intros st f. induction f as [|f [IHv IHl]].
  - split; intros; cbn [PjGrammar.jrv PjGrammar.jrl] in *; unfold PjGrammar.jrefuse in *; discriminate.
  - split.
    + intros d x ok t r tr ok' H. cbn [PjGrammar.jrv] in H.
      destruct (PjGrammar.skip x) as [|b y] eqn:Ex; cbv beta iota in H;
        [unfold PjGrammar.jrefuse in H; discriminate H|].
      assert (Hs : vv_sfx (b :: y) x) by (rewrite <- Ex; apply vv_sfx_skip).
      destruct (b =? 123); cbv beta iota in H.
      { exact (vv_sfx_trans _ _ _ (vv_sfx_cont (PjGrammar.jrl st f) _ _ _ _ _ _ _ _
          (fun o' n0 cap0 acc0 y0 ok1 t1 r1 tr1 ok2 => IHl (S d) o' n0 cap0 acc0 y0 ok1 t1 r1 tr1 ok2) H) Hs). }
      destruct (b =? 91); cbv beta iota in H.
      { exact (vv_sfx_trans _ _ _ (vv_sfx_cont (PjGrammar.jrl st f) _ _ _ _ _ _ _ _
          (fun o' n0 cap0 acc0 y0 ok1 t1 r1 tr1 ok2 => IHl (S d) o' n0 cap0 acc0 y0 ok1 t1 r1 tr1 ok2) H) Hs). }
      destruct (b =? 34); cbv beta iota in H.
      { apply PjGrammar.jbind_some in H as ([s r1] & t1 & ok1 & t2 & Es & H & _). cbv beta iota in H.
        unfold PjGrammar.jret in H. cbv beta in H. inversion H; subst.
        exact (vv_sfx_trans _ _ _ (vv_sfx_string _ _ _ _ _ _ Es) (vv_sfx_cons _ _ _ Hs)). }
      destruct (b =? 116); cbv beta iota in H.
      { exact (vv_sfx_trans _ _ _ (vv_sfx_lit _ _ _ _ _ _ _ _ H) Hs). }
      destruct (b =? 102); cbv beta iota in H.
      { exact (vv_sfx_trans _ _ _ (vv_sfx_lit _ _ _ _ _ _ _ _ H) Hs). }
      destruct (b =? 110); cbv beta iota in H.
      { exact (vv_sfx_trans _ _ _ (vv_sfx_lit _ _ _ _ _ _ _ _ H) Hs). }
      exact (vv_sfx_trans _ _ _ (vv_sfx_number _ _ _ _ _ _ _ H) Hs).
    + intros d o n cap acc y ok t r tr ok' H. cbn [PjGrammar.jrl] in H.
      apply PjGrammar.jbind_some in H as (cap1 & tg & ok1 & t2 & _ & H & _). cbv beta in H.
      apply PjGrammar.jbind_some in H as ([nm y1] & tn & ok2 & t3 & En & H & _). cbv beta iota in H.
      apply PjGrammar.jbind_some in H as ([v r0] & tv & ok3 & t4 & Ev & H & _). cbv beta iota in H.
      pose proof (vv_sfx_name _ _ _ _ _ _ _ En) as Hy1.
      pose proof (IHv d y1 ok2 v r0 tv ok3 Ev) as Hr0.
      destruct (PjGrammar.skip r0) as [|c r1] eqn:Er; cbv beta iota in H;
        [unfold PjGrammar.jrefuse in H; discriminate H|].
      assert (Hs : vv_sfx r1 y).
      { apply (vv_sfx_trans _ r0); [|exact (vv_sfx_trans _ _ _ Hr0 Hy1)].
        apply (vv_sfx_cons c). rewrite <- Er. apply vv_sfx_skip. }
      destruct (c =? 44); cbv beta iota in H.
      { exact (vv_sfx_trans _ _ _ (IHl _ _ _ _ _ _ _ _ _ _ _ H) Hs). }
      destruct (c =? PjGrammar.closer o); cbv beta iota in H; [|unfold PjGrammar.jrefuse in H; discriminate H].
      unfold PjGrammar.jret in H. cbv beta in H. inversion H; subst. exact Hs.
Qed.

(* the rest after a value is a suffix of the text it read *)
Lemma vv_value_suffix : forall d x ok t r tr ok',
  PjGrammar.jr_value prh_jr_strtod d x ok = (Some (t, r), tr, ok') -> exists k, r = skipn k x.
Proof.
  intros d x ok t r tr ok' H. unfold PjGrammar.jr_value in H.
  exact (proj1 (vv_sfx_fuel prh_jr_strtod _) d x ok t r tr ok' H).
Qed.

(* ---- the reader monad's bind over a known first run ---- *)
Lemma vv_jbind_some_run : forall (A C : Type) (m : PjGrammar.M A) (k : A -> PjGrammar.M C) ok a t ok1,
  m ok = (Some a, t, ok1) ->
  PjGrammar.jbind m k ok = (fst (fst (k a ok1)), t ++ snd (fst (k a ok1)), snd (k a ok1)).
Proof.
  intros A C m k ok a t ok1 H. unfold PjGrammar.jbind. rewrite H.
  destruct (k a ok1) as [[r t'] ok2]. reflexivity.
Qed.

Lemma vv_jbind_none_run : forall (A C : Type) (m : PjGrammar.M A) (k : A -> PjGrammar.M C) ok t ok1,
  m ok = (None, t, ok1) -> PjGrammar.jbind m k ok = (None, t, ok1).
Proof. intros A C m k ok t ok1 H. unfold PjGrammar.jbind. rewrite H. reflexivity. Qed.

(* ---- block sizes are not negative ---- *)
Lemma vv_lsum_nonneg : forall D : list (Z * Z), Forall (fun ak => 0 <= snd ak) D -> 0 <= Ledger.lsum D.
Proof.
  induction D as [|[a k] D IH]; intros H; cbn [Ledger.lsum]; [lia|].
  inversion H as [|? ? H1 H2]; subst. cbn [snd] in H1. specialize (IH H2). lia.
Qed.

Lemma vv_D_sizes : forall (D : list (Z * Z)) (L : list nat),
  Permutation (map snd D) (map Z.of_nat L) -> Forall (fun ak => 0 <= snd ak) D.
Proof.
  intros D L HP. apply Forall_forall. intros ak Hin.
  assert (H1 : In (snd ak) (map Z.of_nat L)) by (apply (Permutation_in _ HP); apply in_map; exact Hin).
  apply in_map_iff in H1. destruct H1 as (n & Hn & _). lia.
Qed.

(* the entry text is not empty: the opener is at the entry cursor *)
Lemma vv_skipn_nth : forall (l : list Z) (n : nat) a, nth_error l n = Some a -> skipn n l = a :: skipn (S n) l.
Proof.
  induction l as [|b l IH]; intros n a H; [destruct n; discriminate H|].
  destruct n as [|n]; cbn in H |- *.
  - injection H as Hb. rewrite Hb. reflexivity.
  - apply IH. exact H.
Qed.

Lemma vv_req_ge : forall n, n <= req_size n.
Proof. intros n. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

(* ---- THE KIT'S CUT: the model's FREE LIST (PresetReqAt.jfv / jfl) of a run depends only on the outcomes of the calls the
   run makes, as the run itself does (PjGrammar.agrees). COPIED, names prefixed, PjGrammar names qualified:
   vv_split_call_uniq / vv_agrees_det are lib/Prog/parse_items_model.v split_call_uniq / agrees_det (that file is not in
   this unit's import graph); vv_bind_det / vv_jfc_det / vv_jf_det are a Theorem Labs lane's PItems_value_model.v pvm_bind_det
   / pvm_jfc_det / pvm_jf_det (a working branch 34d46afa0965, Qed there) ---- *)
Lemma vv_split_call_uniq : forall P1 e R P1' e' R', P1 ++ e :: R = P1' ++ e' :: R' ->
  PjGrammar.calls P1 = PjGrammar.calls P1' -> PjGrammar.is_call e = true -> PjGrammar.is_call e' = true ->
  P1 = P1' /\ e = e'.
Proof.
  induction P1 as [|x P1 IH]; intros e R P1' e' R' H Hc He He'; destruct P1' as [|y P1'];
    cbn [app PjGrammar.calls] in *.
  - injection H as -> _. auto.
  - injection H as Hy _. subst y. rewrite He in Hc. discriminate.
  - injection H as Hx _. subst x. rewrite He' in Hc. discriminate.
  - injection H as Hxy H'. subst y.
    destruct (PjGrammar.is_call x); [injection Hc as Hc|];
      destruct (IH _ _ _ _ _ H' Hc He He') as [-> ->]; auto.
Qed.

Lemma vv_agrees_det : forall (A : Type) (m : PjGrammar.M A) ok1 ok2 r t o1, PjGrammar.agrees m ->
  m ok1 = (r, t, o1) ->
  (forall i, (i < PjGrammar.calls t)%nat -> nth i ok2 true = nth i ok1 true) ->
  m ok2 = (r, t, skipn (PjGrammar.calls t) ok2).
Proof.
  intros A m ok1 ok2 r t o1 H E Hag.
  pose proof (PjGrammar.agrees_nil A m H) as N0.
  pose proof (proj1 (H ok1)) as K1. pose proof (proj2 (H ok1)) as K1'.
  pose proof (proj1 (H ok2)) as K2. pose proof (proj2 (H ok2)) as K2'.
  destruct (m []) as [[r0 t0] o0] eqn:E0. cbn [fst snd] in *.
  destruct (PjGrammar.ok_upto_dec ok1 (PjGrammar.calls t0)) as [Hu|(j & Hj & Hf & Hu)].
  - rewrite (K1 Hu) in E. injection E as <- <- _.
    apply K2. intros i Hi. rewrite Hag by exact Hi. apply Hu. exact Hi.
  - destruct (K1' j Hj Hf Hu) as (P1 & e & rest & Em & Et & Hc & Hic).
    rewrite Em in E. injection E as <- <- _.
    assert (CP : PjGrammar.calls (P1 ++ [PjGrammar.EFail (PjGrammar.esize e)]) = S j)
      by (rewrite PjGrammar.calls_app; cbn [PjGrammar.calls PjGrammar.is_call]; lia).
    rewrite CP in Hag |- *.
    assert (Hf2 : nth j ok2 true = false) by (rewrite Hag by lia; exact Hf).
    assert (Hu2 : PjGrammar.ok_upto ok2 j) by (intros i Hi; rewrite Hag by lia; apply Hu; exact Hi).
    destruct (K2' j Hj Hf2 Hu2) as (P1' & e' & rest' & Em' & Et' & Hc' & Hic').
    rewrite Et in Et'. destruct (vv_split_call_uniq _ _ _ _ _ _ Et' ltac:(lia) Hic Hic') as [<- <-].
    exact Em'.
Qed.

Lemma vv_bind_det : forall (A C : Type) (m : PjGrammar.M A) (k : A -> PjGrammar.M C) ok ok' r t1 ok1,
  PjGrammar.agrees m -> m ok = (r, t1, ok1) ->
  (forall i, (i < PjGrammar.calls (snd (fst (PjGrammar.jbind m k ok))))%nat -> nth i ok' true = nth i ok true) ->
  m ok' = (r, t1, skipn (PjGrammar.calls t1) ok') /\ ok1 = skipn (PjGrammar.calls t1) ok /\
  (forall i, (i < PjGrammar.calls t1)%nat -> nth i ok' true = nth i ok true) /\
  (forall a, r = Some a -> forall i, (i < PjGrammar.calls (snd (fst (k a ok1))))%nat ->
     nth i (skipn (PjGrammar.calls t1) ok') true = nth i ok1 true).
Proof.
  intros A C m k ok ok' r t1 ok1 Hm E Hag.
  assert (Hall : forall i, (i < PjGrammar.calls t1)%nat -> nth i ok' true = nth i ok true).
  { intros i Hi. apply Hag. unfold PjGrammar.jbind. rewrite E. destruct r as [a|]; cbn [fst snd]; [|exact Hi].
    destruct (k a ok1) as [[r2 t2] ok2]. cbn [fst snd]. rewrite PjGrammar.calls_app. lia. }
  pose proof (vv_agrees_det A m ok ok' r t1 ok1 Hm E Hall) as E'.
  pose proof (vv_agrees_det A m ok ok r t1 ok1 Hm E (fun i _ => eq_refl)) as E''. rewrite E in E''.
  injection E'' as Eo.
  split; [exact E'|]. split; [exact Eo|]. split; [exact Hall|].
  intros a -> i Hi. destruct (k a ok1) as [[r2 t2] ok2] eqn:Ek. cbn [fst snd] in Hi.
  rewrite PjGrammar.nth_skipn_b, Eo, PjGrammar.nth_skipn_b. apply Hag. unfold PjGrammar.jbind. rewrite E.
  cbn [fst snd]. rewrite Ek. cbn [fst snd]. rewrite PjGrammar.calls_app. lia.
Qed.

Lemma vv_jfc_det : forall sm f d o x ok ok' r t o1,
  (forall d' o' n cap acc af y ok ok',
     (forall i, (i < PjGrammar.calls (snd (fst (PjGrammar.jrl sm f d' o' n cap acc y ok))))%nat ->
        nth i ok' true = nth i ok true) ->
     PresetReqAt.jfl sm f d' o' n cap af y ok' = PresetReqAt.jfl sm f d' o' n cap af y ok) ->
  PjGrammar.jr_cont (PjGrammar.jrl sm f) d o x ok = (r, t, o1) ->
  (forall i, (i < PjGrammar.calls t)%nat -> nth i ok' true = nth i ok true) ->
  PresetReqAt.jf_cont (PresetReqAt.jfl sm f) d o x ok' = PresetReqAt.jf_cont (PresetReqAt.jfl sm f) d o x ok.
Proof.
  intros sm f d o x ok ok' r t o1 IH E Hag. unfold PresetReqAt.jf_cont. unfold PjGrammar.jr_cont in E.
  destruct (Nat.ltb PjGrammar.MAXD (S d)); [reflexivity|]. cbv zeta in E |- *.
  destruct (PjGrammar.skip (tl x)) as [|c r0].
  - apply (IH (S d) o 0%nat 0%nat [] [] [] ok ok'). rewrite E. exact Hag.
  - destruct (c =? PjGrammar.closer o); [reflexivity|].
    apply (IH (S d) o 0%nat 0%nat [] [] (c :: r0) ok ok'). rewrite E. exact Hag.
Qed.

Lemma vv_jf_det : forall sm f,
  (forall d x ok ok', (forall i, (i < PjGrammar.calls (snd (fst (PjGrammar.jrv sm f d x ok))))%nat ->
                                 nth i ok' true = nth i ok true) ->
     PresetReqAt.jfv sm f d x ok' = PresetReqAt.jfv sm f d x ok) /\
  (forall d o n cap acc af y ok ok',
     (forall i, (i < PjGrammar.calls (snd (fst (PjGrammar.jrl sm f d o n cap acc y ok))))%nat ->
        nth i ok' true = nth i ok true) ->
     PresetReqAt.jfl sm f d o n cap af y ok' = PresetReqAt.jfl sm f d o n cap af y ok).
Proof.
  intros sm f. induction f as [|f [IHv IHl]]; [split; intros; reflexivity|]. split.
  - intros d x ok ok' Hag.
    destruct (PjGrammar.jrv sm (S f) d x ok) as [[r t] o1] eqn:EJ0. cbn [fst snd] in Hag.
    pose proof (vv_agrees_det _ _ ok ok' r t o1 (proj1 (PjGrammar.agrees_fuel sm (S f)) d x) EJ0 Hag) as EJ1.
    cbn [PresetReqAt.jfv]. rewrite EJ1, EJ0. cbn [PjGrammar.jrv] in EJ0.
    destruct (PjGrammar.skip x) as [|b y]; cbv beta iota in EJ0 |- *; [reflexivity|].
    destruct (b =? 123); cbv beta iota in EJ0 |- *;
      [exact (vv_jfc_det sm f d true (b :: y) ok ok' r t o1 IHl EJ0 Hag)|].
    destruct (b =? 91); cbv beta iota in EJ0 |- *;
      [exact (vv_jfc_det sm f d false (b :: y) ok ok' r t o1 IHl EJ0 Hag)|].
    reflexivity.
  - intros d o n cap acc af y ok ok' Hag. cbn [PjGrammar.jrl] in Hag. cbn [PresetReqAt.jfl].
    destruct (PjGrammar.grow o n cap ok) as [[g tg] okg] eqn:EG.
    destruct (vv_bind_det _ _ (PjGrammar.grow o n cap) _ ok ok' g tg okg (PjGrammar.agrees_grow o n cap) EG Hag)
      as (EG' & _ & _ & Hag1).
    rewrite EG'. destruct g as [cap1|]; cbv beta iota; [|reflexivity].
    specialize (Hag1 cap1 eq_refl). cbv beta in Hag1.
    destruct (PjGrammar.jr_name o y okg) as [[nr tn] okn] eqn:EN.
    destruct (vv_bind_det _ _ (PjGrammar.jr_name o y) _ okg (skipn (PjGrammar.calls tg) ok') nr tn okn
                (PjGrammar.agrees_jr_name o y) EN Hag1) as (EN' & _ & _ & Hag2).
    rewrite EN'. destruct nr as [[nm y1]|]; cbv beta iota; [|reflexivity].
    specialize (Hag2 (nm, y1) eq_refl). cbv beta iota in Hag2.
    destruct (PjGrammar.jrv sm f d y1 okn) as [[rv tv] okv] eqn:EV.
    destruct (vv_bind_det _ _ (PjGrammar.jrv sm f d y1) _ okn
                (skipn (PjGrammar.calls tn) (skipn (PjGrammar.calls tg) ok')) rv tv okv
                (proj1 (PjGrammar.agrees_fuel sm f) d y1) EV Hag2) as (EV' & _ & HallV & Hag3).
    rewrite (IHv d y1 okn (skipn (PjGrammar.calls tn) (skipn (PjGrammar.calls tg) ok'))
               ltac:(rewrite EV; exact HallV)).
    rewrite EV'. destruct rv as [[v r]|]; cbv beta iota; [|reflexivity].
    specialize (Hag3 (v, r) eq_refl). cbv beta iota in Hag3.
    destruct (PjGrammar.skip r) as [|c r1]; cbv beta iota in Hag3 |- *; [reflexivity|].
    destruct (c =? 44); cbv beta iota in Hag3 |- *; [|reflexivity].
    exact (IHl d o (S n) cap1 ((nm, v) :: acc) _ r1 okv _ Hag3).
Qed.

(* the free list of a value run, at two outcome lists that agree on the run's calls *)
Lemma vv_jfv_det : forall sm f d x ok ok' r t o1, PjGrammar.jrv sm f d x ok = (r, t, o1) ->
  (forall i, (i < PjGrammar.calls t)%nat -> nth i ok' true = nth i ok true) ->
  PresetReqAt.jfv sm f d x ok' = PresetReqAt.jfv sm f d x ok.
Proof. intros sm f d x ok ok' r t o1 Hj H. apply (proj1 (vv_jf_det sm f)). rewrite Hj. exact H. Qed.

(* pj_kidsR over one more element (a Theorem Labs lane's PItems_value_model.v pvm_kids_snoc, copied) *)
Lemma vv_kids_snoc : forall (A : Type) (Pk : Z -> A -> Prop) (l : list A) a x,
  pj_kidsR Pk a (l ++ [x]) <-> pj_kidsR Pk a l /\ Pk (a + 56 * Z.of_nat (length l)) x.
Proof.
  intros A Pk l. induction l as [|y l IH]; intros a x; cbn [app pj_kidsR length].
  - replace (a + 56 * Z.of_nat 0) with a by lia. tauto.
  - rewrite IH. replace (a + 56 + 56 * Z.of_nat (length l)) with (a + 56 * Z.of_nat (S (length l))) by lia. tauto.
Qed.

(* the closer's depth: a container of the members acc fits depth n' exactly when n' = S nn with every member at
   most nn deep (a Theorem Labs lane's PItems_forder.v pi_forder_mk, copied) *)
Lemma vv_mk_depth : forall o (acc : list (list Z * jv)) n', (PjTree.depth (PjGrammar.mk o (rev acc)) <= n')%nat ->
  exists nn, n' = S nn /\ Forall (fun mb => (PjTree.depth (snd mb) <= nn)%nat) acc.
Proof.
  intros o acc n' H. destruct n' as [|nn].
  - exfalso. destruct o; unfold PjGrammar.mk in H; cbn [PjTree.depth] in H; clear - H; lia.
  - exists nn. split; [reflexivity|]. apply Forall_forall. intros [nm u] Hin. cbn [snd].
    apply in_rev in Hin. destruct o; unfold PjGrammar.mk in H.
    + pose proof (PjTree.depth_member (rev acc) nm u Hin) as Hd. clear - H Hd; lia.
    + pose proof (PjTree.depth_item (map snd (rev acc)) u (in_map snd (rev acc) (nm, u) Hin)) as Hd. clear - H Hd; lia.
Qed.


Section V.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}
        {HL : Z}.
#[local] Notation PAI := PI_prog_A.
#[local] Notation PLA := PL_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PAI).
#[local] Notation VAL := (@pa_val _ A_prog_listing PAI).
#[local] Notation BASE := (@pa_val _ A_prog_listing PAI A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.

(* ---- seat 1, slot 6142 (row 210): parse_items' frame (atom 2) with the thirteen saved words and the spill slot
   sp + 24 = shadow(v + 24); the node v (atom 20) with its kids pointer (atom 45) and count (atom 46), its count
   word writable (row 236); s2 = shadow(v + 40), s6 = v + 40, s8 = v + 24 ---- *)
Definition vv_E1 (E : vrd_ient) (P : vrd_ipos) : env :=
  @Eimg _ A_prog_listing PAI (Ereg (ip_regs P) (vi_extras (ie_regs E) ++ [w64 (ip_kids P); w64 (ip_n P)])).
Definition vv_frame1 : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 144 0 0 (vi_frame_chunks ++ [YP09.mkChunk 24 (CVal 8 (vv_sh 20 24))]).
(* the node region; its count word [40, 48) is writable when w (the row-236 store), read-only otherwise *)
Definition vv_node1 (w : bool) : YP09.region :=
  YP09.mkRegion (Some 20%nat) 0 56 (if w then 40 else 0) (if w then 48 else 0)
    [YP09.mkChunk 24 (CVal 8 (SOff 45 0)); YP09.mkChunk 40 (CVal 8 (SOff 46 0))].
Definition vv_regs1 : list sv :=
  sr_set (sr_set (sr_set sr_atoms 18%bv (vv_sh 20 40)) 22%bv (SOff 20 40)) 24%bv (SOff 20 24).
Definition vv_facts1 : facts :=
  mkFacts [(20%nat, mkAF 4096 (2 ^ 47 - 57) 3); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition vv_SH1 : list shent := [mkSHE 20 0 56].
Definition vv_ss1 (w : bool) (k : nat) : sstate :=
  mkSS (4 * Z.of_nat k) vv_regs1 [vv_frame1; vv_node1 w] None vv_facts1.

Lemma vv_E1_low : forall E P (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (vv_E1 E P) n = getr (ip_regs P) r.
Proof.
  intros E P n r Hn. unfold vv_E1.
  assert (Hlt : (n < 32)%nat) by (pose proof (u5_range r); lia).
  rewrite (Eimg_low (PI := PAI) _ n) by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat _ _ n r Hn).
Qed.

Lemma vv_E1_extra : forall E P j, (j < 13)%nat ->
  ew (vv_E1 E P) (32 + j) = nth j (vi_extras (ie_regs E)) (Z_to_bv 64 0).
Proof.
  intros E P j Hj. unfold vv_E1.
  rewrite (Eimg_low (PI := PAI) _ (32 + j)%nat) by (unfold A_TEXT; lia).
  rewrite ew_Ereg_extra. apply app_nth1. cbn [vi_extras length]. lia.
Qed.

Lemma vv_E1_45 : forall E P, ew (vv_E1 E P) 45 = w64 (ip_kids P).
Proof.
  intros E P. unfold vv_E1. rewrite (Eimg_low (PI := PAI) _ 45) by (unfold A_TEXT; lia).
  change 45%nat with (32 + 13)%nat. rewrite ew_Ereg_extra. reflexivity.
Qed.

Lemma vv_E1_46 : forall E P, ew (vv_E1 E P) 46 = w64 (ip_n P).
Proof.
  intros E P. unfold vv_E1. rewrite (Eimg_low (PI := PAI) _ 46) by (unfold A_TEXT; lia).
  change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra. reflexivity.
Qed.

(* the node conjunct of a value slot, whichever the container *)
Lemma vv_islot_inode : forall E P nm, vrd_islot_a B ARx SK E P nm -> exists Dx, vrd_inode E P Dx.
Proof.
  intros E P nm (_ & _ & _ & _ & _ & _ & HK & _).
  destruct (ie_o E).
  - destruct HK as (x & k & _ & _ & HN). exists [(x, k)]. exact HN.
  - destruct HK as (_ & HN). exists []. exact HN.
Qed.

(* the image numbers this step needs, true at prh_img_A by vm_compute (IproC's H_img form, VrdIElem.vrd_chain_keep's
   two premises): parse_items' own frame is the 144 bytes of row 2, its cursor chain starts at s0 = q, and
   parse_value's frame is not negative *)
Hypothesis H_img : pi_frame F_parse_items = 144 /\ pi_s0cur F_parse_items = Some 0 /\ 0 <= pi_frame F_parse_value.

Lemma vv_leaf : ESTACK <= LEAF_pv_pi.
Proof. unfold LEAF_pv_pi, zmaxl, STK_RT_ECALL. cbn [fold_right]. lia. Qed.

(* the stack budget: memset's window under parse_items' frame, and parse_value one level down, fit in parse_items' *)
Lemma vv_stk_items : forall d, ESTACK + 144 <= STK_parse_items d.
Proof.
  intros d. pose proof vv_leaf as HL0. destruct H_img as (H1 & _ & H3).
  unfold STK_parse_items. rewrite H1. pose proof (Zle_0_nat (PjGrammar.MAXD - d)). nia.
Qed.

Lemma vv_stk_call : forall d, (d < PjGrammar.MAXD)%nat ->
  0 <= STK_parse_value (S d) /\ STK_parse_value (S d) + 144 <= STK_parse_items d.
Proof.
  intros d Hd. pose proof vv_leaf as HL0. destruct H_img as (H1 & _ & H3).
  assert (EV : STK_parse_value (S d) =
    Z.of_nat (PjGrammar.MAXD - d)%nat * (pi_frame F_parse_value + pi_frame F_parse_items) + LEAF_pv_pi)
    by (rewrite <- (vv_maxd_succ d Hd); reflexivity).
  rewrite EV. unfold STK_parse_items. rewrite H1.
  pose proof (Zle_0_nat (PjGrammar.MAXD - d)%nat). unfold ESTACK in HL0. split; nia.
Qed.

Lemma vv_seat_gen : forall (w : bool) (kk : nat) CTX CTX0 CW E P ty num str keys cap,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_iframe E P -> vrd_iregs B E P ->
  pj_hdrR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (ie_v E) ty num str (ip_kids P) keys (ip_n P) cap ->
  range_addressable (aview SEGS (w_H (ip_W P)) (ip_mem P)) SHADOW_OFF (ie_v E) 56 ->
  st_ok_pi (fx := ip_fx P) SEGS VAL (vv_E1 E P) (vv_ss1 w kk)
    (restrict (w_H (ip_W P)) (@YK11.mkst (ip_fx P) (ip_regs P) (w64 (A_IPC kk)) (ip_mem P) (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS (SOff 26 0) vv_SH1 (vv_E1 E P) (mrestrict (w_H (ip_W P)) (ip_mem P)).
Proof.
  intros w kk CTX CTX0 CW E P ty num str keys cap HEN HFR HRG HHDR HRAv.
  pose proof (vrd_node_low B ARx HL LAWS CTX CTX0 CW E HEN) as Hvceil.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (vi_saved_of_iframe E P HFR) as HSV.
  destruct HFR as (Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hshv24 & _ & _).
  destruct HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  destruct HHDR as ((Hv8 & HRWv) & _ & _ & _ & (Hk0 & Hkv) & _ & (Hn64 & Hnv) & _).
  destruct HEN as ((HAFN & _) & _ & _ & _ & HRD & _).
  pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (vv_stk_items (ie_d E)) as HSTKi. unfold ESTACK in HSTKi.
  destruct HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNODE & _).
  destruct HNODE as (Hv4096 & _ & _ & _ & _ & Hvmr & _).
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvmr.
  set (E1 := vv_E1 E P).
  assert (U20 : bv_unsigned (ew E1 20) = ie_v E)
    by (subst E1; rewrite (vv_E1_low E P 20 20%bv eq_refl), G20; unfold w64; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E1 26) = SHADOW_OFF)
    by (subst E1; rewrite (vv_E1_low E P 26 26%bv eq_refl), G26; unfold w64, SHADOW_OFF; apply unsigned_lit_small; lia).
  assert (U2 : bv_unsigned (ew E1 2) = spZ (ie_regs E) - 144)
    by (subst E1; rewrite (vv_E1_low E P 2 2%bv eq_refl); exact Hsp).
  split.
  2:{ unfold sh_ok, vv_SH1. constructor; [|constructor]. unfold shent_ok. cbn [she_m she_lo she_hi].
      rewrite U_SOff, U26, U_SOff, U20. rewrite !Z.add_0_r.
      rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
      rewrite (zcanon_id (ie_v E)) by (unfold M64; lia).
      split; [exact HRAv|].
      unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U_SOff, U_SOff, U20, U26, !Z.add_0_r.
      rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
      rewrite (zcanon_id (ie_v E)) by (unfold M64; lia).
      intros a Ha. change (Z.min 0 56) with 0 in Ha. change (Z.max 0 56) with 56 in Ha.
      unfold SHADOW_OFF in *. lia. }
  rewrite (restrict_mkst_fx (fx := ip_fx P)).
  change (w64 (A_IPC kk)) with (Z_to_bv 64 (BASE + 4 * Z.of_nat kk)).
  unfold vv_ss1. apply (pa_entry_st_ok_full (fx := ip_fx P)).
  - unfold vv_regs1.
    apply vv_regs_ok_set; [apply vv_regs_ok_set; [apply vv_regs_ok_set; [apply regs_ok_Eimg_Ereg|]|]|].
    + rewrite G18, denot_lit_U, (vv_sh_U E1 20 40 (ie_v E) U20 U26) by lia. reflexivity.
    + rewrite G22, denot_lit_U, U_SOff, U20, zcanon_id by (unfold M64; lia). reflexivity.
    + rewrite G24, denot_lit_U, U_SOff, U20, zcanon_id by (unfold M64; lia). reflexivity.
  - destruct w; vm_compute; reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok, vv_frame1.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_app. split.
      * unfold vi_frame_chunks.
        repeat apply Forall_cons; try apply Forall_nil;
        lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
          let j := eval vm_compute in (n - 32)%nat in
          apply (vi_chunk8 _ _ _ _ _ (nth j (vi_extras (ie_regs E)) (Z_to_bv 64 0)));
          [exact (vv_E1_extra E P j ltac:(lia))
          | replace (spZ (ie_regs E) - 144 + off) with (spZ (ie_regs E) - 8 - 8 * Z.of_nat j) by (cbn; lia);
            exact (HSV j ltac:(lia))] end.
      * constructor; [|constructor].
        apply (chunk_ok_val SEGS E1 _ _ 24 8 (vv_sh 20 24) (shadow_addr (ie_v E + 24))).
        -- rewrite denot_lit_U, (vv_sh_U E1 20 24 (ie_v E) U20 U26) by lia. reflexivity.
        -- cbn [Z.of_N]. unfold shadow_addr, SHADOW_OFF.
           pose proof (Z.div_pos (ie_v E + 24) 8). pose proof (Z.div_le_upper_bound (ie_v E + 24) 8 (2 ^ 44)). lia.
        -- cbn [Z.of_N]. lia.
        -- replace (spZ (ie_regs E) - 144 + 24) with (spZ (ie_regs E) - 120) by lia. exact Hshv24.
    + unfold region_ok, vv_node1.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HRWv; destruct w; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (vi_chunk8 _ _ _ _ _ (w64 (ip_kids P))); [exact (vv_E1_45 E P)|].
        unfold w64. rewrite unsigned_lit_small by lia. exact Hkv.
      * apply (vi_chunk8 _ _ _ _ _ (w64 (ip_n P))); [exact (vv_E1_46 E P)|].
        unfold w64. rewrite unsigned_lit_small by lia. exact Hnv.
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | exact (conj I I)].
    unfold extent_disjoint, vv_frame1, vv_node1. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U2, U20. right. lia.
  - unfold vv_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I | exact I]].
    split; [|split; [|exact I]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U20. split; [lia|]. split; [change (2 ^ 3) with 8; exact Hv8 | lia].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U26. split; [lia|]. split; [reflexivity | lia].
Qed.

Lemma vv_seat1 : forall (w : bool) (kk : nat) CTX CTX0 CW E P nm,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_islot_a B ARx SK E P nm ->
  st_ok_pi (fx := ip_fx P) SEGS VAL (vv_E1 E P) (vv_ss1 w kk)
    (restrict (w_H (ip_W P)) (@YK11.mkst (ip_fx P) (ip_regs P) (w64 (A_IPC kk)) (ip_mem P) (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS (SOff 26 0) vv_SH1 (vv_E1 E P) (mrestrict (w_H (ip_W P)) (ip_mem P)).
Proof.
  intros w kk CTX CTX0 CW E P nm HEN HI.
  destruct (vv_islot_inode E P nm HI) as [Dx HN].
  destruct HI as (HFR & HRG & _).
  destruct HN as (HHDR & _ & _ & _ & _ & _ & _ & _ & HRAv & _).
  exact (vv_seat_gen w kk CTX CTX0 CW E P _ _ _ _ _ HEN HFR HRG HHDR HRAv).
Qed.

(* ---- the node's bytes are journal-writable at every loop position: prhReader_at's places at entry, carried to P
   by rd_blocks_move (blocks and frames persist); the window place is empty (vrd_node_low) ---- *)
Lemma vv_v_awr : forall CTX CTX0 CW E P a,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_ijrn B ARx SK E P ->
  ie_v E <= a < ie_v E + 56 ->
  awr_byte (STK_parse_items (ie_d E) + ie_e E) (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
    (ablocks B (ie_ly E) (ie_S E)) (ablocks B (ip_ly P) (ip_S P)) (ip_ly P) [] a
  \/ wr_fp_frame (rd_fp (ie_q E) (ie_v E)) (ie_S E) (ip_ly P) a.
Proof.
  intros CTX CTX0 CW E P a HEN HJN Ha.
  pose proof (vrd_node_low B ARx HL LAWS CTX CTX0 CW E HEN) as Hvceil.
  destruct HEN as ((HAFN & _) & _ & _ & _ & HRD & _).
  destruct HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNODE & _ & _ & _ & HLED & _).
  destruct HNODE as (_ & _ & _ & _ & HATv & _).
  destruct HJN as (HJ & _ & _ & _ & _ & HBM & _).
  destruct HBM as (_ & HABP & HFRP & _).
  pose proof HJ as (_ & Hly & _).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
  assert (HFP : inFP (rd_fp (ie_q E) (ie_v E)) a)
    by (unfold rd_fp; exists (ie_v E, ie_v E + 56); split; [right; right; left; reflexivity | cbn [fst snd]; lia]).
  assert (Hold : forall x, In x (ablocks B (ie_ly E) (ie_S E)) -> In x (ablocks B (ip_ly P) (ip_S P)))
    by (intros x Hx; apply (Permutation_in _ (Permutation_sym HABP)); apply in_or_app; right; exact Hx).
  pose proof (@cf_head_nonneg cp) as Hh0.
  destruct HATv as [(a1 & k1 & Hin1 & Hlo & Hhi) | [(b & m & Hinb & _ & Hlo & Hhi) |
                   [(cid & pos & Hf & Hlo & Hhi) | (Hlo & Hhi)]]].
  - destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a1 k1 _ _ HLED Hin1) as (Hk1 & Hab1 & _).
    left. right. left. split; [exact HFP|]. exists (a1 - cf_head), (k1 + cf_head). split; [exact (Hold _ Hab1)|].
    unfold req_size. destruct (Z.eqb_spec (k1 + cf_head) 0); lia.
  - left. right. left. split; [exact HFP|]. exists b, m. split; [exact (Hold _ Hinb)|].
    unfold req_size. destruct (Z.eqb_spec m 0); lia.
  - right. split; [exact HFP|]. exists cid, pos. split; [exact Hf|].
    unfold in_zr, frame_rng, frame_addr in *. cbn [fst snd]. rewrite EF. lia.
  - exfalso. pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
    pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _). lia.
Qed.

(* ---- PART A: rows 210..223, the memset of kids[n], to the return site row 224 ---- *)
Definition vv_set (E : vrd_ient) (P : vrd_ipos) (nm : list Z) : Prop :=
  vrd_islot_a B ARx SK E P nm /\
  pj_zeroR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (ip_kids P + 56 * ip_n P).

(* __asan_memset (row 223) by the kit's intrinsic text in its m-form (a Theorem Labs lane's YGcallMxmn.v
   aintrin_realizes_xm at OSet: YGcallMx.v's aintrin_realizes_x with the memnorm keep as its last post conjunct), as
   VrdNum carries __asan_memcpy's: one named Section hypothesis until preset's ASan memset row lands; at any float
   state *)
Hypothesis H_checked_memset : forall fx' : YK11.FPState,
  aintrin_realizes_xm (fx := fx') SEGS B ARx OSet (pa_sigma AS___asan_memset).

(* image facts: the harness head is at least one word wide and the engine laws' head width is it (the kit's
   prh_head_wide, discharged by a Theorem Labs lane's preset_head_wide; IelemE's H_HL), and alloc.c's statics are image bytes
   (discharged at prh_img_A by S1ImgA.v pst_in_img_A) *)
Hypothesis H_head : 8 <= cf_head /\ HL = cf_head.
Hypothesis H_pst : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a.
Hypothesis H_s0s : pi_s0cur F_parse_string = Some 0.
(* IelemE's after-call image facts (VrdIStep.v Section S, the same names and statements) *)
Hypothesis H_zsal : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
Hypothesis H_imgvis : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
Hypothesis H_pst_ro : forall a, Exists (in_zr a) prh_pst -> ~ in_roP SEGS pa_relro_lo pa_relro_hi a.

Variables (CTXv CTX0v CWv : list (list Z)).

(* THE MEMORY INVARIANT the step carries (a Theorem Labs lane's generic-P ruling 12:18Z; WalkNumEnd's form): any Pm with the
   runner laws (srr_inv_laws), kept across a call whose text keeps memnorm (srr_inv_call, ruling 12:22Z: the memset
   row and parse_value), and giving memnorm at a call (srr_inv_mn, ruling 12:23Z: parse_value's ENTRY premise
   PRH_FnParse.v:181). The three are a Theorem Labs lane's YSRrMemnorm.v (blob a1c1ece77b14). Its instance, once at
   parse_items' top: Pm m := memnorm segs mem0 -> memnorm segs m (srr_inv_laws_imp over srr_inv_laws_memnorm_k,
   srr_inv_call_imp, srr_inv_mn_imp from parse_items' own entry premise PRH_FnParse.v:252). The inner Section VI
   holds exactly Pm and its three laws, in VrdIElem.tvrd_ival_aG's order, so that the step closes over them as that
   text quantifies them (vrd_ival_okG at the end of this file). *)
Section VI.
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
Hypothesis PCALL : srr_inv_call SEGS Pm.
Hypothesis PMN : srr_inv_mn SEGS Pm.

(* vv_D_apart: sub-lane IvalR (IvalR_sep.v), Qed *)
(* the blocks a loop position owns: no duplicates, live allocator blocks, apart from the image, the node v, the
   text, and from each other *)
Lemma vv_D_apart : forall CTX CTX0 CW E P,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_ijrn B ARx SK E P -> vrd_icur B E P -> vrd_imodel E P ->
  NoDup (ip_D P) /\
  (forall a k, In (a, k) (ip_D P) ->
     0 <= k /\ In (a - cf_head, k + cf_head) (ablocks B (ip_ly P) (ip_S P)) /\
     4096 <= a - cf_head /\ a + k <= alloc_ceiling /\
     (forall x, a - cf_head <= x < a + k ->
        ~ in_img SEGS x /\ ~ (ie_v E <= x < ie_v E + 56) /\ ~ (ie_text E <= x < ie_text E + ie_len E))) /\
  (forall a k a' k', In (a, k) (ip_D P) -> In (a', k') (ip_D P) -> a <> a' ->
     a + k <= a' - cf_head \/ a' + k' <= a - cf_head) /\
  pj_apartR (ip_D P) (ie_v E).
Proof.
  intros CTX CTX0 CW E P HEN HJN HCUR HMOD.
  pose proof cf_head_nonneg as Hcf0.
  destruct HEN as ((HAFN & _) & _ & _ & _ & HRD & _).
  pose proof HAFN as (HARE & _).
  pose proof HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhome & _ & Hnode & _ & _ & Hvwin & HLEDE & _).
  pose proof Hnode as (_ & _ & _ & _ & Hvat & _).
  destruct HJN as (HJ & _ & _ & _ & _ & HBM & _).
  pose proof HJ as (HARP & Hly & _ & _ & _ & Hfrs & _).
  destruct HBM as (HnotE & HabP & _ & _).
  destruct HCUR as (_ & _ & _ & _ & HLEDP & _).
  destruct HMOD as (_ & _ & HLM & _).
  destruct HLM as (_ & _ & _ & HPerm & _).
  destruct HLEDP as (_ & HNDP & HFLP & _).
  destruct HLEDE as (_ & _ & HFLE & _).
  destruct (alx_layout SEGS B ARx LAWS _ _ _ _ _ _ _ HARE Hly) as (_ & Hfa & _).
  (* a block the position owns is a harness block at the position *)
  assert (HhbP : forall a k, In (a, k) (ip_D P) ->
    0 <= k /\ In (a - cf_head, k + cf_head) (ablocks B (ip_ly P) (ip_S P))).
  { intros a k Hin.
    assert (HinL : In (a, k) (ip_Lam P))
      by (apply (Permutation_in _ (Permutation_sym HPerm)); apply in_or_app; left; exact Hin).
    destruct (proj1 (Forall_forall _ _) HFLP (a, k) HinL) as (Hk & Hab & _). cbn [fst snd] in Hk, Hab.
    split; [exact Hk | exact Hab]. }
  (* the entry's blocks are blocks at the position *)
  assert (HabE2P : forall b, In b (ablocks B (ie_ly E) (ie_S E)) -> In b (ablocks B (ip_ly P) (ip_S P))).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HabP)). apply in_or_app. right. exact Hb. }
  (* a block the position owns is apart from every block of the entry *)
  assert (HsepE : forall a k b n, In (a, k) (ip_D P) -> In (b, n) (ablocks B (ie_ly E) (ie_S E)) ->
     a + k <= b \/ b + n <= a - cf_head).
  { intros a k b n Hin Hb. destruct (HhbP a k Hin) as (Hk & Hab).
    assert (Hd : (a - cf_head, k + cf_head) <> (b, n)).
    { intros Eq. apply (HnotE a k Hin). rewrite Eq. exact Hb. }
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HARP Hab (HabE2P _ Hb) Hd) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz.
    pose proof (vv_req_ge (k + cf_head)). pose proof (vv_req_ge n). lia. }
  assert (Hone : forall a k, In (a, k) (ip_D P) ->
     0 <= k /\ In (a - cf_head, k + cf_head) (ablocks B (ip_ly P) (ip_S P)) /\
     4096 <= a - cf_head /\ a + k <= alloc_ceiling /\
     (forall x, a - cf_head <= x < a + k ->
        ~ in_img SEGS x /\ ~ (ie_v E <= x < ie_v E + 56) /\ ~ (ie_text E <= x < ie_text E + ie_len E))).
  { intros a k Hin. destruct (HhbP a k Hin) as (Hk & Hab).
    destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HARP Hab) as (_ & H4k & Hc & _).
    pose proof (vv_req_ge (k + cf_head)) as Hr.
    split; [exact Hk|]. split; [exact Hab|]. split; [exact H4k|]. split; [lia|].
    intros x Hx. split; [|split].
    - apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ x HARP Hab). lia.
    - (* the node: prhReader_at's four places at the entry *)
      intros Hv.
      destruct Hvat as [(a1 & k1 & Hin1 & Hlo & Hhi) | [(b & m & Hinb & _ & Hlo & Hhi) |
                        [(cid & pos & Hf & Hlo & Hhi) | Hww]]].
      + destruct (proj1 (Forall_forall _ _) HFLE (a1, k1) Hin1) as (Hk1 & Hab1 & _). cbn [fst snd] in Hk1, Hab1.
        destruct (HsepE a k _ _ Hin Hab1); lia.
      + destruct (HsepE a k _ _ Hin Hinb); lia.
      + assert (Hin' : In (cid, pos) (frames (ip_S P))) by (rewrite Hfrs; exact Hf).
        pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HARP Hab Hin') as Hz.
        unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite Hfa in Hz. lia.
      + lia.
    - (* the text: prhReader_home at the entry *)
      intros Ht.
      destruct Hhome as [[(b & m & Hinb & Hlo & Hhi) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] |
                         (b & m & Hinb & _ & Hlo & Hhi)].
      + destruct (proj1 (Forall_forall _ _) HFLE (b, m) Hinb) as (Hm & Habm & _). cbn [fst snd] in Hm, Habm.
        destruct (HsepE a k _ _ Hin Habm); lia.
      + destruct (Hro x Ht) as (Hr0 & _).
        apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ x HARP Hab); [lia|].
        destruct Hr0 as [(s & Hs & _ & Hsl) | Hrel].
        * exists s. split; [exact Hs | exact Hsl].
        * exact (@pa_relro_img _ _ PI_prog_A x Hrel).
      + destruct (Hro x Ht) as (Hr0 & _).
        apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ x HARP Hab); [lia|].
        destruct Hr0 as [(s & Hs & _ & Hsl) | Hrel].
        * exists s. split; [exact Hs | exact Hsl].
        * exact (@pa_relro_img _ _ PI_prog_A x Hrel).
      + destruct (HsepE a k _ _ Hin Hinb); lia. }
  split.
  { assert (H0 : Permutation (map fst (ip_Lam P)) (map fst (ip_D P ++ ie_Lam E)))
      by (apply Permutation_map; exact HPerm).
    assert (HN : List.NoDup (map fst (ip_Lam P))) by (first [exact HNDP | apply NoDup_ListNoDup; exact HNDP]).
    assert (H1 : List.NoDup (map fst (ip_D P ++ ie_Lam E))) by exact (Permutation_NoDup H0 HN).
    rewrite map_app in H1. apply List.NoDup_app_remove_r in H1. apply List.NoDup_map_inv in H1.
    first [exact H1 | apply NoDup_ListNoDup; exact H1]. }
  split; [exact Hone|].
  split.
  { intros a k a' k' Hin Hin' Hne.
    destruct (HhbP a k Hin) as (Hk & Hab). destruct (HhbP a' k' Hin') as (Hk' & Hab').
    assert (Hd : (a - cf_head, k + cf_head) <> (a' - cf_head, k' + cf_head)) by (intros Eq; injection Eq; lia).
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HARP Hab Hab' Hd) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz.
    pose proof (vv_req_ge (k + cf_head)). pose proof (vv_req_ge (k' + cf_head)). lia. }
  intros [a k] x Hin Hh Hv. unfold pj_holdsR in Hh. cbn [fst snd] in Hh.
  destruct (Hone a k Hin) as (_ & _ & _ & _ & Hx).
  destruct (Hx x ltac:(lia)) as (_ & Hnv & _). exact (Hnv Hv).
Qed.
Definition vv_upd (P : vrd_ipos) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : vrd_ipos :=
  MkIPos (ip_fx P) (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) regs mem md k (ip_n P) (ip_cap P) (ip_kids P) (ip_keys P)
    (ip_p P) (ip_acc P) (ip_f P) (ip_cont P) (ip_ok P) (ip_tr P) (ip_D P) (ip_Lam P) (ip_peak P) (ip_cnt P)
    (ip_fail P) (ip_ran P).
(* vv_islot_wkeep: sub-lane IvalL (IvalL_wkeep.v), Qed *)
Ltac vv_proj := cbn [vv_upd ip_fx ip_ly ip_S ip_Hp ip_W ip_regs ip_mem ip_md ip_k ip_n ip_cap ip_kids ip_keys ip_p
  ip_acc ip_f ip_cont ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran].

(* ---- helpers: address arithmetic, the shadow band, byte transport ---- *)

Lemma vv_floor8 : forall y, y - 7 <= y / 8 * 8 <= y.
Proof.
  intros y. pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)). lia.
Qed.

(* range_addressable reads only shadow bytes, which lie in [kLowShadowBeg, kHighMemBeg) for an address below 2^47 *)
Lemma vv_ra_keep : forall (rd rd' : Z -> option Z) a len,
  (forall s, kLowShadowBeg <= s < kHighMemBeg -> rd' s = rd s) -> 0 <= a -> a + len <= 2 ^ 47 ->
  range_addressable rd SHADOW_OFF a len -> range_addressable rd' SHADOW_OFF a len.
Proof.
  intros rd rd' a len Hk Ha Hl H x Hx. destruct (H x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite Hk; [exact Hs|]. unfold shadow_of_addr.
  assert (0 <= x / 8) by (apply Z.div_pos; lia).
  assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF. lia.
Qed.

Lemma vv_shv_keep : forall (rd rd' : Z -> option Z) x n,
  (forall s, kLowShadowBeg <= s < kHighMemBeg -> rd' s = rd s) -> 0 <= x -> 0 < n -> x + n <= 2 ^ 47 - 64 ->
  shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof.
  intros rd rd' x n Hk Hx Hn Hxn H s Hs. rewrite Hk; [exact (H s Hs)|].
  unfold shadow_addr in Hs.
  pose proof (vv_floor8 (SHADOW_OFF + x / 8)). pose proof (vv_floor8 (SHADOW_OFF + (x + n - 1) / 8)).
  assert (0 <= x / 8) by (apply Z.div_pos; lia).
  assert ((x + n - 1) / 8 < 2 ^ 44 - 8) by (apply Z.div_lt_upper_bound; lia).
  unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* the kids block is one entry of the position's block list; every other entry differs from it *)
Lemma vv_perm_other : forall (D Dx ks Di : list (Z * Z)) K C, 0 < C -> List.NoDup D ->
  Permutation D (Dx ++ kids_blkR K C ++ ks ++ Di) ->
  In (K, 56 * C) D /\ (forall b, In b Dx \/ In b ks \/ In b Di -> In b D /\ b <> (K, 56 * C)).
Proof.
  intros D Dx ks Di K C HC HND HP.
  assert (Ek : kids_blkR K C = [(K, 56 * C)])
    by (unfold kids_blkR; rewrite (proj2 (Z.eqb_neq C 0)) by lia; reflexivity).
  rewrite Ek in HP. cbn [app] in HP.
  assert (HND' : List.NoDup (Dx ++ (K, 56 * C) :: ks ++ Di)) by (eapply Permutation_NoDup; [exact HP | exact HND]).
  pose proof (@NoDup_remove_2 _ Dx (ks ++ Di) (K, 56 * C) HND') as Hnot.
  split.
  - eapply Permutation_in; [exact (Permutation_sym HP)|]. apply in_or_app. right. left. reflexivity.
  - intros b Hb. split.
    + eapply Permutation_in; [exact (Permutation_sym HP)|].
      destruct Hb as [Hb | [Hb | Hb]]; apply in_or_app;
        [left; exact Hb | right; right; apply in_or_app; left; exact Hb
        | right; right; apply in_or_app; right; exact Hb].
    + intros ->. apply Hnot.
      destruct Hb as [Hb | [Hb | Hb]]; apply in_or_app;
        [left; exact Hb | right; apply in_or_app; left; exact Hb | right; apply in_or_app; right; exact Hb].
Qed.

Lemma vv_keptL : forall (regs regs' : bvmap 5 word) (z : Z) (r : bv 5),
  aregs_preserved regs regs' -> acallee_saved z -> bv_unsigned r = z -> getr regs' r = getr regs r.
Proof.
  intros regs regs' z r H Hc Hz. pose proof (H z Hc) as HH.
  rewrite <- Hz, Z_to_bv_bv_unsigned in HH. exact HH.
Qed.

Lemma vv_mbyte_of_aview : forall (H : word -> bool) (m m' : word -> option byte) a,
  aview SEGS H m' a = aview SEGS H m a -> mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a.
Proof.
  intros H m m' a E. unfold aview in E.
  destruct (mbyte SEGS (mrestrict H m') a) as [b'|], (mbyte SEGS (mrestrict H m) a) as [b|];
    cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* a byte the restricted memory had writable stays writable when presence is kept *)
Lemma vv_writable_keep : forall (H : word -> bool) (m m' : word -> option byte) a,
  writable_at SEGS (mrestrict H m) a -> (apresent H m a -> apresent H m' a) ->
  writable_at SEGS (mrestrict H m') a.
Proof.
  intros H m m' a. unfold writable_at, wview, mrestrict, apresent. cbv beta.
  destruct (H (Z_to_bv 64 a)) eqn:Eh; intros Hw Hp; [exact Hw|].
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
  - destruct (Hp (conj eq_refl (ex_intro _ b eq_refl))) as [_ [b' Hb']]. rewrite Hb'. discriminate.
  - destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

Lemma vv_rd_keep : forall (H : word -> bool) (m m' : word -> option byte) (Pz : Z -> Prop),
  (forall a, Pz a -> aview SEGS H m' a = aview SEGS H m a) ->
  (forall a, apresent H m a -> apresent H m' a) ->
  rd_keep SEGS (mrestrict H m) (mrestrict H m') Pz.
Proof.
  intros H m m' Pz HA HP. split.
  - intros a Ha. apply vv_mbyte_of_aview. exact (HA a Ha).
  - intros a _ Hw. exact (vv_writable_keep H m m' a Hw (HP a)).
Qed.

(* the ledger rides on a change that keeps the statics and the harness blocks' head words (S1Ledger's
   prh_ledger_kept_aview: on the kit's ledger the statics carry g_most and g_own_ran_out too) *)
Lemma vv_ledger_keep : forall ly S Hp (Wx : world SEGS) (m m' : word -> option byte) Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp Wx m Lam peak cnt fail ran most own ->
  (forall a, Exists (in_zr a) prh_pst -> aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a) ->
  (forall a kk i, In (a, kk) Lam -> 0 <= i < 8 ->
     aview SEGS (w_H Wx) m' (a - cf_head + i) = aview SEGS (w_H Wx) m (a - cf_head + i)) ->
  prh_ledger B ly S Hp Wx m' Lam peak cnt fail ran most own.
Proof.
  intros ly S Hp Wx m m' Lam peak cnt fail ran most own HLd Hs Hh.
  eapply prh_ledger_kept_aview; [exact HLd | exact Hs | exact Hh | intros a kk _ Hab; exact Hab | apply Permutation_refl].
Qed.

(* ---- THE KIT'S CUT: the batch kit's layer (VrdIElem.vrd_incaps / vrd_iforder) across a write into the free slots kids[n, cap)
   (row 223's memset). VrdIFd.vrd_k1_keep's keep covers every byte of every block of the position, which the write
   breaks (the free slots are bytes of the kids block); the layer reads only the members' slots kids[0, n) and the
   bytes of the OTHER blocks (the keys array, the members' and the key's blocks), so this is vrd_k1_keep with its keep
   narrowed to those. Dy (vrd_inode's) and Dx (the order list's) need not be the same list. ---- *)
Lemma vv_k1_keep_w : forall E P P2 Dx Dy af,
  ip_kids P2 = ip_kids P -> ip_keys P2 = ip_keys P -> ip_n P2 = ip_n P -> ip_cap P2 = ip_cap P ->
  ip_acc P2 = ip_acc P -> ip_D P2 = ip_D P -> ip_Lam P2 = ip_Lam P -> 0 < ip_cap P -> List.NoDup (ip_D P) ->
  rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P2)) (ip_mem P2))
    (fun z => ip_kids P <= z < ip_kids P + 56 * ip_n P \/
              exists b, In b (ip_D P) /\ b <> (ip_kids P, 56 * ip_cap P) /\ pj_holdsR b z) ->
  vrd_inode E P Dy -> vrd_incaps E P -> vrd_iforder E P Dx af ->
  vrd_incaps E P2 /\ vrd_iforder E P2 Dx af.
Proof.
  intros E P P2 Dx Dy af Ek Ey En Ec Ea ED EL Hcp HNd HK HND HNC HFO.
  pose proof HND as (_ & Hnc & _ & _ & _ & Hlen & (Di & HDp & Hsub) & _).
  destruct (vv_perm_other _ _ _ _ _ _ Hcp HNd HDp) as (_ & Hoth).
  assert (Hln : Z.of_nat (length (rev (ip_acc P))) = ip_n P) by (rewrite length_rev; exact Hlen).
  split.
  - unfold vrd_incaps in HNC |- *. rewrite Ea, Ek.
    assert (HK' : rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P2)) (ip_mem P2))
                    (fun z => ip_kids P <= z < ip_kids P + 56 * Z.of_nat (length (rev (ip_acc P))) \/ rd_blk Di z)).
    { eapply rd_keep_mono; [exact HK|]. intros z [Hz | Hz]; [left; lia | right].
      unfold rd_blk in Hz. apply Exists_exists in Hz as (b & Hb & Hz).
      destruct (Hoth b (or_intror (or_intror Hb))) as (HbD & Hne). exists b. exact (conj HbD (conj Hne Hz)). }
    revert Hsub. destruct (ie_o E); intros Hsub.
    + exact (vrd_ncaps_keep_mems SEGS (rev (ip_acc P)) _ _ _ (ip_kids P) (ip_keys P) Di Hsub HNC HK').
    + exact (vrd_ncaps_keep_items SEGS (rev (ip_acc P)) _ _ _ (ip_kids P) Di Hsub HNC HK').
  - intros Hh nn Hnn. rewrite Ea in Hnn.
    destruct (HFO Hh nn Hnn) as (Di' & Facc & HP & HOI & Hm).
    destruct (vv_perm_other _ _ _ _ _ _ Hcp HNd HP) as (_ & Hoth').
    exists Di', Facc. rewrite ED, Ek, Ey, Ec, En, EL. split; [exact HP|]. split; [|exact Hm].
    apply (PRH_PjOrder.pf_oitemsR_frame SEGS nn _ _ _ _ (ie_o E) (ip_kids P) (ip_keys P) (Z.to_nat (ip_n P)) Di' Facc
             HOI).
    + exact (PRH_PjOrder.pf_oitemsR_lblk SEGS _ _ nn _ _ _ _ _ _ HOI).
    + apply (vrd_agree_of_keep SEGS). eapply rd_keep_mono; [exact HK|].
      intros y Hy'. unfold PRH_PjOrder.pf_ofoot in Hy'. destruct Hy' as [Hy | [(Hks & Hy) | (b & Hb & Hy)]].
      * left. lia.
      * right. exists (ip_keys P, 8 * ip_cap P).
        assert (Hky : In (ip_keys P, 8 * ip_cap P) (keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P))).
        { rewrite Hks. unfold keys_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0)) by lia. cbn. left. reflexivity. }
        destruct (Hoth' _ (or_intror (or_introl Hky))) as (HkyD & Hkyne).
        split; [exact HkyD|]. split; [exact Hkyne|]. unfold pj_holdsR. cbn [fst snd]. lia.
      * right. exists b. destruct (Hoth' b (or_intror (or_intror Hb))) as (HbD & Hne). exact (conj HbD (conj Hne Hy)).
Qed.

(* a key slot's reader (PRH_Reader.pj_keyR) reads only the slot word, and only for an object; its block is the
   ledger's, so a ledger that grew still holds it *)
Lemma vv_keyR_keep : forall m m' (lblk lblk' : Z -> Z -> Prop) (ks : bool) ka Dk,
  pj_keyR SEGS m lblk ks ka Dk -> (forall x k, lblk x k -> lblk' x k) ->
  (ks = true -> rd_keep SEGS m m' (fun z => ka <= z < ka + 8)) ->
  pj_keyR SEGS m' lblk' ks ka Dk.
Proof.
  intros m m' lblk lblk' ks ka Dk H Hlb HK. unfold pj_keyR in *. destruct ks; [|exact H].
  destruct H as (x & Hr & Hx). exists x. split; [exact (rd_u64_keep SEGS m m' ka x Hr (HK eq_refl))|].
  destruct Hx as [Hx | (k & Hk & HD)]; [left; exact Hx | right; exists k; split; [exact (Hlb x k Hk) | exact HD]].
Qed.

(* one more completed slot at the end of an order list: its value's list, then its key (PRH_PjOrder.pf_oitemsR's slot
   order; the ordered twin of vv_pf_snoc, as a Theorem Labs lane's PItems_forder.v pis_fo_snoc_gen) *)
Lemma vv_pfo_snoc : forall m lblk (Pq : Z -> list (Z * Z) -> list (Z * Z) -> Prop) ks a ka n D F Dk D1 F1,
  PRH_PjOrder.pf_oitemsR SEGS m lblk Pq ks a ka n D F ->
  pj_keyR SEGS m lblk ks (ka + 8 * Z.of_nat n) Dk -> Pq (a + 56 * Z.of_nat n) D1 F1 ->
  PRH_PjOrder.pf_oitemsR SEGS m lblk Pq ks a ka (S n) (D ++ Dk ++ D1) (F ++ F1 ++ Dk).
Proof.
  intros m lblk Pq ks a ka n; revert a ka; induction n as [|n IH]; intros a ka D F Dk D1 F1 HD Hk HP.
  - cbn [PRH_PjOrder.pf_oitemsR] in HD |- *. destruct HD as (-> & ->).
    exists Dk, D1, F1, [], []. split; [rewrite app_nil_r; reflexivity|]. split; [rewrite app_nil_r; reflexivity|].
    split; [refine (eq_ind _ (fun z => pj_keyR SEGS m lblk ks z Dk) Hk _ _); lia|].
    split; [refine (eq_ind _ (fun z => Pq z D1 F1) HP _ _); lia|]. split; reflexivity.
  - cbn [PRH_PjOrder.pf_oitemsR] in HD |- *.
    destruct HD as (Dk0 & E1 & G1 & E2 & G2 & -> & -> & H0 & H1 & H2).
    exists Dk0, E1, G1, (E2 ++ Dk ++ D1), (G2 ++ F1 ++ Dk).
    split; [rewrite <- !app_assoc; reflexivity|]. split; [rewrite <- !app_assoc; reflexivity|].
    split; [exact H0|]. split; [exact H1|].
    apply (IH (a + 56) (ka + 8) E2 G2 Dk D1 F1 H2).
    + refine (eq_ind _ (fun z => pj_keyR SEGS m lblk ks z Dk) Hk _ _); lia.
    + refine (eq_ind _ (fun z => Pq z D1 F1) HP _ _); lia.
Qed.

(* an order list over a permutation of its block list (a Theorem Labs lane's PItems_value_model.v pvm_foR_perm, copied) *)
Lemma vv_foR_perm : forall m lblk d p D D' F, Permutation D D' ->
  PRH_PjOrder.pj_foR SEGS m lblk d p D F -> PRH_PjOrder.pj_foR SEGS m lblk d p D' F.
Proof.
  intros m lblk d p D D' F HP H.
  assert (G : forall Pi, PRH_PjOrder.pj_oshapeR SEGS m lblk Pi p D F -> PRH_PjOrder.pj_oshapeR SEGS m lblk Pi p D' F).
  { intros Pi (HN & HA & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & Fi & Hh & Hs & Hk & Hy &
      HPm & HPi & HF).
    split; [ first [ eapply Permutation_NoDup; [exact HP | exact HN]
                   | apply NoDup_ListNoDup; eapply Permutation_NoDup;
                     [exact HP | apply NoDup_ListNoDup; exact HN] ] |].
    split; [intros b x Hb Hx; eapply HA; [|exact Hx]; eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hb]|].
    exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di, Fi.
    split; [exact Hh|]. split; [exact Hs|]. split; [exact Hk|]. split; [exact Hy|].
    split; [eapply Permutation_trans; [apply Permutation_sym; exact HP | exact HPm]|]. split; [exact HPi | exact HF]. }
  destruct d; cbn [PRH_PjOrder.pj_foR] in H |- *; apply G; exact H.
Qed.

(* ---- the value-slot position across a write into kids[n, cap) (row 223's __asan_memset of kids[n]) ---- *)
Lemma vv_islot_wkeep : forall CTX CTX0 CW E P nm regs' mem' md' k' (X : Z -> Prop),
  pi_frame F_parse_items = 144 ->
  (forall a, Exists (in_zr a) prh_pst -> in_img SEGS a) ->
  8 <= cf_head ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_islot_a B ARx SK E P nm ->
  (forall a, X a -> ip_kids P + 56 * ip_n P <= a < ip_kids P + 56 * ip_cap P) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E) (spZ (ie_regs E) + ie_e E)
    (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem' md' k' (ie_CW E) ->
  aregs_preserved (ip_regs P) regs' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> ~ (spZ (ip_regs P) - ESTACK <= a < spZ (ip_regs P)) ->
     aview SEGS (w_H (ip_W P)) mem' a = aview SEGS (w_H (ip_W P)) (ip_mem P) a) ->
  (forall a, apresent (w_H (ip_W P)) (ip_mem P) a -> apresent (w_H (ip_W P)) mem' a) ->
  vrd_islot_a B ARx SK E (vv_upd P regs' mem' md' k') nm.
Proof.
  intros CTX CTX0 CW E P nm regs' mem' md' k' X Himg Hpst Hcf8 HEN HSL HX HJ HRP HM HPR.
  pose proof cf_head_nonneg as Hcf0.
  pose proof asan_consts as ((Hac1 & Hac2) & _ & _ & _ & _).
  assert (HES : ESTACK = 4096) by reflexivity.
  pose proof (vrd_node_low B ARx HL LAWS CTX CTX0 CW E HEN) as Hvceil.
  pose proof HEN as ((HAFN & _) & _ & _ & _ & HRD & _).
  pose proof HAFN as (_ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (_ & _ & Hceil0 & Hslo0 & Hshi0 & H470 & _ & Htop0 & Htop0').
  pose proof HRD as (_ & _ & _ & _ & _ & _ & Hqlo & Hqhi & _ & _ & _ & _ & Hnode & _).
  pose proof Hnode as (Hv4096 & _).
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HstkJ & _).
  pose proof HstkJ as (_ & _ & _ & _ & HshiJ & H47J & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  pose proof HSL as (HFR & HRG & HCU & HJN & HMD & Hncap & HNODE & HCONT & HCAP & HNC & (Dk & af & lk & HKR & HFO & Hlk &
    HFL)).
  pose proof HFR as (Hsp & _).
  pose proof HCU as (Hinok & Hraq & Hsrc & Hhome & Hled & Hfrm & Hcnt).
  pose proof HJN as (HJ0 & HWIN & Hfz & Hfk & Hrod & Hbm & (ch' & Hch & Hspn)).
  pose proof HJ0 as (HAR & _).
  pose proof (vv_D_apart CTX CTX0 CW E P HEN HJN HCU HMD) as (HND0 & HBLK & _ & _).
  assert (HND : List.NoDup (ip_D P)) by (first [exact HND0 | apply NoDup_ListNoDup; exact HND0]).
  pose proof Hinok as (_ & _ & _ & _ & _ & Htx0 & _ & _ & Hlen & _ & _ & _).
  pose proof Hsrc as (_ & Htx4096 & Htxc & _).
  (* the stack: memset's window lies above alloc_ceiling *)
  assert (HSTK : 144 + ESTACK <= STK_parse_items (ie_d E)).
  { unfold STK_parse_items. rewrite Himg. pose proof (pi_frame_nonneg F_parse_value).
    assert (ESTACK <= LEAF_pv_pi) by (unfold LEAF_pv_pi, zmaxl, STK_RT_ECALL; cbn [fold_right]; lia).
    assert (0 <= Z.of_nat (PjGrammar.MAXD - ie_d E) * (pi_frame F_parse_value + 144))
      by (apply Z.mul_nonneg_nonneg; lia).
    lia. }
  assert (Hcs : alloc_ceiling <= spZ (ip_regs P) - ESTACK) by lia.
  (* the kids block *)
  assert (Hex : exists Dx, vrd_inode E P Dx).
  { revert HNODE. destruct (ie_o E); [intros (x & k & _ & _ & Hn) | intros (_ & Hn)]; eexists; exact Hn. }
  destruct Hex as (Dx0 & HN0).
  pose proof HN0 as (_ & (HN0n & HN0c) & _ & _ & _ & _ & (Di0 & HDi0 & _) & _).
  assert (HC : 0 < ip_cap P) by lia.
  pose proof (proj1 (vv_perm_other _ _ _ _ _ _ HC HND HDi0)) as HKD.
  destruct (HBLK _ _ HKD) as (_ & HabK & HK4096 & HKceil & HKbytes).
  pose proof (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR HabK) as (_ & _ & _ & HappK & _).
  assert (HrqK : req_size (56 * ip_cap P + cf_head) = 56 * ip_cap P + cf_head)
    by (unfold req_size; destruct (Z.eqb_spec (56 * ip_cap P + cf_head) 0); lia).
  rewrite HrqK in HappK.
  assert (HXf : forall a, X a -> ip_kids P + 56 * ip_n P <= a < ip_kids P + 56 * ip_cap P /\ app_addr a /\
     ~ in_img SEGS a /\ ~ (ie_v E <= a < ie_v E + 56) /\ ~ (ie_text E <= a < ie_text E + ie_len E)).
  { intros a Ha. pose proof (HX a Ha) as Hr.
    destruct (HKbytes a ltac:(lia)) as (Hi & Hv & Ht).
    split; [exact Hr|]. split; [apply (in_app_addr _ _ a HappK); lia|]. exact (conj Hi (conj Hv Ht)). }
  (* the four kinds of kept bytes *)
  assert (K1 : forall a, spZ (ip_regs P) <= a < 2 ^ 64 ->
    aview SEGS (w_H (ip_W P)) mem' a = aview SEGS (w_H (ip_W P)) (ip_mem P) a).
  { intros a Ha. apply HM; [lia | intros HXa; destruct (HXf a HXa) as (Hr & _); lia | lia]. }
  assert (K2 : forall a, 0 <= a < alloc_ceiling -> ~ X a ->
    aview SEGS (w_H (ip_W P)) mem' a = aview SEGS (w_H (ip_W P)) (ip_mem P) a).
  { intros a Ha Hn. apply HM; [lia | exact Hn | lia]. }
  assert (K3 : forall s, kLowShadowBeg <= s < kHighMemBeg ->
    aview SEGS (w_H (ip_W P)) mem' s = aview SEGS (w_H (ip_W P)) (ip_mem P) s).
  { intros s Hs. unfold kLowShadowBeg, kHighMemBeg in Hs. apply HM; [lia | | lia].
    intros HXs. destruct (HXf s HXs) as (_ & Happ & _).
    unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Happ. lia. }
  assert (K5 : forall a k, In (a - cf_head, k + cf_head) (ablocks B (ip_ly P) (ip_S P)) -> 0 <= k ->
    (a, k) <> (ip_kids P, 56 * ip_cap P) -> forall z, a - cf_head <= z < a + k ->
    aview SEGS (w_H (ip_W P)) mem' z = aview SEGS (w_H (ip_W P)) (ip_mem P) z).
  { intros a k Hab Hk Hne z Hz.
    pose proof (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & H4096 & Hceil & _).
    assert (Hrq : req_size (k + cf_head) = k + cf_head)
      by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
    rewrite Hrq in Hceil.
    assert (Hne' : (a - cf_head, k + cf_head) <> (ip_kids P - cf_head, 56 * ip_cap P + cf_head)).
    { intros Eq. injection Eq as E1 E2. apply Hne. f_equal; lia. }
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hab HabK Hne') as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq, HrqK in Hd.
    apply K2; [lia|]. intros HXz. destruct (HXf z HXz) as (Hr & _). lia. }
  assert (Gb : forall b, In b (ip_D P) -> b <> (ip_kids P, 56 * ip_cap P) ->
    forall z, fst b - cf_head <= z < fst b + snd b ->
    aview SEGS (w_H (ip_W P)) mem' z = aview SEGS (w_H (ip_W P)) (ip_mem P) z).
  { intros [a k] Hb Hne z Hz. cbn [fst snd] in Hz. destruct (HBLK a k Hb) as (Hk & Hab & _).
    exact (K5 a k Hab Hk Hne z Hz). }
  assert (KR : forall (r : bv 5) z, acallee_saved z -> bv_unsigned r = z -> getr regs' r = getr (ip_regs P) r)
    by (intros r z Hz Hr; exact (vv_keptL (ip_regs P) regs' z r HRP Hz Hr)).
  assert (Hspr : spZ regs' = spZ (ip_regs P)).
  { unfold spZ. erewrite (KR _ 2) by first [unfold acallee_saved; lia | reflexivity]. reflexivity. }
  (* the node *)
  assert (HIN : forall Dx, vrd_inode E P Dx -> vrd_inode E (vv_upd P regs' mem' md' k') Dx).
  { intros Dx HN. unfold vrd_inode in HN |- *. vv_proj.
    destruct HN as (N1 & N2 & N3 & N4 & N5 & N6 & (Di & HDi & HDR) & N8 & N9 & N10 & N11 & N12).
    destruct (vv_perm_other _ _ _ _ _ _ HC HND HDi) as (_ & Hoth).
    refine (conj _ (conj N2 (conj N3 (conj N4 (conj N5 (conj N6 (conj _ (conj _ (conj _ (conj _ (conj _ N12))))))))))).
    - eapply (pj_hdrR_keep SEGS); [exact N1|]. apply vv_rd_keep; [|exact HPR].
      intros z Hz. apply K2; [lia|]. intros HXz. destruct (HXf z HXz) as (_ & _ & _ & Hv & _). exact (Hv Hz).
    - exists Di. split; [exact HDi|].
      revert HDR. destruct (ie_o E) eqn:Eo; intros HDR.
      + assert (Hky6 : In (ip_keys P, 8 * ip_cap P) (keys_blkR 6 (ip_keys P) (ip_cap P))).
        { unfold keys_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0)) by lia. cbn. left. reflexivity. }
        destruct (Hoth (ip_keys P, 8 * ip_cap P)
          (or_intror (or_introl ltac:(first [exact Hky6 | rewrite Eo; exact Hky6])))) as (HkyD & Hkyne).
        eapply (pj_memsR_keep SEGS); [exact HDR | intros x0 k0 _ H0; exact H0 |].
        apply vv_rd_keep; [|exact HPR]. intros z Hz.
        rewrite length_rev, N6 in Hz.
        destruct Hz as [Hz | [Hz | Hz]].
        * apply K2; [lia|]. intros HXz. destruct (HXf z HXz) as (Hr & _). lia.
        * apply (Gb _ HkyD Hkyne). cbn [fst snd]. lia.
        * apply Exists_exists in Hz as (b & Hb & Hz). unfold pj_holdsR in Hz.
          destruct (Hoth b (or_intror (or_intror Hb))) as (HbD & Hbne).
          apply (Gb b HbD Hbne). lia.
      + eapply (pj_itemsR_keep SEGS); [exact HDR | intros x0 k0 _ H0; exact H0 |].
        apply vv_rd_keep; [|exact HPR]. intros z Hz.
        rewrite length_map, length_rev, N6 in Hz.
        destruct Hz as [Hz | Hz].
        * apply K2; [lia|]. intros HXz. destruct (HXf z HXz) as (Hr & _). lia.
        * apply Exists_exists in Hz as (b & Hb & Hz). unfold pj_holdsR in Hz.
          destruct (Hoth b (or_intror (or_intror Hb))) as (HbD & Hbne).
          apply (Gb b HbD Hbne). lia.
    - intros z Hz. exact (vv_writable_keep (w_H (ip_W P)) (ip_mem P) mem' z (N8 z Hz) (HPR z)).
    - apply (vv_ra_keep _ _ _ _ K3); [lia | lia | exact N9].
    - intros HC'. apply (vv_ra_keep _ _ _ _ K3); [lia | lia | exact (N10 HC')].
    - intros Ho HC'.
      assert (Hky : In (ip_keys P, 8 * ip_cap P) (keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P))).
      { rewrite Ho. unfold keys_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0)) by lia. cbn. left. reflexivity. }
      destruct (Hoth _ (or_intror (or_introl Hky))) as (HkyD & _).
      destruct (HBLK _ _ HkyD) as (_ & _ & Hk4096 & Hkceil & _).
      apply (vv_ra_keep _ _ _ _ K3); [lia | lia | exact (N11 Ho HC')]. }
  (* THE BATCH KIT'S LAYER (the kit's cut): the members' caps and the order list read no byte the write changed *)
  assert (HK1 : vrd_incaps E (vv_upd P regs' mem' md' k') /\ vrd_iforder E (vv_upd P regs' mem' md' k') Dk af).
  { apply (vv_k1_keep_w E P (vv_upd P regs' mem' md' k') Dk Dx0 af eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
             eq_refl HC HND); [|exact HN0 | exact HNC | exact HFO].
    vv_proj. apply vv_rd_keep; [|exact HPR]. intros z [Hz | (b & Hb & Hne & Hz)].
    - apply K2; [lia|]. intros HXz. destruct (HXf z HXz) as (Hr & _). lia.
    - apply (Gb b Hb Hne). unfold pj_holdsR in Hz. lia. }
  unfold vrd_islot_a.
  refine (conj _ (conj _ (conj _ (conj _ (conj HMD (conj Hncap (conj _ (conj HCONT (conj HCAP
    (conj (proj1 HK1) _)))))))))).
  - (* the frame *)
    unfold vrd_iframe. vv_proj.
    destruct HFR as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16
      & F17 & F18).
    refine (conj _ _); [rewrite Hspr; exact F0|].
    repeat (refine (conj _ _);
      [apply (val_mem_kept SEGS (w_H (ip_W P)) (w_H (ip_W P)) (ip_mem P) mem');
         [intros k0 Hk0; apply K1; cbn in Hk0; lia | assumption] |]).
    intros a Ha. apply HPR. exact (F18 a Ha).
  - (* the registers *)
    unfold vrd_iregs. vv_proj.
    destruct HRG as (R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
      (conj _ _))))))))))))).
    + erewrite (KR _ 3) by first [unfold acallee_saved; lia | reflexivity]. exact R3.
    + erewrite (KR _ 4) by first [unfold acallee_saved; lia | reflexivity]. exact R4.
    + erewrite (KR _ 8) by first [unfold acallee_saved; lia | reflexivity]. exact R8.
    + erewrite (KR _ 9) by first [unfold acallee_saved; lia | reflexivity]. exact R9.
    + erewrite (KR _ 18) by first [unfold acallee_saved; lia | reflexivity]. exact R18.
    + erewrite (KR _ 19) by first [unfold acallee_saved; lia | reflexivity]. exact R19.
    + erewrite (KR _ 20) by first [unfold acallee_saved; lia | reflexivity]. exact R20.
    + erewrite (KR _ 21) by first [unfold acallee_saved; lia | reflexivity]. exact R21.
    + erewrite (KR _ 22) by first [unfold acallee_saved; lia | reflexivity]. exact R22.
    + erewrite (KR _ 23) by first [unfold acallee_saved; lia | reflexivity]. exact R23.
    + erewrite (KR _ 24) by first [unfold acallee_saved; lia | reflexivity]. exact R24.
    + erewrite (KR _ 25) by first [unfold acallee_saved; lia | reflexivity]. exact R25.
    + erewrite (KR _ 26) by first [unfold acallee_saved; lia | reflexivity]. exact R26.
    + erewrite (KR _ 27) by first [unfold acallee_saved; lia | reflexivity]. exact R27.
  - (* the cursor, the text, the ledger *)
    unfold vrd_icur. vv_proj.
    refine (conj _ (conj _ (conj _ (conj Hhome (conj _ (conj Hfrm Hcnt)))))).
    + eapply (pj_in_okR_keep SEGS); [exact Hinok|]. apply vv_rd_keep; [|exact HPR].
      intros z [Hz | Hz].
      * apply K1. lia.
      * apply K2; [lia|]. intros HXz. destruct (HXf z HXz) as (_ & _ & _ & _ & Ht). exact (Ht Hz).
    + apply (vv_ra_keep _ _ _ _ K3); [lia | lia | exact Hraq].
    + destruct Hsrc as (S1 & S2 & S3 & S4 & S5 & S6).
      refine (conj _ (conj S2 (conj S3 (conj S4 (conj _ _))))).
      * refine (garr8_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem')
          (ie_text E) (ie_tb E) S1 _).
        apply vv_rd_keep; [|exact HPR]. intros z Hz. apply K2; [lia|].
        intros HXz. destruct (HXf z HXz) as (_ & _ & _ & _ & Ht). apply Ht. lia.
      * apply (vv_ra_keep _ _ _ _ K3); [lia | lia | exact S5].
      * intros Hl. apply (vv_shv_keep _ _ _ _ K3); [lia | lia | lia | exact (S6 Hl)].
    + apply (vv_ledger_keep _ _ _ _ (ip_mem P)); [exact Hled | |].
      * intros a Ha. pose proof (Hpst a Ha) as Hi. pose proof (@pa_segs_low _ _ PI_prog_A a Hi) as Hlow.
        apply K2; [unfold kLowMemEnd in Hlow; lia|].
        intros HXa. destruct (HXf a HXa) as (_ & _ & Hni & _). exact (Hni Hi).
      * intros a kk i Hin Hi.
        pose proof Hled as (_ & _ & HLB & _). rewrite Forall_forall in HLB.
        destruct (HLB (a, kk) Hin) as (Hk0 & Hab0 & _). cbn [fst snd] in Hk0, Hab0.
        pose proof (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab0) as (_ & H4096 & _).
        destruct (Z.eq_dec a (ip_kids P)) as [EaK | NaK].
        { apply K2; [lia|]. intros HXz. destruct (HXf _ HXz) as (Hr & _). lia. }
        { apply (K5 a kk Hab0 Hk0); [intros Eq; injection Eq as Eq1 _; exact (NaK Eq1) | lia]. }
  - (* the journal, the window, the read-only view, the chain *)
    unfold vrd_ijrn. vv_proj.
    refine (conj HJ (conj _ (conj Hfz (conj Hfk (conj _ (conj Hbm _)))))).
    + intros a Ha Hn. rewrite K1 by lia. exact (HWIN a Ha Hn).
    + unfold arodata_okP in *. intros a Hro Hn He.
      assert (Hi : in_img SEGS a).
      { destruct Hro as [(sg & Hin & _ & Hr) | Hr];
          [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PI_prog_A a Hr)]. }
      pose proof (@pa_segs_low _ _ PI_prog_A a Hi) as Hlow. unfold kLowMemEnd in Hlow.
      rewrite K2; [exact (Hrod a Hro Hn He) | lia |].
      intros HXa. destruct (HXf a HXa) as (_ & _ & Hni & _). exact (Hni Hi).
    + exists ch'. split; [|exact Hspn].
      apply (achain_kept (ip_ly P) (aview SEGS (w_H (ip_W P)) (ip_mem P)) _ _ _ _ (spZ (ie_regs E) - 144) Hch);
        [lia | lia |].
      intros a Ha. apply K1. lia.
  - (* the key slot and the node *)
    vv_proj. revert HNODE. destruct (ie_o E) eqn:Eo; intros HNODE.
    + destruct HNODE as (x & k & Hr64 & Hcstr & Hn).
      pose proof Hn as (_ & (Hn0 & Hnc) & _ & _ & _ & _ & (Di & HDi & _) & _).
      destruct (vv_perm_other _ _ _ _ _ _ HC HND HDi) as (_ & Hoth).
      assert (Hky6 : In (ip_keys P, 8 * ip_cap P) (keys_blkR 6 (ip_keys P) (ip_cap P))).
      { unfold keys_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0)) by lia. cbn. left. reflexivity. }
      assert (Hky : In (ip_keys P, 8 * ip_cap P) (keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P)))
        by (rewrite Eo; exact Hky6).
      destruct (Hoth _ (or_intror (or_introl Hky))) as (HkyD & Hkyne).
      destruct (Hoth (x, k) (or_introl (or_introl eq_refl))) as (HxD & Hxne).
      exists x, k. refine (conj _ (conj _ (HIN _ Hn))).
      * eapply (rd_u64_keep SEGS); [exact Hr64|]. apply vv_rd_keep; [|exact HPR].
        intros z Hz. apply (Gb _ HkyD Hkyne). cbn [fst snd]. lia.
      * eapply (pj_cstrR_keep SEGS); [exact Hcstr | exact (fun h => h) |]. apply vv_rd_keep; [|exact HPR].
        intros z Hz. apply (Gb _ HxD Hxne). cbn [fst snd]. lia.
    + destruct HNODE as (Hnm & Hn). exact (conj Hnm (HIN _ Hn)).
  - (* The batch-kit layer's key slot: its word is a byte of the keys array, another block than the kids array *)
    exists Dk, af, lk. refine (conj _ (conj (proj2 HK1) (conj Hlk HFL))).
    vv_proj. apply (vv_keyR_keep _ _ _ _ _ _ _ HKR (fun _ _ h => h)). intros Ho.
    assert (Hky : In (ip_keys P, 8 * ip_cap P) (keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P))).
    { rewrite Ho. unfold keys_blkR. rewrite (proj2 (Z.eqb_neq (ip_cap P) 0)) by lia. cbn. left. reflexivity. }
    destruct (vv_perm_other _ _ _ _ _ _ HC HND HDi0) as (_ & Hoth).
    destruct (Hoth _ (or_intror (or_introl Hky))) as (HkyD & Hkyne).
    apply vv_rd_keep; [|exact HPR]. intros z Hz. apply (Gb _ HkyD Hkyne). cbn [fst snd]. lia.
Qed.


(* a run over the read-only seat writes nothing *)
Lemma vv_frame_ro : forall E' kk (m m' : word -> option byte),
  frame_of E' (ss_mem (vv_ss1 false kk)) m m' -> forall x, m' x = m x.
Proof.
  intros E' kk m m' HF x. apply HF. intros (r & Hin & Hr).
  cbn [vv_ss1 ss_mem In] in Hin. destruct Hin as [<- | [<- | []]];
    cbn [vv_frame1 vv_node1 YP09.r_wlo YP09.r_whi] in Hr; lia.
Qed.

(* the slot address the code computes, kids + 56 n *)
Lemma vv_slot_U : forall E kids n, bv_unsigned (ew E 45) = kids -> bv_unsigned (ew E 46) = n ->
  0 <= kids -> 0 <= n -> kids + 56 * n < 2 ^ 63 ->
  U E (SAlu ALU_ADD (SOff 45 0) (SMd M_MUL (SOff 46 0) (SLit 56))) = kids + 56 * n.
Proof.
  intros E kids n Hk Hn Hk0 Hn0 Hb. rewrite U_SAlu, U_SMd, U_SOff, U_SOff, U_SLit, Hk, Hn. cbn [zalu_raw zmd_raw].
  rewrite !Z.add_0_r. unfold zcanon, M64.
  rewrite (Z.mod_small kids) by lia. rewrite (Z.mod_small n) by lia. change (56 mod 2 ^ 64) with 56.
  rewrite ?bv_swrap_small by (unfold bv_half_modulus, bv_modulus; cbn; lia).
  rewrite (Z.mod_small (n * 56)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma vv_partA : forall CTX CTX0 CW E P nm,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_islot_a B ARx SK E P nm -> Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_ISLOT_SLOT P)
    (fun W2 c2 => (exists P', W2 = ip_W P' /\ c2 = vrd_cfg A_IMSET_RET P' /\ ip_n P' = ip_n P /\ vv_set E P' nm) /\
                  Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P nm HEN HI HPM.
  destruct (vv_seat1 false A_ISLOT_SLOT CTX CTX0 CW E P nm HEN HI) as [HS SHOK].
  pose proof HI as (HFR & HRG & HCU & HJN & HMD & Hnc & HKEY & Hcont).
  pose proof (vrd_ijrn_base B ARx SK E P HJN) as HJ.
  assert (HEI : img_env VAL A_LIM (vv_E1 E P)) by (unfold vv_E1; apply Eimg_env).
  assert (HR0 : forall r, getr (ip_regs P) r = sv_denot (vv_E1 E P) (sr_get vv_regs1 r))
    by (intros r; exact (st_ok_pi_restrict_reg _ _ _ _ r HS)).
  pose (RUN := paj_run_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  unfold vrd_cfg.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vi_Bspan;
    [eapply awr_ok_cons_ro; [cbn; lia | eapply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]]|].
  pose proof (vv_frame_ro _ _ _ _ HF) as HM.
  pose proof (proj1 HJ) as HART. cbv beta in HART.
  assert (Q10 : getr (ms_regs ms) 10 =
    sv_denot (vv_E1 E P) (SAlu ALU_ADD (SOff 45 0) (SMd M_MUL (SOff 46 0) (SLit 56)))).
  { rewrite (st_ok_restrict_reg SEGS _ _ _ ms (10%bv : bv 5) HS). reflexivity. }
  assert (HKR : aregs_preserved (ip_regs P) (ms_regs ms)).
  { intros r Hr. unfold acallee_saved in Hr.
    rewrite (st_ok_restrict_reg SEGS _ _ _ ms (Z_to_bv 5 r) HS), HR0.
    assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                 r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      apply (f_equal (sv_denot (vv_E1 E P))); vm_compute; reflexivity. }
  pmkst HS.
  prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  (* ---- the facts of the slot ---- *)
  pose proof (vrd_node_low B ARx HL LAWS CTX CTX0 CW E HEN) as Hvceil.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof H_head as (Hh8 & HLh).
  pose proof (vv_stk_items (ie_d E)) as HSTKi. unfold ESTACK in HSTKi.
  pose proof HFR as (Hsp & _).
  pose proof HRG as (G3 & G4 & _).
  pose proof HCU as (HIN & HRAq & HSRC & HHOME & HLED & HFRB & HCNT).
  destruct (vv_islot_inode E P nm HI) as [Dx HN].
  pose proof HN as (HHDR & Hn0 & Hcap & Hc0 & Hlin & Hlen & (Di & HPD & HIT) & HRW & HRAv & HRAk & HRAy & Hky0).
  assert (Hcpos : 0 < ip_cap P) by lia.
  destruct (Hlin Hcpos) as (HLk & _).
  assert (HinD : In (ip_kids P, 56 * ip_cap P) (ip_D P)).
  { apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. right. apply in_or_app. left.
    unfold kids_blkR. destruct (Z.eqb_spec (ip_cap P) 0); [lia | left; reflexivity]. }
  destruct (vv_D_apart CTX CTX0 CW E P HEN HJN HCU HMD) as (HND & HDB & HDD & HDAP).
  destruct (HDB _ _ HinD) as (Hk0 & HkAB & Hk4096 & Hkceil & HkX).
  pose proof HJN as (_ & HWIN & HFZ & HFK & HROD & HBM & HCH).
  pose proof HBM as (HBnew & HABP & HFRP & HPK).
  pose proof (HBnew _ _ HinD) as HkE.
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED HLk) as (_ & _ & HkHp & Hk16 & _).
  pose proof HEN as ((HAFN & _) & _ & _ & _ & HRD & _).
  pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof HRD as (_ & _ & _ & _ & _ & HFW & _).
  destruct HFW as (He0 & He16 & Hetop & Hepres).
  assert (Hreq : req_size (56 * ip_cap P + cf_head) = 56 * ip_cap P + cf_head)
    by (unfold req_size; destruct (Z.eqb_spec (56 * ip_cap P + cf_head) 0); lia).
  assert (U45 : bv_unsigned (ew (vv_E1 E P) 45) = ip_kids P)
    by (rewrite vv_E1_45; unfold w64; apply unsigned_lit_small; lia).
  assert (U46 : bv_unsigned (ew (vv_E1 E P) 46) = ip_n P)
    by (rewrite vv_E1_46; unfold w64; apply unsigned_lit_small; lia).
  set (dS := ip_kids P + 56 * ip_n P) in *.
  assert (HdS : getr (ms_regs ms) 10 = w64 dS)
    by (rewrite Q10, denot_lit_U, (vv_slot_U (vv_E1 E P) (ip_kids P) (ip_n P) U45 U46) by lia; reflexivity).
  assert (HspT : spZ (ms_regs ms) = spZ (ie_regs E) + ie_e E + - (ie_e E + 144)).
  { unfold spZ at 1. rewrite Q2, (vv_E1_low E P 2 2%bv eq_refl). fold (spZ (ip_regs P)). rewrite Hsp. lia. }
  assert (Ho16 : (- (ie_e E + 144)) mod 16 = 0).
  { apply Z.mod_opp_l_z; [lia|]. rewrite Z.add_mod by lia. rewrite He16. reflexivity. }
  eapply SRr'_bind.
  { (* the call keeps the world: the plain step of the memset row, lifted to SRr' (YA0nH.SRr_SRr') *)
    apply (SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
      eapply (aj_intrin_at_xmR (fx := ip_fx P) (SK := SK) SEGS B prh_pst ARx LAWS (@pa_segs_low _ _ PAI)
        (wle' SEGS YGcfRehidePost.RZ_cf) OSet
        (pa_sigma AS___asan_memset) (H_checked_memset (ip_fx P)) (ip_W P) rT mT
        (STK_parse_items (ie_d E) + ie_e E) (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
        (ie_ly E) (set_depot (st_depot (ip_S P)) (ie_S E)) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) [] (ip_ly P) (ip_S P)
        (ip_Hp P) dT (ip_k P)
        dS 0 56 (- (ie_e E + 144)) _ HJ) end.
    - exact HdS.
    - rewrite Q11. reflexivity.
    - rewrite Q12. reflexivity.
    - lia.
    - lia.
    - lia.
    - exact HspT.
    - exact Ho16.
    - lia.
    - unfold ESTACK. lia.
    - rewrite Q3, (vv_E1_low E P 3 3%bv eq_refl). exact G3.
    - rewrite Q4, (vv_E1_low E P 4 4%bv eq_refl). exact G4.
    - exact Q1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split.
      + right. right. left. exists (ip_kids P - cf_head), (56 * ip_cap P + cf_head).
        split; [exact HkAB|]. split; [exact HkE|]. rewrite Hreq. lia.
      + unfold ESTACK. lia.
    - destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HART HkAB) as (_ & _ & _ & Happ & _).
      rewrite Hreq in Happ. unfold in_app, amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia.
    - intros x Hx. rewrite (vi_aview_all _ _ _ (fun y => ltac:(unfold mrestrict; rewrite HM; reflexivity))).
      apply (HRAk Hcpos). lia.
    - intros _. destruct (alx_hshadow SEGS B ARx LAWS _ _ _ _ _ _ _ _ HART HkAB HkHp) as (_ & Hhull).
      rewrite Hreq, HLh in Hhull.
      replace (ip_kids P - cf_head + cf_head) with (ip_kids P) in Hhull by lia.
      replace (56 * ip_cap P + cf_head - cf_head) with (56 * ip_cap P) in Hhull by lia.
      apply (vv_hull_sub _ (ip_kids P) (56 * ip_cap P)); [apply Hhull; lia | lia | lia].
    - exact I. }
  cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Hset & Hfr5 & Hpres5 & Hmn5).
  apply SRr'_ret. split; [|exact (PCALL _ _ Hmn5 HPM)].
  exists (vv_upd P regs5 mem5 md5 (ip_k P)).
  split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|].
  assert (HAV : forall a, aview SEGS (w_H (ip_W P)) (ms_mem ms) a = aview SEGS (w_H (ip_W P)) (ip_mem P) a)
    by (apply vi_aview_all; intros y; unfold mrestrict; rewrite HM; reflexivity).
  split.
  - apply (vv_islot_wkeep CTX CTX0 CW E P nm regs5 mem5 md5 (ip_k P) (fun a => dS <= a < dS + 56)
             (proj1 H_img) H_pst Hh8 HEN HI).
    + intros a Ha. subst dS. lia.
    + exact (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ5).
    + intros r Hr. rewrite (HP5 r Hr). exact (HKR r Hr).
    + intros a Ha HnX HnW. rewrite <- (HAV a). apply Hfr5; [exact Ha | exact HnX |].
      rewrite <- HspT. unfold spZ at 1 2. rewrite Q2, (vv_E1_low E P 2 2%bv eq_refl). exact HnW.
    + intros a (Hh & b & Hb). apply Hpres5. split; [exact Hh|]. exists b. rewrite HM. exact Hb.
  - cbn [vv_upd ip_W ip_mem ip_kids ip_n]. intros j Hj. cbn [length repeat] in Hj.
    assert (Hbyte : nth j (repeat 0 56) 0 = 0) by (rewrite nth_repeat; reflexivity).
    rewrite Hbyte. split; [|lia].
    intros k Hk. replace k with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r. fold dS.
    pose proof (Hset (Z.of_nat j) ltac:(lia)) as Hz. change (0 mod 256) with 0 in Hz.
    unfold aview in Hz. destruct (mbyte SEGS (mrestrict (w_H (ip_W P)) mem5) (dS + Z.of_nat j)) as [b|] eqn:Eb;
      [|discriminate Hz].
    injection Hz as Hz. f_equal. apply bv_eq. rewrite Hz. reflexivity.
Qed.

(* ---- after the value (row 238, slot 6170): the model at the separator. vrd_jval's continuation once the value is
   read, VERBATIM, with the element already counted and accumulated ---- *)
Definition vrd_jsep (d : nat) (o : bool) (n cap : nat) (acc : list (list Z * jv)) (f : nat) (r : list Z)
  : PjGrammar.M (jv * list Z) :=
  match PjGrammar.skip r with
  | c :: r1 =>
      if c =? 44 then PjGrammar.jrl prh_jr_strtod f d o n cap acc r1
      else if c =? PjGrammar.closer o then PjGrammar.jret (PjGrammar.mk o (rev acc), r1)
      else PjGrammar.jrefuse
  | [] => PjGrammar.jrefuse
  end.

(* the model's FREE LIST at the separator (the kit's cut): VrdIElem.vrd_jfvk's continuation once the value is read,
   VERBATIM (PresetReqAt.jfl's body), with the element's list already in the accumulator af1 and the count one up *)
Definition vrd_jfsep (f d : nat) (o : bool) (n cap : nat) (af1 r : list Z) (ok : list bool) : list Z :=
  match PjGrammar.skip r with
  | c :: r1 => if c =? 44 then PresetReqAt.jfl ReaderRes.jr_strtod f d o n cap af1 r1 ok
               else af1 ++ PresetReqAt.arrz o cap
  | [] => af1 ++ PresetReqAt.arrz o cap
  end.

(* THE BATCH KIT'S LAYER AT THE SEPARATOR (the kit's cut): what vrd_icomma_a and vrd_iexit_a ask of it - cap = ncap of the count
   (already one up), the members' caps, and the completed slots' order list against af with the model's free list at
   jfl's body after the value (vrd_jfsep), at the same fuel as ip_cont *)
Definition vv_k1sep (E : vrd_ient) (P : vrd_ipos) : Prop :=
  ip_cap P = Z.of_nat (PresetReqAt.ncap (Z.to_nat (ip_n P))) /\ vrd_incaps E P /\
  exists af, vrd_iforder E P [] af /\
    (forall okr, prhPi_frees (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P ++ okr) =
       vrd_jfsep (ip_f P) (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) af
         (rest_atR (ie_tb E) (ie_text E) (ip_p P)) okr).

(* the position after the count store: one more element in the node and in the model, the cursor past the value;
   the kit's cut appends the batch kit's layer (vv_k1sep) *)
Definition vv_sep (E : vrd_ient) (P : vrd_ipos) : Prop :=
  vrd_iframe E P /\ vrd_iregs B E P /\ vrd_inode E P [] /\ vrd_icur B E P /\ vrd_ijrn B ARx SK E P /\
  vrd_imodel E P /\ 0 < ip_n P /\
  ip_cont P = vrd_jsep (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P)
                (rest_atR (ie_tb E) (ie_text E) (ip_p P)) /\
  vv_k1sep E P.

(* the model's free list after a GRANTED value: vrd_jfvk at the value's granted prefix is vrd_jfsep, with the value's
   own list prhPv_frees (the callee's post's) between the completed slots' af and the key's lk *)
Lemma vv_fl_some : forall d o x ok0 f n cap af lk y ok t r tr okr0,
  (forall okr, prhPi_frees d o x (ok0 ++ okr) = vrd_jfvk f (S d) o n cap af lk y okr) ->
  (2 * length y + 1 <= f)%nat ->
  PjGrammar.jr_value prh_jr_strtod (S d) y ok = (Some (t, r), tr, okr0) ->
  forall okr, prhPi_frees d o x ((ok0 ++ repeat true (PjGrammar.calls tr)) ++ okr) =
    vrd_jfsep f (S d) o (S n) cap (af ++ prhPv_frees (S d) y ok ++ lk) r okr.
Proof.
  intros d o x ok0 f n cap af lk y ok t r tr okr0 HF Hf HV okr.
  pose proof (PjGrammar.agrees_jr_value prh_jr_strtod (S d) y) as HAG.
  destruct (vl_agrees_some _ _ _ _ _ _ HAG HV) as (_ & _ & HUP & HVG).
  rewrite <- app_assoc, (HF (repeat true (PjGrammar.calls tr) ++ okr)). unfold vrd_jfvk.
  assert (HJ : PjGrammar.jrv ReaderRes.jr_strtod f (S d) y (repeat true (PjGrammar.calls tr) ++ okr) =
               (Some (t, r), tr, okr))
    by (rewrite (PjGrammar.jr_value_fuel ReaderRes.jr_strtod f (S d) y _ Hf); exact (HVG okr)).
  assert (HJF : PresetReqAt.jfv ReaderRes.jr_strtod f (S d) y (repeat true (PjGrammar.calls tr) ++ okr) =
                prhPv_frees (S d) y ok).
  { unfold prhPv_frees. rewrite (PresetFreeFo.jfv_fuel ReaderRes.jr_strtod f (S d) y _ Hf).
    apply (vv_jfv_det ReaderRes.jr_strtod (Nat.succ (2 * length y)) (S d) y ok _ (Some (t, r)) tr okr0).
    - assert (Hf1 : (2 * length y + 1 <= Nat.succ (2 * length y))%nat) by (rewrite Nat.add_1_r; apply le_n).
      rewrite (PjGrammar.jr_value_fuel ReaderRes.jr_strtod _ (S d) y ok Hf1). exact HV.
    - intros i Hi. rewrite app_nth1 by (rewrite repeat_length; exact Hi). rewrite nth_repeat.
      symmetry. exact (HUP i Hi). }
  rewrite HJ, HJF. unfold vrd_jfsep. cbv zeta. reflexivity.
Qed.

(* ... and after a REFUSED value: the partial child's list, the key's, then the arrays (jfl's None arm) *)
Lemma vv_fl_none : forall d o x ok0 f n cap af lk y ok tr okr0,
  (forall okr, prhPi_frees d o x (ok0 ++ okr) = vrd_jfvk f (S d) o n cap af lk y okr) ->
  (2 * length y + 1 <= f)%nat ->
  PjGrammar.jr_value prh_jr_strtod (S d) y ok = (None, tr, okr0) ->
  prhPi_frees d o x (ok0 ++ ok) = (af ++ prhPv_frees (S d) y ok ++ lk) ++ PresetReqAt.arrz o cap.
Proof.
  intros d o x ok0 f n cap af lk y ok tr okr0 HF Hf HV. rewrite (HF ok). unfold vrd_jfvk.
  assert (HJ : PjGrammar.jrv ReaderRes.jr_strtod f (S d) y ok = (None, tr, okr0))
    by (rewrite (PjGrammar.jr_value_fuel ReaderRes.jr_strtod f (S d) y ok Hf); exact HV).
  rewrite HJ. unfold prhPv_frees. rewrite (PresetFreeFo.jfv_fuel ReaderRes.jr_strtod f (S d) y ok Hf).
  cbv zeta. reflexivity.
Qed.

(* the head of the white-space loop (row 246, slot 6178): a0 = a2 = the cursor, a1 = the text's end, a byte left *)
Definition vv_wsl (E : vrd_ient) (P : vrd_ipos) : Prop :=
  vv_sep E P /\ getr (ip_regs P) 10 = w64 (ip_p P) /\ getr (ip_regs P) 12 = w64 (ip_p P) /\
  getr (ip_regs P) 11 = w64 (ie_text E + ie_len E) /\ ip_p P < ie_text E + ie_len E.

(* the separator test (row 265, slot 6197): a1 = the text's end, the cursor at the first non-white byte (or the end) *)
Definition vv_tail (E : vrd_ient) (P : vrd_ipos) : Prop :=
  vv_sep E P /\ getr (ip_regs P) 11 = w64 (ie_text E + ie_len E) /\
  PjGrammar.skip (rest_atR (ie_tb E) (ie_text E) (ip_p P)) = rest_atR (ie_tb E) (ie_text E) (ip_p P).

(* ---- the model lemmas of sub-lane IvalM ---- *)
(* the live room of the continuation after one call of the granted run *)

(* the allocator counter at the call's entry, and its slack over the calls the loop has made so far *)
Lemma vv_cnt_bound : forall CTX CTX0 CW E P,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_imodel E P ->
  0 <= ie_cnt E /\ ie_cnt E + Z.of_nat (PjGrammar.calls (ip_tr P)) < 2 ^ 64.
Proof.
  intros CTX CTX0 CW E P HEN HM.
  destruct HEN as (_ & _ & _ & _ & HRD & _ & Hnth & _).
  destruct HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLED & _ & HCB).
  pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HLED) as (_ & _ & Hcnt & _).
  destruct HM as (_ & HRUN & _).
  pose proof (HRUN []) as H0.
  pose proof (vv_skipn_nth _ _ _ Hnth) as HX.
  unfold rest_atR in H0, HCB. rewrite HX in H0, HCB.
  pose proof (PjGrammar.vspec_jr_items prh_jr_strtod (ie_d E) (ie_o E) (if ie_o E then 123 else 91)
                (skipn (S (Z.to_nat (ie_p E - ie_text E))) (ie_tb E)) (ip_ok P ++ [])) as HS.
  rewrite H0 in HS. unfold PjGrammar.vspec in HS. destruct HS as (HS1 & _).
  cbn [fst snd] in HS1. rewrite vi_calls_app in HS1. cbn [length] in HS1, HCB.
  split; lia.
Qed.
(* THE CALL'S ALL-GRANTED TRACE AT THE VALUE: the trace so far, then parse_value's granted trace, then the rest
   (VrdCallPos.vc_gt_split over vrd_jval's bind, the value's run at the position's fuel being jr_value's) *)
Lemma vv_gt_val : forall E P nm, vrd_imodel E P ->
  ip_cont P = vrd_jval (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P)) (Z.to_nat (ip_cap P)) (ip_acc P) (ip_f P) nm
                (rest_atR (ie_tb E) (ie_text E) (ip_p P)) ->
  exists more, prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) =
    ip_tr P ++ prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) ++ more.
Proof.
  intros E P nm HM Hc. pose proof HM as (_ & _ & _ & _ & HF & _).
  rewrite (vc_gt_split E P HM), Hc. unfold vrd_jval.
  match goal with |- context [snd (fst (PjGrammar.jbind ?m ?k []))] =>
    destruct (prhReader_jbind_pre _ _ m k []) as (t & Ht); rewrite Ht end.
  rewrite (PjGrammar.jr_value_fuel prh_jr_strtod (ip_f P) (S (ie_d E)) _ [] HF).
  exists t. unfold prhPv_gtrace. try rewrite <- !app_assoc. reflexivity.
Qed.

(* the trace of a value read makes at most the calls of the value's granted trace *)
Lemma vv_calls_val : forall d x ok,
  (PjGrammar.calls (snd (fst (PjGrammar.jr_value prh_jr_strtod d x ok))) <= PjGrammar.calls (prhPv_gtrace d x))%nat.
Proof. intros d x ok. exact (vc_calls_le_granted _ _ ok (PjGrammar.agrees_jr_value prh_jr_strtod d x)). Qed.

(* the steps so far granted every call: the counter and the failure index are the entry's plus those calls, and
   g_ran_out is the entry's (prh_oks refuses nothing on an all-true list) *)
Lemma vv_granted_regs : forall CTX CTX0 CW E P, vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_imodel E P ->
  ip_cnt P = ie_cnt E + Z.of_nat (PjGrammar.calls (ip_tr P)) /\ ip_fail P = ie_fail E /\ ip_ran P = ie_ran E.
Proof.
  intros CTX CTX0 CW E P HEN HM.
  destruct (vv_cnt_bound CTX CTX0 CW E P HEN HM) as (Hc0 & Hcb).
  pose proof HM as (HOK & _ & HLM & _).
  pose proof HLM as HLMg. rewrite HOK in HLMg.
  destruct (vi_lm_granted _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLMg Hc0 Hcb) as (Hcnt & Hfl).
  split; [exact Hcnt|]. split; [exact Hfl|].
  destruct HLM as ((_ & [Hran | (_ & k & _ & Hk & _)] & _) & _); [exact Hran|].
  unfold prh_refused in Hk. rewrite HOK, vrd_nth_rep_true in Hk. discriminate Hk.
Qed.

(* THE OUTCOME AFTER parse_value REFUSED (res = -1): parse_value's own OUTCOME clause (tparse_value_specX's post,
   verbatim at S := ip_S P1, S' := ip_S P2, res := None) at the run's position the trace so far reaches composes onto
   the exit's: the whole call's counter premise gives the callee's (the steps so far granted every call), the
   callee's answer is its granted run's, so the whole call's granted trace is the trace so far followed by it *)
Lemma vv_outc_callee : forall CTX CTX0 CW E P1 P2 nm ok tr okr0,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_imodel E P1 ->
  ip_cont P1 = vrd_jval (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P1)) (Z.to_nat (ip_cap P1)) (ip_acc P1) (ip_f P1) nm
                 (rest_atR (ie_tb E) (ie_text E) (ip_p P1)) ->
  PjGrammar.jr_value prh_jr_strtod (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P1)) ok = (None, tr, okr0) ->
  ip_ok P2 = ip_ok P1 ++ ok -> ip_tr P2 = ip_tr P1 ++ tr ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (ip_S P1) ->
     PRH_Base.prh_run_at sm x os i
       (PresetReqAt.rd_hevs (prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P1)))) ->
     PRH_Base.prh_cons_from sm x os i
       (length (PresetReqAt.rd_hevs (prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P1))))) ->
     (ip_fail P1 < ip_cnt P1 \/
      ip_cnt P1 + Z.of_nat (PjGrammar.calls (prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P1))))
        <= ip_fail P1) ->
     ip_ran P2 = ip_ran P1 /\
     fst (PjGrammar.jr_value ReaderRes.jr_strtod (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P1)) []) =
       (@None (jv * list Z), tr) /\
     exists hist', PresetRoomPos.iface_room_pos sm x os
       (i + length (PresetReqAt.rd_hevs (prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P1)))))%nat
       H0 hist' (ip_S P2)) ->
  vc_outc E P2.
Proof.
  intros CTX CTX0 CW E P1 P2 nm ok tr okr0 HEN HM1 HC1 HV Hok2 Htr2 HOCv sm x0 os i H0 hist HP HR HC Hctr.
  destruct (vv_granted_regs CTX CTX0 CW E P1 HEN HM1) as (Hcnt1 & Hfl1 & Hran1).
  pose proof HM1 as (HOK1 & HRUN1 & _ & _ & HFUEL1 & _ & _ & _ & HXF1 & _).
  (* the callee's granted run, from its OUTCOME at the position the trace so far reaches *)
  destruct (vv_gt_val E P1 nm HM1 HC1) as (more & HG).
  set (x := rest_atR (ie_tb E) (ie_text E) (ip_p P1)) in *.
  set (X := rest_atR (ie_tb E) (ie_text E) (ie_p E)) in *.
  rewrite HG in HR, HC.
  assert (Ha : PresetReqAt.rd_hevs (ip_tr P1 ++ prhPv_gtrace (S (ie_d E)) x ++ more) =
               PresetReqAt.rd_hevs (ip_tr P1) ++ PresetReqAt.rd_hevs (prhPv_gtrace (S (ie_d E)) x) ++
               PresetReqAt.rd_hevs more)
    by (unfold PresetReqAt.rd_hevs; rewrite !flat_map_app; reflexivity).
  rewrite Ha in HR, HC. rewrite !length_app in HC.
  apply PRH_Base.prh_run_at_app_iff in HR as [HR1 HR2].
  apply PRH_Base.prh_run_at_app_iff in HR2 as [HR2 _].
  apply PRH_Base.prh_cons_from_app_iff in HC as [_ HC2].
  apply PRH_Base.prh_cons_from_app_iff in HC2 as [HC2 _].
  destruct (HXF1 sm x0 os i H0 hist HP HR1) as (h1 & Hh1).
  assert (Hctr1 : ip_fail P1 < ip_cnt P1 \/
                  ip_cnt P1 + Z.of_nat (PjGrammar.calls (prhPv_gtrace (S (ie_d E)) x)) <= ip_fail P1).
  { rewrite HG, !vi_calls_app in Hctr. rewrite Hcnt1, Hfl1. destruct Hctr as [Hc | Hc]; [left | right]; lia. }
  destruct (HOCv sm x0 os _ H0 h1 Hh1 HR2 HC2 Hctr1) as (Hran2 & Hans & h2 & Hh2).
  rewrite vrd_strtod_same in Hans.
  (* so the continuation at P1 refuses on the granted run, after exactly the callee's granted trace *)
  assert (Hgtv : prhPv_gtrace (S (ie_d E)) x = tr) by (unfold prhPv_gtrace; rewrite Hans; reflexivity).
  assert (Hcv0 : fst (ip_cont P1 []) = (@None (jv * list Z), tr)).
  { rewrite HC1. unfold vrd_jval, PjGrammar.jbind.
    rewrite (PjGrammar.jr_value_fuel prh_jr_strtod (ip_f P1) (S (ie_d E)) x [] HFUEL1).
    destruct (PjGrammar.jr_value prh_jr_strtod (S (ie_d E)) x []) as [[r0 t0] o0].
    cbn [fst] in Hans. injection Hans as -> ->. reflexivity. }
  pose proof (PjGrammar.agrees_jr_items prh_jr_strtod (ie_d E) (ie_o E) X (ip_ok P1)) as (HA & _).
  assert (HE := HA (fun k _ => eq_trans (f_equal (fun l => nth k l true) HOK1) (vrd_nth_rep_true _ k))).
  pose proof (HRUN1 []) as H0r. rewrite app_nil_r in H0r. fold X in H0r. rewrite H0r in HE.
  destruct (ip_cont P1 []) as [[c1 c2] c3] eqn:Hc0. cbn [fst] in Hcv0. injection Hcv0 as -> ->.
  cbn [fst snd] in HE.
  assert (HGfull : prhPi_gtrace (ie_d E) (ie_o E) X = ip_tr P1 ++ tr)
    by (unfold prhPi_gtrace; apply (f_equal (fun z => snd (fst z))) in HE; cbn [fst snd] in HE; rewrite <- HE;
        reflexivity).
  split; [rewrite Hran2; exact Hran1|]. split.
  - rewrite vrd_strtod_same.
    apply (f_equal (fun z => fst (fst z))) in HE. cbn [fst snd] in HE.
    rewrite Hok2, HRUN1, HC1. unfold vrd_jval.
    assert (HVf : PjGrammar.jrv prh_jr_strtod (ip_f P1) (S (ie_d E)) x ok = (None, tr, okr0))
      by (rewrite (PjGrammar.jr_value_fuel prh_jr_strtod (ip_f P1) (S (ie_d E)) x ok HFUEL1); exact HV).
    rewrite (vv_jbind_none_run _ _ _ _ _ _ _ HVf). cbn [fst snd].
    unfold prhPi_gtrace in HGfull. fold X.
    destruct (PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E) X []) as [[g1 g2] g3].
    cbn [fst snd] in HE, HGfull |- *. rewrite <- HE, HGfull. reflexivity.
  - exists h2. rewrite HGfull, <- Hgtv.
    replace (i + length (PresetReqAt.rd_hevs (ip_tr P1 ++ prhPv_gtrace (S (ie_d E)) x)))%nat
      with (i + length (PresetReqAt.rd_hevs (ip_tr P1)) + length (PresetReqAt.rd_hevs (prhPv_gtrace (S (ie_d E)) x)))%nat
      by (unfold PresetReqAt.rd_hevs; rewrite flat_map_app, length_app; lia).
    exact Hh2.
Qed.

Lemma vv_model_some : forall CTX CTX0 CW E P1 P2 nm ok t r tr okr0 D,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_imodel E P1 ->
  ip_cont P1 = vrd_jval (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P1)) (Z.to_nat (ip_cap P1)) (ip_acc P1) (ip_f P1) nm
                 (rest_atR (ie_tb E) (ie_text E) (ip_p P1)) ->
  PjGrammar.jr_value prh_jr_strtod (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P1)) ok = (Some (t, r), tr, okr0) ->
  rd_ledger_move (ip_Lam P1) (ip_peak P1) (ip_cnt P1) (ip_fail P1) (ip_ran P1) (ie_most E) ok
    (prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P1))) tr D
    (ip_Lam P2) (ip_peak P2) (ip_cnt P2) (ip_fail P2) (ip_ran P2) ->
  room_live_cf (ip_S P2) ->
  (* the callee's hull use over its all-granted events (the text's conjunct after room_live_cf) *)
  PresetHullBudget.hull_used (ip_S P1) (ip_S P2)
    (PresetReqAt.rd_hevs (prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P1)))) ->
  blocks_bytes (ip_S P2) <= blocks_bytes (ip_S P1) + prh_held tr ->
  Ledger.lsum D = PjGrammar.held tr ->
  (* the callee's position transfer and live requests over its events *)
  vc_xfer (ip_S P1) (ip_S P2) tr -> vc_live (ip_S P1) (ip_S P2) tr ->
  rest_atR (ie_tb E) (ie_text E) (ip_p P2) = r ->
  ip_ok P2 = ip_ok P1 ++ repeat true (PjGrammar.calls tr) -> ip_tr P2 = ip_tr P1 ++ tr -> ip_D P2 = ip_D P1 ++ D ->
  ip_acc P2 = (nm, t) :: ip_acc P1 -> ip_f P2 = ip_f P1 ->
  ip_n P2 = ip_n P1 + 1 -> ip_cap P2 = ip_cap P1 -> 0 <= ip_n P1 ->
  ip_cont P2 = vrd_jsep (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P2)) (Z.to_nat (ip_cap P2)) (ip_acc P2) (ip_f P2)
                 (rest_atR (ie_tb E) (ie_text E) (ip_p P2)) ->
  vrd_imodel E P2.
Proof.
  intros CTX CTX0 CW E P1 P2 nm ok t r tr okr0 D HEN HM1 HC1 HV HLM HRL HHU HBB HLD HXF HLV Hp2 Hok2 Htr2 HD2 Hacc2
    Hf2 Hn2 Hcap2 Hn0 HC2.
  destruct (vv_cnt_bound CTX CTX0 CW E P1 HEN HM1) as (Hc0 & Hcb).
  destruct (vv_gt_val E P1 nm HM1 HC1) as (more & HG).
  pose proof HM1 as HM1'.
  destruct HM1 as (HOK1 & HRUN1 & HLM1 & HROOM1 & HFUEL1 & HBB1 & HDEP1 & HLS1 & HXF1 & HLV1 & HHU1).
  set (x := rest_atR (ie_tb E) (ie_text E) (ip_p P1)) in *.
  pose proof (PjGrammar.agrees_jr_value prh_jr_strtod (S (ie_d E)) x) as HAG.
  destruct (vl_agrees_some _ _ _ _ _ _ HAG HV) as (_ & _ & HUP & HVG).
  destruct (PjGrammar.agrees_some _ _ _ _ _ _ HAG HV) as (HV0 & _).
  assert (HJV : forall okr, PjGrammar.jrv prh_jr_strtod (ip_f P1) (S (ie_d E)) x okr =
                            PjGrammar.jr_value prh_jr_strtod (S (ie_d E)) x okr)
    by (intros okr; exact (PjGrammar.jr_value_fuel prh_jr_strtod (ip_f P1) (S (ie_d E)) x okr HFUEL1)).
  assert (HC2' : ip_cont P2 = vrd_jsep (S (ie_d E)) (ie_o E) (S (Z.to_nat (ip_n P1))) (Z.to_nat (ip_cap P1))
                                ((nm, t) :: ip_acc P1) (ip_f P1) r).
  { rewrite HC2, Hp2, Hacc2, Hf2, Hcap2, Hn2, (Z2Nat.inj_add (ip_n P1) 1 Hn0 ltac:(lia)).
    change (Z.to_nat 1) with 1%nat. rewrite Nat.add_1_r. reflexivity. }
  (* the continuation at P1 is the value's run followed by the continuation at P2 *)
  assert (HK : forall ok0 okr, PjGrammar.jr_value prh_jr_strtod (S (ie_d E)) x ok0 = (Some (t, r), tr, okr) ->
     ip_cont P1 ok0 = (fst (fst (ip_cont P2 okr)), tr ++ snd (fst (ip_cont P2 okr)), snd (ip_cont P2 okr))).
  { intros ok0 okr H. rewrite <- HJV in H. rewrite HC1. unfold vrd_jval.
    rewrite (vv_jbind_some_run _ _ _ _ _ _ _ _ H). rewrite HC2'. reflexivity. }
  assert (HLMg : rd_ledger_move (ip_Lam P1) (ip_peak P1) (ip_cnt P1) (ip_fail P1) (ip_ran P1) (ie_most E)
                   (repeat true (PjGrammar.calls tr)) (prhPv_gtrace (S (ie_d E)) x ++ more) tr D
                   (ip_Lam P2) (ip_peak P2) (ip_cnt P2) (ip_fail P2) (ip_ran P2)).
  { apply vc_lm_gt_ext; [unfold prhPv_gtrace; rewrite HV0; cbn [fst snd]; lia |].
    destruct HLM as (O & R1 & R2 & R3 & R4 & R5 & R6).
    refine (conj (vl_oks_granted _ _ _ _ _ _ _ _ HUP O) (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 _)))))).
    (* the granted prefix refuses nothing, under ok and under the all-true list alike: both refusal peaks are 0 *)
    rewrite R6, !prh_refused_peak_granted; [reflexivity | ..];
      intros i Hi He; first [rewrite vrd_nth_rep_true in He | rewrite (HUP i Hi) in He]; discriminate He. }
  assert (HLZ : Permutation (lszR (ip_tr P1 ++ tr)) (lszR (ip_tr P1) ++ lszR tr)).
  { pose proof (vv_lszR_app prh_jr_strtod (S (ie_d E)) x ok (ip_tr P1)) as H. rewrite HV in H. exact H. }
  assert (Hheld : 0 <= PjGrammar.held tr).
  { rewrite <- HLD. apply vv_lsum_nonneg. destruct HLM as (_ & _ & _ & _ & HQ & _). exact (vv_D_sizes _ _ HQ). }
  unfold vrd_imodel.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
  - rewrite Hok2, Htr2, HOK1, vi_calls_app, repeat_app. reflexivity.
  - intros okr. rewrite Hok2, <- app_assoc, HRUN1, (HK _ okr (HVG okr)), Htr2. cbn [fst snd].
    rewrite app_assoc. reflexivity.
  - rewrite HG, Hok2, Htr2, HD2. rewrite HOK1 in HLM1 |- *.
    exact (vl_ledger_move_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc0 Hcb HLM1 HLMg HLS1 HLZ).
  - rewrite (HK [] [] HV0) in HROOM1. cbn [fst snd] in HROOM1.
    exact (vl_room_tail (ip_S P1) (ip_S P2) tr _ HROOM1 HRL HLV).
  - rewrite Hp2, Hf2. pose proof (PjGrammar.jr_value_rest _ _ _ _ _ _ _ _ HV) as Hr. lia.
  - rewrite Htr2. unfold prh_held in *. rewrite vi_held_app, vi_calls_app, Nat2Z.inj_add, Z.mul_add_distr_l. lia.
  - rewrite Hacc2. constructor; [|exact HDEP1]. exact (PjGrammar.jr_value_depth _ _ _ _ _ _ _ _ HV).
  - rewrite HD2, Htr2, vi_lsum_app, vi_held_app, HLS1, HLD. reflexivity.
  - rewrite Htr2. exact (vc_xfer_app _ _ _ _ _ HXF1 HXF).
  - rewrite Htr2. exact (vc_live_app _ _ _ _ _ HLV1 HLV).
  - (* the hull use: the position's, then the callee's over its all-granted events, which on the granted run are
       the value's own trace (VrdIStep.vi_hull_step) *)
    assert (Egt : prhPv_gtrace (S (ie_d E)) x = tr) by (unfold prhPv_gtrace; rewrite HV0; reflexivity).
    rewrite Htr2. exact (vi_hull_step _ _ _ (ip_tr P1) tr _ (f_equal PresetReqAt.rd_hevs Egt) HHU1 HHU).
Qed.

Lemma vv_model_none : forall CTX CTX0 CW E P1 P2 nm ok tr okr0 D,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_imodel E P1 ->
  ip_cont P1 = vrd_jval (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P1)) (Z.to_nat (ip_cap P1)) (ip_acc P1) (ip_f P1) nm
                 (rest_atR (ie_tb E) (ie_text E) (ip_p P1)) ->
  PjGrammar.jr_value prh_jr_strtod (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P1)) ok = (None, tr, okr0) ->
  rd_ledger_move (ip_Lam P1) (ip_peak P1) (ip_cnt P1) (ip_fail P1) (ip_ran P1) (ie_most E) ok
    (prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P1))) tr D
    (ip_Lam P2) (ip_peak P2) (ip_cnt P2) (ip_fail P2) (ip_ran P2) ->
  blocks_bytes (ip_S P2) <= blocks_bytes (ip_S P1) + prh_held tr ->
  Ledger.lsum D = PjGrammar.held tr ->
  ip_ok P2 = ip_ok P1 ++ ok -> ip_tr P2 = ip_tr P1 ++ tr -> ip_D P2 = ip_D P1 ++ D ->
  (* the callee's position transfer, live requests and OUTCOME clause (tparse_value_specX's post, res := None) *)
  vc_xfer (ip_S P1) (ip_S P2) tr -> vc_live (ip_S P1) (ip_S P2) tr ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (ip_S P1) ->
     PRH_Base.prh_run_at sm x os i
       (PresetReqAt.rd_hevs (prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P1)))) ->
     PRH_Base.prh_cons_from sm x os i
       (length (PresetReqAt.rd_hevs (prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P1))))) ->
     (ip_fail P1 < ip_cnt P1 \/
      ip_cnt P1 + Z.of_nat (PjGrammar.calls (prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P1))))
        <= ip_fail P1) ->
     ip_ran P2 = ip_ran P1 /\
     fst (PjGrammar.jr_value ReaderRes.jr_strtod (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P1)) []) =
       (@None (jv * list Z), tr) /\
     exists hist', PresetRoomPos.iface_room_pos sm x os
       (i + length (PresetReqAt.rd_hevs (prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P1)))))%nat
       H0 hist' (ip_S P2)) ->
  rd_ledger_move (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E) (ip_ok P2)
    (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr P2)
    (ip_D P2) (ip_Lam P2) (ip_peak P2) (ip_cnt P2) (ip_fail P2) (ip_ran P2) /\
  blocks_bytes (ip_S P2) <= blocks_bytes (ie_S E) + prh_held (ip_tr P2) /\
  Ledger.lsum (ip_D P2) = PjGrammar.held (ip_tr P2) /\
  PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P2) =
    (None, ip_tr P2, okr0) /\
  vc_xfer (ie_S E) (ip_S P2) (ip_tr P2) /\ vc_live (ie_S E) (ip_S P2) (ip_tr P2) /\ vc_outc E P2.
Proof.
  intros CTX CTX0 CW E P1 P2 nm ok tr okr0 D HEN HM1 HC1 HV HLM HBB HLD Hok2 Htr2 HD2 HXF HLV HOCv.
  destruct (vv_cnt_bound CTX CTX0 CW E P1 HEN HM1) as (Hc0 & Hcb).
  destruct (vv_gt_val E P1 nm HM1 HC1) as (more & HG).
  pose proof (vv_outc_callee CTX CTX0 CW E P1 P2 nm ok tr okr0 HEN HM1 HC1 HV Hok2 Htr2 HOCv) as HOC.
  destruct HM1 as (HOK1 & HRUN1 & HLM1 & _ & HFUEL1 & HBB1 & _ & HLS1 & HXF1 & HLV1 & _).
  set (x := rest_atR (ie_tb E) (ie_text E) (ip_p P1)) in *.
  assert (HLZ : Permutation (lszR (ip_tr P1 ++ tr)) (lszR (ip_tr P1) ++ lszR tr)).
  { pose proof (vv_lszR_app prh_jr_strtod (S (ie_d E)) x ok (ip_tr P1)) as H. rewrite HV in H. exact H. }
  assert (HVf : PjGrammar.jrv prh_jr_strtod (ip_f P1) (S (ie_d E)) x ok = (None, tr, okr0)).
  { rewrite (PjGrammar.jr_value_fuel prh_jr_strtod (ip_f P1) (S (ie_d E)) x ok HFUEL1). exact HV. }
  assert (HLMx : rd_ledger_move (ip_Lam P1) (ip_peak P1) (ip_cnt P1) (ip_fail P1) (ip_ran P1) (ie_most E) ok
                   (prhPv_gtrace (S (ie_d E)) x ++ more) tr D
                   (ip_Lam P2) (ip_peak P2) (ip_cnt P2) (ip_fail P2) (ip_ran P2)).
  { apply vc_lm_gt_ext; [|exact HLM].
    pose proof (vv_calls_val (S (ie_d E)) x ok) as Hk. rewrite HV in Hk. exact Hk. }
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ HOC)))))).
  - rewrite HG, Hok2, Htr2, HD2. rewrite HOK1 in HLM1 |- *.
    exact (vl_ledger_move_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc0 Hcb HLM1 HLMx HLS1 HLZ).
  - rewrite Htr2. unfold prh_held in *. rewrite vi_held_app, vi_calls_app, Nat2Z.inj_add, Z.mul_add_distr_l. lia.
  - rewrite HD2, Htr2, vi_lsum_app, vi_held_app, HLS1, HLD. reflexivity.
  - rewrite Hok2, HRUN1, HC1. unfold vrd_jval. rewrite (vv_jbind_none_run _ _ _ _ _ _ _ HVf). cbn [fst snd].
    rewrite Htr2. reflexivity.
  - rewrite Htr2. exact (vc_xfer_app _ _ _ _ _ HXF1 HXF).
  - rewrite Htr2. exact (vc_live_app _ _ _ _ _ HLV1 HLV).
Qed.

(* ---- IvalM batch 2: the held peak and the counter across the call, the float registers ---- *)

(* the held peak of the trace up to and through a value read stays in the call's bound *)

(* the trace of a bind starts with the trace of its first computation *)
Lemma vv_jbind_tr_prefix : forall (A C : Type) (m : PjGrammar.M A) (k : A -> PjGrammar.M C) ok res t ok1,
  m ok = (res, t, ok1) -> exists u, snd (fst (PjGrammar.jbind m k ok)) = t ++ u.
Proof.
  intros A C m k ok res t ok1 H. unfold PjGrammar.jbind. rewrite H. destruct res as [a|].
  - destruct (k a ok1) as [[r t'] ok2]. exists t'. reflexivity.
  - exists []. rewrite app_nil_r. reflexivity.
Qed.

Lemma vv_hpeak_call : forall CTX CTX0 CW E P1 nm ok res tr okr0,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_imodel E P1 ->
  ip_cont P1 = vrd_jval (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P1)) (Z.to_nat (ip_cap P1)) (ip_acc P1) (ip_f P1) nm
                 (rest_atR (ie_tb E) (ie_text E) (ip_p P1)) ->
  PjGrammar.jr_value prh_jr_strtod (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P1)) ok = (res, tr, okr0) ->
  hpeakR (ip_tr P1 ++ tr) <= 224 * Z.of_nat (length (rest_atR (ie_tb E) (ie_text E) (ie_p E))) +
                             512 * Z.of_nat (PjGrammar.MAXD - ie_d E).
Proof.
  intros CTX CTX0 CW E P1 nm ok res tr okr0 HEN HM1 HC1 HV.
  destruct HEN as (_ & _ & _ & _ & _ & _ & Hnth & _).
  destruct HM1 as (_ & HRUN1 & _ & _ & HFUEL1 & _).
  pose proof (HRUN1 ok) as H0.
  rewrite <- (PjGrammar.jr_value_fuel prh_jr_strtod (ip_f P1) _ _ ok HFUEL1) in HV.
  assert (Hpre : exists u, snd (fst (ip_cont P1 ok)) = tr ++ u).
  { rewrite HC1. unfold vrd_jval. eapply vv_jbind_tr_prefix. exact HV. }
  destruct Hpre as (u & Hu).
  pose proof (vv_skipn_nth _ _ _ Hnth) as HX.
  pose proof (PjGrammar.vspec_jr_items prh_jr_strtod (ie_d E) (ie_o E) (if ie_o E then 123 else 91)
                (skipn (S (Z.to_nat (ie_p E - ie_text E))) (ie_tb E)) (ip_ok P1 ++ ok)) as HS.
  rewrite <- HX in HS.
  change (skipn (Z.to_nat (ie_p E - ie_text E)) (ie_tb E)) with (rest_atR (ie_tb E) (ie_text E) (ie_p E)) in HS.
  rewrite H0 in HS. unfold PjGrammar.vspec in HS. destruct HS as (_ & HS2 & _).
  cbn [fst snd] in HS2. rewrite Hu, app_assoc in HS2.
  pose proof (PjGrammar.pos_prefix (ip_tr P1 ++ tr) u) as Hpp.
  pose proof (vl_hpeak_le_pos (ip_tr P1 ++ tr)) as Hhp.
  set (mm := (PjGrammar.MAXD - ie_d E)%nat) in *. clearbody mm.
  lia.
Qed.

(* the counter's slack after a granted value read *)
Lemma vv_cnt_after : forall E P1 ok t r tr okr0 most gt D Lam' peak' cnt' fail' ran',
  ip_cnt P1 + 2 * Z.of_nat (length (rest_atR (ie_tb E) (ie_text E) (ip_p P1))) + 2 < 2 ^ 64 - 1 -> 0 <= ip_cnt P1 ->
  PjGrammar.jr_value prh_jr_strtod (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P1)) ok = (Some (t, r), tr, okr0) ->
  rd_ledger_move (ip_Lam P1) (ip_peak P1) (ip_cnt P1) (ip_fail P1) (ip_ran P1) most ok gt tr D Lam' peak' cnt' fail'
    ran' ->
  cnt' + 2 * Z.of_nat (length r) + 2 < 2 ^ 64 - 1.
Proof.
  intros E P1 ok t r tr okr0 most gt D Lam' peak' cnt' fail' ran' Hc Hc0 HV HLM.
  pose proof (PjGrammar.vspec_jr_value prh_jr_strtod (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P1)) ok)
    as HS.
  rewrite HV in HS. unfold PjGrammar.vspec in HS. destruct HS as (_ & _ & HS).
  destruct (HS t r eq_refl) as (_ & HS2 & _). cbn [fst snd] in HS2.
  destruct HLM as (_ & Hcnt & _).
  rewrite Hcnt, Z.mod_small by lia. lia.
Qed.

(* the float state's kept registers compose *)



(* ==== PART B: rows 224..237 - the arguments, `jal parse_value` (row 231), the count store, the result test ==== *)

(* a bind's trace starts with its first computation's trace *)
Lemma vv_jbind_tr : forall (A C : Type) (m : PjGrammar.M A) (k : A -> PjGrammar.M C) ok,
  exists t2, snd (fst (PjGrammar.jbind m k ok)) = snd (fst (m ok)) ++ t2.
Proof.
  intros A C m k ok. unfold PjGrammar.jbind.
  destruct (m ok) as [[[a|] t] ok1]; cbn [fst snd].
  - destruct (k a ok1) as [[r t'] ok2]. exists t'. reflexivity.
  - exists []. rewrite app_nil_r. reflexivity.
Qed.

(* the room for a run is room for its every prefix (the kit's cut: rd_room's live conjunct is per event,
   PRH_Base.prh_live_evs, and the prefix's events are a prefix of the run's: VrdLedgerStep.vl_live_evs_prefix) *)
Lemma vv_room_prefix : forall S t1 t2, rd_room S (t1 ++ t2) -> rd_room S t1.
Proof.
  intros S t1 t2 (H1 & H2 & H3). split; [exact H1|].
  rewrite vi_maxreq_app in H2. split; [lia|].
  assert (Ha : PresetReqAt.rd_hevs (t1 ++ t2) = PresetReqAt.rd_hevs t1 ++ PresetReqAt.rd_hevs t2)
    by (unfold PresetReqAt.rd_hevs; apply flat_map_app).
  rewrite Ha in H3. exact (vl_live_evs_prefix S _ _ H3).
Qed.

(* ---- the count store and the node after a call: sub-lanes IvalR (IvalR_B.v) and IvalA (IvalA_after.v), Qed ---- *)
(* ---- Qed lemmas proved separately and copied verbatim ---- *)
(* ================================================================================================
   PART B: the count store v->n := n + 1 (rows 232..237) and the node after a granted / refused element.
   ================================================================================================ *)

(* ADDED PREMISES (IvalR-2, see the final report):
   - vv_node_store_keep / vv_node_store_keep0 take `ie_v E + 8 <= a0` (the window starts at or above v + 8).
     WHY: without it the statement is FALSE. The node may sit at the base of a non-harness allocator block
     (rd_pre's prhReader_at, second arm), and then a ledger block's hidden head is the word [v, v + 8), whose
     bytes prh_ledger reads; a store at a0 = v would break it. The caller's window is [v + 40, v + 48).
   - vv_inode_snoc / vv_fd_exit take, besides vv_D_apart's NoDup / pairwise conjuncts at P1 and 0 <= cf_head,
     `NoDup (map fst (ip_Lam P1))` (vrd_icur's prh_ledger) and `ip_D P1 subset ip_Lam P1` (vrd_imodel's
     rd_ledger_move). WHY: a block of the position based AT kids with a size other than 56 * cap would reach
     into the slot kids[n], and no conjunct of vrd_inode or vv_D_apart excludes it; the ledger's distinct
     first components do (prh_fst_unique), which with NoDup (ip_D P1) leaves only the kids array itself. *)

Ltac vr_proj := unfold vk_move; cbn [ip_fx ip_ly ip_S ip_Hp ip_W ip_regs ip_mem ip_md ip_k ip_n ip_cap ip_kids
  ip_keys ip_p ip_acc ip_f ip_cont ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran].

(* ---- the bounds of a call: the loop's frame is above the ceiling, the node below it and below the shadow
   (prhPv_node's amem_range, whose high arm is refuted by the ceiling) ---- *)
Lemma vv_bnd : forall CTX CTX0 CW E, vrd_ient_ok B ARx CTX CTX0 CW E ->
  alloc_ceiling <= spZ (ie_regs E) - 144 /\ 0 <= ie_e E /\ spZ (ie_regs E) + ie_e E <= 2 ^ 47 /\
  spZ (ie_regs E) <= ie_q E /\ ie_q E + 24 <= spZ (ie_regs E) + ie_e E /\
  4096 <= ie_v E /\ ie_v E + 56 <= alloc_ceiling /\
  (ie_v E + 56 <= SHADOW_OFF \/ kHighShadowEnd <= ie_v E).
Proof.
  intros CTX CTX0 CW E HEN.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (vrd_node_low B ARx HL LAWS CTX CTX0 CW E HEN) as Hvceil.
  pose proof (vv_stk_items (ie_d E)) as HSTKi. unfold ESTACK in HSTKi.
  pose proof HEN as ((HAF & _) & _ & _ & _ & HRD & _).
  pose proof HAF as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & HS0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
  pose proof HRD as (_ & _ & _ & _ & _ & (He0 & _ & Hetop & _) & Hq0 & Hq24 & _ & _ & _ & _ & HNODE & _).
  pose proof HNODE as (Hv4096 & _ & _ & _ & _ & Hvmr & _).
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvmr.
  unfold SHADOW_OFF, kHighShadowEnd. repeat split; lia.
Qed.

(* ---- where the node sits at the position: a live allocator block or a live fake frame (rd_pre's prhPv_node
   at the entry, carried to P by rd_blocks_move; the granted-window case is refuted by vrd_node_low) ---- *)
Lemma vv_node_place : forall CTX CTX0 CW E P,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_ijrn B ARx SK E P ->
  (exists b m, In (b, m) (ablocks B (ip_ly P) (ip_S P)) /\ b <= ie_v E /\ ie_v E + 56 <= b + req_size m) \/
  (exists cid pos, In (cid, pos) (frames (ip_S P)) /\
     frame_addr (ip_ly P) cid pos <= ie_v E /\ ie_v E + 56 <= frame_addr (ip_ly P) cid pos + fs_frame_bytes cid).
Proof.
  intros CTX CTX0 CW E P HEN HJN.
  pose proof (vrd_node_low B ARx HL LAWS CTX CTX0 CW E HEN) as Hvceil.
  pose proof (@cf_head_nonneg cp) as Hh0.
  pose proof HEN as ((HAFN & _) & _ & _ & _ & HRD & _).
  pose proof HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNODE & _ & _ & _ & HLED & _).
  pose proof HNODE as (_ & _ & _ & _ & HATv & _).
  pose proof HJN as (HJ & _ & _ & _ & _ & HBM & _).
  pose proof HJ as (_ & Hly & _).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
  pose proof HBM as (_ & HABP & HFRP & _).
  assert (Hold : forall x, In x (ablocks B (ie_ly E) (ie_S E)) -> In x (ablocks B (ip_ly P) (ip_S P)))
    by (intros x Hx; apply (Permutation_in _ (Permutation_sym HABP)); apply in_or_app; right; exact Hx).
  destruct HATv as [(a1 & k1 & Hin1 & Hlo & Hhi) | [(b & m & Hinb & _ & Hlo & Hhi) |
                   [(cid & pos & Hf & Hlo & Hhi) | (Hlo & Hhi)]]].
  - destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a1 k1 _ _ HLED Hin1) as (Hk1 & Hab1 & _).
    left. exists (a1 - cf_head), (k1 + cf_head). split; [exact (Hold _ Hab1)|].
    unfold req_size. destruct (Z.eqb_spec (k1 + cf_head) 0); lia.
  - left. exists b, m. split; [exact (Hold _ Hinb)|].
    unfold req_size. destruct (Z.eqb_spec m 0); lia.
  - right. exists cid, pos. split; [apply (Permutation_in _ (Permutation_sym HFRP)); exact Hf|].
    unfold frame_addr in *. rewrite EF. lia.
  - exfalso. pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
    pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _). lia.
Qed.

(* the node's bytes are not image bytes (AR_laws_x's client-image law at the position) *)
Lemma vv_nimg : forall CTX CTX0 CW E P a,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_ijrn B ARx SK E P ->
  ie_v E <= a < ie_v E + 56 -> ~ in_img SEGS a.
Proof.
  intros CTX CTX0 CW E P a HEN HJN Ha.
  pose proof HJN as ((HAR & _) & _).
  destruct (vv_node_place CTX CTX0 CW E P HEN HJN) as [(b & m & Hin & H1 & H2) | (cid & pos & Hf & H1 & H2)].
  - exact (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ b m a HAR Hin ltac:(lia)).
  - exact (frm_img_x SEGS B ARx LAWS _ _ _ _ _ _ cid pos a HAR Hf ltac:(lia)).
Qed.

(* a ledger head's eight bytes lie below v + 8 or at or above v + 56: the head block and the node's place are
   the same allocator block (and then the head is at its base, at or below v) or separate by AR_laws_x's sep law *)
Lemma vv_head_apart : forall CTX CTX0 CW E P Lam peak cnt fail ran most own a k i,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_ijrn B ARx SK E P ->
  prh_ledger B (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) Lam peak cnt fail ran most own ->
  In (a, k) Lam -> 0 <= i < 8 ->
  a - cf_head + i < ie_v E + 8 \/ ie_v E + 56 <= a - cf_head + i.
Proof.
  intros CTX CTX0 CW E P Lam peak cnt fail ran most own a k i HEN HJN HLED Hin Hi.
  pose proof H_head as (Hh8 & _).
  pose proof HJN as ((HAR & _) & _).
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HLED Hin) as (Hk0 & Hab & _).
  assert (Hkc : 0 <= k + cf_head) by lia.
  pose proof (req_size_pos (k + cf_head) Hkc) as (Hr1 & Hr2).
  destruct (vv_node_place CTX CTX0 CW E P HEN HJN) as [(b & m & Hinb & H1 & H2) | (cid & pos & Hf & H1 & H2)].
  - destruct (Z.eq_dec (a - cf_head) b) as [Eb | Nb]; [left; lia|].
    assert (Hne : (b, m) <> (a - cf_head, k + cf_head)) by (intros E0; injection E0 as E1 E2; lia).
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ b m (a - cf_head) (k + cf_head) HAR Hinb Hab Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ (a - cf_head) (k + cf_head) cid pos HAR Hab Hf) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* ---- the shadow facts across a store BELOW the shadow region (the node is below kLowMemEnd) ---- *)
Lemma vv_keep_ra_low : forall (H : word -> bool) (m m' : word -> option byte) a0 w a n,
  (forall x : word, ~ (a0 <= bv_unsigned x < a0 + w) -> mrestrict H m' x = mrestrict H m x) ->
  0 <= a0 -> (a0 + w <= SHADOW_OFF \/ kHighShadowEnd + 8 <= a0) -> 0 <= a -> a + n <= 2 ^ 47 ->
  range_addressable (aview SEGS H m) SHADOW_OFF a n -> range_addressable (aview SEGS H m') SHADOW_OFF a n.
Proof.
  intros H m m' a0 w a n HK H0 Hlo Ha Han HR x Hx. destruct (HR x Hx) as (s & Hs & Hok).
  exists s. split; [|exact Hok]. unfold shadow_of_addr in *.
  assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (vk_keep_av H m m' a0 (a0 + w) _ HK) by (unfold SHADOW_OFF, kHighShadowEnd in *; lia). exact Hs.
Qed.

Lemma vv_keep_hull_low : forall (H : word -> bool) (m m' : word -> option byte) a0 w a n,
  (forall x : word, ~ (a0 <= bv_unsigned x < a0 + w) -> mrestrict H m' x = mrestrict H m x) ->
  0 <= a0 -> (a0 + w <= SHADOW_OFF \/ kHighShadowEnd + 8 <= a0) -> 0 <= a -> a + n <= 2 ^ 47 -> 0 < n ->
  shadow_hull_vis (aview SEGS H m) a n -> shadow_hull_vis (aview SEGS H m') a n.
Proof.
  intros H m m' a0 w a n HK H0 Hlo Ha Han Hn HV s Hs. unfold shadow_addr in Hs.
  assert (Hd1 : 0 <= (a + n - 1) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (Hd0 : 0 <= a / 8) by (apply Z.div_pos; lia).
  assert (Esh : SHADOW_OFF / 8 * 8 = SHADOW_OFF) by (unfold SHADOW_OFF; reflexivity).
  pose proof (Z.div_le_mono SHADOW_OFF (SHADOW_OFF + a / 8) 8 ltac:(lia) ltac:(lia)) as Hm1.
  assert (Hup : (SHADOW_OFF + (a + n - 1) / 8) / 8 * 8 <= SHADOW_OFF + (a + n - 1) / 8)
    by (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
  assert (Hs2 : SHADOW_OFF <= s < kHighShadowEnd + 8) by (unfold SHADOW_OFF, kHighShadowEnd in *; lia).
  rewrite (vk_keep_av H m m' a0 (a0 + w) _ HK) by (unfold SHADOW_OFF, kHighShadowEnd in *; lia).
  apply HV. exact Hs.
Qed.

(* ================================ R1: the count store ================================ *)

Lemma vv_store_core : forall CTX CTX0 CW E P (regs : bvmap 5 word) mem' md' k' a0 w,
  vrd_ient_ok B ARx CTX CTX0 CW E ->
  vrd_iframe E P -> vrd_ijrn B ARx SK E P ->
  ie_v E + 8 <= a0 -> a0 + w <= ie_v E + 56 -> 0 <= w ->
  (forall x : word, ~ (a0 <= bv_unsigned x < a0 + w) ->
     mrestrict (w_H (ip_W P)) mem' x = mrestrict (w_H (ip_W P)) (ip_mem P) x) ->
  spZ regs = spZ (ip_regs P) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E) (spZ (ie_regs E) + ie_e E)
    (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem' md' k' (ie_CW E) ->
  vrd_iframe E (vk_move P regs mem' md' k' (ip_p P)) /\
  vrd_ijrn B ARx SK E (vk_move P regs mem' md' k' (ip_p P)) /\
  rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem')
    (fun a => 0 <= a < 2 ^ 64 /\ ~ (a0 <= a < a0 + w)) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (a0 <= a < a0 + w) ->
     aview SEGS (w_H (ip_W P)) mem' a = aview SEGS (w_H (ip_W P)) (ip_mem P) a) /\
  (forall Lam peak cnt fail ran most own,
     prh_ledger B (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) Lam peak cnt fail ran most own ->
     prh_ledger B (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem' Lam peak cnt fail ran most own).
Proof.
  intros CTX CTX0 CW E P regs mem' md' k' a0 w HEN HFR HJN Hw0 Hw1 Hw2 HK Hsp HJ'.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof H_head as (Hh8 & HLh).
  destruct (vv_bnd CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv4 & Bv56 & Bvsh).
  pose proof HJN as ((HAR & _) & _).
  assert (Hnimg : forall a, ie_v E <= a < ie_v E + 56 -> ~ in_img SEGS a)
    by (intros a Ha; exact (vv_nimg CTX CTX0 CW E P a HEN HJN Ha)).
  assert (HAV : forall a, 0 <= a < 2 ^ 64 -> ~ (a0 <= a < a0 + w) ->
            aview SEGS (w_H (ip_W P)) mem' a = aview SEGS (w_H (ip_W P)) (ip_mem P) a)
    by (intros a Ha Hn; exact (vk_keep_av _ (ip_mem P) mem' a0 (a0 + w) a HK Ha Hn)).
  assert (HKall : rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem')
            (fun a => 0 <= a < 2 ^ 64 /\ ~ (a0 <= a < a0 + w)))
    by (apply (vk_keep_rd _ (ip_mem P) mem' a0 (a0 + w) _ HK); intros a Ha; exact Ha).
  split; [|split; [|split; [|split]]].
  - (* the frame *)
    pose proof HFR as (Hf0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 &
      F17 & Fpres).
    unfold vrd_iframe. cbv zeta. vr_proj.
    split; [rewrite Hsp; exact Hf0|].
    repeat match goal with
    | |- val_mem _ _ _ _ _ /\ _ => split; [eapply VrdFrame.val_mem_keep; [eassumption|];
                                     eapply VrdFrame.rd_keep_mono; [exact HKall | cbn; intros; lia]|]
    end.
    intros a Ha.
    apply (vk_apresent_keep _ (ip_mem P) mem' a0 w a HK); [lia | lia | exact (Fpres a Ha)].
  - (* the journal, the caller window, the read-only view and the chain *)
    pose proof HJN as (HJ & Hwin & Hfz & Hfk & Haro & Hbm & Hch).
    unfold vrd_ijrn. vr_proj.
    split; [exact HJ'|].
    split.
    { intros a Ha Hnf. rewrite <- (Hwin a Ha Hnf). apply HAV; lia. }
    split; [exact Hfz|]. split; [exact Hfk|].
    split.
    { intros a Hro Hno Herr.
      assert (Hi : in_img SEGS a).
      { destruct Hro as [(s & Hs & _ & Hr) | Hr];
          [exists s; split; [exact Hs | exact Hr] | exact (@pa_relro_img _ _ PAI a Hr)]. }
      pose proof (@pa_segs_low _ _ PAI a Hi) as Hl. unfold kLowMemEnd in Hl.
      rewrite HAV; [exact (Haro a Hro Hno Herr) | lia |].
      intros Hbad. exact (Hnimg a ltac:(lia) Hi). }
    split; [exact Hbm|].
    apply (vrd_chain_keep_w B ARx SK HL LAWS CTX CTX0 CW E P (ip_W P) mem' (ip_ly P)
             (proj1 H_img) (proj1 (proj2 H_img)) HEN HFR HJN eq_refl).
    intros a Ha Hnf. apply HAV; lia.
  - exact HKall.
  - exact HAV.
  - (* the ledger: the statics are image bytes, the heads are apart from the node *)
    intros Lam peak cnt fail ran most own HLED.
    assert (Hhead_rng : forall a k i, In (a, k) Lam -> 0 <= i < 8 -> 0 <= a - cf_head + i < 2 ^ 64).
    { intros a k i Hin Hi.
      destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HLED Hin) as (Hk0 & Hab & _).
      destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & H4 & Hc & _).
      assert (Hkc : 0 <= k + cf_head) by lia.
      pose proof (req_size_pos (k + cf_head) Hkc) as (Hr1 & Hr2). lia. }
    eapply prh_ledger_kept_aview; [exact HLED | | | |].
    + intros a Ha. pose proof (@pa_segs_low _ _ PAI a (H_pst a Ha)) as Hl. unfold kLowMemEnd in Hl.
      apply HAV; [lia|]. intros Hbad. exact (Hnimg a ltac:(lia) (H_pst a Ha)).
    + intros a k i Hin Hi.
      pose proof (vv_head_apart CTX CTX0 CW E P Lam peak cnt fail ran most own a k i HEN HJN HLED Hin Hi) as Hap.
      apply HAV; [exact (Hhead_rng a k i Hin Hi) | lia].
    + intros a k _ Hab. exact Hab.
    + apply Permutation_refl.
Qed.

(* R1 WITHOUT the cursor: the frame, the ledger at the new memory, the journal facts and the keep *)
Lemma vv_node_store_keep0 : forall CTX CTX0 CW E P (regs : bvmap 5 word) mem' md' k' a0 w,
  vrd_ient_ok B ARx CTX CTX0 CW E ->
  vrd_iframe E P ->
  prh_ledger B (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P)
    (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P) (ie_most E) (ie_own E) ->
  vrd_ijrn B ARx SK E P ->
  ie_v E <= a0 -> ie_v E + 8 <= a0 -> a0 + w <= ie_v E + 56 -> 0 <= w ->
  (forall x : word, ~ (a0 <= bv_unsigned x < a0 + w) ->
     mrestrict (w_H (ip_W P)) mem' x = mrestrict (w_H (ip_W P)) (ip_mem P) x) ->
  spZ regs = spZ (ip_regs P) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E) (spZ (ie_regs E) + ie_e E)
    (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem' md' k' (ie_CW E) ->
  vrd_iframe E (vk_move P regs mem' md' k' (ip_p P)) /\
  prh_ledger B (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem'
    (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P) (ie_most E) (ie_own E) /\
  vrd_ijrn B ARx SK E (vk_move P regs mem' md' k' (ip_p P)) /\
  rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem')
    (fun a => 0 <= a < 2 ^ 64 /\ ~ (a0 <= a < a0 + w)).
Proof.
  intros CTX CTX0 CW E P regs mem' md' k' a0 w HEN HFR HLED HJN Hv0 Hw0 Hw1 Hw2 HK Hsp HJ'.
  destruct (vv_store_core CTX CTX0 CW E P regs mem' md' k' a0 w HEN HFR HJN Hw0 Hw1 Hw2 HK Hsp HJ')
    as (Gfr & Gjr & Gkp & Gav & Gled).
  split; [exact Gfr|]. split; [exact (Gled _ _ _ _ _ _ _ HLED)|]. split; [exact Gjr | exact Gkp].
Qed.

Lemma vv_node_store_keep : forall CTX CTX0 CW E P (regs : bvmap 5 word) mem' md' k' a0 w,
  vrd_ient_ok B ARx CTX CTX0 CW E ->
  vrd_iframe E P -> vrd_icur B E P -> vrd_ijrn B ARx SK E P ->
  ie_v E <= a0 -> ie_v E + 8 <= a0 -> a0 + w <= ie_v E + 56 -> 0 <= w ->
  (forall x : word, ~ (a0 <= bv_unsigned x < a0 + w) ->
     mrestrict (w_H (ip_W P)) mem' x = mrestrict (w_H (ip_W P)) (ip_mem P) x) ->
  spZ regs = spZ (ip_regs P) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E) (spZ (ie_regs E) + ie_e E)
    (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem' md' k' (ie_CW E) ->
  vrd_iframe E (vk_move P regs mem' md' k' (ip_p P)) /\
  vrd_icur B E (vk_move P regs mem' md' k' (ip_p P)) /\
  vrd_ijrn B ARx SK E (vk_move P regs mem' md' k' (ip_p P)) /\
  rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem')
    (fun a => 0 <= a < 2 ^ 64 /\ ~ (a0 <= a < a0 + w)).
Proof.
  intros CTX CTX0 CW E P regs mem' md' k' a0 w HEN HFR HCU HJN Hv0 Hw0 Hw1 Hw2 HK Hsp HJ'.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (vv_bnd CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv4 & Bv56 & Bvsh).
  pose proof HEN as (_ & _ & _ & _ & HRD & _).
  pose proof HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hqv & Htv & _).
  destruct (vv_store_core CTX CTX0 CW E P regs mem' md' k' a0 w HEN HFR HJN Hw0 Hw1 Hw2 HK Hsp HJ')
    as (Gfr & Gjr & Gkp & Gav & Gled).
  pose proof HCU as (Hpin & Hraq & Hsrc & Hhome & Hled & Hfrm & Hcnt).
  pose proof Hpin as (_ & _ & _ & _ & _ & Htxt0 & Htxt62 & Hple & Hlen & Hgarr & Hqt & Hd32).
  pose proof Hsrc as (Hby & Ht4 & Htl & Ham & Hra & Hhull).
  split; [exact Gfr|].
  split; [|split; [exact Gjr | exact Gkp]].
  unfold vrd_icur. cbv zeta. vr_proj.
  split.
  { eapply pj_in_okR_keep; [exact Hpin|].
    eapply VrdFrame.rd_keep_mono; [exact Gkp|]. intros z Hz. cbv beta in Hz. split; lia. }
  split.
  { apply (vv_keep_ra_low _ (ip_mem P) mem' a0 w (ie_q E) 24 HK);
      [lia | unfold SHADOW_OFF, kHighShadowEnd in *; lia | lia | lia | exact Hraq]. }
  split.
  { split; [|split; [exact Ht4 | split; [exact Htl | split; [exact Ham | split]]]].
    - unfold PRH_Base.bytes_at in *.
      eapply garr8_keep; [exact Hby|].
      eapply VrdFrame.rd_keep_mono; [exact Gkp|]. intros z Hz. cbv beta in Hz. split; lia.
    - apply (vv_keep_ra_low _ (ip_mem P) mem' a0 w (ie_text E) (Z.of_nat (length (ie_tb E))) HK);
        [lia | unfold SHADOW_OFF, kHighShadowEnd in *; lia | lia | lia | exact Hra].
    - intros Hl0.
      apply (vv_keep_hull_low _ (ip_mem P) mem' a0 w (ie_text E) (Z.of_nat (length (ie_tb E))) HK);
        [lia | unfold SHADOW_OFF, kHighShadowEnd in *; lia | lia | lia | lia | exact (Hhull Hl0)]. }
  split; [exact Hhome|].
  split; [exact (Gled _ _ _ _ _ _ _ Hled)|].
  split; [exact Hfrm | exact Hcnt].
Qed.

(* ================ the representation lemmas of IvalR_rep.v (copied, Qed there) ================ *)

Lemma vv_items_snoc : forall (P : Z -> jv -> list (Z * Z) -> Prop) a l D u Du,
  pj_itemsR P a l D -> P (a + 56 * Z.of_nat (length l)) u Du -> pj_itemsR P a (l ++ [u]) (D ++ Du).
Proof.
  intros P a l; revert a; induction l as [|w r IH]; intros a D u Du HD HP.
  - cbn [pj_itemsR] in HD; subst D. cbn [pj_itemsR app].
    exists Du, []. split; [rewrite app_nil_r; reflexivity|]. split; [|reflexivity].
    refine (eq_ind _ (fun z => P z u Du) HP _ _); cbn [length]; lia.
  - cbn [pj_itemsR] in HD. destruct HD as (D1 & D2 & -> & H1 & H2). cbn [pj_itemsR app].
    exists D1, (D2 ++ Du). split; [rewrite <- app_assoc; reflexivity|]. split; [exact H1|].
    apply (IH (a + 56) D2 u Du H2).
    refine (eq_ind _ (fun z => P z u Du) HP _ _); cbn [length]; lia.
Qed.

Lemma vv_mems_snoc : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) a ka l D nm u x k Du,
  pj_memsR SEGS m lblk P a ka l D ->
  rd_u64 SEGS m (ka + 8 * Z.of_nat (length l)) x -> pj_cstrR SEGS m lblk x k nm ->
  P (a + 56 * Z.of_nat (length l)) u Du ->
  pj_memsR SEGS m lblk P a ka (l ++ [(nm, u)]) (D ++ (x, k) :: Du).
Proof.
  intros m lblk P a ka l; revert a ka; induction l as [|[nm0 w] r IH];
    intros a ka D nm u x k Du HD Hx Hc HP.
  - cbn [pj_memsR] in HD; subst D. cbn [pj_memsR app].
    exists x, k, Du, []. split; [rewrite app_nil_r; reflexivity|].
    split; [refine (eq_ind _ (fun z => rd_u64 SEGS m z x) Hx _ _); cbn [length]; lia|].
    split; [exact Hc|].
    split; [refine (eq_ind _ (fun z => P z u Du) HP _ _); cbn [length]; lia|reflexivity].
  - cbn [pj_memsR] in HD. destruct HD as (x0 & k0 & D1 & D2 & -> & H0 & H1 & H2 & H3).
    cbn [pj_memsR app].
    exists x0, k0, D1, (D2 ++ (x, k) :: Du). split; [rewrite <- app_assoc; reflexivity|].
    split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
    apply (IH (a + 56) (ka + 8) D2 nm u x k Du H3).
    + refine (eq_ind _ (fun z => rd_u64 SEGS m z x) Hx _ _); cbn [length]; lia.
    + exact Hc.
    + refine (eq_ind _ (fun z => P z u Du) HP _ _); cbn [length]; lia.
Qed.

Lemma vv_pf_S : forall m lblk (P : Z -> list (Z * Z) -> Prop) ks a ka n D,
  pf_itemsR SEGS m lblk P ks a ka (S n) D <->
  exists Dk D1 D2, D = Dk ++ D1 ++ D2 /\ pj_keyR SEGS m lblk ks ka Dk /\ P a D1 /\
    pf_itemsR SEGS m lblk P ks (a + 56) (ka + 8) n D2.
Proof. intros. split; intros H; exact H. Qed.

Lemma vv_pf_snoc : forall m lblk (P : Z -> list (Z * Z) -> Prop) ks a ka n D Dk D1,
  pf_itemsR SEGS m lblk P ks a ka n D ->
  pj_keyR SEGS m lblk ks (ka + 8 * Z.of_nat n) Dk -> P (a + 56 * Z.of_nat n) D1 ->
  pf_itemsR SEGS m lblk P ks a ka (S n) (D ++ Dk ++ D1).
Proof.
  intros m lblk P ks a ka n; revert a ka; induction n as [|n IH]; intros a ka D Dk D1 HD Hk HP.
  - cbn [pf_itemsR] in HD; subst D. apply (proj2 (vv_pf_S _ _ _ _ _ _ _ _)).
    exists Dk, D1, []. split; [rewrite app_nil_r; reflexivity|].
    split; [refine (eq_ind _ (fun z => pj_keyR SEGS m lblk ks z Dk) Hk _ _); lia|].
    split; [refine (eq_ind _ (fun z => P z D1) HP _ _); lia|].
    cbn [pf_itemsR]; reflexivity.
  - destruct (proj1 (vv_pf_S _ _ _ _ _ _ _ _) HD) as (Dk0 & E1 & E2 & -> & H0 & H1 & H2).
    apply (proj2 (vv_pf_S _ _ _ _ _ _ _ _)).
    exists Dk0, E1, (E2 ++ Dk ++ D1). split; [rewrite <- !app_assoc; reflexivity|].
    split; [exact H0|]. split; [exact H1|].
    apply (IH (a + 56) (ka + 8) E2 Dk D1 H2).
    + refine (eq_ind _ (fun z => pj_keyR SEGS m lblk ks z Dk) Hk _ _); lia.
    + refine (eq_ind _ (fun z => P z D1) HP _ _); lia.
Qed.

Lemma vv_fd_node : forall m lblk k v ty kids keys n cap (ks : bool) Dit Dall,
  pj_hdrR SEGS m v ty 0 0 kids keys n cap ->
  NoDup Dall -> pj_apartR Dall v ->
  0 < cap -> lblk kids (56 * cap) -> 0 <= n <= cap ->
  (if ks then lblk keys (8 * cap) else keys = 0) ->
  pf_itemsR SEGS m lblk (pj_fdR SEGS m lblk k) ks kids keys (Z.to_nat n) Dit ->
  Permutation Dall ([(kids, 56 * cap)] ++ (if ks then [(keys, 8 * cap)] else []) ++ Dit) ->
  pj_fdR SEGS m lblk (S k) v Dall.
Proof.
  intros m lblk k v ty kids keys n cap ks Dit Dall Hh Hnd Hap Hc Hk Hn Hks Hit Hp.
  cbn [pj_fdR]. unfold pj_fshapeR.
  split; [exact Hnd|]. split; [exact Hap|].
  exists ty, 0, 0, kids, keys, n, cap, ks, [], [(kids, 56 * cap)],
    (if ks then [(keys, 8 * cap)] else []), Dit.
  split; [exact Hh|].
  split; [left; split; reflexivity|].
  split; [right; exists (56 * cap); split; [exact Hk|split; [lia|reflexivity]]|].
  split.
  { destruct ks.
    - right. split; [reflexivity|]. exists (8 * cap). split; [exact Hks|split; [lia|reflexivity]].
    - left. split; [exact Hks|split; reflexivity]. }
  split; [exact Hp|exact Hit].
Qed.

(* ================ R2 / R3: the node after the element ================ *)

Lemma vv_nodup_dup : forall (l l1 l2 l3 : list (Z * Z)) (x : Z * Z),
  NoDup l -> Permutation l (l1 ++ (x :: l2) ++ l3) -> In x l3 -> False.
Proof.
  intros l l1 l2 l3 x HN HP Hin.
  assert (HN0 : List.NoDup l) by (first [exact HN | apply NoDup_ListNoDup; exact HN]).
  assert (HN' : List.NoDup (l1 ++ (x :: l2) ++ l3)) by (eapply Permutation_NoDup; [exact HP | exact HN0]).
  apply NoDup_remove_2 in HN'. apply HN'. apply in_or_app. right. apply in_or_app. right. exact Hin.
Qed.

Lemma vv_perm_move : forall (x : Z * Z) (A Dn : list (Z * Z)), Permutation (x :: A ++ Dn) (A ++ x :: Dn).
Proof. intros x A Dn. apply Permutation_middle. Qed.

Lemma vv_rd_rw_sub : forall m a n a' n', rd_rw SEGS m a n -> a <= a' -> a' + n' <= a + n -> rd_rw SEGS m a' n'.
Proof. intros m a n a' n' H H1 H2 x Hx. apply H. lia. Qed.

(* a block of the position that is not the kids array does not meet the slot kids[n] *)
Lemma vv_slot_off : forall (D : list (Z * Z)) kids cap n a k z,
  (forall a1 k1 a2 k2, In (a1, k1) D -> In (a2, k2) D -> a1 <> a2 ->
     a1 + k1 <= a2 - cf_head \/ a2 + k2 <= a1 - cf_head) ->
  0 <= cf_head ->
  In (kids, 56 * cap) D -> In (a, k) D -> a <> kids ->
  0 <= n -> n < cap -> a <= z < a + k ->
  ~ (kids + 56 * n <= z < kids + 56 * n + 56).
Proof.
  intros D kids cap n a k z Hpw Hcf Hk Ha Hne Hn Hnc Hz Hbad.
  destruct (Hpw a k kids (56 * cap) Ha Hk Hne) as [H1 | H2]; lia.
Qed.

(* the members read so far, at the later memory: the only block of the position based at kids is the kids
   array itself (the ledger's first components are distinct), so no block the members read meets the slot *)
Lemma vv_old_keep : forall E P1 (m2 : word -> option byte) (Lam2 : list (Z * Z)) Dx,
  vrd_inode E P1 Dx ->
  ip_n P1 < ip_cap P1 ->
  0 <= cf_head ->
  NoDup (ip_D P1) ->
  (forall a k a' k', In (a, k) (ip_D P1) -> In (a', k') (ip_D P1) -> a <> a' ->
     a + k <= a' - cf_head \/ a' + k' <= a - cf_head) ->
  NoDup (map fst (ip_Lam P1)) ->
  (forall a k, In (a, k) (ip_D P1) -> In (a, k) (ip_Lam P1)) ->
  (forall a k, In (a, k) (ip_Lam P1) -> In (a, k) Lam2) ->
  rd_keep SEGS (mrestrict (w_H (ip_W P1)) (ip_mem P1)) m2
    (fun a => rd_blk (ip_D P1) a /\ ~ (ip_kids P1 + 56 * ip_n P1 <= a < ip_kids P1 + 56 * ip_n P1 + 56)) ->
  exists Di,
    Permutation (ip_D P1) (Dx ++ [(ip_kids P1, 56 * ip_cap P1)] ++
      (if ie_o E then [(ip_keys P1, 8 * ip_cap P1)] else []) ++ Di) /\
    (if ie_o E
     then pj_memsR SEGS m2 (prh_lin Lam2) (pj_nodeR SEGS m2 (prh_lin Lam2))
            (ip_kids P1) (ip_keys P1) (rev (ip_acc P1)) Di
     else pj_itemsR (pj_nodeR SEGS m2 (prh_lin Lam2)) (ip_kids P1) (map snd (rev (ip_acc P1))) Di).
Proof.
  intros E P1 m2 Lam2 Dx HND Hnc Hcf HNoD Hpw HLND HDL HLM HK.
  pose proof HND as (Hhdr & Hn0 & Hcap & Hc0 & Hlin & Hlen & (Di & HPerm & HTree) & Hrw & Hrav & Hrak & Hrakeys & Hkz).
  assert (Hcpos : 0 < ip_cap P1) by lia.
  assert (Ec : (ip_cap P1 =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (EK : kids_blkR (ip_kids P1) (ip_cap P1) = [(ip_kids P1, 56 * ip_cap P1)])
    by (unfold kids_blkR; rewrite Ec; reflexivity).
  assert (EY : keys_blkR (if ie_o E then 6 else 5) (ip_keys P1) (ip_cap P1) =
               (if ie_o E then [(ip_keys P1, 8 * ip_cap P1)] else []))
    by (unfold keys_blkR; rewrite Ec; destruct (ie_o E); reflexivity).
  rewrite EK, EY in HPerm.
  exists Di. split; [exact HPerm|].
  assert (Hsub : forall b, In b (Dx ++ [(ip_kids P1, 56 * ip_cap P1)] ++
                   (if ie_o E then [(ip_keys P1, 8 * ip_cap P1)] else []) ++ Di) -> In b (ip_D P1))
    by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPerm) Hb)).
  assert (Hkin : In (ip_kids P1, 56 * ip_cap P1) (ip_D P1))
    by (apply Hsub; apply in_or_app; right; left; reflexivity).
  assert (HDiin : forall b, In b Di -> In b (ip_D P1))
    by (intros b Hb; apply Hsub; apply in_or_app; right; apply in_or_app; right;
        apply in_or_app; right; exact Hb).
  assert (HDik : forall k, ~ In (ip_kids P1, k) Di).
  { intros k Hin.
    assert (Hk1 : In (ip_kids P1, k) (ip_Lam P1)) by (apply HDL; apply HDiin; exact Hin).
    assert (Hk2 : In (ip_kids P1, 56 * ip_cap P1) (ip_Lam P1)) by (apply HDL; exact Hkin).
    assert (Ek : k = 56 * ip_cap P1) by (exact (prh_fst_unique _ _ _ _ HLND Hk1 Hk2)).
    subst k.
    refine (vv_nodup_dup (ip_D P1) Dx [] _ (ip_kids P1, 56 * ip_cap P1) HNoD HPerm _).
    apply in_or_app. right. exact Hin. }
  assert (HGood : forall z, (ip_kids P1 <= z < ip_kids P1 + 56 * ip_n P1
                   \/ (ie_o E = true /\ ip_keys P1 <= z < ip_keys P1 + 8 * ip_n P1)
                   \/ rd_blk Di z) ->
          rd_blk (ip_D P1) z /\ ~ (ip_kids P1 + 56 * ip_n P1 <= z < ip_kids P1 + 56 * ip_n P1 + 56)).
  { intros z [Hz | [(Ho & Hz) | Hz]].
    - split; [apply (rd_blk_in _ (ip_kids P1, 56 * ip_cap P1)); [exact Hkin | cbn [fst snd]; lia] | lia].
    - assert (Hyin : In (ip_keys P1, 8 * ip_cap P1) (ip_D P1)).
      { apply Hsub. apply in_or_app. right. apply in_or_app. right. rewrite Ho.
        apply in_or_app. left. left. reflexivity. }
      split; [apply (rd_blk_in _ (ip_keys P1, 8 * ip_cap P1)); [exact Hyin | cbn [fst snd]; lia]|].
      destruct (Z.eq_dec (ip_keys P1) (ip_kids P1)) as [Eq | Nq]; [lia|].
      exact (vv_slot_off (ip_D P1) (ip_kids P1) (ip_cap P1) (ip_n P1) (ip_keys P1) (8 * ip_cap P1) z
               Hpw Hcf Hkin Hyin Nq ltac:(lia) ltac:(lia) ltac:(lia)).
    - apply Exists_exists in Hz as ([a k] & Hb & Hx). unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
      split; [apply (rd_blk_in _ (a, k)); [exact (HDiin _ Hb) | cbn [fst snd]; lia]|].
      destruct (Z.eq_dec a (ip_kids P1)) as [Eq | Nq]; [subst a; exfalso; exact (HDik k Hb)|].
      exact (vv_slot_off (ip_D P1) (ip_kids P1) (ip_cap P1) (ip_n P1) a k z
               Hpw Hcf Hkin (HDiin _ Hb) Nq ltac:(lia) ltac:(lia) Hx). }
  destruct (ie_o E) eqn:Ho.
  - eapply pj_memsR_keep; [exact HTree | intros x k Hin Hb; exact (HLM x k Hb)|].
    eapply VrdFrame.rd_keep_mono; [exact HK|].
    rewrite length_rev, Hlen. intros z [Hz | [Hz | Hz]]; apply HGood;
      [left; lia | right; left; split; [reflexivity | lia] | right; right; exact Hz].
  - eapply pj_itemsR_keep; [exact HTree | intros x k Hin Hb; exact (HLM x k Hb)|].
    eapply VrdFrame.rd_keep_mono; [exact HK|].
    rewrite length_map, length_rev, Hlen. intros z [Hz | Hz]; apply HGood;
      [left; lia | right; right; exact Hz].
Qed.

Lemma vv_inode_snoc : forall E P1 P2 nm Dx t D,
  vrd_inode E P1 Dx ->
  (if ie_o E then exists x k, Dx = [(x, k)] /\
       rd_u64 SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (ip_keys P1 + 8 * ip_n P1) x /\
       pj_cstrR SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (prh_lin (ip_Lam P2)) x k nm
   else Dx = []) ->
  ip_n P1 < ip_cap P1 ->
  ip_n P2 = ip_n P1 + 1 -> ip_cap P2 = ip_cap P1 -> ip_kids P2 = ip_kids P1 -> ip_keys P2 = ip_keys P1 ->
  ip_acc P2 = (nm, t) :: ip_acc P1 -> ip_D P2 = ip_D P1 ++ D ->
  (forall a k, In (a, k) (ip_Lam P1) -> In (a, k) (ip_Lam P2)) ->
  pj_hdrR SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (ie_v E) (if ie_o E then 6 else 5) 0 0
    (ip_kids P1) (ip_keys P1) (ip_n P1 + 1) (ip_cap P1) ->
  rd_keep SEGS (mrestrict (w_H (ip_W P1)) (ip_mem P1)) (mrestrict (w_H (ip_W P2)) (ip_mem P2))
    (fun a => rd_blk (ip_D P1) a /\ ~ (ip_kids P1 + 56 * ip_n P1 <= a < ip_kids P1 + 56 * ip_n P1 + 56)) ->
  pj_nodeR SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (prh_lin (ip_Lam P2)) (ip_kids P1 + 56 * ip_n P1) t D ->
  range_addressable (aview SEGS (w_H (ip_W P2)) (ip_mem P2)) SHADOW_OFF (ie_v E) 56 ->
  (0 < ip_cap P2 -> range_addressable (aview SEGS (w_H (ip_W P2)) (ip_mem P2)) SHADOW_OFF (ip_kids P2) (56 * ip_cap P2)) ->
  (ie_o E = true -> 0 < ip_cap P2 ->
     range_addressable (aview SEGS (w_H (ip_W P2)) (ip_mem P2)) SHADOW_OFF (ip_keys P2) (8 * ip_cap P2)) ->
  (* ADDED PREMISES *)
  0 <= cf_head ->
  NoDup (ip_D P1) ->
  (forall a k a' k', In (a, k) (ip_D P1) -> In (a', k') (ip_D P1) -> a <> a' ->
     a + k <= a' - cf_head \/ a' + k' <= a - cf_head) ->
  NoDup (map fst (ip_Lam P1)) ->
  (forall a k, In (a, k) (ip_D P1) -> In (a, k) (ip_Lam P1)) ->
  vrd_inode E P2 [].
Proof.
  intros E P1 P2 nm Dx t D HND HKY Hnc Hn2 Hcap2 Hkids2 Hkeys2 Hacc2 HD2 HLM Hhdr2 HK HNode
    Hrav2 Hrak2 Hrakeys2 Hcf HNoD Hpw HLND HDL.
  pose proof HND as (Hhdr1 & Hn01 & Hcap1 & Hc01 & Hlin1 & Hlen1 & _ & Hrw1 & _).
  pose proof HND as Hkz1'. destruct Hkz1' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hkz1).
  assert (Hcpos : 0 < ip_cap P1) by lia.
  assert (Ec : (ip_cap P1 =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (EK : kids_blkR (ip_kids P1) (ip_cap P1) = [(ip_kids P1, 56 * ip_cap P1)])
    by (unfold kids_blkR; rewrite Ec; reflexivity).
  assert (EY : keys_blkR (if ie_o E then 6 else 5) (ip_keys P1) (ip_cap P1) =
               (if ie_o E then [(ip_keys P1, 8 * ip_cap P1)] else []))
    by (unfold keys_blkR; rewrite Ec; destruct (ie_o E); reflexivity).
  destruct (vv_old_keep E P1 (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (ip_Lam P2) Dx
              HND Hnc Hcf HNoD Hpw HLND HDL HLM HK) as (Di & HPerm & HTree2).
  unfold vrd_inode. cbv zeta.
  rewrite Hkids2, Hkeys2, Hn2, Hcap2.
  split; [exact Hhdr2|].
  split; [lia|]. split; [lia|].
  split; [intros Hz; exfalso; lia|].
  split.
  { intros Hc. destruct (Hlin1 Hcpos) as (HLk & HLy). split.
    - unfold prh_lin in *. exact (HLM _ _ HLk).
    - intros Ho. unfold prh_lin in *. exact (HLM _ _ (HLy Ho)). }
  split.
  { rewrite Hacc2. cbn [length]. rewrite Nat2Z.inj_succ. lia. }
  split.
  { rewrite EK, EY.
    destruct (ie_o E) eqn:Ho.
    - destruct HKY as (x & k & HDx & Hu64 & Hcstr).
      exists (Di ++ (x, k) :: D). split.
      + rewrite HD2, HDx in *. cbn [app].
        eapply Permutation_trans; [apply Permutation_app_tail; exact HPerm|].
        cbn [app].
        etransitivity; [apply perm_swap|]. apply perm_skip.
        etransitivity; [apply perm_swap|]. apply perm_skip.
        apply vv_perm_move.
      + rewrite <- Hlen1 in Hu64, HNode.
        rewrite <- (length_rev (ip_acc P1)) in Hu64, HNode.
        replace (rev (ip_acc P2)) with (rev (ip_acc P1) ++ [(nm, t)])
          by (rewrite Hacc2; cbn [rev]; reflexivity).
        exact (vv_mems_snoc _ _ _ _ _ _ _ nm t x k D HTree2 Hu64 Hcstr HNode).
    - subst Dx. exists (Di ++ D). split.
      + rewrite HD2. cbn [app].
        eapply Permutation_trans; [apply Permutation_app_tail; exact HPerm|].
        cbn [app]. rewrite <- ?app_assoc. apply Permutation_refl.
      + replace (map snd (rev (ip_acc P2))) with (map snd (rev (ip_acc P1)) ++ [t])
          by (rewrite Hacc2; cbn [rev]; rewrite map_app; reflexivity).
        rewrite <- Hlen1 in HNode.
        rewrite <- (length_rev (ip_acc P1)) in HNode.
        rewrite <- (length_map snd (rev (ip_acc P1))) in HNode.
        exact (vv_items_snoc _ _ _ _ t D HTree2 HNode). }
  split.
  { eapply rd_rw_keep;
      [apply (vv_rd_rw_sub _ (ip_kids P1 + 56 * ip_n P1) (56 * (ip_cap P1 - ip_n P1)));
       [exact Hrw1 | lia | lia]|].
    eapply VrdFrame.rd_keep_mono; [exact HK|]. intros z Hz. cbv beta in Hz. split.
    - apply (rd_blk_in _ (ip_kids P1, 56 * ip_cap P1)).
      + apply (Permutation_in _ (Permutation_sym HPerm)).
        apply in_or_app. right. left. reflexivity.
      + cbn [fst snd]. lia.
    - lia. }
  split; [exact Hrav2|].
  split; [intros Hc; rewrite <- Hkids2, <- Hcap2; apply Hrak2; lia|].
  split; [intros Ho Hc; rewrite <- Hkeys2, <- Hcap2; apply Hrakeys2; [exact Ho | lia]|].
  intros Ho. exact (Hkz1 Ho).
Qed.

Lemma vv_fd_exit : forall E P1 P2 nm Dx D,
  vrd_inode E P1 Dx ->
  (if ie_o E then exists x k, Dx = [(x, k)] /\
       rd_u64 SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (ip_keys P1 + 8 * ip_n P1) x /\
       pj_cstrR SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (prh_lin (ip_Lam P2)) x k nm
   else Dx = []) ->
  ip_n P1 < ip_cap P1 -> (ie_d E < PjGrammar.MAXD)%nat ->
  ip_D P2 = ip_D P1 ++ D ->
  (forall a k, In (a, k) (ip_Lam P1) -> In (a, k) (ip_Lam P2)) ->
  Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - S (ie_d E))%nat) (ip_acc P1) ->
  pj_hdrR SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (ie_v E) (if ie_o E then 6 else 5) 0 0
    (ip_kids P1) (ip_keys P1) (ip_n P1 + 1) (ip_cap P1) ->
  rd_keep SEGS (mrestrict (w_H (ip_W P1)) (ip_mem P1)) (mrestrict (w_H (ip_W P2)) (ip_mem P2))
    (fun a => rd_blk (ip_D P1) a /\ ~ (ip_kids P1 + 56 * ip_n P1 <= a < ip_kids P1 + 56 * ip_n P1 + 56)) ->
  pj_fdR SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (prh_lin (ip_Lam P2)) (PjGrammar.MAXD - S (ie_d E))
    (ip_kids P1 + 56 * ip_n P1) D ->
  NoDup (ip_D P2) -> pj_apartR (ip_D P2) (ie_v E) ->
  (* ADDED PREMISES *)
  0 <= cf_head ->
  NoDup (ip_D P1) ->
  (forall a k a' k', In (a, k) (ip_D P1) -> In (a', k') (ip_D P1) -> a <> a' ->
     a + k <= a' - cf_head \/ a' + k' <= a - cf_head) ->
  NoDup (map fst (ip_Lam P1)) ->
  (forall a k, In (a, k) (ip_D P1) -> In (a, k) (ip_Lam P1)) ->
  pj_fdR SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (prh_lin (ip_Lam P2)) (PjGrammar.MAXD - ie_d E)
    (ie_v E) (ip_D P2).
Proof.
  intros E P1 P2 nm Dx D HND HKY Hnc Hd HD2 HLM Hdep Hhdr2 HK Hfd HNoD2 Hap2 Hcf HNoD Hpw HLND HDL.
  pose proof HND as (Hhdr1 & Hn01 & Hcap1 & Hc01 & Hlin1 & Hlen1 & _ & Hrw1 & _).
  pose proof HND as Hkz1'. destruct Hkz1' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hkz1).
  assert (Hcpos : 0 < ip_cap P1) by lia.
  destruct (vv_old_keep E P1 (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (ip_Lam P2) Dx
              HND Hnc Hcf HNoD Hpw HLND HDL HLM HK) as (Di & HPerm & HTree2).
  assert (Ek : (PjGrammar.MAXD - ie_d E)%nat = S (PjGrammar.MAXD - S (ie_d E))%nat) by lia.
  rewrite Ek.
  assert (Hcnt : Z.to_nat (ip_n P1 + 1) = S (length (ip_acc P1))) by lia.
  destruct (ie_o E) eqn:Ho.
  - destruct HKY as (x & k & HDx & Hu64 & Hcstr).
    assert (HFa : Forall (fun mm => rd_nodefd SEGS (snd mm)) (rev (ip_acc P1)))
      by (apply Forall_forall; intros u _; apply vrd_nodefd_all).
    assert (Hdp : Forall (fun mm => (PjTree.depth (snd mm) <= PjGrammar.MAXD - S (ie_d E))%nat) (rev (ip_acc P1)))
      by (apply Forall_rev; exact Hdep).
    pose proof (vrd_fd_mems SEGS (rev (ip_acc P1)) HFa (PjGrammar.MAXD - S (ie_d E))%nat
                  (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (prh_lin (ip_Lam P2))
                  (ip_kids P1) (ip_keys P1) Di HTree2 Hdp) as Hpf.
    rewrite length_rev in Hpf.
    apply (vv_fd_node (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (prh_lin (ip_Lam P2))
             (PjGrammar.MAXD - S (ie_d E))%nat (ie_v E) 6 (ip_kids P1) (ip_keys P1)
             (ip_n P1 + 1) (ip_cap P1) true (Di ++ [(x, k)] ++ D) (ip_D P2)).
    + exact Hhdr2.
    + exact HNoD2.
    + exact Hap2.
    + exact Hcpos.
    + destruct (Hlin1 Hcpos) as (HLk & _). unfold prh_lin in *. exact (HLM _ _ HLk).
    + lia.
    + destruct (Hlin1 Hcpos) as (_ & HLy). unfold prh_lin in *. exact (HLM _ _ (HLy eq_refl)).
    + rewrite Hcnt.
      apply (vv_pf_snoc (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (prh_lin (ip_Lam P2))
               (pj_fdR SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (prh_lin (ip_Lam P2))
                  (PjGrammar.MAXD - S (ie_d E))%nat) true (ip_kids P1) (ip_keys P1)
               (length (ip_acc P1)) Di [(x, k)] D Hpf).
      * cbn [pj_keyR]. exists x. split.
        -- rewrite Hlen1. exact Hu64.
        -- right. exists k. split; [exact (proj1 Hcstr) | reflexivity].
      * rewrite Hlen1. exact Hfd.
    + rewrite HD2. rewrite HDx in HPerm. cbn [app].
      eapply Permutation_trans; [apply Permutation_app_tail; exact HPerm|].
      cbn [app].
      etransitivity; [apply perm_swap|]. apply perm_skip.
      etransitivity; [apply perm_swap|]. apply perm_skip.
      apply vv_perm_move.
  - subst Dx.
    assert (HFa : Forall (rd_nodefd SEGS) (map snd (rev (ip_acc P1))))
      by (apply Forall_forall; intros u _; apply vrd_nodefd_all).
    assert (Hdp : Forall (fun u => (PjTree.depth u <= PjGrammar.MAXD - S (ie_d E))%nat)
                    (map snd (rev (ip_acc P1))))
      by (apply Forall_map; apply Forall_rev; exact Hdep).
    pose proof (vrd_fd_items SEGS (map snd (rev (ip_acc P1))) HFa (PjGrammar.MAXD - S (ie_d E))%nat
                  (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (prh_lin (ip_Lam P2))
                  (ip_kids P1) (ip_keys P1) Di HTree2 Hdp) as Hpf.
    rewrite length_map, length_rev in Hpf.
    apply (vv_fd_node (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (prh_lin (ip_Lam P2))
             (PjGrammar.MAXD - S (ie_d E))%nat (ie_v E) 5 (ip_kids P1) (ip_keys P1)
             (ip_n P1 + 1) (ip_cap P1) false (Di ++ [] ++ D) (ip_D P2)).
    + exact Hhdr2.
    + exact HNoD2.
    + exact Hap2.
    + exact Hcpos.
    + destruct (Hlin1 Hcpos) as (HLk & _). unfold prh_lin in *. exact (HLM _ _ HLk).
    + lia.
    + exact (Hkz1 eq_refl).
    + rewrite Hcnt.
      apply (vv_pf_snoc (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (prh_lin (ip_Lam P2))
               (pj_fdR SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (prh_lin (ip_Lam P2))
                  (PjGrammar.MAXD - S (ie_d E))%nat) false (ip_kids P1) (ip_keys P1)
               (length (ip_acc P1)) Di [] D Hpf).
      * cbn [pj_keyR]. reflexivity.
      * rewrite Hlen1. exact Hfd.
    + rewrite HD2. cbn [app].
      eapply Permutation_trans; [apply Permutation_app_tail; exact HPerm|].
      cbn [app]. rewrite <- ?app_assoc. apply Permutation_refl.
Qed.

(* ==== THE KIT'S CUT: THE BATCH KIT'S LAYER ACROSS THE VALUE (the free order and the capacities of the completed slots, the
   slot the value filled, and the refused partial slot; a Theorem Labs lane's B' twins PItems_value_aftv.v / PItems_forder.v
   pis_fo_snoc / pis_fo_item on a working branch 34d46afa0965) ==== *)

(* the bytes the completed slots read at a value slot (the members' slots, the key slots, the members' blocks) are
   bytes of the position's blocks off the free slot kids[n]: vv_old_keep's HGood, for any extra block list Dx and
   members' block list Di the position's block list splits into, and over the whole keys array *)
Lemma vv_old_good : forall E P1 Dx Di,
  ip_n P1 < ip_cap P1 -> 0 <= ip_n P1 -> 0 <= cf_head -> NoDup (ip_D P1) ->
  (forall a k a' k', In (a, k) (ip_D P1) -> In (a', k') (ip_D P1) -> a <> a' ->
     a + k <= a' - cf_head \/ a' + k' <= a - cf_head) ->
  NoDup (map fst (ip_Lam P1)) ->
  (forall a k, In (a, k) (ip_D P1) -> In (a, k) (ip_Lam P1)) ->
  Permutation (ip_D P1) (Dx ++ kids_blkR (ip_kids P1) (ip_cap P1) ++
                         keys_blkR (if ie_o E then 6 else 5) (ip_keys P1) (ip_cap P1) ++ Di) ->
  forall z, (ip_kids P1 <= z < ip_kids P1 + 56 * ip_n P1 \/
             (ie_o E = true /\ ip_keys P1 <= z < ip_keys P1 + 8 * ip_cap P1) \/ rd_blk Di z) ->
  rd_blk (ip_D P1) z /\ ~ (ip_kids P1 + 56 * ip_n P1 <= z < ip_kids P1 + 56 * ip_n P1 + 56).
Proof.
  intros E P1 Dx Di Hnc Hn0 Hcf HNoD Hpw HLND HDL HPerm z Hz.
  assert (Hcpos : 0 < ip_cap P1) by lia.
  assert (Ec : (ip_cap P1 =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (EK : kids_blkR (ip_kids P1) (ip_cap P1) = [(ip_kids P1, 56 * ip_cap P1)])
    by (unfold kids_blkR; rewrite Ec; reflexivity).
  assert (EY : keys_blkR (if ie_o E then 6 else 5) (ip_keys P1) (ip_cap P1) =
               (if ie_o E then [(ip_keys P1, 8 * ip_cap P1)] else []))
    by (unfold keys_blkR; rewrite Ec; destruct (ie_o E); reflexivity).
  rewrite EK, EY in HPerm.
  assert (Hsub : forall b, In b (Dx ++ [(ip_kids P1, 56 * ip_cap P1)] ++
                   (if ie_o E then [(ip_keys P1, 8 * ip_cap P1)] else []) ++ Di) -> In b (ip_D P1))
    by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPerm) Hb)).
  assert (Hkin : In (ip_kids P1, 56 * ip_cap P1) (ip_D P1))
    by (apply Hsub; apply in_or_app; right; left; reflexivity).
  assert (HDiin : forall b, In b Di -> In b (ip_D P1))
    by (intros b Hb; apply Hsub; apply in_or_app; right; apply in_or_app; right;
        apply in_or_app; right; exact Hb).
  assert (HDik : forall k, ~ In (ip_kids P1, k) Di).
  { intros k Hin.
    assert (Hk1 : In (ip_kids P1, k) (ip_Lam P1)) by (apply HDL; apply HDiin; exact Hin).
    assert (Hk2 : In (ip_kids P1, 56 * ip_cap P1) (ip_Lam P1)) by (apply HDL; exact Hkin).
    assert (Ek : k = 56 * ip_cap P1) by (exact (prh_fst_unique _ _ _ _ HLND Hk1 Hk2)).
    subst k.
    refine (vv_nodup_dup (ip_D P1) Dx [] _ (ip_kids P1, 56 * ip_cap P1) HNoD HPerm _).
    apply in_or_app. right. exact Hin. }
  destruct Hz as [Hz | [(Ho & Hz) | Hz]].
  - split; [apply (rd_blk_in _ (ip_kids P1, 56 * ip_cap P1)); [exact Hkin | cbn [fst snd]; lia] | lia].
  - assert (Hyin : In (ip_keys P1, 8 * ip_cap P1) (ip_D P1)).
    { apply Hsub. apply in_or_app. right. apply in_or_app. right. rewrite Ho.
      apply in_or_app. left. left. reflexivity. }
    split; [apply (rd_blk_in _ (ip_keys P1, 8 * ip_cap P1)); [exact Hyin | cbn [fst snd]; lia]|].
    destruct (Z.eq_dec (ip_keys P1) (ip_kids P1)) as [Eq | Nq].
    + (* one base, one ledger entry: the sizes 8 cap and 56 cap would be equal *)
      exfalso. rewrite Eq in Hyin.
      pose proof (prh_fst_unique _ _ _ _ HLND (HDL _ _ Hyin) (HDL _ _ Hkin)). lia.
    + exact (vv_slot_off (ip_D P1) (ip_kids P1) (ip_cap P1) (ip_n P1) (ip_keys P1) (8 * ip_cap P1) z
               Hpw Hcf Hkin Hyin Nq ltac:(lia) ltac:(lia) ltac:(lia)).
  - apply Exists_exists in Hz as ([a k] & Hb & Hx). unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    split; [apply (rd_blk_in _ (a, k)); [exact (HDiin _ Hb) | cbn [fst snd]; lia]|].
    destruct (Z.eq_dec a (ip_kids P1)) as [Eq | Nq]; [subst a; exfalso; exact (HDik k Hb)|].
    exact (vv_slot_off (ip_D P1) (ip_kids P1) (ip_cap P1) (ip_n P1) a k z
             Hpw Hcf Hkin (HDiin _ Hb) Nq ltac:(lia) ltac:(lia) Hx).
Qed.

(* the completed slots' order list and the key slot keys[n] at a later memory and a grown ledger *)
Lemma vv_oitems_frame : forall E P1 m2 Lam2 Dk Di1 Facc1 nn,
  ip_n P1 < ip_cap P1 -> 0 <= ip_n P1 -> 0 <= cf_head -> NoDup (ip_D P1) ->
  (forall a k a' k', In (a, k) (ip_D P1) -> In (a', k') (ip_D P1) -> a <> a' ->
     a + k <= a' - cf_head \/ a' + k' <= a - cf_head) ->
  NoDup (map fst (ip_Lam P1)) ->
  (forall a k, In (a, k) (ip_D P1) -> In (a, k) (ip_Lam P1)) ->
  (forall a k, In (a, k) (ip_Lam P1) -> In (a, k) Lam2) ->
  Permutation (ip_D P1) (Dk ++ kids_blkR (ip_kids P1) (ip_cap P1) ++
                         keys_blkR (if ie_o E then 6 else 5) (ip_keys P1) (ip_cap P1) ++ Di1) ->
  rd_keep SEGS (mrestrict (w_H (ip_W P1)) (ip_mem P1)) m2
    (fun a => rd_blk (ip_D P1) a /\ ~ (ip_kids P1 + 56 * ip_n P1 <= a < ip_kids P1 + 56 * ip_n P1 + 56)) ->
  PRH_PjOrder.pf_oitemsR SEGS (mrestrict (w_H (ip_W P1)) (ip_mem P1)) (prh_lin (ip_Lam P1))
    (PRH_PjOrder.pj_foR SEGS (mrestrict (w_H (ip_W P1)) (ip_mem P1)) (prh_lin (ip_Lam P1)) nn)
    (ie_o E) (ip_kids P1) (ip_keys P1) (Z.to_nat (ip_n P1)) Di1 Facc1 ->
  pj_keyR SEGS (mrestrict (w_H (ip_W P1)) (ip_mem P1)) (prh_lin (ip_Lam P1)) (ie_o E)
    (ip_keys P1 + 8 * ip_n P1) Dk ->
  PRH_PjOrder.pf_oitemsR SEGS m2 (prh_lin Lam2) (PRH_PjOrder.pj_foR SEGS m2 (prh_lin Lam2) nn)
    (ie_o E) (ip_kids P1) (ip_keys P1) (Z.to_nat (ip_n P1)) Di1 Facc1 /\
  pj_keyR SEGS m2 (prh_lin Lam2) (ie_o E) (ip_keys P1 + 8 * ip_n P1) Dk.
Proof.
  intros E P1 m2 Lam2 Dk Di1 Facc1 nn Hnc Hn0 Hcf HNoD Hpw HLND HDL HLM HP1 HK HOI1 HKR.
  pose proof (vv_old_good E P1 Dk Di1 Hnc Hn0 Hcf HNoD Hpw HLND HDL HP1) as HG.
  split.
  - apply (PRH_PjOrder.pf_oitemsR_frame SEGS nn _ _ _ _ (ie_o E) (ip_kids P1) (ip_keys P1) (Z.to_nat (ip_n P1))
             Di1 Facc1 HOI1).
    + intros x k Hin. exact (HLM x k (PRH_PjOrder.pf_oitemsR_lblk SEGS _ _ nn _ _ _ _ _ _ HOI1 x k Hin)).
    + apply (vrd_agree_of_keep SEGS). eapply rd_keep_mono; [exact HK|].
      intros y Hy'. unfold PRH_PjOrder.pf_ofoot in Hy'. apply HG.
      destruct Hy' as [Hy | [(Hks & Hy) | Hy]];
        [left; lia | right; left; split; [exact Hks | lia] | right; right; apply Exists_exists; exact Hy].
  - apply (vv_keyR_keep _ _ (prh_lin (ip_Lam P1)) _ (ie_o E) _ Dk HKR).
    + intros x k Hx. exact (HLM x k Hx).
    + intros Ho. eapply rd_keep_mono; [exact HK|]. intros z Hz. apply HG. right. left. split; [exact Ho | lia].
Qed.

(* THE BATCH KIT'S LAYER AFTER A GRANTED VALUE: the members' caps one longer (the new member's caps are the callee's
   pj_ncapR) and the completed slots' order list one slot longer (the value's subtree, the callee's order list, then
   its key), at the memory after the count store; its requests are af, the value's fv, then the key's lk *)
Lemma vv_k1_snoc : forall E P1 P2 nm t D Dx Dk af lk fv,
  vrd_inode E P1 Dx -> vrd_incaps E P1 -> vrd_iforder E P1 Dk af ->
  pj_keyR SEGS (mrestrict (w_H (ip_W P1)) (ip_mem P1)) (prh_lin (ip_Lam P1)) (ie_o E)
    (ip_keys P1 + 8 * ip_n P1) Dk ->
  (cf_head = PresetReqAt.HEAD -> map (fun b => snd b + cf_head) Dk = lk) ->
  ip_n P1 < ip_cap P1 ->
  ip_n P2 = ip_n P1 + 1 -> ip_cap P2 = ip_cap P1 -> ip_kids P2 = ip_kids P1 -> ip_keys P2 = ip_keys P1 ->
  ip_acc P2 = (nm, t) :: ip_acc P1 -> ip_D P2 = ip_D P1 ++ D ->
  (forall a k, In (a, k) (ip_Lam P1) -> In (a, k) (ip_Lam P2)) ->
  rd_keep SEGS (mrestrict (w_H (ip_W P1)) (ip_mem P1)) (mrestrict (w_H (ip_W P2)) (ip_mem P2))
    (fun a => rd_blk (ip_D P1) a /\ ~ (ip_kids P1 + 56 * ip_n P1 <= a < ip_kids P1 + 56 * ip_n P1 + 56)) ->
  pj_ncapR SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (ip_kids P1 + 56 * ip_n P1) t ->
  (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat ->
     exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (prh_lin (ip_Lam P2)) n
       (ip_kids P1 + 56 * ip_n P1) D F /\ map (fun b => snd b + cf_head) F = fv) ->
  0 <= cf_head -> NoDup (ip_D P1) ->
  (forall a k a' k', In (a, k) (ip_D P1) -> In (a', k') (ip_D P1) -> a <> a' ->
     a + k <= a' - cf_head \/ a' + k' <= a - cf_head) ->
  NoDup (map fst (ip_Lam P1)) ->
  (forall a k, In (a, k) (ip_D P1) -> In (a, k) (ip_Lam P1)) ->
  vrd_incaps E P2 /\ vrd_iforder E P2 [] (af ++ fv ++ lk).
Proof.
  intros E P1 P2 nm t D Dx Dk af lk fv HND HNC HFO HKR Hlk Hnc Hn2 Hcap2 Hkids2 Hkeys2 Hacc2 HD2 HLM HK
    HSC HSFO Hcf HNoD Hpw HLND HDL.
  pose proof HND as (_ & Hn01 & _ & _ & _ & Hlen1 & (Di & HPerm & HTree) & _).
  assert (Hlr : Z.of_nat (length (rev (ip_acc P1))) = ip_n P1) by (rewrite length_rev; exact Hlen1).
  split.
  - unfold vrd_incaps in HNC |- *. rewrite Hacc2, Hkids2. cbn [rev].
    apply (proj2 (vv_kids_snoc _ _ _ _ _)). split.
    + assert (HK' : rd_keep SEGS (mrestrict (w_H (ip_W P1)) (ip_mem P1)) (mrestrict (w_H (ip_W P2)) (ip_mem P2))
                      (fun z => ip_kids P1 <= z < ip_kids P1 + 56 * Z.of_nat (length (rev (ip_acc P1))) \/
                                rd_blk Di z)).
      { eapply rd_keep_mono; [exact HK|]. intros z Hz.
        apply (vv_old_good E P1 Dx Di Hnc ltac:(lia) Hcf HNoD Hpw HLND HDL HPerm z).
        destruct Hz as [Hz | Hz]; [left; lia | right; right; exact Hz]. }
      revert HTree. destruct (ie_o E); intros HTree.
      * exact (vrd_ncaps_keep_mems SEGS (rev (ip_acc P1)) _ _ _ (ip_kids P1) (ip_keys P1) Di HTree HNC HK').
      * exact (vrd_ncaps_keep_items SEGS (rev (ip_acc P1)) _ _ _ (ip_kids P1) Di HTree HNC HK').
    + cbv beta. cbn [snd]. rewrite Hlr. exact HSC.
  - intros Hh nn Hnn. rewrite Hacc2 in Hnn. apply Forall_cons_iff in Hnn as (Hdt & Hdacc). cbn [snd] in Hdt.
    destruct (HFO Hh nn Hdacc) as (Di1 & Facc1 & HP1 & HOI1 & Hm1).
    destruct (HSFO Hh nn Hdt) as (Ft & HFt & HmFt).
    destruct (vv_oitems_frame E P1 (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (ip_Lam P2) Dk Di1 Facc1 nn
                Hnc ltac:(lia) Hcf HNoD Hpw HLND HDL HLM HP1 HK HOI1 HKR) as (HOI2 & HKR2).
    exists (Di1 ++ Dk ++ D), (Facc1 ++ Ft ++ Dk).
    rewrite HD2, Hkids2, Hkeys2, Hcap2, Hn2.
    split.
    + cbn [app]. eapply Permutation_trans; [apply Permutation_app_tail; exact HP1|].
      rewrite <- !app_assoc. eapply Permutation_trans; [apply Permutation_app_comm|].
      rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_head.
      apply Permutation_app_comm.
    + split.
      * rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat. rewrite Nat.add_1_r.
        apply (vv_pfo_snoc _ _ _ (ie_o E) (ip_kids P1) (ip_keys P1) (Z.to_nat (ip_n P1)) Di1 Facc1 Dk D Ft HOI2).
        -- rewrite Z2Nat.id by lia. exact HKR2.
        -- rewrite Z2Nat.id by lia. exact HFt.
      * rewrite !map_app, Hm1, HmFt, (Hlk Hh). reflexivity.
Qed.

(* THE PARTIAL FREE ORDER AT A REFUSED VALUE (the post's None arm): the count store made the refused slot the
   node's n + 1-st, so the node's order list is the completed slots', then the slot's (the callee's partial list,
   then its key), then the arrays; its requests are af, the child's fv, the key's lk, then arrz *)
Lemma vv_fo_exit : forall E P1 P2 D Dx Dk af lk fv,
  vrd_inode E P1 Dx -> vrd_iforder E P1 Dk af ->
  pj_keyR SEGS (mrestrict (w_H (ip_W P1)) (ip_mem P1)) (prh_lin (ip_Lam P1)) (ie_o E)
    (ip_keys P1 + 8 * ip_n P1) Dk ->
  (cf_head = PresetReqAt.HEAD -> map (fun b => snd b + cf_head) Dk = lk) ->
  ip_n P1 < ip_cap P1 -> (ie_d E < PjGrammar.MAXD)%nat ->
  ip_D P2 = ip_D P1 ++ D ->
  (forall a k, In (a, k) (ip_Lam P1) -> In (a, k) (ip_Lam P2)) ->
  Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - S (ie_d E))%nat) (ip_acc P1) ->
  pj_hdrR SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (ie_v E) (if ie_o E then 6 else 5) 0 0
    (ip_kids P1) (ip_keys P1) (ip_n P1 + 1) (ip_cap P1) ->
  rd_keep SEGS (mrestrict (w_H (ip_W P1)) (ip_mem P1)) (mrestrict (w_H (ip_W P2)) (ip_mem P2))
    (fun a => rd_blk (ip_D P1) a /\ ~ (ip_kids P1 + 56 * ip_n P1 <= a < ip_kids P1 + 56 * ip_n P1 + 56)) ->
  (cf_head = PresetReqAt.HEAD -> forall n, (PjGrammar.MAXD - S (ie_d E) <= n)%nat ->
     exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (prh_lin (ip_Lam P2)) n
       (ip_kids P1 + 56 * ip_n P1) D F /\ map (fun b => snd b + cf_head) F = fv) ->
  NoDup (ip_D P2) -> pj_apartR (ip_D P2) (ie_v E) ->
  0 <= cf_head -> NoDup (ip_D P1) ->
  (forall a k a' k', In (a, k) (ip_D P1) -> In (a', k') (ip_D P1) -> a <> a' ->
     a + k <= a' - cf_head \/ a' + k' <= a - cf_head) ->
  NoDup (map fst (ip_Lam P1)) ->
  (forall a k, In (a, k) (ip_D P1) -> In (a, k) (ip_Lam P1)) ->
  cf_head = PresetReqAt.HEAD -> forall n, (PjGrammar.MAXD - ie_d E <= n)%nat ->
    exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (prh_lin (ip_Lam P2)) n (ie_v E)
      (ip_D P2) F /\
      map (fun b => snd b + cf_head) F = (af ++ fv ++ lk) ++ PresetReqAt.arrz (ie_o E) (Z.to_nat (ip_cap P1)).
Proof.
  intros E P1 P2 D Dx Dk af lk fv HND HFO HKR Hlk Hnc Hd HD2 HLM Hdep Hhdr2 HK HSFO HNoD2 Hap2 Hcf HNoD Hpw HLND
    HDL Hh n Hn.
  pose proof HND as (_ & Hn01 & _ & _ & Hlin1 & _ & _ & _ & _ & _ & _ & Hkz1).
  assert (Hcpos : 0 < ip_cap P1) by lia.
  destruct n as [|nn]; [lia|].
  assert (Hdacc : Forall (fun mm => (PjTree.depth (snd mm) <= nn)%nat) (ip_acc P1))
    by exact (vi_dep_le (ip_acc P1) (PjGrammar.MAXD - S (ie_d E)) nn ltac:(lia) Hdep).
  destruct (HFO Hh nn Hdacc) as (Di1 & Facc1 & HP1 & HOI1 & Hm1).
  destruct (HSFO Hh nn ltac:(lia)) as (Fc & HFc & HmFc).
  destruct (vv_oitems_frame E P1 (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (ip_Lam P2) Dk Di1 Facc1 nn
              Hnc ltac:(lia) Hcf HNoD Hpw HLND HDL HLM HP1 HK HOI1 HKR) as (HOI2 & HKR2).
  assert (HOI3 : PRH_PjOrder.pf_oitemsR SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (prh_lin (ip_Lam P2))
                   (PRH_PjOrder.pj_foR SEGS (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (prh_lin (ip_Lam P2)) nn)
                   (ie_o E) (ip_kids P1) (ip_keys P1) (S (Z.to_nat (ip_n P1))) (Di1 ++ Dk ++ D)
                   (Facc1 ++ Fc ++ Dk)).
  { apply (vv_pfo_snoc _ _ _ (ie_o E) (ip_kids P1) (ip_keys P1) (Z.to_nat (ip_n P1)) Di1 Facc1 Dk D Fc HOI2).
    - rewrite Z2Nat.id by lia. exact HKR2.
    - rewrite Z2Nat.id by lia. exact HFc. }
  assert (Ec : (ip_cap P1 =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (EK : kids_blkR (ip_kids P1) (ip_cap P1) = [(ip_kids P1, 56 * ip_cap P1)])
    by (unfold kids_blkR; rewrite Ec; reflexivity).
  assert (EY : keys_blkR (if ie_o E then 6 else 5) (ip_keys P1) (ip_cap P1) =
               (if ie_o E then [(ip_keys P1, 8 * ip_cap P1)] else []))
    by (unfold keys_blkR; rewrite Ec; destruct (ie_o E); reflexivity).
  pose proof (vrd_arrz_blk (ie_o E) (ip_kids P1) (ip_keys P1) (ip_cap P1) ltac:(lia) Hh) as HAZ.
  rewrite EK, EY in HP1, HAZ.
  assert (Hcnt : Z.to_nat (ip_n P1 + 1) = S (Z.to_nat (ip_n P1))) by lia.
  exists ((Facc1 ++ Fc ++ Dk) ++ [(ip_kids P1, 56 * ip_cap P1)] ++
          (if ie_o E then [(ip_keys P1, 8 * ip_cap P1)] else [])).
  split.
  2: { rewrite map_app, HAZ, !map_app, Hm1, HmFc, (Hlk Hh). rewrite <- !app_assoc. reflexivity. }
  destruct (ie_o E) eqn:Ho.
  - apply (vi_part_fo _ _ (ie_v E) 6 (ip_kids P1) (ip_keys P1) (ip_n P1 + 1) (ip_cap P1) true
             [(ip_kids P1, 56 * ip_cap P1)] [(ip_keys P1, 8 * ip_cap P1)] (Di1 ++ Dk ++ D) (ip_D P2)
             (Facc1 ++ Fc ++ Dk) nn HNoD2 Hap2 Hhdr2).
    + right. exists (56 * ip_cap P1). split; [exact (HLM _ _ (proj1 (Hlin1 Hcpos))) | split; [lia | reflexivity]].
    + right. split; [reflexivity|]. exists (8 * ip_cap P1).
      split; [exact (HLM _ _ (proj2 (Hlin1 Hcpos) eq_refl)) | split; [lia | reflexivity]].
    + rewrite HD2. cbn [app] in HP1 |- *.
      eapply Permutation_trans; [apply Permutation_app_tail; exact HP1|].
      rewrite <- !app_assoc. eapply Permutation_trans; [apply Permutation_app_comm|].
      cbn [app]. apply perm_skip. apply perm_skip. rewrite <- app_assoc. apply Permutation_app_head.
      apply Permutation_app_comm.
    + rewrite Hcnt. exact HOI3.
  - apply (vi_part_fo _ _ (ie_v E) 5 (ip_kids P1) (ip_keys P1) (ip_n P1 + 1) (ip_cap P1) false
             [(ip_kids P1, 56 * ip_cap P1)] [] (Di1 ++ Dk ++ D) (ip_D P2) (Facc1 ++ Fc ++ Dk) nn HNoD2 Hap2 Hhdr2).
    + right. exists (56 * ip_cap P1). split; [exact (HLM _ _ (proj1 (Hlin1 Hcpos))) | split; [lia | reflexivity]].
    + left. split; [exact (Hkz1 eq_refl) | split; reflexivity].
    + rewrite HD2. cbn [app] in HP1 |- *.
      eapply Permutation_trans; [apply Permutation_app_tail; exact HP1|].
      rewrite <- !app_assoc. eapply Permutation_trans; [apply Permutation_app_comm|].
      cbn [app]. apply perm_skip. rewrite <- app_assoc. apply Permutation_app_head.
      apply Permutation_app_comm.
    + rewrite Hcnt. exact HOI3.
Qed.

(* an order list across a memory that keeps its node's 56 bytes and its blocks' bytes (PRH_PjOrder.pj_foR_frame) *)
Lemma vv_fo_keep : forall m m' lblk n p D F,
  PRH_PjOrder.pj_foR SEGS m lblk n p D F ->
  rd_keep SEGS m m' (fun a => p <= a < p + 56 \/ rd_blk D a) ->
  PRH_PjOrder.pj_foR SEGS m' lblk n p D F.
Proof.
  intros m m' lblk n p D F HF HK.
  exact (PRH_PjOrder.pj_foR_frame SEGS n m m' lblk lblk p D F HF (PRH_PjOrder.pj_foR_lblk SEGS m lblk n p D F HF)
           (vrd_agree_of_keep SEGS m m' _ (rd_keep_foot SEGS m m' p D HK))).
Qed.

(* ---- IvalA: the count store's run (rows 232..237) and the transports across it ---- *)

(* the run over the writable-count seat writes only the count word [v + 40, v + 48) *)
Lemma vv_frame_node : forall E' cs0 cs (m m' : word -> option byte) v,
  frame_of E' [YP09.mkRegion (Some 2%nat) 0 144 0 0 cs0; YP09.mkRegion (Some 20%nat) 0 56 40 48 cs] m m' ->
  bv_unsigned (ew E' 20) = v -> forall x : word, ~ (v + 40 <= bv_unsigned x < v + 48) -> m' x = m x.
Proof.
  intros E' cs0 cs m m' v HF Hv x Hx. apply HF. intros (r & Hin & Hr).
  destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
  rewrite Hv in Hr. lia.
Qed.

Lemma vv_awr_node : forall E' cs0 cs STK sp0 FP bl0 blc S ly own v,
  bv_unsigned (ew E' 20) = v ->
  (forall a, v + 40 <= a < v + 48 -> awr_byte STK sp0 FP bl0 blc ly own a \/ wr_fp_frame FP S ly a) ->
  awr_ok_fr E' [YP09.mkRegion (Some 2%nat) 0 144 0 0 cs0; YP09.mkRegion (Some 20%nat) 0 56 40 48 cs]
    STK sp0 FP bl0 blc S ly own.
Proof.
  intros E' cs0 cs STK sp0 FP bl0 blc S ly own v Hv HA a (r & Hin & Ha).
  destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [lia|].
  rewrite Hv in Ha. apply HA. lia.
Qed.

(* a region of a symbolic state holds in the machine memory (IvalR_C.v's vv_region_nth) *)
Lemma vv_region_nth : forall (fxP : YK11.FPState) E ss ms i r,
  st_ok_pi (fx := fxP) SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof.
  intros fxP E ss ms i r HS Hi. pose proof (st_ok_mem_ok SEGS E _ ms HS) as HM.
  destruct HM as (_ & Hrs & _). assert (Hin : In r (ss_mem ss)) by exact (nth_error_In _ _ Hi).
  destruct ss. exact (proj1 (Forall_forall _ _) Hrs r Hin).
Qed.

(* the count word n + 1 and the window's writability, read off the node region after the run *)
Lemma vv_node_facts : forall E' (m : word -> option byte) cs v n,
  region_ok SEGS E' m (YP09.mkRegion (Some 20%nat) 0 56 40 48 (YP09.mkChunk 40 (CVal 8 (SOff 46 1)) :: cs)) ->
  bv_unsigned (ew E' 20) = v -> ew E' 46 = w64 n -> 0 <= n -> n + 1 < 2 ^ 64 ->
  val_mem SEGS m (v + 40) 8 (n + 1) /\ (forall a, v + 40 <= a < v + 48 -> writable_at SEGS m a).
Proof.
  intros E' m cs v n (_ & _ & Hw & Hcs) Hv Hn Hn0 Hn1.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in Hw, Hcs. rewrite Hv in Hw, Hcs.
  split.
  - pose proof (proj1 (Forall_forall _ _) Hcs _ (or_introl eq_refl)) as Hck.
    apply (val_of_chunk_ok SEGS E' m v 40 8 (SOff 46 1) (n + 1) Hck); [| cbn; lia | cbn; lia].
    cbn [sv_denot]. rewrite Hn. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - intros a Ha. replace a with (v + (a - v)) by lia. apply Hw. lia.
Qed.

(* shadow bytes are not app bytes: a store into an app window keeps every shadow byte below 2 ^ 47 *)
Lemma vv_keep_ra_node : forall (H : word -> bool) (m m' : word -> option byte) lo hi a n,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mrestrict H m' x = mrestrict H m x) ->
  amem_range lo (hi - lo) -> 0 <= a -> a + n <= 2 ^ 47 ->
  range_addressable (aview SEGS H m) SHADOW_OFF a n -> range_addressable (aview SEGS H m') SHADOW_OFF a n.
Proof.
  intros H m m' lo hi a n HK Hlo Ha Han HR x Hx. destruct (HR x Hx) as (s & Hs & Hok).
  exists s. split; [|exact Hok]. unfold shadow_of_addr in *.
  assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (vk_keep_av H m m' lo hi _ HK); [exact Hs | unfold SHADOW_OFF; lia |].
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.

Lemma vv_keep_hull_node : forall (H : word -> bool) (m m' : word -> option byte) lo hi a n,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mrestrict H m' x = mrestrict H m x) ->
  amem_range lo (hi - lo) -> 0 <= a -> a + n <= 2 ^ 47 - 128 -> 0 < n ->
  shadow_hull_vis (aview SEGS H m) a n -> shadow_hull_vis (aview SEGS H m') a n.
Proof.
  intros H m m' lo hi a n HK Hlo Ha Han Hn HV s Hs. unfold shadow_addr in Hs.
  assert (H1 : 0 <= (a + n - 1) / 8 < 2 ^ 44 - 16) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (H2 : 0 <= a / 8) by (apply Z.div_pos; lia).
  assert (H3 : (SHADOW_OFF + a / 8) / 8 * 8 >= SHADOW_OFF).
  { change SHADOW_OFF with (268431360 * 8). rewrite Z.div_add_l by lia.
    pose proof (Z.div_pos (a / 8) 8 H2 ltac:(lia)). lia. }
  assert (H4 : (SHADOW_OFF + (a + n - 1) / 8) / 8 * 8 <= SHADOW_OFF + (a + n - 1) / 8)
    by (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
  rewrite (vk_keep_av H m m' lo hi _ HK); [apply HV; exact Hs | unfold SHADOW_OFF in *; lia |].
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.

(* the node header after the count store *)
Lemma vv_hdr_store : forall (m m' : word -> option byte) p ty num str kids keys n cap n',
  pj_hdrR SEGS m p ty num str kids keys n cap ->
  rd_keep SEGS m m' (fun x => p <= x < p + 56 /\ ~ (p + 40 <= x < p + 48)) ->
  val_mem SEGS m' (p + 40) 8 n' -> 0 <= n' < 2 ^ 64 ->
  (forall a, p + 40 <= a < p + 48 -> writable_at SEGS m' a) ->
  pj_hdrR SEGS m' p ty num str kids keys n' cap.
Proof.
  intros m m' p ty num str kids keys n cap n' ((Hal & Hrw) & Hty & Hnum & Hstr & Hk & Hy & _ & Hc) HK Hv Hn' Hw.
  unfold pj_hdrR. split; [split; [exact Hal|]|].
  { intros x Hx. destruct (Z_lt_le_dec x (p + 40)) as [H1|H1]; [|destruct (Z_lt_le_dec x (p + 48)) as [H2|H2]].
    - apply (proj2 HK); [lia | apply Hrw; lia].
    - apply Hw; lia.
    - apply (proj2 HK); [lia | apply Hrw; lia]. }
  split; [eapply rd_u32_keep; [exact Hty | eapply rd_keep_mono; [exact HK | intros x Hx; cbv beta in *; lia]]|].
  split; [eapply rd_u64_keep; [exact Hnum | eapply rd_keep_mono; [exact HK | intros x Hx; cbv beta in *; lia]]|].
  split; [eapply rd_u64_keep; [exact Hstr | eapply rd_keep_mono; [exact HK | intros x Hx; cbv beta in *; lia]]|].
  split; [eapply rd_u64_keep; [exact Hk | eapply rd_keep_mono; [exact HK | intros x Hx; cbv beta in *; lia]]|].
  split; [eapply rd_u64_keep; [exact Hy | eapply rd_keep_mono; [exact HK | intros x Hx; cbv beta in *; lia]]|].
  split; [split; [exact Hn' | exact Hv]|].
  eapply rd_u64_keep; [exact Hc | eapply rd_keep_mono; [exact HK | intros x Hx; cbv beta in *; lia]].
Qed.

Lemma vv_rd_keep_trans : forall m1 m2 m3 (Pz : Z -> Prop),
  rd_keep SEGS m1 m2 Pz -> rd_keep SEGS m2 m3 Pz -> rd_keep SEGS m1 m3 Pz.
Proof.
  intros m1 m2 m3 Pz [A1 B1] [A2 B2]. split; intros a Ha.
  - rewrite (A2 a Ha). exact (A1 a Ha).
  - intros Hw. exact (B2 a Ha (B1 a Ha Hw)).
Qed.

Lemma vv_in_after_keep : forall (m m' : word -> option byte) q text len lo hi,
  pj_in_afterR SEGS m q text len lo hi -> rd_keep SEGS m m' (fun x => q <= x < q + 24) ->
  pj_in_afterR SEGS m' q text len lo hi.
Proof.
  intros m m' q text len lo hi (p' & d' & Hp & Hd & V1 & V2 & V3 & Hrw) HK.
  exists p', d'. split; [exact Hp|]. split; [exact Hd|].
  split; [eapply val_mem_keep; [exact V1 | eapply rd_keep_mono; [exact HK | intros x Hx; cbv beta in *; cbn in Hx; lia]]|].
  split; [eapply val_mem_keep; [exact V2 | eapply rd_keep_mono; [exact HK | intros x Hx; cbv beta in *; cbn in Hx; lia]]|].
  split; [eapply val_mem_keep; [exact V3 | eapply rd_keep_mono; [exact HK | intros x Hx; cbv beta in *; cbn in Hx; lia]]|].
  eapply rd_rw_keep; [exact Hrw | exact HK].
Qed.

(* the cursor past the value: the rest there is the value's rest *)
Lemma vv_rest_after : forall (tb : list Z) text len p k,
  Z.of_nat (length tb) = len -> text <= p <= text + len ->
  rest_atR tb text (text + len - Z.of_nat (length (skipn k (rest_atR tb text p)))) = skipn k (rest_atR tb text p).
Proof.
  intros tb text len p k Hl Hp. unfold rest_atR.
  rewrite vv_skipn_skipn, length_skipn.
  destruct (Nat.le_gt_cases (Z.to_nat (p - text) + k) (length tb)) as [Hj|Hj].
  - f_equal. rewrite Nat2Z.inj_sub by exact Hj. lia.
  - assert (Hs : skipn (Z.to_nat (p - text) + k)%nat tb = []) by (apply skipn_all2; lia).
    rewrite Hs. apply skipn_all2. lia.
Qed.

(* the blocks a position owns, from the ledger at the position and the composed ledger permutation (IvalR_sep.v's
   vv_D_apart, its proof with vrd_icur / vrd_imodel replaced by the two conjuncts it reads) *)
Lemma vv_D_apart_led : forall CTX CTX0 CW E P,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_ijrn B ARx SK E P ->
  prh_ledger B (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P)
    (ip_ran P) (ie_most E) (ie_own E) ->
  Permutation (ip_Lam P) (ip_D P ++ ie_Lam E) ->
  NoDup (ip_D P) /\
  (forall a k, In (a, k) (ip_D P) ->
     0 <= k /\ In (a - cf_head, k + cf_head) (ablocks B (ip_ly P) (ip_S P)) /\
     4096 <= a - cf_head /\ a + k <= alloc_ceiling /\
     (forall x, a - cf_head <= x < a + k ->
        ~ in_img SEGS x /\ ~ (ie_v E <= x < ie_v E + 56) /\ ~ (ie_text E <= x < ie_text E + ie_len E))) /\
  (forall a k a' k', In (a, k) (ip_D P) -> In (a', k') (ip_D P) -> a <> a' ->
     a + k <= a' - cf_head \/ a' + k' <= a - cf_head) /\
  pj_apartR (ip_D P) (ie_v E).
Proof.
  intros CTX CTX0 CW E P HEN HJN HLEDP HPerm.
  pose proof cf_head_nonneg as Hcf0.
  destruct HEN as ((HAFN & _) & _ & _ & _ & HRD & _).
  pose proof HAFN as (HARE & _).
  pose proof HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhome & _ & Hnode & _ & _ & Hvwin & HLEDE & _).
  pose proof Hnode as (_ & _ & _ & _ & Hvat & _).
  destruct HJN as (HJ & _ & _ & _ & _ & HBM & _).
  pose proof HJ as (HARP & Hly & _ & _ & _ & Hfrs & _).
  destruct HBM as (HnotE & HabP & _ & _).
  destruct HLEDP as (_ & HNDP & HFLP & _).
  destruct HLEDE as (_ & _ & HFLE & _).
  destruct (alx_layout SEGS B ARx LAWS _ _ _ _ _ _ _ HARE Hly) as (_ & Hfa & _).
  assert (HhbP : forall a k, In (a, k) (ip_D P) ->
    0 <= k /\ In (a - cf_head, k + cf_head) (ablocks B (ip_ly P) (ip_S P))).
  { intros a k Hin.
    assert (HinL : In (a, k) (ip_Lam P))
      by (apply (Permutation_in _ (Permutation_sym HPerm)); apply in_or_app; left; exact Hin).
    destruct (proj1 (Forall_forall _ _) HFLP (a, k) HinL) as (Hk & Hab & _). cbn [fst snd] in Hk, Hab.
    split; [exact Hk | exact Hab]. }
  assert (HabE2P : forall b, In b (ablocks B (ie_ly E) (ie_S E)) -> In b (ablocks B (ip_ly P) (ip_S P))).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HabP)). apply in_or_app. right. exact Hb. }
  assert (HsepE : forall a k b n, In (a, k) (ip_D P) -> In (b, n) (ablocks B (ie_ly E) (ie_S E)) ->
     a + k <= b \/ b + n <= a - cf_head).
  { intros a k b n Hin Hb. destruct (HhbP a k Hin) as (Hk & Hab).
    assert (Hd : (a - cf_head, k + cf_head) <> (b, n)).
    { intros Eq. apply (HnotE a k Hin). rewrite Eq. exact Hb. }
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HARP Hab (HabE2P _ Hb) Hd) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz.
    pose proof (vv_req_ge (k + cf_head)). pose proof (vv_req_ge n). lia. }
  assert (Hone : forall a k, In (a, k) (ip_D P) ->
     0 <= k /\ In (a - cf_head, k + cf_head) (ablocks B (ip_ly P) (ip_S P)) /\
     4096 <= a - cf_head /\ a + k <= alloc_ceiling /\
     (forall x, a - cf_head <= x < a + k ->
        ~ in_img SEGS x /\ ~ (ie_v E <= x < ie_v E + 56) /\ ~ (ie_text E <= x < ie_text E + ie_len E))).
  { intros a k Hin. destruct (HhbP a k Hin) as (Hk & Hab).
    destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HARP Hab) as (_ & H4k & Hc & _).
    pose proof (vv_req_ge (k + cf_head)) as Hr.
    split; [exact Hk|]. split; [exact Hab|]. split; [exact H4k|]. split; [lia|].
    intros x Hx. split; [|split].
    - apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ x HARP Hab). lia.
    - intros Hv.
      destruct Hvat as [(a1 & k1 & Hin1 & Hlo & Hhi) | [(b & m & Hinb & _ & Hlo & Hhi) |
                        [(cid & pos & Hf & Hlo & Hhi) | Hww]]].
      + destruct (proj1 (Forall_forall _ _) HFLE (a1, k1) Hin1) as (Hk1 & Hab1 & _). cbn [fst snd] in Hk1, Hab1.
        destruct (HsepE a k _ _ Hin Hab1); lia.
      + destruct (HsepE a k _ _ Hin Hinb); lia.
      + assert (Hin' : In (cid, pos) (frames (ip_S P))) by (rewrite Hfrs; exact Hf).
        pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HARP Hab Hin') as Hz.
        unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite Hfa in Hz. lia.
      + lia.
    - intros Ht.
      destruct Hhome as [[(b & m & Hinb & Hlo & Hhi) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] |
                         (b & m & Hinb & _ & Hlo & Hhi)].
      + destruct (proj1 (Forall_forall _ _) HFLE (b, m) Hinb) as (Hm & Habm & _). cbn [fst snd] in Hm, Habm.
        destruct (HsepE a k _ _ Hin Habm); lia.
      + destruct (Hro x Ht) as (Hr0 & _).
        apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ x HARP Hab); [lia|].
        destruct Hr0 as [(s & Hs & _ & Hsl) | Hrel].
        * exists s. split; [exact Hs | exact Hsl].
        * exact (@pa_relro_img _ _ PI_prog_A x Hrel).
      + destruct (Hro x Ht) as (Hr0 & _).
        apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ x HARP Hab); [lia|].
        destruct Hr0 as [(s & Hs & _ & Hsl) | Hrel].
        * exists s. split; [exact Hs | exact Hsl].
        * exact (@pa_relro_img _ _ PI_prog_A x Hrel).
      + destruct (HsepE a k _ _ Hin Hinb); lia. }
  split.
  { assert (H0 : Permutation (map fst (ip_Lam P)) (map fst (ip_D P ++ ie_Lam E)))
      by (apply Permutation_map; exact HPerm).
    assert (HN : List.NoDup (map fst (ip_Lam P))) by (first [exact HNDP | apply NoDup_ListNoDup; exact HNDP]).
    assert (H1 : List.NoDup (map fst (ip_D P ++ ie_Lam E))) by exact (Permutation_NoDup H0 HN).
    rewrite map_app in H1. apply List.NoDup_app_remove_r in H1. apply List.NoDup_map_inv in H1.
    first [exact H1 | apply NoDup_ListNoDup; exact H1]. }
  split; [exact Hone|].
  split.
  { intros a k a' k' Hin Hin' Hne.
    destruct (HhbP a k Hin) as (Hk & Hab). destruct (HhbP a' k' Hin') as (Hk' & Hab').
    assert (Hd : (a - cf_head, k + cf_head) <> (a' - cf_head, k' + cf_head)) by (intros Eq; injection Eq; lia).
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HARP Hab Hab' Hd) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz.
    pose proof (vv_req_ge (k + cf_head)). pose proof (vv_req_ge (k' + cf_head)). lia. }
  intros [a k] x Hin Hh Hv. unfold pj_holdsR in Hh. cbn [fst snd] in Hh.
  destruct (Hone a k Hin) as (_ & _ & _ & _ & Hx).
  destruct (Hx x ltac:(lia)) as (_ & Hnv & _). exact (Hnv Hv).
Qed.


(* ---- after parse_value returned (row 232, slot 6164) ---- *)
Definition A_IPVRET_SLOT : nat := 6164%nat.

(* fpre's fourth conjunct at row 231's `jal parse_value` (raZ regs < YM05.alloc_ceiling): the return pc, listing slot
   A_IPVRET_SLOT, is below the run's allocation ceiling - PRW_StepKit's ONE copy (pa_slot_lt_ceil_b) in a CLOSED goal
   with the listing instance named (VrdIStep.vi_grow_ret_slot_ceil's form; inside the call proof its vm_compute ran
   away: the S3 walk, 2026-10-29) *)
Lemma vv_ret_slot_ceil : bv_unsigned (Z_to_bv 64 (BASE + 24656)) < YM05.alloc_ceiling.
Proof.
  pose proof (PRW_StepKit.pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PAI) 24656 ltac:(lia) ltac:(vm_compute; reflexivity)) as H.
  rewrite unsigned_lit_small; [exact H|]. rewrite vi_base. unfold A_prog_base. lia.
Qed.

(* the post of Part B: the separator state with the count n + 1 (the count store sets v->n := n + 1), or an exit,
   and the memory invariant at the reached state *)
Definition vv_postB (E : vrd_ient) (n : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => ((exists P', W2 = ip_W P' /\ c2 = vrd_cfg A_ISEP_SLOT P' /\ ip_n P' = n + 1 /\ vv_sep E P') \/
                (exists P' res, W2 = ip_W P' /\ c2 = vrd_cfg A_IEPI_SLOT P' /\ vrd_iexit_a B ARx SK E P' res)) /\
               Pm (ms_mem (cfg_ms c2)).

(* Pr carries the machine state the callee returned (its world, layout, allocator state, registers, memory, model,
   journal count and float state) and the counters, blocks, trace and ok list composed through the call; its count,
   cursor and model continuation are still P's. Everything here is what vv_partB derives right after the call. *)
Lemma vv_after_call : forall E P nm Pr ok res tr okr0 D,
  vrd_ient_ok B ARx CTXv CTX0v CWv E -> vv_set E P nm ->
  ip_n Pr = ip_n P -> ip_cap Pr = ip_cap P -> ip_kids Pr = ip_kids P -> ip_keys Pr = ip_keys P ->
  ip_acc Pr = ip_acc P -> ip_f Pr = ip_f P -> ip_cont Pr = ip_cont P -> ip_p Pr = ip_p P ->
  ip_ok Pr = ip_ok P ++ ok -> ip_tr Pr = ip_tr P ++ tr -> ip_D Pr = ip_D P ++ D ->
  vrd_iframe E Pr -> vrd_iregs B E Pr -> vrd_ijrn B ARx SK E Pr ->
  pj_hdrR SEGS (mrestrict (w_H (ip_W Pr)) (ip_mem Pr)) (ie_v E) (if ie_o E then 6 else 5) 0 0
    (ip_kids P) (ip_keys P) (ip_n P) (ip_cap P) ->
  rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W Pr)) (ip_mem Pr))
    (fun a => ~ inFP (rd_fp (ie_q E) (ip_kids P + 56 * ip_n P)) a /\
              (ie_v E <= a < ie_v E + 56 \/ rd_blk (ip_D P) a)) ->
  (* the callee's post, verbatim from tparse_value_specX (S d) (the kit's cut, PRH_FnParse.v blob f0d92dcec7e9, :313-384)
     at S := ip_S P, S' := ip_S Pr, in the text's order: the ledger, room_live_cf, the hull use, the live requests,
     the POSITION TRANSFER, the OUTCOME, the OUTCOME OF AN INJECTED READING, the ledger move over parse_value's own
     granted trace, the blocks move, and the result's arms with the cut's free order (first after getr, both arms) and
     pj_ncapR (Some arm, after pj_nodeR) *)
  PjGrammar.jr_value prh_jr_strtod (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) ok = (res, tr, okr0) ->
  prh_ledger B (ip_ly Pr) (ip_S Pr) (ip_Hp Pr) (ip_W Pr) (ip_mem Pr)
    (ip_Lam Pr) (ip_peak Pr) (ip_cnt Pr) (ip_fail Pr) (ip_ran Pr) (ie_most E) (ie_own E) ->
  room_live_cf (ip_S Pr) ->
  PresetHullBudget.hull_used (ip_S P) (ip_S Pr)
    (PresetReqAt.rd_hevs (prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P)))) ->
  vc_live (ip_S P) (ip_S Pr) tr ->
  vc_xfer (ip_S P) (ip_S Pr) tr ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (ip_S P) ->
     PRH_Base.prh_run_at sm x os i
       (PresetReqAt.rd_hevs (prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P)))) ->
     PRH_Base.prh_cons_from sm x os i
       (length (PresetReqAt.rd_hevs (prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P))))) ->
     (ip_fail P < ip_cnt P \/
      ip_cnt P + Z.of_nat (PjGrammar.calls (prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P))))
        <= ip_fail P) ->
     ip_ran Pr = ip_ran P /\
     fst (PjGrammar.jr_value ReaderRes.jr_strtod (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) []) =
       (res, tr) /\
     exists hist', PresetRoomPos.iface_room_pos sm x os
       (i + length (PresetReqAt.rd_hevs (prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P)))))%nat
       H0 hist' (ip_S Pr)) ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (ip_S P) ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_value ReaderRes.jr_strtod (S (ie_d E))
       (rest_atR (ie_tb E) (ie_text E) (ip_p P)) (PresetReqAt.okk (Z.to_nat (ip_fail P - ip_cnt P))))))) ->
     PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs (snd (fst (PjGrammar.jr_value ReaderRes.jr_strtod
       (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) (PresetReqAt.okk (Z.to_nat (ip_fail P - ip_cnt P)))))))) ->
     ip_cnt P <= ip_fail P <
       ip_cnt P + Z.of_nat (PjGrammar.calls (prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P)))) ->
     PRH_Base.prh_granted ok (ip_cnt P) (ip_fail P) (PjGrammar.calls tr)) ->
  rd_ledger_move (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P) (ie_most E) ok
    (prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P))) tr D
    (ip_Lam Pr) (ip_peak Pr) (ip_cnt Pr) (ip_fail Pr) (ip_ran Pr) ->
  rd_blocks_move B (ip_ly P) (ip_S P) (ip_ly Pr) (ip_S Pr) D tr (rest_atR (ie_tb E) (ie_text E) (ip_p P))
    (S (ie_d E)) ->
  blocks_bytes (ip_S Pr) <= blocks_bytes (ip_S P) + prh_held tr ->
  Ledger.lsum D = PjGrammar.held tr ->
  match res with
  | Some (t, r) =>
      getr (ip_regs Pr) 10 = w64 0 /\
      (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat ->
         exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H (ip_W Pr)) (ip_mem Pr)) (prh_lin (ip_Lam Pr)) n
           (ip_kids P + 56 * ip_n P) D F /\
           map (fun b => snd b + cf_head) F = prhPv_frees (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) ok) /\
      pj_in_okR SEGS (mrestrict (w_H (ip_W Pr)) (ip_mem Pr)) (ie_q E) (ie_text E) (ie_len E)
        (ie_text E + ie_len E - Z.of_nat (length r)) (Z.of_nat (S (ie_d E))) (ie_tb E) /\
      pj_nodeR SEGS (mrestrict (w_H (ip_W Pr)) (ip_mem Pr)) (prh_lin (ip_Lam Pr)) (ip_kids P + 56 * ip_n P) t D /\
      pj_ncapR SEGS (mrestrict (w_H (ip_W Pr)) (ip_mem Pr)) (ip_kids P + 56 * ip_n P) t /\
      Ledger.lsum D <= 224 * (Z.of_nat (length (rest_atR (ie_tb E) (ie_text E) (ip_p P))) - Z.of_nat (length r))
  | None =>
      getr (ip_regs Pr) 10 = w64 (-1) /\
      (cf_head = PresetReqAt.HEAD -> forall n, (PjGrammar.MAXD - S (ie_d E) <= n)%nat ->
         exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H (ip_W Pr)) (ip_mem Pr)) (prh_lin (ip_Lam Pr)) n
           (ip_kids P + 56 * ip_n P) D F /\
           map (fun b => snd b + cf_head) F = prhPv_frees (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) ok) /\
      pj_in_afterR SEGS (mrestrict (w_H (ip_W Pr)) (ip_mem Pr)) (ie_q E) (ie_text E) (ie_len E)
        (Z.of_nat (S (ie_d E))) 33 /\
      pj_fdR SEGS (mrestrict (w_H (ip_W Pr)) (ip_mem Pr)) (prh_lin (ip_Lam Pr)) (PjGrammar.MAXD - S (ie_d E))
        (ip_kids P + 56 * ip_n P) D
  end ->
  (* the facts no journal keeps, at Pr (IelemE's vrd_icur_after_call / vrd_node_ra_after_call / vrd_lam_shadow) *)
  src_rd (ip_W Pr) (ip_mem Pr) (ie_text E) (ie_tb E) ->
  prhReader_home B (ip_ly Pr) (ip_S Pr) (ip_Hp Pr) (ip_Lam Pr) (ie_text E) (ie_len E) ->
  range_addressable (aview SEGS (w_H (ip_W Pr)) (ip_mem Pr)) SHADOW_OFF (ie_q E) 24 ->
  range_addressable (aview SEGS (w_H (ip_W Pr)) (ip_mem Pr)) SHADOW_OFF (ie_v E) 56 ->
  (0 < ip_cap P -> range_addressable (aview SEGS (w_H (ip_W Pr)) (ip_mem Pr)) SHADOW_OFF
                     (ip_kids P) (56 * ip_cap P)) ->
  (ie_o E = true -> 0 < ip_cap P ->
     range_addressable (aview SEGS (w_H (ip_W Pr)) (ip_mem Pr)) SHADOW_OFF (ip_keys P) (8 * ip_cap P)) ->
  Pm (ip_mem Pr) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W Pr) (vrd_cfg A_IPVRET_SLOT Pr) (vv_postB E (ip_n P)).
Proof.
  intros E P nm Pr ok res tr okr0 D HEN (HI & HZ) Hn Hcap Hkids Hkeys Hacc Hf Hcont Hp Hok Htr HD
    HFR HRG HJN HHDR HKP HV HLED HRL HHU HLVc HXFc HOCc HIJc HLM HBM HBB HLD HRES HSRC HHOME HRAq HRAv HRAk HRAy HPM.
  (* ---- the facts of P, of the entry and of Pr ---- *)
  pose proof HI as (HFRp & HRGp & HCU & HJNp & HMD & Hnc & HKEY & HC1 & HCAP1 & HNC1 &
                    (Dk & af & lk & HKR1 & HFO1 & Hlk1 & HFL1)).
  pose proof HMD as (_ & _ & _ & _ & HFUEL & _).
  pose proof HMD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHU0).
  pose proof HCU as (HIN & _ & _ & _ & HLEDp & Hfrm & Hcnt).
  pose proof HIN as (_ & _ & _ & _ & _ & Ht0 & Htl & Hpp & Hlen & _ & _ & Hdep).
  assert (Hd : (ie_d E < PjGrammar.MAXD)%nat) by (unfold PjGrammar.MAXD; lia).
  pose proof HEN as (_ & _ & _ & _ & HRDE & _).
  pose proof HRDE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNODE & _ & Htv & _).
  pose proof HNODE as (_ & _ & _ & _ & _ & Hamv & _).
  pose proof (vrd_node_low B ARx HL LAWS CTXv CTX0v CWv E HEN) as Hvceil.
  destruct (vk_sp_bounds B ARx CTXv CTX0v CWv E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (@cf_head_nonneg cp) as Hh0.
  assert (Hamw : amem_range (ie_v E + 40) (ie_v E + 40 + 8 - (ie_v E + 40))) by (unfold amem_range in *; lia).
  (* the key clause of the value slot, at P *)
  assert (HKX : exists Dx, vrd_inode E P Dx /\
     (if ie_o E then exists x k, Dx = [(x, k)] /\
        rd_u64 SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (ip_keys P + 8 * ip_n P) x /\
        pj_cstrR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (prh_lin (ip_Lam P)) x k nm
      else Dx = [])).
  { revert HKEY. destruct (ie_o E); intros HKEY.
    - destruct HKEY as (x & k & Hx & Hc & HN). exists [(x, k)]. split; [exact HN|].
      exists x, k. exact (conj eq_refl (conj Hx Hc)).
    - destruct HKEY as (_ & HN). exists []. split; [exact HN | reflexivity]. }
  destruct HKX as (Dx & HNx & HKC).
  pose proof HNx as (_ & Hn0 & Hcap54 & _ & Hlin & Hlenacc & (Di & HPD & _) & _).
  assert (Hcpos : 0 < ip_cap P) by lia.
  assert (HDsub : forall b, In b (Dx ++ kids_blkR (ip_kids P) (ip_cap P) ++
                     keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) ++ Di) -> In b (ip_D P))
    by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPD) Hb)).
  assert (HinK : In (ip_kids P, 56 * ip_cap P) (ip_D P)).
  { apply HDsub. apply in_or_app. right. apply in_or_app. left. unfold kids_blkR.
    destruct (Z.eqb_spec (ip_cap P) 0); [lia | left; reflexivity]. }
  assert (HDr : forall b, In b (ip_D P) -> In b (ip_D Pr))
    by (intros b Hb; rewrite HD; apply in_or_app; left; exact Hb).
  pose proof HMD as (_ & _ & HLM0 & _ & _ & _ & HDEP & _).
  pose proof HLM0 as (_ & Hcnt0 & _ & HLp0 & _).
  pose proof HLM as (_ & _ & _ & HLp1 & _).
  assert (Hc0 : 0 <= ip_cnt P)
    by (rewrite Hcnt0; apply Z.mod_pos_bound; lia).
  assert (HLpr : Permutation (ip_Lam Pr) (ip_D Pr ++ ie_Lam E)).
  { rewrite HD. eapply perm_trans; [exact HLp1|]. eapply perm_trans; [apply Permutation_app_head; exact HLp0|].
    rewrite app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
  assert (HLamI : forall a k, In (a, k) (ip_Lam P) -> In (a, k) (ip_Lam Pr))
    by (intros a k Hin; apply (Permutation_in _ (Permutation_sym HLp1)); apply in_or_app; right; exact Hin).
  destruct (vv_D_apart_led CTXv CTX0v CWv E Pr HEN HJN HLED HLpr) as (HNDr & HDBr & _ & HDAPr).
  destruct (vv_D_apart_led CTXv CTX0v CWv E P HEN HJNp HLEDp HLp0) as (HNDp & _ & HDDp & _).
  pose proof HLEDp as (_ & HNDL & _).
  assert (HDLp : forall a k, In (a, k) (ip_D P) -> In (a, k) (ip_Lam P))
    by (intros a k Hin; apply (Permutation_in _ (Permutation_sym HLp0)); apply in_or_app; left; exact Hin).
  pose proof HJN as ((HARr & _) & _).
  assert (Hsep2 : forall a k a' k', In (a, k) (ip_D Pr) -> In (a', k') (ip_D Pr) -> (a, k) <> (a', k') ->
                    a + k <= a' \/ a' + k' <= a).
  { intros a k a' k' H1 H2 Hne.
    destruct (HDBr a k H1) as (Hk & Hab & _). destruct (HDBr a' k' H2) as (Hk' & Hab' & _).
    assert (Hdf : (a - cf_head, k + cf_head) <> (a' - cf_head, k' + cf_head))
      by (intros Eq; apply Hne; injection Eq as E1 E2; f_equal; lia).
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HARr Hab Hab' Hdf) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz.
    pose proof (vv_req_ge (k + cf_head)). pose proof (vv_req_ge (k' + cf_head)). lia. }
  assert (Hblk : forall a, rd_blk (ip_D Pr) a -> 4096 <= a < alloc_ceiling /\ ~ (ie_v E <= a < ie_v E + 56)).
  { intros a Ha. unfold rd_blk in Ha. apply Exists_exists in Ha as ([b k] & Hin & Hh).
    unfold pj_holdsR in Hh. cbn [fst snd] in Hh.
    destruct (HDBr b k Hin) as (Hk & _ & H4 & Hc & Hx). destruct (Hx a ltac:(lia)) as (_ & Hnv & _).
    split; [lia | exact Hnv]. }
  pose proof (HDBr _ _ (HDr _ HinK)) as (_ & _ & HK4 & HKc & _).
  (* ---- every memory transport across the count store, for any memory that differs only in the count word ---- *)
  assert (HXF : forall mem' : word -> option byte,
     (forall x : word, ~ (ie_v E + 40 <= bv_unsigned x < ie_v E + 40 + 8) ->
        mrestrict (w_H (ip_W Pr)) mem' x = mrestrict (w_H (ip_W Pr)) (ip_mem Pr) x) ->
     val_mem SEGS (mrestrict (w_H (ip_W Pr)) mem') (ie_v E + 40) 8 (ip_n P + 1) ->
     (forall a, ie_v E + 40 <= a < ie_v E + 48 -> writable_at SEGS (mrestrict (w_H (ip_W Pr)) mem') a) ->
     (if ie_o E then exists x k, Dx = [(x, k)] /\
        rd_u64 SEGS (mrestrict (w_H (ip_W Pr)) mem') (ip_keys P + 8 * ip_n P) x /\
        pj_cstrR SEGS (mrestrict (w_H (ip_W Pr)) mem') (prh_lin (ip_Lam Pr)) x k nm
      else Dx = []) /\
     pj_hdrR SEGS (mrestrict (w_H (ip_W Pr)) mem') (ie_v E) (if ie_o E then 6 else 5) 0 0
       (ip_kids P) (ip_keys P) (ip_n P + 1) (ip_cap P) /\
     rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W Pr)) mem')
       (fun a => rd_blk (ip_D P) a /\ ~ (ip_kids P + 56 * ip_n P <= a < ip_kids P + 56 * ip_n P + 56)) /\
     rd_keep SEGS (mrestrict (w_H (ip_W Pr)) (ip_mem Pr)) (mrestrict (w_H (ip_W Pr)) mem')
       (fun a => ip_kids P + 56 * ip_n P <= a < ip_kids P + 56 * ip_n P + 56 \/ rd_blk D a) /\
     rd_keep SEGS (mrestrict (w_H (ip_W Pr)) (ip_mem Pr)) (mrestrict (w_H (ip_W Pr)) mem')
       (fun a => ie_q E <= a < ie_q E + 24 \/ ie_text E <= a < ie_text E + ie_len E)).
  { intros mem' HKm Hv1 Hw1.
    assert (HK0 : forall Pz : Z -> Prop,
       (forall a, Pz a -> 0 <= a < 2 ^ 64 /\ ~ (ie_v E + 40 <= a < ie_v E + 40 + 8)) ->
       rd_keep SEGS (mrestrict (w_H (ip_W Pr)) (ip_mem Pr)) (mrestrict (w_H (ip_W Pr)) mem') Pz)
      by (intros Pz HP; exact (vk_keep_rd _ (ip_mem Pr) mem' _ _ Pz HKm HP)).
    assert (HKPD : rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W Pr)) mem')
       (fun a => rd_blk (ip_D P) a /\ ~ (ip_kids P + 56 * ip_n P <= a < ip_kids P + 56 * ip_n P + 56))).
    { apply (vv_rd_keep_trans _ (mrestrict (w_H (ip_W Pr)) (ip_mem Pr))).
      - eapply rd_keep_mono; [exact HKP|]. intros a (Hb & Hns).
        assert (Hb' : rd_blk (ip_D Pr) a) by (rewrite HD; apply rd_blk_app_l; exact Hb).
        destruct (Hblk a Hb') as (Ha1 & _).
        split; [|right; exact Hb].
        intros (r0 & Hin & Hr0). cbn [rd_fp In] in Hin.
        destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr0; lia.
      - apply HK0. intros a (Hb & _).
        assert (Hb' : rd_blk (ip_D Pr) a) by (rewrite HD; apply rd_blk_app_l; exact Hb).
        destruct (Hblk a Hb') as (Ha1 & Ha2). lia. }
    refine (conj _ (conj _ (conj HKPD (conj _ _)))).
    - (* the key slot and the key's block *)
      revert HKC. destruct (ie_o E) eqn:Ho; intros HKC; [|exact HKC].
      destruct HKC as (x & k & -> & Hx & Hc). exists x, k. split; [reflexivity|].
      assert (HinY : In (ip_keys P, 8 * ip_cap P) (ip_D P)).
      { apply HDsub. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. unfold keys_blkR.
        try rewrite Ho. destruct (Z.eqb_spec (ip_cap P) 0); [lia | left; reflexivity]. }
      assert (HinX : In (x, k) (ip_D P)) by (apply HDsub; left; reflexivity).
      assert (HNDl : List.NoDup (ip_D Pr)) by (first [exact HNDr | apply NoDup_ListNoDup; exact HNDr]).
      rewrite HD in HNDl. apply List.NoDup_app_remove_r in HNDl.
      pose proof (Permutation_NoDup HPD HNDl) as HN2. cbn [app] in HN2.
      apply List.NoDup_cons_iff in HN2 as (Hni & _).
      assert (Hxk : (x, k) <> (ip_kids P, 56 * ip_cap P)).
      { intros Eq. apply Hni. rewrite Eq. apply in_or_app. left. unfold kids_blkR.
        destruct (Z.eqb_spec (ip_cap P) 0); [lia | left; reflexivity]. }
      assert (Hyk : (ip_keys P, 8 * ip_cap P) <> (ip_kids P, 56 * ip_cap P)) by (intros Eq; injection Eq as _ E2; lia).
      pose proof (Hsep2 _ _ _ _ (HDr _ HinX) (HDr _ HinK) Hxk) as Hapx.
      pose proof (Hsep2 _ _ _ _ (HDr _ HinY) (HDr _ HinK) Hyk) as Hapy.
      pose proof (HDBr _ _ (HDr _ HinX)) as (Hk0 & _).
      split.
      + eapply rd_u64_keep; [exact Hx | eapply rd_keep_mono; [exact HKPD|]].
        intros z Hz. cbv beta in Hz |- *. split; [|lia].
        apply (rd_blk_in _ (ip_keys P, 8 * ip_cap P)); [exact HinY | cbn [fst snd]; lia].
      + eapply pj_cstrR_keep; [exact Hc | unfold prh_lin; apply HLamI | eapply rd_keep_mono; [exact HKPD|]].
        intros z Hz. cbv beta in Hz |- *. split; [|lia].
        apply (rd_blk_in _ (x, k)); [exact HinX | cbn [fst snd]; lia].
    - (* the header, count n + 1 *)
      apply (vv_hdr_store _ _ _ _ _ _ _ _ _ _ _ HHDR); [| exact Hv1 | lia | exact Hw1].
      apply HK0. intros a Ha. lia.
    - (* the new slot and the subtree's blocks *)
      apply HK0. intros a [Ha | Ha].
      + assert (Hb : rd_blk (ip_D Pr) a)
          by (apply (rd_blk_in _ (ip_kids P, 56 * ip_cap P)); [exact (HDr _ HinK) | cbn [fst snd]; lia]).
        destruct (Hblk a Hb). lia.
      + assert (Hb : rd_blk (ip_D Pr) a) by (rewrite HD; apply rd_blk_app_r; exact Ha).
        destruct (Hblk a Hb). lia.
    - (* the cursor cells and the text *)
      apply HK0. intros a [Ha | Ha]; lia. }
  (* ---- the seat at slot 6164 ---- *)
  assert (HHDRr : pj_hdrR SEGS (mrestrict (w_H (ip_W Pr)) (ip_mem Pr)) (ie_v E) (if ie_o E then 6 else 5) 0 0
                    (ip_kids Pr) (ip_keys Pr) (ip_n Pr) (ip_cap Pr))
    by (rewrite Hkids, Hkeys, Hn, Hcap; exact HHDR).
  destruct (vv_seat_gen true A_IPVRET_SLOT CTXv CTX0v CWv E Pr _ _ _ _ _ HEN HFR HRG HHDRr HRAv) as [HS SHOK].
  (* the runner is stated at the empty budget: the journal rebased to Pr's depot (VrdIElem.vrd_ijrn_base) *)
  pose proof (vrd_ijrn_base B ARx SK E Pr HJN) as HJ.
  pose proof HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  assert (HEI : img_env VAL A_LIM (vv_E1 E Pr)) by (unfold vv_E1; apply Eimg_env).
  assert (HR0 : forall r, getr (ip_regs Pr) r = sv_denot (vv_E1 E Pr) (sr_get vv_regs1 r))
    by (intros r; exact (st_ok_pi_restrict_reg _ _ _ _ r HS)).
  assert (U20 : bv_unsigned (ew (vv_E1 E Pr) 20) = ie_v E)
    by (rewrite (vv_E1_low E Pr 20 20%bv eq_refl), G20; unfold w64; apply unsigned_lit_small; lia).
  assert (HAWv : forall a, ie_v E + 40 <= a < ie_v E + 48 ->
     awr_byte (STK_parse_items (ie_d E) + ie_e E) (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
       (ablocks B (ie_ly E) (ie_S E)) (ablocks B (ip_ly Pr) (ip_S Pr)) (ip_ly Pr) [] a
     \/ wr_fp_frame (rd_fp (ie_q E) (ie_v E)) (ie_S E) (ip_ly Pr) a)
    by (intros a Ha; apply (vv_v_awr CTXv CTX0v CWv E Pr a HEN HJN); lia).
  pose (RUN := paj_run_xf_invR (fx := ip_fx Pr) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (RUNTO := paj_run_to_xf_invR (fx := ip_fx Pr) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (BR := paj_branchR (fx := ip_fx Pr) (PI := PAI) (wle' SEGS YGcfRehidePost.RZ_cf)).
  unfold vrd_cfg.
  (* rows 232..236: the shadow test of v + 40 (folded), v->n := n + 1 *)
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vi_Bspan; [exact (vv_awr_node _ _ _ _ _ _ _ _ _ _ _ _ U20 HAWv)|].
  rename ms into ms1.
  pose proof (vv_frame_node _ _ _ _ _ _ HFr U20) as HM1. clear HF HFr HG.
  (* row 237: `bnez a0` *)
  psrr_branch_tok RUN BR HS SHOK vi_Bspan.
  - (* taken: parse_value refused (a0 = -1); `li s2, -1` and on to the exit *)
    destruct res as [[t r]|].
    { exfalso. destruct HRES as (H10 & _). cbn [sv_denot] in Hc.
      rewrite (vv_E1_low E Pr 10 10%bv eq_refl), H10 in Hc. vm_compute in Hc. discriminate Hc. }
    destruct HRES as (H10 & HFO2 & HINA & HFD).
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vi_Bspan (4 * Z.of_nat A_IEPI_SLOT);
      [exact (vv_awr_node _ _ _ _ _ _ _ _ _ _ _ _ U20 HAWv)|].
    match goal with ms0 : machine_state |- _ => lazymatch ms0 with ms1 => fail | _ => rename ms0 into ms2 end end.
    pose proof (vv_frame_node _ _ _ _ _ _ HFr U20) as HM2. clear HF HFr HG.
    assert (HKm : forall x : word, ~ (ie_v E + 40 <= bv_unsigned x < ie_v E + 40 + 8) ->
              mrestrict (w_H (ip_W Pr)) (ms_mem ms2) x = mrestrict (w_H (ip_W Pr)) (ip_mem Pr) x)
      by (intros x Hx; rewrite (HM2 x ltac:(lia)); exact (HM1 x ltac:(lia))).
    match type of HS with st_ok_pi _ _ ?E' ?ss _ =>
      let r := eval vm_compute in (nth 1 (ss_mem ss) vv_frame1) in
      pose proof (vv_region_nth _ E' ss _ 1 r HS ltac:(vm_compute; reflexivity)) as HR1 end.
    cbn [ms_mem restrict] in HR1.
    destruct (vv_node_facts _ _ _ (ie_v E) (ip_n Pr) HR1 U20 (vv_E1_46 E Pr) ltac:(lia) ltac:(lia)) as (Hv1 & Hw1).
    rewrite Hn in Hv1.
    match type of HS with st_ok_pi _ _ _ ?ss2 _ =>
      assert (HKR : forall r, sr_get (ss_regs ss2) r = sr_get vv_regs1 r -> getr (ms_regs ms2) r = getr (ip_regs Pr) r)
        by (intros r0 Hr0; rewrite (st_ok_restrict_reg SEGS _ _ _ ms2 r0 HS), HR0;
            apply (f_equal (sv_denot (vv_E1 E Pr))); exact Hr0) end.
    assert (K18 : getr (ms_regs ms2) 18 = w64 (-1)).
    { rewrite (st_ok_restrict_reg SEGS _ _ _ ms2 _ HS).
      match goal with |- sv_denot _ (sr_get ?l ?r) = _ =>
        let v := eval vm_compute in (sr_get l r) in change (sr_get l r) with v end.
      cbn [sv_denot]. unfold w64. first [reflexivity | apply bv_eq; vm_compute; reflexivity]. }
    assert (Hsp2 : spZ (ms_regs ms2) = spZ (ip_regs Pr))
      by (unfold spZ; rewrite HKR by (vm_compute; reflexivity); reflexivity).
    destruct (HXF (ms_mem ms2) HKm Hv1 Hw1) as (HKC3 & HHDR3 & HKPD & HKSD & HKQT).
    pmkst HS.
    lazymatch goal with |- SRrG _ _ _ (mkCfg _ ?md) _ => set (md2 := md) in * end.
    destruct (vv_node_store_keep0 CTXv CTX0v CWv E Pr (ms_regs ms2) (ms_mem ms2) md2 (ip_k Pr) (ie_v E + 40) 8
                HEN HFR HLED HJN ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HKm Hsp2
                (vrd_ijrn_unbase B ARx SK E Pr _ _ _ _ _ _ _ HJN HJ)) as (F1 & F2 & F3 & _).
    destruct (vv_model_none CTXv CTX0v CWv E P (vk_move Pr (ms_regs ms2) (ms_mem ms2) md2 (ip_k Pr) (ip_p Pr))
                nm ok tr okr0 D HEN HMD HC1 HV HLM HBB HLD Hok Htr HD HXFc HLVc HOCc)
      as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
    apply SRr'_ret. unfold vv_postB. split; [|exact HPM]. right.
    exists (vk_move Pr (ms_regs ms2) (ms_mem ms2) md2 (ip_k Pr) (ip_p Pr)), (-1).
    split; [reflexivity|]. split; [unfold vrd_cfg, vk_move; cbn [ip_fx ip_regs ip_mem ip_md]; reflexivity|].
    unfold vrd_iexit_a.
    (* the call's all-granted trace at the value: the trace so far, parse_value's granted trace, the rest *)
    destruct (vv_gt_val E P nm HMD HC1) as (more & HG).
    (* vrd_iexit_a's order: frame, journal, gp, tp, s2, res, ledger, room, TRANSFER, OUTCOME, ledger move, blocks
       bytes, lsum, the answer, LIVE, HULL (the position's use, then the refusing callee's: VrdIStep.vi_hull_exit),
       the OUTCOME OF AN INJECTED READING (last bullet) *)
    refine (conj F1 (conj F3 (conj _ (conj _ (conj _ (conj _ (conj F2 (conj HRL (conj L5 (conj L7
              (conj L1 (conj L2 (conj L3 (conj _ (conj L6
                 (conj (vi_hull_exit _ _ _ (ip_tr P) _ more _ _ HG eq_refl HHU0 HHU) _)))))))))))))))).
    + unfold vk_move; cbn [ip_regs]. rewrite HKR by (vm_compute; reflexivity). exact G3.
    + unfold vk_move; cbn [ip_regs]. rewrite HKR by (vm_compute; reflexivity). exact G4.
    + exact K18.
    + right; reflexivity.
    + exists [], okr0. split; [exact L4|]. split; [intros Hr0; discriminate Hr0|]. intros _.
      replace (Z.of_nat (S (ie_d E))) with (Z.of_nat (ie_d E) + 1) in HINA by lia.
      split; [eapply vv_in_after_keep; [exact HINA | eapply rd_keep_mono; [exact HKQT | intros a Ha; left; exact Ha]]|].
      split.
      * eapply (vv_fd_exit E P _ nm Dx D HNx).
        -- exact HKC3.
        -- exact Hnc.
        -- exact Hd.
        -- exact HD.
        -- exact HLamI.
        -- exact HDEP.
        -- exact HHDR3.
        -- exact HKPD.
        -- eapply pj_fdR_keep; [exact HFD | intros x k _ Hx; exact Hx | exact HKSD].
        -- exact HNDr.
        -- exact HDAPr.
        -- exact Hh0.
        -- exact HNDp.
        -- exact HDDp.
        -- exact HNDL.
        -- exact HDLp.
      * (* The kit's cut: THE PARTIAL FREE ORDER - the completed slots', the refused slot's (the callee's partial list,
           then its key), then the arrays; the model's list is jfl's None arm (vv_fl_none) *)
        intros Hhd nx Hnx.
        assert (HSFO : cf_head = PresetReqAt.HEAD -> forall n1, (PjGrammar.MAXD - S (ie_d E) <= n1)%nat ->
                  exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H (ip_W Pr)) (ms_mem ms2)) (prh_lin (ip_Lam Pr)) n1
                    (ip_kids P + 56 * ip_n P) D F /\
                    map (fun b => snd b + cf_head) F =
                      prhPv_frees (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) ok).
        { intros Hh' n1 Hn1. destruct (HFO2 Hh' n1 Hn1) as (Fc & HFc & HmFc). exists Fc.
          exact (conj (vv_fo_keep _ _ _ _ _ _ _ HFc HKSD) HmFc). }
        destruct (vv_fo_exit E P (vk_move Pr (ms_regs ms2) (ms_mem ms2) md2 (ip_k Pr) (ip_p Pr)) D Dx Dk af lk
                    (prhPv_frees (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) ok)
                    HNx HFO1 HKR1 Hlk1 Hnc Hd HD HLamI HDEP HHDR3 HKPD HSFO HNDr HDAPr Hh0 HNDp HDDp HNDL HDLp
                    Hhd nx Hnx) as (F & HF & HmF).
        exists F. split; [exact HF|]. rewrite HmF. unfold vk_move; cbn [ip_ok]. rewrite Hok.
        rewrite (vv_fl_none _ _ _ _ _ _ _ _ _ _ _ _ _ HFL1 HFUEL HV). reflexivity.
    + (* THE OUTCOME OF AN INJECTED READING: the position's oks, then parse_value's (VrdIElem.vrd_inj_exit); its part
         is its own injected-reading clause inside its window and its outcome clause past it (VrdIElem.vrd_inj_callee),
         at the counter the steps so far reached (vv_granted_regs) *)
      destruct (vv_granted_regs CTXv CTX0v CWv E P HEN HMD) as (Hcnt1 & Hfl1 & _).
      intros sm0 x0 os0 i0 H00 hist0 Hq1 Hq2 Hq3 Hq4. unfold vk_move. cbn [ip_ok ip_tr]. rewrite Hok, Htr.
      eapply (vrd_inj_exit E P ok tr); [exact HMD | | exact Hq1 | exact Hq2 | exact Hq3 | exact Hq4].
      refine (vrd_inj_callee E P _ (PjGrammar.jr_value prh_jr_strtod (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P)))
                ok None tr okr0 (ip_cnt P) (PjGrammar.agrees_jr_value prh_jr_strtod _ _)
                (vrd_nf_jr_value prh_jr_strtod _ _) _ HV Hcnt1 _ _).
      * (* parse_value's run begins the continuation's (vrd_jval's bind at the position's fuel) *)
        intros okt. rewrite HC1. unfold vrd_jval.
        match goal with |- context [snd (fst (PjGrammar.jbind ?m ?k okt))] =>
          destruct (vrd_jbind_prefix _ _ m k okt) as (t2 & Et2); rewrite Et2 end.
        rewrite (PjGrammar.jr_value_fuel prh_jr_strtod (ip_f P) (S (ie_d E)) _ okt HFUEL). exists t2. reflexivity.
      * rewrite <- Hfl1. exact HIJc.
      * intros sm1 x1 os1 i1 H01 hist1 Hpo Hro Hco Hwo. rewrite <- Hfl1 in Hwo.
        exact (proj1 (proj2 (HOCc sm1 x1 os1 i1 H01 hist1 Hpo Hro Hco Hwo))).
  - (* not taken: parse_value read a value (a0 = 0); on to the separator *)
    destruct res as [[t r]|].
    2:{ exfalso. destruct HRES as (H10 & _). cbn [sv_denot] in Hc.
        rewrite (vv_E1_low E Pr 10 10%bv eq_refl), H10 in Hc. vm_compute in Hc. discriminate Hc. }
    destruct HRES as (H10 & HFO2 & HIN2 & HNODE2 & HNCAP2 & _).
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vi_Bspan (4 * Z.of_nat A_ISEP_SLOT);
      [exact (vv_awr_node _ _ _ _ _ _ _ _ _ _ _ _ U20 HAWv)|].
    match goal with ms0 : machine_state |- _ => lazymatch ms0 with ms1 => fail | _ => rename ms0 into ms2 end end.
    pose proof (vv_frame_node _ _ _ _ _ _ HFr U20) as HM2. clear HF HFr HG.
    assert (HKm : forall x : word, ~ (ie_v E + 40 <= bv_unsigned x < ie_v E + 40 + 8) ->
              mrestrict (w_H (ip_W Pr)) (ms_mem ms2) x = mrestrict (w_H (ip_W Pr)) (ip_mem Pr) x)
      by (intros x Hx; rewrite (HM2 x ltac:(lia)); exact (HM1 x ltac:(lia))).
    match type of HS with st_ok_pi _ _ ?E' ?ss _ =>
      let r := eval vm_compute in (nth 1 (ss_mem ss) vv_frame1) in
      pose proof (vv_region_nth _ E' ss _ 1 r HS ltac:(vm_compute; reflexivity)) as HR1 end.
    cbn [ms_mem restrict] in HR1.
    destruct (vv_node_facts _ _ _ (ie_v E) (ip_n Pr) HR1 U20 (vv_E1_46 E Pr) ltac:(lia) ltac:(lia)) as (Hv1 & Hw1).
    rewrite Hn in Hv1.
    match type of HS with st_ok_pi _ _ _ ?ss2 _ =>
      assert (HKR : forall r, sr_get (ss_regs ss2) r = sr_get vv_regs1 r -> getr (ms_regs ms2) r = getr (ip_regs Pr) r)
        by (intros r0 Hr0; rewrite (st_ok_restrict_reg SEGS _ _ _ ms2 r0 HS), HR0;
            apply (f_equal (sv_denot (vv_E1 E Pr))); exact Hr0) end.
    assert (Hsp2 : spZ (ms_regs ms2) = spZ (ip_regs Pr))
      by (unfold spZ; rewrite HKR by (vm_compute; reflexivity); reflexivity).
    destruct (HXF (ms_mem ms2) HKm Hv1 Hw1) as (HKC3 & HHDR3 & HKPD & HKSD & HKQT).
    pmkst HS.
    lazymatch goal with |- SRrG _ _ _ (mkCfg _ ?md) _ => set (md2 := md) in * end.
    destruct (vv_node_store_keep0 CTXv CTX0v CWv E Pr (ms_regs ms2) (ms_mem ms2) md2 (ip_k Pr) (ie_v E + 40) 8
                HEN HFR HLED HJN ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HKm Hsp2
                (vrd_ijrn_unbase B ARx SK E Pr _ _ _ _ _ _ _ HJN HJ)) as (F1 & F2 & F3 & _).
    destruct (vv_value_suffix _ _ _ _ _ _ _ HV) as (kk & Hrk).
    assert (Hrest3 : rest_atR (ie_tb E) (ie_text E) (ie_text E + ie_len E - Z.of_nat (length r)) = r)
      by (rewrite Hrk; apply vv_rest_after; [exact Hlen | lia]).
    replace (Z.of_nat (S (ie_d E))) with (Z.of_nat (ie_d E) + 1) in HIN2 by lia.
    pose proof (pj_nodeR_keep SEGS t _ _ _ _ _ _ HNODE2 (fun x k _ Hx => Hx) HKSD) as HNODE3.
    pose proof HBM as (_ & _ & HfrP & _).
    apply SRr'_ret. unfold vv_postB. split; [|exact HPM]. left.
    exists (MkIPos (ip_fx Pr) (ip_ly Pr) (ip_S Pr) (ip_Hp Pr) (ip_W Pr) (ms_regs ms2) (ms_mem ms2) md2 (ip_k Pr)
      (ip_n P + 1) (ip_cap P) (ip_kids P) (ip_keys P) (ie_text E + ie_len E - Z.of_nat (length r))
      ((nm, t) :: ip_acc P) (ip_f P)
      (vrd_jsep (S (ie_d E)) (ie_o E) (Z.to_nat (ip_n P + 1)) (Z.to_nat (ip_cap P)) ((nm, t) :: ip_acc P) (ip_f P) r)
      (ip_ok P ++ repeat true (PjGrammar.calls tr)) (ip_tr Pr) (ip_D Pr)
      (ip_Lam Pr) (ip_peak Pr) (ip_cnt Pr) (ip_fail Pr) (ip_ran Pr)).
    split; [reflexivity|]. split; [unfold vrd_cfg; cbn [ip_fx ip_regs ip_mem ip_md]; reflexivity|].
    split; [reflexivity|].
    unfold vv_sep.
    refine (conj F1 (conj _ (conj _ (conj _ (conj F3 (conj _ (conj _ (conj _ _)))))))).
    + (* the registers *)
      unfold vrd_iregs. cbn [ip_regs]. repeat (rewrite HKR by (vm_compute; reflexivity)). exact HRG.
    + (* the node, one element longer *)
      eapply (vv_inode_snoc E P _ nm Dx t D HNx).
      * exact HKC3.
      * exact Hnc.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * exact HD.
      * exact HLamI.
      * exact HHDR3.
      * exact HKPD.
      * exact HNODE3.
      * apply (vv_keep_ra_node _ (ip_mem Pr) (ms_mem ms2) _ _ _ _ HKm Hamw); [lia | lia | exact HRAv].
      * cbn [ip_cap ip_kids]. intros Hc'.
        apply (vv_keep_ra_node _ (ip_mem Pr) (ms_mem ms2) _ _ _ _ HKm Hamw); [lia | lia | exact (HRAk Hc')].
      * cbn [ip_cap ip_keys]. intros Ho Hc'.
        assert (HinY : In (ip_keys P, 8 * ip_cap P) (ip_D P)).
        { apply HDsub. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. unfold keys_blkR.
          rewrite Ho. destruct (Z.eqb_spec (ip_cap P) 0); [lia | left; reflexivity]. }
        pose proof (HDBr _ _ (HDr _ HinY)) as (_ & _ & HY4 & HYc & _).
        apply (vv_keep_ra_node _ (ip_mem Pr) (ms_mem ms2) _ _ _ _ HKm Hamw); [lia | lia | exact (HRAy Ho Hc')].
      * exact Hh0.
      * exact HNDp.
      * exact HDDp.
      * exact HNDL.
      * exact HDLp.
    + (* the cursor, the text, the ledger *)
      unfold vrd_icur. cbv zeta.
      cbn [ip_W ip_mem ip_p ip_ly ip_S ip_Hp ip_Lam ip_peak ip_cnt ip_fail ip_ran].
      refine (conj _ (conj _ (conj _ (conj HHOME (conj F2 (conj _ _)))))).
      * eapply pj_in_okR_keep; [exact HIN2 | exact HKQT].
      * apply (vv_keep_ra_node _ (ip_mem Pr) (ms_mem ms2) _ _ _ _ HKm Hamw); [lia | lia | exact HRAq].
      * destruct HSRC as (Hby & Ht4 & Htl' & Ham & Hra & Hhull).
        split; [|split; [exact Ht4 | split; [exact Htl' | split; [exact Ham | split]]]].
        -- unfold PRH_Base.bytes_at in *. eapply garr8_keep; [exact Hby|].
           eapply rd_keep_mono; [exact HKQT|]. intros a Ha. right. lia.
        -- apply (vv_keep_ra_node _ (ip_mem Pr) (ms_mem ms2) _ _ _ _ HKm Hamw); [lia | lia | exact Hra].
        -- intros Hl. apply (vv_keep_hull_node _ (ip_mem Pr) (ms_mem ms2) _ _ _ _ HKm Hamw);
             [lia | lia | lia | exact (Hhull Hl)].
      * rewrite (Permutation_length HfrP). exact Hfrm.
      * rewrite Hrest3. exact (vv_cnt_after E P ok t r tr okr0 _ _ D _ _ _ _ _ Hcnt Hc0 HV HLM).
    + (* the model *)
      eapply (vv_model_some CTXv CTX0v CWv E P _ nm ok t r tr okr0 D HEN HMD HC1 HV).
      * exact HLM.
      * exact HRL.
      * exact HHU.
      * exact HBB.
      * exact HLD.
      * exact HXFc.
      * exact HLVc.
      * exact Hrest3.
      * reflexivity.
      * exact Htr.
      * exact HD.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * lia.
      * cbn [ip_cont ip_n ip_cap ip_acc ip_f ip_p]. rewrite Hrest3. reflexivity.
    + cbn [ip_n]. lia.
    + cbn [ip_cont ip_n ip_cap ip_acc ip_f ip_p]. rewrite Hrest3. reflexivity.
    + (* The kit's cut: THE BATCH KIT'S LAYER at the separator - the callee's caps and order list join the completed slots' at the
         memory after the count store (vv_k1_snoc); the model's free list is vrd_jfsep with the value's list
         prhPv_frees in the accumulator (vv_fl_some) *)
      pose proof (pj_ncapR_keep SEGS t _ _ _ _ _ HNODE2 HNCAP2 HKSD) as HNCAP3.
      assert (HSFO : cf_head = PresetReqAt.HEAD -> forall n0, (PjTree.depth t <= n0)%nat ->
                exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H (ip_W Pr)) (ms_mem ms2)) (prh_lin (ip_Lam Pr)) n0
                  (ip_kids P + 56 * ip_n P) D F /\
                  map (fun b => snd b + cf_head) F =
                    prhPv_frees (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) ok).
      { intros Hhd nx Hnx. destruct (HFO2 Hhd nx Hnx) as (F & HF & HmF). exists F.
        exact (conj (vv_fo_keep _ _ _ _ _ _ _ HF HKSD) HmF). }
      match goal with |- vv_k1sep E ?P2 =>
        destruct (vv_k1_snoc E P P2 nm t D Dx Dk af lk
                    (prhPv_frees (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) ok)
                    HNx HNC1 HFO1 HKR1 Hlk1 Hnc eq_refl eq_refl eq_refl eq_refl eq_refl HD HLamI HKPD HNCAP3 HSFO
                    Hh0 HNDp HDDp HNDL HDLp) as (HNC2 & HFO3) end.
      unfold vv_k1sep. cbn [ip_cap ip_n ip_ok ip_f ip_p].
      split; [|split; [exact HNC2|]].
      * replace (Z.to_nat (ip_n P + 1)) with (S (Z.to_nat (ip_n P))) by lia. exact HCAP1.
      * exists (af ++ prhPv_frees (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P)) ok ++ lk).
        split; [exact HFO3|].
        intros okr. rewrite Hrest3.
        replace (Z.to_nat (ip_n P + 1)) with (S (Z.to_nat (ip_n P))) by lia.
        exact (vv_fl_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HFL1 HFUEL HV okr).
Qed.

(* parse_value at the call's OWN nesting S (ie_d E) is a premise here, not the Section's all-depths H_parse_value: the
   parse_items / parse_value descending induction on d supplies only that nesting (check 2's finding, 2026-10-30) *)
Lemma vv_partB : forall E P nm,
  (forall fx' : YK11.FPState, @tparse_value_specX fx' rc ci cp PI RL A_prog_listing PAI B ARx SK (S (ie_d E))
                                CTXv CTX0v CWv) ->
  vrd_ient_ok B ARx CTXv CTX0v CWv E -> vv_set E P nm -> Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_IMSET_RET P) (vv_postB E (ip_n P)).
Proof.
  intros E P nm HPV HEN (HI & HZ) HPM.
  destruct (vv_seat1 false A_IMSET_RET CTXv CTX0v CWv E P nm HEN HI) as [HS SHOK].
  pose proof HI as (HFR & HRG & HCU & HJN & HMD & Hnc & HKEY & Hcont & _).
  (* the runner is stated at the empty budget: the journal rebased to P's depot (VrdIElem.vrd_ijrn_base) *)
  pose proof (vrd_ijrn_base B ARx SK E P HJN) as HJ.
  assert (HEI : img_env VAL A_LIM (vv_E1 E P)) by (unfold vv_E1; apply Eimg_env).
  assert (HR0 : forall r, getr (ip_regs P) r = sv_denot (vv_E1 E P) (sr_get vv_regs1 r))
    by (intros r; exact (st_ok_pi_restrict_reg _ _ _ _ r HS)).
  pose (RUN := paj_run_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  unfold vrd_cfg.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vi_Bspan;
    [eapply awr_ok_cons_ro; [cbn; lia | eapply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]]|].
  (* the run wrote nothing *)
  assert (EQm : ms_mem ms = ip_mem P)
    by (apply functional_extensionality; intros x; exact (vv_frame_ro _ _ _ _ HF x)).
  rewrite EQm in HPM.
  assert (Q11 : getr (ms_regs ms) 11 =
    sv_denot (vv_E1 E P) (SAlu ALU_ADD (SOff 45 0) (SMd M_MUL (SOff 46 0) (SLit 56))))
    by (rewrite (st_ok_restrict_reg SEGS _ _ _ ms (11%bv : bv 5) HS); reflexivity).
  assert (HKR : aregs_preserved (ip_regs P) (ms_regs ms)).
  { intros r Hr. unfold acallee_saved in Hr.
    rewrite (st_ok_restrict_reg SEGS _ _ _ ms (Z_to_bv 5 r) HS), HR0.
    assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                 r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      apply (f_equal (sv_denot (vv_E1 E P))); vm_compute; reflexivity. }
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
  (* ---- the facts of the slot and the position ---- *)
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof H_head as (Hh8 & HLh).
  pose proof H_img as (Himg1 & Himg2 & Himg3).
  pose proof HFR as (Hsp & _).
  pose proof HRG as (G3 & G4 & G8 & _).
  pose proof HCU as (HIN & HRAq & HSRC & HHOME & HLED & HFRB & HCNT).
  destruct (vv_islot_inode E P nm HI) as [Dx HN].
  pose proof HN as (HHDR & Hn0 & Hcap & Hc0 & Hlin & Hlen & (Di & HPD & HIT) & HRW & HRAv & HRAk & HRAy & Hky0).
  assert (Hcpos : 0 < ip_cap P) by lia.
  destruct (Hlin Hcpos) as (HLk & _).
  assert (HinD : In (ip_kids P, 56 * ip_cap P) (ip_D P)).
  { apply (Permutation_in _ (Permutation_sym HPD)). apply in_or_app. right. apply in_or_app. left.
    unfold kids_blkR. destruct (Z.eqb_spec (ip_cap P) 0); [lia | left; reflexivity]. }
  destruct (vv_D_apart CTXv CTX0v CWv E P HEN HJN HCU HMD) as (HND & HDB & HDD & HDAP).
  destruct (HDB _ _ HinD) as (Hk0 & HkAB & Hk4096 & Hkceil & HkX).
  pose proof HJN as (_ & HWIN & HFZ & HFK & HROD & HBM & HCH).
  pose proof HBM as (HBnew & HABP & HFRP & HPK).
  pose proof (HBnew _ _ HinD) as HkE.
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLED HLk) as (_ & _ & HkHp & Hk16 & _).
  pose proof HEN as ((HAFN & _ & Hhi0) & _ & _ & _ & HRD & _ & _ & _ & (_ & HSEC0 & H240) & _ & HCLOS & _ & _ & _ & _ &
                     HIRET & _).
  (* the text's hull budget at the entry: the last component of vrd_ient_ok's trailing slot *)
  pose proof HEN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & HHB)).
  pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof HRD as (HFZ0 & HMU & HUN1 & HUN2 & _ & HFW & Hq0 & Hq24 & _ & _ & _ & HMAXR & _).
  (* rd_pre's appended conjunct (the kit's cut, PRH_FnParse.v:227): the text ends below the ceiling, the entry's *)
  pose proof HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTXC).
  pose proof HFW as (He0 & He16 & Hetop & Hepres).
  pose proof HIN as (_ & _ & _ & _ & Hq8 & _ & _ & _ & HtbL & _ & _ & Hdep).
  assert (Hd : (ie_d E < PjGrammar.MAXD)%nat) by (unfold PjGrammar.MAXD; lia).
  destruct (vv_stk_call (ie_d E) Hd) as (Hpv0 & Hpv1).
  assert (Hreq : req_size (56 * ip_cap P + cf_head) = 56 * ip_cap P + cf_head)
    by (unfold req_size; destruct (Z.eqb_spec (56 * ip_cap P + cf_head) 0); lia).
  assert (U45 : bv_unsigned (ew (vv_E1 E P) 45) = ip_kids P)
    by (rewrite vv_E1_45; unfold w64; apply unsigned_lit_small; lia).
  assert (U46 : bv_unsigned (ew (vv_E1 E P) 46) = ip_n P)
    by (rewrite vv_E1_46; unfold w64; apply unsigned_lit_small; lia).
  set (dS := ip_kids P + 56 * ip_n P) in *.
  assert (EdS : dS = ip_kids P + 56 * ip_n P) by reflexivity.
  clearbody dS.
  assert (HdS : getr (ms_regs ms) 11 = w64 dS)
    by (rewrite EdS, Q11, denot_lit_U, (vv_slot_U (vv_E1 E P) (ip_kids P) (ip_n P) U45 U46) by lia; reflexivity).
  assert (HspT : spZ (ms_regs ms) = spZ (ie_regs E) + ie_e E + - (ie_e E + 144)).
  { unfold spZ at 1. rewrite Q2, (vv_E1_low E P 2 2%bv eq_refl). fold (spZ (ip_regs P)). rewrite Hsp. lia. }
  assert (Hspc : spZ (ms_regs ms) = spZ (ie_regs E) - 144) by lia.
  assert (Ho16 : (- (ie_e E + 144)) mod 16 = 0).
  { apply Z.mod_opp_l_z; [lia|]. rewrite Z.add_mod by lia. rewrite He16. reflexivity. }
  assert (HqR : getr (ms_regs ms) 8 = w64 (ie_q E)) by (rewrite Q8, (vv_E1_low E P 8 8%bv eq_refl); exact G8).
  assert (Hq10 : getr (ms_regs ms) 10 = w64 (ie_q E)) by (rewrite Q10, (vv_E1_low E P 8 8%bv eq_refl); exact G8).
  assert (Hs0q : s0Z (ms_regs ms) = ie_q E).
  { unfold s0Z. rewrite HqR. unfold w64. apply unsigned_lit_small. lia. }
  (* the call-site position: P's state at the call's registers and model *)
  set (mdc := with_vm_backing (m_vm_lazy (ip_md P)) mat (ip_md P)) in *.
  set (Pc := vk_move P (ms_regs ms) (ip_mem P) mdc (ip_k P) (ip_p P)).
  (* the journal at the call, back at the budget ie_CW E (VrdIElem.vrd_ijrn_unbase): the budgeted call rule takes it *)
  pose proof (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ) as HJw.
  assert (HJc : ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
      (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E)
      (ie_md E) [] (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) mdc (ip_k P) (ie_CW E))
    by (rewrite <- EQm; exact HJw).
  assert (VK : vrd_iframe E Pc /\ vrd_inode E Pc Dx /\ vrd_icur B E Pc /\ vrd_ijrn B ARx SK E Pc).
  { apply (vk_cur_store_keep B ARx SK LAWS Hh8 H_pst CTXv CTX0v CWv E P Dx (ms_regs ms) (ip_mem P) mdc (ip_k P)
             (ip_p P) alloc_ceiling 0).
    all: first [ assumption | lia | (intros a Ha; lia) | (intros x _; reflexivity)
               | (rewrite Hspc, Hsp; reflexivity) ]. }
  destruct VK as (HFRc & HNc & HCUc & HJNc).
  destruct (vrd_reader_call_pre B ARx SK LAWS CTXv CTX0v CWv E Pc (ms_regs ms) Himg1 Himg2 H_s0s HEN HFRc HJNc
              Hspc HqR) as (HCURc & (HCENc & HCWc) & HCHc & Hq16 & Hq24c & HFWc & HRODc & HSHIc).
  destruct (HCHc (spZ (ms_regs ms)) (Z.le_refl _)) as (ch1 & Hch1 & Hsp1).
  pose proof HMD as (Hok & HFAC & HLM & HROOM & HFUEL & HBB & HDEP & HLSUM & HXF0 & HLV0 & HHU0).
  (* the call's all-granted trace through parse_value's (the live counts at its inner calls) *)
  destruct (vv_gt_val E P nm HMD Hcont) as (more & Hgt).
  eapply SRr'_bind.
  (* The kit's cut: parse_value's text posts fpostWFbm at wbudget CW 0, so the BUDGETED call rule (VrdArm.vrd_call_WFb_P,
     the caller's journal at its budget WS0 := ie_CW E, the memory invariant carried by srr_inv_call) *)
  { eapply (vrd_call_WFb_P (fx := ip_fx P) B ARx SK LAWS Pm PCALL) with
      (o := - (ie_e E + 144)) (e1 := ie_e E + 144) (STK1 := STK_parse_value (S (ie_d E)))
      (FP1 := rd_fp (ie_q E) dS) (ch1 := ch1).
    - exact HS.
    - reflexivity.
    - exact HJw.
    - exact HspT.
    - exact Ho16.
    - lia.
    - exact Hpv0.
    - lia.
    - lia.
    - rewrite Q3, (vv_E1_low E P 3 3%bv eq_refl). exact G3.
    - rewrite Q4, (vv_E1_low E P 4 4%bv eq_refl). exact G4.
    - exact Q1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - pose proof (@pa_B_ok _ _ PI_prog_A) as HBok. rewrite unsigned_lit_small by lia. lia.
    - rewrite Hs0q, EQm. replace (spZ (ie_regs E) + ie_e E + - (ie_e E + 144)) with (spZ (ms_regs ms)) by lia.
      exact Hch1.
    - cbn [cfg_ms ms_mem]. rewrite EQm. exact HPM.
    - intros HPRE. cbn [ss_pc setpc].
      rewrite EQm in HPRE |- *.
      assert (HART : ARx (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) mdc) by exact (proj1 HJc).
      destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HART HkAB) as (_ & _ & _ & Happ & HkPres & _).
      rewrite Hreq in Happ, HkPres.
      (* the room for parse_value's granted run: a prefix of the position's granted continuation *)
      assert (HROOMv : rd_room (ip_S P) (prhPv_gtrace (S (ie_d E)) (rest_atR (ie_tb E) (ie_text E) (ip_p P)))).
      { rewrite Hcont in HROOM. unfold vrd_jval in HROOM.
        lazymatch type of HROOM with rd_room _ (snd (fst (PjGrammar.jbind ?m ?k []))) =>
          destruct (vv_jbind_tr _ _ m k []) as (t2 & Et2) end.
        rewrite Et2 in HROOM. rewrite PjGrammar.jr_value_fuel in HROOM by exact HFUEL.
        exact (vv_room_prefix _ _ t2 HROOM). }
      (* the slot is apart from the text *)
      assert (Htx : ie_text E + ie_len E <= dS \/ dS + 56 <= ie_text E).
      { destruct (Z_le_gt_dec (ie_text E + ie_len E) dS) as [H1 | H1]; [left; exact H1|].
        destruct (Z_le_gt_dec (dS + 56) (ie_text E)) as [H2 | H2]; [right; exact H2|].
        exfalso.
        assert (Hx : ip_kids P - cf_head <= Z.max dS (ie_text E) < ip_kids P + 56 * ip_cap P).
        { lia. }
        destruct (HkX (Z.max dS (ie_text E)) Hx) as (_ & _ & H3). apply H3.
        pose proof HEN as (_ & _ & _ & _ & (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & HpE & _) & _) & Hplt & _).
        lia. }
      refine (HPV (ip_fx P) (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ms_regs ms) (ip_mem P)
                mdc ch1 (ie_e E + 144) (ie_q E) (ie_text E) (ie_len E) (ip_p P) (ie_tb E) dS
                (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P) (ie_most E) (ie_own E)
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
      + (* fpre: the entry pre, the read-only view, the stack top, the return pc below the ceiling (the closed slot
           lemma) and the float state's frm_zero (vrd_ijrn's) *)
        split; [exact HPRE|]. split; [exact HRODc|]. split; [exact HSHIc|].
        unfold raZ. rewrite Q1. split; [exact vv_ret_slot_ceil | exact HFZ].
      + (* the text's memnorm entry premise (PRH_FnParse.v:181), from the invariant at the call (srr_inv_mn) *)
        exact (PMN _ HPM).
      + unfold raZ. rewrite Q1. pose proof (@pa_B_ok _ _ PI_prog_A) as HBok.
        rewrite unsigned_lit_small by lia. rewrite Hsp1.
        exact (HIRET 6164%nat ltac:(cbn; tauto)).
      + exact HCLOS.
      + exact HCENc.
      + (* the cursor set at the call (the kit's cut, PRH_FnParse.v:279), vrd_reader_call_pre's *)
        exact HCWc.
      + exists ch1. split; [rewrite Hs0q; exact Hch1 | reflexivity].
      + right. split; [lia|]. exists ch1. unfold prh_s0. rewrite H_s0s, Z.add_0_r. exact Hch1.
      + exact Hq10.
      + exact HdS.
      + split; [exact HFZ|]. split; [exact HMU|]. split; [exact HUN1|]. split; [exact HUN2|].
        split; [replace (Z.of_nat (S (ie_d E))) with (Z.of_nat (ie_d E) + 1) by lia; exact HIN|].
        split; [exact HFWc|]. split; [lia|]. split; [exact Hq24c|]. split; [exact HRAq|].
        split; [exact HSRC|]. split; [exact HHOME|]. split; [exact HMAXR|].
        split.
        { split; [lia|]. split; [lia|]. split.
          { split; [lia|]. intros x Hx. apply HRW. lia. }
          split; [exact HZ|]. split.
          { left. exists (ip_kids P), (56 * ip_cap P). split; [exact HLk | lia]. }
          split.
          { unfold in_app, amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia. }
          split.
          { intros a Ha. split; [exact (proj2 (HkPres a ltac:(lia)))|]. lia. }
          intros x Hx. apply (HRAk Hcpos). lia. }
        split; [right; lia|]. split; [intros _; exact Htx|]. split; [left; lia|].
        split; [exact HLED|]. split; [lia|]. split; [exact HCNT|]. exact HTXC.
      + exact HROOMv.
      + (* the wild room at the call state (the kit's cut, PRH_FnParse.v:302), from the entry's along the journal at the
           budget CW (VrdIElem.vrd_wild_room_at) *)
        exact (vrd_wild_room_at B ARx SK CTXv CTX0v CWv E Pc HEN HJNc).
      + (* the live counts at parse_value's inner calls, from the entry's along the call's granted events *)
        eapply Z.le_trans; [| exact HSEC0]. apply Nat2Z.inj_le. rewrite Hgt.
        exact (vi_pk_mid _ (ie_S E) (ip_S P) (ip_tr P) _ more HLV0).
      + eapply Z.le_trans; [| exact H240]. apply Nat2Z.inj_le. rewrite Hgt.
        exact (vi_pk_mid _ (ie_S E) (ip_S P) (ip_tr P) _ more HLV0).
      + (* the hull budget at parse_value's all-granted events: the entry's, past the events so far
           (PresetHullBudget.hull_budget_infix over the call's all-granted events split at the call) *)
        pose proof HHB as HHB'. rewrite Hgt, !PresetHullBudget.hull_rd_app in HHB'.
        exact (PresetHullBudget.hull_budget_infix (ie_S E) (ip_S P) _ _ _ HHB' HHU0).
      + rewrite (vv_maxd_succ (ie_d E) Hd). exact HFRB.
    - intros a Ha. destruct Ha as (r & Hin & Hr). cbn [rd_fp In] in Hin.
      destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
      + left. exists (ie_q E, ie_q E + 8). split; [left; reflexivity | cbn [fst snd]; lia].
      + left. exists (ie_q E + 16, ie_q E + 20). split; [right; left; reflexivity | cbn [fst snd]; lia].
      + right. left. exists (ip_kids P - cf_head), (56 * ip_cap P + cf_head). split; [exact HkAB|].
        split; [exact HkE|]. rewrite Hreq. lia. }
  intros W' c' Hwle (fx2 & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ2 & HFK2 & HWB & HJ2 & HJ1 &
                     HWIN1 & HPR2 & HQ2 & HPM2).
  rewrite EQm in HJ1, HWIN1.
  cbn [cfg_ms ms_mem] in HPM2.
  destruct HQ2 as (ok & res & tr & okr0 & D & Lam' & peak' & cnt' & fail' & ran' & Hjv & HLED2 & HRL2 & HHU2 &
                   HLV2 & HXF2 & HOC2 & HIJ2 & HLM2 & HBM2 & HBB2 & HLS2 & HRES).
  set (Pr := MkIPos fx2 ly2 S2 Hp2 W' regs2 mem2 md2 (ip_k P + k1) (ip_n P) (ip_cap P) (ip_kids P) (ip_keys P)
               (ip_p P) (ip_acc P) (ip_f P) (ip_cont P) (ip_ok P ++ ok) (ip_tr P ++ tr) (ip_D P ++ D)
               Lam' peak' cnt' fail' ran').
  pose proof HBM2 as (HBn2 & HBp2 & HBf2 & _).
  assert (Hincl : forall b, In b (ablocks B (ip_ly P) (ip_S P)) -> In b (ablocks B ly2 S2))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HBp2)); apply in_or_app; right; exact Hb).
  (* the frame, the registers, the journal and the byte keep at Pr, by vrd_pos_after_call *)
  pose proof HLM as (_ & _ & _ & HLMp & _).
  pose proof HLM2 as (_ & _ & _ & HLMp2 & _).
  assert (HPERM : Permutation Lam' ((ip_D P ++ D) ++ ie_Lam E)).
  { eapply perm_trans; [exact HLMp2|]. eapply perm_trans; [apply Permutation_app_head; exact HLMp|].
    rewrite app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
  destruct (vrd_pos_after_call (fx := fx) B ARx SK LAWS H_pst_ro CTXv CTX0v CWv E Pc Pr
              (STK_parse_value (S (ie_d E)) + (ie_e E + 144)) (rd_fp (ie_q E) dS) k1 WS1 D tr Himg1 Himg2 HEN HFRc
              (vc_iregs_pres B E P Pc HRG HKR) HJNc)
    as (HFRr & HRGr & HJNr & HKEEP).
  { intros a (r & Hin & Hr). cbn [rd_fp In] in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; [left; lia | right; left; lia | right; right; lia]. }
  { exact HJ1. }
  { intros a Ha Hn. apply HWIN1; [lia | exact Hn]. }
  { exact HPR2. }
  { exact HJ2. }
  { exact HWB. }
  { exact HFZ2. }
  { exact HFK2. }
  { exact HBn2. }
  { exact HBp2. }
  { exact HBf2. }
  { reflexivity. }
  { reflexivity. }
  { exact (vv_hpeak_call CTXv CTX0v CWv E P nm ok res tr okr0 HEN HMD Hcont Hjv). }
  pose proof HJNr as (_ & _ & _ & _ & _ & HBMr & _).
  (* the facts no journal keeps, by IelemE's lemmas *)
  assert (HICr : src_rd W' mem2 (ie_text E) (ie_tb E) /\
                 prhReader_home B ly2 S2 Hp2 Lam' (ie_text E) (ie_len E) /\
                 range_addressable (aview SEGS (w_H W') mem2) SHADOW_OFF (ie_q E) 24)
    by (eapply (vrd_icur_after_call (fx := fx)); eauto).
  destruct HICr as (HSRCr & HHOMEr & HRAqr).
  assert (HRAvr : range_addressable (aview SEGS (w_H W') mem2) SHADOW_OFF (ie_v E) 56)
    by (eapply (vrd_node_ra_after_call (fx := fx)); eauto).

  assert (HLamIn : forall a k, In (a, k) (ip_Lam P) -> In (a, k) Lam')
    by (intros a k Hin; apply (Permutation_in _ (Permutation_sym HLMp2)); apply in_or_app; right; exact Hin).
  pose proof (vrd_node_low B ARx HL LAWS CTXv CTX0v CWv E HEN) as Hvceil.
  assert (HSTKpi : 144 <= STK_parse_items (ie_d E)) by (pose proof (vv_stk_items (ie_d E)); unfold ESTACK in *; lia).
  rewrite EdS in HKEEP, HRES.
  assert (HHDRr : pj_hdrR SEGS (mrestrict (w_H W') mem2) (ie_v E) (if ie_o E then 6 else 5) 0 0
                    (ip_kids P) (ip_keys P) (ip_n P) (ip_cap P)).
  { apply (pj_hdrR_keep SEGS _ _ _ _ _ _ _ _ _ _ HHDR). eapply rd_keep_mono; [exact HKEEP|].
    intros a Ha. split; [|left; exact Ha].
    intros (r & Hin & Hr). cbn [rd_fp In] in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; [lia | lia |].
    apply (HDAP (ip_kids P, 56 * ip_cap P) a HinD); [unfold pj_holdsR; cbn [fst snd]; lia | exact Ha]. }
  assert (HART2 : ARx ly2 S2 Hp2 W' mem2 md2) by exact (proj1 HJ2).
  assert (HRAkr : 0 < ip_cap P ->
            range_addressable (aview SEGS (w_H W') mem2) SHADOW_OFF (ip_kids P) (56 * ip_cap P)).
  { intros Hc. destruct (Hlin Hc) as (HL1 & _). pose proof (HLamIn _ _ HL1) as Hin2.
    eapply proj1. eapply vrd_lam_shadow; eauto. }
  assert (HRAyr : ie_o E = true -> 0 < ip_cap P ->
            range_addressable (aview SEGS (w_H W') mem2) SHADOW_OFF (ip_keys P) (8 * ip_cap P)).
  { intros Ho Hc. destruct (Hlin Hc) as (_ & HL2). pose proof (HLamIn _ _ (HL2 Ho)) as Hin2.
    eapply proj1. eapply vrd_lam_shadow; eauto. }
  assert (HSET : vv_set E P nm) by (split; [exact HI | rewrite <- EdS; exact HZ]).
  refine (vv_after_call E P nm Pr ok res tr okr0 D HEN HSET eq_refl eq_refl eq_refl eq_refl eq_refl
            eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HFRr HRGr HJNr HHDRr HKEEP
            Hjv HLED2 HRL2 HHU2 HLV2 HXF2 HOC2 HIJ2 HLM2 HBM2 HBB2 HLS2 HRES HSRCr HHOMEr HRAqr HRAvr HRAkr HRAyr HPM2).
Qed.


(* ==== PART C: rows 238..264, sub-lane IvalR (IvalR_C.v), Qed ==== *)

(* ==== PART C: the white-space scan after the value, rows 238..264 ==== *)

Definition vv_EO (regs : bvmap 5 word) (p e : Z) : env :=
  @Eimg _ A_prog_listing PAI (Ereg regs [w64 p; w64 e]).
Definition vv_sr0 : list sv := sr_set (sr_set sr_atoms 23%bv (vv_sh 8 8)) 27%bv (vv_sh 8 0).
Definition vv_cur (w : bool) : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 24 0 (if w then 8 else 0)
    [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition vv_facts0 : facts :=
  mkFacts [ (8%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (32%nat, mkAF 0 (2 ^ 62) 0); (33%nat, mkAF 0 (2 ^ 62) 0) ] [] [].
Definition vv_SH0 : list shent := [mkSHE 8 0 24].
Definition vv_ss0 (k : nat) : sstate := mkSS (4 * Z.of_nat k) vv_sr0 [vv_cur false] None vv_facts0.

Lemma vv_seat0 : forall (fxP : YK11.FPState) (W : world SEGS) regs mem q p en (k : nat),
  getr regs 8 = w64 q -> getr regs 26 = w64 SHADOW_OFF ->
  getr regs 23 = w64 (shadow_addr (q + 8)) -> getr regs 27 = w64 (shadow_addr q) ->
  2 ^ 46 <= q -> q + 24 <= 2 ^ 47 -> q mod 8 = 0 ->
  val_mem SEGS (mrestrict (w_H W) mem) q 8 p -> val_mem SEGS (mrestrict (w_H W) mem) (q + 8) 8 en ->
  0 <= p <= 2 ^ 62 -> 0 <= en <= 2 ^ 62 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF q 24 ->
  st_ok_pi (fx := fxP) SEGS VAL (vv_EO regs p en) (vv_ss0 k)
    (restrict (w_H W) (@YK11.mkst fxP regs (w64 (A_IPC k)) mem (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS (SOff 26 0) vv_SH0 (vv_EO regs p en) (mrestrict (w_H W) mem).
Proof.
  intros fxP W regs mem q p en k R8 R26 R23 R27 Hq1 Hq2 Hq8 Vp Ve Hp He Hra.
  set (EO := vv_EO regs p en).
  assert (EL : forall j, (j < 32)%nat -> forall r : bv 5, Z.of_nat j = bv_unsigned r -> ew EO j = getr regs r).
  { intros j Hj r Hr. unfold EO, vv_EO. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat regs _ j r Hr). }
  assert (E8 : ew EO 8 = w64 q) by (rewrite (EL 8%nat ltac:(lia) 8%bv eq_refl); exact R8).
  assert (E26 : ew EO 26 = w64 SHADOW_OFF) by (rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl); exact R26).
  assert (E32 : ew EO 32 = w64 p).
  { unfold EO, vv_EO. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
  assert (E33 : ew EO 33 = w64 en).
  { unfold EO, vv_EO. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (U8 : bv_unsigned (ew EO 8) = q) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew EO 26) = SHADOW_OFF)
    by (rewrite E26; unfold w64, SHADOW_OFF; apply unsigned_lit_small; lia).
  assert (Uq : U EO (SOff 8 0) = q) by (rewrite U_SOff, U8, Z.add_0_r; apply zcanon_id; unfold M64; lia).
  assert (UB : U EO (SOff 26 0) = SHADOW_OFF)
    by (rewrite U_SOff, U26, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
  split.
  - rewrite (restrict_mkst_fx (fx := fxP)).
    change (w64 (A_IPC k)) with (Z_to_bv 64 (BASE + 4 * Z.of_nat k)).
    unfold vv_ss0. apply (pa_entry_st_ok_full (fx := fxP)).
    + unfold vv_sr0. apply vv_regs_ok_set; [apply vv_regs_ok_set; [apply regs_ok_Eimg_Ereg|]|].
      * rewrite R23, denot_lit_U, (vv_sh_U EO 8 8 q U8 U26) by lia. reflexivity.
      * rewrite R27, denot_lit_U, (vv_sh_U EO 8 0 q U8 U26) by lia. rewrite Z.add_0_r. reflexivity.
    + reflexivity.
    + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, vv_cur.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U8.
      split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS EO _ q 0 8 (SOff 32 0) p);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
          | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact Vp.
      * apply (chunk_ok_val SEGS EO _ q 8 8 (SOff 33 0) en);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
          | cbn; lia | cbn; lia |].
        exact Ve.
    + cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
    + split; [|split; [exact I | exact I]].
      cbn [vv_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E8, E26, E32, E33. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - unfold sh_ok, vv_SH0. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W) mem EO (SOff 26 0) 8 q 24 q 0 24 Hra UB Uq); [lia | lia |].
    intros x Hx. unfold SHADOW_OFF in *. lia.
Qed.

(* ---- pure facts: the rest of the text, white space (a Theorem Labs lane's IproC VrdIPro.v, restated) ---- *)
Lemma vv_rest_cons : forall tb text p, text <= p -> (Z.to_nat (p - text) < length tb)%nat ->
  rest_atR tb text p = nth (Z.to_nat (p - text)) tb 0 :: rest_atR tb text (p + 1).
Proof.
  intros tb text p H1 H2. unfold rest_atR.
  replace (Z.to_nat (p + 1 - text)) with (S (Z.to_nat (p - text))) by lia.
  revert H2. generalize (Z.to_nat (p - text)) as k. clear. induction tb as [|b r IH]; intros [|k] Hk; cbn in *; try lia.
  - reflexivity.
  - apply IH. lia.
Qed.

Lemma vv_rest_end : forall tb text p, Z.of_nat (length tb) <= p - text -> rest_atR tb text p = [].
Proof. intros tb text p H. unfold rest_atR. apply skipn_all2. lia. Qed.

Lemma vv_skip_ws : forall b r, PjGrammar.ws b = true -> PjGrammar.skip (b :: r) = PjGrammar.skip r.
Proof. intros b r H. cbn [PjGrammar.skip]. rewrite H. reflexivity. Qed.

Lemma vv_skip_nws : forall b r, PjGrammar.ws b = false -> PjGrammar.skip (b :: r) = b :: r.
Proof. intros b r H. cbn [PjGrammar.skip]. rewrite H. reflexivity. Qed.

Lemma vv_ws_32 : forall b, 32 < b -> PjGrammar.ws b = false.
Proof.
  intros b H. unfold PjGrammar.ws.
  repeat match goal with |- context [Z.eqb ?a ?c] => destruct (Z.eqb_spec a c); [lia|] end. reflexivity.
Qed.

(* rows 56..58 of the prologue build the mask in s9, whose set bits 9, 10, 13 and 32 are PjGrammar.ws *)
Lemma vv_mask_ws : forall b, 0 <= b <= 32 ->
  Z.land (Z.shiftr 4294977024 (b mod 64)) 1 = (if PjGrammar.ws b then 1 else 0).
Proof.
  intros b Hb.
  assert (Hall : forallb (fun x => Z.eqb (Z.land (Z.shiftr 4294977024 (x mod 64)) 1)
                                         (if PjGrammar.ws x then 1 else 0))
                         (map Z.of_nat (seq 0 33)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall.
  apply Z.eqb_eq, Hall, in_map_iff. exists (Z.to_nat b).
  split; [lia | apply in_seq; lia].
Qed.

(* ---- the cursor's position bounds ---- *)
Lemma vv_q_bounds : forall CTX CTX0 CW E, vrd_ient_ok B ARx CTX CTX0 CW E ->
  2 ^ 46 <= ie_q E /\ ie_q E + 24 <= 2 ^ 47.
Proof.
  intros CTX CTX0 CW E HEN.
  destruct HEN as ((HAF & _) & _ & _ & _ & HRD & _).
  destruct HAF as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & HS0 & Hceil & Hslo & _ & H47 & _ & _ & Htop).
  destruct HRD as (_ & _ & _ & _ & _ & (He0 & _ & Hetop & _) & Hq0 & Hq24 & _).
  pose proof asan_consts as (C1 & _).
  split; lia.
Qed.

(* a run over the read-only cursor seat writes nothing *)
Lemma vv_frame_ro0 : forall E' (m m' : word -> option byte), frame_of E' [vv_cur false] m m' -> forall x, m' x = m x.
Proof.
  intros E' m m' HF x. apply HF. intros (r & Hin & Hr). destruct Hin as [<- | []].
  cbn [vv_cur YP09.r_wlo YP09.r_whi] in Hr. lia.
Qed.

(* the live registers after a run: the atoms are kept, and s7 / s11 keep their seated shadow expressions *)
Definition vv_live : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma vv_regs_after : forall (fxP : YK11.FPState) (H : word -> bool) E' ss ms regs0 extra,
  st_ok_pi (fx := fxP) SEGS VAL E' ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E' ->
  sr_get (ss_regs ss) 23%bv = vv_sh 8 8 -> sr_get (ss_regs ss) 27%bv = vv_sh 8 0 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26]%bv = true ->
  getr regs0 23 = sv_denot E' (vv_sh 8 8) -> getr regs0 27 = sv_denot E' (vv_sh 8 0) ->
  forall r, In r vv_live -> getr (ms_regs ms) r = getr regs0 r.
Proof.
  intros fxP H E' ss ms regs0 extra HS HA H23 H27 Hl R23 R27 r Hr.
  pose proof (st_ok_pi_restrict_reg (fx := fxP) H E' ss ms r HS) as Hg.
  assert (HK : forall r', In r' [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26]%bv -> getr (ms_regs ms) r' = getr regs0 r')
    by exact (regs_kept_of_st_ok_pi (fx := fxP) E' ss (restrict H ms) regs0 extra
                [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26]%bv HS HA Hl).
  unfold vv_live in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ first [ rewrite H23 in Hg; rewrite Hg; symmetry; exact R23
            | rewrite H27 in Hg; rewrite Hg; symmetry; exact R27
            | apply HK; cbn; tauto ] |]).
  destruct Hr.
Qed.

(* a region of a symbolic state holds in the machine memory *)

(* ---- the cursor after a store confined to q->p ---- *)
Lemma vv_pin_keep : forall (H : word -> bool) (m m' : word -> option byte) q text len p p' d tb,
  pj_in_okR SEGS (mrestrict H m) q text len p d tb -> 0 <= q -> q + 24 <= 2 ^ 64 ->
  (forall x : word, ~ (q <= bv_unsigned x < q + 8) -> mrestrict H m' x = mrestrict H m x) ->
  val_mem SEGS (mrestrict H m') q 8 p' ->
  (forall a, q <= a < q + 8 -> writable_at SEGS (mrestrict H m') a) ->
  text <= p' <= text + len ->
  pj_in_okR SEGS (mrestrict H m') q text len p' d tb.
Proof.
  intros H m m' q text len p p' d tb (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & Hg & Hqt & Hd)
    Hq0 Hq64 HK Vp' Hw Hp'.
  assert (HKr : forall Pz, (forall a, Pz a -> 0 <= a < 2 ^ 64 /\ ~ (q <= a < q + 8)) ->
            rd_keep SEGS (mrestrict H m) (mrestrict H m') Pz)
    by (intros Pz HP; exact (vk_keep_rd H m m' q (q + 8) Pz HK HP)).
  unfold pj_in_okR.
  split; [exact Vp'|].
  split; [eapply val_mem_keep; [exact Ve | apply HKr; intros a Ha; cbn in Ha; lia]|].
  split; [eapply val_mem_keep; [exact Vd | apply HKr; intros a Ha; cbn in Ha; lia]|].
  split.
  { intros x Hx. destruct (Z_lt_le_dec x (q + 8)) as [Hl | Hl]; [apply Hw; lia|].
    destruct (HKr (fun a => q + 8 <= a < q + 24) ltac:(intros a Ha; cbv beta in Ha; lia)) as [_ HW2].
    apply HW2; [lia | apply Hrw; lia]. }
  split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Htl|]. split; [lia|]. split; [exact Hlen|].
  split; [eapply garr8_keep; [exact Hg | apply HKr; intros a Ha; cbv beta in Ha; lia]|].
  exact (conj Hqt Hd).
Qed.

Lemma vv_pin_same : forall (H : word -> bool) (m m' : word -> option byte) q text len p d tb,
  pj_in_okR SEGS (mrestrict H m) q text len p d tb -> 0 <= q -> q + 24 <= 2 ^ 64 ->
  (forall x : word, mrestrict H m' x = mrestrict H m x) ->
  pj_in_okR SEGS (mrestrict H m') q text len p d tb.
Proof.
  intros H m m' q text len p d tb Hin Hq0 Hq64 HK.
  assert (HKr : forall Pz, (forall a, Pz a -> 0 <= a < 2 ^ 64) -> rd_keep SEGS (mrestrict H m) (mrestrict H m') Pz)
    by (intros Pz HP; apply (vk_keep_rd H m m' 0 0); [intros x _; apply HK | intros a Ha; split; [apply HP; exact Ha | lia]]).
  pose proof Hin as (Vp & _ & _ & Hrw & _ & _ & _ & Hpp & _).
  apply (vv_pin_keep H m m' q text len p p d tb Hin Hq0 Hq64); [intros x _; apply HK | | | lia].
  - eapply val_mem_keep; [exact Vp | apply HKr; intros a Ha; cbn in Ha; lia].
  - intros a Ha. destruct (HKr (fun x => q <= x < q + 8) ltac:(intros x Hx; cbv beta in Hx; lia)) as [_ HW2].
    apply HW2; [exact Ha | apply Hrw; lia].
Qed.

(* THE KIT'S CUT: THE BATCH KIT'S LAYER ACROSS A STEP THAT CHANGES NO BYTE OF THE POSITION'S BLOCKS (the cursor's own words: the
   white-space scan, the separator test): VrdIFd.vrd_k1_keep with its block-byte keep given and the position's own
   ledger, which holds its blocks (vrd_imodel's ledger move) *)
Lemma vv_k1_hi : forall E P P2 af,
  vrd_imodel E P -> vrd_inode E P [] -> vrd_incaps E P -> vrd_iforder E P [] af ->
  ip_kids P2 = ip_kids P -> ip_keys P2 = ip_keys P -> ip_n P2 = ip_n P -> ip_cap P2 = ip_cap P ->
  ip_acc P2 = ip_acc P -> ip_D P2 = ip_D P -> ip_Lam P2 = ip_Lam P ->
  rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (rd_blk (ip_D P)) ->
  vrd_incaps E P2 /\ vrd_iforder E P2 [] af.
Proof.
  intros E P P2 af HMD HND HNC HFO Ek Ey En Ec Ea ED EL HK.
  pose proof HMD as (_ & _ & HLM & _).
  pose proof HLM as (_ & _ & _ & HLp & _).
  apply (vrd_k1_keep E P P2 [] af Ek Ey En Ec Ea ED); [| exact HK | exact HND | exact HNC | exact HFO].
  intros x k Hin. rewrite EL. unfold prh_lin. apply (Permutation_in _ (Permutation_sym HLp)).
  apply in_or_app. left. exact Hin.
Qed.

(* ---- a loop position moved to a new machine state and a cursor whose skipped rest is the same ---- *)
Lemma vv_move_sep : forall CTX CTX0 CW E P regs' mem' md' p',
  vrd_ient_ok B ARx CTX CTX0 CW E -> vv_sep E P ->
  (forall r, In r vv_live -> getr regs' r = getr (ip_regs P) r) ->
  (forall x : word, ~ (ie_q E <= bv_unsigned x < ie_q E + 8) ->
     mrestrict (w_H (ip_W P)) mem' x = mrestrict (w_H (ip_W P)) (ip_mem P) x) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
    (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem' md' (ip_k P) (ie_CW E) ->
  pj_in_okR SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E) (ie_text E) (ie_len E) p' (Z.of_nat (ie_d E) + 1)
    (ie_tb E) ->
  (length (rest_atR (ie_tb E) (ie_text E) p') <= length (rest_atR (ie_tb E) (ie_text E) (ip_p P)))%nat ->
  PjGrammar.skip (rest_atR (ie_tb E) (ie_text E) p') = PjGrammar.skip (rest_atR (ie_tb E) (ie_text E) (ip_p P)) ->
  vv_sep E (vk_move P regs' mem' md' (ip_k P) p').
Proof.
  intros CTX CTX0 CW E P regs' mem' md' p' HEN HSEP HR HK HJ' Hpin' Hlen Hsk.
  destruct HSEP as (HFR & HRG & HND & HCU & HJN & HMD & Hn0 & Hcont & HK1s).
  pose proof H_img as (Himg1 & Himg2 & _).
  destruct (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  pose proof asan_consts as (C1 & _).
  assert (Hsp : spZ regs' = spZ (ip_regs P)) by (unfold spZ; rewrite (HR 2%bv ltac:(cbn; tauto)); reflexivity).
  destruct (vk_cur_store_keep B ARx SK LAWS (proj1 H_head) H_pst CTX CTX0 CW E P [] regs' mem' md' (ip_k P) p'
              (ie_q E) 8 Himg1 Himg2 HEN HFR HND HCU HJN ltac:(lia) ltac:(lia) ltac:(lia)) as (F1 & F2 & F3 & F4).
  - intros a Ha. exists (ie_q E, ie_q E + 8). split; [left; reflexivity | cbn [fst snd]; lia].
  - intros a Ha Hf. lia.
  - exact HK.
  - exact Hsp.
  - exact HJ'.
  - exact Hpin'.
  - exact Hlen.
  - split; [exact F1|].
    split.
    { unfold vrd_iregs in *. unfold vk_move; cbn [ip_regs]. rewrite !HR by (cbn; tauto). exact HRG. }
    split; [exact F2|]. split; [exact F3|]. split; [exact F4|].
    split.
    { destruct HMD as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
      unfold vrd_imodel. unfold vk_move.
      cbn [ip_ok ip_tr ip_cont ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran ip_S ip_p ip_f ip_acc].
      split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
      split; [lia|]. exact (conj M6 (conj M7 M8)). }
    split; [exact Hn0|].
    split.
    { unfold vk_move; cbn [ip_cont ip_n ip_cap ip_acc ip_f ip_p]. rewrite Hcont. unfold vrd_jsep. rewrite Hsk.
      reflexivity. }
    (* The kit's cut: the batch kit's layer - the store missed every block of the position (they lie below alloc_ceiling) *)
    destruct HK1s as (HCAP & HNC & (af & HFO & HFL)).
    destruct (vv_D_apart CTX CTX0 CW E P HEN HJN HCU HMD) as (_ & HDB & _ & _).
    destruct (vv_k1_hi E P (vk_move P regs' mem' md' (ip_k P) p') af HMD HND HNC HFO eq_refl eq_refl eq_refl
                eq_refl eq_refl eq_refl eq_refl) as (HNC2 & HFO2).
    { apply (vk_keep_rd _ (ip_mem P) mem' (ie_q E) (ie_q E + 8) _ HK). intros z Hz.
      unfold rd_blk in Hz. apply Exists_exists in Hz as ([a k] & Hin & Hr). unfold pj_holdsR in Hr.
      cbn [fst snd] in Hr. destruct (HDB a k Hin) as (Hk & _ & H4 & Hc & _). pose proof (@cf_head_nonneg cp). lia. }
    unfold vv_k1sep. refine (conj HCAP (conj HNC2 (ex_intro _ af (conj HFO2 _)))).
    intros okr. unfold vk_move; cbn [ip_ok ip_f ip_n ip_cap ip_p]. rewrite (HFL okr). unfold vrd_jfsep. rewrite Hsk.
    reflexivity.
Qed.

(* ==== C1: rows 238..245, the shadow gates of q + 8 and q, the loads of p and end, `bgeu p, end` ==== *)
Lemma vv_partC1 : forall CTX CTX0 CW E P,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vv_sep E P -> Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_ISEP_SLOT P)
    (fun W2 c2 => ((exists P', W2 = ip_W P' /\ c2 = vrd_cfg A_IWSL_SLOT P' /\ ip_n P' = ip_n P /\ vv_wsl E P') \/
                   (exists P', W2 = ip_W P' /\ c2 = vrd_cfg A_ITAIL_SLOT P' /\ ip_n P' = ip_n P /\ vv_tail E P')) /\
                  Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P HEN HSEP HPM.
  pose proof HSEP as (HFR & HRG & HND & HCU & HJN & HMD & Hn0 & Hcont & HK1s).
  pose proof (vrd_ijrn_base B ARx SK E P HJN) as HJ.
  destruct (vv_q_bounds CTX CTX0 CW E HEN) as [Hq1 Hq2].
  pose proof HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof HCU as (Hin & Hraq & _).
  pose proof Hin as (Vp & Ve & _ & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & _).
  assert (Hp62 : 0 <= ip_p P <= 2 ^ 62) by lia.
  assert (He62 : 0 <= ie_text E + ie_len E <= 2 ^ 62) by lia.
  destruct (vv_seat0 (ip_fx P) (ip_W P) (ip_regs P) (ip_mem P) (ie_q E) (ip_p P) (ie_text E + ie_len E)
              A_ISEP_SLOT G8 G26 G23 G27 Hq1 Hq2 Hq8 Vp Ve Hp62 He62 Hraq) as [HS SHOK].
  set (EO := vv_EO (ip_regs P) (ip_p P) (ie_text E + ie_len E)) in *.
  assert (HEI : img_env VAL A_LIM EO) by (unfold EO, vv_EO; apply Eimg_env).
  assert (E32 : ew EO 32 = w64 (ip_p P)).
  { unfold EO, vv_EO. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 0). }
  assert (E33 : ew EO 33 = w64 (ie_text E + ie_len E)).
  { unfold EO, vv_EO. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 1). }
  assert (HA : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E)]) EO)
    by (split; [intros j Hj; unfold EO, vv_EO; rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia); reflexivity
               | reflexivity]).
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 23%bv HS) as R23. cbn [ms_regs restrict mkst] in R23.
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 27%bv HS) as R27. cbn [ms_regs restrict mkst] in R27.
  change (sr_get (ss_regs (vv_ss0 A_ISEP_SLOT)) 23%bv) with (vv_sh 8 8) in R23.
  change (sr_get (ss_regs (vv_ss0 A_ISEP_SLOT)) 27%bv) with (vv_sh 8 0) in R27.
  destruct (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  pose (RUN := paj_run_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (RUNTO := paj_run_to_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (BR := paj_branchR (fx := ip_fx P) (PI := PAI) (wle' SEGS YGcfRehidePost.RZ_cf)).
  unfold vrd_cfg.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vi_Bspan; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|].
  match goal with H : frame_of _ _ (ip_mem P) _ |- _ => rename H into HF1 end.
  match goal with ms0 : machine_state |- _ => rename ms0 into ms1 end.
  pose proof (vv_frame_ro0 _ _ _ HF1) as HM1.
  psrr_branch_tok RUN BR HS SHOK vi_Bspan.
  - (* p >= end: on to the separator test with p = end *)
    match goal with H : branch_taken _ _ _ = true |- _ => rename H into Hb end.
    assert (Hpe : ip_p P = ie_text E + ie_len E).
    { rewrite branch_geu_U, (U_atom EO 32 (ip_p P) E32), (U_atom EO 33 _ E33) in Hb by lia.
      apply Bool.negb_true_iff, Z.ltb_ge in Hb. lia. }
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vi_Bspan (4 * Z.of_nat A_ITAIL_SLOT);
      [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|].
    match goal with H : frame_of _ _ (ms_mem ms1) _ |- _ => rename H into HF2 end.
    match goal with ms0 : machine_state |- _ => lazymatch ms0 with ms1 => fail | _ => rename ms0 into ms2 end end.
    pose proof (vv_frame_ro0 _ _ _ HF2) as HM2.
    assert (HRk : forall r, In r vv_live -> getr (ms_regs ms2) r = getr (ip_regs P) r).
    { eapply (vv_regs_after _ _ _ _ _ _ _ HS HA); [reflexivity | reflexivity | vm_compute; reflexivity | exact R23 | exact R27]. }
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 11%bv HS) as R11.
    match type of R11 with _ = sv_denot _ (sr_get ?l _) =>
      let v := eval vm_compute in (sr_get l 11%bv) in change (sr_get l 11%bv) with v in R11 end.
    cbn [sv_denot] in R11. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in R11. rewrite E33 in R11.
    cbn [ms_regs restrict] in R11.
    assert (HKm : forall x : word, mrestrict (w_H (ip_W P)) (ms_mem ms2) x = mrestrict (w_H (ip_W P)) (ip_mem P) x)
      by (intros x; unfold mrestrict; rewrite HM2, HM1; reflexivity).
    pmkst HS.
    lazymatch goal with |- SRrG _ _ _ (mkCfg _ ?md) _ => set (md2 := md) in * end.
    apply SRr'_ret. split; [|exact HPM]. right.
    exists (vk_move P (ms_regs ms2) (ms_mem ms2) md2 (ip_k P) (ip_p P)).
    split; [reflexivity|]. split; [unfold vrd_cfg, vk_move; cbn [ip_fx ip_regs ip_mem ip_md]; reflexivity|].
    split; [reflexivity|].
    split; [|split].
    + apply (vv_move_sep CTX CTX0 CW E P (ms_regs ms2) (ms_mem ms2) md2 (ip_p P) HEN HSEP HRk
               (fun x _ => HKm x) (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ)).
      * exact (vv_pin_same _ _ _ _ _ _ _ _ _ Hin ltac:(lia) ltac:(lia) HKm).
      * apply Nat.le_refl.
      * reflexivity.
    + exact R11.
    + unfold vk_move; cbn [ip_p]. rewrite Hpe, vv_rest_end by lia. reflexivity.
  - (* p < end: `mv a0, a2` to the loop head *)
    match goal with H : branch_taken _ _ _ = false |- _ => rename H into Hb end.
    assert (Hpe : ip_p P < ie_text E + ie_len E).
    { rewrite branch_geu_U, (U_atom EO 32 (ip_p P) E32), (U_atom EO 33 _ E33) in Hb by lia.
      apply Bool.negb_false_iff, Z.ltb_lt in Hb. exact Hb. }
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vi_Bspan (4 * Z.of_nat A_IWSL_SLOT);
      [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|].
    match goal with H : frame_of _ _ (ms_mem ms1) _ |- _ => rename H into HF2 end.
    match goal with ms0 : machine_state |- _ => lazymatch ms0 with ms1 => fail | _ => rename ms0 into ms2 end end.
    pose proof (vv_frame_ro0 _ _ _ HF2) as HM2.
    assert (HRk : forall r, In r vv_live -> getr (ms_regs ms2) r = getr (ip_regs P) r).
    { eapply (vv_regs_after _ _ _ _ _ _ _ HS HA); [reflexivity | reflexivity | vm_compute; reflexivity | exact R23 | exact R27]. }
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 10%bv HS) as R10.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 11%bv HS) as R11.
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 12%bv HS) as R12.
    match type of R10 with _ = sv_denot _ (sr_get ?l _) =>
      let v := eval vm_compute in (sr_get l 10%bv) in change (sr_get l 10%bv) with v in R10;
      let v := eval vm_compute in (sr_get l 11%bv) in change (sr_get l 11%bv) with v in R11;
      let v := eval vm_compute in (sr_get l 12%bv) in change (sr_get l 12%bv) with v in R12 end.
    cbn [sv_denot] in R10, R11, R12. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in R10, R11, R12.
    rewrite E32 in R10, R12. rewrite E33 in R11. cbn [ms_regs restrict] in R10, R11, R12.
    assert (HKm : forall x : word, mrestrict (w_H (ip_W P)) (ms_mem ms2) x = mrestrict (w_H (ip_W P)) (ip_mem P) x)
      by (intros x; unfold mrestrict; rewrite HM2, HM1; reflexivity).
    pmkst HS.
    lazymatch goal with |- SRrG _ _ _ (mkCfg _ ?md) _ => set (md2 := md) in * end.
    apply SRr'_ret. split; [|exact HPM]. left.
    exists (vk_move P (ms_regs ms2) (ms_mem ms2) md2 (ip_k P) (ip_p P)).
    split; [reflexivity|]. split; [unfold vrd_cfg, vk_move; cbn [ip_fx ip_regs ip_mem ip_md]; reflexivity|].
    split; [reflexivity|].
    split.
    + apply (vv_move_sep CTX CTX0 CW E P (ms_regs ms2) (ms_mem ms2) md2 (ip_p P) HEN HSEP HRk
               (fun x _ => HKm x) (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ)).
      * exact (vv_pin_same _ _ _ _ _ _ _ _ _ Hin ltac:(lia) ltac:(lia) HKm).
      * apply Nat.le_refl.
      * reflexivity.
    + unfold vk_move; cbn [ip_regs ip_p]. exact (conj R10 (conj R12 (conj R11 Hpe))).
Qed.

(* ==== C2: the white-space loop, rows 246..264 ==== *)
Definition vv_EW (regs : bvmap 5 word) (p e b : Z) : env :=
  @Eimg _ A_prog_listing PAI (Ereg regs [w64 p; w64 e; w64 b]).
Definition vv_srW : list sv := sr_set (sr_set (sr_set vv_sr0 10%bv (SOff 32 0)) 11%bv (SOff 33 0)) 12%bv (SOff 32 0).
Definition vv_byte : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition vv_factsW : facts :=
  mkFacts [ (8%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (32%nat, mkAF 4096 (2 ^ 47 - 8) 0); (33%nat, mkAF 4096 (2 ^ 47 - 8) 0);
            (34%nat, mkAF 0 255 0) ] [] [].
Definition vv_ssW (k : nat) : sstate := mkSS (4 * Z.of_nat k) vv_srW [vv_cur true; vv_byte] None vv_factsW.

Lemma vv_seatW : forall (fxP : YK11.FPState) (W : world SEGS) regs mem q p en b (k : nat),
  getr regs 8 = w64 q -> getr regs 26 = w64 SHADOW_OFF ->
  getr regs 23 = w64 (shadow_addr (q + 8)) -> getr regs 27 = w64 (shadow_addr q) ->
  getr regs 10 = w64 p -> getr regs 11 = w64 en -> getr regs 12 = w64 p ->
  2 ^ 46 <= q -> q + 24 <= 2 ^ 47 -> q mod 8 = 0 ->
  val_mem SEGS (mrestrict (w_H W) mem) q 8 p -> val_mem SEGS (mrestrict (w_H W) mem) (q + 8) 8 en ->
  4096 <= p <= 2 ^ 47 - 8 -> 4096 <= en <= 2 ^ 47 - 8 ->
  val_mem SEGS (mrestrict (w_H W) mem) p 1 b -> 0 <= b < 256 -> (p + 1 <= q \/ q + 24 <= p) ->
  rd_rw SEGS (mrestrict (w_H W) mem) q 24 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF q 24 ->
  st_ok_pi (fx := fxP) SEGS VAL (vv_EW regs p en b) (vv_ssW k)
    (restrict (w_H W) (@YK11.mkst fxP regs (w64 (A_IPC k)) mem (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS (SOff 26 0) vv_SH0 (vv_EW regs p en b) (mrestrict (w_H W) mem).
Proof.
  intros fxP W regs mem q p en b k R8 R26 R23 R27 R10 R11 R12 Hq1 Hq2 Hq8 Vp Ve Hp He Vb Hb Hdj Hrw Hra.
  set (EW := vv_EW regs p en b).
  assert (EL : forall j, (j < 32)%nat -> forall r : bv 5, Z.of_nat j = bv_unsigned r -> ew EW j = getr regs r).
  { intros j Hj r Hr. unfold EW, vv_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat regs _ j r Hr). }
  assert (E8 : ew EW 8 = w64 q) by (rewrite (EL 8%nat ltac:(lia) 8%bv eq_refl); exact R8).
  assert (E26 : ew EW 26 = w64 SHADOW_OFF) by (rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl); exact R26).
  assert (E32 : ew EW 32 = w64 p).
  { unfold EW, vv_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
  assert (E33 : ew EW 33 = w64 en).
  { unfold EW, vv_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
  assert (E34 : ew EW 34 = w64 b).
  { unfold EW, vv_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2). }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (U8 : bv_unsigned (ew EW 8) = q) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew EW 26) = SHADOW_OFF)
    by (rewrite E26; unfold w64, SHADOW_OFF; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew EW 32) = p) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
  assert (Uq : U EW (SOff 8 0) = q) by (rewrite U_SOff, U8, Z.add_0_r; apply zcanon_id; unfold M64; lia).
  assert (UB : U EW (SOff 26 0) = SHADOW_OFF)
    by (rewrite U_SOff, U26, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
  assert (S32 : sv_denot EW (SOff 32 0) = w64 p).
  { cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (S33 : sv_denot EW (SOff 33 0) = w64 en).
  { cbn [sv_denot]. rewrite E33, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split.
  - rewrite (restrict_mkst_fx (fx := fxP)).
    change (w64 (A_IPC k)) with (Z_to_bv 64 (BASE + 4 * Z.of_nat k)).
    unfold vv_ssW. apply (pa_entry_st_ok_full (fx := fxP)).
    + unfold vv_srW, vv_sr0.
      apply vv_regs_ok_set; [apply vv_regs_ok_set; [apply vv_regs_ok_set;
        [apply vv_regs_ok_set; [apply vv_regs_ok_set; [apply regs_ok_Eimg_Ereg|]|]|]|]|].
      * rewrite R23, denot_lit_U, (vv_sh_U EW 8 8 q U8 U26) by lia. reflexivity.
      * rewrite R27, denot_lit_U, (vv_sh_U EW 8 0 q U8 U26) by lia. rewrite Z.add_0_r. reflexivity.
      * rewrite R10. symmetry. exact S32.
      * rewrite R11. symmetry. exact S33.
      * rewrite R12. symmetry. exact S32.
    + reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * unfold region_ok, vv_cur.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U8.
        split; [lia|]. split; [lia|]. split; [intros a Ha; apply Hrw; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val SEGS EW _ q 0 8 (SOff 32 0) p); [exact S32 | cbn; lia | cbn; lia |].
           rewrite Z.add_0_r. exact Vp.
        -- apply (chunk_ok_val SEGS EW _ q 8 8 (SOff 33 0) en); [exact S33 | cbn; lia | cbn; lia |].
           exact Ve.
      * unfold region_ok, vv_byte.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U32.
        split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS EW _ p 0 1 (SOff 34 0) b);
          [cbn [sv_denot]; rewrite E34, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
          | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact Vb.
    + apply pairwise_disjoint_of_extents. unfold vv_cur, vv_byte, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U8, U32.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [vv_factsW f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E8, E26, E32, E33, E34. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - unfold sh_ok, vv_SH0. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W) mem EW (SOff 26 0) 8 q 24 q 0 24 Hra UB Uq); [lia | lia |].
    intros x Hx. unfold SHADOW_OFF in *. lia.
Qed.

(* the loop's write is confined to the cursor's p word *)
Lemma vv_frame_w : forall E' cs (m m' : word -> option byte) q,
  frame_of E' [YP09.mkRegion (Some 8%nat) 0 24 0 8 cs; vv_byte] m m' -> bv_unsigned (ew E' 8) = q ->
  forall x : word, ~ (q <= bv_unsigned x < q + 8) -> m' x = m x.
Proof.
  intros E' cs m m' q HF Hq x Hx. apply HF. intros (r & Hin & Hr). destruct Hin as [<- | [<- | []]];
    cbn [vv_byte YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [rewrite Hq in Hr|]; lia.
Qed.

Lemma vv_awr_w : forall E' cs STK sp0 FP bl0 blc ly own q,
  bv_unsigned (ew E' 8) = q -> (forall a, q <= a < q + 8 -> awr_byte STK sp0 FP bl0 blc ly own a) ->
  awr_ok E' [YP09.mkRegion (Some 8%nat) 0 24 0 8 cs; vv_byte] STK sp0 FP bl0 blc ly own.
Proof.
  intros E' cs STK sp0 FP bl0 blc ly own q Hq Ha.
  eapply awr_ok_cons_gen; [reflexivity | exact Hq | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Hr. apply Ha. lia.
Qed.

(* the cursor's p word and its writability, read off a cursor region of a symbolic state *)
Lemma vv_cur_facts : forall E' (m : word -> option byte) e1 e2 q v,
  region_ok SEGS E' m
    (YP09.mkRegion (Some 8%nat) 0 24 0 8 [YP09.mkChunk 0 (CVal 8 e1); YP09.mkChunk 8 (CVal 8 e2)]) ->
  bv_unsigned (ew E' 8) = q -> sv_denot E' e1 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS m q 8 v /\ (forall a, q <= a < q + 8 -> writable_at SEGS m a).
Proof.
  intros E' m e1 e2 q v (_ & _ & Hw & Hcs) Hq He Hv.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in Hw, Hcs. rewrite Hq in Hw, Hcs.
  split.
  - pose proof (proj1 (Forall_forall _ _) Hcs _ (or_introl eq_refl)) as Hck.
    pose proof (val_of_chunk_ok SEGS E' m q 0 8 e1 v Hck He ltac:(cbn; lia) ltac:(cbn; lia)) as Hv'.
    rewrite Z.add_0_r in Hv'. exact Hv'.
  - intros a Ha. replace a with (q + (a - q)) by lia. apply Hw. lia.
Qed.

Definition vv_keptR (H : word -> bool) (q : Z) (m m0 : word -> option byte) : Prop :=
  forall x : word, ~ (q <= bv_unsigned x < q + 8) -> mrestrict H m x = mrestrict H m0 x.

Lemma vv_kept_step : forall E' cs (H : word -> bool) q (m0 m1 m : word -> option byte),
  frame_of E' [YP09.mkRegion (Some 8%nat) 0 24 0 8 cs; vv_byte] (mrestrict H m1) (mrestrict H m) ->
  bv_unsigned (ew E' 8) = q -> vv_keptR H q m1 m0 -> vv_keptR H q m m0.
Proof.
  intros E' cs H q m0 m1 m HF Hq HK x Hx. rewrite (vv_frame_w _ _ _ _ _ HF Hq x Hx). exact (HK x Hx).
Qed.

Lemma vv_denot_off : forall E' n v c, ew E' n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E' (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E' n v c Hn Hv Hc. cbn [sv_denot]. rewrite Hn. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. Qed.

(* the move of a loop position across the loop's own runs: the cursor's p word read off the run's region *)
Lemma vv_move_w : forall CTX CTX0 CW E P regs' mem' md' p',
  vrd_ient_ok B ARx CTX CTX0 CW E -> vv_sep E P ->
  (forall r, In r vv_live -> getr regs' r = getr (ip_regs P) r) ->
  vv_keptR (w_H (ip_W P)) (ie_q E) mem' (ip_mem P) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
    (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem' md' (ip_k P) (ie_CW E) ->
  val_mem SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E) 8 p' ->
  (forall a, ie_q E <= a < ie_q E + 8 -> writable_at SEGS (mrestrict (w_H (ip_W P)) mem') a) ->
  ie_text E <= p' <= ie_text E + ie_len E ->
  (length (rest_atR (ie_tb E) (ie_text E) p') <= length (rest_atR (ie_tb E) (ie_text E) (ip_p P)))%nat ->
  PjGrammar.skip (rest_atR (ie_tb E) (ie_text E) p') = PjGrammar.skip (rest_atR (ie_tb E) (ie_text E) (ip_p P)) ->
  vv_sep E (vk_move P regs' mem' md' (ip_k P) p').
Proof.
  intros CTX CTX0 CW E P regs' mem' md' p' HEN HSEP HR HK HJ' Vp' Hw Hp' Hlen Hsk.
  apply (vv_move_sep CTX CTX0 CW E P regs' mem' md' p' HEN HSEP HR HK HJ'); [|exact Hlen | exact Hsk].
  pose proof HSEP as (_ & _ & _ & (Hin & _) & _).
  destruct (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  pose proof asan_consts as (C1 & _).
  exact (vv_pin_keep _ _ _ _ _ _ _ _ _ _ Hin ltac:(lia) ltac:(lia) HK Vp' Hw Hp').
Qed.

Lemma vv_mask_U : forall E' b, U E' (SOff 25 0) = 4294977024 -> U E' (SOff 34 0) = b -> 0 <= b <= 32 ->
  U E' (SAlu ALU_AND (SAlu ALU_SRL (SOff 25 0) (SOff 34 0)) (SLit 1)) = (if PjGrammar.ws b then 1 else 0).
Proof.
  intros E' b H25 H34 Hb. rewrite U_and_lit by lia. rewrite U_SAlu. cbn [zalu_raw]. rewrite H25, H34.
  assert (Hall : forallb (fun x => Z.eqb (Z.land (zcanon (Z.shiftr 4294977024 (Z.land x 63))) 1)
                                         (if PjGrammar.ws x then 1 else 0))
                         (map Z.of_nat (seq 0 33)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall.
  apply Z.eqb_eq, Hall, in_map_iff. exists (Z.to_nat b).
  split; [lia | apply in_seq; lia].
Qed.

Lemma vv_iter : forall CTX CTX0 CW E P,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vv_wsl E P -> Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_IWSL_SLOT P)
    (fun W2 c2 => ((exists P', W2 = ip_W P' /\ c2 = vrd_cfg A_ITAIL_SLOT P' /\ ip_n P' = ip_n P /\ vv_tail E P') /\
                   Pm (ms_mem (cfg_ms c2))) \/
       exists P', (0 <= ie_text E + ie_len E - ip_p P' < ie_text E + ie_len E - ip_p P) /\
         (W2 = ip_W P' /\ c2 = vrd_cfg A_IWSL_SLOT P' /\ Pm (ip_mem P') /\ ip_n P' = ip_n P /\ vv_wsl E P')).
Proof.
  intros CTX CTX0 CW E P HEN HW HPM.
  destruct HW as (HSEP & R10 & R12 & R11 & Hpe).
  pose proof HSEP as (HFR & HRG & HND & HCU & HJN & HMD & Hn0 & Hcont & HK1s).
  pose proof (vrd_ijrn_base B ARx SK E P HJN) as HJ.
  destruct (vv_q_bounds CTX CTX0 CW E HEN) as [Hq1 Hq2].
  pose proof HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof HCU as (Hin & Hraq & HSRC & _).
  pose proof Hin as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & Hgarr & Hqt & Hd).
  pose proof HSRC as (_ & Ht4096 & Htceil & _ & HRAt & _).
  destruct (vk_sp_bounds B ARx CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (b := nth (Z.to_nat (ip_p P - ie_text E)) (ie_tb E) 0).
  destruct (Hgarr (Z.to_nat (ip_p P - ie_text E)) ltac:(lia)) as [Vb Hb].
  replace (ie_text E + Z.of_nat (Z.to_nat (ip_p P - ie_text E))) with (ip_p P) in Vb by lia.
  fold b in Vb, Hb.
  assert (Hrest : rest_atR (ie_tb E) (ie_text E) (ip_p P) = b :: rest_atR (ie_tb E) (ie_text E) (ip_p P + 1))
    by (apply vv_rest_cons; lia).
  destruct (vv_seatW (ip_fx P) (ip_W P) (ip_regs P) (ip_mem P) (ie_q E) (ip_p P) (ie_text E + ie_len E) b
              A_IWSL_SLOT G8 G26 G23 G27 R10 R11 R12 Hq1 Hq2 Hq8 Vp Ve ltac:(lia) ltac:(lia) Vb Hb ltac:(lia)
              Hrw Hraq) as [HS SHOK].
  set (EW := vv_EW (ip_regs P) (ip_p P) (ie_text E + ie_len E) b) in *.
  assert (HEI : img_env VAL A_LIM EW) by (unfold EW, vv_EW; apply Eimg_env).
  assert (EL : forall j, (j < 32)%nat -> forall r : bv 5, Z.of_nat j = bv_unsigned r -> ew EW j = getr (ip_regs P) r).
  { intros j Hj r Hr. unfold EW, vv_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat (ip_regs P) _ j r Hr). }
  assert (E32 : ew EW 32 = w64 (ip_p P)).
  { unfold EW, vv_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 0). }
  assert (E33 : ew EW 33 = w64 (ie_text E + ie_len E)).
  { unfold EW, vv_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 1). }
  assert (E34 : ew EW 34 = w64 b).
  { unfold EW, vv_EW. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ip_regs P) _ 2). }
  assert (U8 : bv_unsigned (ew EW 8) = ie_q E)
    by (rewrite (EL 8%nat ltac:(lia) 8%bv eq_refl), G8; unfold w64; apply unsigned_lit_small; lia).
  assert (UB : U EW (SOff 26 0) = SHADOW_OFF).
  { apply U_atom; [rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl), G26; reflexivity | unfold SHADOW_OFF; lia]. }
  assert (U32 : U EW (SOff 32 0) = ip_p P) by (apply U_atom; [exact E32 | lia]).
  assert (HAW : forall a, ie_q E <= a < ie_q E + 8 ->
     awr_byte (STK_parse_items (ie_d E) + ie_e E) (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
       (ablocks B (ie_ly E) (ie_S E)) (ablocks B (ip_ly P) (ip_S P)) (ip_ly P) [] a)
    by (intros a Ha; left; pose proof (vv_stk_items (ie_d E)); unfold ESTACK in *; lia).
  assert (HA0 : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 b]) EW)
    by (split; [intros j Hj; unfold EW, vv_EW; rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia); reflexivity
               | reflexivity]).
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 23%bv HS) as R23. cbn [ms_regs restrict mkst] in R23.
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 27%bv HS) as R27. cbn [ms_regs restrict mkst] in R27.
  change (sr_get (ss_regs (vv_ssW A_IWSL_SLOT)) 23%bv) with (vv_sh 8 8) in R23.
  change (sr_get (ss_regs (vv_ssW A_IWSL_SLOT)) 27%bv) with (vv_sh 8 0) in R27.
  pose (RUN := paj_run_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (RUNTO := paj_run_to_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (BR := paj_branchR (fx := ip_fx P) (PI := PAI) (wle' SEGS YGcfRehidePost.RZ_cf)).
  unfold vrd_cfg.
  (* rows 246..250: the byte's shadow (its partial-granule test folded by the engine), the byte *)
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vi_Bspan;
    [ cbn [ms_mem mkst]; rewrite UB, U32; intros x Hx; apply HRAt; lia
    | unfold vv_ssW, vv_cur; cbn [ss_mem]; exact (vv_awr_w _ _ _ _ _ _ _ _ _ _ U8 HAW)
    | ].
  match type of HS with st_ok_pi _ _ ?E' _ _ => set (E1 := E') in * end.
  rename ms into ms1.
  assert (HK0 : vv_keptR (w_H (ip_W P)) (ie_q E) (ip_mem P) (ip_mem P)) by (intros x _; reflexivity).
  pose proof (vv_kept_step _ _ _ _ _ _ _ HFr U8 HK0) as HK1. clear HF HFr HG HK0.
  assert (E1o : forall j, (j < 512)%nat -> ew E1 j = ew EW j)
    by (intros j Hj; unfold E1; rewrite !ew_ewset_other by lia; reflexivity).
  assert (U8' : bv_unsigned (ew E1 8) = ie_q E) by (rewrite (E1o 8%nat ltac:(lia)); exact U8).
  assert (HA1 : env_agree 32 (Ereg (ip_regs P) [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 b]) E1)
    by (split; [intros j Hj; rewrite (E1o j ltac:(lia)); unfold EW, vv_EW;
                rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia); reflexivity | reflexivity]).
  assert (R23' : getr (ip_regs P) 23 = sv_denot E1 (vv_sh 8 8)) by exact R23.
  assert (R27' : getr (ip_regs P) 27 = sv_denot E1 (vv_sh 8 0)) by exact R27.
  assert (U1_21 : U E1 (SOff 21 0) = 32)
    by (apply U_atom; [rewrite (E1o 21%nat ltac:(lia)), (EL 21%nat ltac:(lia) 21%bv eq_refl), G21; reflexivity | lia]).
  assert (U1_34 : U E1 (SOff 34 0) = b) by (apply U_atom; [rewrite (E1o 34%nat ltac:(lia)), E34; reflexivity | lia]).
  assert (U1_25 : U E1 (SOff 25 0) = 4294977024)
    by (apply U_atom; [rewrite (E1o 25%nat ltac:(lia)), (EL 25%nat ltac:(lia) 25%bv eq_refl), G25; reflexivity | lia]).
  assert (E1_32 : ew E1 32 = w64 (ip_p P)) by (rewrite (E1o 32%nat ltac:(lia)); exact E32).
  assert (E1_33 : ew E1 33 = w64 (ie_text E + ie_len E)) by (rewrite (E1o 33%nat ltac:(lia)); exact E33).
  assert (S1_32 : sv_denot E1 (SOff 32 0) = Z_to_bv 64 (ip_p P))
    by (rewrite (vv_denot_off E1 32 (ip_p P) 0 E1_32) by lia; rewrite Z.add_0_r; reflexivity).
  assert (S1_32p : sv_denot E1 (SOff 32 1) = Z_to_bv 64 (ip_p P + 1))
    by (exact (vv_denot_off E1 32 (ip_p P) 1 E1_32 ltac:(lia) ltac:(lia))).
  assert (S1_33 : sv_denot E1 (SOff 33 0) = w64 (ie_text E + ie_len E))
    by (rewrite (vv_denot_off E1 33 (ie_text E + ie_len E) 0 E1_33) by lia; rewrite Z.add_0_r; reflexivity).
  (* row 251: `bltu s5, a3`, 32 < b leaves the loop *)
  psrr_branch_tok RUN BR HS SHOK vi_Bspan.
  - (* 32 < b: not white space, to the separator test *)
    match goal with H : branch_taken _ _ _ = true |- _ => rename H into Hbr end.
    assert (Hb32 : 32 < b) by (rewrite branch_ltu_U, U1_21, U1_34 in Hbr; apply Z.ltb_lt in Hbr; exact Hbr).
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vi_Bspan (4 * Z.of_nat A_ITAIL_SLOT);
      [exact (vv_awr_w _ _ _ _ _ _ _ _ _ _ U8' HAW)|].
    rename ms into ms2.
    pose proof (vv_kept_step _ _ _ _ _ _ _ HFr U8' HK1) as HK2. clear HF HFr HG.
    assert (HRk : forall r, In r vv_live -> getr (ms_regs ms2) r = getr (ip_regs P) r).
    { eapply (vv_regs_after _ _ _ _ _ _ _ HS HA1);
        [reflexivity | reflexivity | vm_compute; reflexivity | exact R23' | exact R27']. }
    match type of HS with st_ok_pi _ _ ?E' ?ss _ =>
      let r := eval vm_compute in (nth 0 (ss_mem ss) vv_byte) in
      pose proof (vv_region_nth _ E' ss _ 0 r HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict] in HR0.
    destruct (vv_cur_facts _ _ _ _ (ie_q E) (ip_p P) HR0 U8' S1_32 ltac:(lia)) as [Vp2 Hw2].
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 11%bv HS) as Q11.
    match type of Q11 with _ = sv_denot _ (sr_get ?l _) =>
      let v := eval vm_compute in (sr_get l 11%bv) in change (sr_get l 11%bv) with v in Q11 end.
    cbn [ms_regs restrict] in Q11. rewrite S1_33 in Q11.
    pmkst HS.
    lazymatch goal with |- SRrG _ _ _ (mkCfg _ ?md) _ => set (md2 := md) in * end.
    apply SRr'_ret. left. split; [|exact HPM].
    exists (vk_move P (ms_regs ms2) (ms_mem ms2) md2 (ip_k P) (ip_p P)).
    split; [reflexivity|]. split; [unfold vrd_cfg, vk_move; cbn [ip_fx ip_regs ip_mem ip_md]; reflexivity|].
    split; [reflexivity|].
    split; [|split].
    + apply (vv_move_w CTX CTX0 CW E P _ _ _ _ HEN HSEP HRk HK2 (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ)
               Vp2 Hw2); [lia | apply Nat.le_refl | reflexivity].
    + exact Q11.
    + unfold vk_move; cbn [ip_p]. rewrite Hrest. apply vv_skip_nws, vv_ws_32. exact Hb32.
  - match goal with H : branch_taken _ _ _ = false |- _ => rename H into Hbr end.
    assert (Hb32 : b <= 32) by (rewrite branch_ltu_U, U1_21, U1_34 in Hbr; apply Z.ltb_ge in Hbr; exact Hbr).
    (* rows 252..254: the mask test *)
    paj_run_tok_x_inv RUN HS HJ SHOK HPM vi_Bspan; [exact (vv_awr_w _ _ _ _ _ _ _ _ _ _ U8' HAW)|].
    rename ms into ms2.
    pose proof (vv_kept_step _ _ _ _ _ _ _ HFr U8' HK1) as HK2. clear HF HFr HG.
    assert (HM : U E1 (SAlu ALU_AND (SAlu ALU_SRL (SOff 25 0) (SOff 34 0)) (SLit 1)) =
                 (if PjGrammar.ws b then 1 else 0)) by (apply vv_mask_U; [exact U1_25 | exact U1_34 | lia]).
    psrr_branch_tok RUN BR HS SHOK vi_Bspan.
    + (* the mask bit is 0: not white space, to the separator test *)
      match goal with H : branch_taken _ _ _ = true |- _ => rename H into Hbr2 end.
      assert (Hws : PjGrammar.ws b = false).
      { rewrite branch_eq_U, HM, (U_lit E1 0) in Hbr2 by lia.
        destruct (PjGrammar.ws b); [discriminate Hbr2 | reflexivity]. }
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vi_Bspan (4 * Z.of_nat A_ITAIL_SLOT);
        [exact (vv_awr_w _ _ _ _ _ _ _ _ _ _ U8' HAW)|].
      rename ms into ms3.
      pose proof (vv_kept_step _ _ _ _ _ _ _ HFr U8' HK2) as HK3. clear HF HFr HG.
      assert (HRk : forall r, In r vv_live -> getr (ms_regs ms3) r = getr (ip_regs P) r).
      { eapply (vv_regs_after _ _ _ _ _ _ _ HS HA1);
          [reflexivity | reflexivity | vm_compute; reflexivity | exact R23' | exact R27']. }
      match type of HS with st_ok_pi _ _ ?E' ?ss _ =>
        let r := eval vm_compute in (nth 0 (ss_mem ss) vv_byte) in
        pose proof (vv_region_nth _ E' ss _ 0 r HS ltac:(vm_compute; reflexivity)) as HR0 end.
      cbn [ms_mem restrict] in HR0.
      destruct (vv_cur_facts _ _ _ _ (ie_q E) (ip_p P) HR0 U8' S1_32 ltac:(lia)) as [Vp3 Hw3].
      pose proof (st_ok_pi_restrict_reg _ _ _ _ 11%bv HS) as Q11.
      match type of Q11 with _ = sv_denot _ (sr_get ?l _) =>
        let v := eval vm_compute in (sr_get l 11%bv) in change (sr_get l 11%bv) with v in Q11 end.
      cbn [ms_regs restrict] in Q11. rewrite S1_33 in Q11.
      pmkst HS.
      lazymatch goal with |- SRrG _ _ _ (mkCfg _ ?md) _ => set (md3 := md) in * end.
      apply SRr'_ret. left. split; [|exact HPM].
      exists (vk_move P (ms_regs ms3) (ms_mem ms3) md3 (ip_k P) (ip_p P)).
      split; [reflexivity|]. split; [unfold vrd_cfg, vk_move; cbn [ip_fx ip_regs ip_mem ip_md]; reflexivity|].
      split; [reflexivity|].
      split; [|split].
      * apply (vv_move_w CTX CTX0 CW E P _ _ _ _ HEN HSEP HRk HK3 (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ)
                 Vp3 Hw3); [lia | apply Nat.le_refl | reflexivity].
      * exact Q11.
      * unfold vk_move; cbn [ip_p]. rewrite Hrest. apply vv_skip_nws. exact Hws.
    + (* white space: rows 255..260, the shadow gate of q, q->p := p + 1, `bne p + 1, end` *)
      match goal with H : branch_taken _ _ _ = false |- _ => rename H into Hbr2 end.
      assert (Hws : PjGrammar.ws b = true).
      { rewrite branch_eq_U, HM, (U_lit E1 0) in Hbr2 by lia.
        destruct (PjGrammar.ws b); [reflexivity | discriminate Hbr2]. }
      paj_run_tok_x_inv RUN HS HJ SHOK HPM vi_Bspan; [exact (vv_awr_w _ _ _ _ _ _ _ _ _ _ U8' HAW)|].
      rename ms into ms3.
      pose proof (vv_kept_step _ _ _ _ _ _ _ HFr U8' HK2) as HK3. clear HF HFr HG.
      assert (U1_32p : U E1 (SOff 32 1) = ip_p P + 1) by (apply U_atom_off; [exact E1_32 | lia | lia]).
      assert (U1_33 : U E1 (SOff 33 0) = ie_text E + ie_len E) by (apply U_atom; [exact E1_33 | lia]).
      psrr_branch_tok RUN BR HS SHOK vi_Bspan.
      * (* p + 1 <> end: back to the loop head *)
        match goal with H : branch_taken _ _ _ = true |- _ => rename H into Hbr3 end.
        assert (Hlt : ip_p P + 1 < ie_text E + ie_len E).
        { rewrite branch_ne_U, U1_32p, U1_33 in Hbr3. apply Bool.negb_true_iff, Z.eqb_neq in Hbr3. lia. }
        paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vi_Bspan (4 * Z.of_nat A_IWSL_SLOT);
          [exact (vv_awr_w _ _ _ _ _ _ _ _ _ _ U8' HAW)|].
        rename ms into ms4.
        pose proof (vv_kept_step _ _ _ _ _ _ _ HFr U8' HK3) as HK4. clear HF HFr HG.
        assert (HRk : forall r, In r vv_live -> getr (ms_regs ms4) r = getr (ip_regs P) r).
        { eapply (vv_regs_after _ _ _ _ _ _ _ HS HA1);
            [reflexivity | reflexivity | vm_compute; reflexivity | exact R23' | exact R27']. }
        match type of HS with st_ok_pi _ _ ?E' ?ss _ =>
          let r := eval vm_compute in (nth 0 (ss_mem ss) vv_byte) in
          pose proof (vv_region_nth _ E' ss _ 0 r HS ltac:(vm_compute; reflexivity)) as HR0 end.
        cbn [ms_mem restrict] in HR0.
        destruct (vv_cur_facts _ _ _ _ (ie_q E) (ip_p P + 1) HR0 U8' S1_32p ltac:(lia)) as [Vp4 Hw4].
        pose proof (st_ok_pi_restrict_reg _ _ _ _ 10%bv HS) as Q10.
        pose proof (st_ok_pi_restrict_reg _ _ _ _ 11%bv HS) as Q11.
        pose proof (st_ok_pi_restrict_reg _ _ _ _ 12%bv HS) as Q12.
        match type of Q10 with _ = sv_denot _ (sr_get ?l _) =>
          let v := eval vm_compute in (sr_get l 10%bv) in change (sr_get l 10%bv) with v in Q10;
          let v := eval vm_compute in (sr_get l 11%bv) in change (sr_get l 11%bv) with v in Q11;
          let v := eval vm_compute in (sr_get l 12%bv) in change (sr_get l 12%bv) with v in Q12 end.
        cbn [ms_regs restrict] in Q10, Q11, Q12. rewrite S1_33 in Q11. rewrite S1_32p in Q10, Q12.
        pmkst HS.
        lazymatch goal with |- SRrG _ _ _ (mkCfg _ ?md) _ => set (md4 := md) in * end.
        apply SRr'_ret. right.
        exists (vk_move P (ms_regs ms4) (ms_mem ms4) md4 (ip_k P) (ip_p P + 1)).
        split; [unfold vk_move; cbn [ip_p]; lia|].
        split; [reflexivity|]. split; [unfold vrd_cfg, vk_move; cbn [ip_fx ip_regs ip_mem ip_md]; reflexivity|].
        split; [exact HPM|].
        split; [reflexivity|].
        split.
         -- apply (vv_move_w CTX CTX0 CW E P _ _ _ _ HEN HSEP HRk HK4
                     (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ) Vp4 Hw4); [lia | |].
           ++ rewrite Hrest. cbn [length]. lia.
           ++ rewrite Hrest, vv_skip_ws by exact Hws. reflexivity.
        -- unfold vk_move; cbn [ip_regs ip_p]. exact (conj Q10 (conj Q12 (conj Q11 Hlt))).
      * (* p + 1 = end: `j` to the separator test *)
        match goal with H : branch_taken _ _ _ = false |- _ => rename H into Hbr3 end.
        assert (Heq : ip_p P + 1 = ie_text E + ie_len E).
        { rewrite branch_ne_U, U1_32p, U1_33 in Hbr3. apply Bool.negb_false_iff, Z.eqb_eq in Hbr3. exact Hbr3. }
        paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vi_Bspan (4 * Z.of_nat A_ITAIL_SLOT);
          [exact (vv_awr_w _ _ _ _ _ _ _ _ _ _ U8' HAW)|].
        rename ms into ms4.
        pose proof (vv_kept_step _ _ _ _ _ _ _ HFr U8' HK3) as HK4. clear HF HFr HG.
        assert (HRk : forall r, In r vv_live -> getr (ms_regs ms4) r = getr (ip_regs P) r).
        { eapply (vv_regs_after _ _ _ _ _ _ _ HS HA1);
            [reflexivity | reflexivity | vm_compute; reflexivity | exact R23' | exact R27']. }
        match type of HS with st_ok_pi _ _ ?E' ?ss _ =>
          let r := eval vm_compute in (nth 0 (ss_mem ss) vv_byte) in
          pose proof (vv_region_nth _ E' ss _ 0 r HS ltac:(vm_compute; reflexivity)) as HR0 end.
        cbn [ms_mem restrict] in HR0.
        destruct (vv_cur_facts _ _ _ _ (ie_q E) (ip_p P + 1) HR0 U8' S1_32p ltac:(lia)) as [Vp4 Hw4].
        pose proof (st_ok_pi_restrict_reg _ _ _ _ 11%bv HS) as Q11.
        match type of Q11 with _ = sv_denot _ (sr_get ?l _) =>
          let v := eval vm_compute in (sr_get l 11%bv) in change (sr_get l 11%bv) with v in Q11 end.
        cbn [ms_regs restrict] in Q11. rewrite S1_33 in Q11.
        pmkst HS.
        lazymatch goal with |- SRrG _ _ _ (mkCfg _ ?md) _ => set (md4 := md) in * end.
        apply SRr'_ret. left. split; [|exact HPM].
        exists (vk_move P (ms_regs ms4) (ms_mem ms4) md4 (ip_k P) (ip_p P + 1)).
        split; [reflexivity|]. split; [unfold vrd_cfg, vk_move; cbn [ip_fx ip_regs ip_mem ip_md]; reflexivity|].
        split; [reflexivity|].
        split; [|split].
         -- apply (vv_move_w CTX CTX0 CW E P _ _ _ _ HEN HSEP HRk HK4
                     (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ) Vp4 Hw4); [lia | |].
           ++ rewrite Hrest. cbn [length]. lia.
           ++ rewrite Hrest, vv_skip_ws by exact Hws. reflexivity.
        -- exact Q11.
        -- unfold vk_move; cbn [ip_p]. rewrite vv_rest_end by lia. reflexivity.
Qed.

(* ==== C2: the loop, by SRr'_loopZ with measure (text + len) - p ==== *)
Lemma vv_partC2 : forall CTX CTX0 CW E P,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vv_wsl E P -> Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_IWSL_SLOT P)
    (fun W2 c2 => (exists P', W2 = ip_W P' /\ c2 = vrd_cfg A_ITAIL_SLOT P' /\ ip_n P' = ip_n P /\ vv_tail E P') /\
                  Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P0 HEN HW0 HPM0.
  refine (SRr'_loopZ SEGS YGcfRehidePost.RZ_cf vrd_ipos (fun P => ie_text E + ie_len E - ip_p P)
           (fun P W c => W = ip_W P /\ c = vrd_cfg A_IWSL_SLOT P /\ Pm (ip_mem P) /\ ip_n P = ip_n P0 /\ vv_wsl E P)
           (fun W2 c2 => (exists P', W2 = ip_W P' /\ c2 = vrd_cfg A_ITAIL_SLOT P' /\ ip_n P' = ip_n P0 /\
                                     vv_tail E P') /\
                         Pm (ms_mem (cfg_ms c2)))
           _ P0 (ip_W P0) (vrd_cfg A_IWSL_SLOT P0) _).
  - intros P W c (-> & -> & HPM & Hn & HW).
    eapply SRr'_mono; [exact (vv_iter CTX CTX0 CW E P HEN HW HPM)|].
    intros W' c' _ [((P' & HW' & Hc' & Hn' & HT) & HPc) | (P' & Hm & HW' & Hc' & HPP & Hn' & HW2)].
    + left. split; [exists P'; split; [exact HW'|]; split; [exact Hc'|]; split; [congruence | exact HT] | exact HPc].
    + right. exists P'. split; [exact Hm|]. split; [exact HW'|]. split; [exact Hc'|]. split; [exact HPP|].
      split; [congruence | exact HW2].
  - split; [reflexivity|]. split; [reflexivity|]. split; [exact HPM0|]. split; [reflexivity | exact HW0].
Qed.



(* ==== PART D: sub-lane IvalL (IvalL_D.v), Qed ==== *)
(* ---- PART D: the separator test (rows 265..279), the closer (326..346) and the two exits ---- *)

(* atoms 32 / 33 / 34 / 35: the cursor's p word, its end word, the byte at p, the cursor's depth word *)
Definition vd_E (regs : bvmap 5 word) (p en b dep : Z) : env :=
  @Eimg _ A_prog_listing PAI (Ereg regs [w64 p; w64 en; w64 b; w64 dep]).
Definition vd_sr : list sv :=
  sr_set (sr_set (sr_set sr_atoms 9%bv (SOff 8 16)) 11%bv (SOff 33 0)) 27%bv (vv_sh 8 0).
Definition vd_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 144 0 0 [YP09.mkChunk 16 (CVal 8 (vv_sh 8 16))].
Definition vd_cur0 : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition vd_cur1 : YP09.region :=
  YP09.mkRegion (Some 8%nat) 8 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition vd_cur2 : YP09.region :=
  YP09.mkRegion (Some 8%nat) 16 24 16 20 [YP09.mkChunk 16 (CVal 4 (SOff 35 0))].
Definition vd_byte : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition vd_facts : facts :=
  mkFacts [ (8%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (32%nat, mkAF 4096 (2 ^ 47 - 8) 0); (33%nat, mkAF 4096 (2 ^ 47 - 8) 0);
            (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 32 0) ] [] [].
Definition vd_SH : list shent := [mkSHE 8 0 24; mkSHE 32 0 1].
Definition vd_ss (k : nat) : sstate :=
  mkSS (4 * Z.of_nat k) vd_sr [vd_frame; vd_cur0; vd_cur1; vd_cur2; vd_byte] None vd_facts.
(* the same seat with no byte and no write window: the p = end path stores nothing *)
Definition vd_cur0E : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition vd_cur2E : YP09.region :=
  YP09.mkRegion (Some 8%nat) 16 24 0 0 [YP09.mkChunk 16 (CVal 4 (SOff 35 0))].
Definition vd_SHE : list shent := [mkSHE 8 0 24].
Definition vd_ssE (k : nat) : sstate :=
  mkSS (4 * Z.of_nat k) vd_sr [vd_frame; vd_cur0E; vd_cur1; vd_cur2E] None vd_facts.


Lemma vd_seat : forall (fxP : YK11.FPState) (W : world SEGS) regs mem q sp p en b dep (k : nat),
  getr regs 2 = w64 sp -> getr regs 8 = w64 q -> getr regs 9 = w64 (q + 16) ->
  getr regs 11 = w64 en -> getr regs 26 = w64 SHADOW_OFF -> getr regs 27 = w64 (shadow_addr q) ->
  2 ^ 46 <= q -> q + 24 <= 2 ^ 47 -> q mod 8 = 0 -> sp + 144 <= q -> 2 ^ 46 <= sp ->
  4096 <= p -> p + 1 <= 2 ^ 47 - 8 -> p + 1 <= sp ->
  4096 <= en -> en + 8 <= 2 ^ 47 -> 0 <= b < 256 -> 0 <= dep <= 32 ->
  val_mem SEGS (mrestrict (w_H W) mem) q 8 p ->
  val_mem SEGS (mrestrict (w_H W) mem) (q + 8) 8 en ->
  val_mem SEGS (mrestrict (w_H W) mem) (q + 16) 4 dep ->
  val_mem SEGS (mrestrict (w_H W) mem) (sp + 16) 8 (shadow_addr (q + 16)) ->
  val_mem SEGS (mrestrict (w_H W) mem) p 1 b ->
  rd_rw SEGS (mrestrict (w_H W) mem) q 24 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF q 24 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p 1 ->
  (p + 1 <= kLowMemEnd \/ kHighMemBeg <= p) ->
  st_ok_pi (fx := fxP) SEGS VAL (vd_E regs p en b dep) (vd_ss k)
    (restrict (w_H W) (@YK11.mkst fxP regs (w64 (A_IPC k)) mem (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS (SOff 26 0) vd_SH (vd_E regs p en b dep) (mrestrict (w_H W) mem).
Proof.
  intros fxP W regs mem q sp p en b dep k R2 R8 R9 R11 R26 R27 Hq1 Hq2 Hq8 Hspq Hsp1
    Hp1 Hp2 Hps He1 He2 Hb Hdep Vp Ve Vd Vsh Vb Hrw Hraq Hrap Hap.
  set (ED := vd_E regs p en b dep).
  assert (EL : forall j, (j < 32)%nat -> forall r : bv 5, Z.of_nat j = bv_unsigned r -> ew ED j = getr regs r).
  { intros j Hj r Hr. unfold ED, vd_E. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat regs _ j r Hr). }
  assert (E2 : ew ED 2 = w64 sp) by (rewrite (EL 2%nat ltac:(lia) 2%bv eq_refl); exact R2).
  assert (E8 : ew ED 8 = w64 q) by (rewrite (EL 8%nat ltac:(lia) 8%bv eq_refl); exact R8).
  assert (E26 : ew ED 26 = w64 SHADOW_OFF) by (rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl); exact R26).
  assert (E32 : ew ED 32 = w64 p).
  { unfold ED, vd_E. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
  assert (E33 : ew ED 33 = w64 en).
  { unfold ED, vd_E. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
  assert (E34 : ew ED 34 = w64 b).
  { unfold ED, vd_E. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2). }
  assert (E35 : ew ED 35 = w64 dep).
  { unfold ED, vd_E. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 3). }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (U8 : bv_unsigned (ew ED 8) = q) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew ED 26) = SHADOW_OFF)
    by (rewrite E26; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U2 : bv_unsigned (ew ED 2) = sp) by (rewrite E2; unfold w64; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew ED 32) = p) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
  assert (Uq : U ED (SOff 8 0) = q)
    by (unfold U; cbn [sv_denot]; rewrite E8, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned;
        apply unsigned_lit_small; lia).
  assert (Up : U ED (SOff 32 0) = p)
    by (unfold U; cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned;
        apply unsigned_lit_small; lia).
  assert (UB : U ED (SOff 26 0) = SHADOW_OFF)
    by (unfold U; cbn [sv_denot]; rewrite E26, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned;
        apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (S32 : sv_denot ED (SOff 32 0) = w64 p)
    by (cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (S33 : sv_denot ED (SOff 33 0) = w64 en)
    by (cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (S34 : sv_denot ED (SOff 34 0) = w64 b)
    by (cbn [sv_denot]; rewrite E34, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (S35 : sv_denot ED (SOff 35 0) = w64 dep)
    by (cbn [sv_denot]; rewrite E35, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (S9 : sv_denot ED (SOff 8 16) = w64 (q + 16)).
  { rewrite denot_lit_U, U_SOff, U8, zcanon_id by (unfold M64; lia). reflexivity. }
  split.
  - rewrite (restrict_mkst_fx (fx := fxP)).
    change (w64 (A_IPC k)) with (Z_to_bv 64 (BASE + 4 * Z.of_nat k)).
    unfold vd_ss. apply (pa_entry_st_ok_full (fx := fxP)).
    + unfold vd_sr.
      apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity |]
                           | reflexivity |] | reflexivity |].
      * rewrite R9. symmetry. exact S9.
      * rewrite R11. symmetry. exact S33.
      * rewrite R27. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned. fold (U ED (vv_sh 8 0)).
        rewrite (vv_sh_U ED 8 0 q U8 U26) by lia. unfold shadow_addr. rewrite Z.add_0_r.
        assert (0 <= q / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
        unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
        rewrite Z.mod_small by (unfold SHADOW_OFF; lia). reflexivity.
    + vm_compute; reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
        [|apply Forall_nil]]]]].
      * unfold region_ok, vd_frame.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS ED _ sp 16 8 (vv_sh 8 16) (shadow_addr (q + 16))).
        -- rewrite denot_lit_U, (vv_sh_U ED 8 16 q U8 U26) by lia. reflexivity.
        -- cbn [Z.of_N]. unfold shadow_addr, SHADOW_OFF.
           assert (0 <= (q + 16) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia.
        -- cbn [Z.of_N]. lia.
        -- exact Vsh.
      * unfold region_ok, vd_cur0.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hrw; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS ED _ q 0 8 (SOff 32 0) p); [exact S32 | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact Vp.
      * unfold region_ok, vd_cur1.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS ED _ q 8 8 (SOff 33 0) en); [exact S33 | cbn; lia | cbn; lia | exact Ve].
      * unfold region_ok, vd_cur2.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hrw; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS ED _ q 16 4 (SOff 35 0) dep); [exact S35 | cbn; lia | cbn; lia | exact Vd].
      * unfold region_ok, vd_byte.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS ED _ p 0 1 (SOff 34 0) b); [exact S34 | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact Vb.
    + apply pairwise_disjoint_of_extents.
      unfold vd_frame, vd_cur0, vd_cur1, vd_cur2, vd_byte, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U2, U8, U32.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [vd_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U8, U26, U32, E33, E34, E35. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - unfold sh_ok, vd_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (shent_ok_of_range SEGS (w_H W) mem ED (SOff 26 0) 8 q 24 q 0 24 Hraq UB Uq); [lia | lia |].
      intros x Hx. unfold SHADOW_OFF in *. lia.
    + apply (shent_ok_of_range SEGS (w_H W) mem ED (SOff 26 0) 32 p 1 p 0 1 Hrap UB Up); [lia | lia |].
      intros x Hx. unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg in *. lia.
Qed.

Lemma vd_seatE : forall (fxP : YK11.FPState) (W : world SEGS) regs mem q sp p en dep (k : nat),
  getr regs 2 = w64 sp -> getr regs 8 = w64 q -> getr regs 9 = w64 (q + 16) ->
  getr regs 11 = w64 en -> getr regs 26 = w64 SHADOW_OFF -> getr regs 27 = w64 (shadow_addr q) ->
  2 ^ 46 <= q -> q + 24 <= 2 ^ 47 -> q mod 8 = 0 -> sp + 144 <= q -> 2 ^ 46 <= sp ->
  4096 <= p -> p + 1 <= 2 ^ 47 - 8 ->
  4096 <= en -> en + 8 <= 2 ^ 47 -> 0 <= dep <= 32 ->
  val_mem SEGS (mrestrict (w_H W) mem) q 8 p ->
  val_mem SEGS (mrestrict (w_H W) mem) (q + 8) 8 en ->
  val_mem SEGS (mrestrict (w_H W) mem) (q + 16) 4 dep ->
  val_mem SEGS (mrestrict (w_H W) mem) (sp + 16) 8 (shadow_addr (q + 16)) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF q 24 ->
  st_ok_pi (fx := fxP) SEGS VAL (vd_E regs p en 0 dep) (vd_ssE k)
    (restrict (w_H W) (@YK11.mkst fxP regs (w64 (A_IPC k)) mem (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS (SOff 26 0) vd_SHE (vd_E regs p en 0 dep) (mrestrict (w_H W) mem).
Proof.
  intros fxP W regs mem q sp p en dep k R2 R8 R9 R11 R26 R27 Hq1 Hq2 Hq8 Hspq Hsp1
    Hp1 Hp2 He1 He2 Hdep Vp Ve Vd Vsh Hraq.
  set (ED := vd_E regs p en 0 dep).
  assert (EL : forall j, (j < 32)%nat -> forall r : bv 5, Z.of_nat j = bv_unsigned r -> ew ED j = getr regs r).
  { intros j Hj r Hr. unfold ED, vd_E. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat regs _ j r Hr). }
  assert (E2 : ew ED 2 = w64 sp) by (rewrite (EL 2%nat ltac:(lia) 2%bv eq_refl); exact R2).
  assert (E8 : ew ED 8 = w64 q) by (rewrite (EL 8%nat ltac:(lia) 8%bv eq_refl); exact R8).
  assert (E26 : ew ED 26 = w64 SHADOW_OFF) by (rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl); exact R26).
  assert (E32 : ew ED 32 = w64 p).
  { unfold ED, vd_E. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
  assert (E33 : ew ED 33 = w64 en).
  { unfold ED, vd_E. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
  assert (E34 : ew ED 34 = w64 0).
  { unfold ED, vd_E. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2). }
  assert (E35 : ew ED 35 = w64 dep).
  { unfold ED, vd_E. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 3). }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (U8 : bv_unsigned (ew ED 8) = q) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew ED 26) = SHADOW_OFF)
    by (rewrite E26; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U2 : bv_unsigned (ew ED 2) = sp) by (rewrite E2; unfold w64; apply unsigned_lit_small; lia).
  assert (Uq : U ED (SOff 8 0) = q)
    by (rewrite U_SOff, U8, Z.add_0_r; apply zcanon_id; unfold M64; lia).
  assert (UB : U ED (SOff 26 0) = SHADOW_OFF)
    by (rewrite U_SOff, U26, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
  assert (S32 : sv_denot ED (SOff 32 0) = w64 p)
    by (cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (S33 : sv_denot ED (SOff 33 0) = w64 en)
    by (cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (S35 : sv_denot ED (SOff 35 0) = w64 dep)
    by (cbn [sv_denot]; rewrite E35, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (S9 : sv_denot ED (SOff 8 16) = w64 (q + 16)).
  { rewrite denot_lit_U, U_SOff, U8, zcanon_id by (unfold M64; lia). reflexivity. }
  split.
  - rewrite (restrict_mkst_fx (fx := fxP)).
    change (w64 (A_IPC k)) with (Z_to_bv 64 (BASE + 4 * Z.of_nat k)).
    unfold vd_ssE. apply (pa_entry_st_ok_full (fx := fxP)).
    + unfold vd_sr.
      apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity |]
                           | reflexivity |] | reflexivity |].
      * rewrite R9. symmetry. exact S9.
      * rewrite R11. symmetry. exact S33.
      * rewrite R27. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned. fold (U ED (vv_sh 8 0)).
        rewrite (vv_sh_U ED 8 0 q U8 U26) by lia. unfold shadow_addr. rewrite Z.add_0_r.
        assert (0 <= q / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
        unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
        rewrite Z.mod_small by (unfold SHADOW_OFF; lia). reflexivity.
    + vm_compute; reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      * unfold region_ok, vd_frame.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS ED _ sp 16 8 (vv_sh 8 16) (shadow_addr (q + 16))).
        -- rewrite denot_lit_U, (vv_sh_U ED 8 16 q U8 U26) by lia. reflexivity.
        -- cbn [Z.of_N]. unfold shadow_addr, SHADOW_OFF.
           assert (0 <= (q + 16) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia.
        -- cbn [Z.of_N]. lia.
        -- exact Vsh.
      * unfold region_ok, vd_cur0E.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS ED _ q 0 8 (SOff 32 0) p); [exact S32 | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact Vp.
      * unfold region_ok, vd_cur1.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS ED _ q 8 8 (SOff 33 0) en); [exact S33 | cbn; lia | cbn; lia | exact Ve].
      * unfold region_ok, vd_cur2E.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS ED _ q 16 4 (SOff 35 0) dep); [exact S35 | cbn; lia | cbn; lia | exact Vd].
    + apply pairwise_disjoint_of_extents.
      unfold vd_frame, vd_cur0E, vd_cur1, vd_cur2E, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U2, U8.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [vd_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U8, U26, E32, E33, E34, E35. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - unfold sh_ok, vd_SHE. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W) mem ED (SOff 26 0) 8 q 24 q 0 24 Hraq UB Uq); [lia | lia |].
    intros x Hx. unfold SHADOW_OFF in *. lia.
Qed.

(* the numeric facts every state of this step needs. The kit's cut: the text's end is STRICTLY below the ceiling (rd_pre's
   appended conjunct, PRH_FnParse.v:227); src_rd dropped its `+ 8` (PRH_Base.v:1660), so the old
   `text + len + 8 <= alloc_ceiling` has no source and no access here needs it *)
Lemma vd_bounds : forall CTX CTX0 CW E P, vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_iframe E P -> vrd_icur B E P ->
  2 ^ 46 <= ie_q E /\ ie_q E + 24 <= 2 ^ 47 /\ ie_q E mod 8 = 0 /\
  spZ (ip_regs P) = spZ (ie_regs E) - 144 /\ 2 ^ 46 <= spZ (ip_regs P) /\
  spZ (ip_regs P) + 144 <= ie_q E /\ alloc_ceiling <= spZ (ip_regs P) /\
  4096 <= ie_text E /\ ie_text E <= ip_p P <= ie_text E + ie_len E /\
  ie_text E + ie_len E < alloc_ceiling /\ alloc_ceiling < 2 ^ 47 - 8 /\
  Z.of_nat (length (ie_tb E)) = ie_len E /\
  (ie_text E + ie_len E + 1 <= kLowMemEnd \/ kHighMemBeg <= ie_text E).
Proof.
  intros CTX CTX0 CW E P HEN HFR HCU.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (vv_stk_items (ie_d E)) as HSTKi. unfold ESTACK in HSTKi.
  pose proof HFR as (Hsp & _).
  pose proof HCU as (Hinok & Hraq & Hsrc & _).
  pose proof Hinok as (_ & _ & _ & Hrw & Hq8 & Ht0 & Htl & Hpp & Hlen & _).
  pose proof Hsrc as (_ & Ht4 & Htc & Ham & _).
  destruct HEN as ((HAFN & _) & _ & _ & _ & HRD & _).
  pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof HRD as (_ & _ & _ & _ & _ & HFW & Hqlo & Hqhi & _).
  pose proof HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTXC).
  destruct HFW as (He0 & He16 & Hetop & Hepres).
  rewrite Hlen in Ham. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham.
  repeat split; unfold kLowMemEnd, kHighMemBeg in *; try lia.
Qed.

Lemma vd_seat_at : forall CTX CTX0 CW E P (k : nat),
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_iframe E P -> vrd_iregs B E P -> vrd_icur B E P ->
  getr (ip_regs P) 11 = w64 (ie_text E + ie_len E) ->
  ip_p P < ie_text E + ie_len E ->
  st_ok_pi (fx := ip_fx P) SEGS VAL
    (vd_E (ip_regs P) (ip_p P) (ie_text E + ie_len E)
          (nth (Z.to_nat (ip_p P - ie_text E)) (ie_tb E) 0) (Z.of_nat (ie_d E) + 1)) (vd_ss k)
    (restrict (w_H (ip_W P)) (@YK11.mkst (ip_fx P) (ip_regs P) (w64 (A_IPC k)) (ip_mem P) (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS (SOff 26 0) vd_SH
      (vd_E (ip_regs P) (ip_p P) (ie_text E + ie_len E)
            (nth (Z.to_nat (ip_p P - ie_text E)) (ie_tb E) 0) (Z.of_nat (ie_d E) + 1))
      (mrestrict (w_H (ip_W P)) (ip_mem P)).
Proof.
  intros CTX CTX0 CW E P k HEN HFR HRG HCU R11 Hpe.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (vd_bounds CTX CTX0 CW E P HEN HFR HCU)
    as (Bq1 & Bq2 & Bq8 & Bsp & Bsp46 & Bspq & Bspc & Bt4 & (Btp & Bpe) & Btc & Bac & Blen & Bam).
  pose proof HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof HCU as (Hinok & Hraq & Hsrc & _).
  pose proof Hinok as (Vp & Ve & Vd & Hrw & _ & _ & _ & _ & _ & Hgarr & _ & Hd32).
  pose proof Hsrc as (_ & _ & _ & _ & Hrat & _).
  pose proof HFR as (Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Vsh & _).
  assert (R2 : getr (ip_regs P) 2 = w64 (spZ (ip_regs P)))
    by (unfold w64, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
  set (j := Z.to_nat (ip_p P - ie_text E)).
  assert (Hj : (j < length (ie_tb E))%nat) by (subst j; lia).
  destruct (Hgarr j Hj) as (Vb & Hb255).
  assert (Etj : ie_text E + Z.of_nat j = ip_p P) by (subst j; lia).
  rewrite Etj in Vb.
  apply (vd_seat (ip_fx P) (ip_W P) (ip_regs P) (ip_mem P) (ie_q E) (spZ (ip_regs P)) (ip_p P)
           (ie_text E + ie_len E) (nth j (ie_tb E) 0) (Z.of_nat (ie_d E) + 1) k
           R2 G8 G9 R11 G26 G27);
    try lia.
  - exact Vp.
  - exact Ve.
  - exact Vd.
    (* the frame slot sp + 16 = sp0 - 128 *)
  - replace (spZ (ip_regs P) + 16) with (spZ (ie_regs E) - 128) by lia. exact Vsh.
  - exact Vb.
  - exact Hrw.
  - exact Hraq.
  - intros x Hx. apply Hrat. rewrite Blen. lia.
Qed.

Lemma vd_seatE_at : forall CTX CTX0 CW E P (k : nat),
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_iframe E P -> vrd_iregs B E P -> vrd_icur B E P ->
  getr (ip_regs P) 11 = w64 (ie_text E + ie_len E) ->
  st_ok_pi (fx := ip_fx P) SEGS VAL
    (vd_E (ip_regs P) (ip_p P) (ie_text E + ie_len E) 0 (Z.of_nat (ie_d E) + 1)) (vd_ssE k)
    (restrict (w_H (ip_W P)) (@YK11.mkst (ip_fx P) (ip_regs P) (w64 (A_IPC k)) (ip_mem P) (YK11.seg_rom SEGS)))
  /\ sh_ok SEGS (SOff 26 0) vd_SHE
      (vd_E (ip_regs P) (ip_p P) (ie_text E + ie_len E) 0 (Z.of_nat (ie_d E) + 1))
      (mrestrict (w_H (ip_W P)) (ip_mem P)).
Proof.
  intros CTX CTX0 CW E P k HEN HFR HRG HCU R11.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (vd_bounds CTX CTX0 CW E P HEN HFR HCU)
    as (Bq1 & Bq2 & Bq8 & Bsp & Bsp46 & Bspq & Bspc & Bt4 & (Btp & Bpe) & Btc & Bac & Blen & Bam).
  pose proof HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  pose proof HCU as (Hinok & Hraq & Hsrc & _).
  pose proof Hinok as (Vp & Ve & Vd & Hrw & _ & _ & _ & _ & _ & Hgarr & _ & Hd32).
  pose proof HFR as (Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Vsh & _).
  assert (R2 : getr (ip_regs P) 2 = w64 (spZ (ip_regs P)))
    by (unfold w64, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
  apply (vd_seatE (ip_fx P) (ip_W P) (ip_regs P) (ip_mem P) (ie_q E) (spZ (ip_regs P)) (ip_p P)
           (ie_text E + ie_len E) (Z.of_nat (ie_d E) + 1) k R2 G8 G9 R11 G26 G27);
    try lia.
  - exact Vp.
  - exact Ve.
  - exact Vd.
  - replace (spZ (ip_regs P) + 16) with (spZ (ie_regs E) - 128) by lia. exact Vsh.
  - exact Hraq.
Qed.

(* the live registers after a run that keeps the atoms and the two seated expressions *)
Definition vd_live : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma vd_regs_after : forall (fxP : YK11.FPState) (H : word -> bool) E' ss ms regs0 extra,
  st_ok_pi (fx := fxP) SEGS VAL E' ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E' ->
  sr_get (ss_regs ss) 9%bv = SOff 8 16 -> sr_get (ss_regs ss) 27%bv = vv_sh 8 0 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv = true ->
  getr regs0 9 = sv_denot E' (SOff 8 16) -> getr regs0 27 = sv_denot E' (vv_sh 8 0) ->
  forall r, In r vd_live -> getr (ms_regs ms) r = getr regs0 r.
Proof.
  intros fxP H E' ss ms regs0 extra HS HA H9 H27 Hl R9 R27 r Hr.
  pose proof (st_ok_pi_restrict_reg (fx := fxP) H E' ss ms r HS) as Hg.
  assert (HK : forall r', In r' [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv ->
                 getr (ms_regs ms) r' = getr regs0 r')
    by exact (regs_kept_of_st_ok_pi (fx := fxP) E' ss (restrict H ms) regs0 extra
                [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv HS HA Hl).
  unfold vd_live in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ first [ rewrite H9 in Hg; rewrite Hg; symmetry; exact R9
            | rewrite H27 in Hg; rewrite Hg; symmetry; exact R27
            | apply HK; cbn; tauto ] |]).
  destruct Hr.
Qed.

(* ---- the model at the separator ---- *)

Lemma vd_jsep_comma : forall d o n cap acc f r c r1,
  PjGrammar.skip r = r -> r = c :: r1 -> c = 44 ->
  vrd_jsep d o n cap acc f r = PjGrammar.jrl prh_jr_strtod f d o n cap acc r1.
Proof.
  intros d o n cap acc f r c r1 Hsk Hr Hc. unfold vrd_jsep. rewrite Hsk, Hr, Hc. reflexivity.
Qed.

Lemma vd_jsep_closer : forall d o n cap acc f r c r1,
  PjGrammar.skip r = r -> r = c :: r1 -> c = PjGrammar.closer o ->
  vrd_jsep d o n cap acc f r = PjGrammar.jret (PjGrammar.mk o (rev acc), r1).
Proof.
  intros d o n cap acc f r c r1 Hsk Hr Hc. unfold vrd_jsep. rewrite Hsk, Hr, Hc.
  replace (PjGrammar.closer o =? 44) with false
    by (unfold PjGrammar.closer; destruct o; reflexivity).
  rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma vd_jsep_refuse_nil : forall d o n cap acc f r,
  PjGrammar.skip r = r -> r = [] -> vrd_jsep d o n cap acc f r = PjGrammar.jrefuse.
Proof. intros d o n cap acc f r Hsk Hr. unfold vrd_jsep. rewrite Hsk, Hr. reflexivity. Qed.

Lemma vd_jsep_refuse_other : forall d o n cap acc f r c r1,
  PjGrammar.skip r = r -> r = c :: r1 -> c <> 44 -> c <> PjGrammar.closer o ->
  vrd_jsep d o n cap acc f r = PjGrammar.jrefuse.
Proof.
  intros d o n cap acc f r c r1 Hsk Hr H44 Hcl. unfold vrd_jsep. rewrite Hsk, Hr.
  rewrite (proj2 (Z.eqb_neq c 44) H44), (proj2 (Z.eqb_neq c (PjGrammar.closer o)) Hcl). reflexivity.
Qed.

(* the position the step hands on: new machine state, cursor, fuel and block list *)
Definition vd_pos (P : vrd_ipos) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k p : Z)
  (f : nat) (D : list (Z * Z)) : vrd_ipos :=
  MkIPos (ip_fx P) (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) regs mem md k
    (ip_n P) (ip_cap P) (ip_kids P) (ip_keys P) p (ip_acc P) f (ip_cont P)
    (ip_ok P) (ip_tr P) D (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P).

Ltac vd_proj := unfold vd_pos; cbn [ip_fx ip_ly ip_S ip_Hp ip_W ip_regs ip_mem ip_md ip_k ip_n ip_cap ip_kids
  ip_keys ip_p ip_acc ip_f ip_cont ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran].

(* the model's answer for the whole call, from the position's factorisation at okr = [] *)
Lemma vd_answer : forall E P, vrd_imodel E P ->
  PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E)
    (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P) =
  (fst (fst (ip_cont P [])), ip_tr P ++ snd (fst (ip_cont P [])), snd (ip_cont P [])).
Proof.
  intros E P (_ & HF & _). pose proof (HF []) as H. rewrite app_nil_r in H. exact H.
Qed.

(* the memory a chunk of the symbolic state holds, after a run *)
Lemma vd_chunk_val : forall (fxP : YK11.FPState) (H : word -> bool) E ss ms i r j off (n : N) e v,
  st_ok_pi (fx := fxP) SEGS VAL E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal n e)) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem SEGS (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
  intros fxP H E ss ms i r j off n e v HS Hi Hj He Hv Hn.
  unfold st_ok_pi, abs_ss in HS.
  pose proof (st_ok_mem_ok SEGS E _ _ HS) as (_ & Hrs & _).
  cbn [ss_mem setpc] in Hrs.
  pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
  cbn [ms_mem restrict] in Hcs |- *.
  apply (val_of_chunk_ok SEGS E _ _ off n e v); [|exact He | exact Hv | exact Hn].
  exact (proj1 (Forall_forall _ _) Hcs _ (nth_error_In _ _ Hj)).
Qed.

(* the bytes a run of this step leaves alone: everything below the allocator ceiling *)
Lemma vd_keep_low : forall (H : word -> bool) (m m' : word -> option byte) (Wset Pz : Z -> Prop),
  (forall x : word, ~ Wset (bv_unsigned x) -> mrestrict H m' x = mrestrict H m x) ->
  (forall a, Wset a -> alloc_ceiling <= a) -> (forall a, Pz a -> 0 <= a < alloc_ceiling) ->
  rd_keep SEGS (mrestrict H m) (mrestrict H m') Pz.
Proof.
  intros H m m' Wset Pz HK HW HP.
  pose proof asan_consts as ((Hc1 & Hc2) & _).
  assert (HN : forall a, Pz a -> ~ Wset (bv_unsigned (Z_to_bv 64 a))).
  { intros a Ha. destruct (HP a Ha) as (Ha0 & Ha1).
    rewrite unsigned_lit_small by lia. intros Hw. pose proof (HW a Hw). lia. }
  split.
  - intros a Ha. unfold mbyte. rewrite (HK (Z_to_bv 64 a)) by (apply HN; exact Ha). reflexivity.
  - intros a Ha Hw. unfold writable_at, wview in *.
    rewrite (HK (Z_to_bv 64 a)) by (apply HN; exact Ha). exact Hw.
Qed.


(* ---- from IvalL_Drep.v (sub-lane) ---- *)
(* ==== PART D (WalkIval.IvalL.PartDRep): the pure representation lemmas of the exits ==== *)

(* a partly built container, freeable to depth S k (proved separately and copied verbatim) *)

(* a closed container (proved separately and copied verbatim) *)
Lemma vv_node_close : forall m lblk v (o : bool) kids keys n cap Di (acc : list (list Z * jv)),
  pj_hdrR SEGS m v (if o then 6 else 5) 0 0 kids keys n cap -> (o = false -> keys = 0) ->
  n = Z.of_nat (length acc) -> n <= cap -> 0 < cap ->
  lblk kids (56 * cap) -> (o = true -> lblk keys (8 * cap)) ->
  (if o then pj_memsR SEGS m lblk (pj_nodeR SEGS m lblk) kids keys (rev acc) Di
   else pj_itemsR (pj_nodeR SEGS m lblk) kids (map snd (rev acc)) Di) ->
  NoDup (kids_blkR kids cap ++ keys_blkR (if o then 6 else 5) keys cap ++ Di) ->
  pj_apartR (kids_blkR kids cap ++ keys_blkR (if o then 6 else 5) keys cap ++ Di) v ->
  pj_nodeR SEGS m lblk v (PjGrammar.mk o (rev acc))
    (kids_blkR kids cap ++ keys_blkR (if o then 6 else 5) keys cap ++ Di).
Proof.
  intros m lblk v o kids keys n cap Di acc Hh Hko Hn Hnc Hc Hk Hky Hit Hnd Hap.
  assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (ED : kids_blkR kids cap ++ keys_blkR (if o then 6 else 5) keys cap ++ Di =
               (kids, 56 * cap) :: (if o then [(keys, 8 * cap)] else []) ++ Di).
  { unfold kids_blkR, keys_blkR. rewrite Ec. destruct o; reflexivity. }
  rewrite ED in Hnd, Hap |- *.
  destruct o.
  - split; [exact Hnd|]. split; [exact Hap|].
    exists 0, 0, kids, keys, n, cap. split; [exact Hh|].
    split; [reflexivity|]. split; [rewrite length_rev; exact Hn|]. split; [exact Hnc|].
    split; [right; split; [exact Hc|split; [exact Hk|exact (Hky eq_refl)]]|].
    exists Di. rewrite Ec. split; [reflexivity|exact Hit].
  - specialize (Hko eq_refl). subst keys.
    split; [exact Hnd|]. split; [exact Hap|].
    exists 0, 0, kids, 0, n, cap. split; [exact Hh|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [rewrite length_map, length_rev; exact Hn|]. split; [exact Hnc|].
    split; [right; split; [exact Hc|exact Hk]|].
    exists Di. rewrite Ec. split; [reflexivity|exact Hit].
Qed.

(* the list from the n-th element on, when that element exists *)
Lemma vv_skipn_nth_error : forall (l : list Z) n c, nth_error l n = Some c -> skipn n l = c :: skipn (S n) l.
Proof.
  induction l as [|b r IH]; intros [|n] c H; cbn [nth_error skipn] in *; try discriminate.
  - injection H as Hb. subst b. reflexivity.
  - apply IH. exact H.
Qed.

Definition vv_Dfix (E : vrd_ient) (P : vrd_ipos) (Di : list (Z * Z)) : list (Z * Z) :=
  kids_blkR (ip_kids P) (ip_cap P) ++ keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) ++ Di.

(* the blocks a closed / partly built container owns, in the shape pj_nodeR and pj_fdR force *)
Lemma vv_exit_rep : forall CTX CTX0 CW E P,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_inode E P [] -> vrd_icur B E P -> vrd_ijrn B ARx SK E P ->
  vrd_imodel E P -> 0 < ip_n P ->
  exists D', Permutation (ip_D P) D' /\
    pj_nodeR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (prh_lin (ip_Lam P)) (ie_v E)
      (PjGrammar.mk (ie_o E) (rev (ip_acc P))) D' /\
    pj_fdR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (prh_lin (ip_Lam P)) (PjGrammar.MAXD - ie_d E) (ie_v E) D'.
Proof.
  intros CTX CTX0 CW E P HEN HN HCU HJN HMD Hnpos.
  destruct (vv_D_apart CTX CTX0 CW E P HEN HJN HCU HMD) as (HND & _ & _ & HDAP).
  pose proof HN as (HHDR & Hn0 & _ & _ & Hlin & Hlen & (Di & HPD & HIT) & _ & _ & _ & _ & Hky0).
  pose proof HMD as (_ & _ & _ & _ & _ & _ & HDEP & _).
  pose proof HCU as (HIN & _).
  pose proof HIN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd).
  assert (Hcpos : 0 < ip_cap P) by lia.
  destruct (Hlin Hcpos) as (HLk & HLy).
  assert (HdM : (ie_d E < PjGrammar.MAXD)%nat) by (unfold PjGrammar.MAXD; lia).
  assert (HP' : Permutation (ip_D P) (vv_Dfix E P Di)) by exact HPD.
  assert (HND' : NoDup (vv_Dfix E P Di)).
  { apply NoDup_ListNoDup. eapply Permutation_NoDup; [exact HP'|]. apply NoDup_ListNoDup. exact HND. }
  assert (HAP' : pj_apartR (vv_Dfix E P Di) (ie_v E)).
  { intros b x Hb Hx. exact (HDAP b x (Permutation_in _ (Permutation_sym HP') Hb) Hx). }
  exists (vv_Dfix E P Di). split; [exact HP'|]. split.
  - exact (vv_node_close _ _ (ie_v E) (ie_o E) (ip_kids P) (ip_keys P) (ip_n P) (ip_cap P) Di (ip_acc P)
             HHDR Hky0 (eq_sym Hlen) (proj2 Hn0) Hcpos HLk HLy HIT HND' HAP').
  - replace (PjGrammar.MAXD - ie_d E)%nat with (S (PjGrammar.MAXD - S (ie_d E)))%nat
      by (unfold PjGrammar.MAXD in *; lia).
    assert (HIT' : pf_itemsR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (prh_lin (ip_Lam P))
              (pj_fdR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (prh_lin (ip_Lam P))
                 (PjGrammar.MAXD - S (ie_d E)))
              (ie_o E) (ip_kids P) (ip_keys P) (Z.to_nat (ip_n P)) Di).
    { replace (Z.to_nat (ip_n P)) with (length (ip_acc P)) by lia.
      destruct (ie_o E).
      - rewrite <- (length_rev (ip_acc P)).
        apply (vrd_fd_mems _ (rev (ip_acc P))).
        + apply Forall_forall. intros mm _. apply vrd_nodefd_all.
        + exact HIT.
        + apply Forall_rev. exact HDEP.
      - rewrite <- (length_rev (ip_acc P)), <- (length_map snd (rev (ip_acc P))).
        apply (vrd_fd_items _ (map snd (rev (ip_acc P)))).
        + apply Forall_forall. intros u _. apply vrd_nodefd_all.
        + exact HIT.
        + apply Forall_map. apply Forall_rev. exact HDEP. }
    refine (vv_fd_node _ _ _ (ie_v E) _ (ip_kids P) (ip_keys P) (ip_n P) (ip_cap P) (ie_o E) Di (vv_Dfix E P Di)
              HHDR HND' HAP' Hcpos HLk Hn0 _ HIT' _).
    + destruct (ie_o E); [exact (HLy eq_refl) | exact (Hky0 eq_refl)].
    + assert (Ec : (ip_cap P =? 0) = false) by (apply Z.eqb_neq; lia).
      unfold vv_Dfix, kids_blkR, keys_blkR. rewrite Ec.
      destruct (ie_o E); exact (Permutation_refl _).
Qed.

(* the two moves only see their block list up to order *)
Lemma vv_blocks_move_perm : forall ly0 S0 ly1 S1 D D' tr x d,
  Permutation D D' -> rd_blocks_move B ly0 S0 ly1 S1 D tr x d -> rd_blocks_move B ly0 S0 ly1 S1 D' tr x d.
Proof.
  intros ly0 S0 ly1 S1 D D' tr x d HP (H1 & H2 & H3 & H4).
  split; [|split; [|split; [exact H3 | exact H4]]].
  - intros a k Hin. apply H1. exact (Permutation_in _ (Permutation_sym HP) Hin).
  - eapply Permutation_trans; [exact H2|]. apply Permutation_app_tail. unfold prhReader_ab.
    apply Permutation_map. exact HP.
Qed.

Lemma vv_ledger_move_perm : forall Lam peak cnt fail ran most ok gt tr D D' Lam' peak' cnt' fail' ran',
  Permutation D D' ->
  rd_ledger_move Lam peak cnt fail ran most ok gt tr D Lam' peak' cnt' fail' ran' ->
  rd_ledger_move Lam peak cnt fail ran most ok gt tr D' Lam' peak' cnt' fail' ran'.
Proof.
  intros Lam peak cnt fail ran most ok gt tr D D' Lam' peak' cnt' fail' ran' HP (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  assert (HLn : length D = length D') by (apply Permutation_length; exact HP).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [eapply Permutation_trans; [exact H4 | apply Permutation_app_tail; exact HP]|].
  split; [eapply Permutation_trans; [apply Permutation_map; apply Permutation_sym; exact HP | exact H5]|].
  split; [rewrite <- HLn; exact H6 | exact H7].
Qed.

(* the user bytes a finished run holds are paid for by the text it ate (PjGrammar.G10_1_items) *)
Lemma vv_held_bound : forall CTX CTX0 CW E P r2 okr,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_imodel E P ->
  PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P) =
    (Some (PjGrammar.mk (ie_o E) (rev (ip_acc P)), r2), ip_tr P, okr) ->
  Ledger.lsum (ip_D P) <= 224 * (Z.of_nat (length (rest_atR (ie_tb E) (ie_text E) (ie_p E))) - Z.of_nat (length r2)).
Proof.
  intros CTX CTX0 CW E P r2 okr HEN HMD HJ.
  destruct HMD as (_ & _ & _ & _ & _ & _ & _ & HLS & _). rewrite HLS.
  destruct HEN as (_ & _ & _ & _ & _ & _ & Hnth & _).
  assert (HR : rest_atR (ie_tb E) (ie_text E) (ie_p E) =
               (if ie_o E then 123 else 91) :: skipn (S (Z.to_nat (ie_p E - ie_text E))) (ie_tb E))
    by (unfold rest_atR; exact (vv_skipn_nth_error _ _ _ Hnth)).
  rewrite HR in HJ |- *.
  exact (PjGrammar.G10_1_items _ _ _ _ _ _ _ _ _ _ HJ).
Qed.

(* the text at the cursor, one byte at a time *)
Lemma vd_rest_cons : forall tb text p c, 0 < text -> text <= p ->
  nth_error tb (Z.to_nat (p - text)) = Some c -> rest_atR tb text p = c :: rest_atR tb text (p + 1).
Proof.
  intros tb text p c Ht Hp H. unfold rest_atR.
  replace (Z.to_nat (p + 1 - text)) with (S (Z.to_nat (p - text))) by lia.
  exact (vv_skipn_nth_error _ _ _ H).
Qed.

Lemma vd_rest_end : forall tb text len p, Z.of_nat (length tb) = len -> 0 < text -> p = text + len ->
  rest_atR tb text p = [].
Proof. intros tb text len p Hl Ht Hp. unfold rest_atR. apply skipn_all2. lia. Qed.

Lemma vv_rest_len : forall tb text p c, 0 < text -> text <= p ->
  nth_error tb (Z.to_nat (p - text)) = Some c ->
  (length (rest_atR tb text p) = S (length (rest_atR tb text (p + 1))))%nat.
Proof. intros tb text p c Ht Hp H. rewrite (vd_rest_cons tb text p c Ht Hp H). reflexivity. Qed.

(* the refusal exit's cursor fact, from the position's own cursor *)
Lemma vv_in_after : forall E P,
  vrd_icur B E P ->
  pj_in_afterR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (ie_q E) (ie_text E) (ie_len E)
    (Z.of_nat (ie_d E) + 1) 33.
Proof.
  intros E P HCU. destruct HCU as (HIN & _).
  destruct HIN as (H0 & H8 & H16 & Hrw & _ & _ & _ & Hp & _ & _ & _ & Hd).
  exists (ip_p P), (Z.of_nat (ie_d E) + 1).
  split; [exact Hp|]. split; [lia|]. split; [exact H0|]. split; [exact H8|]. split; [exact H16 | exact Hrw].
Qed.


(* ---- from IvalL_Dstore.v (sub-lane) ---- *)
(* ==== the transport of a loop position across a store into a SET X of addresses: VrdCurStore.v's
   vk_cur_store_keep with the window [a0, a0 + n) replaced by X (the cursor's p field [q, q + 8) and its depth
   word [q + 16, q + 20)). The depth store changes the cursor's depth word, so vrd_icur is NOT produced and
   pj_in_okR is neither assumed nor concluded: the ledger, the cursor's shadow range, the text window and the
   presence of every byte come back as separate conjuncts. Presence inside X is the journal's stack presence
   (X lies in rd_fp q v above the ceiling, so in the caller window [sp0, sp0 + e)). ==== *)

(* a position moved to a new machine state and cursor; every other field is P's *)
Definition vv_movep (P : vrd_ipos) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k p : Z)
  : vrd_ipos :=
  MkIPos (ip_fx P) (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) regs mem md k
    (ip_n P) (ip_cap P) (ip_kids P) (ip_keys P) p (ip_acc P) (ip_f P) (ip_cont P)
    (ip_ok P) (ip_tr P) (ip_D P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P).

(* ---- the byte-level keep outside a set ---- *)
Lemma vv_keep_rd : forall (H : word -> bool) (m m' : word -> option byte) (X Pz : Z -> Prop),
  (forall x : word, ~ X (bv_unsigned x) -> mrestrict H m' x = mrestrict H m x) ->
  (forall a, Pz a -> 0 <= a < 2 ^ 64 /\ ~ X a) ->
  rd_keep SEGS (mrestrict H m) (mrestrict H m') Pz.
Proof.
  intros H m m' X Pz HK HP. split.
  - intros a Ha. destruct (HP a Ha) as [Hr Hn]. unfold mbyte.
    rewrite (HK (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; exact Hn). reflexivity.
  - intros a Ha Hw. destruct (HP a Ha) as [Hr Hn]. unfold writable_at, wview in *.
    rewrite (HK (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; exact Hn). exact Hw.
Qed.

Lemma vv_keep_av : forall (H : word -> bool) (m m' : word -> option byte) (X : Z -> Prop) a,
  (forall x : word, ~ X (bv_unsigned x) -> mrestrict H m' x = mrestrict H m x) ->
  0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros H m m' X a HK Hr Hn. unfold aview, mbyte.
  rewrite (HK (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; exact Hn). reflexivity.
Qed.

Lemma vv_keep_ra : forall (H : word -> bool) (m m' : word -> option byte) (X : Z -> Prop) a n,
  (forall x : word, ~ X (bv_unsigned x) -> mrestrict H m' x = mrestrict H m x) ->
  (forall z, X z -> 2 ^ 46 <= z) -> 0 <= a -> a + n <= 2 ^ 48 ->
  range_addressable (aview SEGS H m) SHADOW_OFF a n -> range_addressable (aview SEGS H m') SHADOW_OFF a n.
Proof.
  intros H m m' X a n HK Hlo Ha Han HR x Hx. destruct (HR x Hx) as (s & Hs & Hok).
  exists s. split; [|exact Hok]. unfold shadow_of_addr in *.
  assert (0 <= x / 8 < 2 ^ 45) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (vv_keep_av H m m' X _ HK);
    [exact Hs | unfold SHADOW_OFF; lia | intros Hw; pose proof (Hlo _ Hw); unfold SHADOW_OFF in *; lia].
Qed.

Lemma vv_keep_hull : forall (H : word -> bool) (m m' : word -> option byte) (X : Z -> Prop) a n,
  (forall x : word, ~ X (bv_unsigned x) -> mrestrict H m' x = mrestrict H m x) ->
  (forall z, X z -> 2 ^ 46 <= z) -> 0 <= a -> a + n <= 2 ^ 48 -> 0 < n ->
  shadow_hull_vis (aview SEGS H m) a n -> shadow_hull_vis (aview SEGS H m') a n.
Proof.
  intros H m m' X a n HK Hlo Ha Han Hn HV s Hs. unfold shadow_addr in Hs.
  assert (0 <= (a + n - 1) / 8 < 2 ^ 45) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (0 <= a / 8) by (apply Z.div_pos; lia).
  assert (Hs2 : 0 <= s < 2 ^ 46).
  { split.
    - assert (0 <= (SHADOW_OFF + a / 8) / 8 * 8) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; unfold SHADOW_OFF; lia). lia.
    - assert ((SHADOW_OFF + (a + n - 1) / 8) / 8 * 8 <= SHADOW_OFF + (a + n - 1) / 8) by
        (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
      unfold SHADOW_OFF in *. lia. }
  rewrite (vv_keep_av H m m' X _ HK); [apply HV; exact Hs | lia | intros Hw; pose proof (Hlo _ Hw); lia].
Qed.

(* ---- the harness blocks lie below the allocator ceiling ---- *)
Lemma vv_lam_low : forall ly S Hp W mem md Lam peak cnt fail ran most own a k,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  0 <= k /\ 4096 <= a /\ a + k <= alloc_ceiling.
Proof.
  intros ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HL0 Hin.
  destruct (prh_ledger_hblock (L := A_prog_listing) (PA := PAI) B ly S Hp W mem Lam peak cnt fail ran a k most own
              HL0 Hin)
    as (Hk & Hab & _).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4 & Hc & _).
  pose proof (req_size_pos (k + cf_head)) as Hrq. pose proof (@cf_head_nonneg cp) as Hch.
  destruct Hrq as [_ Hrq]; [lia|]. lia.
Qed.

(* ---- the bytes below the allocator ceiling are kept ---- *)
Lemma vv_keep_low : forall (H : word -> bool) (m m' : word -> option byte) (X Pz : Z -> Prop),
  (forall x : word, ~ X (bv_unsigned x) -> mrestrict H m' x = mrestrict H m x) ->
  (forall z, X z -> alloc_ceiling <= z) -> (forall a, Pz a -> 0 <= a < alloc_ceiling) ->
  rd_keep SEGS (mrestrict H m) (mrestrict H m') Pz.
Proof.
  intros H m m' X Pz HK HX HP. apply (vv_keep_rd H m m' X Pz HK).
  intros a Ha. pose proof asan_consts as (C1 & _). destruct (HP a Ha). split; [lia|].
  intros Hx. pose proof (HX a Hx). lia.
Qed.

Lemma vv_apresent_keep : forall (H : word -> bool) (m m' : word -> option byte) (X : Z -> Prop) a,
  (forall x : word, ~ X (bv_unsigned x) -> mrestrict H m' x = mrestrict H m x) ->
  0 <= a < 2 ^ 64 -> ~ X a -> apresent H m a -> apresent H m' a.
Proof.
  intros H m m' X a HK Hr Hn [Hh (b & Hb)]. split; [exact Hh|]. exists b.
  pose proof (HK (Z_to_bv 64 a)) as E. rewrite unsigned_lit_small in E by lia. specialize (E Hn).
  unfold mrestrict in E. rewrite Hh in E. rewrite E. exact Hb.
Qed.

(* presence of every address: outside X by the keep; X lies in [lo, hi), where the new memory is present *)
Lemma vv_apresent_all : forall (H : word -> bool) (m m' : word -> option byte) (X : Z -> Prop) lo hi a,
  (forall x : word, ~ X (bv_unsigned x) -> mrestrict H m' x = mrestrict H m x) ->
  (forall z, X z -> lo <= z < hi) -> (forall z, lo <= z < hi -> apresent H m' z) ->
  apresent H m a -> apresent H m' a.
Proof.
  intros H m m' X lo hi a HK HX Hin [Hh (b & Hb)].
  assert (Ez : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a)) = Z_to_bv 64 a) by apply Z_to_bv_bv_unsigned.
  destruct (Z_lt_dec (bv_unsigned (Z_to_bv 64 a)) lo) as [H1 | H1];
    [| destruct (Z_lt_dec (bv_unsigned (Z_to_bv 64 a)) hi) as [H2 | H2]].
  2:{ destruct (Hin (bv_unsigned (Z_to_bv 64 a)) ltac:(lia)) as [Hh' (b' & Hb')]. rewrite Ez in Hh', Hb'.
      split; [exact Hh'|]. exists b'. exact Hb'. }
  all: split; [exact Hh|]; exists b;
    pose proof (HK (Z_to_bv 64 a)) as E;
    assert (Hn : ~ X (bv_unsigned (Z_to_bv 64 a))) by (intros Hx; pose proof (HX _ Hx); lia);
    specialize (E Hn); unfold mrestrict in E; rewrite Hh in E; rewrite E; exact Hb.
Qed.

(* the harness blocks a position holds (its D) lie below the ceiling *)
Lemma vv_D_low : forall ly S Hp W mem md ly0 S0 D tr rest d b x,
  ARx ly S Hp W mem md -> rd_blocks_move B ly0 S0 ly S D tr rest d -> In b D -> pj_holdsR b x ->
  4096 <= x < alloc_ceiling.
Proof.
  intros ly S Hp W mem md ly0 S0 D tr rest d [a k] x HAR (_ & HPm & _) Hin Hx.
  unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
  assert (Hab : In (a - cf_head, k + cf_head) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HPm)). apply in_or_app. left. unfold prhReader_ab.
    exact (in_map (fun ak => (fst ak - cf_head, snd ak + cf_head)) D (a, k) Hin). }
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4 & Hc & _).
  pose proof (@cf_head_nonneg cp) as Hch.
  destruct (req_size_pos (k + cf_head)) as [_ Hrq]; [lia|]. lia.
Qed.

(* the stack bounds every position needs *)
Lemma vv_sp_bounds : forall CTX CTX0 CW E, vrd_ient_ok B ARx CTX CTX0 CW E ->
  alloc_ceiling <= spZ (ie_regs E) /\ 0 <= ie_e E /\ spZ (ie_regs E) + ie_e E <= 2 ^ 47 /\
  spZ (ie_regs E) <= ie_q E /\ ie_q E + 24 <= spZ (ie_regs E) + ie_e E /\ 4096 <= ie_v E.
Proof.
  intros CTX CTX0 CW E HEN.
  destruct HEN as ((HAF & _) & _ & _ & _ & HRD & _).
  destruct HAF as (_ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & HS0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
  destruct HRD as (_ & _ & _ & _ & _ & (He0 & _ & Hetop & _) & Hq0 & Hq24 & _ & _ & _ & _ & (Hv4 & _) & _).
  repeat split; lia.
Qed.

Ltac vv_mproj := unfold vv_movep; cbn [ip_fx ip_ly ip_S ip_Hp ip_W ip_regs ip_mem ip_md ip_k ip_n ip_cap ip_kids
  ip_keys ip_p ip_acc ip_f ip_cont ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran].

(* ==== THE TRANSPORT OVER A SET ==== *)
Lemma vv_store_keepX : forall CTX CTX0 CW E P Dx regs mem' md' k' p' (X : Z -> Prop),
  pi_frame F_parse_items = 144 -> pi_s0cur F_parse_items = Some 0 ->
  vrd_ient_ok B ARx CTX CTX0 CW E ->
  vrd_iframe E P -> vrd_inode E P Dx -> vrd_icur B E P -> vrd_ijrn B ARx SK E P ->
  (forall a, X a -> alloc_ceiling <= a < 2 ^ 64) ->
  (forall a, X a -> inFP (rd_fp (ie_q E) (ie_v E)) a) ->
  (forall a, X a -> ~ (spZ (ie_regs E) - 144 <= a < spZ (ie_regs E))) ->
  (forall x : word, ~ X (bv_unsigned x) ->
     mrestrict (w_H (ip_W P)) mem' x = mrestrict (w_H (ip_W P)) (ip_mem P) x) ->
  spZ regs = spZ (ip_regs P) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
    (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem' md' k' (ie_CW E) ->
  vrd_iframe E (vv_movep P regs mem' md' k' p') /\
  vrd_inode E (vv_movep P regs mem' md' k' p') Dx /\
  vrd_ijrn B ARx SK E (vv_movep P regs mem' md' k' p') /\
  prh_ledger B (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem'
    (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P) (ie_most E) (ie_own E) /\
  range_addressable (aview SEGS (w_H (ip_W P)) mem') SHADOW_OFF (ie_q E) 24 /\
  src_rd (ip_W P) mem' (ie_text E) (ie_tb E) /\
  (forall a, apresent (w_H (ip_W P)) (ip_mem P) a -> apresent (w_H (ip_W P)) mem' a).
Proof.
  intros CTX CTX0 CW E P Dx regs mem' md' k' p' X Himg Hs0c HEN HFR HND HCU HJN Hxr Hwfp Hwfr HK Hsp HJ'.
  pose proof asan_consts as (C1 & _).
  pose proof (proj1 H_head) as HW.
  destruct (vv_sp_bounds CTX CTX0 CW E HEN) as (Bsp & Be0 & Bse & Bq0 & Bq24 & Bv).
  assert (Bv56 : ie_v E + 56 <= alloc_ceiling) by exact (vrd_node_low B ARx HL LAWS CTX CTX0 CW E HEN).
  pose proof HJN as ((HAR & _) & _).
  pose proof HJN as (_ & _ & _ & _ & _ & HBM & _).
  assert (Bsp0 : 0 <= spZ (ie_regs E) - 144).
  { pose proof HFR as (Hf0 & _). rewrite <- Hf0. unfold spZ.
    pose proof (bv_unsigned_in_range 64 (getr (ip_regs P) 2%bv)) as Hr. lia. }
  assert (HXlo : forall z, X z -> alloc_ceiling <= z) by (intros z Hz; exact (proj1 (Hxr z Hz))).
  assert (HX46 : forall z, X z -> 2 ^ 46 <= z) by (intros z Hz; pose proof (Hxr z Hz); lia).
  assert (HKfr : rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem')
                   (fun x => spZ (ie_regs E) - 144 <= x < spZ (ie_regs E))).
  { apply (vv_keep_rd _ (ip_mem P) mem' X _ HK). intros a Ha. split; [lia|]. intros Hw. exact (Hwfr a Hw Ha). }
  assert (HKlow : forall Pz, (forall a, Pz a -> 0 <= a < alloc_ceiling) ->
     rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem') Pz)
    by (intros Pz HP; exact (vv_keep_low _ (ip_mem P) mem' X Pz HK HXlo HP)).
  assert (HDlow : forall b x, In b (ip_D P) -> pj_holdsR b x -> 4096 <= x < alloc_ceiling)
    by (intros b x Hb Hx; exact (vv_D_low _ _ _ _ _ _ _ _ _ _ _ _ b x HAR HBM Hb Hx)).
  pose proof HCU as (_ & Hraq & Hsrc & _ & Hled & _ & _).
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - (* the frame *)
    pose proof HFR as (Hf0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 &
      F17 & Fpres).
    unfold vrd_iframe. cbv zeta. vv_mproj.
    split; [rewrite Hsp; exact Hf0|].
    repeat match goal with
    | |- val_mem _ _ _ _ _ /\ _ => split; [eapply VrdFrame.val_mem_keep; [eassumption|];
                                     eapply VrdFrame.rd_keep_mono; [exact HKfr | cbn; intros; lia]|]
    end.
    intros a Ha.
    apply (vv_apresent_keep _ (ip_mem P) mem' X a HK); [lia | intros Hw; exact (Hwfr a Hw Ha) | exact (Fpres a Ha)].
  - (* the node and the trees *)
    pose proof HND as (Hhdr & Hnc & Hcap & Hc0 & Hlin & Hlen & (Di & HPerm & HTree) & Hrw & Hrav & Hrak & Hrakeys & Hkz).
    assert (HDsub : forall b, In b (Dx ++ kids_blkR (ip_kids P) (ip_cap P) ++
                      keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) ++ Di) -> In b (ip_D P))
      by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPerm) Hb)).
    assert (Hkids : 0 < ip_cap P -> In (ip_kids P, 56 * ip_cap P) (ip_D P)).
    { intros Hc. apply HDsub. apply in_or_app. right. apply in_or_app. left. unfold kids_blkR.
      destruct (Z.eqb_spec (ip_cap P) 0); [lia | left; reflexivity]. }
    assert (Hkeys : ie_o E = true -> 0 < ip_cap P -> In (ip_keys P, 8 * ip_cap P) (ip_D P)).
    { intros Ho Hc. apply HDsub. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      unfold keys_blkR. rewrite Ho. destruct (Z.eqb_spec (ip_cap P) 0); [lia | left; reflexivity]. }
    assert (HDi : forall z, rd_blk Di z -> 4096 <= z < alloc_ceiling).
    { intros z Hz. unfold rd_blk in Hz. apply Exists_exists in Hz as (b & Hb & Hz).
      apply (HDlow b z); [|exact Hz]. apply HDsub. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. right. exact Hb. }
    assert (Hkr : forall z, 0 < ip_cap P -> ip_kids P <= z < ip_kids P + 56 * ip_cap P -> 4096 <= z < alloc_ceiling)
      by (intros z Hc Hz; exact (HDlow _ z (Hkids Hc) Hz)).
    assert (Hyr : forall z, ie_o E = true -> 0 < ip_cap P -> ip_keys P <= z < ip_keys P + 8 * ip_cap P ->
                    4096 <= z < alloc_ceiling)
      by (intros z Ho Hc Hz; exact (HDlow _ z (Hkeys Ho Hc) Hz)).
    unfold vrd_inode. cbv zeta. vv_mproj.
    split; [eapply pj_hdrR_keep; [exact Hhdr | apply HKlow; intros; lia]|].
    split; [exact Hnc|]. split; [exact Hcap|]. split; [exact Hc0|]. split; [exact Hlin|]. split; [exact Hlen|].
    split.
    { exists Di. split; [exact HPerm|].
      destruct (ie_o E) eqn:Ho; rewrite ?Ho in HTree.
      - eapply pj_memsR_keep; [exact HTree | intros; assumption | apply HKlow].
        rewrite length_rev, Hlen. intros z [Hz | [Hz | Hz]].
        + assert (0 < ip_cap P) by lia. pose proof (Hkr z ltac:(lia) ltac:(lia)). lia.
        + assert (0 < ip_cap P) by lia. pose proof (Hyr z eq_refl ltac:(lia) ltac:(lia)). lia.
        + pose proof (HDi z Hz). lia.
      - eapply pj_itemsR_keep; [exact HTree | intros; assumption | apply HKlow].
        rewrite length_map, length_rev, Hlen. intros z [Hz | Hz].
        + assert (0 < ip_cap P) by lia. pose proof (Hkr z ltac:(lia) ltac:(lia)). lia.
        + pose proof (HDi z Hz). lia. }
    split.
    { eapply rd_rw_keep; [exact Hrw | apply HKlow]. intros z Hz.
      destruct (Z.eq_dec (ip_cap P) 0) as [Hc | Hc]; [lia|].
      pose proof (Hkr z ltac:(lia) ltac:(lia)). lia. }
    split; [apply (vv_keep_ra _ (ip_mem P) mem' X (ie_v E) 56 HK); [exact HX46 | lia | lia | exact Hrav]|].
    split.
    { intros Hc. pose proof (Hkr (ip_kids P) Hc ltac:(lia)). pose proof (Hkr (ip_kids P + 56 * ip_cap P - 1) Hc ltac:(lia)).
      apply (vv_keep_ra _ (ip_mem P) mem' X _ _ HK); [exact HX46 | lia | lia | exact (Hrak Hc)]. }
    split; [|exact Hkz].
    intros Ho Hc. pose proof (Hyr (ip_keys P) Ho Hc ltac:(lia)).
    pose proof (Hyr (ip_keys P + 8 * ip_cap P - 1) Ho Hc ltac:(lia)).
    apply (vv_keep_ra _ (ip_mem P) mem' X _ _ HK); [exact HX46 | lia | lia | exact (Hrakeys Ho Hc)].
  - (* the journal, the caller window, the read-only view and the chain *)
    pose proof HJN as (HJ & Hwin & Hfz & Hfk & Haro & Hbm & Hch).
    unfold vrd_ijrn. vv_mproj.
    split; [exact HJ'|].
    split.
    { intros a Ha Hnf. rewrite <- (Hwin a Ha Hnf).
      apply (vv_keep_av _ (ip_mem P) mem' X a HK); [lia | intros Hw; exact (Hnf (Hwfp a Hw))]. }
    split; [exact Hfz|]. split; [exact Hfk|].
    split.
    { intros a Hro Hno Herr.
      assert (Hi : in_img SEGS a).
      { destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (@pa_relro_img _ _ PAI a Hr)]. }
      pose proof (@pa_segs_low _ _ PAI a Hi) as Hl. unfold kLowMemEnd in Hl.
      rewrite (vv_keep_av _ (ip_mem P) mem' X a HK);
        [exact (Haro a Hro Hno Herr) | lia | intros Hw; pose proof (HXlo a Hw); lia]. }
    split; [exact Hbm|].
    eapply VrdIElem.vrd_chain_keep_w; try eassumption; try reflexivity.
    intros a Ha Hnf. apply (vv_keep_av _ (ip_mem P) mem' X a HK); [lia | intros Hw; exact (Hnf (Hwfp a Hw))].
  - (* the ledger *)
    eapply prh_ledger_kept_aview; [exact Hled | | | |].
    + intros a Ha. pose proof (@pa_segs_low _ _ PAI a (H_pst a Ha)) as Hl. unfold kLowMemEnd in Hl.
      apply (vv_keep_av _ (ip_mem P) mem' X a HK); [lia | intros Hw; pose proof (HXlo a Hw); lia].
    + intros a k i Hin Hi.
      destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ Hled Hin) as (Hk0 & Hab & _).
      destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & H4 & Hc & _).
      destruct (req_size_pos (k + cf_head)) as [_ Hrq]; [lia|].
      apply (vv_keep_av _ (ip_mem P) mem' X _ HK); [lia | intros Hw; pose proof (HXlo _ Hw); lia].
    + intros a k _ Hab. exact Hab.
    + apply Permutation_refl.
  - (* the cursor's shadow *)
    apply (vv_keep_ra _ (ip_mem P) mem' X (ie_q E) 24 HK); [exact HX46 | lia | lia | exact Hraq].
  - (* the text window *)
    destruct Hsrc as (Hby & Ht4 & Htl & Ham & Hra & Hhull).
    split; [|split; [exact Ht4 | split; [exact Htl | split; [exact Ham | split]]]].
    + unfold PRH_Base.bytes_at in *. eapply garr8_keep; [exact Hby | apply HKlow].
      intros; lia.
    + apply (vv_keep_ra _ (ip_mem P) mem' X _ _ HK); [exact HX46 | lia | lia | exact Hra].
    + intros Hl. apply (vv_keep_hull _ (ip_mem P) mem' X _ _ HK); [exact HX46 | lia | lia | lia | exact (Hhull Hl)].
  - (* presence: outside X by the keep, inside X by the journal's stack presence (X lies in [q, q + 20)) *)
    pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
    assert (HSTK : 0 <= STK_parse_items (ie_d E)).
    { unfold STK_parse_items. rewrite Himg. pose proof (pi_frame_nonneg F_parse_value).
      assert (0 <= LEAF_pv_pi) by (unfold LEAF_pv_pi, zmaxl; cbn [fold_right]; lia).
      assert (0 <= Z.of_nat (PjGrammar.MAXD - ie_d E) * (pi_frame F_parse_value + 144))
        by (apply Z.mul_nonneg_nonneg; lia).
      lia. }
    intros a Ha.
    apply (vv_apresent_all _ (ip_mem P) mem' X
             (spZ (ie_regs E) + ie_e E - (STK_parse_items (ie_d E) + ie_e E)) (spZ (ie_regs E) + ie_e E) a HK);
      [| exact HJpres | exact Ha].
    intros z Hz. pose proof (HXlo z Hz). destruct (Hwfp z Hz) as (r & Hin & Hr).
    cbn [rd_fp In] in Hin. destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia.
Qed.

(* ---- a run that stores nothing leaves the memory alone ---- *)
Lemma vd_frame_ro : forall E' (rs : smem) (m m' : word -> option byte),
  frame_of E' rs m m' -> Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> forall x, m' x = m x.
Proof.
  intros E' rs m m' HF Hro x. apply HF. intros (r & Hin & Hr).
  pose proof (proj1 (Forall_forall _ _) Hro r Hin) as Hw. cbv beta in Hw. lia.
Qed.

Ltac vd_awr_ro :=
  apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
  apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil.

(* the journal only sees the block list up to order *)
Lemma vd_ijrn_perm : forall E P regs mem' md' k' p' f D',
  Permutation (ip_D P) D' ->
  vrd_ijrn B ARx SK E (vv_movep P regs mem' md' k' p') ->
  vrd_ijrn B ARx SK E (vd_pos P regs mem' md' k' p' f D').
Proof.
  intros E P regs mem' md' k' p' f D' HP HJ.
  unfold vrd_ijrn in HJ |- *. unfold vv_movep, vd_pos in HJ |- *.
  cbn [ip_fx ip_ly ip_S ip_Hp ip_W ip_regs ip_mem ip_md ip_k ip_n ip_cap ip_kids ip_keys ip_p ip_acc
       ip_f ip_cont ip_ok ip_tr ip_D ip_Lam ip_peak ip_cnt ip_fail ip_ran] in HJ |- *.
  destruct HJ as (J1 & J2 & J3 & J4 & J5 & J6 & J7).
  split; [exact J1|]. split; [exact J2|]. split; [exact J3|]. split; [exact J4|]. split; [exact J5|].
  split; [exact (vv_blocks_move_perm _ _ _ _ _ _ _ _ _ HP J6) | exact J7].
Qed.

(* the bytes a run over this seat may change: the cursor's p word and its depth word *)
Lemma vd_keepX : forall (E' : env) (rs : smem) (q : Z) (m m' : word -> option byte),
  frame_of E' rs m m' ->
  Forall (fun r => forall o, YP09.r_wlo r <= o < YP09.r_whi r ->
            q <= base_val E' (YP09.r_base r) + o < q + 8 \/
            q + 16 <= base_val E' (YP09.r_base r) + o < q + 20) rs ->
  forall x : word, ~ (q <= bv_unsigned x < q + 8 \/ q + 16 <= bv_unsigned x < q + 20) -> m' x = m x.
Proof.
  intros E' rs q m m' HF HR x Hx. apply HF. intros (r & Hin & Hr).
  pose proof (proj1 (Forall_forall _ _) HR r Hin) as H. cbv beta in H.
  exfalso. apply Hx.
  pose proof (H (bv_unsigned x - base_val E' (YP09.r_base r)) ltac:(lia)) as Hd. lia.
Qed.

Lemma vd_rest_len_eq : forall tb text len p', Z.of_nat (length tb) = len -> text <= p' <= text + len ->
  Z.of_nat (length (rest_atR tb text p')) = text + len - p'.
Proof.
  intros tb text len p' Hl Hp. unfold rest_atR. rewrite length_skipn, Nat2Z.inj_sub by lia. lia.
Qed.

(* a byte that was writable stays writable when presence is kept *)
Lemma vd_writable_keep : forall (H : word -> bool) (m m' : word -> option byte) a,
  writable_at SEGS (mrestrict H m) a -> (apresent H m a -> apresent H m' a) ->
  writable_at SEGS (mrestrict H m') a.
Proof.
  intros H m m' a. unfold writable_at, wview, mrestrict, apresent. cbv beta.
  destruct (H (Z_to_bv 64 a)) eqn:Eh; intros Hw Hp; [exact Hw|].
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
  - destruct (Hp (conj eq_refl (ex_intro _ b eq_refl))) as [_ [b' Hb']]. rewrite Hb'. discriminate.
  - destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

(* THE KIT'S CUT: THE EXIT'S FREE ORDER AND CAPACITY from the separator's batch-kit layer (vv_k1sep), at a later memory that keeps
   the node's bytes and its blocks', over a permutation D' of the block list: the order list is the completed slots'
   then the arrays (VrdIFd.vrd_inode_fo), at both depth bounds the post asks; at the separator's stop (no comma) its
   requests are the model's whole list (vrd_jfsep at okr = []); the caps are VrdIFd.vrd_inode_ncap's *)
Lemma vv_exit_fo : forall CTX CTX0 CW E P (m' : word -> option byte) D',
  vrd_ient_ok B ARx CTX CTX0 CW E -> vv_sep E P ->
  match PjGrammar.skip (rest_atR (ie_tb E) (ie_text E) (ip_p P)) with c :: _ => c <> 44 | [] => True end ->
  Permutation (ip_D P) D' ->
  rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) m' (fun a => ie_v E <= a < ie_v E + 56 \/ rd_blk D' a) ->
  (cf_head = PresetReqAt.HEAD -> forall n, (PjGrammar.MAXD - ie_d E <= n)%nat ->
     exists F, PRH_PjOrder.pj_foR SEGS m' (prh_lin (ip_Lam P)) n (ie_v E) D' F /\
       map (fun b => snd b + cf_head) F =
         prhPi_frees (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P)) /\
  (cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth (PjGrammar.mk (ie_o E) (rev (ip_acc P))) <= n)%nat ->
     exists F, PRH_PjOrder.pj_foR SEGS m' (prh_lin (ip_Lam P)) n (ie_v E) D' F /\
       map (fun b => snd b + cf_head) F =
         prhPi_frees (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P)) /\
  (pj_nodeR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (prh_lin (ip_Lam P)) (ie_v E)
     (PjGrammar.mk (ie_o E) (rev (ip_acc P))) D' ->
   pj_ncapR SEGS m' (ie_v E) (PjGrammar.mk (ie_o E) (rev (ip_acc P)))).
Proof.
  intros CTX CTX0 CW E P m' D' HEN HSEP Hstop HPermD HK.
  pose proof HSEP as (HFR & HRG & HND & HCU & HJN & HMD & Hn0 & Hcont & (HCAP & HNC & (af & HFO & HFL))).
  pose proof HMD as (_ & _ & _ & _ & _ & _ & HDEP & _).
  pose proof HCU as (HIN & _).
  pose proof HIN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdep).
  assert (Hd : (ie_d E < PjGrammar.MAXD)%nat) by (unfold PjGrammar.MAXD; lia).
  (* the model's whole list at the stop *)
  assert (HFr : prhPi_frees (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P) =
                af ++ PresetReqAt.arrz (ie_o E) (Z.to_nat (ip_cap P))).
  { rewrite <- (app_nil_r (ip_ok P)), (HFL []). unfold vrd_jfsep.
    destruct (PjGrammar.skip (rest_atR (ie_tb E) (ie_text E) (ip_p P))) as [|c r1] eqn:Es; [reflexivity|].
    try rewrite Es in Hstop. rewrite (proj2 (Z.eqb_neq c 44) Hstop). reflexivity. }
  (* the order list at S nn, every member at most nn deep *)
  assert (HFOn : forall nn, Forall (fun mm => (PjTree.depth (snd mm) <= nn)%nat) (ip_acc P) ->
            cf_head = PresetReqAt.HEAD ->
            exists F, PRH_PjOrder.pj_foR SEGS m' (prh_lin (ip_Lam P)) (S nn) (ie_v E) D' F /\
              map (fun b => snd b + cf_head) F =
                prhPi_frees (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P)).
  { intros nn Hdacc Hh.
    destruct (vrd_inode_fo B ARx SK LAWS CTX CTX0 CW E P af nn HEN HND HCU HJN HMD HFO Hh Hdacc) as (F & HF & HmF).
    exists F. split; [|rewrite HFr; exact HmF].
    exact (vv_fo_keep _ _ _ _ _ _ _ (vv_foR_perm _ _ _ _ _ _ _ HPermD HF) HK). }
  split; [|split].
  - intros Hh n Hn. destruct n as [|nn]; [lia|].
    exact (HFOn nn (vi_dep_le (ip_acc P) (PjGrammar.MAXD - S (ie_d E)) nn ltac:(lia) HDEP) Hh).
  - intros Hh n Hn. destruct (vv_mk_depth (ie_o E) (ip_acc P) n Hn) as (nn & -> & Hdacc).
    exact (HFOn nn Hdacc Hh).
  - intros HNd. exact (pj_ncapR_keep SEGS _ _ _ _ _ _ HNd (vrd_inode_ncap E P HND HNC HCAP) HK).
Qed.

(* THE HULL USE at an exit on the granted prefix: the call's all-granted trace is the trace so far, then the
   continuation's granted trace (VrdCallPos.vc_gt_split), and the position used at most its events so far
   (VrdIStep.vi_hull_exit, with no callee between) *)
Lemma vv_hull_at_exit : forall E P, vrd_imodel E P ->
  PresetHullBudget.hull_used (ie_S E) (ip_S P)
    (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))).
Proof.
  intros E P HM. pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHU).
  exact (vi_hull_exit _ _ _ (ip_tr P) [] (snd (fst (ip_cont P []))) _ [] (vc_gt_split E P HM) eq_refl HHU
           (PresetHullBudget.hull_used_refl _ _)).
Qed.

(* ---- THE EXIT, from a run that wrote only the cursor's own words ---- *)
Lemma vd_exit_make : forall CTX CTX0 CW E P regs mem' md' k' p' res D' r2 okr (X : Z -> Prop),
  vrd_ient_ok B ARx CTX CTX0 CW E -> vv_sep E P ->
  (forall a, X a -> ie_q E <= a < ie_q E + 8 \/ ie_q E + 16 <= a < ie_q E + 20) ->
  (forall x : word, ~ X (bv_unsigned x) ->
     mrestrict (w_H (ip_W P)) mem' x = mrestrict (w_H (ip_W P)) (ip_mem P) x) ->
  spZ regs = spZ (ip_regs P) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
    (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem' md' k' (ie_CW E) ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 18 = w64 res ->
  (res = 0 \/ res = -1) -> Permutation (ip_D P) D' ->
  (res = 0 -> pj_nodeR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (prh_lin (ip_Lam P)) (ie_v E)
                (PjGrammar.mk (ie_o E) (rev (ip_acc P))) D') ->
  (res = -1 -> pj_fdR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (prh_lin (ip_Lam P))
                 (PjGrammar.MAXD - ie_d E) (ie_v E) D') ->
  PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P) =
    ((if res =? 0 then Some (PjGrammar.mk (ie_o E) (rev (ip_acc P)), r2) else None), ip_tr P, okr) ->
  (res = 0 -> val_mem SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E) 8
                (ie_text E + ie_len E - Z.of_nat (length r2)) /\
              val_mem SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E + 16) 4 (Z.of_nat (ie_d E)) /\
              (Z.of_nat (length r2) <= ie_len E)%Z) ->
  (res = -1 -> exists pa da, val_mem SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E) 8 pa /\
                 val_mem SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E + 16) 4 da /\
                 ie_text E <= pa <= ie_text E + ie_len E /\ Z.of_nat (ie_d E) + 1 <= da <= 33) ->
  (* The kit's cut: the separator test's stop is no comma (the free order's model list at the stop, vv_exit_fo) *)
  match PjGrammar.skip (rest_atR (ie_tb E) (ie_text E) (ip_p P)) with c :: _ => c <> 44 | [] => True end ->
  vrd_iexit_a B ARx SK E (vd_pos P regs mem' md' k' p' (ip_f P) D') res.
Proof.
  intros CTX CTX0 CW E P regs mem' md' k' p' res D' r2 okr X HEN HSEP HX HK Hsp HJ HG3 HG4 HG18 Hres
    HPermD HNodeD HFdD HAns Hcur0 Hcur1 Hstop.
  pose proof HSEP as (HFR & HRG & HND & HCU & HJN & HMD & Hn0 & Hcont & HK1s).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (vd_bounds CTX CTX0 CW E P HEN HFR HCU)
    as (Bq1 & Bq2 & Bq8 & Bsp & Bsp46 & Bspq & Bspc & Bt4 & (Btp & Bpe) & Btc & Bac & Blen & Bam).
  pose proof HMD as (HMok & HMfac & HMlm & HMroom & HMf & HMbb & HMdep & HMls & HMxf & HMlv).
  pose proof HCU as (Hinok & Hraq & Hsrc & Hhome & HLED & Hfrm & Hcnt).
  pose proof Hinok as (Vp0 & Ve0 & Vd0 & Hrw0 & Hq8m & Ht0 & Htl62 & Hpp0 & Hlen0 & Hgarr0 & Hqtx & Hd32).
  pose proof (vrd_node_low B ARx HL LAWS CTX CTX0 CW E HEN) as Hvceil.
  pose proof HEN as ((HAFN & _) & _ & _ & _ & HRD & _).
  pose proof HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNODE & _).
  pose proof HNODE as (Hv4096 & _).
  assert (HXc : forall a, X a -> alloc_ceiling <= a) by (intros a Ha; destruct (HX a Ha); lia).
  destruct (vv_store_keepX CTX CTX0 CW E P [] regs mem' md' k' p' X
              (proj1 H_img) (proj1 (proj2 H_img)) HEN HFR HND HCU HJN
              ltac:(intros a Ha; destruct (HX a Ha); lia)
              ltac:(intros a Ha; unfold rd_fp, inFP;
                    destruct (HX a Ha) as [Hr | Hr];
                    [exists (ie_q E, ie_q E + 8); split; [left; reflexivity | cbn [fst snd]; lia]
                    |exists (ie_q E + 16, ie_q E + 20); split;
                       [right; left; reflexivity | cbn [fst snd]; lia]])
              ltac:(intros a Ha; destruct (HX a Ha); lia)
              HK Hsp HJ)
    as (KFR & KND & KJN & KLED & KRA & KSRC & KPR).
  (* the node and the blocks it owns are below the allocator ceiling, so the cursor's words miss them *)
  destruct (vv_D_apart CTX CTX0 CW E P HEN HJN HCU HMD) as (_ & HDB & _ & _).
  assert (HKnode : rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P)) mem')
                     (fun a => ie_v E <= a < ie_v E + 56 \/ rd_blk D' a)).
  { apply (vd_keep_low _ (ip_mem P) mem' X _ HK HXc).
    intros z [Hz | Hz]; [lia|].
    apply Exists_exists in Hz as ((a, k) & Hin & Hr). unfold pj_holdsR in Hr. cbn [fst snd] in Hr.
    destruct (HDB a k (Permutation_in _ (Permutation_sym HPermD) Hin)) as (Hk & _ & H4 & Hc & _).
    pose proof (@cf_head_nonneg cp). lia. }
  destruct (vv_exit_fo CTX CTX0 CW E P (mrestrict (w_H (ip_W P)) mem') D' HEN HSEP Hstop HPermD HKnode)
    as (HFOn & HFOs & HNCs).
  (* the cursor's end word and its writability ride on *)
  assert (Ve1 : val_mem SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E + 8) 8 (ie_text E + ie_len E)).
  { apply (VrdFrame.val_mem_keep SEGS _ _ _ _ _ Ve0).
    apply (vv_keep_rd _ (ip_mem P) mem' X _ HK).
    intros z Hz. cbv beta in Hz. split; [lia|]. intros HXz. destruct (HX z HXz); lia. }
  assert (Hrw1 : rd_rw SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E) 24)
    by (intros z Hz; exact (vd_writable_keep _ (ip_mem P) mem' z (Hrw0 z Hz) (KPR z))).
  unfold vrd_iexit_a. vd_proj.
  split; [exact KFR|].
  split; [exact (vd_ijrn_perm E P _ _ _ _ _ (ip_f P) D' HPermD KJN)|].
  split; [exact HG3|]. split; [exact HG4|]. split; [exact HG18|]. split; [exact Hres|].
  (* vrd_iexit_a's order: ledger, room, TRANSFER, OUTCOME, ledger move, blocks bytes, lsum, the answer, LIVE. The
     exit is on the GRANTED prefix ip_ok P (the separator test refuses on the text, never on an allocation), so the
     OUTCOME is VrdCallPos.vc_outc_granted's *)
  assert (HLMp : rd_ledger_move (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E) (ip_ok P)
                   (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr P) D'
                   (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P))
    by exact (vv_ledger_move_perm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPermD HMlm).
  split; [exact KLED|]. split; [exact (proj1 HMroom)|]. split; [exact HMxf|].
  split; [exact (vc_outc_granted E (vd_pos P regs mem' md' k' p' (ip_f P) D') _ okr HMok HAns HLMp HMxf)|].
  split; [exact HLMp|].
  split; [exact HMbb|].
  split; [rewrite <- (vi_lsum_perm _ _ HPermD); exact HMls|].
  (* LIVE, HULL, and the OUTCOME OF AN INJECTED READING: the exit is on the granted prefix (VrdIElem.vrd_inj_granted) *)
  split; [|exact (conj (proj1 HMlv) (conj (vv_hull_at_exit E P HMD) (vrd_inj_granted E P HMok)))].
  exists r2, okr. split; [exact HAns|]. split.
  - intros H0. destruct (Hcur0 H0) as (Vp1 & Vd1 & Hr2len).
    split.
    + split; [exact Vp1|]. split; [exact Ve1|]. split; [exact Vd1|].
      split; [exact Hrw1|]. split; [exact Hq8m|]. split; [exact Ht0|]. split; [exact Htl62|].
      split; [pose proof (Zle_0_nat (length r2)); lia|]. split; [exact Hlen0|].
      split; [exact (proj1 KSRC)|]. split; [exact Hqtx | lia].
    + split.
      * exact (pj_nodeR_keep SEGS _ _ _ _ _ _ _ (HNodeD H0) (fun x k _ Hl => Hl) HKnode).
      * split.
        -- rewrite <- (vi_lsum_perm _ _ HPermD).
           apply (vv_held_bound CTX CTX0 CW E P r2 okr HEN HMD).
           rewrite HAns, H0. reflexivity.
        -- (* The kit's cut: the Some-arm free order and caps (vv_exit_fo) *)
           split; [exact HFOs | exact (HNCs (HNodeD H0))].
  - intros H1. destruct (Hcur1 H1) as (pa & da & Vp1 & Vd1 & Hpa & Hda).
    split.
    + exists pa, da. split; [lia|]. split; [lia|]. split; [exact Vp1|]. split; [exact Ve1|].
      split; [exact Vd1 | exact Hrw1].
    + split; [exact (pj_fdR_keep SEGS _ _ _ _ _ _ _ (HFdD H1) (fun x k _ Hl => Hl) HKnode)|].
      (* The kit's cut: the None-arm free order (vv_exit_fo) *)
      exact HFOn.
Qed.

(* ---- THE COMMA: the position the loop head is re-entered from ---- *)
Lemma vd_comma_make : forall CTX CTX0 CW E P regs mem' md' k' (X : Z -> Prop),
  vrd_ient_ok B ARx CTX CTX0 CW E -> vv_sep E P ->
  PjGrammar.skip (rest_atR (ie_tb E) (ie_text E) (ip_p P)) = rest_atR (ie_tb E) (ie_text E) (ip_p P) ->
  ip_p P < ie_text E + ie_len E ->
  nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some 44 ->
  (forall a, X a -> ie_q E <= a < ie_q E + 8 \/ ie_q E + 16 <= a < ie_q E + 20) ->
  (forall x : word, ~ X (bv_unsigned x) ->
     mrestrict (w_H (ip_W P)) mem' x = mrestrict (w_H (ip_W P)) (ip_mem P) x) ->
  (forall r, In r vd_live -> getr regs r = getr (ip_regs P) r) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E) (rd_fp (ie_q E) (ie_v E))
    (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) mem' md' k' (ie_CW E) ->
  val_mem SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E) 8 (ip_p P + 1) ->
  val_mem SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E + 16) 4 (Z.of_nat (ie_d E) + 1) ->
  vrd_icomma_a B ARx SK E (vd_pos P regs mem' md' k' (ip_p P + 1) (pred (ip_f P)) (ip_D P)).
Proof.
  intros CTX CTX0 CW E P regs mem' md' k' X HEN HSEP Hskip Hpe Hnth HX HK HR HJ Vp1 Vd1.
  pose proof HSEP as (HFR & HRG & HND & HCU & HJN & HMD & Hn0 & Hcont & HK1s).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (vd_bounds CTX CTX0 CW E P HEN HFR HCU)
    as (Bq1 & Bq2 & Bq8 & Bsp & Bsp46 & Bspq & Bspc & Bt4 & (Btp & Bpe) & Btc & Bac & Blen & Bam).
  pose proof HMD as (HMok & HMfac & HMlm & HMroom & HMf & HMbb & HMdep & HMls & HMxf & HMlv).
  pose proof HCU as (Hinok & Hraq & Hsrc & Hhome & HLED & Hfrm & Hcnt).
  pose proof Hinok as (Vp0 & Ve0 & Vd0 & Hrw0 & Hq8m & Ht0 & Htl62 & Hpp0 & Hlen0 & Hgarr0 & Hqtx & Hd32).
  assert (Hsp : spZ regs = spZ (ip_regs P))
    by (unfold spZ; rewrite (HR 2%bv ltac:(cbn; tauto)); reflexivity).
  assert (HXc : forall a, X a -> alloc_ceiling <= a) by (intros a Ha; destruct (HX a Ha); lia).
  destruct (vv_store_keepX CTX CTX0 CW E P [] regs mem' md' k' (ip_p P + 1) X
              (proj1 H_img) (proj1 (proj2 H_img)) HEN HFR HND HCU HJN
              ltac:(intros a Ha; destruct (HX a Ha); lia)
              ltac:(intros a Ha; unfold rd_fp, inFP;
                    destruct (HX a Ha) as [Hr | Hr];
                    [exists (ie_q E, ie_q E + 8); split; [left; reflexivity | cbn [fst snd]; lia]
                    |exists (ie_q E + 16, ie_q E + 20); split;
                       [right; left; reflexivity | cbn [fst snd]; lia]])
              ltac:(intros a Ha; destruct (HX a Ha); lia)
              HK Hsp HJ)
    as (KFR & KND & KJN & KLED & KRA & KSRC & KPR).
  assert (Ve1 : val_mem SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E + 8) 8 (ie_text E + ie_len E)).
  { apply (VrdFrame.val_mem_keep SEGS _ _ _ _ _ Ve0).
    apply (vv_keep_rd _ (ip_mem P) mem' X _ HK).
    intros z Hz. cbv beta in Hz. split; [lia|]. intros HXz. destruct (HX z HXz); lia. }
  assert (Hrw1 : rd_rw SEGS (mrestrict (w_H (ip_W P)) mem') (ie_q E) 24)
    by (intros z Hz; exact (vd_writable_keep _ (ip_mem P) mem' z (Hrw0 z Hz) (KPR z))).
  (* the text at the cursor *)
  assert (Hrest : rest_atR (ie_tb E) (ie_text E) (ip_p P) = 44 :: rest_atR (ie_tb E) (ie_text E) (ip_p P + 1))
    by (apply vd_rest_cons; [lia | lia | exact Hnth]).
  assert (Hrlen : (length (rest_atR (ie_tb E) (ie_text E) (ip_p P))
                   = S (length (rest_atR (ie_tb E) (ie_text E) (ip_p P + 1))))%nat)
    by (rewrite Hrest; reflexivity).
  assert (Hf1 : (1 <= ip_f P)%nat) by (rewrite Hrlen in HMf; lia).
  unfold vrd_icomma_a. vd_proj.
  split; [exact KFR|].
  split.
  { unfold vrd_iregs in HRG |- *. rewrite !HR by (unfold vd_live; cbn; tauto). exact HRG. }
  split; [exact KND|].
  split.
  { unfold vrd_icur. cbv zeta. vd_proj.
    split.
    { split; [exact Vp1|]. split; [exact Ve1|]. split; [exact Vd1|].
      split; [exact Hrw1|]. split; [exact Hq8m|]. split; [exact Ht0|]. split; [exact Htl62|].
      split; [lia|]. split; [exact Hlen0|]. split; [exact (proj1 KSRC)|]. split; [exact Hqtx | lia]. }
    split; [exact KRA|]. split; [exact KSRC|]. split; [exact Hhome|]. split; [exact KLED|].
    split; [exact Hfrm|]. rewrite Hrlen in Hcnt. lia. }
  split; [exact KJN|].
  split.
  { unfold vrd_imodel. vd_proj.
    split; [exact HMok|]. split; [exact HMfac|]. split; [exact HMlm|]. split; [exact HMroom|].
    split; [rewrite Hrlen in HMf; lia|]. split; [exact HMbb|]. split; [exact HMdep|].
    split; [exact HMls|]. split; [exact HMxf | exact HMlv]. }
  split; [exact Hn0|].
  split; [rewrite Hrlen in Hcnt; lia|].
  split.
  { rewrite Hcont. rewrite (vd_jsep_comma _ _ _ _ _ _ _ 44 _ Hskip Hrest eq_refl).
    replace (S (pred (ip_f P))) with (ip_f P) by lia. reflexivity. }
  (* The kit's cut: the batch kit's layer before the next grow - the comma's store missed every block of the position
     (vv_k1_hi); the model's free list is jfl at the next loop head (vrd_jfsep's comma arm) *)
  destruct HK1s as (HCAP & HNC & (af & HFO & HFL)).
  destruct (vv_D_apart CTX CTX0 CW E P HEN HJN HCU HMD) as (_ & HDB & _ & _).
  destruct (vv_k1_hi E P (vd_pos P regs mem' md' k' (ip_p P + 1) (pred (ip_f P)) (ip_D P)) af HMD HND HNC HFO
              eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as (HNC2 & HFO2).
  { apply (vd_keep_low _ (ip_mem P) mem' X _ HK HXc). intros z Hz.
    unfold rd_blk in Hz. apply Exists_exists in Hz as ([a k] & Hin & Hr). unfold pj_holdsR in Hr.
    cbn [fst snd] in Hr. destruct (HDB a k Hin) as (Hk & _ & H4 & Hc & _). pose proof (@cf_head_nonneg cp). lia. }
  refine (conj HCAP (conj HNC2 (ex_intro _ af (conj HFO2 _)))).
  intros okr. rewrite (HFL okr). unfold vrd_jfsep. rewrite Hskip, Hrest.
  replace (S (pred (ip_f P))) with (ip_f P) by lia. reflexivity.
Qed.

(* ---- the refusal at the end of the text: rows 265..268, 309, to the exit with res = -1 ---- *)
Lemma vd_partD_end : forall CTX CTX0 CW E P,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vv_tail E P -> ip_p P = ie_text E + ie_len E -> Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_ITAIL_SLOT P)
    (fun W2 c2 => (exists P' res, W2 = ip_W P' /\ c2 = vrd_cfg A_IEPI_SLOT P' /\ vrd_iexit_a B ARx SK E P' res) /\
                  Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P HEN HT Hpe HPM.
  destruct HT as (HSEP & R11 & Hskip).
  pose proof HSEP as (HFR & HRG & HND & HCU & HJN & HMD & Hn0 & Hcont & HK1s).
  (* the runner is stated at the empty budget: the journal rebased to P's depot (VrdIElem.vrd_ijrn_base) *)
  pose proof (vrd_ijrn_base B ARx SK E P HJN) as HJ.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (vd_bounds CTX CTX0 CW E P HEN HFR HCU)
    as (Bq1 & Bq2 & Bq8 & Bsp & Bsp46 & Bspq & Bspc & Bt4 & (Btp & Bpe) & Btc & Bac & Blen & Bam).
  destruct (vd_seatE_at CTX CTX0 CW E P A_ITAIL_SLOT HEN HFR HRG HCU R11) as [HS SHOK].
  set (ED := vd_E (ip_regs P) (ip_p P) (ie_text E + ie_len E) 0 (Z.of_nat (ie_d E) + 1)) in *.
  assert (HEI : img_env VAL A_LIM ED) by (unfold ED, vd_E; apply Eimg_env).
  pose proof HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  assert (HA : env_agree 32 (Ereg (ip_regs P)
                 [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 0; w64 (Z.of_nat (ie_d E) + 1)]) ED)
    by (split; [intros j Hj; unfold ED, vd_E; rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia); reflexivity
               | reflexivity]).
  assert (E32 : ew ED 32 = w64 (ip_p P)).
  { unfold ED, vd_E. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_extra (ip_regs P) _ 0). }
  assert (E33 : ew ED 33 = w64 (ie_text E + ie_len E)).
  { unfold ED, vd_E. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_extra (ip_regs P) _ 1). }
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 9%bv HS) as R9d.
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 27%bv HS) as R27d.
  change (sr_get (ss_regs (vd_ssE A_ITAIL_SLOT)) 9%bv) with (SOff 8 16) in R9d.
  change (sr_get (ss_regs (vd_ssE A_ITAIL_SLOT)) 27%bv) with (vv_sh 8 0) in R27d.
  cbn [ms_regs restrict] in R9d, R27d.
  destruct (vv_exit_rep CTX CTX0 CW E P HEN HND HCU HJN HMD Hn0) as (D' & HPermD & HNodeD & HFdD).
  pose (RUN := paj_run_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (RUNTO := paj_run_to_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (BR := paj_branchR (fx := ip_fx P) (PI := PAI) (wle' SEGS YGcfRehidePost.RZ_cf)).
  unfold vrd_cfg.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vi_Bspan.
  { vd_awr_ro. }
  match goal with H : frame_of _ _ (ip_mem P) _ |- _ => rename H into HF1 end.
  assert (HM1 : forall x, ms_mem ms x = ip_mem P x)
    by (eapply vd_frame_ro; [exact HF1 | repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil]).
  psrr_branch_tok RUN BR HS SHOK vi_Bspan.
  - (* p >= end: on to row 309 and the exit *)
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vi_Bspan (4 * Z.of_nat A_IEPI_SLOT).
    { vd_awr_ro. }
    match goal with H : frame_of _ _ (ms_mem ms) _ |- _ => rename H into HF2 end.
    match goal with ms0 : machine_state |- _ =>
      lazymatch ms0 with ms => fail | _ => rename ms0 into ms2 end end.
    assert (HM2 : forall x, ms_mem ms2 x = ip_mem P x).
    { intros x. rewrite <- (HM1 x). eapply vd_frame_ro;
        [exact HF2 | repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil]. }
    assert (HRk : forall r, In r [2; 3; 4]%bv -> getr (ms_regs ms2) r = getr (ip_regs P) r)
      by exact (regs_kept_of_st_ok_pi (fx := ip_fx P) ED _ _ (ip_regs P) _ [2; 3; 4]%bv HS HA
                  ltac:(vm_compute; reflexivity)).
    pose proof (st_ok_pi_restrict_reg _ _ _ _ 18%bv HS) as Q18.
    match type of Q18 with _ = sv_denot _ (sr_get ?l _) =>
      let v := eval vm_compute in (sr_get l 18%bv) in change (sr_get l 18%bv) with v in Q18 end.
    cbn [sv_denot ms_regs restrict] in Q18.
    assert (Hsp2 : spZ (ms_regs ms2) = spZ (ip_regs P))
      by (unfold spZ; rewrite (HRk 2%bv ltac:(cbn; tauto)); reflexivity).
    assert (HMr : forall x : word, mrestrict (w_H (ip_W P)) (ms_mem ms2) x
                                   = mrestrict (w_H (ip_W P)) (ip_mem P) x)
      by (intros x; unfold mrestrict; rewrite HM2; reflexivity).
    destruct (vv_store_keepX CTX CTX0 CW E P [] (ms_regs ms2) (ms_mem ms2) _ (ip_k P) (ip_p P)
                (fun _ : Z => False) (proj1 H_img) (proj1 (proj2 H_img)) HEN HFR HND HCU HJN
                ltac:(intros a []) ltac:(intros a []) ltac:(intros a []) ltac:(intros x _; apply HMr)
                Hsp2 (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ))
      as (KFR & KND & KJN & KLED & KRA & KSRC & KPR).
    pose proof (vi_keep_all (mrestrict (w_H (ip_W P)) (ip_mem P))
                            (mrestrict (w_H (ip_W P)) (ms_mem ms2)) HMr) as HKall.
    pmkst HS. apply SRr'_ret. split; [|exact HPM].
    refine (ex_intro _ (vd_pos P (ms_regs ms2) (ms_mem ms2) _ (ip_k P) (ip_p P) (ip_f P) D')
              (ex_intro _ (-1) _)).
    split; [reflexivity|]. split; [reflexivity|].
    (* the model at the end of the text refuses *)
    assert (Hrnil : rest_atR (ie_tb E) (ie_text E) (ip_p P) = [])
      by (apply (vd_rest_end (ie_tb E) (ie_text E) (ie_len E)); [exact Blen | lia | exact Hpe]).
    assert (Hcref : ip_cont P = PjGrammar.jrefuse)
      by (rewrite Hcont; apply (vd_jsep_refuse_nil _ _ _ _ _ _ _ Hskip Hrnil)).
    pose proof (vd_answer E P HMD) as HAns. rewrite Hcref in HAns.
    cbn [PjGrammar.jrefuse fst snd] in HAns. rewrite app_nil_r in HAns.
    pose proof HMD as (HMok & HMfac & HMlm & HMroom & HMf & HMbb & HMdep & HMls & HMxf & HMlv).
    pose proof HCU as (Hinok & Hraq & Hsrc & Hhome & HLED & Hfrm & Hcnt).
    assert (HLMp : rd_ledger_move (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E) (ip_ok P)
                     (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr P) D'
                     (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P))
      by exact (vv_ledger_move_perm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPermD HMlm).
    (* the refusal on the text is on the GRANTED prefix: the OUTCOME is vc_outc_granted's *)
    lazymatch goal with |- vrd_iexit_a _ _ _ _ ?P' _ =>
      pose proof (vc_outc_granted E P' _ _ HMok HAns HLMp HMxf) as HOC end.
    unfold vrd_iexit_a. vd_proj.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
      (conj _ (conj _ (conj _ (conj _ _))))))))))))));
      [ (* frame *) exact KFR
      | (* journal *) exact (vd_ijrn_perm E P _ _ _ _ _ (ip_f P) D' HPermD KJN)
      | rewrite (HRk 3%bv ltac:(cbn; tauto)); exact G3
      | rewrite (HRk 4%bv ltac:(cbn; tauto)); exact G4
      | rewrite Q18; apply bv_eq; vm_compute; reflexivity
      | right; reflexivity
      | exact KLED
      | exact (proj1 HMroom)
      | exact HMxf
      | exact HOC
      | exact HLMp
      | exact HMbb
      | rewrite <- (vi_lsum_perm _ _ HPermD); exact HMls
      |
      | exact (conj (proj1 HMlv) (conj (vv_hull_at_exit E P HMD) (vrd_inj_granted E P HMok))) ].
    exists [], []. split; [exact HAns|]. split; [intros Hx; discriminate Hx|].
    intros _.
    (* The kit's cut: the None-arm free order, from the separator's batch-kit layer at the end of the text (vv_exit_fo) *)
    destruct (vv_exit_fo CTX CTX0 CW E P (mrestrict (w_H (ip_W P)) (ms_mem ms2)) D' HEN HSEP
                ltac:(rewrite Hskip, Hrnil; exact I) HPermD ltac:(apply HKall)) as (HFOn & _ & _).
    split; [exact (vi_in_after_keep _ _ _ _ _ _ _ (vv_in_after E P HCU) HKall)|].
    split; [eapply (pj_fdR_keep SEGS); [exact HFdD | intros x k _ Hl; exact Hl | apply HKall]|].
    exact HFOn.
  - exfalso. match goal with H : branch_taken _ _ _ = false |- _ => rename H into Hb end.
    rewrite branch_geu_U, (U_atom ED 32 (ip_p P) E32), (U_atom ED 33 _ E33) in Hb by lia.
    apply Bool.negb_false_iff, Z.ltb_lt in Hb. lia.
Qed.


Ltac vd_awr HU :=
  eapply awr_ok_cons_ro; [cbn; lia|];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 8%nat _);
    [reflexivity | exact HU
    | let a := fresh "a" in let Ha := fresh "Ha" in
      intros a Ha; cbn [vd_cur0 YP09.r_wlo YP09.r_whi] in Ha; left; lia |];
  eapply awr_ok_cons_ro; [cbn; lia|];
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 8%nat _);
    [reflexivity | exact HU
    | let a := fresh "a" in let Ha := fresh "Ha" in
      intros a Ha; cbn [vd_cur2 YP09.r_wlo YP09.r_whi] in Ha; left; lia |];
  eapply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil.

Ltac vd_fa HU :=
  cbn [vd_ss vd_ssE ss_mem add_cond];
  repeat (apply Forall_cons;
    [let o := fresh "o" in let Ho := fresh "Ho" in
     intros o Ho; cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val
                       vd_frame vd_cur0 vd_cur1 vd_cur2 vd_byte vd_cur0E vd_cur2E] in Ho |- *;
     cbn [ew ewset Nat.eqb] in *; rewrite ?HU; lia|]);
  apply Forall_nil.

(* ---- the separator test with a byte left: rows 265..279 / 326..346 ---- *)
Lemma vd_partD_byte : forall CTX CTX0 CW E P,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vv_tail E P -> ip_p P < ie_text E + ie_len E -> Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_ITAIL_SLOT P)
    (fun W2 c2 => ((exists P', W2 = ip_W P' /\ c2 = vrd_cfg A_ICOMMA_SLOT P' /\ ip_n P' = ip_n P /\
                               vrd_icomma_a B ARx SK E P') \/
                   (exists P' res, W2 = ip_W P' /\ c2 = vrd_cfg A_IEPI_SLOT P' /\ vrd_iexit_a B ARx SK E P' res)) /\
                  Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P HEN HT Hpe HPM.
  destruct HT as (HSEP & R11 & Hskip).
  pose proof HSEP as (HFR & HRG & HND & HCU & HJN & HMD & Hn0 & Hcont & HK1s).
  (* the runner is stated at the empty budget: the journal rebased to P's depot (VrdIElem.vrd_ijrn_base) *)
  pose proof (vrd_ijrn_base B ARx SK E P HJN) as HJ.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (vd_bounds CTX CTX0 CW E P HEN HFR HCU)
    as (Bq1 & Bq2 & Bq8 & Bsp & Bsp46 & Bspq & Bspc & Bt4 & (Btp & Bpe) & Btc & Bac & Blen & Bam).
  pose proof HMD as (HMok & HMfac & HMlm & HMroom & HMf & HMbb & HMdep & HMls & HMxf & HMlv).
  pose proof HCU as (Hinok & Hraq & Hsrc & Hhome & HLED & Hfrm & Hcnt).
  pose proof Hinok as (Vp0 & Ve0 & Vd0 & Hrw0 & Hq8m & Ht0 & Htl62 & Hpp0 & Hlen0 & Hgarr0 & Hqtx & Hd32).
  pose proof HRG as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  destruct (vd_seat_at CTX CTX0 CW E P A_ITAIL_SLOT HEN HFR HRG HCU R11 Hpe) as [HS SHOK].
  set (bb := nth (Z.to_nat (ip_p P - ie_text E)) (ie_tb E) 0) in *.
  set (ED := vd_E (ip_regs P) (ip_p P) (ie_text E + ie_len E) bb (Z.of_nat (ie_d E) + 1)) in *.
  assert (HEI : img_env VAL A_LIM ED) by (unfold ED, vd_E; apply Eimg_env).
  assert (EL : forall j, (j < 32)%nat -> forall r : bv 5, Z.of_nat j = bv_unsigned r ->
                 ew ED j = getr (ip_regs P) r).
  { intros j Hj r Hr. unfold ED, vd_E. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat (ip_regs P) _ j r Hr). }
  assert (E19 : ew ED 19 = w64 (if ie_o E then 1 else 0))
    by (rewrite (EL 19%nat ltac:(lia) 19%bv eq_refl); exact G19).
  assert (U8 : bv_unsigned (ew ED 8) = ie_q E)
    by (rewrite (EL 8%nat ltac:(lia) 8%bv eq_refl), G8; unfold w64; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew ED 26) = SHADOW_OFF)
    by (rewrite (EL 26%nat ltac:(lia) 26%bv eq_refl), G26; unfold w64; apply unsigned_lit_small;
        unfold SHADOW_OFF; lia).
  assert (R9v : forall EV : env, bv_unsigned (ew EV 8) = ie_q E ->
                  getr (ip_regs P) 9 = sv_denot EV (SOff 8 16)).
  { intros EV H8. rewrite denot_lit_U, U_SOff, H8, zcanon_id by (unfold M64; lia). exact G9. }
  assert (R27v : forall EV : env, bv_unsigned (ew EV 8) = ie_q E ->
                  bv_unsigned (ew EV 26) = SHADOW_OFF -> getr (ip_regs P) 27 = sv_denot EV (vv_sh 8 0)).
  { intros EV H8 H26. rewrite G27. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned.
    fold (U EV (vv_sh 8 0)). rewrite (vv_sh_U EV 8 0 (ie_q E) H8 H26) by lia.
    unfold shadow_addr. rewrite Z.add_0_r.
    assert (0 <= ie_q E / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_small by (unfold SHADOW_OFF; lia). reflexivity. }
  assert (E32 : ew ED 32 = w64 (ip_p P)).
  { unfold ED, vd_E. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_extra (ip_regs P) _ 0). }
  assert (E33 : ew ED 33 = w64 (ie_text E + ie_len E)).
  { unfold ED, vd_E. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_extra (ip_regs P) _ 1). }
  assert (E34 : ew ED 34 = w64 bb).
  { unfold ED, vd_E. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_extra (ip_regs P) _ 2). }
  assert (E35 : ew ED 35 = w64 (Z.of_nat (ie_d E) + 1)).
  { unfold ED, vd_E. rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia).
    exact (ew_Ereg_extra (ip_regs P) _ 3). }
  assert (HA : env_agree 32 (Ereg (ip_regs P)
                 [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 bb; w64 (Z.of_nat (ie_d E) + 1)]) ED)
    by (split; [intros j Hj; unfold ED, vd_E; rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia); reflexivity
               | reflexivity]).
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 9%bv HS) as R9d.
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 27%bv HS) as R27d.
  change (sr_get (ss_regs (vd_ss A_ITAIL_SLOT)) 9%bv) with (SOff 8 16) in R9d.
  change (sr_get (ss_regs (vd_ss A_ITAIL_SLOT)) 27%bv) with (vv_sh 8 0) in R27d.
  cbn [ms_regs restrict] in R9d, R27d.
  assert (Hbyte : nth_error (ie_tb E) (Z.to_nat (ip_p P - ie_text E)) = Some bb)
    by (unfold bb; apply nth_error_nth'; lia).
  assert (Hb255 : 0 <= bb < 256).
  { unfold bb. destruct (Hgarr0 (Z.to_nat (ip_p P - ie_text E)) ltac:(lia)) as (_ & H255). exact H255. }
  assert (Hrest : rest_atR (ie_tb E) (ie_text E) (ip_p P) = bb :: rest_atR (ie_tb E) (ie_text E) (ip_p P + 1))
    by (apply vd_rest_cons; [lia | lia | exact Hbyte]).
  assert (Hrlen : (length (rest_atR (ie_tb E) (ie_text E) (ip_p P))
                   = S (length (rest_atR (ie_tb E) (ie_text E) (ip_p P + 1))))%nat)
    by (rewrite Hrest; reflexivity).
  destruct (vv_exit_rep CTX CTX0 CW E P HEN HND HCU HJN HMD Hn0) as (D' & HPermD & HNodeD & HFdD).
  pose proof (vd_answer E P HMD) as HAns0.
  pose (RUN := paj_run_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (RUNTO := paj_run_to_x_invR (fx := ip_fx P) (SK := SK) (PL := PLA) (PI := PAI) B prh_pst ARx LAWS Pm PLAW (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_refl SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  pose (BR := paj_branchR (fx := ip_fx P) (PI := PAI) (wle' SEGS YGcfRehidePost.RZ_cf)).
  pose proof (vv_stk_items (ie_d E)) as HSTK. unfold ESTACK in HSTK.
  pose proof HEN as ((HAFN & _) & _ & _ & _ & HRD & _).
  pose proof HRD as (_ & _ & _ & _ & _ & _ & Hqlo & Hqhi & _).
  unfold vrd_cfg.
  (* rows 265..267 *)
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vi_Bspan.
  { vd_awr U8. }
  match goal with ms0 : machine_state |- _ => rename ms0 into m1 end.
  match goal with H : frame_of _ _ (mrestrict _ (ip_mem P)) _ |- _ => rename H into F1 end.
  assert (K1 : forall x : word, ~ (ie_q E <= bv_unsigned x < ie_q E + 8 \/
                                   ie_q E + 16 <= bv_unsigned x < ie_q E + 20) ->
                 mrestrict (w_H (ip_W P)) (ms_mem m1) x = mrestrict (w_H (ip_W P)) (ip_mem P) x)
    by (apply (vd_keepX _ _ (ie_q E) _ _ F1); vd_fa U8).
  (* row 268: the end of the text *)
  psrr_branch_tok RUN BR HS SHOK vi_Bspan.
  { exfalso. match goal with H : branch_taken _ _ _ = true |- _ => rename H into Hb end.
    rewrite branch_geu_U, (U_atom ED 32 (ip_p P) E32), (U_atom ED 33 _ E33) in Hb by lia.
    apply Bool.negb_true_iff, Z.ltb_ge in Hb. lia. }
  (* rows 269..274: the byte at the cursor *)
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vi_Bspan.
  { vd_awr U8. }
  match goal with ms0 : machine_state |- _ => lazymatch ms0 with m1 => fail | _ => rename ms0 into m2 end end.
  match goal with H : frame_of _ _ (mrestrict _ (ms_mem m1)) _ |- _ => rename H into F2 end.
  assert (K2 : forall x : word, ~ (ie_q E <= bv_unsigned x < ie_q E + 8 \/
                                   ie_q E + 16 <= bv_unsigned x < ie_q E + 20) ->
                 mrestrict (w_H (ip_W P)) (ms_mem m2) x = mrestrict (w_H (ip_W P)) (ip_mem P) x).
  { intros x Hx. rewrite (vd_keepX _ _ (ie_q E) _ _ F2 ltac:(vd_fa U8) x Hx). exact (K1 x Hx). }
  (* row 275: the comma test *)
  psrr_branch_tok RUN BR HS SHOK vi_Bspan.
  - (* the byte is not a comma *)
    match goal with H : branch_taken _ (sv_denot ?EV _) _ = true |- _ =>
      rewrite branch_ne_U, (U_atom EV 34 bb E34), (U_lit EV 44) in H by lia;
      apply Bool.negb_true_iff, Z.eqb_neq in H; rename H into Hb44 end.
    (* rows 326..330 *)
    paj_run_tok_x_inv RUN HS HJ SHOK HPM vi_Bspan.
    { vd_awr U8. }
    match goal with ms0 : machine_state |- _ =>
      lazymatch ms0 with m1 => fail | m2 => fail | _ => rename ms0 into m3 end end.
    match goal with H : frame_of _ _ (mrestrict _ (ms_mem m2)) _ |- _ => rename H into F3 end.
    assert (K3 : forall x : word, ~ (ie_q E <= bv_unsigned x < ie_q E + 8 \/
                                     ie_q E + 16 <= bv_unsigned x < ie_q E + 20) ->
                   mrestrict (w_H (ip_W P)) (ms_mem m3) x = mrestrict (w_H (ip_W P)) (ip_mem P) x).
    { intros x Hx. rewrite (vd_keepX _ _ (ie_q E) _ _ F3 ltac:(vd_fa U8) x Hx). exact (K2 x Hx). }
    (* row 331: array or object *)
    psrr_branch_tok RUN BR HS SHOK vi_Bspan.
    + (* an array *)
      match goal with H : branch_taken _ (sv_denot ?EV _) _ = true |- _ =>
        rewrite branch_eq_U, (U_atom EV 19 (if ie_o E then 1 else 0) E19), (U_lit EV 0) in H
          by (destruct (ie_o E); lia);
        apply Z.eqb_eq in H; rename H into Ho end.
      assert (Hof : ie_o E = false) by (destruct (ie_o E); [discriminate Ho | reflexivity]).
      (* rows 332..334: the closer byte *)
      paj_run_tok_x_inv RUN HS HJ SHOK HPM vi_Bspan.
      { vd_awr U8. }
      match goal with ms0 : machine_state |- _ =>
        lazymatch ms0 with m1 => fail | m2 => fail | m3 => fail | _ => rename ms0 into m4 end end.
      match goal with H : frame_of _ _ (mrestrict _ (ms_mem m3)) _ |- _ => rename H into F4 end.
      assert (K4 : forall x : word, ~ (ie_q E <= bv_unsigned x < ie_q E + 8 \/
                                       ie_q E + 16 <= bv_unsigned x < ie_q E + 20) ->
                     mrestrict (w_H (ip_W P)) (ms_mem m4) x = mrestrict (w_H (ip_W P)) (ip_mem P) x).
      { intros x Hx. rewrite (vd_keepX _ _ (ie_q E) _ _ F4 ltac:(vd_fa U8) x Hx). exact (K3 x Hx). }
      (* row 335: the closer test *)
      psrr_branch_tok RUN BR HS SHOK vi_Bspan.
      * (* not the closer: the refusal exit *)
        match goal with H : branch_taken _ _ (sv_denot ?EV _) = true |- _ =>
          rewrite branch_ne_U, (U_lit EV 93), (U_atom EV 34 bb E34) in H by lia;
          apply Bool.negb_true_iff, Z.eqb_neq in H; rename H into Hbc end.
        (* the refusal exit: run the branch to row 310 *)
        paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vi_Bspan (4 * Z.of_nat A_IEPI_SLOT).
        { vd_awr U8. }
        match goal with ms0 : machine_state |- _ =>
          lazymatch ms0 with m1 => fail | m2 => fail | m3 => fail | m4 => fail
          | _ => rename ms0 into m5 end end.
        match goal with H : frame_of _ _ (mrestrict _ (ms_mem m4)) _ |- _ => rename H into F5 end.
        assert (K5 : forall x : word, ~ (ie_q E <= bv_unsigned x < ie_q E + 8 \/
                                         ie_q E + 16 <= bv_unsigned x < ie_q E + 20) ->
                       mrestrict (w_H (ip_W P)) (ms_mem m5) x = mrestrict (w_H (ip_W P)) (ip_mem P) x).
        { intros x Hx. rewrite (vd_keepX _ _ (ie_q E) _ _ F5 ltac:(vd_fa U8) x Hx). exact (K4 x Hx). }
        prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
        prreg HS (18%bv : bv 5) Q18.
        rewrite (EL 2%nat ltac:(lia) 2%bv eq_refl) in Q2.
        rewrite (EL 3%nat ltac:(lia) 3%bv eq_refl) in Q3.
        rewrite (EL 4%nat ltac:(lia) 4%bv eq_refl) in Q4.
        pose proof (vd_chunk_val (ip_fx P) _ _ _ _ 1%nat _ 0%nat 0 8 (SOff 32 0) (ip_p P) HS
                      eq_refl eq_refl
                      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E32, Z.add_0_r; unfold w64;
                            rewrite Z_to_bv_bv_unsigned; reflexivity)
                      ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as Vpx.
        pose proof (vd_chunk_val (ip_fx P) _ _ _ _ 3%nat _ 0%nat 16 4 (SOff 35 0)
                      (Z.of_nat (ie_d E) + 1) HS eq_refl eq_refl
                      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E35, Z.add_0_r; unfold w64;
                            rewrite Z_to_bv_bv_unsigned; reflexivity)
                      ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as Vdx.
        cbn [base_val YP09.r_base ew ewset Nat.eqb] in Vpx, Vdx.
        rewrite U8 in Vpx, Vdx. rewrite Z.add_0_r in Vpx.
        change (N.to_nat 8) with 8%nat in Vpx. change (N.to_nat 4) with 4%nat in Vdx.
        pmkst HS. apply SRr'_ret. split; [|exact HPM]. right.
        refine (ex_intro _ (vd_pos P (ms_regs m5) (ms_mem m5) _ (ip_k P) (ip_p P) (ip_f P) D')
                  (ex_intro _ (-1) _)).
        split; [reflexivity|]. split; [reflexivity|].
        assert (Hcref : ip_cont P = PjGrammar.jrefuse).
        { rewrite Hcont. apply (vd_jsep_refuse_other _ _ _ _ _ _ _ bb _ Hskip Hrest Hb44).
           rewrite Hof; unfold PjGrammar.closer; lia. }
        pose proof HAns0 as HA1. rewrite Hcref in HA1.
        cbn [PjGrammar.jrefuse fst snd] in HA1. rewrite app_nil_r in HA1.
        refine (vd_exit_make CTX CTX0 CW E P (ms_regs m5) (ms_mem m5) _ (ip_k P) (ip_p P) (-1) D' [] []
                 (fun a => ie_q E <= a < ie_q E + 8 \/ ie_q E + 16 <= a < ie_q E + 20)
                 HEN HSEP ltac:(intros a Ha; exact Ha) K5
                 ltac:(unfold spZ; rewrite Q2; reflexivity) (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ)
                 ltac:(rewrite Q3; exact G3) ltac:(rewrite Q4; exact G4)
                 ltac:(rewrite Q18; apply bv_eq; vm_compute; reflexivity)
                 ltac:(right; reflexivity) HPermD
                 ltac:(intros Hx; discriminate Hx) ltac:(intros _; exact HFdD)
                 ltac:(cbn [Z.eqb]; exact HA1)
                 ltac:(intros Hx; discriminate Hx) _ ltac:(rewrite Hskip, Hrest; cbv beta iota; lia)).
        intros _. exists (ip_p P), (Z.of_nat (ie_d E) + 1).
        split; [exact Vpx|]. split; [exact Vdx|]. split; [lia | lia].
      * (* the closer: the success exit *)
        match goal with H : branch_taken _ _ (sv_denot ?EV _) = false |- _ =>
          rewrite branch_ne_U, (U_lit EV 93), (U_atom EV 34 bb E34) in H by lia;
          apply Bool.negb_false_iff, Z.eqb_eq in H; rename H into Hbc end.
        paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vi_Bspan (4 * Z.of_nat A_IEPI_SLOT).
        { vd_awr U8. }
        match goal with ms0 : machine_state |- _ =>
          lazymatch ms0 with m1 => fail | m2 => fail | m3 => fail | m4 => fail
          | _ => rename ms0 into m5 end end.
        match goal with H : frame_of _ _ (mrestrict _ (ms_mem m4)) _ |- _ => rename H into F5 end.
        assert (K5 : forall x : word, ~ (ie_q E <= bv_unsigned x < ie_q E + 8 \/
                                         ie_q E + 16 <= bv_unsigned x < ie_q E + 20) ->
                       mrestrict (w_H (ip_W P)) (ms_mem m5) x = mrestrict (w_H (ip_W P)) (ip_mem P) x).
        { intros x Hx. rewrite (vd_keepX _ _ (ie_q E) _ _ F5 ltac:(vd_fa U8) x Hx). exact (K4 x Hx). }
        prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
        prreg HS (18%bv : bv 5) Q18.
        rewrite (EL 2%nat ltac:(lia) 2%bv eq_refl) in Q2.
        rewrite (EL 3%nat ltac:(lia) 3%bv eq_refl) in Q3.
        rewrite (EL 4%nat ltac:(lia) 4%bv eq_refl) in Q4.
        pose proof (vd_chunk_val (ip_fx P) _ _ _ _ 1%nat _ 0%nat 0 8 (SOff 32 1) (ip_p P + 1) HS
                      eq_refl eq_refl
                      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E32; unfold w64;
                            rewrite unsigned_lit_small by lia; reflexivity)
                      ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as Vpx.
        pose proof (vd_chunk_val (ip_fx P) _ _ _ _ 3%nat _ 0%nat 16 4 (SOff 35 (-1))
                      (Z.of_nat (ie_d E)) HS eq_refl eq_refl
                      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E35; unfold w64;
                            rewrite unsigned_lit_small by lia; f_equal; lia)
                      ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as Vdx.
        cbn [base_val YP09.r_base ew ewset Nat.eqb] in Vpx, Vdx.
        rewrite U8 in Vpx, Vdx. rewrite Z.add_0_r in Vpx.
        change (N.to_nat 8) with 8%nat in Vpx. change (N.to_nat 4) with 4%nat in Vdx.
        assert (Hr2 : Z.of_nat (length (rest_atR (ie_tb E) (ie_text E) (ip_p P + 1)))
                      = ie_text E + ie_len E - (ip_p P + 1))
          by (apply (vd_rest_len_eq _ _ (ie_len E)); [exact Blen | lia]).
        pmkst HS. apply SRr'_ret. split; [|exact HPM]. right.
        refine (ex_intro _ (vd_pos P (ms_regs m5) (ms_mem m5) _ (ip_k P) (ip_p P) (ip_f P) D')
                  (ex_intro _ 0 _)).
        split; [reflexivity|]. split; [reflexivity|].
        assert (Hcref : ip_cont P =
                  PjGrammar.jret (PjGrammar.mk (ie_o E) (rev (ip_acc P)),
                                  rest_atR (ie_tb E) (ie_text E) (ip_p P + 1))).
        { rewrite Hcont. apply (vd_jsep_closer _ _ _ _ _ _ _ bb _ Hskip Hrest).
           rewrite Hof; unfold PjGrammar.closer; lia. }
        pose proof HAns0 as HA1. rewrite Hcref in HA1.
        cbn [PjGrammar.jret fst snd] in HA1. rewrite app_nil_r in HA1.
        refine (vd_exit_make CTX CTX0 CW E P (ms_regs m5) (ms_mem m5) _ (ip_k P) (ip_p P) 0 D'
                 (rest_atR (ie_tb E) (ie_text E) (ip_p P + 1)) []
                 (fun a => ie_q E <= a < ie_q E + 8 \/ ie_q E + 16 <= a < ie_q E + 20)
                 HEN HSEP ltac:(intros a Ha; exact Ha) K5
                 ltac:(unfold spZ; rewrite Q2; reflexivity) (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ)
                 ltac:(rewrite Q3; exact G3) ltac:(rewrite Q4; exact G4)
                 ltac:(rewrite Q18; apply bv_eq; vm_compute; reflexivity)
                 ltac:(left; reflexivity) HPermD
                 ltac:(intros _; exact HNodeD) ltac:(intros Hx; discriminate Hx)
                 ltac:(cbn [Z.eqb]; exact HA1)
                 _ ltac:(intros Hx; discriminate Hx) ltac:(rewrite Hskip, Hrest; cbv beta iota; lia)).
        intros _. split; [rewrite Hr2; replace (ie_text E + ie_len E - (ie_text E + ie_len E - (ip_p P + 1)))
                            with (ip_p P + 1) by lia; exact Vpx|].
        split; [exact Vdx | rewrite Hr2; lia].
    + (* an object *)
      match goal with H : branch_taken _ (sv_denot ?EV _) _ = false |- _ =>
        rewrite branch_eq_U, (U_atom EV 19 (if ie_o E then 1 else 0) E19), (U_lit EV 0) in H
          by (destruct (ie_o E); lia);
        apply Z.eqb_neq in H; rename H into Ho end.
      assert (Hof : ie_o E = true) by (destruct (ie_o E); [reflexivity | exfalso; apply Ho; reflexivity]).
      (* rows 332..334: the closer byte *)
      paj_run_tok_x_inv RUN HS HJ SHOK HPM vi_Bspan.
      { vd_awr U8. }
      match goal with ms0 : machine_state |- _ =>
        lazymatch ms0 with m1 => fail | m2 => fail | m3 => fail | _ => rename ms0 into m4 end end.
      match goal with H : frame_of _ _ (mrestrict _ (ms_mem m3)) _ |- _ => rename H into F4 end.
      assert (K4 : forall x : word, ~ (ie_q E <= bv_unsigned x < ie_q E + 8 \/
                                       ie_q E + 16 <= bv_unsigned x < ie_q E + 20) ->
                     mrestrict (w_H (ip_W P)) (ms_mem m4) x = mrestrict (w_H (ip_W P)) (ip_mem P) x).
      { intros x Hx. rewrite (vd_keepX _ _ (ie_q E) _ _ F4 ltac:(vd_fa U8) x Hx). exact (K3 x Hx). }
      (* row 335: the closer test *)
      psrr_branch_tok RUN BR HS SHOK vi_Bspan.
      * (* not the closer: the refusal exit *)
        match goal with H : branch_taken _ _ (sv_denot ?EV _) = true |- _ =>
          rewrite branch_ne_U, (U_lit EV 125), (U_atom EV 34 bb E34) in H by lia;
          apply Bool.negb_true_iff, Z.eqb_neq in H; rename H into Hbc end.
        (* the refusal exit: run the branch to row 310 *)
        paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vi_Bspan (4 * Z.of_nat A_IEPI_SLOT).
        { vd_awr U8. }
        match goal with ms0 : machine_state |- _ =>
          lazymatch ms0 with m1 => fail | m2 => fail | m3 => fail | m4 => fail
          | _ => rename ms0 into m5 end end.
        match goal with H : frame_of _ _ (mrestrict _ (ms_mem m4)) _ |- _ => rename H into F5 end.
        assert (K5 : forall x : word, ~ (ie_q E <= bv_unsigned x < ie_q E + 8 \/
                                         ie_q E + 16 <= bv_unsigned x < ie_q E + 20) ->
                       mrestrict (w_H (ip_W P)) (ms_mem m5) x = mrestrict (w_H (ip_W P)) (ip_mem P) x).
        { intros x Hx. rewrite (vd_keepX _ _ (ie_q E) _ _ F5 ltac:(vd_fa U8) x Hx). exact (K4 x Hx). }
        prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
        prreg HS (18%bv : bv 5) Q18.
        rewrite (EL 2%nat ltac:(lia) 2%bv eq_refl) in Q2.
        rewrite (EL 3%nat ltac:(lia) 3%bv eq_refl) in Q3.
        rewrite (EL 4%nat ltac:(lia) 4%bv eq_refl) in Q4.
        pose proof (vd_chunk_val (ip_fx P) _ _ _ _ 1%nat _ 0%nat 0 8 (SOff 32 0) (ip_p P) HS
                      eq_refl eq_refl
                      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E32, Z.add_0_r; unfold w64;
                            rewrite Z_to_bv_bv_unsigned; reflexivity)
                      ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as Vpx.
        pose proof (vd_chunk_val (ip_fx P) _ _ _ _ 3%nat _ 0%nat 16 4 (SOff 35 0)
                      (Z.of_nat (ie_d E) + 1) HS eq_refl eq_refl
                      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E35, Z.add_0_r; unfold w64;
                            rewrite Z_to_bv_bv_unsigned; reflexivity)
                      ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as Vdx.
        cbn [base_val YP09.r_base ew ewset Nat.eqb] in Vpx, Vdx.
        rewrite U8 in Vpx, Vdx. rewrite Z.add_0_r in Vpx.
        change (N.to_nat 8) with 8%nat in Vpx. change (N.to_nat 4) with 4%nat in Vdx.
        pmkst HS. apply SRr'_ret. split; [|exact HPM]. right.
        refine (ex_intro _ (vd_pos P (ms_regs m5) (ms_mem m5) _ (ip_k P) (ip_p P) (ip_f P) D')
                  (ex_intro _ (-1) _)).
        split; [reflexivity|]. split; [reflexivity|].
        assert (Hcref : ip_cont P = PjGrammar.jrefuse).
        { rewrite Hcont. apply (vd_jsep_refuse_other _ _ _ _ _ _ _ bb _ Hskip Hrest Hb44).
           rewrite Hof; unfold PjGrammar.closer; lia. }
        pose proof HAns0 as HA1. rewrite Hcref in HA1.
        cbn [PjGrammar.jrefuse fst snd] in HA1. rewrite app_nil_r in HA1.
        refine (vd_exit_make CTX CTX0 CW E P (ms_regs m5) (ms_mem m5) _ (ip_k P) (ip_p P) (-1) D' [] []
                 (fun a => ie_q E <= a < ie_q E + 8 \/ ie_q E + 16 <= a < ie_q E + 20)
                 HEN HSEP ltac:(intros a Ha; exact Ha) K5
                 ltac:(unfold spZ; rewrite Q2; reflexivity) (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ)
                 ltac:(rewrite Q3; exact G3) ltac:(rewrite Q4; exact G4)
                 ltac:(rewrite Q18; apply bv_eq; vm_compute; reflexivity)
                 ltac:(right; reflexivity) HPermD
                 ltac:(intros Hx; discriminate Hx) ltac:(intros _; exact HFdD)
                 ltac:(cbn [Z.eqb]; exact HA1)
                 ltac:(intros Hx; discriminate Hx) _ ltac:(rewrite Hskip, Hrest; cbv beta iota; lia)).
        intros _. exists (ip_p P), (Z.of_nat (ie_d E) + 1).
        split; [exact Vpx|]. split; [exact Vdx|]. split; [lia | lia].
      * (* the closer: the success exit *)
        match goal with H : branch_taken _ _ (sv_denot ?EV _) = false |- _ =>
          rewrite branch_ne_U, (U_lit EV 125), (U_atom EV 34 bb E34) in H by lia;
          apply Bool.negb_false_iff, Z.eqb_eq in H; rename H into Hbc end.
        paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vi_Bspan (4 * Z.of_nat A_IEPI_SLOT).
        { vd_awr U8. }
        match goal with ms0 : machine_state |- _ =>
          lazymatch ms0 with m1 => fail | m2 => fail | m3 => fail | m4 => fail
          | _ => rename ms0 into m5 end end.
        match goal with H : frame_of _ _ (mrestrict _ (ms_mem m4)) _ |- _ => rename H into F5 end.
        assert (K5 : forall x : word, ~ (ie_q E <= bv_unsigned x < ie_q E + 8 \/
                                         ie_q E + 16 <= bv_unsigned x < ie_q E + 20) ->
                       mrestrict (w_H (ip_W P)) (ms_mem m5) x = mrestrict (w_H (ip_W P)) (ip_mem P) x).
        { intros x Hx. rewrite (vd_keepX _ _ (ie_q E) _ _ F5 ltac:(vd_fa U8) x Hx). exact (K4 x Hx). }
        prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
        prreg HS (18%bv : bv 5) Q18.
        rewrite (EL 2%nat ltac:(lia) 2%bv eq_refl) in Q2.
        rewrite (EL 3%nat ltac:(lia) 3%bv eq_refl) in Q3.
        rewrite (EL 4%nat ltac:(lia) 4%bv eq_refl) in Q4.
        pose proof (vd_chunk_val (ip_fx P) _ _ _ _ 1%nat _ 0%nat 0 8 (SOff 32 1) (ip_p P + 1) HS
                      eq_refl eq_refl
                      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E32; unfold w64;
                            rewrite unsigned_lit_small by lia; reflexivity)
                      ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as Vpx.
        pose proof (vd_chunk_val (ip_fx P) _ _ _ _ 3%nat _ 0%nat 16 4 (SOff 35 (-1))
                      (Z.of_nat (ie_d E)) HS eq_refl eq_refl
                      ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E35; unfold w64;
                            rewrite unsigned_lit_small by lia; f_equal; lia)
                      ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as Vdx.
        cbn [base_val YP09.r_base ew ewset Nat.eqb] in Vpx, Vdx.
        rewrite U8 in Vpx, Vdx. rewrite Z.add_0_r in Vpx.
        change (N.to_nat 8) with 8%nat in Vpx. change (N.to_nat 4) with 4%nat in Vdx.
        assert (Hr2 : Z.of_nat (length (rest_atR (ie_tb E) (ie_text E) (ip_p P + 1)))
                      = ie_text E + ie_len E - (ip_p P + 1))
          by (apply (vd_rest_len_eq _ _ (ie_len E)); [exact Blen | lia]).
        pmkst HS. apply SRr'_ret. split; [|exact HPM]. right.
        refine (ex_intro _ (vd_pos P (ms_regs m5) (ms_mem m5) _ (ip_k P) (ip_p P) (ip_f P) D')
                  (ex_intro _ 0 _)).
        split; [reflexivity|]. split; [reflexivity|].
        assert (Hcref : ip_cont P =
                  PjGrammar.jret (PjGrammar.mk (ie_o E) (rev (ip_acc P)),
                                  rest_atR (ie_tb E) (ie_text E) (ip_p P + 1))).
        { rewrite Hcont. apply (vd_jsep_closer _ _ _ _ _ _ _ bb _ Hskip Hrest).
           rewrite Hof; unfold PjGrammar.closer; lia. }
        pose proof HAns0 as HA1. rewrite Hcref in HA1.
        cbn [PjGrammar.jret fst snd] in HA1. rewrite app_nil_r in HA1.
        refine (vd_exit_make CTX CTX0 CW E P (ms_regs m5) (ms_mem m5) _ (ip_k P) (ip_p P) 0 D'
                 (rest_atR (ie_tb E) (ie_text E) (ip_p P + 1)) []
                 (fun a => ie_q E <= a < ie_q E + 8 \/ ie_q E + 16 <= a < ie_q E + 20)
                 HEN HSEP ltac:(intros a Ha; exact Ha) K5
                 ltac:(unfold spZ; rewrite Q2; reflexivity) (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ)
                 ltac:(rewrite Q3; exact G3) ltac:(rewrite Q4; exact G4)
                 ltac:(rewrite Q18; apply bv_eq; vm_compute; reflexivity)
                 ltac:(left; reflexivity) HPermD
                 ltac:(intros _; exact HNodeD) ltac:(intros Hx; discriminate Hx)
                 ltac:(cbn [Z.eqb]; exact HA1)
                 _ ltac:(intros Hx; discriminate Hx) ltac:(rewrite Hskip, Hrest; cbv beta iota; lia)).
        intros _. split; [rewrite Hr2; replace (ie_text E + ie_len E - (ie_text E + ie_len E - (ip_p P + 1)))
                            with (ip_p P + 1) by lia; exact Vpx|].
        split; [exact Vdx | rewrite Hr2; lia].
  - (* the byte is a comma *)
    match goal with H : branch_taken _ (sv_denot ?EV _) _ = false |- _ =>
      rewrite branch_ne_U, (U_atom EV 34 bb E34), (U_lit EV 44) in H by lia;
      apply Bool.negb_false_iff, Z.eqb_eq in H; rename H into Hb44 end.
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vi_Bspan (4 * Z.of_nat A_ICOMMA_SLOT).
    { vd_awr U8. }
    match goal with ms0 : machine_state |- _ =>
      lazymatch ms0 with m1 => fail | m2 => fail | _ => rename ms0 into m3 end end.
    match goal with H : frame_of _ _ (mrestrict _ (ms_mem m2)) _ |- _ => rename H into F3 end.
    assert (K3 : forall x : word, ~ (ie_q E <= bv_unsigned x < ie_q E + 8 \/
                                     ie_q E + 16 <= bv_unsigned x < ie_q E + 20) ->
                   mrestrict (w_H (ip_W P)) (ms_mem m3) x = mrestrict (w_H (ip_W P)) (ip_mem P) x).
    { intros x Hx. rewrite (vd_keepX _ _ (ie_q E) _ _ F3 ltac:(vd_fa U8) x Hx). exact (K2 x Hx). }
    assert (HRk : forall r, In r vd_live -> getr (ms_regs m3) r = getr (ip_regs P) r).
    { match type of HS with st_ok_pi _ _ ?EV _ _ =>
        assert (HA' : env_agree 32 (Ereg (ip_regs P)
                        [w64 (ip_p P); w64 (ie_text E + ie_len E); w64 bb;
                         w64 (Z.of_nat (ie_d E) + 1)]) EV);
          [ split; [intros jj Hjj | reflexivity];
            rewrite !ew_ewset_other by lia; unfold ED, vd_E;
            rewrite (Eimg_low (PI := PAI)) by (unfold A_TEXT; lia); reflexivity
          | eapply (vd_regs_after _ _ _ _ _ _ _ HS HA');
            [reflexivity | reflexivity | vm_compute; reflexivity | | ] ] end.
      - apply R9v. cbn [ew ewset Nat.eqb]. exact U8.
      - apply R27v; cbn [ew ewset Nat.eqb]; [exact U8 | exact U26]. }
    pose proof (vd_chunk_val (ip_fx P) _ _ _ _ 1%nat _ 0%nat 0 8 (SOff 32 1) (ip_p P + 1) HS
                  eq_refl eq_refl
                  ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E32; unfold w64;
                        rewrite unsigned_lit_small by lia; reflexivity)
                  ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as Vp1.
    cbn [base_val YP09.r_base ew ewset Nat.eqb] in Vp1. rewrite U8 in Vp1.
    change (N.to_nat 8) with 8%nat in Vp1. rewrite Z.add_0_r in Vp1.
    pmkst HS. apply SRr'_ret. split; [|exact HPM]. left.
    refine (ex_intro _ (vd_pos P (ms_regs m3) (ms_mem m3) _ (ip_k P) (ip_p P + 1) (pred (ip_f P)) (ip_D P)) _).
    split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|].
    pose proof (vd_chunk_val (ip_fx P) _ _ _ _ 3%nat _ 0%nat 16 4 (SOff 35 0)
                  (Z.of_nat (ie_d E) + 1) HS eq_refl eq_refl
                  ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E35, Z.add_0_r; unfold w64;
                        rewrite Z_to_bv_bv_unsigned; reflexivity)
                  ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as Vd1.
    cbn [base_val YP09.r_base ew ewset Nat.eqb] in Vd1. rewrite U8 in Vd1.
    change (N.to_nat 4) with 4%nat in Vd1.
    apply (vd_comma_make CTX CTX0 CW E P (ms_regs m3) (ms_mem m3) _ (ip_k P)
             (fun a => ie_q E <= a < ie_q E + 8 \/ ie_q E + 16 <= a < ie_q E + 20) HEN HSEP Hskip Hpe
             ltac:(rewrite <- Hb44; exact Hbyte)
             ltac:(intros a Ha; exact Ha) K3 HRk (vrd_ijrn_unbase B ARx SK E P _ _ _ _ _ _ _ HJN HJ) Vp1 Vd1).
Qed.

(* ---- PART D: the separator test (rows 265..279), the closer (rows 326..346) and the two exits ---- *)
Lemma vv_partD : forall CTX CTX0 CW E P,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vv_tail E P -> Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_ITAIL_SLOT P)
    (fun W2 c2 => ((exists P', W2 = ip_W P' /\ c2 = vrd_cfg A_ICOMMA_SLOT P' /\ ip_n P' = ip_n P /\
                               vrd_icomma_a B ARx SK E P') \/
                   (exists P' res, W2 = ip_W P' /\ c2 = vrd_cfg A_IEPI_SLOT P' /\ vrd_iexit_a B ARx SK E P' res)) /\
                  Pm (ms_mem (cfg_ms c2))).
Proof.
  intros CTX CTX0 CW E P HEN HT HPM.
  pose proof HT as (HSEP & _ & _).
  pose proof HSEP as (HFR & _ & _ & HCU & _).
  destruct (vd_bounds CTX CTX0 CW E P HEN HFR HCU)
    as (_ & _ & _ & _ & _ & _ & _ & _ & (Btp & Bpe) & _).
  destruct (Z_le_lt_eq_dec (ip_p P) (ie_text E + ie_len E) Bpe) as [Hlt | Heq].
  - exact (vd_partD_byte CTX CTX0 CW E P HEN HT Hlt HPM).
  - eapply SRr'_mono; [exact (vd_partD_end CTX CTX0 CW E P HEN HT Heq HPM)|].
    intros W' c' _ (HQ & HPm'). split; [right; exact HQ | exact HPm'].
Qed.


(* ==== THE ELEMENT STEP ==== *)
(* VrdIElem.v's tvrd_ival_aP (A2Ipro's text, VrdIElem.v at b6d759e9b2b9: parse_value at the element's nesting
   S (ie_d E) is its first premise), PROVED for the Section's Pm: the slot premises, Pm (ip_mem P), and the post with
   the PROGRESS conjunct ip_n P' = ip_n P + 1 at the comma (the count store adds the element: vv_postB) and Pm at the
   reached memory. The local tvrd_ival_aP this file used to carry is DELETED (its comma arm had no count), and the old
   tvrd_ival_a is NOT restored: it is false at the real instance (the header's counterexample). vrd_ival_holds_Pd is
   the step spelled out; vrd_ival_holds_P is the same at VrdIElem's name, and vrd_ival_okG its G form. *)
Theorem vrd_ival_holds_Pd : forall E P nm,
  (forall fx' : YK11.FPState, @tparse_value_specX fx' rc ci cp PI RL A_prog_listing PAI B ARx SK (S (ie_d E))
                                CTXv CTX0v CWv) ->
  vrd_ient_ok B ARx CTXv CTX0v CWv E -> vrd_islot_a B ARx SK E P nm -> Pm (ip_mem P) ->
  SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P) (vrd_cfg A_ISLOT_SLOT P)
    (fun W2 c2 =>
       ((exists P', W2 = ip_W P' /\ c2 = vrd_cfg A_ICOMMA_SLOT P' /\ vrd_icomma_a B ARx SK E P' /\ ip_n P' = ip_n P + 1) \/
        (exists P' res, W2 = ip_W P' /\ c2 = vrd_cfg A_IEPI_SLOT P' /\ vrd_iexit_a B ARx SK E P' res)) /\
       Pm (ms_mem (cfg_ms c2))).
Proof.
  intros E P nm HPV HEN HI HPM.
  eapply SRr'_bind; [exact (vv_partA CTXv CTX0v CWv E P nm HEN HI HPM)|].
  intros W1 c1 _ ((P1 & -> & -> & Hn1 & HSET) & HPM1).
  eapply SRr'_bind; [exact (vv_partB E P1 nm HPV HEN HSET HPM1)|].
  intros W2 c2 _ ([(P2 & -> & -> & Hn2 & HSEP) | (P2 & res & -> & -> & HX)] & HPM2).
  - (* the separator, then Part D from the separator test *)
    assert (HD : forall P4, vv_tail E P4 -> Pm (ip_mem P4) -> ip_n P4 = ip_n P + 1 ->
               SRr' SEGS YGcfRehidePost.RZ_cf (ip_W P4) (vrd_cfg A_ITAIL_SLOT P4)
                 (fun W5 c5 =>
                    ((exists P', W5 = ip_W P' /\ c5 = vrd_cfg A_ICOMMA_SLOT P' /\ vrd_icomma_a B ARx SK E P' /\
                                 ip_n P' = ip_n P + 1) \/
                     (exists P' res, W5 = ip_W P' /\ c5 = vrd_cfg A_IEPI_SLOT P' /\ vrd_iexit_a B ARx SK E P' res)) /\
                    Pm (ms_mem (cfg_ms c5)))).
    { intros P4 HTAIL HPM4 Hn4.
      eapply SRr'_mono; [exact (vv_partD CTXv CTX0v CWv E P4 HEN HTAIL HPM4)|].
      intros W5 c5 _ ([(P5 & HW5 & Hc5 & Hn5 & HC) | HX] & HPM5).
      - split; [left; exists P5; split; [exact HW5|]; split; [exact Hc5|]; split; [exact HC | lia] | exact HPM5].
      - split; [right; exact HX | exact HPM5]. }
    eapply SRr'_bind; [exact (vv_partC1 CTXv CTX0v CWv E P2 HEN HSEP HPM2)|].
    intros W3 c3 _ ([(P3 & -> & -> & Hn3 & HWSL) | (P3 & -> & -> & Hn3 & HTAIL)] & HPM3).
    + eapply SRr'_bind; [exact (vv_partC2 CTXv CTX0v CWv E P3 HEN HWSL HPM3)|].
      intros W4 c4 _ ((P4 & -> & -> & Hn4 & HTAIL) & HPM4). exact (HD P4 HTAIL HPM4 ltac:(lia)).
    + exact (HD P3 HTAIL HPM3 ltac:(lia)).
  - apply SRr'_ret. split; [right; exists P2, res; auto | exact HPM2].
Qed.

Theorem vrd_ival_holds_P : tvrd_ival_aP B ARx SK Pm CTXv CTX0v CWv.
Proof.
  unfold tvrd_ival_aP. intros E P nm HPV HEN HI HPM. exact (vrd_ival_holds_Pd E P nm HPV HEN HI HPM).
Qed.

End VI.

(* THE STEP AS VrdIElem.v FIXES IT (tvrd_ival_aG): for every memory invariant with the runner laws, the call law and
   the memnorm law, VrdIElem's tvrd_ival_aP *)
Theorem vrd_ival_okG : tvrd_ival_aG B ARx SK CTXv CTX0v CWv.
Proof. intros Pm' L C M. exact (vrd_ival_holds_P Pm' L C M). Qed.

End V.

Print Assumptions vrd_ival_okG.
Print Assumptions vrd_ival_holds_Pd.
