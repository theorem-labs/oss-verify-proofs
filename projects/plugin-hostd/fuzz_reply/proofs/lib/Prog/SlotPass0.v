(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths, module names, addresses and numbers changed; 655 of its 764 lines of code are new or changed and 1120 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/relay_instance_gone_b_seg.v, with its module paths and module names changed; 188 of its 239 lines of code are new or changed and 713 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/SlotPass5A.v, with its module paths and module names changed; 957 of its 1013 lines of code are new or changed and 183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass5Check.v, with its module paths and module names changed; 1126 of its 1248 lines of code are new or changed and 891 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT FrameAPI SlotKept SlotPack
  AllocPack AllocPack3 SlotPack3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement StatementKept SlotInv SlotRI3 SlotNcWt
  ListFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c
  RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c
  RelayRep HarnessRep ListRep CheckRep drain_b_c source_reset_c op_add_c check_bounded_c SlotInv SlotSteps SlotHead SlotHeadP SlotRes KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotHeadRun SlotHeadPick SlotHeadQ SlotWalk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessGlue HarnessFrame RelayRunT RelayRunF
  HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotEntryRun SlotEntry SlotMove.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YO0x YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Image.
Import ListNotations.
Local Open Scope Z_scope.

Definition op0_pend (i : option nat) : list (list (list byte)) :=
  match i with Some _ => [[]] | None => [] end.

(* Op 0's post state L' A': RI holds at every view that covers its blocks, adds the new source's empty pending list,
   and moves the view's nc blocks by the partial buffer op_add makes (op0_adds). *)
Definition op0_RV_t (RI : res_inv) (E : sstart) (k : Z) (L : layout) (A : astate) (G out : Z) (es : list rentry)
    (hj : list (hsrc * nat)) (i : option nat) (q : Z) (L' : layout) (A' : astate) : Prop :=
  forall G' out' es' hj',
    (forall x m, In (x, m) (blocks L' A') -> In (x, m) (blocks L A) \/ In x (target_addrs G' out' es' hj')) ->
    pend_view hj' = pend_view hj ++ op0_pend i -> ek_view hj' = ek_view hj -> (length es' <= 4)%nat ->
    (length hj' <= 4)%nat ->
    nc_move (view_of G out es hj) L A (view_of G' out' es' hj') L' A' [] (op0_adds q i) ->
    List.NoDup (map fst (blocks L' A')) ->
    (forall p n n', In (p, n) (user_blocks A) -> In (p, n') (user_blocks A') ->
       In (ptr_addr L p) (rv_nc (view_of G out es hj)) -> ~ In (ptr_addr L p) (map fst (@nil (Z * Z))) ->
       In (ptr_addr L' p) (rv_nc (view_of G' out' es' hj'))) ->
    ncs (view_of G' out' es' hj') L' A' <= nc_wt es' hj' -> nc_wt es' hj' <= nc_wt es hj ->
    RI E k (view_of G' out' es' hj') L' A'.

Definition op0_RV_s (RI : res_inv) (E : sstart) (k : Z) (L : layout) (A : astate) (G out : Z) (es : list rentry)
    (hj : list (hsrc * nat)) (i : option nat) (FD N : Z) (L' : layout) (A' : astate) (qs : list sptr) : Prop :=
  forall q,
    (i <> None ->
       live_at L' A' (resolveF qs (Ret 0)) q PARTIAL_BYTES /\
       live_at L' A' (resolveF qs (relay_add_tbl FD N 16 1 (known_at L A G))) G SRC_TABLE) ->
    op0_RV_t RI E k L A G out es hj i q L' A'.

Definition op0_res_s (RI : res_inv) : Prop :=
  forall E k L A i FD N G out es hj, RI E k (view_of G out es hj) L A -> 0 < k <= ss_n E ->
    op_at E (k - 1) = 0 -> (i <> None -> 0 <= N < 4) ->
    res_tr pack3_form (op0_RV_s RI E k L A G out es hj i FD N) A (op_add_tr i FD N 16 (known_at L A G)).

Lemma p0_jal : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x13cec) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
      x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 OP_ADD) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
      x28 x29 x30 x31) F (Z_to_bv 64 0x13ce8) fc None m ro).
Proof. intros. step. apply evt_done. reflexivity. Qed.

Lemma p0_j : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms => ms = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
      x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 TAIL_CHECK) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
      x28 x29 x30 x31) F (Z_to_bv 64 0x13cec) fc None m ro).
Proof. intros. step. apply evt_done. reflexivity. Qed.

Lemma p0_regs_jal : forall regs R1,
  Regs6ss.xregs_eqv (mkR (Z_to_bv 64 0x13cec) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
    (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10) (reg_get regs 11)
    (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15) (reg_get regs 16) (reg_get regs 17)
    (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23)
    (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29)
    (reg_get regs 30) (reg_get regs 31)) R1 ->
  getr R1 1 = Z_to_bv 64 0x13cec /\ forall r, 2 <= r < 32 -> getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
  intros regs R1 X. split; [geq X|].
  intros r Hr.
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9 \/ r = 10 \/ r = 11 \/ r = 12 \/
    r = 13 \/ r = 14 \/ r = 15 \/ r = 16 \/ r = 17 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ r = 28 \/ r = 29 \/ r = 30 \/ r = 31) by lia.
  repeat (destruct C as [C|C]; [subst r; geq X|]); subst r; geq X.
Qed.

Lemma p0_regs_same : forall regs R2,
  Regs6ss.xregs_eqv (Regs6ss.mkR_of regs) R2 -> forall r, 1 <= r < 32 -> getr R2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
  intros regs R2 X r Hr. unfold Regs6ss.mkR_of in X.
  assert (C : r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9 \/ r = 10 \/ r = 11 \/
    r = 12 \/ r = 13 \/ r = 14 \/ r = 15 \/ r = 16 \/ r = 17 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ r = 28 \/ r = 29 \/ r = 30 \/ r = 31) by lia.
  repeat (destruct C as [C|C]; [subst r; geq X|]); subst r; geq X.
Qed.

Lemma p0_ub_nonneg : forall s p n, WF s -> In (p, n) (user_blocks s) -> 0 <= n.
Proof.
  intros s p n HW Hin.
  destruct (YO0x.user_blocks_frame s p n HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & En & Ep).
  pose proof (YO10.block_in_slot s g am idx fr HW Hu Hi Hfr) as (_ & _ & H). lia.
Qed.

Definition with_keys (e : rentry) (ks : list (Z * list byte * list byte)) : rentry :=
  RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) (re_buf e) (re_used e) (re_cap e) (re_hp e) (re_kh e) (re_pad2 e)
     ks (re_U e) (re_junk e).

Definition ent_rel (e e' : rentry) : Prop := exists ks, map fst ks = map fst (re_keys e) /\ e' = with_keys e ks.

Lemma keys_fst_len : forall (ks ks' : list (Z * list byte * list byte)), map fst ks' = map fst ks -> length ks' = length ks.
Proof. intros ks ks' H. rewrite <- (length_map fst ks'), H, length_map. reflexivity. Qed.

Lemma keys_fst_addr : forall ks ks', map fst ks' = map fst ks -> map key_addr ks' = map key_addr ks.
Proof.
  intros ks ks' H. replace (map key_addr ks') with (map fst (map fst ks')) by (rewrite map_map; reflexivity).
  replace (map key_addr ks) with (map fst (map fst ks)) by (rewrite map_map; reflexivity). rewrite H. reflexivity.
Qed.

Lemma keys_fst_text : forall ks ks', map fst ks' = map fst ks -> map key_text ks' = map key_text ks.
Proof.
  intros ks ks' H. replace (map key_text ks') with (map snd (map fst ks')) by (rewrite map_map; reflexivity).
  replace (map key_text ks) with (map snd (map fst ks)) by (rewrite map_map; reflexivity). rewrite H. reflexivity.
Qed.

Lemma keys_fst_texts : forall ks ks', map fst ks' = map fst ks -> keys_texts ks' = keys_texts ks.
Proof.
  intros ks ks' H. unfold keys_texts.
  replace (map (fun k => bzs (key_text k)) ks') with (map bzs (map key_text ks')) by (rewrite map_map; reflexivity).
  replace (map (fun k => bzs (key_text k)) ks) with (map bzs (map key_text ks)) by (rewrite map_map; reflexivity).
  rewrite (keys_fst_text ks ks' H). reflexivity.
Qed.

Lemma keys_fst_total : forall ks ks', map fst ks' = map fst ks -> keys_total ks' = keys_total ks.
Proof.
  induction ks as [|k ks IH]; intros [|k' ks'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2.
  change (Z.of_nat (length (key_text k')) + 5 + keys_total ks' = Z.of_nat (length (key_text k)) + 5 + keys_total ks).
  rewrite (IH ks' H2). unfold key_text. rewrite H1. reflexivity.
Qed.

Lemma keys_fst_ptrs : forall ks ks', map fst ks' = map fst ks -> key_ptrs ks' = key_ptrs ks.
Proof.
  induction ks as [|k ks IH]; intros [|k' ks'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2.
  change (le8 (Z_to_bv 64 (key_addr k')) ++ key_ptrs ks' = le8 (Z_to_bv 64 (key_addr k)) ++ key_ptrs ks).
  rewrite (IH ks' H2). unfold key_addr. rewrite H1. reflexivity.
Qed.

Lemma ent_rel_bytes : forall e e', ent_rel e e' -> entry_bytes e' = entry_bytes e.
Proof.
  intros e e' (ks & H & ->). unfold entry_bytes, re_nheld, with_keys.
  cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_pad2 re_keys].
  rewrite (keys_fst_len _ _ H). reflexivity.
Qed.

Lemma ent_rel_blocks : forall e e', ent_rel e e' -> entry_blocks e' = entry_blocks e.
Proof.
  intros e e' (ks & H & ->). unfold entry_blocks, with_keys. cbn [re_cap re_buf re_hp re_keys].
  rewrite (keys_fst_addr _ _ H). reflexivity.
Qed.

Lemma ent_rel_fd : forall e e', ent_rel e e' -> re_fd e' = re_fd e.
Proof. intros e e' (ks & _ & ->). reflexivity. Qed.

Lemma ent_rel_cost : forall e e' p, ent_rel e e' -> pair_cost e' p = pair_cost e p.
Proof.
  intros e e' p (ks & H & ->). unfold pair_cost, with_keys. cbn [re_keys re_skip re_used].
  rewrite (keys_fst_total _ _ H). reflexivity.
Qed.

Lemma ents_rel_blocks : forall es es', Forall2 ent_rel es es' -> map entry_blocks es' = map entry_blocks es.
Proof. intros es es' H. induction H as [|e e' es es' H1 H2 IH]; [reflexivity|]. cbn [map]. rewrite IH, (ent_rel_blocks _ _ H1). reflexivity. Qed.

Lemma ents_rel_bytes : forall es es', Forall2 ent_rel es es' -> map entry_bytes es' = map entry_bytes es.
Proof. intros es es' H. induction H as [|e e' es es' H1 H2 IH]; [reflexivity|]. cbn [map]. rewrite IH, (ent_rel_bytes _ _ H1). reflexivity. Qed.

Lemma ents_rel_fd : forall es es', Forall2 ent_rel es es' -> map re_fd es' = map re_fd es.
Proof. intros es es' H. induction H as [|e e' es es' H1 H2 IH]; [reflexivity|]. cbn [map]. rewrite IH, (ent_rel_fd _ _ H1). reflexivity. Qed.

Lemma ents_rel_len : forall es es', Forall2 ent_rel es es' -> length es' = length es.
Proof. intros es es' H. induction H as [|e e' es es' H1 H2 IH]; [reflexivity|]. cbn [length]. rewrite IH. reflexivity. Qed.

Lemma ents_rel_cost : forall es es' hj, Forall2 ent_rel es es' -> slot_cost es' hj = slot_cost es hj.
Proof.
  intros es es' hj H. revert hj. induction H as [|e e' es es' H1 H2 IH]; intros [|p hj]; try reflexivity.
  change (pair_cost e' p + slot_cost es' hj = pair_cost e p + slot_cost es hj).
  rewrite IH, (ent_rel_cost _ _ _ H1). reflexivity.
Qed.

Lemma ents_rel_target : forall G OUT es es' hj, Forall2 ent_rel es es' ->
  target_addrs G OUT es' hj = target_addrs G OUT es hj.
Proof. intros G OUT es es' hj H. unfold target_addrs. rewrite (ents_rel_blocks _ _ H). reflexivity. Qed.

Lemma ent_rel_nc : forall e e', ent_rel e e' -> entry_nc e' = entry_nc e.
Proof. intros e e' (ks & _ & ->). reflexivity. Qed.

Lemma ents_rel_nc : forall es es', Forall2 ent_rel es es' -> map entry_nc es' = map entry_nc es.
Proof. intros es es' H. induction H as [|e e' es es' H1 H2 IH]; [reflexivity|]. cbn [map]. rewrite IH, (ent_rel_nc _ _ H1). reflexivity. Qed.

Lemma ents_rel_nw : forall es es', Forall2 ent_rel es es' -> AllocBound.zsum nw_ent es' = AllocBound.zsum nw_ent es.
Proof.
  intros es es' H. induction H as [|e e' es es' H1 _ IH]; [reflexivity|]. destruct H1 as (ks & HK & ->).
  rewrite !AllocBound.zsum_cons, IH. f_equal. unfold nw_ent, re_nheld, with_keys.
  cbn [re_cap re_used re_hp re_kh re_keys]. rewrite (keys_fst_len (re_keys e) ks HK). reflexivity.
Qed.

Section Frame.
Context {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis BW : blocks_writable B API.
Hypothesis SLK : block_slack_present B API.
Hypothesis ERRA : errno_addr B = 0x311ec.
Hypothesis GLB : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Variables (K sp G : Z) (W : Z -> Prop).
Variables (L : layout) (A : astate) (mem : word -> option byte) (md : Model).
Variables (L' : layout) (A' : astate) (mem' : word -> option byte) (md' : Model).
Hypothesis HM : aa_MR API L A mem md.
Hypothesis RM : rmid B API K sp W (fun _ => False) L A mem md L' A' mem' md'.
Hypothesis SPK : YM05.alloc_ceiling <= sp - K.
Hypothesis K0 : 0 <= K.
Hypothesis SPT : sp < 2 ^ 63.
Hypothesis GB : In (G, 896) (blocks L A).
Hypothesis GF : G + 896 <= YM05.alloc_ceiling.
Hypothesis WG : forall a, W a -> (0x30fc0 <= a < 0x311c0) \/ (G <= a < G + 896).
Hypothesis WD : forall a, W a \/ ~ W a.

Lemma fr_blk : forall q k i, In (q, k) (blocks L A) -> q <> G -> 0 <= i < k -> ~ W (q + i).
Proof.
  intros q k i Hin HG Hi X. destruct (WG _ X) as [D|D].
  - apply (hf_blk_img B API AX L A mem md q k i HM Hin Hi). exact (proj1 (GLB _ (in_G_bss _ D))).
  - destruct (blocks_disjoint B API L A mem md G 896 q k HM GB Hin (fun e => HG (eq_sym e))); lia.
Qed.

Lemma fr_kept : forall q, q <> G -> kept_block W (fun _ => False) L A q.
Proof. intros q HG. split; [intros []|]. intros k i Hin Hi. exact (fr_blk q k i Hin HG Hi). Qed.

Lemma fr_img : forall a, in_img B a -> ~ (0x30fc0 <= a < 0x311c0) -> ~ W a.
Proof.
  intros a Ha HN X. destruct (WG _ X) as [D|D]; [exact (HN D)|].
  apply (hf_blk_img B API AX L A mem md G 896 (a - G) HM GB ltac:(lia)). replace (G + (a - G)) with a by lia. exact Ha.
Qed.

Lemma fr_hi : forall a, YM05.alloc_ceiling <= a -> ~ W a.
Proof. intros a Ha X. pose proof (@YM05.alloc_ceiling_value rc) as AC. destruct (WG _ X); lia. Qed.

Lemma fr_cells : forall a cs, rw_cells (ms_segs B) mem a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> in_globals frame_G (a + i) /\ ~ W (a + i)) ->
  rw_cells (ms_segs B) mem' a cs.
Proof.
  intros a cs H D. apply (rmid_rw_img B API AX K sp W (fun _ => False) L A mem md L' A' mem' md' a cs
    (hg_img_low B SEG) SPK HM RM H).
  intros i Hi. destruct (D i Hi) as [Hg NW]. split; [exact (GLB _ Hg)|exact NW].
Qed.

Lemma fr_rw_hi : forall a cs, rw_cells (ms_segs B) mem a cs -> sp <= a -> a + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
  rw_cells (ms_segs B) mem' a cs.
Proof.
  intros a cs H Ha Hb. pose proof (@YM05.alloc_ceiling_value rc) as AC.
  assert (S1 : YM05.alloc_ceiling <= sp) by lia. assert (S2 : errno_addr B + 4 <= sp) by (rewrite ERRA; lia).
  apply (rmid_rw_hi (rc := rc) B API K sp W (fun _ => False) L A mem md L' A' mem' md' a cs S1 S2 HM RM H Ha Hb).
  intros i Hi. apply fr_hi. lia.
Qed.

Lemma fr_ik : forall E0, image_kept B E0 mem ->
  YM05.alloc_ceiling + SLOT_STACK <= spZ (ss_regs E0) -> spZ (ss_regs E0) < 2 ^ 63 ->
  spZ (ss_regs E0) - SLOT_STACK <= sp - K -> sp <= spZ (ss_regs E0) ->
  (forall a, W a -> in_img B a -> writable_at (ms_segs B) mem a /\ writable_at (ms_segs B) mem' a) ->
  image_kept B E0 mem'.
Proof.
  intros E0 (IK1 & IK2 & IK3 & IK4) H1 H1' H2 H3 HWW.
  pose proof (aa_laws API) as LAWS. pose proof (@YM05.alloc_ceiling_value rc) as AC.
  pose proof RM as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & BY & _ & SKW).
  assert (NO : forall a, YM05.alloc_ceiling <= a -> ~ owned B L A a /\ ~ owned B L' A' a).
  { intros a Ha. split; intro O;
      [pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HM O)|pose proof (mr_owned_low _ _ LAWS _ _ _ _ a M1 O)]; lia. }
  split; [|split; [|split]].
  - intros a HA H4 H5 H6 H7.
    assert (NG : ~ (0x30fc0 <= a < 0x311c0)) by (intro D; exact (H7 (in_G_bss _ D))).
    destruct (rmid_img B API AX K sp W (fun _ => False) L A mem md L' A' mem' md' a (hg_img_low B SEG) SPK HM RM
      (conj HA (conj H4 (conj H5 H6))) (fr_img a HA NG)) as [X Y].
    destruct (IK1 a HA H4 H5 H6 H7) as [X0 Y0]. split; [congruence|tauto].
  - intros a HA. pose proof (IK2 a HA) as Y0. destruct (GLB a HA) as (Hi & P2 & P3 & P4).
    destruct (WD a) as [Wa|Wa].
    + destruct (HWW a Wa Hi) as [Y1 Y2]. tauto.
    + destruct (rmid_img B API AX K sp W (fun _ => False) L A mem md L' A' mem' md' a (hg_img_low B SEG) SPK HM RM
        (conj Hi (conj P2 (conj P3 P4))) Wa) as [_ Y]. tauto.
  - intros a HA HNS.
    destruct (NO a (proj1 HA)) as [N1 N2].
    destruct (BY a (or_introl HA) N1 N2) as [X Y].
    + unfold sk. intros [X|X]; apply HNS; unfold lib_scratch; [left; lia|right; exact X].
    + apply fr_hi. lia.
    + destruct (IK3 a HA HNS) as [X0 Y0]. split; [congruence|tauto].
  - intros a HA.
    assert (D : sk B K sp a \/ ~ sk B K sp a) by (unfold sk; lia).
    destruct D as [D|D]; [exact (SKW a D)|].
    pose proof (IK4 a HA) as W0.
    assert (Ha : YM05.alloc_ceiling <= a < 2 ^ 64).
    { unfold lib_scratch, sk in *. destruct HA as [HA|HA]; [lia|exfalso; apply D; right; exact HA]. }
    destruct (NO a (proj1 Ha)) as [N1 N2].
    destruct (BY a (or_introl Ha) N1 N2 D (fr_hi a (proj1 Ha))) as [_ Y]. tauto.
Qed.

Lemma fr_dk : forall E0 TA TA', WF (ss_A E0) -> driver_kept B E0 TA L A mem -> In G TA ->
  (forall a, In a TA -> In a TA') ->
  (forall x, In x (blocks L' A') -> In x (blocks L A) \/ In (fst x) TA') ->
  (forall a, In a TA' -> ~ In a TA -> forall p m, In (p, m) (blocks L A) -> 0 < m -> p <> a) ->
  (0 < ss_n E0 -> (exists q, In (q, ss_n E0) (user_blocks (ss_A E0)) /\ ptr_addr (ss_L E0) q = ss_p E0) /\
     ~ In (ss_p E0, ss_n E0) (ss_T E0)) ->
  driver_kept B E0 TA' L' A' mem'.
Proof.
  intros E0 TA TA' HW0 (DK1 & DK2 & DK3 & DK4) GT INC BL NEW INP.
  pose proof RM as (M1 & _ & _ & _ & _ & PA & SV & Z0 & _ & _ & _ & BK & _).
  assert (KEEP : forall q m, In (q, m) (user_blocks (ss_A E0)) -> ~ In (ptr_addr (ss_L E0) q, m) (ss_T E0) ->
    exists q', In (q', m) (user_blocks A) /\ In (q', m) (user_blocks A') /\ ptr_addr L q' = ptr_addr (ss_L E0) q /\
      ptr_addr L' q' = ptr_addr (ss_L E0) q /\ (0 < m -> ~ In (ptr_addr (ss_L E0) q) TA')).
  { intros q m Hq HT. destruct (DK1 q m Hq HT) as (NT & q' & Hq' & EQ).
    pose proof (p0_ub_nonneg _ _ _ HW0 Hq) as Hm0.
    assert (NT' : 0 < m -> ~ In (ptr_addr (ss_L E0) q) TA').
    { intros Hm X. destruct (in_dec Z.eq_dec (ptr_addr (ss_L E0) q) TA) as [Y|Y]; [exact (NT Hm Y)|].
      apply (NEW _ X Y (ptr_addr L q') m); [|exact Hm|exact EQ].
      exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (q', m) Hq'). }
    destruct (Z.eq_dec m 0) as [->|Hm].
    - destruct (Z0 q' Hq') as (Hq'' & EQ'). exists q'. split; [exact Hq'|]. split; [exact Hq''|].
      split; [exact EQ|]. split; [congruence|exact NT'].
    - assert (Hp : 0 < m) by lia. pose proof (SV q' m Hq' Hp (fun X => X)) as Hq''.
      pose proof (PA q' m Hq' Hq'' (fun X => X)) as EQ'.
      exists q'. split; [exact Hq'|]. split; [exact Hq''|]. split; [exact EQ|]. split; [congruence|exact NT']. }
  split; [|split; [|split]].
  - intros q m Hq HT. destruct (KEEP q m Hq HT) as (q' & _ & Hq'' & _ & EQ' & NT').
    split; [exact NT'|]. exists q'. split; [exact Hq''|exact EQ'].
  - intros q m i Hq HT HNP Hi.
    destruct (KEEP q m Hq HT) as (q' & Hq' & Hq'' & EQ & _ & NT').
    assert (NG : ptr_addr L q' <> G).
    { rewrite EQ. intro X. apply (NT' ltac:(lia)). rewrite X. apply INC. exact GT. }
    rewrite <- EQ.
    rewrite (BK q' m i Hq' Hq'' (fun X => X) Hi
      (fr_blk _ m i (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (q', m) Hq') NG Hi)).
    rewrite EQ. exact (DK2 q m i Hq HT HNP Hi).
  - intros i Hi. destruct (INP ltac:(lia)) as ((q & Hq & EP) & HT).
    rewrite <- EP in HT. destruct (KEEP q (ss_n E0) Hq HT) as (q' & Hq' & Hq'' & EQ & _ & NT').
    assert (NG : ptr_addr L q' <> G).
    { rewrite EQ. intro X. apply (NT' ltac:(lia)). rewrite X. apply INC. exact GT. }
    rewrite <- EP, <- EQ.
    rewrite (BK q' (ss_n E0) i Hq' Hq'' (fun X => X) Hi
      (fr_blk _ _ i (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (q', ss_n E0) Hq') NG Hi)).
    rewrite EQ, EP. exact (DK3 i Hi).
  - intros q m Hin. destruct (BL (q, m) Hin) as [X|X].
    + destruct (DK4 q m X) as [Y|Y]; [left; exact Y|right; exact (INC _ Y)].
    + right. exact X.
Qed.

Lemma fr_out : forall nout cap out, output_at B L A mem nout cap out ->
  (0 < bv_unsigned cap -> bv_unsigned out <> G) -> output_at B L' A' mem' nout cap out.
Proof.
  intros nout cap out H0 HG. unfold output_at in *. cbv zeta in *.
  destruct H0 as ((O & junk & H) & HC). split; [|exact HC]. exists O, junk.
  destruct H as [H|(H1 & H2 & Hin & Hfr & Hby & H3 & H4)]; [left; exact H|right].
  split; [exact H1|]. split; [exact H2|].
  pose proof (HG H1) as NG.
  split; [exact (proj1 (rmid_block B API BW K sp W (fun _ => False) L A mem md L' A' mem' md' _ _ 0 RM Hin H1
    (fun X => X) ltac:(lia) (fr_blk _ _ 0 Hin NG ltac:(lia))))|].
  split; [exact Hfr|].
  split; [|split; assumption].
  apply (rmid_bytes_block B API BW K sp W (fun _ => False) L A mem md L' A' mem' md' _ _ _ _ RM Hin H1 (fun X => X) Hby);
    [lia|rewrite length_app; lia|].
  intros i Hi. rewrite length_app in Hi. apply (fr_blk _ _ i Hin NG). lia.
Qed.

Definition key_ok (L0 : layout) (A0 : astate) (m0 : word -> option byte) (k : Z * list byte * list byte) : Prop :=
  In (key_addr k, Z.of_nat (length (key_text k)) + 1) (blocks L0 A0) /\
  fresh_block B (key_addr k) (Z.of_nat (length (key_text k)) + 1) /\
  bytes_at (ms_segs B) m0 (key_addr k) (key_text k ++ Z_to_bv 8 0 :: key_slack k) /\
  ~ In (Z_to_bv 8 0) (key_text k) /\ 14 <= Z.of_nat (length (key_text k)) <= 6000 /\
  (- (key_addr k + Z.of_nat (length (key_text k)) + 1)) mod 8 <= Z.of_nat (length (key_slack k)).

Lemma fr_key : forall k, key_ok L A mem k -> key_addr k <> G -> exists sl, key_ok L' A' mem' (fst k, sl).
Proof.
  intros [[a t] s] (HB & HF & HY & HZ & HL & HS) HG. unfold key_ok. cbn [key_addr key_text key_slack fst snd] in *.
  pose proof RM as (M1 & _).
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (FB : 4096 <= a /\ a + (Z.of_nat (length t) + 1) <= YM05.alloc_ceiling) by (destruct HF as (F1 & F2 & _); lia).
  destruct (rmid_block B API BW K sp W (fun _ => False) L A mem md L' A' mem' md' a _ 0 RM HB ltac:(lia) (fun X => X)
    ltac:(lia) (fr_blk a _ 0 HB HG ltac:(lia))) as (HB' & _ & _).
  pose proof (Z.mod_pos_bound (- (a + (Z.of_nat (length t) + 1))) 8 ltac:(lia)) as R8.
  destruct (present_rw_cells (ms_segs B) mem' (a + (Z.of_nat (length t) + 1))
    (Z.to_nat ((- (a + (Z.of_nat (length t) + 1))) mod 8)) ltac:(lia) ltac:(lia)) as (sl & SL).
  { intros i Hi. apply (SLK L' A' mem' md' a (Z.of_nat (length t) + 1) _ M1 HB').
    assert (RD : 8 * ((a + (Z.of_nat (length t) + 1) + 7) / 8) =
      a + (Z.of_nat (length t) + 1) + (- (a + (Z.of_nat (length t) + 1))) mod 8) by (Z.div_mod_to_equations; lia).
    lia. }
  destruct SL as ((WFc & BYs) & _). cbn [cells_wf cell_wf] in WFc. destruct WFc as [LS _].
  cbn [cells_bytes cbytes] in BYs. rewrite app_nil_r in BYs.
  exists sl.
  split; [exact HB'|]. split; [exact HF|].
  split.
  { replace (t ++ Z_to_bv 8 0 :: sl) with ((t ++ [Z_to_bv 8 0]) ++ sl) by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split.
    - replace (t ++ Z_to_bv 8 0 :: s) with ((t ++ [Z_to_bv 8 0]) ++ s) in HY by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app in HY. destruct HY as [HY _].
      apply (rmid_bytes_block B API BW K sp W (fun _ => False) L A mem md L' A' mem' md' a _ a _ RM HB ltac:(lia)
        (fun X => X) HY); [lia|rewrite length_app; cbn [length]; lia|].
      intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply (fr_blk a _ i HB HG). lia.
    - rewrite length_app. cbn [length]. replace (a + Z.of_nat (length t + 1)) with (a + (Z.of_nat (length t) + 1)) by lia.
      exact BYs. }
  split; [exact HZ|]. split; [exact HL|]. rewrite LS. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma fr_keys : forall ks, Forall (key_ok L A mem) ks -> (forall k, In k ks -> key_addr k <> G) ->
  exists ks', map fst ks' = map fst ks /\ Forall (key_ok L' A' mem') ks'.
Proof.
  induction ks as [|k ks IH]; intros HF HG; [exists []; split; [reflexivity|constructor]|].
  inversion HF as [|? ? Hk Hks]; subst.
  destruct (fr_key k Hk (HG k (or_introl eq_refl))) as (sl & Hk').
  destruct (IH Hks (fun k0 H => HG k0 (or_intror H))) as (ks' & E & Hks').
  exists ((fst k, sl) :: ks'). split; [cbn; rewrite E; reflexivity|constructor; assumption].
Qed.

Lemma fr_entry : forall e, RelayRep.entry_ok B L A mem e -> (forall q, In q (entry_blocks e) -> q <> G) ->
  exists e', ent_rel e e' /\ RelayRep.entry_ok B L' A' mem' e'.
Proof.
  intros e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & BU & H10 & HP & ND1 & ND2 & KS) HG.
  destruct (fr_keys (re_keys e) KS) as (ks' & EK & KS').
  { intros k Hk. apply HG. unfold entry_blocks. rewrite !in_app_iff. right. right. apply in_map. exact Hk. }
  pose proof (keys_fst_len _ _ EK) as LK.
  exists (with_keys e ks'). split; [exists ks'; split; [exact EK|reflexivity]|].
  unfold RelayRep.entry_ok, re_nheld, with_keys in *.
  cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk].
  rewrite LK.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
  split.
  { destruct BU as [BU|(Hc & Hin & Hfr & Hj & Hcells)]; [left; exact BU|right].
    assert (NG : re_buf e <> G).
    { apply HG. unfold entry_blocks. rewrite (proj2 (Z.eqb_neq (re_cap e) 0) ltac:(lia)). left. reflexivity. }
    split; [exact Hc|].
    split; [exact (proj1 (rmid_block B API BW K sp W (fun _ => False) L A mem md L' A' mem' md' _ _ 0 RM Hin Hc
      (fun X => X) ltac:(lia) (fr_blk _ _ 0 Hin NG ltac:(lia))))|].
    split; [exact Hfr|]. split; [exact Hj|].
    apply (rmid_rw_block B API BW K sp W (fun _ => False) L A mem md L' A' mem' md' _ _ _ _ RM Hin Hc (fun X => X) Hcells);
      [lia|cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia|].
    intros i Hi. cbn [cells_size csize] in Hi. rewrite Nat.add_0_r, Z2Nat.id in Hi by lia.
    apply (fr_blk _ _ i Hin NG). lia. }
  split; [exact H10|].
  split.
  { destruct HP as [(Hh & Hk0)|(Hin & Hfr & Hn & Hk8 & Hby)].
    - left. split; [exact Hh|]. rewrite Hk0 in EK. destruct ks'; [reflexivity|discriminate].
    - right.
      assert (NG : re_hp e <> G).
      { destruct Hfr as (F1 & _). apply HG. unfold entry_blocks. rewrite in_app_iff. right.
        rewrite (proj2 (Z.eqb_neq (re_hp e) 0) ltac:(lia)). left. reflexivity. }
      split; [exact (proj1 (rmid_block B API BW K sp W (fun _ => False) L A mem md L' A' mem' md' _ _ 0 RM Hin
        ltac:(lia) (fun X => X) ltac:(lia) (fr_blk _ _ 0 Hin NG ltac:(lia))))|].
      split; [exact Hfr|]. split; [exact Hn|]. split; [exact Hk8|].
      rewrite (keys_fst_ptrs _ _ EK).
      pose proof (slot_key_ptrs_length (re_keys e)) as KPL.
      apply (rmid_bytes_block B API BW K sp W (fun _ => False) L A mem md L' A' mem' md' _ _ _ _ RM Hin ltac:(lia)
        (fun X => X) Hby); [lia|rewrite KPL; lia|].
      intros i Hi. rewrite KPL in Hi. apply (fr_blk _ _ i Hin NG). lia. }
  split; [rewrite (keys_fst_addr _ _ EK); exact ND1|].
  split; [rewrite (keys_fst_text _ _ EK); exact ND2|].
  exact KS'.
Qed.

Lemma fr_ents : forall es, Forall (RelayRep.entry_ok B L A mem) es ->
  (forall e q, In e es -> In q (entry_blocks e) -> q <> G) ->
  exists es', Forall2 ent_rel es es' /\ Forall (RelayRep.entry_ok B L' A' mem') es'.
Proof.
  induction es as [|e es IH]; intros HF HG; [exists []; split; constructor|].
  inversion HF as [|? ? He Hes]; subst.
  destruct (fr_entry e He (fun q Hq => HG e q (or_introl eq_refl) Hq)) as (e' & R & He').
  destruct (IH Hes (fun e0 q H Hq => HG e0 q (or_intror H) Hq)) as (es' & Rs & Hes').
  exists (e' :: es'). split; constructor; assumption.
Qed.

Lemma fr_src : forall HA h, src_at B L A mem HA h ->
  (forall x, 0 <= x < 96 -> in_globals frame_G (HA + x) /\ ~ W (HA + x)) ->
  (forall q, In q (hs_blocks h) -> q <> G) ->
  src_at B L' A' mem' HA h.
Proof.
  intros HA h S HX HG. apply src_at_iff in S. destruct S as (SB & LE & LH & ND). apply src_at_iff.
  assert (IMGP : forall x, 0 <= x < 96 -> img_plain B (HA + x) /\ ~ W (HA + x)).
  { intros x Hx. destruct (HX x Hx) as [Hg NW]. split; [exact (GLB _ Hg)|exact NW]. }
  split; [|split; [|split; [|exact ND]]].
  - apply (src_base_rmid B API AX BW K sp W (fun _ => False) L A mem md L' A' mem' md' HA h SEG SPK HM RM SB).
    + intros i Hi. apply IMGP. lia.
    + intros q Hq. apply fr_kept. apply HG. unfold hs_blocks. rewrite !in_app_iff. cbn [In].
      destruct Hq as [Hq|Hq]; [left; exact Hq|right; left; left; symmetry; exact Hq].
  - apply (list_at_rmid B API AX BW K sp W (fun _ => False) L A mem md L' A' mem' md' (HA + 64) (hs_expected h) true
      SEG SPK HM RM LE).
    + intros i Hi. replace (HA + 64 + i) with (HA + (64 + i)) by lia. apply IMGP. lia.
    + intros q Hq. apply fr_kept. apply HG. unfold hs_blocks. rewrite !in_app_iff. tauto.
  - apply (list_at_rmid B API AX BW K sp W (fun _ => False) L A mem md L' A' mem' md' (HA + 80) (hs_held h) true
      SEG SPK HM RM LH).
    + intros i Hi. replace (HA + 80 + i) with (HA + (80 + i)) by lia. apply IMGP. lia.
    + intros q Hq. apply fr_kept. apply HG. unfold hs_blocks. rewrite !in_app_iff. tauto.
Qed.

Lemma fr_pair : forall t e e' p, pair_ok B L A mem t e p -> ent_rel e e' ->
  (forall x, 0 <= x < 96 -> ~ W (G_S + SRC_SIZE * Z.of_nat (snd p) + x)) ->
  (forall q, In q (hs_blocks (fst p)) -> q <> G) ->
  pair_ok B L' A' mem' t e' p.
Proof.
  intros t e e' p HP ER HX HG. unfold pair_ok in *. cbv zeta in *.
  destruct HP as (S & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  destruct ER as (ks & EK & ->). unfold with_keys. cbn [re_fd re_eof re_skip re_U re_keys].
  split.
  { apply fr_src; [exact S| |exact HG]. intros x Hx. split; [|exact (HX x Hx)].
    apply in_G_bss. unfold G_S, SRC_SIZE. lia. }
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [rewrite (keys_fst_texts _ _ EK); exact H4|].
  repeat split; assumption.
Qed.

Lemma fr_pairs : forall t es es' hj, Forall2 (pair_ok B L A mem t) es hj -> Forall2 ent_rel es es' ->
  (forall p x, In p hj -> 0 <= x < 96 -> ~ W (G_S + SRC_SIZE * Z.of_nat (snd p) + x)) ->
  (forall p q, In p hj -> In q (hs_blocks (fst p)) -> q <> G) ->
  Forall2 (pair_ok B L' A' mem' t) es' hj.
Proof.
  intros t es es' hj H. revert es'. induction H as [|e p es hj HP HR IH]; intros es' ER HX HG.
  - inversion ER. constructor.
  - inversion ER as [|? e' ? es'' R1 R2]; subst. constructor.
    + apply (fr_pair t e e' p HP R1); [intros x Hx; exact (HX p x (or_introl eq_refl) Hx)|].
      intros q Hq. exact (HG p q (or_introl eq_refl) Hq).
    + apply IH; [exact R2| |].
      * intros p0 x H0 Hx. exact (HX p0 x (or_intror H0) Hx).
      * intros p0 q H0 Hq. exact (HG p0 q (or_intror H0) Hq).
Qed.

End Frame.

Lemma p0_fz_some : forall os i, first_zero os = Some i -> (i < length os)%nat /\ nth i os 0 = 0.
Proof.
  induction os as [|o os IH]; intros i H; cbn [first_zero] in H; [discriminate|].
  destruct (Z.eqb_spec o 0) as [->|Ho].
  - injection H as <-. cbn. split; [lia|reflexivity].
  - destruct (first_zero os) as [i'|] eqn:Hf; cbn in H; [|discriminate].
    injection H as <-. destruct (IH i' eq_refl) as [H1 H2]. cbn [length nth]. split; [lia|exact H2].
Qed.

Lemma p0_flag_cells : forall rc B L A mem t nfd G OUT es hj i,
  relay_at (rc := rc) B L A mem t nfd G OUT es hj -> (i < 4)%nat ->
  rw_cells (ms_segs B) mem (G_S + SRC_SIZE * Z.of_nat i + 4) [C4 (Z_to_bv 64 (open_flag hj i))].
Proof.
  intros rc B L A mem t nfd G OUT es hj i (_ & _ & _ & _ & _ & _ & PA & _ & ZH & _) HI.
  unfold open_flag. destruct (slot_open hj i) eqn:HO.
  - unfold slot_open in HO. apply existsb_exists in HO. destruct HO as (q & HQ & HE).
    apply Nat.eqb_eq in HE. subst q. apply in_map_iff in HQ. destruct HQ as ([h q] & EQ & HQ). cbn in EQ. subst q.
    destruct (pair_find _ _ _ _ _ (h, i) PA HQ) as [e HP].
    destruct HP as (SRC & _). cbv zeta in SRC. cbn [fst snd] in SRC.
    destruct SRC as (C & _ & _ & OPEN & _). rewrite OPEN in C.
    destruct (hg_cut _ _ _ [C4 (Z_to_bv 64 (hs_fd h))]
      [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 (hs_closed h)); C4 (Z_to_bv 64 (hs_eintr h))] C) as [_ C2].
    exact (proj1 (hg_cut _ _ _ [C4 (Z_to_bv 64 1)] [C4 (Z_to_bv 64 (hs_closed h)); C4 (Z_to_bv 64 (hs_eintr h))] C2)).
  - specialize (ZH i HI HO).
    assert (S' : rw_cells (ms_segs B) mem (G_S + SRC_SIZE * Z.of_nat i)
        [CB 4 (nulbytes 4); C4 (Z_to_bv 64 0); CB 88 (nulbytes 88)])
      by (eapply rw_cells_retype; [exact ZH|cbn; tauto|reflexivity]).
    destruct (hg_cut _ _ _ [CB 4 (nulbytes 4)] [C4 (Z_to_bv 64 0); CB 88 (nulbytes 88)] S') as [_ S2].
    exact (proj1 (hg_cut _ _ _ [C4 (Z_to_bv 64 0)] [CB 88 (nulbytes 88)] S2)).
Qed.

Lemma p0_open_count : forall (hj : list (hsrc * nat)) i, List.NoDup (map snd hj) ->
  (forall p, In p hj -> (snd p < 4)%nat) -> (i < 4)%nat -> slot_open hj i = false -> (length hj < 4)%nat.
Proof.
  intros hj i ND LT HI HO.
  assert (INC : incl (map snd hj) (remove Nat.eq_dec i (seq 0 4))).
  { intros x Hx. apply in_in_remove.
    - intros ->. assert (X : existsb (Nat.eqb i) (map snd hj) = true).
      { apply existsb_exists. exists i. split; [exact Hx|apply Nat.eqb_refl]. }
      unfold slot_open in HO. congruence.
    - apply in_map_iff in Hx as (p & <- & Hp). apply in_seq. pose proof (LT p Hp). lia. }
  pose proof (NoDup_incl_length ND INC) as HL. rewrite length_map in HL.
  destruct i as [|[|[|[|i]]]]; cbn in HL; lia.
Qed.

Definition p0_ne (FD : Z) : rentry := RE FD 0 0 (nulbytes 4) 0 0 0 0 0 (nulbytes 4) [] [] [].

Lemma p0_ne_bytes : forall FD, entry_bytes (p0_ne FD) = new_entry FD.
Proof.
  intros FD. unfold entry_bytes, new_entry, p0_ne, re_nheld.
  cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_keys re_pad2 length Z.of_nat].
  f_equal.
Qed.

Lemma p0_ne_ok : forall rc B L A mem FD, 0 <= FD < 2 ^ 31 -> RelayRep.entry_ok (rc := rc) B L A mem (p0_ne FD).
Proof.
  intros rc B L A mem FD HFD. unfold RelayRep.entry_ok, p0_ne, re_nheld.
  cbn [re_eof re_skip re_pad1 re_pad2 re_fd re_cap re_U re_used re_buf re_hp re_keys re_junk].
  repeat split; try reflexivity; try (left; repeat split; reflexivity);
    try constructor; try tauto; try lia.
Qed.

Lemma p0_new_pair : forall rc B L A mem t FD q pj i, 0 <= t -> (i < 4)%nat ->
  src_at (rc := rc) B L A mem (G_S + SRC_SIZE * Z.of_nat i) (new_src FD q pj) ->
  pair_ok (rc := rc) B L A mem t (p0_ne FD) (new_src FD q pj, i).
Proof.
  intros rc B L A mem t FD q pj i Ht HI HS. unfold pair_ok. cbv zeta. cbn [fst snd].
  split; [exact HS|]. split; [exact HI|].
  unfold p0_ne, new_src, empty_list, pending_stream, texts, same_set, drain_b_c.keys_texts, hs_W.
  cbn. repeat split; try constructor; try tauto; try lia.
  all: unfold hl_n, WRITE_MAX; cbn; lia.
Qed.

Lemma p0_cost_cons : forall e es p hj, slot_cost (e :: es) (p :: hj) = pair_cost e p + slot_cost es hj.
Proof. reflexivity. Qed.

Lemma p0_cost_app : forall es hj e p, length es = length hj ->
  slot_cost (es ++ [e]) (hj ++ [p]) = slot_cost es hj + pair_cost e p.
Proof.
  induction es as [|e0 es IH]; intros [|p0 hj] e p H; cbn [length] in H; try discriminate.
  - cbn. lia.
  - injection H as H. cbn [app]. rewrite !p0_cost_cons, (IH hj e p H). lia.
Qed.

Lemma p0_new_cost : forall FD q pj i, pair_cost (p0_ne FD) (new_src FD q pj, i) = 0.
Proof. reflexivity. Qed.

Lemma p0_target_app : forall G OUT es hj FD q pj i,
  target_addrs G OUT (es ++ [p0_ne FD]) (hj ++ [(new_src FD q pj, i)]) = target_addrs G OUT es hj ++ [q].
Proof.
  intros. unfold target_addrs. rewrite !map_app, !concat_app. cbn. rewrite !app_nil_r. rewrite <- !app_assoc.
  reflexivity.
Qed.

Lemma p0_nc_app : forall G OUT es hj FD q pj i,
  rv_nc (view_of G OUT (es ++ [p0_ne FD]) (hj ++ [(new_src FD q pj, i)])) = rv_nc (view_of G OUT es hj) ++ [q].
Proof.
  intros. unfold view_of. cbn [rv_nc]. rewrite !map_app, !concat_app. cbn. rewrite !app_nil_r. rewrite <- !app_assoc.
  reflexivity.
Qed.

Lemma p0_list_blocks : forall rc B L A mem LA l lines x,
  list_at (rc := rc) B L A mem LA l lines -> In x (list_blocks l) -> exists m, 0 < m /\ In (x, m) (blocks L A).
Proof.
  intros rc B L A mem LA l lines x (C & HN & AR & ND1 & ND2 & RS) Hx. unfold list_blocks in Hx.
  apply in_app_or in Hx as [Hx|Hx].
  - revert Hx. destruct (Z.eqb_spec (hl_cap l) 0) as [H0|H0]; intros Hx; [destruct Hx|].
    destruct Hx as [<-|[]].
    destruct AR as [(Hc & _)|(Hc & Hin & _)]; [lia|]. exists (16 * hl_cap l). split; [lia|exact Hin].
  - apply in_map_iff in Hx as (r & <- & Hr). rewrite Forall_forall in RS. destruct (RS r Hr) as (Hin & _).
    exists (Z.of_nat (length (snd r)) + 1). split; [lia|exact Hin].
Qed.

Lemma p0_src_blocks : forall rc B L A mem HA h x,
  src_at (rc := rc) B L A mem HA h -> In x (hs_blocks h) -> exists m, 0 < m /\ In (x, m) (blocks L A).
Proof.
  intros rc B L A mem HA h x (C1 & H1 & H2 & H3 & H4 & LP & C2 & H5 & H6 & H7 & IN & FR & HJ & C3 & NZ & LE & LH & ND) Hx.
  unfold hs_blocks in Hx. rewrite !in_app_iff in Hx.
  destruct Hx as [Hx|[[<-|[]]|[Hx|Hx]]].
  - exact (p0_list_blocks _ _ _ _ _ _ _ _ x LP Hx).
  - exists 6000. split; [lia|exact IN].
  - exact (p0_list_blocks _ _ _ _ _ _ _ _ x LE Hx).
  - exact (p0_list_blocks _ _ _ _ _ _ _ _ x LH Hx).
Qed.

Lemma p0_entry_blocks : forall rc B L A mem e x,
  RelayRep.entry_ok (rc := rc) B L A mem e -> In x (entry_blocks e) -> exists m, 0 < m /\ In (x, m) (blocks L A).
Proof.
  intros rc B L A mem e x (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & BU & H10 & HP & ND1 & ND2 & KS) Hx.
  unfold entry_blocks in Hx. apply in_app_or in Hx as [Hx|Hx].
  - revert Hx. destruct (Z.eqb_spec (re_cap e) 0) as [H0|H0]; intros Hx; [destruct Hx|].
    destruct Hx as [<-|[]]. destruct BU as [(Hc & _)|(Hc & Hin & _)]; [lia|].
    exists (re_cap e). split; [lia|exact Hin].
  - apply in_app_or in Hx as [Hx|Hx].
    + revert Hx. destruct (Z.eqb_spec (re_hp e) 0) as [H0|H0]; intros Hx; [destruct Hx|].
      destruct Hx as [<-|[]]. destruct HP as [(Hh & _)|(Hin & _ & _ & Hk8 & _)]; [lia|].
      exists (re_kh e). split; [lia|exact Hin].
    + apply in_map_iff in Hx as (k & <- & Hk). rewrite Forall_forall in KS. destruct (KS k Hk) as (Hin & _).
      exists (Z.of_nat (length (key_text k)) + 1). split; [lia|exact Hin].
Qed.

Lemma p0_target_blocks : forall rc B L A mem t nfd G es hj nout cap out,
  relay_at (rc := rc) B L A mem t nfd G (bv_unsigned out) es hj -> output_at (rc := rc) B L A mem nout cap out ->
  forall x, In x (target_addrs G (bv_unsigned out) es hj) -> x = 0 \/ exists m, 0 < m /\ In (x, m) (blocks L A).
Proof.
  intros rc B L A mem t nfd G es hj nout cap out ((tail & TAB) & GIN & GFR & HES & HFD & HRG & PA & HND & ZH & NDT)
    ((O & junk & HO) & HC) x Hx.
  unfold target_addrs in Hx. destruct Hx as [<-|[<-|Hx]].
  - right. exists SRC_TABLE. split; [unfold SRC_TABLE, SRC_ENTRY; lia|exact GIN].
  - destruct HO as [(H1 & H2 & _)|(H1 & H2 & H3 & _)]; [left; exact H2|right].
    exists (bv_unsigned cap). split; [exact H1|exact H3].
  - right. apply in_app_or in Hx as [Hx|Hx].
    + apply in_concat in Hx as (l & Hl & Hx). apply in_map_iff in Hl as (e & <- & He).
      rewrite Forall_forall in HES. exact (p0_entry_blocks _ _ _ _ _ e x (HES e He) Hx).
    + apply in_concat in Hx as (l & Hl & Hx). apply in_map_iff in Hl as (p & <- & Hp).
      destruct (pair_find _ _ _ _ _ p PA Hp) as [e (SRC & _)].
      exact (p0_src_blocks _ _ _ _ _ _ _ x SRC Hx).
Qed.
Lemma p0_ents_len : forall rc B L A mem es, Forall (RelayRep.entry_ok (rc := rc) B L A mem) es ->
  Z.of_nat (length (concat (map entry_bytes es))) = SRC_ENTRY * Z.of_nat (length es).
Proof.
  intros rc B L A mem es. induction es as [|e es IH]; intros H; [reflexivity|].
  inversion H as [|? ? He Hes]; subst. cbn [map concat length].
  rewrite length_app, (entry_size _ _ _ _ _ _ He), Nat2Z.inj_add, (IH Hes). unfold SRC_ENTRY. lia.
Qed.

Lemma p0_os_nth : forall hj i, (i < 4)%nat -> nth i (map (open_flag hj) (seq 0 4)) 0 = open_flag hj i.
Proof. intros hj i H. destruct i as [|[|[|[|i]]]]; [reflexivity..|lia]. Qed.

Lemma p0_hj_lt : forall rc B L A mem t es hj, Forall2 (pair_ok (rc := rc) B L A mem t) es hj ->
  forall p, In p hj -> (snd p < 4)%nat.
Proof. intros rc B L A mem t es hj H p Hp. destruct (pair_find _ _ _ _ _ p H Hp) as [e (_ & HL & _)]. exact HL. Qed.

Definition p0_W (i : nat) (G N a : Z) : Prop :=
  0x31040 + 96 * Z.of_nat i <= a < 0x31040 + 96 * Z.of_nat i + 96 \/ 0x30fe0 <= a < 0x30fe0 + 4 \/
  0x31018 + 4 <= a < 0x31018 + 8 \/ 0x30fd8 <= a < 0x30fd8 + 8 \/ 0x30ff0 <= a < 0x30ff0 + 8 \/
  (0 < 16 /\ G + 56 * N <= a < G + 56 * (N + 1)).

Ltac p0_num := unfold p0_W, G_S, SRC_SIZE, SOURCES_MAX, G_NFD, Statement.G_LOCK, relay_event_c.G_LOCK,
  Statement.G_NSRC, relay_add_b_c.G_NSRC, check_bounded_c.G_NSRC, StatementKept.G_SRC, relay_add_b_c.G_SRC,
  check_bounded_c.G_SRC, Statement.G_THREAD_UP, relay_finish_b_c.G_THREAD_UP, relay_finish_b_c.G_LISTEN,
  G_WAKE0, G_WAKE1, G_BROKEN, CheckRep.G_GONE, G_DEAD, G_EINTR, G_OUTV, SRC_TABLE, SRC_ENTRY, G_RELAY_LO.

Ltac p0_num_in H := unfold p0_W, G_S, SRC_SIZE, SOURCES_MAX, G_NFD, Statement.G_LOCK, relay_event_c.G_LOCK,
  Statement.G_NSRC, relay_add_b_c.G_NSRC, check_bounded_c.G_NSRC, StatementKept.G_SRC, relay_add_b_c.G_SRC,
  check_bounded_c.G_SRC, Statement.G_THREAD_UP, relay_finish_b_c.G_THREAD_UP, relay_finish_b_c.G_LISTEN,
  G_WAKE0, G_WAKE1, G_BROKEN, CheckRep.G_GONE, G_DEAD, G_EINTR, G_OUTV, SRC_TABLE, SRC_ENTRY, G_RELAY_LO in H.

Lemma p0_frame : forall B API LS SH SK ra empty rc fx j E CS,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  ms_segs B = rsegs /\ ms_tp B = 0x31290 /\ ms_errno_off B = -164 /\ errno_addr B = 0x311ec /\
  AllocExtra B (aa_MR (API rc)) /\ blocks_writable B (API rc) /\ block_slack_present B (API rc) /\
  (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
     ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4)).
Proof.
  intros B API LS SH SK ra empty rc fx j E CS (FF & _ & _ & _).
  assert (FA : @frame_allocator rc fx B (API rc)).
  { assert (ALL : forall rc fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    exact (ALL rc fx). }
  assert (ETP : ms_tp B = 0x31290) by (unfold frame_facts in FF; tauto).
  assert (EOFF : ms_errno_off B = -164) by (unfold frame_facts in FF; tauto).
  split; [unfold frame_facts in FF; tauto|]. split; [exact ETP|]. split; [exact EOFF|].
  split; [unfold errno_addr; rewrite ETP, EOFF; reflexivity|].
  split; [unfold frame_allocator in FA; tauto|]. split; [unfold frame_allocator in FA; tauto|].
  split; [unfold frame_allocator in FA; tauto|]. unfold frame_facts in FF; tauto.
Qed.

Lemma p0_target_G : forall G OUT es hj, NoDup (target_addrs G OUT es hj) ->
  OUT <> G /\ (forall e q, In e es -> In q (entry_blocks e) -> q <> G) /\
  (forall p q, In p hj -> In q (hs_blocks (fst p)) -> q <> G).
Proof.
  intros G OUT es hj H. apply NoDup_ListNoDup in H. unfold target_addrs in H.
  inversion H as [|? ? HG _]; subst. split; [|split].
  - intros EQ. apply HG. left. exact EQ.
  - intros e q He Hq EQ. subst q. apply HG. right. apply in_or_app. left. apply in_concat.
    exists (entry_blocks e). split; [apply in_map; exact He|exact Hq].
  - intros p q Hp Hq EQ. subst q. apply HG. right. apply in_or_app. right. apply in_concat.
    exists (hs_blocks (fst p)). split; [apply (in_map (fun p => hs_blocks (fst p))); exact Hp|exact Hq].
Qed.

Lemma p0_nodup_snoc : forall (X : Type) (l : list X) x, List.NoDup l -> ~ In x l -> List.NoDup (l ++ [x]).
Proof.
  intros X l. induction l as [|y l IH]; intros x H Hx; cbn; [constructor; [intros []|constructor]|].
  inversion H as [|? ? Hy Hl]; subst. constructor.
  - rewrite in_app_iff. intros [X1|[X1|[]]]; [exact (Hy X1)|subst; apply Hx; left; reflexivity].
  - apply IH; [exact Hl|intros X1; apply Hx; right; exact X1].
Qed.

Lemma p0_open_snoc : forall (hj : list (hsrc * nat)) p jj,
  slot_open (hj ++ [p]) jj = slot_open hj jj || Nat.eqb jj (snd p).
Proof. intros hj p jj. unfold slot_open. rewrite map_app, existsb_app. cbn. rewrite orb_false_r. reflexivity. Qed.

Lemma p0_tail_keep : forall E t K regs R1 regs' R2,
  tail_regs E t K regs ->
  (forall r, 2 <= r < 32 -> getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  regs_preserved R1 regs' ->
  (forall r, 1 <= r < 32 -> getr R2 (Z_to_bv 5 r) = getr regs' (Z_to_bv 5 r)) ->
  tail_regs E t K R2.
Proof.
  intros E t K regs R1 regs' R2 ((B2 & B3 & B4 & B20) & (F19 & F21 & F24 & F25 & F26 & F27) & R8 & R23 & R22) H1 RP H2.
  refine (conj (conj _ (conj _ (conj _ _))) (conj (conj _ (conj _ (conj _ (conj _ (conj _ _))))) (conj _ (conj _ _)))).
  - exact (eq_trans (H2 2 ltac:(lia)) (eq_trans (RP 2 ltac:(unfold callee_saved; lia)) (eq_trans (H1 2 ltac:(lia)) B2))).
  - exact (eq_trans (H2 3 ltac:(lia)) (eq_trans (RP 3 ltac:(unfold callee_saved; lia)) (eq_trans (H1 3 ltac:(lia)) B3))).
  - exact (eq_trans (H2 4 ltac:(lia)) (eq_trans (RP 4 ltac:(unfold callee_saved; lia)) (eq_trans (H1 4 ltac:(lia)) B4))).
  - exact (eq_trans (H2 20 ltac:(lia)) (eq_trans (RP 20 ltac:(unfold callee_saved; lia)) (eq_trans (H1 20 ltac:(lia)) B20))).
  - exact (eq_trans (H2 19 ltac:(lia)) (eq_trans (RP 19 ltac:(unfold callee_saved; lia)) (eq_trans (H1 19 ltac:(lia)) F19))).
  - exact (eq_trans (H2 21 ltac:(lia)) (eq_trans (RP 21 ltac:(unfold callee_saved; lia)) (eq_trans (H1 21 ltac:(lia)) F21))).
  - exact (eq_trans (H2 24 ltac:(lia)) (eq_trans (RP 24 ltac:(unfold callee_saved; lia)) (eq_trans (H1 24 ltac:(lia)) F24))).
  - exact (eq_trans (H2 25 ltac:(lia)) (eq_trans (RP 25 ltac:(unfold callee_saved; lia)) (eq_trans (H1 25 ltac:(lia)) F25))).
  - exact (eq_trans (H2 26 ltac:(lia)) (eq_trans (RP 26 ltac:(unfold callee_saved; lia)) (eq_trans (H1 26 ltac:(lia)) F26))).
  - exact (eq_trans (H2 27 ltac:(lia)) (eq_trans (RP 27 ltac:(unfold callee_saved; lia)) (eq_trans (H1 27 ltac:(lia)) F27))).
  - exact (eq_trans (H2 8 ltac:(lia)) (eq_trans (RP 8 ltac:(unfold callee_saved; lia)) (eq_trans (H1 8 ltac:(lia)) R8))).
  - exact (eq_trans (H2 23 ltac:(lia)) (eq_trans (RP 23 ltac:(unfold callee_saved; lia)) (eq_trans (H1 23 ltac:(lia)) R23))).
  - exact (eq_trans (H2 22 ltac:(lia)) (eq_trans (RP 22 ltac:(unfold callee_saved; lia)) (eq_trans (H1 22 ltac:(lia)) R22))).
Qed.

Lemma p0_post_some : forall B API LS SH SK ra empty rc fx j E CS RI t K
    (fx' : FPState) L A mem md cl br gn dd ei G nfd mx nout cap out es hj
    L' A' mem' md' R2 i q pj rest,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  frm_zero (@fp_csr fx') -> 0 <= t < OPS_MAX -> 0 <= K <= ss_n E -> ss_n E < INPUT_MAX ->
  tail_regs E t K R2 ->
  aa_MR (API rc) L A mem md -> (exists vm, md = with_vmmaps vm (ss_md E)) ->
  image_kept (rc := rc) B E mem -> stack_mid B E mem ->
  driver_kept B E (target_addrs G (bv_unsigned out) es hj) L A mem ->
  globals_at B mem cl br gn dd ei (Z.of_nat (length es)) G nfd mx nout cap out -> 0 <= nfd <= t + 1 ->
  output_at (rc := rc) B L A mem nout cap out -> relay_at (rc := rc) B L A mem t nfd G (bv_unsigned out) es hj ->
  slot_cost es hj <= K -> (i < 4)%nat -> slot_open hj i = false ->
  rmid B (API rc) OP_ADD_K (slot_sp E) (p0_W i G (Z.of_nat (length es))) (fun _ => False)
    L A mem md L' A' mem' md' ->
  st_init_done A' = true -> ro_agree (ms_segs B) mem' -> op0_RV_t RI E K L A G (bv_unsigned out) es hj (Some i) q L' A' ->
  src_at (rc := rc) B L' A' mem' (G_S + SRC_SIZE * Z.of_nat i) (new_src (FIRST_FD + nfd) q pj) ->
  rw_cells (ms_segs B) mem' G_NFD [C4 (Z_to_bv 64 (nfd + 1))] ->
  rw_cells (ms_segs B) mem' G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells (ms_segs B) mem' G_NSRC [C4 (Z_to_bv 64 (Z.of_nat (length es) + 1)); C4 (Z_to_bv 64 16)] ->
  rw_cells (ms_segs B) mem' G_SRC [C8 (Z_to_bv 64 G)] ->
  In (G, SRC_TABLE) (blocks L' A') ->
  Z.of_nat (length rest) = SRC_TABLE - SRC_ENTRY * (Z.of_nat (length es) + 1) ->
  rw_cells (ms_segs B) mem' G
    [CB (Z.to_nat SRC_TABLE) (concat (map entry_bytes es) ++ new_entry (FIRST_FD + nfd) ++ rest)] ->
  fresh_block (rc := rc) B q PARTIAL_BYTES ->
  (forall p m, In (p, m) (blocks L A) -> 0 < m -> p <> q) ->
  (exists d1 d2, blocks L' A' = d1 ++ (q, PARTIAL_BYTES) :: d2 /\ d1 ++ d2 = blocks L A) ->
  MI (rc := rc) B (API rc) E RI t K TAIL_CHECK (fun _ _ _ r => tail_regs E t K r)
    (mkCfg (@YK11.mkst fx' R2 (Z_to_bv 64 TAIL_CHECK) mem' (seg_rom (ms_segs B))) md').
Proof.
  intros B API LS SH SK ra empty rc fx j E CS RI t K fx' L A mem md cl br gn dd ei G nfd mx nout cap out es hj
    L' A' mem' md' R2 i q pj rest HF FZ Ht Hk Hn HRG HMR HVM HIK HST HDK HGL Hnfd HOUT HREL Hcost HI HO RM
    INIT' RO' HRI' SRC0 NFD1 LOCK1 NSRC1 GSRC1 GBL' RL GTAB QF QNEW (d1 & d2 & EB & ED).
  destruct (p0_frame B API LS SH SK ra empty rc fx j E CS HF) as (SEG & ETP & EOFF & ERRA & AX & BW & SLK & GLB).
  pose proof HF as (_ & _ & (((_ & HW0 & _ & _ & _ & _ & SPLO & SPHI & _ & _ & _ & _ & _ & INPUT & _) & _) &
    _ & _ & _ & _ & _ & NI & _) & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  set (W := p0_W i G (Z.of_nat (length es))) in *.
  pose proof HREL as ((tail & TL & TAB) & GIN & GFR & HES & HNDF & HFD & PA & HNDS & ZH & NDT).
  pose proof HGL as (GL1 & GL2 & GL3 & GL4 & GL5 & GL6 & GL7 & GL8 & GL9 & GL10 & GL11 & GL12 & GL13 & GLE & GLR).
  pose proof RM as (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & MD1 & _ & _ & _).
  assert (HLEN : length es = length hj) by exact (Forall2_length PA).
  assert (N4 : (length es < 4)%nat).
  { rewrite HLEN. exact (p0_open_count hj i (proj1 (NoDup_ListNoDup _) HNDS) (p0_hj_lt _ _ _ _ _ _ _ _ PA) HI HO). }
  assert (SPK : YM05.alloc_ceiling <= slot_sp E - OP_ADD_K).
  { change OP_ADD_K with 8352. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  assert (K0 : 0 <= OP_ADD_K) by (change OP_ADD_K with 8352; lia).
  assert (GB : In (G, 896) (blocks L A)) by exact GIN.
  assert (GF : G + 896 <= YM05.alloc_ceiling).
  { destruct GFR as (_ & H & _). unfold SRC_TABLE, SRC_ENTRY in H. lia. }
  assert (WG : forall a, W a -> 200640 <= a < 201152 \/ G <= a < G + 896).
  { intros a X. unfold W in X. p0_num_in X. lia. }
  assert (WD : forall a, W a \/ ~ W a) by (intros a; unfold W; p0_num; lia).
  assert (GTI : forall a, in_img B a -> ~ (G <= a < G + 896)).
  { intros a Ha X. destruct GFR as (_ & _ & NX). apply (NX (a - G)); [unfold SRC_TABLE, SRC_ENTRY; lia|].
    replace (G + (a - G)) with a by lia. exact Ha. }
  assert (NWG : forall a, (0x20d38 <= a < 0x20d48 \/ 0x30fc0 <= a < 0x311c0) ->
      ~ (0x31040 + 96 * Z.of_nat i <= a < 0x31040 + 96 * Z.of_nat i + 96) ->
      ~ (0x30fd8 <= a < 0x30fe4) -> ~ (0x3101c <= a < 0x31020) -> ~ (0x30ff0 <= a < 0x30ff8) ->
      in_globals frame_G a /\ ~ W a).
  { intros a Ha N1 N2 N3 N5. assert (IG : in_globals frame_G a).
    { destruct Ha as [Ha|Ha]; [exists 0x20d38, 16; split; [left; reflexivity|lia]|apply in_G_bss; lia]. }
    split; [exact IG|]. intros X. pose proof (proj1 (GLB a IG)) as HIa. unfold W in X. p0_num_in X.
    destruct X as [X|[X|[X|[X|[X|(_ & X)]]]]]; try lia. apply (GTI a HIa). lia. }
  pose proof (fr_cells B (API rc) SEG AX GLB OP_ADD_K (slot_sp E) W L A mem md L' A' mem' md' HMR RM SPK) as FC.
  pose proof (fr_rw_hi B (API rc) ERRA OP_ADD_K (slot_sp E) G W L A mem md L' A' mem' md' HMR RM SPK K0 GF WG) as FH.
  destruct (p0_target_G _ _ _ _ NDT) as (GNO & GNE & GNH).
  destruct (fr_ents B (API rc) AX BW SLK GLB OP_ADD_K (slot_sp E) G W L A mem md L' A' mem' md' HMR RM GB WG es HES GNE)
    as (es' & ER & HES').
  assert (PX : forall p x, In p hj -> 0 <= x < 96 -> ~ W (G_S + SRC_SIZE * Z.of_nat (snd p) + x)).
  { intros p x Hp Hx X.
    assert (Hpi : snd p <> i).
    { intros EQ. assert (Y : slot_open hj i = true).
      { unfold slot_open. apply existsb_exists. exists (snd p). split; [apply in_map; exact Hp|rewrite EQ; apply Nat.eqb_refl]. }
      congruence. }
    pose proof (p0_hj_lt _ _ _ _ _ _ _ _ PA p Hp) as Hp4.
    assert (IG : in_globals frame_G (G_S + SRC_SIZE * Z.of_nat (snd p) + x)) by (apply in_G_bss; p0_num; lia).
    pose proof (proj1 (GLB _ IG)) as HIa. unfold W in X. p0_num_in X. p0_num_in HIa.
    destruct X as [X|[X|[X|[X|[X|(_ & X)]]]]]; try lia. apply (GTI _ HIa). lia. }
  pose proof (fr_pairs B (API rc) SEG AX BW GLB OP_ADD_K (slot_sp E) G W L A mem md L' A' mem' md' HMR RM SPK GB WG
    t es es' hj PA ER PX GNH) as PA'.
  assert (QT : ~ In q (target_addrs G (bv_unsigned out) es hj)).
  { intros X. destruct (p0_target_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ HREL HOUT q X) as [Q0|(m & Hm & Hin)].
    - destruct QF as (QL & _). lia.
    - exact (QNEW q m Hin Hm eq_refl). }
  assert (REL' : relay_at (rc := rc) B L' A' mem' (t + 1) (nfd + 1) G (bv_unsigned out)
      (es' ++ [p0_ne (FIRST_FD + nfd)]) (hj ++ [(new_src (FIRST_FD + nfd) q pj, i)])).
  { unfold relay_at. split; [|split; [exact GBL'|split; [exact GFR|]]].
    { exists rest. unfold table_at. split.
      - rewrite length_app, (ents_rel_len _ _ ER). cbn [length]. rewrite RL. unfold SRC_TABLE, SRC_ENTRY. lia.
      - rewrite map_app, concat_app, (ents_rel_bytes _ _ ER). cbn [map concat]. rewrite app_nil_r, p0_ne_bytes, <- app_assoc.
        exact GTAB. }
    split.
    { apply Forall_app. split; [exact HES'|]. constructor; [|constructor].
      apply p0_ne_ok. unfold FIRST_FD, OPS_MAX in *. lia. }
    split.
    { apply NoDup_ListNoDup. rewrite map_app, (ents_rel_fd _ _ ER). cbn [map].
      apply p0_nodup_snoc; [apply NoDup_ListNoDup; exact HNDF|]. intros X.
      rewrite Forall_forall in HFD. apply in_map_iff in X as (e & EQ & He). pose proof (HFD e He) as Y.
      cbn [re_fd p0_ne] in EQ. lia. }
    split.
    { apply Forall_app. split.
      - rewrite Forall_forall in HFD |- *. intros e' He'.
        assert (X : In (re_fd e') (map re_fd es)) by (rewrite <- (ents_rel_fd _ _ ER); apply in_map; exact He').
        apply in_map_iff in X as (e & EQ & He). pose proof (HFD e He). lia.
      - constructor; [cbn [re_fd p0_ne]; lia|constructor]. }
    split.
    { apply Forall2_app.
      - eapply Forall2_impl; [|exact PA']. intros e p H. eapply pair_ok_t; [exact H|lia].
      - constructor; [|constructor]. apply p0_new_pair; [lia|exact HI|exact SRC0]. }
    split.
    { apply NoDup_ListNoDup. rewrite map_app. cbn [map snd].
      apply p0_nodup_snoc; [apply NoDup_ListNoDup; exact HNDS|]. intros X. unfold slot_open in HO.
      assert (Y : existsb (Nat.eqb i) (map snd hj) = true) by (apply existsb_exists; exists i; split; [exact X|apply Nat.eqb_refl]).
      congruence. }
    split.
    { intros jj Hj Hso. rewrite p0_open_snoc in Hso. apply orb_false_iff in Hso as [Hso1 Hso2].
      cbn [snd] in Hso2. apply Nat.eqb_neq in Hso2.
      apply FC; [exact (ZH jj Hj Hso1)|]. intros x Hx. cbn in Hx. apply NWG; p0_num; lia. }
    rewrite p0_target_app, (ents_rel_target _ _ _ _ _ ER). apply NoDup_ListNoDup.
    apply p0_nodup_snoc; [apply NoDup_ListNoDup; exact NDT|exact QT]. }
  assert (GL' : globals_at B mem' cl br gn dd ei (Z.of_nat (length (es' ++ [p0_ne (FIRST_FD + nfd)]))) G (nfd + 1)
      mx nout cap out).
  { replace (Z.of_nat (length (es' ++ [p0_ne (FIRST_FD + nfd)]))) with (Z.of_nat (length es) + 1)
      by (rewrite length_app, (ents_rel_len _ _ ER); cbn [length]; lia).
    unfold globals_at.
    split; [apply FC; [exact GL1|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [apply FC; [exact GL2|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [apply FC; [exact GL3|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [apply FC; [exact GL4|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [apply FC; [exact GL5|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [apply FC; [exact GL6|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [apply FC; [exact GL7|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [exact NSRC1|]. split; [exact NFD1|]. split; [exact GSRC1|].
    split; [apply FC; [exact GL11|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [exact LOCK1|].
    split; [apply FC; [exact GL13|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [rewrite SEG; exact (entry_errno_cells B SEG ETP EOFF mem')|].
    exact GLR. }
  assert (ST' : stack_mid B E mem').
  { destruct HST as (ST1 & ST2 & ST3). unfold stack_mid.
    split; [apply FH; [exact ST1|lia|unfold saved_cells; cbn; unfold slot_sp, SLOT_FRAME in *; lia]|].
    split; [apply FH; [exact ST2|lia|cbn; unfold slot_sp, SLOT_FRAME in *; lia]|].
    apply FH; [exact ST3|lia|cbn; unfold slot_sp, SLOT_FRAME in *; lia]. }
  assert (IK' : image_kept (rc := rc) B E mem').
  { apply (fr_ik B (API rc) SEG AX GLB OP_ADD_K (slot_sp E) G W L A mem md L' A' mem' md' HMR RM SPK GB GF WG WD E HIK).
    - exact SPLO.
    - exact SPHI.
    - change OP_ADD_K with 8352. unfold slot_sp, SLOT_FRAME, SLOT_STACK. lia.
    - unfold slot_sp, SLOT_FRAME. lia.
    - intros a X Ha. assert (BS : 0x30fc0 <= a < 0x311c0).
      { destruct (WG a X) as [Y|Y]; [lia|exfalso; exact (GTI a Ha Y)]. }
      rewrite SEG. split; [exact (proj1 (entry_global_access mem a (in_G_bss a BS)))|
        exact (proj1 (entry_global_access mem' a (in_G_bss a BS)))]. }
  assert (DK' : driver_kept B E (target_addrs G (bv_unsigned out) (es' ++ [p0_ne (FIRST_FD + nfd)])
      (hj ++ [(new_src (FIRST_FD + nfd) q pj, i)])) L' A' mem').
  { rewrite p0_target_app, (ents_rel_target _ _ _ _ _ ER).
    apply (fr_dk B (API rc) AX GLB OP_ADD_K (slot_sp E) G W L A mem md L' A' mem' md' HMR RM GB WG E
      (target_addrs G (bv_unsigned out) es hj)); [exact HW0|exact HDK|left; reflexivity| | | |].
    - intros a Ha. apply in_or_app. left. exact Ha.
    - intros x Hx. rewrite EB in Hx. apply in_app_or in Hx as [Hx|[<-|Hx]].
      + left. rewrite <- ED. apply in_or_app. left. exact Hx.
      + right. apply in_or_app. right. left. reflexivity.
      + left. rewrite <- ED. apply in_or_app. right. exact Hx.
    - intros a Ha Hna p m Hpm Hm. apply in_app_or in Ha as [Ha|[<-|[]]]; [contradiction|exact (QNEW p m Hpm Hm)].
    - intros HN0. split; [|exact (NI HN0)].
      destruct INPUT as [(HN & _)|(_ & qp & HQP & HPP)]; [lia|exists qp; split; assumption]. }
  pose proof (fr_out B (API rc) AX BW GLB OP_ADD_K (slot_sp E) G W L A mem md L' A' mem' md' HMR RM GB WG
    nout cap out HOUT (fun _ => GNO)) as OUT'.
  assert (HVM' : exists vm, md' = with_vmmaps vm (ss_md E)).
  { destruct HVM as (vm & E1). destruct MD1 as (vm' & E2). exists vm'. rewrite E2, E1. apply with_vmmaps_twice. }
  unfold MI.
  exists fx', L', A', R2, mem', md', cl, br, gn, dd, ei, G, (nfd + 1), mx, nout, cap, out,
    (es' ++ [p0_ne (FIRST_FD + nfd)]), (hj ++ [(new_src (FIRST_FD + nfd) q pj, i)]).
  replace (t + (if (TAIL_CHECK =? TAIL_CHECK) || (TAIL_CHECK =? TAIL_STEP) then 2 else 1)) with (t + 2)
    by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
  replace (t + (if (TAIL_CHECK =? TAIL_CHECK) || (TAIL_CHECK =? TAIL_STEP) then 1 else 0)) with (t + 1)
    by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
  split; [reflexivity|]. split; [exact FZ|]. split; [exact Ht|]. split; [exact Hk|]. split; [exact Hn|].
  split; [exact HRG|].
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact INIT'|]. split; [exact HVM'|].
  split; [exact RO'|]. split; [exact IK'|]. split; [exact ST'|]. split; [exact DK'|]. split; [exact GL'|].
  split; [lia|]. split; [exact OUT'|]. split; [exact REL'|].
  split; [rewrite length_app, (ents_rel_len _ _ ER); cbn [length]; lia|].
  split.
  { rewrite p0_cost_app by (rewrite (ents_rel_len _ _ ER); exact HLEN).
    rewrite p0_new_cost, (ents_rel_cost _ _ hj ER). lia. }
  apply HRI'.
  - intros qq mm HQ. rewrite EB in HQ. apply in_app_or in HQ as [HQ|[HQ|HQ]].
    + left. rewrite <- ED. apply in_or_app. left. exact HQ.
    + right. injection HQ as <- <-. rewrite p0_target_app. apply in_or_app. right. left. reflexivity.
    + left. rewrite <- ED. apply in_or_app. right. exact HQ.
  - unfold pend_view. rewrite map_app. reflexivity.
  - transitivity (ek_view hj ++ []); [|apply app_nil_r]. unfold ek_view. rewrite map_app, concat_app. reflexivity.
  - rewrite length_app, (ents_rel_len _ _ ER). cbn [length]. lia.
  - rewrite length_app. cbn [length]. lia.
  - (* op_add made the new source's partial buffer (q, PARTIAL_BYTES) and kept every other block. *)
    change (op0_adds q (Some i)) with [(q, PARTIAL_BYTES)].
    apply (entry_mv_ins _ _ _ _ _ _ (rv_nc (view_of G (bv_unsigned out) es hj)) []);
      [exact (entry_blk_nd B API LS SH SK ra empty rc fx j E CS _ _ _ _ HF HMR)|
       exact (entry_blk_nd B API LS SH SK ra empty rc fx j E CS _ _ _ _ HF M1)| | | | | | | | |].
    + rewrite app_nil_r. apply Permutation_refl.
    + rewrite p0_nc_app. unfold view_of. cbn [rv_nc]. rewrite (ents_rel_nc _ _ ER). apply Permutation_refl.
    + intros x m Hx. rewrite EB in Hx. apply entry_in_mid in Hx as [Ex|Hx].
      * right. rewrite <- Ex. left. reflexivity.
      * left. rewrite <- ED. exact Hx.
    + intros x m Hx. rewrite EB. apply entry_in_mid. right. rewrite ED. exact Hx.
    + intros u [<-|[]]. rewrite EB. apply entry_in_mid. left. reflexivity.
    + constructor; [intros []|constructor].
    + intros u [<-|[]] Hin. exact (QNEW q PARTIAL_BYTES Hin ltac:(unfold PARTIAL_BYTES; lia) eq_refl).
    + intros x m Hx. exact (entry_blk_nn rc B (API rc) _ _ _ _ x m M1 Hx).
    + intros g [].
  - exact (entry_blk_nd B API LS SH SK ra empty rc fx j E CS _ _ _ _ HF M1).
  - intros p n n' Hp _ Hin _. pose proof RM as (_ & _ & _ & LY1 & _).
    rewrite (lf_addr A L L' p n (mr_wf _ _ (aa_laws (API rc)) _ _ _ _ HMR) LY1 Hp).
    rewrite p0_nc_app. apply in_or_app. left.
    unfold view_of in Hin |- *. cbn [rv_nc] in Hin |- *. rewrite (ents_rel_nc _ _ ER). exact Hin.
  - exact (ncs_le_wt B (API rc) L' A' mem' md' (t + 1) (nfd + 1) G nout cap out _ _ M1 OUT' REL'
      ltac:(rewrite length_app, (ents_rel_len _ _ ER); cbn [length]; lia)
      (entry_blk_nd B API LS SH SK ra empty rc fx j E CS _ _ _ _ HF M1)).
  - unfold nc_wt. rewrite !AllocBound.zsum_app, !AllocBound.zsum_cons, !AllocBound.zsum_nil, (ents_rel_nw _ _ ER).
    rewrite !length_app, (ents_rel_len _ _ ER). cbn [length fst].
    rewrite nw_src_new. change (nw_ent (p0_ne (FIRST_FD + nfd))) with NW_ENT0.
    unfold NW_ENT0, NW_SRC0, PARTIAL_BYTES. lia.
Qed.

Lemma p0_post_none : forall B API LS SH SK ra empty rc fx j E CS RI t K
    (fx' : FPState) L A mem md cl br gn dd ei G nfd mx nout cap out es hj L' A' mem' md' R2,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  frm_zero (@fp_csr fx') -> 0 <= t < OPS_MAX -> 0 <= K <= ss_n E -> ss_n E < INPUT_MAX ->
  tail_regs E t K R2 ->
  aa_MR (API rc) L A mem md -> (exists vm, md = with_vmmaps vm (ss_md E)) ->
  image_kept (rc := rc) B E mem -> stack_mid B E mem ->
  driver_kept B E (target_addrs G (bv_unsigned out) es hj) L A mem ->
  globals_at B mem cl br gn dd ei (Z.of_nat (length es)) G nfd mx nout cap out -> 0 <= nfd <= t + 1 ->
  output_at (rc := rc) B L A mem nout cap out -> relay_at (rc := rc) B L A mem t nfd G (bv_unsigned out) es hj ->
  (length es <= 4)%nat -> slot_cost es hj <= K ->
  rmid B (API rc) OP_ADD_K (slot_sp E) (fun _ => False) (fun _ => False) L A mem md L' A' mem' md' ->
  blocks L' A' = blocks L A ->
  st_init_done A' = true -> ro_agree (ms_segs B) mem' -> op0_RV_t RI E K L A G (bv_unsigned out) es hj None 0 L' A' ->
  MI (rc := rc) B (API rc) E RI t K TAIL_CHECK (fun _ _ _ r => tail_regs E t K r)
    (mkCfg (@YK11.mkst fx' R2 (Z_to_bv 64 TAIL_CHECK) mem' (seg_rom (ms_segs B))) md').
Proof.
  intros B API LS SH SK ra empty rc fx j E CS RI t K fx' L A mem md cl br gn dd ei G nfd mx nout cap out es hj
    L' A' mem' md' R2 HF FZ Ht Hk Hn HRG HMR HVM HIK HST HDK HGL Hnfd HOUT HREL Hes Hcost RM EB INIT' RO' HRI'.
  destruct (p0_frame B API LS SH SK ra empty rc fx j E CS HF) as (SEG & ETP & EOFF & ERRA & AX & BW & SLK & GLB).
  pose proof HF as (_ & _ & (((_ & HW0 & _ & _ & _ & _ & SPLO & SPHI & _ & _ & _ & _ & _ & INPUT & _) & _) &
    _ & _ & _ & _ & _ & NI & _) & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof HREL as ((tail & TL & TAB) & GIN & GFR & HES & HNDF & HFD & PA & HNDS & ZH & NDT).
  pose proof HGL as (GL1 & GL2 & GL3 & GL4 & GL5 & GL6 & GL7 & GL8 & GL9 & GL10 & GL11 & GL12 & GL13 & GLE & GLR).
  pose proof RM as (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & MD1 & _ & _ & _).
  assert (HLEN : length es = length hj) by exact (Forall2_length PA).
  assert (SPK : YM05.alloc_ceiling <= slot_sp E - OP_ADD_K).
  { change OP_ADD_K with 8352. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  assert (K0 : 0 <= OP_ADD_K) by (change OP_ADD_K with 8352; lia).
  assert (GB : In (G, 896) (blocks L A)) by exact GIN.
  assert (GF : G + 896 <= YM05.alloc_ceiling).
  { destruct GFR as (_ & H & _). unfold SRC_TABLE, SRC_ENTRY in H. lia. }
  assert (WG : forall a, (fun _ : Z => False) a -> 200640 <= a < 201152 \/ G <= a < G + 896) by (intros a []).
  assert (WD : forall a, (fun _ : Z => False) a \/ ~ (fun _ : Z => False) a) by (intros a; right; intros []).
  assert (NWG : forall a, (0x20d38 <= a < 0x20d48 \/ 0x30fc0 <= a < 0x311c0) ->
      in_globals frame_G a /\ ~ (fun _ : Z => False) a).
  { intros a Ha. split; [|intros []].
    destruct Ha as [Ha|Ha]; [exists 0x20d38, 16; split; [left; reflexivity|lia]|apply in_G_bss; lia]. }
  pose proof (fr_cells B (API rc) SEG AX GLB OP_ADD_K (slot_sp E) (fun _ => False) L A mem md L' A' mem' md'
    HMR RM SPK) as FC.
  pose proof (fr_rw_hi B (API rc) ERRA OP_ADD_K (slot_sp E) G (fun _ => False) L A mem md L' A' mem' md'
    HMR RM SPK K0 GF WG) as FH.
  destruct (p0_target_G _ _ _ _ NDT) as (GNO & GNE & GNH).
  destruct (fr_ents B (API rc) AX BW SLK GLB OP_ADD_K (slot_sp E) G (fun _ => False) L A mem md L' A' mem' md'
    HMR RM GB WG es HES GNE) as (es' & ER & HES').
  pose proof (fr_pairs B (API rc) SEG AX BW GLB OP_ADD_K (slot_sp E) G (fun _ => False) L A mem md L' A' mem' md'
    HMR RM SPK GB WG t es es' hj PA ER (fun _ _ _ _ X => X) GNH) as PA'.
  assert (REL' : relay_at (rc := rc) B L' A' mem' (t + 1) nfd G (bv_unsigned out) es' hj).
  { unfold relay_at. split; [|split; [rewrite EB; exact GIN|split; [exact GFR|]]].
    { exists tail. unfold table_at. split; [rewrite (ents_rel_len _ _ ER); exact TL|].
      rewrite (ents_rel_bytes _ _ ER).
      apply (rmid_rw_block B (API rc) BW OP_ADD_K (slot_sp E) (fun _ => False) (fun _ => False)
        L A mem md L' A' mem' md' G 896 G _ RM GIN ltac:(lia) (fun X => X) TAB); [lia|cbn; lia|intros x _ []]. }
    split; [exact HES'|].
    split; [rewrite (ents_rel_fd _ _ ER); exact HNDF|].
    split.
    { rewrite Forall_forall in HFD |- *. intros e' He'.
      assert (X : In (re_fd e') (map re_fd es)) by (rewrite <- (ents_rel_fd _ _ ER); apply in_map; exact He').
      apply in_map_iff in X as (e & EQ & He). pose proof (HFD e He). lia. }
    split; [eapply Forall2_impl; [|exact PA']; intros e p H; eapply pair_ok_t; [exact H|lia]|].
    split; [exact HNDS|].
    split; [intros jj Hj Hso; apply FC; [exact (ZH jj Hj Hso)|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    rewrite (ents_rel_target _ _ _ _ _ ER). exact NDT. }
  assert (GL' : globals_at B mem' cl br gn dd ei (Z.of_nat (length es')) G nfd mx nout cap out).
  { rewrite (ents_rel_len _ _ ER). unfold globals_at.
    split; [apply FC; [exact GL1|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [apply FC; [exact GL2|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [apply FC; [exact GL3|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [apply FC; [exact GL4|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [apply FC; [exact GL5|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [apply FC; [exact GL6|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [apply FC; [exact GL7|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [apply FC; [exact GL8|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [apply FC; [exact GL9|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [apply FC; [exact GL10|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [apply FC; [exact GL11|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [apply FC; [exact GL12|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [apply FC; [exact GL13|intros x Hx; cbn in Hx; apply NWG; p0_num; lia]|].
    split; [rewrite SEG; exact (entry_errno_cells B SEG ETP EOFF mem')|].
    exact GLR. }
  assert (ST' : stack_mid B E mem').
  { destruct HST as (ST1 & ST2 & ST3). unfold stack_mid.
    split; [apply FH; [exact ST1|lia|unfold saved_cells; cbn; unfold slot_sp, SLOT_FRAME in *; lia]|].
    split; [apply FH; [exact ST2|lia|cbn; unfold slot_sp, SLOT_FRAME in *; lia]|].
    apply FH; [exact ST3|lia|cbn; unfold slot_sp, SLOT_FRAME in *; lia]. }
  assert (IK' : image_kept (rc := rc) B E mem').
  { apply (fr_ik B (API rc) SEG AX GLB OP_ADD_K (slot_sp E) G (fun _ => False) L A mem md L' A' mem' md'
      HMR RM SPK GB GF WG WD E HIK).
    - exact SPLO.
    - exact SPHI.
    - change OP_ADD_K with 8352. unfold slot_sp, SLOT_FRAME, SLOT_STACK. lia.
    - unfold slot_sp, SLOT_FRAME. lia.
    - intros a []. }
  assert (DK' : driver_kept B E (target_addrs G (bv_unsigned out) es' hj) L' A' mem').
  { rewrite (ents_rel_target _ _ _ _ _ ER).
    apply (fr_dk B (API rc) AX GLB OP_ADD_K (slot_sp E) G (fun _ => False) L A mem md L' A' mem' md' HMR RM GB WG E
      (target_addrs G (bv_unsigned out) es hj)); [exact HW0|exact HDK|left; reflexivity| | | |].
    - intros a Ha. exact Ha.
    - intros x Hx. left. rewrite <- EB. exact Hx.
    - intros a Ha Hna. contradiction.
    - intros HN0. split; [|exact (NI HN0)].
      destruct INPUT as [(HN & _)|(_ & qp & HQP & HPP)]; [lia|exists qp; split; assumption]. }
  pose proof (fr_out B (API rc) AX BW GLB OP_ADD_K (slot_sp E) G (fun _ => False) L A mem md L' A' mem' md'
    HMR RM GB WG nout cap out HOUT (fun _ => GNO)) as OUT'.
  assert (HVM' : exists vm, md' = with_vmmaps vm (ss_md E)).
  { destruct HVM as (vm & E1). destruct MD1 as (vm' & E2). exists vm'. rewrite E2, E1. apply with_vmmaps_twice. }
  unfold MI.
  exists fx', L', A', R2, mem', md', cl, br, gn, dd, ei, G, nfd, mx, nout, cap, out, es', hj.
  replace (t + (if (TAIL_CHECK =? TAIL_CHECK) || (TAIL_CHECK =? TAIL_STEP) then 2 else 1)) with (t + 2)
    by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
  replace (t + (if (TAIL_CHECK =? TAIL_CHECK) || (TAIL_CHECK =? TAIL_STEP) then 1 else 0)) with (t + 1)
    by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
  split; [reflexivity|]. split; [exact FZ|]. split; [exact Ht|]. split; [exact Hk|]. split; [exact Hn|].
  split; [exact HRG|].
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact INIT'|]. split; [exact HVM'|].
  split; [exact RO'|]. split; [exact IK'|]. split; [exact ST'|]. split; [exact DK'|]. split; [exact GL'|].
  split; [lia|]. split; [exact OUT'|]. split; [exact REL'|].
  split; [rewrite (ents_rel_len _ _ ER); exact Hes|].
  split; [rewrite (ents_rel_cost _ _ hj ER); exact Hcost|].
  apply HRI'.
  - intros qq mm HQ. left. rewrite <- EB. exact HQ.
  - rewrite app_nil_r. reflexivity.
  - reflexivity.
  - rewrite (ents_rel_len _ _ ER). exact Hes.
  - rewrite <- HLEN. exact Hes.
  - (* No slot was free: op_add made no block. *)
    change (op0_adds 0 None) with (@nil (Z * Z)).
    apply (entry_mv_ins _ _ _ _ _ _ (rv_nc (view_of G (bv_unsigned out) es hj)) []);
      [exact (entry_blk_nd B API LS SH SK ra empty rc fx j E CS _ _ _ _ HF HMR)|
       exact (entry_blk_nd B API LS SH SK ra empty rc fx j E CS _ _ _ _ HF M1)| | | | | | | | |].
    + rewrite app_nil_r. apply Permutation_refl.
    + unfold view_of. cbn [rv_nc map]. rewrite (ents_rel_nc _ _ ER), app_nil_r. apply Permutation_refl.
    + intros x m Hx. left. rewrite <- EB. exact Hx.
    + intros x m Hx. rewrite EB. exact Hx.
    + intros u [].
    + constructor.
    + intros u [].
    + intros x m Hx. exact (entry_blk_nn rc B (API rc) _ _ _ _ x m M1 Hx).
    + intros g [].
  - exact (entry_blk_nd B API LS SH SK ra empty rc fx j E CS _ _ _ _ HF M1).
  - intros p n n' Hp _ Hin _. pose proof RM as (_ & _ & _ & LY1 & _).
    rewrite (lf_addr A L L' p n (mr_wf _ _ (aa_laws (API rc)) _ _ _ _ HMR) LY1 Hp).
    unfold view_of in Hin |- *. cbn [rv_nc] in Hin |- *. rewrite (ents_rel_nc _ _ ER). exact Hin.
  - exact (ncs_le_wt B (API rc) L' A' mem' md' (t + 1) nfd G nout cap out _ _ M1 OUT' REL'
      ltac:(rewrite (ents_rel_len _ _ ER); exact Hes)
      (entry_blk_nd B API LS SH SK ra empty rc fx j E CS _ _ _ _ HF M1)).
  - unfold nc_wt. rewrite (ents_rel_nw _ _ ER), (ents_rel_len _ _ ER). lia.
Qed.

Lemma MI_op0 : forall B API LS SH SK ra empty rc fx j E CS RI t K s c,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  (forall fx', @op_add_contract fx' rc B (API rc) pack3_form) ->
  op0_res_s RI -> 0 < K -> op_at E (K - 1) = 0 ->
  MI (rc := rc) B (API rc) E RI t K 0x13ce8
    (fun _ hj no regs => no = 0 /\ disp_src 0 s hj /\ disp_regs E t K s regs) c ->
  SR (ms_segs B) c (MI (rc := rc) B (API rc) E RI t K TAIL_CHECK (fun _ _ _ r => tail_regs E t K r)).
Proof.
  intros B API LS SH SK ra empty rc fx j E CS RI t K s c HF HOA HRES HK0 HOP HM.
  pose proof HF as (FF & HJ & HP & HCS).
  destruct HP as (PRE & RES & PACK & MIS & GI & LIVE & NI & IMG & RO & TASK & FZ0).
  destruct PRE as (PRE & LEN & DATA & SINK & FD & FS & FDC & SP47).
  destruct PRE as (HM0 & HW0 & HB0 & INIT0 & RA0 & ALIGN & SPLO & SPHI & WST & TP & WERR & RP & RN & INPUT & ROD).
  assert (SEG : ms_segs B = rsegs) by (unfold frame_facts in FF; tauto).
  assert (ETP : ms_tp B = 0x31290) by (unfold frame_facts in FF; tauto).
  assert (EOFF : ms_errno_off B = -164) by (unfold frame_facts in FF; tauto).
  assert (GLB : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
      ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4))
    by (unfold frame_facts in FF; tauto).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  destruct HM as (fx' & L & A & regs & mem & md & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
    -> & FZ & Ht & Hk & Hn & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd & HOUT & HREL &
    Hes & Hcost & HRI).
  replace (t + (if (0x13ce8 =? TAIL_CHECK) || (0x13ce8 =? TAIL_STEP) then 1 else 0)) with t in HREL
    by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
  replace (t + (if (0x13ce8 =? TAIL_CHECK) || (0x13ce8 =? TAIL_STEP) then 2 else 1)) with (t + 1) in Hnfd
    by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
  destruct HR as (_ & _ & (B2 & B3 & B4 & B20) & (F19 & F21 & F24 & F25 & F26 & F27) & R8 & R23 & R22 & _ & _).
  assert (HTR : tail_regs E t K regs) by exact (conj (conj B2 (conj B3 (conj B4 B20)))
    (conj (conj F19 (conj F21 (conj F24 (conj F25 (conj F26 F27))))) (conj R8 (conj R23 R22)))).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & _).
  pose proof HREL as ((tail & TL & TAB) & GIN & GFR & HES & HNDF & HFD & PA & HNDS & ZH & NDT).
  pose proof HGL as (GL1 & GL2 & GL3 & GL4 & GL5 & GL6 & GL7 & GL8 & GL9 & GL10 & GL11 & GL12 & GL13 & GLE & GLR).
  set (os := map (open_flag hj) (seq 0 4)).
  set (N := Z.of_nat (length es)).
  assert (HLEN : length es = length hj) by exact (Forall2_length PA).
  assert (HNC : first_zero os <> None -> 0 <= N < 4).
  { destruct (first_zero os) as [i|] eqn:FZO; [intros _|intros X; exfalso; exact (X eq_refl)].
    destruct (p0_fz_some os i FZO) as (HI & HZ). assert (LOS : length os = 4%nat) by reflexivity. rewrite LOS in HI.
    unfold os in HZ. rewrite (p0_os_nth hj i HI) in HZ. unfold open_flag in HZ.
    destruct (slot_open hj i) eqn:HO; [discriminate|].
    pose proof (p0_open_count hj i (proj1 (NoDup_ListNoDup _) HNDS) (p0_hj_lt _ _ _ _ _ _ _ _ PA) HI HO) as HC.
    unfold N. rewrite HLEN. lia. }
  destruct (HRES E K L A (first_zero os) (FIRST_FD + nfd) N G (bv_unsigned out) es hj HRI ltac:(lia) HOP HNC)
    as (bnd & ROK & ROOM & RIK).
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply p0_jal. }
  intros ms1 (can1 & -> & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  destruct (p0_regs_jal regs R1 X1) as (R1ra0 & R1r).
  assert (R1ra : YK11.getr R1 1 = Z_to_bv 64 0x13cec) by exact R1ra0.
  rewrite <- SEG.
  assert (G2 : YK11.getr R1 2 = Z_to_bv 64 (slot_sp E)) by exact (eq_trans (R1r 2 ltac:(lia)) B2).
  assert (SP1 : spZ R1 = slot_sp E).
  { unfold spZ. rewrite G2. apply unsigned_lit. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  assert (CPK : call_pre_k (rc := rc) B (aa_MR (API rc)) OP_ADD_K L A R1 mem md).
  { unfold call_pre_k. split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|].
    split; [rewrite R1ra; apply ret_ok_even; vm_compute; reflexivity|].
    rewrite SP1. split; [unfold slot_sp, SLOT_FRAME; Z.div_mod_to_equations; lia|].
    split; [change OP_ADD_K with 8352; unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|].
    split; [unfold slot_sp, SLOT_FRAME; lia|].
    split.
    { intros a Ha. apply (proj2 (proj2 (proj2 HIK))). unfold lib_scratch. left.
      change OP_ADD_K with 8352 in Ha. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
    split; [exact (eq_trans (R1r 4 ltac:(lia)) (eq_trans B4 TP))|].
    split; [intros a Ha; apply (proj2 (proj2 (proj2 HIK))); unfold lib_scratch; right; exact Ha|].
    rewrite HINIT. discriminate. }
  assert (WAKEB : bytes_at (ms_segs B) mem G_WAKE1 (le4 (Z_to_bv 64 (-1)))).
  { pose proof (proj2 (hg_cut _ mem G_WAKE0 [C4 (Z_to_bv 64 (-1))] [C4 (Z_to_bv 64 (-1))] GL2)) as W1'.
    destruct W1' as [[_ HBY] _]. cbn [cells_bytes cbytes] in HBY. rewrite app_nil_r in HBY. exact HBY. }
  eapply SR_bind.
  { apply (HOA fx' L A R1 mem md bnd os nfd N 16 G (concat (map entry_bytes es)) tail).
    - exact SEG.
    - exact CPK.
    - exact HINIT.
    - exact HRO.
    - intros a Ha. exact (proj1 (entry_errno_image B SEG ETP EOFF a Ha)).
    - intros a Ha. apply GLB. apply in_G_bss. unfold G_S, SRC_SIZE, SOURCES_MAX, G_RELAY_LO in *. lia.
    - intros a Ha. apply GLB. exists 0x20d38, 16. split; [left; reflexivity|unfold G_WAKE1 in *; lia].
    - reflexivity.
    - intros i Hi. unfold os. rewrite (p0_os_nth hj i Hi). split; [unfold open_flag; destruct (slot_open hj i); lia|].
      exact (p0_flag_cells _ _ _ _ _ _ _ _ _ _ _ i HREL Hi).
    - intros i Hi. unfold os. rewrite (p0_os_nth hj i Hi). unfold open_flag.
      destruct (slot_open hj i) eqn:HO; [discriminate|]. intros _. exact (ZH i Hi HO).
    - exact GL9.
    - unfold OPS_MAX in Ht. lia.
    - exact GL12.
    - exact WAKEB.
    - exact GL8.
    - exact GL10.
    - right. split; [reflexivity|]. split; [exact GIN|]. split; [exact GFR|].
      split; [exact (p0_ents_len _ _ _ _ _ _ HES)|]. split; [unfold N, SRC_TABLE, SRC_ENTRY; lia|]. exact TAB.
    - exact ROK.
    - exact HNC.
    - exact ROOM. }
  intros c' (L' & A' & regs' & mem' & md' & -> & INIT' & RO' & PNONE & PSOME).
  rewrite R1ra0.
  destruct (first_zero os) as [i|] eqn:FZO.
  - destruct (PSOME i eq_refl) as (q & G' & pj & rest & RP' & (qs & QLEN & ROK' & LQ & LG) & HA0 & SRC0 & NFD1 &
      LOCK1 & WAKE1' & NSRC1 & GSRC1 & GBL' & GF' & RL & GTAB & QB & QF & QNEW & CASES').
    destruct CASES' as [(C0 & _)|(_ & HGG & _ & EBS)]; [discriminate C0|]. subst G'.
    destruct (rp_split B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ RP') as [RM RPR].
    rewrite SP1 in RM.
    destruct (p0_fz_some os i FZO) as (HI4 & HZ). assert (LOS : length os = 4%nat) by reflexivity.
    rewrite LOS in HI4.
    assert (HOi : slot_open hj i = false).
    { unfold os in HZ. rewrite (p0_os_nth hj i HI4) in HZ. unfold open_flag in HZ.
      destruct (slot_open hj i); [discriminate|reflexivity]. }
    destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ (proj1 RM)) as (Hh' & Hl' & _).
    rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh'|exact Hl'|].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply p0_j. }
    intros ms2 (can2 & -> & EQ2).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
    apply SR_ret. rewrite <- SEG. try rewrite FZO in RIK.
    exact (p0_post_some B API LS SH SK ra empty rc fx j E CS RI t K fx' L A mem md cl br gn dd ei G nfd mx nout cap out
      es hj L' A' mem' md' R2 i q pj rest HF FZ Ht Hk Hn
      (p0_tail_keep E t K regs R1 regs' R2 HTR R1r RPR (p0_regs_same regs' R2 X2))
      HMR HVM HIK HST HDK HGL Hnfd HOUT HREL Hcost HI4 HOi RM INIT' RO'
      (RIK L' A' qs QLEN ROK' q (fun _ => conj LQ LG)) SRC0 NFD1 LOCK1 NSRC1 GSRC1
      GBL' RL GTAB QF QNEW EBS).
  - destruct (PNONE eq_refl) as (RP' & EB & RF').
    destruct (rp_split B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ RP') as [RM RPR].
    rewrite SP1 in RM.
    destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ (proj1 RM)) as (Hh' & Hl' & _).
    rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh'|exact Hl'|].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply p0_j. }
    intros ms2 (can2 & -> & EQ2).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
    apply SR_ret. rewrite <- SEG. try rewrite FZO in RIK.
    exact (p0_post_none B API LS SH SK ra empty rc fx j E CS RI t K fx' L A mem md cl br gn dd ei G nfd mx nout cap out
      es hj L' A' mem' md' R2 HF FZ Ht Hk Hn
      (p0_tail_keep E t K regs R1 regs' R2 HTR R1r RPR (p0_regs_same regs' R2 X2))
      HMR HVM HIK HST HDK HGL Hnfd HOUT HREL Hes Hcost RM EB INIT' RO'
      (RIK L' A' [] eq_refl RF' 0 (fun X => match X eq_refl with end))).
Qed.

Lemma pass0_holds : check_bounded_contract ->
  (forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
     @op_add_contract fx rc B (API rc) pack3_form) ->
  forall RI, RI_mono RI -> op0_res_s RI -> pass_ok RI 0.
Proof.
  intros CB HOA RI RIM HRES B API LS SH SK ra empty rc fx j E CS HF t k c HL Ht Hk Hop. cbv beta in Hop.
  assert (K0 : 0 <= k).
  { destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hk0 & _).
    lia. }
  eapply SR_bind; [exact (LI_dispatch B API LS SH SK ra empty rc fx j E CS RI t k c HF RIM HL Ht Hk)|].
  intros c' [(s & HM)|(k'' & HL')]; [|apply SR_ret; exists k''; exact HL'].
  rewrite Hop in HM. change (jt_target 0) with 0x13ce8 in HM. change (disp_k E 0 k) with (k + 1) in HM.
  eapply SR_bind.
  { exact (MI_op0 B API LS SH SK ra empty rc fx j E CS RI t (k + 1) s c' HF
      (fun fx' => HOA B API LS SH SK ra empty rc fx' (proj1 HF)) HRES ltac:(lia)
      ltac:(replace (k + 1 - 1) with k by lia; exact Hop) HM). }
  intros c2 H2.
  eapply SR_mono; [exact (MI_tail B API LS SH SK ra empty rc fx j E CS RI t (k + 1) _ c2 HF CB (fun _ _ _ _ X => X)
    (walk_op0 E t k (LI_walk _ _ _ _ _ _ _ _ HL) (frame_len B API LS SH SK ra empty rc fx j E CS HF) Hk Hop) H2)|].
  intros c3 H3. exists (k + 1). exact H3.
Qed.
