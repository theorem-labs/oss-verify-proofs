(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 613 of its 658 lines of code are new or changed and 1184 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/SlotPass9G.v, with its module paths changed; 3552 of its 3638 lines of code are new or changed and 572 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayRunT RelayRunF ListTr RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep HarnessRep ListRep CheckRep HarnessTr drain_b_c relay_remove_b_c source_reset_c op_add_c check_bounded_c check_no_loss_c check_no_loss_read_c check_shape_ends_c check_shape_done_c SlotInv SlotSteps SlotHead SlotHeadP SlotHeadQ SlotRes SlotReads KindB HarnessGlue SlotPass4R SlotPass4C HarnessFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import relay_remove_b_lem RelayCap relay_remove_b_aux SlotMove SlotWalk SlotHeadQD TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require relay_source_c relay_source relay_reads_c relay_reads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require AllocBound.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require SlotRI3 SlotNcWt ListFrame SlotPass2Mv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require SlotCaps3 SlotP5R3G SlotDrain3
  relay_instance_gone_b_lem.
Import ListNotations.
Local Open Scope Z_scope.

Lemma p4u_global_image : forall a, in_globals G_reply a ->
  wview rsegs (fun _ => None) (wa a) <> None /\ seg_rom rsegs (wa a) <> None.
Proof.
  intros a (lo & len & [EQ|[EQ|[]]] & HA); injection EQ as <- <-.
  - assert (C : forallb (fun i =>
        match wview rsegs (fun _ => None) (wa (0x21620 + i)), seg_rom rsegs (wa (0x21620 + i)) with
        | Some _, Some _ => true | _, _ => false end) (map Z.of_nat (seq 0 16)) = true)
      by (vm_compute; reflexivity).
    pose proof (zseq_forall _ _ C (a - 0x21620) ltac:(cbn; lia)) as H.
    change (match wview rsegs (fun _ => None) (wa (0x21620 + (a - 0x21620))),
                  seg_rom rsegs (wa (0x21620 + (a - 0x21620))) with
            | Some _, Some _ => true | _, _ => false end = true) in H.
    replace (0x21620 + (a - 0x21620)) with a in H by lia.
    destruct (wview rsegs (fun _ => None) (wa a)) as [v|] eqn:W;
      destruct (seg_rom rsegs (wa a)) as [u|] eqn:R; cbn in H; try congruence.
    split; congruence.
  - assert (C : forallb (fun i =>
        match wview rsegs (fun _ => None) (wa (0x318a0 + i)), seg_rom rsegs (wa (0x318a0 + i)) with
        | Some _, Some _ => true | _, _ => false end) (map Z.of_nat (seq 0 512)) = true)
      by (vm_compute; reflexivity).
    pose proof (zseq_forall _ _ C (a - 0x318a0) ltac:(cbn; lia)) as H.
    change (match wview rsegs (fun _ => None) (wa (0x318a0 + (a - 0x318a0))),
                  seg_rom rsegs (wa (0x318a0 + (a - 0x318a0))) with
            | Some _, Some _ => true | _, _ => false end = true) in H.
    replace (0x318a0 + (a - 0x318a0)) with a in H by lia.
    destruct (wview rsegs (fun _ => None) (wa a)) as [v|] eqn:W;
      destruct (seg_rom rsegs (wa a)) as [u|] eqn:R; cbn in H; try congruence.
    split; congruence.
Qed.

Lemma p4u_global_access : forall m a, in_globals G_reply a ->
  writable_at rsegs m a /\ exists v, mbyte rsegs m a = Some v.
Proof.
  intros m a HA. destruct (p4u_global_image a HA) as [W R].
  unfold writable_at, wview, mbyte, wa in *. destruct (m (Z_to_bv 64 a)) as [v|] eqn:M.
  - split; [discriminate|exists v; reflexivity].
  - split; [exact W|]. change (exists v, seg_rom rsegs (Z_to_bv 64 a) = Some v).
    destruct (seg_rom rsegs (Z_to_bv 64 a)) as [v|]; [exists v; reflexivity|contradiction].
Qed.

Section P4Res.
Variable F : ResFormT.
Variable RI : res_inv.

Definition p4_lines (e : rentry) (h : hsrc) : list (list Z) :=
  if re_eof e =? 0 then lines (hs_state h) (bzs (pending_stream h)) else [].

Definition p4_list_blk (L : layout) (A : astate) (l : hlist) : Prop :=
  (hl_cap l = 0 \/ In (hl_v l, 16 * hl_cap l) (blocks L A)) /\
  Forall (fun r => In (fst r, Z.of_nat (length (snd r)) + 1) (blocks L A)) (hl_recs l).

Definition p4_src_blk (L : layout) (A : astate) (h : hsrc) : Prop :=
  p4_list_blk L A (hs_pending h) /\ In (hs_partial h, 6000) (blocks L A) /\
  p4_list_blk L A (hs_expected h) /\ p4_list_blk L A (hs_held h) /\ NoDup (hs_blocks h).

Definition p4_ent_blk (L : layout) (A : astate) (e : rentry) : Prop :=
  (re_cap e = 0 \/ In (re_buf e, re_cap e) (blocks L A)) /\ (re_hp e = 0 \/ In (re_hp e, re_kh e) (blocks L A)) /\
  Forall (fun k => In (key_addr k, Z.of_nat (length (key_text k)) + 1) (blocks L A)) (re_keys e).

Definition p4_dels (out CAP q1 CAP1 : Z) (e : rentry) (h : hsrc) : list (Z * Z) :=
  out_move_dels out CAP q1 CAP1 ++ entry_dels e ++ src_dels h.

Definition p4_adds (out CAP q1 CAP1 : Z) : list (Z * Z) := out_move_adds out CAP q1 CAP1.

Definition p4_RV (E : sstart) (K : Z) (L0 : layout) (A0 : astate) (G out : Z) (es : list rentry)
    (hj : list (hsrc * nat)) (CAP OUT1 CAP1 : Z) (e : rentry) (h : hsrc) (L4 : layout) (A4 : astate) : Prop :=
  forall G' out' es' hj',
    (forall x m, In (x, m) (blocks L4 A4) -> In (x, m) (blocks L0 A0) \/ In x (target_addrs G' out' es' hj')) ->
    Permutation (pend_view hj) (map snd (hl_recs (hs_pending h)) :: pend_view hj') ->
    Permutation (ek_view hj) (ekeys_hl (hs_expected h) ++ ek_view hj') ->
    (length es' <= 4)%nat -> (length hj' <= 4)%nat ->
    nc_move (view_of G out es hj) L0 A0 (view_of G' out' es' hj') L4 A4 (p4_dels out CAP OUT1 CAP1 e h)
      (p4_adds out CAP OUT1 CAP1) ->
    List.NoDup (map fst (blocks L4 A4)) ->
    (forall p n n', In (p, n) (user_blocks A0) -> In (p, n') (user_blocks A4) ->
       In (ptr_addr L0 p) (rv_nc (view_of G out es hj)) ->
       ~ In (ptr_addr L0 p) (map fst (p4_dels out CAP OUT1 CAP1 e h)) ->
       In (ptr_addr L4 p) (rv_nc (view_of G' out' es' hj'))) ->
    SlotRI3.ncs (view_of G' out' es' hj') L4 A4 <= nc_wt es' hj' -> nc_wt es' hj' <= nc_wt es hj ->
    RI E K (view_of G' out' es' hj') L4 A4.

Definition p4_lv4 (E : sstart) (K : Z) (L0 : layout) (A0 : astate) (G out : Z) (es : list rentry)
    (hj : list (hsrc * nat)) (CAP OUT1 CAP1 : Z) (e : rentry) (h : hsrc)
    (L3 : layout) (A3 : astate) (h3 : hsrc) (L4 : layout) (A4 : astate) (qs : list sptr) : Prop :=
  (forall x m, In (x, m) (blocks L4 A4) -> In (x, m) (blocks L3 A3) /\ ~ In x (hs_blocks h3)) ->
  (forall x m, In (x, m) (blocks L3 A3) -> ~ In x (hs_blocks h3) -> In (x, m) (blocks L4 A4)) ->
  (forall p n n', In (p, n) (user_blocks A3) -> In (p, n') (user_blocks A4) -> ptr_addr L4 p = ptr_addr L3 p) ->
  p4_RV E K L0 A0 G out es hj CAP OUT1 CAP1 e h L4 A4.

Definition p4_lv3 (E : sstart) (K : Z) (L0 : layout) (A0 : astate) (G out : Z) (es : list rentry)
    (hj : list (hsrc * nat)) (CAP OUT1 CAP1 : Z) (e : rentry) (h : hsrc)
    (L2 : layout) (A2 : astate) (h2 : hsrc) (L3 : layout) (A3 : astate) (qs : list sptr) : Prop :=
  forall (H'' : hlist) (ds : list (Z * list byte)),
    hl_v H'' = hl_v (hs_held h2) -> hl_cap H'' = hl_cap (hs_held h2) ->
    Permutation (hl_recs (hs_held h2)) (hl_recs H'' ++ ds) ->
    (forall x m, In (x, m) (blocks L3 A3) -> In (x, m) (blocks L2 A2) /\ ~ In x (map fst ds)) ->
    (forall x m, In (x, m) (blocks L2 A2) -> ~ In x (hs_blocks h2) -> In (x, m) (blocks L3 A3)) ->
    p4_src_blk L3 A3 (set_held h2 H'') ->
    (forall p n n', In (p, n) (user_blocks A2) -> In (p, n') (user_blocks A3) -> ptr_addr L3 p = ptr_addr L2 p) ->
    List.NoDup (map fst (blocks L3 A3)) ->
    res_tr F (p4_lv4 E K L0 A0 G out es hj CAP OUT1 CAP1 e h L3 A3 (set_held h2 H'')) A3
      (source_reset_tr (known_at L3 A3) (set_held h2 H'')).

Definition p4_lv2 (E : sstart) (K : Z) (L0 : layout) (A0 : astate) (G out : Z) (es : list rentry)
    (hj : list (hsrc * nat)) (CAP OUT1 CAP1 : Z) (e : rentry) (h : hsrc)
    (L1 : layout) (A1 : astate) (h1 : hsrc) (L2 : layout) (A2 : astate) (qs : list sptr) : Prop :=
  forall (E' H' : hlist),
    sh_real L2 qs (check_no_loss_sh 0 (sh_of (known_at L1 A1) (hs_held h1))
      (map (shr (known_at L1 A1)) (hl_recs (hs_expected h1)))) H' ->
    sh_live A2 qs (check_no_loss_sh 0 (sh_of (known_at L1 A1) (hs_held h1))
      (map (shr (known_at L1 A1)) (hl_recs (hs_expected h1)))) ->
    hl_recs E' = [] -> hl_v E' = hl_v (hs_expected h1) -> hl_cap E' = hl_cap (hs_expected h1) ->
    NoDup (texts H') -> texts H' = upds (texts (hs_held h1)) (texts (hs_expected h1)) ->
    (forall x m, In (x, m) (blocks L2 A2) ->
       (In (x, m) (blocks L1 A1) /\ (0 < m -> ~ In x (map fst (hl_recs (hs_expected h1)) ++ list_blocks (hs_held h1)))) \/
       In x (list_blocks H')) ->
    (forall x m, In (x, m) (blocks L1 A1) -> 0 < m ->
       ~ In x (map fst (hl_recs (hs_expected h1)) ++ list_blocks (hs_held h1)) -> ~ In x (list_blocks H')) ->
    (forall x m, In (x, m) (blocks L1 A1) -> ~ In x (hs_blocks h1) -> In (x, m) (blocks L2 A2)) ->
    p4_src_blk L2 A2 (set_exp_held h1 E' H') ->
    (forall p n n', In (p, n) (user_blocks A1) -> In (p, n') (user_blocks A2) -> ptr_addr L2 p = ptr_addr L1 p) ->
    List.NoDup (map fst (blocks L2 A2)) ->
    forall (gone : Z) (d : list byte), gone = 0 \/ gone = 1 ->
      res_tr F (p4_lv3 E K L0 A0 G out es hj CAP OUT1 CAP1 e h L2 A2 (set_exp_held h1 E' H')) A2
        (check_shape_ends_tr (known_at L2 A2) gone [] (hl_recs H') d).

Definition p4_lv1 (E : sstart) (K : Z) (L0 : layout) (A0 : astate) (G out : Z) (es : list rentry)
    (hj : list (hsrc * nat)) (lv : bool) (MX CAP CAP1 : Z) (e : rentry) (h : hsrc) (L1 : layout) (A1 : astate)
    (qs : list sptr) : Prop :=
  forall (OUT' CAP' : Z) (olv : bool) (h1 : hsrc),
    (olv = true -> live_at L1 A1 (resolveF qs (remove_entry_out lv MX 0 CAP e h 0
       (drain_start (known_at L0 A0) (known_at L0 A0 out) e h))) OUT' CAP1) ->
    (olv = false -> OUT' = out /\ CAP1 = CAP) ->
    (re_eof e = 0 -> src_links L1 A1 qs (known_at L0 A0)
       (after_drain_adr lv MX 0 CAP e h 0 (drain_start (known_at L0 A0) (known_at L0 A0 out) e h)) h1) ->
    (forall x m, In (x, m) (blocks L1 A1) ->
       (In (x, m) (blocks L0 A0) /\ x <> out /\ ~ In x (entry_blocks e) /\ (re_eof e = 0 -> ~ In x (hs_blocks h))) \/
       (re_eof e = 0 /\ In x (hs_blocks h1)) \/ x = OUT') ->
    (forall x m, In (x, m) (blocks L0 A0) -> x <> out -> ~ In x (entry_blocks e) ->
       (re_eof e = 0 -> ~ In x (hs_blocks h)) -> In (x, m) (blocks L1 A1)) ->
    (forall x m, In (x, m) (blocks L0 A0) -> 0 < m -> x <> out -> ~ In x (entry_blocks e) ->
       (re_eof e = 0 -> ~ In x (hs_blocks h)) -> x <> OUT' /\ (re_eof e = 0 -> ~ In x (hs_blocks h1))) ->
    (re_eof e = 0 -> NoDup (OUT' :: hs_blocks h1)) ->
    (OUT' = out /\ (0 < CAP -> In (out, CAP) (blocks L1 A1))) \/ In (OUT', CAP') (blocks L1 A1) ->
    (re_eof e <> 0 -> h1 = h) ->
    (re_eof e = 0 -> hl_recs (hs_pending h1) = []) ->
    hs_held h1 = hs_held h ->
    map snd (hl_recs (hs_expected h1)) = map (map (Z_to_bv 8)) (p4_lines e h) ->
    p4_src_blk L1 A1 h1 ->
    (forall p n n', In (p, n) (user_blocks A0) -> In (p, n') (user_blocks A1) -> ptr_addr L1 p = ptr_addr L0 p) ->
    List.NoDup (map fst (blocks L1 A1)) ->
    hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1))) < 2 ^ 22 ->
    (re_eof e = 0 -> hl_cap (hs_expected h1) = ds_ecap (drain_fin lv MX 0 CAP e h)) ->
    (re_eof e = 0 -> hl_v (hs_pending h1) = hl_v (hs_pending h) /\ hl_cap (hs_pending h1) = hl_cap (hs_pending h) /\
       hs_partial h1 = hs_partial h) ->
    res_tr F (p4_lv2 E K L0 A0 G out es hj CAP OUT' CAP1 e h L1 A1 h1) A1
      (check_no_loss_tr 0 (sh_of (known_at L1 A1) (hs_held h1)) (map (shr (known_at L1 A1)) (hl_recs (hs_expected h1)))).

Definition p4_res : Prop :=
  forall E K L A G out es hj q e h i (lv : bool) (MX CAP : Z),
    RI E K (view_of G out es hj) L A -> List.NoDup (map fst (blocks L A)) -> WF A -> slot_cost es hj <= K ->
    NoDup (target_addrs G out es hj) ->
    nth_error es q = Some e -> nth_error hj q = Some (h, i) ->
    p4_ent_blk L A e -> p4_src_blk L A h -> (CAP = 0 \/ In (out, CAP) (blocks L A)) ->
    0 <= MX <= 255 -> 0 <= CAP <= TBBYTES ->
    0 <= re_fd e -> find (fun x => re_fd x =? re_fd e) es = Some e ->
    (re_eof e = 0 -> SlotP5R3G.drain3 e h) ->
    remove_entry_cap lv MX 0 CAP e h <= SlotCaps3.NMAX ->
    (re_hp e <> 0 -> re_kh e <> 0) -> (CAP = 0 -> forall m, ~ In (out, m) (blocks L A)) ->
    (length es <= 4)%nat -> (length hj <= 4)%nat ->
    res_tr F (p4_lv1 E K L A G out es hj lv MX CAP (remove_entry_cap lv MX 0 CAP e h) e h) A
      (relay_remove_tr lv MX 0 CAP (re_fd e) es h (known_at L A) 0 (known_at L A out)).

End P4Res.

Definition p4_ks (G : list (list Z)) : Z :=
  fold_right (fun xl acc => xl + 5 + acc) 0 (map (fun x => Z.of_nat (length x)) G).

Lemma p4_ks_app : forall G1 G2, p4_ks (G1 ++ G2) = p4_ks G1 + p4_ks G2.
Proof. intros G1 G2. unfold p4_ks. induction G1 as [|x G1 IH]; cbn [app map fold_right]; lia. Qed.

Lemma p4_ks_perm : forall G G', Permutation G G' -> p4_ks G = p4_ks G'.
Proof.
  intros G G' P. induction P as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; unfold p4_ks in *;
    cbn [map fold_right] in *; lia.
Qed.

Lemma p4_gesture_begin : forall l x, gesture l = Some (GBegin, x) -> (length x + 6 = length l)%nat.
Proof.
  intros l x H. unfold gesture in H.
  destruct (list_eqb (firstn 13 l) K_GESTURE && Z.eqb (nth 13 l 0) SPACE && Nat.ltb 13 (length l)); [|discriminate].
  destruct (last_space_from 0 l) as [j|] eqn:E; [|discriminate].
  destruct (Nat.ltb 13 j) eqn:J; [|discriminate].
  pose proof (last_space_lt l 0 j E) as LT.
  destruct (list_eqb (skipn (S j) l) W_BEGIN) eqn:W.
  - injection H as <-. unfold list_eqb in W.
    destruct (list_eq_dec Z.eq_dec (skipn (S j) l) W_BEGIN) as [Ew|]; [|discriminate].
    pose proof (f_equal (@length Z) Ew) as Lw. rewrite length_skipn in Lw. cbn in Lw.
    rewrite length_firstn. lia.
  - destruct (list_eqb (skipn (S j) l) W_END); discriminate.
Qed.

Lemma p4_ks_seen : forall H l, p4_ks (seen_arr H l) <= p4_ks H + Z.of_nat (length l) + 1.
Proof.
  intros H l. unfold seen_arr. destruct (gesture l) as [[[|] x]|] eqn:EG.
  - pose proof (p4_gesture_begin l x EG) as LX. destruct (index_of x H); [lia|].
    rewrite p4_ks_app. change (p4_ks [x]) with (Z.of_nat (length x) + 5 + 0). lia.
  - destruct (index_of x H) as [n|] eqn:EI; [|lia].
    destruct (index_of_some x H n EI) as (a & b & -> & <-).
    pose proof (p4_ks_perm _ _ (swap_remove_perm [] a x b)) as P.
    change (p4_ks (x :: swap_remove [] (length a) (a ++ x :: b))) with
      (Z.of_nat (length x) + 5 + p4_ks (swap_remove [] (length a) (a ++ x :: b))) in P. lia.
  - lia.
Qed.

Lemma p4_ks_lines : forall rl live mx no cap H ka j o ha ks,
  p4_ks (snd (fst (snd (fst (lines_run live mx no cap H ka rl j o ha ks))))) <=
  p4_ks H + Z.of_nat (length (with_nul rl)).
Proof.
  induction rl as [|l r IH]; intros live mx no cap H ka j o ha ks; [cbn [lines_run fst snd]; cbn; lia|].
  cbn [lines_run]. cbv zeta. cbn [fst snd].
  match goal with |- context [lines_run live mx ?no1 ?cap1 (seen_arr H l) ?ka1 r ?j1 ?o1 ?ha1 ?ks1] =>
    pose proof (IH live mx no1 cap1 (seen_arr H l) ka1 j1 o1 ha1 ks1) as X end.
  pose proof (p4_ks_seen H l) as Y. rewrite with_nul_cons_len. lia.
Qed.

Lemma p4_ks_drain : forall f live mx s j a, relay_instance_gone_b_lem.dr_inv s ->
  p4_ks (ds_H (fst (snd (drain_run f live mx s j a)))) <=
  p4_ks (ds_H s) + Z.of_nat (length (with_nul (lines (ds_ref s) (relay_instance_gone_b_lem.dr_rest s)))).
Proof.
  induction f as [|f IH]; intros live mx [c u sk H ka ei pd off rf en ec no oc] j a INV;
    [cbn [drain_run fst snd ds_H]; lia|].
  unfold relay_instance_gone_b_lem.dr_inv in INV. unfold relay_instance_gone_b_lem.dr_rest.
  cbn [ds_u ds_skip ds_ref ds_cap ds_pend ds_off ds_eintr ds_no ds_H] in INV |- *.
  destruct INV as (J & HC & HP).
  pose proof J as (Jk & Jw & Jl & Jz).
  pose proof (relay_instance_gone_b_lem.rig_ll_z _ Jl) as UL'.
  assert (UL'' : 0 <= Z.of_nat (length u) <= 6000) by (clear - UL'; lia).
  pose proof (relay_instance_gone_b_lem.rig_grow c (Z.of_nat (length u)) j (da_buf a) HC UL'') as [G1 G2].
  cbn [drain_run ds_cap ds_u ds_skip ds_H ds_ka ds_eintr ds_pend ds_off ds_ref ds_en ds_ecap ds_no ds_ocap].
  set (cp := fst (snd (grow_tr c (Z.of_nat (length u)) j (da_buf a)))) in *.
  destruct ei.
  - assert (IV : relay_instance_gone_b_lem.dr_inv (DS cp u sk H ka false pd off rf en ec no oc)).
    { unfold relay_instance_gone_b_lem.dr_inv. cbn [ds_u ds_skip ds_ref ds_cap ds_pend ds_off].
      split; [exact J|]. split; [lia | exact HP]. }
    cbn [fst snd].
    match goal with |- context [drain_run f live mx (DS cp u sk H ka false pd off rf en ec no oc) ?jj ?aa] =>
      pose proof (IH live mx _ jj aa IV) as E1 end.
    unfold relay_instance_gone_b_lem.dr_rest in E1. cbn [ds_pend ds_off ds_ref ds_H] in E1. lia.
  - destruct pd as [|r0 rs]; [cbn [fst snd ds_H]; lia|].
    destruct HP as [HO HF].
    match goal with |- context [Z.min ?a ?b <=? 0] => remember (Z.min a b) as nn eqn:Enn end.
    destruct (Z.leb_spec nn 0) as [X|X]; [cbn [fst snd ds_H]; lia|].
    assert (NL : nn <= Z.of_nat (length r0) - off) by (rewrite Enn; lia).
    set (d := firstn (Z.to_nat nn) (skipn (Z.to_nat off) r0)) in *.
    pose proof (chunk_ok u sk rf d J) as CK.
    destruct (chunk u sk d) as [[u' sk'] rl] eqn:ECH.
    destruct CK as [Erl J'].
    set (PEND := if off + nn =? Z.of_nat (length r0) then rs else r0 :: rs) in *.
    set (OFF := if off + nn =? Z.of_nat (length r0) then 0 else off + nn) in *.
    assert (RS : relay_instance_gone_b_lem.dr_rest_of (r0 :: rs) off =
                 d ++ relay_instance_gone_b_lem.dr_rest_of PEND OFF /\
                 relay_instance_gone_b_lem.dr_pend_ok PEND OFF).
    { unfold PEND, OFF, d. cbn [relay_instance_gone_b_lem.dr_rest_of].
      destruct (Z.eqb_spec (off + nn) (Z.of_nat (length r0))) as [W|W].
      - split.
        + rewrite firstn_all2 by (rewrite length_skipn; lia). f_equal.
          destruct rs as [|r1 rs1]; reflexivity.
        + destruct rs as [|r1 rs1]; [exact I|]. inversion HF as [|? ? HF1 HF2]; subst.
          cbn [relay_instance_gone_b_lem.dr_pend_ok]. split; [lia | exact HF2].
      - split.
        + cbn [relay_instance_gone_b_lem.dr_rest_of].
          replace (Z.to_nat (off + nn)) with (Z.to_nat nn + Z.to_nat off)%nat by lia.
          rewrite <- skipn_skipn, app_assoc, firstn_skipn. reflexivity.
        + cbn [relay_instance_gone_b_lem.dr_pend_ok]. split; [lia | exact HF]. }
    assert (IVG : forall H' ka' en' ec' no' oc',
               relay_instance_gone_b_lem.dr_inv (DS cp u' sk' H' ka' false PEND OFF (feed rf d) en' ec' no' oc')).
    { intros. unfold relay_instance_gone_b_lem.dr_inv. cbn [ds_u ds_skip ds_ref ds_cap ds_pend ds_off].
      split; [exact J'|]. split; [lia | exact (proj2 RS)]. }
    match goal with |- context [lines_run live mx no oc H ka rl ?j3 ?o3 ?h3 ?k3] =>
      pose proof (p4_ks_lines rl live mx no oc H ka j3 o3 h3 k3) as LK;
      destruct (lines_run live mx no oc H ka rl j3 o3 h3 k3) as [[t1 [[oc1 H1] ka1]] [[o1 ha1] ks1]] end.
    cbn [fst snd] in LK |- *.
    match goal with |- context [drain_run f live mx (DS _ _ _ _ _ _ _ _ _ ?en' ?ec' ?no' _) ?jj ?aa] =>
      pose proof (IH live mx _ jj aa (IVG H1 ka1 en' ec' no' oc1)) as E1 end.
    unfold relay_instance_gone_b_lem.dr_rest in E1. cbn [ds_pend ds_off ds_ref ds_H] in E1.
    rewrite Erl in LK. rewrite (proj1 RS), lines_app, relay_instance_gone_b_lem.rig_wn_app. lia.
Qed.

Lemma p4_cap_nmax : forall lv mx CAP e h,
  0 <= CAP <= TBBYTES ->
  (re_eof e = 0 -> relay_instance_gone_b_lem.dr_inv (drain_init 0 CAP e h) /\
     relay_instance_gone_b_lem.dr_rest (drain_init 0 CAP e h) = bzs (pending_stream h)) ->
  2 * (Z.of_nat (length (with_nul (if re_eof e =? 0 then lines (hs_state h) (bzs (pending_stream h)) else []))) +
    keys_total (re_keys e)) < 2 ^ 28 ->
  remove_entry_cap lv mx 0 CAP e h <= SlotCaps3.NMAX.
Proof.
  intros lv mx CAP e h HC HD HB.
  pose proof (remove_entry_cap_le_no lv mx 0 CAP e h) as R.
  change (fold_right (fun xl acc => xl + 5 + acc) 0
    (map (fun x => Z.of_nat (length x)) (ds_H (after_drain lv mx 0 CAP e h))))
    with (p4_ks (ds_H (after_drain lv mx 0 CAP e h))) in R.
  assert (KS : forall ks, p4_ks (keys_texts ks) = keys_total ks)
    by (intros ks; unfold p4_ks; rewrite keys_total_texts; reflexivity).
  assert (W : ds_no (after_drain lv mx 0 CAP e h) + p4_ks (ds_H (after_drain lv mx 0 CAP e h)) <=
      2 * Z.of_nat (length (with_nul (if re_eof e =? 0 then lines (hs_state h) (bzs (pending_stream h)) else []))) +
      keys_total (re_keys e)).
  { destruct (Z.eq_dec (re_eof e) 0) as [E0|E0].
    - rewrite (after_drain_fin lv mx 0 CAP e h E0), (rc_if_t _ _ _ E0).
      destruct (HD E0) as (DI & DR).
      destruct (relay_instance_gone_b_lem.rig_drain_model lv mx 0 CAP e h DI DR) as (N & _).
      pose proof (p4_ks_drain (S (S (length (pending_stream h)))) lv mx (drain_init 0 CAP e h) 0%nat dadr0 DI) as P.
      rewrite DR in P.
      change (ds_H (drain_init 0 CAP e h)) with (keys_texts (re_keys e)) in P.
      change (ds_ref (drain_init 0 CAP e h)) with (hs_state h) in P. rewrite KS in P.
      unfold drain_fin, drain_go in N |- *. lia.
    - rewrite (after_drain_init lv mx 0 CAP e h E0), (rc_if_f _ _ _ E0).
      change (ds_no (drain_init 0 CAP e h)) with 0. change (ds_H (drain_init 0 CAP e h)) with (keys_texts (re_keys e)).
      rewrite KS, with_nul_nil_len. lia. }
  pose proof (keys_total_nonneg (re_keys e)) as KN.
  pose proof (Zle_0_nat (length (with_nul (if re_eof e =? 0 then lines (hs_state h) (bzs (pending_stream h)) else []))))
    as WN.
  unfold SlotCaps3.NMAX, TBBYTES in *. lia.
Qed.

Lemma p4_sum_app : forall {X} (f : X -> Z) a b,
  fold_right Z.add 0 (map f (a ++ b)) = fold_right Z.add 0 (map f a) + fold_right Z.add 0 (map f b).
Proof. intros X f a b. induction a as [|x a IH]; cbn [app map fold_right]; lia. Qed.

Lemma p4_sum_remove : forall (f : list Z -> Z) (m : list (list Z)) a, (forall y, 0 <= f y) -> In a m ->
  f a + fold_right Z.add 0 (map f (remove (list_eq_dec Z.eq_dec) a m)) <= fold_right Z.add 0 (map f m).
Proof.
  intros f m a Hf. induction m as [|b m IH]; intros Ha; [destruct Ha|].
  cbn [remove]. destruct (list_eq_dec Z.eq_dec a b) as [<-|NE].
  - cbn [map fold_right]. destruct (in_dec (list_eq_dec Z.eq_dec) a m) as [Hm|Hm].
    + specialize (IH Hm). pose proof (Hf a). lia.
    + rewrite notin_remove by exact Hm. lia.
  - destruct Ha as [->|Ha]; [congruence|]. cbn [map fold_right]. specialize (IH Ha). pose proof (Hf b). lia.
Qed.

Lemma p4_sum_incl : forall (f : list Z -> Z) (l m : list (list Z)), (forall y, 0 <= f y) ->
  List.NoDup l -> incl l m -> fold_right Z.add 0 (map f l) <= fold_right Z.add 0 (map f m).
Proof.
  intros f l. induction l as [|a l IH]; intros m Hf ND HI.
  - cbn [map fold_right]. apply sum_nonneg. apply Forall_forall. intros y _. apply Hf.
  - apply List.NoDup_cons_iff in ND as [NI ND].
    assert (Ha : In a m) by (apply HI; left; reflexivity).
    assert (HI' : incl l (remove (list_eq_dec Z.eq_dec) a m)).
    { intros y Hy. apply in_in_remove; [intros ->; exact (NI Hy)|apply HI; right; exact Hy]. }
    specialize (IH _ Hf ND HI'). pose proof (p4_sum_remove f m a Hf Ha). cbn [map fold_right]. lia.
Qed.

Definition p4_gk (l : list Z) : list (list Z) :=
  match gesture l with Some (GBegin, x) => [x] | _ => [] end.

Fixpoint p4_gks (Ls : list (list Z)) : list (list Z) :=
  match Ls with [] => [] | l :: Ls' => p4_gk l ++ p4_gks Ls' end.

Lemma p4_upd_incl : forall G l, incl (upd G l) (G ++ p4_gk l).
Proof.
  intros G l y Hy. unfold upd, p4_gk in *. destruct (gesture l) as [[k x]|]; [destruct k|].
  - destruct (existsb (list_eqb x) G); [apply in_or_app; left; exact Hy|exact Hy].
  - apply filter_In in Hy. rewrite app_nil_r. exact (proj1 Hy).
  - rewrite app_nil_r. exact Hy.
Qed.

Lemma p4_upds_incl : forall Ls G, incl (upds G Ls) (G ++ p4_gks Ls).
Proof.
  unfold upds. induction Ls as [|l Ls IH]; intros G y Hy; cbn [fold_left p4_gks] in *.
  - rewrite app_nil_r. exact Hy.
  - apply IH in Hy. apply in_app_or in Hy as [Hy|Hy].
    + apply p4_upd_incl in Hy. apply in_app_or in Hy as [Hy|Hy]; apply in_or_app;
        [left; exact Hy|right; apply in_or_app; left; exact Hy].
    + apply in_or_app. right. apply in_or_app. right. exact Hy.
Qed.

Lemma p4_gk_len : forall l x, In x (p4_gk l) -> (length x + 6 = length l)%nat.
Proof.
  intros l x H. unfold p4_gk, gesture in H.
  destruct (list_eqb (firstn 13 l) K_GESTURE && Z.eqb (nth 13 l 0) SPACE && Nat.ltb 13 (length l));
    [|cbn in H; destruct H].
  destruct (last_space_from 0 l) as [j|] eqn:EJ; [|cbn in H; destruct H].
  destruct (Nat.ltb 13 j); [|cbn in H; destruct H].
  destruct (list_eqb (skipn (S j) l) W_BEGIN) eqn:W.
  - cbn in H. destruct H as [<-|[]]. unfold list_eqb in W.
    destruct (list_eq_dec Z.eq_dec (skipn (S j) l) W_BEGIN) as [Ew|]; [|discriminate].
    pose proof (f_equal (@length Z) Ew) as Lw. rewrite length_skipn in Lw. cbn in Lw.
    pose proof (last_space_lt l 0 j EJ). rewrite length_firstn. lia.
  - destruct (list_eqb (skipn (S j) l) W_END); cbn in H; destruct H.
Qed.

Lemma p4_gks_sum : forall Ls,
  fold_right Z.add 0 (map (fun y => Z.of_nat (length y) + 5) (p4_gks Ls)) <= Z.of_nat (length (with_nul Ls)).
Proof.
  induction Ls as [|l Ls IH]; [cbn; lia|]. cbn [p4_gks]. rewrite p4_sum_app.
  assert (H1 : fold_right Z.add 0 (map (fun y => Z.of_nat (length y) + 5) (p4_gk l)) <= Z.of_nat (length l) + 1).
  { destruct (p4_gk l) as [|x [|x' r]] eqn:EG; cbn [map fold_right]; [lia| |].
    - pose proof (p4_gk_len l x ltac:(rewrite EG; left; reflexivity)). lia.
    - exfalso. unfold p4_gk in EG. destruct (gesture l) as [[k y]|]; [destruct k|]; discriminate. }
  unfold with_nul in *. cbn [map concat]. rewrite length_app, length_app. cbn [length]. lia.
Qed.

Lemma p4_keys_total_texts : forall ks,
  keys_total ks = fold_right Z.add 0 (map (fun y => Z.of_nat (length y) + 5) (keys_texts ks)).
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  change (keys_total (k :: ks)) with (Z.of_nat (length (key_text k)) + 5 + keys_total ks).
  change (keys_texts (k :: ks)) with (bzs (key_text k) :: keys_texts ks).
  cbn [map fold_right]. rewrite IH, bzs_length. reflexivity.
Qed.

Lemma p4_keys_upds : forall (ks ks' : list (Z * list byte * list byte)) Ls,
  NoDup (keys_texts ks') -> same_set (keys_texts ks') (upds (keys_texts ks) Ls) ->
  keys_total ks' <= keys_total ks + Z.of_nat (length (with_nul Ls)).
Proof.
  intros ks ks' Ls ND SS. rewrite !p4_keys_total_texts.
  assert (I : incl (keys_texts ks') (keys_texts ks ++ p4_gks Ls)).
  { intros y Hy. apply p4_upds_incl. apply (proj1 (SS y)). exact Hy. }
  assert (POS : forall y : list Z, 0 <= Z.of_nat (length y) + 5) by (intros y; lia).
  pose proof (p4_sum_incl (fun y => Z.of_nat (length y) + 5) _ _ POS
    (proj1 (NoDup_ListNoDup _) ND) I) as S.
  rewrite p4_sum_app in S. pose proof (p4_gks_sum Ls). lia.
Qed.

Lemma p4_find_lt : forall y rs i, find_text y rs = Some i -> (i < length rs)%nat.
Proof.
  intros y rs. induction rs as [|r rs' IH]; intros i; cbn [find_text]; [discriminate|].
  destruct (list_eqb (bzs (snd r)) (bzs y)); [intros EQ; injection EQ as <-; cbn [length]; lia|].
  destruct (find_text y rs') as [k|] eqn:EK; cbn [option_map]; [|discriminate].
  intros EQ. injection EQ as <-. pose proof (IH k ltac:(first [exact EK|reflexivity])). cbn [length]. lia.
Qed.

Lemma p4_ends_perm : forall P w rs d rs' ds c, ends_run P rs d w = Some (rs', ds, c) ->
  Permutation rs (rs' ++ ds).
Proof.
  intros P w. induction w as [|w IH]; intros rs d rs' ds c H; cbn [ends_run] in H.
  - injection H as <- <- _. rewrite app_nil_r. apply Permutation_refl.
  - destruct (split_nul d) as [[l d']|]; [|discriminate].
    match type of H with context [if ?b then _ else _] => destruct b end; [|discriminate].
    match type of H with context [match find_text ?y ?r with _ => _ end] =>
      destruct (find_text y r) as [i|] eqn:FT end; [|discriminate].
    match type of H with context [match ends_run ?a ?b ?c0 ?dd with _ => _ end] =>
      destruct (ends_run a b c0 dd) as [[[r1 d1] c1]|] eqn:ER end; [|discriminate].
    injection H as <- <- _.
    pose proof (p4_find_lt _ _ _ FT) as Hi.
    specialize (IH _ _ _ _ _ ER).
    eapply Permutation_trans; [|apply Permutation_middle].
    rewrite (split_at rs i (0, []) Hi) at 1. unfold drop_nth in IH.
    eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip. exact IH.
Qed.

Lemma p4_ff : forall B API LS SH SK ra empty, frame_facts B API LS SH SK ra empty ->
  ms_segs B = rsegs /\ ms_tp B = 0x31b70 /\ ms_errno_off B = -164 /\ ms_lock B = 0x51e70 /\
  ms_libc B = 0x51e00 /\ ms_got_guard B = 0x205e0 /\ ms_guard B = 0x51de0 /\ ms_debruijn B = 0x104e0 /\
  ms_size_classes B = 0x10500 /\ ms_small_cnt B = 0x10560 /\ ms_med_cnt B = 0x1057b /\
  ms_vmlock B = Some 0x52654 /\ ms_ctx B = 0x51e78 /\
  (forall rc, errno_addr B + 4 <= @YM05.alloc_ceiling rc) /\
  (forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
     ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4)) /\
  (forall rc fx, @frame_allocator rc fx B (API rc)).
Proof. intros B API LS SH SK ra empty FF. unfold frame_facts in FF. tauto. Qed.

Lemma p4_in_img : forall B lo hi, ms_segs B = rsegs ->
  existsb (fun s : word * word => (bv_unsigned (fst s) <=? lo) && (hi <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
    (segments_reserved rsegs) = true ->
  forall a, lo <= a < hi -> in_img B a.
Proof.
  intros B lo hi SEG C a Ha.
  apply existsb_exists in C as (s & HS & HB). apply andb_prop in HB as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  unfold in_img. rewrite SEG. split; [intros EQ; rewrite EQ in HS; destruct HS|].
  exists s. split; [exact HS|lia].
Qed.

Lemma p4_errno : forall B API LS SH SK ra empty, frame_facts B API LS SH SK ra empty ->
  errno_addr B = 0x31acc /\ forall a, errno_addr B <= a < errno_addr B + 4 -> in_img B a.
Proof.
  intros B API LS SH SK ra empty FF.
  destruct (p4_ff _ _ _ _ _ _ _ FF) as (SEG & TP & EO & _).
  assert (EA : errno_addr B = 0x31acc) by (unfold errno_addr; rewrite TP, EO; reflexivity).
  split; [exact EA|]. rewrite EA. apply (p4_in_img B 0x31acc 0x31ad0 SEG). vm_compute. reflexivity.
Qed.

Lemma p4_end5 : forall B API LS SH SK ra empty, frame_facts B API LS SH SK ra empty ->
  forall a, END5_ADDR <= a < END5_ADDR + 5 -> img_plain B a.
Proof.
  intros B API LS SH SK ra empty FF a Ha.
  destruct (p4_ff _ _ _ _ _ _ _ FF) as (SEG & TP & EO & LK & LC & GG & GD & DB & SC & SM & MC & VM & CX & _).
  unfold END5_ADDR in Ha. unfold img_plain. split; [|split; [|split]].
  - apply (p4_in_img B 0x10353 0x10358 SEG); [vm_compute; reflexivity|lia].
  - unfold static_owned, vml_lo, vml_len. rewrite LK, LC, GG, GD, DB, SC, SM, MC, VM. lia.
  - rewrite CX. unfold CTX_SIZE. lia.
  - unfold errno_addr. rewrite TP, EO. lia.
Qed.

Lemma p4_glob_plain : forall B API LS SH SK ra empty, frame_facts B API LS SH SK ra empty ->
  forall a, in_globals G_reply a -> img_plain B a.
Proof.
  intros B API LS SH SK ra empty FF a Ha.
  destruct (p4_ff _ _ _ _ _ _ _ FF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FG & _).
  unfold img_plain. exact (FG a Ha).
Qed.

Definition PF_ADDR : Z := 0x102e9.
Definition PF_SLACK : list byte :=
  [Z_to_bv 8 0x2e; Z_to_bv 8 0; Z_to_bv 8 0x75; Z_to_bv 8 0x73; Z_to_bv 8 0x61; Z_to_bv 8 0x67].

Lemma p4_pf_bytes : forall m, ro_agree rsegs m -> bytes_at rsegs m PF_ADDR ([] ++ Z_to_bv 8 0 :: PF_SLACK).
Proof.
  intros m Hro.
  pose proof (ro_cells_image rsegs (normalize rsegs m) PF_ADDR ([] ++ Z_to_bv 8 0 :: PF_SLACK)
    (mem_inv_normalize rsegs m) ltac:(vm_compute; reflexivity) ltac:(unfold PF_ADDR; lia)
    ltac:(unfold PF_ADDR; cbn; lia)) as RO.
  destruct RO as [_ RO]. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO.
  exact (proj2 (bytes_at_rel rsegs m (normalize rsegs m) PF_ADDR _ (mem_rel_normalize rsegs m Hro)) RO).
Qed.

Lemma p4_pf_ro : forall i, 0 <= i < 7 -> ro_addr rsegs (Z_to_bv 64 (PF_ADDR + i)) = true.
Proof.
  intros i Hi.
  assert (C : forallb (fun k => ro_addr rsegs (Z_to_bv 64 (PF_ADDR + Z.of_nat k))) (seq 0 7) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C (Z.to_nat i)).
  rewrite Z2Nat.id in C by lia. apply C. apply in_seq. lia.
Qed.

Lemma p4_cells_keep : forall segs m m' a cs, rw_cells segs m a cs ->
  (forall x, a <= x < a + Z.of_nat (cells_size cs) ->
     mbyte segs m' x = mbyte segs m x /\ (writable_at segs m x <-> writable_at segs m' x)) ->
  rw_cells segs m' a cs.
Proof.
  intros segs m m' a cs H K. apply (rw_cells_transfer segs m); [exact H|].
  intros i Hi. destruct (K (a + i) ltac:(lia)) as [X Y]. split; [exact X|tauto].
Qed.

Lemma p4_keep_post : forall B API LS SH SK ra empty rc fx j E CS K' E' F' L A regs mem md L' A' regs' mem' md',
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  relay_post (rc := rc) B (API rc) K' E' F' L A regs mem md L' A' regs' mem' md' ->
  aa_MR (API rc) L A mem md -> spZ regs = slot_sp E -> 0 <= K' <= 65344 ->
  (forall a, E' a -> in_globals G_reply a \/ (0 <= a < @YM05.alloc_ceiling rc /\ ~ in_img B a) \/
     (slot_sp E + 40 <= a < slot_sp E + 48)) ->
  (forall a, slot_sp E + 40 <= a < slot_sp E + 48 -> ~ E' a \/ writable_at (ms_segs B) mem' a) ->
  image_kept (rc := rc) B E mem -> stack_mid B E mem ->
  image_kept (rc := rc) B E mem' /\ stack_mid B E mem'.
Proof.
  intros B API LS SH SK ra empty rc fx j E CS K' E' F' L A regs mem md L' A' regs' mem' md'
    HF RP HM HSP HK HE HW (IK1 & IK2 & IK3 & IK4) (ST1 & ST2 & ST3).
  pose proof HF as (FF & _ & PRE & _).
  destruct (p4_ff _ _ _ _ _ _ _ FF) as (SEG & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ERR & _ & FA).
  assert (AX : AllocExtra B (aa_MR (API rc))) by (specialize (FA rc fx); unfold frame_allocator in FA; tauto).
  pose proof (proj1 (proj1 PRE)) as LP. destruct LP as (_ & _ & _ & _ & _ & _ & SPLO & SPHI & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof (ERR rc) as ER.
  destruct RP as (M' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FR & _ & SW).
  assert (NOH : forall L0 A0 m0 md0 a, aa_MR (API rc) L0 A0 m0 md0 -> @YM05.alloc_ceiling rc <= a ->
      ~ owned B L0 A0 a).
  { intros L0 A0 m0 md0 a H0 Ha Ho. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a H0 Ho). lia. }
  assert (GL : forall a, in_globals G_reply a -> a < 0x31aa0).
  { intros a HG0. unfold in_globals, G_reply, frame_G in HG0.
    destruct HG0 as (lo & len & [EQ|[EQ|[]]] & G1); injection EQ as <- <-; lia. }
  assert (KEEP : forall a, @YM05.alloc_ceiling rc <= a < 2 ^ 64 -> ~ (slot_sp E - K' <= a < slot_sp E) -> ~ E' a ->
      mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
      (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha N1 N2. apply FR; [left; exact Ha|apply (NOH _ _ _ _ a HM); lia|apply (NOH _ _ _ _ a M'); lia| |exact N2].
    unfold scratch_k. rewrite HSP. intros [X|X]; lia. }
  assert (NEH : forall a, ~ (slot_sp E + 40 <= a < slot_sp E + 48) -> @YM05.alloc_ceiling rc <= a -> ~ E' a).
  { intros a N1 N2 X. destruct (HE a X) as [G0|[G0|G0]]; [pose proof (GL a G0)|lia|lia].
    unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  split.
  - split; [|split; [|split]].
    + intros a HI HS HC HEr HG. destruct (IK1 a HI HS HC HEr HG) as [EA WA].
      assert (PA : img_plain B a) by (unfold img_plain; tauto).
      pose proof (in_img_low B SEG a HI) as IL.
      assert (NE : ~ E' a).
      { intros X. destruct (HE a X) as [G0|[(_ & G0)|G0]]; [exact (HG G0)|exact (G0 HI)|].
        unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
      assert (NS : ~ scratch_k B K' regs a).
      { unfold scratch_k. rewrite HSP. intros [X|X]; [unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|exact (HEr X)]. }
      destruct (FR a (or_intror HI) (hg_img_not_owned B (API rc) AX L A mem md a HM PA)
        (hg_img_not_owned B (API rc) AX L' A' mem' md' a M' PA) NS NE) as [E1 W1].
      split; [congruence|tauto].
    + intros a HG. rewrite SEG. split; intros _; exact (proj1 (p4u_global_access _ a HG)).
    + intros a HA HNS. destruct (IK3 a HA HNS) as [EA WA].
      assert (N1 : ~ (slot_sp E - K' <= a < slot_sp E)).
      { intros X. apply HNS. unfold lib_scratch. left. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
      assert (N2 : ~ (slot_sp E + 40 <= a < slot_sp E + 48)).
      { intros X. apply HNS. unfold lib_scratch. left. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
      destruct (KEEP a HA N1 (NEH a N2 ltac:(lia))) as [E1 W1]. split; [congruence|tauto].
    + intros a HS. pose proof (IK4 a HS) as WA. unfold lib_scratch in HS.
      destruct HS as [HS|HS]; [|apply SW; unfold scratch_k; right; exact HS].
      destruct (Z_lt_le_dec a (slot_sp E)) as [L1|L1].
      * destruct (Z_le_gt_dec (slot_sp E - K') a) as [L2|L2]; [apply SW; unfold scratch_k; left; rewrite HSP; lia|].
        assert (N2 : ~ (slot_sp E + 40 <= a < slot_sp E + 48)) by lia.
        destruct (KEEP a ltac:(unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia) ltac:(lia)
          (NEH a N2 ltac:(unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia))) as [_ W1]. tauto.
      * destruct (Z_lt_le_dec a (slot_sp E + 40)) as [L3|L3];
          [|destruct (Z_lt_le_dec a (slot_sp E + 48)) as [L4|L4]].
        -- destruct (KEEP a ltac:(unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia) ltac:(lia)
             (NEH a ltac:(lia) ltac:(unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia))) as [_ W1]. tauto.
        -- destruct (HW a ltac:(lia)) as [N3|W3]; [|exact W3].
           destruct (KEEP a ltac:(unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia) ltac:(lia) N3) as [_ W1]. tauto.
        -- destruct (KEEP a ltac:(unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia) ltac:(lia)
             (NEH a ltac:(lia) ltac:(unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia))) as [_ W1]. tauto.
  - assert (KS : forall x, slot_sp E <= x < slot_sp E + 40 \/ slot_sp E + 48 <= x < slot_sp E + 192 ->
        mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\
        (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x)).
    { intros x Hx. apply KEEP; [unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|lia|].
      apply NEH; [lia|unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia]. }
    unfold stack_mid. split; [|split].
    + apply (p4_cells_keep _ mem); [exact ST1|]. intros x Hx. unfold saved_cells in Hx.
      cbn [cells_size csize] in Hx. apply KS. lia.
    + apply (p4_cells_keep _ mem); [exact ST2|]. intros x Hx. cbn [cells_size csize] in Hx. apply KS. lia.
    + apply (p4_cells_keep _ mem); [exact ST3|]. intros x Hx. cbn [cells_size csize] in Hx. apply KS. lia.
Qed.

Lemma p4_keep_mu : forall B API LS SH SK ra empty rc fx j E CS mem mem',
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  munch [(slot_sp E - 16, slot_sp E); (slot_sp E + 40, slot_sp E + 48)] mem mem' -> wmono (ms_segs B) mem mem' ->
  image_kept (rc := rc) B E mem -> stack_mid B E mem ->
  image_kept (rc := rc) B E mem' /\ stack_mid B E mem'.
Proof.
  intros B API LS SH SK ra empty rc fx j E CS mem mem' HF MU WM (IK1 & IK2 & IK3 & IK4) (ST1 & ST2 & ST3).
  pose proof HF as (FF & _ & PRE & _).
  destruct (p4_ff _ _ _ _ _ _ _ FF) as (SEG & _).
  pose proof (proj1 (proj1 PRE)) as LP. destruct LP as (_ & _ & _ & _ & _ & _ & SPLO & SPHI & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (slot_sp E - 16 <= a < slot_sp E) ->
      ~ (slot_sp E + 40 <= a < slot_sp E + 48) ->
      mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
      (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha N0 N. split; [apply (munch_mbyte _ _ _ _ a MU Ha)|apply (munch_writable _ _ _ _ a MU Ha)];
      cbn [outside]; (split; [lia|split; [lia|exact I]]). }
  split.
  - split; [|split; [|split]].
    + intros a HI HS HC HEr HG. destruct (IK1 a HI HS HC HEr HG) as [EA WA].
      pose proof (in_img_low B SEG a HI) as IL.
      destruct (KEEP a ltac:(lia) ltac:(unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia)
        ltac:(unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia)) as [E1 W1].
      split; [congruence|tauto].
    + intros a HG. rewrite SEG. split; intros _; exact (proj1 (p4u_global_access _ a HG)).
    + intros a HA HNS. destruct (IK3 a HA HNS) as [EA WA].
      assert (N0 : ~ (slot_sp E - 16 <= a < slot_sp E)).
      { intros X. apply HNS. unfold lib_scratch. left. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
      assert (N : ~ (slot_sp E + 40 <= a < slot_sp E + 48)).
      { intros X. apply HNS. unfold lib_scratch. left. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
      destruct (KEEP a ltac:(lia) N0 N) as [E1 W1].
      split; [congruence|tauto].
    + intros a HS. apply WM. exact (IK4 a HS).
  - unfold stack_mid. split; [|split].
    + apply (p4_cells_keep _ mem); [exact ST1|]. intros x Hx. unfold saved_cells in Hx.
      cbn [cells_size csize] in Hx. apply KEEP; unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia.
    + apply (p4_cells_keep _ mem); [exact ST2|]. intros x Hx. cbn [cells_size csize] in Hx.
      apply KEEP; unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia.
    + apply (p4_cells_keep _ mem); [exact ST3|]. intros x Hx. cbn [cells_size csize] in Hx.
      apply KEEP; unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia.
Qed.

Lemma p4_glob_cells : forall m a (n : nat), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> in_globals G_reply (a + i)) -> exists bs, rw_cells rsegs m a [CB n bs].
Proof.
  intros m a n H0 H1 HG.
  destruct (rk_bytes_of_mbytes rsegs m a n H0 H1) as (bs & Lb & Hb).
  { intros i Hi. exact (proj2 (p4u_global_access m (a + i) (HG i Hi))). }
  exists bs. split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi.
    exact (proj1 (p4u_global_access m (a + i) (HG i ltac:(lia)))).
Qed.

Section KB.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.

Definition p4_kb (m m' : word -> option byte) (lo : Z) : Prop := forall a, 0 <= a < lo -> rk_kb2 B m m' a.

Lemma p4_rw_kb : forall m m' lo a cs, p4_kb m m' lo -> rw_cells (ms_segs B) m a cs ->
  a + Z.of_nat (cells_size cs) <= lo -> rw_cells (ms_segs B) m' a cs.
Proof.
  intros m m' lo a cs K H L. pose proof (rw_cells_bound _ _ _ _ H) as BD.
  apply (rk_rw_kb2 B m); [exact H|]. intros i Hi. apply K. lia.
Qed.

Lemma p4_by_kb : forall m m' lo a bs, p4_kb m m' lo -> bytes_at (ms_segs B) m a bs ->
  a + Z.of_nat (length bs) <= lo -> bytes_at (ms_segs B) m' a bs.
Proof.
  intros m m' lo a bs K H L. pose proof H as (H0 & _).
  apply (rk_bytes_kb2 B m); [exact H|]. intros i Hi. apply K. lia.
Qed.

Lemma p4_mu_kb : forall m m' lo hi, munch [(lo, hi)] m m' -> wmono (ms_segs B) m m' -> lo <= 2 ^ 64 ->
  p4_kb m m' lo.
Proof.
  intros m m' lo hi MU WM HL a Ha. apply (rk_mu_kb2 B [(lo, hi)] m m' a MU WM); [lia|].
  cbn [outside]. split; [lia|exact I].
Qed.

Lemma p4_fresh_rw : forall m m' a n cs, p4_kb m m' (@YM05.alloc_ceiling rc + 8) -> fresh_block B a n ->
  Z.of_nat (cells_size cs) <= n -> rw_cells (ms_segs B) m a cs -> rw_cells (ms_segs B) m' a cs.
Proof. intros m m' a n cs K (F0 & F1 & _) L H. apply (p4_rw_kb m m' _ a cs K H). lia. Qed.

Lemma p4_fresh_by : forall m m' a n bs, p4_kb m m' (@YM05.alloc_ceiling rc + 8) -> fresh_block B a n ->
  Z.of_nat (length bs) <= n + 7 -> bytes_at (ms_segs B) m a bs -> bytes_at (ms_segs B) m' a bs.
Proof. intros m m' a n bs K (F0 & F1 & _) L H. apply (p4_by_kb m m' _ a bs K H). lia. Qed.

Lemma p4_ent_kb : forall L A m m' e, p4_kb m m' (@YM05.alloc_ceiling rc + 8) ->
  RelayRep.entry_ok B L A m e -> RelayRep.entry_ok B L A m' (short_entry e).
Proof.
  intros L A m m' e K (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & BU & H10 & HP & ND1 & ND2 & KS).
  unfold RelayRep.entry_ok, re_nheld in *.
  cbn [short_entry re_fd re_eof re_skip re_pad1 re_pad2 re_buf re_used re_cap re_hp re_kh re_keys re_U re_junk].
  rewrite length_map, short_keys_ptrs, short_keys_addr, short_keys_text.
  do 9 (split; [assumption|]). split.
  { destruct BU as [BU|(C & IN & FR & J & BC)]; [left; exact BU|right].
    split; [exact C|]. split; [exact IN|]. split; [exact FR|]. split; [exact J|].
    eapply p4_fresh_rw; [exact K|exact FR|cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia|exact BC]. }
  split; [exact H10|]. split.
  { destruct HP as [(HP & HK)|(IN & FR & HC & HH & HB)].
    - left. split; [exact HP|]. rewrite HK. reflexivity.
    - right. split; [exact IN|]. split; [exact FR|]. split; [exact HC|]. split; [exact HH|].
      eapply p4_fresh_by; [exact K|exact FR| |exact HB].
      rewrite slot_key_ptrs_length. lia. }
  split; [exact ND1|]. split; [exact ND2|].
  apply Forall_map. eapply Forall_impl; [|exact KS].
  intros [[addr txt] slack] (IN & FR & HB & NZ & LEN & PAD).
  cbn [short_key key_addr key_text key_slack fst snd] in *.
  split; [exact IN|]. split; [exact FR|]. split.
  { eapply p4_fresh_by; [exact K|exact FR| |].
    - cbn [short_key key_addr key_text key_slack fst snd]. rewrite length_app. cbn [length]. rewrite length_firstn. lia.
    - rewrite bytes_at_app in HB |- *. destruct HB as [HB HT]. split; [exact HB|].
      change (bytes_at (ms_segs B) m (addr + Z.of_nat (length txt)) (firstn 8 (Z_to_bv 8 0 :: slack))).
      apply bytes_at_prefix. exact HT. }
  split; [exact NZ|]. split; [exact LEN|]. rewrite length_firstn.
  pose proof (Z.mod_pos_bound (- (addr + Z.of_nat (length txt) + 1)) 8 ltac:(lia)). lia.
Qed.

Lemma p4_src_kb : forall (API : AllocAPI B) L A m m' md HA h, aa_MR API L A m md ->
  p4_kb m m' (@YM05.alloc_ceiling rc + 8) -> HA + 96 <= @YM05.alloc_ceiling rc ->
  src_at B L A m HA h -> src_at B L A m' HA h.
Proof.
  intros API L A m m' md HA h HM K HB S. pose proof S as (S1 & _).
  pose proof (rw_cells_bound _ _ _ _ S1) as BD.
  apply (rk_src_at_kept B L A m L A m' HA h S).
  - intros i Hi. apply K. lia.
  - intros q _ k Hin. split; [exact Hin|]. intros i Hi.
    destruct (rk_blk B API L A m md q k i HM Hin Hi) as (_ & Q0 & Q1 & _). apply K. lia.
Qed.

Lemma p4_list_blk_of : forall L A m LA l b, list_at B L A m LA l b -> p4_list_blk L A l.
Proof.
  intros L A m LA l b (_ & _ & AR & _ & _ & FA). split.
  - destruct AR as [(X & _)|(_ & X & _)]; [left; exact X|right; exact X].
  - eapply Forall_impl; [|exact FA]. intros r (X & _). exact X.
Qed.

Lemma p4_src_blk_of : forall L A m HA h, src_at B L A m HA h -> p4_src_blk L A h.
Proof.
  intros L A m HA h (_ & _ & _ & _ & _ & LP & _ & _ & _ & _ & PIn & _ & _ & _ & _ & LE & LH & ND).
  split; [exact (p4_list_blk_of _ _ _ _ _ _ LP)|]. split; [exact PIn|].
  split; [exact (p4_list_blk_of _ _ _ _ _ _ LE)|]. split; [exact (p4_list_blk_of _ _ _ _ _ _ LH)|exact ND].
Qed.

Lemma p4_ent_blk_of : forall L A m e, RelayRep.entry_ok B L A m e -> p4_ent_blk L A e.
Proof.
  intros L A m e (_ & _ & _ & _ & _ & _ & _ & _ & _ & BU & _ & HP & _ & _ & KS).
  split; [destruct BU as [(X & _)|(_ & X & _)]; [left; exact X|right; exact X]|].
  split; [destruct HP as [(X & _)|(X & _)]; [left; exact X|right; exact X]|].
  eapply Forall_impl; [|exact KS]. intros k (X & _). exact X.
Qed.

End KB.

Lemma p4_eb_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof. intros e H1 H2. unfold entry_bytes. rewrite !length_app, !length_le4, !length_le8, H1, H2. reflexivity. Qed.

Lemma p4_concat_len : forall l, Forall (fun e => length (entry_bytes e) = 56%nat) l ->
  length (concat (map entry_bytes l)) = (56 * length l)%nat.
Proof. induction 1 as [|x l Hx _ IH]; cbn [map concat length]; [reflexivity|]. rewrite length_app, Hx, IH. lia. Qed.

Lemma p4_tab_entry : forall segs m G es tail i,
  bytes_at segs m G (concat (map entry_bytes es) ++ tail) -> Forall (fun e => length (entry_bytes e) = 56%nat) es ->
  (i < length es)%nat -> bytes_at segs m (G + 56 * Z.of_nat i) (entry_bytes (nth i es no_entry)).
Proof.
  intros segs m G es tail i HB HL Hi.
  assert (LF : length (concat (map entry_bytes (firstn i es))) = (56 * i)%nat).
  { rewrite p4_concat_len; [rewrite length_firstn; lia|]. apply Forall_forall. intros x Hx.
    rewrite Forall_forall in HL. apply HL. rewrite <- (firstn_skipn i es). apply in_or_app. left. exact Hx. }
  rewrite (split_at es i no_entry Hi) in HB. rewrite map_app, concat_app in HB. cbn [map concat] in HB.
  rewrite <- !app_assoc in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
  apply bytes_at_app in HB. destruct HB as [HB _]. rewrite LF in HB.
  replace (G + 56 * Z.of_nat i) with (G + Z.of_nat (56 * i)) by lia. exact HB.
Qed.

Lemma p4_f2_nth : forall {X Y} (P : X -> Y -> Prop) xs ys q y, Forall2 P xs ys -> nth_error ys q = Some y ->
  exists x, nth_error xs q = Some x /\ P x y.
Proof.
  intros X Y P xs ys q y H. revert q. induction H as [|x y0 xs ys Hxy H IH]; intros q Hq.
  - destruct q; discriminate.
  - destruct q as [|q]; cbn in Hq |- *; [injection Hq as <-; exists x; split; [reflexivity|exact Hxy]|exact (IH q Hq)].
Qed.

Lemma p4_nth_combine : forall {X Y} (l1 : list X) (l2 : list Y) n x y,
  nth_error l1 n = Some x -> nth_error l2 n = Some y -> In (x, y) (combine l1 l2).
Proof.
  intros X Y l1. induction l1 as [|a l1 IH]; intros [|b l2] n x y H1 H2; destruct n as [|n]; cbn in *;
    try discriminate.
  - injection H1 as <-. injection H2 as <-. left. reflexivity.
  - right. exact (IH l2 n x y H1 H2).
Qed.

Lemma p4_slot_in : forall (hj : list (hsrc * nat)) k, slot_open hj k = true -> exists h, In (h, k) hj.
Proof.
  intros hj k H. unfold slot_open in H. apply existsb_exists in H as (x & Hx & Ex).
  apply Nat.eqb_eq in Ex. subst x. apply in_map_iff in Hx as ([h q] & Eq & Hin). cbn in Eq. subst q.
  exists h. exact Hin.
Qed.

Lemma p4_pick : forall (P : rentry -> hsrc * nat -> Prop) es hj k, Forall2 P es hj -> slot_open hj k = true ->
  exists q e h, nth_error es q = Some e /\ nth_error hj q = Some (h, k) /\ P e (h, k).
Proof.
  intros P es hj k F2 HO. destruct (p4_slot_in hj k HO) as (h & Hin).
  apply In_nth_error in Hin as (q & Hq). destruct (p4_f2_nth P es hj q (h, k) F2 Hq) as (e & He & HP).
  exists q, e, h. split; [exact He|]. split; [exact Hq|exact HP].
Qed.

Lemma p4_nodup_neq : forall {X Y} (f : X -> Y) (l : list X) a b x y, NoDup (map f l) ->
  nth_error l a = Some x -> nth_error l b = Some y -> a <> b -> f x <> f y.
Proof.
  intros X Y f l a b x y ND Ha Hb Nab Exy. apply NoDup_ListNoDup in ND.
  apply Nab. apply (proj1 (List.NoDup_nth_error (map f l)) ND a b).
  - rewrite length_map. apply nth_error_Some. rewrite Ha. discriminate.
  - rewrite !nth_error_map, Ha, Hb. cbn. rewrite Exy. reflexivity.
Qed.

Definition p4_slot_fd (hj : list (hsrc * nat)) (k : nat) : Z :=
  match find (fun p => Nat.eqb (snd p) k) hj with Some p => hs_fd (fst p) | None => 0 end.

Definition p4_fs (hj : list (hsrc * nat)) : list Z :=
  map (fun k => if slot_open hj k then p4_slot_fd hj k else 0) (seq 0 4).

Definition p4_os (hj : list (hsrc * nat)) : list Z := map (fun k => if slot_open hj k then 1 else 0) (seq 0 4).

Lemma p4_others : forall rc B L A mem t es hj e h i q,
  Forall2 (pair_ok (rc := rc) B L A mem t) es hj -> NoDup (map snd hj) -> NoDup (map re_fd es) ->
  (forall k, (k < 4)%nat -> slot_open hj k = false ->
     rw_cells (ms_segs B) mem (G_S + SRC_SIZE * Z.of_nat k) [CB 96%nat (nulbytes 96)]) ->
  nth_error es q = Some e -> nth_error hj q = Some (h, i) ->
  others_at B mem i (re_fd e) (p4_fs hj) (p4_os hj).
Proof.
  intros rc B L A mem t es hj e h i q F2 NDS NDF ZS He Hh.
  split; [unfold p4_fs; rewrite length_map, length_seq; reflexivity|].
  split; [unfold p4_os; rewrite length_map, length_seq; reflexivity|].
  intros k Hk Nk.
  assert (EF : nth k (p4_fs hj) 0 = if slot_open hj k then p4_slot_fd hj k else 0)
    by (unfold p4_fs; destruct k as [|[|[|[|k]]]]; [reflexivity|reflexivity|reflexivity|reflexivity|lia]).
  assert (EO : nth k (p4_os hj) 0 = if slot_open hj k then 1 else 0)
    by (unfold p4_os; destruct k as [|[|[|[|k]]]]; [reflexivity|reflexivity|reflexivity|reflexivity|lia]).
  rewrite EF, EO. destruct (slot_open hj k) eqn:SO.
  - unfold p4_slot_fd. destruct (find (fun p => Nat.eqb (snd p) k) hj) as [[h2 k2]|] eqn:FD.
    2:{ exfalso. destruct (p4_slot_in hj k SO) as (h3 & H3).
        pose proof (find_none _ _ FD (h3, k) H3) as X. cbn in X. rewrite Nat.eqb_refl in X. discriminate. }
    apply find_some in FD as [Hin Ek]. cbn [snd] in Ek. apply Nat.eqb_eq in Ek. subst k2. cbn [fst].
    apply In_nth_error in Hin as (q2 & Hq2).
    destruct (p4_f2_nth _ es hj q2 (h2, k) F2 Hq2) as (e2 & He2 & PO).
    destruct PO as (SRC & _ & FDE & _). cbn [fst snd] in SRC, FDE.
    destruct SRC as (C1 & _ & _ & HOP & HFD & _).
    assert (Nq : q2 <> q).
    { intros ->. rewrite Hh in Hq2. injection Hq2 as _ X. exact (Nk (eq_sym X)). }
    split.
    + rewrite HOP in C1.
      change [C4 (Z_to_bv 64 (hs_fd h2)); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 (hs_closed h2));
              C4 (Z_to_bv 64 (hs_eintr h2))]
        with ([C4 (Z_to_bv 64 (hs_fd h2)); C4 (Z_to_bv 64 1)] ++
              [C4 (Z_to_bv 64 (hs_closed h2)); C4 (Z_to_bv 64 (hs_eintr h2))]) in C1.
      exact (proj1 (hg_cut _ _ _ _ _ C1)).
    + split; [right; rewrite FDE; exact (p4_nodup_neq re_fd es q2 q e2 e NDF He2 He Nq)|exact HFD].
  - pose proof (ZS k Hk SO) as Z0.
    assert (Z1 : rw_cells (ms_segs B) mem (G_S + SRC_SIZE * Z.of_nat k)
        ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ [CB 88 (nulbytes 88)]))
      by (eapply rw_cells_retype; [exact Z0|cbn; tauto|reflexivity]).
    split; [exact (proj1 (hg_cut _ _ _ _ _ Z1))|]. split; [left; reflexivity|lia].
Qed.

Lemma p4_cpk : forall B API LS SH SK ra empty rc fx j E CS K' L A regs mem md (ra' : Z),
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  aa_MR (API rc) L A mem md -> WF A -> bounded A -> st_init_done A = true -> image_kept (rc := rc) B E mem ->
  getr regs 1 = Z_to_bv 64 ra' -> 0 <= ra' < 2 ^ 64 -> ra' mod 2 = 0 ->
  getr regs 2 = Z_to_bv 64 (slot_sp E) -> getr regs 4 = getr (ss_regs E) 4 -> 0 <= K' <= 65344 ->
  call_pre_k (rc := rc) B (aa_MR (API rc)) K' L A regs mem md.
Proof.
  intros B API LS SH SK ra empty rc fx j E CS K' L A regs mem md ra' HF HM HW HB HI (_ & _ & _ & IK4)
    R1 Hra Hev R2 R4 HK.
  pose proof HF as (FF & _ & PRE & _).
  destruct (proj1 (proj1 PRE)) as (_ & _ & _ & _ & _ & ALIGN & SPLO & SPHI & _ & TP & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC.
  assert (REGSP : spZ regs = slot_sp E).
  { unfold spZ. change (bv_unsigned (getr regs 2) = slot_sp E). rewrite R2. apply unsigned_lit.
    unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  unfold call_pre_k. split; [exact HM|]. split; [exact HW|]. split; [exact HB|].
  split; [change (YK0s.ret_ok (getr regs 1)); rewrite R1; apply ret_ok_even; rewrite unsigned_lit by lia; exact Hev|].
  rewrite REGSP. split; [unfold slot_sp, SLOT_FRAME; Z.div_mod_to_equations; lia|].
  split; [unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|]. split; [unfold slot_sp, SLOT_FRAME; lia|].
  split; [intros a Ha; apply IK4; unfold lib_scratch; left; unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|].
  split; [change (getr regs 4 = Z_to_bv 64 (ms_tp B)); rewrite R4; exact TP|].
  split; [intros a Ha; apply IK4; unfold lib_scratch; right; exact Ha|].
  rewrite HI. discriminate.
Qed.

Definition p4_sv (E : sstart) (t K s : Z) (regs : bvmap 5 word) : Prop :=
  base_regs E regs /\ fix_regs E regs /\ getr regs 8 = Z_to_bv 64 (ss_p E + K) /\
  getr regs 26 = Z_to_bv 64 (ss_n E - K) /\ getr regs 22 = Z_to_bv 64 t /\ getr regs 9 = Z_to_bv 64 s.

Ltac p4_pres RP X r := exact (eq_trans (RP r ltac:(unfold callee_saved; lia)) X).

Lemma p4_sv_pres : forall E t K s R R', p4_sv E t K s R -> regs_preserved R R' -> p4_sv E t K s R'.
Proof.
  intros E t K s R R' ((B2 & B3 & B4 & B20) & (F23 & F25 & F21 & F19 & F27 & F24) & R8 & R26 & R22 & R9) RP.
  split; [split; [p4_pres RP B2 2|split; [p4_pres RP B3 3|split; [p4_pres RP B4 4|p4_pres RP B20 20]]]|].
  split; [split; [p4_pres RP F23 23|split; [p4_pres RP F25 25|split; [p4_pres RP F21 21|
    split; [p4_pres RP F19 19|split; [p4_pres RP F27 27|p4_pres RP F24 24]]]]]|].
  split; [p4_pres RP R8 8|]. split; [p4_pres RP R26 26|]. split; [p4_pres RP R22 22|p4_pres RP R9 9].
Qed.

Lemma p4_sv_tail : forall E t K s R, p4_sv E t K s R -> tail_regs E t K R.
Proof. intros E t K s R (H1 & H2 & H3 & H4 & H5 & _). split; [exact H1|]. split; [exact H2|]. tauto. Qed.

Ltac p4_rx X := etransitivity; [apply (getr_of_eqv _ _ _ X); reflexivity|]; first [assumption|reflexivity].

Ltac p4_svx X SVp :=
  let H := fresh "SVX" in pose proof SVp as H;
  destruct H as ((? & ? & ? & ?) & (? & ? & ? & ? & ? & ?) & ? & ? & ? & ?);
  split; [split; [p4_rx X|split; [p4_rx X|split; [p4_rx X|p4_rx X]]]|];
  split; [split; [p4_rx X|split; [p4_rx X|split; [p4_rx X|split; [p4_rx X|split; [p4_rx X|p4_rx X]]]]]|];
  split; [p4_rx X|]; split; [p4_rx X|]; split; [p4_rx X|p4_rx X].

Definition p4_rs (x y : rentry) : Prop :=
  exists ks, map fst ks = map fst (re_keys x) /\ y = rk_with_keys x ks.

Lemma p4_kt_map : forall a b : list (Z * list byte * list byte), map key_text a = map key_text b ->
  keys_total a = keys_total b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn [map] in H; try discriminate; [reflexivity|].
  injection H as H1 H2. change (Z.of_nat (length (key_text x)) + 5 + keys_total a =
    Z.of_nat (length (key_text y)) + 5 + keys_total b). rewrite H1, (IH b H2). reflexivity.
Qed.

Lemma p4_rs_facts : forall x y, p4_rs x y ->
  entry_bytes y = entry_bytes x /\ entry_blocks y = entry_blocks x /\ re_fd y = re_fd x /\
  re_eof y = re_eof x /\ re_skip y = re_skip x /\ re_used y = re_used x /\ re_U y = re_U x /\
  keys_texts (re_keys y) = keys_texts (re_keys x) /\ keys_total (re_keys y) = keys_total (re_keys x).
Proof.
  intros x y (ks & Eks & ->). destruct (rk_map_fst_keys (re_keys x) ks Eks) as (EA & ET & EL & EP & EX).
  split; [exact (rk_entry_bytes_wk x ks EL)|]. split; [exact (rk_entry_blocks_wk x ks EA)|].
  cbn [rk_with_keys re_fd re_eof re_skip re_used re_U re_keys].
  do 5 (split; [reflexivity|]). split; [exact EX|]. exact (p4_kt_map _ _ ET).
Qed.

Lemma p4_rs_cost : forall l l' hj, Forall2 p4_rs l l' -> slot_cost l' hj = slot_cost l hj.
Proof.
  intros l l' hj H. revert hj. induction H as [|x y l l' Hxy H IH]; intros [|p hj]; try reflexivity.
  change (pair_cost y p + slot_cost l' hj = pair_cost x p + slot_cost l hj). rewrite IH.
  destruct (p4_rs_facts x y Hxy) as (_ & _ & _ & _ & E5 & E6 & _ & _ & E9). unfold pair_cost.
  rewrite E5, E6, E9. reflexivity.
Qed.

Lemma p4_rs_map : forall {Y} (f : rentry -> Y) l l', (forall x y, p4_rs x y -> f y = f x) -> Forall2 p4_rs l l' ->
  map f l' = map f l.
Proof. intros Y f l l' HF H. induction H as [|x y l l' Hxy H IH]; [reflexivity|]. cbn [map]. rewrite (HF x y Hxy), IH. reflexivity. Qed.

Lemma p4_rs_nw : forall x y, p4_rs x y -> nw_ent y = nw_ent x.
Proof.
  intros x y (ks & Eks & ->). unfold nw_ent, re_nheld, rk_with_keys. cbn [re_cap re_used re_hp re_kh re_keys].
  rewrite <- (length_map fst ks), Eks, length_map. reflexivity.
Qed.

Lemma p4_rs_wt : forall l l' hj, Forall2 p4_rs l l' -> nc_wt l' hj = nc_wt l hj.
Proof.
  intros l l' hj H. assert (Z : AllocBound.zsum nw_ent l' = AllocBound.zsum nw_ent l).
  { induction H as [|x y l l' Hxy H IH]; [reflexivity|]. rewrite !AllocBound.zsum_cons, IH, (p4_rs_nw x y Hxy).
    reflexivity. }
  unfold nc_wt. rewrite Z, (Forall2_length H). reflexivity.
Qed.

Lemma p4_blk_eb : forall L A e, p4_ent_blk L A e -> SlotPass2Mv.p2_eb L A e.
Proof. intros L A e (X1 & X2 & _). split; assumption. Qed.

Lemma p4_blk_sb : forall L A h, p4_src_blk L A h -> SlotPass2Mv.p2_sb L A h.
Proof. intros L A h ((X1 & _) & X2 & (X3 & _) & (X4 & _) & _). split; [exact X1|split; [exact X2|split; assumption]]. Qed.

Lemma p4_rs_target : forall G O l l' hj, Forall2 p4_rs l l' -> target_addrs G O l' hj = target_addrs G O l hj.
Proof.
  intros G O l l' hj H. unfold target_addrs. rewrite (p4_rs_map entry_blocks l l'); [reflexivity| |exact H].
  intros x y Hxy. exact (proj1 (proj2 (p4_rs_facts x y Hxy))).
Qed.

Lemma p4_pair_rs : forall rc B L A m t x y p, pair_ok (rc := rc) B L A m t x p -> p4_rs x y -> pair_ok (rc := rc) B L A m t y p.
Proof.
  intros rc B L A m t x y p PO Hxy. destruct (p4_rs_facts x y Hxy) as (_ & _ & E3 & E4 & E5 & _ & E7 & E8 & _).
  unfold pair_ok in *. cbv zeta in *. rewrite E3, E4, E5, E7, E8. exact PO.
Qed.

Lemma p4_f2_comb : forall {X Y Z0} (R1 : X -> Y -> Prop) (R2 : X -> Z0 -> Prop) (R3 : Z0 -> Y -> Prop) l1 l2 l3,
  Forall2 R1 l1 l2 -> Forall2 R2 l1 l3 -> (forall x y z, In (x, y) (combine l1 l2) -> R1 x y -> R2 x z -> R3 z y) ->
  Forall2 R3 l3 l2.
Proof.
  intros X Y Z0 R1 R2 R3 l1 l2 l3 H1. revert l3. induction H1 as [|x y l1 l2 Hxy H1 IH]; intros l3 H2 HC.
  - inversion H2; constructor.
  - inversion H2 as [|? z ? l3' Hxz H2']; subst. constructor.
    + apply (HC x y z); [left; reflexivity|exact Hxy|exact Hxz].
    + apply IH; [exact H2'|]. intros a b c' Hab. apply HC. right. exact Hab.
Qed.

Lemma p4_nd_swap : forall (a b b' : Z) l, NoDup (a :: b :: l) -> ~ In b' (a :: l) -> NoDup (a :: b' :: l).
Proof.
  intros a b b' l ND NI. apply NoDup_ListNoDup in ND. apply NoDup_ListNoDup.
  apply List.NoDup_cons_iff in ND as [N1 ND]. apply List.NoDup_cons_iff in ND as [N2 ND].
  constructor; [intros [X|X]; [apply NI; left; exact (eq_sym X)|apply N1; right; exact X]|].
  constructor; [intros X; apply NI; right; exact X|exact ND].
Qed.

Lemma p4_rat_map : forall {X Y} (f : X -> Y) (l : list X) i, remove_at i (map f l) = map f (remove_at i l).
Proof.
  intros X Y f l i. destruct l as [|x p] using List.rev_ind; [reflexivity|]. clear IHp.
  rewrite map_app. cbn [map]. rewrite !remove_at_app_last, length_map.
  destruct (Nat.eqb i (length p)); [reflexivity|]. rewrite map_app, firstn_map, skipn_map. reflexivity.
Qed.

Lemma p4_rp_zero : forall rc B (API : AllocAPI B) K' E' F' L A R m md L' A' R' m' md' x,
  relay_post (rc := rc) B API K' E' F' L A R m md L' A' R' m' md' -> In (x, 0) (blocks L A) -> In (x, 0) (blocks L' A').
Proof.
  intros rc B API K' E' F' L A R m md L' A' R' m' md' x RP Hin.
  destruct RP as (_ & _ & _ & _ & _ & _ & _ & Z0 & _). unfold blocks in *.
  apply in_map_iff in Hin as ([p k] & EQ & Hp). cbn [fst snd] in EQ. injection EQ as <- ->.
  destruct (Z0 p Hp) as (H1 & H2). apply in_map_iff. exists (p, 0). cbn [fst snd]. rewrite H2. split; [reflexivity|exact H1].
Qed.

Lemma p4_eb_pos : forall rc B L A m e y, RelayRep.entry_ok (rc := rc) B L A m e -> In y (entry_blocks e) ->
  exists k, 0 < k /\ In (y, k) (blocks L A).
Proof.
  intros rc B L A m e y (_ & _ & _ & _ & _ & _ & _ & _ & _ & BU & _ & HP & _ & _ & KS) Hy.
  unfold entry_blocks in Hy. apply in_app_iff in Hy as [Hy|Hy].
  - destruct (re_cap e =? 0) eqn:EC; [destruct Hy|]. destruct Hy as [<-|[]]. apply Z.eqb_neq in EC.
    destruct BU as [(X & _)|(C & IN & _)]; [lia|]. exists (re_cap e). split; [lia|exact IN].
  - apply in_app_iff in Hy as [Hy|Hy].
    + destruct (re_hp e =? 0) eqn:EH; [destruct Hy|]. destruct Hy as [<-|[]]. apply Z.eqb_neq in EH.
      destruct HP as [(X & _)|(IN & _ & _ & K8 & _)]; [lia|]. exists (re_kh e). split; [lia|exact IN].
    + apply in_map_iff in Hy as (k & <- & Hk). rewrite Forall_forall in KS. destruct (KS k Hk) as (IN & _).
      exists (Z.of_nat (length (key_text k)) + 1). split; [lia|exact IN].
Qed.

Lemma p4_f2_in_r : forall {X Y} (R : X -> Y -> Prop) l l' y, Forall2 R l l' -> In y l' -> exists x, In x l /\ R x y.
Proof.
  intros X Y R l l' y H. induction H as [|x y0 l l' Hxy H IH]; intros Hy; [destruct Hy|].
  destruct Hy as [<-|Hy]; [exists x; split; [left; reflexivity|exact Hxy]|].
  destruct (IH Hy) as (x0 & Hx0 & R0). exists x0. split; [right; exact Hx0|exact R0].
Qed.

Lemma p4_pick_rs : forall rc B (API : AllocAPI B) L A m (l : list rentry),
  Forall (rk_entry_okk B L A m) l -> exists l', Forall2 p4_rs l l' /\ Forall (RelayRep.entry_ok (rc := rc) B L A m) l'.
Proof.
  intros rc B API L A m l H. induction H as [|x l (ks & Eks & OK) H IH].
  - exists []. split; constructor.
  - destruct IH as (l' & F2 & FA). exists (rk_with_keys x ks :: l'). split.
    + constructor; [exists ks; split; [exact Eks|reflexivity]|exact F2].
    + constructor; [exact OK|exact FA].
Qed.

Lemma p4_nth_fd : forall es n, nth n (map re_fd es) 0 = re_fd (nth n es no_entry).
Proof. induction es as [|e es IH]; intros [|n]; cbn; [reflexivity|reflexivity|reflexivity|apply IH]. Qed.

Lemma p4_eb_split : forall e, entry_bytes e = le4 (Z_to_bv 64 (re_fd e)) ++ le4 (Z_to_bv 64 (re_eof e)) ++
  (le4 (Z_to_bv 64 (re_skip e)) ++ re_pad1 e ++
   le8 (Z_to_bv 64 (re_buf e)) ++ le8 (Z_to_bv 64 (re_used e)) ++ le8 (Z_to_bv 64 (re_cap e)) ++
   le8 (Z_to_bv 64 (re_hp e)) ++ le4 (Z_to_bv 64 (re_nheld e)) ++ re_pad2 e).
Proof. reflexivity. Qed.

Lemma p4_eb_nc : forall e, entry_blocks e = entry_nc e ++ map key_addr (re_keys e).
Proof. intros e. unfold entry_blocks, entry_nc. rewrite app_assoc. reflexivity. Qed.

Definition p4_srecs (h : hsrc) : list Z :=
  map fst (hl_recs (hs_pending h)) ++ map fst (hl_recs (hs_expected h)) ++ map fst (hl_recs (hs_held h)).

Lemma p4_hb_nc : forall h, Permutation (hs_blocks h) (src_nc h ++ p4_srecs h).
Proof.
  intros h. apply (Permutation_count_occ Z.eq_dec). intros x.
  unfold hs_blocks, list_blocks, src_nc, arr_nc, p4_srecs. rewrite !count_occ_app. lia.
Qed.

Lemma p4_rs_nc : forall x y, p4_rs x y -> entry_nc y = entry_nc x.
Proof. intros x y (ks & _ & ->). reflexivity. Qed.

Lemma p4_src_find : forall es q e, NoDup (map re_fd es) -> nth_error es q = Some e ->
  relay_source_c.src_find (re_fd e) es = Some (q, e).
Proof.
  induction es as [|x es IH]; intros q e ND Hq; [destruct q; discriminate|].
  apply NoDup_ListNoDup in ND. cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI ND].
  destruct q as [|q]; cbn in Hq.
  - injection Hq as <-. cbn [relay_source_c.src_find]. rewrite Z.eqb_refl. reflexivity.
  - cbn [relay_source_c.src_find].
    assert (NE : re_fd x <> re_fd e) by (intros X; apply NI; rewrite X; apply in_map; exact (nth_error_In es q Hq)).
    rewrite (proj2 (Z.eqb_neq _ _) NE). rewrite (IH q e (proj2 (NoDup_ListNoDup _) ND) Hq). reflexivity.
Qed.

Lemma p4_nodup_fst : forall {X Y} (l : list (X * Y)) x a b, List.NoDup (map fst l) -> In (x, a) l -> In (x, b) l ->
  a = b.
Proof.
  intros X Y l. induction l as [|[y c] l IH]; intros x a b ND Ha Hb; [destruct Ha|].
  cbn [map fst] in ND. inversion ND as [|z l' Hn Hl]; subst.
  destruct Ha as [Ea|Ha]; destruct Hb as [Eb|Hb].
  - injection Ea as E1 E2. injection Eb as E3 E4. congruence.
  - injection Ea as E1 E2. subst. exfalso. apply Hn. exact (in_map fst _ (x, b) Hb).
  - injection Eb as E3 E4. subst. exfalso. apply Hn. exact (in_map fst _ (x, a) Ha).
  - exact (IH x a b Hl Ha Hb).
Qed.

Definition p4_rflag (eof : Z) : Z := if eof =? 0 then 1 else 0.

Section P4Run.
Context {rc : YM05.RunCeil} {fx : FPState}.
Variables (F : ResFormT) (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape)
  (SH : sink_head) (SK : sink_syms) (ra empty : Z) (j : nat) (E : sstart) (CS : list byte -> list Z) (RI : res_inv).
Hypothesis HF : slot_frame B API LS SH SK ra empty rc fx j E CS.
Hypothesis RRc : forall fx', @relay_remove_contract fx' rc B (API rc) F.
Hypothesis CNRc : check_no_loss_read_contract.
Hypothesis CNLc : forall fx', @check_no_loss_contract fx' rc B (API rc) F.
Hypothesis CSEc : forall fx', @check_shape_ends_contract fx' rc B (API rc) F.
Hypothesis CSDc : check_shape_done_contract.
Hypothesis SRSc : forall fx', @source_reset_contract fx' rc B (API rc) F.
Hypothesis P4r : p4_res F RI.
Hypothesis CBc : check_bounded_contract.

Variables (fx0 : FPState) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte)
  (md0 : Model) (cl br gn dd ei G nfd : Z) (mx nout cap out : word) (es : list rentry) (hj : list (hsrc * nat))
  (t K s : Z) (e : rentry) (h : hsrc) (i q : nat).
Hypothesis FZ : frm_zero (@fp_csr fx0).
Hypothesis Ht : 0 <= t < OPS_MAX.
Hypothesis Hk : 0 <= K <= ss_n E.
Hypothesis Hn : ss_n E < INPUT_MAX.
Hypothesis HNO : bv_unsigned nout = 0.
Hypothesis HDR : disp_regs E t K s regs0.
Hypothesis HMR : aa_MR (API rc) L0 A0 mem0 md0.
Hypothesis HWF : WF A0.
Hypothesis HBD : bounded A0.
Hypothesis HINIT : st_init_done A0 = true.
Hypothesis HVM : exists vm, md0 = with_vmmaps vm (ss_md E).
Hypothesis HRO : ro_agree (ms_segs B) mem0.
Hypothesis HIK : image_kept (rc := rc) B E mem0.
Hypothesis HST : stack_mid B E mem0.
Hypothesis HDK : driver_kept B E (target_addrs G (bv_unsigned out) es hj) L0 A0 mem0.
Hypothesis HGL : globals_at B mem0 cl br gn dd ei (Z.of_nat (length es)) G nfd mx nout cap out.
Hypothesis Hnfd : 0 <= nfd <= t + 1.
Hypothesis HOUT : output_at (rc := rc) B L0 A0 mem0 nout cap out.
Hypothesis HREL : relay_at (rc := rc) B L0 A0 mem0 t nfd G (bv_unsigned out) es hj.
Hypothesis Hes : (length es <= 4)%nat.
Hypothesis Hcost : slot_cost es hj <= K.
Hypothesis HRI : RI E K (view_of G (bv_unsigned out) es hj) L0 A0.
Hypothesis HW : walk_at (ss_pl E) (t + 1) K.
Hypothesis Hqe : nth_error es q = Some e.
Hypothesis Hqh : nth_error hj q = Some (h, i).
Hypothesis Hs : s = G_S + SRC_SIZE * Z.of_nat i.

Lemma r_seg : ms_segs B = rsegs.
Proof. pose proof HF as (FF & _). exact (proj1 (p4_ff _ _ _ _ _ _ _ FF)). Qed.

Lemma r_fa : @frame_allocator rc fx B (API rc).
Proof.
  pose proof HF as (FF & _). destruct (p4_ff _ _ _ _ _ _ _ FF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & FA). exact (FA rc fx).
Qed.

Lemma r_AX : AllocExtra B (aa_MR (API rc)).
Proof. pose proof r_fa as FA. unfold frame_allocator in FA. tauto. Qed.
Lemma r_BW : blocks_writable B (API rc).
Proof. pose proof r_fa as FA. unfold frame_allocator in FA. tauto. Qed.
Lemma r_CTX : ctx_owned B (API rc).
Proof. pose proof r_fa as FA. unfold frame_allocator in FA. tauto. Qed.
Lemma r_BSP : block_slack_present B (API rc).
Proof. pose proof r_fa as FA. unfold frame_allocator in FA. tauto. Qed.
Lemma r_ND : blocks_nodup B (API rc).
Proof. pose proof r_fa as FA. unfold frame_allocator in FA. tauto. Qed.

Lemma r_ea : errno_addr B = 0x31acc.
Proof. pose proof HF as (FF & _). exact (proj1 (p4_errno _ _ _ _ _ _ _ FF)). Qed.

Lemma r_sp : @YM05.alloc_ceiling rc + SLOT_STACK <= spZ (ss_regs E) /\ spZ (ss_regs E) < 2 ^ 63 /\
  spZ (ss_regs E) mod 16 = 0.
Proof.
  pose proof HF as (_ & _ & PRE & _).
  destruct (proj1 (proj1 PRE)) as (_ & _ & _ & _ & _ & ALIGN & SPLO & SPHI & _). tauto.
Qed.

Ltac p4_num := pose proof r_sp as (SPLO & SPHI & SPAL); pose proof (@YM05.alloc_ceiling_value rc) as ACV;
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL; unfold slot_sp, SLOT_FRAME, SLOT_STACK in *.

Ltac p4_cst := unfold G_BROKEN, G_EINTR, G_OUTV, G_DEAD, G_CLIENT, G_RELAY_LO, relay_event_c.G_LOCK,
  Statement.G_LOCK, Statement.G_NSRC, check_bounded_c.G_NSRC, relay_add_b_c.G_NSRC, check_bounded_c.G_SRC,
  relay_add_b_c.G_SRC, StatementKept.G_SRC, StatementKept.G_NOUT, check_shape_done_c.G_NOUT, StatementKept.G_OUT,
  CheckRep.G_GONE, check_no_loss_c.G_GONE, check_shape_ends_c.G_GONE, G_WAKE1, HarnessRep.G_S, Statement.G_S,
  drain_b_c.G_S, source_reset_c.G_S, check_shape_ends_c.G_S, gesture_model_c.G_S, relay_source_c.G_NSRC,
  relay_source_c.G_SRC,
  SRC_SIZE, SRC_TABLE, SRC_ENTRY, G_NFD, relay_finish_b_c.G_LISTEN, relay_finish_b_c.G_THREAD_UP,
  Statement.G_THREAD_UP, G_WAKE0, SOURCES_MAX in *.

Lemma r_pair : pair_ok (rc := rc) B L0 A0 mem0 t e (h, i).
Proof.
  pose proof HREL as (_ & _ & _ & _ & _ & _ & PA & _).
  destruct (p4_f2_nth _ es hj q (h, i) PA Hqh) as (e' & He' & PO). rewrite Hqe in He'.
  injection He' as <-. exact PO.
Qed.

Lemma r_eok : RelayRep.entry_ok B L0 A0 mem0 e.
Proof.
  pose proof HREL as (_ & _ & _ & HES & _). rewrite Forall_forall in HES. apply HES.
  exact (nth_error_In es q Hqe).
Qed.

Lemma r_q : (q < length es)%nat /\ (q < length hj)%nat /\ length es = length hj.
Proof.
  pose proof HREL as (_ & _ & _ & _ & _ & _ & PA & _). pose proof (Forall2_length PA) as L.
  split; [apply nth_error_Some; rewrite Hqe; discriminate|]. split; [apply nth_error_Some; rewrite Hqh; discriminate|].
  exact L.
Qed.

Lemma r_J1 : re_eof e = 0 -> J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h).
Proof.
  intros E0. pose proof r_pair as PO. cbv zeta in PO. cbn [fst snd] in PO.
  destruct PO as (_ & _ & _ & SKU & _). destruct (SKU E0) as [SKO SKW].
  pose proof r_eok as (_ & SK01 & _ & _ & _ & _ & EUL & EUS & EUZ & _).
  unfold J1, hs_state. cbn [ls_k ls_w]. rewrite SKO.
  split; [reflexivity|]. split.
  - intros F0. apply SKW. destruct SK01 as [S|S]; [exact S|]. rewrite <- SKO, S in F0. discriminate.
  - split.
    + unfold bzs. rewrite length_map. apply Nat2Z.inj_le. change (Z.of_nat LINE_LIMIT) with 6000.
      clear - EUL EUS. lia.
    + unfold nozero, bzs. apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & Hb).
      intros Z0. apply EUZ. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. unfold bz in Z0.
      rewrite Z0. reflexivity.
Qed.

Lemma r_pok : forall NO CAP e0, rma_pok (drain_init NO CAP e0 h).
Proof.
  intros NO CAP e0. pose proof r_pair as PO. cbv zeta in PO. cbn [fst snd] in PO.
  destruct PO as (SRC & _). destruct SRC as (_ & _ & _ & _ & _ & LP & _ & OFFD & _). cbn [fst snd] in LP, OFFD.
  destruct LP as (_ & _ & _ & _ & _ & HR).
  unfold rma_pok, drain_init. cbn [ds_off ds_pend].
  destruct OFFD as [(R0 & O0)|(r & rs & ERq & ORq)].
  - rewrite R0. split; [clear - O0; lia | exact I].
  - rewrite ERq in HR |- *. cbn [map]. split; [clear - ORq; lia|].
    split; [unfold bzs; rewrite length_map; clear - ORq; lia|].
    apply Forall_map. apply Forall_forall. intros r' Hr'. apply Forall_inv_tail in HR.
    destruct (proj1 (Forall_forall _ _) HR r' Hr') as (_ & _ & _ & _ & L1x). unfold bzs. rewrite length_map.
    exact (L1x eq_refl).
Qed.

Lemma r_capc : re_cap e = 0 \/ 8192 <= re_cap e.
Proof. pose proof r_eok as (_ & _ & _ & _ & _ & ECP & _). clear - ECP. lia. Qed.

Definition r_cap1 : Z :=
  remove_entry_cap (send_live cl br dd 1) (bv_unsigned mx) 0 (bv_unsigned cap) (short_entry e) h.

Definition r_mh : word -> option byte :=
  write_to_mem (normalize rsegs mem0) (Z_to_bv 64 (slot_sp E + 40)) (le8 (Z_to_bv 64 0)).

Lemma p4_sv_ext : forall R R', (forall r, getr R' r = getr R r) -> p4_sv E t K s R -> p4_sv E t K s R'.
Proof. intros R R' X SV. unfold p4_sv, base_regs, fix_regs in *. rewrite !X. exact SV. Qed.

Lemma r_rr_val : relay_reads_c.relay_reads_r (re_fd e) es = if re_eof e =? 0 then 1 else 0.
Proof.
  pose proof HREL as (_ & _ & _ & _ & NDF & _). unfold relay_reads_c.relay_reads_r.
  rewrite (p4_src_find es q e NDF Hqe). reflexivity.
Qed.

Lemma r_head : SR (ms_segs B) (mkCfg (@YK11.mkst fx0 regs0 (Z_to_bv 64 0x142d0) mem0 (seg_rom (ms_segs B))) md0)
  (fun c => exists R1 m1, c = mkCfg (@YK11.mkst fx0 R1 (Z_to_bv 64 RELAY_REMOVE) m1 (seg_rom (ms_segs B))) md0 /\
     (munch [(slot_sp E - 16, slot_sp E); (slot_sp E + 40, slot_sp E + 48)] mem0 m1 /\ wmono (ms_segs B) mem0 m1 /\
      bytes_at (ms_segs B) m1 (slot_sp E + 40) (le8 (Z_to_bv 64 0))) /\
     p4_sv E t K s R1 /\ getr R1 1 = Z_to_bv 64 0x142f4 /\ getr R1 10 = Z_to_bv 64 (re_fd e) /\
     getr R1 18 = Z_to_bv 64 (p4_rflag (re_eof e))).
Proof.
  pose proof r_seg as SEG. pose proof r_pair as PO. pose proof r_eok as EOK.
  destruct r_q as (Hq1 & Hq2 & LQ).
  pose proof HREL as ((tail & TAB) & GIN & GFR & HES & NDF & _).
  cbv zeta in PO. cbn [fst snd] in PO. destruct PO as (SRC & Hi4 & FDE & _).
  pose proof EOK as (EO1 & _ & EP1 & EP2 & EFD & _).
  destruct HDR as ((B2 & B3 & B4 & B20) & (F23 & F25 & F21 & F19 & F27 & F24) & R8 & R26 & R22 & R9).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & _).
  pose proof HIK as (_ & _ & _ & IK4).
  destruct GFR as (GF0 & GF1 & _). unfold SRC_TABLE, SRC_ENTRY in GF1.
  assert (Hi : (i < 4)%nat) by exact Hi4. clear Hi4.
  pose proof HGL as (_ & _ & _ & _ & _ & _ & _ & G8 & _ & G10 & _).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (SB : @YM05.alloc_ceiling rc + 65000 <= slot_sp E - 16 /\ slot_sp E + 48 < 2 ^ 63).
  { pose proof r_sp as (SPLO & SPHI & SPAL). unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  assert (RO : ro_agree rsegs mem0) by (rewrite <- SEG; exact HRO).
  assert (HS0 : 0 < s < 2 ^ 64 /\ s mod 8 = 0).
  { rewrite Hs. clear - Hi. p4_cst. split; [lia|Z.div_mod_to_equations; lia]. }
  assert (HSB : s + 4 <= slot_sp E - 16) by (rewrite Hs; clear - Hi SB ACV; p4_cst; lia).
  assert (GAL : G mod 8 = 0).
  { pose proof GIN as GIN'. unfold blocks in GIN'. apply in_map_iff in GIN' as ([p k'] & EG & Hp).
    cbn [fst snd] in EG. injection EG as EG _. rewrite <- EG.
    pose proof (mr_blocks_aligned _ _ (aa_laws (API rc)) L0 A0 mem0 md0 p k' HMR Hp) as H16.
    Z.div_mod_to_equations. lia. }
  assert (EL : Forall (fun x => length (entry_bytes x) = 56%nat) es).
  { eapply Forall_impl; [|exact HES]. intros x (_ & _ & X3 & X4 & _). exact (p4_eb_len x X3 X4). }
  assert (BS : bytes_at rsegs mem0 s (le4 (Z_to_bv 64 (re_fd e)))).
  { pose proof SRC as (C1 & _). destruct C1 as ((_ & BY) & _). cbn [cells_bytes cbytes] in BY.
    rewrite app_nil_r, bytes_at_app in BY. rewrite SEG, FDE in BY. rewrite Hs. exact (proj1 BY). }
  assert (BN : bytes_at rsegs mem0 relay_source_c.G_NSRC (le4 (Z_to_bv 64 (Z.of_nat (length es))))).
  { destruct G8 as ((_ & BY) & _). cbn [cells_bytes cbytes] in BY. rewrite app_nil_r, bytes_at_app in BY.
    rewrite SEG in BY. exact (proj1 BY). }
  assert (BG : bytes_at rsegs mem0 relay_source_c.G_SRC (le8 (Z_to_bv 64 G))).
  { destruct G10 as ((_ & BY) & _). cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
    rewrite SEG in BY. exact BY. }
  assert (BT : bytes_at rsegs mem0 G (concat (map entry_bytes es))).
  { destruct TAB as (_ & TC). destruct TC as ((_ & BY) & _). cbn [cells_bytes cbytes] in BY.
    rewrite app_nil_r, bytes_at_app in BY. rewrite SEG in BY. exact (proj1 BY). }
  assert (BYN : forall a bs, bytes_at rsegs mem0 a bs -> a + Z.of_nat (length bs) <= slot_sp E + 40 ->
    bytes_at rsegs r_mh a bs).
  { intros a bs H L. unfold r_mh. change (Z_to_bv 64 (slot_sp E + 40)) with (wa (slot_sp E + 40)).
    apply bytes_at_write_other; [apply bytes_at_normalize; [exact RO|exact H]|lia|rewrite length_le8; lia|left; exact L]. }
  assert (STO : store_ok rsegs (normalize rsegs mem0) (Z_to_bv 64 (slot_sp E + 40)) 8 = true).
  { replace (slot_sp E + 40) with (slot_sp E + 40 + 0) by lia.
    change (Z_to_bv 64 (slot_sp E + 40 + 0)) with (wa (slot_sp E + 40 + 0)).
    apply (wr_at_store_ok rsegs (normalize rsegs mem0) (slot_sp E + 40) 8 0 8); [|lia|lia].
    apply (wr_at_norm rsegs mem0); [apply mem_rel_normalize; exact RO| |].
    - split; [lia|]. split; [lia|]. intros k0 Hk0. rewrite <- SEG.
      apply IK4. unfold lib_scratch. left. pose proof r_sp as (SPLO & SPHI & SPAL).
      unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
    - intros k0 Hk0. unfold wa. apply ro_addr_hi. lia. }
  assert (MI1 : mem_inv rsegs r_mh).
  { unfold r_mh. apply mem_inv_store; [apply mem_inv_normalize|rewrite length_le8; exact STO]. }
  assert (ST0 : stk rsegs mem0 (slot_sp E - 16) (slot_sp E)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (WA : writable_at rsegs mem0 a).
    { rewrite <- SEG. apply IK4. unfold lib_scratch. left. pose proof r_sp as (SPLO & SPHI & SPAL).
      unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
    split; [exact WA|]. destruct (writable_hi_present mem0 a ltac:(lia) WA) as [b HB].
    exists b. unfold mrd, wa. rewrite HB. reflexivity. }
  assert (ST1 : stk rsegs r_mh (slot_sp E - 16) (slot_sp E)).
  { unfold r_mh. change (Z_to_bv 64 (slot_sp E + 40)) with (wa (slot_sp E + 40)).
    apply stk_write; [apply stk_normalize; [exact ST0|lia]|lia|rewrite length_le8; lia]. }
  assert (US : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (USP : bv_unsigned (Z_to_bv 64 (slot_sp E)) = slot_sp E) by (apply unsigned_lit; lia).
  assert (UG : bv_unsigned (Z_to_bv 64 G) = G) by (apply unsigned_lit; lia).
  pose proof (relay_reads.relay_reads_holds relay_source.relay_source_holds) as RRD.
  unfold relay_reads_c.relay_reads_contract, relay_reads_c.RELAY_READS, relay_reads_c.RELAY_READS_K,
    relay_source_c.G_NSRC, relay_source_c.G_SRC in RRD.
  unfold relay_source_c.G_NSRC, relay_source_c.G_SRC in BN, BG.
  assert (E2 : reg_get regs0 2 = Z_to_bv 64 (slot_sp E)) by exact B2.
  assert (E3 : reg_get regs0 3 = getr (ss_regs E) 3) by exact B3.
  assert (E4 : reg_get regs0 4 = getr (ss_regs E) 4) by exact B4.
  assert (E8 : reg_get regs0 8 = Z_to_bv 64 (ss_p E + K)) by exact R8.
  assert (E9 : reg_get regs0 9 = Z_to_bv 64 s) by exact R9.
  assert (E19 : reg_get regs0 19 = Z_to_bv 64 4) by exact F19.
  assert (E20 : reg_get regs0 20 = Z_to_bv 64 G_RELAY_LO) by exact B20.
  assert (E21 : reg_get regs0 21 = Z_to_bv 64 10) by exact F21.
  assert (E22 : reg_get regs0 22 = Z_to_bv 64 t) by exact R22.
  assert (E23 : reg_get regs0 23 = Z_to_bv 64 (slot_sp E + 32)) by exact F23.
  assert (E24 : reg_get regs0 24 = Z_to_bv 64 1) by exact F24.
  assert (E25 : reg_get regs0 25 = Z_to_bv 64 DIV10) by exact F25.
  assert (E26 : reg_get regs0 26 = Z_to_bv 64 (ss_n E - K)) by exact R26.
  assert (E27 : reg_get regs0 27 = Z_to_bv 64 (G_S + 4)) by exact F27.
  pose proof (mem_rel_normalize rsegs mem0 RO) as HR0.
  rewrite SEG.
  eapply (kseg regs0 (Z_to_bv 64 0x142d0) mem0 md0 (fun ms => exists R m,
      ms = MS R (@fp_regs fx0) (Z_to_bv 64 RELAY_REMOVE) (@fp_csr fx0) None m (seg_rom rsegs) /\
      munch [(slot_sp E - 16, slot_sp E); (slot_sp E + 40, slot_sp E + 48)] (normalize rsegs mem0) m /\
      wmono rsegs (normalize rsegs mem0) m /\ bytes_at rsegs m (slot_sp E + 40) (le8 (Z_to_bv 64 0)) /\
      p4_sv E t K s R /\ getr R 1 = Z_to_bv 64 0x142f4 /\ getr R 10 = Z_to_bv 64 (re_fd e) /\
      getr R 18 = Z_to_bv 64 (p4_rflag (re_eof e))));
    [exact wx_apart_rsegs|exact RO|exact Hh|exact Hl| | |].
  - unfold Regs6ss.mkR_of. rewrite E2, E3, E4, E8, E9, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    eapply evt_cut; [apply (p4_head (slot_sp E) s) with (m1 := r_mh); [exact STO|reflexivity]|].
    intros ms1 ->.
    eapply evt_cut.
    { eapply RRD with (lo := slot_sp E - 16) (fd := re_fd e) (g := Z_to_bv 64 G) (es := es);
        rewrite ?US, ?USP, ?UG.
      - lia.
      - exact (proj2 HS0).
      - clear - EFD. lia.
      - apply BYN; [exact BS|rewrite length_le4; lia].
      - clear - Hes. lia.
      - apply BYN; [exact BN|rewrite length_le4; clear - SB ACV; lia].
      - apply BYN; [exact BG|rewrite length_le8; clear - SB ACV; lia].
      - split.
        + apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) HES x Hx) as (_ & _ & X3 & X4 & X5 & _).
          split; [exact X3|]. split; [exact X4|]. clear - X5. lia.
        + apply BYN; [exact BT|]. rewrite (p4_concat_len es EL), Nat2Z.inj_mul. clear - GF1 Hes SB ACV. lia.
      - apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) HES x Hx) as (X1 & _).
        clear - X1. lia.
      - intros _. split; [lia|exact GAL].
      - exact MI1.
      - exact ST1.
      - lia.
      - left. lia.
      - left. clear - SB ACV. lia.
      - left. clear - SB ACV. lia.
      - intros _. left. clear - GF1 Hes SB ACV. lia. }
    intros ms2 (a1' & a2' & a3' & a4' & a5' & a6' & a7' & m2 & -> & MU2 & WM2 & _ & _).
    rewrite USP in MU2. rewrite ret_pc_even by lia. rewrite r_rr_val.
    assert (BS2 : bytes_at rsegs m2 s (le4 (Z_to_bv 64 (re_fd e)))).
    { apply (bytes_at_transfer rsegs r_mh); [apply BYN; [exact BS|rewrite length_le4; lia]|].
      intros i0 Hi0. rewrite length_le4 in Hi0. apply (munch_mbyte rsegs _ _ _ _ MU2); [lia|].
      cbn [outside]. split; [lia|exact I]. }
    assert (BZ1 : bytes_at rsegs r_mh (slot_sp E + 40) (le8 (Z_to_bv 64 0))).
    { unfold r_mh. change (Z_to_bv 64 (slot_sp E + 40)) with (wa (slot_sp E + 40)).
      apply bytes_at_write_same; [lia|rewrite length_le8; lia]. }
    eapply evt_mono.
    { apply (p4_loop s (re_fd e)); [lia|exact (proj2 HS0)|clear - EFD; lia|].
      exact (p4_rd4 m2 s _ s BS2 eq_refl). }
    intros ms3 ->. do 2 eexists. split; [reflexivity|].
    split.
    { apply (munch_trans _ _ r_mh).
      - unfold r_mh. change (Z_to_bv 64 (slot_sp E + 40)) with (wa (slot_sp E + 40)).
        eapply munch_write; [apply munch_refl|lia|rewrite length_le8; lia|].
        cbn [inside]. right. left. rewrite length_le8. lia.
      - eapply munch_weaken; [|exact MU2]. unfold sub_fp. intros x Hx. cbn [outside] in Hx |- *. tauto. }
    split; [apply (wmono_trans rsegs (normalize rsegs mem0) r_mh m2); [unfold r_mh; apply wmono_write, wmono_refl|exact WM2]|].
    split.
    { apply (bytes_at_transfer rsegs r_mh); [exact BZ1|]. intros i0 Hi0. rewrite length_le8 in Hi0.
      apply (munch_mbyte rsegs _ _ _ _ MU2); [lia|]. cbn [outside]. split; [lia|exact I]. }
    split; [unfold p4_sv, base_regs, fix_regs; repeat split; reflexivity|].
    split; [reflexivity|]. split; reflexivity.
  - intros s0 (R & m & -> & _). exists R, (Z_to_bv 64 RELAY_REMOVE), m. reflexivity.
  - intros R pc' m0 regs1 m1 (R' & m' & EQ & MU & WM & BZ & SV & RA & FD & EO) GR MREL ROS.
    injection EQ as ER EP EM. subst R' pc' m'.
    apply SR_ret. exists regs1, m1. split; [reflexivity|].
    split; [split; [exact (munch_rel rsegs _ mem0 _ m1 m0 HR0 MREL ROS MU)|]|].
    { split; [exact (wmono_rel rsegs mem0 _ m1 m0 HR0 MREL ROS WM)|].
      exact (proj2 (bytes_at_rel rsegs m1 m0 _ _ MREL) BZ). }
    split; [exact (p4_sv_ext R regs1 GR SV)|].
    split; [rewrite GR; exact RA|]. split; [rewrite GR; exact FD|]. rewrite GR; exact EO.
Qed.

Section M1.
Variable r_m1 : word -> option byte.
Hypothesis HM1 : munch [(slot_sp E - 16, slot_sp E); (slot_sp E + 40, slot_sp E + 48)] mem0 r_m1 /\
  wmono (ms_segs B) mem0 r_m1 /\ bytes_at (ms_segs B) r_m1 (slot_sp E + 40) (le8 (Z_to_bv 64 0)).

Lemma r_mu1 : munch [(slot_sp E - 16, slot_sp E); (slot_sp E + 40, slot_sp E + 48)] mem0 r_m1 /\
  wmono (ms_segs B) mem0 r_m1.
Proof. destruct HM1 as (MU & WM & _). split; assumption. Qed.

Lemma r_kb1 : p4_kb B mem0 r_m1 (slot_sp E - 16).
Proof.
  destruct r_mu1 as [MU WM]. intros a Ha. apply (rk_mu_kb2 B _ mem0 r_m1 a MU WM); [p4_num; lia|].
  cbn [outside]. split; [lia|split; [lia|exact I]].
Qed.

Lemma r_mr1 : aa_MR (API rc) L0 A0 r_m1 md0.
Proof.
  destruct r_mu1 as [MU WM]. destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & Hmat).
  apply (mr_frame _ _ (aa_laws (API rc)) L0 A0 mem0 r_m1 md0 md0 HMR).
  - intros a HO. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HMR HO) as HA.
    apply (munch_mbyte _ _ _ _ a MU); [p4_num; lia|cbn [outside]; split; [p4_num; lia|split; [p4_num; lia|exact I]]].
  - intros a HO HP. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HMR HO) as HA.
    eapply munch_present; [exact MU| | |exact HP];
      [p4_num; lia|cbn [outside]; split; [p4_num; lia|split; [p4_num; lia|exact I]]].
  - intros p n k HP HK. destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ p n k HMR HP HK) as (PR & B0 & B1 & _).
    eapply munch_present; [exact MU| | |exact PR];
      [p4_num; lia|cbn [outside]; split; [p4_num; lia|split; [p4_num; lia|exact I]]].
  - reflexivity.
  - exact Hh.
  - exact Hl.
  - exact Hmat.
Qed.

Lemma r_ro1 : ro_agree (ms_segs B) r_m1.
Proof.
  destruct r_mu1 as [MU WM]. pose proof r_seg as SEG.
  intros a HA. pose proof (bv_unsigned_in_range 64 a) as AB. change (bv_modulus 64) with (2 ^ 64) in AB.
  pose proof (ro_in_img B SEG (bv_unsigned a) AB) as RI0.
  rewrite Z_to_bv_bv_unsigned, <- SEG in RI0. specialize (RI0 HA).
  pose proof (in_img_low B SEG _ RI0) as AL.
  unfold mrd. rewrite (MU a) by (cbn [outside]; split; [p4_num; lia|split; [p4_num; lia|exact I]]). apply HRO. exact HA.
Qed.

Lemma r_kvals : 0 <= RELAY_REMOVE_K <= 65344 /\ 0 <= CHECK_NO_LOSS_K <= 65344 /\
  0 <= CHECK_SHAPE_ENDS_K <= 65344 /\ 0 <= SOURCE_RESET_K <= 65344.
Proof. repeat split; apply Z.leb_le; vm_compute; reflexivity. Qed.

Lemma r_fd_uniq : forall e2, In e2 (map short_entry es) -> re_fd e2 = re_fd e -> e2 = short_entry e.
Proof.
  intros e2 He2 Hf. pose proof HREL as (_ & _ & _ & _ & NDF & _).
  assert (NDF1 : NoDup (map re_fd (map short_entry es))) by (rewrite map_map; exact NDF).
  apply In_nth_error in He2 as (a & Ha).
  assert (Hb : nth_error (map short_entry es) q = Some (short_entry e)) by (rewrite nth_error_map, Hqe; reflexivity).
  destruct (Nat.eq_dec a q) as [->|N].
  - rewrite Hb in Ha. injection Ha as <-. reflexivity.
  - exfalso. exact (p4_nodup_neq re_fd _ a q e2 (short_entry e) NDF1 Ha Hb N Hf).
Qed.

Lemma r_in_e1 : In (short_entry e) (map short_entry es).
Proof. apply in_map. exact (nth_error_In es q Hqe). Qed.

Lemma r_nd_h : NoDup (G :: bv_unsigned out :: concat (map entry_blocks es) ++ hs_blocks h).
Proof.
  pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NDT). unfold target_addrs in NDT.
  destruct r_q as (_ & Hq2 & _).
  apply NoDup_ListNoDup in NDT. apply NoDup_ListNoDup.
  destruct hj as [|p0 hj0] eqn:EH; [cbn in Hq2; lia|]. rewrite <- EH in *.
  pose proof (p4_perm_concat_map (fun p : hsrc * nat => hs_blocks (fst p)) _ _ (remove_at_perm hj q p0 Hq2)) as P2.
  rewrite (nth_error_nth hj q p0 Hqh) in P2.
  change (concat (map (fun p : hsrc * nat => hs_blocks (fst p)) ((h, i) :: remove_at q hj))) with
    (hs_blocks h ++ concat (map (fun p : hsrc * nat => hs_blocks (fst p)) (remove_at q hj))) in P2.
  assert (P3 : Permutation (G :: bv_unsigned out :: concat (map entry_blocks es) ++
      concat (map (fun p : hsrc * nat => hs_blocks (fst p)) hj))
      ((G :: bv_unsigned out :: concat (map entry_blocks es) ++ hs_blocks h) ++
       concat (map (fun p : hsrc * nat => hs_blocks (fst p)) (remove_at q hj)))).
  { cbn [app]. apply perm_skip, perm_skip. rewrite <- app_assoc. apply Permutation_app_head. exact P2. }
  pose proof (Permutation_NoDup P3 NDT) as N. apply NoDup_app_remove_r in N. exact N.
Qed.

Lemma r_pcost : pair_cost e (h, i) <= K /\ K < 2 ^ 26.
Proof.
  pose proof HREL as (_ & _ & _ & HES & _).
  split; [|unfold INPUT_MAX in Hn; lia].
  apply (Z.le_trans _ (slot_cost es hj)); [|exact Hcost].
  apply pair_cost_le_slot; [exact (p4_nth_combine es hj q e (h, i) Hqe Hqh)|].
  eapply Forall_impl; [|exact HES]. intros x (_ & _ & _ & _ & _ & _ & X7 & _).
  pose proof (Zle_0_nat (length (re_U x))). lia.
Qed.

Definition r_Err (a : Z) : Prop :=
  send_writes true (bv_unsigned out) (bv_unsigned cap) a \/ G_LOCK + 4 <= a < G_LOCK + 8 \/
  G_NSRC <= a < G_NSRC + 4 \/ G <= a < G + SRC_TABLE \/
  ((exists e0, In e0 (map short_entry es) /\ re_fd e0 = re_fd e /\ re_eof e0 = 0) /\
   G_S + SRC_SIZE * Z.of_nat i + 12 <= a < G_S + SRC_SIZE * Z.of_nat i + SRC_SIZE) \/
  (exists e0 q0 m0, In e0 (map short_entry es) /\ re_fd e0 = re_fd e /\ In (q0, m0) (blocks L0 A0) /\
     q0 <= a < q0 + m0 /\ (In q0 (entry_blocks e0) \/ (re_eof e0 = 0 /\ In q0 (hs_blocks h)))).

Definition r_Frr (e' : rentry) (q0 : Z) : Prop :=
  ((exists e0, In e0 (map short_entry es) /\ re_fd e0 = re_fd e /\
     send_live cl br dd (Z.of_nat (length (with_nul (if re_eof e0 =? 0 then lines (hs_state h) (bzs (pending_stream h))
       else []))) + keys_total (re_keys e')) = true) /\ q0 = bv_unsigned out) \/
  (exists e0, In e0 (map short_entry es) /\ re_fd e0 = re_fd e /\
     (In q0 (entry_blocks e0) \/ (re_eof e0 = 0 /\ In q0 (hs_blocks h)))).

Definition r_TOT (e' : rentry) : Z := Z.of_nat (length (with_nul (p4_lines e h))) + keys_total (re_keys e').

Lemma r_blk_img : forall L A m md x k a, aa_MR (API rc) L A m md -> In (x, k) (blocks L A) -> x <= a < x + k ->
  ~ in_img B a.
Proof.
  intros L A m md x k a HM Hin Ha. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & EQ & Hp).
  cbn [fst snd] in EQ. injection EQ as <- <-.
  pose proof (ax_blocks_img r_AX L A m md p k' (a - ptr_addr L p) HM Hp ltac:(lia)) as X.
  replace (ptr_addr L p + (a - ptr_addr L p)) with a in X by lia. exact X.
Qed.

Lemma r_blk_rng : forall L A m md x k, aa_MR (API rc) L A m md -> In (x, k) (blocks L A) ->
  4096 <= x /\ x + k <= @YM05.alloc_ceiling rc.
Proof.
  intros L A m md x k HM Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & EQ & Hp).
  cbn [fst snd] in EQ. injection EQ as <- <-. exact (mr_blocks_range _ _ (aa_laws (API rc)) L A m md p k' HM Hp).
Qed.

Lemma r_blk_dis : forall L A m md x k q0 m0 a, aa_MR (API rc) L A m md -> In (x, k) (blocks L A) ->
  In (q0, m0) (blocks L A) -> q0 <> x -> x <= a < x + k -> ~ (q0 <= a < q0 + m0).
Proof.
  intros L A m md x k q0 m0 a HM H1 H2 N Ha X.
  destruct (blocks_disjoint B (API rc) L A m md x k q0 m0 HM H1 H2 (fun E0 => N (eq_sym E0))); lia.
Qed.

Lemma r_blk_nn : forall L A m md x k, aa_MR (API rc) L A m md -> In (x, k) (blocks L A) -> 0 <= k.
Proof.
  intros L A m md x k HM Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & EQ & Hp).
  cbn [fst snd] in EQ. injection EQ as <- <-. exact (rk_ub_nonneg A p k' (mr_wf _ _ (aa_laws (API rc)) L A m md HM) Hp).
Qed.

Lemma r_nd_pos : forall L A m md x k, aa_MR (API rc) L A m md -> In (x, 0) (blocks L A) -> In (x, k) (blocks L A) ->
  0 < k -> False.
Proof.
  intros L A m md x k HM H0 Hk1 Pk. pose proof (r_ND L A m md HM) as ND.
  assert (ND' : List.NoDup (map fst (blocks L A))) by first [exact ND | exact (proj1 (NoDup_ListNoDup _) ND)].
  pose proof (p4_nodup_fst _ x 0 k ND' H0 Hk1). lia.
Qed.

Lemma r_gimg : forall a, 0x318a0 <= a < 0x31aa0 -> img_plain B a.
Proof. intros a Ha. pose proof HF as (FF & _). exact (p4_glob_plain _ _ _ _ _ _ _ FF a (in_G_bss a Ha)). Qed.

Lemma r_gimg2 : forall a, 0x21620 <= a < 0x21630 -> img_plain B a.
Proof.
  intros a Ha. pose proof HF as (FF & _). apply (p4_glob_plain _ _ _ _ _ _ _ FF a).
  exists 0x21620, 16. split; [left; reflexivity|lia].
Qed.

Lemma r_nd_mid : forall {X} (l1 l2 : list X) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof. intros X l1 l2 x ND H1 H2. exact (hf_nodup_disj l1 l2 x ND H1 H2). Qed.

Lemma r_nd_split : List.NoDup (G :: bv_unsigned out :: entry_blocks e ++ hs_blocks h ++
  concat (map entry_blocks (remove_at q es)) ++ concat (map (fun p : hsrc * nat => hs_blocks (fst p)) (remove_at q hj))).
Proof.
  pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NDT). unfold target_addrs in NDT.
  destruct r_q as (Hq1 & Hq2 & _).
  apply NoDup_ListNoDup in NDT.
  pose proof (p4_perm_concat_map entry_blocks _ _ (remove_at_perm es q no_entry Hq1)) as P1.
  rewrite (nth_error_nth es q no_entry Hqe) in P1.
  pose proof (p4_perm_concat_map (fun p : hsrc * nat => hs_blocks (fst p)) _ _ (remove_at_perm hj q (h, i) Hq2)) as P2.
  rewrite (nth_error_nth hj q (h, i) Hqh) in P2.
  change (concat (map entry_blocks (e :: remove_at q es))) with
    (entry_blocks e ++ concat (map entry_blocks (remove_at q es))) in P1.
  change (concat (map (fun p : hsrc * nat => hs_blocks (fst p)) ((h, i) :: remove_at q hj))) with
    (hs_blocks h ++ concat (map (fun p : hsrc * nat => hs_blocks (fst p)) (remove_at q hj))) in P2.
  refine (Permutation_NoDup _ NDT). apply perm_skip, perm_skip.
  eapply Permutation_trans; [apply Permutation_app; [exact P1|exact P2]|].
  rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_swap_app.
Qed.

Lemma r_ta_in : forall y, In y (target_addrs G (bv_unsigned out) es hj) ->
  y = G \/ y = bv_unsigned out \/ In y (entry_blocks e) \/ In y (hs_blocks h) \/
  In y (concat (map entry_blocks (remove_at q es))) \/
  In y (concat (map (fun p : hsrc * nat => hs_blocks (fst p)) (remove_at q hj))).
Proof.
  intros y Hy. destruct r_q as (Hq1 & Hq2 & _). unfold target_addrs in Hy.
  destruct Hy as [<-|[<-|Hy]]; [left; reflexivity|right; left; reflexivity|].
  apply in_app_iff in Hy as [Hy|Hy].
  - pose proof (p4_perm_concat_map entry_blocks _ _ (remove_at_perm es q no_entry Hq1)) as P1.
    rewrite (nth_error_nth es q no_entry Hqe) in P1. apply (Permutation_in y P1) in Hy.
    change (In y (entry_blocks e ++ concat (map entry_blocks (remove_at q es)))) in Hy.
    apply in_app_iff in Hy as [Hy|Hy]; [right; right; left; exact Hy|right; right; right; right; left; exact Hy].
  - pose proof (p4_perm_concat_map (fun p : hsrc * nat => hs_blocks (fst p)) _ _ (remove_at_perm hj q (h, i) Hq2)) as P2.
    rewrite (nth_error_nth hj q (h, i) Hqh) in P2. apply (Permutation_in y P2) in Hy.
    change (In y (hs_blocks h ++ concat (map (fun p : hsrc * nat => hs_blocks (fst p)) (remove_at q hj)))) in Hy.
    apply in_app_iff in Hy as [Hy|Hy]; [right; right; right; left; exact Hy|right; right; right; right; right; exact Hy].
Qed.

Lemma r_ta_eh : forall y, In y (entry_blocks e) \/ In y (hs_blocks h) -> In y (target_addrs G (bv_unsigned out) es hj).
Proof.
  intros y Hy. unfold target_addrs. right. right. destruct Hy as [Hy|Hy]; apply in_or_app; [left|right].
  - apply in_concat. exists (entry_blocks e). split; [apply in_map; exact (nth_error_In es q Hqe)|exact Hy].
  - apply in_concat. exists (hs_blocks h). split; [|exact Hy].
    apply (in_map (fun p : hsrc * nat => hs_blocks (fst p)) _ (h, i)). exact (nth_error_In hj q Hqh).
Qed.

Lemma r_ta_rest : forall y, In y (concat (map entry_blocks (remove_at q es))) \/
  In y (concat (map (fun p : hsrc * nat => hs_blocks (fst p)) (remove_at q hj))) ->
  In y (target_addrs G (bv_unsigned out) es hj).
Proof.
  intros y Hy. destruct r_q as (Hq1 & Hq2 & _). unfold target_addrs. right. right.
  destruct Hy as [Hy|Hy]; apply in_or_app; [left|right].
  - apply in_concat in Hy as (l & Hl & Hy). apply in_map_iff in Hl as (x & <- & Hx).
    apply in_concat. exists (entry_blocks x). split; [apply in_map; exact (p4_in_remove_at es q x Hq1 Hx)|exact Hy].
  - apply in_concat in Hy as (l & Hl & Hy). apply in_map_iff in Hl as (x & <- & Hx).
    apply in_concat. exists (hs_blocks (fst x)). split; [|exact Hy].
    apply (in_map (fun p : hsrc * nat => hs_blocks (fst p))). exact (p4_in_remove_at hj q x Hq2 Hx).
Qed.

Lemma r_nd_facts :
  G <> bv_unsigned out /\ ~ In G (entry_blocks e) /\ ~ In G (hs_blocks h) /\
  ~ In (bv_unsigned out) (entry_blocks e) /\ ~ In (bv_unsigned out) (hs_blocks h) /\
  (forall x, In x (hs_blocks h) -> ~ In x (entry_blocks e)) /\
  (forall x, In x (concat (map entry_blocks (remove_at q es))) \/
             In x (concat (map (fun p : hsrc * nat => hs_blocks (fst p)) (remove_at q hj))) ->
     x <> G /\ x <> bv_unsigned out /\ ~ In x (entry_blocks e) /\ ~ In x (hs_blocks h)).
Proof.
  pose proof r_nd_split as ND.
  apply List.NoDup_cons_iff in ND as [NG ND]. apply List.NoDup_cons_iff in ND as [NO ND].
  split; [intros EQ; apply NG; left; exact (eq_sym EQ)|].
  split; [intros X; apply NG; right; apply in_or_app; left; exact X|].
  split; [intros X; apply NG; right; apply in_or_app; right; apply in_or_app; left; exact X|].
  split; [intros X; apply NO; apply in_or_app; left; exact X|].
  split; [intros X; apply NO; apply in_or_app; right; apply in_or_app; left; exact X|].
  split; [intros x Hh He; exact (r_nd_mid _ _ x ND He (in_or_app _ _ _ (or_introl Hh)))|].
  intros x Hx. assert (Hx' : In x (concat (map entry_blocks (remove_at q es)) ++
    concat (map (fun p : hsrc * nat => hs_blocks (fst p)) (remove_at q hj)))) by (apply in_or_app; exact Hx).
  split; [intros ->; apply NG; right; apply in_or_app; right; apply in_or_app; right; exact Hx'|].
  split; [intros ->; apply NO; apply in_or_app; right; apply in_or_app; right; exact Hx'|].
  split; [intros He; exact (r_nd_mid _ _ x ND He (in_or_app _ _ _ (or_intror Hx')))|].
  intros Hh. rewrite app_assoc in ND. apply (r_nd_mid _ _ x ND (in_or_app _ _ _ (or_intror Hh)) Hx').
Qed.

Definition r_HA : Z := G_S + SRC_SIZE * Z.of_nat i.

Lemma r_i4 : (i < 4)%nat.
Proof. pose proof r_pair as (_ & X & _). exact X. Qed.

Lemma r_svsp : forall R, p4_sv E t K s R -> spZ R = slot_sp E.
Proof.
  intros R ((B2 & _) & _). unfold spZ. change (bv_unsigned (getr R 2) = slot_sp E). rewrite B2.
  apply unsigned_lit. p4_num. lia.
Qed.

Lemma p4_sv_eqv : forall R R', p4_sv E t K s R -> Regs6ss.xregs_eqv (Regs6ss.mkR_of R) R' -> p4_sv E t K s R'.
Proof.
  intros R R' ((B2 & B3 & B4 & B20) & (F19 & F21 & F24 & F25 & F26 & F27) & R8 & R23 & R22 & R9) X.
  split; [split; [|split; [|split]]|split; [split; [|split; [|split; [|split; [|split]]]]|]];
    [etransitivity; [apply (getr_of_eqv _ _ _ X); reflexivity|]; assumption ..|].
  split; [etransitivity; [apply (getr_of_eqv _ _ _ X); reflexivity|]; exact R8|].
  split; [etransitivity; [apply (getr_of_eqv _ _ _ X); reflexivity|]; exact R23|].
  split; [etransitivity; [apply (getr_of_eqv _ _ _ X); reflexivity|]; exact R22|].
  etransitivity; [apply (getr_of_eqv _ _ _ X); reflexivity|]; exact R9.
Qed.

Lemma r_rw_wr : forall m a cs x, rw_cells (ms_segs B) m a cs -> a <= x < a + Z.of_nat (cells_size cs) ->
  writable_at (ms_segs B) m x.
Proof.
  intros m a cs x (_ & _ & _ & W) Hx. unfold writable_at. replace x with (a + (x - a)) by lia.
  exact (W (x - a) ltac:(lia)).
Qed.

Lemma p4_list_pos : forall L A m LA l b x, list_at B L A m LA l b -> In x (list_blocks l) ->
  exists k, 0 < k /\ In (x, k) (blocks L A).
Proof.
  intros L A m LA l b x (_ & _ & AR & _ & _ & FA) Hq. unfold list_blocks in Hq.
  apply in_app_iff in Hq as [Hq|Hq].
  - destruct (hl_cap l =? 0) eqn:EC; [destruct Hq|]. apply Z.eqb_neq in EC. destruct Hq as [<-|[]].
    destruct AR as [(X & _)|(Hc & Hin & _)]; [lia|]. exists (16 * hl_cap l). split; [lia|exact Hin].
  - apply in_map_iff in Hq as (r & <- & Hr). rewrite Forall_forall in FA. destruct (FA r Hr) as (Hin & _).
    exists (Z.of_nat (length (snd r)) + 1). split; [lia|exact Hin].
Qed.

Lemma p4_list_v : forall L A m LA l b, list_at B L A m LA l b -> 0 < hl_cap l ->
  In (hl_v l, 16 * hl_cap l) (blocks L A) /\ In (hl_v l) (list_blocks l).
Proof.
  intros L A m LA l b (_ & _ & AR & _) HC. destruct AR as [(X & _)|(_ & Hin & _)]; [lia|].
  split; [exact Hin|]. unfold list_blocks. rewrite (proj2 (Z.eqb_neq (hl_cap l) 0) ltac:(lia)). left. reflexivity.
Qed.

Lemma p4_hs_pos : forall L A m HA hh x, src_at B L A m HA hh -> In x (hs_blocks hh) ->
  exists k, 0 < k /\ In (x, k) (blocks L A).
Proof.
  intros L A m HA hh x (_ & _ & _ & _ & _ & LP & _ & _ & _ & _ & PIn & _ & _ & _ & _ & LE & LH & _) Hx.
  unfold hs_blocks in Hx. apply in_app_iff in Hx as [Hx|Hx]; [exact (p4_list_pos _ _ _ _ _ _ x LP Hx)|].
  apply in_app_iff in Hx as [Hx|Hx]; [destruct Hx as [<-|[]]; exists 6000; split; [lia|exact PIn]|].
  apply in_app_iff in Hx as [Hx|Hx]; [exact (p4_list_pos _ _ _ _ _ _ x LE Hx)|exact (p4_list_pos _ _ _ _ _ _ x LH Hx)].
Qed.

Lemma p4_nd_kt : forall ks, NoDup (map key_text ks) -> NoDup (keys_texts ks).
Proof.
  intros ks ND. apply NoDup_ListNoDup in ND. apply NoDup_ListNoDup. unfold keys_texts.
  rewrite <- (map_map key_text bzs). apply Finite.Injective_map_NoDup; [|exact ND].
  intros x y H. exact (bzs_inj x y H).
Qed.

Lemma p4_kt0 : forall ks, keys_total ks = 0 -> ks = [].
Proof.
  intros [|k ks] H; [reflexivity|]. exfalso. pose proof (keys_total_nonneg ks).
  change (Z.of_nat (length (key_text k)) + 5 + keys_total ks = 0) in H. lia.
Qed.

Section RR.
Variables (R1 R2 : bvmap 5 word) (L1 : layout) (A1 : astate) (mem2 : word -> option byte) (md1 : Model)
  (OUT' CAP' : Z) (junk0 junk' LB : list byte) (e' : rentry) (h' : hsrc) (tail' : list byte) (qs1 : list sptr).
Hypothesis SV1 : p4_sv E t K s R1.
Hypothesis EO1 : getr R1 18 = Z_to_bv 64 (p4_rflag (re_eof e)).
Hypothesis OD0 : (bv_unsigned cap = 0 /\ bv_unsigned out = 0 /\ bv_unsigned nout = 0 /\ @nil byte = []) \/
  (0 < bv_unsigned cap /\ bv_unsigned nout <= bv_unsigned cap /\ In (bv_unsigned out, bv_unsigned cap) (blocks L0 A0) /\
   fresh_block B (bv_unsigned out) (bv_unsigned cap) /\ bytes_at (ms_segs B) r_m1 (bv_unsigned out) ([] ++ junk0) /\
   Z.of_nat (length (@nil byte)) = bv_unsigned nout /\
   Z.of_nat (length junk0) = bv_unsigned cap - bv_unsigned nout).
Hypothesis RP1 : relay_post (rc := rc) B (API rc) RELAY_REMOVE_K r_Err (r_Frr e') L0 A0 R1 r_m1 md0 L1 A1 R2 mem2 md1.
Hypothesis INI1 : st_init_done A1 = true.
Hypothesis RI1 : p4_lv1 F RI E K L0 A0 G (bv_unsigned out) (map short_entry es) hj (send_live cl br dd 1)
  (bv_unsigned mx) (bv_unsigned cap) r_cap1 (short_entry e) h L1 A1 qs1.
Hypothesis QL1 : (send_live cl br dd (r_TOT e') = true ->
    live_at L1 A1 (resolveF qs1 (remove_entry_out (send_live cl br dd 1) (bv_unsigned mx) 0 (bv_unsigned cap)
      (short_entry e) h 0 (drain_start (known_at L0 A0) (known_at L0 A0 (bv_unsigned out)) (short_entry e) h)))
      OUT' CAP') /\
  (re_eof e = 0 -> src_links L1 A1 qs1 (known_at L0 A0) (after_drain_adr (send_live cl br dd 1) (bv_unsigned mx) 0
     (bv_unsigned cap) (short_entry e) h 0 (drain_start (known_at L0 A0) (known_at L0 A0 (bv_unsigned out))
       (short_entry e) h)) h').
Hypothesis RO2 : ro_agree (ms_segs B) mem2.
Hypothesis LK2 : rw_cells (ms_segs B) mem2 G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Hypothesis WK2 : bytes_at (ms_segs B) mem2 G_WAKE1 (le4 (Z_to_bv 64 (-1))).
Hypothesis GS2 : rw_cells (ms_segs B) mem2 G_SRC [C8 (Z_to_bv 64 G)].
Hypothesis GIN2 : In (G, SRC_TABLE) (blocks L1 A1).
Hypothesis CL2 : rw_cells (ms_segs B) mem2 G_CLIENT [C4 (Z_to_bv 64 cl)].
Hypothesis ER2 : exists ev', rw_cells (ms_segs B) mem2 (errno_addr B) [C4 ev'].
Hypothesis NS2 : rw_cells (ms_segs B) mem2 G_NSRC
  [C4 (Z_to_bv 64 (Z.of_nat (length (map short_entry es)) - 1)); C4 (Z_to_bv 64 16)].
Hypothesis TB2 : table_at B mem2 G (remove_at q (map short_entry es)) tail'.
Hypothesis FDe' : re_fd e' = re_fd e.
Hypothesis EOe' : re_eof e' = re_eof e.
Hypothesis EOF0 : re_eof e = 0 ->
  src_at B L1 A1 mem2 (G_S + SRC_SIZE * Z.of_nat i) h' /\ hs_eintr h' = 0 /\ hl_recs (hs_pending h') = [] /\
  hs_off h' = 0 /\
  map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (p4_lines e h) /\
  hs_held h' = hs_held h /\ NoDup (keys_texts (re_keys e')) /\
  same_set (keys_texts (re_keys e')) (upds (keys_texts (re_keys (short_entry e))) (p4_lines e h)).
Hypothesis EOF1 : re_eof e = 1 -> re_keys e' = re_keys (short_entry e).
Hypothesis ECA1 : re_eof e = 0 ->
  hl_cap (hs_expected h') = ds_ecap (drain_fin (send_live cl br dd 1) (bv_unsigned mx) 0 (bv_unsigned cap) (short_entry e) h).
Hypothesis PPK1 : re_eof e = 0 ->
  hl_v (hs_pending h') = hl_v (hs_pending h) /\ hl_cap (hs_pending h') = hl_cap (hs_pending h) /\
  hs_partial h' = hs_partial h.
Hypothesis LB2 : bzs LB = with_nul (p4_lines e h).
Hypothesis BR2 : rw_cells (ms_segs B) mem2 G_BROKEN
  [C1 (Z_to_bv 8 (if send_off cl br (r_TOT e') then br else dd))].
Hypothesis EI2 : rw_cells (ms_segs B) mem2 G_EINTR
  [C1 (Z_to_bv 8 (if send_off cl br (r_TOT e') then ei else 0))].
Hypothesis BK2a : forall q0 m, In (q0, m) (blocks L0 A0) -> q0 <> bv_unsigned out ->
  ~ In q0 (entry_blocks (short_entry e)) -> (re_eof e = 0 -> ~ In q0 (hs_blocks h)) -> In (q0, m) (blocks L1 A1).
Hypothesis BK2b : forall q0 m, In (q0, m) (blocks L0 A0) -> 0 < m -> q0 <> bv_unsigned out ->
  ~ In q0 (entry_blocks (short_entry e)) -> (re_eof e = 0 -> ~ In q0 (hs_blocks h)) ->
  q0 <> OUT' /\ (re_eof e = 0 -> ~ In q0 (hs_blocks h')).
Hypothesis ND2 : re_eof e = 0 -> NoDup (OUT' :: hs_blocks h').
Hypothesis BK2c : forall q0 m, In (q0, m) (blocks L1 A1) ->
  (In (q0, m) (blocks L0 A0) /\ q0 <> bv_unsigned out /\ ~ In q0 (entry_blocks (short_entry e)) /\
   (re_eof e = 0 -> ~ In q0 (hs_blocks h))) \/ (re_eof e = 0 /\ In q0 (hs_blocks h')) \/ q0 = OUT'.
Hypothesis LV0 : send_live cl br dd (r_TOT e') = false ->
  rw_cells (ms_segs B) mem2 G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] /\
  (0 < bv_unsigned cap -> In (bv_unsigned out, bv_unsigned cap) (blocks L1 A1) /\
     bytes_at (ms_segs B) mem2 (bv_unsigned out) ([] ++ junk0)) /\ OUT' = bv_unsigned out.
Hypothesis LV1 : send_live cl br dd (r_TOT e') = true ->
  bv_unsigned nout + r_TOT e' <= CAP' /\ CAP' <= Z.max (bv_unsigned cap) (2 * (bv_unsigned nout + r_TOT e')) /\
  In (OUT', CAP') (blocks L1 A1) /\ fresh_block B OUT' CAP' /\
  bytes_at (ms_segs B) mem2 OUT' ([] ++ LB ++ keys_out (re_keys e') ++ junk') /\
  Z.of_nat (length junk') = CAP' - bv_unsigned nout - r_TOT e' /\
  rw_cells (ms_segs B) mem2 G_OUTV
    [C8 mx; C8 (Z_to_bv 64 (bv_unsigned nout + r_TOT e')); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')].
Hypothesis CAPX : (send_live cl br dd (r_TOT e') = true -> CAP' = r_cap1) /\
  (send_live cl br dd (r_TOT e') = false -> r_cap1 = bv_unsigned cap).

Lemma rr_nF : forall x, x <> bv_unsigned out -> ~ In x (entry_blocks e) -> (re_eof e = 0 -> ~ In x (hs_blocks h)) ->
  ~ r_Frr e' x.
Proof.
  intros x N1 N2 N3 [(_ & X)|(e0 & He0 & Hf & X)]; [exact (N1 X)|].
  rewrite (r_fd_uniq e0 He0 Hf) in X. rewrite short_entry_blocks in X.
  destruct X as [X|(X1 & X2)]; [exact (N2 X)|]. exact (N3 X1 X2).
Qed.

Lemma rr_nE_blk : forall x k a, In (x, k) (blocks L0 A0) -> x <= a < x + k -> x <> bv_unsigned out -> x <> G ->
  ~ In x (entry_blocks e) -> (re_eof e = 0 -> ~ In x (hs_blocks h)) -> ~ r_Err a.
Proof.
  intros x k a Hin Ha N1 N2 N3 N4.
  pose proof (r_blk_img _ _ _ _ _ _ a HMR Hin Ha) as NI.
  assert (GI : forall y, 0x318a0 <= y < 0x31aa0 -> in_img B y) by (intros y Hy; exact (proj1 (r_gimg y Hy))).
  pose proof r_pair as (_ & Hi4 & _). cbn [snd] in Hi4.
  intros [X|[X|[X|[X|[(_ & X)|(e0 & q0 & m0 & He0 & Hf & Hq0 & Hr & X)]]]]].
  - unfold send_writes in X. destruct X as [X|[X|[X|(_ & X)]]].
    + apply NI, GI. p4_cst. lia.
    + apply NI, GI. p4_cst. lia.
    + apply NI, GI. p4_cst. lia.
    + pose proof HOUT as ((O1 & j1 & [(C0 & _)|(CP & _ & OIN & _)]) & _); [lia|].
      exact (r_blk_dis _ _ _ _ _ _ _ _ a HMR Hin OIN (fun E0 => N1 (eq_sym E0)) Ha X).
  - apply NI, GI. p4_cst. lia.
  - apply NI, GI. p4_cst. lia.
  - pose proof HREL as (_ & GIN & _).
    exact (r_blk_dis _ _ _ _ _ _ _ _ a HMR Hin GIN (fun E0 => N2 (eq_sym E0)) Ha X).
  - apply NI, GI. p4_cst. lia.
  - rewrite (r_fd_uniq e0 He0 Hf) in X. rewrite short_entry_blocks in X.
    assert (NQ : q0 <> x).
    { intros ->. destruct X as [X|(X1 & X2)]; [exact (N3 X)|exact (N4 X1 X2)]. }
    exact (r_blk_dis _ _ _ _ _ _ _ _ a HMR Hin Hq0 NQ Ha Hr).
Qed.

Lemma rr_bk : forall x, x <> bv_unsigned out -> x <> G -> ~ In x (entry_blocks e) ->
  (re_eof e = 0 -> ~ In x (hs_blocks h)) -> rk_bkept B L0 A0 mem0 L1 A1 mem2 x.
Proof.
  intros x N1 N2 N3 N4 k Hin.
  destruct (rk_rp_kept B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ x k r_mr1 RP1 (rr_nF x N1 N3 N4) Hin) as (H1 & H2).
  split; [exact H1|]. intros y Hy.
  eapply rk_kb2_trans.
  - apply r_kb1. pose proof (r_blk_rng _ _ _ _ _ _ HMR Hin). p4_num. lia.
  - apply H2; [exact Hy|]. exact (rr_nE_blk x k (x + y) Hin ltac:(lia) N1 N2 N3 N4).
Qed.

Lemma rr_sk : forall a, (0 <= a < 2 ^ 21 \/ slot_sp E <= a < 2 ^ 64) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
  ~ scratch_k B RELAY_REMOVE_K R1 a.
Proof.
  intros a Ha HE. pose proof r_kvals as (KV & _). pose proof SV1 as ((B2 & _) & _).
  assert (SP1 : spZ R1 = slot_sp E).
  { unfold spZ. change (bv_unsigned (getr R1 2) = slot_sp E). rewrite B2. apply unsigned_lit. p4_num. lia. }
  unfold scratch_k. rewrite SP1. p4_num. intros [X|X]; [lia|exact (HE X)].
Qed.

Lemma rr_gb : forall a, img_plain B a -> ~ r_Err a -> rk_kb2 B mem0 mem2 a.
Proof.
  intros a P NE. pose proof r_seg as SEG. pose proof (in_img_low B SEG a (proj1 P)) as IL.
  eapply rk_kb2_trans; [apply r_kb1; p4_num; lia|].
  apply (rk_rp_gkept B (API rc) r_AX _ _ _ _ _ _ _ _ _ _ _ _ _ a r_mr1 RP1 (or_introl P) NE).
  apply rr_sk; [lia|]. destruct P as (_ & _ & _ & PE). exact PE.
Qed.

Lemma rr_nE : forall a, in_img B a -> a <> 0x318a4 -> a <> 0x318b0 -> ~ (0x318e0 <= a < 0x318f8) ->
  ~ (0x318fc <= a < 0x31900) -> ~ (0x318b8 <= a < 0x318bc) ->
  (re_eof e = 0 -> ~ (G_S + SRC_SIZE * Z.of_nat i + 12 <= a < G_S + SRC_SIZE * Z.of_nat i + SRC_SIZE)) ->
  ~ r_Err a.
Proof.
  intros a IA N1 N2 N3 N4 N5 N6 [X|[X|[X|[X|[(EX & X)|(e0 & q0 & m0 & He0 & Hf & Hq0 & Hr & X)]]]]].
  - unfold send_writes in X. destruct X as [X|[X|[X|(_ & X)]]]; [p4_cst; lia|p4_cst; lia|p4_cst; lia|].
    pose proof HOUT as ((O1 & j1 & [(C0 & _)|(CP & _ & OIN & _)]) & _); [lia|].
    exact (r_blk_img _ _ _ _ _ _ a HMR OIN X IA).
  - p4_cst. lia.
  - p4_cst. lia.
  - pose proof HREL as (_ & GIN & _). exact (r_blk_img _ _ _ _ _ _ a HMR GIN X IA).
  - destruct EX as (e0 & He0 & Hf & He). rewrite (r_fd_uniq e0 He0 Hf) in He. exact (N6 He X).
  - exact (r_blk_img _ _ _ _ _ _ a HMR Hq0 Hr IA).
Qed.

Lemma r_at1 : rw_cells (ms_segs B) r_m1 (slot_sp E + 40) [C8 (Z_to_bv 64 0)].
Proof.
  pose proof HIK as (_ & _ & _ & IK4). destruct HM1 as (MU & WM & BZ).
  split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BZ.
  - cbn [cells_size csize]. split; [p4_num; lia|]. split; [p4_num; lia|]. intros k0 Hk0.
    apply WM. apply IK4. unfold lib_scratch. left. p4_num. lia.
Qed.

Lemma rr_at : rw_cells (ms_segs B) mem2 (slot_sp E + 40) [C8 (Z_to_bv 64 0)].
Proof.
  apply (rk_rw_kb2 B r_m1); [exact r_at1|]. intros k0 Hk0. cbn [cells_size csize] in Hk0.
  apply (rk_rp_gkept B (API rc) r_AX _ _ _ _ _ _ _ _ _ _ _ _ _ _ r_mr1 RP1); [right; p4_num; lia| |].
  - intros [X|[X|[X|[X|[(_ & X)|(e0 & q0 & m0 & _ & _ & Hq0 & Hr & _)]]]]].
    + unfold send_writes in X. destruct X as [X|[X|[X|(_ & X)]]]; [p4_cst; p4_num; lia|p4_cst; p4_num; lia|
        p4_cst; p4_num; lia|].
      pose proof HOUT as ((O1 & j1 & [(C0 & _)|(CP & _ & OIN & _)]) & _); [lia|].
      pose proof (r_blk_rng _ _ _ _ _ _ HMR OIN). p4_num. lia.
    + p4_cst. p4_num. lia.
    + p4_cst. p4_num. lia.
    + pose proof HREL as (_ & GIN & _). pose proof (r_blk_rng _ _ _ _ _ _ HMR GIN). p4_num. p4_cst. lia.
    + pose proof r_pair as (_ & Hi4 & _). cbn [snd] in Hi4. p4_cst. p4_num. lia.
    + pose proof (r_blk_rng _ _ _ _ _ _ HMR Hq0). p4_num. lia.
  - apply rr_sk; [p4_num; lia|]. rewrite r_ea. p4_num. lia.
Qed.

Definition r_lv : bool := send_live cl br dd (r_TOT e').
Definition r_no2 : word := if r_lv then Z_to_bv 64 (bv_unsigned nout + r_TOT e') else nout.
Definition r_cap2 : word := if r_lv then Z_to_bv 64 CAP' else cap.
Definition r_out2 : word := if r_lv then Z_to_bv 64 OUT' else out.
Definition r_ob : list byte := if r_lv then LB ++ keys_out (re_keys e') else [].
Definition r_h1 : hsrc := if re_eof e =? 0 then h' else h.

Lemma rr_outv : rw_cells (ms_segs B) mem2 G_OUTV [C8 mx; C8 r_no2; C8 r_cap2; C8 r_out2].
Proof.
  unfold r_no2, r_cap2, r_out2. destruct r_lv eqn:LV.
  - destruct (LV1 LV) as (_ & _ & _ & _ & _ & _ & X). exact X.
  - exact (proj1 (LV0 LV)).
Qed.

Lemma rr_wn : Z.of_nat (length (with_nul (p4_lines e h))) <=
  (if re_skip e =? 0 then re_used e else 0) + Z.of_nat (length (pending_stream h)).
Proof.
  pose proof r_pair as PO. cbv zeta in PO. cbn [fst snd] in PO. destruct PO as (SRC & _ & _ & SKU & _).
  pose proof r_eok as (_ & _ & _ & _ & _ & _ & EUL & _).
  unfold p4_lines. destruct (re_eof e =? 0) eqn:EQ.
  - apply Z.eqb_eq in EQ. destruct (SKU EQ) as [S1 S2].
    pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OV & _).
    exact (reads_bound e h S1 S2 OV EUL).
  - cbn [with_nul map concat length]. pose proof (Zle_0_nat (length (pending_stream h))).
    pose proof (Zle_0_nat (length (re_U e))). destruct (re_skip e =? 0); lia.
Qed.

Lemma rr_eof01 : re_eof e = 0 \/ re_eof e = 1.
Proof. pose proof r_eok as (X & _). exact X. Qed.

Lemma rr_keys : keys_total (re_keys e') <= keys_total (re_keys e) + Z.of_nat (length (with_nul (p4_lines e h))).
Proof.
  destruct rr_eof01 as [E0|E1].
  - destruct (EOF0 E0) as (_ & _ & _ & _ & _ & _ & NDK & SSK').
    cbn [short_entry re_keys] in SSK'. rewrite short_keys_texts in SSK'. exact (p4_keys_upds _ _ _ NDK SSK').
  - rewrite (EOF1 E1). cbn [short_entry re_keys]. rewrite short_keys_total.
    pose proof (Zle_0_nat (length (with_nul (p4_lines e h)))). lia.
Qed.

Lemma rr_tot : 0 <= r_TOT e' <= 2 * K.
Proof.
  pose proof rr_wn as W. pose proof rr_keys as KK. pose proof r_pcost as (PC & _).
  unfold pair_cost in PC. cbn [fst] in PC. unfold r_TOT.
  pose proof (keys_total_nonneg (re_keys e')). pose proof (keys_total_nonneg (re_keys e)).
  pose proof (Zle_0_nat (length (with_nul (p4_lines e h)))). pose proof (Zle_0_nat (length (pending_stream h))).
  pose proof r_eok as (_ & _ & _ & _ & _ & _ & EUL & _). pose proof (Zle_0_nat (length (re_U e))).
  destruct (re_skip e =? 0); lia.
Qed.

Lemma rr_no2 : bv_unsigned r_no2 = if r_lv then r_TOT e' else 0.
Proof.
  pose proof rr_tot. pose proof r_pcost as (_ & K26). unfold r_no2. rewrite HNO.
  destruct r_lv; [apply unsigned_lit; lia|exact HNO].
Qed.

Lemma rr_out2 : bv_unsigned r_out2 = OUT'.
Proof.
  unfold r_out2. destruct r_lv eqn:LV.
  - destruct (LV1 LV) as (C1 & _ & _ & (F0 & F1 & _) & _). pose proof rr_tot. rewrite HNO in C1.
    apply unsigned_lit. pose proof (@YM05.alloc_ceiling_lt rc). lia.
  - symmetry. exact (proj2 (proj2 (LV0 LV))).
Qed.

Lemma rr_live_pos : r_lv = true -> 0 < r_TOT e'.
Proof.
  unfold r_lv, send_live, send_off. pose proof rr_tot. intros X.
  destruct (r_TOT e' =? 0) eqn:T0; [rewrite orb_true_r in X; discriminate|]. apply Z.eqb_neq in T0. lia.
Qed.

Lemma rr_output : output_at (rc := rc) B L1 A1 mem2 r_no2 r_cap2 r_out2.
Proof.
  pose proof rr_tot as TT. pose proof r_pcost as (_ & K26). pose proof HOUT as (_ & OCAP).
  unfold output_at. cbv zeta. rewrite rr_no2, rr_out2.
  unfold r_cap2. destruct r_lv eqn:LV.
  - destruct (LV1 LV) as (C1 & C2 & IN & FR & BY & LJ & _). rewrite HNO in C1, C2, LJ.
    assert (CP : bv_unsigned (Z_to_bv 64 CAP') = CAP').
    { apply unsigned_lit. unfold TBBYTES in *. lia. }
    rewrite CP. split; [|unfold TBBYTES in *; lia].
    exists (LB ++ keys_out (re_keys e')), junk'. right.
    assert (LLB : Z.of_nat (length LB) = Z.of_nat (length (with_nul (p4_lines e h)))).
    { rewrite <- (bzs_length LB), LB2. reflexivity. }
    pose proof (rr_live_pos LV) as TP.
    split; [lia|]. split; [lia|]. split; [exact IN|]. split; [exact FR|].
    split; [rewrite <- app_assoc; exact BY|]. split; [|lia].
    rewrite length_app, Nat2Z.inj_add, LLB, keys_out_length. reflexivity.
  - destruct (LV0 LV) as (_ & BK & EO). rewrite EO. split; [|exact OCAP].
    pose proof HOUT as ((O1 & j1 & OD) & _). exists [], junk0.
    destruct OD0 as [(C0 & O0 & N0 & _)|(CP & NO & _ & FR & _ & _ & LJ)]; [left; repeat split; lia|right].
    destruct (BK CP) as (IN & BY). rewrite HNO in LJ. split; [exact CP|]. split; [lia|]. split; [exact IN|].
    split; [exact FR|]. split; [exact BY|]. split; [reflexivity|exact LJ].
Qed.

Lemma rr_h1 : src_at B L1 A1 mem2 (G_S + SRC_SIZE * Z.of_nat i) r_h1.
Proof.
  unfold r_h1. destruct (re_eof e =? 0) eqn:EQ.
  - apply Z.eqb_eq in EQ. exact (proj1 (EOF0 EQ)).
  - apply Z.eqb_neq in EQ. pose proof r_pair as PO. cbv zeta in PO. cbn [fst snd] in PO.
    destruct PO as (SRC & Hi4 & _).
    pose proof r_nd_facts as (NGO & NGE & NGH & NOE & NOH & NHE & _).
    apply (rk_src_at_kept B L0 A0 mem0 L1 A1 mem2 _ h SRC).
    + intros k0 Hk0.
      assert (Hi : (i < 4)%nat) by exact Hi4.
      assert (IA : img_plain B (G_S + SRC_SIZE * Z.of_nat i + k0)) by (apply r_gimg; p4_cst; lia).
      apply rr_gb; [exact IA|].
      apply rr_nE; [exact (proj1 IA)|p4_cst; lia|p4_cst; lia|p4_cst; lia|p4_cst; lia|p4_cst; lia|intros X; lia].
    + intros x Hx. apply rr_bk; [intros ->; exact (NOH Hx)|intros ->; exact (NGH Hx)|exact (NHE x Hx)|
        intros X; lia].
Qed.

Lemma rr_mr2 : aa_MR (API rc) L1 A1 mem2 md1 /\ WF A1 /\ bounded A1.
Proof. destruct RP1 as (M & W & Bd & _). tauto. Qed.

Lemma rr_ik : image_kept (rc := rc) B E mem2 /\ stack_mid B E mem2.
Proof.
  destruct r_mu1 as [MU WM].
  destruct (p4_keep_mu B API LS SH SK ra empty rc fx j E CS mem0 r_m1 HF MU WM HIK HST) as [IK1 ST1].
  pose proof r_kvals as (KV & _). pose proof r_i4 as Hi.
  apply (p4_keep_post B API LS SH SK ra empty rc fx j E CS RELAY_REMOVE_K r_Err (r_Frr e') L0 A0 R1 r_m1 md0
    L1 A1 R2 mem2 md1 HF RP1 r_mr1 (r_svsp R1 SV1) KV); [| |exact IK1|exact ST1].
  - intros a [X|[X|[X|[X|[(_ & X)|(e0 & q0 & m0 & _ & _ & Hq0 & Hr & _)]]]]].
    + unfold send_writes in X. destruct X as [X|[X|[X|(_ & X)]]];
        [left; apply in_G_bss; p4_cst; lia|left; apply in_G_bss; p4_cst; lia|left; apply in_G_bss; p4_cst; lia|].
      right; left. pose proof HOUT as ((O1 & j1 & [(C0 & _)|(CP & _ & OIN & _)]) & _); [lia|].
      pose proof (r_blk_rng _ _ _ _ _ _ HMR OIN). split; [lia|exact (r_blk_img _ _ _ _ _ _ a HMR OIN X)].
    + left; apply in_G_bss; p4_cst; lia.
    + left; apply in_G_bss; p4_cst; lia.
    + right; left. pose proof HREL as (_ & GIN & _). pose proof (r_blk_rng _ _ _ _ _ _ HMR GIN).
      split; [p4_cst; lia|exact (r_blk_img _ _ _ _ _ _ a HMR GIN X)].
    + left; apply in_G_bss; p4_cst; lia.
    + right; left. pose proof (r_blk_rng _ _ _ _ _ _ HMR Hq0).
      split; [lia|exact (r_blk_img _ _ _ _ _ _ a HMR Hq0 Hr)].
  - intros a Ha. right. apply (r_rw_wr _ _ _ a rr_at). cbn [cells_size csize]. lia.
Qed.

Definition r_E1 : hlist := hs_expected r_h1.
Definition r_H1 : hlist := hs_held r_h1.
Definition r_A1 : Z := if gn =? 0 then 0 + Z.of_nat (length (bstream r_E1)) else 0.

Lemma rr_held1 : r_H1 = hs_held h.
Proof.
  unfold r_H1, r_h1. destruct (re_eof e =? 0) eqn:EQ; [|reflexivity]. apply Z.eqb_eq in EQ.
  destruct (EOF0 EQ) as (_ & _ & _ & _ & _ & X & _). exact X.
Qed.

Lemma rr_exp1 : map snd (hl_recs r_E1) = map (map (Z_to_bv 8)) (p4_lines e h).
Proof.
  pose proof r_pair as (_ & _ & _ & _ & _ & _ & EXP0 & _). cbn [fst] in EXP0.
  unfold r_E1, r_h1, p4_lines. destruct (re_eof e =? 0) eqn:EQ.
  - apply Z.eqb_eq in EQ. destruct (EOF0 EQ) as (_ & _ & _ & _ & X & _). unfold p4_lines in X.
    rewrite (proj2 (Z.eqb_eq _ _) EQ) in X. rewrite X, EXP0. reflexivity.
  - rewrite EXP0. reflexivity.
Qed.

Lemma rr_lzr : Forall zrange (p4_lines e h).
Proof. unfold p4_lines. destruct (re_eof e =? 0); [apply p4_lines_zr|constructor]. Qed.

Lemma rr_texts1 : texts r_E1 = p4_lines e h.
Proof. exact (texts_lines r_E1 _ rr_exp1 rr_lzr). Qed.

Lemma rr_bs1 : bstream r_E1 = LB.
Proof. exact (p4_bstream r_E1 _ LB rr_exp1 rr_lzr LB2). Qed.

Lemma rr_lb_len : Z.of_nat (length LB) = Z.of_nat (length (with_nul (p4_lines e h))).
Proof. rewrite <- (bzs_length LB), LB2. reflexivity. Qed.

Lemma rr_hn1 : hl_n r_E1 = Z.of_nat (length (p4_lines e h)).
Proof.
  unfold hl_n. rewrite <- (length_map snd (hl_recs r_E1)), rr_exp1, length_map. reflexivity.
Qed.

Lemma rr_gn : (gn = 0 /\ cl = 3 /\ br = 0 /\ dd = 0) \/ (gn = 1 /\ (cl = -1 \/ br = 1 \/ dd = 1)).
Proof.
  pose proof HGL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HCL & HBR & HGN & HDD & HEI & (G0 & G1) & _).
  destruct HGN as [->| ->]; [left; split; [reflexivity|exact (G0 eq_refl)]|right; split; [reflexivity|exact (G1 eq_refl)]].
Qed.

Lemma rr_lv_gn : r_lv = (gn =? 0) && negb (r_TOT e' =? 0).
Proof.
  pose proof HGL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HCL & HBR & HGN & HDD & _).
  unfold r_lv, send_live, send_off. pose proof HGL as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (G0 & G1) & _).
  destruct HGN as [-> | ->].
  - destruct (G0 eq_refl) as (-> & -> & ->). cbn. destruct (r_TOT e' =? 0); reflexivity.
  - pose proof (G1 eq_refl) as X.
    destruct HCL as [-> | ->]; destruct HBR as [-> | ->]; destruct HDD as [-> | ->]; cbn;
      try reflexivity; try (rewrite andb_false_r; reflexivity); destruct X as [X|[X|X]]; discriminate.
Qed.

Lemma rr_tot0 : r_TOT e' = 0 -> p4_lines e h = [] /\ re_keys e' = [] /\ LB = [].
Proof.
  intros T0. unfold r_TOT in T0. pose proof (keys_total_nonneg (re_keys e')).
  pose proof (Zle_0_nat (length (with_nul (p4_lines e h)))).
  assert (W0 : Z.of_nat (length (with_nul (p4_lines e h))) = 0) by lia.
  split; [exact (p4_with_nul_nil _ W0)|]. split; [apply p4_kt0; lia|].
  pose proof rr_lb_len as LL. destruct LB; [reflexivity|cbn [length] in LL; lia].
Qed.

Lemma rr_skip : gn = 0 -> skipn (Z.to_nat r_A1) r_ob = keys_out (re_keys e').
Proof.
  intros G0. unfold r_A1, r_ob. rewrite G0. cbn [Z.eqb]. rewrite rr_bs1.
  replace (Z.to_nat (0 + Z.of_nat (length LB))) with (length LB) by lia.
  destruct r_lv eqn:LV; [apply skipn_len_app|].
  rewrite rr_lv_gn, G0 in LV. cbn in LV. destruct (r_TOT e' =? 0) eqn:T0; [|discriminate].
  apply Z.eqb_eq in T0. destruct (rr_tot0 T0) as (_ & -> & ->). reflexivity.
Qed.

Lemma rr_cnl_pre : gn = 0 -> exists rest, skipn (Z.to_nat 0) r_ob = bstream r_E1 ++ rest.
Proof.
  intros G0. rewrite rr_bs1. unfold r_ob. destruct r_lv eqn:LV; [exists (keys_out (re_keys e')); reflexivity|].
  rewrite rr_lv_gn, G0 in LV. cbn in LV. destruct (r_TOT e' =? 0) eqn:T0; [|discriminate].
  apply Z.eqb_eq in T0. destruct (rr_tot0 T0) as (_ & _ & ->). exists []. reflexivity.
Qed.

Lemma rr_ob_len : Z.of_nat (length r_ob) = bv_unsigned r_no2.
Proof.
  rewrite rr_no2. unfold r_ob. destruct r_lv; [|reflexivity].
  rewrite length_app, Nat2Z.inj_add, rr_lb_len, keys_out_length. reflexivity.
Qed.

Lemma rr_A1_le : 0 <= r_A1 <= bv_unsigned r_no2.
Proof.
  rewrite rr_no2. pose proof rr_tot. unfold r_A1. rewrite rr_bs1, rr_lb_len.
  pose proof (Zle_0_nat (length (with_nul (p4_lines e h)))). pose proof (keys_total_nonneg (re_keys e')).
  destruct (gn =? 0) eqn:G0; [|destruct r_lv; lia]. apply Z.eqb_eq in G0.
  destruct r_lv eqn:LV; [unfold r_TOT; lia|].
  rewrite rr_lv_gn, G0 in LV. cbn in LV. destruct (r_TOT e' =? 0) eqn:T0; [|discriminate].
  apply Z.eqb_eq in T0. unfold r_TOT in T0. lia.
Qed.

Lemma rr_SRC0 : src_at B L0 A0 mem0 r_HA h.
Proof. pose proof r_pair as (X & _). exact X. Qed.

Lemma rr_nh1 : forall x k, In (x, k) (blocks L0 A0) -> x <> bv_unsigned out -> ~ In x (entry_blocks e) ->
  ~ In x (hs_blocks h) -> In (x, k) (blocks L1 A1) -> ~ In x (hs_blocks r_h1).
Proof.
  intros x k H0 N1 N2 N3 H1 X. unfold r_h1 in X. destruct (re_eof e =? 0) eqn:EQ; [|exact (N3 X)].
  apply Z.eqb_eq in EQ. pose proof rr_mr2 as (M1 & _).
  destruct (p4_hs_pos _ _ _ _ _ x rr_h1 ltac:(unfold r_h1; rewrite (proj2 (Z.eqb_eq _ _) EQ); exact X))
    as (k' & Pk' & Hk').
  destruct (Z_lt_le_dec 0 k) as [Pk|Pk].
  - refine (proj2 (BK2b x k H0 Pk N1 _ (fun _ => N3)) EQ X). rewrite short_entry_blocks. exact N2.
  - assert (k = 0) as -> by (pose proof (r_blk_nn _ _ _ _ _ _ M1 H1); lia).
    exact (r_nd_pos _ _ _ _ _ _ M1 H1 Hk' Pk').
Qed.

Lemma rr_out_h1 : ~ In OUT' (hs_blocks r_h1).
Proof.
  pose proof r_nd_facts as (NGO & NGE & NGH & NOE & NOH & NHE & _).
  unfold r_h1. destruct (re_eof e =? 0) eqn:EQ.
  - apply Z.eqb_eq in EQ. pose proof (ND2 EQ) as ND. apply NoDup_ListNoDup in ND.
    apply List.NoDup_cons_iff in ND as [X _]. exact X.
  - apply Z.eqb_neq in EQ. intros X. destruct r_lv eqn:LV.
    + destruct (p4_hs_pos _ _ _ _ _ _ rr_SRC0 X) as (k & Pk & Hk1).
      refine (proj1 (BK2b OUT' k Hk1 Pk _ _ (fun Z0 => False_ind _ (EQ Z0))) eq_refl).
      * intros E0. apply NOH. rewrite <- E0. exact X.
      * rewrite short_entry_blocks. exact (NHE _ X).
    + unfold r_lv in LV. rewrite (proj2 (proj2 (LV0 LV))) in X. exact (NOH X).
Qed.

Lemma rr_G_h1 : ~ In G (hs_blocks r_h1).
Proof.
  pose proof r_nd_facts as (NGO & NGE & NGH & NOE & NOH & NHE & _). pose proof HREL as (_ & GIN & _).
  apply (rr_nh1 G SRC_TABLE GIN NGO NGE NGH GIN2).
Qed.

Lemma rr_ndk : NoDup (keys_texts (re_keys e')).
Proof.
  destruct rr_eof01 as [E0|E1].
  - destruct (EOF0 E0) as (_ & _ & _ & _ & _ & _ & X & _). exact X.
  - rewrite (EOF1 E1). cbn [short_entry re_keys]. rewrite short_keys_texts.
    pose proof r_eok as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDT & _). exact (p4_nd_kt _ NDT).
Qed.

Lemma rr_ss : same_set (keys_texts (re_keys e')) (upds (texts (hs_held h)) (p4_lines e h)).
Proof.
  pose proof r_pair as (_ & _ & _ & _ & SSK & _). cbn [fst] in SSK.
  destruct rr_eof01 as [E0|E1].
  - destruct (EOF0 E0) as (_ & _ & _ & _ & _ & _ & _ & X). cbn [short_entry re_keys] in X.
    rewrite short_keys_texts in X. exact (p4_held_set _ _ _ _ SSK X).
  - rewrite (EOF1 E1). cbn [short_entry re_keys]. rewrite short_keys_texts.
    assert (NZ : re_eof e <> 0) by lia. unfold p4_lines. rewrite (proj2 (Z.eqb_neq _ _) NZ). exact SSK.
Qed.

Definition r_Ecnl (AT a : Z) : Prop :=
  r_HA + 64 <= a < r_HA + 96 \/ AT <= a < AT + 8 \/
  (0 < hl_cap r_E1 /\ hl_v r_E1 <= a < hl_v r_E1 + 16 * hl_cap r_E1) \/
  (0 < hl_cap r_H1 /\ hl_v r_H1 <= a < hl_v r_H1 + 16 * hl_cap r_H1).
Definition r_Fcnl (x : Z) : Prop := In x (map fst (hl_recs r_E1) ++ list_blocks r_H1).

Lemma rr_F1 : forall x, r_Fcnl x -> In x (hs_blocks r_h1).
Proof.
  intros x Hx. unfold r_Fcnl in Hx. unfold hs_blocks. apply in_app_iff in Hx as [Hx|Hx].
  - apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. unfold list_blocks.
    apply in_or_app. right. exact Hx.
  - apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hx.
Qed.

Section CNL.
Variables (R3 R4 : bvmap 5 word) (L2 : layout) (A2 : astate) (mem3 : word -> option byte) (md2 : Model)
  (E' H' : hlist) (qs2 : list sptr).
Hypothesis SV3 : p4_sv E t K s R3.
Hypothesis AT3 : bv_unsigned (getr R3 11) = slot_sp E + 40.
Hypothesis RP3 : relay_post (rc := rc) B (API rc) CHECK_NO_LOSS_K (r_Ecnl (bv_unsigned (getr R3 11))) r_Fcnl
  L1 A1 R3 mem2 md1 L2 A2 R4 mem3 md2.
Hypothesis INI3 : st_init_done A2 = true.
Hypothesis RI3 : p4_lv2 F RI E K L0 A0 G (bv_unsigned out) (map short_entry es) hj (bv_unsigned cap) OUT' r_cap1
  (short_entry e) h L1 A1 r_h1 L2 A2 qs2.
Hypothesis SHR3 : sh_real L2 qs2 (check_no_loss_sh 0 (sh_of (known_at L1 A1) (hs_held r_h1))
  (map (shr (known_at L1 A1)) (hl_recs (hs_expected r_h1)))) H'.
Hypothesis SHL3 : sh_live A2 qs2 (check_no_loss_sh 0 (sh_of (known_at L1 A1) (hs_held r_h1))
  (map (shr (known_at L1 A1)) (hl_recs (hs_expected r_h1)))).
Hypothesis RO3 : ro_agree (ms_segs B) mem3.
Hypothesis SR3 : src_at B L2 A2 mem3 r_HA (set_exp_held r_h1 E' H').
Hypothesis ER3 : hl_recs E' = [].
Hypothesis EV3 : hl_v E' = hl_v r_E1.
Hypothesis EC3 : hl_cap E' = hl_cap r_E1.
Hypothesis NDH3 : NoDup (texts H').
Hypothesis TH3 : texts H' = upds (texts r_H1) (texts r_E1).
Hypothesis AC3 : rw_cells (ms_segs B) mem3 (bv_unsigned (getr R3 11)) [C8 (Z_to_bv 64 r_A1)].
Hypothesis GN3 : bytes_at (ms_segs B) mem3 G_NOUT (le8 r_no2).
Hypothesis GG3 : bytes_at (ms_segs B) mem3 G_GONE [Z_to_bv 8 gn].
Hypothesis GO3 : bytes_at (ms_segs B) mem3 G_OUT (le8 r_out2).
Hypothesis OB3 : bytes_at (ms_segs B) mem3 (bv_unsigned r_out2) r_ob.
Hypothesis BK3b : forall q0 m, In (q0, m) (blocks L2 A2) ->
  (In (q0, m) (blocks L1 A1) /\ (0 < m -> ~ r_Fcnl q0)) \/ In q0 (list_blocks H').
Hypothesis BK3c : forall q0 m, In (q0, m) (blocks L1 A1) -> 0 < m -> ~ r_Fcnl q0 -> ~ In q0 (list_blocks H').

Definition r_h2 : hsrc := set_exp_held r_h1 E' H'.

Lemma cn_mr : aa_MR (API rc) L2 A2 mem3 md2 /\ WF A2 /\ bounded A2.
Proof. destruct RP3 as (M & W & Bd & _). tauto. Qed.

Lemma cn_arr : forall x k a, In (x, k) (blocks L1 A1) -> ~ In x (hs_blocks r_h1) -> x <= a < x + k ->
  ~ r_Ecnl (bv_unsigned (getr R3 11)) a.
Proof.
  intros x k a Hin Nx Ha. pose proof rr_mr2 as (M1 & _). pose proof rr_h1 as S1.
  pose proof S1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LE & LH & _).
  pose proof (r_blk_img _ _ _ _ _ _ a M1 Hin Ha) as NI. pose proof (r_blk_rng _ _ _ _ _ _ M1 Hin) as BR.
  pose proof r_i4 as Hi. rewrite AT3.
  intros [X|[X|[(C & X)|(C & X)]]].
  - apply NI. apply (proj1 (r_gimg a ltac:(unfold r_HA in X; p4_cst; lia))).
  - p4_num. lia.
  - destruct (p4_list_v _ _ _ _ _ _ LE C) as (V1 & V2).
    refine (r_blk_dis _ _ _ _ _ _ _ _ a M1 Hin V1 _ Ha X). intros EQ. apply Nx. rewrite <- EQ.
    unfold hs_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact V2.
  - destruct (p4_list_v _ _ _ _ _ _ LH C) as (V1 & V2).
    refine (r_blk_dis _ _ _ _ _ _ _ _ a M1 Hin V1 _ Ha X). intros EQ. apply Nx. rewrite <- EQ.
    unfold hs_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact V2.
Qed.

Lemma ck1 : forall x k, In (x, k) (blocks L1 A1) -> ~ In x (hs_blocks r_h1) ->
  In (x, k) (blocks L2 A2) /\ (forall a, x <= a < x + k -> rk_kb2 B mem2 mem3 a) /\ ~ In x (hs_blocks r_h2).
Proof.
  intros x k Hin Nx. pose proof rr_mr2 as (M1 & _). pose proof cn_mr as (M2 & _).
  assert (NF : ~ r_Fcnl x) by (intros X; exact (Nx (rr_F1 x X))).
  destruct (rk_rp_kept B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ x k M1 RP3 NF Hin) as (H1 & H2).
  split; [exact H1|]. split.
  { intros a Ha. replace a with (x + (a - x)) by lia. apply H2; [lia|].
    replace (x + (a - x)) with a by lia. exact (cn_arr x k a Hin Nx Ha). }
  unfold r_h2, hs_blocks, set_exp_held. cbn [hs_pending hs_partial hs_expected hs_held].
  intros X. apply in_app_iff in X as [X|X]; [apply Nx; unfold hs_blocks; apply in_or_app; left; exact X|].
  apply in_app_iff in X as [X|X]; [apply Nx; unfold hs_blocks; apply in_or_app; right; apply in_or_app; left; exact X|].
  apply in_app_iff in X as [X|X].
  - unfold list_blocks in X. rewrite ER3, EV3, EC3 in X. cbn [map] in X. rewrite app_nil_r in X.
    apply Nx. unfold hs_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    unfold list_blocks. apply in_or_app. left. exact X.
  - destruct (Z_lt_le_dec 0 k) as [Pk|Pk].
    + exact (BK3c x k Hin Pk NF X).
    + pose proof SR3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LH & _).
      destruct (p4_list_pos _ _ _ _ _ _ x LH X) as (k' & Pk' & Hk').
      assert (k = 0) as -> by (pose proof (r_blk_nn _ _ _ _ _ _ M1 Hin); lia).
      exact (r_nd_pos _ _ _ _ _ _ M2 H1 Hk' Pk').
Qed.

Lemma cg1 : forall a, img_plain B a -> ~ (r_HA <= a < r_HA + 96) -> rk_kb2 B mem2 mem3 a.
Proof.
  intros a P NH. pose proof rr_mr2 as (M1 & _). pose proof r_seg as SEG.
  pose proof (in_img_low B SEG a (proj1 P)) as IL. pose proof rr_h1 as S1.
  pose proof S1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LE & LH & _).
  apply (rk_rp_gkept B (API rc) r_AX _ _ _ _ _ _ _ _ _ _ _ _ _ a M1 RP3 (or_introl P)).
  - rewrite AT3. intros [X|[X|[(C & X)|(C & X)]]]; [lia|p4_num; lia| |].
    + destruct (p4_list_v _ _ _ _ _ _ LE C) as (V1 & _).
      apply (r_blk_img _ _ _ _ _ _ a M1 V1 X). exact (proj1 P).
    + destruct (p4_list_v _ _ _ _ _ _ LH C) as (V1 & _).
      apply (r_blk_img _ _ _ _ _ _ a M1 V1 X). exact (proj1 P).
  - unfold scratch_k. rewrite (r_svsp R3 SV3). pose proof r_kvals as (_ & KV & _).
    destruct P as (_ & _ & _ & PE). p4_num. intros [X|X]; [lia|exact (PE X)].
Qed.

Lemma cn_ik : image_kept (rc := rc) B E mem3 /\ stack_mid B E mem3.
Proof.
  destruct rr_ik as [IK ST]. pose proof r_kvals as (_ & KV & _). pose proof r_i4 as Hi.
  pose proof rr_mr2 as (M1 & _). pose proof rr_h1 as S1.
  pose proof S1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LE & LH & _).
  apply (p4_keep_post B API LS SH SK ra empty rc fx j E CS CHECK_NO_LOSS_K _ r_Fcnl L1 A1 R3 mem2 md1
    L2 A2 R4 mem3 md2 HF RP3 M1 (r_svsp R3 SV3) KV); [| |exact IK|exact ST].
  - rewrite AT3. intros a [X|[X|[(C & X)|(C & X)]]]; unfold r_E1, r_H1 in *.
    + left. apply in_G_bss. unfold r_HA in X. p4_cst. lia.
    + right; right. lia.
    + right; left. destruct (p4_list_v _ _ _ _ _ _ LE C) as (V1 & _). pose proof (r_blk_rng _ _ _ _ _ _ M1 V1).
      split; [lia|exact (r_blk_img _ _ _ _ _ _ a M1 V1 X)].
    + right; left. destruct (p4_list_v _ _ _ _ _ _ LH C) as (V1 & _). pose proof (r_blk_rng _ _ _ _ _ _ M1 V1).
      split; [lia|exact (r_blk_img _ _ _ _ _ _ a M1 V1 X)].
  - intros a Ha. right. apply (r_rw_wr _ _ _ a AC3). cbn [cells_size csize]. rewrite AT3. lia.
Qed.

Lemma p4_ft : forall rs : list (Z * list byte), filter (fun r => prefixb [] (snd r)) rs = rs.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  transitivity (if prefixb [] (snd r) then r :: filter (fun r => prefixb [] (snd r)) rs
                else filter (fun r => prefixb [] (snd r)) rs); [cbn; destruct (prefixb [] (snd r)); reflexivity|].
  rewrite prefixb_nil, IH. reflexivity.
Qed.

Lemma p4_ff0 : forall rs : list (Z * list byte), filter (fun r => negb (prefixb [] (snd r))) rs = [].
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  transitivity (if negb (prefixb [] (snd r)) then r :: filter (fun r => negb (prefixb [] (snd r))) rs
                else filter (fun r => negb (prefixb [] (snd r))) rs); [cbn; destruct (negb (prefixb [] (snd r))); reflexivity|].
  rewrite prefixb_nil, IH. reflexivity.
Qed.

Definition r_Ecse (AT a : Z) : Prop :=
  r_HA + 88 <= a < r_HA + 92 \/ AT <= a < AT + 8 \/ (0 < hl_cap H' /\ hl_v H' <= a < hl_v H' + 16 * hl_cap H').

Lemma cn_lbH : forall x, In x (list_blocks H') -> In x (hs_blocks r_h2).
Proof.
  intros x Hx. unfold r_h2, hs_blocks, set_exp_held. cbn [hs_pending hs_partial hs_expected hs_held].
  apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hx.
Qed.

Lemma p4_sum5 : forall l : list (list Z), 5 * Z.of_nat (length l) <= fold_right Z.add 0 (map (fun y => Z.of_nat (length y) + 5) l).
Proof. induction l as [|y l IH]; cbn [length map fold_right]; [lia|]. pose proof (Zle_0_nat (length y)). lia. Qed.

Lemma cn_hn : hl_n H' < 2 ^ 26.
Proof.
  rewrite <- p4_texts_length.
  assert (I : incl (texts H') (texts (hs_held h) ++ p4_gks (p4_lines e h))).
  { intros y Hy. rewrite TH3, rr_held1, rr_texts1 in Hy. exact (p4_upds_incl _ _ y Hy). }
  pose proof (NoDup_incl_length (proj1 (NoDup_ListNoDup _) NDH3) I) as LI. rewrite length_app in LI.
  pose proof r_pair as (_ & _ & _ & _ & SSK & NDH & _). cbn [fst] in SSK, NDH.
  pose proof (p4_held_len (re_keys e) (hs_held h) NDH SSK) as HL.
  pose proof r_eok as (_ & _ & _ & _ & _ & _ & EUL & _ & _ & _ & _ & _ & _ & _ & EKS).
  assert (K14 : Forall (fun x => 14 <= Z.of_nat (length (key_text x))) (re_keys e)).
  { eapply Forall_impl; [|exact EKS]. intros k (_ & _ & _ & _ & X & _). lia. }
  pose proof (keys_total_count _ K14) as KC. pose proof (p4_gks_sum (p4_lines e h)) as GS.
  pose proof (p4_sum5 (p4_gks (p4_lines e h))) as S5. pose proof rr_wn as WN. pose proof r_pcost as (PC & K26).
  unfold pair_cost in PC. cbn [fst] in PC. pose proof (Zle_0_nat (length (pending_stream h))).
  pose proof (Zle_0_nat (length (re_U e))).
  destruct (re_skip e =? 0); lia.
Qed.

Lemma cn_ends : gn = 0 -> exists rs' ds',
  ends_run [] (hl_recs H') (skipn (Z.to_nat r_A1) r_ob) (want_of [] (hl_recs H')) =
  Some (rs', ds', keys_total (re_keys e')).
Proof.
  intros G0. rewrite (rr_skip G0), <- (app_nil_r (keys_out (re_keys e'))), <- keys_out_length.
  apply p4_ends_some; [exact rr_ndk|exact NDH3| |].
  - change (rtexts (hl_recs H')) with (texts H'). rewrite TH3, rr_held1, rr_texts1. exact rr_ss.
  - pose proof SR3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LH & _).
    change (hs_held (set_exp_held r_h1 E' H')) with H' in LH.
    destruct LH as (_ & _ & _ & _ & _ & FA).
    apply (p4_nozero _ (hl_recs H')).
    + eapply Forall_impl; [|exact FA]. intros r (_ & _ & _ & X & _). exact (proj1 (X eq_refl)).
    + intros y Hy. change (rtexts (hl_recs H')) with (texts H'). rewrite TH3, rr_held1, rr_texts1.
      exact (proj1 (rr_ss y) Hy).
Qed.

Section CSE.
Variables (R5 R6 : bvmap 5 word) (L3 : layout) (A3 : astate) (mem4 : word -> option byte) (md3 : Model)
  (H'' : hlist) (ds : list (Z * list byte)) (c : Z) (qs3 : list sptr).
Hypothesis SV5 : p4_sv E t K s R5.
Hypothesis AT5 : bv_unsigned (getr R5 12) = slot_sp E + 40.
Hypothesis RP5 : relay_post (rc := rc) B (API rc) CHECK_SHAPE_ENDS_K (r_Ecse (bv_unsigned (getr R5 12)))
  (fun x => In x (map fst (hl_recs H'))) L2 A2 R5 mem3 md2 L3 A3 R6 mem4 md3.
Hypothesis INI5 : st_init_done A3 = true.
Hypothesis RI5 : p4_lv3 F RI E K L0 A0 G (bv_unsigned out) (map short_entry es) hj (bv_unsigned cap) OUT' r_cap1
  (short_entry e) h L2 A2 r_h2 L3 A3 qs3.
Hypothesis RO5 : ro_agree (ms_segs B) mem4.
Hypothesis SR5 : src_at B L3 A3 mem4 r_HA (set_held r_h2 H'').
Hypothesis HV5 : hl_v H'' = hl_v H'.
Hypothesis HC5 : hl_cap H'' = hl_cap H'.
Hypothesis CS5 : (gn <> 0 /\ hl_recs H'' = filter (fun r => negb (prefixb [] (snd r))) (hl_recs H') /\
    ds = filter (fun r => prefixb [] (snd r)) (hl_recs H') /\ c = 0) \/
  (gn = 0 /\ ends_run [] (hl_recs H') (skipn (Z.to_nat r_A1) r_ob) (want_of [] (hl_recs H')) = Some (hl_recs H'', ds, c)).
Hypothesis AC5 : rw_cells (ms_segs B) mem4 (bv_unsigned (getr R5 12)) [C8 (Z_to_bv 64 (r_A1 + c))].
Hypothesis GN5 : bytes_at (ms_segs B) mem4 G_NOUT (le8 r_no2).
Hypothesis BK5b : forall q0 m, In (q0, m) (blocks L3 A3) -> In (q0, m) (blocks L2 A2) /\ ~ In q0 (map fst ds).

Definition r_h3 : hsrc := set_held r_h2 H''.

Lemma cs_mr : aa_MR (API rc) L3 A3 mem4 md3 /\ WF A3 /\ bounded A3.
Proof. destruct RP5 as (M & W & Bd & _). tauto. Qed.

Lemma cs_split : forall r, In r (hl_recs H') -> In r (hl_recs H'') \/ In r ds.
Proof.
  intros r Hr. destruct CS5 as [(_ & EH & ED & _)|(_ & ER)].
  - right. rewrite ED, p4_ft. exact Hr.
  - apply in_app_or. exact (Permutation_in r (p4_ends_perm _ _ _ _ _ _ _ ER) Hr).
Qed.

Lemma cs_sub : forall r, In r (hl_recs H'') -> In r (hl_recs H').
Proof.
  intros r Hr. destruct CS5 as [(_ & EH & _)|(_ & ER)].
  - rewrite EH, p4_ff0 in Hr. destruct Hr.
  - apply (Permutation_in r (Permutation_sym (p4_ends_perm _ _ _ _ _ _ _ ER))). apply in_or_app. left. exact Hr.
Qed.

Lemma cs_lb : forall x, In x (list_blocks H'') -> In x (list_blocks H').
Proof.
  intros x Hx. unfold list_blocks in *. rewrite HV5, HC5 in Hx. apply in_app_iff in Hx as [Hx|Hx];
    apply in_or_app; [left; exact Hx|right]. apply in_map_iff in Hx as (r & <- & Hr). apply in_map. exact (cs_sub r Hr).
Qed.

Lemma ck2 : forall x k, In (x, k) (blocks L2 A2) -> ~ In x (hs_blocks r_h2) ->
  In (x, k) (blocks L3 A3) /\ (forall a, x <= a < x + k -> rk_kb2 B mem3 mem4 a) /\ ~ In x (hs_blocks r_h3).
Proof.
  intros x k Hin Nx. pose proof cn_mr as (M2 & _). pose proof SR3 as S2.
  pose proof S2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LH & _).
  assert (NF : ~ In x (map fst (hl_recs H'))).
  { intros X. apply Nx, cn_lbH. unfold list_blocks. apply in_or_app. right. exact X. }
  destruct (rk_rp_kept B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ x k M2 RP5 NF Hin) as (H1 & H2).
  split; [exact H1|]. split.
  { intros a Ha. replace a with (x + (a - x)) by lia. apply H2; [lia|]. replace (x + (a - x)) with a by lia.
    pose proof (r_blk_img _ _ _ _ _ _ a M2 Hin Ha) as NI. pose proof (r_blk_rng _ _ _ _ _ _ M2 Hin) as BR.
    pose proof r_i4 as Hi. unfold r_Ecse. rewrite AT5. intros [X|[X|(C & X)]].
    - apply NI. apply (proj1 (r_gimg a ltac:(unfold r_HA in X; p4_cst; lia))).
    - p4_num. lia.
    - destruct (p4_list_v _ _ _ _ _ _ LH C) as (V1 & V2).
      refine (r_blk_dis _ _ _ _ _ _ _ _ a M2 Hin V1 _ Ha X). intros EQ. apply Nx. rewrite <- EQ. apply cn_lbH. exact V2. }
  unfold r_h3, hs_blocks, set_held. cbn [hs_pending hs_partial hs_expected hs_held].
  intros X. apply in_app_iff in X as [X|X]; [apply Nx; unfold hs_blocks; apply in_or_app; left; exact X|].
  apply in_app_iff in X as [X|X]; [apply Nx; unfold hs_blocks; apply in_or_app; right; apply in_or_app; left; exact X|].
  apply in_app_iff in X as [X|X].
  - apply Nx. unfold hs_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact X.
  - apply Nx. apply cn_lbH. exact (cs_lb x X).
Qed.

Lemma cg2 : forall a, img_plain B a -> ~ (r_HA <= a < r_HA + 96) -> rk_kb2 B mem3 mem4 a.
Proof.
  intros a P NH. pose proof cn_mr as (M2 & _). pose proof r_seg as SEG.
  pose proof (in_img_low B SEG a (proj1 P)) as IL.
  pose proof SR3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LH & _).
  apply (rk_rp_gkept B (API rc) r_AX _ _ _ _ _ _ _ _ _ _ _ _ _ a M2 RP5 (or_introl P)).
  - unfold r_Ecse. rewrite AT5. intros [X|[X|(C & X)]]; [lia|p4_num; lia|].
    destruct (p4_list_v _ _ _ _ _ _ LH C) as (V1 & _). apply (r_blk_img _ _ _ _ _ _ a M2 V1 X). exact (proj1 P).
  - unfold scratch_k. rewrite (r_svsp R5 SV5). pose proof r_kvals as (_ & _ & KV & _).
    destruct P as (_ & _ & _ & PE). p4_num. intros [X|X]; [lia|exact (PE X)].
Qed.

Lemma cs_ik : image_kept (rc := rc) B E mem4 /\ stack_mid B E mem4.
Proof.
  destruct cn_ik as [IK ST]. pose proof r_kvals as (_ & _ & KV & _). pose proof r_i4 as Hi.
  pose proof cn_mr as (M2 & _).
  pose proof SR3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LH & _).
  change (hs_held (set_exp_held r_h1 E' H')) with H' in LH.
  apply (p4_keep_post B API LS SH SK ra empty rc fx j E CS CHECK_SHAPE_ENDS_K _ _ L2 A2 R5 mem3 md2
    L3 A3 R6 mem4 md3 HF RP5 M2 (r_svsp R5 SV5) KV); [| |exact IK|exact ST].
  - unfold r_Ecse. rewrite AT5. intros a [X|[X|(C & X)]].
    + left. apply in_G_bss. unfold r_HA in X. p4_cst. lia.
    + right; right. lia.
    + right; left. destruct (p4_list_v _ _ _ _ _ _ LH C) as (V1 & _). pose proof (r_blk_rng _ _ _ _ _ _ M2 V1).
      split; [lia|exact (r_blk_img _ _ _ _ _ _ a M2 V1 X)].
  - intros a Ha. right. apply (r_rw_wr _ _ _ a AC5). cbn [cells_size csize]. rewrite AT5. lia.
Qed.

Lemma cs_at : Z_to_bv 64 (r_A1 + c) = r_no2.
Proof.
  assert (N0 : nout = Z_to_bv 64 0) by (rewrite <- HNO; symmetry; apply Z_to_bv_bv_unsigned).
  destruct CS5 as [(G1 & _ & _ & C0)|(G0 & ER)].
  - assert (LV : r_lv = false) by (rewrite rr_lv_gn; destruct (gn =? 0) eqn:X; [apply Z.eqb_eq in X; congruence|reflexivity]).
    unfold r_A1, r_no2. rewrite LV, C0, (proj2 (Z.eqb_neq gn 0) G1), N0. reflexivity.
  - destruct (cn_ends G0) as (rs' & ds' & ER').
    rewrite ER in ER'. injection ER' as _ _ ->.
    unfold r_A1, r_no2. rewrite G0, rr_bs1. cbn [Z.eqb]. rewrite HNO.
    destruct r_lv eqn:LV.
    + f_equal. rewrite rr_lb_len. unfold r_TOT. lia.
    + rewrite rr_lv_gn, G0 in LV. cbn in LV. destruct (r_TOT e' =? 0) eqn:T0; [|discriminate].
      apply Z.eqb_eq in T0. destruct (rr_tot0 T0) as (_ & -> & ->). rewrite N0. reflexivity.
Qed.

Section SRS.
Variables (R7 R8 : bvmap 5 word) (L4 : layout) (A4 : astate) (mem5 : word -> option byte) (md4 : Model)
  (qs4 : list sptr).
Hypothesis SV7 : p4_sv E t K s R7.
Hypothesis RP7 : relay_post (rc := rc) B (API rc) SOURCE_RESET_K (fun a => r_HA <= a < r_HA + SRC_SIZE)
  (fun x => src_at B L3 A3 mem4 r_HA r_h3 /\ In x (hs_blocks r_h3)) L3 A3 R7 mem4 md3 L4 A4 R8 mem5 md4.
Hypothesis INI7 : st_init_done A4 = true.
Hypothesis RO7 : ro_agree (ms_segs B) mem5.
Hypothesis Z7 : rw_cells (ms_segs B) mem5 r_HA [CB 96%nat (nulbytes 96)].
Hypothesis RI7 : p4_lv4 RI E K L0 A0 G (bv_unsigned out) (map short_entry es) hj (bv_unsigned cap) OUT' r_cap1
  (short_entry e) h L3 A3 r_h3 L4 A4 qs4.
Hypothesis BK7b : forall q0 m, In (q0, m) (blocks L4 A4) -> In (q0, m) (blocks L3 A3) /\ ~ In q0 (hs_blocks r_h3).

Lemma sr_mr : aa_MR (API rc) L4 A4 mem5 md4 /\ WF A4 /\ bounded A4.
Proof. destruct RP7 as (M & W & Bd & _). tauto. Qed.

Lemma ck3 : forall x k, In (x, k) (blocks L3 A3) -> ~ In x (hs_blocks r_h3) ->
  In (x, k) (blocks L4 A4) /\ (forall a, x <= a < x + k -> rk_kb2 B mem4 mem5 a).
Proof.
  intros x k Hin Nx. pose proof cs_mr as (M3 & _).
  assert (NF : ~ (src_at B L3 A3 mem4 r_HA r_h3 /\ In x (hs_blocks r_h3))) by (intros (_ & X); exact (Nx X)).
  destruct (rk_rp_kept B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ x k M3 RP7 NF Hin) as (H1 & H2).
  split; [exact H1|]. intros a Ha. replace a with (x + (a - x)) by lia. apply H2; [lia|].
  replace (x + (a - x)) with a by lia. intros X. apply (r_blk_img _ _ _ _ _ _ a M3 Hin Ha).
  pose proof r_i4 as Hi. exact (proj1 (r_gimg a ltac:(unfold r_HA in X; p4_cst; lia))).
Qed.

Lemma cg3 : forall a, img_plain B a -> ~ (r_HA <= a < r_HA + 96) -> rk_kb2 B mem4 mem5 a.
Proof.
  intros a P NH. pose proof cs_mr as (M3 & _).
  apply (rk_rp_gkept B (API rc) r_AX _ _ _ _ _ _ _ _ _ _ _ _ _ a M3 RP7 (or_introl P)).
  - unfold SRC_SIZE. exact NH.
  - unfold scratch_k. rewrite (r_svsp R7 SV7). pose proof r_kvals as (_ & _ & _ & KV).
    pose proof r_seg as SEG. pose proof (in_img_low B SEG a (proj1 P)) as IL.
    destruct P as (_ & _ & _ & PE). p4_num. intros [X|X]; [lia|exact (PE X)].
Qed.

Lemma sr_ik : image_kept (rc := rc) B E mem5 /\ stack_mid B E mem5.
Proof.
  destruct cs_ik as [IK ST]. pose proof r_kvals as (_ & _ & _ & KV). pose proof r_i4 as Hi.
  pose proof cs_mr as (M3 & _).
  apply (p4_keep_post B API LS SH SK ra empty rc fx j E CS SOURCE_RESET_K _ _ L3 A3 R7 mem4 md3
    L4 A4 R8 mem5 md4 HF RP7 M3 (r_svsp R7 SV7) KV); [| |exact IK|exact ST].
  - intros a X. left. apply in_G_bss. unfold r_HA in X. p4_cst. lia.
  - intros a Ha. left. unfold r_HA. p4_cst. p4_num. lia.
Qed.

Lemma tk : forall x k, In (x, k) (blocks L1 A1) -> ~ In x (hs_blocks r_h1) ->
  In (x, k) (blocks L4 A4) /\ (forall a, x <= a < x + k -> rk_kb2 B mem2 mem5 a).
Proof.
  intros x k Hin Nx. destruct (ck1 x k Hin Nx) as (H1 & K1 & N1). destruct (ck2 x k H1 N1) as (H2 & K2 & N2).
  destruct (ck3 x k H2 N2) as (H3 & K3). split; [exact H3|]. intros a Ha.
  eapply rk_kb2_trans; [exact (K1 a Ha)|]. eapply rk_kb2_trans; [exact (K2 a Ha)|exact (K3 a Ha)].
Qed.

Lemma tg : forall a, img_plain B a -> ~ (r_HA <= a < r_HA + 96) -> rk_kb2 B mem2 mem5 a.
Proof.
  intros a P NH. eapply rk_kb2_trans; [exact (cg1 a P NH)|]. eapply rk_kb2_trans; [exact (cg2 a P NH)|exact (cg3 a P NH)].
Qed.

Lemma fin_h1 : forall x m, In (x, m) (blocks L1 A1) -> (0 < m -> ~ r_Fcnl x) -> ~ In x (hs_blocks r_h3) ->
  ~ In x (hs_blocks r_h1).
Proof.
  intros x m H1 NF N3 X. pose proof rr_mr2 as (M1 & _).
  destruct (Z_lt_le_dec 0 m) as [Pm|Pm].
  2: { destruct (p4_hs_pos _ _ _ _ _ x rr_h1 X) as (k' & Pk' & Hk').
       assert (m = 0) as -> by (pose proof (r_blk_nn _ _ _ _ _ _ M1 H1); lia).
       exact (r_nd_pos _ _ _ _ _ _ M1 H1 Hk' Pk'). }
  pose proof (NF Pm) as NF'. clear NF.
  unfold hs_blocks in X. apply in_app_iff in X as [X|X].
  { apply N3. unfold r_h3, r_h2, hs_blocks, set_held, set_exp_held. cbn [hs_pending hs_partial hs_expected hs_held].
    apply in_or_app. left. exact X. }
  apply in_app_iff in X as [X|X].
  { apply N3. unfold r_h3, r_h2, hs_blocks, set_held, set_exp_held. cbn [hs_pending hs_partial hs_expected hs_held].
    apply in_or_app. right. apply in_or_app. left. exact X. }
  apply in_app_iff in X as [X|X].
  - unfold list_blocks in X. apply in_app_iff in X as [X|X].
    + apply N3. unfold r_h3, r_h2, hs_blocks, set_held, set_exp_held. cbn [hs_pending hs_partial hs_expected hs_held].
      apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. unfold list_blocks.
      rewrite ER3, EV3, EC3. apply in_or_app. left. exact X.
    + apply NF'. unfold r_Fcnl. apply in_or_app. left. exact X.
  - apply NF'. unfold r_Fcnl. apply in_or_app. right. exact X.
Qed.

Lemma fin_rv : forall x m, In (x, m) (blocks L4 A4) ->
  (In (x, m) (blocks L0 A0) /\ x <> bv_unsigned out /\ ~ In x (entry_blocks e) /\ ~ In x (hs_blocks h)) \/ x = OUT'.
Proof.
  intros x m H4. destruct (BK7b x m H4) as (H3 & N3). destruct (BK5b x m H3) as (H2 & Nds).
  destruct (BK3b x m H2) as [(H1 & NF)|XH].
  - destruct (BK2c x m H1) as [(H0 & NO & NE & NH)|[(E0 & XH)|XO]].
    + left. rewrite short_entry_blocks in NE. split; [exact H0|]. split; [exact NO|]. split; [exact NE|].
      intros Xh. apply (fin_h1 x m H1 NF N3). unfold r_h1. destruct (re_eof e =? 0) eqn:EQ.
      * apply Z.eqb_eq in EQ. exfalso. exact (NH EQ Xh).
      * exact Xh.
    + exfalso. apply (fin_h1 x m H1 NF N3). unfold r_h1. rewrite (proj2 (Z.eqb_eq _ _) E0). exact XH.
    + right. exact XO.
  - exfalso. apply N3. unfold r_h3, hs_blocks, set_held. cbn [hs_pending hs_partial hs_expected hs_held].
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
    unfold list_blocks in XH |- *. rewrite HV5, HC5. apply in_app_iff in XH as [XH|XH]; [apply in_or_app; left; exact XH|].
    apply in_map_iff in XH as (r & <- & Hr). destruct (cs_split r Hr) as [Hr'|Hd].
    + apply in_or_app. right. apply in_map. exact Hr'.
    + exfalso. apply Nds. apply in_map. exact Hd.
Qed.

Lemma fin_fk : forall x k, In (x, k) (blocks L0 A0) -> x <> bv_unsigned out -> x <> G -> ~ In x (entry_blocks e) ->
  ~ In x (hs_blocks h) -> In (x, k) (blocks L4 A4) /\ (forall a, x <= a < x + k -> rk_kb2 B mem0 mem5 a).
Proof.
  intros x k H0 N1 N2 N3 N4. destruct (rr_bk x N1 N2 N3 (fun _ => N4) k H0) as (H1 & K1).
  destruct (tk x k H1 (rr_nh1 x k H0 N1 N3 N4 H1)) as (H4 & K4).
  split; [exact H4|]. intros a Ha. eapply rk_kb2_trans; [|exact (K4 a Ha)].
  replace a with (x + (a - x)) by lia. apply K1. lia.
Qed.

Lemma fin_bk : forall x, x <> bv_unsigned out -> x <> G -> ~ In x (entry_blocks e) -> ~ In x (hs_blocks h) ->
  rk_bkept B L0 A0 mem0 L4 A4 mem5 x.
Proof.
  intros x N1 N2 N3 N4 k Hin. destruct (fin_fk x k Hin N1 N2 N3 N4) as (H4 & K4). split; [exact H4|].
  intros i0 Hi0. apply K4. lia.
Qed.

Lemma fin_out : output_at (rc := rc) B L4 A4 mem5 r_no2 r_cap2 r_out2.
Proof.
  pose proof rr_output as RO. unfold output_at in RO |- *. cbv zeta in RO |- *.
  destruct RO as ((O & jk & OD) & OC). split; [|exact OC]. exists O, jk.
  destruct OD as [Z0|(CP & NO & IN & FR & BY & LO & LJ)]; [left; exact Z0|right].
  rewrite rr_out2 in IN, FR, BY |- *.
  destruct (tk OUT' (bv_unsigned r_cap2) IN rr_out_h1) as (H4 & K4).
  split; [exact CP|]. split; [exact NO|]. split; [exact H4|]. split; [exact FR|].
  split; [|split; assumption].
  apply (rk_bytes_kb2 B mem2); [exact BY|]. intros i0 Hi0. apply K4. rewrite length_app, Nat2Z.inj_add in Hi0. lia.
Qed.

Lemma fin_rw0 : forall a cs, rw_cells (ms_segs B) mem0 a cs ->
  (forall x, a <= x < a + Z.of_nat (cells_size cs) -> img_plain B x /\ ~ (r_HA <= x < r_HA + 96) /\ ~ r_Err x) ->
  rw_cells (ms_segs B) mem5 a cs.
Proof.
  intros a cs H KK. apply (rk_rw_kb2 B mem0); [exact H|]. intros i0 Hi0.
  assert (Hx : a <= a + i0 < a + Z.of_nat (cells_size cs)) by lia.
  destruct (KK (a + i0) Hx) as (P & N1 & N2).
  eapply rk_kb2_trans; [exact (rr_gb _ P N2)|exact (tg _ P N1)].
Qed.

Lemma fin_rw2 : forall a cs, rw_cells (ms_segs B) mem2 a cs ->
  (forall x, a <= x < a + Z.of_nat (cells_size cs) -> img_plain B x /\ ~ (r_HA <= x < r_HA + 96)) ->
  rw_cells (ms_segs B) mem5 a cs.
Proof.
  intros a cs H KK. apply (rk_rw_kb2 B mem2); [exact H|]. intros i0 Hi0.
  assert (Hx : a <= a + i0 < a + Z.of_nat (cells_size cs)) by lia.
  destruct (KK (a + i0) Hx) as (P & N1). exact (tg _ P N1).
Qed.

Lemma fin_g0 : forall x, 0x21620 <= x < 0x21630 \/ 0x318a0 <= x < 0x318a4 \/ 0x318a5 <= x < 0x318b0 \/
  0x318b1 <= x < 0x318b8 \/ 0x318bc <= x < 0x318e0 \/ 0x31904 <= x < 0x31920 ->
  img_plain B x /\ ~ (r_HA <= x < r_HA + 96) /\ ~ r_Err x.
Proof.
  intros x Hx. assert (P : img_plain B x) by (destruct Hx as [X|X]; [apply r_gimg2; lia|apply r_gimg; lia]).
  split; [exact P|]. split; [unfold r_HA; p4_cst; lia|].
  apply rr_nE; [exact (proj1 P)|lia|lia|lia|lia|lia|intros _; p4_cst; lia].
Qed.

Lemma fin_g2 : forall x, 0x318a0 <= x < 0x31920 -> img_plain B x /\ ~ (r_HA <= x < r_HA + 96).
Proof. intros x Hx. split; [apply r_gimg; lia|unfold r_HA; p4_cst; lia]. Qed.

Lemma fin_rest : forall y, In y (concat (map entry_blocks (remove_at q es))) \/
  In y (concat (map (fun p : hsrc * nat => hs_blocks (fst p)) (remove_at q hj))) ->
  rk_bkept B L0 A0 mem0 L4 A4 mem5 y.
Proof.
  intros y Hy. pose proof r_nd_facts as (_ & _ & _ & _ & _ & _ & REST). destruct (REST y Hy) as (N1 & N2 & N3 & N4).
  exact (fin_bk y N2 N1 N3 N4).
Qed.

Lemma fin_eok : Forall (rk_entry_okk B L4 A4 mem5) (remove_at q es).
Proof.
  apply Forall_forall. intros x Hx. pose proof HREL as (_ & _ & _ & HES & _). destruct r_q as (Hq1 & _ & _).
  pose proof sr_mr as (M4 & _).
  apply (rk_entry_okk_kept B (API rc) r_BSP L0 A0 mem0 L4 A4 mem5 md4 x); [|exact M4|].
  - apply rk_entry_okk_of. rewrite Forall_forall in HES. exact (HES x (p4_in_remove_at es q x Hq1 Hx)).
  - intros y Hy. apply fin_rest. left. apply in_concat. exists (entry_blocks x). split; [apply in_map; exact Hx|exact Hy].
Qed.

Lemma fin_pairs : Forall2 (pair_ok (rc := rc) B L4 A4 mem5 t) (remove_at q es) (remove_at q hj).
Proof.
  pose proof HREL as (_ & _ & _ & _ & _ & _ & PA & NDS & _). destruct r_q as (Hq1 & Hq2 & _).
  apply (p4_forall2_mem _ _ _ _ (Forall2_remove_at _ es hj q PA)).
  intros x [hh k] Hc PO.
  assert (Hp : In (hh, k) (remove_at q hj)) by exact (in_combine_r _ _ _ _ Hc).
  assert (Nk : k <> i).
  { pose proof (p4_nodup_map_remove_at snd hj q (h, i) Hq2 NDS) as (_ & NI).
    rewrite (nth_error_nth hj q (h, i) Hqh) in NI. cbn [snd] in NI. intros ->. apply NI.
    exact (in_map snd _ _ Hp). }
  unfold pair_ok in PO |- *. cbv zeta in PO |- *. cbn [fst snd] in PO |- *.
  destruct PO as (SRC & K4 & REST). split; [|split; [exact K4|exact REST]].
  apply (rk_src_at_kept B L0 A0 mem0 L4 A4 mem5 _ hh SRC).
  - intros k0 Hk0. assert (Hk4 : (k < 4)%nat) by exact K4. pose proof r_i4 as Hi.
    assert (IA : img_plain B (G_S + SRC_SIZE * Z.of_nat k + k0)) by (apply r_gimg; p4_cst; lia).
    eapply rk_kb2_trans; [apply rr_gb; [exact IA|]|apply tg; [exact IA|unfold r_HA; p4_cst; lia]].
    apply rr_nE; [exact (proj1 IA)|p4_cst; lia|p4_cst; lia|p4_cst; lia|p4_cst; lia|p4_cst; lia|].
    intros _ X. p4_cst. lia.
  - intros y Hy. apply fin_rest. right. apply in_concat. exists (hs_blocks hh). split; [|exact Hy].
    apply (in_map (fun p : hsrc * nat => hs_blocks (fst p)) _ (hh, k)). exact Hp.
Qed.

Lemma fin_zero : forall k, (k < 4)%nat -> slot_open (remove_at q hj) k = false ->
  rw_cells (ms_segs B) mem5 (G_S + SRC_SIZE * Z.of_nat k) [CB 96%nat (nulbytes 96)].
Proof.
  intros k Hk4 SO. pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & NDS & ZS & _). destruct r_q as (Hq1 & Hq2 & _).
  destruct (Nat.eq_dec k i) as [->|Nk]; [exact Z7|].
  pose proof (p4_slot_open_remove_at hj q (h, i) Hq2 NDS) as (_ & SOR).
  rewrite (nth_error_nth hj q (h, i) Hqh) in SOR. cbn [snd] in SOR. rewrite (SOR k Nk) in SO.
  apply fin_rw0; [exact (ZS k Hk4 SO)|]. intros x Hx. cbn [cells_size csize] in Hx. pose proof r_i4 as Hi.
  assert (IA : img_plain B x) by (apply r_gimg; p4_cst; lia). split; [exact IA|]. split; [unfold r_HA; p4_cst; lia|].
  apply rr_nE; [exact (proj1 IA)|p4_cst; lia|p4_cst; lia|p4_cst; lia|p4_cst; lia|p4_cst; lia|intros _ X; p4_cst; lia].
Qed.

Lemma fin_pos : forall y, In y (concat (map entry_blocks (remove_at q es))) \/
  In y (concat (map (fun p : hsrc * nat => hs_blocks (fst p)) (remove_at q hj))) ->
  exists k, 0 < k /\ In (y, k) (blocks L0 A0).
Proof.
  intros y [Hy|Hy]; destruct r_q as (Hq1 & Hq2 & _); pose proof HREL as (_ & _ & _ & HES & _ & _ & PA & _).
  - apply in_concat in Hy as (l & Hl & Hy). apply in_map_iff in Hl as (x & <- & Hx).
    rewrite Forall_forall in HES. exact (p4_eb_pos rc B L0 A0 mem0 x y (HES x (p4_in_remove_at es q x Hq1 Hx)) Hy).
  - apply in_concat in Hy as (l & Hl & Hy). apply in_map_iff in Hl as (x & <- & Hx).
    destruct (pair_find _ _ _ es hj x PA (p4_in_remove_at hj q x Hq2 Hx)) as (x0 & PO).
    destruct PO as (SRC & _). exact (p4_hs_pos _ _ _ _ _ y SRC Hy).
Qed.

Lemma fin_ofr : forall y, In y (G :: concat (map entry_blocks (remove_at q es)) ++
  concat (map (fun p : hsrc * nat => hs_blocks (fst p)) (remove_at q hj))) -> y <> OUT'.
Proof.
  intros y Hy. pose proof r_nd_facts as (NGO & NGE & NGH & _ & _ & _ & REST).
  destruct Hy as [<-|Hy].
  - pose proof HREL as (_ & GIN & _).
    refine (proj1 (BK2b G SRC_TABLE GIN ltac:(unfold SRC_TABLE, SRC_ENTRY; lia) NGO _ (fun _ => NGH))).
    rewrite short_entry_blocks. exact NGE.
  - apply in_app_iff in Hy. destruct (REST y Hy) as (N1 & N2 & N3 & N4). destruct (fin_pos y Hy) as (k & Pk & Hk1).
    refine (proj1 (BK2b y k Hk1 Pk N2 _ (fun _ => N4))). rewrite short_entry_blocks. exact N3.
Qed.

Lemma fin_nd : NoDup (target_addrs G OUT' (remove_at q es) (remove_at q hj)).
Proof.
  pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NDT). destruct r_q as (Hq1 & Hq2 & _).
  pose proof (p4_target_remove_at G (bv_unsigned out) es hj q Hq1 Hq2 NDT) as ND. unfold target_addrs in *.
  apply (p4_nd_swap _ _ _ _ ND). intros X. exact (fin_ofr OUT' X eq_refl).
Qed.

Lemma fin_zero_keep : forall x, In (x, 0) (blocks L0 A0) -> In (x, 0) (blocks L4 A4).
Proof.
  intros x H0. apply (p4_rp_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x RP7).
  apply (p4_rp_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x RP5).
  apply (p4_rp_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x RP3).
  exact (p4_rp_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x RP1 H0).
Qed.

Lemma fin_dk : driver_kept B E (target_addrs G OUT' (remove_at q es) (remove_at q hj)) L4 A4 mem5.
Proof.
  pose proof HDK as (DK1 & DK2 & DK3 & DK4).
  assert (TA' : forall y, In y (target_addrs G OUT' (remove_at q es) (remove_at q hj)) ->
    y = OUT' \/ y = G \/ In y (concat (map entry_blocks (remove_at q es))) \/
    In y (concat (map (fun p : hsrc * nat => hs_blocks (fst p)) (remove_at q hj)))).
  { intros y Hy. unfold target_addrs in Hy. destruct Hy as [<-|[<-|Hy]]; [right; left; reflexivity|left; reflexivity|].
    apply in_app_iff in Hy as [Hy|Hy]; [right; right; left; exact Hy|right; right; right; exact Hy]. }
  assert (INT : forall y, In y (target_addrs G OUT' (remove_at q es) (remove_at q hj)) -> y <> OUT' ->
    In y (target_addrs G (bv_unsigned out) es hj)).
  { intros y Hy Ny. destruct (TA' y Hy) as [X|[X|X]]; [congruence|subst y; unfold target_addrs; left; reflexivity|].
    exact (r_ta_rest y X). }
  assert (FOR : forall x, ~ In x (target_addrs G (bv_unsigned out) es hj) ->
    x <> bv_unsigned out /\ x <> G /\ ~ In x (entry_blocks e) /\ ~ In x (hs_blocks h)).
  { intros x NT. split; [intros ->; apply NT; unfold target_addrs; right; left; reflexivity|].
    split; [intros ->; apply NT; unfold target_addrs; left; reflexivity|].
    split; intros X; apply NT; apply r_ta_eh; [left|right]; exact X. }
  assert (UB : forall p m, In (p, m) (user_blocks A0) -> In (ptr_addr L0 p, m) (blocks L0 A0))
    by (intros p m Hp; exact (in_map (fun b => (ptr_addr L0 (fst b), snd b)) _ (p, m) Hp)).
  assert (BU : forall x m, In (x, m) (blocks L4 A4) -> exists p, In (p, m) (user_blocks A4) /\ ptr_addr L4 p = x).
  { intros x m Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p m'] & EQ & Hp). cbn [fst snd] in EQ.
    injection EQ as <- <-. exists p. split; [exact Hp|reflexivity]. }
  unfold driver_kept. split; [|split; [|split]].
  - intros q0 m Hq0 NT. destruct (DK1 q0 m Hq0 NT) as (NTA & q1 & Hq1' & Eq1).
    assert (B0 : In (ptr_addr (ss_L E) q0, m) (blocks L0 A0)) by (rewrite <- Eq1; exact (UB q1 m Hq1')).
    split.
    + intros Pm X. pose proof (NTA Pm) as NT0. destruct (FOR _ NT0) as (N1 & N2 & N3 & N4).
      destruct (Z.eq_dec (ptr_addr (ss_L E) q0) OUT') as [EO|NO].
      * refine (proj1 (BK2b _ m B0 Pm N1 _ (fun _ => N4)) EO). rewrite short_entry_blocks. exact N3.
      * exact (NT0 (INT _ X NO)).
    + destruct (Z_lt_le_dec 0 m) as [Pm|Pm].
      * destruct (FOR _ (NTA Pm)) as (N1 & N2 & N3 & N4).
        destruct (fin_fk _ m B0 N1 N2 N3 N4) as (H4 & _). exact (BU _ m H4).
      * assert (m = 0) as -> by (pose proof (rk_ub_nonneg A0 q1 m HWF Hq1'); lia).
        exact (BU _ 0 (fin_zero_keep _ B0)).
  - intros q0 m i0 Hq0 NT NP Hi0. destruct (DK1 q0 m Hq0 NT) as (NTA & q1 & Hq1' & Eq1).
    assert (B0 : In (ptr_addr (ss_L E) q0, m) (blocks L0 A0)) by (rewrite <- Eq1; exact (UB q1 m Hq1')).
    assert (Pm : 0 < m) by lia.
    destruct (FOR _ (NTA Pm)) as (N1 & N2 & N3 & N4).
    destruct (fin_fk _ m B0 N1 N2 N3 N4) as (_ & K4).
    rewrite <- (DK2 q0 m i0 Hq0 NT NP Hi0).
    assert (Hr : ptr_addr (ss_L E) q0 <= ptr_addr (ss_L E) q0 + i0 < ptr_addr (ss_L E) q0 + m) by lia.
    exact (proj1 (K4 _ Hr)).
  - intros i0 Hi0. pose proof HF as (_ & _ & PRE & _).
    destruct PRE as (PRE & _ & _ & _ & _ & _ & NI & _). destruct PRE as (PRE & _).
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INPUT & _).
    destruct INPUT as [(HN0 & _)|(HN & qp & HQP & HPP)]; [lia|].
    assert (NT : ~ In (ptr_addr (ss_L E) qp, ss_n E) (ss_T E)) by (rewrite HPP; exact (NI HN)).
    destruct (DK1 qp (ss_n E) HQP NT) as (NTA & q1 & Hq1' & Eq1).
    assert (B0 : In (ptr_addr (ss_L E) qp, ss_n E) (blocks L0 A0)) by (rewrite <- Eq1; exact (UB q1 _ Hq1')).
    destruct (FOR _ (NTA HN)) as (N1 & N2 & N3 & N4).
    destruct (fin_fk _ _ B0 N1 N2 N3 N4) as (_ & K4).
    rewrite <- (DK3 i0 Hi0). rewrite HPP in K4.
    assert (Hr : ss_p E <= ss_p E + i0 < ss_p E + ss_n E) by lia. exact (proj1 (K4 _ Hr)).
  - intros q0 m Hq0. destruct (fin_rv q0 m Hq0) as [(H0 & NO & NE & NH)|EO].
    + destruct (DK4 q0 m H0) as [X|X]; [left; exact X|right].
      destruct (r_ta_in q0 X) as [Y|[Y|[Y|[Y|Y]]]].
      * subst q0. unfold target_addrs. left. reflexivity.
      * exfalso. exact (NO Y).
      * exfalso. exact (NE Y).
      * exfalso. exact (NH Y).
      * unfold target_addrs. right. right. apply in_app_iff. exact Y.
    + right. subst q0. unfold target_addrs. right. left. reflexivity.
Qed.

Lemma fin_md : exists vm, md4 = with_vmmaps vm (ss_md E).
Proof.
  destruct HVM as (v0 & E0).
  destruct RP1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (v1 & V1) & _).
  destruct RP3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (v3 & V3) & _).
  destruct RP5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (v5 & V5) & _).
  destruct RP7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (v7 & V7) & _).
  exists v7. rewrite V7, V5, V3, V1, E0, !rk_vm_twice. reflexivity.
Qed.

Lemma fin_glob : globals_at B mem5 cl (if send_off cl br (r_TOT e') then br else dd) gn dd
  (if send_off cl br (r_TOT e') then ei else 0) (Z.of_nat (length (remove_at q es))) G nfd mx r_no2 r_cap2 r_out2.
Proof.
  pose proof HGL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & ER & HCL & HBR & HGN &
    HDD & HEI & (C0 & C1) & HMX).
  destruct r_q as (Hq1 & _ & _). pose proof HF as (FF & _).
  destruct (p4_ff _ _ _ _ _ _ _ FF) as (SEG & TP & EOff & _).
  assert (LN : Z.of_nat (length (remove_at q es)) = Z.of_nat (length (map short_entry es)) - 1)
    by (rewrite remove_at_length, length_map by exact Hq1; lia).
  unfold globals_at.
  split; [apply fin_rw0; [exact G1|intros x Hx; apply fin_g0; cbn [cells_size csize] in Hx; p4_cst; lia]|].
  split; [apply fin_rw0; [exact G2|intros x Hx; apply fin_g0; cbn [cells_size csize] in Hx; p4_cst; lia]|].
  split; [apply fin_rw0; [exact G3|intros x Hx; apply fin_g0; cbn [cells_size csize] in Hx; p4_cst; lia]|].
  split; [apply fin_rw2; [exact BR2|intros x Hx; apply fin_g2; cbn [cells_size csize] in Hx; p4_cst; lia]|].
  split; [apply fin_rw0; [exact G5|intros x Hx; apply fin_g0; cbn [cells_size csize] in Hx; p4_cst; lia]|].
  split; [apply fin_rw0; [exact G6|intros x Hx; apply fin_g0; cbn [cells_size csize] in Hx; p4_cst; lia]|].
  split; [apply fin_rw2; [exact EI2|intros x Hx; apply fin_g2; cbn [cells_size csize] in Hx; p4_cst; lia]|].
  split; [rewrite LN; apply fin_rw2; [exact NS2|intros x Hx; apply fin_g2; cbn [cells_size csize] in Hx; p4_cst; lia]|].
  split; [apply fin_rw0; [exact G9|intros x Hx; apply fin_g0; cbn [cells_size csize] in Hx; p4_cst; lia]|].
  split; [apply fin_rw0; [exact G10|intros x Hx; apply fin_g0; cbn [cells_size csize] in Hx; p4_cst; lia]|].
  split; [apply fin_rw2; [exact rr_outv|intros x Hx; apply fin_g2; cbn [cells_size csize] in Hx; p4_cst; lia]|].
  split; [apply fin_rw2; [exact LK2|intros x Hx; apply fin_g2; cbn [cells_size csize] in Hx; p4_cst; lia]|].
  split; [apply fin_rw0; [exact G13|intros x Hx; apply fin_g0; cbn [cells_size csize] in Hx; p4_cst; lia]|].
  split.
  { rewrite SEG. pose proof r_ea as EA. pose proof (@YM05.alloc_ceiling_value rc) as ACV.
    apply rk_err_cells; [lia|lia|]. intros i0 Hi0. rewrite <- SEG.
    destruct RP7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SW). apply SW. unfold scratch_k. right. lia. }
  split; [exact HCL|]. split; [destruct (send_off cl br (r_TOT e')); [exact HBR|exact HDD]|].
  split; [exact HGN|]. split; [exact HDD|].
  split; [destruct (send_off cl br (r_TOT e')); [exact HEI|left; reflexivity]|].
  split; [|exact HMX]. split.
  - intros Hg. destruct (C0 Hg) as (X1 & X2 & X3). rewrite X2, X3. split; [exact X1|].
    split; [destruct (send_off cl 0 (r_TOT e')); reflexivity|reflexivity].
  - intros Hg. destruct (C1 Hg) as [X|[X|X]]; [left; exact X| |right; right; exact X].
    right; left. unfold send_off. rewrite X, Z.eqb_refl, orb_true_r. reflexivity.
Qed.

Lemma f_out0 : (bv_unsigned cap = 0 /\ bv_unsigned out = 0) \/
  (0 < bv_unsigned cap /\ In (bv_unsigned out, bv_unsigned cap) (blocks L0 A0)).
Proof.
  pose proof HOUT as ((O & jk & OD) & _). destruct OD as [(X1 & X2 & _)|(X1 & _ & X3 & _)]; [left|right]; tauto.
Qed.

Lemma f_moved : out_same (bv_unsigned out) (bv_unsigned cap) OUT' r_cap1 = false -> r_lv = true /\ CAP' = r_cap1.
Proof.
  intros Sm. destruct r_lv eqn:LV.
  - split; [reflexivity|]. exact (proj1 CAPX LV).
  - exfalso. destruct (LV0 LV) as (_ & _ & EO). pose proof (proj2 CAPX LV) as C1.
    unfold out_same in Sm. rewrite EO, C1, !Z.eqb_refl in Sm. discriminate.
Qed.

Lemma f_stay : out_same (bv_unsigned out) (bv_unsigned cap) OUT' r_cap1 = true ->
  OUT' = bv_unsigned out /\ r_cap1 = bv_unsigned cap.
Proof. unfold out_same. intros Sm. apply andb_prop in Sm as [S1 S2]. apply Z.eqb_eq in S1, S2. tauto. Qed.

Lemma f_new : out_same (bv_unsigned out) (bv_unsigned cap) OUT' r_cap1 = false -> In (OUT', r_cap1) (blocks L4 A4).
Proof.
  intros Sm. destruct (f_moved Sm) as (LV & C1). destruct (LV1 LV) as (_ & _ & IN & _).
  rewrite <- C1. exact (proj1 (tk _ _ IN rr_out_h1)).
Qed.

Lemma f_stay_blk : out_same (bv_unsigned out) (bv_unsigned cap) OUT' r_cap1 = true -> 0 < bv_unsigned cap ->
  In (bv_unsigned out, bv_unsigned cap) (blocks L4 A4).
Proof.
  intros Sm Cp. destruct (f_stay Sm) as (EO & C1).
  assert (N : ~ In (bv_unsigned out) (hs_blocks r_h1)) by (rewrite <- EO; exact rr_out_h1).
  destruct r_lv eqn:LV.
  - destruct (LV1 LV) as (_ & _ & IN & _). rewrite (proj1 CAPX LV), C1, EO in IN. exact (proj1 (tk _ _ IN N)).
  - destruct (LV0 LV) as (_ & X & _). exact (proj1 (tk _ _ (proj1 (X Cp)) N)).
Qed.

Definition f_RE : list Z := concat (map entry_nc (remove_at q (map short_entry es))).
Definition f_RH : list Z := concat (map (fun p : hsrc * nat => src_nc (fst p)) (remove_at q hj)).

Lemma f_nc0 : Permutation (rv_nc (view_of G (bv_unsigned out) (map short_entry es) hj))
  (G :: bv_unsigned out :: entry_nc e ++ src_nc h ++ f_RE ++ f_RH).
Proof.
  destruct r_q as (Hq1 & Hq2 & _).
  assert (Hq1' : (q < length (map short_entry es))%nat) by (rewrite length_map; exact Hq1).
  pose proof (p4_perm_concat_map entry_nc _ _ (remove_at_perm (map short_entry es) q no_entry Hq1')) as P1.
  assert (NQ : nth q (map short_entry es) no_entry = short_entry e).
  { change no_entry with (short_entry no_entry). rewrite map_nth. rewrite (nth_error_nth es q no_entry Hqe).
    reflexivity. }
  rewrite NQ in P1.
  pose proof (p4_perm_concat_map (fun p : hsrc * nat => src_nc (fst p)) _ _ (remove_at_perm hj q (h, i) Hq2)) as P2.
  rewrite (nth_error_nth hj q (h, i) Hqh) in P2.
  change (concat (map entry_nc (short_entry e :: remove_at q (map short_entry es)))) with (entry_nc e ++ f_RE) in P1.
  change (concat (map (fun p : hsrc * nat => src_nc (fst p)) ((h, i) :: remove_at q hj))) with (src_nc h ++ f_RH) in P2.
  unfold view_of. cbn [rv_nc]. apply perm_skip, perm_skip.
  eapply Permutation_trans; [apply Permutation_app; [exact P1|exact P2]|].
  rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_swap_app.
Qed.

Lemma f_nc4 : forall es', Forall2 p4_rs (remove_at q es) es' ->
  rv_nc (view_of G OUT' es' (remove_at q hj)) = G :: OUT' :: f_RE ++ f_RH.
Proof.
  intros es' RS. unfold view_of, f_RE, f_RH. cbn [rv_nc].
  rewrite (p4_rs_map entry_nc _ _ p4_rs_nc RS), p4_rat_map, map_map. reflexivity.
Qed.

Lemma f_enc_in : forall x, In x (entry_nc e) -> In x (entry_blocks e).
Proof. intros x Hx. rewrite p4_eb_nc. apply in_or_app. left. exact Hx. Qed.

Lemma f_snc_in : forall x, In x (src_nc h) -> In x (hs_blocks h).
Proof. intros x Hx. apply (Permutation_in x (Permutation_sym (p4_hb_nc h))). apply in_or_app. left. exact Hx. Qed.

Lemma f_rest : forall x, In x (f_RE ++ f_RH) ->
  x <> G /\ x <> bv_unsigned out /\ ~ In x (entry_blocks e) /\ ~ In x (hs_blocks h).
Proof.
  intros x Hx. pose proof r_nd_facts as (_ & _ & _ & _ & _ & _ & NR). apply NR.
  apply in_app_iff in Hx as [Hx|Hx]; [left|right].
  - unfold f_RE in Hx. rewrite p4_rat_map in Hx. apply in_concat in Hx as (l & Hl & Hx).
    apply in_map_iff in Hl as (y & <- & Hy). apply in_map_iff in Hy as (z & <- & Hz).
    apply in_concat. exists (entry_blocks z). split; [apply in_map; exact Hz|].
    rewrite p4_eb_nc. apply in_or_app. left. exact Hx.
  - unfold f_RH in Hx. apply in_concat in Hx as (l & Hl & Hx). apply in_map_iff in Hl as (p & <- & Hp).
    apply in_concat. exists (hs_blocks (fst p)). split; [apply (in_map (fun p0 : hsrc * nat => hs_blocks (fst p0))); exact Hp|].
    apply (Permutation_in x (Permutation_sym (p4_hb_nc (fst p)))). apply in_or_app. left. exact Hx.
Qed.

Lemma f_eh_notR : forall x, In x (entry_blocks e) \/ In x (hs_blocks h) ->
  x <> G /\ x <> bv_unsigned out /\ ~ In x (f_RE ++ f_RH).
Proof.
  intros x Hx. pose proof r_nd_facts as (_ & NGE & NGH & NOE & NOH & _ & _).
  split; [intros ->; destruct Hx as [Hx|Hx]; [exact (NGE Hx)|exact (NGH Hx)]|].
  split; [intros ->; destruct Hx as [Hx|Hx]; [exact (NOE Hx)|exact (NOH Hx)]|].
  intros HRx. destruct (f_rest x HRx) as (_ & _ & N1 & N2). destruct Hx as [Hx|Hx]; [exact (N1 Hx)|exact (N2 Hx)].
Qed.

Lemma f_nd_parts : List.NoDup (entry_nc e) /\ List.NoDup (src_nc h).
Proof.
  pose proof r_nd_split as ND. apply List.NoDup_cons_iff in ND as [_ ND]. apply List.NoDup_cons_iff in ND as [_ ND].
  pose proof (NoDup_app_remove_r _ _ ND) as NE. pose proof (NoDup_app_remove_l _ _ ND) as NH.
  pose proof (NoDup_app_remove_r _ _ NH) as NH'.
  rewrite p4_eb_nc in NE. split; [exact (NoDup_app_remove_r _ _ NE)|].
  exact (NoDup_app_remove_r _ _ (Permutation_NoDup (p4_hb_nc h) NH')).
Qed.

Lemma f_eh_dels : forall t, In t (entry_dels (short_entry e) ++ src_dels h) ->
  In (fst t) (entry_blocks e) \/ In (fst t) (hs_blocks h).
Proof.
  intros u Hu. apply (in_map fst) in Hu. rewrite map_app, mv_map_fst_entry, mv_map_fst_src in Hu.
  apply in_app_iff in Hu as [Hu|Hu]; [left; exact (f_enc_in _ Hu)|right; exact (f_snc_in _ Hu)].
Qed.

Lemma f_eh_nd : List.NoDup (map fst (entry_dels (short_entry e) ++ src_dels h)).
Proof.
  pose proof f_nd_parts as (NDE & NDH). pose proof r_nd_facts as (_ & _ & _ & _ & _ & NHE & _).
  rewrite map_app, mv_map_fst_entry, mv_map_fst_src. apply mv_nodup_app; [exact NDE|exact NDH|].
  intros a Ha Hb. exact (NHE a (f_snc_in a Hb) (f_enc_in a Ha)).
Qed.

Lemma f_eh_in : incl (entry_dels (short_entry e) ++ src_dels h) (blocks L0 A0).
Proof.
  intros u Hu. pose proof (p4_ent_blk_of B L0 A0 mem0 e r_eok) as (EB1 & EB2 & _).
  pose proof (p4_src_blk_of B L0 A0 mem0 _ h rr_SRC0) as ((PA & _) & PP & (EA & _) & (HA & _) & _).
  apply in_app_iff in Hu as [Hu|Hu].
  - change (In u (entry_dels e)) in Hu. unfold entry_dels in Hu. apply in_app_iff in Hu as [Hu|Hu].
    + destruct (re_cap e =? 0) eqn:C; [destruct Hu|]. destruct Hu as [<-|[]].
      destruct EB1 as [X|X]; [apply Z.eqb_neq in C; contradiction|exact X].
    + destruct (re_hp e =? 0) eqn:C; [destruct Hu|]. destruct Hu as [<-|[]].
      destruct EB2 as [X|X]; [apply Z.eqb_neq in C; contradiction|exact X].
  - unfold src_dels, arr_sz in Hu. apply in_app_iff in Hu as [Hu|Hu].
    + destruct (hl_cap (hs_pending h) =? 0) eqn:C; [destruct Hu|]. destruct Hu as [<-|[]].
      destruct PA as [X|X]; [apply Z.eqb_neq in C; contradiction|exact X].
    + destruct Hu as [<-|Hu]; [exact PP|]. rewrite ?app_nil_l in Hu. apply in_app_iff in Hu as [Hu|Hu].
      * destruct (hl_cap (hs_expected h) =? 0) eqn:C; [destruct Hu|]. destruct Hu as [<-|[]].
        destruct EA as [X|X]; [apply Z.eqb_neq in C; contradiction|exact X].
      * destruct (hl_cap (hs_held h) =? 0) eqn:C; [destruct Hu|]. destruct Hu as [<-|[]].
        destruct HA as [X|X]; [apply Z.eqb_neq in C; contradiction|exact X].
Qed.

Lemma f_old_in4 : forall x m, In (x, m) (blocks L0 A0) -> x <> bv_unsigned out -> ~ In x (entry_blocks e) ->
  ~ In x (hs_blocks h) -> In (x, m) (blocks L4 A4).
Proof.
  intros x m H0 N1 N2 N3. destruct (Z.eq_dec x G) as [->|NG].
  - pose proof HREL as (_ & GIN & _). pose proof (proj1 (NoDup_ListNoDup _) (r_ND L0 A0 mem0 md0 HMR)) as ND0.
    rewrite (mv_fst_uniq _ G m SRC_TABLE ND0 H0 GIN). exact (proj1 (tk G SRC_TABLE GIN2 rr_G_h1)).
  - exact (proj1 (fin_fk x m H0 N1 NG N2 N3)).
Qed.

Lemma f_move : forall es', Forall2 p4_rs (remove_at q es) es' ->
  nc_move (view_of G (bv_unsigned out) (map short_entry es) hj) L0 A0 (view_of G OUT' es' (remove_at q hj)) L4 A4
    (p4_dels (bv_unsigned out) (bv_unsigned cap) OUT' r_cap1 (short_entry e) h)
    (p4_adds (bv_unsigned out) (bv_unsigned cap) OUT' r_cap1).
Proof.
  intros es' RS.
  pose proof r_nd_facts as (NGO & NGE & NGH & NOE & NOH & NHE & _).
  pose proof (proj1 (NoDup_ListNoDup _) (r_ND L0 A0 mem0 md0 HMR)) as ND0.
  pose proof sr_mr as (M4 & _). pose proof (proj1 (NoDup_ListNoDup _) (r_ND L4 A4 mem5 md4 M4)) as ND4.
  pose proof f_nc0 as PN0.
  pose (kE := fun x : Z => negb (existsb (Z.eqb x) (entry_blocks e ++ hs_blocks h))).
  assert (KE : forall t, In t (entry_dels (short_entry e) ++ src_dels h) -> kE (fst t) = false).
  { intros u Hu. unfold kE. apply mv_negb_in. apply in_or_app. exact (f_eh_dels u Hu). }
  assert (KEo : kE (bv_unsigned out) = true).
  { unfold kE. apply mv_negb_nin. intros Hx. apply in_app_iff in Hx as [Hx|Hx]; [exact (NOE Hx)|exact (NOH Hx)]. }
  assert (NC : forall x, In x (map fst (entry_dels (short_entry e) ++ src_dels h)) ->
     In x (entry_blocks e) \/ In x (hs_blocks h)).
  { intros x Hx. apply in_map_iff in Hx as (u & <- & Hu). exact (f_eh_dels u Hu). }
  unfold p4_dels, p4_adds, out_move_dels, out_move_adds.
  destruct (out_same (bv_unsigned out) (bv_unsigned cap) OUT' r_cap1) eqn:ES; cbn [orb].
  - destruct (f_stay ES) as (EO & C1). rewrite app_nil_l.
    exists (G :: bv_unsigned out :: f_RE ++ f_RH), [], (List.filter (fun t => kE (fst t)) (blocks L0 A0)), [],
      (List.filter (fun t => negb (existsb (Z.eqb (fst t)) (map fst (entry_dels (short_entry e) ++ src_dels h))))
        (List.filter (fun t => negb (kE (fst t))) (blocks L0 A0))).
    split.
    { eapply Permutation_trans; [exact PN0|]. rewrite map_app, mv_map_fst_entry, mv_map_fst_src, app_nil_r.
      change (entry_nc (short_entry e)) with (entry_nc e). apply perm_skip, perm_skip.
      rewrite (app_assoc (entry_nc e)). apply Permutation_app_comm. }
    split; [rewrite (f_nc4 es' RS), EO; cbn [map]; rewrite app_nil_r; apply Permutation_refl|].
    split; [exact (mv_split3 _ _ kE ND0 f_eh_nd f_eh_in KE)|].
    split.
    { rewrite app_nil_l, app_nil_r. apply NoDup_Permutation.
      - exact (NoDup_map_inv _ _ ND4).
      - apply NoDup_filter. exact (NoDup_map_inv _ _ ND0).
      - intros [x m]. rewrite filter_In. cbn [fst]. split.
        + intros H4. destruct (fin_rv x m H4) as [(H0 & _ & Ne & Nh)|EOx].
          * split; [exact H0|]. unfold kE. apply mv_negb_nin. intros Hx.
            apply in_app_iff in Hx as [Hx|Hx]; [exact (Ne Hx)|exact (Nh Hx)].
          * rewrite EOx, EO in H4 |- *. split; [|exact KEo].
            destruct f_out0 as [(C0 & O0)|(Cp & IN0)].
            -- exfalso. rewrite O0 in H4. pose proof (r_blk_rng _ _ _ _ _ _ M4 H4) as (X & _). clear - X. lia.
            -- rewrite (mv_fst_uniq _ _ m (bv_unsigned cap) ND4 H4 (f_stay_blk ES Cp)). exact IN0.
        + intros (H0 & Hkp). unfold kE in Hkp. apply mv_negb_out in Hkp.
          assert (Ne : ~ In x (entry_blocks e)) by (intros X; apply Hkp; apply in_or_app; left; exact X).
          assert (Nh : ~ In x (hs_blocks h)) by (intros X; apply Hkp; apply in_or_app; right; exact X).
          destruct (Z.eq_dec x (bv_unsigned out)) as [->|No]; [|exact (f_old_in4 x m H0 No Ne Nh)].
          destruct f_out0 as [(C0 & O0)|(Cp & IN0)].
          * exfalso. rewrite O0 in H0. pose proof (r_blk_rng _ _ _ _ _ _ HMR H0) as (X & _). clear - X. lia.
          * rewrite (mv_fst_uniq _ _ m (bv_unsigned cap) ND0 H0 IN0). exact (f_stay_blk ES Cp). }
    split; [intros x m H4; exact (r_blk_nn _ _ _ _ _ _ M4 H4)|].
    split; [intros [x m] Hu; exact (r_blk_nn _ _ _ _ _ _ HMR (f_eh_in _ Hu))|].
    split; [exact f_eh_nd|].
    split.
    { intros u Hu. pose proof (f_eh_dels u Hu) as Hx. destruct (f_eh_notR (fst u) Hx) as (N1 & N2 & N3).
      split.
      - intros [X|[X|X]]; [exact (N1 (eq_sym X))|exact (N2 (eq_sym X))|exact (N3 X)].
      - intros m HB. apply filter_In in HB as (_ & HB). cbn [fst] in HB. rewrite (KE u Hu) in HB. discriminate. }
    split.
    { intros u Hu. rewrite !filter_In in Hu. destruct Hu as ((_ & Hkp) & Hd). split.
      - apply negb_true_iff in Hkp. unfold kE in Hkp.
        apply negb_false_iff in Hkp. apply mv_inb in Hkp. apply in_app_iff in Hkp.
        destruct (f_eh_notR (fst u) Hkp) as (N1 & N2 & N3).
        intros [X|[X|X]]; [exact (N1 (eq_sym X))|exact (N2 (eq_sym X))|exact (N3 X)].
      - exact (mv_negb_out _ _ Hd). }
    intros g0 [].
  - destruct (f_moved ES) as (LV & C1).
    pose (kM := fun x : Z => kE x && negb (x =? bv_unsigned out)).
    pose (od := if bv_unsigned cap =? 0 then @nil (Z * Z) else [(bv_unsigned out, bv_unsigned cap)]).
    pose (gl := if bv_unsigned cap =? 0 then [bv_unsigned out] else @nil Z).
    change (if bv_unsigned cap =? 0 then [] else [(bv_unsigned out, bv_unsigned cap)]) with od.
    assert (ODf : forall t, In t od -> t = (bv_unsigned out, bv_unsigned cap) /\ 0 < bv_unsigned cap /\
      In t (blocks L0 A0)).
    { intros u Hu. unfold od in Hu. destruct (bv_unsigned cap =? 0) eqn:C; [destruct Hu|].
      destruct Hu as [<-|[]]. apply Z.eqb_neq in C.
      destruct f_out0 as [(C0 & _)|(Cp & IN0)]; [contradiction|]. split; [reflexivity|]. split; [exact Cp|exact IN0]. }
    assert (OG : Permutation [bv_unsigned out] (map fst od ++ gl)).
    { unfold od, gl. destruct (bv_unsigned cap =? 0); apply Permutation_refl. }
    assert (GN : forall g0, In g0 gl -> g0 = bv_unsigned out /\ bv_unsigned cap = 0).
    { intros g0 Hg. unfold gl in Hg. destruct (bv_unsigned cap =? 0) eqn:C; [|destruct Hg].
      destruct Hg as [<-|[]]. apply Z.eqb_eq in C. split; [reflexivity|exact C]. }
    assert (DL : forall t, In t (od ++ entry_dels (short_entry e) ++ src_dels h) ->
      (t = (bv_unsigned out, bv_unsigned cap) /\ 0 < bv_unsigned cap /\ In t (blocks L0 A0)) \/
      In t (entry_dels (short_entry e) ++ src_dels h)).
    { intros u Hu. apply in_app_iff in Hu as [Hu|Hu]; [left; exact (ODf u Hu)|right; exact Hu]. }
    assert (KD : forall t, In t (od ++ entry_dels (short_entry e) ++ src_dels h) -> kM (fst t) = false).
    { intros u Hu. unfold kM. destruct (DL u Hu) as [(-> & _ & _)|Hu'].
      - cbn [fst]. rewrite Z.eqb_refl, andb_false_r. reflexivity.
      - rewrite (KE u Hu'). reflexivity. }
    assert (NDD : List.NoDup (map fst (od ++ entry_dels (short_entry e) ++ src_dels h))).
    { rewrite map_app. apply mv_nodup_app; [|exact f_eh_nd|].
      - unfold od. destruct (bv_unsigned cap =? 0); repeat constructor. intros [].
      - intros a Ha Hb. apply in_map_iff in Ha as (u & <- & Hu). destruct (ODf u Hu) as (-> & _ & _).
        cbn [fst] in Hb. destruct (NC _ Hb) as [X|X]; [exact (NOE X)|exact (NOH X)]. }
    assert (DIN : incl (od ++ entry_dels (short_entry e) ++ src_dels h) (blocks L0 A0)).
    { intros u Hu. destruct (DL u Hu) as [(_ & _ & X)|X]; [exact X|exact (f_eh_in u X)]. }
    assert (CP : 0 < r_cap1).
    { rewrite <- C1. destruct (LV1 LV) as (Y1 & _). pose proof (rr_live_pos LV) as TP. rewrite HNO in Y1.
      clear - Y1 TP. lia. }
    exists (G :: f_RE ++ f_RH), gl, (List.filter (fun t => kM (fst t)) (blocks L0 A0)), [],
      (List.filter (fun t => negb (existsb (Z.eqb (fst t)) (map fst (od ++ entry_dels (short_entry e) ++ src_dels h))))
        (List.filter (fun t => negb (kM (fst t))) (blocks L0 A0))).
    split.
    { eapply Permutation_trans; [exact PN0|]. apply perm_skip.
      rewrite !map_app, mv_map_fst_entry, mv_map_fst_src. change (entry_nc (short_entry e)) with (entry_nc e).
      apply (Permutation_count_occ Z.eq_dec). intros x.
      pose proof (proj1 (Permutation_count_occ Z.eq_dec _ _) OG x) as CO.
      change (bv_unsigned out :: entry_nc e ++ src_nc h ++ f_RE ++ f_RH) with
        ([bv_unsigned out] ++ entry_nc e ++ src_nc h ++ f_RE ++ f_RH).
      rewrite !count_occ_app in *. clear - CO. lia. }
    split.
    { rewrite (f_nc4 es' RS). cbn [map fst]. apply perm_skip. apply Permutation_cons_append. }
    split; [exact (mv_split3 _ _ kM ND0 NDD DIN KD)|].
    split.
    { rewrite app_nil_r. apply NoDup_Permutation.
      - exact (NoDup_map_inv _ _ ND4).
      - eapply Permutation_NoDup; [apply Permutation_cons_append|]. constructor.
        + intros HB. apply filter_In in HB as (H0 & Hkp). cbn [fst] in Hkp. unfold kM, kE in Hkp.
          apply andb_prop in Hkp as (Hk1 & Hk2). apply mv_negb_out in Hk1. apply negb_true_iff in Hk2.
          apply Z.eqb_neq in Hk2.
          assert (NE : ~ In OUT' (entry_blocks (short_entry e))).
          { rewrite short_entry_blocks. intros X. apply Hk1. apply in_or_app. left. exact X. }
          destruct (BK2b OUT' r_cap1 H0 CP Hk2 NE (fun _ X => Hk1 (in_or_app _ _ _ (or_intror X)))) as (X & _).
          exact (X eq_refl).
        + apply NoDup_filter. exact (NoDup_map_inv _ _ ND0).
      - intros [x m]. rewrite in_app_iff, filter_In. cbn [fst In]. split.
        + intros H4. destruct (fin_rv x m H4) as [(H0 & No & Ne & Nh)|EOx].
          * left. split; [exact H0|]. unfold kM, kE. rewrite mv_negb_nin.
            -- cbn [andb]. apply negb_true_iff. apply Z.eqb_neq. exact No.
            -- intros Hx. apply in_app_iff in Hx as [Hx|Hx]; [exact (Ne Hx)|exact (Nh Hx)].
          * right. left. subst x. rewrite (mv_fst_uniq _ _ m r_cap1 ND4 H4 (f_new ES)). reflexivity.
        + intros [(H0 & Hkp)|[EQ|[]]].
          * unfold kM, kE in Hkp. apply andb_prop in Hkp as (Hk1 & Hk2). apply mv_negb_out in Hk1.
            apply negb_true_iff in Hk2. apply Z.eqb_neq in Hk2.
            apply (f_old_in4 x m H0 Hk2); intros X; apply Hk1; apply in_or_app; [left|right]; exact X.
          * injection EQ as <- <-. exact (f_new ES). }
    split; [intros x m H4; exact (r_blk_nn _ _ _ _ _ _ M4 H4)|].
    split; [intros [x m] Hu; exact (r_blk_nn _ _ _ _ _ _ HMR (DIN _ Hu))|].
    split; [exact NDD|].
    split.
    { intros u Hu. split.
      - destruct (DL u Hu) as [(-> & _ & _)|Hu'].
        + cbn [fst]. intros [X|X]; [exact (NGO X)|]. destruct (f_rest _ X) as (_ & X2 & _). exact (X2 eq_refl).
        + destruct (f_eh_notR (fst u) (f_eh_dels u Hu')) as (N1 & _ & N3).
          intros [X|X]; [exact (N1 (eq_sym X))|exact (N3 X)].
      - intros m HB. apply filter_In in HB as (_ & HB). cbn [fst] in HB. rewrite (KD u Hu) in HB. discriminate. }
    split.
    { intros u Hu. rewrite !filter_In in Hu. destruct Hu as ((_ & Hkp) & Hd). split.
      - apply negb_true_iff in Hkp. unfold kM, kE in Hkp. apply andb_false_iff in Hkp as [Hkp|Hkp].
        + apply negb_false_iff in Hkp. apply mv_inb in Hkp. apply in_app_iff in Hkp.
          destruct (f_eh_notR (fst u) Hkp) as (N1 & _ & N3).
          intros [X|X]; [exact (N1 (eq_sym X))|exact (N3 X)].
        + apply negb_false_iff in Hkp. apply Z.eqb_eq in Hkp. rewrite Hkp.
          intros [X|X]; [exact (NGO X)|]. destruct (f_rest _ X) as (_ & X2 & _). exact (X2 eq_refl).
      - exact (mv_negb_out _ _ Hd). }
    intros g0 Hg m Hm. destruct (GN g0 Hg) as (-> & C0).
    destruct f_out0 as [(_ & O0)|(Cp & _)]; [|rewrite C0 in Cp; clear - Cp; lia].
    rewrite O0 in Hm. pose proof (r_blk_rng _ _ _ _ _ _ HMR Hm) as (X & _). clear - X. lia.
Qed.

Lemma r_fin : SR (ms_segs B) (mkCfg (@YK11.mkst fx0 R8 (Z_to_bv 64 0x14330) mem5 (seg_rom (ms_segs B))) md4)
  (LI (rc := rc) B (API rc) E RI (t + 1) K).
Proof.
  pose proof r_seg as SEG. pose proof sr_mr as (M4 & W4 & B4).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ M4) as (Hh & Hl & _).
  assert (SV8 : p4_sv E t K s R8).
  { destruct RP7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RPr & _). exact (p4_sv_pres E t K s R7 R8 SV7 RPr). }
  destruct (p4_pick_rs rc B (API rc) L4 A4 mem5 _ fin_eok) as (es' & RS & EOK').
  destruct r_q as (Hq1 & Hq2 & LQ).
  pose proof HREL as ((tail & TAB) & GIN & GFR & HES & NDF & FDR & PA & NDS & ZS & NDT).
  assert (NN : Forall (fun x => 0 <= re_used x) es).
  { eapply Forall_impl; [|exact HES]. intros x (_ & _ & _ & _ & _ & _ & X7 & _). lia. }
  destruct (tk G SRC_TABLE GIN2 rr_G_h1) as (GIN4 & GK).
  assert (TAB5 : table_at B mem5 G es' tail').
  { destruct TB2 as (TL & TC).
    assert (EB : map entry_bytes es' = map entry_bytes (remove_at q (map short_entry es))).
    { rewrite (p4_rs_map entry_bytes _ _ (fun x y H => proj1 (p4_rs_facts x y H)) RS), p4_rat_map, map_map.
      apply map_ext. intros x. symmetry. apply short_entry_bytes. }
    split; [rewrite TL, <- (Forall2_length RS), p4_rat_map, length_map; reflexivity|].
    rewrite EB. apply (rk_rw_kb2 B mem2); [exact TC|]. intros i0 Hi0. cbn [cells_size csize] in Hi0.
    apply GK. unfold SRC_TABLE, SRC_ENTRY. lia. }
  assert (REL4 : relay_at (rc := rc) B L4 A4 mem5 t nfd G OUT' es' (remove_at q hj)).
  { split; [exists tail'; exact TAB5|]. split; [exact GIN4|]. split; [exact GFR|]. split; [exact EOK'|].
    split.
    { rewrite (p4_rs_map re_fd _ _ (fun x y H => proj1 (proj2 (proj2 (p4_rs_facts x y H)))) RS).
      exact (proj1 (p4_nodup_map_remove_at re_fd es q no_entry Hq1 NDF)). }
    split.
    { apply Forall_forall. intros y Hy. destruct (p4_f2_in_r _ _ _ y RS Hy) as (x & Hx & Rxy).
      rewrite (proj1 (proj2 (proj2 (p4_rs_facts x y Rxy)))). rewrite Forall_forall in FDR.
      exact (FDR x (p4_in_remove_at es q x Hq1 Hx)). }
    split; [exact (p4_f2_comb _ _ _ _ _ _ fin_pairs RS (fun x y z _ P R => p4_pair_rs rc B L4 A4 mem5 t x z y P R))|].
    split; [exact (proj1 (p4_nodup_map_remove_at snd hj q (h, i) Hq2 NDS))|].
    split; [exact fin_zero|].
    rewrite (p4_rs_target _ _ _ _ _ RS). exact fin_nd. }
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply p4_jump. }
  intros ms1 (can1 & -> & EQ1). destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R9 & -> & X1).
  assert (SV9 : p4_sv E t K s R9) by exact (p4_sv_eqv R8 R9 SV8 X1).
  rewrite <- SEG.
  eapply (MI_tail B API LS SH SK ra empty rc fx j E CS RI t K (fun _ _ _ r => tail_regs E t K r));
    [exact HF|exact CBc|intros; assumption|exact HW|].
  exists fx0, L4, A4, R9, mem5, md4, cl, (if send_off cl br (r_TOT e') then br else dd), gn, dd,
    (if send_off cl br (r_TOT e') then ei else 0), G, nfd, mx, r_no2, r_cap2, r_out2, es', (remove_at q hj).
  split; [rewrite ?SEG; reflexivity|].
  split; [exact FZ|]. split; [exact Ht|]. split; [exact Hk|]. split; [exact Hn|].
  split; [exact (p4_sv_tail E t K s R9 SV9)|].
  split; [exact M4|]. split; [exact W4|]. split; [exact B4|]. split; [exact INI7|].
  split; [exact fin_md|]. split; [exact RO7|].
  split; [exact (proj1 sr_ik)|]. split; [exact (proj2 sr_ik)|].
  split; [rewrite rr_out2, (p4_rs_target _ _ _ _ _ RS); exact fin_dk|].
  split; [rewrite <- (Forall2_length RS); exact fin_glob|].
  split; [(revert Hnfd; cbn; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia)|].
  split; [exact fin_out|].
  split; [rewrite rr_out2; eapply relay_at_t; [exact REL4|cbn; repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia]|].
  split; [rewrite <- (Forall2_length RS), remove_at_length by exact Hq1; lia|].
  split; [rewrite (p4_rs_cost _ _ _ RS); pose proof (slot_cost_remove_at es hj q LQ Hq1 NN); lia|].
  assert (NB4 : List.NoDup (map fst (blocks L4 A4))).
  { pose proof (r_ND L4 A4 mem5 md4 M4) as X. first [exact X|exact (proj1 (NoDup_ListNoDup _) X)]. }
  assert (LY04 : layout_le A0 L0 L4).
  { destruct RP1 as (_ & _ & _ & Y1 & N1 & _). destruct RP3 as (_ & _ & _ & Y2 & N2 & _).
    destruct RP5 as (_ & _ & _ & Y3 & N3 & _). destruct RP7 as (_ & _ & _ & Y4 & _).
    apply (ListFrame.lf_layout_trans A0 A3 L0 L3 L4); [lia| |exact Y4].
    apply (ListFrame.lf_layout_trans A0 A2 L0 L2 L3); [lia| |exact Y3].
    exact (ListFrame.lf_layout_trans A0 A1 L0 L1 L2 N1 Y1 Y2). }
  assert (NCS4 : SlotRI3.ncs (view_of G OUT' es' (remove_at q hj)) L4 A4 <= nc_wt es' (remove_at q hj)).
  { rewrite <- rr_out2.
    apply (SlotNcWt.ncs_le_wt (rc := rc) B (API rc) L4 A4 mem5 md4 t nfd G r_no2 r_cap2 r_out2 es' (remove_at q hj) M4
      fin_out).
    - rewrite rr_out2. exact REL4.
    - rewrite <- (Forall2_length RS), remove_at_length by exact Hq1. clear - Hes. lia.
    - exact NB4. }
  assert (WT4 : nc_wt es' (remove_at q hj) <= nc_wt (map short_entry es) hj).
  { rewrite (p4_rs_wt _ _ _ RS).
    pose proof (f_equal rv_wt (short_view G 0 es hj)) as SW. cbn [rv_wt view_of] in SW. rewrite SW.
    pose proof (remove_at_perm es q e Hq1) as PE. rewrite (nth_error_nth es q e Hqe) in PE.
    pose proof (remove_at_perm hj q (h, i) Hq2) as PH. rewrite (nth_error_nth hj q (h, i) Hqh) in PH.
    rewrite Forall_forall in NN.
    exact (SlotPass2Mv.p4_wt_remove es hj e (h, i) (remove_at q es) (remove_at q hj) PE PH
      (NN e (nth_error_In es q Hqe))). }
  pose proof cs_mr as (_ & W3 & _). pose proof RP7 as (_ & _ & _ & LY34 & _).
  unfold p4_lv4, p4_RV in RI7.
  apply RI7; [exact BK7b|intros x m Hx Nx; exact (proj1 (ck3 x m Hx Nx))
    |exact (fun p n n' Hp _ => ListFrame.lf_addr A3 L3 L4 p n W3 LY34 Hp)| | | | | | | | | |].
  - intros x m Hx. destruct (fin_rv x m Hx) as [(H0 & _)|EO]; [left; exact H0|right].
    unfold target_addrs. rewrite rr_out2. right. left. exact (eq_sym EO).
  - unfold pend_view.
    pose proof (p4_map_remove_at (fun p : hsrc * nat => map snd (hl_recs (hs_pending (fst p)))) hj q (h, i) Hq2) as PM.
    rewrite (nth_error_nth hj q (h, i) Hqh) in PM. exact PM.
  - unfold ek_view.
    pose proof (p4_perm_concat_map (fun p : hsrc * nat => ekeys_hl (hs_expected (fst p))) _ _
      (remove_at_perm hj q (h, i) Hq2)) as PM.
    rewrite (nth_error_nth hj q (h, i) Hqh) in PM. exact PM.
  - rewrite <- (Forall2_length RS), remove_at_length by exact Hq1. clear - Hes. lia.
  - rewrite remove_at_length by exact Hq2. clear - Hes LQ. lia.
  - rewrite rr_out2. exact (f_move es' RS).
  - exact NB4.
  - rewrite rr_out2. exact (SlotPass2Mv.p2_nc_keep _ _ _ _ _ _ _ _ HWF LY04 (f_move es' RS)).
  - rewrite rr_out2. exact NCS4.
  - exact WT4.
Qed.

End SRS.

Lemma cs_perm : Permutation (hl_recs H') (hl_recs H'' ++ ds).
Proof.
  destruct CS5 as [(_ & EH & ED & _)|(_ & ER)].
  - rewrite EH, ED, p4_ff0, p4_ft. cbn [app]. apply Permutation_refl.
  - exact (p4_ends_perm _ _ _ _ _ _ _ ER).
Qed.

Lemma cs_kept : forall x m, In (x, m) (blocks L2 A2) -> ~ In x (hs_blocks r_h2) -> In (x, m) (blocks L3 A3).
Proof. intros x m Hx Nx. exact (proj1 (ck2 x m Hx Nx)). Qed.

Lemma r_srs_call : SR (ms_segs B) (mkCfg (@YK11.mkst fx0 R6 (Z_to_bv 64 0x14320) mem4 (seg_rom (ms_segs B))) md3)
  (LI (rc := rc) B (API rc) E RI (t + 1) K).
Proof.
  pose proof r_seg as SEG. pose proof cs_mr as (M3 & W3 & Bd3).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ M3) as (Hh & Hl & _).
  assert (SV6 : p4_sv E t K s R6).
  { destruct RP5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RPr & _). exact (p4_sv_pres E t K s R5 R6 SV5 RPr). }
  pose proof SV6 as ((B2 & B3 & B4 & B20) & _ & _ & _ & _ & R9).
  assert (RA : ov_read_bytes rsegs mem4 (Z_to_bv 64 (slot_sp E + 40)) 8 = Some (le8 (Z_to_bv 64 (r_A1 + c)))).
  { pose proof AC5 as AC. rewrite AT5 in AC. destruct AC as ((_ & BY) & _). cbn [cells_bytes cbytes] in BY.
    rewrite app_nil_r in BY. rewrite SEG in BY. exact (p4_rd8 _ _ _ _ BY eq_refl). }
  assert (GN : bytes_at rsegs mem4 check_shape_done_c.G_NOUT (le8 (Z_to_bv 64 (r_A1 + c)))).
  { rewrite cs_at, <- SEG. exact GN5. }
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    assert (E2 : reg_get R6 2 = Z_to_bv 64 (slot_sp E)) by exact B2.
    assert (E9 : reg_get R6 9 = Z_to_bv 64 s) by exact R9.
    rewrite E2, E9. eapply (p4_done CSDc (slot_sp E) s); [exact RA|exact GN]. }
  intros ms1 (can1 & (a1 & ->) & EQ1). destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R7 & -> & X1).
  assert (SV7 : p4_sv E t K s R7) by (p4_svx X1 SV6).
  assert (RA7 : getr R7 1 = Z_to_bv 64 0x14330) by (etransitivity; [apply (getr_of_eqv _ _ _ X1); reflexivity|]; reflexivity).
  assert (A07 : getr R7 10 = Z_to_bv 64 (G_S + SRC_SIZE * Z.of_nat i)).
  { etransitivity; [apply (getr_of_eqv _ _ _ X1); reflexivity|]. cbn. rewrite Hs. reflexivity. }
  pose proof SV7 as ((S2 & _ & S4 & _) & _).
  rewrite <- SEG.
  pose proof cn_mr as (_ & W2 & _). pose proof RP5 as (_ & _ & _ & LY23 & _).
  destruct (RI5 H'' ds HV5 HC5 cs_perm BK5b cs_kept (p4_src_blk_of B L3 A3 mem4 _ _ SR5)
    (fun p n n' Hp _ => ListFrame.lf_addr A2 L2 L3 p n W2 LY23 Hp)
    ltac:(pose proof (r_ND L3 A3 mem4 md3 M3) as XN; first [exact XN|exact (proj1 (NoDup_ListNoDup _) XN)]))
    as (bnd3 & ROK & _ & RIK).
  pose proof r_kvals as (_ & _ & _ & KV). pose proof r_i4 as Hi.
  eapply SR_bind.
  { apply (SRSc fx0 L3 A3 R7 mem4 md3 bnd3 r_h3 i).
    - exact SEG.
    - exact (p4_cpk B API LS SH SK ra empty rc fx j E CS SOURCE_RESET_K L3 A3 R7 mem4 md3 0x14330 HF M3 W3 Bd3
        INI5 (proj1 cs_ik) RA7 ltac:(lia) eq_refl S2 S4 KV).
    - exact INI5.
    - exact RO5.
    - intros a Ha. apply r_gimg. p4_cst. lia.
    - exact Hi.
    - exact A07.
    - left. exact SR5.
    - destruct (p4_glob_cells mem4 (G_S + SRC_SIZE * Z.of_nat i + 60) 4) as (pad & PC); [p4_cst; lia|p4_cst; lia| |].
      + intros k0 Hk0. apply in_G_bss. p4_cst. lia.
      + exists pad. rewrite SEG. exact PC.
    - exact ROK. }
  intros c' (L4 & A4 & R8 & mem5 & md4 & -> & RP & INI & RO & ZZ & SRCB & _).
  destruct (SRCB SR5) as ((qs4 & LQ4 & RF) & _ & BKb). rewrite RA7.
  exact (r_fin R7 R8 L4 A4 mem5 md4 qs4 SV7 RP INI RO ZZ (RIK L4 A4 qs4 LQ4 RF) BKb).
Qed.
End CSE.

Lemma cn_kept : forall x m, In (x, m) (blocks L1 A1) -> ~ In x (hs_blocks r_h1) -> In (x, m) (blocks L2 A2).
Proof. intros x m Hx Nx. exact (proj1 (ck1 x m Hx Nx)). Qed.

Lemma r_cse_call : SR (ms_segs B) (mkCfg (@YK11.mkst fx0 R4 (Z_to_bv 64 0x1430c) mem3 (seg_rom (ms_segs B))) md2)
  (LI (rc := rc) B (API rc) E RI (t + 1) K).
Proof.
  pose proof r_seg as SEG. pose proof cn_mr as (M2 & W2 & Bd2).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ M2) as (Hh & Hl & _).
  assert (SV4 : p4_sv E t K s R4).
  { destruct RP3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RPr & _). exact (p4_sv_pres E t K s R3 R4 SV3 RPr). }
  pose proof SV4 as ((B2 & _) & _ & _ & _ & _ & R9).
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    assert (E2 : reg_get R4 2 = Z_to_bv 64 (slot_sp E)) by exact B2.
    assert (E9 : reg_get R4 9 = Z_to_bv 64 s) by exact R9.
    rewrite E2, E9. apply (p4_ends (slot_sp E) s). }
  intros ms1 (can1 & -> & EQ1). destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R5 & -> & X1).
  assert (SV5 : p4_sv E t K s R5) by (p4_svx X1 SV4).
  assert (RA5 : getr R5 1 = Z_to_bv 64 0x14320) by (etransitivity; [apply (getr_of_eqv _ _ _ X1); reflexivity|]; reflexivity).
  assert (A05 : getr R5 10 = Z_to_bv 64 (G_S + SRC_SIZE * Z.of_nat i)).
  { etransitivity; [apply (getr_of_eqv _ _ _ X1); reflexivity|]. cbn. rewrite Hs. reflexivity. }
  assert (A15 : getr R5 11 = Z_to_bv 64 0x102e9) by (etransitivity; [apply (getr_of_eqv _ _ _ X1); reflexivity|]; reflexivity).
  assert (A25 : getr R5 12 = Z_to_bv 64 (slot_sp E + 40)) by (etransitivity; [apply (getr_of_eqv _ _ _ X1); reflexivity|]; reflexivity).
  pose proof SV5 as ((S2 & _ & S4 & _) & _).
  pose proof r_sp as (SPLO & SPHI & SPAL). pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  assert (PFV : bv_unsigned (getr R5 11) = PF_ADDR) by (rewrite A15; apply unsigned_lit; unfold PF_ADDR; lia).
  assert (ATV : bv_unsigned (getr R5 12) = slot_sp E + 40)
    by (rewrite A25; apply unsigned_lit; unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia).
  rewrite <- SEG.
  assert (GN01 : gn = 0 \/ gn = 1) by (destruct rr_gn as [(X & _)|(X & _)]; [left|right]; exact X).
  pose proof rr_mr2 as (_ & W1 & _). pose proof RP3 as (_ & _ & _ & LY12 & _).
  destruct (RI3 E' H' SHR3 SHL3 ER3 EV3 EC3 NDH3 TH3 BK3b BK3c cn_kept (p4_src_blk_of B L2 A2 mem3 _ _ SR3)
    (fun p n n' Hp _ => ListFrame.lf_addr A1 L1 L2 p n W1 LY12 Hp)
    ltac:(pose proof (r_ND L2 A2 mem3 md2 M2) as XN; first [exact XN|exact (proj1 (NoDup_ListNoDup _) XN)])
    gn (skipn (Z.to_nat r_A1) r_ob) GN01) as (bnd2 & ROK & _ & RIK).
  pose proof r_kvals as (_ & _ & KV & _). pose proof r_i4 as Hi.
  eapply SR_bind.
  { apply (CSEc fx0 L2 A2 R5 mem3 md2 bnd2 r_h2 i gn r_A1 r_no2 r_out2 r_ob [] PF_SLACK).
    - exact SEG.
    - exact (p4_cpk B API LS SH SK ra empty rc fx j E CS CHECK_SHAPE_ENDS_K L2 A2 R5 mem3 md2 0x14320 HF M2 W2 Bd2
        INI3 (proj1 cn_ik) RA5 ltac:(lia) eq_refl S2 S4 KV).
    - exact INI3.
    - exact RO3.
    - intros a Ha. apply r_gimg. p4_cst. lia.
    - exact Hi.
    - exact A05.
    - exact SR3.
    - exact NDH3.
    - exact cn_hn.
    - rewrite PFV, SEG. apply p4_pf_bytes. rewrite <- SEG. exact RO3.
    - intros [].
    - rewrite PFV. unfold PF_ADDR, PF_SLACK. cbn. lia.
    - right. rewrite PFV. split; [unfold PF_ADDR; lia|]. split; [unfold PF_ADDR, PF_SLACK; cbn; lia|].
      intros i0 Hi0. rewrite SEG. apply p4_pf_ro. unfold PF_SLACK in Hi0. cbn in Hi0. lia.
    - rewrite ATV. unfold slot_sp, SLOT_FRAME. Z.div_mod_to_equations. lia.
    - rewrite (r_svsp R5 SV5), ATV. lia.
    - rewrite ATV. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
    - right. rewrite PFV, ATV. unfold PF_ADDR, PF_SLACK. cbn. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
    - rewrite ATV. rewrite AT3 in AC3. exact AC3.
    - lia.
    - exact GG3.
    - exact GN3.
    - exact GO3.
    - exact OB3.
    - exact rr_ob_len.
    - unfold r_ob. destruct r_lv eqn:LV; [right|left; reflexivity].
      destruct (LV1 LV) as (C1 & _ & IN & FR & _). rewrite HNO in C1. exists CAP'.
      rewrite rr_no2, LV, rr_out2. destruct (ck1 OUT' CAP' IN rr_out_h1) as (IN2 & _ & NH2).
      split; [lia|]. split; [exact IN2|]. split; [exact FR|]. exact NH2.
    - exact rr_A1_le.
    - intros G0. destruct (cn_ends G0) as (rs' & ds' & X). cbv zeta. unfold r_h2. cbn [hs_held set_exp_held].
      rewrite X. discriminate.
    - exact ROK. }
  intros c' (L3 & A3 & R6 & mem4 & md3 & H'' & ds & c & -> & RP & INI & (qs3 & LQ3 & RF) & RO & SR & HV & HC & ND &
    CSx & AC & _ & _ & GN & _ & _ & _ & BKb).
  rewrite RA5.
  exact (r_srs_call R5 R6 L3 A3 mem4 md3 H'' ds c qs3 SV5 ATV RP INI (RIK L3 A3 qs3 LQ3 RF) RO SR HV HC CSx AC GN BKb).
Qed.

End CNL.

Lemma rr_bk1 : forall x m, In (x, m) (blocks L1 A1) ->
  (In (x, m) (blocks L0 A0) /\ x <> bv_unsigned out /\ ~ In x (entry_blocks (short_entry e)) /\
   (re_eof e = 0 -> ~ In x (hs_blocks h))) \/ (re_eof e = 0 /\ In x (hs_blocks r_h1)) \/ x = OUT'.
Proof.
  intros x m Hx. destruct (BK2c x m Hx) as [X|[(E0 & X)|X]]; [left; exact X| |right; right; exact X].
  right. left. split; [exact E0|]. unfold r_h1. rewrite (proj2 (Z.eqb_eq _ _) E0). exact X.
Qed.

Lemma rr_bk3 : forall x m, In (x, m) (blocks L0 A0) -> 0 < m -> x <> bv_unsigned out ->
  ~ In x (entry_blocks (short_entry e)) -> (re_eof e = 0 -> ~ In x (hs_blocks h)) ->
  x <> OUT' /\ (re_eof e = 0 -> ~ In x (hs_blocks r_h1)).
Proof.
  intros x m H0 Hm N1 N2 N3. destruct (BK2b x m H0 Hm N1 N2 N3) as (X1 & X2). split; [exact X1|].
  intros E0. unfold r_h1. rewrite (proj2 (Z.eqb_eq _ _) E0). exact (X2 E0).
Qed.

Lemma rr_nd1 : re_eof e = 0 -> NoDup (OUT' :: hs_blocks r_h1).
Proof. intros E0. unfold r_h1. rewrite (proj2 (Z.eqb_eq _ _) E0). exact (ND2 E0). Qed.

Lemma rr_outb : (OUT' = bv_unsigned out /\ (0 < bv_unsigned cap -> In (bv_unsigned out, bv_unsigned cap) (blocks L1 A1))) \/
  In (OUT', CAP') (blocks L1 A1).
Proof.
  destruct r_lv eqn:LV.
  - right. destruct (LV1 LV) as (_ & _ & X & _). exact X.
  - left. destruct (LV0 LV) as (_ & X & EO). split; [exact EO|]. intros C. exact (proj1 (X C)).
Qed.

Lemma rr_h1eq : re_eof e <> 0 -> r_h1 = h.
Proof. intros NE. unfold r_h1. rewrite (proj2 (Z.eqb_neq _ _) NE). reflexivity. Qed.

Lemma rr_pend1 : re_eof e = 0 -> hl_recs (hs_pending r_h1) = [].
Proof.
  intros E0. unfold r_h1. rewrite (proj2 (Z.eqb_eq _ _) E0). destruct (EOF0 E0) as (_ & _ & X & _). exact X.
Qed.

Lemma rr_qla : r_lv = true ->
  live_at L1 A1 (resolveF qs1 (remove_entry_out (send_live cl br dd 1) (bv_unsigned mx) 0 (bv_unsigned cap)
    (short_entry e) h 0 (drain_start (known_at L0 A0) (known_at L0 A0 (bv_unsigned out)) (short_entry e) h)))
    OUT' r_cap1.
Proof. intros LV. rewrite <- (proj1 CAPX LV). exact (proj1 QL1 LV). Qed.

Lemma rr_qlb : r_lv = false -> OUT' = bv_unsigned out /\ r_cap1 = bv_unsigned cap.
Proof. intros LV. split; [exact (proj2 (proj2 (LV0 LV)))|exact (proj2 CAPX LV)]. Qed.

Lemma rr_qlc : re_eof (short_entry e) = 0 ->
  src_links L1 A1 qs1 (known_at L0 A0) (after_drain_adr (send_live cl br dd 1) (bv_unsigned mx) 0
    (bv_unsigned cap) (short_entry e) h 0 (drain_start (known_at L0 A0) (known_at L0 A0 (bv_unsigned out))
      (short_entry e) h)) r_h1.
Proof.
  intros E0. change (re_eof e = 0) in E0. unfold r_h1. rewrite (proj2 (Z.eqb_eq _ _) E0). exact (proj2 QL1 E0).
Qed.

Lemma r_rr_done : SR (ms_segs B) (mkCfg (@YK11.mkst fx0 R2 (Z_to_bv 64 0x142f4) mem2 (seg_rom (ms_segs B))) md1)
  (LI (rc := rc) B (API rc) E RI (t + 1) K).
Proof.
  pose proof r_seg as SEG. pose proof rr_mr2 as (M1 & W1 & Bd1).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ M1) as (Hh & Hl & _).
  assert (RPr : regs_preserved R1 R2) by (destruct RP1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  assert (SV2 : p4_sv E t K s R2) by exact (p4_sv_pres E t K s R1 R2 SV1 RPr).
  assert (EO2 : getr R2 18 = Z_to_bv 64 (p4_rflag (re_eof e)))
    by exact (eq_trans (RPr 18 ltac:(unfold callee_saved; lia)) EO1).
  pose proof SV2 as ((B2 & _) & _ & _ & _ & _ & R9).
  pose proof r_sp as (SPLO & SPHI & SPAL). pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof r_i4 as Hi.
  assert (PZ : re_eof e = 0 -> bytes_at rsegs mem2 (s + 24) (le4 (Z_to_bv 64 0))).
  { intros E0. pose proof rr_h1 as S1. unfold r_h1 in S1. rewrite (proj2 (Z.eqb_eq _ _) E0) in S1.
    destruct (EOF0 E0) as (_ & _ & PN & _).
    destruct S1 as (_ & _ & _ & _ & _ & (LC & _) & _).
    destruct LC as ((_ & BY) & _). cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
    rewrite bytes_at_app in BY. destruct BY as (_ & BY). rewrite bytes_at_app in BY. destruct BY as (BY & _).
    rewrite length_le8 in BY. unfold hl_n in BY. rewrite PN in BY. cbn [length Z.of_nat] in BY.
    rewrite SEG in BY. replace (s + 24) with (G_S + SRC_SIZE * Z.of_nat i + 16 + Z.of_nat 8) by (rewrite Hs; lia).
    exact BY. }
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    assert (E2 : reg_get R2 2 = Z_to_bv 64 (slot_sp E)) by exact B2.
    assert (E9 : reg_get R2 9 = Z_to_bv 64 s) by exact R9.
    assert (E18 : reg_get R2 18 = Z_to_bv 64 (if re_eof e =? 0 then 1 else 0)) by exact EO2.
    rewrite E2, E9, E18. apply (p4_mid CNRc (slot_sp E) s (re_eof e)); [exact rr_eof01| | | |exact PZ].
    - rewrite Hs. clear - Hi. p4_cst. lia.
    - rewrite Hs. clear - Hi. p4_cst. Z.div_mod_to_equations. lia.
    - unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  intros ms1 (can1 & -> & EQ1). destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R3 & -> & X1).
  assert (SV3 : p4_sv E t K s R3) by (p4_svx X1 SV2).
  assert (RA3 : getr R3 1 = Z_to_bv 64 0x1430c) by (etransitivity; [apply (getr_of_eqv _ _ _ X1); reflexivity|]; reflexivity).
  assert (A03 : getr R3 10 = Z_to_bv 64 (G_S + SRC_SIZE * Z.of_nat i)).
  { etransitivity; [apply (getr_of_eqv _ _ _ X1); reflexivity|]. cbn. rewrite Hs. reflexivity. }
  assert (A13 : getr R3 11 = Z_to_bv 64 (slot_sp E + 40)) by (etransitivity; [apply (getr_of_eqv _ _ _ X1); reflexivity|]; reflexivity).
  pose proof SV3 as ((S2 & _ & S4 & _) & _).
  assert (ATV : bv_unsigned (getr R3 11) = slot_sp E + 40)
    by (rewrite A13; apply unsigned_lit; unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia).
  rewrite <- SEG.
  pose proof r_pair as (_ & _ & _ & _ & SSK & NDH & _). cbn [fst] in SSK, NDH.
  pose proof r_eok as (_ & _ & _ & _ & _ & _ & EUL & _ & _ & _ & _ & _ & _ & _ & EKS).
  assert (K14 : Forall (fun x => 14 <= Z.of_nat (length (key_text x))) (re_keys e)).
  { eapply Forall_impl; [|exact EKS]. intros k (_ & _ & _ & _ & X & _). lia. }
  pose proof HREL as (_ & _ & _ & HES & _).
  assert (NN : Forall (fun x => 0 <= re_used x) es).
  { eapply Forall_impl; [|exact HES]. intros x (_ & _ & _ & _ & _ & _ & X7 & _). lia. }
  pose proof r_pcost as (_ & K26).
  destruct (p4_cnl_bound e h i (hs_held h) (p4_lines e h) es hj K (p4_nth_combine es hj q e (h, i) Hqe Hqh) NN Hcost K26
    K14 (p4_held_len _ _ NDH SSK) rr_wn) as (BND1 & BND2).
  pose proof RP1 as (_ & _ & _ & LY01 & _).
  destruct (RI1 OUT' CAP' r_lv r_h1 rr_qla rr_qlb rr_qlc rr_bk1 BK2a rr_bk3 rr_nd1 rr_outb rr_h1eq rr_pend1
    rr_held1 rr_exp1
    (p4_src_blk_of B L1 A1 mem2 _ _ rr_h1)
    (fun p n n' Hp _ => ListFrame.lf_addr A0 L0 L1 p n HWF LY01 Hp)
    ltac:(pose proof (r_ND L1 A1 mem2 md1 M1) as XN; first [exact XN|exact (proj1 (NoDup_ListNoDup _) XN)])
    ltac:(change (hs_held r_h1) with r_H1; change (hs_expected r_h1) with r_E1; rewrite rr_held1, rr_texts1;
          exact BND1)
    ltac:(intros E0; cbn [short_entry re_eof] in E0; unfold r_h1; rewrite (proj2 (Z.eqb_eq _ _) E0);
          exact (ECA1 E0))
    ltac:(intros E0; cbn [short_entry re_eof] in E0; unfold r_h1; rewrite (proj2 (Z.eqb_eq _ _) E0);
          exact (PPK1 E0)))
    as (bnd1 & ROK & ROOM & RIK).
  pose proof r_kvals as (_ & KV & _).
  pose proof HGL as (_ & _ & _ & _ & G5 & _).
  assert (GG : bytes_at (ms_segs B) mem2 G_GONE [Z_to_bv 8 gn]).
  { assert (C : rw_cells (ms_segs B) mem2 CheckRep.G_GONE [C1 (Z_to_bv 8 gn)]).
    { apply (rk_rw_kb2 B mem0); [exact G5|]. intros i0 Hi0. cbn [cells_size csize] in Hi0.
      assert (IA : img_plain B (CheckRep.G_GONE + i0)) by (apply r_gimg; p4_cst; lia).
      apply rr_gb; [exact IA|].
      apply rr_nE; [exact (proj1 IA)|p4_cst; lia|p4_cst; lia|p4_cst; lia|p4_cst; lia|p4_cst; lia|intros _; p4_cst; lia]. }
    destruct C as ((_ & BY) & _). cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exact BY. }
  assert (GNO : bytes_at (ms_segs B) mem2 G_NOUT (le8 r_no2) /\ bytes_at (ms_segs B) mem2 G_OUT (le8 r_out2)).
  { pose proof rr_outv as ((_ & BY) & _). cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
    rewrite !bytes_at_app, !length_le8 in BY. destruct BY as (_ & BN & _ & BO). split.
    - replace G_NOUT with (G_OUTV + Z.of_nat 8) by (p4_cst; reflexivity). exact BN.
    - replace G_OUT with (G_OUTV + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by (p4_cst; reflexivity). exact BO. }
  assert (OB : bytes_at (ms_segs B) mem2 (bv_unsigned r_out2) r_ob).
  { rewrite rr_out2. unfold r_ob. destruct r_lv eqn:LV.
    - destruct (LV1 LV) as (_ & _ & _ & _ & BY & _). cbn [app] in BY. rewrite app_assoc in BY.
      apply bytes_at_app in BY. exact (proj1 BY).
    - destruct (LV0 LV) as (_ & _ & EO). rewrite EO. pose proof (bv_unsigned_in_range 64 out) as BR.
      unfold bv_modulus in BR. split; [lia|]. split; [cbn [length Z.of_nat]; lia|]. intros i0 Hi0. cbn in Hi0. lia. }
  eapply SR_bind.
  { apply (CNLc fx0 L1 A1 R3 mem2 md1 bnd1 r_h1 i gn 0 r_no2 r_out2 r_ob).
    - exact SEG.
    - exact (p4_cpk B API LS SH SK ra empty rc fx j E CS CHECK_NO_LOSS_K L1 A1 R3 mem2 md1 0x1430c HF M1 W1 Bd1
        INI1 (proj1 rr_ik) RA3 ltac:(lia) eq_refl S2 S4 KV).
    - exact INI1.
    - exact RO2.
    - intros a Ha. apply r_gimg. p4_cst. lia.
    - exact Hi.
    - exact A03.
    - exact rr_h1.
    - change (hs_held r_h1) with r_H1. rewrite rr_held1. exact NDH.
    - change (hs_expected r_h1) with r_E1. rewrite rr_hn1. exact BND2.
    - change (hs_held r_h1) with r_H1. change (hs_expected r_h1) with r_E1. rewrite rr_held1, rr_texts1. exact BND1.
    - rewrite ATV. unfold slot_sp, SLOT_FRAME. Z.div_mod_to_equations. lia.
    - rewrite (r_svsp R3 SV3), ATV. lia.
    - rewrite ATV. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
    - rewrite ATV. exact rr_at.
    - destruct rr_gn as [(X & _)|(X & _)]; lia.
    - exact GG.
    - exact (proj1 GNO).
    - exact (proj2 GNO).
    - exact OB.
    - exact rr_ob_len.
    - unfold r_ob. destruct r_lv eqn:LV; [right|left; reflexivity].
      destruct (LV1 LV) as (C1 & _ & IN & FR & _). rewrite HNO in C1. exists CAP'.
      rewrite rr_no2, LV, rr_out2. split; [lia|]. split; [exact IN|]. split; [exact FR|exact rr_out_h1].
    - rewrite rr_no2. pose proof rr_tot. destruct r_lv; lia.
    - exact rr_cnl_pre.
    - exact ROK.
    - exact ROOM. }
  intros c' (L2 & A2 & R4 & mem3 & md2 & E' & H' & -> & RP & INI & (qs2 & LQ2 & RF & SHR & SHL) & RO & SR & ER & EV &
    EC & ND & _ & TH & AC & GG' & GN & GO & OBb & _ & BKb & BKc).
  rewrite RA3.
  exact (r_cse_call R3 R4 L2 A2 mem3 md2 E' H' qs2 SV3 ATV RP INI (RIK L2 A2 qs2 LQ2 RF) SHR SHL RO SR ER EV EC ND TH AC
    GN GG' GO OBb BKb BKc).
Qed.

End RR.

Lemma p4_lit64 : forall z, (0 <=? z) && (z <? 2 ^ 64) = true -> 0 <= z < 2 ^ 64.
Proof. intros z H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. Qed.

Lemma r_gb40 : forall x, x <= 0x31b00 -> x <= slot_sp E - 16.
Proof. intros x Hx. p4_num. lia. Qed.

Lemma r_gc : forall x, (x <=? 0x31b00) = true -> x <= slot_sp E - 16.
Proof. intros x Hx. apply r_gb40. apply Z.leb_le. exact Hx. Qed.

Lemma r_blk40 : forall x, x <= @YM05.alloc_ceiling rc + 8 -> x <= slot_sp E - 16.
Proof. intros x Hx. p4_num. lia. Qed.

Lemma r_ha96 : G_S + SRC_SIZE * Z.of_nat i + 96 <= @YM05.alloc_ceiling rc.
Proof. pose proof r_i4 as Hi. pose proof (@YM05.alloc_ceiling_value rc) as ACV. p4_cst. lia. Qed.

Lemma r_kb8 : p4_kb B mem0 r_m1 (@YM05.alloc_ceiling rc + 8).
Proof. intros a Ha. apply r_kb1. p4_num. lia. Qed.

Lemma r_rr_call : forall R1, p4_sv E t K s R1 -> getr R1 1 = Z_to_bv 64 0x142f4 ->
  getr R1 10 = Z_to_bv 64 (re_fd e) -> getr R1 18 = Z_to_bv 64 (p4_rflag (re_eof e)) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx0 R1 (Z_to_bv 64 RELAY_REMOVE) r_m1 (seg_rom (ms_segs B))) md0)
    (LI (rc := rc) B (API rc) E RI (t + 1) K).
Proof.
  intros R1 SV1 RA1 FD1 EO1.
  pose proof r_seg as SEG. pose proof r_kb1 as KB. pose proof r_pair as PO. pose proof r_eok as EOK.
  destruct r_q as (Hq1 & Hq2 & LQ). pose proof r_pcost as (PCK & K26).
  pose proof HF as (FF & _).
  destruct (p4_ff _ _ _ _ _ _ _ FF) as (_ & TP & EOff & _).
  pose proof (p4_errno _ _ _ _ _ _ _ FF) as (EA & EIMG).
  pose proof r_kb8 as KB8.
  pose proof HREL as ((tail & TAB) & GIN & GFR & HES & NDF & FDR & PA & NDS & ZS & NDT).
  pose proof HGL as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & ER & HCL & HBR & HGN &
    HDD & HEI & HGG & HMX).
  pose proof HOUT as ((O0 & junk0 & OD) & OCAP).
  assert (O0N : O0 = []).
  { destruct OD as [(_ & _ & _ & ->)|(_ & _ & _ & _ & _ & LO & _)]; [reflexivity|].
    rewrite HNO in LO. destruct O0; [reflexivity|cbn [length] in LO; lia]. }
  subst O0.
  cbv zeta in PO. cbn [fst snd] in PO.
  destruct PO as (SRC & Hi4 & FDE & SKU & SSK & NDH & EXP0 & PN & PCP & PLW & ECAP & HCAP).
  pose proof EOK as (EO01 & SK01 & EP1 & EP2 & EFD & ECP & EUL & EUS & EUZ & EBU & ENH & EHP & ENA & ENT & EKS).
  assert (FDS : bv_signed (getr R1 10) = re_fd e) by (rewrite FD1; apply p4_signed; lia).
  assert (CAPR : 0 <= bv_unsigned cap <= TBBYTES).
  { pose proof (bv_unsigned_in_range 64 cap) as X. unfold bv_modulus in X. lia. }
  assert (MXR : 0 <= bv_unsigned mx <= 255).
  { pose proof (bv_unsigned_in_range 64 mx) as X. unfold bv_modulus in X. lia. }
  assert (NQE : nth_error (map short_entry es) q = Some (short_entry e)) by (rewrite nth_error_map, Hqe; reflexivity).
  assert (K14 : Forall (fun x => 14 <= Z.of_nat (length (key_text x))) (re_keys e)).
  { eapply Forall_impl; [|exact EKS]. intros k (_ & _ & _ & _ & X & _). clear - X. lia. }
  pose proof (keys_total_count _ K14) as KC. unfold pair_cost in PCK. cbn [fst] in PCK.
  pose proof (Zle_0_nat (length (pending_stream h))) as NN1. pose proof (Zle_0_nat (length (re_U e))) as NN2.
  pose proof (keys_total_nonneg (re_keys e)) as NN3. pose proof (Zle_0_nat (length (re_keys e))) as NN4.
  assert (PLB : Z.of_nat (length (pending_stream h)) < 2 ^ 26)
    by (clear - PCK K26 NN1 NN2 NN3 EUL; destruct (re_skip e =? 0); lia).
  assert (FND : find (fun x => re_fd x =? re_fd (short_entry e)) (map short_entry es) = Some (short_entry e)).
  { destruct (find (fun x => re_fd x =? re_fd (short_entry e)) (map short_entry es)) as [x|] eqn:EF.
    - apply find_some in EF as [Hx Fx]. apply Z.eqb_eq in Fx. rewrite (r_fd_uniq x Hx Fx). reflexivity.
    - exfalso. pose proof (find_none _ _ EF (short_entry e) r_in_e1) as X. cbv beta in X.
      rewrite Z.eqb_refl in X. discriminate. }
  assert (DIN : re_eof (short_entry e) = 0 ->
      relay_instance_gone_b_lem.dr_inv (drain_init 0 (bv_unsigned cap) (short_entry e) h) /\
      relay_instance_gone_b_lem.dr_rest (drain_init 0 (bv_unsigned cap) (short_entry e) h) = bzs (pending_stream h)).
  { intros E0. destruct (SKU E0) as [SKO SKW].
    pose proof SRC as (_ & _ & _ & _ & _ & LP & _ & OFFD & _).
    apply (relay_instance_gone_b_lem.rig_dinit 0 (bv_unsigned cap) (short_entry e) h);
      cbn [short_entry re_skip re_U re_cap].
    - exact SK01.
    - exact SKO.
    - exact SKW.
    - clear - EUL EUS; lia.
    - exact EUZ.
    - exact r_capc.
    - exact OFFD.
    - destruct LP as (_ & _ & _ & _ & _ & HR). apply Forall_forall. intros r Hr.
      destruct (proj1 (Forall_forall _ _) HR r Hr) as (_ & _ & _ & _ & L1x). exact (L1x eq_refl). }
  assert (DR3 : re_eof (short_entry e) = 0 -> SlotP5R3G.drain3 (short_entry e) h).
  { intros E0. cbn [fst] in EXP0, PLW, ECAP. apply SlotDrain3.drain3_holds.
    - cbn [short_entry re_cap]. clear - ECP; lia.
    - unfold ent_ka. cbn [short_entry re_hp re_kh]. destruct (Z.eqb_spec (re_hp e) 0); [lia|].
      destruct EHP as [(X & _)|(_ & _ & _ & K8 & _)]; [contradiction|lia].
    - exact (r_J1 E0).
    - pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & OFFD & _).
      destruct OFFD as [(_ & X)|(r & rs & _ & X)]; cbn [fst] in X; lia.
    - unfold re_nheld. cbn [short_entry re_keys]. rewrite length_map.
      clear - PCK K26 KC NN1 NN2 NN3 NN4 EUL. destruct (re_skip e =? 0); lia.
    - pose proof ECAP as EC'. unfold ecap_ok in EC'.
      destruct EC' as [X|(k0 & Hk0 & X)]; [left; exact X|right; exists k0; split; [lia|exact X]].
    - unfold hl_n. rewrite EXP0. cbn [length Z.of_nat]. unfold WRITE_MAX, OPS_MAX in *. clear - PLW Ht. lia. }
  assert (CAPN : remove_entry_cap (send_live cl br dd 1) (bv_unsigned mx) 0 (bv_unsigned cap) (short_entry e) h <=
      SlotCaps3.NMAX).
  { apply p4_cap_nmax; [exact CAPR|exact DIN|].
    pose proof (rr_wn [] [] e) as WN. unfold p4_lines in WN. cbn [short_entry re_eof re_keys]. rewrite short_keys_total.
    clear - WN PCK K26 NN1 NN2 NN3 EUL. destruct (re_eof e =? 0); destruct (re_skip e =? 0); lia. }
  assert (KH : re_hp (short_entry e) <> 0 -> re_kh (short_entry e) <> 0).
  { cbn [short_entry re_hp re_kh]. intros HP0. destruct EHP as [(X & _)|(_ & _ & _ & K8 & _)]; [contradiction|lia]. }
  assert (OZ0 : bv_unsigned cap = 0 -> forall m, ~ In (bv_unsigned out, m) (blocks L0 A0)).
  { intros C0 m Hm. destruct OD as [(_ & OZ & _)|(CP & _)]; [|lia].
    pose proof (r_blk_rng L0 A0 mem0 md0 _ _ HMR Hm) as (LO & _). lia. }
  destruct (P4r E K L0 A0 G (bv_unsigned out) (map short_entry es) hj q (short_entry e) h i (send_live cl br dd 1)
    (bv_unsigned mx) (bv_unsigned cap) ltac:(rewrite short_view; exact HRI)
    ltac:(pose proof (r_ND L0 A0 mem0 md0 HMR) as XN; first [exact XN|exact (proj1 (NoDup_ListNoDup _) XN)])
    HWF ltac:(rewrite short_cost; exact Hcost)
    ltac:(rewrite short_target; exact NDT) NQE Hqh
    (p4_ent_blk_of B L0 A0 r_m1 (short_entry e) (p4_ent_kb B L0 A0 mem0 r_m1 e KB8 EOK))
    (p4_src_blk_of B L0 A0 mem0 _ h SRC)
    ltac:(destruct OD as [(X & _)|(_ & _ & X & _)]; [left; exact X|right; exact X]) MXR CAPR
    ltac:(cbn [short_entry re_fd]; clear - EFD; lia) FND DR3 CAPN KH OZ0
    ltac:(rewrite length_map; exact Hes) ltac:(clear - Hes LQ; lia))
    as (bnd & ROK & ROOM & RIK).
  pose proof r_kvals as (KV & _).
  destruct r_mu1 as [MU WM].
  destruct (p4_keep_mu B API LS SH SK ra empty rc fx j E CS mem0 r_m1 HF MU WM HIK HST) as [IK1 ST1].
  pose proof SV1 as ((S2 & _ & S4 & _) & _).
  pose proof r_i4 as Hi.
  assert (RW1 : forall a cs, rw_cells (ms_segs B) mem0 a cs -> a + Z.of_nat (cells_size cs) <= slot_sp E - 16 ->
    rw_cells (ms_segs B) r_m1 a cs) by (intros a cs H L; exact (p4_rw_kb B mem0 r_m1 _ a cs KB H L)).
  assert (BY1 : forall a bs, bytes_at (ms_segs B) mem0 a bs -> a + Z.of_nat (length bs) <= slot_sp E - 16 ->
    bytes_at (ms_segs B) r_m1 a bs) by (intros a bs H L; exact (p4_by_kb B mem0 r_m1 _ a bs KB H L)).
  assert (NQ' : nth q (map short_entry es) no_entry = short_entry e).
  { change no_entry with (short_entry no_entry). rewrite map_nth. rewrite (nth_error_nth es q no_entry Hqe). reflexivity. }
  assert (GB : G + 896 <= @YM05.alloc_ceiling rc) by (destruct GFR as (_ & X & _); exact X).
  eapply SR_bind.
  { apply (RRc fx0 L0 A0 R1 r_m1 md0 bnd (map short_entry es) G tail h i (p4_fs hj) (p4_os hj) [] junk0
      cl br dd ei mx nout cap out).
    - exact SEG.
    - exact (p4_cpk B API LS SH SK ra empty rc fx j E CS RELAY_REMOVE_K L0 A0 R1 r_m1 md0 0x142f4 HF r_mr1 HWF HBD
        HINIT IK1 RA1 (p4_lit64 0x142f4 eq_refl) eq_refl S2 S4 KV).
    - exact HINIT.
    - unfold errno_addr, ERRNO_OFF. rewrite EOff. reflexivity.
    - rewrite EA. reflexivity.
    - rewrite EA. apply Z.leb_le. vm_compute. reflexivity.
    - exact r_ro1.
    - intros a Ha. apply r_gimg. clear - Ha. p4_cst. lia.
    - intros a Ha. apply r_gimg2. clear - Ha. p4_cst. lia.
    - exact EIMG.
    - exact (p4_end5 _ _ _ _ _ _ _ FF).
    - rewrite FDS. clear - EFD. lia.
    - apply RW1; [exact G12|apply r_gc; vm_compute; reflexivity].
    - destruct G2 as ((_ & BYW) & _). cbn [cells_bytes cbytes] in BYW. rewrite app_nil_r, bytes_at_app, length_le4 in BYW.
      destruct BYW as (_ & BYW). apply BY1; [|apply r_gc; vm_compute; reflexivity].
      replace G_WAKE1 with (G_WAKE0 + Z.of_nat 4) by (p4_cst; reflexivity). exact BYW.
    - rewrite length_map. apply RW1; [exact G8|apply r_gc; vm_compute; reflexivity].
    - apply RW1; [exact G10|apply r_gc; vm_compute; reflexivity].
    - rewrite length_map. clear - Hes. lia.
    - exact GIN.
    - exact GFR.
    - destruct TAB as (TL & TC). split; [rewrite length_map; exact TL|].
      rewrite map_map. replace (map (fun x => entry_bytes (short_entry x)) es) with (map entry_bytes es)
        by (apply map_ext; intros x; symmetry; apply short_entry_bytes).
      apply RW1; [exact TC|apply r_blk40; cbn [cells_size csize]; clear - GB; unfold SRC_TABLE, SRC_ENTRY in *; lia].
    - apply Forall_map. eapply Forall_impl; [|exact HES]. intros x Hx. exact (p4_ent_kb B L0 A0 mem0 r_m1 x KB8 Hx).
    - rewrite map_map. exact NDF.
    - rewrite map_map. replace (map (fun x => entry_blocks (short_entry x)) es) with (map entry_blocks es)
        by (apply map_ext; intros x; symmetry; apply short_entry_blocks).
      unfold target_addrs in NDT. apply NoDup_ListNoDup in NDT. apply NoDup_ListNoDup.
      apply List.NoDup_cons_iff in NDT as [N1 NDT]. apply List.NoDup_cons_iff in NDT as [N2 NDT].
      constructor; [intros X; apply N1; destruct X as [X|X]; [left; exact X|right; apply in_or_app; left; exact X]|].
      constructor; [intros X; apply N2; apply in_or_app; left; exact X|]. exact (NoDup_app_remove_r _ _ NDT).
    - exact HCL.
    - exact HBR.
    - exact HDD.
    - exact HEI.
    - destruct (hg_cut _ _ _ [C4 (Z_to_bv 64 (-1))] [C4 (Z_to_bv 64 cl)] G1) as (_ & GC).
      apply RW1; [|apply r_gc; vm_compute; reflexivity].
      replace G_CLIENT with (relay_finish_b_c.G_LISTEN + Z.of_nat (cells_size [C4 (Z_to_bv 64 (-1))]))
        by (p4_cst; reflexivity). exact GC.
    - apply RW1; [exact G4|apply r_gc; vm_compute; reflexivity].
    - apply RW1; [exact G6|apply r_gc; vm_compute; reflexivity].
    - apply RW1; [exact G7|apply r_gc; vm_compute; reflexivity].
    - apply RW1; [exact G11|apply r_gc; vm_compute; reflexivity].
    - destruct ER as (ev & ERc). exists ev. apply RW1; [exact ERc|rewrite EA; apply r_gc; vm_compute; reflexivity].
    - destruct OD as [X|(CP & NO & IN & FR & BY & LO & LJ)]; [left; exact X|right].
      split; [exact CP|]. split; [exact NO|]. split; [exact IN|]. split; [exact FR|].
      split; [|split; assumption]. apply BY1; [exact BY|]. apply r_blk40. destruct FR as (_ & F1 & _).
      cbn [app] in LJ |- *. rewrite HNO in LJ. clear - F1 LJ. lia.
    - exact ROK.
    - intros e0 He0 Hf Heof. rewrite FDS in Hf |- *. rewrite (r_fd_uniq e0 He0 Hf) in Heof |- *.
      split; [exact (p4_src_kb B (API rc) L0 A0 mem0 r_m1 md0 (G_S + SRC_SIZE * Z.of_nat i) h HMR KB8 r_ha96 SRC)|].
      split.
      { destruct (p4_others rc B L0 A0 mem0 t es hj e h i q PA NDS NDF ZS Hqe Hqh) as (OL1 & OL2 & OT).
        split; [exact OL1|]. split; [exact OL2|]. intros k Hk4 Nk. destruct (OT k Hk4 Nk) as (C & X & Y).
        split; [apply RW1; [exact C|apply r_gb40; cbn [cells_size csize]; clear - Hk4; p4_cst; lia]|
          split; [exact X|exact Y]]. }
      split; [exact Hi|]. split; [exact FDE|]. destruct (SKU Heof) as [SK1 SK2].
      split; [exact SK1|]. split; [exact SK2|].
      split.
      { rewrite map_map. replace (map (fun x => entry_blocks (short_entry x)) es) with (map entry_blocks es)
          by (apply map_ext; intros x; symmetry; apply short_entry_blocks). exact r_nd_h. }
      split; [exact PLB|]. split; [exact (proj2 (ecap_ok_lt _ ECAP))|].
      unfold re_nheld. cbn [short_entry re_keys]. rewrite length_map.
      clear - PCK K26 KC NN1 NN2 NN3 NN4 EUL. destruct (re_skip e =? 0); lia.
    - cbv zeta. rewrite HNO, FDS. exact ROOM. }
  intros c' (L1 & A1 & R2 & mem2 & md1 & OUT' & CAP' & junk' & LB & e' & h' & tail' & -> & RP & INI &
    (qs1 & LQ1 & RF & QLs) & RO & LK & WK & GS & GIN' & CL & ER' & _ & POST).
  rewrite FDS in RP. rewrite HNO, FDS in LQ1, RF.
  assert (H1 : (q < length (map short_entry es))%nat) by (rewrite length_map; exact Hq1).
  assert (H2 : re_fd (nth q (map short_entry es) no_entry) = bv_signed (getr R1 10)) by (rewrite NQ', FDS; reflexivity).
  pose proof (POST q H1 H2) as PQ. cbv zeta in PQ. rewrite NQ' in PQ.
  assert (QL : (send_live cl br dd (r_TOT e') = true ->
      live_at L1 A1 (resolveF qs1 (remove_entry_out (send_live cl br dd 1) (bv_unsigned mx) 0 (bv_unsigned cap)
        (short_entry e) h 0 (drain_start (known_at L0 A0) (known_at L0 A0 (bv_unsigned out)) (short_entry e) h)))
        OUT' CAP') /\
    (re_eof e = 0 -> src_links L1 A1 qs1 (known_at L0 A0) (after_drain_adr (send_live cl br dd 1) (bv_unsigned mx) 0
       (bv_unsigned cap) (short_entry e) h 0 (drain_start (known_at L0 A0) (known_at L0 A0 (bv_unsigned out))
         (short_entry e) h)) h')).
  { pose proof (QLs q H1 H2) as X. cbv zeta in X. rewrite NQ', HNO in X. exact X. }
  destruct PQ as (NS & TB & FD' & EO' & P0 & P1 & LBx & BR & EI & BKa & BKb & ND & BKc & LV0 & LV1).
  assert (EOF0' : re_eof e = 0 -> src_at B L1 A1 mem2 (G_S + SRC_SIZE * Z.of_nat i) h' /\ hs_eintr h' = 0 /\
    hl_recs (hs_pending h') = [] /\ hs_off h' = 0 /\
    map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (p4_lines e h) /\
    hs_held h' = hs_held h /\ NoDup (keys_texts (re_keys e')) /\
    same_set (keys_texts (re_keys e')) (upds (keys_texts (re_keys (short_entry e))) (p4_lines e h))).
  { intros E0. destruct (P0 E0) as (X1 & _ & X2 & X3 & X4 & _ & _ & _ & _ & X5 & _ & X6 & X7 & X8 & _).
    exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 X8))))))). }
  assert (LV1' : send_live cl br dd (r_TOT e') = true ->
    bv_unsigned nout + r_TOT e' <= CAP' /\ CAP' <= Z.max (bv_unsigned cap) (2 * (bv_unsigned nout + r_TOT e')) /\
    In (OUT', CAP') (blocks L1 A1) /\ fresh_block B OUT' CAP' /\
    bytes_at (ms_segs B) mem2 OUT' ([] ++ LB ++ keys_out (re_keys e') ++ junk') /\
    Z.of_nat (length junk') = CAP' - bv_unsigned nout - r_TOT e' /\
    rw_cells (ms_segs B) mem2 G_OUTV
      [C8 mx; C8 (Z_to_bv 64 (bv_unsigned nout + r_TOT e')); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')]).
  { intros LVt. destruct (LV1 LVt) as (Y1 & YC & Y3 & Y4 & Y5 & Y6 & Y7).
    assert (Y2 : CAP' <= Z.max (bv_unsigned cap) (2 * (bv_unsigned nout + r_TOT e'))).
    { rewrite YC. unfold r_TOT, p4_lines.
      refine (remove_entry_cap_le (send_live cl br dd 1) (bv_unsigned mx) (bv_unsigned nout)
        (bv_unsigned cap) (short_entry e) h (re_keys e') _ _).
      - intros E0. split.
        + exact (rma_fin_no (send_live cl br dd 1) (bv_unsigned mx) (bv_unsigned nout)
            (bv_unsigned cap) (short_entry e) h (r_J1 E0) (r_pok _ _ _) r_capc).
        + destruct (P0 E0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XH & _). exact XH.
      - intros NE. destruct EO01 as [X|X]; [exfalso; exact (NE X)|]. rewrite (P1 X). reflexivity. }
    exact (conj Y1 (conj Y2 (conj Y3 (conj Y4 (conj Y5 (conj Y6 Y7)))))). }
  assert (CAPX' : (send_live cl br dd (r_TOT e') = true -> CAP' = r_cap1) /\
    (send_live cl br dd (r_TOT e') = false -> r_cap1 = bv_unsigned cap)).
  { split.
    - intros LVt. destruct (LV1 LVt) as (_ & YC & _). rewrite YC. unfold r_cap1. rewrite HNO. reflexivity.
    - intros LVf. destruct (Z.eq_dec (r_TOT e') 0) as [T0|T0].
      + assert (KT : keys_total (re_keys e') = 0 /\ p4_lines e h = []).
        { unfold r_TOT in T0. pose proof (keys_total_nonneg (re_keys e')) as KN.
          pose proof (Zle_0_nat (length (with_nul (p4_lines e h)))) as WN.
          split; [clear - T0 KN WN; lia|]. destruct (p4_lines e h) as [|l ls]; [reflexivity|].
          rewrite with_nul_cons_len in T0, WN. pose proof (Zle_0_nat (length l)) as LN.
          pose proof (Zle_0_nat (length (with_nul ls))) as LSn. exfalso. clear - T0 KN LN LSn. lia. }
        destruct KT as (KT & LT). apply p4_kt0 in KT.
        unfold r_cap1, remove_entry_cap, gestures_end_cap. cbv zeta.
        destruct EO01 as [E0|E1].
        * rewrite (after_drain_fin _ _ _ _ (short_entry e) h E0).
          destruct (P0 E0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XH & _).
          rewrite HNO in XH. rewrite <- XH, KT. cbn [keys_texts map keys_end_run snd].
          assert (LT' : lines (hs_state h) (bzs (pending_stream h)) = []).
          { unfold p4_lines in LT. rewrite (proj2 (Z.eqb_eq _ _) E0) in LT. exact LT. }
          rewrite (proj2 (rma_fin_live (send_live cl br dd 1) false (bv_unsigned mx) 0
            (bv_unsigned cap) (short_entry e) h 0%nat dadr0 (r_J1 E0) (proj1 (r_pok 0 (bv_unsigned cap) (short_entry e)))
            LT')).
          apply rma_fin_cap.
        * assert (NE : re_eof (short_entry e) <> 0) by (cbn; rewrite E1; discriminate).
          rewrite (after_drain_init _ _ _ _ (short_entry e) h NE).
          unfold drain_init. cbn [ds_H ds_ocap ds_no]. rewrite <- (P1 E1), KT. reflexivity.
      + unfold r_cap1. rewrite <- (rma_live_nz cl br dd (r_TOT e') T0), LVf. apply remove_entry_cap_dead. }
  pose proof (RIK L1 A1 qs1 LQ1 RF) as RI1.
  assert (ECA1' : re_eof e = 0 -> hl_cap (hs_expected h') =
      ds_ecap (drain_fin (send_live cl br dd 1) (bv_unsigned mx) 0 (bv_unsigned cap) (short_entry e) h)).
  { intros E0. destruct (P0 E0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XE).
    rewrite HNO in XE. exact XE. }
  assert (PPK1' : re_eof e = 0 ->
      hl_v (hs_pending h') = hl_v (hs_pending h) /\ hl_cap (hs_pending h') = hl_cap (hs_pending h) /\
      hs_partial h' = hs_partial h).
  { intros E0. destruct (P0 E0) as (_ & _ & _ & _ & _ & Y1 & Y2 & Y3 & _). exact (conj Y1 (conj Y2 Y3)). }
  assert (OD0 : (bv_unsigned cap = 0 /\ bv_unsigned out = 0 /\ bv_unsigned nout = 0 /\ @nil byte = []) \/
    (0 < bv_unsigned cap /\ bv_unsigned nout <= bv_unsigned cap /\ In (bv_unsigned out, bv_unsigned cap) (blocks L0 A0) /\
     fresh_block B (bv_unsigned out) (bv_unsigned cap) /\ bytes_at (ms_segs B) r_m1 (bv_unsigned out) ([] ++ junk0) /\
     Z.of_nat (length (@nil byte)) = bv_unsigned nout /\
     Z.of_nat (length junk0) = bv_unsigned cap - bv_unsigned nout)).
  { destruct OD as [X|(CP & NO & IN & FR & BY & LO & LJ)]; [left; exact X|right].
    split; [exact CP|]. split; [exact NO|]. split; [exact IN|]. split; [exact FR|].
    split; [|split; assumption]. apply BY1; [exact BY|]. destruct FR as (_ & F1 & _). cbn [app] in LJ |- *.
    rewrite HNO in LJ. p4_num. lia. }
  rewrite RA1.
  eapply (r_rr_done R1 R2 L1 A1 mem2 md1 OUT' CAP' junk0 junk' LB e' h' tail' qs1); eassumption.
Qed.
End M1.

Lemma r_all : SR (ms_segs B) (mkCfg (@YK11.mkst fx0 regs0 (Z_to_bv 64 0x142d0) mem0 (seg_rom (ms_segs B))) md0)
  (LI (rc := rc) B (API rc) E RI (t + 1) K).
Proof.
  eapply SR_bind; [exact r_head|]. intros c (R1 & m1 & -> & HM & SV1 & RA1 & FD1 & EO1).
  exact (r_rr_call m1 HM R1 SV1 RA1 FD1 EO1).
Qed.

End P4Run.

Lemma MI_op4 : forall F B API LS SH SK ra empty rc fx j E CS RI t K s c,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> check_bounded_contract ->
  (forall fx', @relay_remove_contract fx' rc B (API rc) F) -> check_no_loss_read_contract ->
  (forall fx', @check_no_loss_contract fx' rc B (API rc) F) ->
  (forall fx', @check_shape_ends_contract fx' rc B (API rc) F) -> check_shape_done_contract ->
  (forall fx', @source_reset_contract fx' rc B (API rc) F) ->
  p4_res F RI -> walk_at (ss_pl E) (t + 1) K ->
  MI (rc := rc) B (API rc) E RI t K 0x142d0 (fun _ hj no regs => no = 0 /\ disp_src 4 s hj /\ disp_regs E t K s regs) c ->
  SR (ms_segs B) c (LI (rc := rc) B (API rc) E RI (t + 1) K).
Proof.
  intros F B API LS SH SK ra empty rc fx j E CS RI t K s c HF CBc RRc CNRc CNLc CSEc CSDc SRSc P4r HW HM.
  destruct HM as (fx0 & L0 & A0 & regs0 & mem0 & md0 & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
    -> & FZ & Ht & Hk & Hn & (HNO & HDS & HDR) & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd &
    HOUT & HREL & Hes & Hcost & HRI).
  replace (t + (if (0x142d0 =? TAIL_CHECK) || (0x142d0 =? TAIL_STEP) then 1 else 0)) with t in HREL
    by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
  replace (t + (if (0x142d0 =? TAIL_CHECK) || (0x142d0 =? TAIL_STEP) then 2 else 1)) with (t + 1) in Hnfd
    by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
  destruct HDS as [(_ & i & Hi4 & HO & Hs)|([X|X] & _)]; [|discriminate X|discriminate X].
  pose proof HREL as (_ & _ & _ & _ & _ & _ & PA & _).
  destruct (p4_pick _ es hj i PA HO) as (q & e & h & Hqe & Hqh & _).
  eapply (r_all (fx := fx)); eassumption.
Qed.

Theorem pass4_holds : forall F, check_bounded_contract -> check_no_loss_read_contract -> check_shape_done_contract ->
  (forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
     @relay_remove_contract fx rc B (API rc) F /\ @check_no_loss_contract fx rc B (API rc) F /\
     @check_shape_ends_contract fx rc B (API rc) F /\ @source_reset_contract fx rc B (API rc) F) ->
  forall RI, RI_mono RI -> p4_res F RI ->
  pass_ok RI 4.
Proof.
  intros F CB CNR CSD CON RI RIM P4r B API LS SH SK ra empty rc fx j E CS HF t k c HL Ht Hk Hop.
  cbv beta in Hop.
  eapply SR_bind; [exact (LI_dispatch B API LS SH SK ra empty rc fx j E CS RI t k c HF RIM HL Ht Hk)|].
  intros c' [(s & HM)|(k'' & HL')]; [|apply SR_ret; exists k''; exact HL'].
  rewrite Hop in HM. change (jt_target 4) with 0x142d0 in HM.
  pose proof HF as (FF & _).
  eapply SR_mono; [eapply (MI_op4 F B API LS SH SK ra empty rc fx j E CS RI t (disp_k E 4 k) s c' HF CB
    (fun fx' => proj1 (CON B API LS SH SK ra empty rc fx' FF)) CNR
    (fun fx' => proj1 (proj2 (CON B API LS SH SK ra empty rc fx' FF)))
    (fun fx' => proj1 (proj2 (proj2 (CON B API LS SH SK ra empty rc fx' FF)))) CSD
    (fun fx' => proj2 (proj2 (proj2 (CON B API LS SH SK ra empty rc fx' FF))))
    P4r (walk_pick E t k 4 (LI_walk _ _ _ _ _ _ _ _ HL) (frame_len B API LS SH SK ra empty rc fx j E CS HF) Hk Hop
      (or_intror (or_intror (or_introl eq_refl)))) HM)|].
  intros c2 H2. exists (disp_k E 4 k). exact H2.
Qed.
