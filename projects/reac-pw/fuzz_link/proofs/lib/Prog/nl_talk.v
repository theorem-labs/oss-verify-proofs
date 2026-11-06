(* nl_talk (reac_link_alias.c:37-93), PLAIN build: the walk of its contract (lib/Prog/nl_talk_c.v) on
   the plain image, 162 instructions at 0x16008.

   The function opens the fake socket, sends the request, and reads chunks until a chunk's walk
   answers; its inner loops are lib/Prog/nt_scan.v (msg_loop, attr_loop, info_loop), the facts about
   g_nl's fields and link_spec's exchange are lib/Prog/nt_lem.v. This file walks the rest: the
   prologue (a 16512-byte frame with three stack probes), fuzz_socket and fuzz_send and their failure
   arms, the receive loop, the RTM_NEWLINK entry, fuzz_close and the epilogue, and shows the result
   is link_spec's talk_core of the fake kernel the function found. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_str mk_marks mk_leaf mk_call
  nt_lem nt_scan copy_attr_c fuzz_socket_c fuzz_send_c fuzz_recv_c fuzz_close_c __errno_location_c nl_talk_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
Local Open Scope Z_scope.

Definition nt_pre := ltac:(let t := eval cbv delta [nl_talk_contract] in nl_talk_contract in
                            lazymatch t with leaf _ _ ?P _ _ => exact P end).
Definition nt_wr := ltac:(let t := eval cbv delta [nl_talk_contract] in nl_talk_contract in
                           lazymatch t with leaf _ _ _ ?P _ => exact P end).
Definition nt_post := ltac:(let t := eval cbv delta [nl_talk_contract] in nl_talk_contract in
                             lazymatch t with leaf _ _ _ _ ?P => exact P end).
Lemma nl_talk_contract_eq : nl_talk_contract = leaf NL_TALK 16592 nt_pre nt_wr nt_post.
Proof. reflexivity. Qed.

(* the Posts of the fake kernel's four calls, read off their contracts *)
Definition nt_cl_post := ltac:(let t := eval cbv delta [fuzz_close_contract] in fuzz_close_contract in
                                lazymatch t with leaf _ _ _ _ ?P => exact P end).
Lemma nt_cl_post_ext : post_ext nt_cl_post.
Proof.
  intros r1 r2 m q1 q2 m' E1 E2 H. unfold nt_cl_post, arg in *. intros bs NK.
  destruct (H bs NK) as (bs' & H1). exists bs'. rewrite <- E1, <- E2. exact H1.
Qed.
Definition nt_re_post := ltac:(let t := eval cbv delta [fuzz_recv_contract] in fuzz_recv_contract in
                                lazymatch t with leaf _ _ _ _ ?P => exact P end).
Lemma nt_re_post_ext : post_ext nt_re_post.
Proof.
  intros r1 r2 m q1 q2 m' E1 E2 H. unfold nt_re_post, arg, errno_at in *. intros bs NK.
  destruct (H bs NK) as (bs' & H1). exists bs'. repeat rewrite <- E1. repeat rewrite <- E2. exact H1.
Qed.
Definition nt_so_post := ltac:(let t := eval cbv delta [fuzz_socket_contract] in fuzz_socket_contract in
                                lazymatch t with leaf _ _ _ _ ?P => exact P end).
Lemma nt_so_post_ext : post_ext nt_so_post.
Proof.
  intros r1 r2 m q1 q2 m' E1 E2 H. unfold nt_so_post, arg, errno_at in *. intros bs NK.
  destruct (H bs NK) as (bs' & H1). exists bs'. repeat rewrite <- E1. repeat rewrite <- E2. exact H1.
Qed.
Definition nt_se_post := ltac:(let t := eval cbv delta [fuzz_send_contract] in fuzz_send_contract in
                                lazymatch t with leaf _ _ _ _ ?P => exact P end).
Lemma nt_se_post_ext : post_ext nt_se_post.
Proof.
  intros r1 r2 m q1 q2 m' E1 E2 H. unfold nt_se_post, arg, errno_at in *. intros bs req NK RQ RL.
  repeat rewrite <- E1 in RQ, RL. destruct (H bs req NK RQ RL) as (bs' & H1). exists bs'.
  repeat rewrite <- E1. repeat rewrite <- E2. exact H1.
Qed.

Lemma getr10_mkR : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 : word,
  getr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 10 = a0.
Proof. reflexivity. Qed.
Lemma getr12_mkR : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 : word,
  getr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) 12 = a2.
Proof. reflexivity. Qed.

Lemma rw_cells_u8arr : forall m A cs, rw_cells rsegs m A cs ->
  exists bs, u8arr rsegs m A bs /\ length bs = cells_size cs.
Proof.
  intros m A cs H. destruct (rw_cells_forget rsegs m A cs H) as [junk RC]. exists junk.
  split; [exact (u8arr_of_rw_cells rsegs m A _ junk RC)|]. destruct RC as [[HJ _] _]. cbn in HJ. tauto.
Qed.

Lemma u8arr_join : forall m a xs ys, u8arr rsegs m a xs -> u8arr rsegs m (a + Z.of_nat (length xs)) ys ->
  u8arr rsegs m a (xs ++ ys).
Proof.
  intros m a xs ys [B1 W1] [B2 W2]. split.
  - apply bytes_at_app. split; assumption.
  - rewrite length_app. destruct W1 as (Ha & Hn & H1). destruct W2 as (Ha2 & Hn2 & H2).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (length xs))) as [L|L].
    + apply H1. lia.
    + replace (a + i) with (a + Z.of_nat (length xs) + (i - Z.of_nat (length xs))) by lia. apply H2. lia.
Qed.

Lemma stk_u8arr : forall m lo hi, stk rsegs m lo hi -> lo <= hi ->
  exists bs, u8arr rsegs m lo bs /\ Z.of_nat (length bs) = hi - lo.
Proof.
  intros m lo hi S H. destruct (stk_bytes rsegs m lo hi S H) as (bs & L & B). exists bs.
  split; [|lia]. split; [exact B|]. destruct S as (H1 & H2 & HS).
  split; [lia|]. split; [lia|]. intros i Hi. apply (HS (lo + i)). lia.
Qed.

Lemma stk_cat : forall m lo a cs b hi, stk rsegs m lo a -> rw_cells rsegs m a cs -> stk rsegs m b hi ->
  a + Z.of_nat (cells_size cs) = b -> lo <= a -> b <= hi -> stk rsegs m lo hi.
Proof.
  intros m lo a cs b hi S1 C S2 E H1 H2. pose proof (stk_release rsegs m lo a cs S1 C H1) as S. rewrite E in S.
  exact (stk_merge rsegs m lo b hi S S2 ltac:(pose proof (rw_cells_bound rsegs m a cs C); lia)).
Qed.

Lemma uwz : forall e, 0 <= e < 2 ^ 64 -> bv_unsigned (wz e) = e.
Proof. intros e H. unfold wz. apply unsigned_lit. lia. Qed.

Section Body.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (lo : Z) (sp4w : word).
Let R0 := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
Let W0 := (bv_unsigned sp - 16592, bv_unsigned sp) :: nt_wr R0 m0.
Let SVc := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Let Q := fun ms' => exists (regs' : bvmap 5 word) (m' : word -> option byte),
  ms' = MS regs' F (ret_pc ra) fc None m' (seg_rom rsegs) /\
  regs_preserved R0 regs' /\ munch W0 m0 m' /\
  wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ nt_post R0 m0 regs' m'.

Hypothesis HSP4 : bv_unsigned sp4w = bv_unsigned sp - 16512.
Hypothesis LO0 : 0 <= lo /\ lo + 16592 <= bv_unsigned sp.
Hypothesis SP0 : bv_unsigned sp < 2 ^ 63.
(* nl_talk's Pre at the entry registers, one conjunct at a time *)
Variables (kbs0 req : list byte).
Hypothesis NK0 : nlk_at m0 kbs0.
Hypothesis FG0 : apart_gnl (bv_unsigned sp - 16592) 16592.
Hypothesis WF0 : nlk_wf kbs0.
Hypothesis OP0 : nk_open kbs0 = 0.
Hypothesis EW0 : wr_at rsegs m0 (bv_unsigned tp + ERRNO_TP_OFF) 4.
Hypothesis EF0 : bv_unsigned tp + ERRNO_TP_OFF + 4 <= bv_unsigned sp - 16592 \/ bv_unsigned sp <= bv_unsigned tp + ERRNO_TP_OFF.
Hypothesis EG0 : apart_gnl (bv_unsigned tp + ERRNO_TP_OFF) 4.
Hypothesis RQ0 : bytes_at rsegs m0 (bv_unsigned a0) req.
Hypothesis RL0 : Z.of_nat (length req) = bv_unsigned a1.
Hypothesis RL1 : 0 <= bv_unsigned a1 <= NL_SENT_LEN.
Hypothesis BK0 : buf_arg m0 (bv_unsigned a2) (bv_unsigned a3).
Hypothesis BA0 : buf_arg m0 (bv_unsigned a4) (bv_unsigned a5).
Hypothesis ERQ : apart (bv_unsigned tp + ERRNO_TP_OFF) 4 (bv_unsigned a0) (bv_unsigned a1).
Hypothesis EK0 : bv_unsigned a2 <> 0 -> apart (bv_unsigned tp + ERRNO_TP_OFF) 4 (bv_unsigned a2) (bv_unsigned a3).
Hypothesis EA0 : bv_unsigned a4 <> 0 -> apart (bv_unsigned tp + ERRNO_TP_OFF) 4 (bv_unsigned a4) (bv_unsigned a5).
Hypothesis KA0 : bv_unsigned a2 <> 0 -> 1 <= bv_unsigned a3 -> bv_unsigned a4 <> 0 -> 1 <= bv_unsigned a5 ->
  apart (bv_unsigned a2) (bv_unsigned a3) (bv_unsigned a4) (bv_unsigned a5).
Hypothesis OC0 : nk_opened kbs0 + 1 < 2 ^ 31.
Hypothesis CC0 : nk_closed kbs0 + 1 < 2 ^ 31.
Hypothesis RG0 : apart_gnl (bv_unsigned a0) (bv_unsigned a1).
Hypothesis RF0 : bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - 16592 \/ bv_unsigned sp <= bv_unsigned a0.
Hypothesis KF0 : bv_unsigned a2 <> 0 ->
  (bv_unsigned a2 + bv_unsigned a3 <= bv_unsigned sp - 16592 \/ bv_unsigned sp <= bv_unsigned a2)
  /\ apart_gnl (bv_unsigned a2) (bv_unsigned a3).
Hypothesis AF0 : bv_unsigned a4 <> 0 ->
  (bv_unsigned a4 + bv_unsigned a5 <= bv_unsigned sp - 16592 \/ bv_unsigned sp <= bv_unsigned a4)
  /\ apart_gnl (bv_unsigned a4) (bv_unsigned a5).
Hypothesis MI0 : mem_inv rsegs m0.
Hypothesis ST0 : stk rsegs m0 lo (bv_unsigned sp).

Lemma kbs_req_unique : forall kbs req', nlk_at m0 kbs -> bytes_at rsegs m0 (bv_unsigned a0) req' ->
  Z.of_nat (length req') = bv_unsigned a1 -> kbs = kbs0 /\ req' = req.
Proof.
  intros kbs req' [[B _] L] RQ RL. destruct NK0 as [[B0 _] L0]. split.
  - apply (bytes_at_unique m0 A_G_NL); [exact B | exact B0 | lia].
  - apply (bytes_at_unique m0 (bv_unsigned a0)); [exact RQ | exact RQ0 | lia].
Qed.

Lemma nt_post_ext : forall q1 q2 m', getr_same q1 q2 -> nt_post R0 m0 q1 m' -> nt_post R0 m0 q2 m'.
Proof.
  intros q1 q2 m' E H. unfold nt_post in *. intros kbs req' NK RQ RL.
  specialize (H kbs req' NK RQ RL). cbv zeta in H |- *. rewrite <- E. exact H.
Qed.

Lemma QX : q_ext Q.
Proof. unfold Q. apply leaf_q_ext. exact nt_post_ext. Qed.

(* 0x16244 .. 0x1628c: the answer into a0, the 13 saved words back, the frame released, ret *)
Lemma nt_epi : forall m rc (ra1 t01 t11 t21 s01 s1' a01 a11 a21 a31 a41 a51 a61 a71 s2' s3' s4' s5' s7' s8' s9'
    s10' s11' t31 t41 t51 t61 : word) cs24 bj,
  mem_inv rsegs m -> wmono rsegs m0 m -> munch W0 m0 m -> stk rsegs m lo (bv_unsigned sp4w) ->
  rw_cells rsegs m (bv_unsigned sp4w) cs24 -> cells_size cs24 = 24%nat ->
  u8arr rsegs m (bv_unsigned sp4w + 24) bj -> Z.of_nat (length bj) = 16384 ->
  rw_cells rsegs m (bv_unsigned sp4w + 16408) SVc ->
  (forall regs', getr regs' 10 = wz rc -> nt_post R0 m0 regs' m) ->
  evt rsegs Q (MS (mkR ra1 sp4w gp tp t01 t11 t21 s01 s1' a01 a11 a21 a31 a41 a51 a61 a71
                       s2' s3' s4' s5' (wz rc) s7' s8' s9' s10' s11' t31 t41 t51 t61)
                  F (Z_to_bv 64 0x16244) fc None m (seg_rom rsegs)).
Proof.
  intros m rc ra1 t01 t11 t21 s01 s1' a01 a11 a21 a31 a41 a51 a61 a71 s2' s3' s4' s5' s7' s8' s9' s10' s11'
    t31 t41 t51 t61 cs24 bj MI WM MU ST FA L24 FB LB FS PST.
  pose proof (bv_unsigned_in_range 64 sp4w) as R4. unfold bv_modulus in R4.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS.
  zstep. zstep. zstep. zstep.
  remember (Z_to_bv 64 (bv_unsigned sp4w + 14480)) as spE eqn:HSE.
  assert (USE : bv_unsigned spE = bv_unsigned sp4w + 14480) by (subst spE; apply unsigned_lit; lia).
  replace (bv_unsigned sp4w + 16408) with (bv_unsigned spE + 1928) in FS by lia. unfold SVc in FS.
  do 13 zstep.
  zstep.
  replace (Z_to_bv 64 (bv_unsigned spE + 2032)) with sp
    by (apply bv_eq; rewrite unsigned_lit by lia; lia).
  zstep.
  (* the frame, released in its three pieces *)
  pose proof (stk_release rsegs m lo _ cs24 ST FA ltac:(lia)) as ST1. rewrite L24 in ST1.
  pose proof (stk_release rsegs m lo _ _ ST1 (rw_cells_of_u8arr rsegs m _ bj FB) ltac:(lia)) as ST2.
  cbn [cells_size csize] in ST2. rewrite Nat.add_0_r, LB in ST2.
  replace (bv_unsigned sp4w + Z.of_nat 24 + 16384) with (bv_unsigned spE + 1928) in ST2 by lia.
  pose proof (stk_release rsegs m lo _ _ ST2 FS ltac:(lia)) as ST3.
  cbn [cells_size csize Nat.add] in ST3.
  lazymatch type of ST3 with stk _ _ _ ?h => replace h with (bv_unsigned sp) in ST3 by lia end.
  apply evt_done. unfold Q. do 2 eexists. split; [reflexivity|].
  split; [eapply regs_preserved_mkR|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST3|].
  apply PST. reflexivity.
Qed.

(* what the footprint the contract allows contains *)
Lemma W0_out : forall x, outside W0 x ->
  ~ (bv_unsigned sp - 16592 <= x < bv_unsigned sp) /\ ~ (A_G_NL <= x < A_G_NL + NK_N_SENT + 4) /\
  ~ (bv_unsigned tp + ERRNO_TP_OFF <= x < bv_unsigned tp + ERRNO_TP_OFF + 4) /\
  (bv_unsigned a2 <> 0 -> ~ (bv_unsigned a2 <= x < bv_unsigned a2 + bv_unsigned a3)) /\
  (bv_unsigned a4 <> 0 -> ~ (bv_unsigned a4 <= x < bv_unsigned a4 + bv_unsigned a5)).
Proof.
  intros x H. unfold W0, nt_wr in H. cbn beta in H. unfold R0 in H.
  rewrite mkR_a2, mkR_a3, mkR_a4, mkR_a5, mkR_errno in H. cbn [outside] in H.
  destruct H as (H1 & H2 & H3 & H4 & H5 & _).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; intros Hn; [rewrite (proj2 (Z.eqb_neq _ 0) Hn) in H4 | rewrite (proj2 (Z.eqb_neq _ 0) Hn) in H5]; assumption.
Qed.

(* 0x1623c .. 0x16240: fuzz_close, then the epilogue; the exchange ended by the receive loop *)
Lemma nt_out : fuzz_close_contract -> forall m kbs v j (ra1 t01 t11 t21 s1' a01 a11 a21 a31 a41 a51 a61 a71
    s2' s3' s4' s5' s7' s8' s9' s10' s11' t31 t41 t51 t61 : word) cs24 bj,
  mem_inv rsegs m -> wmono rsegs m0 m -> munch W0 m0 m -> stk rsegs m lo (bv_unsigned sp4w) ->
  rw_cells rsegs m (bv_unsigned sp4w) cs24 -> cells_size cs24 = 24%nat ->
  u8arr rsegs m (bv_unsigned sp4w + 24) bj -> Z.of_nat (length bj) = 16384 ->
  rw_cells rsegs m (bv_unsigned sp4w + 16408) SVc ->
  nlk_at m kbs -> nlk_wf kbs ->
  nk_chunks kbs = nk_chunks kbs0 -> nk_end_errno kbs = nk_end_errno kbs0 -> nk_n_if kbs = nk_n_if kbs0 ->
  nk_socket_errno kbs = 0 -> nk_send_errno kbs = 0 -> nk_open kbs = 1 -> nk_opened kbs = nk_opened kbs0 + 1 ->
  nk_closed kbs = nk_closed kbs0 -> nk_misuse kbs = nk_misuse kbs0 ->
  nk_sent kbs = owe (nk_sent kbs0) req -> nk_n_sent kbs = Z.of_nat (length (nk_sent kbs)) ->
  nk_next kbs = Z.of_nat j ->
  nk_socket_errno kbs0 = 0 -> nk_send_errno kbs0 = 0 ->
  chunk_loop (S (length (nk_chunks kbs0))) (nk_chunks kbs0) (Z.to_nat (nk_next kbs0)) = (v, j) ->
  bufst m0 m (bv_unsigned a2) (bv_unsigned a3) (a_kind (nlv_attrs v)) ->
  bufst m0 m (bv_unsigned a4) (bv_unsigned a5) (a_alias (nlv_attrs v)) ->
  evt rsegs Q (MS (mkR ra1 sp4w gp tp t01 t11 t21 (wz NL_FD) s1' a01 a11 a21 a31 a41 a51 a61 a71
                       s2' s3' s4' s5' (wz (nlv_rc v (nk_end_errno kbs0))) s7' s8' s9' s10' s11' t31 t41 t51 t61)
                  F (Z_to_bv 64 0x1623c) fc None m (seg_rom rsegs)).
Proof.
  intros HCL m kbs v j ra1 t01 t11 t21 s1' a01 a11 a21 a31 a41 a51 a61 a71 s2' s3' s4' s5' s7' s8' s9' s10' s11'
    t31 t41 t51 t61 cs24 bj MI WM MU ST FA L24 FB LB FS NK WF EC EE EI ES ESE EOP EOD ECL EMI ESN ENS ENX S0 SE0 CL
    BKs BAs.
  pose proof (bv_unsigned_in_range 64 sp4w) as R4. unfold bv_modulus in R4.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS.
  zstep. zstep.
  eapply (leaf_call FUZZ_CLOSE 0 _ _ _ HCL nt_cl_post_ext Q QX).
  { exists kbs. split; [exact NK|]. split; [exact WF|]. rewrite ECL. lia. }
  { exact MI. }
  { exact ST. }
  { lia. }
  { lia. }
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MUc WMc MIc STc PO.
  cbv beta in MUc, PO. rewrite mkR_a0 in PO.
  destruct (PO kbs NK) as (kbs' & NK' & WF' & R10 & OP' & OPD' & CL' & MS').
  rewrite ret_pc_even by (lia || reflexivity).
  unfold apart_gnl in FG0. unfold NK_SIZE in FG0.
  set (Wc := [(bv_unsigned sp4w - 0, bv_unsigned sp4w); (A_G_NL + NK_OPEN, A_G_NL + NK_MISUSE + 4)]) in MUc.
  (* every field of g_nl outside [NK_OPEN, NK_MISUSE + 4) is kept *)
  assert (KEEP : forall o n, 0 <= o -> 0 <= n -> o + n <= NK_SIZE ->
                   (o + n <= NK_OPEN \/ NK_MISUSE + 4 <= o) -> disjoint_from Wc (A_G_NL + o) n).
  { intros o n H1 H2 H3 H4. unfold Wc, NK_SIZE, NK_OPEN, NK_MISUSE in *. cbn [disjoint_from].
    split; [lia | split; [lia | exact I]]. }
  assert (FK : forall off, 0 <= off -> off + 4 <= NK_OPEN \/ NK_MISUSE + 4 <= off -> off + 4 <= NK_SIZE ->
                 fld_u32 kbs' off = fld_u32 kbs off).
  { intros off H1 H2 H3. unfold fld_u32. apply (fld_keep Wc m m'); try assumption; try lia.
    apply KEEP; lia. }
  assert (EC' : nk_chunks kbs' = nk_chunks kbs0).
  { rewrite <- EC. apply nk_chunks_keep; [exact WF|].
    apply (nlk_slice_keep Wc m m'); try assumption; try (unfold NK_NEXT, NK_SIZE; lia).
    apply KEEP; unfold NK_NEXT, NK_SIZE, NK_OPEN; lia. }
  assert (EN' : nk_sent kbs' = nk_sent kbs).
  { apply nk_sent_keep; [exact WF|].
    apply (nlk_slice_keep Wc m m'); try assumption; try (unfold NK_SENT, NK_N_SENT, NK_SIZE; lia).
    apply KEEP; unfold NK_SENT, NK_N_SENT, NK_SIZE, NK_OPEN, NK_MISUSE; lia. }
  assert (EE' : nk_end_errno kbs' = nk_end_errno kbs0)
    by (rewrite <- EE; apply FK; unfold NK_END_ERRNO, NK_OPEN, NK_SIZE; lia).
  assert (EI' : nk_n_if kbs' = nk_n_if kbs0)
    by (rewrite <- EI; apply FK; unfold NK_N_IF, NK_MISUSE, NK_SIZE; lia).
  assert (ES' : nk_socket_errno kbs' = 0)
    by (rewrite <- ES; apply FK; unfold NK_SOCKET_ERRNO, NK_OPEN, NK_SIZE; lia).
  assert (ESE' : nk_send_errno kbs' = 0)
    by (rewrite <- ESE; apply FK; unfold NK_SEND_ERRNO, NK_OPEN, NK_SIZE; lia).
  assert (ENX' : nk_next kbs' = Z.of_nat j)
    by (rewrite <- ENX; apply FK; unfold NK_NEXT, NK_OPEN, NK_SIZE; lia).
  assert (ENS' : nk_n_sent kbs' = nk_n_sent kbs)
    by (apply FK; unfold NK_N_SENT, NK_MISUSE, NK_SIZE; lia).
  assert (SUB : forall x, outside W0 x -> outside Wc x).
  { intros x Hx. destruct (W0_out x Hx) as (H1 & H2 & _). unfold Wc, NK_OPEN, NK_MISUSE, NK_N_SENT in *.
    cbn [outside]. split; [lia | split; [lia | exact I]]. }
  apply (nt_epi m' (nlv_rc v (nk_end_errno kbs0))) with (cs24 := cs24) (bj := bj).
  - exact MIc.
  - exact (wmono_trans rsegs _ _ _ WM WMc).
  - exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MUc)).
  - exact STc.
  - apply (rw_cells_transport rsegs Wc m m'); [exact FA | exact MUc | exact WMc |].
    rewrite L24. unfold Wc. cbn [disjoint_from]. split; [lia | split; [unfold NK_OPEN, NK_MISUSE; lia | exact I]].
  - exact L24.
  - apply (u8arr_transport rsegs Wc m m'); [exact FB | exact MUc | exact WMc |].
    rewrite LB. unfold Wc. cbn [disjoint_from]. split; [lia | split; [unfold NK_OPEN, NK_MISUSE; lia | exact I]].
  - exact LB.
  - apply (rw_cells_transport rsegs Wc m m'); [exact FS | exact MUc | exact WMc |].
    unfold SVc. cbn [cells_size csize Nat.add]. unfold Wc. cbn [disjoint_from].
    split; [lia | split; [unfold NK_OPEN, NK_MISUSE; lia | exact I]].
  - (* the Post *)
    intros regs' R10x. unfold nt_post. intros kbsx reqx NKx RQx RLx.
    unfold R0 in RQx, RLx. rewrite mkR_a0 in RQx. rewrite mkR_a1 in RLx.
    destruct (kbs_req_unique kbsx reqx NKx RQx RLx) as [E1 E2]. subst kbsx reqx. cbv zeta.
    unfold R0. rewrite ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_a5.
    set (K0 := nk_kstate kbs0).
    assert (KS : k_sock K0 = 0) by exact S0.
    assert (KE : k_send K0 = 0) by exact SE0.
    assert (CLK : chunk_loop (S (length (k_chunks K0))) (k_chunks K0) (k_next K0) = (v, j)) by exact CL.
    pose proof (talk_loop K0 KS KE) as TL. cbv zeta in TL. rewrite CLK in TL. cbn [fst snd] in TL.
    destruct TL as (TRC & TAT & TAF & TOW).
    rewrite TRC, TAT, TAF, TOW.
    assert (KEK : k_end K0 = nk_end_errno kbs0) by reflexivity.
    split; [rewrite KEK; exact R10x|].
    split.
    { exists kbs'. split; [exact NK'|]. split; [exact WF'|].
      split; [exact EC'|]. split; [exact EE'|]. split; [exact EI'|]. split; [exact ES'|].
      split; [exact ESE'|]. split; [exact ENX'|].
      split; [rewrite EN'; exact ESN|]. split; [rewrite ENS', EN'; exact ENS|].
      split; [exact OP'|].
      split; [rewrite MS', EOP; unfold wz, NL_FD; rewrite unsigned_lit by lia;
              replace ((7 =? 7) && negb (1 =? 0)) with true by reflexivity; exact EMI|].
      split; [rewrite OPD', CL', EOD, ECL; lia|].
      split; [intros H; exfalso; exact (H S0)|].
      intros _. rewrite OPD'. exact EOD. }
    assert (DB : forall b n, b <> 0 -> (b + n <= bv_unsigned sp - 16592 \/ bv_unsigned sp <= b) ->
                   apart_gnl b n -> disjoint_from Wc b n).
    { intros b n Hb H1 H2. unfold apart_gnl, NK_SIZE in H2. unfold Wc. cbn [disjoint_from].
      split; [lia | split; [unfold NK_OPEN, NK_MISUSE; lia | exact I]]. }
    assert (BK' : bufst m0 m' (bv_unsigned a2) (bv_unsigned a3) (a_kind (nlv_attrs v))).
    { eapply bufst_keep; [exact BKs | exact MUc | exact WMc |]. intros Hb _. destruct (KF0 Hb) as [H1 H2]. exact (DB _ _ Hb H1 H2). }
    assert (BA' : bufst m0 m' (bv_unsigned a4) (bv_unsigned a5) (a_alias (nlv_attrs v))).
    { eapply bufst_keep; [exact BAs | exact MUc | exact WMc |]. intros Hb _. destruct (AF0 Hb) as [H1 H2]. exact (DB _ _ Hb H1 H2). }
    destruct BK' as [BKr BKt]. destruct BA' as [BAr BAt].
    split; [intros pay E; rewrite E in BKt; exact BKt|].
    split; [intros pay E; rewrite E in BAt; exact BAt|].
    split; [intros E; rewrite E in BKt; exact BKt|].
    split; [intros E; rewrite E in BAt; exact BAt|].
    split; [exact BKr | exact BAr].
Qed.

(* the context nt_scan's attribute walks run in, at this function's frame *)
Lemma sc_LO : 0 <= lo /\ lo + 80 <= bv_unsigned sp4w.
Proof. lia. Qed.
Lemma sc_SPB : bv_unsigned sp4w + 16512 < 2 ^ 63.
Proof. lia. Qed.
Lemma sc_KSEP : bv_unsigned a2 <> 0 -> 1 <= bv_unsigned a3 ->
  apart (bv_unsigned a2) (bv_unsigned a3) (bv_unsigned sp4w - 80) 16592 /\ apart_gnl (bv_unsigned a2) (bv_unsigned a3).
Proof. intros H _. destruct (KF0 H) as [H1 H2]. split; [unfold apart; lia | exact H2]. Qed.
Lemma sc_ASEP : bv_unsigned a4 <> 0 -> 1 <= bv_unsigned a5 ->
  apart (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned sp4w - 80) 16592 /\ apart_gnl (bv_unsigned a4) (bv_unsigned a5).
Proof. intros H _. destruct (AF0 H) as [H1 H2]. split; [unfold apart; lia | exact H2]. Qed.
Lemma sc_GSEP : apart_gnl (bv_unsigned sp4w - 80) 16592.
Proof. unfold apart_gnl in *. lia. Qed.
Lemma sc_WFR : forall x, outside W0 x -> outside [(bv_unsigned sp4w - 80, bv_unsigned sp4w)] x.
Proof. intros x H. destruct (W0_out x H) as (H1 & _). cbn [outside]. split; [lia | exact I]. Qed.
Lemma sc_WK : forall x, outside W0 x -> bv_unsigned a2 <> 0 ->
  outside [(bv_unsigned a2, bv_unsigned a2 + bv_unsigned a3)] x.
Proof. intros x H Hk. destruct (W0_out x H) as (_ & _ & _ & H4 & _). cbn [outside]. split; [exact (H4 Hk) | exact I]. Qed.
Lemma sc_WA : forall x, outside W0 x -> bv_unsigned a4 <> 0 ->
  outside [(bv_unsigned a4, bv_unsigned a4 + bv_unsigned a5)] x.
Proof. intros x H Hk. destruct (W0_out x H) as (_ & _ & _ & _ & H5). cbn [outside]. split; [exact (H5 Hk) | exact I]. Qed.

(* 0x16170 .. 0x16190: the first RTM_NEWLINK; its attributes walk from off + 32, after alias_n is
   spilled to sp + 16 *)
Lemma nt_link : copy_attr_contract -> fuzz_close_contract -> forall m kbs c rest f off ml j j0 j1
    (ra1 t01 t11 t21 a01 a31 a41 a51 a61 a71 t31 t41 t51 t61 : word),
  mem_inv rsegs m -> wmono rsegs m0 m -> munch W0 m0 m -> stk rsegs m lo (bv_unsigned sp4w) ->
  rw_cells rsegs m (bv_unsigned sp4w) [CB 16 j0; CB 8 j1] ->
  bytes_at rsegs m (bv_unsigned sp4w + 24) (c ++ rest) -> wr_at rsegs m (bv_unsigned sp4w + 24) 16384 ->
  Z.of_nat (length (c ++ rest)) = 16384 -> (length c <= 4096)%nat ->
  rw_cells rsegs m (bv_unsigned sp4w + 16408) SVc ->
  nlk_at m kbs -> nlk_wf kbs ->
  nk_chunks kbs = nk_chunks kbs0 -> nk_end_errno kbs = nk_end_errno kbs0 -> nk_n_if kbs = nk_n_if kbs0 ->
  nk_socket_errno kbs = 0 -> nk_send_errno kbs = 0 -> nk_open kbs = 1 -> nk_opened kbs = nk_opened kbs0 + 1 ->
  nk_closed kbs = nk_closed kbs0 -> nk_misuse kbs = nk_misuse kbs0 ->
  nk_sent kbs = owe (nk_sent kbs0) req -> nk_n_sent kbs = Z.of_nat (length (nk_sent kbs)) ->
  nk_next kbs = Z.of_nat j -> wr_at rsegs m (bv_unsigned tp + ERRNO_TP_OFF) 4 ->
  nk_socket_errno kbs0 = 0 -> nk_send_errno kbs0 = 0 ->
  chunk_loop (S (length (nk_chunks kbs0))) (nk_chunks kbs0) (Z.to_nat (nk_next kbs0))
    = (NlLink (attr_scan f c (off + 32) (ml - 32) no_attrs), j) ->
  (Z.to_nat (ml - 32) < f)%nat -> 0 <= off -> 16 <= ml -> off + ml <= Z.of_nat (length c) ->
  bufst m0 m (bv_unsigned a2) (bv_unsigned a3) None ->
  bufst m0 m (bv_unsigned a4) (bv_unsigned a5) None ->
  evt rsegs Q (MS (mkR ra1 sp4w gp tp t01 t11 t21 (wz NL_FD) a5 a01 (Z_to_bv 64 (bv_unsigned sp4w + 24 + off))
                       (Z_to_bv 64 ml) a31 a41 a51 a61 a71 a4 a3 a2 (Z_to_bv 64 16) (Z_to_bv 64 2)
                       (Z_to_bv 64 15) s8 s9 s10 s11 t31 t41 t51 t61)
                  F (Z_to_bv 64 0x16170) fc None m (seg_rom rsegs)).
Proof.
  intros HCA HCL m kbs c rest f off ml j j0 j1 ra1 t01 t11 t21 a01 a31 a41 a51 a61 a71 t31 t41 t51 t61
    MI WM MU ST FA BB BW LCR LC FS NK WF EC EE EI ES ESE EOP EOD ECL EMI ESN ENS ENX EW S0 SE0 CL HF H0 H16 HL
    BKs BAs.
  pose proof (bv_unsigned_in_range 64 sp4w) as R4. unfold bv_modulus in R4.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS.
  zstep. rewrite (bv_swrap_small 32 (ml + -32)) by (replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity; lia).
  zstep. zstep. if_cases K1; zify_cond K1; rewrite sgn_lit in K1 by lia.
  { (* fewer than 4 bytes of attributes: no attribute at all *)
    rewrite as_small in CL by lia.
    zstep. zstep.
    apply (nt_out HCL m kbs (NlLink no_attrs) j) with (cs24 := [CB 16 j0; CB 8 j1]) (bj := c ++ rest);
      try assumption; try reflexivity.
    all: split; [assumption | rewrite LCR; assumption]. }
  (* 0x1617c: sd s1, 0x10(sp): alias_n into the spill slot *)
  pose proof (munch_refl [(bv_unsigned sp4w + 16, bv_unsigned sp4w + 24)] m) as MUS.
  pose proof (wmono_refl rsegs m) as WMS.
  unfold W0, nt_wr in MU. cbv beta in MU. unfold R0 in MU.
  rewrite ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_a5, ?mkR_errno in MU.
  destruct NK as [NKA NKL]. pose proof FG0 as FG1. unfold apart_gnl, NK_SIZE in FG1, NKL.
  zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
  assert (BK2 : bufst m0 m2 (bv_unsigned a2) (bv_unsigned a3) None).
  { eapply bufst_keep; [exact BKs | exact MUS | exact WMS |]. intros Hb _. destruct (KF0 Hb) as [H1 _].
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (BA2 : bufst m0 m2 (bv_unsigned a4) (bv_unsigned a5) None).
  { eapply bufst_keep; [exact BAs | exact MUS | exact WMS |]. intros Hb _. destruct (AF0 Hb) as [H1 _].
    cbn [disjoint_from]. split; [lia | exact I]. }
  zstep. zstep. zstep. zstep. zstep.
  replace (bv_unsigned sp4w + 24 + off + 32) with (bv_unsigned sp4w + 24 + (off + 32)) by lia.
  replace (ml + -32) with (ml - 32) by lia.
  apply (attr_loop m0 W0 lo sp4w a2 a3 a4 a5 j0 SVc c rest kbs (bv_unsigned tp + ERRNO_TP_OFF) Q gp tp
           (wz NL_FD) F fc QX sc_LO sc_SPB LCR LC sc_KSEP sc_ASEP KA0 sc_GSEP sc_WFR sc_WK sc_WA HCA
           f (off + 32) (ml - 32) no_attrs m2); [lia | lia | lia | lia | |].
  { exact (conj MI (conj WM (conj MU (conj ST (conj FA (conj BB (conj BW (conj FS (conj eq_refl
             (conj (conj NKA NKL) (conj EW (conj BK2 BA2)))))))))))). }
  intros m' ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' AI'.
  destruct AI' as (MI' & WM' & MU' & ST' & FA' & BB' & BW' & FS' & SVS' & NK' & EW' & BK' & BA').
  apply (nt_out HCL m' kbs (NlLink (attr_scan f c (off + 32) (ml - 32) no_attrs)) j)
    with (cs24 := [CB 16 j0; C8 a5]) (bj := c ++ rest); try assumption; try reflexivity.
  all: split; [assumption | rewrite LCR; assumption].
Qed.

Lemma um1 : bv_unsigned (Z_to_bv 64 (-1)) = 2 ^ 64 - 1.
Proof. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma lw_u32 : forall v, 0 <= v < 2 ^ 31 -> sx32 (wz v) = wz v.
Proof.
  intros v H. unfold sx32, wz. rewrite unsigned_lit by lia. f_equal.
  apply bv_swrap_small. replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. lia.
Qed.

(* 0x16128 .. 0x16134: recv failed, so the exchange answers -errno (the end errno) *)
Lemma nt_rfail : fuzz_close_contract -> __errno_location_contract -> forall m kbs j cs24 bj
    (ra1 t01 t11 t21 s1' a01 a11 a21 a31 a41 a51 a61 a71 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11'
     t31 t41 t51 t61 : word),
  mem_inv rsegs m -> wmono rsegs m0 m -> munch W0 m0 m -> stk rsegs m lo (bv_unsigned sp4w) ->
  rw_cells rsegs m (bv_unsigned sp4w) cs24 -> cells_size cs24 = 24%nat ->
  u8arr rsegs m (bv_unsigned sp4w + 24) bj -> Z.of_nat (length bj) = 16384 ->
  rw_cells rsegs m (bv_unsigned sp4w + 16408) SVc ->
  nlk_at m kbs -> nlk_wf kbs ->
  nk_chunks kbs = nk_chunks kbs0 -> nk_end_errno kbs = nk_end_errno kbs0 -> nk_n_if kbs = nk_n_if kbs0 ->
  nk_socket_errno kbs = 0 -> nk_send_errno kbs = 0 -> nk_open kbs = 1 -> nk_opened kbs = nk_opened kbs0 + 1 ->
  nk_closed kbs = nk_closed kbs0 -> nk_misuse kbs = nk_misuse kbs0 ->
  nk_sent kbs = owe (nk_sent kbs0) req -> nk_n_sent kbs = Z.of_nat (length (nk_sent kbs)) ->
  nk_next kbs = Z.of_nat j ->
  u32_at m (bv_unsigned tp + ERRNO_TP_OFF) (nk_end_errno kbs0) ->
  nk_socket_errno kbs0 = 0 -> nk_send_errno kbs0 = 0 ->
  chunk_loop (S (length (nk_chunks kbs0))) (nk_chunks kbs0) (Z.to_nat (nk_next kbs0)) = (NlNone, j) ->
  bufst m0 m (bv_unsigned a2) (bv_unsigned a3) None ->
  bufst m0 m (bv_unsigned a4) (bv_unsigned a5) None ->
  evt rsegs Q (MS (mkR ra1 sp4w gp tp t01 t11 t21 (wz NL_FD) s1' a01 a11 a21 a31 a41 a51 a61 a71
                       s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t31 t41 t51 t61)
                  F (Z_to_bv 64 0x16128) fc None m (seg_rom rsegs)).
Proof.
  intros HCL HEL m kbs j cs24 bj ra1 t01 t11 t21 s1' a01 a11 a21 a31 a41 a51 a61 a71 s2' s3' s4' s5' s6' s7'
    s8' s9' s10' s11' t31 t41 t51 t61 MI WM MU ST FA L24 FB LB FS NK WF EC EE EI ES ESE EOP EOD ECL EMI ESN ENS
    ENX EU S0 SE0 CL BKs BAs.
  pose proof (bv_unsigned_in_range 64 sp4w) as R4. unfold bv_modulus in R4.
  destruct WF0 as (_ & _ & _ & _ & _ & _ & _ & _ & WE0 & _).
  zstep.
  eapply evt_cut; [apply HEL | intros ms' ->].
  rewrite ret_pc_even by (lia || reflexivity).
  assert (RDE : ov_read_bytes rsegs m (wa (bv_unsigned tp + ERRNO_TP_OFF + 0)) 4 = Some (le4 (wz (nk_end_errno kbs0)))).
  { unfold u32_at in EU. rewrite (bytes_at_read rsegs m _ _ 0 4 EU) by (try lia; rewrite length_le4; lia).
    rewrite skipn_O. apply f_equal. apply firstn_all2. rewrite length_le4. lia. }
  zstep. rewrite lw_u32 by lia.
  zstep. unfold wz at 2. rewrite unsigned_lit by lia.
  rewrite (bv_swrap_small 32 (0 - nk_end_errno kbs0))
    by (replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity; lia).
  replace (0 - nk_end_errno kbs0) with (nlv_rc NlNone (nk_end_errno kbs0)) by (cbn [nlv_rc]; lia).
  zstep.
  apply (nt_out HCL m kbs NlNone j) with (cs24 := cs24) (bj := bj); assumption.
Qed.

(* 0x160d8 .. : a chunk c came in; its message walk either ends (back to recv, Knone), or answers *)
Lemma nt_after_recv : copy_attr_contract -> fuzz_close_contract -> forall m kbs c rest i f j0 j1
    (ra1 t01 t11 t21 a11 a21 a31 a41 a51 a61 a71 t31 t41 t51 t61 : word),
  mem_inv rsegs m -> wmono rsegs m0 m -> munch W0 m0 m -> stk rsegs m lo (bv_unsigned sp4w) ->
  rw_cells rsegs m (bv_unsigned sp4w) [CB 16 j0; CB 8 j1] ->
  bytes_at rsegs m (bv_unsigned sp4w + 24) (c ++ rest) -> wr_at rsegs m (bv_unsigned sp4w + 24) 16384 ->
  Z.of_nat (length (c ++ rest)) = 16384 -> (length c <= 4096)%nat ->
  rw_cells rsegs m (bv_unsigned sp4w + 16408) SVc ->
  nlk_at m kbs -> nlk_wf kbs ->
  nk_chunks kbs = nk_chunks kbs0 -> nk_end_errno kbs = nk_end_errno kbs0 -> nk_n_if kbs = nk_n_if kbs0 ->
  nk_socket_errno kbs = 0 -> nk_send_errno kbs = 0 -> nk_open kbs = 1 -> nk_opened kbs = nk_opened kbs0 + 1 ->
  nk_closed kbs = nk_closed kbs0 -> nk_misuse kbs = nk_misuse kbs0 ->
  nk_sent kbs = owe (nk_sent kbs0) req -> nk_n_sent kbs = Z.of_nat (length (nk_sent kbs)) ->
  nk_next kbs = Z.of_nat (S i) -> wr_at rsegs m (bv_unsigned tp + ERRNO_TP_OFF) 4 ->
  nk_socket_errno kbs0 = 0 -> nk_send_errno kbs0 = 0 ->
  nth_error (nk_chunks kbs0) i = Some c ->
  chunk_loop (S (length (nk_chunks kbs0))) (nk_chunks kbs0) (Z.to_nat (nk_next kbs0))
    = chunk_loop (S f) (nk_chunks kbs0) i ->
  bufst m0 m (bv_unsigned a2) (bv_unsigned a3) None ->
  bufst m0 m (bv_unsigned a4) (bv_unsigned a5) None ->
  (chunk_walk c = NlNone -> forall a0' a1' a2' a3' : word,
     evt rsegs Q (MS (mkR ra1 sp4w gp tp t01 t11 t21 (wz NL_FD) a5 a0' a1' a2' a3' a41 a51 a61 a71
                          a4 a3 a2 (Z_to_bv 64 16) (Z_to_bv 64 2) (Z_to_bv 64 15) s8 s9 s10 s11 t31 t41 t51 t61)
                     F (Z_to_bv 64 0x16110) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra1 sp4w gp tp t01 t11 t21 (wz NL_FD) a5 (Z_to_bv 64 (Z.of_nat (length c))) a11 a21 a31
                       a41 a51 a61 a71 a4 a3 a2 (Z_to_bv 64 16) (Z_to_bv 64 2) (Z_to_bv 64 15) s8 s9 s10 s11
                       t31 t41 t51 t61)
                  F (Z_to_bv 64 0x160d8) fc None m (seg_rom rsegs)).
Proof.
  intros HCA HCL m kbs c rest i f j0 j1 ra1 t01 t11 t21 a11 a21 a31 a41 a51 a61 a71 t31 t41 t51 t61
    MI WM MU ST FA BB BW LCR LC FS NK WF EC EE EI ES ESE EOP EOD ECL EMI ESN ENS ENX EW S0 SE0 NC CL BKs BAs KN.
  pose proof (bv_unsigned_in_range 64 sp4w) as R4. unfold bv_modulus in R4.
  assert (FB : u8arr rsegs m (bv_unsigned sp4w + 24) (c ++ rest)) by (split; [exact BB | rewrite LCR; exact BW]).
  zstep. if_cases K1; zify_cond K1.
  { (* fewer than 16 bytes: no message *)
    apply KN. unfold chunk_walk. cbn [msg_scan]. unfold NL_HDR.
    replace (Z.of_nat (length c) <? 16) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  zstep.
  replace (bv_unsigned sp4w + 24) with (bv_unsigned sp4w + 24 + 0) by lia.
  apply (msg_loop ra1 sp4w gp tp t01 t11 t21 (wz NL_FD) a5 a41 a51 a61 a71 a4 a3 a2 s8 s9 s10 s11 t31 t41 t51 t61
           F fc m (bv_unsigned sp4w + 24) c rest Q BB LC (S (length c)) 0 (Z.of_nat (length c)));
    [lia | lia | lia | lia | | |].
  - (* the walk ended: the next chunk *)
    intros HW a0' a1' a2' a3'. apply KN. exact HW.
  - (* an NLMSG_ERROR: its code, or -EIO *)
    intros rc HE a0' a1' a2' a3'.
    assert (HV : chunk_walk c <> NlNone) by (unfold chunk_walk; destruct HE as [[-> _]| ->]; discriminate).
    rewrite (chunk_loop_hit f (nk_chunks kbs0) i c NC HV) in CL.
    assert (RC : nlv_rc (chunk_walk c) (nk_end_errno kbs0) = rc)
      by (unfold chunk_walk; destruct HE as [[-> ->]| ->]; reflexivity).
    rewrite <- RC.
    apply (nt_out HCL m kbs (chunk_walk c) (S i)) with (cs24 := [CB 16 j0; CB 8 j1]) (bj := c ++ rest);
      try assumption; try reflexivity.
    + unfold chunk_walk. destruct HE as [[-> _]| ->]; exact BKs.
    + unfold chunk_walk. destruct HE as [[-> _]| ->]; exact BAs.
  - (* the first RTM_NEWLINK *)
    intros f' off' ml HL HF H0 H16 HO a0' a3'.
    assert (HV : chunk_walk c <> NlNone) by (unfold chunk_walk; rewrite HL; discriminate).
    rewrite (chunk_loop_hit f (nk_chunks kbs0) i c NC HV) in CL. unfold chunk_walk in CL. rewrite HL in CL.
    replace (bv_unsigned sp4w + 24 + 0 + off') with (bv_unsigned sp4w + 24 + off') by lia.
    exact (nt_link HCA HCL m kbs c rest f' off' ml (S i) j0 j1 ra1 t01 t11 t21 a0' a3' a41 a51 a61 a71
             t31 t41 t51 t61 MI WM MU ST FA BB BW LCR LC FS NK WF EC EE EI ES ESE EOP EOD ECL EMI ESN ENS ENX EW
             S0 SE0 CL HF H0 H16 HO BKs BAs).
Qed.

(* what holds at each call of fuzz_recv: the socket is open, the request sent, i chunks read *)
Definition oinv (m : word -> option byte) (kbs : list byte) (i : nat) (j0 j1 bj : list byte) : Prop :=
  mem_inv rsegs m /\ wmono rsegs m0 m /\ munch W0 m0 m /\ stk rsegs m lo (bv_unsigned sp4w) /\
  rw_cells rsegs m (bv_unsigned sp4w) [CB 16 j0; CB 8 j1] /\
  u8arr rsegs m (bv_unsigned sp4w + 24) bj /\ Z.of_nat (length bj) = 16384 /\
  rw_cells rsegs m (bv_unsigned sp4w + 16408) SVc /\
  nlk_at m kbs /\ nlk_wf kbs /\
  nk_chunks kbs = nk_chunks kbs0 /\ nk_end_errno kbs = nk_end_errno kbs0 /\ nk_n_if kbs = nk_n_if kbs0 /\
  nk_socket_errno kbs = 0 /\ nk_send_errno kbs = 0 /\ nk_open kbs = 1 /\ nk_opened kbs = nk_opened kbs0 + 1 /\
  nk_closed kbs = nk_closed kbs0 /\ nk_misuse kbs = nk_misuse kbs0 /\
  nk_sent kbs = owe (nk_sent kbs0) req /\ nk_n_sent kbs = Z.of_nat (length (nk_sent kbs)) /\
  nk_next kbs = Z.of_nat i /\ wr_at rsegs m (bv_unsigned tp + ERRNO_TP_OFF) 4 /\
  bufst m0 m (bv_unsigned a2) (bv_unsigned a3) None /\ bufst m0 m (bv_unsigned a4) (bv_unsigned a5) None.

(* one call of fuzz_recv(fd, sp + 24, 16384, 0), returning to rpc *)
Lemma nt_recv_call : fuzz_recv_contract -> forall rpc m kbs i j0 j1 bj
    (t01 t11 t21 s1' a41 a51 a61 a71 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t31 t41 t51 t61 : word),
  oinv m kbs i j0 j1 bj ->
  (forall m' kbs' c rest (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     oinv m' kbs' (S i) j0 j1 (c ++ rest) -> nth_error (nk_chunks kbs0) i = Some c -> (length c <= 4096)%nat ->
     evt rsegs Q (MS (mkR ra' sp4w gp tp t0' t1' t2' (wz NL_FD) s1' (Z_to_bv 64 (Z.of_nat (length c))) a1' a2' a3'
                          a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
                     F (ret_pc (Z_to_bv 64 rpc)) fc None m' (seg_rom rsegs))) ->
  (forall m' kbs' bj' (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     oinv m' kbs' i j0 j1 bj' -> nk_n_chunks kbs0 <= Z.of_nat i ->
     u32_at m' (bv_unsigned tp + ERRNO_TP_OFF) (nk_end_errno kbs0) ->
     evt rsegs Q (MS (mkR ra' sp4w gp tp t0' t1' t2' (wz NL_FD) s1' (wz (-1)) a1' a2' a3'
                          a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
                     F (ret_pc (Z_to_bv 64 rpc)) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR (Z_to_bv 64 rpc) sp4w gp tp t01 t11 t21 (wz NL_FD) s1' (wz NL_FD)
                       (Z_to_bv 64 (bv_unsigned sp4w + 24)) (Z_to_bv 64 16384) (Z_to_bv 64 0)
                       a41 a51 a61 a71 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t31 t41 t51 t61)
                  F (Z_to_bv 64 FUZZ_RECV) fc None m (seg_rom rsegs)).
Proof.
  intros HRE rpc m kbs i j0 j1 bj t01 t11 t21 s1' a41 a51 a61 a71 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11'
    t31 t41 t51 t61 OI KS KF.
  destruct OI as (MI & WM & MU & ST & FA & FB & LB & FS & NK & WF & EC & EE & EI & ES & ESE & EOP & EOD & ECL
                  & EMI & ESN & ENS & ENX & EW & BKs & BAs).
  pose proof (bv_unsigned_in_range 64 sp4w) as R4. unfold bv_modulus in R4.
  pose proof FG0 as FG1. unfold apart_gnl, NK_SIZE in FG1. pose proof EG0 as EG1. unfold apart_gnl, NK_SIZE in EG1.
  eapply (leaf_call FUZZ_RECV 80 _ _ _ HRE nt_re_post_ext Q QX).
  { cbv beta. rewrite ?mkR_sp, ?mkR_a1, ?mkR_a2, ?mkR_errno.
    rewrite !unsigned_lit by lia.
    pose proof EF0 as EF1. unfold link_mem.ERRNO_TP_OFF, __errno_location_c.ERRNO_TP_OFF in EF1, EG1 |- *.
    exists kbs, bj. split; [exact NK|].
    split; [unfold frame_apart_gnl, apart_gnl; rewrite mkR_sp; unfold NK_SIZE; lia|].
    split; [exact WF|]. split; [exact EW|].
    split; [unfold apart_frame; rewrite mkR_sp; lia|]. split; [exact EG0|].
    split; [unfold NL_CHUNK_MAX; lia|].
    split; [pose proof (rw_cells_of_u8arr rsegs m _ bj FB) as RC; replace (Z.to_nat 16384) with (length bj) by lia;
            exact RC|].
    split; [unfold apart_gnl, NK_SIZE; lia|].
    unfold apart_frame; rewrite mkR_sp; lia. }
  { exact MI. }
  { exact ST. }
  { lia. }
  { lia. }
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MUc WMc MIc STc PO.
  cbv beta in MUc, PO. rewrite ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_errno in MUc. rewrite ?unsigned_lit in MUc by lia.
  destruct (PO kbs NK) as (kbs' & NK' & WF' & ENC' & EE' & ES' & ESE' & EC' & EOP' & EOD' & ECL' & ENS' & EMI'
                           & PF & PS & RCB).
  rewrite mkR_a0 in EMI'. unfold wz, NL_FD in EMI'. rewrite unsigned_lit in EMI' by lia.
  rewrite EOP in EMI'. replace ((7 =? 7) && negb (1 =? 0)) with true in EMI' by reflexivity.
  set (Wr := (bv_unsigned sp4w - 80, bv_unsigned sp4w)
             :: [(A_G_NL + NK_NEXT, A_G_NL + NK_MISUSE + 4);
                 (bv_unsigned tp + ERRNO_TP_OFF, bv_unsigned tp + ERRNO_TP_OFF + 4);
                 (bv_unsigned sp4w + 24, bv_unsigned sp4w + 24 + 16384)]) in MUc.
  pose proof EF0 as EF2. unfold link_mem.ERRNO_TP_OFF, __errno_location_c.ERRNO_TP_OFF in EF2, EG1.
  assert (KEEP : forall o n, 0 <= o -> 0 <= n -> o + n <= NK_SIZE ->
                   (o + n <= NK_NEXT \/ NK_MISUSE + 4 <= o) -> disjoint_from Wr (A_G_NL + o) n).
  { intros o n H1 H2 H3 H4. unfold Wr, NK_SIZE, NK_NEXT, NK_MISUSE in *. cbn [disjoint_from].
    unfold link_mem.ERRNO_TP_OFF, __errno_location_c.ERRNO_TP_OFF. repeat split; lia. }
  assert (ESN' : nk_sent kbs' = nk_sent kbs).
  { apply nk_sent_keep; [exact WF|].
    apply (nlk_slice_keep Wr m m'); try assumption; try (unfold NK_SENT, NK_N_SENT, NK_SIZE; lia).
    apply KEEP; unfold NK_SENT, NK_N_SENT, NK_SIZE, NK_NEXT, NK_MISUSE; lia. }
  assert (EI' : nk_n_if kbs' = nk_n_if kbs).
  { unfold nk_n_if, fld_u32. apply (fld_keep Wr m m'); try assumption; try (unfold NK_N_IF, NK_SIZE; lia).
    apply KEEP; unfold NK_N_IF, NK_MISUSE, NK_SIZE; lia. }
  assert (SUB : forall x, outside W0 x -> outside Wr x).
  { intros x Hx. destruct (W0_out x Hx) as (H1 & H2 & H3 & _).
    unfold link_mem.ERRNO_TP_OFF, __errno_location_c.ERRNO_TP_OFF in H3.
    unfold Wr, NK_NEXT, NK_MISUSE, NK_N_SENT in *. cbn [outside].
    unfold link_mem.ERRNO_TP_OFF, __errno_location_c.ERRNO_TP_OFF. repeat split; lia. }
  assert (DFR : forall a n, bv_unsigned sp4w <= a -> a + n <= bv_unsigned sp4w + 24 \/ bv_unsigned sp4w + 16408 <= a ->
                  a + n <= bv_unsigned sp - 0 -> 0 <= n -> disjoint_from Wr a n).
  { intros a n H1 H2 H3 H4. unfold Wr. cbn [disjoint_from].
    unfold link_mem.ERRNO_TP_OFF, __errno_location_c.ERRNO_TP_OFF. unfold NK_SIZE in FG1.
    unfold NK_NEXT, NK_MISUSE. repeat split; lia. }
  assert (FA' : rw_cells rsegs m' (bv_unsigned sp4w) [CB 16 j0; CB 8 j1]).
  { apply (rw_cells_transport rsegs Wr m m'); [exact FA | exact MUc | exact WMc |].
    cbn [cells_size csize Nat.add]. apply DFR; lia. }
  assert (FS' : rw_cells rsegs m' (bv_unsigned sp4w + 16408) SVc).
  { apply (rw_cells_transport rsegs Wr m m'); [exact FS | exact MUc | exact WMc |].
    unfold SVc. cbn [cells_size csize Nat.add]. apply DFR; lia. }
  assert (DB : forall b n, b <> 0 -> (b + n <= bv_unsigned sp - 16592 \/ bv_unsigned sp <= b) ->
                 apart_gnl b n -> apart (bv_unsigned tp + ERRNO_TP_OFF) 4 b n -> disjoint_from Wr b n).
  { intros b n Hb H1 H2 H3. unfold apart_gnl, NK_SIZE in H2. unfold apart in H3. unfold Wr. cbn [disjoint_from].
    unfold link_mem.ERRNO_TP_OFF, __errno_location_c.ERRNO_TP_OFF in *. unfold NK_NEXT, NK_MISUSE.
    repeat split; lia. }
  assert (BK' : bufst m0 m' (bv_unsigned a2) (bv_unsigned a3) None).
  { eapply bufst_keep; [exact BKs | exact MUc | exact WMc |]. intros Hb _.
    destruct (KF0 Hb) as [H1 H2]. exact (DB _ _ Hb H1 H2 (EK0 Hb)). }
  assert (BA' : bufst m0 m' (bv_unsigned a4) (bv_unsigned a5) None).
  { eapply bufst_keep; [exact BAs | exact MUc | exact WMc |]. intros Hb _.
    destruct (AF0 Hb) as [H1 H2]. exact (DB _ _ Hb H1 H2 (EA0 Hb)). }
  pose proof (wr_at_transport rsegs _ _ _ _ EW WMc) as EW'.
  pose proof (wr_at_transport rsegs _ _ _ _ (proj2 FB) WMc) as BW'. rewrite LB in BW'.
  pose proof (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MUc)) as MU'.
  pose proof (wmono_trans rsegs _ _ _ WM WMc) as WM'.
  destruct (Z_lt_le_dec (nk_next kbs) (nk_n_chunks kbs)) as [LT|GE].
  - (* a chunk *)
    destruct (PS LT) as (R10 & NX' & rest & BB' & LR'). rewrite getr10_mkR in R10. subst a0'.
    rewrite mkR_a1, unsigned_lit in BB' by lia. rewrite mkR_a2, unsigned_lit in LR' by lia.
    pose proof (nk_chunk_len kbs (nk_next kbs) WF ltac:(destruct WF as (_ & HN & _); lia)) as LC.
    apply (KS m' kbs' (nk_chunk kbs (nk_next kbs)) rest).
    + unfold oinv.
      assert (LCR : Z.of_nat (length (nk_chunk kbs (nk_next kbs) ++ rest)) = 16384) by (rewrite length_app; lia).
      assert (FB' : u8arr rsegs m' (bv_unsigned sp4w + 24) (nk_chunk kbs (nk_next kbs) ++ rest))
        by (split; [exact BB' | rewrite LCR; exact BW']).
      refine (conj MIc (conj WM' (conj MU' (conj STc (conj FA' (conj FB'
               (conj LCR (conj FS' (conj NK' (conj WF' _)))))))))).
      split; [rewrite EC'; exact EC|]. split; [rewrite EE'; exact EE|]. split; [rewrite EI'; exact EI|].
      split; [rewrite ES'; exact ES|]. split; [rewrite ESE'; exact ESE|]. split; [rewrite EOP'; exact EOP|].
      split; [rewrite EOD'; exact EOD|]. split; [rewrite ECL'; exact ECL|]. split; [rewrite EMI'; exact EMI|].
      split; [rewrite ESN'; exact ESN|]. split; [rewrite ENS', ESN'; exact ENS|].
      split; [rewrite NX', ENX; lia|]. split; [exact EW'|]. split; [exact BK' | exact BA'].
    + rewrite <- EC. replace i with (Z.to_nat (nk_next kbs)) by lia.
      apply nk_chunks_nth. destruct WF as (_ & HN & _). lia.
    + exact LC.
  - (* the queue is empty: recv answers -1 and leaves the end errno *)
    destruct (PF GE) as (R10 & NX' & EU). rewrite getr10_mkR in R10. subst a0'.
    rewrite mkR_errno in EU. rewrite EE in EU.
    destruct RCB as [junk RCB]. rewrite mkR_a1, mkR_a2, !unsigned_lit in RCB by lia.
    assert (LJ : Z.of_nat (length junk) = 16384) by (destruct RCB as [[HJ _] _]; cbn in HJ; lia).
    pose proof (u8arr_of_rw_cells rsegs m' _ _ _ RCB) as FBj.
    apply (KF m' kbs' junk).
    + unfold oinv.
      refine (conj MIc (conj WM' (conj MU' (conj STc (conj FA' (conj FBj
               (conj LJ (conj FS' (conj NK' (conj WF' _)))))))))).
      split; [rewrite EC'; exact EC|]. split; [rewrite EE'; exact EE|]. split; [rewrite EI'; exact EI|].
      split; [rewrite ES'; exact ES|]. split; [rewrite ESE'; exact ESE|]. split; [rewrite EOP'; exact EOP|].
      split; [rewrite EOD'; exact EOD|]. split; [rewrite ECL'; exact ECL|]. split; [rewrite EMI'; exact EMI|].
      split; [rewrite ESN'; exact ESN|]. split; [rewrite ENS', ESN'; exact ENS|].
      split; [rewrite NX', ENX; reflexivity|]. split; [exact EW'|]. split; [exact BK' | exact BA'].
    + rewrite <- (nk_chunks_length kbs0 WF0), <- EC, (nk_chunks_length kbs WF). lia.
    + exact EU.
Qed.

(* 0x16110 .. 0x16124: the receive loop: fetch the next chunk and walk it, until a chunk answers or
   the queue is empty *)
Lemma nt_loop : copy_attr_contract -> fuzz_close_contract -> fuzz_recv_contract -> __errno_location_contract ->
  forall n i m kbs j0 j1 bj (ra1 t01 t11 t21 a01 a11 a21 a31 a41 a51 a61 a71 t31 t41 t51 t61 : word),
  (length (nk_chunks kbs0) - i < n)%nat -> (Z.to_nat (nk_next kbs0) <= i)%nat ->
  oinv m kbs i j0 j1 bj ->
  chunk_loop (S (length (nk_chunks kbs0))) (nk_chunks kbs0) (Z.to_nat (nk_next kbs0))
    = chunk_loop (S (length (nk_chunks kbs0)) + Z.to_nat (nk_next kbs0) - i) (nk_chunks kbs0) i ->
  nk_socket_errno kbs0 = 0 -> nk_send_errno kbs0 = 0 ->
  evt rsegs Q (MS (mkR ra1 sp4w gp tp t01 t11 t21 (wz NL_FD) a5 a01 a11 a21 a31 a41 a51 a61 a71
                       a4 a3 a2 (Z_to_bv 64 16) (Z_to_bv 64 2) (Z_to_bv 64 15) s8 s9 s10 s11 t31 t41 t51 t61)
                  F (Z_to_bv 64 0x16110) fc None m (seg_rom rsegs)).
Proof.
  intros HCA HCL HRE HEL n. induction n as [|n IH];
    intros i m kbs j0 j1 bj ra1 t01 t11 t21 a01 a11 a21 a31 a41 a51 a61 a71 t31 t41 t51 t61 HN HI OI CL0 S0 SE0;
    [lia|].
  pose proof (bv_unsigned_in_range 64 sp4w) as R4. unfold bv_modulus in R4.
  zstep. zstep. zstep. zstep. zstep.
  eapply (nt_recv_call HRE 0x16124 m kbs i j0 j1 bj); [exact OI | |].
  - (* a chunk came in *)
    intros m' kbs' c rest ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' OI' NC LC.
    rewrite ret_pc_even by (lia || reflexivity).
    destruct OI' as (MI & WM & MU & ST & FA & FB & LB & FS & NK & WF & EC & EE & EI & ES & ESE & EOP & EOD
                     & ECL & EMI & ESN & ENS & ENX & EW & BKs & BAs).
    pose proof FB as [BB BW]. rewrite LB in BW.
    assert (HL : (i < length (nk_chunks kbs0))%nat) by (apply nth_error_Some; rewrite NC; discriminate).
    zstep. if_cases K; zify_cond K; try unfold wz in K; try rewrite sgn_lit in K by lia; [| exfalso; lia].
    set (f := (length (nk_chunks kbs0) + Z.to_nat (nk_next kbs0) - i)%nat).
    assert (CL1 : chunk_loop (S (length (nk_chunks kbs0))) (nk_chunks kbs0) (Z.to_nat (nk_next kbs0))
                  = chunk_loop (S f) (nk_chunks kbs0) i) by (rewrite CL0; f_equal; unfold f; lia).
    apply (nt_after_recv HCA HCL m' kbs' c rest i f j0 j1); try assumption.
    intros HW a0' a1'' a2'' a3''.
    apply (IH (S i) m' kbs' j0 j1 (c ++ rest)); [lia | lia | | | exact S0 | exact SE0].
    + exact (conj MI (conj WM (conj MU (conj ST (conj FA (conj FB
               (conj LB (conj FS (conj NK (conj WF (conj EC (conj EE (conj EI (conj ES (conj ESE (conj EOP
               (conj EOD (conj ECL (conj EMI (conj ESN (conj ENS (conj ENX (conj EW (conj BKs BAs)))))))))))))))))))))))).
    + rewrite CL1. rewrite (chunk_loop_step f (nk_chunks kbs0) i c NC HW). first [reflexivity | f_equal; unfold f; lia].
  - (* the queue is empty *)
    intros m' kbs' bj' ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' OI' GE EU.
    rewrite ret_pc_even by (lia || reflexivity).
    destruct OI' as (MI & WM & MU & ST & FA & FB & LB & FS & NK & WF & EC & EE & EI & ES & ESE & EOP & EOD
                     & ECL & EMI & ESN & ENS & ENX & EW & BKs & BAs).
    zstep. if_cases K; zify_cond K; [try unfold wz in K; rewrite um1 in K; lia|].
    apply (nt_rfail HCL HEL m' kbs' i [CB 16 j0; CB 8 j1] bj'); try assumption; try reflexivity.
    rewrite CL0. apply chunk_loop_end. apply nth_error_None.
    pose proof (nk_chunks_length kbs0 WF0). lia.
Qed.

(* 0x160b4 .. 0x160d4: the first fuzz_recv, after the request went out *)
Lemma nt_first : copy_attr_contract -> fuzz_close_contract -> fuzz_recv_contract -> __errno_location_contract ->
  forall m kbs j0 j1 bj (ra1 t01 t11 t21 a01 a11 a21 a31 a41 a51 a61 a71 s5' s6' s7' t31 t41 t51 t61 : word),
  oinv m kbs (Z.to_nat (nk_next kbs0)) j0 j1 bj ->
  nk_socket_errno kbs0 = 0 -> nk_send_errno kbs0 = 0 ->
  evt rsegs Q (MS (mkR ra1 sp4w gp tp t01 t11 t21 (wz NL_FD) a5 a01 a11 a21 a31 a41 a51 a61 a71
                       a4 a3 a2 s5' s6' s7' s8 s9 s10 s11 t31 t41 t51 t61)
                  F (Z_to_bv 64 0x160b4) fc None m (seg_rom rsegs)).
Proof.
  intros HCA HCL HRE HEL m kbs j0 j1 bj ra1 t01 t11 t21 a01 a11 a21 a31 a41 a51 a61 a71 s5' s6' s7' t31 t41 t51 t61
    OI S0 SE0.
  pose proof (bv_unsigned_in_range 64 sp4w) as R4. unfold bv_modulus in R4.
  set (i0 := Z.to_nat (nk_next kbs0)) in *.
  zstep. zstep. zstep. zstep. zstep.
  eapply (nt_recv_call HRE 0x160c8 m kbs i0 j0 j1 bj); [exact OI | |].
  - (* a chunk came in *)
    intros m' kbs' c rest ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' OI' NC LC.
    rewrite ret_pc_even by (lia || reflexivity).
    destruct OI' as (MI & WM & MU & ST & FA & FB & LB & FS & NK & WF & EC & EE & EI & ES & ESE & EOP & EOD
                     & ECL & EMI & ESN & ENS & ENX & EW & BKs & BAs).
    pose proof FB as [BB BW]. rewrite LB in BW.
    assert (HL : (i0 < length (nk_chunks kbs0))%nat) by (apply nth_error_Some; rewrite NC; discriminate).
    zstep. if_cases K; zify_cond K; try unfold wz in K; try rewrite sgn_lit in K by lia; [exfalso; lia|].
    zstep. zstep. zstep.
    apply (nt_after_recv HCA HCL m' kbs' c rest i0 (length (nk_chunks kbs0)) j0 j1); try assumption; try reflexivity.
    intros HW a0' a1'' a2'' a3''.
    apply (nt_loop HCA HCL HRE HEL (S (length (nk_chunks kbs0))) (S i0) m' kbs' j0 j1 (c ++ rest));
      [lia | unfold i0; lia | | | exact S0 | exact SE0].
    + exact (conj MI (conj WM (conj MU (conj ST (conj FA (conj FB
               (conj LB (conj FS (conj NK (conj WF (conj EC (conj EE (conj EI (conj ES (conj ESE (conj EOP
               (conj EOD (conj ECL (conj EMI (conj ESN (conj ENS (conj ENX (conj EW (conj BKs BAs)))))))))))))))))))))))).
    + fold i0. rewrite (chunk_loop_step (length (nk_chunks kbs0)) (nk_chunks kbs0) i0 c NC HW).
      first [reflexivity | f_equal; lia].
  - (* the queue is empty *)
    intros m' kbs' bj' ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' OI' GE EU.
    rewrite ret_pc_even by (lia || reflexivity).
    destruct OI' as (MI & WM & MU & ST & FA & FB & LB & FS & NK & WF & EC & EE & EI & ES & ESE & EOP & EOD
                     & ECL & EMI & ESN & ENS & ENX & EW & BKs & BAs).
    zstep. if_cases K; zify_cond K; [|try unfold wz in K; rewrite um1 in K; lia].
    apply (nt_rfail HCL HEL m' kbs' i0 [CB 16 j0; CB 8 j1] bj'); try assumption; try reflexivity.
    fold i0. apply chunk_loop_end. apply nth_error_None.
    pose proof (nk_chunks_length kbs0 WF0). lia.
Qed.

(* the footprint of a callee nl_talk calls with sp = sp4w: its own frame below sp4w, a part of g_nl
   up to the request ring, errno *)
Definition okC (W : list ivl) : Prop :=
  Forall (fun lh : ivl => let (l, h) := lh in
    (bv_unsigned sp - 16592 <= l /\ h <= bv_unsigned sp4w) \/
    (A_G_NL <= l /\ h <= A_G_NL + NK_N_SENT + 4) \/
    (l = bv_unsigned tp + ERRNO_TP_OFF /\ h = l + 4)) W.

Lemma okC_ext : forall W b n, okC W -> 0 <= n ->
  (b + n <= bv_unsigned sp - 16592 \/ bv_unsigned sp <= b) -> apart_gnl b n ->
  apart (bv_unsigned tp + ERRNO_TP_OFF) 4 b n -> disjoint_from W b n.
Proof.
  intros W b n OK H0 H1 H2 H3. unfold apart_gnl, NK_SIZE in H2. unfold apart in H3.
  induction OK as [|[l h] W P OK IH]; [exact I|]. cbn [disjoint_from]. split; [|exact IH].
  unfold NK_N_SENT in P. lia.
Qed.

Lemma okC_frame : forall W a n, okC W -> bv_unsigned sp4w <= a -> a + n <= bv_unsigned sp -> 0 <= n ->
  disjoint_from W a n.
Proof.
  intros W a n OK H1 H2 H3. pose proof FG0 as G. pose proof EF0 as E. unfold apart_gnl, NK_SIZE in G.
  induction OK as [|[l h] W P OK IH]; [exact I|]. cbn [disjoint_from]. split; [|exact IH].
  unfold NK_N_SENT in P. lia.
Qed.

Lemma okC_sub : forall W, okC W -> forall x, outside W0 x -> outside W x.
Proof.
  intros W OK x Hx. destruct (W0_out x Hx) as (H1 & H2 & H3 & _).
  induction OK as [|[l h] W P OK IH]; [exact I|]. cbn [outside]. split; [|exact IH]. lia.
Qed.

Ltac okc := repeat (apply Forall_cons; [cbn beta iota;
  unfold NK_SOCKET_ERRNO, NK_SEND_ERRNO, NK_OPEN, NK_MISUSE, NK_N_SENT, NK_NEXT, NK_SIZE,
    link_mem.ERRNO_TP_OFF, __errno_location_c.ERRNO_TP_OFF in *; lia|]); apply Forall_nil.

Ltac nsp := repeat match goal with
  | |- context [Z.sub (Z.add ?b ?c) ?d] => is_Zlit c; is_Zlit d;
      let v := eval vm_compute in (c - d)%Z in replace (Z.sub (Z.add b c) d) with (Z.add b v) by lia
  | |- context [Z.add (Z.add ?b ?c) ?d] => is_Zlit c; is_Zlit d;
      let v := eval vm_compute in (c + d)%Z in replace (Z.add (Z.add b c) d) with (Z.add b v) by lia
  end.

Ltac djn := cbn [disjoint_from];
  unfold NK_SOCKET_ERRNO, NK_SEND_ERRNO, NK_OPEN, NK_MISUSE, NK_N_SENT, NK_NEXT, NK_SIZE, NK_SENT,
    link_mem.ERRNO_TP_OFF, __errno_location_c.ERRNO_TP_OFF in *; repeat split; lia.

(* what holds of the frame, the buffers, errno and the request from the prologue to fuzz_recv *)
Definition finvb (mb m : word -> option byte) (j0 j1 bj : list byte) : Prop :=
  mem_inv rsegs m /\ wmono rsegs mb m /\ munch W0 mb m /\ stk rsegs m lo (bv_unsigned sp4w) /\
  rw_cells rsegs m (bv_unsigned sp4w) [CB 16 j0; CB 8 j1] /\
  u8arr rsegs m (bv_unsigned sp4w + 24) bj /\ Z.of_nat (length bj) = 16384 /\
  rw_cells rsegs m (bv_unsigned sp4w + 16408) SVc /\
  wr_at rsegs m (bv_unsigned tp + ERRNO_TP_OFF) 4 /\
  bufst mb m (bv_unsigned a2) (bv_unsigned a3) None /\ bufst mb m (bv_unsigned a4) (bv_unsigned a5) None /\
  bytes_at rsegs m (bv_unsigned a0) req.
Definition finv := finvb m0.

Lemma fkeep : forall W m m' j0 j1 bj, finv m j0 j1 bj -> okC W -> munch W m m' -> wmono rsegs m m' ->
  mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp4w) -> finv m' j0 j1 bj.
Proof.
  intros W m m' j0 j1 bj (MI & WM & MU & ST & FA & FB & LB & FS & EW & BK & BA & RQ) OK MUc WMc MIc STc.
  pose proof (bv_unsigned_in_range 64 sp4w) as R4. unfold bv_modulus in R4.
  pose proof (bv_unsigned_in_range 64 a3) as R3. pose proof (bv_unsigned_in_range 64 a5) as R5.
  unfold bv_modulus in R3, R5.
  split; [exact MIc|]. split; [exact (wmono_trans rsegs _ _ _ WM WMc)|].
  split; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (okC_sub W OK) MUc))|].
  split; [exact STc|].
  split; [apply (rw_cells_transport rsegs W m m'); [exact FA | exact MUc | exact WMc |];
          cbn [cells_size csize Nat.add]; apply okC_frame; [exact OK | lia | lia | lia]|].
  split; [apply (u8arr_transport rsegs W m m'); [exact FB | exact MUc | exact WMc |];
          rewrite LB; apply okC_frame; [exact OK | lia | lia | lia]|].
  split; [exact LB|].
  split; [apply (rw_cells_transport rsegs W m m'); [exact FS | exact MUc | exact WMc |];
          unfold SVc; cbn [cells_size csize Nat.add]; apply okC_frame; [exact OK | lia | lia | lia]|].
  split; [exact (wr_at_transport rsegs _ _ _ _ EW WMc)|].
  split; [eapply bufst_keep; [exact BK | exact MUc | exact WMc |]; intros Hb _;
          destruct (KF0 Hb) as [H1 H2]; apply (okC_ext W); [exact OK | lia | exact H1 | exact H2 | exact (EK0 Hb)]|].
  split; [eapply bufst_keep; [exact BA | exact MUc | exact WMc |]; intros Hb _;
          destruct (AF0 Hb) as [H1 H2]; apply (okC_ext W); [exact OK | lia | exact H1 | exact H2 | exact (EA0 Hb)]|].
  apply (bytes_at_transport rsegs W m m'); [exact RQ | exact MUc |].
  rewrite RL0. apply (okC_ext W); [exact OK | lia | exact RF0 | exact RG0 | exact ERQ].
Qed.

(* the fields of g_nl below NK_SOCKET_ERRNO and past the request ring: no callee of the socket phase
   writes them *)
Lemma gnl_keep : forall W m m' bs bs', nlk_at m bs -> nlk_at m' bs' -> munch W m m' -> nlk_wf bs ->
  disjoint_from W (A_G_NL + 0) NK_SOCKET_ERRNO ->
  disjoint_from W (A_G_NL + (NK_N_SENT + 4)) (NK_SIZE - (NK_N_SENT + 4)) ->
  nk_chunks bs' = nk_chunks bs /\ nk_next bs' = nk_next bs /\ nk_end_errno bs' = nk_end_errno bs /\
  nk_n_if bs' = nk_n_if bs.
Proof.
  intros W m m' bs bs' NK NK' MU WF D1 D2.
  pose proof (nlk_slice_keep W m m' bs bs' 0 NK_SOCKET_ERRNO NK NK' MU D1
                ltac:(lia) ltac:(unfold NK_SOCKET_ERRNO; lia) ltac:(unfold NK_SOCKET_ERRNO, NK_SIZE; lia)) as S1.
  pose proof (nlk_slice_keep W m m' bs bs' (NK_N_SENT + 4) (NK_SIZE - (NK_N_SENT + 4)) NK NK' MU D2
                ltac:(unfold NK_N_SENT; lia) ltac:(unfold NK_N_SENT, NK_SIZE; lia) ltac:(lia)) as S2.
  split; [apply (nk_chunks_keep bs bs' WF);
          apply (slice_sub_eq bs bs' 0 NK_SOCKET_ERRNO 0 NK_NEXT); unfold NK_SOCKET_ERRNO, NK_NEXT; try lia; exact S1|].
  split; [unfold nk_next, fld_u32;
          apply (rdn_sub_eq bs bs' 0 NK_SOCKET_ERRNO NK_NEXT 4); unfold NK_SOCKET_ERRNO, NK_NEXT; try lia; exact S1|].
  split; [unfold nk_end_errno, fld_u32;
          apply (rdn_sub_eq bs bs' 0 NK_SOCKET_ERRNO NK_END_ERRNO 4);
          unfold NK_SOCKET_ERRNO, NK_END_ERRNO; try lia; exact S1|].
  unfold nk_n_if, fld_u32.
  apply (rdn_sub_eq bs bs' (NK_N_SENT + 4) (NK_SIZE - (NK_N_SENT + 4)) NK_N_IF 4);
    unfold NK_N_SENT, NK_SIZE, NK_N_IF; try lia; exact S2.
Qed.

Lemma gnl_keep_sent : forall W m m' bs bs', nlk_at m bs -> nlk_at m' bs' -> munch W m m' -> nlk_wf bs ->
  disjoint_from W (A_G_NL + NK_SENT) (NK_N_SENT + 4 - NK_SENT) -> nk_sent bs' = nk_sent bs.
Proof.
  intros W m m' bs bs' NK NK' MU WF D. apply (nk_sent_keep bs bs' WF).
  apply (nlk_slice_keep W m m' bs bs' NK_SENT (NK_N_SENT + 4 - NK_SENT) NK NK' MU D);
    unfold NK_SENT, NK_N_SENT, NK_SIZE; lia.
Qed.

(* the contract's Post on an exchange that ends before any chunk is read *)
Lemma post_early : forall m kbs1 rc,
  nlk_at m kbs1 -> nlk_wf kbs1 ->
  nk_chunks kbs1 = nk_chunks kbs0 -> nk_end_errno kbs1 = nk_end_errno kbs0 -> nk_n_if kbs1 = nk_n_if kbs0 ->
  nk_socket_errno kbs1 = 0 -> nk_send_errno kbs1 = k_send (talk_after (nk_kstate kbs0)) ->
  nk_next kbs1 = nk_next kbs0 -> nk_sent kbs1 = nk_sent kbs0 ->
  nk_open kbs1 = 0 -> nk_misuse kbs1 = nk_misuse kbs0 ->
  nk_opened kbs1 - nk_closed kbs1 = nk_opened kbs0 - nk_closed kbs0 ->
  (nk_socket_errno kbs0 <> 0 -> nk_opened kbs1 = nk_opened kbs0) ->
  (nk_socket_errno kbs0 = 0 -> nk_opened kbs1 = nk_opened kbs0 + 1) ->
  talk_rc_lib (nk_kstate kbs0) = rc -> talk_attrs (nk_kstate kbs0) = no_attrs ->
  talk_owes (nk_kstate kbs0) = false ->
  k_next (talk_after (nk_kstate kbs0)) = k_next (nk_kstate kbs0) ->
  bufst m0 m (bv_unsigned a2) (bv_unsigned a3) None -> bufst m0 m (bv_unsigned a4) (bv_unsigned a5) None ->
  forall regs', getr regs' 10 = wz rc -> nt_post R0 m0 regs' m.
Proof.
  intros m kbs1 rc NK WF EC EE EI ES ESE ENX ESN EOP EMI EOD O1 O2 TRC TAT TOW TKN BKs BAs regs' R10.
  unfold nt_post. intros kbsx reqx NKx RQx RLx.
  unfold R0 in RQx, RLx. rewrite mkR_a0 in RQx. rewrite mkR_a1 in RLx.
  destruct (kbs_req_unique kbsx reqx NKx RQx RLx) as [E1 E2]. subst kbsx reqx. cbv zeta.
  unfold R0. rewrite ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_a5.
  rewrite TRC, TAT, TOW, TKN.
  split; [exact R10|].
  split.
  { exists kbs1. split; [exact NK|]. split; [exact WF|].
    split; [exact EC|]. split; [exact EE|]. split; [exact EI|]. split; [exact ES|]. split; [exact ESE|].
    split; [rewrite ENX; unfold nk_kstate; cbn [k_next]; rewrite Z2Nat.id; [reflexivity|];
            destruct WF0 as (_ & HN & _); lia|].
    split; [exact ESN|]. split; [exact (nk_sent_len kbs1 WF)|].
    split; [exact EOP|]. split; [exact EMI|]. split; [exact EOD|]. split; [exact O1 | exact O2]. }
  destruct BKs as [BKr BKt]. destruct BAs as [BAr BAt]. try unfold no_attrs. cbn [a_kind a_alias].
  split; [intros pay E; discriminate E|]. split; [intros pay E; discriminate E|].
  split; [intros _; exact BKt|]. split; [intros _; exact BAt|]. split; [exact BKr | exact BAr].
Qed.

Lemma negw_wz : forall e, 0 <= e < 2 ^ 31 -> bv_swrap 32 (0 - bv_unsigned (wz e)) = - e.
Proof.
  intros e H. rewrite uwz by lia. rewrite bv_swrap_small; [lia|].
  replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity. lia.
Qed.

(* 0x16098, socket failed: errno's value, negated, is the answer; no close *)
Lemma nt_sfail : __errno_location_contract -> forall m kbs1 j0 j1 bj
    (ra1 t01 t11 t21 s01 s11 a11 a21 a31 a41 a51 a61 a71 s21 s31 s41 s51 s61 s71 s81 s91 s101 s111
     t31 t41 t51 t61 : word),
  finv m j0 j1 bj -> nlk_at m kbs1 -> nlk_wf kbs1 -> nk_socket_errno kbs0 <> 0 ->
  u32_at m (bv_unsigned tp + ERRNO_TP_OFF) (nk_socket_errno kbs0) ->
  nk_chunks kbs1 = nk_chunks kbs0 -> nk_end_errno kbs1 = nk_end_errno kbs0 -> nk_n_if kbs1 = nk_n_if kbs0 ->
  nk_socket_errno kbs1 = 0 -> nk_send_errno kbs1 = nk_send_errno kbs0 -> nk_next kbs1 = nk_next kbs0 ->
  nk_sent kbs1 = nk_sent kbs0 -> nk_open kbs1 = nk_open kbs0 -> nk_opened kbs1 = nk_opened kbs0 ->
  nk_closed kbs1 = nk_closed kbs0 -> nk_misuse kbs1 = nk_misuse kbs0 ->
  evt rsegs Q (MS (mkR ra1 sp4w gp tp t01 t11 t21 s01 s11 (wz (-1)) a11 a21 a31 a41 a51 a61 a71
                       s21 s31 s41 s51 s61 s71 s81 s91 s101 s111 t31 t41 t51 t61)
                  F (Z_to_bv 64 0x16098) fc None m (seg_rom rsegs)).
Proof.
  intros HEL m kbs1 j0 j1 bj ra1 t01 t11 t21 q0 q1 b1 b2 b3 b4 b5 b6 b7 q2 q3 q4 q5 q6 q7 q8 q9
    q10 q11 t31 t41 t51 t61 FI NK WF S0 EU EC EE EI ES ESE ENX ESN EOP EOD ECL EMI.
  destruct FI as (MI & WM & MU & ST & FA & FB & LB & FS & EW & BKs & BAs & RQ).
  pose proof (bv_unsigned_in_range 64 sp4w) as R4. unfold bv_modulus in R4.
  pose proof WF0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & WS0 & _).
  zstep. if_cases K; zify_cond K; [|try unfold wz in K; rewrite um1 in K; lia].
  zstep.
  eapply evt_cut; [apply HEL | intros ms' ->].
  rewrite ret_pc_even by (lia || reflexivity).
  assert (RDE : ov_read_bytes rsegs m (wa (bv_unsigned tp + ERRNO_TP_OFF + 0)) 4
                = Some (le4 (wz (nk_socket_errno kbs0)))).
  { unfold u32_at in EU. rewrite (bytes_at_read rsegs m _ _ 0 4 EU) by (try lia; rewrite length_le4; lia).
    rewrite skipn_O. apply f_equal. apply firstn_all2. rewrite length_le4. lia. }
  zstep. rewrite lw_u32 by lia.
  zstep. rewrite negw_wz by lia.
  zstep.
  assert (KS : k_sock (nk_kstate kbs0) <> 0) by (unfold nk_kstate; cbn [k_sock]; exact S0).
  pose proof (talk_sock (nk_kstate kbs0) KS) as (TRC & TAT & TAF & TOW).
  eapply (nt_epi m (- nk_socket_errno kbs0)) with (cs24 := [CB 16 j0; CB 8 j1]) (bj := bj);
    [exact MI | exact WM | exact MU | exact ST | exact FA | reflexivity | exact FB | exact LB | exact FS |].
  apply (post_early m kbs1 (- nk_socket_errno kbs0) NK WF EC EE EI ES).
  - rewrite TAF. unfold nk_kstate. cbn [k_send]. exact ESE.
  - exact ENX.
  - exact ESN.
  - rewrite EOP. exact OP0.
  - exact EMI.
  - rewrite EOD, ECL. reflexivity.
  - intros _. exact EOD.
  - intros H. contradiction.
  - rewrite TRC. unfold nk_kstate. cbn [k_sock]. reflexivity.
  - exact TAT.
  - exact TOW.
  - rewrite TAF. reflexivity.
  - exact BKs.
  - exact BAs.
Qed.

(* 0x16098, socket open: fuzz_send, its failure arm (errno, close), else the first fuzz_recv *)
Lemma nt_send : copy_attr_contract -> fuzz_send_contract -> fuzz_recv_contract -> fuzz_close_contract ->
  __errno_location_contract -> forall m kbs1 j0 j1 bj
    (ra1 t01 t11 t21 s01 a11 a21 a31 a41 a51 a61 a71 t31 t41 t51 t61 : word),
  finv m j0 j1 bj -> nlk_at m kbs1 -> nlk_wf kbs1 -> nk_socket_errno kbs0 = 0 ->
  nk_chunks kbs1 = nk_chunks kbs0 -> nk_end_errno kbs1 = nk_end_errno kbs0 -> nk_n_if kbs1 = nk_n_if kbs0 ->
  nk_socket_errno kbs1 = 0 -> nk_send_errno kbs1 = nk_send_errno kbs0 -> nk_next kbs1 = nk_next kbs0 ->
  nk_sent kbs1 = nk_sent kbs0 -> nk_open kbs1 = 1 -> nk_opened kbs1 = nk_opened kbs0 + 1 ->
  nk_closed kbs1 = nk_closed kbs0 -> nk_misuse kbs1 = nk_misuse kbs0 ->
  evt rsegs Q (MS (mkR ra1 sp4w gp tp t01 t11 t21 s01 a5 (wz NL_FD) a11 a21 a31 a41 a51 a61 a71
                       a4 a3 a2 a1 a0 s7 s8 s9 s10 s11 t31 t41 t51 t61)
                  F (Z_to_bv 64 0x16098) fc None m (seg_rom rsegs)).
Proof.
  intros HCA HSE HRE HCL HEL m kbs1 j0 j1 bj ra1 t01 t11 t21 s01 a11 a21 a31 a41 a51 a61 a71 t31 t41 t51 t61
    FI NK WF S0 EC EE EI ES ESE ENX ESN EOP EOD ECL EMI.
  pose proof (bv_unsigned_in_range 64 sp4w) as R4. unfold bv_modulus in R4.
  pose proof FG0 as FG1. pose proof EG0 as EG1. unfold apart_gnl, NK_SIZE in FG1, EG1.
  pose proof EF0 as EF1. pose proof WF0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WSE0 & _).
  pose proof FI as (MI & WM & MU & ST & FA & FB & LB & FS & EW & BKs & BAs & RQ).
  zstep. if_cases K; zify_cond K; [rewrite uwz in K by (unfold NL_FD; lia); unfold NL_FD in K; lia|].
  zstep. zstep. zstep. zstep. zstep.
  eapply (leaf_call FUZZ_SEND 48 _ _ _ HSE nt_se_post_ext Q QX).
  { cbv beta. unfold frame_apart_gnl, apart_frame.
    rewrite ?mkR_sp, ?mkR_a1, ?mkR_a2, ?mkR_errno.
    exists kbs1, req. split; [exact NK|].
    split; [unfold apart_gnl, NK_SIZE; lia|]. split; [exact WF|]. split; [exact EW|].
    split; [unfold link_mem.ERRNO_TP_OFF, __errno_location_c.ERRNO_TP_OFF in *; lia|]. split; [exact EG0|].
    split; [exact RQ|]. split; [exact RL0|]. split; [exact RL1|]. split; [exact RG0|].
    lia. }
  { exact MI. }
  { exact ST. }
  { lia. }
  { lia. }
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MUc WMc MIc STc PO.
  cbv beta in MUc, PO. rewrite ?mkR_errno in MUc, PO. rewrite ?mkR_a0, ?mkR_a1, ?mkR_a2 in PO.
  rewrite ret_pc_even by (lia || reflexivity).
  destruct (PO kbs1 req NK RQ RL0) as (kbs2 & NK2 & WF2 & ESO2 & EE2 & EOP2 & EOD2 & ECL2 & EMI2 & PF2 & PS2).
  rewrite uwz, EOP in EMI2 by (unfold NL_FD; lia).
  replace ((NL_FD =? NL_FD) && negb (1 =? 0)) with true in EMI2 by reflexivity.
  assert (OKS : okC ((bv_unsigned sp4w - 48, bv_unsigned sp4w)
                     :: [(A_G_NL + NK_SEND_ERRNO, A_G_NL + NK_N_SENT + 4);
                         (bv_unsigned tp + ERRNO_TP_OFF, bv_unsigned tp + ERRNO_TP_OFF + 4)])) by okc.
  pose proof (fkeep _ m m' j0 j1 bj FI OKS MUc WMc MIc STc) as FI2.
  destruct (gnl_keep _ m m' kbs1 kbs2 NK NK2 MUc WF ltac:(djn) ltac:(djn)) as (EC2 & ENX2 & EE2' & EI2).
  destruct (Z.eq_dec (nk_send_errno kbs0) 0) as [SE0|SE0].
  - (* sent: the first fuzz_recv *)
    rewrite <- ESE in SE0. destruct (PS2 SE0) as (R10 & ES2 & ESN2 & ENS2).
    rewrite getr10_mkR, getr12_mkR in R10. subst a0'.
    zstep. if_cases K2; zify_cond K2; [unfold NL_SENT_LEN in RL1; lia|].
    rewrite ESE in SE0.
    apply (nt_first HCA HCL HRE HEL m' kbs2 j0 j1 bj); [| exact S0 | exact SE0].
    destruct FI2 as (MI2 & WM2 & MU2 & ST2 & FA2 & FB2 & LB2 & FS2 & EW2 & BK2 & BA2 & RQ2).
    unfold oinv.
    refine (conj MI2 (conj WM2 (conj MU2 (conj ST2 (conj FA2 (conj FB2 (conj LB2 (conj FS2 (conj NK2
             (conj WF2 _)))))))))).
    split; [rewrite EC2; exact EC|]. split; [rewrite EE2; exact EE|]. split; [rewrite EI2; exact EI|].
    split; [rewrite ESO2; exact ES|]. split; [exact ES2|]. split; [rewrite EOP2; exact EOP|].
    split; [rewrite EOD2; exact EOD|]. split; [rewrite ECL2; exact ECL|]. split; [rewrite EMI2; exact EMI|].
    split; [rewrite ESN2, ESN; reflexivity|]. split; [rewrite ENS2, ESN2; reflexivity|].
    split; [rewrite ENX2, ENX; rewrite Z2Nat.id; [reflexivity|]; destruct WF0 as (_ & HN & _); lia|].
    split; [exact EW2|]. split; [exact BK2 | exact BA2].
  - (* send failed: errno, then close *)
    assert (SE1 : nk_send_errno kbs1 <> 0) by (rewrite ESE; exact SE0).
    destruct (PF2 SE1) as (R10 & ES2 & EU & ENS2 & ESN2).
    rewrite getr10_mkR in R10. subst a0'. rewrite ESE in EU.
    try change link_mem.ERRNO_TP_OFF with __errno_location_c.ERRNO_TP_OFF in EU.
    zstep. if_cases K2; zify_cond K2; [|try unfold wz in K2; rewrite um1 in K2; lia].
    zstep.
    eapply evt_cut; [apply HEL | intros ms' ->].
    rewrite ret_pc_even by (lia || reflexivity).
    assert (RDE : ov_read_bytes rsegs m' (wa (bv_unsigned tp + ERRNO_TP_OFF + 0)) 4
                  = Some (le4 (wz (nk_send_errno kbs0)))).
    { unfold u32_at in EU. rewrite (bytes_at_read rsegs m' _ _ 0 4 EU) by (try lia; rewrite length_le4; lia).
      rewrite skipn_O. apply f_equal. apply firstn_all2. rewrite length_le4. lia. }
    zstep. rewrite lw_u32 by lia.
    zstep. zstep.
    destruct FI2 as (MI2 & WM2 & MU2 & ST2 & FA2 & FB2 & LB2 & FS2 & EW2 & BK2 & BA2 & RQ2).
    eapply (leaf_call FUZZ_CLOSE 0 _ _ _ HCL nt_cl_post_ext Q QX).
    { exists kbs2. split; [exact NK2|]. split; [exact WF2|]. rewrite ECL2, ECL. lia. }
    { exact MI2. }
    { exact ST2. }
    { lia. }
    { lia. }
    intros ra'' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m'' MUd WMd MId STd PO3.
    cbv beta in MUd, PO3. rewrite ?mkR_a0 in PO3.
    destruct (PO3 kbs2 NK2) as (kbs3 & NK3 & WF3 & R103 & OP3 & OPD3 & CL3 & MS3).
    rewrite ret_pc_even by (lia || reflexivity).
    assert (OKC : okC [(bv_unsigned sp4w - 0, bv_unsigned sp4w); (A_G_NL + NK_OPEN, A_G_NL + NK_MISUSE + 4)])
      by okc.
    pose proof (fkeep _ m' m'' j0 j1 bj (conj MI2 (conj WM2 (conj MU2 (conj ST2 (conj FA2 (conj FB2 (conj LB2
                  (conj FS2 (conj EW2 (conj BK2 (conj BA2 RQ2))))))))))) OKC MUd WMd MId STd) as FI3.
    destruct FI3 as (MI3 & WM3 & MU3 & ST3 & FA3 & FB3 & LB3 & FS3 & EW3 & BK3 & BA3 & RQ3).
    destruct (gnl_keep _ m' m'' kbs2 kbs3 NK2 NK3 MUd WF2 ltac:(djn) ltac:(djn)) as (EC3 & ENX3 & EE3 & EI3).
    assert (ESN3 : nk_sent kbs3 = nk_sent kbs2) by exact (gnl_keep_sent _ m' m'' kbs2 kbs3 NK2 NK3 MUd WF2 ltac:(djn)).
    assert (ES3 : nk_socket_errno kbs3 = nk_socket_errno kbs2).
    { unfold nk_socket_errno, fld_u32.
      apply (fld_keep _ m' m'' kbs2 kbs3 NK_SOCKET_ERRNO 4 NK2 NK3 MUd);
        [djn | unfold NK_SOCKET_ERRNO; lia | lia | unfold NK_SOCKET_ERRNO, NK_SIZE; lia]. }
    assert (ESE3 : nk_send_errno kbs3 = nk_send_errno kbs2).
    { unfold nk_send_errno, fld_u32.
      apply (fld_keep _ m' m'' kbs2 kbs3 NK_SEND_ERRNO 4 NK2 NK3 MUd);
        [djn | unfold NK_SEND_ERRNO; lia | lia | unfold NK_SEND_ERRNO, NK_SIZE; lia]. }
    rewrite EOP2, EOP in MS3. rewrite uwz in MS3 by (unfold NL_FD; lia).
    replace ((NL_FD =? NL_FD) && negb (1 =? 0)) with true in MS3 by reflexivity.
    zstep. rewrite negw_wz by lia.
    zstep.
    assert (KS : k_sock (nk_kstate kbs0) = 0) by (unfold nk_kstate; cbn [k_sock]; exact S0).
    assert (KSE : k_send (nk_kstate kbs0) <> 0) by (unfold nk_kstate; cbn [k_send]; exact SE0).
    pose proof (talk_send (nk_kstate kbs0) KS KSE) as (TRC & TAT & TAF & TOW).
    eapply (nt_epi m'' (- nk_send_errno kbs0)) with (cs24 := [CB 16 j0; CB 8 j1]) (bj := bj);
      [exact MI3 | exact WM3 | exact MU3 | exact ST3 | exact FA3 | reflexivity | exact FB3 | exact LB3 | exact FS3 |].
    apply (post_early m'' kbs3 (- nk_send_errno kbs0) NK3 WF3).
    + rewrite EC3, EC2. exact EC.
    + rewrite EE3, EE2. exact EE.
    + rewrite EI3, EI2. exact EI.
    + rewrite ES3, ESO2. exact ES.
    + rewrite TAF, ESE3. exact ES2.
    + rewrite ENX3, ENX2. exact ENX.
    + rewrite ESN3, ESN2. exact ESN.
    + exact OP3.
    + rewrite MS3, EMI2. exact EMI.
    + rewrite OPD3, CL3, EOD2, ECL2, EOD, ECL. lia.
    + intros H. contradiction.
    + intros _. rewrite OPD3, EOD2. exact EOD.
    + rewrite TRC. unfold nk_kstate. cbn [k_send]. reflexivity.
    + exact TAT.
    + exact TOW.
    + rewrite TAF. reflexivity.
    + exact BK3.
    + exact BA3.
Qed.

(* 0x16008 .. 0x16090: the prologue (13 saved words, three stack probes, a 16512-byte frame) and the
   arguments of fuzz_socket. Stated for any memory m, so the store steps leave the section's facts
   about m0 alone. *)
Lemma nt_prologue : forall m, mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> nlk_at m kbs0 ->
  wr_at rsegs m (bv_unsigned tp + ERRNO_TP_OFF) 4 -> bytes_at rsegs m (bv_unsigned a0) req ->
  buf_arg m (bv_unsigned a2) (bv_unsigned a3) -> buf_arg m (bv_unsigned a4) (bv_unsigned a5) ->
  (forall m1 j0 j1 bj (x0 x1 x2 x6 : word), finvb m m1 j0 j1 bj -> nlk_at m1 kbs0 ->
     evt rsegs Q (MS (mkR ra sp4w gp tp t0 t1 t2 s0 a5 x0 x1 x2 a3 a4 a5 x6 a7 a4 a3 a2 a1 a0 s7 s8 s9 s10 s11
                          t3 t4 t5 t6)
                     F (Z_to_bv 64 0x16094) fc None m1 (seg_rom rsegs))) ->
  evt rsegs Q (MS R0 F (Z_to_bv 64 NL_TALK) fc None m (seg_rom rsegs)).
Proof.
  intros m MIm STm NKm EWm RQm BKm BAm K. unfold R0.
  pose proof (bv_unsigned_in_range 64 sp4w) as R4. unfold bv_modulus in R4.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS.
  pose proof (bv_unsigned_in_range 64 a3) as R3. pose proof (bv_unsigned_in_range 64 a5) as R5.
  unfold bv_modulus in R3, R5.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 16512, bv_unsigned sp)] m) as MUF.
  pose proof MIm as MI. destruct NKm as [NKA NKL].
  pose proof LO0 as LO1. pose proof SP0 as SP1. pose proof HSP4 as HS4.
  pose proof FG0 as FG1. pose proof EG0 as EG1. unfold apart_gnl, NK_SIZE in FG1, EG1, NKL.
  assert (KEEP : (bytes_at rsegs m (bv_unsigned a0) req /\ True) /\
                 bufst m m (bv_unsigned a2) (bv_unsigned a3) None /\
                 bufst m m (bv_unsigned a4) (bv_unsigned a5) None).
  { split; [split; [exact RQm | exact I]|].
    split; split; [exact BKm | intros _ s _ H; exact H | exact BAm | intros _ s _ H; exact H]. }
  clear RQm.
  destruct (stk_split rsegs m lo (bv_unsigned sp - 16512) (bv_unsigned sp) STm ltac:(lia)) as [STL SF].
  carve_frame 104%nat SF.
  destruct (stk_split rsegs m _ (bv_unsigned sp + -6120) _ SF ltac:(lia)) as [SF1 SH1]. carve_frame 8%nat SF1.
  destruct (stk_split rsegs m _ (bv_unsigned sp + -10216) _ SF1 ltac:(lia)) as [SF2 SH2]. carve_frame 8%nat SF2.
  destruct (stk_split rsegs m _ (bv_unsigned sp + -14312) _ SF2 ltac:(lia)) as [SF3 SH3]. carve_frame 8%nat SF3.
  zstep.
  do 13 zstep.
  do 3 (zstep; zstep; nsp; zstep).
  zstep; nsp. zstep; nsp.
  do 6 zstep.
  do 4 zstep.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  replace (Z_to_bv 64 (bv_unsigned sp + -16512)) with sp4w by (apply bv_eq; rewrite unsigned_lit by lia; lia).
  match goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) => replace p with 0x16094 by (unfold NL_TALK; lia) end.
  (* the frame as finv states it *)
  destruct (stk_split rsegs m1 _ (bv_unsigned sp - 16488) _ SF3 ltac:(lia)) as [S24 SB].
  pose proof (stk_cat m1 _ _ _ _ _ SB FR2 SH3 ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(lia) ltac:(lia)) as B1.
  pose proof (stk_cat m1 _ _ _ _ _ B1 FR1 SH2 ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(lia) ltac:(lia)) as B2.
  pose proof (stk_cat m1 _ _ _ _ _ B2 FR0 SH1 ltac:(cbn [cells_size csize Nat.add]; lia) ltac:(lia) ltac:(lia)) as B3.
  destruct (stk_u8arr m1 _ _ B3 ltac:(lia)) as (bj & FBj & LBj).
  destruct (stk_carve rsegs m1 _ _ 24 S24 ltac:(lia)) as [_ (junk24 & F24)].
  pose proof (rw_cells_split_CB rsegs m1 _ [] 24 junk24 [] [16; 8]%nat F24 eq_refl) as F24'.
  cbn [app mk_CB_cells] in F24'.
  destruct KEEP as ([RQ _] & BKs & BAs).
  assert (SUBF : forall x, outside W0 x -> outside [(bv_unsigned sp - 16512, bv_unsigned sp)] x).
  { intros x Hx. destruct (W0_out x Hx) as (H1 & _). cbn [outside]. split; [lia | exact I]. }
  apply (K m1 (firstn 16 junk24) (firstn 8 (skipn 16 junk24)) bj); [|exact (conj NKA NKL)].
  split; [exact MI|]. split; [exact WM|]. split; [exact (munch_weaken _ _ _ _ SUBF MUF)|].
  split; [replace (bv_unsigned sp4w) with (bv_unsigned sp - 16512) by lia; exact STL|].
  split; [replace (bv_unsigned sp4w) with (bv_unsigned sp - 16488 - Z.of_nat 24) by lia; exact F24'|].
  split; [replace (bv_unsigned sp4w + 24) with (bv_unsigned sp - 16488) by lia; exact FBj|].
  split; [lia|].
  split; [replace (bv_unsigned sp4w + 16408) with (bv_unsigned sp + -104) by lia; exact FR|].
  split; [exact EWm|].
  split; [eapply bufst_keep; [exact BKs | exact MUF | exact WM |]; intros Hb _;
          destruct (KF0 Hb) as [H1 _]; cbn [disjoint_from]; split; [lia | exact I]|].
  split; [eapply bufst_keep; [exact BAs | exact MUF | exact WM |]; intros Hb _;
          destruct (AF0 Hb) as [H1 _]; cbn [disjoint_from]; split; [lia | exact I]|].
  apply (bytes_at_transport rsegs [(bv_unsigned sp - 16512, bv_unsigned sp)] m m1); [exact RQ | exact MUF |].
  rewrite RL0. cbn [disjoint_from]. split; [lia | exact I].
Qed.

(* the whole walk: prologue, fuzz_socket, then its two arms *)
Lemma nt_entry : copy_attr_contract -> fuzz_socket_contract -> fuzz_send_contract -> fuzz_recv_contract ->
  fuzz_close_contract -> __errno_location_contract ->
  evt rsegs Q (MS R0 F (Z_to_bv 64 NL_TALK) fc None m0 (seg_rom rsegs)).
Proof.
  intros HCA HSO HSE HRE HCL HEL.
  apply (nt_prologue m0 MI0 ST0 NK0 EW0 RQ0 BK0 BA0).
  intros m1 j0 j1 bj x0 x1 x2 x6 FI NK1.
  pose proof (bv_unsigned_in_range 64 sp4w) as R4. unfold bv_modulus in R4.
  pose proof FG0 as FG1. pose proof EG0 as EG1. unfold apart_gnl, NK_SIZE in FG1, EG1.
  pose proof HSP4 as HS4. pose proof LO0 as LO1.
  assert (MI : mem_inv rsegs m1) by (destruct FI as (MI & _); exact MI).
  zstep.
  eapply (leaf_call FUZZ_SOCKET 32 _ _ _ HSO nt_so_post_ext Q QX).
  { cbv beta. unfold frame_apart_gnl, apart_frame. rewrite ?mkR_sp, ?mkR_errno.
    exists kbs0. split; [exact NK1|]. split; [unfold apart_gnl, NK_SIZE; lia|]. split; [exact WF0|].
    split; [destruct FI as (_ & _ & _ & _ & _ & _ & _ & _ & EW & _); exact EW|].
    split; [pose proof EF0 as EF1; unfold link_mem.ERRNO_TP_OFF, __errno_location_c.ERRNO_TP_OFF in *; lia|].
    split; [exact EG0 | exact OC0]. }
  { exact MI. }
  { destruct FI as (_ & _ & _ & ST & _). exact ST. }
  { lia. }
  { lia. }
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MUc WMc MIc STc PO.
  cbv beta in MUc, PO. rewrite ?mkR_errno in MUc, PO.
  rewrite ret_pc_even by (lia || reflexivity).
  destruct (PO kbs0 NK1) as (kbs1 & NK2 & WF1 & ESE1 & EE1 & ECL1 & PF & PS).
  assert (OKS : okC ((bv_unsigned sp4w - 32, bv_unsigned sp4w)
                     :: [(A_G_NL + NK_SOCKET_ERRNO, A_G_NL + NK_MISUSE + 4);
                         (bv_unsigned tp + ERRNO_TP_OFF, bv_unsigned tp + ERRNO_TP_OFF + 4)])) by okc.
  pose proof (fkeep _ m1 m2 _ _ bj FI OKS MUc WMc MIc STc) as FI2.
  destruct (gnl_keep _ m1 m2 kbs0 kbs1 NK1 NK2 MUc WF0 ltac:(djn) ltac:(djn)) as (EC1 & ENX1 & EE1' & EI1).
  assert (ESN1 : nk_sent kbs1 = nk_sent kbs0) by exact (gnl_keep_sent _ m1 m2 kbs0 kbs1 NK1 NK2 MUc WF0 ltac:(djn)).
  destruct (Z.eq_dec (nk_socket_errno kbs0) 0) as [S0|S0].
  - destruct (PS S0) as (R10 & ES1 & EOP1 & EOD1 & EMI1). rewrite getr10_mkR in R10. subst a0'.
    rewrite OP0 in EMI1.
    apply (nt_send HCA HSE HRE HCL HEL m2 kbs1 _ _ bj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             FI2 NK2 WF1 S0 EC1 EE1 EI1 ES1 ESE1 ENX1 ESN1 EOP1 EOD1 ECL1).
    rewrite EMI1. reflexivity.
  - destruct (PF S0) as (R10 & ES1 & EU & EOP1 & EOD1 & EMI1). rewrite getr10_mkR in R10. subst a0'.
    exact (nt_sfail HEL m2 kbs1 _ _ bj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             FI2 NK2 WF1 S0 EU EC1 EE1 EI1 ES1 ESE1 ENX1 ESN1 EOP1 EOD1 ECL1 EMI1).
Qed.

End Body.

Theorem nl_talk_holds : copy_attr_contract -> fuzz_socket_contract -> fuzz_send_contract -> fuzz_recv_contract ->
  fuzz_close_contract -> __errno_location_contract -> nl_talk_contract.
Proof.
  intros HCA HSO HSE HRE HCL HEL. rewrite nl_talk_contract_eq. apply leaf_intro.
  - intros r1 r2 m E H. unfold nt_pre, arg, errno_at, apart_frame, frame_apart_gnl, spZ in *.
    repeat rewrite <- E. exact H.
  - intros r1 r2 m E. unfold nt_wr, arg, errno_at. repeat rewrite E. reflexivity.
  - intros r1 r2 m q1 q2 m' E1 E2 H. unfold nt_post, arg in *. intros kbs req NK RQ RL.
    repeat rewrite <- E1 in RQ, RL. specialize (H kbs req NK RQ RL). cbv zeta in H |- *.
    repeat rewrite <- E1. repeat rewrite <- E2. exact H.
  - intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
      regs PRE MI ST LO SP.
    destruct PRE as (kbs & req & NK & FG & WF & OP & EW & EF & EG & RQ & RL & RL1 & BK & BA & ERQ & EK & EA & KA
                     & OC & CC & RG & RF & KF & AF).
    unfold regs in *. unfold frame_apart_gnl, apart_frame in *.
    rewrite ?mkR_sp, ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_a5, ?mkR_errno in *.
    pose proof ST as ST'. destruct ST' as [L0 _].
    refine (nt_entry ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo (Z_to_bv 64 (bv_unsigned sp - 16512)) _ (conj L0 LO) SP kbs req NK FG WF OP EW EF EG RQ RL
              RL1 BK BA ERQ EK EA KA OC CC RG RF KF AF MI ST HCA HSO HSE HRE HCL HEL).
    rewrite unsigned_lit; [reflexivity | lia].
Qed.

Print Assumptions nl_talk_holds.
