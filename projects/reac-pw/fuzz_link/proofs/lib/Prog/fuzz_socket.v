(* fuzz_socket (netlink.h:72-87), PLAIN build: the walk of its contract (lib/Prog/fuzz_socket_c.v) on the plain
   image, 0x134a0-0x13527 (34 instructions, a 32-byte frame), and the three instructions of ___errno_location
   (0x16e04: `mv a0, tp; addi a0, a0, -0xa4; ret`) it calls. Each instruction is fetched from the image and
   decoded by computation (lib/Lib/Step.v `step`).
   The six fields socket_errno .. misuse (g_nl + 0x4020c .. 0x40224) are cut out of `nlk_at` as cells, the walk
   reads and writes them there, and they are joined back at the end (lib/Prog/kn_nlk.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf kn_nlk fuzz_socket_c.
Local Open Scope Z_scope.

(* the Post, from the six cells the walk leaves *)
Lemma socket_post : forall m m' bs (x0 x1 x2 x3 x4 x5 : word) (R' : bvmap 5 word) (ea : Z),
  nlk_at m bs -> nlk_wf bs -> nk_opened bs + 1 < 2 ^ 31 ->
  bytes_at rsegs m' A_G_NL (firstn (Z.to_nat NK_SOCKET_ERRNO) bs) ->
  rw_cells rsegs m' (A_G_NL + NK_SOCKET_ERRNO) [C4 x0; C4 x1; C4 x2; C4 x3; C4 x4; C4 x5] ->
  bytes_at rsegs m' (A_G_NL + NK_SOCKET_ERRNO + Z.of_nat (cells_size [C4 x0; C4 x1; C4 x2; C4 x3; C4 x4; C4 x5]))
    (skipn (Z.to_nat NK_SOCKET_ERRNO + cells_size [C4 x0; C4 x1; C4 x2; C4 x3; C4 x4; C4 x5]) bs) ->
  wr_at rsegs m' A_G_NL NK_SIZE ->
  bv_unsigned x0 mod 2 ^ 32 = 0 ->
  bv_unsigned x1 mod 2 ^ 32 = nk_send_errno bs ->
  bv_unsigned x4 mod 2 ^ 32 = nk_closed bs ->
  (nk_socket_errno bs <> 0 ->
     getr R' 10 = wz (-1) /\ u32_at m' ea (nk_socket_errno bs) /\
     bv_unsigned x2 mod 2 ^ 32 = nk_open bs /\ bv_unsigned x3 mod 2 ^ 32 = nk_opened bs /\
     bv_unsigned x5 mod 2 ^ 32 = nk_misuse bs) ->
  (nk_socket_errno bs = 0 ->
     getr R' 10 = wz NL_FD /\ bv_unsigned x2 mod 2 ^ 32 = 1 /\ bv_unsigned x3 mod 2 ^ 32 = nk_opened bs + 1 /\
     bv_unsigned x5 mod 2 ^ 32 = (if nk_open bs =? 0 then nk_misuse bs else 1)) ->
  forall bs0, nlk_at m bs0 -> exists bs', nlk_at m' bs' /\ nlk_wf bs'
     /\ nk_send_errno bs' = nk_send_errno bs0 /\ nk_end_errno bs' = nk_end_errno bs0
     /\ nk_closed bs' = nk_closed bs0
     /\ (nk_socket_errno bs0 <> 0 ->
           getr R' 10 = wz (-1) /\ nk_socket_errno bs' = 0
           /\ u32_at m' ea (nk_socket_errno bs0)
           /\ nk_open bs' = nk_open bs0 /\ nk_opened bs' = nk_opened bs0
           /\ nk_misuse bs' = nk_misuse bs0)
     /\ (nk_socket_errno bs0 = 0 ->
           getr R' 10 = wz NL_FD /\ nk_socket_errno bs' = 0
           /\ nk_open bs' = 1 /\ nk_opened bs' = nk_opened bs0 + 1
           /\ nk_misuse bs' = (if nk_open bs0 =? 0 then nk_misuse bs0 else 1)).
Proof.
  intros m m' bs x0 x1 x2 x3 x4 x5 R' ea NK WF ON B1 C B3 W V0 V1 V4 VE VO bs0 NK0.
  rewrite (nlk_at_unique m bs0 bs NK0 NK). clear bs0 NK0.
  pose proof NK as [_ HL].
  destruct (nlk_join_rd m' bs NK_SOCKET_ERRNO [C4 x0; C4 x1; C4 x2; C4 x3; C4 x4; C4 x5] HL
              ltac:(kn_side) ltac:(kn_side) ltac:(kn_side) B1 C B3 W) as (bs' & NK' & HL' & OUT & IN).
  exists bs'. split; [exact NK'|].
  cbn [cells_size csize cells_bytes cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in OUT, IN.
  pose proof WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
  unfold nk_n_chunks, nk_next, nk_n_sent, nk_n_if, nk_open, nk_opened, nk_closed, nk_misuse,
    nk_end_errno, nk_socket_errno, nk_send_errno, fld_u32, fld_u64, NL_FD in *.
  nk_nums.
  rewrite (IN 262668 4), (IN 262672 4), (IN 262676 4), (IN 262680 4), (IN 262684 4), (IN 262688 4) by lia.
  rdn_cells.
  rewrite V0, V1, V4.
  assert (O : forall a n, 0 <= a -> 0 <= n -> a + n <= 262668 \/ 262692 <= a -> rdn bs' a n = rdn bs a n)
    by (intros a n Ha Hn H; apply (OUT a n Ha Hn); lia).
  rewrite (O 262664 4) by lia.
  assert (Q : 0 <= bv_unsigned x2 mod 2 ^ 32 <= 1 /\ 0 <= bv_unsigned x3 mod 2 ^ 32 < 2 ^ 31 /\
              0 <= bv_unsigned x5 mod 2 ^ 32 <= 1).
  { destruct (Z.eq_dec (rdn bs 262668 4) 0) as [Z0|Z0].
    - destruct (VO Z0) as (_ & -> & -> & ->). split; [lia|]. split; [lia|].
      destruct (rdn bs 262676 4 =? 0); lia.
    - destruct (VE Z0) as (_ & _ & -> & -> & ->). lia. }
  split.
  - apply (nlk_wf_same_queues bs bs' WF).
    all: unfold nk_n_chunks, nk_next, nk_n_sent, nk_n_if, nk_open, nk_opened, nk_closed, nk_misuse,
      nk_end_errno, nk_socket_errno, nk_send_errno, fld_u32, fld_u64; nk_nums.
    all: rewrite ?(IN 262668 4), ?(IN 262672 4), ?(IN 262676 4), ?(IN 262680 4), ?(IN 262684 4), ?(IN 262688 4)
           by lia; rdn_cells; rewrite ?V0, ?V1, ?V4.
    + apply O; lia.
    + apply O; lia.
    + apply O; lia.
    + intros i Hi. apply O; lia.
    + intros i Hi. apply O; lia.
    + rewrite (O 262660 4) by lia. lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + rewrite (O 262664 4) by lia. lia.
    + lia.
    + lia.
  - split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
    + intros Z0. destruct (VE Z0) as (R10 & EU & -> & -> & ->).
      exact (conj R10 (conj eq_refl (conj EU (conj eq_refl (conj eq_refl eq_refl))))).
    + intros Z0. destruct (VO Z0) as (R10 & -> & -> & ->).
      exact (conj R10 (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))).
Qed.

(* the end of every path: the epilogue's frame release, the return, and the Post *)
Ltac sock_end sp tp a0 :=
  lazymatch goal with FR : rw_cells _ _ (bv_unsigned sp + -32) _, ST : stk _ _ _ (bv_unsigned sp + -32) |- _ =>
    release_frame FR ST (bv_unsigned sp) end;
  apply evt_done; eexists _, _; split; [reflexivity|];
  split; [solve_rp|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [eassumption|];
  lazymatch goal with
  | NK : nlk_at ?m0 ?bs, WF : nlk_wf ?bs, PRE : bytes_at _ _ 203648 ?pre, POST : bytes_at _ _ 466340 ?post,
    CE : rw_cells _ _ 466316 _, WRA : wr_at _ _ 203648 271992,
    Epre : ?pre = _, Epost : ?post = _ |- _ =>
      subst pre post;
      eapply (socket_post m0 _ bs _ _ _ _ _ _ _ (bv_unsigned tp + -164)); [exact NK | exact WF | eassumption
        | exact PRE | exact CE | exact POST | exact WRA | .. ]
  end;
  unfold nk_open, nk_opened, nk_closed, nk_misuse, nk_send_errno, nk_socket_errno, fld_u32, NL_FD in *; nk_nums;
  try (intros; split; [reflexivity|]);
  try (split; [eassumption|]);
  try (unfold wz; rewrite ?unsigned_lit by lia; rewrite ?Z.mod_small by lia;
       repeat match goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y) end; cbn [andb negb];
       try lia; repeat split; try lia; assumption).

Theorem fuzz_socket_holds : fuzz_socket_contract.
Proof.
  unfold fuzz_socket_contract. apply leaf_intro.
  - intros r1 r2 m E H. cbv beta in H |- *.
    unfold frame_apart_gnl, apart_frame, apart_gnl, errno_at, spZ in *. rewrite <- ?E. exact H.
  - intros r1 r2 m E. cbv beta. unfold errno_at. rewrite <- ?E. reflexivity.
  - intros r1 r2 m q1 q2 m' E E' H. cbv beta in H |- *. unfold errno_at in *. rewrite <- ?E, <- ?E'. exact H.
  - unfold leaf_walk, FUZZ_SOCKET.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros (bs & NK & FA & WF & WE & EF & EG & ON) MI ST LO SP.
    unfold frame_apart_gnl, apart_frame, apart_gnl, A_G_NL, NK_SIZE in FA, EF, EG.
    change (spZ (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6))
      with (bv_unsigned sp) in FA, EF.
    change (errno_at (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6))
      with (bv_unsigned tp + -164) in WE, EF, EG.
    pose proof NK as [_ HL].
    pose proof WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
    assert (SP0 : 0 <= NK_SOCKET_ERRNO) by (nk_nums; lia).
    assert (SP1 : NK_SOCKET_ERRNO + 4 * Z.of_nat 6 <= NK_SIZE) by (nk_nums; lia).
    destruct (nlk_split_u32 m bs NK_SOCKET_ERRNO 6 NK SP0 SP1) as (PRE & CE & POST & WRA). clear SP0 SP1.
    change (u32_cells bs NK_SOCKET_ERRNO 6) with
      [C4 (wz (nk_socket_errno bs)); C4 (wz (nk_send_errno bs)); C4 (wz (nk_open bs)); C4 (wz (nk_opened bs));
       C4 (wz (nk_closed bs)); C4 (wz (nk_misuse bs))] in CE.
    change (A_G_NL + NK_SOCKET_ERRNO) with 466316 in CE.
    change (A_G_NL + NK_SOCKET_ERRNO + 4 * Z.of_nat 6) with 466340 in POST.
    change A_G_NL with 203648 in PRE, WRA. change NK_SIZE with 271992 in WRA.
    remember (firstn (Z.to_nat NK_SOCKET_ERRNO) bs) as pre eqn:Epre.
    remember (skipn (Z.to_nat NK_SOCKET_ERRNO + 4 * 6) bs) as post eqn:Epost.
    assert (LPre : Z.of_nat (length pre) = 262668) by (subst pre; rewrite length_firstn; nk_nums; lia).
    assert (LPo : Z.of_nat (length post) = 9300) by (subst post; rewrite length_skipn; nk_nums; lia).
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (466316, 466340);
                            (bv_unsigned tp + -164, bv_unsigned tp + -164 + 4)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (zr_word tp) as Rtp. unfold inr64 in Rtp.
    pose proof WE as [WE0 [WE1 _]].
    carve_frame 32%nat ST.
    zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep.
    zstep. rewrite sx32_wz by lia.
    zstep. if_cases K.
    + (* socket_errno = 0 *)
      zify_cond K. try (unfold wz in K; rewrite unsigned_lit in K by lia).
      zstep. rewrite sx32_wz by lia. zstep. if_cases K2.
      * (* open = 0 *)
        zify_cond K2. try (unfold wz in K2; rewrite unsigned_lit in K2 by lia).
        zstep. zstep. zstep. rewrite sx32_wz by lia. zstep. zstep. zstep. zstep. zstep.
        zstep. zstep. zstep. zstep. zstep.
        sock_end sp tp a0.
      * (* open <> 0: misuse *)
        zify_cond K2. try (unfold wz in K2; rewrite unsigned_lit in K2 by lia).
        zstep. zstep. zstep. zstep.
        zstep. zstep. zstep. rewrite sx32_wz by lia. zstep. zstep. zstep. zstep. zstep.
        zstep. zstep. zstep. zstep. zstep.
        sock_end sp tp a0.
    + (* socket_errno <> 0 *)
      zify_cond K. try (unfold wz in K; rewrite unsigned_lit in K by lia).
      zstep. zstep. zstep. zstep.
      match goal with WE : wr_at _ ?mm (bv_unsigned tp + -164) 4 |- _ =>
        pose proof (wr_at_store_ok rsegs mm (bv_unsigned tp + -164) 4 0 4 WE ltac:(lia) ltac:(lia)) as HSe end.
      rewrite Z.add_0_r in HSe.
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a ?bs) _) =>
        let E := addr_expr a in
        change (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs);
        assert (ERB : bytes_at rsegs (write_to_mem mm (wa E) bs) E bs)
          by (apply bytes_at_write_same; rewrite ?length_le4; lia)
      end.
      store_done.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      sock_end sp tp a0.
Qed.
