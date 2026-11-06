(* fuzz_close (netlink.h:139-146), PLAIN build: the walk of its contract (lib/Prog/fuzz_close_c.v) on the plain
   image, 0x13778-0x137bf (18 instructions, no frame). Each instruction is fetched from the image and decoded by
   computation (lib/Lib/Step.v `step`).
   The four fields open, opened, closed, misuse (g_nl + 0x40214 .. 0x40224) are cut out of `nlk_at` as cells,
   the walk reads and writes them there, and they are joined back at the end (lib/Prog/kn_nlk.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf kn_nlk fuzz_close_c.
Local Open Scope Z_scope.

(* the Post, from the four cells the walk leaves *)
Lemma close_post : forall m m' bs (x0 x1 x2 x3 : word) (a0v : Z) (R' : bvmap 5 word),
  nlk_at m bs -> nlk_wf bs ->
  bytes_at rsegs m' A_G_NL (firstn (Z.to_nat NK_OPEN) bs) ->
  rw_cells rsegs m' (A_G_NL + NK_OPEN) [C4 x0; C4 x1; C4 x2; C4 x3] ->
  bytes_at rsegs m' (A_G_NL + NK_OPEN + Z.of_nat (cells_size [C4 x0; C4 x1; C4 x2; C4 x3]))
    (skipn (Z.to_nat NK_OPEN + cells_size [C4 x0; C4 x1; C4 x2; C4 x3]) bs) ->
  wr_at rsegs m' A_G_NL NK_SIZE ->
  bv_unsigned x0 mod 2 ^ 32 = 0 ->
  bv_unsigned x1 mod 2 ^ 32 = nk_opened bs ->
  bv_unsigned x2 mod 2 ^ 32 = nk_closed bs + 1 ->
  bv_unsigned x3 mod 2 ^ 32 = (if (a0v =? NL_FD) && negb (nk_open bs =? 0) then nk_misuse bs else 1) ->
  nk_closed bs + 1 < 2 ^ 31 ->
  getr R' 10 = wz 0 ->
  forall bs0, nlk_at m bs0 -> exists bs', nlk_at m' bs'
    /\ nlk_wf bs' /\ getr R' 10 = wz 0
    /\ nk_open bs' = 0 /\ nk_opened bs' = nk_opened bs0
    /\ nk_closed bs' = nk_closed bs0 + 1
    /\ nk_misuse bs' = (if (a0v =? NL_FD) && negb (nk_open bs0 =? 0) then nk_misuse bs0 else 1).
Proof.
  intros m m' bs x0 x1 x2 x3 a0v R' NK WF B1 C B3 W V0 V1 V2 V3 CL R10 bs0 NK0.
  rewrite (nlk_at_unique m bs0 bs NK0 NK). clear bs0 NK0.
  pose proof NK as [_ HL].
  assert (J : nlk_at m' (upd_bytes bs (Z.to_nat NK_OPEN) (cells_bytes [C4 x0; C4 x1; C4 x2; C4 x3])) /\
              length (upd_bytes bs (Z.to_nat NK_OPEN) (cells_bytes [C4 x0; C4 x1; C4 x2; C4 x3])) = length bs)
    by (apply nlk_join; [exact HL | kn_side | kn_side | exact B1 | exact C | exact B3 | exact W]).
  destruct J as [NK' LU].
  exists (upd_bytes bs (Z.to_nat NK_OPEN) (cells_bytes [C4 x0; C4 x1; C4 x2; C4 x3])).
  split; [exact NK'|].
  assert (OUT : forall a n, 0 <= a -> 0 <= n -> a + n <= NK_OPEN \/ NK_OPEN + 16 <= a ->
    rdn (upd_bytes bs (Z.to_nat NK_OPEN) (cells_bytes [C4 x0; C4 x1; C4 x2; C4 x3])) a n = rdn bs a n).
  { intros a n Ha Hn H. apply rdn_join_out; kn_side. }
  assert (IN : forall a n, NK_OPEN <= a -> a + n <= NK_OPEN + 16 -> 0 <= n ->
    rdn (upd_bytes bs (Z.to_nat NK_OPEN) (cells_bytes [C4 x0; C4 x1; C4 x2; C4 x3])) a n =
    rdn (le4 x0 ++ le4 x1 ++ le4 x2 ++ le4 x3 ++ []) (a - NK_OPEN) n).
  { intros a n H1 H2 Hn. rewrite rdn_join_in by kn_side. reflexivity. }
  unfold nlk_wf, nk_n_chunks, nk_next, nk_n_sent, nk_n_if, nk_open, nk_opened, nk_closed, nk_misuse,
    nk_end_errno, nk_socket_errno, nk_send_errno, fld_u32, fld_u64 in *.
  rewrite (IN NK_OPEN 4), (IN NK_OPENED 4), (IN NK_CLOSED 4), (IN NK_MISUSE 4) by (nk_nums; lia).
  rewrite (OUT NK_N_CHUNKS 4), (OUT NK_NEXT 4), (OUT NK_N_SENT 4), (OUT NK_N_IF 4), (OUT NK_END_ERRNO 4),
    (OUT NK_SOCKET_ERRNO 4), (OUT NK_SEND_ERRNO 4) by (nk_nums; lia).
  nk_nums. rdn_cells.
  rewrite V0, V1, V2, V3.
  destruct WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
  split; [|split; [exact R10|split; [reflexivity|split; [reflexivity|split; [reflexivity|reflexivity]]]]].
  refine (conj W1 (conj W2 (conj W3 (conj W4 (conj _ (conj _ (conj _ (conj _ (conj W9 (conj W10 (conj W11 (conj _ _)))))))))))).
  - lia.
  - lia.
  - lia.
  - match goal with |- context [if ?c then _ else _] => destruct c end; lia.
  - intros i Hi. rewrite (OUT (262144 + 8 * i) 8) by lia. apply W12. lia.
  - intros i Hi. rewrite (OUT (270888 + 8 * i) 8) by lia. apply W13. lia.
Qed.

(* the end of every path: the frame-free return and the Post *)
Ltac close_end a0 :=
  apply evt_done; eexists _, _; split; [reflexivity|];
  split; [solve_rp|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [eassumption|];
  lazymatch goal with
  | NK : nlk_at ?m0 ?bs, WF : nlk_wf ?bs, PRE : bytes_at _ _ 203648 ?pre, POST : bytes_at _ _ 466340 ?post,
    CE : rw_cells _ _ 466324 _, WRA : wr_at _ _ 203648 271992,
    Epre : ?pre = _, Epost : ?post = _ |- _ =>
      subst pre post;
      eapply (close_post m0 _ bs _ _ _ _ (bv_unsigned a0)); [exact NK | exact WF | exact PRE | exact CE | exact POST
        | exact WRA | .. ]
  end;
  unfold nk_open, nk_opened, nk_closed, nk_misuse, fld_u32, NL_FD in *; nk_nums;
  try (unfold wz; rewrite ?unsigned_lit by lia; rewrite ?Z.mod_small by lia;
       repeat match goal with |- context [?x =? ?y] => destruct (Z.eqb_spec x y) end; cbn [andb negb]; lia);
  try reflexivity.

Theorem fuzz_close_holds : fuzz_close_contract.
Proof.
  unfold fuzz_close_contract. apply leaf_intro.
  - intros r1 r2 m _ H. exact H.
  - intros r1 r2 m _. reflexivity.
  - intros r1 r2 m q1 q2 m' E E' H. cbv beta in H |- *. unfold arg in *. rewrite <- ?E, <- ?E'. exact H.
  - unfold leaf_walk, FUZZ_CLOSE.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros (bs & NK & WF & CL) MI ST LO SP.
    pose proof NK as [_ HL].
    pose proof WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
    assert (SP0 : 0 <= NK_OPEN) by (nk_nums; lia).
    assert (SP1 : NK_OPEN + 4 * Z.of_nat 4 <= NK_SIZE) by (nk_nums; lia).
    destruct (nlk_split_u32 m bs NK_OPEN 4 NK SP0 SP1) as (PRE & CE & POST & WRA). clear SP0 SP1.
    change (u32_cells bs NK_OPEN 4) with
      [C4 (wz (nk_open bs)); C4 (wz (nk_opened bs)); C4 (wz (nk_closed bs)); C4 (wz (nk_misuse bs))] in CE.
    change (A_G_NL + NK_OPEN) with 466324 in CE.
    change (A_G_NL + NK_OPEN + 4 * Z.of_nat 4) with 466340 in POST.
    change A_G_NL with 203648 in PRE, WRA. change NK_SIZE with 271992 in WRA.
    remember (firstn (Z.to_nat NK_OPEN) bs) as pre eqn:Epre.
    remember (skipn (Z.to_nat NK_OPEN + 4 * 4) bs) as post eqn:Epost.
    assert (LPre : Z.of_nat (length pre) = 262676) by (subst pre; rewrite length_firstn; nk_nums; lia).
    assert (LPo : Z.of_nat (length post) = 9300) by (subst post; rewrite length_skipn; nk_nums; lia).
    pose proof (munch_refl [(bv_unsigned sp - 0, bv_unsigned sp); (466324, 466340)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases K.
    + (* a0 <> 7: misuse *)
      zify_cond K.
      zstep. zstep. zstep. zstep. zstep. rewrite sx32_wz by lia. zstep. zstep. zstep. zstep. zstep.
      close_end a0.
    + zify_cond K.
      zstep. rewrite sx32_wz by lia. zstep. if_cases K2.
      * (* open <> 0: no misuse *)
        zify_cond K2. try (unfold wz in K2; rewrite unsigned_lit in K2 by lia).
        zstep. zstep. zstep. rewrite sx32_wz by lia. zstep. zstep. zstep. zstep. zstep.
        close_end a0.
      * (* open = 0: misuse *)
        zify_cond K2. try (unfold wz in K2; rewrite unsigned_lit in K2 by lia).
        zstep. zstep. zstep. zstep. zstep. rewrite sx32_wz by lia. zstep. zstep. zstep. zstep. zstep.
        close_end a0.
Qed.
