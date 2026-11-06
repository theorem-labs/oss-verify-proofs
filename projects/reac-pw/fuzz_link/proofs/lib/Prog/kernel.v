(* kernel (fuzz_link.c:256-282), PLAIN build: the walk of its contract (lib/Prog/kernel_c.v) on the plain image,
   0x14190-0x14faf (3616 bytes, msg_build and the nl_* writers inlined, a 4336-byte frame). Each instruction is
   fetched from the image and decoded by computation (lib/Lib/Step.v `step`).

   The walk is cut into lemmas at the join blocks of the control-flow graph:
     kn_k0.v   the fixed context (kfix, kf_ok), the state predicates, the epilogue (k_exit);
     kn_k1.v   the queueing of a chunk into g_nl, the empty-cursor path, the raw-input path, the end of a
               message path (k_queue, k_c78, k_c88, k_c64, k_raw, k_d44, k_d5c, k_d88);
     kn_k2.v   the chunk loop (k_body, k_latch, k_loop, k_first);
     kn_k3.v   the entry: frame, saved registers, the flags / errno / end-errno bytes, the writes into g_nl,
               the chunk count and the spill slots (k_entry, k_f8);
     kn_kmsg.v the message loop of one chunk (k_msgloop), kn_k07.v kinds 0 and 7 of msg_build (k_kind07).
   This file builds the context from the contract's Pre and proves the Post from the facts the walk returns:
   g_nl's queue holds the chunks kernel queued, nothing of g_nl from `open` on moves, the interface table and
   its names are outside every write, and the cursor advanced inside the input. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf mk_call kn_nlk kn_kfr kn_k0
  kn_k1 kn_k2 kn_k3 kn_kmsg kernel_c nl_error_c attr_text_c nl_error attr_text.
Local Open Scope Z_scope.

(* ==========================================================================
   1. g_nl from `open` on is the entry's
   ========================================================================== *)

Lemma slice_skip : forall b1 b2 a n, skipn (Z.to_nat 262676) b1 = skipn (Z.to_nat 262676) b2 -> 262676 <= a ->
  slice b1 a n = slice b2 a n.
Proof.
  intros b1 b2 a n E H. unfold slice.
  replace (Z.to_nat a) with (Z.to_nat (a - 262676) + Z.to_nat 262676)%nat by lia.
  rewrite <- !skipn_skipn, E. reflexivity.
Qed.

Lemma rdn_skip : forall b1 b2 a n, skipn (Z.to_nat 262676) b1 = skipn (Z.to_nat 262676) b2 -> 262676 <= a ->
  rdn b1 a n = rdn b2 a n.
Proof. intros. unfold rdn. f_equal. apply slice_skip; assumption. Qed.

Lemma kgnl_post : forall c kbs j, kgnl c kbs j -> nlk_wf (kf_kbs0 c) -> 0 <= j <= 3 ->
  nlk_wf kbs /\ nk_next kbs = 0 /\ 0 <= nk_n_chunks kbs <= 3
  /\ In (nk_end_errno kbs) nl_errno_tab
  /\ (nk_socket_errno kbs = 0 \/ In (nk_socket_errno kbs) nl_errno_tab)
  /\ (nk_send_errno kbs = 0 \/ In (nk_send_errno kbs) nl_errno_tab)
  /\ nk_open kbs = nk_open (kf_kbs0 c) /\ nk_opened kbs = nk_opened (kf_kbs0 c)
  /\ nk_closed kbs = nk_closed (kf_kbs0 c) /\ nk_misuse kbs = nk_misuse (kf_kbs0 c)
  /\ nk_n_sent kbs = nk_n_sent (kf_kbs0 c) /\ nk_sent kbs = nk_sent (kf_kbs0 c)
  /\ nk_n_if kbs = nk_n_if (kf_kbs0 c).
Proof.
  intros c kbs j (GL & GS & GJ & GN & GE & GSO & GSE & GC) WF JR.
  assert (R : forall a n, 262676 <= a -> rdn kbs a n = rdn (kf_kbs0 c) a n)
    by (intros a n Ha; apply rdn_skip; assumption).
  assert (EO : nk_open kbs = nk_open (kf_kbs0 c)) by (unfold nk_open, fld_u32, NK_OPEN; apply R; lia).
  assert (EOd : nk_opened kbs = nk_opened (kf_kbs0 c)) by (unfold nk_opened, fld_u32, NK_OPENED; apply R; lia).
  assert (EC : nk_closed kbs = nk_closed (kf_kbs0 c)) by (unfold nk_closed, fld_u32, NK_CLOSED; apply R; lia).
  assert (EM : nk_misuse kbs = nk_misuse (kf_kbs0 c)) by (unfold nk_misuse, fld_u32, NK_MISUSE; apply R; lia).
  assert (ES : nk_n_sent kbs = nk_n_sent (kf_kbs0 c)) by (unfold nk_n_sent, fld_u32, NK_N_SENT; apply R; lia).
  assert (EI : nk_n_if kbs = nk_n_if (kf_kbs0 c)) by (unfold nk_n_if, fld_u32, NK_N_IF; apply R; lia).
  assert (ESENT : nk_sent kbs = nk_sent (kf_kbs0 c)).
  { unfold nk_sent. rewrite ES. apply map_ext. intros i. unfold nk_sent_one, fld_u64, NK_SENT, NK_SENT_LEN.
    rewrite (R (270888 + 8 * Z.of_nat i)) by lia. apply slice_skip; [exact GS | unfold NL_SENT_LEN; lia]. }
  pose proof WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
  assert (EE : 0 <= rdn kbs 262664 4 < 2 ^ 31) by (pose proof (nl_errno_tab_range _ GE); lia).
  assert (ESO : 0 <= rdn kbs 262668 4 < 2 ^ 31)
    by (destruct GSO as [->|GSO]; [lia | pose proof (nl_errno_tab_range _ GSO); lia]).
  assert (ESE : 0 <= rdn kbs 262672 4 < 2 ^ 31)
    by (destruct GSE as [->|GSE]; [lia | pose proof (nl_errno_tab_range _ GSE); lia]).
  unfold nk_next, nk_n_chunks, nk_end_errno, nk_socket_errno, nk_send_errno, fld_u32, NK_NEXT, NK_N_CHUNKS,
    NK_END_ERRNO, NK_SOCKET_ERRNO, NK_SEND_ERRNO.
  rewrite GJ, GN.
  split.
  - unfold nlk_wf. rewrite EO, EOd, EC, EM, ES, EI.
    unfold nk_next, nk_n_chunks, nk_end_errno, nk_socket_errno, nk_send_errno, fld_u32, NK_NEXT, NK_N_CHUNKS,
      NK_END_ERRNO, NK_SOCKET_ERRNO, NK_SEND_ERRNO.
    rewrite GJ, GN.
    refine (conj _ (conj _ (conj W3 (conj W4 (conj W5 (conj W6 (conj W7 (conj W8 (conj EE (conj ESO (conj ESE
      (conj _ _)))))))))))).
    + unfold NL_CHUNKS. lia.
    + lia.
    + intros i Hi. unfold fld_u64, NK_CHUNK_LEN, NL_CHUNK_MAX. apply GC. lia.
    + intros i Hi. unfold fld_u64, NK_SENT_LEN. rewrite R by lia. apply W13. exact Hi.
  - split; [reflexivity|]. split; [lia|]. split; [exact GE|]. split; [exact GSO|]. split; [exact GSE|].
    exact (conj EO (conj EOd (conj EC (conj EM (conj ES (conj ESENT EI)))))).
Qed.

(* ==========================================================================
   2. The interface table, outside every write
   ========================================================================== *)

Lemma iftab_keep : forall c m m' kbs' tab,
  (kSP c <= 203648 \/ 475640 <= kSP c + -4416) -> (kCUR c + 16 <= 203648 \/ 475640 <= kCUR c) ->
  munch (kW c) (kf_m0 c) m' -> iftab_at (kf_m0 c) (kf_kbs0 c) tab ->
  nk_n_if kbs' = nk_n_if (kf_kbs0 c) ->
  (forall i nm ix p, nth_error tab i = Some (nm, ix) ->
     u64_at (kf_m0 c) (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> kapart c p (Z.of_nat (length nm) + 1)) ->
  m = kf_m0 c ->
  iftab_at m' kbs' tab.
Proof.
  intros c m m' kbs' tab FG CG MU (TN & TL & TE) EN AP _.
  split; [rewrite EN; exact TN|]. split; [exact TL|].
  intros i nm ix Hi. destruct (TE i nm ix Hi) as (IXR & p & U & P0 & (CB & CN) & U32).
  pose proof (proj1 (nth_error_Some tab i) ltac:(rewrite Hi; discriminate)) as Hlt.
  pose proof (AP i nm ix p Hi U) as (A1 & A2 & A3 & A4).
  split; [exact IXR|]. exists p.
  unfold kW in MU. unfold A_G_NL, NK_IF_NAME, NK_IF_INDEX in *.
  split; [|split; [exact P0|split; [split; [|exact CN]|]]].
  - unfold u64_at in *. eapply bytes_at_transport; [exact U | exact MU | ].
    rewrite length_le8. cbn [disjoint_from]. lia.
  - eapply bytes_at_transport; [exact CB | exact MU | ].
    rewrite length_app. cbn [length disjoint_from]. lia.
  - unfold u32_at in *. eapply bytes_at_transport; [exact U32 | exact MU | ].
    rewrite length_le4. cbn [disjoint_from]. lia.
Qed.

(* ==========================================================================
   3. The cursor's two words are the memory's
   ========================================================================== *)

Lemma le8_inj : forall w1 w2 : word, le8 w1 = le8 w2 -> w1 = w2.
Proof.
  intros w1 w2 E. apply bv_eq.
  pose proof (bv_unsigned_in_range 64 w1) as R1. pose proof (bv_unsigned_in_range 64 w2) as R2.
  unfold bv_modulus in R1, R2. change (2 ^ Z.of_N 64) with (2 ^ 64) in R1, R2.
  assert (B : bytes_le_to_Z (le8 w1) = bytes_le_to_Z (le8 w2)) by (rewrite E; reflexivity).
  unfold le8, word_to_le_bytes in B. rewrite !bytes_le_to_Z_to_le_bytes in B by lia.
  change (8 * Z.of_nat 8) with 64 in B. rewrite !Z.mod_small in B by lia. exact B.
Qed.

Lemma cursor_unique : forall m A (w1 w2 w3 w4 : word),
  rw_cells rsegs m A [C8 w1; C8 w2] -> rw_cells rsegs m A [C8 w3; C8 w4] -> w3 = w1 /\ w4 = w2.
Proof.
  intros m A w1 w2 w3 w4 [[_ B1] _] [[_ B2] _]. cbn [cells_bytes cbytes] in B1, B2. rewrite app_nil_r in B1, B2.
  assert (E : le8 w3 ++ le8 w4 = le8 w1 ++ le8 w2).
  { apply (bytes_at_unique m A); [exact B2 | exact B1 | rewrite !length_app, !length_le8; reflexivity]. }
  pose proof (f_equal (firstn 8) E) as F1. pose proof (f_equal (skipn 8) E) as F2.
  rewrite !firstn_app, !length_le8 in F1. rewrite !skipn_app, !length_le8 in F2.
  cbn [Nat.sub firstn skipn] in F1, F2.
  rewrite !firstn_all2 in F1 by (rewrite length_le8; lia). rewrite !app_nil_r in F1.
  rewrite !skipn_all2 in F2 by (rewrite length_le8; lia). cbn [app] in F2.
  split; apply le8_inj; assumption.
Qed.

(* ==========================================================================
   4. The contract
   ========================================================================== *)

Lemma regs_preserved_kR0 : forall c R R',
  getr R 2 = kf_sp c -> getr R 3 = kf_gp c -> getr R 4 = kf_tp c -> getr R 8 = kf_s0 c -> getr R 9 = kf_s1 c ->
  getr R 18 = kf_s2 c -> getr R 19 = kf_s3 c -> getr R 20 = kf_s4 c -> getr R 21 = kf_s5 c ->
  getr R 22 = kf_s6 c -> getr R 23 = kf_s7 c -> getr R 24 = kf_s8 c -> getr R 25 = kf_s9 c ->
  getr R 26 = kf_s10 c -> getr R 27 = kf_s11 c ->
  regs_preserved (kR0 c) R' -> regs_preserved R R'.
Proof.
  intros c R R' E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 RP r Hr. rewrite (RP r Hr).
  unfold callee_saved in Hr.
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [symmetry; assumption..|].
  assert (r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
    as Hc by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; symmetry; assumption.
Qed.

Section Top.
Hypothesis KMS : k_msgloop_stmt.

Theorem kernel_holds_ms : kernel_contract.
Proof.
  unfold kernel_contract. apply leaf_intro.
  - intros r1 r2 m E H. cbv beta in H |- *.
    unfold kernel_apart, frame_apart_gnl, apart_frame, apart_gnl, arg, spZ in *. rewrite <- ?E. exact H.
  - intros r1 r2 m E. cbv beta. unfold arg. rewrite <- ?E. reflexivity.
  - intros r1 r2 m q1 q2 m' E E' H. cbv beta in H |- *. unfold arg in *. rewrite <- ?E. exact H.
  - unfold leaf_walk, KERNEL.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta.
    intros (kbs & wp & wn & NK & FA & WF & CU & AG & AF & (d & IN & LD) & KA & TA & TT & (la & sl & LA & SL & LSL)
            & LAF & CLA & IFT) MI ST LO SP.
    rewrite ?mkR_a0 in *. rewrite ?mkR_sp in *.
    unfold kernel_apart, frame_apart_gnl, apart_frame, apart_gnl in *. rewrite ?mkR_a0, ?mkR_sp in *.
    lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
    pose (c := KFix ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a0 wp wn d kbs la QQ).
    assert (HC : kf_ok c).
    { pose proof ST as (ST0 & ST1 & _).
      constructor; unfold kapart, c; cbn [kf_ra kf_sp kf_gp kf_tp kf_s0 kf_s1 kf_s2 kf_s3 kf_s4 kf_s5 kf_s6 kf_s7 kf_s8 kf_s9
        kf_s10 kf_s11 kf_F kf_fc kf_m0 kf_lo kf_a0 kf_wp kf_wn kf_d kf_kbs0 kf_la0 kf_Q];
        unfold A_G_NL, NK_SIZE, A_LONG_ALIAS, LONG_ALIAS_SIZE, A_TEXTS, TEXTS_N in *.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - exact IN.
      - exact LD.
      - lia.
      - exact NK.
      - exact WF.
      - exact CU.
      - exact LA.
      - exists sl. split; [exact SL | exact LSL].
      - lia.
      - intros i Hi. destruct (TT i ltac:(unfold TEXTS_N; lia)) as (p & s & slack & U & P0 & B & NZ & SLK & LS & KP).
        unfold kernel_apart, apart_frame, apart_gnl in KP. rewrite ?mkR_a0, ?mkR_sp in KP.
        exists p, s, slack. unfold NL_CHUNK_MAX, A_G_NL, NK_SIZE, A_LONG_ALIAS, LONG_ALIAS_SIZE in *.
        refine (conj U (conj P0 (conj B (conj NZ (conj SLK (conj LS _)))))). lia.
      - exact MI.
      - exact ST.
      - unfold QQ. apply leaf_q_ext. intros q1 q2 m' _ H. exact H.
      - intros R' m' kbs' j adv la' RP MU WM MI' ST' NK' GI JR ADV CUR LA'.
        unfold QQ. exists R', m'. split; [reflexivity|].
        split.
        { eapply (regs_preserved_kR0 c); [reflexivity..|]. exact RP. }
        split.
        { intros x Hx. apply MU. unfold kW. cbn [kf_sp kf_a0 c] in *. cbn [outside] in *.
          unfold A_G_NL, NK_CHUNK, NK_OPEN, A_LONG_ALIAS, LONG_ALIAS_SIZE, arg in Hx. rewrite ?mkR_a0 in Hx. lia. }
        split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
        cbv beta. intros kbs0 NK0.
        assert (E0 : kbs0 = kbs) by (apply (nlk_at_unique m); assumption). subst kbs0.
        pose proof GI as [GL' _].
        destruct (kgnl_post c kbs' j GI WF JR) as (WF' & NX & NC & EE & ESO & ESE & EO & EOd & EC & EM & ES & ESENT & EI).
        change (kf_kbs0 c) with kbs in *.
        exists kbs'.
        split; [split; [exact NK' | exact GL']|].
        refine (conj WF' (conj NX (conj NC (conj EE (conj ESO (conj ESE (conj EO (conj EOd (conj EC (conj EM
          (conj ES (conj ESENT (conj EI (conj _ (conj _ _))))))))))))))).
        + intros tab IT. eapply (iftab_keep c m m' kbs' tab); [ | | exact MU | exact IT | exact EI | | reflexivity];
            [unfold c; cbn [kf_sp kf_a0]; lia | unfold c; cbn [kf_sp kf_a0]; lia | ].
          intros i nm ix p Hi U. pose proof (IFT tab i nm ix p IT Hi U) as KP.
          unfold kapart, c; cbn [kf_sp kf_a0].
          unfold A_G_NL, NK_SIZE, A_LONG_ALIAS, LONG_ALIAS_SIZE in *. lia.
        + intros wp' wn' CU'. rewrite ?mkR_a0 in CU' |- *.
          destruct (cursor_unique m _ wp wn wp' wn' CU CU') as [-> ->].
          exists adv. split; [exact ADV | exact CUR].
        + exists la'. exact LA'. }
    exact (k_entry c HC KMS t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
Qed.

End Top.

(* kernel's contract over the contracts of its two own callees, nl_error (kinds 1 and 2 of msg_build) and
   attr_text (kinds 0 and 7); memset and memcpy enter through their walks *)
Theorem kernel_holds_h : nl_error_contract -> attr_text_contract -> kernel_contract.
Proof. intros NLE ATC. exact (kernel_holds_ms (k_msgloop NLE ATC)). Qed.

(* ... and over their walks (lib/Prog/nl_error.v, lib/Prog/attr_text.v) *)
Theorem kernel_holds : kernel_contract.
Proof. exact (kernel_holds_h nl_error_holds attr_text_holds). Qed.
