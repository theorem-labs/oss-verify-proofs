(* model_read (fuzz_link.c:386-401), PLAIN build: the walk of its contract (lib/Prog/model_read_c.v)
   on the plain image, 0x14ffc, 232 bytes (link/ct/dis/plain/model_read.s).

   Shape: a 96-byte frame; kind[0] = 0 and alias[0] = 0 when the buffer is there (0x15038, 0x15044);
   -EINVAL for a NULL or empty name (0x1504c, 0x15054); index_of (0x1505c), -ENODEV for 0
   (0x15060); then a 32-byte RTM_GETLINK in the frame at sp+8: memset of sp+20..sp+40 (0x15074)
   and four word stores (0x15088-0x15094); talk (0x150b4) answers.
   The walk first reaches 0x15048 by any of the nine store patterns (the cut `P48`), then goes on
   from one state. index_of and talk are `leaf` contracts, called through lib/Prog/mk_call.v
   `leaf_call`; memset is the libc contract, instantiated closed at the end. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import
  link_mem mk_leaf mk_call hp_md_kit model_read_c index_of_c talk_c memset_c memset.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
Local Open Scope Z_scope.

(* ---- pure facts ---- *)

Lemma buf_arg_munch : forall W m m' a c, buf_arg m a c -> munch W m m' -> wmono rsegs m m' ->
  (a <> 0 -> 1 <= c -> disjoint_from W a c) -> buf_arg m' a c.
Proof.
  intros W m m' a c B Hm Hw Hd Ha Hc. destruct (B Ha Hc) as [j HJ]. exists j.
  apply (rw_cells_transport rsegs W m m' a _ HJ Hm Hw). cbn [cells_size csize].
  rewrite Nat.add_0_r, Z2Nat.id by lia. exact (Hd Ha Hc).
Qed.

(* what a refused read leaves: the model block and the two buffers as the stores left them *)
Lemma refused_tail : forall m1 mF sp0 pm ka kc aa ac mbs kbs reqs,
  munch [(sp0 - 240, sp0)] m1 mF -> wmono rsegs m1 mF ->
  model_at m1 pm mbs -> model_wf mbs -> (pm + MD_SIZE <= sp0 - 240 \/ sp0 <= pm) ->
  (ka <> 0 -> kc <> 0 -> bytes_at rsegs m1 ka [zb 0]) -> (ka <> 0 -> ka + kc <= sp0 - 240 \/ sp0 <= ka) ->
  buf_arg m1 ka kc ->
  (aa <> 0 -> ac <> 0 -> bytes_at rsegs m1 aa [zb 0]) -> (aa <> 0 -> aa + ac <= sp0 - 240 \/ sp0 <= aa) ->
  buf_arg m1 aa ac ->
  reqs = md_reqs mbs -> 0 <= kc -> 0 <= ac ->
  (exists mbs', model_at mF pm mbs' /\ model_wf mbs'
      /\ md_next mbs' = Z.of_nat (k_next (md_kstate mbs kbs))
      /\ md_socket_errno mbs' = k_sock (md_kstate mbs kbs)
      /\ md_send_errno mbs' = k_send (md_kstate mbs kbs)
      /\ md_reqs mbs' = reqs /\ md_n_req mbs' = Z.of_nat (length reqs)
      /\ md_n_mark mbs' = md_n_mark mbs /\ md_marks mbs' = md_marks mbs)
  /\ (ka <> 0 -> 1 <= kc -> cstr_at mF ka [])
  /\ (aa <> 0 -> 1 <= ac -> cstr_at mF aa [])
  /\ (ka <> 0 -> 1 <= kc -> exists junk, rw_cells rsegs mF ka [CB (Z.to_nat kc) junk])
  /\ (aa <> 0 -> 1 <= ac -> exists junk, rw_cells rsegs mF aa [CB (Z.to_nat ac) junk]).
Proof.
  intros m1 mF sp0 pm ka kc aa ac mbs kbs reqs MUf WMf MA1 MWF AFM K0 AFK BK A0 AFA BA -> Hkc Hac.
  pose proof MWF as (Hr & Hn & _).
  split; [|split; [|split; [|split]]].
  - exists mbs. split; [apply (model_at_munch _ m1 mF _ mbs MA1 MUf WMf); apply clear1; lia|].
    split; [exact MWF|]. cbn [md_kstate k_next k_sock k_send].
    split; [rewrite Z2Nat.id by lia; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [unfold md_reqs; rewrite length_map, length_seq, Z2Nat.id by lia; reflexivity|].
    split; reflexivity.
  - intros Ha Hc. apply cstr_nil_of_byte. apply (bytes_at_munch _ m1 mF _ _ (K0 Ha ltac:(lia)) MUf).
    cbn [length]. apply clear1. pose proof (AFK Ha). lia.
  - intros Ha Hc. apply cstr_nil_of_byte. apply (bytes_at_munch _ m1 mF _ _ (A0 Ha ltac:(lia)) MUf).
    cbn [length]. apply clear1. pose proof (AFA Ha). lia.
  - intros Ha Hc. destruct (BK Ha Hc) as [j HJ]. exists j.
    apply (rw_cells_transport rsegs _ m1 mF _ _ HJ MUf WMf). cbn [disjoint_from cells_size csize].
    pose proof (AFK Ha). split; [lia | exact I].
  - intros Ha Hc. destruct (BA Ha Hc) as [j HJ]. exists j.
    apply (rw_cells_transport rsegs _ m1 mF _ _ HJ MUf WMf). cbn [disjoint_from cells_size csize].
    pose proof (AFA Ha). split; [lia | exact I].
Qed.

Lemma clear3 : forall l1 h1 l2 h2 l3 h3 v n,
  (v + n <= l1 \/ h1 <= v) -> (v + n <= l2 \/ h2 <= v \/ h2 <= l2) -> (v + n <= l3 \/ h3 <= v \/ h3 <= l3) ->
  clear_of [(l1, h1); (l2, h2); (l3, h3)] v n.
Proof. intros. intros x Hx. cbn [outside]. repeat split; lia. Qed.

(* the 32 request bytes the walk builds at sp+8 *)
Lemma req_read_at : forall m A j v1 v2 v3 z1 v4 z2 idx,
  rw_cells rsegs m A [CB 8 j; C4 v1; C4 v2; C4 v3] ->
  rw_cells rsegs m (A + 20) [CB 8 z1; C4 v4; CB 8 z2] ->
  0 <= idx < 2 ^ 31 ->
  bv_unsigned v1 = 32 -> bv_unsigned v2 = 65554 -> bv_unsigned v3 = 1 -> bv_unsigned v4 = idx ->
  z1 = zeros 8 -> z2 = zeros 8 ->
  bytes_at rsegs m (A + 8) (req_read idx).
Proof.
  intros m A j v1 v2 v3 z1 v4 z2 idx [[W1 B1] _] [[_ B2] _] Hi E1 E2 E3 E4 -> ->.
  cbn [cells_wf cell_wf] in W1. destruct W1 as [Lj _].
  cbn [cells_bytes cbytes] in B1, B2. unfold le4 in B1, B2.
  rewrite E1, E2, E3 in B1. rewrite E4 in B2. rewrite !app_nil_r in B1, B2.
  apply bytes_at_app in B1. destruct B1 as [_ B1]. rewrite Lj in B1.
  assert (ER : req_read idx =
    (Z_to_le_bytes 4 32 ++ Z_to_le_bytes 2 RTM_GETLINK ++ Z_to_le_bytes 2 F_REQUEST ++ Z_to_le_bytes 4 1
     ++ zeros 4 ++ zeros 4) ++ (Z_to_le_bytes 4 idx ++ zeros 8)).
  { unfold req_read, req_head. rewrite !app_assoc. reflexivity. }
  assert (EP : Z_to_le_bytes 4 32 ++ Z_to_le_bytes 2 RTM_GETLINK ++ Z_to_le_bytes 2 F_REQUEST ++ Z_to_le_bytes 4 1
               ++ zeros 4 ++ zeros 4
             = (Z_to_le_bytes 4 32 ++ Z_to_le_bytes 4 65554 ++ Z_to_le_bytes 4 1) ++ zeros 8)
    by (apply bytes_eq_bz; vm_compute; reflexivity).
  rewrite ER, EP, <- app_assoc. apply bytes_at_app. split.
  - replace (A + 8) with (A + Z.of_nat 8) by lia. exact B1.
  - replace (A + 8 + Z.of_nat (length (Z_to_le_bytes 4 32 ++ Z_to_le_bytes 4 65554 ++ Z_to_le_bytes 4 1)))
      with (A + 20) by (cbn; lia).
    exact B2.
Qed.

Lemma buf_after_store : forall m A c b j, 1 <= c ->
  rw_cells rsegs m A [C1 b; CB (Z.to_nat c - 1) j] -> exists junk, rw_cells rsegs m A [CB (Z.to_nat c) junk].
Proof.
  intros m A c b j Hc H. destruct (rw_cells_C1_forget _ _ _ _ _ H) as [jj HJ]. exists jj.
  replace (Z.to_nat c) with (S (Z.to_nat c - 1)) by lia. exact HJ.
Qed.

Lemma buf_head_rest : forall m A n j, (1 <= n)%nat -> rw_cells rsegs m A [CB n j] ->
  rw_cells rsegs m A [CB 1 (firstn 1 j)] /\ rw_cells rsegs m (A + 1) [CB (n - 1) (skipn 1 j)].
Proof.
  intros m A n j Hn H. apply (rw_cells_cb_cut _ _ _ _ 1%nat) in H; [|lia].
  change [CB 1 (firstn 1 j); CB (n - 1) (skipn 1 j)]
    with ([CB 1 (firstn 1 j)] ++ [CB (n - 1) (skipn 1 j)]) in H.
  apply rw_cells_app in H. destruct H as [H1 H2]. split; [exact H1|]. exact H2.
Qed.

Lemma buf_join_after : forall m A c b j, 1 <= c ->
  rw_cells rsegs m A [C1 b] -> rw_cells rsegs m (A + 1) [CB (Z.to_nat c - 1) j] ->
  exists junk, rw_cells rsegs m A [CB (Z.to_nat c) junk].
Proof.
  intros m A c b j Hc H1 H2.
  assert (H : rw_cells rsegs m A ([C1 b] ++ [CB (Z.to_nat c - 1) j])) by (apply rw_cells_join; [exact H1 | exact H2]).
  exact (buf_after_store m A c b j Hc H).
Qed.

(* sb zero, 0(w) into a buffer whose head cell is CB 1 *)
Ltac store0 w :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with H : rw_cells rsegs mm (bv_unsigned w) (CB 1 ?j1 :: _) |- _ =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mm w 1 = true)
        by (apply (rw_cells_store_ok_at rsegs mm (bv_unsigned w) _ 0 (CB 1 j1) 1 w H);
            [reflexivity | reflexivity | symmetry; apply wa_of_var; lia]);
      zstep;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m2 w ?bs) _) =>
        replace (write_to_mem m2 w bs) with (write_to_mem m2 (wa (bv_unsigned w + Z.of_nat 0)) (le1 (zxb (zb 0))))
          by (f_equal; first [apply wa_of_var; lia | symmetry; apply wa_of_var; lia | reflexivity]) end;
      clear HS; mem_after_store
    end
  end.

Ltac p48fin :=
  apply evt_done; eexists; eexists; eexists; eexists;
  split; [reflexivity|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [first [left; reflexivity | right; repeat split; lia]|];
  split; [first [left; reflexivity | right; repeat split; lia]|];
  split; [intros ? ?; first [lia | eapply rw_cells_head_byte; eassumption]|];
  split; [intros ? ?; first [lia | eapply rw_cells_head_byte; eassumption]|];
  split; intros ? ?; first [lia | eapply buf_join_after; [lia | eassumption | eassumption]].

Section Walk.
Hypothesis HIDX : index_of_contract_P.
Hypothesis HTALK : talk_contract.
Hypothesis HMS : memset_contract.

Theorem model_read_holds : model_read_contract.
Proof.
  unfold model_read_contract. apply leaf_intro.
  - intros r1 r2 m E H. unfold arg, apart_frame, frame_apart_gnl, spZ in *. rewrite <- !E. exact H.
  - intros r1 r2 m E. unfold arg. rewrite !E. reflexivity.
  - intros r1 r2 m q1 q2 m' E1 E2 H. unfold arg in *. rewrite <- !E1, <- !E2. exact H.
  - unfold leaf_walk, MODEL_READ.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros HPRE MI ST LO SP.
    destruct HPRE as (mbs & kbs & tab & nm & MA & MWF & NK & FAG & NWF & IT & SA & BK & BA & AGM & AFM
                      & AFN & AFK & AFA & AFT & ANK & AK & AA & AKA).
    unfold frame_apart_gnl, apart_frame in *.
    rewrite ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_a5, ?mkR_sp in *.
    remember (if bv_unsigned a2 =? 0 then 0 else bv_unsigned a3) as kn eqn:Ekn.
    remember (if bv_unsigned a4 =? 0 then 0 else bv_unsigned a5) as an eqn:Ean.
    lazymatch goal with |- evt _ ?Q _ => assert (HQ : q_ext Q) end.
    { apply leaf_q_ext. intros q1 q2 m' E H. cbv beta in *. rewrite <- !E. exact H. }
    pose proof (zr_word sp) as Rsp. pose proof (zr_word a0) as Ra0. pose proof (zr_word a1) as Ra1.
    pose proof (zr_word a2) as Ra2. pose proof (zr_word a3) as Ra3. pose proof (zr_word a4) as Ra4.
    pose proof (zr_word a5) as Ra5. unfold inr64 in *.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + MD_SIZE);
                            (bv_unsigned a2, bv_unsigned a2 + kn); (bv_unsigned a4, bv_unsigned a4 + an)] m) as MU.
    assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
    eapply evt_cut with (P := fun ms => exists m1 jf kz az,
      ms = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 a5 a4 a0 a1 a2 a3 a4 a5 a6 a7
                   a3 a2 a0 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15048) fc None m1 (seg_rom rsegs)
      /\ rw_cells rsegs m1 (bv_unsigned sp + -96) [CB 40 jf; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ munch [(bv_unsigned sp + -96, bv_unsigned sp); (bv_unsigned a2, bv_unsigned a2 + kz);
                (bv_unsigned a4, bv_unsigned a4 + az)] m m1
      /\ munch [(bv_unsigned sp - 240, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + MD_SIZE);
                (bv_unsigned a2, bv_unsigned a2 + kn); (bv_unsigned a4, bv_unsigned a4 + an)] m m1
      /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp + -96)
      /\ (kz = 0 \/ (kz = 1 /\ bv_unsigned a2 <> 0 /\ bv_unsigned a3 <> 0))
      /\ (az = 0 \/ (az = 1 /\ bv_unsigned a4 <> 0 /\ bv_unsigned a5 <> 0))
      /\ (bv_unsigned a2 <> 0 -> bv_unsigned a3 <> 0 -> bytes_at rsegs m1 (bv_unsigned a2) [zb 0])
      /\ (bv_unsigned a4 <> 0 -> bv_unsigned a5 <> 0 -> bytes_at rsegs m1 (bv_unsigned a4) [zb 0])
      /\ buf_arg m1 (bv_unsigned a2) (bv_unsigned a3) /\ buf_arg m1 (bv_unsigned a4) (bv_unsigned a5)).
    { (* the nine store patterns *)
      destruct (Z.eq_dec (bv_unsigned a2) 0) as [KA0|KA0].
      + destruct (Z.eq_dec (bv_unsigned a4) 0) as [AA0|AA0].
      ++ pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (bv_unsigned a2, bv_unsigned a2 + 0);
                                (bv_unsigned a4, bv_unsigned a4 + 0)] m) as MUc.
        carve_frame 96%nat ST. do 13 zstep.
        zstep. if_true.
        zstep. if_true.
        p48fin.
      ++ destruct (Z.eq_dec (bv_unsigned a5) 0) as [AC0|AC0].
        ** pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (bv_unsigned a2, bv_unsigned a2 + 0);
                                (bv_unsigned a4, bv_unsigned a4 + 0)] m) as MUc.
        carve_frame 96%nat ST. do 13 zstep.
        zstep. if_true.
        zstep. if_false. zstep. if_true.
        p48fin.
        ** assert (Han : an = bv_unsigned a5) by (rewrite Ean; destruct (Z.eqb_spec (bv_unsigned a4) 0); lia).
        specialize (AFA AA0). destruct (BA AA0 ltac:(lia)) as (ja & BAc).
        apply buf_head_rest in BAc; [|lia]. destruct BAc as [BAch BAcr].
        pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (bv_unsigned a2, bv_unsigned a2 + 0);
                                (bv_unsigned a4, bv_unsigned a4 + 1)] m) as MUc.
        carve_frame 96%nat ST. do 13 zstep.
        zstep. if_true.
        zstep. if_false. zstep. if_false. store0 a4.
        p48fin.
      + destruct (Z.eq_dec (bv_unsigned a3) 0) as [KC0|KC0].
        * destruct (Z.eq_dec (bv_unsigned a4) 0) as [AA0|AA0].
      ++ pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (bv_unsigned a2, bv_unsigned a2 + 0);
                                (bv_unsigned a4, bv_unsigned a4 + 0)] m) as MUc.
        carve_frame 96%nat ST. do 13 zstep.
        zstep. if_false. zstep. if_true.
        zstep. if_true.
        p48fin.
      ++ destruct (Z.eq_dec (bv_unsigned a5) 0) as [AC0|AC0].
        ** pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (bv_unsigned a2, bv_unsigned a2 + 0);
                                (bv_unsigned a4, bv_unsigned a4 + 0)] m) as MUc.
        carve_frame 96%nat ST. do 13 zstep.
        zstep. if_false. zstep. if_true.
        zstep. if_false. zstep. if_true.
        p48fin.
        ** assert (Han : an = bv_unsigned a5) by (rewrite Ean; destruct (Z.eqb_spec (bv_unsigned a4) 0); lia).
        specialize (AFA AA0). destruct (BA AA0 ltac:(lia)) as (ja & BAc).
        apply buf_head_rest in BAc; [|lia]. destruct BAc as [BAch BAcr].
        pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (bv_unsigned a2, bv_unsigned a2 + 0);
                                (bv_unsigned a4, bv_unsigned a4 + 1)] m) as MUc.
        carve_frame 96%nat ST. do 13 zstep.
        zstep. if_false. zstep. if_true.
        zstep. if_false. zstep. if_false. store0 a4.
        p48fin.
        * destruct (Z.eq_dec (bv_unsigned a4) 0) as [AA0|AA0].
      ++ assert (Hkn : kn = bv_unsigned a3) by (rewrite Ekn; destruct (Z.eqb_spec (bv_unsigned a2) 0); lia).
        specialize (AFK KA0). destruct (BK KA0 ltac:(lia)) as (jk & BKc).
        apply buf_head_rest in BKc; [|lia]. destruct BKc as [BKch BKcr].
        pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (bv_unsigned a2, bv_unsigned a2 + 1);
                                (bv_unsigned a4, bv_unsigned a4 + 0)] m) as MUc.
        carve_frame 96%nat ST. do 13 zstep.
        zstep. if_false. zstep. if_false. store0 a2.
        zstep. if_true.
        p48fin.
      ++ destruct (Z.eq_dec (bv_unsigned a5) 0) as [AC0|AC0].
        ** assert (Hkn : kn = bv_unsigned a3) by (rewrite Ekn; destruct (Z.eqb_spec (bv_unsigned a2) 0); lia).
        specialize (AFK KA0). destruct (BK KA0 ltac:(lia)) as (jk & BKc).
        apply buf_head_rest in BKc; [|lia]. destruct BKc as [BKch BKcr].
        pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (bv_unsigned a2, bv_unsigned a2 + 1);
                                (bv_unsigned a4, bv_unsigned a4 + 0)] m) as MUc.
        carve_frame 96%nat ST. do 13 zstep.
        zstep. if_false. zstep. if_false. store0 a2.
        zstep. if_false. zstep. if_true.
        p48fin.
        ** assert (Hkn : kn = bv_unsigned a3) by (rewrite Ekn; destruct (Z.eqb_spec (bv_unsigned a2) 0); lia).
        specialize (AFK KA0). destruct (BK KA0 ltac:(lia)) as (jk & BKc).
        apply buf_head_rest in BKc; [|lia]. destruct BKc as [BKch BKcr].
        assert (Han : an = bv_unsigned a5) by (rewrite Ean; destruct (Z.eqb_spec (bv_unsigned a4) 0); lia).
        specialize (AFA AA0). destruct (BA AA0 ltac:(lia)) as (ja & BAc).
        apply buf_head_rest in BAc; [|lia]. destruct BAc as [BAch BAcr].
        pose proof (AKA KA0 AA0 ltac:(lia) ltac:(lia)) as AKA'. unfold apart in AKA'.
        pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp); (bv_unsigned a2, bv_unsigned a2 + 1);
                                (bv_unsigned a4, bv_unsigned a4 + 1)] m) as MUc.
        carve_frame 96%nat ST. do 13 zstep.
        zstep. if_false. zstep. if_false. store0 a2.
        zstep. if_false. zstep. if_false. store0 a4.
        p48fin. }
    clear MU WM MI ST.
    intros ms (m1 & jf & kz & az & -> & FR & MUw & MU & WM & MI & ST & KZ & AZ & K0B & A0B & BK1 & BA1).
    (* ---- the views at m1 ---- *)
    assert (KZr : kz = 0 \/ (kz = 1 /\ bv_unsigned a2 <> 0 /\ 1 <= bv_unsigned a3)) by lia.
    assert (AZr : az = 0 \/ (az = 1 /\ bv_unsigned a4 <> 0 /\ 1 <= bv_unsigned a5)) by lia.
    clear KZ AZ.
    assert (DK : kz = 0 \/ (apart_gnl (bv_unsigned a2) (bv_unsigned a3)
                           /\ apart (bv_unsigned a2) (bv_unsigned a3) (bv_unsigned a0) MD_SIZE
                           /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
                                 u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
                                 apart (bv_unsigned a2) (bv_unsigned a3) p (Z.of_nat (length n2) + 1))
                           /\ (forall s, nm = Some s ->
                                 apart (bv_unsigned a2) (bv_unsigned a3) (bv_unsigned a1) (Z.of_nat (length s) + 1)))).
    { destruct KZr as [?|(_ & Ha & Hc)]; [left; assumption | right].
      destruct (AK Ha Hc) as (X1 & X2 & X3). refine (conj X1 (conj X2 (conj X3 _))).
      intros s Hs. exact (proj1 (ANK s Hs) Ha Hc). }
    assert (DA : az = 0 \/ (apart_gnl (bv_unsigned a4) (bv_unsigned a5)
                           /\ apart (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a0) MD_SIZE
                           /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
                                 u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
                                 apart (bv_unsigned a4) (bv_unsigned a5) p (Z.of_nat (length n2) + 1))
                           /\ (forall s, nm = Some s ->
                                 apart (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a1) (Z.of_nat (length s) + 1)))).
    { destruct AZr as [?|(_ & Ha & Hc)]; [left; assumption | right].
      destruct (AA Ha Hc) as (X1 & X2 & X3). refine (conj X1 (conj X2 (conj X3 _))).
      intros s Hs. exact (proj2 (ANK s Hs) Ha Hc). }
    assert (CG : clear_of [(bv_unsigned sp + -96, bv_unsigned sp); (bv_unsigned a2, bv_unsigned a2 + kz);
                           (bv_unsigned a4, bv_unsigned a4 + az)] A_G_NL NK_SIZE).
    { apply clear3.
      - clear - FAG. unfold apart_gnl in *. lia.
      - clear - DK KZr. destruct DK as [?|(X & _)]; unfold apart_gnl in *; lia.
      - clear - DA AZr. destruct DA as [?|(X & _)]; unfold apart_gnl in *; lia. }
    assert (MA1 : model_at m1 (bv_unsigned a0) mbs).
    { apply (model_at_munch _ m m1 _ mbs MA MUw WM). apply clear3.
      - clear - AFM. lia.
      - clear - DK KZr. destruct DK as [?|(_ & X & _)]; unfold apart in *; lia.
      - clear - DA AZr. destruct DA as [?|(_ & X & _)]; unfold apart in *; lia. }
    assert (NK1 : nlk_at m1 kbs) by exact (nlk_at_munch _ m m1 kbs NK MUw WM CG).
    assert (IT1 : iftab_at m1 kbs tab).
    { apply (iftab_at_munch _ m m1 kbs tab IT MUw CG). intros i n2 ix p Hi Hp. apply clear3.
      - pose proof (AFT i n2 ix p Hi Hp) as X. clear - X. lia.
      - destruct DK as [?|(_ & _ & X & _)]; [clear - KZr H; lia|].
        pose proof (X i n2 ix p Hi Hp) as Y. clear - Y KZr. unfold apart in *. lia.
      - destruct DA as [?|(_ & _ & X & _)]; [clear - AZr H; lia|].
        pose proof (X i n2 ix p Hi Hp) as Y. clear - Y AZr. unfold apart in *. lia. }
    assert (CS1 : forall s, nm = Some s -> cstr_at m1 (bv_unsigned a1) s).
    { intros s Hs. subst nm. destruct SA as [Hn0 Hc].
      apply (cstr_at_munch _ m m1 _ s Hc MUw). apply clear3.
      - pose proof (AFN Hn0 s eq_refl) as X. clear - X. lia.
      - destruct DK as [?|(_ & _ & _ & X)]; [clear - KZr H; lia|].
        pose proof (X s eq_refl) as Y. clear - Y KZr. unfold apart in *. lia.
      - destruct DA as [?|(_ & _ & _ & X)]; [clear - AZr H; lia|].
        pose proof (X s eq_refl) as Y. clear - Y AZr. unfold apart in *. lia. }
    assert (SLOT : forall i p, 0 <= i < 80 -> u64_at m1 (A_G_NL + NK_IF_NAME + 8 * i) p ->
                     u64_at m (A_G_NL + NK_IF_NAME + 8 * i) p)
      by (intros i p Hi Hp; exact (u64_slot_back _ m m1 i p MUw CG Hi Hp)).
    clear MUw.
    (* the frame in three pieces: [sp-96, sp-76) [sp-76, sp-56) [sp-56, sp) *)
    change [CB 40 jf; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      with ([CB 40 jf] ++ [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) in FR.
    apply rw_cells_app in FR. destruct FR as [FR40 FRhi].
    apply (rw_cells_cb_cut _ _ _ _ 20%nat) in FR40; [|lia].
    change [CB 20 (firstn 20 jf); CB (40 - 20) (skipn 20 jf)]
      with ([CB 20 (firstn 20 jf)] ++ [CB (40 - 20) (skipn 20 jf)]) in FR40.
    apply rw_cells_app in FR40. destruct FR40 as [FRlo FRmid].
    cbn [cells_size csize Nat.add Nat.sub] in FRhi, FRmid.
    replace (bv_unsigned sp + -96 + Z.of_nat 40) with (bv_unsigned sp + -56) in FRhi by lia.
    replace (bv_unsigned sp + -96 + Z.of_nat 20) with (bv_unsigned sp + -76) in FRmid by lia.
    pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp)] m1) as MUf.
    pose proof (wmono_refl rsegs m1) as WMf.
    assert (U96 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96)
      by (apply unsigned_lit; lia).
    pose proof SA as SA'.
    destruct nm as [s|].
    2: { cbn [str_arg] in SA. zstep. zstep. if_true. do 9 zstep.
          apply evt_done. eexists. eexists. split; [reflexivity|].
          split; [apply regs_preserved_mkR|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
          split.
          { pose proof (stk_release rsegs _ _ _ _ ST FRlo ltac:(lia)) as S1. cbn [cells_size csize Nat.add] in S1.
            replace (bv_unsigned sp + -96 + Z.of_nat 20) with (bv_unsigned sp + -76) in S1 by lia.
            pose proof (stk_release rsegs _ _ _ _ S1 FRmid ltac:(lia)) as S2. cbn [cells_size csize Nat.add] in S2.
            replace (bv_unsigned sp + -76 + Z.of_nat 20) with (bv_unsigned sp + -56) in S2 by lia.
            pose proof (stk_release rsegs _ _ _ _ S2 FRhi ltac:(lia)) as S3. cbn [cells_size csize Nat.add] in S3.
            replace (bv_unsigned sp + -56 + Z.of_nat 56) with (bv_unsigned sp) in S3 by lia. exact S3. }
          intros mbs0 kbs0 tab0 nm0 MA0 NK0 IT0 SA0.
          pose proof (model_at_uniq _ _ _ _ MA0 MA) as ->. pose proof (nlk_at_uniq _ _ _ NK0 NK) as ->.
          pose proof (iftab_uniq _ _ _ _ IT0 IT) as ->. pose proof (str_arg_uniq _ _ _ _ SA0 SA') as ->.
          cbv zeta. cbn [read_model read_core length Nat.eqb r_rc r_kind r_alias r_reqs r_state].
          split; [reflexivity|].
          exact (refused_tail m1 m1 (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a2) (bv_unsigned a3)
                   (bv_unsigned a4) (bv_unsigned a5) mbs kbs _ MUf WMf MA1 MWF AFM K0B AFK BK1 A0B AFA BA1
                   eq_refl ltac:(lia) ltac:(lia)). }
    destruct SA as [Hn0 _]. pose proof (CS1 s eq_refl) as CSm.
    zstep. zstep. if_false.
    destruct s as [|c s'].
    { (* the empty name *)
      assert (HR : ov_read_bytes rsegs m1 a1 1 = Some [zb 0]).
      { pose proof (bytes_at_ov_read rsegs m1 (bv_unsigned a1) ([] ++ [zb 0]) 0 1 (proj1 CSm) ltac:(cbn; lia)) as E.
        rewrite (wa_of_var a1 (bv_unsigned a1 + Z.of_nat 0)) in E by lia. exact E. }
      zstep. zstep. if_true. do 9 zstep.
      apply evt_done. eexists. eexists. split; [reflexivity|].
          split; [apply regs_preserved_mkR|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
          split.
          { pose proof (stk_release rsegs _ _ _ _ ST FRlo ltac:(lia)) as S1. cbn [cells_size csize Nat.add] in S1.
            replace (bv_unsigned sp + -96 + Z.of_nat 20) with (bv_unsigned sp + -76) in S1 by lia.
            pose proof (stk_release rsegs _ _ _ _ S1 FRmid ltac:(lia)) as S2. cbn [cells_size csize Nat.add] in S2.
            replace (bv_unsigned sp + -76 + Z.of_nat 20) with (bv_unsigned sp + -56) in S2 by lia.
            pose proof (stk_release rsegs _ _ _ _ S2 FRhi ltac:(lia)) as S3. cbn [cells_size csize Nat.add] in S3.
            replace (bv_unsigned sp + -56 + Z.of_nat 56) with (bv_unsigned sp) in S3 by lia. exact S3. }
          intros mbs0 kbs0 tab0 nm0 MA0 NK0 IT0 SA0.
          pose proof (model_at_uniq _ _ _ _ MA0 MA) as ->. pose proof (nlk_at_uniq _ _ _ NK0 NK) as ->.
          pose proof (iftab_uniq _ _ _ _ IT0 IT) as ->. pose proof (str_arg_uniq _ _ _ _ SA0 SA') as ->.
          cbv zeta. cbn [read_model read_core length Nat.eqb r_rc r_kind r_alias r_reqs r_state].
          split; [reflexivity|].
          exact (refused_tail m1 m1 (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a2) (bv_unsigned a3)
                   (bv_unsigned a4) (bv_unsigned a5) mbs kbs _ MUf WMf MA1 MWF AFM K0B AFK BK1 A0B AFA BA1
                   eq_refl ltac:(lia) ltac:(lia)). }
    assert (HR : ov_read_bytes rsegs m1 a1 1 = Some [c]).
    { pose proof (bytes_at_ov_read rsegs m1 (bv_unsigned a1) ((c :: s') ++ [zb 0]) 0 1 (proj1 CSm)
                    ltac:(cbn; lia)) as E.
      rewrite (wa_of_var a1 (bv_unsigned a1 + Z.of_nat 0)) in E by lia. exact E. }
    assert (Hc0 : c <> zb 0) by (intros ->; apply (proj2 CSm); left; reflexivity).
    assert (HC : bv_unsigned (Z_to_bv 64 (bv_unsigned c)) <> 0).
    { rewrite unsigned_lit; [exact (byte_ne0 c Hc0)|]. pose proof (bv_unsigned_in_range 8 c) as Hb.
      unfold bv_modulus in Hb. cbn in Hb. lia. }
    zstep. zstep. if_false. zstep. zstep.
    eapply (leaf_call _ _ _ _ _ HIDX).
    { intros r1 r2 mm q1 q2 mm' E1 E2 H bs tb nn H1 H2 H3. rewrite <- E2. apply (H bs tb nn H1 H2).
      unfold arg in *. rewrite E1. exact H3. }
    { exact HQ. }
    { exists kbs, tab, (c :: s'). unfold apart_frame, frame_apart_gnl. rewrite ?mkR_a0, ?mkR_sp, U96.
      refine (conj NK1 (conj _ (conj IT1 (conj Hn0 (conj CSm (conj _ _)))))).
      - clear - FAG. unfold apart_gnl in *. lia.
      - pose proof (AFN Hn0 (c :: s') eq_refl) as X. clear - X. lia.
      - intros i n2 ix p Hi Hp.
        assert (Li : 0 <= Z.of_nat i < 80).
        { assert (L : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
          destruct IT1 as (_ & HL & _). lia. }
        pose proof (AFT i n2 ix p Hi (SLOT (Z.of_nat i) p Li Hp)) as X. clear - X. lia. }
    { exact MI. }
    { rewrite U96. exact ST. }
    { rewrite U96. lia. }
    { rewrite U96. lia. }
    intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MUi WMi MIi STi POi.
    cbv beta in POi. unfold writes_nothing in MUi. rewrite U96 in MUi, STi.
    assert (IDX : a0' = wz (index_of tab (c :: s'))) by exact (POi kbs tab (c :: s') NK1 IT1 CSm).
    clear POi.
    transport_after_call rsegs m1 m2 MUi WMi.
    clear MUi WMi MI. rename MIi into MI. try clear ST. rename STi into ST.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    assert (Ridx : 0 <= index_of tab (c :: s') < 2 ^ 31)
      by exact (index_of_range tab _ (iftab_range m kbs tab IT)).
    assert (UA : bv_unsigned a0' = index_of tab (c :: s')) by (rewrite IDX; unfold wz; apply unsigned_lit; lia).
    destruct (Z.eq_dec (index_of tab (c :: s')) 0) as [I0|I0].
    { zstep. if_true. zstep. do 9 zstep.
      apply evt_done. eexists. eexists. split; [reflexivity|].
          split; [apply regs_preserved_mkR|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
          split.
          { pose proof (stk_release rsegs _ _ _ _ ST FRlo ltac:(lia)) as S1. cbn [cells_size csize Nat.add] in S1.
            replace (bv_unsigned sp + -96 + Z.of_nat 20) with (bv_unsigned sp + -76) in S1 by lia.
            pose proof (stk_release rsegs _ _ _ _ S1 FRmid ltac:(lia)) as S2. cbn [cells_size csize Nat.add] in S2.
            replace (bv_unsigned sp + -76 + Z.of_nat 20) with (bv_unsigned sp + -56) in S2 by lia.
            pose proof (stk_release rsegs _ _ _ _ S2 FRhi ltac:(lia)) as S3. cbn [cells_size csize Nat.add] in S3.
            replace (bv_unsigned sp + -56 + Z.of_nat 56) with (bv_unsigned sp) in S3 by lia. exact S3. }
          intros mbs0 kbs0 tab0 nm0 MA0 NK0 IT0 SA0.
          pose proof (model_at_uniq _ _ _ _ MA0 MA) as ->. pose proof (nlk_at_uniq _ _ _ NK0 NK) as ->.
          pose proof (iftab_uniq _ _ _ _ IT0 IT) as ->. pose proof (str_arg_uniq _ _ _ _ SA0 SA') as ->.
          unfold read_model, read_core. cbv zeta. cbn [length Nat.eqb]. rewrite I0. cbn [Z.eqb r_rc r_kind r_alias r_reqs r_state].
          split; [reflexivity|].
          exact (refused_tail m1 m2 (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a2) (bv_unsigned a3)
                   (bv_unsigned a4) (bv_unsigned a5) mbs kbs _ MUf WMf MA1 MWF AFM K0B AFK BK1 A0B AFA BA1
                   eq_refl ltac:(lia) ltac:(lia)). }
    zstep. if_false. do 5 zstep.
    (* memset(sp+20, 0, 20) *)
    eapply evt_cut.
    { eapply HMS; [ | exact MI ].
      lazymatch goal with |- rw_cells _ _ (bv_unsigned ?v) [CB (Z.to_nat (bv_unsigned ?w)) _] =>
        replace (bv_unsigned v) with (bv_unsigned sp + -76)
          by (rewrite ?U96; repeat (rewrite unsigned_lit by (rewrite ?U96; lia)); lia);
        replace (Z.to_nat (bv_unsigned w)) with 20%nat by (vm_compute; reflexivity) end.
      exact FRmid. }
    intros ms' (t0m & t1m & t2m & a1m & a2m & a3m & a4m & a5m & a6m & a7m & t3m & t4m & t5m & t6m & m3 & -> & MUm & WMm & MIm & FZ).
    lazymatch type of MUm with munch [(bv_unsigned ?v, _ + bv_unsigned ?w)] _ _ =>
      assert (Uv : bv_unsigned v = bv_unsigned sp + -76)
        by (rewrite ?U96; repeat (rewrite unsigned_lit by (rewrite ?U96; lia)); lia);
      assert (Uw : bv_unsigned w = 20) by (vm_compute; reflexivity) end.
    rewrite Uv, Uw in MUm. rewrite Uv in FZ.
    assert (FZ' : rw_cells rsegs m3 (bv_unsigned sp + -76) [CB 20 (zeros 20)]) by exact FZ.
    clear FZ Uv Uw.
    replace (bv_unsigned sp + -76 + 20) with (bv_unsigned sp + -56) in MUm by lia.
    transport_after_call rsegs m2 m3 MUm WMm.
    clear MUm WMm MI. rename MIm into MI.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    (* the four words of the request, then talk's arguments *)
    do 16 zstep.
    set (idx := index_of tab (c :: s')) in *.
    (* what talk needs, in the memory before the call *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m4 _) =>
      assert (MA4 : model_at m4 (bv_unsigned a0) mbs)
        by (apply (model_at_munch _ m1 m4 _ mbs MA1 MUf WMf); apply clear1; clear - AFM; lia);
      assert (NK4 : nlk_at m4 kbs)
        by (apply (nlk_at_munch _ m1 m4 kbs NK1 MUf WMf); apply clear1; clear - FAG; unfold apart_gnl in *; lia);
      assert (BK4 : buf_arg m4 (bv_unsigned a2) (bv_unsigned a3))
        by (apply (buf_arg_munch _ m1 m4 _ _ BK1 MUf WMf); intros Ha Hc; pose proof (AFK Ha) as X;
            cbn [disjoint_from]; split; [clear - X; lia | exact I]);
      assert (BA4 : buf_arg m4 (bv_unsigned a4) (bv_unsigned a5))
        by (apply (buf_arg_munch _ m1 m4 _ _ BA1 MUf WMf); intros Ha Hc; pose proof (AFA Ha) as X;
            cbn [disjoint_from]; split; [clear - X; lia | exact I]);
      assert (K04 : bv_unsigned a2 <> 0 -> bv_unsigned a3 <> 0 -> bytes_at rsegs m4 (bv_unsigned a2) [zb 0])
        by (intros Ha Hc; apply (bytes_at_munch _ m1 m4 _ _ (K0B Ha Hc) MUf); cbn [length]; apply clear1;
            pose proof (AFK Ha) as X; clear - X Ra3 Hc; lia);
      assert (A04 : bv_unsigned a4 <> 0 -> bv_unsigned a5 <> 0 -> bytes_at rsegs m4 (bv_unsigned a4) [zb 0])
        by (intros Ha Hc; apply (bytes_at_munch _ m1 m4 _ _ (A0B Ha Hc) MUf); cbn [length]; apply clear1;
            pose proof (AFA Ha) as X; clear - X Ra5 Hc; lia);
      assert (RQ4 : bytes_at rsegs m4 (bv_unsigned sp + -88) (req_read idx))
        by (replace (bv_unsigned sp + -88) with (bv_unsigned sp + -96 + 8) by lia;
            eapply (req_read_at m4 (bv_unsigned sp + -96));
            [ exact FRlo
            | replace (bv_unsigned sp + -96 + 20) with (bv_unsigned sp + -76) by lia; exact FZ'
            | exact Ridx | reflexivity | reflexivity | reflexivity | exact UA | reflexivity | reflexivity ])
    end.
    clear MUf WMf.
    assert (KNd : kn = 0 \/ (bv_unsigned a2 <> 0 /\ kn = bv_unsigned a3
                    /\ (bv_unsigned a2 + bv_unsigned a3 <= bv_unsigned sp - 240 \/ bv_unsigned sp <= bv_unsigned a2))).
    { rewrite Ekn. destruct (Z.eqb_spec (bv_unsigned a2) 0) as [E|E]; [left; reflexivity|].
      right. split; [exact E|]. split; [reflexivity | exact (AFK E)]. }
    assert (ANd : an = 0 \/ (bv_unsigned a4 <> 0 /\ an = bv_unsigned a5
                    /\ (bv_unsigned a4 + bv_unsigned a5 <= bv_unsigned sp - 240 \/ bv_unsigned sp <= bv_unsigned a4))).
    { rewrite Ean. destruct (Z.eqb_spec (bv_unsigned a4) 0) as [E|E]; [left; reflexivity|].
      right. split; [exact E|]. split; [reflexivity | exact (AFA E)]. }
    (* talk(m, sp+8, 32, kind, kind_n, alias, alias_n) *)
    eapply (leaf_call _ _ _ _ _ HTALK).
    { intros r1 r2 mm q1 q2 mm' E1 E2 H. unfold arg, spZ in *. rewrite <- !E1, <- !E2. exact H. }
    { exact HQ. }
    { exists mbs, kbs, (req_read idx).
      unfold apart_frame, frame_apart_gnl.
      rewrite ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_a5, ?mkR_a6, ?mkR_sp, U96.
      rewrite (unsigned_lit (bv_unsigned sp + -88)) by lia. rewrite (unsigned_lit 32) by lia.
      split; [exact MA4|]. split; [exact MWF|]. split; [exact NK4|].
      split; [clear - FAG; unfold apart_gnl in *; lia|]. split; [exact NWF|].
      split; [exact RQ4|]. split; [rewrite req_read_len; reflexivity|]. split; [unfold NL_SENT_LEN; lia|].
      split; [exact BK4|]. split; [exact BA4|].
      split; [unfold apart; clear - AFM; lia|].
      split; [intros Ha Hc; destruct (AK Ha Hc) as (X1 & X2 & _); exact (conj X1 X2)|].
      split; [intros Ha Hc; destruct (AA Ha Hc) as (X1 & X2 & _); exact (conj X1 X2)|].
      split; [intros Ha Hc Hb Hd; exact (AKA Ha Hb Hc Hd)|].
      split; [exact AGM|]. split; [clear - AFM; lia|]. split; [lia|].
      split; [intros Ha; pose proof (AFK Ha) as X; clear - X; lia|].
      intros Ha; pose proof (AFA Ha) as X; clear - X; lia. }
    { exact MI. }
    { rewrite U96. exact ST. }
    { rewrite U96. lia. }
    { rewrite U96. lia. }
    intros ra2 t02 t12 t22 a02 a12 a22 a32 a42 a52 a62 a72 t32 t42 t52 t62 m5 MUt WMt MIt STt POt.
    cbv beta zeta in MUt, POt.
    rewrite ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_a3, ?mkR_a4, ?mkR_a5, ?mkR_a6, ?mkR_sp in MUt, POt.
    rewrite ?U96 in MUt, STt, POt.
    rewrite <- Ekn, <- Ean in MUt.
    destruct (POt mbs kbs (req_read idx) MA4 NK4
                ltac:(rewrite mkR_a1, (unsigned_lit (bv_unsigned sp + -88)) by lia; exact RQ4)
                ltac:(rewrite req_read_len; reflexivity))
      as (RC & (mbs' & MA5 & MWF5 & NX5 & SO5 & SN5 & NM5 & MK5 & RQ5 & NR5) & KT & AT & KN & AN & KB5 & AB5).
    clear POt.
    transport_after_call rsegs m3 m5 MUt WMt.
    clear MUt WMt MI. rename MIt into MI. try clear ST. rename STt into ST. try rewrite U96 in ST.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    zstep. do 9 zstep.
    apply evt_done. eexists. eexists. split; [reflexivity|].
    split; [apply regs_preserved_mkR|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split.
    { pose proof (stk_release rsegs _ _ _ _ ST FRlo ltac:(lia)) as S1. cbn [cells_size csize Nat.add] in S1.
      replace (bv_unsigned sp + -96 + Z.of_nat 20) with (bv_unsigned sp + -76) in S1 by lia.
      pose proof (stk_release rsegs _ _ _ _ S1 FZ' ltac:(lia)) as S2. cbn [cells_size csize Nat.add] in S2.
      replace (bv_unsigned sp + -76 + Z.of_nat 20) with (bv_unsigned sp + -56) in S2 by lia.
      pose proof (stk_release rsegs _ _ _ _ S2 FRhi ltac:(lia)) as S3. cbn [cells_size csize Nat.add] in S3.
      replace (bv_unsigned sp + -56 + Z.of_nat 56) with (bv_unsigned sp) in S3 by lia. exact S3. }
    intros mbs0 kbs0 tab0 nm0 MA0 NK0 IT0 SA0.
    pose proof (model_at_uniq _ _ _ _ MA0 MA) as ->. pose proof (nlk_at_uniq _ _ _ NK0 NK) as ->.
    pose proof (iftab_uniq _ _ _ _ IT0 IT) as ->. pose proof (str_arg_uniq _ _ _ _ SA0 SA') as ->.
    unfold read_model, read_core. cbv zeta. cbn [length Nat.eqb]. fold idx.
    rewrite (proj2 (Z.eqb_neq idx 0) I0). cbn [r_rc r_kind r_alias r_reqs r_state].
    split; [exact RC|].
    split.
    { exists mbs'. split; [exact MA5|]. split; [exact MWF5|]. split; [exact NX5|].
      split; [rewrite talk_after_sock; exact SO5|]. split; [exact SN5|].
      split; [exact RQ5|]. split; [rewrite NR5, RQ5; reflexivity|]. split; [exact NM5 | exact MK5]. }
    split.
    { intros Ha Hc. rewrite (proj2 (Z.ltb_ge _ _) Hc). unfold text_of_attr.
      destruct (a_kind (talk_attrs (md_kstate mbs kbs))) as [pay|] eqn:EK; [first [exact (KT pay eq_refl Ha Hc) | exact (KT pay EK Ha Hc)]|].
      apply cstr_nil_of_byte. apply (bytes_at_munch _ m3 m5 _ _ (K04 Ha ltac:(lia)) ltac:(first [exact (KN eq_refl) | exact (KN EK)])).
      cbn [length]. destruct (AK Ha Hc) as (_ & X1 & _). pose proof (AFK Ha) as X2. unfold apart in X1.
      destruct (Z.eqb_spec (bv_unsigned a4) 0) as [E4|E4]; cbv iota.
      - apply clear3; [clear - X1 Hc; lia | right; right; lia | rewrite ?mkR_sp, ?U96; clear - X2 Hc; lia].
      - destruct (Z.eq_dec (bv_unsigned a5) 0) as [E5|E5].
        + apply clear3; [clear - X1 Hc; lia | clear - E5; lia | rewrite ?mkR_sp, ?U96; clear - X2 Hc; lia].
        + pose proof (AKA Ha E4 Hc ltac:(lia)) as X3. unfold apart in X3.
          apply clear3; [clear - X1 Hc; lia | clear - X3 Hc; lia | rewrite ?mkR_sp, ?U96; clear - X2 Hc; lia]. }
    split.
    { intros Ha Hc. rewrite (proj2 (Z.ltb_ge _ _) Hc). unfold text_of_attr.
      destruct (a_alias (talk_attrs (md_kstate mbs kbs))) as [pay|] eqn:EA; [first [exact (AT pay eq_refl Ha Hc) | exact (AT pay EA Ha Hc)]|].
      apply cstr_nil_of_byte. apply (bytes_at_munch _ m3 m5 _ _ (A04 Ha ltac:(lia)) ltac:(first [exact (AN eq_refl) | exact (AN EA)])).
      cbn [length]. destruct (AA Ha Hc) as (_ & X1 & _). pose proof (AFA Ha) as X2. unfold apart in X1.
      destruct (Z.eqb_spec (bv_unsigned a2) 0) as [E2|E2]; cbv iota.
      - apply clear3; [clear - X1 Hc; lia | right; right; lia | rewrite ?mkR_sp, ?U96; clear - X2 Hc; lia].
      - destruct (Z.eq_dec (bv_unsigned a3) 0) as [E3|E3].
        + apply clear3; [clear - X1 Hc; lia | clear - E3; lia | rewrite ?mkR_sp, ?U96; clear - X2 Hc; lia].
        + pose proof (AKA E2 Ha ltac:(lia) Hc) as X3. unfold apart in X3.
          apply clear3; [clear - X1 Hc; lia | clear - X3 Hc; lia | rewrite ?mkR_sp, ?U96; clear - X2 Hc; lia]. }
    split; [exact KB5 | exact AB5].
Qed.
End Walk.

(* memset's walk is in the tree: the closed form takes only the two own callees *)
Theorem model_read_holds_closed : index_of_contract_P -> talk_contract -> model_read_contract.
Proof. intros HI HT. exact (model_read_holds HI HT memset_holds). Qed.

Print Assumptions model_read_holds.
Print Assumptions model_read_holds_closed.
About model_read_holds.
About model_read_holds_closed.
