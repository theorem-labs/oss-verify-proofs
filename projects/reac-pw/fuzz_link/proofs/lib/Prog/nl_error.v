(* nl_error (netlink.h:305-315), PLAIN build: the walk of lib/Prog/nl_error_c.v on the plain
   image. 140 instructions at 0x154b4: nl_begin(w, NL_ERROR) (five puts), a 20-byte body on its
   own frame whose first four bytes are the code, nl_put of `cut` of those bytes, nl_end and
   nl_pad. Every one of those steps is guarded by `w->n + k > 4096`, which raises w->full and
   leaves w->n where it was, so the code has six points where two or three paths meet. The walk
   is written as one continuation per meeting point, innermost first, each stated over the
   registers that differ between the paths that reach it; what every one of them carries about
   memory is `nest` below, the two pieces of lib/Prog/hp_wr_kit.v plus this function's frame. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import
  link_mem mk_leaf hp_wr_kit nl_error_c memcpy_c memset_c memcpy memset.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
Local Open Scope Z_scope.

(* the memory this walk carries: the reply writer (hp_wr_kit `stk` window and the two field
   cells), its own frame, and what the `leaf` shape owes the caller *)
Definition nest (m0 m : word -> option byte) (w lo sp0 n f : Z)
    (s4v s3v s2v s1v s0v rav : word) (j j2 : list byte) : Prop :=
  stk rsegs m w (w + 4112) /\
  (exists tn tf pad, rw_cells rsegs m (w + 4096) [CB 8 tn; CB 4 tf; CB 4 pad] /\
     bytes_le_to_Z tn = n /\ bytes_le_to_Z tf = f) /\
  0 <= n <= 4096 /\ 0 <= f <= 1 /\
  munch [(sp0 + -80, sp0); (w, w + 4112)] m0 m /\ wmono rsegs m0 m /\
  mem_inv rsegs m /\ stk rsegs m lo (sp0 + -80) /\
  length j = 12%nat /\ length j2 = 20%nat /\
  rw_cells rsegs m (sp0 + -80)
    [CB 12 j; CB 20 j2; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

(* the `store_ok` a byte store into w->b at a register-held offset needs: it comes from the
   `stk` window the walk carries over the whole structure *)
Ltac sb_ok w n :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let H := fresh "HS" in
      assert (H : store_ok rsegs mm (wa (w + n)) 1 = true)
        by (eapply nw_store_ok; [ eassumption | lia | unfold NW_SIZE; lia ])
  end.

(* the prologue leaves the 32 bytes under the saved registers as one cell; the walk carries
   them as the 12 unused bytes and the 20 the body is built in *)
Ltac split_frame :=
  match goal with
  | H : rw_cells rsegs ?mm ?A (CB 32 ?jj :: ?post) |- _ =>
      let L := fresh "Ljj" in
      assert (L : length jj = 32%nat) by (destruct H as [[Hwf _] _]; cbn in Hwf; tauto);
      apply (rw_cells_split_CB rsegs mm A [] 32 jj post [12%nat; 20%nat]) in H;
        [ | reflexivity ];
      cbn [mk_CB_cells app] in H
  end.

Lemma nest_intro : forall m0 m w lo sp0 n f s4v s3v s2v s1v s0v rav j j2 tn tf pad,
  stk rsegs m w (w + 4112) ->
  rw_cells rsegs m (w + 4096) [CB 8 tn; CB 4 tf; CB 4 pad] ->
  bytes_le_to_Z tn = n -> bytes_le_to_Z tf = f ->
  0 <= n <= 4096 -> 0 <= f <= 1 ->
  munch [(sp0 + -80, sp0); (w, w + 4112)] m0 m -> wmono rsegs m0 m ->
  mem_inv rsegs m -> stk rsegs m lo (sp0 + -80) ->
  rw_cells rsegs m (sp0 + -80)
    [CB 12 j; CB 20 j2; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  length j = 12%nat -> length j2 = 20%nat ->
  nest m0 m w lo sp0 n f s4v s3v s2v s1v s0v rav j j2.
Proof.
  intros. unfold nest.
  split; [assumption|]. split; [exists tn, tf, pad; split; [assumption|split; assumption]|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* nl_pad's `srliw`/`slli` pair, as a value: w->n rounded up to the next multiple of four *)
Lemma align4_val : forall x, 0 <= x <= 4096 ->
  Z.shiftl (bv_swrap 32 (Z.shiftr (bv_wrap 32 (x + 3)) 2) mod 18446744073709551616) 2
  = (x + 3) / 4 * 4.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus.
  change (bv_modulus 32) with 4294967296.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
  rewrite (Z.mod_small (x + 3) 4294967296) by lia.
  assert (Hd : 0 <= (x + 3) / 4 <= 1024) by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small ((x + 3) / 4 + 4294967296 / 2) 4294967296) by lia.
  replace ((x + 3) / 4 + 4294967296 / 2 - 4294967296 / 2) with ((x + 3) / 4) by lia.
  rewrite (Z.mod_small ((x + 3) / 4) 18446744073709551616) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. reflexivity.
Qed.

(* the writer's state across a callee (memcpy, memset) that wrote only [a, a + k) of w->b *)
Lemma nest_call : forall m0 m m' w lo sp0 n f s4v s3v s2v s1v s0v rav j j2 a k,
  nest m0 m w lo sp0 n f s4v s3v s2v s1v s0v rav j j2 ->
  (w + 4112 <= sp0 + -80 \/ sp0 <= w) ->
  w <= a -> 0 <= k -> a + k <= w + 4096 ->
  munch [(a, a + k)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  (forall x, a <= x < a + k -> exists b, mrd rsegs m' (wa x) = Some b) ->
  nest m0 m' w lo sp0 n f s4v s3v s2v s1v s0v rav j j2.
Proof.
  intros m0 m m' w lo sp0 n f s4v s3v s2v s1v s0v rav j j2 a k
    (SW & (tn & tf & pad & HC & Hn & Hf) & HNb & HFb & MU & WM & MI & ST & Lj & Lj2 & FR)
    APF Ha Hk Hak MUc WMc MIc Hcov.
  assert (Hcase : forall x, outside [(a, a + k)] x \/ (exists b, mrd rsegs m' (wa x) = Some b)).
  { intros x. destruct (Z.leb_spec a x); destruct (Z.ltb_spec x (a + k)).
    - right. apply Hcov. lia.
    - left. cbn [outside]. split; [lia | exact I].
    - left. cbn [outside]. split; [lia | exact I].
    - left. cbn [outside]. split; [lia | exact I]. }
  unfold nest.
  split; [eapply stk_transport_mrd; [exact SW | exact MUc | exact WMc | intros x _; apply Hcase]|].
  split.
  { exists tn, tf, pad. split; [|split; assumption].
    eapply rw_cells_transport; [exact HC | exact MUc | exact WMc |].
    cbn [disjoint_from cells_size csize]. split; [lia | exact I]. }
  split; [exact HNb|]. split; [exact HFb|].
  split.
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc].
    unfold sub_fp. cbn [outside]. intros x (H1 & H2 & _). split; [lia | exact I]. }
  split; [eapply wmono_trans; eassumption|].
  split; [exact MIc|].
  split; [eapply stk_transport_mrd; [exact ST | exact MUc | exact WMc | intros x _; apply Hcase]|].
  split; [exact Lj|]. split; [exact Lj2|].
  eapply rw_cells_transport; [exact FR | exact MUc | exact WMc |].
  cbn [disjoint_from cells_size csize]. split; [lia | exact I].
Qed.

Lemma bytes_at_firstn : forall m A bs (k : nat),
  bytes_at rsegs m A bs -> bytes_at rsegs m A (firstn k bs).
Proof.
  intros m A bs k H. rewrite <- (firstn_skipn k bs) in H.
  apply (proj1 (bytes_at_app rsegs m A _ _)) in H. exact (proj1 H).
Qed.

(* the 20 bytes of the body, out of the frame cells the walk carries *)
Lemma frame_body : forall m A j bts post (k : nat),
  rw_cells rsegs m A (CB 12 j :: CB 20 bts :: post) -> length j = 12%nat ->
  bytes_at rsegs m (A + 12) (firstn k bts).
Proof.
  intros m A j bts post k [[_ Hb] _] Lj.
  cbn [cells_bytes cbytes] in Hb.
  apply (proj1 (bytes_at_app rsegs m A j _)) in Hb. destruct Hb as [_ Hb].
  rewrite Lj in Hb. cbn [Z.of_nat] in Hb.
  apply (proj1 (bytes_at_app rsegs m (A + 12) bts _)) in Hb.
  apply bytes_at_firstn. exact (proj1 Hb).
Qed.

Ltac fix_ret :=
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k)
      by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

Theorem nl_error_holds_h : memcpy_contract -> memset_contract -> nl_error_contract.
Proof.
  intros MEMCPY MEMSET.
  unfold nl_error_contract. apply leaf_intro.
  - intros r1 r2 m E H.
    assert (SPG : forall R : bvmap 5 word, spZ R = bv_unsigned (getr R 2)) by reflexivity.
    unfold arg, apart_frame in *. rewrite !SPG in *. rewrite <- !E. exact H.
  - intros r1 r2 m E. unfold arg. rewrite <- !E. reflexivity.
  - intros r1 r2 m q1 q2 m' E _ H. unfold arg in *. rewrite <- E. exact H.
  - unfold leaf_walk, NL_ERROR_F.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m lo.
    cbv zeta. intros PRE MI ST LO SP.
    destruct PRE as (bs0 & HW0 & HWF0 & APF & HCUT). rewrite !mkR_a0.
    rewrite mkR_a0 in HW0, APF. rewrite mkR_a2 in HCUT. unfold NL_ERR_BODY in HCUT.
    unfold apart_frame, NW_SIZE in APF. rewrite mkR_sp in APF.
    pose proof (nlw_bound m (bv_unsigned a0) bs0 HW0) as [HwA HwB]. unfold NW_SIZE in HwB.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
    pose proof (zr_word a2) as Ra2. unfold inr64 in Ra2.
    destruct HWF0 as [HN0 HF0]. unfold NL_CHUNK_MAX in HN0.
    pose proof (stk_of_nlw m (bv_unsigned a0) bs0 HW0) as SW. unfold NW_SIZE in SW.
    destruct (nlw_cells m (bv_unsigned a0) bs0 HW0) as (tn0 & tf0 & pad0 & HC & Htn & Htf).
    assert (Ltn0 : length tn0 = 8%nat) by (destruct HC as [[Hwf _] _]; cbn in Hwf; tauto).
    assert (Ltf0 : length tf0 = 4%nat) by (destruct HC as [[Hwf _] _]; cbn in Hwf; tauto).
    assert (Lpd0 : length pad0 = 4%nat) by (destruct HC as [[Hwf _] _]; cbn in Hwf; tauto).
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp);
                            (bv_unsigned a0, bv_unsigned a0 + 4112)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
    carve_frame 80%nat ST.
    match goal with |- evt _ ?QQ _ => set (Q := QQ) end.

    (* ================= the epilogue, 0x156c4 ================= *)
    assert (KEpi : forall (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                           s2' s3' s4' t3' t4' t5' t6' : word)
                          (m' : word -> option byte) (n f : Z) (j j2 : list byte),
      nest m m' (bv_unsigned a0) lo (bv_unsigned sp) n f s4 s3 s2 s1 s0 ra j j2 ->
      nw_n bs0 <= n ->
      evt rsegs Q (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' s0' s1'
                           a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4'
                           s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F (Z_to_bv 64 0x156c4) fc None m' (seg_rom rsegs))).
    { intros ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6'
             m' n f j j2 HN HLE.
      destruct HN as (SW' & (tn & tf & pad & HC' & Htn' & Htf') & HNb & HFb &
                      MU' & WM' & MI' & ST' & Lj & Lj2 & FR').
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      apply evt_done. unfold Q.
      eexists. exists m'. split; [reflexivity|].
      split; [apply regs_preserved_mkR|].
      split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|].
      split.
      { pose proof (stk_release rsegs m' lo (bv_unsigned sp + -80) _ ST' FR' ltac:(lia)) as X.
        cbn [cells_size csize Nat.add] in X.
        replace (bv_unsigned sp + -80 + Z.of_nat 80) with (bv_unsigned sp) in X by lia. exact X. }
      intros bs Hbs. rewrite (nlw_at_unique m (bv_unsigned a0) bs bs0 Hbs HW0).
      destruct (nlw_from m' (bv_unsigned a0) n f tn tf pad SW' HC' Htn' Htf')
        as (bs' & HW' & En & Ef).
      exists bs'. split; [exact HW'|].
      split; [split; rewrite ?En, ?Ef; unfold NL_CHUNK_MAX; lia | lia]. }

    (* ================= nl_pad, 0x1567c ================= *)
    assert (KPad : forall (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                           s2' s3' s4' t3' t4' t5' t6' : word)
                          (m' : word -> option byte) (n f : Z) (j j2 : list byte),
      s0' = a0 -> s2' = Z_to_bv 64 (bv_unsigned a0 + 4096) -> a0' = Z_to_bv 64 n ->
      nest m m' (bv_unsigned a0) lo (bv_unsigned sp) n f s4 s3 s2 s1 s0 ra j j2 ->
      nw_n bs0 <= n ->
      evt rsegs Q (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' s0' s1'
                           a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4'
                           s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F (Z_to_bv 64 0x1567c) fc None m' (seg_rom rsegs))).
    { intros ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6'
             m' n f j j2 Es0 Es2 Ea0 HN HLE. subst s0' s2' a0'.
      pose proof HN as (SW' & (tn & tf & pad & HC' & Htn' & Htf') & HNb & HFb &
                        MU' & WM' & MI' & ST' & Lj & Lj2 & FR').
      assert (Lpd : length pad = 4%nat) by (destruct HC' as [[Hwf _] _]; cbn in Hwf; tauto).
      assert (Ltf : length tf = 4%nat) by (destruct HC' as [[Hwf _] _]; cbn in Hwf; tauto).
      zstep. zstep. zstep. zstep.
      rewrite (align4_val n ltac:(lia)).
      remember ((n + 3) / 4 * 4) as P eqn:EP.
      assert (HP : n <= P <= 4096) by (subst P; Z.div_mod_to_equations; lia). clear EP.
      zstep. zstep. if_cases Hg.
      2: { (* 4 * ((n+3)/4) is never above 4096 for n <= 4096, so this exit never runs *)
           cbv iota. zify_cond Hg. exfalso. revert Hg. Z.div_mod_to_equations. lia. }
      cbv iota. clear Hg.
      zstep. if_cases Hg2.
      - (* w->n is already a multiple of four: nothing to pad *)
        cbv iota. zify_cond Hg2.
        zstep.
        eapply KEpi with (n := n) (f := f); [|exact HLE].
        match goal with
        | HX : rw_cells rsegs ?mm (bv_unsigned a0 + 4096) [?c0; ?c1; CB 4 pad] |- _ =>
            pose proof (cells_nw mm (bv_unsigned a0 + 4096) c0 c1 pad HX
                          eq_refl eq_refl I Ltf Lpd) as HCr
        end.
        cbn [cbytes] in HCr.
        eapply nest_intro;
          [ eassumption | exact HCr
          | rewrite bytes_le_to_Z_le8, unsigned_lit by lia; reflexivity
          | exact Htf' | lia | lia
          | eassumption | eassumption | eassumption | eassumption | eassumption
          | exact Lj | exact Lj2 ].
      - (* memset(w->b + w->n, 0, P - w->n), then w->n = P *)
        cbv iota. zify_cond Hg2.
        zstep. zstep. zstep. zstep. zstep.
        destruct (cells_of_stk m' (bv_unsigned a0) (bv_unsigned a0 + 4112)
                    (bv_unsigned a0 + n) (Z.to_nat (P - n)) SW' ltac:(lia) ltac:(lia))
          as (zjunk & Hjl & HJ).
        eapply evt_cut.
        { eapply MEMSET with (junk := zjunk); [|exact MI'].
          rewrite !unsigned_lit by lia. exact HJ. }
        intros ms' (t0x & t1x & t2x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x
                    & t6x & m2 & Ems & MUc & WMc & MIc & CC).
        subst ms'. rewrite !unsigned_lit in MUc, CC by lia.
        assert (COV : forall x, bv_unsigned a0 + n <= x < bv_unsigned a0 + n + (P - n) ->
                        exists b, mrd rsegs m2 (wa x) = Some b).
        { intros x Hx. eapply stk_cover_cells; [exact CC | cbn [cells_size csize]; lia]. }
        pose proof (nest_call m m' m2 (bv_unsigned a0) lo (bv_unsigned sp) n f s4 s3 s2 s1 s0 ra
                      j j2 (bv_unsigned a0 + n) (P - n) HN APF ltac:(lia) ltac:(lia) ltac:(lia)
                      MUc WMc MIc COV) as HN2.
        clear SW' HC' MU' WM' MI' ST' FR' Htn' Htf' HN CC COV MUc WMc HJ.
        destruct HN2 as (SW2 & (tn2 & tf2 & pad2 & HC2 & Htn2 & Htf2) & HNb2 & HFb2 &
                         MU2 & WM2 & MI2 & ST2 & Lj2a & Lj2b & FR2).
        assert (Ltn2 : length tn2 = 8%nat) by (destruct HC2 as [[Hwf _] _]; cbn in Hwf; tauto).
        assert (Ltf2 : length tf2 = 4%nat) by (destruct HC2 as [[Hwf _] _]; cbn in Hwf; tauto).
        assert (Lpd2 : length pad2 = 4%nat) by (destruct HC2 as [[Hwf _] _]; cbn in Hwf; tauto).
        fix_ret.
        zstep. rewrite (ld_cb tn2 Ltn2), Htn2. zstep. zstep.
        eapply KEpi with (n := P) (f := f); [|lia].
        match goal with
        | HX : rw_cells rsegs ?mm (bv_unsigned a0 + 4096) [?c0; ?c1; CB 4 pad2] |- _ =>
            pose proof (cells_nw mm (bv_unsigned a0 + 4096) c0 c1 pad2 HX
                          eq_refl eq_refl I Ltf2 Lpd2) as HCr
        end.
        cbn [cbytes] in HCr.
        eapply nest_intro;
          [ eassumption | exact HCr
          | rewrite bytes_le_to_Z_le8, unsigned_lit by lia; lia
          | exact Htf2 | lia | lia
          | eassumption | eassumption | eassumption | eassumption | eassumption
          | exact Lj2a | exact Lj2b ]. }

    (* ================= nl_end, 0x15650 ================= *)
    assert (KEnd : forall (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                           s2' s3' s4' t3' t4' t5' t6' : word)
                          (m' : word -> option byte) (n f : Z) (j j2 : list byte),
      s0' = a0 -> s2' = Z_to_bv 64 (bv_unsigned a0 + 4096) -> a0' = Z_to_bv 64 n ->
      s3' = Z_to_bv 64 (bv_unsigned a0 + nw_n bs0) -> s4' = Z_to_bv 64 (nw_n bs0) ->
      nest m m' (bv_unsigned a0) lo (bv_unsigned sp) n f s4 s3 s2 s1 s0 ra j j2 ->
      nw_n bs0 <= n ->
      evt rsegs Q (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' s0' s1'
                           a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4'
                           s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F (Z_to_bv 64 0x15650) fc None m' (seg_rom rsegs))).
    { intros ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6'
             m' n f j j2 Es0 Es2 Ea0 Es3 Es4 HN HLE. subst s0' s2' a0' s3' s4'.
      destruct HN as (SW' & (tn & tf & pad & HC' & Htn' & Htf') & HNb & HFb &
                      MU' & WM' & MI' & ST' & Lj & Lj2 & FR').
      assert (Ltn : length tn = 8%nat) by (destruct HC' as [[Hwf _] _]; cbn in Hwf; tauto).
      assert (Ltf : length tf = 4%nat) by (destruct HC' as [[Hwf _] _]; cbn in Hwf; tauto).
      assert (Lpd : length pad = 4%nat) by (destruct HC' as [[Hwf _] _]; cbn in Hwf; tauto).
      zstep. zstep. if_cases Hg.
      + (* the message is shorter than its own header: nl_set32 writes nothing *)
        cbv iota. zify_cond Hg.
        eapply KPad with (n := n) (f := f);
          [ reflexivity | reflexivity | reflexivity | | exact HLE ].
        eapply nest_intro;
          [ eassumption | exact HC' | exact Htn' | exact Htf' | lia | lia
          | eassumption | eassumption | eassumption | eassumption | eassumption
          | exact Lj | exact Lj2 ].
      + (* the length of the message goes into the first word of its header *)
        cbv iota. zify_cond Hg.
        assert (Hb : nw_n bs0 + 4 <= n) by (revert Hg; Z.div_mod_to_equations; lia).
        sb_ok (bv_unsigned a0) (nw_n bs0).
        zstep. zstep. zstep. zstep. zstep. store_done.
        sb_ok (bv_unsigned a0) (nw_n bs0 + 1).
        zstep. store_done.
        sb_ok (bv_unsigned a0) (nw_n bs0 + 2).
        zstep. store_done.
        sb_ok (bv_unsigned a0) (nw_n bs0 + 3).
        zstep. store_done.
        zstep. rewrite (ld_cb tn Ltn), Htn'.
        eapply KPad with (n := n) (f := f);
          [ reflexivity | reflexivity | reflexivity | | exact HLE ].
        eapply nest_intro;
          [ eassumption | eassumption | exact Htn' | exact Htf' | lia | lia
          | eassumption | eassumption | eassumption | eassumption | eassumption
          | exact Lj | exact Lj2 ]. }

    (* ================= the body and nl_put, 0x155f4 ================= *)
    assert (KBody : forall (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                            s2' s3' s4' t3' t4' t5' t6' : word)
                           (m' : word -> option byte) (n f : Z) (j j2 : list byte),
      s0' = a0 -> s2' = Z_to_bv 64 (bv_unsigned a0 + 4096) -> a0' = Z_to_bv 64 n ->
      s3' = Z_to_bv 64 (bv_unsigned a0 + nw_n bs0) -> s4' = Z_to_bv 64 (nw_n bs0) ->
      s1' = a2 ->
      nest m m' (bv_unsigned a0) lo (bv_unsigned sp) n f s4 s3 s2 s1 s0 ra j j2 ->
      nw_n bs0 <= n ->
      evt rsegs Q (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' s0' s1'
                           a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4'
                           s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F (Z_to_bv 64 0x155f4) fc None m' (seg_rom rsegs))).
    { intros ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6'
             m' n f j j2 Es0 Es2 Ea0 Es3 Es4 Es1 HN HLE. subst s0' s2' a0' s3' s4' s1'.
      (* 0x15610, where the two readings of `cut` meet: C is the clamped one *)
      assert (KPut : forall (C : Z) (m2 : word -> option byte) (n2 f2 : Z) (jx j2x : list byte)
                            (s1v ra2 t02 t12 t22 a12 a22 a32 a42 a52 a62 a72 t32 t42 t52 t62 : word),
        0 <= C <= 20 -> bv_unsigned s1v = C ->
        nest m m2 (bv_unsigned a0) lo (bv_unsigned sp) n2 f2 s4 s3 s2 s1 s0 ra jx j2x ->
        nw_n bs0 <= n2 ->
        evt rsegs Q (MS (mkR ra2 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t02 t12 t22 a0
                             s1v (Z_to_bv 64 n2) a12 a22 a32 a42 a52 a62 a72
                             (Z_to_bv 64 (bv_unsigned a0 + 4096))
                             (Z_to_bv 64 (bv_unsigned a0 + nw_n bs0)) (Z_to_bv 64 (nw_n bs0))
                             s5 s6 s7 s8 s9 s10 s11 t32 t42 t52 t62)
                        F (Z_to_bv 64 0x15610) fc None m2 (seg_rom rsegs))).
      { intros C m2 n2 f2 jx j2x s1v ra2 t02 t12 t22 a12 a22 a32 a42 a52 a62 a72 t32 t42 t52 t62
               HC20 Es1v HN2 HLE2.
        assert (Es1w : s1v = Z_to_bv 64 C)
          by (apply bv_eq; rewrite Es1v; symmetry; apply unsigned_lit; lia).
        subst s1v.
        pose proof HN2 as (SW2 & (tn2 & tf2 & pad2 & HC2 & Htn2 & Htf2) & HNb2 & HFb2 &
                           MU2 & WM2 & MI2 & ST2 & Ljx & Lj2x & FR2).
        assert (Ltn2 : length tn2 = 8%nat) by (destruct HC2 as [[Hwf _] _]; cbn in Hwf; tauto).
        assert (Ltf2 : length tf2 = 4%nat) by (destruct HC2 as [[Hwf _] _]; cbn in Hwf; tauto).
        assert (Lpd2 : length pad2 = 4%nat) by (destruct HC2 as [[Hwf _] _]; cbn in Hwf; tauto).
        zstep. zstep. zstep. zstep. if_cases Hg.
        - (* the body fits *)
          cbv iota. zify_cond Hg.
          assert (Hb : n2 + C <= 4096) by (revert Hg; Z.div_mod_to_equations; lia).
          zstep. if_cases Hg2.
          + (* nothing to copy: w->n is stored back unchanged *)
            cbv iota. zify_cond Hg2.
            zstep. zstep.
            eapply KEnd with (n := n2 + C) (f := f2);
              [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
              | | lia ].
            match goal with
            | HX : rw_cells rsegs ?mm (bv_unsigned a0 + 4096) [?c0; ?c1; CB 4 pad2] |- _ =>
                pose proof (cells_nw mm (bv_unsigned a0 + 4096) c0 c1 pad2 HX
                              eq_refl eq_refl I Ltf2 Lpd2) as HCr
            end.
            cbn [cbytes] in HCr.
            eapply nest_intro;
              [ eassumption | exact HCr
              | rewrite bytes_le_to_Z_le8, unsigned_lit by lia; reflexivity
              | exact Htf2 | lia | lia
              | eassumption | eassumption | eassumption | eassumption | eassumption
              | exact Ljx | exact Lj2x ].
          + (* memcpy(w->b + w->n, the body, C), then w->n = w->n + C *)
            cbv iota. zify_cond Hg2.
            pose proof (frame_body m2 (bv_unsigned sp + -80) jx j2x
                          [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] (Z.to_nat C) FR2 Ljx) as HSrc.
            destruct (cells_of_stk m2 (bv_unsigned a0) (bv_unsigned a0 + 4112)
                        (bv_unsigned a0 + n2) (Z.to_nat C) SW2 ltac:(lia) ltac:(lia))
              as (zjunk & Hjl & HJ).
            zstep. zstep. zstep. zstep.
            eapply evt_cut.
            { eapply MEMCPY with (src := firstn (Z.to_nat C) j2x) (junk := zjunk);
                [ rewrite !unsigned_lit by lia;
                  replace (bv_unsigned sp + -68) with (bv_unsigned sp + -80 + 12) by lia;
                  exact HSrc
                | rewrite !unsigned_lit by lia; rewrite firstn_length; lia
                | rewrite !unsigned_lit by lia; exact HJ
                | rewrite !unsigned_lit by lia; lia
                | exact MI2 ]. }
            intros ms' (t0y & t1y & t2y & a1y & a2y & a3y & a4y & a5y & a6y & a7y & t3y & t4y
                        & t5y & t6y & m3 & Ems & MUc & WMc & MIc & CC & BSc).
            subst ms'. rewrite !unsigned_lit in MUc, CC by lia.
            assert (COV : forall x, bv_unsigned a0 + n2 <= x < bv_unsigned a0 + n2 + C ->
                            exists b, mrd rsegs m3 (wa x) = Some b).
            { intros x Hx. eapply stk_cover_cells; [exact CC | cbn [cells_size csize]; lia]. }
            pose proof (nest_call m m2 m3 (bv_unsigned a0) lo (bv_unsigned sp) n2 f2
                          s4 s3 s2 s1 s0 ra jx j2x (bv_unsigned a0 + n2) C HN2 APF
                          ltac:(lia) ltac:(lia) ltac:(lia) MUc WMc MIc COV) as HN3.
            clear SW2 HC2 MU2 WM2 MI2 ST2 FR2 Htn2 Htf2 HN2 CC BSc COV MUc WMc HJ HSrc.
            destruct HN3 as (SW3 & (tn3 & tf3 & pad3 & HC3 & Htn3 & Htf3) & HNb3 & HFb3 &
                             MU3 & WM3 & MI3 & ST3 & Lj3a & Lj3b & FR3).
            assert (Ltn3 : length tn3 = 8%nat) by (destruct HC3 as [[Hwf _] _]; cbn in Hwf; tauto).
            assert (Ltf3 : length tf3 = 4%nat) by (destruct HC3 as [[Hwf _] _]; cbn in Hwf; tauto).
            assert (Lpd3 : length pad3 = 4%nat) by (destruct HC3 as [[Hwf _] _]; cbn in Hwf; tauto).
            fix_ret.
            zstep. rewrite (ld_cb tn3 Ltn3), Htn3. zstep. zstep. zstep.
            eapply KEnd with (n := n2 + C) (f := f2);
              [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | lia ].
            match goal with
            | HX : rw_cells rsegs ?mm (bv_unsigned a0 + 4096) [?c0; ?c1; CB 4 pad3] |- _ =>
                pose proof (cells_nw mm (bv_unsigned a0 + 4096) c0 c1 pad3 HX
                              eq_refl eq_refl I Ltf3 Lpd3) as HCr
            end.
            cbn [cbytes] in HCr.
            eapply nest_intro;
              [ eassumption | exact HCr
              | rewrite bytes_le_to_Z_le8, unsigned_lit by lia; reflexivity
              | exact Htf3 | lia | lia
              | eassumption | eassumption | eassumption | eassumption | eassumption
              | exact Lj3a | exact Lj3b ].
        - (* the body does not fit: w->full is raised *)
          cbv iota. zify_cond Hg.
          zstep. zstep. zstep.
          eapply KEnd with (n := n2) (f := bytes_le_to_Z (le4 (Z_to_bv 64 1)));
            [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | lia ].
          match goal with
          | HX : rw_cells rsegs ?mm (bv_unsigned a0 + 4096) [?c0; ?c1; CB 4 pad2] |- _ =>
              pose proof (cells_nw mm (bv_unsigned a0 + 4096) c0 c1 pad2 HX
                            eq_refl eq_refl Ltn2 I Lpd2) as HCr
          end.
          cbn [cbytes] in HCr.
          eapply nest_intro;
            [ eassumption | exact HCr | exact Htn2 | reflexivity | lia
            | rewrite bytes_le_to_Z_le4, unsigned_lit by lia; lia
            | eassumption | eassumption | eassumption | eassumption | eassumption
            | exact Ljx | exact Lj2x ]. }
      (* the five `sw` that build the body on the frame, then the sign test on `cut` *)
      pose proof HN as (SW' & (tn & tf & pad & HC' & Htn' & Htf') & HNb & HFb &
                        MU' & WM' & MI' & ST' & Lj & Lj2 & FR').
      apply (rw_cells_split_CB rsegs m' (bv_unsigned sp + -80) [CB 12 j] 20 j2
               [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] [4%nat; 4%nat; 4%nat; 4%nat; 4%nat])
        in FR'; [|reflexivity].
      cbn [mk_CB_cells app] in FR'.
      zstep. zstep. zstep. zstep. zstep.
      match goal with
      | HX : rw_cells rsegs ?mm (bv_unsigned sp + -80)
               (CB 12 j :: ?d0 :: ?d1 :: ?d2 :: ?d3 :: ?d4 :: ?post) |- _ =>
          pose proof (rw_cells_merge rsegs mm (bv_unsigned sp + -80) [CB 12 j]
                        [d0; d1; d2; d3; d4] post HX) as FRm
      end.
      cbn [cells_size csize cells_bytes cbytes app] in FRm.
      zstep. if_cases Hgs.
      + (* `cut` read as a signed int is not negative: the contract bounds it by 20 *)
        cbv iota. zify_cond Hgs.
        eapply KPut with (C := bv_unsigned a2) (n2 := n) (f2 := f);
          [ lia | reflexivity | | exact HLE ].
        eapply nest_intro;
          [ exact SW' | exact HC' | exact Htn' | exact Htf' | lia | lia
          | exact MU' | exact WM' | exact MI' | exact ST' | exact FRm
          | exact Lj | rewrite !app_length, !length_le4; reflexivity ].
      + (* it is negative: the whole 20-byte body is written *)
        cbv iota. zify_cond Hgs.
        zstep.
        eapply KPut with (C := 20) (n2 := n) (f2 := f);
          [ lia | apply unsigned_lit; lia | | exact HLE ].
        eapply nest_intro;
          [ exact SW' | exact HC' | exact Htn' | exact Htf' | lia | lia
          | exact MU' | exact WM' | exact MI' | exact ST' | exact FRm
          | exact Lj | rewrite !app_length, !length_le4; reflexivity ]. }

    (* ================= nl_put32 of the flags, 0x15588 ================= *)
    assert (KPut4 : forall (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                            s2' s3' s4' t3' t4' t5' t6' : word)
                           (m' : word -> option byte) (n f : Z) (j j2 : list byte),
      s0' = a0 -> s2' = Z_to_bv 64 (bv_unsigned a0 + 4096) -> a0' = Z_to_bv 64 n ->
      s3' = Z_to_bv 64 (bv_unsigned a0 + nw_n bs0) -> s4' = Z_to_bv 64 (nw_n bs0) ->
      s1' = a2 -> a2' = Z_to_bv 64 (-4093) ->
      nest m m' (bv_unsigned a0) lo (bv_unsigned sp) n f s4 s3 s2 s1 s0 ra j j2 ->
      nw_n bs0 <= n ->
      evt rsegs Q (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' s0' s1'
                           a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4'
                           s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F (Z_to_bv 64 0x15588) fc None m' (seg_rom rsegs))).
    { intros ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6'
             m' n f j j2 Es0 Es2 Ea0 Es3 Es4 Es1 Ea2 HN HLE. subst s0' s2' a0' s3' s4' s1' a2'.
      destruct HN as (SW' & (tn & tf & pad & HC' & Htn' & Htf') & HNb & HFb &
                      MU' & WM' & MI' & ST' & Lj & Lj2 & FR').
      assert (Ltn : length tn = 8%nat) by (destruct HC' as [[Hwf _] _]; cbn in Hwf; tauto).
      assert (Ltf : length tf = 4%nat) by (destruct HC' as [[Hwf _] _]; cbn in Hwf; tauto).
      assert (Lpd : length pad = 4%nat) by (destruct HC' as [[Hwf _] _]; cbn in Hwf; tauto).
      zstep. zstep. zstep. zstep. if_cases Hg.
      + (* w->n + 4 > 4096: w->full is raised *)
        cbv iota. zify_cond Hg.
        assert (Hb : 4093 <= n) by (revert Hg; Z.div_mod_to_equations; lia).
        zstep. zstep. zstep.
        eapply KBody;
          [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | | exact HLE ].
        match goal with
        | HX : rw_cells rsegs ?mm (bv_unsigned a0 + 4096) [?c0; ?c1; CB 4 pad] |- _ =>
            pose proof (cells_nw mm (bv_unsigned a0 + 4096) c0 c1 pad HX
                          eq_refl eq_refl Ltn I Lpd) as HCr
        end.
        cbn [cbytes] in HCr.
        eapply nest_intro;
          [ eassumption | exact HCr | exact Htn' | reflexivity | lia
          | rewrite bytes_le_to_Z_le4, unsigned_lit by lia; lia
          | eassumption | eassumption | eassumption | eassumption | eassumption
          | exact Lj | exact Lj2 ].
      + (* the flag word goes in *)
        cbv iota. zify_cond Hg.
        assert (Hb : n + 4 <= 4096) by (revert Hg; Z.div_mod_to_equations; lia).
        sb_ok (bv_unsigned a0) n.
        zstep. zstep. zstep. store_done.
        sb_ok (bv_unsigned a0) (n + 1).
        zstep. store_done.
        sb_ok (bv_unsigned a0) (n + 2).
        zstep. store_done.
        sb_ok (bv_unsigned a0) (n + 3).
        zstep. store_done.
        zstep. rewrite (ld_cb tn Ltn), Htn'.
        zstep. zstep. zstep. zstep. zstep. if_cases Hg2.
        * (* the trailing zero word goes in too *)
          cbv iota. zify_cond Hg2.
          assert (Hb2 : n + 8 <= 4096) by (revert Hg2; Z.div_mod_to_equations; lia).
          sb_ok (bv_unsigned a0) (n + 4).
          zstep. zstep. store_done.
          sb_ok (bv_unsigned a0) (n + 5).
          zstep. store_done.
          sb_ok (bv_unsigned a0) (n + 6).
          zstep. store_done.
          sb_ok (bv_unsigned a0) (n + 7).
          zstep. store_done.
          zstep. zstep. zstep.
          eapply KBody;
            [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
            | | lia ].
          match goal with
          | HX : rw_cells rsegs ?mm (bv_unsigned a0 + 4096) [?c0; ?c1; CB 4 pad] |- _ =>
              pose proof (cells_nw mm (bv_unsigned a0 + 4096) c0 c1 pad HX
                            eq_refl eq_refl I Ltf Lpd) as HCr
          end.
          cbn [cbytes] in HCr.
          eapply nest_intro;
            [ eassumption | exact HCr
            | rewrite bytes_le_to_Z_le8, unsigned_lit by lia; reflexivity
            | exact Htf' | lia | lia
            | eassumption | eassumption | eassumption | eassumption | eassumption
            | exact Lj | exact Lj2 ].
        * (* the trailing zero word does not fit: w->full is raised *)
          cbv iota. zify_cond Hg2.
          assert (Hb2 : 4089 <= n) by (revert Hg2; Z.div_mod_to_equations; lia).
          zstep. zstep. zstep.
          eapply KBody;
            [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
            | | lia ].
          match goal with
          | HX : rw_cells rsegs ?mm (bv_unsigned a0 + 4096) [?c0; ?c1; CB 4 pad] |- _ =>
              pose proof (cells_nw mm (bv_unsigned a0 + 4096) c0 c1 pad HX
                            eq_refl eq_refl I I Lpd) as HCr
          end.
          cbn [cbytes] in HCr.
          eapply nest_intro;
            [ eassumption | exact HCr
            | rewrite bytes_le_to_Z_le8, unsigned_lit by lia; reflexivity
            | reflexivity | lia
            | rewrite bytes_le_to_Z_le4, unsigned_lit by lia; lia
            | eassumption | eassumption | eassumption | eassumption | eassumption
            | exact Lj | exact Lj2 ]. }

    (* ================= nl_put16 of the type, 0x15528 ================= *)
    assert (KPut2 : forall (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                            s2' s3' s4' t3' t4' t5' t6' : word)
                           (m' : word -> option byte) (n f : Z) (j j2 : list byte),
      s0' = a0 -> s2' = Z_to_bv 64 (bv_unsigned a0 + 4096) -> a0' = Z_to_bv 64 n ->
      s3' = Z_to_bv 64 (bv_unsigned a0 + nw_n bs0) -> s4' = Z_to_bv 64 (nw_n bs0) ->
      s1' = a2 -> a2' = Z_to_bv 64 (-4093) ->
      nest m m' (bv_unsigned a0) lo (bv_unsigned sp) n f s4 s3 s2 s1 s0 ra j j2 ->
      nw_n bs0 <= n ->
      evt rsegs Q (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0' t1' t2' s0' s1'
                           a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4'
                           s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F (Z_to_bv 64 0x15528) fc None m' (seg_rom rsegs))).
    { intros ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6'
             m' n f j j2 Es0 Es2 Ea0 Es3 Es4 Es1 Ea2 HN HLE. subst s0' s2' a0' s3' s4' s1' a2'.
      destruct HN as (SW' & (tn & tf & pad & HC' & Htn' & Htf') & HNb & HFb &
                      MU' & WM' & MI' & ST' & Lj & Lj2 & FR').
      assert (Ltn : length tn = 8%nat) by (destruct HC' as [[Hwf _] _]; cbn in Hwf; tauto).
      assert (Ltf : length tf = 4%nat) by (destruct HC' as [[Hwf _] _]; cbn in Hwf; tauto).
      assert (Lpd : length pad = 4%nat) by (destruct HC' as [[Hwf _] _]; cbn in Hwf; tauto).
      zstep. zstep. zstep. zstep. zstep. if_cases Hg.
      + (* w->n + 2 > 4096: w->full is raised and the type is not written *)
        cbv iota. zify_cond Hg.
        assert (Hb : 4095 <= n) by (revert Hg; Z.div_mod_to_equations; lia).
        zstep. zstep. zstep.
        eapply KPut4;
          [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
          | reflexivity | | exact HLE ].
        match goal with
        | HX : rw_cells rsegs ?mm (bv_unsigned a0 + 4096) [?c0; ?c1; CB 4 pad] |- _ =>
            pose proof (cells_nw mm (bv_unsigned a0 + 4096) c0 c1 pad HX
                          eq_refl eq_refl Ltn I Lpd) as HCr
        end.
        cbn [cbytes] in HCr.
        eapply nest_intro;
          [ eassumption | exact HCr | exact Htn' | reflexivity | lia
          | rewrite bytes_le_to_Z_le4, unsigned_lit by lia; lia
          | eassumption | eassumption | eassumption | eassumption | eassumption
          | exact Lj | exact Lj2 ].
      + (* the type goes in *)
        cbv iota. zify_cond Hg.
        assert (Hb : n + 2 <= 4096) by (revert Hg; Z.div_mod_to_equations; lia).
        sb_ok (bv_unsigned a0) n.
        zstep. zstep. zstep. store_done.
        sb_ok (bv_unsigned a0) (n + 1).
        zstep. store_done.
        zstep. rewrite (ld_cb tn Ltn), Htn'.
        zstep. zstep. zstep. zstep. zstep. if_cases Hg2.
        * (* the two padding bytes of the type word go in too *)
          cbv iota. zify_cond Hg2.
          assert (Hb2 : n + 4 <= 4096) by (revert Hg2; Z.div_mod_to_equations; lia).
          sb_ok (bv_unsigned a0) (n + 2).
          zstep. zstep. store_done.
          sb_ok (bv_unsigned a0) (n + 3).
          zstep. store_done.
          zstep. zstep. zstep.
          eapply KPut4;
            [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
            | reflexivity | | lia ].
          match goal with
          | HX : rw_cells rsegs ?mm (bv_unsigned a0 + 4096) [?c0; ?c1; CB 4 pad] |- _ =>
              pose proof (cells_nw mm (bv_unsigned a0 + 4096) c0 c1 pad HX
                            eq_refl eq_refl I Ltf Lpd) as HCr
          end.
          cbn [cbytes] in HCr.
          eapply nest_intro;
            [ eassumption | exact HCr
            | rewrite bytes_le_to_Z_le8, unsigned_lit by lia; reflexivity
            | exact Htf' | lia | lia
            | eassumption | eassumption | eassumption | eassumption | eassumption
            | exact Lj | exact Lj2 ].
        * (* w->n + 4 > 4096 after the type: w->full is raised *)
          cbv iota. zify_cond Hg2.
          assert (Hb2 : 4093 <= n) by (revert Hg2; Z.div_mod_to_equations; lia).
          zstep. zstep. zstep.
          eapply KPut4;
            [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
            | reflexivity | | lia ].
          match goal with
          | HX : rw_cells rsegs ?mm (bv_unsigned a0 + 4096) [?c0; ?c1; CB 4 pad] |- _ =>
              pose proof (cells_nw mm (bv_unsigned a0 + 4096) c0 c1 pad HX
                            eq_refl eq_refl I I Lpd) as HCr
          end.
          cbn [cbytes] in HCr.
          eapply nest_intro;
            [ eassumption | exact HCr
            | rewrite bytes_le_to_Z_le8, unsigned_lit by lia; reflexivity
            | reflexivity | lia
            | rewrite bytes_le_to_Z_le4, unsigned_lit by lia; lia
            | eassumption | eassumption | eassumption | eassumption | eassumption
            | exact Lj | exact Lj2 ]. }

    (* ================= the entry block, 0x154b4 ================= *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep. zstep.
    rewrite (ld_cb tn0 Ltn0), Htn.
    zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases Hg.
    + (* w->n + 4 <= 4096: the four bytes of the length word go in *)
      cbv iota. zify_cond Hg.
      assert (Hn4 : nw_n bs0 + 4 <= 4096) by (revert Hg; Z.div_mod_to_equations; lia).
      sb_ok (bv_unsigned a0) (nw_n bs0).
      zstep. store_done.
      sb_ok (bv_unsigned a0) (nw_n bs0 + 1).
      zstep. store_done.
      sb_ok (bv_unsigned a0) (nw_n bs0 + 2).
      zstep. store_done.
      sb_ok (bv_unsigned a0) (nw_n bs0 + 3).
      zstep. store_done.
      zstep. rewrite (ld_cb tn0 Ltn0), Htn.
      zstep. zstep.
      split_frame.
      eapply KPut2;
        [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | reflexivity | | lia ].
      match goal with
      | HX : rw_cells rsegs ?mm (bv_unsigned a0 + 4096) [?c0; ?c1; CB 4 pad0] |- _ =>
          pose proof (cells_nw mm (bv_unsigned a0 + 4096) c0 c1 pad0 HX
                        eq_refl eq_refl I Ltf0 Lpd0) as HCr
      end.
      cbn [cbytes] in HCr.
      eapply nest_intro;
        [ eassumption | exact HCr
        | rewrite bytes_le_to_Z_le8, unsigned_lit by lia; reflexivity
        | exact Htf | lia | lia
        | eassumption | eassumption | eassumption | eassumption | eassumption
        | rewrite firstn_length; lia | rewrite firstn_length, skipn_length; lia ].
    + (* the length word does not fit: w->full is raised *)
      cbv iota. zify_cond Hg.
      assert (Hn4 : 4093 <= nw_n bs0) by (revert Hg; Z.div_mod_to_equations; lia).
      zstep. zstep. zstep. zstep.
      split_frame.
      eapply KPut2;
        [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | reflexivity | | lia ].
      match goal with
      | HX : rw_cells rsegs ?mm (bv_unsigned a0 + 4096) [?c0; ?c1; CB 4 pad0] |- _ =>
          pose proof (cells_nw mm (bv_unsigned a0 + 4096) c0 c1 pad0 HX
                        eq_refl eq_refl Ltn0 I Lpd0) as HCr
      end.
      cbn [cbytes] in HCr.
      eapply nest_intro;
        [ eassumption | exact HCr | exact Htn | reflexivity | lia
        | rewrite bytes_le_to_Z_le4, unsigned_lit by lia; lia
        | eassumption | eassumption | eassumption | eassumption | eassumption
        | rewrite firstn_length; lia | rewrite firstn_length, skipn_length; lia ].
Qed.

(* the two libc callees this walk uses have their own walks in the tree *)
Theorem nl_error_holds : nl_error_contract.
Proof. apply nl_error_holds_h; [exact memcpy_holds | exact memset_holds]. Qed.

Print Assumptions nl_error_holds.
