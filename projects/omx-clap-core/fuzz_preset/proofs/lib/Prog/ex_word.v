From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import strlen_c bcmp_c ex_word_c.
Import ListNotations.
Open Scope Z_scope.

Local Ltac not_in0 :=
  let H := fresh in intro H; cbn [map In] in H;
  repeat (destruct H as [H|H]; [apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate|]); exact H.

Local Ltac lit_case MI :=
  lazymatch goal with
  | |- exists sl, bytes_at rsegs _ ?w (?W ++ _ :: sl) /\ _ =>
      let n := eval vm_compute in (Z.to_nat ((- (w + Z.of_nat (length W) + 1)) mod 8)) in
      let s := eval vm_compute in (image_bytes rsegs (w + Z.of_nat (length W) + 1) n) in
      lazymatch s with
      | Some ?l => exists l
      end;
      split; [ apply (ro_bytes_at rsegs); [ exact MI | lia | cbn; lia | apply (ro_bytes_b_sound rsegs); vm_compute; reflexivity ] | ];
      split; [ not_in0 | ];
      split; [ vm_compute; congruence | ];
      split; [ cbn; lia | lia ]
  end.

Lemma ex_word_lit_facts : forall m w W, mem_inv rsegs m -> ex_word_lit w W ->
  exists sl, bytes_at rsegs m w (W ++ Z_to_bv 8 0 :: sl) /\ ~ In (Z_to_bv 8 0) W /\
    (- (w + Z.of_nat (length W) + 1)) mod 8 <= Z.of_nat (length sl) /\
    (4 <= length W <= 5)%nat /\ 0x10000 <= w <= 0x10400.
Proof.
  intros m w W MI [[-> ->]|[[-> ->]|[-> ->]]]; unfold LIT_TRUE, LIT_FALSE, LIT_NULL; lit_case MI.
Qed.

Lemma ex_word_le8_lo : forall a b : word, firstn 8 (skipn (Z.to_nat 0) (le8 a ++ le8 b)) = le8 a.
Proof.
  intros. change (Z.to_nat 0) with 0%nat. rewrite skipn_O, firstn_app, length_le8, Nat.sub_diag, firstn_O, app_nil_r.
  apply firstn_all2. rewrite length_le8. lia.
Qed.

Lemma ex_word_le8_hi : forall a b : word, firstn 8 (skipn (Z.to_nat 8) (le8 a ++ le8 b)) = le8 b.
Proof.
  intros. change (Z.to_nat 8) with 8%nat. rewrite skipn_app, length_le8, Nat.sub_diag, skipn_O.
  replace (skipn 8 (le8 a)) with (@nil byte) by (symmetry; apply skipn_all2; rewrite length_le8; lia).
  cbn [app]. apply firstn_all2. rewrite length_le8. lia.
Qed.

Lemma ex_word_ltu : forall E P n, 0 <= P <= E -> E < 2^64 -> 0 <= n < 2^64 ->
  bv_ltu (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 E) - bv_unsigned (Z_to_bv 64 P))) (Z_to_bv 64 n) = (E - P <? n).
Proof.
  intros E P n HP HE Hn. unfold bv_ltu.
  rewrite (unsigned_lit E) by lia. rewrite (unsigned_lit P) by lia.
  rewrite (unsigned_lit (E - P)) by lia. rewrite (unsigned_lit n) by lia. reflexivity.
Qed.

Lemma ex_word_memcmp : forall n l r v, memcmp_model l r n = Some v ->
  -255 <= v <= 255 /\ (v = 0 <-> firstn n l = firstn n r).
Proof.
  induction n as [|n IH]; intros l r v H; cbn in H.
  - injection H as <-. cbn. split; [lia | tauto].
  - destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|].
    pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
    unfold bv_modulus in Ra, Rb. change (2 ^ Z.of_N 8) with 256 in Ra, Rb.
    revert H. destruct (bv_unsigned a =? bv_unsigned b) eqn:E; intros H.
    + apply Z.eqb_eq in E. destruct (IH l r v H) as [R I]. split; [exact R|].
      assert (a = b) by (apply bv_eq; exact E). subst b. cbn [firstn].
      rewrite I. split; [intros ->; reflexivity | intros Hc; injection Hc; auto].
    + apply Z.eqb_neq in E. injection H as <-. split; [lia|]. cbn [firstn].
      split; [lia | intros Hc; injection Hc as Hab _; subst; contradiction].
Qed.

Lemma ex_word_skipn : forall m a bs k, bytes_at rsegs m a bs -> (k <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (skipn k bs).
Proof.
  intros m a bs k H Hk. rewrite <- (firstn_skipn k bs) in H.
  apply bytes_at_app in H. destruct H as [_ H]. rewrite firstn_length_le in H by lia. exact H.
Qed.

Lemma ex_word_eqz : forall c, -2^63 <= c < 2^63 -> bv_eqb (Z_to_bv 64 c) (Z_to_bv 64 0) = (c =? 0).
Proof.
  intros c Hc. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  apply Bool.eq_iff_eq_true. rewrite !Z.eqb_eq. split; intro H; [|subst; reflexivity].
  Z.div_mod_to_equations. lia.
Qed.

Lemma ex_word_sx : forall t ty, 0 <= t < 2^32 -> 0 <= ty <= 2 ->
  bv_eqb (sx32 (Z_to_bv 64 t)) (Z_to_bv 64 ty) = (t =? ty).
Proof.
  intros t ty Ht Hy. unfold bv_eqb, sx32. rewrite (unsigned_lit t) by lia. rewrite !unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  apply Bool.eq_iff_eq_true. rewrite !Z.eqb_eq. split; intro H; [|subst]; Z.div_mod_to_equations; lia.
Qed.

Lemma ex_word_v0 : forall v, 0 <= v < 2^64 -> v <> 0 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = false.
Proof. intros v Hv H0. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. exact H0. Qed.

Local Ltac cur_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

Local Ltac run := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step end).

Local Ltac widen MU W' :=
  apply (munch_weaken _ W') in MU; [ | unfold sub_fp; cbn [outside]; intros ? HO; intuition lia ].

Local Ltac wstore NP :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    let E := addr_expr a in
    change (write_to_mem m a bs) with (write_to_mem m (wa E) bs);
    pose proof (bytes_at_write_same segs m E bs ltac:(lia) ltac:(simpl_sizes; lia)) as NP;
    lazymatch goal with
    | HI : mem_inv segs m, HS : store_ok segs m _ _ = true |- _ =>
        apply (mem_inv_store segs m (wa E) bs) in HI; [ | exact HS ]; clear HS
    end;
    transport_chunks segs m E bs;
    footprint_after_store segs m E bs;
    let m' := fresh "mw" in
    set (m' := write_to_mem m (wa E) bs) in *;
    clearbody m'
  end.

Local Ltac tail_ok q WQ :=
  step; step;
  let mm := cur_mem in
  let SQ := fresh "SQ" in
  pose proof (wr_at_store_ok rsegs mm q 8 0 8%nat WQ ltac:(lia) ltac:(lia)) as SQ;
  rewrite Z.add_0_r in SQ;
  step;
  let NP := fresh "NP" in wstore NP;
  run.

Theorem ex_word_holds : strlen_contract -> bcmp_contract -> ex_word_contract.
Proof.
  intros STRLEN BCMP.
  unfold ex_word_contract, EX_WORD, EX_WORD_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo q x0 i0 w ty v t x W -> -> -> -> LIT TY HQ WQ WD HX XE HI HV MI ST LO OQ OX.
  unfold ex_word_off, EX_WORD_K in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (bytes_at_bound _ _ _ _ HQ) as BQ. rewrite length_app, !length_le8 in BQ.
  pose proof (bytes_at_bound _ _ _ _ HX) as BX.
  pose proof WD as (BD & BD' & _).
  carve_frame 64%nat ST.
  do 14 step.
  destruct (ex_word_lit_facts _ w W MI LIT) as (sl & BW & NZ & SL & LW & WR).
  step.
  eapply evt_cut.
  { eapply STRLEN with (str := W) (slack := sl).
    - rewrite unsigned_lit by lia. exact BW.
    - exact NZ.
    - rewrite unsigned_lit by lia. exact SL.
    - exact MI. }
  post_call rsegs m1.
  step.
  let mm := cur_mem in
  assert (RP : ov_read_bytes rsegs mm (wa (q + 0)) 8 = Some (le8 (Z_to_bv 64 (x0 + i0))))
    by (rewrite (bytes_at_read rsegs mm q _ 0 8 HQ) by (rewrite ?length_app, ?length_le8; lia); f_equal; apply ex_word_le8_lo);
  assert (RE : ov_read_bytes rsegs mm (wa (q + 8)) 8 = Some (le8 (Z_to_bv 64 (x0 + Z.of_nat (length x)))))
    by (rewrite (bytes_at_read rsegs mm q _ 8 8 HQ) by (rewrite ?length_app, ?length_le8; lia); f_equal; apply ex_word_le8_hi).
  step. step. step. step. step.
  if_cases HC.
  - rewrite ex_word_ltu in HC by lia. apply Z.ltb_lt in HC.
    run.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. do 16 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|].
    right. split; [intros [HM _]; lia | split; [reflexivity | assumption]].
  - rewrite ex_word_ltu in HC by lia. apply Z.ltb_ge in HC.
    step. step. step. step.
    destruct (memcmp_model_total (skipn (Z.to_nat i0) x) W (length W)) as [cv CV];
      [ rewrite length_skipn; lia | lia | ].
    eapply evt_cut.
    { eapply BCMP with (ls := skipn (Z.to_nat i0) x) (rs := W) (v := cv).
      - rewrite unsigned_lit by lia. pose proof (ex_word_skipn _ _ _ (Z.to_nat i0) HX ltac:(lia)) as HS.
        rewrite Z2Nat.id in HS by lia. exact HS.
      - rewrite unsigned_lit by lia. exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) BW)).
      - rewrite unsigned_lit by lia. rewrite Nat2Z.id. exact CV.
      - exact MI0. }
    post_call rsegs x15.
    step.
    pose proof (ex_word_memcmp _ _ _ _ CV) as [CR CE]. rewrite firstn_all in CE.
    rewrite (ex_word_eqz cv) by lia.
    destruct (Z.eqb_spec cv 0) as [C0|C0]; cbn [negb].
    2: { run. release_frame FR ST (bv_unsigned sp).
         apply evt_done. do 16 eexists. split; [reflexivity|].
         split; [assumption|]. split; [assumption|]. split; [assumption|].
         right. split; [intros [_ HM]; apply C0, CE, HM | split; [reflexivity | assumption]]. }
    assert (HM : ex_word_match x i0 W) by (split; [lia | apply CE, C0]).
    step.
    destruct (Z.eq_dec v 0) as [V0|V0].
    + subst v. if_true.
      widen MU [(bv_unsigned sp + -64, bv_unsigned sp); (q, q + 8)].
      tail_ok q WQ.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. do 16 eexists. split; [reflexivity|].
      split; [assumption|]. split; [assumption|]. split; [assumption|].
      left. split; [exact HM|]. split; [reflexivity|]. split; [exact NP|].
      right. split; [left; reflexivity | exact MU].
    + destruct (HV V0) as (BV & TR & OV).
      pose proof (bytes_at_bound _ _ _ _ BV) as BB. rewrite length_le4 in BB.
      if_false_by (ex_word_v0 v ltac:(lia) V0).
      let mm := cur_mem in
      pose proof (bytes_at_transport rsegs _ _ _ _ _ BV MU ltac:(cbn [disjoint_from]; rewrite length_le4; split; [lia | exact I])) as BV';
      assert (RV : ov_read_bytes rsegs mm (wa (v + 0)) 4 = Some (le4 (Z_to_bv 64 t)))
        by (rewrite (bytes_at_read rsegs mm v _ 0 4 BV') by (rewrite ?length_le4; lia); reflexivity).
      step. step.
      destruct (Z.eq_dec t ty) as [T0|T0].
      * if_true_by (eq_trans (ex_word_sx t ty TR TY) (proj2 (Z.eqb_eq t ty) T0)).
        widen MU [(bv_unsigned sp + -64, bv_unsigned sp); (q, q + 8)].
        tail_ok q WQ.
        release_frame FR ST (bv_unsigned sp).
        apply evt_done. do 16 eexists. split; [reflexivity|].
        split; [assumption|]. split; [assumption|]. split; [assumption|].
        left. split; [exact HM|]. split; [reflexivity|]. split; [exact NP|].
        right. split; [right; exact T0 | exact MU].
      * if_false_by (eq_trans (ex_word_sx t ty TR TY) (proj2 (Z.eqb_neq t ty) T0)).
        step.
        widen MU [(bv_unsigned sp + -64, bv_unsigned sp); (q, q + 8); (q + 32, q + 36)].
        let mm := cur_mem in
        pose proof (wr_at_store_ok rsegs mm (q + 32) 4 0 4%nat WD ltac:(lia) ltac:(lia)) as SD;
        rewrite Z.add_0_r in SD.
        step.
        wstore ND.
        tail_ok q WQ.
        release_frame FR ST (bv_unsigned sp).
        apply evt_done. do 16 eexists. split; [reflexivity|].
        split; [assumption|]. split; [assumption|]. split; [assumption|].
        left. split; [exact HM|]. split; [reflexivity|]. split; [exact NP|].
        left. split; [exact V0|]. split; [exact T0|]. split; [exact ND | exact MU].
Qed.
