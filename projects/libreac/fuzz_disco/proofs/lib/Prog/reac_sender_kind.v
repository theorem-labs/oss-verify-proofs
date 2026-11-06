From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_rate_snap_c reac_rival_kind_of_c reac_master_only_cadence_ns_c reac_sender_kind_c.
Import ListNotations.
Open Scope Z_scope.

Lemma bytes_at_read0 : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof H as (H0 & H1 & _).
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a bs 0 (length bs) H) by lia.
  f_equal. apply firstn_all.
Qed.

Lemma sx32_lit : forall v, -2^31 <= v < 2^31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. f_equal. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with 2147483648 by reflexivity.
  replace (bv_modulus 32) with 4294967296 by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma sx32_u : forall c, 0 <= c < 2^32 -> sx32 (Z_to_bv 64 c) = Z_to_bv 64 (c - 2^32 * (c / 2^31)).
Proof.
  intros c Hc. unfold sx32. f_equal. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with 2147483648 by reflexivity.
  replace (bv_modulus 32) with 4294967296 by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma zxb_lit : forall d, 0 <= d < 2^8 -> zxb (Z_to_bv 8 d) = Z_to_bv 64 d.
Proof.
  intros d Hd. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hd.
Qed.

Lemma addiw_m1_ltu : forall r, -2^31 <= r < 2^31 ->
  bv_ltu (Z_to_bv 64 1) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 r) + -1))) = negb ((r =? 1) || (r =? 2)).
Proof.
  intros r Hr. unfold bv_ltu. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with 2147483648 by reflexivity.
  replace (bv_modulus 32) with 4294967296 by reflexivity.
  destruct (Z.eqb_spec r 1) as [-> | N1]; [vm_compute; reflexivity |].
  destruct (Z.eqb_spec r 2) as [-> | N2]; [vm_compute; reflexivity |].
  cbn [orb negb]. apply Z.ltb_lt. Z.div_mod_to_equations. lia.
Qed.

Ltac zc HC := unfold bv_eqb, bv_ltu in HC; rewrite ?unsigned_lit_wrap in HC; zify_bool HC; Z.div_mod_to_equations; lia.

Ltac set_a0 V :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode _ _ (TNode _ _ (TNode (TNode _ (Some ?X) _) _ _))) _ _ _ _ _ _) => replace X with V
  end.

Theorem reac_sender_kind_holds :
  reac_rival_kind_of_contract -> reac_master_only_cadence_ns_contract -> reac_sender_kind_contract.
Proof.
  intros RK CADH. unfold reac_sender_kind_contract, REAC_SENDER_KIND.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    e now fps r d s c fs lo E0 He H8 E1 Hnow E2 Hfps HF ST HLO HRT BR B6 B3.
  subst a0 a1 a2.
  unfold RT, A_P6000, A_P3837, RATES in HRT, BR, B6, B3.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof ST as (Hlo & Hhi & _).
  step.
  if_cases HC.
  { assert (E0 : e = 0) by zc HC. subst e. clear HC.
    step. step. step.
    apply evt_done. do 5 eexists. exists F, m.
    split; [reflexivity |].
    split; [apply munch_refl |]. split; [apply wmono_refl |]. split; [exact ST |].
    intros k _ _ _. reflexivity. }
  assert (Ne : e <> 0) by zc HC. clear HC.
  destruct (HF Ne) as (Hr & Hd & Hs & Hc & Hfs & B8 & B12 & B16 & B20 & B32). clear HF.
  pose proof (bytes_at_read0 m _ _ B8) as R8. change (ov_read_bytes rsegs m (wa (e + 8)) 4 = Some (le4 (Z_to_bv 64 r))) in R8.
  pose proof (bytes_at_read0 m _ _ B12) as R12. change (ov_read_bytes rsegs m (wa (e + 12)) 1 = Some [Z_to_bv 8 d]) in R12.
  pose proof (bytes_at_read0 m _ _ B20) as R20. change (ov_read_bytes rsegs m (wa (e + 20)) 4 = Some (le4 (Z_to_bv 64 c))) in R20.
  pose proof (bytes_at_read0 m _ _ B32) as R32. change (ov_read_bytes rsegs m (wa (e + 32)) 8 = Some (le8 (Z_to_bv 64 fs))) in R32.
  step. rewrite (zxb_lit d) by lia. step.
  if_cases HC1.
  { assert (D0 : d <> 0) by zc HC1. clear HC1.
    step.
    assert (HM : reac_sender_kind_model e r d s c fs now = reac_rival_kind_model d r s c).
    { unfold reac_sender_kind_model. rewrite (proj2 (Z.eqb_neq e 0) Ne), (proj2 (Z.eqb_neq d 0) D0). reflexivity. }
    rewrite HM.
    eapply evt_mono.
    { eapply RK with (e := e) (r := r) (d := d) (s := s) (c := c);
        [reflexivity | lia | exact H8 | intros _; exact (conj Hr (conj Hd (conj Hs (conj Hc (conj B8 (conj B12 (conj B16 B20)))))))]. }
    intros ms' (a1' & a2' & a3' & a4' & a5' & Eq). subst ms'.
    rewrite (proj2 (Z.eqb_neq e 0) Ne) in *. cbv iota.
    exists a1', a2', a3', a4', a5', F, m.
    split; [reflexivity |].
    split; [apply munch_refl |]. split; [apply wmono_refl |]. split; [exact ST |].
    intros k _ _ _. reflexivity. }
  assert (D0 : d = 0) by zc HC1. clear HC1.
  step. rewrite (sx32_lit r) by lia. step. step. step.
  rewrite (addiw_m1_ltu r) by lia.
  destruct ((r =? 1) || (r =? 2)) eqn:HR; cbn [negb]; cbv iota.
  { step.
    assert (HM : reac_sender_kind_model e r d s c fs now = reac_rival_kind_model d r s c).
    { unfold reac_sender_kind_model. rewrite (proj2 (Z.eqb_neq e 0) Ne), (proj2 (Z.eqb_eq d 0) D0).
      cbn [negb orb]. rewrite HR. reflexivity. }
    rewrite HM.
    eapply evt_mono.
    { eapply RK with (e := e) (r := r) (d := d) (s := s) (c := c);
        [reflexivity | lia | exact H8 | intros _; exact (conj Hr (conj Hd (conj Hs (conj Hc (conj B8 (conj B12 (conj B16 B20)))))))]. }
    intros ms' (a1' & a2' & a3' & a4' & a5' & Eq). subst ms'.
    rewrite (proj2 (Z.eqb_neq e 0) Ne) in *. cbv iota.
    exists a1', a2', a3', a4', a5', F, m.
    split; [reflexivity |].
    split; [apply munch_refl |]. split; [apply wmono_refl |]. split; [exact ST |].
    intros k _ _ _. reflexivity. }
  assert (HM0 : reac_sender_kind_model e r d s c fs now =
                (if c =? 0 then 3 else if now <=? fs then 3 else if now - fs <? 10^9 then 3 else 2)).
  { unfold reac_sender_kind_model. rewrite (proj2 (Z.eqb_neq e 0) Ne), (proj2 (Z.eqb_eq d 0) D0).
    cbn [negb orb]. rewrite HR. reflexivity. }
  rewrite HM0. clear HM0.
  step. rewrite (sx32_u c) by lia. step. step.
  if_cases HC3.
  { assert (C0 : c = 0) by zc HC3. clear HC3. subst c.
    step. step.
    apply evt_done. do 5 eexists. exists F, m.
    split; [reflexivity |].
    split; [apply munch_refl |]. split; [apply wmono_refl |]. split; [exact ST |].
    intros k _ _ _. reflexivity. }
  assert (C0 : c <> 0) by zc HC3. clear HC3.
  rewrite (proj2 (Z.eqb_neq c 0) C0). cbv iota.
  step. step.
  if_cases HC4.
  { assert (T0 : now <= fs) by zc HC4. clear HC4.
    rewrite (proj2 (Z.leb_le now fs) T0). cbv iota.
    step. step.
    apply evt_done. do 5 eexists. exists F, m.
    split; [reflexivity |].
    split; [apply munch_refl |]. split; [apply wmono_refl |]. split; [exact ST |].
    intros k _ _ _. reflexivity. }
  assert (T0 : fs < now) by zc HC4. clear HC4.
  rewrite (proj2 (Z.leb_gt now fs) T0). cbv iota.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  step. step. step. step. step. step.
  eapply evt_cut.
  { eapply CADH with (fps := fps) (lo := lo).
    all: first [ reflexivity | lia | eassumption
               | rewrite (unsigned_lit (bv_unsigned sp + -16)) by lia; first [eassumption | lia] ]. }
  intros ms' (a1' & a2' & a3' & a4' & a5' & F' & m2 & Eq & MUc & WMc & STc & FK). subst ms'.
  rewrite (unsigned_lit (bv_unsigned sp + -16)) in MUc, STc by lia.
  rewrite (ret_pc_even 91844) by (first [lia | reflexivity]).
  lazymatch goal with FR0 : rw_cells rsegs ?m1 (bv_unsigned sp + -16) ?cs |- _ =>
    pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR0 MUc WMc ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR2;
    pose proof (munch_trans _ m m1 m2 MU ltac:(eapply munch_weaken; [| exact MUc];
      unfold sub_fp; cbn [outside]; intros x [H1 _]; split; [lia | exact I])) as MU2;
    pose proof (wmono_trans rsegs m m1 m2 WM WMc) as WM2;
    clear FR0 MU WM ST MUc WMc
  end.
  rename STc into ST.
  step. step. step. step. step.
  release_frame FR2 ST (bv_unsigned sp).
  step. step. step.
  set_a0 (Z_to_bv 64 (if now - fs <? 10 ^ 9 then 3 else 2)).
  - apply evt_done. do 5 eexists. exists F', m2.
    split; [reflexivity |]. split; [exact MU2 |]. split; [exact WM2 |]. split; [exact ST | exact FK].
  - unfold v_sltu, c_ltu, bv_ltu.
    rewrite (unsigned_lit now), (unsigned_lit fs) by lia. rewrite (unsigned_lit (now - fs)) by lia.
    replace (bv_unsigned (Z_to_bv 64 (10 ^ 9))) with (10 ^ 9) by reflexivity.
    destruct (now - fs <? 10 ^ 9); first [reflexivity | apply bv_eq; vm_compute; reflexivity].
Qed.
