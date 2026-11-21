(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Lib Require Import ITree Nodes Decode Image CTree.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require Import Prelim Monad MSafe MSafeP CMonad CLogic STree Malloc Stdio PState HarnessC Adapter AdapterC Driver DriverC Prog ProgC
  KInv KLink KEv KEvP StepB ModelInv FreshIface TargetSafeC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Common Require Import Keeps.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require Import RSim PTotal.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import ExFlushIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section DriverSpecC.
Context {St ptr : Type}.
Variable io : IOStyle St.
Variable drv_malloc : Z -> Monad.M St (option ptr).
Variable drv_free : ptr -> Monad.M St unit.
Variable read_stage : Z.
Variable alloc_init : Z -> Monad.M St unit.
Variable run : Z -> list Z -> MC St Z.
Variable alloc_count : Monad.M St Z.
Variable own : list (ptr * Z) -> Z -> assn St.

Hypothesis Hm : forall X k n s0, 0 <= n <= 2^62 -> FPRE X k n ->
  mspecP (fun s mo => s = s0 /\ own X k s mo) (drv_malloc n)
         (fun r s mo => match r with Some p => own ((p, n) :: X) (k + 1) s mo /\ n < 2^63 | None => False end).
Hypothesis Hf : forall X k p n, mspecP (own ((p, n) :: X) k) (drv_free p) (fun _ => own X k).
Hypothesis Hperm : forall X Y k s mo, Permutation X Y -> own X k s mo -> own Y k s mo.
Hypothesis Hkle : forall X k k' s mo, k <= k' -> own X k s mo -> own X k' s mo.
Hypothesis Hdiag : forall X k d, diag_ok d -> mspecP (own X k) (io_diag io d) (fun _ => own X k).
Hypothesis Hexit : forall X k, mspecP (own X k) (io_exit io) (fun _ => own X k).
Hypothesis Hinit : forall X k bm, mspecP (own X k) (alloc_init bm) (fun _ => own X k).
Hypothesis Hcount : forall X k, mspecP (own X k) alloc_count (fun _ => own X k).
Hypothesis Hrun : forall X k cfg payload, zlength payload <= MAX_INPUT -> TR_ENTRY X k ->
  cspecP (own X k) (run cfg payload) (fun _ s mo => exists LK k', own (LK ++ X) k' s mo /\ 0 <= k').
Hypothesis Hown_minv : forall X k s mo, own X k s mo -> minv mo /\ m_halted mo = None.
Hypothesis Hown_fds : forall X k s mo mo', own X k s mo ->
  m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> own X k s mo'.

Local Ltac retP := apply mspecP_ret; intros ? ? HH; exact HH.

Lemma own_after_node : forall X k s mo n rsp mo' evs,
  own X k s mo -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo -> own X k s mo'.
Proof.
  intros X k s mo n rsp mo' evs Ho Hst Hvm. destruct (Hown_minv _ _ _ _ Ho) as [Hmi Hh].
  destruct (minv_preserved n mo rsp mo' evs Hmi Hh Hst) as [Hh' Hmi']. eapply Hown_fds; eauto.
Qed.

Lemma malloc_specP : forall X k n, 0 <= n <= 2^62 -> FPRE X k n ->
  mspecP (own X k) (drv_malloc n) (fun r s mo => match r with Some p => own ((p, n) :: X) (k + 1) s mo /\ n < 2^63 | None => False end).
Proof.
  intros X k n Hn HF. apply mspecP_pointwise. intros s0 mo0 H0.
  eapply mspecP_pre; [apply (Hm X k n s0 Hn HF)|]. intros s mo [-> ->]. auto.
Qed.

Definition RDX (X : list (ptr * Z)) : Prop := C31 X = 0 /\ C40 X = 0 /\ C44 X = 0.

Lemma buf_counts : forall X (b : ptr) j, (j <= 10)%nat -> RDX X ->
  C31 ((b, 65536 * 2 ^ Z.of_nat j) :: X) = 0 /\ C40 ((b, 65536 * 2 ^ Z.of_nat j) :: X) = 0 /\ C44 ((b, 65536 * 2 ^ Z.of_nat j) :: X) <= 1.
Proof.
  intros X b j Hj (A & B & C). unfold C31, C40, C44 in *.
  assert (65536 <= 65536 * 2 ^ Z.of_nat j) by (pose proof (Z.pow_pos_nonneg 2 (Z.of_nat j)); nia).
  rewrite !cntr_cons_out by lia. pose proof (cntr_cons_le 65517 74876 b (65536 * 2 ^ Z.of_nat j) X). lia.
Qed.

Definition rd_inv (X : list (ptr * Z)) (k0 : Z) (st : rd_st) : assn St := fun s mo =>
  exists j k, (j <= 10)%nat /\ rd_cap st = 65536 * 2 ^ (Z.of_nat j) /\ k0 <= k <= k0 + 1 + Z.of_nat j
    /\ own ((rd_buf st, rd_cap st) :: X) k s mo /\ zlength (rd_content st) <= rd_cap st.

Definition rd_meas (st : @rd_st ptr) : nat := Z.to_nat (MAX_INPUT + 1 - zlength (rd_content st)).

Lemma read_loop_body_specP : forall X k0 fd path st,
  zlength path <= ARG_MAX_LEN -> 0 <= fd -> RDX X -> 0 <= k0 <= 1 ->
  mspecP (rd_inv X k0 st) (read_loop_body io drv_malloc drv_free read_stage fd path st)
         (fun r s mo => match r with
                        | inl st' => rd_inv X k0 st' s mo /\ (rd_meas st' < rd_meas st)%nat
                        | inr RdExit => exists X' k, own X' k s mo
                        | inr (RdDone buf content) => exists j k, (j <= 10)%nat /\ k0 <= k <= k0 + 11
                                                        /\ own ((buf, 65536 * 2 ^ Z.of_nat j) :: X) k s mo /\ zlength content <= MAX_INPUT
                        end).
Proof.
  intros X k0 fd path st Hpath Hfd HR Hk0. unfold read_loop_body.
  eapply mspecP_bind with
    (Q1 := fun g s mo => match g with
                         | None => exists X' k, own X' k s mo
                         | Some st1 => rd_inv X k0 st1 s mo /\ rd_content st1 = rd_content st /\ zlength (rd_content st) < rd_cap st1
                         end).
  { apply mspecP_if_pre.
    - apply mspecP_if_pre.
      + apply mspecP_pointwise. intros s0 mo0 [[(j & k & _ & _ & _ & Ho & _) _] _].
        eapply mspecP_seq; [eapply mspecP_pre; [apply Hdiag; exact I|]; intros s mo [-> ->]; exact Ho|].
        intros _. apply mspecP_ret. intros s mo Ho'. eexists _, _. exact Ho'.
      + apply mspecP_pointwise. intros s0 mo0 [[(j & k & Hj & Hcap & Hk & Ho0 & Hlen) Heq] Hlt].
        apply Z.eqb_eq in Heq. apply Z.leb_gt in Hlt.
        pose proof (pow2_le_1024 j Hj) as Hp.
        assert (Hj10 : (j < 10)%nat) by (unfold MAX_INPUT in Hlt; assert (j <> 10)%nat by (intros ->; cbn in Hcap; lia); lia).
        eapply mspecP_bind.
        { eapply mspecP_pre; [apply (malloc_specP ((rd_buf st, rd_cap st) :: X) k (rd_cap st * 2)); [lia|]|].
          - unfold FPRE. destruct (buf_counts X (rd_buf st) j Hj HR) as (B1 & B2 & B3). rewrite <- Hcap in B1, B2, B3. lia.
          - intros s mo [-> ->]. exact Ho0. }
        intros [nb|]; cbn beta iota; [| apply mspecP_false].
        apply mspecP_pure. intros _. eapply mspecP_seq.
        { eapply mspecP_pre; [apply (Hf ((nb, rd_cap st * 2) :: X) (k + 1) (rd_buf st) (rd_cap st))|].
          intros s mo Ho. eapply Hperm; [apply perm_swap| exact Ho]. }
        intros _. apply mspecP_ret. intros s mo Ho. cbn. unfold rd_inv. cbn.
        split; [| split; [reflexivity| lia]].
        exists (S j), (k + 1). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. split; [lia|]. split; [lia|]. split; [lia|]. split; [| lia].
        replace (65536 * (2 * 2 ^ Z.of_nat j)) with (rd_cap st * 2) by lia. exact Ho.
    - apply mspecP_ret. intros s mo [(j & k & Hj & Hcap & Hk & Ho & Hlen) Hne]. apply Z.eqb_neq in Hne.
      split; [| split; [reflexivity| lia]]. exists j, k. auto 10. }
  intros [st1|]; cbn beta iota.
  2:{ retP. }
  apply mspecP_pointwise. intros s1 mo1 ((j & k & Hj & Hcap & Hk & Ho & Hlen) & Hct & Hlt).
  pose proof (pow2_le_1024 j Hj) as Hp.
  set (want0 := rd_cap st1 - zlength (rd_content st)).
  set (want := if 65536 <? want0 then 65536 else want0).
  assert (Hwant : 0 < want <= want0 /\ want <= 65536).
  { subst want want0. destruct (Z.ltb_spec 65536 (rd_cap st1 - zlength (rd_content st))); lia. }
  apply mspecP_bind with (Q1 := fun a s mo => s = s1 /\ own ((rd_buf st1, rd_cap st1) :: X) k s mo /\
                       match a with RdErr _ => True | RdData bs => zlength bs <= want end).
  { apply mspecP_sys. intros s mo [-> ->]. split; [exact I|].
    intros rsp mo' evs Hst.
    pose proof (nstep_dec_read fd _ want mo1 rsp mo' evs ltac:(unfold MAX_INPUT, zlength in *; lia) Hst) as (_ & a & Hdec & Ha).
    exists a. split; [exact Hdec|].
    cbn beta. split; [reflexivity|].
    assert (Hvm : m_vmmaps mo' = m_vmmaps mo1).
    { destruct a as [e|bs]; [destruct Ha as [-> _]; reflexivity|].
      destruct Ha as (p & off & data & _ & _ & _ & ->). reflexivity. }
    split; [eapply own_after_node; eauto|].
    destruct a as [e|bs]; [exact I|]. destruct Ha as (p & off & data & _ & _ & -> & _).
    unfold zlength. pose proof (length_file_read_le_count data off want ltac:(unfold zlength, MAX_INPUT in *; lia)). lia. }
  intros [e|bs]; cbn beta iota.
  - eapply mspecP_seq. { eapply mspecP_pre; [apply Hdiag; exact Hpath|]. intros s mo (_ & Ho' & _). exact Ho'. }
    intros _. apply mspecP_ret. intros s mo Ho'. eexists _, _. exact Ho'.
  - apply mspecP_if; intros C.
    + apply mspecP_ret. intros s mo (-> & Ho' & _). exists j, k. split; [exact Hj|]. split; [lia|]. rewrite <- Hcap. split; [exact Ho'|]. rewrite Hct. unfold MAX_INPUT in *. lia.
    + apply mspecP_ret. intros s mo (-> & Ho' & Hbs). apply Nat.eqb_neq in C.
      assert (1 <= zlength bs) by (unfold zlength in *; destruct bs; cbn in *; [congruence|lia]).
      split.
      * unfold rd_inv. cbn. exists j, k. split; [exact Hj|]. split; [exact Hcap|]. split; [lia|]. split; [exact Ho'|].
        rewrite zlength_app, zlength_u8s, Hct. lia.
      * unfold rd_meas. cbn. rewrite zlength_app, zlength_u8s, Hct. unfold MAX_INPUT in *. lia.
Qed.

Lemma read_all_specP : forall X k0 path, zlength path <= ARG_MAX_LEN -> RDX X -> 0 <= k0 <= 1 ->
  mspecP (own X k0) (read_all io drv_malloc drv_free read_stage path)
         (fun r s mo => match r with
                        | RdExit => exists X' k, own X' k s mo
                        | RdDone buf content => exists j k, (j <= 10)%nat /\ k0 <= k <= k0 + 11
                                                  /\ own ((buf, 65536 * 2 ^ Z.of_nat j) :: X) k s mo /\ zlength content <= MAX_INPUT
                        end).
Proof.
  intros X k0 path Hpath HR Hk0. unfold read_all.
  apply mspecP_bind with (Q1 := fun r s mo => own X k0 s mo /\ match r with SVal fd => 0 <= fd | SErr _ => True end).
  { apply mspecP_sys. intros s mo Ho. split; [exact I|]. intros rsp mo' evs Hst.
    destruct (Hown_minv _ _ _ _ Ho) as [Hmi Hh].
    pose proof (nstep_dec_open _ mo rsp mo' evs Hmi Hst) as (_ & a & Hdec & Ha).
    exists a. split; [exact Hdec|]. cbn beta.
    assert (Hvm : m_vmmaps mo' = m_vmmaps mo).
    { destruct a as [e|fd]; [destruct Ha as [-> _]; reflexivity|]. destruct Ha as (_ & _ & _ & ent & _ & ->). reflexivity. }
    split; [eapply own_after_node; eauto|]. destruct a as [e|fd]; [exact I|]. lia. }
  intros [e|fd]; cbn beta iota.
  - apply mspecP_pure. intros _. eapply mspecP_seq; [apply Hdiag; exact Hpath|]. intros _. apply mspecP_ret. intros s mo Ho. eexists _, _. exact Ho.
  - apply mspecP_pure. intros Hfd. eapply mspecP_bind; [apply malloc_specP; [lia| unfold FPRE, RDX in *; lia]|]. intros [buf|]; cbn beta iota; [| apply mspecP_false].
    apply mspecP_pure. intros _.
    eapply mspecP_bind.
    + eapply mspecP_pre.
      * apply (mspecP_loop (read_loop_body io drv_malloc drv_free read_stage fd path) (rd_inv X k0)
                 (fun r s mo => match r with RdExit => exists X' k, own X' k s mo
                                | RdDone buf content => exists j k, (j <= 10)%nat /\ k0 <= k <= k0 + 11
                                    /\ own ((buf, 65536 * 2 ^ Z.of_nat j) :: X) k s mo /\ zlength content <= MAX_INPUT end)
                 rd_meas).
        { intros st. eapply mspecP_post; [apply read_loop_body_specP; [exact Hpath| exact Hfd| exact HR| exact Hk0]|].
          intros [st'|[|b c]] s mo H; exact H. }
        unfold rd_meas, READ_FUEL. cbn [rd_content]. unfold zlength. cbn [length Z.of_nat]. unfold MAX_INPUT. lia.
      * intros s mo Ho. unfold rd_inv. cbn. exists 0%nat, (k0 + 1). cbn [Z.of_nat Z.pow_pos Pos.pow]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [exact Ho| unfold zlength; cbn; lia].
    + intros [|buf' content]; cbn beta iota; [retP|].
      apply mspecP_pointwise. intros s1 mo1 (j & k & Hj & Hk & Ho1 & Hlen).
      eapply mspecP_bind with (Q1 := fun _ s mo => own ((buf', 65536 * 2 ^ Z.of_nat j) :: X) k s mo).
      * apply mspecP_sys. intros s mo [-> ->]. split; [exact I|]. intros rsp mo' evs Hst.
        pose proof (nstep_dec_close fd mo1 rsp mo' evs Hst) as (_ & a & Hdec & Ha).
        exists a. split; [exact Hdec|]. cbn beta.
        assert (Hvm : m_vmmaps mo' = m_vmmaps mo1).
        { destruct a as [e|v]; [destruct Ha as (_ & -> & _); reflexivity|]. destruct Ha as (_ & _ & ->). reflexivity. }
        eapply own_after_node; eauto.
      * intros _. apply mspecP_ret. intros s mo Ho. exists j, k. auto.
Qed.

Lemma main_model_specC : forall X k0 argv,
  Forall (fun a => zlength a <= ARG_MAX_LEN) argv -> RDX X -> 0 <= k0 <= 1 ->
  cspecP (own X k0) (DriverC.main_model io drv_malloc drv_free read_stage alloc_init run alloc_count argv)
         (fun _ s mo => exists X' k, own X' k s mo).
Proof.
  intros X k0 argv Hargv HR Hk0. unfold DriverC.main_model.
  assert (Hnth : forall i, zlength (nth i argv []) <= ARG_MAX_LEN).
  { intros i. destruct (nth_in_or_default i argv []) as [Hin| ->]; [|unfold zlength, ARG_MAX_LEN; cbn; lia].
    exact (proj1 (Forall_forall _ _) Hargv _ Hin). }
  apply cspecP_if; intros _.
  { apply cspecP_lift. eapply mspecP_seq; [apply Hdiag; cbn; apply Hnth|]. intros _. apply mspecP_ret. intros s mo Ho. eexists _, _; exact Ho. }
  eapply cspecP_bind; [apply cspecP_lift; apply (read_all_specP X k0); [apply Hnth| exact HR| exact Hk0]|].
  intros [|buf content]; cbn beta iota; [apply cspecP_ret; intros s mo H; exact H|].
  apply cspecP_exI. intros j. apply cspecP_exI. intros k. apply cspecP_pure_l. intros Hj. apply cspecP_pure_l. intros Hk. apply cspecP_pure. intros Hlen.
  set (cap := 65536 * 2 ^ Z.of_nat j).
  apply cspecP_if; intros _.
  { apply cspecP_lift. eapply mspecP_seq; [apply Hdiag; exact I|]. intros _. eapply mspecP_seq; [apply Hf|]. intros _. apply mspecP_ret. intros s mo Ho; eexists _, _; exact Ho. }
  apply cspecP_if; intros _.
  { apply cspecP_lift. eapply mspecP_seq; [apply Hdiag; exact I|]. intros _. eapply mspecP_seq; [apply Hf|]. intros _. apply mspecP_ret. intros s mo Ho; eexists _, _; exact Ho. }
  eapply cspecP_seq; [apply cspecP_lift; apply Hinit|]. intros _.
  eapply cspecP_bind.
  { apply Hrun; [pose proof (zlength_skipn_le (Z.to_nat (6 + Z.land (le16 content) 0x7fff)) content); lia|].
    unfold TR_ENTRY. destruct (buf_counts X buf j Hj HR) as (B1 & B2 & B3). fold cap in B1, B2, B3. lia. }
  intros status. apply cspecP_exI. intros LK. apply cspecP_exI. intros k'. apply cspecP_pure. intros Hk'.
  eapply cspecP_seq with (R := own ((buf, cap) :: LK ++ X) k').
  { apply cspecP_lift. eapply mspecP_pre with (P := own ((buf, cap) :: LK ++ X) k').
    2:{ intros s mo Ho. eapply Hperm; [| exact Ho]. symmetry. apply Permutation_middle. }
    destruct (Z.testbit _ 15); [| retP].
    eapply mspecP_seq; [apply Hcount|]. intros n. retP. }
  intros status'. eapply cspecP_seq; [apply cspecP_lift; apply Hf|]. intros _. apply cspecP_ret. intros s mo Ho. eexists _, _. exact Ho.
Qed.

Lemma exit_model_specC : forall code,
  cspecP (fun s mo => exists X k, own X k s mo) (DriverC.exit_model io code) (fun _ _ _ => False).
Proof.
  intros code. unfold DriverC.exit_model. apply cspecP_lift. unfold exit_model.
  eapply mspecP_seq with (R := fun s mo => exists X k, own X k s mo).
  - apply mspecP_exI. intros X. apply mspecP_exI. intros k. eapply mspecP_post; [apply Hexit|]. intros a s mo Ho. eexists _, _. exact Ho.
  - intros _. apply mspecP_sys. intros s mo _. split; [exact I|]. intros rsp mo' evs Hst. destruct (nstep_exit_none _ _ _ _ _ Hst).
Qed.
End DriverSpecC.


Local Notation STOTP := (STOT (St:=PState) nstep (fun R0 => texit (R:=R0) nstep nexit)).

Record fkit : Type := mkFK {
  fk_F : list (bptr * Z) -> Z -> mstate -> Prop;
  fk_init : forall resv atop, 0 < atop <= atop_hi -> fk_F [] 0 (strip (minit 0 resv atop));
  fk_perm : forall X Y k cs, Permutation X Y -> fk_F X k cs -> fk_F Y k cs;
  fk_kle : forall X k k' cs, k <= k' -> fk_F X k cs -> fk_F X k' cs;
  fk_m : forall (G : PState -> Model -> Prop) X k n s0, frame_ok G -> 0 <= n <= 2^62 -> FPRE X k n ->
    mspecP (fun s mo => s = s0 /\ (OWN (map fst X) G s mo /\ fk_F X k (ps_m s))) (raw_malloc n)
           (fun r s mo => match r with
                          | Some p => (OWN (p :: map fst X) G s mo /\ fk_F ((p, n) :: X) (k + 1) (ps_m s)) /\ n < 2^63 /\ (KREQ n -> fresh_topb s0 s p = true)
                          | None => False
                          end);
  fk_f : forall (G : PState -> Model -> Prop) X k p n, frame_ok G ->
    mspecP (fun s mo => OWN (p :: map fst X) G s mo /\ fk_F ((p, n) :: X) k (ps_m s)) (raw_free p) (fun _ s mo => OWN (map fst X) G s mo /\ fk_F X k (ps_m s));
  fk_stot_m : forall (G : PState -> Model -> Prop) X k n s mo, frame_ok G -> OWN (map fst X) G s mo -> fk_F X k (ps_m s) ->
    0 <= n -> size_overflows n = false -> FPRE X k n -> tglob nstep PhiP (raw_malloc n s) mo ->
    STOTP (raw_malloc n s) mo
          (fun r s' mo' => exists p, r = Some p /\ OWN (p :: map fst X) G s' mo' /\ fk_F ((p, n) :: X) (k + 1) (ps_m s') /\ n < 2^63
                           /\ (KREQ n -> fresh_topb s s' p = true)
                           /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo);
  fk_stot_f : forall (G : PState -> Model -> Prop) X k p n s mo, frame_ok G -> OWN (p :: map fst X) G s mo -> fk_F ((p, n) :: X) k (ps_m s) ->
    tglob nstep PhiP (raw_free p s) mo ->
    STOTP (raw_free p s) mo
          (fun _ s' mo' => OWN (map fst X) G s' mo' /\ fk_F X k (ps_m s') /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s /\ m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo)
}.

Lemma mspecP_keeps {B A} (f : PState -> B) (R : B -> Prop) (P : assn PState) (m : Monad.M PState A) (Q : A -> assn PState) :
  mspecP P m Q -> keeps f m -> mspecP (fun s mo => P s mo /\ R (f s)) m (fun a s mo => Q a s mo /\ R (f s)).
Proof.
  intros Hm Hk s mo [HP HR]. eapply etwfP_mono; [apply (etwfP_tall (m s) mo _ _ (Hm s mo HP) (Hk s))|].
  intros [a s'] mo' [H1 H2]; cbn in *. rewrite H2. auto.
Qed.

Section Kit.
Variable FM : flush_model.
Variable K : fkit.

Definition own (X : list (bptr * Z)) (k : Z) : assn PState := fun s mo => GI (map fst X) s mo /\ fk_F K X k (ps_m s).

Lemma own_perm : forall X Y k s mo, Permutation X Y -> own X k s mo -> own Y k s mo.
Proof. intros X Y k s mo HP [HG HF]. split; [eapply GI_perm; [apply Permutation_map; exact HP| exact HG]| eapply (fk_perm K); [exact HP| exact HF]]. Qed.
Lemma own_kle : forall X k k' s mo, k <= k' -> own X k s mo -> own X k' s mo.
Proof. intros X k k' s mo Hk [HG HF]. split; [exact HG| eapply (fk_kle K); [exact Hk| exact HF]]. Qed.
Lemma own_minv : forall X k s mo, own X k s mo -> minv mo /\ m_halted mo = None.
Proof. intros X k s mo [HG _]. exact (GI_minv _ _ _ HG). Qed.
Lemma own_fds : forall X k s mo mo', own X k s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> own X k s mo'.
Proof. intros X k s mo mo' [HG HF] E M H. split; [eapply GI_fds; eauto| exact HF]. Qed.

Lemma own_m : forall X k n s0, 0 <= n <= 2^62 -> FPRE X k n ->
  mspecP (fun s mo => s = s0 /\ own X k s mo) (raw_malloc n)
         (fun r s mo => match r with Some p => own ((p, n) :: X) (k + 1) s mo /\ n < 2^63 /\ (KREQ n -> fresh_topb s0 s p = true) | None => False end).
Proof.
  intros X k n s0 Hn HF. unfold own, GI. eapply mspecP_post; [apply (fk_m K Gso X k n s0 frame_ok_Gso Hn HF)|].
  cbv beta. intros [p|] s mo H; [| exact H]. cbn [map fst]. exact H.
Qed.
Lemma own_f : forall X k p n, mspecP (own ((p, n) :: X) k) (raw_free p) (fun _ => own X k).
Proof. intros X k p n. unfold own, GI. cbn [map fst]. apply (fk_f K Gso X k p n frame_ok_Gso). Qed.

Local Ltac lift_keeps L KP := intros; unfold own; eapply mspecP_post;
  [apply (mspecP_keeps ps_m (fk_F K _ _)); [apply mspec_mspecP; apply L; assumption| KP]| cbv beta; intros ? ? ? [H1 H2]; split; [exact H1| exact H2]].

Lemma stderr_pieces_keeps : forall ps buf, keeps ps_m (stderr_pieces (St:=PState) buf ps).
Proof.
  induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces]; [apply keeps_ret|].
  apply keeps_if; [| apply IH]. apply keeps_bind; [apply (stdio_write_k ps_m)| intros; apply IH].
Qed.
Lemma stderr_fprintf_keeps : forall ps, keeps ps_m (stderr_fprintf (St:=PState) ps).
Proof. intros ps. unfold stderr_fprintf. apply keeps_bind; [apply stderr_pieces_keeps|]. intros buf. apply (stdio_write_k ps_m). Qed.
Lemma stderr_fwrite_keeps : forall bs, keeps ps_m (stderr_fwrite (St:=PState) bs).
Proof. intros bs. unfold stderr_fwrite. apply keeps_if; [apply (stdio_write_k ps_m)| apply keeps_ret]. Qed.
Lemma s_diag_keeps : forall d, keeps ps_m (s_diag (St:=PState) d).
Proof. intros d. destruct d; cbn [s_diag]; first [apply stderr_fprintf_keeps| apply stderr_fwrite_keeps]. Qed.

Lemma own_diag : forall X k d, diag_ok d -> mspecP (own X k) (io_diag io d) (fun _ => own X k).
Proof. lift_keeps s_diag_GI ltac:(apply s_diag_keeps). Qed.
Lemma own_emit : forall X k v, mspecP (own X k) (io_emit io v) (fun _ => own X k).
Proof. lift_keeps s_emit_GI ltac:(apply (s_emit_k ps_m); intros; reflexivity). Qed.
Lemma own_exit : forall X k, mspecP (own X k) (io_exit io) (fun _ => own X k).
Proof. lift_keeps stdout_exit_flush_GI ltac:(apply (stdout_exit_flush_k ps_m); intros; reflexivity). Qed.
Lemma own_fpr : forall X k ps, Forall (fun p => zlength p <= TargetSafeC.PIECE_MAX) ps -> mspecP (own X k) (stderr_fprintf ps) (fun _ => own X k).
Proof. lift_keeps stderr_fprintf_GI ltac:(apply stderr_fprintf_keeps). Qed.
Lemma own_fwr : forall X k bs, zlength bs <= TargetSafeC.PIECE_MAX -> mspecP (own X k) (stderr_fwrite bs) (fun _ => own X k).
Proof. lift_keeps stderr_fwrite_GI ltac:(apply stderr_fwrite_keeps). Qed.
Lemma own_init_alloc : forall X k bm, mspecP (own X k) (alloc_init bm) (fun _ => own X k).
Proof. intros X k bm. unfold alloc_init, Adapter.target_alloc_init. apply mspecP_ret. intros s mo H; exact H. Qed.
Lemma own_count : forall X k, mspecP (own X k) alloc_count (fun _ => own X k).
Proof. intros X k. unfold alloc_count, Adapter.target_alloc_count. apply mspecP_ret. intros s mo H; exact H. Qed.
Lemma own_startup : forall X k, mspecP (own X k) startup (fun _ => own X k).
Proof. lift_keeps startup_GI ltac:(unfold startup; keeps_tac). Qed.

(* the launch's model is
   [with_vdso v (init_model ..)], and GI_init takes the 2^33 image bound, mmap_base_min <= mbase and the
   launch's channel reader (all three APPENDED); Spec/ModelOKC.prog_model_ok_D discharges them. *)
Lemma own_init : forall segs brk0 mbase sp lim inp atop v,
  valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
  sp_window_lo <= bv_unsigned sp <= sp_window_hi -> atop = bv_unsigned sp - stack_max_size ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
  reserved_top (segments_reserved segs) + brk_aslr_max <= 2 ^ 33 ->
  mmap_base_min <= bv_unsigned mbase ->
  in_channel_reader inp = true ->
  own [] 0 (ps_init (reservedZ segs) atop) (with_vdso v (init_model (segments_reserved segs) brk0 mbase sp lim inp)).
Proof.
  intros segs brk0 mbase sp lim inp atop v Hbrk Hpos Hsp Eatop Hceil Hlow Hmb Hrdr. split; [eapply GI_init; eauto|].
  cbn [ps_m ps_init]. apply (fk_init K).
  pose proof alloc_ceiling_lo_val. unfold atop_hi, sp_window_lo, sp_window_hi, stack_max_size in *. lia.
Qed.

Lemma runC_P : forall X k cfg payload, zlength payload <= MAX_INPUT -> TR_ENTRY X k ->
  cspecP (own X k) (runC FM cfg payload) (fun _ s mo => exists LK k', own (LK ++ X) k' s mo /\ 0 <= k').
Proof.
  intros X k cfg payload HL HT. unfold runC, fuzz_oneC.
  apply (target_run_spec FM raw_malloc raw_free fresh_topb (io_emit io) own own_m own_f own_perm own_emit own_fpr own_fwr); [| exact HT].
  unfold MAX_INPUT in HL. lia.
Qed.

Lemma own_m_weak : forall X k n s0, 0 <= n <= 2^62 -> FPRE X k n ->
  mspecP (fun s mo => s = s0 /\ own X k s mo) (raw_malloc n)
         (fun r s mo => match r with Some p => own ((p, n) :: X) (k + 1) s mo /\ n < 2^63 | None => False end).
Proof.
  intros X k n s0 Hn HF. eapply mspecP_post; [apply (own_m X k n s0 Hn HF)|]. cbv beta. intros [p|] s mo H; [| exact H].
  destruct H as (H1 & H2 & _). split; [exact H1| exact H2].
Qed.

Theorem prog_withC_P : forall rs argv,
  Forall (fun a => zlength a <= ARG_MAX_LEN) argv ->
  cspecP (own [] 0) (prog_withC FM rs argv) (fun _ _ _ => False).
Proof.
  intros rs argv Hargv. unfold prog_withC.
  eapply cspecP_seq; [apply cspecP_lift, own_startup|]. intros _.
  eapply cspecP_bind.
  - eapply (main_model_specC io raw_malloc raw_free rs alloc_init (runC FM) alloc_count own);
      first [ exact Hargv
            | apply own_m_weak
            | apply own_f | apply own_perm | apply own_kle
            | (intros; apply own_diag; assumption) | apply own_exit | apply own_init_alloc | apply own_count
            | (intros; apply runC_P; assumption) | apply own_minv | apply own_fds
            | (unfold RDX, C31, C40, C44; rewrite !cntr_nil; lia) | lia ].
  - intros code. eapply (exit_model_specC io own). apply own_exit.
Qed.

Corollary prog_withD_P : forall D rs argv,
  Forall (fun a => zlength a <= ARG_MAX_LEN) argv ->
  mspecP (own [] 0) (prog_withD FM D rs argv) (fun _ _ _ => False).
Proof. intros D rs argv Hargv. unfold prog_withD. apply cspecP_RES. apply prog_withC_P. exact Hargv. Qed.
End Kit.
