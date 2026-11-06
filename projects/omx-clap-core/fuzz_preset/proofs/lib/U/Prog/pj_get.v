From Stdlib Require Import ZArith List Lia Bool Arith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import strcmp_c pj_get_c.
Import ListNotations.
Open Scope Z_scope.

Lemma gp_sx32 : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  change (4294967296 / 2) with 2147483648. rewrite Z.mod_small by lia. lia.
Qed.

Lemma gp_rd : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. rewrite <- (Z.add_0_r a) at 1.
  rewrite (bytes_at_read rsegs m a bs 0 (length bs) H) by lia.
  cbn [Z.to_nat skipn]. rewrite firstn_all. reflexivity.
Qed.

Lemma gp_rd64 : forall m a v, pj_u64 rsegs m a v -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof. intros m a v (_ & H). pose proof (gp_rd m a _ H) as R. rewrite length_le8 in R. exact R. Qed.

Lemma gp_rd32 : forall m a v, pj_u32 rsegs m a v -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 (Z_to_bv 64 v)).
Proof. intros m a v (_ & H). pose proof (gp_rd m a _ H) as R. rewrite length_le4 in R. exact R. Qed.

Lemma gp_nz : forall l : list Z, Forall (fun c => 0 < c < 256) l -> ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) l).
Proof.
  intros l H Hin. apply in_map_iff in Hin. destruct Hin as (c & Ec & Hc).
  rewrite Forall_forall in H. specialize (H c Hc).
  apply (f_equal (@bv_unsigned 8)) in Ec. rewrite !Z_to_bv_unsigned in Ec. unfold bv_wrap, bv_modulus in Ec.
  change (2 ^ Z.of_N 8) with 256 in Ec. rewrite !Z.mod_small in Ec by lia. lia.
Qed.

Lemma gp_map_inj : forall l1 l2 : list Z, Forall (fun c => 0 < c < 256) l1 -> Forall (fun c => 0 < c < 256) l2 ->
  map (Z_to_bv 8) l1 = map (Z_to_bv 8) l2 -> l1 = l2.
Proof.
  induction l1 as [|c1 l1 IH]; intros [|c2 l2] H1 H2 E; cbn [map] in E; try discriminate; [reflexivity|].
  assert (Ec : Z_to_bv 8 c1 = Z_to_bv 8 c2) by congruence.
  assert (El : map (Z_to_bv 8) l1 = map (Z_to_bv 8) l2) by congruence.
  inversion H1; subst. inversion H2; subst. f_equal; [|apply IH; assumption].
  apply (f_equal (@bv_unsigned 8)) in Ec. rewrite !Z_to_bv_unsigned in Ec. unfold bv_wrap, bv_modulus in Ec.
  change (2 ^ Z.of_N 8) with 256 in Ec. rewrite !Z.mod_small in Ec by lia. exact Ec.
Qed.

Lemma gp_cb : forall m a s, pj_cbytes rsegs m a s ->
  bytes_at rsegs m (bv_unsigned (Z_to_bv 64 a)) (map (Z_to_bv 8) s ++ [Z_to_bv 8 0]) /\
  ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) s).
Proof.
  intros m a s (HF & HB). pose proof HB as (Ha & Hl & _).
  rewrite length_map, length_app in Hl. cbn [length] in Hl.
  rewrite unsigned_lit by lia. rewrite map_app in HB. cbn [map] in HB.
  split; [exact HB | exact (gp_nz s HF)].
Qed.

Lemma gp_cb_munch : forall W m m' a s, pj_cbytes rsegs m a s -> munch W m m' ->
  disjoint_from W a (Z.of_nat (length s) + 1) -> pj_cbytes rsegs m' a s.
Proof.
  intros W m m' a s (HF & HB) MU HD. split; [exact HF|].
  eapply bytes_at_transport; [exact HB | exact MU |]. rewrite length_map, length_app. cbn [length].
  replace (Z.of_nat (length s + 1)) with (Z.of_nat (length s) + 1) by lia. exact HD.
Qed.

Lemma gp_node_hdr : forall m lblk p t D, pj_node rsegs m lblk p t D ->
  NoDup D /\ pj_apart D p /\ exists num str kids keys n cap, pj_hdr rsegs m p (tag t) num str kids keys n cap.
Proof.
  intros m lblk p t D H. destruct t; cbn [pj_node] in H;
    destruct H as (ND & AP & num & str & kids & keys & n & cap & HH & _);
    (split; [exact ND|]); (split; [exact AP|]); exists num, str, kids, keys, n, cap; exact HH.
Qed.

Lemma gp_items_blocks : forall (lblk : Z -> Z -> Prop) (P : Z -> jv -> list (Z * Z) -> Prop) l a D,
  (forall a' u D1, In u l -> P a' u D1 -> forall x k, In (x, k) D1 -> lblk x k) ->
  pj_items P a l D -> forall x k, In (x, k) D -> lblk x k.
Proof.
  intros lblk P l. induction l as [|u l IH]; intros a D HP H x k Hin; cbn [pj_items] in H.
  - subst D. destruct Hin.
  - destruct H as (D1 & D2 & -> & HPu & Hr). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + exact (HP a u D1 (or_introl eq_refl) HPu x k Hin).
    + apply (IH (a + 56) D2); [|exact Hr|exact Hin]. intros a' u' D1' Hu. apply HP. right. exact Hu.
Qed.

Lemma gp_mems_blocks : forall m (lblk : Z -> Z -> Prop) (P : Z -> jv -> list (Z * Z) -> Prop) l a ka D,
  (forall a' nm u D1, In (nm, u) l -> P a' u D1 -> forall x k, In (x, k) D1 -> lblk x k) ->
  pj_mems rsegs m lblk P a ka l D -> forall x k, In (x, k) D -> lblk x k.
Proof.
  intros m lblk P l. induction l as [|[nm u] l IH]; intros a ka D HP H x k Hin; cbn [pj_mems] in H.
  - subst D. destruct Hin.
  - destruct H as (x0 & k0 & D1 & D2 & -> & _ & (Hl & _) & HPu & Hr).
    destruct Hin as [E|Hin]; [injection E as <- <-; exact Hl|].
    apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + exact (HP a nm u D1 (or_introl eq_refl) HPu x k Hin).
    + apply (IH (a + 56) (ka + 8) D2); [|exact Hr|exact Hin]. intros a' nm' u' D1' Hu. apply (HP a' nm' u' D1'). right. exact Hu.
Qed.

Lemma gp_node_blocks : forall t m lblk p D, pj_node rsegs m lblk p t D -> forall x k, In (x, k) D -> lblk x k.
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind'; intros m lblk p D H x k Hin;
    cbn [pj_node] in H; destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & H).
  - destruct H as (_ & _ & _ & _ & _ & ->). destruct Hin.
  - destruct H as (_ & _ & _ & _ & _ & ->). destruct Hin.
  - destruct H as (_ & _ & _ & _ & _ & ->). destruct Hin.
  - destruct H as (_ & _ & _ & _ & _ & k0 & (Hl & _) & ->). destruct Hin as [E|[]]. injection E as <- <-. exact Hl.
  - destruct H as (_ & _ & _ & _ & k0 & (Hl & _) & ->). destruct Hin as [E|[]]. injection E as <- <-. exact Hl.
  - destruct H as (_ & _ & _ & _ & Hc & Di & -> & Hi). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + destruct (Z.eqb_spec cap 0) as [C0|C0]; [destruct Hin|].
      destruct Hin as [E|[]]. injection E as <- <-. destruct Hc as [(C1 & _)|(_ & Hl)]; [lia | exact Hl].
    + rewrite Forall_forall in IH.
      apply (gp_items_blocks lblk (pj_node rsegs m lblk) items kids Di); [|exact Hi | exact Hin].
      intros a' u D1 Hu H1. exact (IH u Hu m lblk a' D1 H1).
  - destruct H as (_ & _ & _ & Hc & Di & -> & Hi). apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + destruct (Z.eqb_spec cap 0) as [C0|C0]; [destruct Hin|].
      destruct Hc as [(C1 & _)|(_ & Hl1 & Hl2)]; [lia|].
      destruct Hin as [E|[E|[]]]; injection E as <- <-; assumption.
    + rewrite Forall_forall in IH.
      apply (gp_mems_blocks m lblk (pj_node rsegs m lblk) members kids keys Di); [|exact Hi | exact Hin].
      intros a' nm u D1 Hu H1. exact (IH (nm, u) Hu m lblk a' D1 H1).
Qed.

Lemma gp_mems_nth : forall m lblk (P : Z -> jv -> list (Z * Z) -> Prop) l a ka D i nm u,
  pj_mems rsegs m lblk P a ka l D -> nth_error l i = Some (nm, u) ->
  exists x k D1, pj_u64 rsegs m (ka + 8 * Z.of_nat i) x /\ pj_cstr rsegs m lblk x k nm /\
    P (a + 56 * Z.of_nat i) u D1 /\ incl D1 D.
Proof.
  intros m lblk P l. induction l as [|[nm0 u0] l IH]; intros a ka D i nm u H E; [destruct i; discriminate|].
  cbn [pj_mems] in H. destruct H as (x & k & D1 & D2 & -> & Hx & Hc & Hp & Hr).
  destruct i as [|i]; cbn [nth_error] in E.
  - injection E as <- <-. exists x, k, D1. cbn [Z.of_nat]. rewrite !Z.mul_0_r, !Z.add_0_r.
    split; [exact Hx|]. split; [exact Hc|]. split; [exact Hp|].
    intros y Hy. right. apply in_or_app. left. exact Hy.
  - destruct (IH _ _ _ _ _ _ Hr E) as (x' & k' & D1' & H1 & H2 & H3 & H4).
    exists x', k', D1'. replace (ka + 8 * Z.of_nat (S i)) with (ka + 8 + 8 * Z.of_nat i) by lia.
    replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) by lia.
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    intros y Hy. right. apply in_or_app. right. exact (H4 y Hy).
Qed.


Lemma gu_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma gu_signed : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. change (18446744073709551616 / 2) with 9223372036854775808.
  rewrite Z.mod_small by lia. lia.
Qed.

Section Loop.
Variables (sp gp tp t0 t1 t2 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
  (o k keys : Z) (kname : list Z) (members : list (list Z * jv)).
Hypothesis HSC : strcmp_contract.
Hypothesis HK : pj_cbytes rsegs m k kname.
Hypothesis HKEYS : forall i nm u, nth_error members i = Some (nm, u) ->
  exists x, pj_u64 rsegs m (keys + 8 * Z.of_nat i) x /\ pj_cbytes rsegs m x nm.
Hypothesis HN : Z.of_nat (length members) < 2 ^ 44.
Hypothesis HKP : 0 < keys.
Hypothesis HK8 : keys mod 8 = 0.

Lemma gu_loop : forall j i (x1 x10 x11 x12 x13 x18 x19 x22 x23 x24 : word),
  (length members - i = j)%nat -> (i < length members)%nat ->
  x18 = Z_to_bv 64 (-56 * Z.of_nat i) -> x19 = Z_to_bv 64 (Z.of_nat i) -> x22 = Z_to_bv 64 1 ->
  x23 = Z_to_bv 64 (keys + 8 * Z.of_nat i) -> x24 = Z_to_bv 64 (keys + 8 * Z.of_nat i) ->
  (forall j' nm u, (j' < i)%nat -> nth_error members j' = Some (nm, u) -> nm <> kname) ->
  (forall i' u (y1 y10 y11 y12 y13 : word), nth_error members i' = Some (kname, u) ->
     (forall j' nm u', (j' < i')%nat -> nth_error members j' = Some (nm, u') -> nm <> kname) ->
     evt rsegs Q (MS (mkR y1 sp gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 k) y10 y11 y12 y13 a4 a5 a6 a7
                        (Z_to_bv 64 (-56 * Z.of_nat i')) (Z_to_bv 64 (Z.of_nat i')) (Z_to_bv 64 (Z.of_nat (length members)))
                        (Z_to_bv 64 keys) (Z_to_bv 64 1) (Z_to_bv 64 (keys + 8 * Z.of_nat i'))
                        (Z_to_bv 64 (keys + 8 * Z.of_nat i')) s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1654c) fc None m (seg_rom rsegs))) ->
  (forall (y1 y10 y11 y12 y13 y18 y19 y22 y23 y24 : word), (forall nm u, In (nm, u) members -> nm <> kname) ->
     evt rsegs Q (MS (mkR y1 sp gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 k) y10 y11 y12 y13 a4 a5 a6 a7
                        y18 y19 (Z_to_bv 64 (Z.of_nat (length members))) (Z_to_bv 64 keys) y22 y23 y24
                        s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16518) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 k) x10 x11 x12 x13 a4 a5 a6 a7
                     x18 x19 (Z_to_bv 64 (Z.of_nat (length members))) (Z_to_bv 64 keys) x22 x23 x24
                     s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x164d4) fc None m (seg_rom rsegs)).
Proof using HSC HK HKEYS HN HKP HK8.
  induction j as [j IH] using lt_wf_ind.
  intros i x1 x10 x11 x12 x13 x18 x19 x22 x23 x24 Hj Hi E18 E19 E22 E23 E24 Hpre KF KX.
  subst x18 x19 x22 x23 x24.
  destruct (nth_error members i) as [[nm u]|] eqn:Ei; [|apply nth_error_None in Ei; lia].
  destruct (HKEYS i nm u Ei) as (x & HX & HC).
  pose proof HX as (_ & (XL & XH & _)). rewrite length_le8 in XH.
  pose proof (gp_rd64 _ _ _ HX) as RX.
  destruct (gp_cb _ _ _ HC) as (BX & NX).
  destruct (gp_cb _ _ _ HK) as (BK & NK).
  step. step. if_cases H1.
  { zify_cond H1. destruct (Z.ltb_spec (keys + 8 * Z.of_nat i) 1); [lia | cbn in H1; discriminate H1]. }
  step. step. if_cases H2.
  { zify_cond H2. rewrite Z.shiftr_div_pow2 in H2 by lia. rewrite Z.div_small in H2 by lia. contradiction. }
  step. if_cases H3; [zify_cond H3; lia|].
  step. if_cases H4; [zify_cond H4; lia|].
  step. step. if_cases H5.
  { zify_cond H5. rewrite gu_land7 in H5. exfalso. apply H5.
    replace (keys + 8 * Z.of_nat i) with (keys + Z.of_nat i * 8) by lia. rewrite Z_mod_plus_full. exact HK8. }
  step. step. step.
  eapply evt_cut; [exact (HSC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BX NX BK NK) |].
  intros ms' (r & y11 & y12 & y13 & -> & HR).
  replace (ret_pc (Z_to_bv 64 0x16500)) with (Z_to_bv 64 0x16500) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof HC as (HCF & _). pose proof HK as (HKF & _).
  step. if_cases HZ.
  - assert (Er : r = Z_to_bv 64 0) by (unfold bv_eqb in HZ; apply Z.eqb_eq in HZ; apply bv_eq; exact HZ).
    apply HR in Er. apply (gp_map_inj _ _ HCF HKF) in Er. subst nm.
    exact (KF i u _ _ _ _ _ Ei Hpre).
  - assert (Hne : nm <> kname).
    { intros ->. assert (Er : r = Z_to_bv 64 0) by (apply HR; reflexivity). rewrite Er in HZ. vm_compute in HZ. discriminate HZ. }
    assert (Hpre' : forall j' nm' u', (j' < S i)%nat -> nth_error members j' = Some (nm', u') -> nm' <> kname).
    { intros j' nm' u' Hj' Ej'. destruct (Nat.eq_dec j' i) as [->|Hne'].
      - rewrite Ei in Ej'. injection Ej' as <- _. exact Hne.
      - apply (Hpre j' nm' u'); [lia | exact Ej']. }
    step. step. step. step. step. if_cases HS.
    + zify_cond HS.
      eapply (IH (length members - S i)%nat ltac:(lia) (S i)); [reflexivity | lia | f_equal; lia | f_equal; lia | reflexivity
        | f_equal; lia | f_equal; lia | exact Hpre' | exact KF | exact KX].
    + zify_cond HS.
      apply KX. intros nm' u' Hin Ek. subst nm'. apply In_nth_error in Hin. destruct Hin as (j' & Ej').
      assert (Hj' : (j' < length members)%nat) by (apply nth_error_Some; rewrite Ej'; discriminate).
      exact (Hpre' j' kname u' ltac:(lia) Ej' eq_refl).
Qed.
End Loop.

Local Ltac cur_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

Theorem pj_get_holds : strcmp_contract -> pj_get_contract.
Proof.
  intros HSC. unfold pj_get_contract, PJ_GET.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lblk o k kname t D lo E0 E1 HN HK LB SP16 ST LO SD MI.
  subst a0 a1. cbn [disjoint_from] in SD.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 80%nat ST.
  do 11 step.
  let mm := cur_mem in rename mm into m1.
  assert (HK1 : pj_cbytes rsegs m1 k kname) by (eapply gp_cb_munch; [exact HK | exact MU | cbn [disjoint_from]; lia]).
  step.
  destruct (Z.eq_dec o 0) as [O0|O0].
  - subst o. if_true. do 12 step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact HK1|]. left. split; reflexivity.
  - destruct HN as [HN|HN]; [contradiction|].
    pose proof (gp_node_hdr _ _ _ _ _ HN) as (ND & AP & num & str & kids & keys & n & cap & HH).
    pose proof HH as ((O8 & (OL & OH & _)) & _).
    if_cases HZ; [zify_cond HZ; Z.div_mod_to_equations; lia|].
    assert (BL : forall a n', In (a, n') D -> lblk a n') by exact (gp_node_blocks t m lblk o D HN).
    assert (FT : forall z, pj_foot o D z -> outside [(bv_unsigned sp + -80, bv_unsigned sp)] z).
    { intros z [Hz|((a & n') & Hb & Hz)]; cbn [outside] in *; split; try exact I.
      - lia.
      - destruct (LB a n' (BL a n' Hb)) as (_ & _ & _ & Hd). cbn [disjoint_from] in Hd.
        unfold pj_holds in Hz. cbn [fst snd] in Hz. lia. }
    pose proof (pj_node_munch rsegs _ _ _ _ _ _ _ _ HN BL MU FT) as PN.
    lazymatch goal with |- evt _ ?Q _ =>
      assert (EXIT : forall (w : word) z (x1 x8 x9 x11 x12 x13 x14 x18 x19 x20 x21 x22 x23 x24 : word),
        w = Z_to_bv 64 z -> pj_get_res m1 lblk o t D kname z ->
        evt rsegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 x8 x9 w x11 x12 x13
                             x14 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x1651c) fc None m1 (seg_rom rsegs)))
    end.
    { intros w z x1 x8 x9 x11 x12 x13 x14 x18 x19 x20 x21 x22 x23 x24 Ew HRES. subst w.
      do 12 step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. do 16 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact HK1|].
      right. split; [exact O0|]. split; [exact PN|]. exists z. split; [reflexivity|exact HRES]. }
    pose proof (gp_node_hdr _ _ _ _ _ PN) as (_ & _ & num1 & str1 & kids1 & keys1 & n1 & cap1 & HH1).
    pose proof HH1 as (_ & HT & _).
    pose proof (gp_rd32 _ _ _ HT) as RT.
    assert (TG : 0 <= tag t <= 6) by (destruct t; cbn [tag]; lia).
    step. step. step. if_cases HA.
    { zify_cond HA. rewrite gu_land7 in HA. contradiction. }
    step. step.
    rewrite gp_sx32 by lia.
    step. step.
    if_cases HT6.
    + zify_cond HT6. step.
      eapply (EXIT _ 0); [reflexivity|].
      destruct t; unfold pj_get_res; try reflexivity. cbn [tag] in HT6. lia.
    + zify_cond HT6.
      destruct t as [| | | txt bits | s | items | members]; cbn [tag] in HT6; try lia.
      pose proof PN as PN'. cbn [pj_node] in PN'.
      destruct PN' as (_ & _ & num2 & str2 & kids2 & keys2 & n2 & cap2 & HH2 & Hs0 & Hn & Hncap & Hcap & Di & ED & HM).
      pose proof HH2 as (_ & _ & _ & _ & HK24 & HK32 & HK40 & _).
      pose proof (gp_rd64 _ _ _ HK40) as RN. pose proof (gp_rd64 _ _ _ HK32) as RY. pose proof (gp_rd64 _ _ _ HK24) as RK.
      pose proof HK40 as (NR & _).
      step. step.
      if_cases HN0.
      * zify_cond HN0. step. eapply (EXIT _ 0); [reflexivity|]. unfold pj_get_res. left. split; [|reflexivity].
        intros nm u Hin. destruct members; [destruct Hin | cbn [length] in Hn; lia].
      * zify_cond HN0.
        destruct Hcap as [(C0 & _)|(CP & LKI & LKY)]; [lia|].
        destruct (LB _ _ LKI) as (KIP & KI8 & KIH & _).
        destruct (LB _ _ LKY) as (KYP & KY8 & KYH & _).
        assert (HNR : Z.of_nat (length members) < 2 ^ 44) by lia.
        subst n2.
        step. step. step. step. step. step.
        replace (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 keys2)) with (Z_to_bv 64 1)
          by (rewrite v_sltu_b2z, (unsigned_lit 0), (unsigned_lit keys2) by lia;
              rewrite (proj2 (Z.ltb_lt 0 keys2)) by lia; reflexivity).
        assert (HKEYS : forall i nm u, nth_error members i = Some (nm, u) ->
          exists x, pj_u64 rsegs m1 (keys2 + 8 * Z.of_nat i) x /\ pj_cbytes rsegs m1 x nm).
        { intros i nm u E. destruct (gp_mems_nth _ _ _ _ _ _ _ _ _ _ HM E) as (x & kx & D1 & Hx & (_ & _ & Hcb) & _ & _).
          exists x. split; [exact Hx | exact Hcb]. }
        eapply (gu_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 _ o k keys2 kname members HSC HK1 HKEYS HNR KYP KY8
                  (length members - 0) 0%nat _ _ _ _ _ (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 keys2)
                  (Z_to_bv 64 keys2) eq_refl ltac:(lia) ltac:(f_equal; lia) ltac:(f_equal; lia) eq_refl
                  ltac:(f_equal; lia) ltac:(f_equal; lia) ltac:(intros; lia)).
        -- intros i' u y1 y10 y11 y12 y13 Ei' Hpre'.
           destruct (gp_mems_nth _ _ _ _ _ _ _ _ _ _ HM Ei') as (x & kx & D1 & Hx & Hc & Hp & Hinc).
           pose proof (gp_node_hdr _ _ _ _ _ Hp) as (_ & _ & _ & _ & _ & _ & _ & _ & ((_ & (ZL & ZH & _)) & _)).
           assert (Hi' : (i' < length members)%nat) by (apply nth_error_Some; rewrite Ei'; discriminate).
           step. step. step.
           rewrite (unsigned_lit (Z.of_nat i')) by lia.
           step.
           lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.shiftl ?X 6)) - bv_unsigned (Z_to_bv 64 (Z.shiftl ?X 3)))] =>
             replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.shiftl X 6)) - bv_unsigned (Z_to_bv 64 (Z.shiftl X 3))))
               with (Z_to_bv 64 (56 * Z.of_nat i'))
               by (rewrite !Z.shiftl_mul_pow2 by lia; rewrite !unsigned_lit by lia; f_equal; lia)
           end.
           step. step. step. step. if_cases F1.
           { zify_cond F1. rewrite (proj2 (Z.ltb_lt 0 kids2)) in F1 by lia.
             rewrite (proj2 (Z.ltb_ge (56 * Z.of_nat i' + kids2) 1)) in F1 by lia. cbn [Z.b2z] in F1. discriminate F1. }
           step. if_cases F2; [zify_cond F2; lia|].
           step. step. step. step. step. step. if_cases F3.
           { zify_cond F3. rewrite !gu_signed in F3 by lia. rewrite !Z.shiftr_div_pow2 in F3 by lia.
             rewrite !Z.div_small in F3 by lia.
             rewrite !Z.mod_0_l in F3 by lia. rewrite Z.lxor_0_l in F3. lia. }
           step. step.
           eapply (EXIT _ (kids2 + 56 * Z.of_nat i')).
           ++ rewrite !unsigned_lit_wrap. apply Z_to_bv_eqm. Z.div_mod_to_equations. lia.
           ++ unfold pj_get_res. right.
              exists i', u, kids2, D1. split; [exact Ei'|]. split; [exact Hpre'|]. split; [exact HK24|].
              split; [reflexivity|]. split; [exact Hp|].
              intros y Hy. rewrite ED. apply in_or_app. right. apply Hinc. exact Hy.
        -- intros y1 y10 y11 y12 y13 y18 y19 y22 y23 y24 Hnone.
           step. eapply (EXIT _ 0); [reflexivity|]. unfold pj_get_res. left. split; [exact Hnone | reflexivity].
Qed.
