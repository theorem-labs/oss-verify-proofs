From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require
  LibcNeeds_c strlen_c strlen bcmp_c bcmp strchr_c strchr strncasecmp_c strncasecmp plain_c plain
  strncmp_c strncmp isalnum_c isalnum
  check_bounded_alloc_c check_bounded_alloc check_reject_clean_c check_reject_clean
  fuzz_alloc_live_c fuzz_alloc_live fuzz_alloc_peak_c fuzz_alloc_peak fuzz_alloc_peak_reset_c fuzz_alloc_peak_reset
  fuzz_alloc_fail_c fuzz_alloc_fail expected_c expected check_as_written_c check_as_written has_prefixed_c has_prefixed
  memchr_c memchr memchr_ro_c memchr_ro memcpy_c memcpy memset_c memset memset_ro_c memset_ro
  strstr_c strstr snprintf_c snprintf
  fuzz_malloc_c fuzz_malloc fuzz_free_c fuzz_free names_c names readings_c readings readings_scan_c
  as_ruled_c as_ruled
  check_reject_clean_starved_c check_reject_clean_starved check_no_overread_c check_no_overread
  check_round_trip_c check_round_trip ManifestB ManifestFF StatementUbsan.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Spec Require Import StrFun StrFun2 StrStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem.
Import ListNotations.
Local Open Scope Z_scope.

Lemma bv64_small_zero : forall v, -255 <= v <= 255 -> (bv_unsigned (Z_to_bv 64 v) = 0 <-> v = 0).
Proof.
  intros v Hv. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  split; intros H.
  - apply Z.mod_divide in H; [|lia]. destruct H as [k Hk]. lia.
  - subst. reflexivity.
Qed.

Lemma kret_of_same : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m m' (R : word -> Prop)
    t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m lo (bv_unsigned sp) -> R a0 ->
  kret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo 0 m [] R
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m m' R t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    MU WM MI ST HR.
  unfold kret. exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
  refine (conj eq_refl (conj _ (conj WM (conj MI (conj _ HR))))).
  - eapply munch_weaken; [|exact MU]. intros x _. exact I.
  - eapply stk_transport_disjoint; [exact ST|exact MU|exact WM|exact I].
Qed.

Theorem strlen_adapt : strlen_c.strlen_contract -> LibcNeeds_c.strlen_contract.
Proof.
  intros H. unfold LibcNeeds_c.strlen_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo bs slack
    [HB [HF HW]] MI ST.
  eapply evt_mono.
  - apply (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs slack
             HB); [|exact HW|exact MI].
    intros Hin. rewrite Forall_forall in HF. apply (HF _ Hin). reflexivity.
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & _).
    apply kret_of_same; try assumption. reflexivity.
Qed.

Lemma memcmp_iff : forall lb rb, length lb = length rb ->
  exists v, memcmp_model lb rb (length lb) = Some v /\ (v = 0 <-> zbytes lb = zbytes rb) /\ -255 <= v <= 255.
Proof.
  unfold zbytes.
  induction lb as [|a lb IH]; intros [|b rb] HL; cbn in HL; try discriminate.
  - exists 0. split; [reflexivity|]. split; [tauto|lia].
  - injection HL as HL. destruct (IH rb HL) as (v & Hv & Hi & Hr).
    pose proof (byte_range a). pose proof (byte_range b).
    cbn [memcmp_model length map].
    destruct (bv_unsigned a =? bv_unsigned b) eqn:E.
    + apply Z.eqb_eq in E. exists v. split; [exact Hv|]. split; [|exact Hr].
      rewrite Hi, E. split; [intros H'; rewrite H'; reflexivity|intros H'; injection H' as H''; exact H''].
    + apply Z.eqb_neq in E. exists (bv_unsigned a - bv_unsigned b). split; [reflexivity|].
      split; [split; [lia|intros H'; injection H' as H1 _; lia]|lia].
Qed.

Theorem bcmp_adapt : bcmp_c.bcmp_contract -> LibcNeeds_c.bcmp_contract.
Proof.
  intros H. unfold LibcNeeds_c.bcmp_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo lb rb
    HL HR NL NR MI ST.
  assert (HLen : length lb = length rb) by lia.
  destruct (memcmp_iff lb rb HLen) as (v & Hv & Hi & Hr).
  assert (HN : Z.to_nat (bv_unsigned a2) = length lb) by lia.
  eapply evt_mono.
  - apply (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lb rb v
             HL HR); [rewrite HN; exact Hv|exact MI].
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & _).
    apply kret_of_same; try assumption. cbv beta. rewrite bv64_small_zero by lia. exact Hi.
Qed.

Lemma strncmp_iff : forall lb rb k,
  Forall (fun b => bv_unsigned b <> 0) lb -> Forall (fun b => bv_unsigned b <> 0) rb ->
  exists v, strncmp_walk (lb ++ [Z_to_bv 8 0]) (rb ++ [Z_to_bv 8 0]) k = Some v
         /\ (v = 0 <-> firstn (S k) (zbytes lb ++ [0]) = firstn (S k) (zbytes rb ++ [0]))
         /\ -255 <= v <= 255.
Proof.
  assert (Z0 : bv_unsigned (Z_to_bv 8 0) = 0) by reflexivity.
  unfold zbytes.
  induction lb as [|a lb IH]; intros [|b rb] k Hl Hr; cbn [app map].
  - rewrite strncmp.walk_stop by (left; exact Z0). rewrite Z0.
    eexists; split; [reflexivity|]. split; [split; intros; [reflexivity|lia]|lia].
  - inversion Hr as [|? ? Hb Hr']; subst. pose proof (byte_range b).
    rewrite strncmp.walk_stop by (left; exact Z0). rewrite Z0.
    eexists; split; [reflexivity|]. cbn [firstn].
    split; [split; [intros; lia|intros H'; injection H' as H1 _; lia]|lia].
  - inversion Hl as [|? ? Ha Hl']; subst. pose proof (byte_range a).
    rewrite strncmp.walk_stop by (right; left; exact Z0). rewrite Z0.
    eexists; split; [reflexivity|]. cbn [firstn].
    split; [split; [intros; lia|intros H'; injection H' as H1 _; lia]|lia].
  - inversion Hl as [|? ? Ha Hl']; subst. inversion Hr as [|? ? Hb Hr']; subst.
    pose proof (byte_range a). pose proof (byte_range b).
    destruct k as [|k].
    + rewrite strncmp.walk_stop by (right; right; left; reflexivity).
      eexists; split; [reflexivity|]. cbn [firstn].
      split; [split; [intros; f_equal; lia|intros H'; injection H' as H1; lia]|lia].
    + destruct (Z.eq_dec (bv_unsigned a) (bv_unsigned b)) as [E|E].
      * rewrite strncmp.walk_go by assumption.
        destruct (IH rb k Hl' Hr') as (v & Hv & Hi & Hrg).
        exists v. split; [exact Hv|]. split; [|exact Hrg].
        change (firstn (S (S k)) (bv_unsigned a :: map bv_unsigned lb ++ [0]))
          with (bv_unsigned a :: firstn (S k) (map bv_unsigned lb ++ [0])).
        change (firstn (S (S k)) (bv_unsigned b :: map bv_unsigned rb ++ [0]))
          with (bv_unsigned b :: firstn (S k) (map bv_unsigned rb ++ [0])).
        rewrite Hi, E. split; [intros H'; rewrite H'; reflexivity|intros H'; injection H' as H''; exact H''].
      * rewrite strncmp.walk_stop by (right; right; right; exact E).
        eexists; split; [reflexivity|]. cbn [firstn].
        split; [split; [intros; lia|intros H'; injection H' as H1 _; lia]|lia].
Qed.

Theorem strncmp_adapt : strncmp_c.strncmp_contract -> LibcNeeds_c.strncmp_contract.
Proof.
  intros H. unfold LibcNeeds_c.strncmp_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo lb rb
    [HL FL] [HR FR] MI ST.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2. cbn in R2.
  assert (E : exists v, strncmp_model (lb ++ [Z_to_bv 8 0]) (rb ++ [Z_to_bv 8 0]) (bv_unsigned a2) = Some v /\
     (v = 0 <-> firstn (Z.to_nat (bv_unsigned a2)) (zbytes lb ++ [0])
                = firstn (Z.to_nat (bv_unsigned a2)) (zbytes rb ++ [0])) /\ -255 <= v <= 255).
  { unfold strncmp_model. destruct (Z.eqb_spec (bv_unsigned a2) 0) as [Z|NZ].
    - exists 0. rewrite Z. split; [reflexivity|]. split; [split; intros; reflexivity|lia].
    - destruct (strncmp_iff lb rb (Z.to_nat (bv_unsigned a2 - 1)) FL FR) as (v & Hv & Hi & Hr).
      exists v. split; [exact Hv|]. split; [|exact Hr].
      replace (Z.to_nat (bv_unsigned a2)) with (S (Z.to_nat (bv_unsigned a2 - 1))) by lia. exact Hi. }
  destruct E as (v & Hv & Hi & Hr).
  eapply evt_mono.
  - apply (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             (lb ++ [Z_to_bv 8 0]) (rb ++ [Z_to_bv 8 0]) v HL HR Hv MI).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & _).
    apply kret_of_same; try assumption. cbv beta. rewrite bv64_small_zero by lia. exact Hi.
Qed.

Theorem isalnum_adapt : isalnum_c.isalnum_contract -> LibcNeeds_c.isalnum_contract.
Proof.
  intros H. unfold LibcNeeds_c.isalnum_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo HC MI ST.
  pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. cbn in R0.
  assert (B1 : bv_unsigned (Z_to_bv 64 1) = 1) by reflexivity.
  assert (B0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
  eapply evt_mono.
  - apply (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             (bv_unsigned a0)); [lia|symmetry; apply Z_to_bv_bv_unsigned].
  - intros ms' (a1' & ->).
    apply kret_of_same; [apply munch_refl|apply wmono_refl|exact MI|exact ST|].
    cbv beta. change (isalnum_c.alnum_b (bv_unsigned a0)) with (is_alnum (bv_unsigned a0)).
    destruct (is_alnum (bv_unsigned a0)); rewrite ?B1, ?B0; split; intros; (reflexivity || discriminate || lia).
Qed.

Lemma find_byte_idx : forall c (l : list byte),
  find_byte c l = find_idx (fun x => x =? c) (zbytes l).
Proof.
  intros c l. unfold zbytes. induction l as [|b l IH]; cbn; [reflexivity|].
  destruct (bv_unsigned b =? c); [reflexivity|]. rewrite IH. destruct (find_idx _ _); reflexivity.
Qed.

Lemma not_in0_forall : forall l : list byte, Forall (fun b => bv_unsigned b <> 0) l -> ~ In (Z_to_bv 8 0) l.
Proof. intros l HF Hin. rewrite Forall_forall in HF. apply (HF _ Hin). reflexivity. Qed.

Theorem strchr_adapt : strchr_c.strchr_contract -> LibcNeeds_c.strchr_contract.
Proof.
  intros H. unfold LibcNeeds_c.strchr_contract, LibcNeeds_c.STRCHR_K, off_stack.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo bs slack
    [HB [HF HW]] HC MI ST LO SEP.
  eapply evt_mono.
  - apply (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs slack lo
             ST HB (not_in0_forall bs HF) HW MI); [lia|].
    rewrite !Nat2Z.inj_add in SEP. cbn [Z.of_nat Pos.of_succ_nat] in SEP. lia.
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & _).
    unfold kret. exists t0', t1', t2'.
    exists (Z_to_bv 64 (strchr_c.strchr_val (bv_unsigned a0) (bv_unsigned a1 mod 256) bs)).
    exists a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    unfold strchr_c.strchr_val, strchr_res. rewrite Z.mod_small by lia.
    replace (bv_unsigned a1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite find_byte_idx. destruct (find_idx _ _); reflexivity.
Qed.

Theorem strncasecmp_adapt : strncasecmp_c.strncasecmp_contract -> LibcNeeds_c.strncasecmp_contract.
Proof.
  intros H. unfold LibcNeeds_c.strncasecmp_contract, LibcNeeds_c.STRNCASECMP_K, LibcNeeds_c.cstr0, off_stack.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo lb rb
    [HL FL] [HR FR] MI ST LO SL SR.
  rewrite Nat2Z.inj_add in SL, SR. cbn [Z.of_nat Pos.of_succ_nat] in SL, SR.
  eapply evt_mono.
  - apply (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lb rb lo
             ST HL (not_in0_forall lb FL) HR (not_in0_forall rb FR) MI); lia.
  - intros ms' (r & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & _ & _ & HI).
    unfold kret. exists t0', t1', t2', r, a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    split.
    + intros Hr. apply (proj1 HI). apply bv_eq. rewrite Hr. reflexivity.
    + intros Heq. apply (proj2 HI) in Heq. rewrite Heq. reflexivity.
Qed.

Lemma prefix_eqb_mt : forall nd l,
  prefix_eqb nd l = (length nd <=? length l)%nat && zl_eqb (firstn (length nd) l) nd.
Proof.
  induction nd as [|a nd IH]; intros [|b l]; simpl; try reflexivity.
  rewrite IH. destruct (Z.eqb_spec a b) as [E|E].
  - subst b. rewrite Z.eqb_refl. reflexivity.
  - replace (b =? a) with false by (symmetry; apply Z.eqb_neq; congruence).
    destruct (length nd <=? length l)%nat; reflexivity.
Qed.

Lemma find_sub_from_S1 : forall h nd i fuel, find_sub_from h nd i (S fuel) =
  if (i + length nd <=? length h)%nat && zl_eqb (firstn (length nd) (skipn i h)) nd then Some i
  else find_sub_from h nd (S i) fuel.
Proof. reflexivity. Qed.

Lemma find_first_nil : forall nd, find_first [] nd = if prefix_eqb nd [] then Some 0%nat else None.
Proof. reflexivity. Qed.

Lemma find_first_cons : forall x t nd,
  find_first (x :: t) nd = if prefix_eqb nd (x :: t) then Some 0%nat else option_map S (find_first t nd).
Proof. reflexivity. Qed.

Lemma find_sub_from_first : forall n h nd i, length h = (i + n)%nat ->
  find_sub_from h nd i (S n) = option_map (Nat.add i) (find_first (skipn i h) nd).
Proof.
  induction n as [|n IH]; intros h nd i Hl; rewrite find_sub_from_S1;
    (replace (i + length nd <=? length h)%nat with (length nd <=? length (skipn i h))%nat
       by (rewrite length_skipn; apply Bool.eq_iff_eq_true; rewrite !Nat.leb_le; split; intros; lia));
    rewrite <- prefix_eqb_mt.
  - assert (Sk : skipn i h = []) by (apply length_zero_iff_nil; rewrite length_skipn; lia).
    rewrite Sk, find_first_nil. destruct (prefix_eqb nd []); cbn [option_map]; [rewrite Nat.add_0_r|]; reflexivity.
  - destruct (skipn i h) as [|x t] eqn:Sk.
    + apply (f_equal (@length Z)) in Sk. rewrite length_skipn in Sk. cbn [length] in Sk. lia.
    + rewrite find_first_cons. destruct (prefix_eqb nd (x :: t)).
      * cbn [option_map]. rewrite Nat.add_0_r. reflexivity.
      * assert (St : skipn (S i) h = t).
        { replace (S i) with (1 + i)%nat by lia. rewrite <- skipn_skipn, Sk. reflexivity. }
        rewrite (IH h nd (S i)) by lia. rewrite St.
        destruct (find_first t nd); cbn [option_map]; [f_equal; lia|reflexivity].
Qed.

Lemma find_first_sub : forall h nd, find_first h nd = find_sub h nd.
Proof.
  intros h nd. unfold find_sub. rewrite (find_sub_from_first (length h) h nd 0) by lia.
  change (skipn 0 h) with h. destruct (find_first h nd); reflexivity.
Qed.

Theorem strstr_adapt : strstr_c.strstr_contract -> LibcNeeds_c.strstr_contract.
Proof.
  intros H. unfold LibcNeeds_c.strstr_contract, LibcNeeds_c.STRSTR_K, off_stack.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    hb hs nb ns [HB [HF HW]] [NB [NF _]] _ A0 GG [g GW] G1 G2 MI ST LO SH SN.
  replace (nb ++ Z_to_bv 8 0 :: ns) with ((nb ++ [Z_to_bv 8 0]) ++ ns) in NB by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in NB as [NB _].
  rewrite !Nat2Z.inj_add in SH, SN. cbn [Z.of_nat Pos.of_succ_nat] in SH, SN.
  eapply evt_mono.
  - apply (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             hb hs nb lo g ST ltac:(lia) HB (not_in0_forall hb HF) HW A0 NB (not_in0_forall nb NF) MI
             ltac:(lia) ltac:(lia) GG GW G1 G2).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM
      & MI' & ST' & _).
    unfold kret. exists t0', t1', t2', (Z_to_bv 64 (strstr_val (bv_unsigned a0) hb nb)).
    exists a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    unfold strstr_val, zbytes. rewrite find_first_sub.
    destruct (find_sub (map bv_unsigned hb) (map bv_unsigned nb)); reflexivity.
Qed.

Theorem L_strlen : LibcNeeds_c.strlen_contract.
Proof. exact (strlen_adapt strlen.strlen_holds). Qed.

Theorem L_bcmp : LibcNeeds_c.bcmp_contract.
Proof. exact (bcmp_adapt bcmp.bcmp_holds). Qed.

Theorem L_strchr : LibcNeeds_c.strchr_contract.
Proof. exact (strchr_adapt strchr.strchr_holds). Qed.

Theorem L_strncasecmp : LibcNeeds_c.strncasecmp_contract.
Proof. exact (strncasecmp_adapt strncasecmp.strncasecmp_holds). Qed.

Theorem L_strstr : LibcNeeds_c.strstr_contract.
Proof. exact (strstr_adapt strstr.strstr_holds). Qed.

Theorem L_snprintf : snprintf_c.snprintf_contract.
Proof. exact snprintf.snprintf_holds. Qed.

Theorem L_plain : plain_c.plain_contract.
Proof. exact (plain.plain_holds L_strlen). Qed.

Theorem L_check_bounded_alloc : check_bounded_alloc_c.check_bounded_alloc_contract.
Proof. exact check_bounded_alloc.check_bounded_alloc_holds. Qed.

Theorem L_check_reject_clean : check_reject_clean_c.check_reject_clean_contract.
Proof. exact (check_reject_clean.check_reject_clean_holds fuzz_alloc_live.fuzz_alloc_live_holds). Qed.

Theorem L_fuzz_alloc_live : fuzz_alloc_live_c.fuzz_alloc_live_contract.
Proof. exact fuzz_alloc_live.fuzz_alloc_live_holds. Qed.

Theorem L_fuzz_alloc_peak : fuzz_alloc_peak_c.fuzz_alloc_peak_contract.
Proof. exact fuzz_alloc_peak.fuzz_alloc_peak_holds. Qed.

Theorem L_fuzz_alloc_peak_reset : fuzz_alloc_peak_reset_c.fuzz_alloc_peak_reset_contract.
Proof. exact fuzz_alloc_peak_reset.fuzz_alloc_peak_reset_holds. Qed.

Theorem L_fuzz_alloc_fail : fuzz_alloc_fail_c.fuzz_alloc_fail_contract.
Proof. exact fuzz_alloc_fail.fuzz_alloc_fail_holds. Qed.

Theorem L_memchr : memchr_c.memchr_contract.
Proof. exact memchr.memchr_holds. Qed.

Theorem L_memchr_ro : memchr_ro_c.memchr_ro_contract.
Proof. exact memchr_ro.memchr_ro_holds. Qed.

Theorem L_memcpy : memcpy_c.memcpy_contract.
Proof. exact memcpy.memcpy_holds. Qed.

Theorem L_memset : memset_c.memset_contract.
Proof. exact memset.memset_holds. Qed.

Theorem L_memset_ro : memset_ro_c.memset_ro_contract.
Proof. exact memset_ro.memset_ro_holds. Qed.

Theorem L_strncmp : LibcNeeds_c.strncmp_contract.
Proof. exact (strncmp_adapt strncmp.strncmp_holds). Qed.

Theorem L_isalnum : LibcNeeds_c.isalnum_contract.
Proof. exact (isalnum_adapt isalnum.isalnum_holds). Qed.

Theorem L_expected : expected_c.expected_contract.
Proof. exact (expected.expected_holds L_strlen L_strchr L_strncmp L_bcmp L_plain). Qed.

Theorem L_check_as_written : check_as_written_c.check_as_written_contract.
Proof. exact (check_as_written.check_as_written_holds L_expected). Qed.

Theorem L_has_prefixed : has_prefixed_c.has_prefixed_contract.
Proof. exact (has_prefixed.has_prefixed_holds L_strlen L_strstr L_strncmp L_isalnum). Qed.

From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YM05 YO0d YO0f YO09 YP09 YL0g YL0i YL01 YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract FrameAPI.

Section Link.
Context {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
  (SK : sink_syms) (ra empty : Z).
Hypothesis FF : StatementUbsan.frame_facts B API LS SH SK ra empty.

Lemma lk_segs : ms_segs B = Img0.rsegs.
Proof.
  pose proof FF as F. unfold StatementUbsan.frame_facts in F.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma lk_frame_G_free (fx : FPState) :
  forall L A mem md a, aa_MR (API rc) L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Proof.
  pose proof (@ManifestFF.ff_allocator fx rc B API LS SH SK ra empty FF) as FA. unfold frame_allocator in FA.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  match goal with H : forall L A mem md a, aa_MR (API rc) L A mem md -> in_globals frame_G a -> ~ owned B L A a |- _ =>
    exact H end.
Qed.

Lemma lk_errno_low : ManifestB.errno_low B.
Proof. exact (@ManifestFF.ff_errno_low rc B API LS SH SK ra empty FF). Qed.

Lemma lk_malloc : forall fx : FPState, @malloc_contract fx rc B (API rc).
Proof. intros fx. exact (@ManifestFF.ff_malloc fx rc B API LS SH SK ra empty FF). Qed.

Lemma lk_free : forall fx : FPState, @free_contract fx rc B (API rc).
Proof. intros fx. exact (@ManifestFF.ff_free fx rc B API LS SH SK ra empty FF). Qed.

Lemma L_fuzz_malloc : forall fx : FPState, @fuzz_malloc_c.fuzz_malloc_contract fx rc B (API rc).
Proof.
  intros fx.
  exact (@fuzz_malloc.fuzz_malloc_holds fx rc B (API rc) lk_segs
           (proj1 (ManifestFF.ff_malloc_syms_omx B API LS SH SK ra empty FF)) lk_errno_low
           (@fuzz_malloc.omx_globals_free fx rc B (API rc) lk_segs
              (@ManifestFF.ff_alloc_extra fx rc B API LS SH SK ra empty FF) (lk_frame_G_free fx)
              (ManifestFF.ff_globals B API LS SH SK ra empty FF))
           (lk_malloc fx)).
Qed.

Lemma L_fuzz_free : forall fx : FPState, @fuzz_free_c.fuzz_free_contract fx rc B (API rc).
Proof.
  intros fx.
  exact (@fuzz_free.fuzz_free_holds fx rc B (API rc) lk_segs
           (proj2 (ManifestFF.ff_malloc_syms_omx B API LS SH SK ra empty FF))
           (ManifestFF.ff_globals B API LS SH SK ra empty FF)
           (@ManifestFF.ff_alloc_extra fx rc B API LS SH SK ra empty FF) (lk_frame_G_free fx)
           (lk_free fx)).
Qed.

Hypothesis SCAN : readings_scan_c.readings_scan_contract.

Lemma L_readings : forall fx : FPState, @readings_c.readings_contract fx rc B (API rc).
Proof.
  intros fx.
  pose proof lk_segs as SEG.
  pose proof (@ManifestFF.ff_statics_free fx rc B API LS SH SK ra empty FF) as SF.
  pose proof (ManifestFF.ff_statics_facts B API LS SH SK ra empty FF) as SFA.
  pose proof (@ManifestFF.ff_ctx_owned fx rc B API LS SH SK ra empty FF) as CTX.
  pose proof (@ManifestFF.ff_alloc_extra fx rc B API LS SH SK ra empty FF) as AX.
  pose proof (@ManifestFF.ff_block_slack_present fx rc B API LS SH SK ra empty FF) as BSP.
  pose proof lk_errno_low as ERR.
  pose proof (ManifestFF.ff_guard_syms B API LS SH SK ra empty FF) as GS.
  pose proof L_strlen as STRLEN. pose proof L_snprintf as SNP. pose proof L_strstr as STRS.
  pose proof L_fuzz_malloc as MALLOC. pose proof L_fuzz_free as FREE.
  eapply readings.rd_core; eassumption.
Qed.

Lemma L_names : forall fx : FPState, @names_c.names_contract fx rc B (API rc).
Proof.
  intros fx. eapply names.names_holds; first [exact lk_errno_low | exact L_readings].
Qed.

Lemma L_as_ruled : forall fx : FPState, @as_ruled_c.as_ruled_contract fx rc B (API rc).
Proof.
  intros fx.
  exact (@as_ruled.as_ruled_holds fx rc B (API rc) lk_errno_low (ManifestFF.ff_guard_syms B API LS SH SK ra empty FF)
           L_names L_expected).
Qed.

Lemma L_check_reject_clean_starved :
  forall fx : FPState, @check_reject_clean_starved_c.check_reject_clean_starved_contract fx rc B (API rc).
Proof.
  intros fx.
  exact (@check_reject_clean_starved.check_reject_clean_starved_holds fx rc B (API rc) lk_errno_low
           (@ManifestFF.ff_statics_free fx rc B API LS SH SK ra empty FF)
           (ManifestFF.ff_statics_facts B API LS SH SK ra empty FF)
           (@ManifestFF.ff_alloc_extra fx rc B API LS SH SK ra empty FF)
           (ManifestFF.ff_guard_syms B API LS SH SK ra empty FF)
           L_fuzz_alloc_live L_fuzz_alloc_fail L_names L_check_reject_clean).
Qed.

Lemma L_check_no_overread : forall fx : FPState, @check_no_overread_c.check_no_overread_contract fx rc B (API rc).
Proof.
  intros fx.
  exact (@check_no_overread.check_no_overread_holds fx rc B (API rc)
           (@ManifestFF.ff_alloc_extra fx rc B API LS SH SK ra empty FF)
           (@ManifestFF.ff_ctx_owned fx rc B API LS SH SK ra empty FF)
           (ManifestFF.ff_statics_facts B API LS SH SK ra empty FF)
           (@ManifestFF.ff_statics_free fx rc B API LS SH SK ra empty FF)
           lk_errno_low (ManifestFF.ff_statics_noerrno B API LS SH SK ra empty FF)
           (ManifestFF.ff_malloc_syms_omx B API LS SH SK ra empty FF)
           lk_malloc lk_free L_memcpy L_memset L_names).
Qed.

Lemma L_check_round_trip : forall fx : FPState, @check_round_trip_c.check_round_trip_contract fx rc B (API rc).
Proof.
  intros fx.
  exact (@check_round_trip.check_round_trip_holds fx rc B (API rc) L_names L_as_ruled lk_malloc lk_free
           L_snprintf strlen.strlen_holds L_plain
           (ManifestFF.ff_statics_facts B API LS SH SK ra empty FF)
           (@ManifestFF.ff_statics_free fx rc B API LS SH SK ra empty FF)
           lk_errno_low
           (@ManifestFF.ff_ctx_owned fx rc B API LS SH SK ra empty FF)
           (ManifestFF.ff_guard_syms B API LS SH SK ra empty FF)
           (ManifestFF.ff_statics_noerrno B API LS SH SK ra empty FF)
           (ManifestFF.ff_malloc_syms_omx B API LS SH SK ra empty FF)
           (@ManifestFF.ff_alloc_extra fx rc B API LS SH SK ra empty FF)
           (@ManifestFF.ff_block_slack_present fx rc B API LS SH SK ra empty FF)).
Qed.

End Link.
