From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 MemNorm FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel put_dec_c.
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Notation LOWTOP := 140735332483072%Z (only parsing).

Lemma rsegs_low : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? LOWTOP) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma find_segment_in : forall (l : list Segment) x n seg, find_segment l x n = Some seg ->
  In seg l /\ Z.of_N (seg_base seg) <= x /\ x + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction l as [|s l IH]; intros x n seg H; cbn in H; [discriminate|].
  destruct (_ && _)%bool eqn:E.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity | lia].
  - destruct (IH x n seg H) as (H1 & H2 & H3). split; [right; exact H1 | lia].
Qed.

Lemma noseg : forall x, LOWTOP <= x -> find_segment rsegs x 1 = None.
Proof.
  intros x Hx. destruct (find_segment rsegs x 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. destruct (find_segment_in rsegs x 1 seg E) as (Hin & H1 & H2).
  pose proof (proj1 (forallb_forall _ rsegs) rsegs_low seg Hin) as H. cbv beta in H. apply Z.leb_le in H. lia.
Qed.

Lemma noseg_ro : forall x, LOWTOP <= x < 2 ^ 64 -> ro_addr rsegs (wa x) = false.
Proof. intros x Hx. unfold ro_addr. rewrite (wa_unsigned x) by lia. rewrite (noseg x) by lia. reflexivity. Qed.

Lemma noseg_rom : forall x, LOWTOP <= x < 2 ^ 64 -> seg_rom rsegs (wa x) = None.
Proof. intros x Hx. apply seg_rom_unmapped. rewrite wa_unsigned by lia. apply noseg. lia. Qed.

Lemma noseg_mrd : forall m x b, LOWTOP <= x < 2 ^ 64 -> mrd rsegs m (wa x) = Some b -> m (wa x) = Some b.
Proof. intros m x b Hx H. unfold mrd in H. destruct (m (wa x)); [exact H|]. rewrite noseg_rom in H by lia. discriminate. Qed.

Definition mfr (W : list ivl) (m m' : word -> option byte) : Prop :=
  munch W m m' /\ wmono rsegs m m' /\ (forall x, m x <> None -> m' x <> None).

Lemma mfr_refl : forall W m, mfr W m m.
Proof. intros W m. split; [apply munch_refl|]. split; [apply wmono_refl|]. tauto. Qed.

Lemma mfr_trans : forall W m1 m2 m3, mfr W m1 m2 -> mfr W m2 m3 -> mfr W m1 m3.
Proof.
  intros W m1 m2 m3 (A1 & B1 & C1') (A2 & B2 & C2'). split; [eapply munch_trans; eauto|].
  split; [eapply wmono_trans; eauto|]. auto.
Qed.

Lemma mfr_weaken : forall W W' m m', mfr W m m' -> sub_fp W W' -> mfr W' m m'.
Proof. intros W W' m m' (A1 & B1 & C1') HS. split; [eapply munch_weaken; eauto|]. auto. Qed.

Lemma mfr_write : forall W m0 m a bs, mfr W m0 m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  inside W a (Z.of_nat (length bs)) -> mfr W m0 (write_to_mem m (wa a) bs).
Proof.
  intros W m0 m a bs (A1 & B1 & C1') Ha Hl Hin. split; [apply munch_write; auto|].
  split; [apply wmono_write; auto|].
  intros x Hx. rewrite write_to_mem_spec by lia.
  destruct (_ && _)%bool eqn:E; [|apply C1'; exact Hx].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  destruct (nth_error bs (Z.to_nat (bv_unsigned x - a))) eqn:N; [discriminate|].
  apply nth_error_None in N. lia.
Qed.

Lemma mfr_bytes : forall W m m' a bs, mfr W m m' -> bytes_at rsegs m a bs ->
  disjoint_from W a (Z.of_nat (length bs)) -> bytes_at rsegs m' a bs.
Proof. intros W m m' a bs (A1 & _ & _) H Hd. eapply bytes_at_transport; eauto. Qed.

Lemma mfr_wr : forall W m m' a n, mfr W m m' -> wr_at rsegs m a n -> wr_at rsegs m' a n.
Proof. intros W m m' a n (_ & B1 & _) H. eapply wr_at_transport; eauto. Qed.

Lemma mfr_stk : forall W m m' lo hi, mfr W m m' -> stk rsegs m lo hi -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (_ & B1 & C1') (H1 & H2 & H). split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hw [b Hb]]. split; [apply B1, Hw|].
  unfold mrd in Hb |- *. destruct (m (wa a)) as [b0|] eqn:E.
  - destruct (m' (wa a)) as [b1|] eqn:E'; [exists b1; reflexivity|].
    exfalso. apply (C1' (wa a)); [rewrite E; discriminate | exact E'].
  - destruct (m' (wa a)) as [b1|]; [exists b1; reflexivity | exists b; exact Hb].
Qed.

Lemma bytes_at_ro_agree : forall m a bs, ro_agree rsegs m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  ro_bytes rsegs a bs -> bytes_at rsegs m a bs.
Proof.
  intros m a bs HR Ha Hl Hb. split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
  destruct (nth_error bs i) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  destruct (ro_bytes_nth rsegs bs a i b Hb E) as [H1 H2]. rewrite (HR _ H2). exact H1.
Qed.

Lemma stk_norm : forall m lo hi, LOWTOP <= lo -> stk rsegs m lo hi -> stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  assert (Hro : ro_addr rsegs (wa a) = false) by (apply noseg_ro; lia).
  pose proof (mem_rel_normalize rsegs m) as R.
  destruct (H a Ha) as [Hw Hb]. split.
  - unfold wview, normalize. rewrite Hro. exact Hw.
  - unfold mrd, normalize. rewrite Hro. exact Hb.
Qed.

Lemma wr_norm : forall m a n, LOWTOP <= a -> a + n <= 2 ^ 64 -> wr_at rsegs m a n -> wr_at rsegs (normalize rsegs m) a n.
Proof.
  intros m a n Ha Hn (H1 & H2 & H). split; [lia|]. split; [lia|]. intros i Hi.
  assert (Hro : ro_addr rsegs (wa (a + i)) = false) by (apply noseg_ro; lia).
  unfold wview, normalize. rewrite Hro. apply H. exact Hi.
Qed.

Ltac retpc := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?x)] =>
  replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (apply bv_eq; vm_compute; reflexivity) end.

Lemma outside_dec : forall W x, {outside W x} + {~ outside W x}.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|].
  - right. intros [H _]. lia.
  - destruct (IH x) as [H|H]; [left; split; [lia | exact H] | right; tauto].
  - destruct (IH x) as [H|H]; [left; split; [lia | exact H] | right; tauto].
Qed.

Lemma mfr_of : forall W m m', munch W m m' -> wmono rsegs m m' ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ outside W z -> LOWTOP <= z /\ exists b, mrd rsegs m' (wa z) = Some b) ->
  mfr W m m'.
Proof.
  intros W m m' MU WM H. split; [exact MU|]. split; [exact WM|].
  intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Hr. unfold bv_modulus in Hr. cbn in Hr.
  destruct (outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - rewrite (MU x Ho). exact Hx.
  - destruct (H (bv_unsigned x) ltac:(lia) Ho) as [HL [b Hb]].
    assert (Ex : wa (bv_unsigned x) = x) by (unfold wa; apply Z_to_bv_bv_unsigned).
    rewrite Ex in Hb. rewrite <- Ex in Hb |- *. rewrite (noseg_mrd m' (bv_unsigned x) b ltac:(lia) Hb). discriminate.
Qed.

Lemma bytes_at_mrd : forall m a bs z, bytes_at rsegs m a bs -> a <= z < a + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa z) = Some b.
Proof.
  intros m a bs z (H1 & H2 & H) Hz.
  destruct (nth_error bs (Z.to_nat (z - a))) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  exists b. rewrite <- E. rewrite <- H by lia. f_equal. f_equal. lia.
Qed.

Lemma stk_mrd : forall m lo hi z, stk rsegs m lo hi -> lo <= z < hi -> exists b, mrd rsegs m (wa z) = Some b.
Proof. intros m lo hi z (_ & _ & H) Hz. exact (proj2 (H z Hz)). Qed.

Lemma pd_call : put_dec_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo b p v mn : Z) (N : word)
         (Q : machine_state -> Prop),
    a0 = Z_to_bv 64 b -> a1 = Z_to_bv 64 p -> bv_unsigned a2 mod 2^32 = v -> (bv_unsigned a2 < 2^32 \/ 10 <= v) ->
    a3 = Z_to_bv 64 mn -> 0 <= mn <= 10 ->
    bytes_at rsegs m p (le8 N) -> wr_at rsegs m p 8 -> p mod 8 = 0 ->
    wr_at rsegs m (b + bv_unsigned N) (dec_len v mn) ->
    ro_agree rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + PUT_DEC_FRAME <= bv_unsigned sp -> LOWTOP <= lo ->
    LOWTOP <= p -> p + 8 <= 2 ^ 64 -> LOWTOP <= b + bv_unsigned N -> b + bv_unsigned N + dec_len v mn <= 2 ^ 64 ->
    (p + 8 <= b + bv_unsigned N \/ b + bv_unsigned N + dec_len v mn <= p) ->
    (p + 8 <= bv_unsigned sp - PUT_DEC_FRAME \/ bv_unsigned sp <= p) ->
    (b + bv_unsigned N + dec_len v mn <= bv_unsigned sp - PUT_DEC_FRAME \/ bv_unsigned sp <= b + bv_unsigned N) ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       mfr [(bv_unsigned sp - PUT_DEC_FRAME, bv_unsigned sp); (p, p + 8);
            (b + bv_unsigned N, b + bv_unsigned N + dec_len v mn)] m m' ->
       ro_agree rsegs m' ->
       bytes_at rsegs m' (b + bv_unsigned N) (DEC v mn) ->
       bytes_at rsegs m' p (le8 (Z_to_bv 64 (bv_unsigned N + dec_len v mn))) ->
       evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 PUT_DEC) fc None m (seg_rom rsegs)).
Proof.
  intros PD ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo b p v mn N Q E0 E1 E2 E2' E3 Hmn HP HWP Hp8 HWB HRO HST HLO HLT HPL HPH HBL HBH D1 D2 D3 K.
  pose proof (mem_rel_normalize rsegs m HRO) as MR0.
  eapply evt_cut.
  { apply (evt_normalize rsegs) with (m := m); [exact wx_apart_rsegs | exact HRO |].
    eapply PD; try eassumption.
    - apply bytes_at_normalize; assumption.
    - apply wr_norm; [lia | lia | exact HWP].
    - apply wr_norm; [lia | lia | exact HWB].
    - apply mem_inv_normalize.
    - apply stk_norm; assumption. }
  intros s (s0' & (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                   -> & MU & WM & MI & ST & HD & HN) & RL & RS).
  destruct s as [R' F' pc' svc' rv' fc' m' ro'].
  destruct RL as (ER & EF & Epc & Esvc & Erv & Efc & Erom & MR1). cbn in ER, EF, Epc, Esvc, Erv, Efc, Erom, MR1, RS.
  subst R' F' pc' svc' rv' fc' ro'.
  change {| ms_regs := mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6';
            ms_fregs := F; ms_pc_val := ret_pc ra; ms_svc_pending := None; ms_resv := None; ms_fcsr := fc;
            ms_mem := m'; ms_rom := seg_rom rsegs |}
    with (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)).
  apply K.
  - apply mfr_of; [eapply munch_rel; eauto | eapply wmono_rel; eauto |].
    intros z Hz Ho. cbn [outside] in Ho.
    assert (Hc : (bv_unsigned sp - PUT_DEC_FRAME <= z < bv_unsigned sp) \/ (p <= z < p + 8) \/
                 (b + bv_unsigned N <= z < b + bv_unsigned N + dec_len v mn)) by lia.
    rewrite (mrd_rel rsegs m' m0' (wa z) MR1).
    destruct Hc as [Hc|[Hc|Hc]]; (split; [lia|]).
    + apply (stk_mrd m0' lo (bv_unsigned sp)); [exact ST | lia].
    + apply (bytes_at_mrd m0' p _ z HN). rewrite length_le8. lia.
    + apply (bytes_at_mrd m0' _ _ z HD). unfold dec_len in Hc. lia.
  - eapply ro_agree_same; eauto.
  - apply (proj2 (bytes_at_rel rsegs m' m0' _ _ MR1)). exact HD.
  - apply (proj2 (bytes_at_rel rsegs m' m0' _ _ MR1)). exact HN.
Qed.

Lemma rd_all : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. rewrite <- (Z.add_0_r a) at 1.
  rewrite (bytes_at_read rsegs m a bs 0 (length bs) H) by lia. cbn [Z.to_nat skipn]. rewrite firstn_all. reflexivity.
Qed.

Lemma rd_q64 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof. intros m a v H. rewrite <- (length_le8 v) at 1. apply rd_all. exact H. Qed.

Lemma rd_byte : forall m a bs k b, bytes_at rsegs m a bs -> nth_error bs k = Some b ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 1 = Some [b].
Proof.
  intros m a bs k b H E. assert (Hk : (k < length bs)%nat) by (apply nth_error_Some; congruence).
  rewrite (bytes_at_read rsegs m a bs (Z.of_nat k) 1 H) by lia. rewrite Nat2Z.id.
  clear H. revert k E Hk. induction bs as [|x bs IH]; intros [|k] E Hk; cbn in *; try discriminate; try lia.
  - injection E as ->. reflexivity.
  - apply IH; [exact E | lia].
Qed.

Lemma rd_b1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof. intros m a b H. exact (rd_all m a [b] H). Qed.

Ltac st_ok A n :=
  lazymatch goal with
  | WR : wr_at rsegs ?m ?lo ?len |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      let HS := fresh "HS" in
      pose proof (wr_at_store_ok rsegs m lo len (A - lo) n WR ltac:(lia) ltac:(lia)) as HS;
      replace (lo + (A - lo)) with A in HS by lia
  end.

Ltac after_st :=
  try fix_lit_store;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    let A := addr_expr a in
    change (write_to_mem m a bs) with (write_to_mem m (wa A) bs);
    repeat match goal with
    | H : bytes_at rsegs m ?A2 ?bs2 |- _ =>
        first [ apply (bytes_at_write_other rsegs m A bs A2 bs2) in H; [ | lia | simpl_sizes; lia | simpl_sizes; lia ]
              | clear H ]
    | H : wr_at rsegs m ?A2 ?n2 |- _ => apply (wr_at_write rsegs m A2 n2 (wa A) bs) in H
    | H : stk rsegs m ?lo ?hi |- _ => apply (stk_write rsegs m lo hi A bs) in H; [ | lia | simpl_sizes; lia ]
    | H : mfr ?W ?m0 m |- _ =>
        apply (mfr_write W m0 m A bs) in H; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; lia ]
    | H : ov_read_bytes rsegs m _ _ = _ |- _ => clear H
    | H : store_ok rsegs m _ _ = true |- _ => clear H
    end;
    let H := fresh "NW" in
    pose proof (bytes_at_write_same rsegs m A bs ltac:(lia) ltac:(simpl_sizes; lia)) as H;
    let m' := fresh "m" in
    remember (write_to_mem m (wa A) bs) as m' eqn:Heqm; clear Heqm
  end.

From Stdlib Require Import Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Contract KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import RcIdentModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP URzKP.

Lemma s1_outside1 : forall lo hi x, outside [(lo, hi)] x <-> ~ (lo <= x < hi).
Proof. intros lo hi x. cbn. tauto. Qed.

Lemma s1_mbyte_eq : forall segs (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte segs m' a = mbyte segs m a.
Proof. intros segs m m' a H. unfold mbyte. rewrite H. reflexivity. Qed.

Lemma s1_wr_eq : forall segs (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> (writable_at segs m a <-> writable_at segs m' a).
Proof. intros segs m m' a H. unfold writable_at, wview. rewrite H. tauto. Qed.

Lemma s1_ba_keep : forall segs m m' a bs, bytes_at segs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> m' (Z_to_bv 64 (a + i)) = m (Z_to_bv 64 (a + i))) ->
  bytes_at segs m' a bs.
Proof.
  intros segs m m' a bs (H1 & H2 & H) Hk. split; [exact H1|]. split; [exact H2|].
  intros i Hi. rewrite <- (H i Hi). unfold mrd, wa. rewrite (Hk (Z.of_nat i)) by lia. reflexivity.
Qed.

Lemma s1_img_bytes : forall m a bs, ro_agree rsegs m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  ro_bytes_b rsegs a bs = true -> bytes_at rsegs m a bs.
Proof.
  intros m a bs Hra Ha Hl Hb. apply bytes_at_ro_agree; try assumption. apply ro_bytes_b_sound. exact Hb.
Qed.

Lemma s1_bytes_low : forall W m m' a bs C, bytes_at rsegs m a bs -> mfr W m m' ->
  (forall x, ~ outside W x -> C <= x) -> a + Z.of_nat (length bs) <= C -> bytes_at rsegs m' a bs.
Proof.
  intros W m m' a bs C H (MU & _ & _) HW HC. pose proof (bytes_at_bound rsegs m a bs H) as HB.
  apply (s1_ba_keep rsegs m); [exact H|]. intros i Hi. apply MU.
  rewrite MState.unsigned_lit by lia.
  destruct (outside_dec W (a + i)) as [Ho|Ho]; [exact Ho|]. specialize (HW _ Ho). lia.
Qed.

Lemma s1_bytes_sub : forall m a bs k, bytes_at rsegs m a bs -> (k < length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) [nth k bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k (H1 & H2 & H) Hk. split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i.
  rewrite Z.add_0_r. rewrite (H k Hk). cbn. apply nth_error_nth'. exact Hk.
Qed.

Lemma s1_bytes_split : forall m a l1 l2, bytes_at rsegs m a (l1 ++ l2) ->
  bytes_at rsegs m a l1 /\ bytes_at rsegs m (a + Z.of_nat (length l1)) l2.
Proof. intros m a l1 l2 H. apply bytes_at_app. exact H. Qed.

Lemma s1_bytes_join : forall m a l1 l2, bytes_at rsegs m a l1 -> bytes_at rsegs m (a + Z.of_nat (length l1)) l2 ->
  bytes_at rsegs m a (l1 ++ l2).
Proof. intros m a l1 l2 H1 H2. apply bytes_at_app. split; assumption. Qed.

Lemma has_dash_cons : forall b r, has_dash (b :: r) = (bz b =? 45) || has_dash r.
Proof. reflexivity. Qed.

Lemma tok_go_len : forall l d, length (tok_go d l) = (length l - (if negb d && has_dash l then 1 else 0))%nat.
Proof.
  induction l as [|b r IH]; intros d.
  - destruct d; reflexivity.
  - cbn [tok_go]. rewrite has_dash_cons.
    destruct d; cbn [negb andb].
    + cbn [length]. rewrite IH. cbn [negb andb]. lia.
    + destruct (Z.eqb_spec (bz b) 45) as [E|E]; cbn [orb].
      * rewrite IH. cbn [negb andb length]. lia.
      * cbn [length]. rewrite IH. cbn [negb andb]. destruct (has_dash r) eqn:Hr; [|lia].
        assert (length r >= 1)%nat by (destruct r; [discriminate|cbn; lia]). lia.
Qed.

Lemma n_TK_len : forall inp, Z.of_nat (length (n_TK inp)) = n_lt inp.
Proof.
  intros inp. unfold n_TK, TOK, n_lt, n_ln. rewrite tok_go_len. cbn [negb andb].
  destruct (has_dash (n_EXP_NM inp)) eqn:H; [|lia].
  destruct (n_EXP_NM inp) as [|x r]; [discriminate|]. cbn [length]. lia.
Qed.

Lemma n_r_cases : forall inp, n_r inp = 0 \/ n_r inp = -1.
Proof. intros inp. unfold n_r. destruct (_ && _); auto. Qed.

Lemma n_r_zero : forall inp, n_r inp = 0 -> n_wok inp = true /\ n_fits inp = true.
Proof.
  intros inp H. unfold n_r in H. destruct (n_wok inp) eqn:E1, (n_fits inp) eqn:E2; cbn in H; try discriminate.
  split; reflexivity.
Qed.

Lemma n_fits_spec : forall inp, n_fits inp = true ->
  n_ln inp < t_cap_name inp /\ n_lt inp < t_cap_tok inp /\ n_ld inp < t_cap_disp inp.
Proof.
  intros inp H. unfold n_fits in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H1, H2, H3. auto.
Qed.

Lemma FAM_range : forall idb, 0 <= FAM idb <= 3.
Proof.
  intros idb. unfold FAM, reac_box_family_of_c.FAMOF_FAM. cbv zeta.
  destruct (1 =? 0); [lia|]. destruct (_ =? 0); [lia|].
  destruct (list_eq_dec _ _ _); [lia|]. destruct (list_eq_dec _ _ _); [lia|]. destruct (list_eq_dec _ _ _); lia.
Qed.

Lemma n_fam_range : forall inp, 0 <= n_fam inp < 128.
Proof.
  intros inp. unfold n_fam. destruct (128 <=? t_fam_raw inp).
  - change 127 with (Z.ones 7). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (t_fam_raw inp) (2 ^ 7) ltac:(lia)). lia.
  - pose proof (FAM_range (idT inp)). lia.
Qed.

Lemma bz_range' : forall b : byte, 0 <= bz b < 256.
Proof. exact bz_range. Qed.

Lemma zb_bz : forall b : byte, Z_to_bv 8 (bz b) = b.
Proof. intros b. unfold bz. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma first_zero_nth : forall l, (first_zero l < length l)%nat -> bz (nth (first_zero l) l (zb 0)) = 0.
Proof.
  induction l as [|x l IH]; cbn [first_zero length]; intros H; [lia|].
  destruct (Z.eqb_spec (bz x) 0) as [E|E]; [exact E|]. cbn [nth]. apply IH. lia.
Qed.

Lemma first_zero_nz : forall l k, (k < first_zero l)%nat -> bz (nth k l (zb 0)) <> 0.
Proof.
  induction l as [|x l IH]; cbn [first_zero]; intros k H; [lia|].
  destruct (Z.eqb_spec (bz x) 0) as [E|E]; [lia|]. destruct k as [|k]; cbn [nth]; [exact E|]. apply IH. lia.
Qed.

Lemma first_zero_le_len : forall l, (first_zero l <= length l)%nat.
Proof. induction l as [|x l IH]; cbn; [lia|]. destruct (bz x =? 0); lia. Qed.

Lemma model_name_len : forall idb, length idb = ID_SIZE -> length (model_name idb) = 17%nat.
Proof.
  intros idb H. unfold model_name, get, OFF_NAME, NAME_CAP. rewrite length_firstn, length_skipn.
  unfold ID_SIZE in H. lia.
Qed.

Lemma firstn_S_nth : forall (l : list byte) k d, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l d].
Proof.
  induction l as [|x l IH]; intros k d H; cbn [length] in H; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.

Lemma bytes_at_fs : forall m a l k n, bytes_at rsegs m a l -> (k + n <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n (H1 & H2 & H) Hkn.
  assert (Hlen : length (firstn n (skipn k l)) = n) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Hlen; lia|]. intros i Hi. rewrite Hlen in Hi.
  rewrite <- Z.add_assoc, <- Nat2Z.inj_add. rewrite H by lia.
  rewrite nth_error_firstn. destruct (Nat.ltb_spec i n); [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

Lemma name_cstr : forall m a idb, bytes_at rsegs m a idb -> length idb = ID_SIZE -> bz (nthb idb 19) = 0 ->
  cstr m (a + 3) (name_str idb).
Proof.
  intros m a idb H Hl H19. pose proof (model_name_len idb Hl) as Lm.
  assert (Hm : nth 16 (model_name idb) (zb 0) = nth 19 idb (zb 0)).
  { unfold model_name, get, OFF_NAME, NAME_CAP. rewrite nth_first by lia.
    rewrite (nth_skip0 (skipn 3 idb)), skipn_skipn, <- nth_skip0. reflexivity. }
  assert (Hf : (first_zero (model_name idb) <= 16)%nat).
  { apply first_zero_le; [lia|]. rewrite Hm. exact H19. }
  assert (Hz : nth (first_zero (model_name idb)) (model_name idb) (zb 0) = z8).
  { pose proof (first_zero_nth (model_name idb) ltac:(lia)) as E.
    rewrite <- (zb_bz (nth _ (model_name idb) (zb 0))). rewrite E. reflexivity. }
  unfold cstr, name_str. rewrite <- Hz. rewrite <- firstn_S_nth by lia.
  unfold model_name, get, OFF_NAME, NAME_CAP. rewrite firstn_firstn.
  replace (Nat.min (S (first_zero (firstn 17 (skipn 3 idb)))) 17) with (S (first_zero (firstn 17 (skipn 3 idb))))
    by (unfold model_name, get, OFF_NAME, NAME_CAP in Hf; lia).
  change 3 with (Z.of_nat 3). apply bytes_at_fs; [exact H|].
  unfold model_name, get, OFF_NAME, NAME_CAP in Hf. unfold ID_SIZE in Hl. lia.
Qed.

Lemma name_nz : forall idb k, (k < length (name_str idb))%nat -> bz (nth k (name_str idb) (zb 0)) <> 0.
Proof.
  intros idb k Hk. unfold name_str in *. rewrite length_firstn in Hk. rewrite nth_first by lia.
  apply first_zero_nz. lia.
Qed.

Lemma wr_sub : forall m a n a' n', wr_at rsegs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at rsegs m a' n'.
Proof.
  intros m a n a' n' (H1 & H2 & H) Ha Hb Hn. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

Lemma mfr_ro : forall W m m', ro_agree rsegs m -> mfr W m m' -> (forall x, ~ outside W x -> LOWTOP <= x) ->
  ro_agree rsegs m'.
Proof.
  intros W m m' HR (MU & _ & _) HW a Ha. rewrite <- (HR a Ha). unfold mrd.
  assert (Hlo : bv_unsigned a < LOWTOP).
  { unfold ro_addr in Ha. destruct (find_segment rsegs (bv_unsigned a) 1) as [seg|] eqn:E; [|discriminate].
    destruct (find_segment_in rsegs _ 1 seg E) as (Hin & H1 & H2).
    pose proof (proj1 (forallb_forall _ rsegs) rsegs_low seg Hin) as H. cbv beta in H. apply Z.leb_le in H. lia. }
  rewrite (MU a); [reflexivity|]. destruct (outside_dec W (bv_unsigned a)) as [Ho|Ho]; [exact Ho|].
  specialize (HW _ Ho). lia.
Qed.

Lemma nthb_mn0 : forall idb, length idb = ID_SIZE -> nthb (model_name idb) 0 = nthb idb 3.
Proof.
  intros idb Hl. unfold nthb, model_name, get, OFF_NAME, NAME_CAP. rewrite nth_first by lia.
  rewrite <- nth_skip0. reflexivity.
Qed.

Section TacSh1.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma s1_segs : ms_segs B = rsegs.
Proof using FF. destruct FF as [H _]. exact H. Qed.

Lemma s1_img : img_low B.
Proof using FF.
  apply (img_low_of_check B 140735332483072).
  - unfold img_check. rewrite s1_segs. vm_compute. reflexivity.
  - pose proof alloc_ceiling_val. lia.
Qed.

Lemma s1_seg_low : forall x seg, find_segment rsegs x 1 = Some seg -> 0 <= x < alloc_ceiling.
Proof using FF. intros x seg H. destruct s1_img as [_ HI]. rewrite s1_segs in HI. exact (HI x seg H). Qed.

Lemma s1_img_low : forall a, in_img B a -> 0 <= a < alloc_ceiling.
Proof using FF. intros a H. destruct s1_img as [HI _]. exact (HI a H). Qed.

Lemma s1_ro_low : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < alloc_ceiling.
Proof using FF.
  intros a H. unfold ro_addr in H. destruct (find_segment rsegs (bv_unsigned a) 1) as [seg|] eqn:E; [|discriminate].
  exact (proj2 (s1_seg_low _ seg E)).
Qed.

Lemma s1_hi_noseg : forall a : word, alloc_ceiling <= bv_unsigned a -> find_segment rsegs (bv_unsigned a) 1 = None.
Proof using FF.
  intros a H. destruct (find_segment rsegs (bv_unsigned a) 1) as [seg|] eqn:E; [|reflexivity].
  pose proof (s1_seg_low _ seg E). lia.
Qed.

Lemma s1_FR_regs : forall g km hb L A regs regs' mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  FR B APIf ra empty g km hb L A regs' mem md.
Proof.
  intros g km hb L A regs regs' mem md (H1 & H2 & H3 & H4 & H) E2 E3 E4.
  split; [exact H1|]. rewrite E2, E3, E4. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. exact H.
Qed.

Lemma s1_FR_frame : forall g km hb L A regs mem md mem',
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  munch [(g_S g - SLOT_K, g_S g - 104)] mem mem' ->
  wmono rsegs mem mem' ->
  FR B APIf ra empty g km hb L A regs mem' md.
Proof using FF.
  intros g km hb L A regs mem md mem' HF HP HM HW.
  pose proof s1_segs as ES.
  pose proof FF as (_ & _ & _ & _ & _ & _ & HERR & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTP & HEO & _ &
                    HOH & HOL & HTH & _ & _ & _ & _ & HRL & _).
  destruct HF as (HGV & Hsp & Hgp & Htp & Hsav & Hstk & HMI & Hrel & HMR & HWF & Hbd & Hin & Hmd & Hhi & Himg &
                  Hblk & Herr & Hsink & HRES & Hwr).
  pose proof HGV as (Hn & Hp & Hbd0 & HS16 & HSK & HS47 & Hroom & HgS & Htp0).
  pose proof alloc_ceiling_val as Hc. pose proof (HERR rc) as Herrc.
  unfold FR. unfold SLOT_K, SLOT_STACK in *.
  assert (Hout : forall a, 0 <= a < 2 ^ 64 -> a < g_S g - 65536 \/ g_S g - 104 <= a ->
                 mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hx. apply HM. rewrite MState.unsigned_lit by exact Ha. apply s1_outside1. lia. }
  assert (Hlow : forall a, 0 <= a < alloc_ceiling -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a))
    by (intros a Ha; apply Hout; lia).
  assert (HE0 : 0 <= errno_addr B) by (unfold errno_addr; rewrite HTP, HEO; lia).
  split; [exact HGV|]. split; [exact Hsp|]. split; [exact Hgp|]. split; [exact Htp|].
  split.
  { apply (s1_ba_keep rsegs mem); [exact Hsav|]. intros i Hi.
    assert (Hl : length (saved_bytes ra g) = 104%nat)
      by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
    rewrite Hl in Hi. apply Hout; lia. }
  split.
  { destruct Hstk as (S1 & S2 & SH0). split; [exact S1|]. split; [exact S2|]. intros a Ha.
    destruct (SH0 a Ha) as (Hw & _).
    assert (Hu : bv_unsigned (wa a) = a) by (unfold wa; apply MState.unsigned_lit; lia).
    pose proof (HW (wa a) Hw) as Hw'. split; [exact Hw'|].
    assert (Hns : find_segment rsegs (bv_unsigned (wa a)) 1 = None) by (apply s1_hi_noseg; lia).
    unfold wview in Hw'. rewrite Hns in Hw'. unfold mrd.
    destruct (mem' (wa a)) as [b|]; [exists b; reflexivity | exfalso; apply Hw'; reflexivity]. }
  split.
  { unfold MI in *. intros a Ha. rewrite <- (HMI a Ha). unfold mrd.
    pose proof Ha as Ha'. rewrite ES in Ha'.
    pose proof (s1_ro_low a Ha') as X. pose proof (bv_unsigned_in_range 64 a) as R.
    change (bv_modulus 64) with (2 ^ 64) in R.
    rewrite (HM a); [reflexivity|]. apply s1_outside1. lia. }
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite <- (Hrel a Ha).
    destruct (HRL a Ha) as (Hi & _). pose proof (s1_img_low a Hi). apply s1_mbyte_eq. apply Hlow. lia. }
  assert (Hcond : forall x, 0 <= x < alloc_ceiling ->
      (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
      outside [(g_S g - 65536, g_S g - 104)] x) by (intros x Hx _; apply s1_outside1; lia).
  split; [exact (kb_MR_A B (APIf rc) L A mem mem' md _ HMR HM Hcond)|].
  split; [exact HWF|]. split; [exact Hbd|]. split; [exact Hin|]. split; [exact Hmd|].
  split.
  { intros a Ha Hs He. destruct (Hhi a Ha Hs He) as [E1 E2].
    assert (Hx : mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) by (apply Hout; lia).
    rewrite (s1_mbyte_eq _ mem mem' a Hx). split; [exact E1|].
    rewrite E2. apply s1_wr_eq. exact Hx. }
  split.
  { intros a Ha H1 H2 H3. destruct (Himg a Ha H1 H2 H3) as [E1 E2]. pose proof (s1_img_low a Ha).
    assert (Hx : mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) by (apply Hlow; lia).
    rewrite (s1_mbyte_eq _ mem mem' a Hx). split; [exact E1|].
    rewrite E2. apply s1_wr_eq. exact Hx. }
  split.
  { intros a k i Hak Hi. rewrite <- (Hblk a k i Hak Hi).
    apply (kb_blocks_munch B (APIf rc) L A mem mem' md _ HMR HM Hcond a k i); [|exact Hi].
    apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hak. }
  split.
  { intros a Ha. apply (s1_wr_eq _ mem mem' a); [apply Hlow; lia | exact (Herr a Ha)]. }
  split.
  { unfold sink_none, closed_stdio_env in *. destruct Hsink as ((V1 & V2) & V3 & V4).
    split; [split|]; [| |split; [|exact V4]].
    - intros k Hk. rewrite <- (V1 k Hk). apply s1_mbyte_eq. apply Hlow. rewrite HTH. lia.
    - intros k Hk. rewrite <- (V2 k Hk). apply s1_mbyte_eq. apply Hlow. rewrite HOL. lia.
    - intros k Hk. rewrite <- (V3 k Hk). apply s1_mbyte_eq. apply Hlow. rewrite HOH. lia. }
  split; [exact HRES|].
  intros a Ha. pose proof (Hwr a Ha) as X. unfold writable_at in *. rewrite ES in X |- *. apply HW. exact X.
Qed.

Lemma s1_FRx : forall g km hb L A regs regs' mem mem' md W,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  mfr W mem mem' -> sub_fp W [(g_S g - SLOT_K, g_S g - 104)] ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  FR B APIf ra empty g km hb L A regs' mem' md.
Proof using FF.
  intros g km hb L A regs regs' mem mem' md W HF HP (MU & WM & _) HS E2 E3 E4.
  apply (s1_FR_regs g km hb L A regs regs' mem' md); [|exact E2|exact E3|exact E4].
  apply (s1_FR_frame g km hb L A regs mem md mem' HF HP); [|exact WM].
  eapply munch_weaken; eassumption.
Qed.

Lemma s1_cut : forall g pc km hb (P : bvmap 5 word -> (word -> option byte) -> Prop) L A regs mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  P regs mem ->
  CUTST B APIf ra empty g pc km hb P (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom (ms_segs B))) md).
Proof. intros. exists L, A, regs, mem, md. split; [reflexivity|]. split; [assumption|]. split; assumption. Qed.

Lemma s1_run : forall regs pc mem md L A (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) P,
  aa_MR (APIf rc) L A mem md ->
  Exec.evt rsegs (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
      K R pc' mem')
    (MState.MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs', K R pc' mem' -> (forall r, getr regs' r = getr R r) ->
     Rz (ms_segs B) (mkCfg (mkst regs' pc' mem' (seg_rom (ms_segs B))) md) P) ->
  Rz (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof using FF.
  intros regs pc mem md L A K P HM HE HK.
  destruct (kb_md B (APIf rc) L A mem md HM) as [Hh Hz].
  apply (kb_run_rz B regs pc mem md K P Hh Hz); [rewrite s1_segs; exact HE | exact HK].
Qed.

Lemma s1_frame_facts : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
  LOWTOP + 16016 <= fsp g /\ fsp g + 368 <= 2 ^ 47 /\ fsp g mod 16 = 0 /\ ro_agree rsegs mem /\
  wr_at rsegs mem (fsp g - 15000) 15264 /\ stk rsegs mem (fsp g - 16016) (fsp g + 368) /\
  getr regs 2 = Z_to_bv 64 (fsp g).
Proof using FF.
  intros g km hb L A regs mem md HF.
  destruct HF as (HGV & Hsp & Hgp & Htp & Hsav & Hstk & HMI & Hrel & HMR & HWF & Hbd & Hin & Hmd & Hhi & Himg &
                  Hblk & Herr & Hsink & HRES & Hwr).
  pose proof HGV as (Hn & Hp & Hbd0 & HS16 & HSK & HS47 & Hroom & HgS & Htp0).
  pose proof alloc_ceiling_val as Hc. unfold SLOT_K, SLOT_STACK in *. unfold fsp, SLOT_FRAME.
  split; [lia|]. split; [lia|]. split; [apply Z.mod_divide; [lia|]; apply Z.mod_divide in HS16; [|lia];
    destruct HS16 as [q Hq]; exists (q - 23); lia|].
  split; [unfold MI in HMI; rewrite s1_segs in HMI; exact HMI|].
  split.
  { split; [lia|]. split; [lia|]. intros i Hi. pose proof (Hwr (g_S g - 368 - 15000 + i) ltac:(lia)) as W.
    unfold writable_at in W. rewrite s1_segs in W. exact W. }
  split; [replace (g_S g - 368 - 16016) with (g_S g - 16384) by lia; replace (g_S g - 368 + 368) with (g_S g) by lia;
          exact (proj2 (stk_split rsegs mem (g_S g - 65536) (g_S g - 16384) (g_S g) Hstk ltac:(lia)))|].
  exact Hsp.
Qed.

Lemma s1_blk : forall L A mem md p n, aa_MR (APIf rc) L A mem md -> In (p, n) (blocks L A) ->
  4096 <= p /\ p + n <= alloc_ceiling.
Proof.
  intros L A mem md p n HM Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([q n'] & Eq & Hq).
  cbn [fst snd] in Eq. injection Eq as Ep En. subst p n.
  exact (mr_blocks_range _ _ (aa_laws (APIf rc)) _ _ _ _ q n' HM Hq).
Qed.

Lemma s1_OUTS : forall g nm tk dp L A m0 mem md mem' W hb,
  aa_MR (APIf rc) L A m0 md ->
  Permutation (blocks L A) (NMB g nm tk dp ++ hb) ->
  OUTS g nm tk dp mem -> mfr W mem mem' -> (forall x, ~ outside W x -> alloc_ceiling <= x) ->
  OUTS g nm tk dp mem'.
Proof.
  intros g nm tk dp L A m0 mem md mem' W hb HM HP HO MF HW Hr0.
  destruct (HO Hr0) as (C1 & C2 & C3).
  destruct (n_r_zero _ Hr0) as [_ Hfit]. destruct (n_fits_spec _ Hfit) as (F1 & F2 & F3).
  assert (In1 : In (nm, bsz (t_cap_name (g_in g))) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  assert (In2 : In (tk, bsz (t_cap_tok (g_in g))) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); right; left; reflexivity).
  assert (In3 : In (dp, bsz (t_cap_disp (g_in g))) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); right; right; left; reflexivity).
  pose proof (s1_blk L A m0 md _ _ HM In1) as B1. pose proof (s1_blk L A m0 md _ _ HM In2) as B2.
  pose proof (s1_blk L A m0 md _ _ HM In3) as B3. unfold bsz in B1, B2, B3.
  pose proof (n_TK_len (g_in g)) as LT. unfold n_ln, n_ld in F1, F3.
  unfold cstr in *. split; [|split].
  - apply (s1_bytes_low W mem mem' _ _ alloc_ceiling C1 MF HW). rewrite length_app. cbn [length]. lia.
  - apply (s1_bytes_low W mem mem' _ _ alloc_ceiling C2 MF HW). rewrite length_app. cbn [length]. lia.
  - apply (s1_bytes_low W mem mem' _ _ alloc_ceiling C3 MF HW). rewrite length_app. cbn [length]. lia.
Qed.

End TacSh1.

Ltac subfp := let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [outside] in *; repeat split; lia.
