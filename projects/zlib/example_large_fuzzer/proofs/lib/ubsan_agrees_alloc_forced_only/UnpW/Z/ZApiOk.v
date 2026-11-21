(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Prelim ZApi ZHarness.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflateRel RefDeflSafeI1 RefDeflSafeI5b DeflateTaintTop.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState Inftrees InflateFast InflateArms Inflate HarnessSmall ZApiInst.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefZApi RefInflateRel RefInflateInit1 RefInflateInit_run. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeD. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateSafeS2 RefInflateSafeS3 RefInflateEqS RefInflateEqB.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import InflateFrameIn InflateCall.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BoundArith BoundDefs BoundFw. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import BoundTfb BoundMc BoundSlow BoundCore BoundCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma dinit0_some : exists zr, dinit0 = Some (Some ds0, zr).
Proof.
  unfold ds0. destruct dinit0 as [[[s|] zr]|] eqn:E.
  - exists zr. reflexivity.
  - exfalso. assert (H : match dinit0 with Some (Some _, _) => true | _ => false end = true) by (vm_compute; reflexivity).
    rewrite E in H. discriminate H.
  - exfalso. assert (H : match dinit0 with Some (Some _, _) => true | _ => false end = true) by (vm_compute; reflexivity).
    rewrite E in H. discriminate H.
Qed.

Lemma ds0_fields :
  (ds_level ds0, ds_strategy ds0, ds_status ds0, ds_wrap ds0, ds_strstart ds0, ds_lit_bufsize ds0, ds_w_size ds0)
  = (6, 0, INIT_STATE, 1, 0, 16384, 32768)
  /\ (ds_sym_next ds0, ds_pending ds0, ds_bi_valid ds0, ds_lookahead ds0, ds_block_start ds0, ds_match_available ds0, ds_match_length ds0)
     = (0, 0, 0, 0, 0, 0, 2)
  /\ dz0 = ZIface.mkZS 0 0 1 2 MSG_NULL
  /\ (ds_gzhead ds0, ds_insert ds0) = (0, 0).
Proof. split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | split; vm_compute; reflexivity]]. Qed.

Lemma tuple7_eq : forall a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6 b7 : Z,
  (a1, a2, a3, a4, a5, a6, a7) = (b1, b2, b3, b4, b5, b6, b7) ->
  a1 = b1 /\ a2 = b2 /\ a3 = b3 /\ a4 = b4 /\ a5 = b5 /\ a6 = b6 /\ a7 = b7.
Proof. intros. injection H as E1 E2 E3 E4 E5 E6 E7. repeat split; assumption. Qed.

Lemma tuple2_eq : forall a1 a2 b1 b2 : Z, (a1, a2) = (b1, b2) -> a1 = b1 /\ a2 = b2.
Proof. intros. injection H as E1 E2. split; assumption. Qed.

Lemma HI_fresh : forall s z, DD s ->
  ds_level s = 6 -> ds_strategy s = 0 -> ds_status s = INIT_STATE -> ds_wrap s = 1 -> ds_strstart s = 0 ->
  ds_lit_bufsize s = 16384 -> ds_w_size s = 32768 ->
  ds_sym_next s = 0 -> ds_pending s = 0 -> ds_bi_valid s = 0 -> ds_lookahead s = 0 -> ds_block_start s = 0 ->
  ds_match_available s = 0 -> ds_match_length s = 2 -> ds_gzhead s = 0 -> ds_insert s = 0 ->
  zs_total_in z = 0 -> zs_total_out z = 0 -> HI s z.
Proof.
  intros s z HDD L S St W Str Lb Ws Sn Pd Bv Lk Bs Ma Ml Gz Ins Ti To.
  constructor; try assumption.
  - left. repeat split; assumption.
  - intros _. destruct (cov_nil s Sn) as [C N]. constructor.
    + rewrite C, Str, Bs, Ma. reflexivity.
    + intros j Hj. rewrite N in Hj. lia.
    + rewrite Bs. lia.
    + rewrite Ml. intros H; discriminate H.
    + rewrite Ml. lia.
  - rewrite Ti. unfold AposI. rewrite Lk, Str, Bs. lia.
  - rewrite Ti, To. unfold AposI, Mloc, paid. rewrite Lk, Str, Bs, Pd, Bv, St, W. vm_compute. discriminate.
  - left. exact Ins.
Qed.

Lemma dpure_eq : @HarnessSmall.dpure = @DeflateSafe.dpure. Proof. reflexivity. Qed.
Lemma dhooks_eq : HarnessSmall.dhooks = DeflateSafe.dhooks. Proof. reflexivity. Qed.
Lemma dinit0_unfold :
  HarnessSmall.dpure (deflateInit2_m HarnessSmall.dhooks (zc_none zstrm0) Z_DEFAULT_COMPRESSION Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY)
                     (dchs (fun _ => g0)) = dinit0.
Proof. unfold dinit0, dinit_run. reflexivity. Qed.
Lemma dinit0_safe : exists zr,
  DeflateSafe.dpure (deflateInit2_m DeflateSafe.dhooks (zc_none zstrm0) Z_DEFAULT_COMPRESSION Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY)
                    (dchs (fun _ => g0)) = Some (Some ds0, zr).
Proof.
  destruct dinit0_some as [zr E]. exists zr. rewrite <- dinit0_unfold in E. rewrite dpure_eq in E. rewrite dhooks_eq in E. exact E.
Qed.

Lemma HI_init : HI ds0 dz0 /\ zs_total_in dz0 = 0 /\ zs_total_out dz0 = 0 /\ zstrm_okP dz0.
Proof.
  destruct ds0_fields as (E1 & E2 & E3 & E4).
  destruct (tuple7_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ E1) as (L & S & St & W & Str & Lb & Ws).
  destruct (tuple7_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ E2) as (Sn & Pd & Bv & Lk & Bs & Ma & Ml).
  destruct (tuple2_eq _ _ _ _ E4) as (Gz & Ins).
  destruct dinit0_safe as [zr E].
  pose proof (dinit_DD (zc_none zstrm0) Z_DEFAULT_COMPRESSION Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL Z_DEFAULT_STRATEGY ltac:(unfold DEF_MEM_LEVEL; lia)
                (dchs (fun _ => g0)) ds0 zr E) as HDD.
  clear E1 E2 E4 E. revert L S St W Str Lb Ws Sn Pd Bv Lk Bs Ma Ml Gz Ins HDD. generalize ds0.
  intros s L S St W Str Lb Ws Sn Pd Bv Lk Bs Ma Ml Gz Ins HDD.
  rewrite E3. cbn [zs_total_in zs_total_out].
  split; [apply HI_fresh; try assumption; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  unfold zstrm_okP. cbn [zs_total_in zs_total_out zs_adler zs_data_type]. lia.
Qed.

Definition DINV (d : list Z) (x : dstream) (ai : Z) : Prop :=
  HI (dz_s x) (dz_z x) /\ zstrm_okP (dz_z x) /\ 0 <= ai <= 1 /\ zs_total_in (dz_z x) + ai <= zlength d
  /\ (ds_status (dz_s x) = FINISH_STATE -> ai = 0).

Lemma zlen_first_skip : forall (d : list Z) t a, 0 <= t -> 0 <= a -> t + a <= zlength d -> zlength (zfirstn a (zskipn t d)) = a.
Proof.
  intros d t a Ht Ha H. unfold zlength, zfirstn, zskipn in *. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma cbound_eq : forall n, 0 <= n <= 2 ^ 20 -> compressBound_m n = cbound n.
Proof.
  intros n H. unfold compressBound_m, sat_bound64. pose proof (cbound_range n H). unfold cbound in *.
  rewrite wrap64_id by lia.
  (* zlib 1.4 (zl14cmp-r1): compressBound saturates; on this range the sum is at least n, so it does not *)
  assert (S12 : 0 <= Z.shiftr n 12) by (apply Z.shiftr_nonneg; lia).
  assert (S14 : 0 <= Z.shiftr n 14) by (apply Z.shiftr_nonneg; lia).
  assert (S25 : 0 <= Z.shiftr n 25) by (apply Z.shiftr_nonneg; lia).
  match goal with |- context [if ?a <? ?b then _ else _] => destruct (Z.ltb_spec a b) end; [lia | reflexivity].
Qed.

Lemma dcall_step : forall d x ai ain flush,
  bytes_okP d -> zlength d <= 2 ^ 20 -> DINV d x ai ->
  ((flush = Z_NO_FLUSH /\ ain = 1 /\ zs_total_in (dz_z x) < zlength d /\ ds_status (dz_s x) <> FINISH_STATE)
   \/ (flush = Z_FINISH /\ ain = ai)) ->
  let zc := zd_zcall d x ain 1 in
  let r := deflate_m (dz_s x) zc flush in
  let x' := mkDZ (fst r) (zr_strm (snd r)) in
  let ai' := zlength (zc_input zc) - zr_consumed (snd r) in
  DINV d x' ai'
  /\ (zr_rc (snd r) = Z_OK \/ (flush = Z_FINISH /\ zr_rc (snd r) = Z_STREAM_END /\ ds_status (fst r) = FINISH_STATE))
  /\ (flush = Z_NO_FLUSH -> ds_status (fst r) <> FINISH_STATE)
  /\ zs_total_in (dz_z x') = zs_total_in (dz_z x) + zr_consumed (snd r)
  /\ zs_total_out (dz_z x') = zs_total_out (dz_z x) + zlength (zr_output (snd r))
  /\ 0 <= zr_consumed (snd r) /\ 0 <= zlength (zr_output (snd r)) <= 1
  /\ (zr_rc (snd r) = Z_OK -> 0 < zr_consumed (snd r) + zlength (zr_output (snd r)))
  /\ zs_total_out (dz_z x') <= compressBound_m (zlength d).
Proof.
  intros d x ai ain flush Hb Hn (HI0 & Zok & Hai & Hti & Hfin) MODE. cbv zeta.
  pose proof Zok as (T1 & T2 & _).
  assert (Hain : 0 <= ain <= 1 /\ zs_total_in (dz_z x) + ain <= zlength d /\ (ds_status (dz_s x) = FINISH_STATE -> ain = 0)).
  { destruct MODE as [(_ & -> & Hlt & Hnf)|(_ & ->)]; [split; [lia|]; split; [lia | intros E; contradiction] | split; [exact Hai|]; split; assumption]. }
  destruct Hain as (Ha1 & Ha2 & Ha3).
  assert (EL : zlength (zc_input (zd_zcall d x ain 1)) = ain) by (unfold zd_zcall; cbn [zc_input]; apply zlen_first_skip; lia).
  assert (Hzc : dcall_wf (zd_zcall d x ain 1)).
  { unfold dcall_wf. rewrite EL. unfold zd_zcall. cbn [zc_strm zc_avail_out zc_input].
    split; [exact Zok|]. split; [lia|]. split; [lia|]. apply bytes_okP_zfirstn, bytes_okP_zskipn'. exact Hb. }
  assert (HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH) by (destruct MODE as [(F & _)|(F & _)]; [left | right]; exact F).
  pose proof (bcall (dz_s x) (zd_zcall d x ain 1) flush HI0 Hzc HFL) as BC. rewrite EL in BC.
  assert (Estrm : zc_strm (zd_zcall d x ain 1) = dz_z x) by reflexivity.
  assert (Eao : zc_avail_out (zd_zcall d x ain 1) = 1) by reflexivity.
  rewrite Estrm, Eao in BC.
  assert (Hn0 : 0 <= zlength d) by (unfold zlength; lia).
  assert (HB0 : zs_total_out (dz_z x) <= 2 * 2 ^ 20 + 13).
  { pose proof (HI_total_out _ _ HI0) as B.
    pose proof (phi0_budget (zs_total_in (dz_z x)) (zlength d) ltac:(lia)) as PB. pose proof (cb_budget_le (zlength d) ltac:(lia)) as CB.
    pose proof (cbound_range (zlength d) ltac:(lia)). lia. }
  specialize (BC ltac:(intros F; destruct MODE as [(_ & -> & _ & Hnf)|(F4 & _)]; [split; [lia | exact Hnf] | rewrite F in F4; discriminate F4])
                 ltac:(intros E; exact (Ha3 E)) ltac:(lia) ltac:(lia) ltac:(lia)).
  cbv zeta in BC. rewrite EL.
  set (r := deflate_m (dz_s x) (zd_zcall d x ain 1) flush) in *. clearbody r.
  destruct BC as (HI1 & RC & NF & FIN & ETI & ETO & CON & OUT & Zok1 & _ & PRG).
  unfold DINV. cbn [dz_s dz_z].
  assert (HB : zs_total_out (zr_strm (snd r)) <= compressBound_m (zlength d)).
  { pose proof (HI_total_out _ _ HI1) as B. rewrite ETI in B.
    pose proof (phi0_mono (zs_total_in (dz_z x) + zr_consumed (snd r)) (zlength d) ltac:(lia)) as PM.
    pose proof (phi0_budget (zlength d) (zlength d) ltac:(lia)) as PB. pose proof (cb_budget_le (zlength d) ltac:(lia)) as CB.
    rewrite (cbound_eq (zlength d) ltac:(lia)). lia. }
  split.
  { split; [exact HI1|]. split; [exact Zok1|]. split; [lia|]. split; [rewrite ETI; lia|]. intros E. rewrite (FIN E). lia. }
  split; [exact RC|]. split; [exact NF|]. split; [exact ETI|]. split; [exact ETO|]. split; [lia|]. split; [exact OUT|].
  split; [exact PRG | exact HB].
Qed.

Local Ltac pz := change (@Prelim.zlength) with (@zlength) in *.

Lemma d_call_eq : forall d (dsa : dstream * Z) flush,
  ZHarness.d_call zinst d dsa flush =
  (let zc := zd_zcall d (fst dsa) (if flush =? ZApi.Z_NO_FLUSH then 1 else snd dsa) 1 in
   let r := deflate_m (dz_s (fst dsa)) zc flush in
   ((mkDZ (fst r) (zr_strm (snd r)), zlength (zc_input zc) - zr_consumed (snd r)), zr_output (snd r), zr_rc (snd r))).
Proof.
  intros d dsa flush. unfold ZHarness.d_call. cbn [ZApi.d_deflate zinst]. unfold zd_deflate. cbv zeta.
  change (ZApi.DS zinst) with dstream.
  destruct (deflate_m (dz_s (fst dsa)) (zd_zcall d (fst dsa) (if flush =? ZApi.Z_NO_FLUSH then 1 else snd dsa) 1) flush) as [s' zr].
  reflexivity.
Qed.

Lemma DINV_meas : forall d x ai, zlength d <= 2 ^ 20 -> DINV d x ai ->
  0 <= zs_total_in (dz_z x) <= zlength d /\ 0 <= zs_total_out (dz_z x) <= compressBound_m (zlength d).
Proof.
  intros d x ai Hn (HI0 & (T1 & T2 & _) & Hai & Hti & _).
  assert (Hn0 : 0 <= zlength d) by (unfold zlength; lia).
  pose proof (HI_total_out _ _ HI0) as B.
  pose proof (phi0_budget (zs_total_in (dz_z x)) (zlength d) ltac:(lia)) as PB. pose proof (cb_budget_le (zlength d) ltac:(lia)) as CB.
  rewrite (cbound_eq (zlength d) ltac:(lia)). lia.
Qed.

Lemma d_step_ok_true : forall d cl x x' ai' bs,
  0 <= ai' <= 1 -> 0 <= zs_total_in (dz_z x') -> zs_total_in (dz_z x') + ai' <= zlength d ->
  zs_total_out (dz_z x') = zs_total_out (dz_z x) + zlength bs -> zs_total_out (dz_z x') <= cl ->
  ZHarness.d_step_ok zinst d cl x (x', ai') bs = true.
Proof.
  intros d cl x x' ai' bs H1 H2 H3 H4 H5. unfold ZHarness.d_step_ok. cbn [ZApi.d_total_in ZApi.d_total_out zinst fst snd].
  unfold Prelim.zlength, zlength in *. rewrite !andb_true_iff. repeat split; first [apply Z.leb_le; lia | apply Z.eqb_eq; lia].
Qed.

Lemma dloop1_ok : forall fuel d cl dsa out, bytes_okP d -> zlength d <= 2 ^ 20 -> cl = compressBound_m (zlength d) ->
  DINV d (fst dsa) (snd dsa) -> ds_status (dz_s (fst dsa)) <> FINISH_STATE ->
  (zlength d - zs_total_in (dz_z (fst dsa))) + (cl - zs_total_out (dz_z (fst dsa))) < Z.of_nat fuel ->
  exists dsa' out', ZHarness.dloop1 zinst fuel d cl dsa out = Some (dsa', out') /\ DINV d (fst dsa') (snd dsa').
Proof.
  induction fuel as [|f IH]; intros d cl dsa out Hb Hn Hcl HD Hnf Hm.
  - exfalso. destruct (DINV_meas d _ _ Hn HD) as [M1 M2]. rewrite <- Hcl in M2. cbn [Z.of_nat] in Hm. lia.
  - cbn [ZHarness.dloop1]. cbn [ZApi.d_total_in ZApi.d_total_out zinst]. pz. change (ZApi.DS zinst) with dstream in *.
    match goal with |- context [if ?c then _ else Some (dsa, out)] => destruct c eqn:Econd end.
    2:{ exists dsa, out. split; [reflexivity | exact HD]. }
    apply andb_prop in Econd as [Ec1 Ec2]. apply negb_true_iff, Z.eqb_neq in Ec1. apply Z.ltb_lt in Ec2.
    destruct (DINV_meas d _ _ Hn HD) as [M1 M2].
    rewrite d_call_eq. change (ZApi.Z_NO_FLUSH =? ZApi.Z_NO_FLUSH) with true. cbv iota zeta.
    pose proof (dcall_step d (fst dsa) (snd dsa) 1 Z_NO_FLUSH Hb Hn HD ltac:(left; split; [reflexivity|]; split; [reflexivity|]; split; [lia | exact Hnf])) as ST.
    cbv zeta in ST. change ZApi.Z_NO_FLUSH with Z_NO_FLUSH.
    set (zc := zd_zcall d (fst dsa) 1 1) in *. clearbody zc.
    set (r := deflate_m (dz_s (fst dsa)) zc Z_NO_FLUSH) in *. clearbody r.
    destruct ST as (HD' & RC & NF & ETI & ETO & CON & OUT & PRG & HB). cbn [dz_s dz_z] in ETI, ETO, HB, NF.
    assert (Erc : zr_rc (snd r) = Z_OK) by (destruct RC as [E|(F & _)]; [exact E | discriminate F]).
    pose proof HD' as (_ & _ & Hai' & Hti' & _). cbn [dz_s dz_z] in Hti'.
    rewrite (d_step_ok_true d cl (fst dsa) (mkDZ (fst r) (zr_strm (snd r))) _ (zr_output (snd r)) Hai' ltac:(cbn [dz_z]; rewrite ETI; lia) Hti' ETO ltac:(cbn [dz_z]; rewrite Hcl; exact HB)).
    rewrite Erc. change (Z_OK =? ZApi.Z_OK) with true. cbv iota.
    apply (IH d cl _ _ Hb Hn Hcl).
    + cbn [fst snd]. exact HD'.
    + cbn [fst dz_s]. exact (NF eq_refl).
    + cbn [fst dz_z]. rewrite ETI, ETO. specialize (PRG Erc). lia.
Qed.

Lemma dloop2_ok : forall fuel d cl dsa out, bytes_okP d -> zlength d <= 2 ^ 20 -> cl = compressBound_m (zlength d) ->
  DINV d (fst dsa) (snd dsa) ->
  (zlength d - zs_total_in (dz_z (fst dsa))) + (cl - zs_total_out (dz_z (fst dsa))) < Z.of_nat fuel ->
  exists dsa' out', ZHarness.dloop2 zinst fuel d cl dsa out = Some (dsa', out') /\ ds_status (dz_s (fst dsa')) = FINISH_STATE.
Proof.
  induction fuel as [|f IH]; intros d cl dsa out Hb Hn Hcl HD Hm.
  - exfalso. destruct (DINV_meas d _ _ Hn HD) as [M1 M2]. rewrite <- Hcl in M2. cbn [Z.of_nat] in Hm. lia.
  - cbn [ZHarness.dloop2]. cbn [ZApi.d_total_in ZApi.d_total_out zinst]. change (ZApi.DS zinst) with dstream in *.
    destruct (DINV_meas d _ _ Hn HD) as [M1 M2].
    rewrite d_call_eq. change (ZApi.Z_FINISH =? ZApi.Z_NO_FLUSH) with false. cbv iota zeta.
    pose proof (dcall_step d (fst dsa) (snd dsa) (snd dsa) Z_FINISH Hb Hn HD ltac:(right; split; reflexivity)) as ST.
    cbv zeta in ST. change ZApi.Z_FINISH with Z_FINISH.
    set (zc := zd_zcall d (fst dsa) (snd dsa) 1) in *. clearbody zc.
    set (r := deflate_m (dz_s (fst dsa)) zc Z_FINISH) in *. clearbody r.
    destruct ST as (HD' & RC & NF & ETI & ETO & CON & OUT & PRG & HB). cbn [dz_s dz_z] in ETI, ETO, HB.
    pose proof HD' as (_ & _ & Hai' & Hti' & _). cbn [dz_s dz_z] in Hti'.
    rewrite (d_step_ok_true d cl (fst dsa) (mkDZ (fst r) (zr_strm (snd r))) _ (zr_output (snd r)) Hai' ltac:(cbn [dz_z]; rewrite ETI; lia) Hti' ETO ltac:(cbn [dz_z]; rewrite Hcl; exact HB)).
    destruct RC as [Erc|(_ & Erc & Est)]; rewrite Erc.
    + change (Z_OK =? ZApi.Z_STREAM_END) with false. change (Z_OK =? ZApi.Z_OK) with true. cbv iota.
      apply (IH d cl _ _ Hb Hn Hcl).
      * cbn [fst snd]. exact HD'.
      * cbn [fst dz_z]. rewrite ETI, ETO. specialize (PRG Erc). lia.
    + change (Z_STREAM_END =? ZApi.Z_STREAM_END) with true. cbv iota.
      eexists. eexists. split; [reflexivity|]. cbn [fst dz_s]. exact Est.
Qed.

Lemma dend_rc_finish : forall s, ds_status s = FINISH_STATE -> dend_rc s = Z_OK.
Proof. intros s E. unfold dend_rc, deflateStateCheck. cbv zeta. rewrite E. reflexivity. Qed.

Theorem zinst_deflate : forall d, 1 <= Prelim.zlength d <= ZApi.ZH_MAX -> Forall (fun b => 0 <= b < 256) d ->
  ZHarness.test_deflate_pure zinst d (ZApi.z_bound zinst (Prelim.zlength d)) <> None.
Proof.
  intros d Hn Hb. pz. unfold ZApi.ZH_MAX in Hn. cbn [ZApi.z_bound zinst].
  assert (Hn' : zlength d <= 2 ^ 20) by (change (2 ^ 20) with 1048576; lia).
  destruct HI_init as (HI0 & T0 & O0 & Zok0).
  assert (HD0 : DINV d zd_init 0).
  { unfold DINV, zd_init. cbn [dz_s dz_z]. split; [exact HI0|]. split; [exact Zok0|]. split; [lia|]. split; [rewrite T0; lia|]. intros _. reflexivity. }
  assert (Hnf0 : ds_status (dz_s zd_init) <> FINISH_STATE).
  { unfold zd_init. cbn [dz_s]. destruct ds0_fields as (E1 & _). destruct (tuple7_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ E1) as (_ & _ & St & _).
    rewrite St. discriminate. }
  assert (Hcb : 0 <= compressBound_m (zlength d) <= 2 * 2 ^ 20 + 13).
  { rewrite (cbound_eq (zlength d) ltac:(lia)). pose proof (cbound_range (zlength d) ltac:(lia)). lia. }
  unfold ZHarness.test_deflate_pure. cbn [ZApi.d_init zinst]. unfold ZHarness.DSA. change (ZApi.DS zinst) with dstream.
  set (cl := compressBound_m (zlength d)) in *.
  destruct (dloop1_ok (ZHarness.ZD_FUEL d cl) d cl (zd_init, 0) (Prelim.zrepeat 0 cl) Hb Hn' eq_refl HD0 Hnf0) as (dsa1 & out1 & E1 & HD1).
  { unfold ZHarness.ZD_FUEL. pz. cbn [fst]. unfold zd_init. cbn [dz_z]. rewrite T0, O0. lia. }
  rewrite E1.
  destruct (DINV_meas d _ _ Hn' HD1) as [M1 M2]. fold cl in M2.
  destruct (dloop2_ok (ZHarness.ZD_FUEL d cl) d cl dsa1 out1 Hb Hn' eq_refl HD1) as (dsa2 & out2 & E2 & Est).
  { unfold ZHarness.ZD_FUEL. pz. unfold ZHarness.DSA in *. change (ZApi.DS zinst) with dstream in *. lia. }
  rewrite E2. cbn [ZApi.d_end zinst]. unfold ZHarness.DSA in *. change (ZApi.DS zinst) with dstream in *. rewrite (dend_rc_finish _ Est). change (Z_OK =? ZApi.Z_OK) with true. cbv iota. discriminate.
Qed.

Lemma iinit0_eq :
  iinit0 = Some (Some (ireset_s (s_pre g0 5%N MAX_WBITS)), zret0 (ireset_z (s_pre g0 5%N MAX_WBITS) (z_pre (zc_none zstrm0))) Z_OK).
Proof.
  unfold iinit0, iinit_run, HarnessSmall.dpure. rewrite inflateInit2_m_eq. unfold sbind.
  cbn [zalloc HarnessSmall.dhooks mbind fst snd]. change (ir2_bad MAX_WBITS) with false. cbv iota. unfold sret. cbn [fst]. reflexivity.
Qed.

Lemma is0_eq : is0 = ireset_s (s_pre g0 5%N MAX_WBITS).
Proof. unfold is0. rewrite iinit0_eq. reflexivity. Qed.

Lemma INV_is0 : INV is0.
Proof. rewrite is0_eq. apply INV_fresh. reflexivity. Qed.

Lemma iz0_totals : zs_total_in iz0 = 0 /\ zs_total_out iz0 = 0.
Proof. split; vm_compute; reflexivity. Qed.

Definition IINV (x : istream) : Prop := INV (iz_s x) /\ 0 <= zs_total_in (iz_z x) /\ 0 <= zs_total_out (iz_z x).

Lemma i_call_eq : forall c (x : istream) ok,
  ZHarness.i_call zinst c x ok =
  (let r := fst (inflate_p (wans ok) (iz_s x) (zi_zcall c x 1 1) Z_NO_FLUSH) in
   (mkIZ (fst r) (zr_strm (snd r)), zr_output (snd r), zr_rc (snd r))).
Proof.
  intros c x ok. unfold ZHarness.i_call. cbn [ZApi.i_inflate zinst]. unfold zi_inflate. cbv zeta.
  destruct (inflate_p (wans ok) (iz_s x) (zi_zcall c x 1 1) Z_NO_FLUSH) as [[s' zr] asked]. reflexivity.
Qed.

Lemma icall_step : forall c x ok, bytes_ok c -> zlength c < 2 ^ 32 -> IINV x ->
  zs_total_in (iz_z x) < 2 ^ 62 -> zs_total_out (iz_z x) < 2 ^ 62 ->
  let r := fst (inflate_p (wans ok) (iz_s x) (zi_zcall c x 1 1) Z_NO_FLUSH) in
  INV (fst r) /\ 0 <= zlength (zr_output (snd r)) <= 1
  /\ (zr_rc (snd r) = Z_STREAM_END -> zs_total_out (zr_strm (snd r)) = zs_total_out (iz_z x) + zlength (zr_output (snd r)))
  /\ (zr_rc (snd r) = Z_OK ->
        zs_total_out (zr_strm (snd r)) = zs_total_out (iz_z x) + zlength (zr_output (snd r))
        /\ 0 <= zr_consumed (snd r) <= 1
        /\ zs_total_in (zr_strm (snd r)) = zs_total_in (iz_z x) + zr_consumed (snd r)
        /\ 0 < zr_consumed (snd r) + zlength (zr_output (snd r))).
Proof.
  intros c x ok Hb Hl (HI & T1 & T2) T3 T4. cbv zeta.
  set (zc := zi_zcall c x 1 1).
  assert (Hin : 0 <= zlength (zc_input zc) <= 1).
  { unfold zc, zi_zcall. cbn [zc_input]. pose proof (zlength_zfirstn_le 1 (zskipn (zs_total_in (iz_z x)) c) ltac:(lia)). lia. }
  assert (Hz : ZC zc).
  { unfold ZC. split; [unfold zc, zi_zcall; cbn [zc_avail_out]; lia|]. split; [lia|].
    unfold zc, zi_zcall. cbn [zc_input]. apply bytes_okP_zfirstn, bytes_okP_zskipn'. exact Hb. }
  pose proof (inflate_p_pure (wans ok) (iz_s x) zc Z_NO_FLUSH (INV_check _ HI)) as EP.
  set (p := fst (inflate_p (wans ok) (iz_s x) zc Z_NO_FLUSH)) in *. clearbody p.
  pose proof (inflate_m_post Z_NO_FLUSH (iz_s x) zc (wans ok) p HI Hz EP) as (P1 & P2).
  pose proof (inflate_m_post2 Z_NO_FLUSH (iz_s x) zc (wans ok) p HI Hz EP) as (Q1 & _).
  destruct p as [s' zr]. cbn [fst snd] in *.
  assert (Ezo : zs_total_out (zc_strm zc) = zs_total_out (iz_z x)) by reflexivity.
  assert (Ezi : zs_total_in (zc_strm zc) = zs_total_in (iz_z x)) by reflexivity.
  assert (Eao : zc_avail_out zc = 1) by reflexivity.
  rewrite Ezo in P2. rewrite Ezi in Q1. rewrite Eao in P1.
  split; [exact (inflate_INV' (iz_s x) zc Z_NO_FLUSH (wans ok) s' zr HI Hz EP)|].
  split; [exact P1|].
  split; [intros E; rewrite (P2 (or_intror E)); apply wrap64_id; lia|].
  intros E. destruct (Q1 E) as (C1 & C2 & C3).
  split; [rewrite (P2 (or_introl E)); apply wrap64_id; lia|]. split; [lia|]. split; [rewrite C2; apply wrap64_id; lia | exact C3].
Qed.

Lemma iend_rc_INV : forall s, INV s -> iend_rc s = Z_OK.
Proof. intros s H. unfold iend_rc. rewrite (INV_check s H). reflexivity. Qed.

Lemma iloop_ok : forall fuel c size cl (x : istream) uc, bytes_ok c -> cl = zlength c -> cl < 2 ^ 32 -> 0 <= size < 2 ^ 32 ->
  IINV x -> zs_total_in (iz_z x) <= cl -> zs_total_out (iz_z x) <= size ->
  Z.max 0 (size - zs_total_out (iz_z x)) + Z.max 0 (cl - zs_total_in (iz_z x)) < Z.of_nat fuel ->
  match ZHarness.iloop_pure zinst fuel c size cl x uc with
  | ZHarness.IRstuck => False
  | ZHarness.IRdone x' _ => ZApi.i_end zinst x' = ZApi.Z_OK
  | ZHarness.IRerr _ => True
  end.
Proof.
  induction fuel as [|f IH]; intros c size cl x uc Hb Hcl Hc32 Hs HX Hti Hto Hm; [cbn [Z.of_nat] in Hm; lia|].
  cbn [ZHarness.iloop_pure]. cbn [ZApi.i_total_in ZApi.i_total_out zinst]. change (ZApi.IS zinst) with istream in *.
  match goal with |- context [if ?cnd then _ else ZHarness.IRdone x uc] => destruct cnd eqn:Econd end.
  2:{ cbn [ZApi.i_end zinst]. exact (iend_rc_INV _ (proj1 HX)). }
  apply andb_prop in Econd as [Ec1 Ec2]. apply Z.ltb_lt in Ec1. apply Z.ltb_lt in Ec2.
  rewrite i_call_eq. cbv zeta.
  pose proof (icall_step c x true Hb ltac:(lia) HX ltac:(lia) ltac:(lia)) as ST. cbv zeta in ST.
  set (r := fst (inflate_p (wans true) (iz_s x) (zi_zcall c x 1 1) Z_NO_FLUSH)) in *. clearbody r.
  destruct ST as (HI' & OUT & END & OK). destruct HX as (_ & T1 & T2).
  unfold ZHarness.i_out_ok. cbn [ZApi.i_total_out zinst]. pz.
  replace (zs_total_out (iz_z x) + zlength (zr_output (snd r)) <=? size) with true by (symmetry; apply Z.leb_le; lia).
  destruct (Z.eqb_spec (zr_rc (snd r)) ZApi.Z_STREAM_END) as [E1|N1].
  { cbn [ZApi.i_end zinst iz_s]. exact (iend_rc_INV _ HI'). }
  destruct (Z.eqb_spec (zr_rc (snd r)) ZApi.Z_OK) as [E0|N0]; [| exact I].
  destruct (OK E0) as (K1 & K2 & K3 & K4).
  unfold ZHarness.i_next_ok. cbn [ZApi.i_total_in ZApi.i_total_out zinst iz_z].
  replace ((0 <=? zs_total_in (zr_strm (snd r))) && (zs_total_in (zr_strm (snd r)) <=? cl) && (0 <=? zs_total_out (zr_strm (snd r)))
           && (zs_total_out (zr_strm (snd r)) <=? size)) with true
    by (symmetry; rewrite !andb_true_iff; repeat split; apply Z.leb_le; lia).
  apply IH; try assumption.
  - split; [exact HI' | cbn [iz_z]; split; lia].
  - cbn [iz_z]. lia.
  - cbn [iz_z]. lia.
  - cbn [iz_z]. lia.
Qed.

Lemma lv_fin_output : forall flush s2 c r,
  zr_output (snd (RefInflate_runA.lv_fin flush s2 c r)) = arr_slice (ic_outbuf c) 0 (ic_next_out c).
Proof.
  intros flush s2 c r. unfold RefInflate_runA.lv_fin. cbv zeta.
  match goal with |- context [if ?cnd then _ else _] => destruct cnd end; cbn [fst snd zret_of_icall zr_output]; RefInflateSafeH.sacc; reflexivity.
Qed.

Lemma inflate_p_out_same : forall a s zc flush,
  zr_output (snd (fst (inflate_p None s zc flush))) = zr_output (snd (fst (inflate_p (Some a) s zc flush))).
Proof.
  intros [b g] s zc flush. destruct (inflateStateCheck s) eqn:Hc.
  - rewrite !(inflate_p_check _ s zc flush Hc). reflexivity.
  - unfold inflate_p. rewrite (RefInflate_runA.inflate_m_W0 HarnessSmall.dhooks) by exact Hc.
    destruct (inf_loop ivar_ref flush (RefInflate_runA.W0 s zc)) as [stop [s' c' r']]. destruct stop as [|rc].
    + rewrite !RefInflate_runA.inf_leave_eq. unfold sbind.
      destruct (RefInflate_runA.lv_cond flush (RefInflate_runA.s_rest s' r') (RefInflate_runA.c_rest c' r') r').
      * rewrite !updatewindow_dh. cbn [mbind fst snd]. unfold uw_pure.
        destruct (is_window_blk (RefInflate_runA.s_rest s' r')) as [b0|]; [reflexivity|].
        unfold sret. cbn [fst snd]. rewrite lv_fin_output. unfold RefInflate_runA.lv_mem. cbn [snd zret_of_icall zr_output].
        destruct (RefInflate_runA.lv_pre_fields (RefInflate_runA.s_rest s' r') (RefInflate_runA.c_rest c' r') r') as (_ & _ & _ & _ & F5 & F6).
        rewrite ?F5, ?F6. reflexivity.
      * reflexivity.
    + reflexivity.
Qed.

Theorem zinst_ok : ZHarness.zapi_ok zinst.
Proof.
  constructor.
  -   cbn [ZApi.d_total_in ZApi.d_total_out ZApi.d_init zinst]. unfold zd_init. cbn [dz_z].
    destruct HI_init as (_ & T & O & _). split; assumption.
  -   cbn [ZApi.i_total_in ZApi.i_total_out ZApi.i_init zinst]. unfold zi_init. cbn [iz_z]. exact iz0_totals.
  -   intros n Hn. cbn [ZApi.z_bound zinst]. unfold ZApi.ZH_MAX, ZHarness.ZB_MAX in *.
    rewrite (cbound_eq n ltac:(change (2 ^ 20) with 1048576; lia)).
    unfold cbound. rewrite !Z.shiftr_div_pow2 by lia.
    change (2 ^ 12) with 4096; change (2 ^ 14) with 16384; change (2 ^ 25) with 33554432. unfold ZApi.ZH_MAX.
    Z.to_euclidean_division_equations. lia.
  -   cbn [ZApi.z_dstate ZApi.z_dwin ZApi.z_dprev ZApi.z_dhead ZApi.z_dpend ZApi.z_isize ZApi.z_wsize zinst].
    unfold ZApi.ZH_MAX. repeat constructor; lia.
  -   exact zinst_deflate.
  -   intros size c Hs Hl Hb. cbn [ZApi.z_bound zinst] in *. pz.
    unfold ZApi.ZH_MAX in Hs.
    assert (Hcb : 0 <= compressBound_m size <= 2 * 2 ^ 20 + 13).
    { rewrite (cbound_eq size ltac:(change (2 ^ 20) with 1048576; lia)).
      pose proof (cbound_range size ltac:(change (2 ^ 20) with 1048576; lia)). change (2 ^ 20) with 1048576 in *. lia. }
    destruct iz0_totals as [TI0 TO0].
    apply iloop_ok.
    + exact Hb.
    + symmetry. exact Hl.
    + lia.
    + lia.
    + cbn [ZApi.i_init zinst]. unfold zi_init, IINV. cbn [iz_s iz_z]. split; [exact INV_is0|]. rewrite TI0, TO0. lia.
    + cbn [ZApi.i_init zinst]. unfold zi_init. cbn [iz_z]. rewrite TI0. lia.
    + cbn [ZApi.i_init zinst]. unfold zi_init. cbn [iz_z]. rewrite TO0. lia.
    + cbn [ZApi.i_init zinst]. unfold zi_init. cbn [iz_z]. rewrite TI0, TO0. unfold ZHarness.ZI_FUEL. lia.
  -   intros c x H. rewrite i_call_eq. cbv zeta. cbn [snd].
    cbn [ZApi.i_wants_window zinst] in H. unfold zi_wants_window in H. unfold wans in *.
    exact (inflate_p_refused 6%N g0 (iz_s x) (zi_zcall c x 1 1) Z_NO_FLUSH H).
  -   intros c x _. rewrite !i_call_eq. cbv zeta. cbn [fst snd]. unfold wans.
    exact (inflate_p_out_same (6%N, g0) (iz_s x) (zi_zcall c x 1 1) Z_NO_FLUSH).
  -   intros c x ok. rewrite i_call_eq. cbv zeta. cbn [snd]. apply inflate_p_rc_range.
Qed.
