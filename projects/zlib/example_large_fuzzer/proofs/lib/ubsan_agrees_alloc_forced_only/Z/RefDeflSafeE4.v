(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefCompressBlk1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeE1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sym_calls_ext : forall a b lfc ldl dfc ddl sx,
  sym_dist b sx = sym_dist a sx -> sym_lc b sx = sym_lc a sx ->
  sym_calls b lfc ldl dfc ddl sx = sym_calls a lfc ldl dfc ddl sx.
Proof. intros a b lfc ldl dfc ddl sx ED EL. unfold sym_calls. rewrite ED, EL. reflexivity. Qed.

(* [comment removed for export] *)
Lemma clen_sym_calls : forall s lfc ldl dfc ddl j,
  clen (sym_calls s lfc ldl dfc ddl (3 * j)) = dcost ldl ddl s j.
Proof.
  intros s lfc ldl dfc ddl j. unfold sym_calls, dcost, sym_xl, sym_xd, sym_isdist, sym_lcode, sym_dcode.
  destruct (sym_dist s (3 * j) =? 0); cbn [negb clen]; [lia|].
  rewrite !clen_app. cbn [clen].
  destruct (Z.eqb_spec (arr_get extra_lbits_a (arr_get length_code_a (sym_lc s (3 * j)))) 0) as [E1|E1];
  destruct (Z.eqb_spec (arr_get extra_dbits_a (d_code (sym_dist s (3 * j) - 1))) 0) as [E2|E2]; cbn [negb clen app]; lia.
Qed.

(* [comment removed for export] *)
Lemma sym_calls_lens : forall s lfc ldl dfc ddl j,
  0 <= arr_get ldl (sym_lcode s j) <= 15 ->
  (sym_isdist s j = true -> 0 <= arr_get ddl (sym_dcode s j) <= 15) ->
  Forall (fun c => 0 <= snd c <= 16) (sym_calls s lfc ldl dfc ddl (3 * j)).
Proof.
  intros s lfc ldl dfc ddl j HL HD. unfold sym_calls. unfold sym_xl, sym_xd, sym_isdist, sym_lcode, sym_dcode in *.
  apply Forall_forall. intros c Hc.
  destruct (sym_dist s (3 * j) =? 0); cbn [negb] in *.
  - destruct Hc as [Hc|Hc]; [subst c; cbn; lia | contradiction].
  - specialize (HD eq_refl). pose proof (extra_lbits_bound (arr_get length_code_a (sym_lc s (3 * j)))). pose proof (extra_dbits_bound (d_code (sym_dist s (3 * j) - 1))).
    rewrite !in_app_iff in Hc.
    destruct (negb (arr_get extra_lbits_a (arr_get length_code_a (sym_lc s (3 * j))) =? 0));
    destruct (negb (arr_get extra_dbits_a (d_code (sym_dist s (3 * j) - 1)) =? 0)); cbn [In] in Hc;
    repeat match type of Hc with _ \/ _ => destruct Hc as [Hc|Hc] end; try contradiction; subst c; cbn [snd]; lia.
Qed.

(* [comment removed for export] *)
Lemma sym_bytes_agree : forall s0 y j,
  ds_lit_bufsize y = ds_lit_bufsize s0 ->
  (forall i, ds_lit_bufsize s0 + 3 * j <= i < ds_lit_bufsize s0 + 3 * j + 3 -> arr_get (ds_pending_buf y) i = arr_get (ds_pending_buf s0) i) ->
  sym_dist y (3 * j) = sym_dist s0 (3 * j) /\ sym_lc y (3 * j) = sym_lc s0 (3 * j).
Proof.
  intros s0 y j EL EB. unfold sym_dist, sym_d0, sym_d1, sym_lc, sym_buf_get. rewrite EL. rewrite !EB by lia. split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CB.
Variable s0 : deflate_state.
Variable lfc : arr.
Variable ldl : arr.
Variable dfc : arr.
Variable ddl : arr.
Variable N : Z.
Variable W0 : Z.
Let lbs := ds_lit_bufsize s0.
Let PBL := arr_len (ds_pending_buf s0).
Let cost := dcost ldl ddl s0.

Hypothesis HN : 0 <= N.
Hypothesis HPBL : PBL = lbs * 4.
Hypothesis Hroom : lbs + 3 * N + 3 <= PBL.
Hypothesis Hlbs : 0 <= lbs.
(* [comment removed for export] *)
Hypothesis Hsyms : forall j, 0 <= j < N -> sym_okb s0 j.
(* [comment removed for export] *)
Hypothesis HlenL : forall j, 0 <= j < N -> 0 <= arr_get ldl (sym_lcode s0 j) <= 15.
Hypothesis HlenD : forall j, 0 <= j < N -> sym_isdist s0 j = true -> 0 <= arr_get ddl (sym_dcode s0 j) <= 15.
(* [comment removed for export] *)
Hypothesis PREFIX : forall k, 0 <= k < N -> W0 + zsum cost 0 (Z.to_nat k) <= 8 * (lbs + 3 * k).
Hypothesis TOTAL : W0 + zsum cost 0 (Z.to_nat N) <= 8 * PBL.

Lemma cost_nonneg : forall j, 0 <= j < N -> 0 <= cost j.
Proof.
  intros j Hj. subst cost. rewrite <- (clen_sym_calls s0 lfc ldl dfc ddl j). apply clen_nonneg. apply sym_calls_lens; [apply HlenL | apply HlenD]; exact Hj.
Qed.

Lemma zsum_cost_mono : forall a b, 0 <= a <= b -> b <= N -> zsum cost 0 (Z.to_nat a) <= zsum cost 0 (Z.to_nat b).
Proof.
  intros a b Hab Hb. replace (Z.to_nat b) with (Z.to_nat a + Z.to_nat (b - a))%nat by lia.
  rewrite zsum_split. pose proof (zsum_nonneg cost (0 + Z.of_nat (Z.to_nat a)) (Z.to_nat (b - a)) ltac:(intros; apply cost_nonneg; lia)). lia.
Qed.

(* [comment removed for export] *)
Record CBI (k : Z) (y : deflate_state) : Prop := {
  ci_k : 0 <= k <= N;
  ci_lbs : ds_lit_bufsize y = lbs;
  ci_pbl : arr_len (ds_pending_buf y) = PBL;
  ci_sn : ds_sym_next y = 3 * N;
  ci_W : ov_W y = W0 + zsum cost 0 (Z.to_nat k);
  ci_bv : 0 <= ds_bi_valid y <= 16;
  ci_pb : PBB y;
  ci_pend : 0 <= ds_pending y;
  ci_pristine : forall i, ds_pending y <= i -> arr_get (ds_pending_buf y) i = arr_get (ds_pending_buf s0) i }.

Lemma CBI_read : forall k y, CBI k y -> k < N ->
  sym_dist y (3 * k) = sym_dist s0 (3 * k) /\ sym_lc y (3 * k) = sym_lc s0 (3 * k).
Proof.
  intros k y I Hk. destruct I as [Hk0 EL EP ESN EW BV PB PE PR].
  assert (HP : 8 * ds_pending y <= 8 * (lbs + 3 * k)).
  { pose proof (pending_of_W y) as P. pose proof (PREFIX k ltac:(lia)). lia. }
  apply sym_bytes_agree; [exact EL|]. intros i Hi. apply PR. unfold lbs in *. lia.
Qed.

Lemma CBI_step : forall k y, CBI k y -> k < N ->
  let cs := sym_calls y lfc ldl dfc ddl (3 * k) in
  cs = sym_calls s0 lfc ldl dfc ddl (3 * k)
  /\ CBI (k + 1) (sbs_run y cs)
  /\ sym_ok PBL y lfc ldl dfc ddl (3 * k)
  /\ sym_lens y ldl ddl (3 * k)
  /\ (forall i, i < ds_pending y -> arr_get (ds_pending_buf (sbs_run y cs)) i = arr_get (ds_pending_buf y) i)
  /\ ds_pending y <= ds_pending (sbs_run y cs)
  /\ nb_view (sbs_run y cs) = nb_view y.
Proof.
  intros k y I Hk cs.
  destruct (CBI_read k y I Hk) as [ED ELc]. pose proof I as [Hk0 EL EP ESN EW BV PB PE PR].
  assert (Ecs : cs = sym_calls s0 lfc ldl dfc ddl (3 * k)) by (subst cs; apply sym_calls_ext; assumption).
  pose proof (sym_calls_lens s0 lfc ldl dfc ddl k (HlenL k ltac:(lia)) (HlenD k ltac:(lia))) as CL. rewrite <- Ecs in CL.
  pose proof (clen_sym_calls s0 lfc ldl dfc ddl k) as CC. rewrite <- Ecs in CC.
  assert (TW : ov_W y + clen cs <= 8 * PBL).
  { rewrite EW, CC. pose proof (zsum_cost_mono (k + 1) N ltac:(lia) ltac:(lia)) as M.
    replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) in M by lia. rewrite zsum_snoc in M.
    replace (0 + Z.of_nat (Z.to_nat k)) with k in M by lia. change (cost k) with (dcost ldl ddl s0 k) in M. lia. }
  split; [exact Ecs|]. split.
  { constructor.
    - lia.
    - pose proof (nb_view_facts _ _ (sbs_nb_view cs y)) as (V1 & _). rewrite V1. exact EL.
    - rewrite sbs_pbl. exact EP.
    - rewrite sbs_sym_next. exact ESN.
    - rewrite sbs_W, EW, CC. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia. rewrite zsum_snoc.
      replace (0 + Z.of_nat (Z.to_nat k)) with k by lia. change (cost k) with (dcost ldl ddl s0 k). lia.
    - apply sbs_biv; [exact BV | exact CL].
    - apply sbs_PBB. exact PB.
    - pose proof (sbs_pending_mono cs y). lia.
    - intros i Hi. rewrite sbs_frame by lia. apply PR. pose proof (sbs_pending_mono cs y). lia. }
  split.
  { unfold sym_ok. fold cs. split; [lia|]. split; [rewrite EL; unfold lbs, PBL in *; lia|]. split.
    - intros Hd. rewrite ED. pose proof (Hsyms k ltac:(lia)) as [_ B]. lia.
    - apply sbs_ok_of_bound; [exact BV | exact CL | exact TW]. }
  split.
  { unfold sym_lens. cbv zeta. rewrite ED, ELc.
    pose proof (HlenL k ltac:(lia)) as A. pose proof (HlenD k ltac:(lia)) as B. unfold sym_lcode, sym_isdist, sym_dcode in A, B.
    destruct (sym_dist s0 (3 * k) =? 0); cbn [negb] in *; [lia|]. specialize (B eq_refl). lia. }
  split; [intros i Hi; apply sbs_frame; lia|].
  split; [apply sbs_pending_mono | apply sbs_nb_view].
Qed.

(* [comment removed for export] *)
Lemma CB_loop : forall f k y, CBI k y -> k < N -> (Z.to_nat (N - k) <= f)%nat ->
  let y' := compress_block_loop f y lfc ldl dfc ddl (3 * k) in
  CBI N y'
  /\ cb_ok PBL f y lfc ldl dfc ddl (3 * k)
  /\ cb_lens f y lfc ldl dfc ddl (3 * k)
  /\ (forall i, i < ds_pending y -> arr_get (ds_pending_buf y') i = arr_get (ds_pending_buf y) i)
  /\ ds_pending y <= ds_pending y'
  /\ nb_view y' = nb_view y.
Proof.
  induction f as [|f IH]; intros k y INV Hk Hf y'; [lia|].
  destruct (CBI_step k y INV Hk) as (Ecs & I1 & SOK & SLEN & FR & PM & NV).
  subst y'. rewrite cb_loop_S. cbn [cb_ok cb_lens]. cbv zeta.
  set (y1 := sbs_run y (sym_calls y lfc ldl dfc ddl (3 * k))) in *.
  replace (3 * k + 1 + 1 + 1) with (3 * (k + 1)) by lia.
  rewrite (ci_sn _ _ I1).
  destruct (Z.ltb_spec (3 * (k + 1)) (3 * N)) as [C|C].
  - destruct (IH (k + 1) y1 I1 ltac:(lia) ltac:(lia)) as (I2 & OK2 & LEN2 & FR2 & PM2 & NV2).
    split; [exact I2|]. split; [split; [exact SOK | exact OK2]|]. split; [split; [exact SLEN | exact LEN2]|].
    split; [intros i Hi; rewrite FR2 by lia; apply FR; exact Hi|]. split; [lia|]. rewrite NV2. exact NV.
  - assert (k + 1 = N) by lia. rewrite <- H. split; [exact I1|]. split; [split; [exact SOK | exact Logic.I]|]. split; [split; [exact SLEN | exact Logic.I]|].
    split; [exact FR|]. split; [exact PM | exact NV].
Qed.

(* [comment removed for export] *)
Hypothesis HlenE : 0 <= arr_get ldl END_BLOCK <= 15.
Hypothesis TOTALE : W0 + zsum cost 0 (Z.to_nat N) + arr_get ldl END_BLOCK <= 8 * PBL.

Theorem compress_block_facts : forall y, CBI 0 y -> 0 <= ds_bi_buf y < 2 ^ 16 ->
  let y' := compress_block y lfc ldl dfc ddl in
  ov_W y' = W0 + zsum cost 0 (Z.to_nat N) + arr_get ldl END_BLOCK
  /\ compress_block_ok PBL y lfc ldl dfc ddl
  /\ compress_lens_ok y lfc ldl dfc ddl
  /\ nb_view y' = nb_view y /\ 0 <= ds_bi_valid y' <= 16 /\ 0 <= ds_bi_buf y' < 2 ^ 16 /\ PBB y'
  /\ arr_len (ds_pending_buf y') = PBL /\ ds_pending y <= ds_pending y' /\ 8 * ds_pending y' <= ov_W y'
  /\ (forall i, i < ds_pending y -> arr_get (ds_pending_buf y') i = arr_get (ds_pending_buf y) i).
Proof.
  intros y INV Hbb y'. pose proof INV as [_ EL EP ESN EW BV PB PE PR]. change (zsum cost 0 (Z.to_nat 0)) with 0 in EW.
  assert (BI : BINV PBL y) by (unfold BINV; pose proof (pending_of_W y); split; [exact BV|]; split; [exact Hbb|]; pose proof (zsum_nonneg cost 0 (Z.to_nat N) ltac:(intros; apply cost_nonneg; lia)); unfold lbs, PBL in *; lia).
  assert (MAIN : let y1 := (if negb (ds_sym_next y =? 0) then compress_block_loop (Z.to_nat (ds_sym_next y)) y lfc ldl dfc ddl 0 else y) in
                 CBI N y1 /\ (ds_sym_next y <> 0 -> cb_ok PBL (Z.to_nat (ds_sym_next y)) y lfc ldl dfc ddl 0 /\ cb_lens (Z.to_nat (ds_sym_next y)) y lfc ldl dfc ddl 0)
                 /\ (forall i, i < ds_pending y -> arr_get (ds_pending_buf y1) i = arr_get (ds_pending_buf y) i)
                 /\ ds_pending y <= ds_pending y1 /\ nb_view y1 = nb_view y).
  { cbv zeta. rewrite ESN. destruct (Z.eqb_spec (3 * N) 0) as [Z0|NZ]; cbn [negb].
    - assert (N0 : N = 0) by lia. rewrite N0 in *. split; [exact INV|]. split; [intros X; exfalso; apply X; reflexivity|]. split; [intros; reflexivity|]. split; [lia | reflexivity].
    - destruct (CB_loop (Z.to_nat (3 * N)) 0 y INV ltac:(lia) ltac:(lia)) as (I2 & OK2 & LEN2 & FR2 & PM2 & NV2).
      replace (3 * 0) with 0 in * by lia. split; [exact I2|]. split; [intros _; split; assumption|]. split; [exact FR2|]. split; [exact PM2 | exact NV2]. }
  cbv zeta in MAIN. destruct MAIN as (I1 & OKL & FR1 & PM1 & NV1).
  set (y1 := if negb (ds_sym_next y =? 0) then compress_block_loop (Z.to_nat (ds_sym_next y)) y lfc ldl dfc ddl 0 else y) in *.
  pose proof I1 as [_ EL1 EP1 ESN1 EW1 BV1 PB1 PE1 PR1].
  assert (TW : ov_W y1 + clen [(arr_get lfc END_BLOCK, arr_get ldl END_BLOCK)] <= 8 * PBL) by (cbn [clen]; rewrite EW1; lia).
  assert (CL : Forall (fun c => 0 <= snd c <= 16) [(arr_get lfc END_BLOCK, arr_get ldl END_BLOCK)]) by (repeat constructor; cbn; lia).
  assert (EY : y' = sbs_run y1 [(arr_get lfc END_BLOCK, arr_get ldl END_BLOCK)]).
  { subst y' y1. unfold compress_block, send_code. cbn [sbs_run]. reflexivity. }
  rewrite EY.
  split; [rewrite sbs_W, EW1; cbn [clen]; lia|].
  split.
  { unfold compress_block_ok. split; [exact BI|]. split; [exact PB|]. split; [intros Hn; exact (proj1 (OKL Hn))|].
    cbv zeta. fold y1. apply sbs_ok_of_bound; [exact BV1 | exact CL | exact TW]. }
  split; [split; [intros Hn; exact (proj2 (OKL Hn)) | lia]|].
  split; [rewrite sbs_nb_view; exact NV1|].
  split; [apply sbs_biv; [exact BV1 | exact CL]|].
  split; [apply sbs_bib; [exact BV1 | exact CL |]|].
  { (* [comment removed for export] *) subst y1. destruct (negb (ds_sym_next y =? 0)); [| exact Hbb].
    clear - Hbb BV INV HN Hsyms HlenL HlenD PREFIX TOTAL HPBL Hroom Hlbs ESN.
    assert (G : forall f k z, CBI k z -> k < N -> 0 <= ds_bi_buf z < 2 ^ 16 -> 0 <= ds_bi_buf (compress_block_loop f z lfc ldl dfc ddl (3 * k)) < 2 ^ 16).
    { induction f as [|f IH]; intros k z Iz Hk Hz; [exact Hz|]. rewrite cb_loop_S. cbv zeta.
      destruct (CBI_step k z Iz Hk) as (Ecs & I1 & _).
      pose proof (sym_calls_lens s0 lfc ldl dfc ddl k (HlenL k ltac:(pose proof (ci_k _ _ Iz); lia)) (HlenD k ltac:(pose proof (ci_k _ _ Iz); lia))) as CL. rewrite <- Ecs in CL.
      replace (3 * k + 1 + 1 + 1) with (3 * (k + 1)) by lia. rewrite (ci_sn _ _ I1).
      destruct (Z.ltb_spec (3 * (k + 1)) (3 * N)).
      - apply IH; [exact I1 | lia | apply sbs_bib; [exact (ci_bv _ _ Iz) | exact CL | exact Hz]].
      - apply sbs_bib; [exact (ci_bv _ _ Iz) | exact CL | exact Hz]. }
    rewrite ESN. replace 0 with (3 * 0) at 2 by lia. destruct (Z_lt_le_dec 0 N) as [l|l]; [apply (G _ 0 y INV l Hbb)|].
    replace (Z.to_nat (3 * N)) with 0%nat by lia. rewrite cb_loop_0. exact Hbb. }
  split; [apply sbs_PBB; exact PB1|].
  split; [rewrite sbs_pbl; exact EP1|].
  split; [pose proof (sbs_pending_mono [(arr_get lfc END_BLOCK, arr_get ldl END_BLOCK)] y1); lia|].
  split; [pose proof (pending_of_W (sbs_run y1 [(arr_get lfc END_BLOCK, arr_get ldl END_BLOCK)])); pose proof (sbs_biv [(arr_get lfc END_BLOCK, arr_get ldl END_BLOCK)] y1 BV1 CL); lia|].
  intros i Hi. rewrite sbs_frame by lia. apply FR1. exact Hi.
Qed.
End CB.
