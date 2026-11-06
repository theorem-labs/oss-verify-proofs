(* m_file on fuzz_segconf.asan (image A), segment S_MF_KMOD (lib/A/Prog/m_file_s_kmod_m.v): the model, encoding
   and reader lemmas its walk uses. No symbolic execution here. The KMOD model sub-lane of the G2 walk owner's G2.

   - the fold: mk_ln_bound, hfold_len, hfold_firstn, map_lower_firstn_S, lower_range, hfold_nul, hfold_range
     (the loop 0x867f8-0x86844 writes low[i] = lower(v[i]) for i < ln = min(vl, 23));
   - the row: cat_row_lt, cat_ptr_some (fuzz_catalogue_row 0x86878 answers &fuzz_catalogue[r] or NULL);
   - the model: m_refuse_segs, m_upd_segs_len, m_lines_segs_mono, mf_fin_segs_mono, mk_model_segs, mk_fp_seg,
     m_refuse_counters, m_upd_model_counters, m_lines_kept_mono, mf_fin_kept_mono (the segments and the kept
     lines never shrink, so g = c + 256 gi and m_refuse's kept line stay inside M_FILE_FP of the final model);
   - the block: sa_mconf_with_model (the memcpy of low ++ [0] into g->model at 0x86890 and the store
     g->model_set = 1 at 0x868b0 give the block of m_upd c gi (ms_with_model low)), sa_mconf_kept. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_s_kmod_m m_file_mdl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the fold ======================================== *)
Lemma mk_ln_bound : forall vl, (mk_ln vl <= 23)%nat /\ (mk_ln vl <= vl)%nat /\ (0 < vl -> 0 < mk_ln vl)%nat.
Proof. intros vl. unfold mk_ln. split; [lia|]. split; [lia|]. intros H. lia. Qed.

Lemma hfold_len : forall vv, length (h_fold vv 24) = mk_ln (length vv).
Proof. intros vv. unfold h_fold, mk_ln. rewrite length_map, length_firstn. lia. Qed.

Lemma hfold_firstn : forall vv, map lower (firstn (mk_ln (length vv)) vv) = h_fold vv 24.
Proof.
  intros vv. unfold h_fold, mk_ln. f_equal.
  destruct (Nat.le_ge_cases (length vv) 23) as [H|H].
  - rewrite Nat.min_l by exact H. rewrite firstn_all. symmetry. apply firstn_all2. lia.
  - rewrite Nat.min_r by exact H. reflexivity.
Qed.

Lemma map_lower_firstn_S : forall vv i, (i < length vv)%nat ->
  map lower (firstn (S i) vv) = map lower (firstn i vv) ++ [lower (nth i vv 0)].
Proof. intros vv i H. rewrite firstn_S_snoc by exact H. rewrite map_app. reflexivity. Qed.

Lemma lower_range : forall c, 0 <= c < 256 -> 0 <= lower c < 256 /\ (lower c = 0 <-> c = 0).
Proof.
  intros c Hc. unfold lower.
  destruct ((65 <=? c) && (c <=? 90)) eqn:E.
  - apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [lia|]. split; intros; lia.
  - split; [lia | tauto].
Qed.

Lemma kmt_in_firstn {A} n (l : list A) x : In x (firstn n l) -> In x l.
Proof. intros H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.

Lemma hfold_nul : forall vv, ~ In 0 vv -> ~ In 0 (h_fold vv 24).
Proof.
  intros vv H Hin. unfold h_fold in Hin. apply in_map_iff in Hin as (x & Hx & Hxin).
  apply lower_eq0 in Hx. subst x. apply H. exact (kmt_in_firstn _ _ _ Hxin).
Qed.

Lemma hfold_range : forall vv, Forall (fun b => 0 <= b < 256) vv -> Forall (fun b => 0 <= b < 256) (h_fold vv 24).
Proof.
  intros vv H. unfold h_fold. apply Forall_forall. intros y Hy.
  apply in_map_iff in Hy as (x & <- & Hx). apply kmt_in_firstn in Hx.
  rewrite Forall_forall in H. exact (proj1 (lower_range x (H x Hx))).
Qed.

(* ======================================== the row ======================================== *)
Lemma kmt_row_go_lt : forall toks t i r, row_go toks t i = Some r -> (r < i + length toks)%nat.
Proof.
  induction toks as [|k toks IH]; intros t i r H; cbn [row_go] in H; [discriminate|].
  match type of H with context [if ?b then _ else _] => destruct b end.
  - injection H as <-. cbn [length]. lia.
  - apply IH in H. cbn [length]. lia.
Qed.

Lemma cat_row_lt : forall t r, cat_row t = Some r -> (r < pin_spec.CAT_N)%nat.
Proof. intros t r H. unfold cat_row in H. apply kmt_row_go_lt in H. exact H. Qed.

Lemma cat_ptr_some : forall cat r, 0 < cat -> cat + pin_spec.CAT_ROW * Z.of_nat pin_spec.CAT_N <= 2 ^ 64 ->
  (r < pin_spec.CAT_N)%nat -> 0 < seg_spec.cat_ptr cat (Some r) < 2 ^ 64.
Proof.
  intros cat r H0 H1 H2. unfold seg_spec.cat_ptr. unfold pin_spec.CAT_ROW, pin_spec.CAT_N in *. lia.
Qed.

(* ======================================== the model ======================================== *)
(* The sizes come from the shared model file lib/A/Prog/m_file_mdl.v (the KEYA segment lane): m_refuse_sizes, m_upd_sizes,
   upd_nth_length, mf_grows, m_refuse_grows, m_header_ok, m_key_grows. Its m_lines_ok asks mf_cur_ok of the start;
   the premise-free forms below follow from its one-step lemmas. *)
Lemma m_refuse_segs : forall c line knock, mc_seg (m_refuse c line knock) = mc_seg c.
Proof. intros c line knock. exact (proj1 (m_refuse_sizes c line knock)). Qed.

Lemma m_upd_segs_len : forall c i f, length (mc_seg (m_upd c i f)) = length (mc_seg c).
Proof. intros c i f. rewrite (proj1 (m_upd_sizes c i f)). apply upd_nth_length. Qed.

Lemma kmt_m_line_grows : forall st n l, mf_grows (fst st) (fst (m_line st n l)).
Proof.
  intros [c cur] n l. unfold m_line. cbn [fst].
  destruct (512 <=? length l)%nat; [cbn [fst]; apply m_refuse_grows|].
  destruct (h_strip (h_cut_comment l)) as [|b s]; [cbn [fst]; apply mf_grows_refl|].
  destruct (b =? LBR); [exact (proj1 (m_header_ok c (b :: s) n)) | cbn [fst]; apply m_key_grows].
Qed.

Lemma kmt_m_lines_grows : forall ls st n, mf_grows (fst st) (fst (m_lines st n ls)).
Proof.
  induction ls as [|l ls IH]; intros st n; cbn [m_lines]; [apply mf_grows_refl|].
  eapply mf_grows_trans; [apply (kmt_m_line_grows st (n + 1) l) | apply IH].
Qed.

Lemma m_lines_segs_mono : forall ls st n,
  (length (mc_seg (fst st)) <= length (mc_seg (fst (m_lines st n ls))))%nat.
Proof. intros ls st n. exact (proj1 (kmt_m_lines_grows ls st n)). Qed.

Lemma mf_fin_segs_mono : forall st line rest, (length (mc_seg (fst st)) <= length (mc_seg (mf_fin st line rest)))%nat.
Proof. intros st line rest. unfold mf_fin. apply m_lines_segs_mono. Qed.

Lemma mk_model_segs : forall mcc gi vv line, length (mc_seg (mk_mod mcc gi vv line)) = length (mc_seg mcc).
Proof.
  intros mcc gi vv line. unfold mk_mod.
  destruct (cat_row (h_fold vv 24)); [apply m_upd_segs_len | rewrite m_refuse_segs; reflexivity].
Qed.

Lemma mk_fp_seg : forall c k0 mcf gi a, (gi < length (mc_seg mcf))%nat ->
  seg_spec.mseg_addr c gi <= a < seg_spec.mseg_addr c gi + seg_spec.MSEG_SIZE -> inFP (M_FILE_FP c k0 mcf) a.
Proof.
  intros c k0 mcf gi a Hgi Ha. unfold M_FILE_FP. apply inFP_cons. left.
  unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE in *. lia.
Qed.

Lemma m_refuse_counters : forall c line knock,
  mc_refused (m_refuse c line knock) = mc_refused c + 1 /\ mc_overflow (m_refuse c line knock) = mc_overflow c /\
  (length (mc_kept c) <= length (mc_kept (m_refuse c line knock)))%nat /\
  mc_gen (m_refuse c line knock) = mc_gen c /\ mc_reading (m_refuse c line knock) = mc_reading c.
Proof.
  intros c line knock.
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact (proj1 (proj2 (m_refuse_sizes c line knock))) | split; reflexivity].
Qed.

Lemma m_upd_model_counters : forall c gi low,
  mc_refused (m_upd c gi (ms_with_model low)) = mc_refused c /\
  mc_overflow (m_upd c gi (ms_with_model low)) = mc_overflow c /\
  mc_kept (m_upd c gi (ms_with_model low)) = mc_kept c /\
  mc_gen (m_upd c gi (ms_with_model low)) = mc_gen c /\
  mc_reading (m_upd c gi (ms_with_model low)) = mc_reading c.
Proof. intros c gi low. exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))). Qed.

Lemma m_lines_kept_mono : forall ls st n,
  (length (mc_kept (fst st)) <= length (mc_kept (fst (m_lines st n ls))))%nat.
Proof. intros ls st n. exact (proj2 (kmt_m_lines_grows ls st n)). Qed.

Lemma mf_fin_kept_mono : forall st line rest,
  (length (mc_kept (fst st)) <= length (mc_kept (mf_fin st line rest)))%nat.
Proof. intros st line rest. unfold mf_fin. apply m_lines_kept_mono. Qed.

(* ================================= lists of bytes: a splice ================================= *)
(* bs with the bytes [off, off + length w) replaced by w *)
Definition kmt_splice {A} (off : nat) (w bs : list A) : list A := firstn off bs ++ w ++ skipn (off + length w) bs.

Lemma kmt_nth_firstn {A} n (l : list A) i d : (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  revert n l. induction i as [|i IH]; intros n l H; destruct n as [|n]; try lia; destruct l as [|x l]; cbn; auto.
  apply IH. lia.
Qed.

Lemma kmt_nth_skipn {A} n (l : list A) i d : nth i (skipn n l) d = nth (n + i) l d.
Proof.
  revert l. induction n as [|n IH]; intros l; [reflexivity|].
  destruct l as [|x l]; cbn [skipn]; [destruct i; reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma kmt_splice_len {A} off (w bs : list A) : (off + length w <= length bs)%nat ->
  length (kmt_splice off w bs) = length bs.
Proof. intros H. unfold kmt_splice. rewrite !length_app, length_firstn, length_skipn. lia. Qed.

Lemma kmt_nth_splice {A} off (w bs : list A) i d : (off + length w <= length bs)%nat ->
  nth i (kmt_splice off w bs) d =
  if (i <? off)%nat then nth i bs d else if (i <? off + length w)%nat then nth (i - off) w d else nth i bs d.
Proof.
  intros H. unfold kmt_splice.
  destruct (Nat.ltb_spec i off) as [H1|H1].
  - rewrite app_nth1 by (rewrite length_firstn; lia). apply kmt_nth_firstn. exact H1.
  - rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
    replace (Nat.min off (length bs)) with off by lia.
    destruct (Nat.ltb_spec i (off + length w)) as [H2|H2].
    + rewrite app_nth1 by lia. reflexivity.
    + rewrite app_nth2 by lia. rewrite kmt_nth_skipn. f_equal. lia.
Qed.

Lemma kmt_fld_nth o n bs i d : (i < n)%nat -> nth i (seg_spec.fld o n bs) d = nth (o + i) bs d.
Proof. intros H. unfold seg_spec.fld. rewrite kmt_nth_firstn by exact H. apply kmt_nth_skipn. Qed.

Lemma kmt_fld_len o n bs : (o + n <= length bs)%nat -> length (seg_spec.fld o n bs) = n.
Proof. intros H. unfold seg_spec.fld. rewrite length_firstn, length_skipn. lia. Qed.

Lemma kmt_fld_ext o n bs bs' : (o + n <= length bs)%nat -> (o + n <= length bs')%nat ->
  (forall i, (o <= i < o + n)%nat -> nth i bs' ZB0 = nth i bs ZB0) -> seg_spec.fld o n bs' = seg_spec.fld o n bs.
Proof.
  intros H1 H2 H. apply nth_ext with (d := ZB0) (d' := ZB0).
  - rewrite !kmt_fld_len by lia. reflexivity.
  - intros i Hi. rewrite kmt_fld_len in Hi by lia. rewrite !kmt_fld_nth by lia. apply H. lia.
Qed.

Lemma kmt_nth_upd {A} i j (f : A -> A) l d : (i < length l)%nat ->
  nth i (upd_nth j f l) d = if Nat.eqb i j then f (nth i l d) else nth i l d.
Proof.
  revert i j. induction l as [|x l IH]; intros i j H; cbn [length] in H; [lia|].
  destruct i as [|i], j as [|j]; cbn [upd_nth nth Nat.eqb]; try reflexivity.
  apply IH. lia.
Qed.

Lemma kmt_zs_nth : forall f j, (j < length f)%nat -> nth j (seg_spec.zs f) 0 = bv_unsigned (nth j f ZB0).
Proof.
  unfold seg_spec.zs. induction f as [|x f IH]; intros j H; cbn [length] in H; [lia|].
  destruct j as [|j]; cbn [map nth]; [reflexivity|]. apply IH. lia.
Qed.

Lemma kmt_zb_nth : forall l k, Forall (fun b => 0 <= b < 256) l ->
  bv_unsigned (nth k (seg_spec.zb l) ZB0) = nth k l 0.
Proof.
  unfold seg_spec.zb. induction l as [|x l IH]; intros k H.
  - destruct k; cbn [map nth]; unfold ZB0; rewrite Z_to_bv_unsigned; reflexivity.
  - inversion H as [|x' l' Hx Hl]; subst. destruct k as [|k]; cbn [map nth].
    + rewrite Z_to_bv_unsigned. change (bv_wrap 8 x) with (x mod 256). apply Z.mod_small. exact Hx.
    + apply IH. exact Hl.
Qed.

Lemma kmt_wz_range : forall low, Forall (fun b => 0 <= b < 256) low ->
  Forall (fun b => 0 <= b < 256) ([1; 0; 0; 0] ++ low ++ [0]).
Proof.
  intros low H. apply Forall_app. split.
  - repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil.
  - apply Forall_app. split; [exact H|]. apply Forall_cons; [cbv beta; lia | apply Forall_nil].
Qed.

(* one entry: the 4 bytes of model_set at 0x20 become le4 1 and the bytes low ++ [0] land at model (0x24); every
   other byte of the entry is the old one *)
Lemma kmt_mseg_model : forall g F F' low,
  seg_spec.mseg_enc g F -> length F' = 256%nat -> (length low < 24)%nat -> ~ In 0 low ->
  Forall (fun b => 0 <= b < 256) low ->
  (forall j, (j < 256)%nat -> (j < 32 \/ 37 + length low <= j)%nat -> nth j F' ZB0 = nth j F ZB0) ->
  (forall j, (j < 5 + length low)%nat ->
     nth (32 + j) F' ZB0 = nth j (seg_spec.zb ([1; 0; 0; 0] ++ low ++ [0])) ZB0) ->
  seg_spec.mseg_enc (ms_with_model low g) F'.
Proof.
  intros g F F' low (HL & Hname & Hrole & Hrs & Hig & Higs & Hms & Hmod & Hrf & Hif & Hgen) HL' Hlow Hnul Hrange
    Hout Hin.
  assert (Hk : forall o n, (o + n <= 32 \/ 37 + length low <= o)%nat -> (o + n <= 256)%nat ->
            seg_spec.fld o n F' = seg_spec.fld o n F).
  { intros o n H1 H2. apply kmt_fld_ext; [lia | lia | intros i Hi; apply Hout; lia]. }
  unfold seg_spec.mseg_enc, seg_spec.fldz in *.
  cbn [ms_with_model ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set ms_model ms_role_file
       ms_ignore_file ms_gen].
  split; [exact HL'|].
  split; [rewrite Hk by lia; exact Hname|].
  split; [rewrite Hk by (unfold seg_spec.MS_ROLE; lia); exact Hrole|].
  split; [rewrite Hk by (unfold seg_spec.MS_ROLE_SET; lia); exact Hrs|].
  split; [rewrite Hk by (unfold seg_spec.MS_IGNORE; lia); exact Hig|].
  split; [rewrite Hk by (unfold seg_spec.MS_IGNORE_SET; lia); exact Higs|].
  split.
  { (* model_set = 1 *)
    unfold seg_spec.flag_enc.
    transitivity (firstn 4 (seg_spec.zb ([1; 0; 0; 0] ++ low ++ [0]))); [|reflexivity].
    apply nth_ext with (d := ZB0) (d' := ZB0).
    - rewrite kmt_fld_len by (unfold seg_spec.MS_MODEL_SET; lia). reflexivity.
    - intros j Hj. rewrite kmt_fld_len in Hj by (unfold seg_spec.MS_MODEL_SET; lia).
      change (Z.to_nat 4) with 4%nat in Hj.
      rewrite kmt_fld_nth by exact Hj. change (Z.to_nat seg_spec.MS_MODEL_SET) with 32%nat.
      rewrite Hin by lia. symmetry. apply kmt_nth_firstn. exact Hj. }
  split.
  { (* model = low, its NUL *)
    change (Z.to_nat seg_spec.MS_MODEL) with 36%nat. change (Z.to_nat 24) with 24%nat.
    unfold seg_spec.cstr_enc.
    split; [apply kmt_fld_len; lia|].
    split; [exact Hlow|]. split; [exact Hnul|].
    apply nth_ext with (d := 0) (d' := 0).
    - unfold seg_spec.zs. rewrite length_firstn, length_map, kmt_fld_len by lia.
      rewrite length_app. cbn [length]. lia.
    - intros j Hj. unfold seg_spec.zs in Hj.
      rewrite length_firstn, length_map, kmt_fld_len in Hj by lia.
      rewrite kmt_nth_firstn by lia.
      rewrite kmt_zs_nth by (rewrite kmt_fld_len by lia; lia).
      rewrite kmt_fld_nth by lia.
      replace (36 + j)%nat with (32 + (4 + j))%nat by lia.
      rewrite Hin by lia. rewrite kmt_zb_nth by (apply kmt_wz_range; exact Hrange).
      reflexivity. }
  split; [rewrite Hk by (unfold seg_spec.MS_ROLE_FILE; lia); exact Hrf|].
  split; [rewrite Hk by (unfold seg_spec.MS_IGNORE_FILE; lia); exact Hif|].
  rewrite Hk by (unfold seg_spec.MS_GEN; lia). exact Hgen.
Qed.

(* ==================================== the block, through a reader ==================================== *)
Lemma sa_mconf_with_model : forall (rd rd' : reader) (c : Z) (mcc : mconf) (gi : nat) (low : list Z),
  sa_mconf rd c mcc -> (gi < length (mc_seg mcc))%nat -> (length low < 24)%nat -> ~ In 0 low ->
  Forall (fun b => 0 <= b < 256) low ->
  (forall a, c <= a < c + seg_spec.SEG_M_SIZE ->
     ~ (seg_spec.mseg_addr c gi + seg_spec.MS_MODEL_SET <= a < seg_spec.mseg_addr c gi + seg_spec.MS_MODEL_SET + 4) ->
     ~ (seg_spec.mseg_addr c gi + seg_spec.MS_MODEL <= a < seg_spec.mseg_addr c gi + seg_spec.MS_MODEL + Z.of_nat (length low) + 1) ->
     rd' a = rd a) ->
  sa_zs rd' (seg_spec.mseg_addr c gi + seg_spec.MS_MODEL) (low ++ [0]) ->
  sa_val rd' (seg_spec.mseg_addr c gi + seg_spec.MS_MODEL_SET) 4 1 ->
  sa_mconf rd' c (m_upd mcc gi (ms_with_model low)).
Proof.
  intros rd rd' c mcc gi low (bs & Hb & He) Hgi Hlow Hnul Hrange Hk Hzs Hval.
  pose proof He as (HL & Hn32 & Hsegs & Hn & Hov & Href & Hk8 & Hkept & Hknock & Hnk & Hgen & Hrd).
  set (wz := [1; 0; 0; 0] ++ low ++ [0]).
  assert (Hwr : Forall (fun b => 0 <= b < 256) wz) by (apply kmt_wz_range; exact Hrange).
  remember (seg_spec.zb wz) as W eqn:HWd.
  remember (256 * gi + 32)%nat as off eqn:Hoffd.
  assert (HW : length W = (5 + length low)%nat).
  { rewrite HWd. unfold wz, seg_spec.zb. rewrite length_map, !length_app. cbn [length]. lia. }
  assert (HLn : Z.of_nat (length bs) = 9236) by exact HL.
  assert (Hoff : (off + length W <= length bs)%nat) by lia.
  set (bs' := kmt_splice off W bs).
  assert (HL' : length bs' = length bs) by (apply kmt_splice_len; exact Hoff).
  assert (Hnth : forall i, nth i bs' ZB0 =
     if (i <? off)%nat then nth i bs ZB0 else if (i <? off + length W)%nat then nth (i - off) W ZB0 else nth i bs ZB0).
  { intros i. apply kmt_nth_splice. exact Hoff. }
  assert (Hout : forall o n, (o + n <= off \/ off + length W <= o)%nat -> (o + n <= length bs)%nat ->
            seg_spec.fld o n bs' = seg_spec.fld o n bs).
  { intros o n H1 H2. apply kmt_fld_ext; [exact H2 | lia |].
    intros i Hi. rewrite Hnth. destruct (Nat.ltb_spec i off); [reflexivity|].
    destruct (Nat.ltb_spec i (off + length W)); [lia | reflexivity]. }
  unfold sa_mconf, sa_mconfp. exists bs'. split.
  - (* the bytes the reader sees *)
    intros i Hi. rewrite HL' in Hi. rewrite Hnth.
    destruct (Nat.ltb_spec i off) as [H1|H1].
    + rewrite Hk by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.MS_MODEL_SET, seg_spec.MS_MODEL,
                       seg_spec.SEG_M_SIZE; lia).
      exact (Hb i Hi).
    + destruct (Nat.ltb_spec i (off + length W)) as [H2|H2].
      * rewrite HWd. rewrite kmt_zb_nth by exact Hwr.
        destruct (Nat.ltb_spec (i - off) 4) as [H3|H3].
        -- replace (c + Z.of_nat i) with (seg_spec.mseg_addr c gi + seg_spec.MS_MODEL_SET + Z.of_nat (i - off))
             by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.MS_MODEL_SET; lia).
           rewrite (Hval (i - off)%nat H3). f_equal. unfold wz.
           destruct (i - off)%nat as [|[|[|[|k]]]] eqn:E; [reflexivity..|lia].
        -- assert (Hj : (i - off - 4 < length (low ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
           replace (c + Z.of_nat i) with (seg_spec.mseg_addr c gi + seg_spec.MS_MODEL + Z.of_nat (i - off - 4))
             by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.MS_MODEL; lia).
           rewrite (Hzs (i - off - 4)%nat Hj). f_equal. unfold wz.
           rewrite (app_nth2 [1; 0; 0; 0]) by (cbn [length]; lia). reflexivity.
      * rewrite Hk by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.MS_MODEL_SET, seg_spec.MS_MODEL,
                         seg_spec.SEG_M_SIZE; lia).
        exact (Hb i Hi).
  - (* the encoding *)
    unfold seg_spec.mconf_encp, seg_spec.fldz.
    cbn [m_upd m_set_segs mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
    rewrite upd_nth_len.
    split; [rewrite HL'; exact HL|].
    split; [exact Hn32|].
    split.
    { intros i Hi. rewrite kmt_nth_upd by exact Hi. destruct (Nat.eqb_spec i gi) as [->|Hne].
      - apply (kmt_mseg_model _ (seg_spec.fld (256 * gi) 256 bs)).
        + exact (Hsegs gi Hgi).
        + apply kmt_fld_len. rewrite HL'. lia.
        + exact Hlow.
        + exact Hnul.
        + exact Hrange.
        + intros j Hj1 Hj2. rewrite !kmt_fld_nth by exact Hj1. rewrite Hnth.
          destruct (Nat.ltb_spec (256 * gi + j) off); [reflexivity|].
          destruct (Nat.ltb_spec (256 * gi + j) (off + length W)); [lia | reflexivity].
        + intros j Hj. rewrite kmt_fld_nth by lia. rewrite Hnth.
          destruct (Nat.ltb_spec (256 * gi + (32 + j)) off); [lia|].
          destruct (Nat.ltb_spec (256 * gi + (32 + j)) (off + length W)); [|lia].
          replace (256 * gi + (32 + j) - off)%nat with j by lia. rewrite HWd. reflexivity.
      - rewrite Hout by lia. exact (Hsegs i Hi). }
    split; [rewrite Hout by (unfold seg_spec.MC_N; lia); exact Hn|].
    split; [rewrite Hout by (unfold seg_spec.MC_OVERFLOW; lia); exact Hov|].
    split; [rewrite Hout by (unfold seg_spec.MC_REFUSED; lia); exact Href|].
    split; [exact Hk8|].
    split; [intros i Hi; rewrite !Hout by (unfold seg_spec.MC_KEPT, seg_spec.MC_KNOCK; lia); exact (Hkept i Hi)|].
    split; [intros i Hi; rewrite Hout by (unfold seg_spec.MC_KNOCK; lia); exact (Hknock i Hi)|].
    split; [rewrite Hout by (unfold seg_spec.MC_NKEPT; lia); exact Hnk|].
    split; [rewrite Hout by (unfold seg_spec.MC_GEN; lia); exact Hgen|].
    rewrite Hout by (unfold seg_spec.MC_READING; lia). exact Hrd.
Qed.

Lemma sa_mconf_kept : forall (rd rd' : reader) c mc, sa_mconf rd c mc ->
  (forall a, c <= a < c + seg_spec.SEG_M_SIZE -> rd' a = rd a) -> sa_mconf rd' c mc.
Proof.
  intros rd rd' c mc (bs & Hb & He) Hk. unfold sa_mconf, sa_mconfp. exists bs. split; [|exact He].
  intros i Hi. destruct He as (HL & _). rewrite Hk by lia. exact (Hb i Hi).
Qed.

Print Assumptions sa_mconf_with_model.
