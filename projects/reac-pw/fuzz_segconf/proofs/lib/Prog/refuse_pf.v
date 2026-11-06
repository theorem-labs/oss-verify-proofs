(** reac-pw/fuzz_segconf, plain build: refuse's two printf callee premises (Prog/refuse_pf_c.v: rf_snprintf for the
    address prefix, rf_vsnprintf for the 17 refusal formats through refuse's va_list) follow from the printf
    contracts snprintf_contract (Prog/snprintf_c.v) and vsnprintf_contract (Prog/vsnprintf_c.v). No function of the
    binary is walked here: each lemma instantiates the contract at refuse's call shape and reads its post as
    seg_env.ret_post_fp.

    - The text: SegModel.fmt (Spec/SegModel.v) is the printf text both contracts produce. For snprintf, pf_parse and
      pf_text of "%s:%d: " / "%s: " compute it (SegModel.dec is printf_facts_c.pf_dec below 2^31: two digit loops of
      fuel 20 and 11). For vsnprintf, Spec/SegPrintfBridge.seg_printf_model gives the model equation for every
      format of its class; the REFUSE_FORMATS are in SegPrintfBridge.SEG_FORMATS, and va_arg_ok's bounds (a string
      of at most 65535 bytes, an integer in [0, 2^31)) give sp_fit and the INT_MAX bound (|fmt f a| <= |f| + the
      arguments' lengths, at most 3 arguments, |f| <= 200).
    - The arguments: a string's slack is cut to the bytes up to the next 8-byte boundary, so the span read is at most
      |s| + 8 bytes, which va_arg_ok keeps apart from the stack region and the refusal slot.
    - The machine: printf_env's numbers (sa_got_guard, sa_guard, sa_ro_end, sa_img_end of SA) are the contracts'
      GOT_GUARD, GUARD, RO_END, IMG_END; PRINTF_K = SNPRINTF_K >= VSNPRINTF_K.

    The module RpfPure holds the lemmas that mention no image (SegModel, SegPrintfBridge, seg_spec); the UBSan twin
    U/Prog/refuse_pf.v imports it. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP Arr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require Prelim FmtFp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Printf_model.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegPrintfBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import printf_facts_c snprintf_c printf_model_c
  vsnprintf_c refuse_pf_c.
Import ListNotations.
Open Scope Z_scope.

(** * Image-free facts (shared with the UBSan build) *)
Module RpfPure.

(** ** Bytes *)
Lemma rp_byte_rng : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

Lemma rp_zb_zs : forall bs : list byte, zb (zs bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn. f_equal; [|exact IH].
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma rp_zs_pos : forall bs, ~ In 0 (zs bs) -> Forall (fun c => 0 < c < 256) (zs bs).
Proof.
  intros bs Hn. apply Forall_forall. intros c Hc.
  assert (c <> 0) by (intros ->; exact (Hn Hc)).
  unfold zs in Hc. apply in_map_iff in Hc as (b & <- & _). pose proof (rp_byte_rng b). lia.
Qed.

Lemma rp_u64s : forall ws, u64s ws = concat (map le8 ws).
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn -[le8]. rewrite IH. reflexivity. Qed.

(** ** Decimal digits *)
Lemma rp_dec_go_S : forall f n acc,
  dec_go (S f) n acc = if n <? 10 then (48 + n mod 10) :: acc else dec_go f (n / 10) ((48 + n mod 10) :: acc).
Proof. reflexivity. Qed.

(** The digit loop's fuel does not matter once it covers the digits. *)
Lemma rp_dec_go_fuel : forall f n acc g, 0 <= n < 10 ^ Z.of_nat (S f) -> (f <= g)%nat ->
  dec_go (S g) n acc = dec_go (S f) n acc.
Proof.
  induction f as [|f IH]; intros n acc g Hn Hg.
  - rewrite !rp_dec_go_S. change (10 ^ Z.of_nat 1) with 10 in Hn.
    replace (n <? 10) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - destruct g as [|g]; [lia|]. rewrite (rp_dec_go_S (S g)), (rp_dec_go_S (S f)).
    destruct (Z.ltb_spec n 10) as [H|H]; [reflexivity|].
    apply IH; [|lia]. split; [apply Z.div_pos; lia|].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hn by lia. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma rp_dec_nonneg : forall z, 0 <= z < 2 ^ 31 -> dec z = dec_go 11 z [].
Proof.
  intros z Hz. unfold dec. replace (z <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  apply (rp_dec_go_fuel 10 z [] 19); [|lia]. change (10 ^ Z.of_nat 11) with 100000000000. lia.
Qed.

Lemma rp_dec_go_len : forall f n acc, (length (dec_go f n acc) <= f + length acc)%nat.
Proof.
  induction f as [|f IH]; intros n acc; [cbn; lia|]. rewrite rp_dec_go_S.
  destruct (n <? 10); [cbn [length]; lia|].
  pose proof (IH (n / 10) ((48 + n mod 10) :: acc)) as H. cbn [length] in H. lia.
Qed.

Lemma rp_dec_len : forall z, (length (dec z) <= 21)%nat.
Proof.
  intros z. unfold dec. destruct (z <? 0).
  - pose proof (rp_dec_go_len 20 (- z) []) as H. cbn [length] in H |- *. lia.
  - pose proof (rp_dec_go_len 20 z []) as H. cbn [length] in H. lia.
Qed.

(** ** The arguments refuse passes: strings of at most 65535 bytes with no NUL, integers in [0, 2^31). The length
    bound is stated in Z: a nat literal this large is an opaque Nat.of_num_uint term that lia cannot read. *)
Definition arg_small (x : arg) : Prop :=
  match x with AS s => Z.of_nat (length s) <= 65535 /\ ~ In 0 s | AI z => 0 <= z < 2 ^ 31 end.

(** The most text one argument adds to fmt. *)
Definition alen (x : arg) : nat := length (arg_s x) + length (dec (arg_i x)).
Fixpoint asum (a : list arg) : nat := match a with [] => 0 | x :: a' => alen x + asum a' end.

Lemma rp_fmt_len : forall n f a, (length f < n)%nat -> (length (fmt f a) <= length f + asum a)%nat.
Proof.
  induction n as [|n IH]; intros f a Hl; [cbn in Hl; lia|].
  destruct f as [|c f1]; [cbn; lia|]. cbn [length fmt] in Hl |- *.
  destruct (negb (c =? 37)).
  { cbn [length]. pose proof (IH f1 a ltac:(lia)). lia. }
  destruct f1 as [|c1 f2]; [cbn; lia|]. cbn [length] in Hl |- *.
  destruct (c1 =? 115).
  { destruct a as [|x a]; [cbn; lia|]. cbn [asum]. rewrite length_app. pose proof (IH f2 a ltac:(lia)).
    unfold alen. lia. }
  destruct ((c1 =? 100) || (c1 =? 117)).
  { destruct a as [|x a]; [cbn; lia|]. cbn [asum]. rewrite length_app. pose proof (IH f2 a ltac:(lia)).
    unfold alen. lia. }
  destruct (c1 =? 122).
  { destruct f2 as [|c2 f3]; [cbn; lia|]. cbn [length] in Hl |- *. destruct (c2 =? 117); [|cbn; lia].
    destruct a as [|x a]; [cbn; lia|]. cbn [asum]. rewrite length_app. pose proof (IH f3 a ltac:(lia)).
    unfold alen. lia. }
  destruct (c1 =? 46); [|cbn; lia].
  destruct f2 as [|d1 [|d2 [|c3 f4]]]; try (cbn; lia). cbn [length] in Hl |- *.
  destruct (isdigit d1 && isdigit d2 && (c3 =? 115)); [|cbn; lia].
  destruct a as [|x a]; [cbn; lia|]. cbn [asum]. rewrite length_app, length_firstn.
  pose proof (IH f4 a ltac:(lia)). unfold alen. lia.
Qed.

Lemma rp_alen_small : forall x, arg_small x -> Z.of_nat (alen x) <= 65556.
Proof.
  intros [s|z] H; unfold alen; cbn [arg_s arg_i].
  - destruct H as [Hl Hn]. rewrite cut_nul_id by exact Hn. pose proof (rp_dec_len 0). lia.
  - pose proof (rp_dec_len z). cbn [length]. lia.
Qed.

Lemma rp_asum_small : forall a, Forall arg_small a -> Z.of_nat (asum a) <= 65556 * Z.of_nat (length a).
Proof.
  induction 1 as [|x a Hx Ha IH]; cbn [asum length]; [lia|]. pose proof (rp_alen_small x Hx). lia.
Qed.

(** Formats of at most 200 bytes and 3 conversions. *)
Definition fs_small (fs : list (list Z)) : bool :=
  forallb (fun f => Nat.leb (length f) 200 && Nat.leb (length (conv_kinds f)) 3) fs.

Lemma rp_fmt_bound : forall fs f a, fs_small fs = true -> In f fs -> conv_kinds f = map arg_is_s a ->
  Forall arg_small a -> Z.of_nat (length (fmt f a)) <= 200 + 3 * 65556.
Proof.
  intros fs f a Hs Hin Hk Ha. unfold fs_small in Hs. rewrite forallb_forall in Hs. specialize (Hs f Hin).
  apply andb_prop in Hs as [H1 H2]. apply Nat.leb_le in H1. apply Nat.leb_le in H2.
  rewrite Hk, length_map in H2.
  pose proof (rp_fmt_len (S (length f)) f a ltac:(lia)) as L. pose proof (rp_asum_small a Ha) as A. lia.
Qed.

Lemma rp_refuse_small : fs_small REFUSE_FORMATS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rp_addr_small : fs_small [F_addr_line; F_addr] = true.
Proof. vm_compute. reflexivity. Qed.

(** ** sp_fit and the model's argument list of a format of SegPrintfBridge's class *)
(** A model argument of sp_pargs against the spine's argument it reads. *)
Definition pa_rel (x : arg) (p : Printf_model.parg) : Prop :=
  match x with
  | AS s => p = Printf_model.PA_s (cut_nul s)
  | AI z => p = Printf_model.PA_i z \/ p = Printf_model.PA_u z \/ p = Printf_model.PA_ull z
  end.

Lemma rp_fit_pargs : forall n f a, (length f < n)%nat -> SegPrintfBridge.sp_ok f = true ->
  conv_kinds f = map arg_is_s a -> Forall arg_small a ->
  SegPrintfBridge.sp_fit f a /\ Forall2 pa_rel a (SegPrintfBridge.sp_pargs f a).
Proof.
  induction n as [|n IH]; intros f a Hl Hok Hk Ha; [cbn in Hl; lia|].
  destruct f as [|c f1].
  { cbn in Hk. destruct a as [|x a]; [|discriminate Hk]. split; [exact I|constructor]. }
  cbn [length] in Hl.
  destruct (Z.eqb_spec c 37) as [->|Hc].
  2:{ rewrite SegPrintfBridge.sp_ok_lit in Hok by exact Hc. apply andb_prop in Hok as [_ Hok].
      rewrite SegPrintfBridge.fit_lit, SegPrintfBridge.pargs_lit by exact Hc.
      apply IH; [lia | exact Hok | | exact Ha].
      rewrite <- Hk. cbn [conv_kinds]. rewrite (proj2 (Z.eqb_neq c 37) Hc). reflexivity. }
  destruct f1 as [|c1 f2]; [vm_compute in Hok; discriminate Hok|]. cbn [length] in Hl.
  destruct (Z.eqb_spec c1 115) as [->|N1].
  { (* %s *)
    change (SegPrintfBridge.sp_ok f2 = true) in Hok.
    change (true :: conv_kinds f2 = map arg_is_s a) in Hk.
    destruct a as [|x a]; [cbn in Hk; discriminate Hk|]. cbn [map] in Hk. injection Hk as Hx Hk.
    destruct x as [s|z]; [|cbn in Hx; discriminate Hx].
    destruct (IH f2 a ltac:(lia) Hok Hk (Forall_inv_tail Ha)) as [F1 F2].
    split; [exact F1|].
    change (Forall2 pa_rel (AS s :: a) (Printf_model.PA_s (cut_nul s) :: SegPrintfBridge.sp_pargs f2 a)).
    constructor; [reflexivity | exact F2]. }
  destruct (Z.eqb_spec c1 100) as [->|N2].
  { (* %d *)
    change (SegPrintfBridge.sp_ok f2 = true) in Hok.
    change (false :: conv_kinds f2 = map arg_is_s a) in Hk.
    destruct a as [|x a]; [cbn in Hk; discriminate Hk|]. cbn [map] in Hk. injection Hk as Hx Hk.
    destruct x as [s|z]; [cbn in Hx; discriminate Hx|].
    pose proof (Forall_inv Ha) as Hz. cbn in Hz.
    destruct (IH f2 a ltac:(lia) Hok Hk (Forall_inv_tail Ha)) as [F1 F2].
    split.
    - change ((-2^31 <= z < 2^31) /\ SegPrintfBridge.sp_fit f2 a). split; [lia | exact F1].
    - change (Forall2 pa_rel (AI z :: a) (Printf_model.PA_i z :: SegPrintfBridge.sp_pargs f2 a)).
      constructor; [left; reflexivity | exact F2]. }
  destruct (Z.eqb_spec c1 117) as [->|N3].
  { (* %u *)
    change (SegPrintfBridge.sp_ok f2 = true) in Hok.
    change (false :: conv_kinds f2 = map arg_is_s a) in Hk.
    destruct a as [|x a]; [cbn in Hk; discriminate Hk|]. cbn [map] in Hk. injection Hk as Hx Hk.
    destruct x as [s|z]; [cbn in Hx; discriminate Hx|].
    pose proof (Forall_inv Ha) as Hz. cbn in Hz.
    destruct (IH f2 a ltac:(lia) Hok Hk (Forall_inv_tail Ha)) as [F1 F2].
    split.
    - change ((0 <= z < 2^32) /\ SegPrintfBridge.sp_fit f2 a). split; [lia | exact F1].
    - change (Forall2 pa_rel (AI z :: a) (Printf_model.PA_u z :: SegPrintfBridge.sp_pargs f2 a)).
      constructor; [right; left; reflexivity | exact F2]. }
  destruct (Z.eqb_spec c1 122) as [->|N4].
  { (* %zu *)
    destruct f2 as [|c2 f3]; [vm_compute in Hok; discriminate Hok|].
    change ((c2 =? 117) && SegPrintfBridge.sp_ok f3 = true) in Hok. apply andb_prop in Hok as [H117 Hok].
    apply Z.eqb_eq in H117. subst c2. cbn [length] in Hl.
    change (false :: conv_kinds f3 = map arg_is_s a) in Hk.
    destruct a as [|x a]; [cbn in Hk; discriminate Hk|]. cbn [map] in Hk. injection Hk as Hx Hk.
    destruct x as [s|z]; [cbn in Hx; discriminate Hx|].
    pose proof (Forall_inv Ha) as Hz. cbn in Hz.
    destruct (IH f3 a ltac:(lia) Hok Hk (Forall_inv_tail Ha)) as [F1 F2].
    split.
    - change ((0 <= z < 2^64) /\ SegPrintfBridge.sp_fit f3 a). split; [lia | exact F1].
    - change (Forall2 pa_rel (AI z :: a) (Printf_model.PA_ull z :: SegPrintfBridge.sp_pargs f3 a)).
      constructor; [right; right; reflexivity | exact F2]. }
  destruct (Z.eqb_spec c1 46) as [->|N5].
  { (* %.NNs *)
    destruct f2 as [|d1 [|d2 [|c3 f4]]]; try (vm_compute in Hok; discriminate Hok).
    change (isdigit d1 && isdigit d2 && (c3 =? 115) && SegPrintfBridge.sp_ok f4 = true) in Hok.
    apply andb_prop in Hok as [Hok Hf4]. apply andb_prop in Hok as [_ H115].
    apply Z.eqb_eq in H115. subst c3. cbn [length] in Hl.
    change (true :: conv_kinds f4 = map arg_is_s a) in Hk.
    destruct a as [|x a]; [cbn in Hk; discriminate Hk|]. cbn [map] in Hk. injection Hk as Hx Hk.
    destruct x as [s|z]; [|cbn in Hx; discriminate Hx].
    destruct (IH f4 a ltac:(lia) Hf4 Hk (Forall_inv_tail Ha)) as [F1 F2].
    split; [exact F1|].
    change (Forall2 pa_rel (AS s :: a) (Printf_model.PA_s (cut_nul s) :: SegPrintfBridge.sp_pargs f4 a)).
    constructor; [reflexivity | exact F2]. }
  exfalso. rewrite SegPrintfBridge.sp_ok_pct in Hok.
  rewrite (proj2 (Z.eqb_neq _ _) N1), (proj2 (Z.eqb_neq _ _) N2), (proj2 (Z.eqb_neq _ _) N3),
    (proj2 (Z.eqb_neq _ _) N4), (proj2 (Z.eqb_neq _ _) N5) in Hok.
  cbn in Hok. discriminate Hok.
Qed.

Lemma rp_refuse_sub : forall f, In f REFUSE_FORMATS -> In f SegPrintfBridge.SEG_FORMATS.
Proof.
  intros f H. unfold REFUSE_FORMATS in H. unfold SegPrintfBridge.SEG_FORMATS. cbn [In] in H |- *. tauto.
Qed.

(** The model equation of a refusal format at refuse's arguments, and the model's argument list. *)
Lemma rp_model : forall f a, In f REFUSE_FORMATS -> conv_kinds f = map arg_is_s a -> Forall arg_small a ->
  SegPrintfBridge.pm_eq f a /\ Forall2 pa_rel a (SegPrintfBridge.sp_pargs f a).
Proof.
  intros f a Hin Hk Ha.
  destruct (SegPrintfBridge.seg_format_good f (rp_refuse_sub f Hin)) as (Hok & _ & _).
  destruct (rp_fit_pargs (S (length f)) f a ltac:(lia) Hok Hk Ha) as [Hfit Hrel].
  split; [|exact Hrel]. unfold SegPrintfBridge.pm_eq.
  apply SegPrintfBridge.seg_printf_model; [exact Hok | exact Hfit |].
  pose proof (rp_fmt_bound REFUSE_FORMATS f a rp_refuse_small Hin Hk Ha).
  unfold Prelim.zlength, FmtFp.INT_MAX. lia.
Qed.

End RpfPure.
Import RpfPure.

(** * This build's facts *)

(** The pf_arg snprintf reads for a spine argument. *)
Definition to_pf (x : arg) : pf_arg := match x with AS s => APtr s | AI z => AInt z end.

Lemma pf_digits_dec_go : forall f n acc, 0 <= n -> pf_digits f n acc = dec_go f n acc.
Proof.
  induction f as [|f IH]; intros n acc Hn; [reflexivity|]. rewrite rp_dec_go_S. cbn [pf_digits].
  destruct (Z.ltb_spec n 10) as [H|H].
  - rewrite Z.mod_small by lia. reflexivity.
  - apply IH. apply Z.div_pos; lia.
Qed.

Lemma dec_pf_dec : forall z, 0 <= z < 2 ^ 31 -> dec z = pf_dec z.
Proof.
  intros z Hz. rewrite rp_dec_nonneg by exact Hz. unfold pf_dec.
  replace (z <? 0) with false by (symmetry; apply Z.ltb_ge; lia). symmetry. apply pf_digits_dec_go. lia.
Qed.

Lemma pf_bytes_zs : forall bs, pf_bytes (zs bs ++ [0]) = bs ++ [ZERO].
Proof.
  intros bs. unfold pf_bytes. rewrite map_app. change (map (Z_to_bv 8) (zs bs)) with (zb (zs bs)).
  rewrite rp_zb_zs. reflexivity.
Qed.

(** The format at fp: its bytes and NUL. *)
Lemma fmt_bytes : forall m fp f, cstrz_at rsegs m fp f -> bytes_at rsegs m fp (pf_bytes (f ++ [0])).
Proof. intros m fp f (bs & B & <- & _). rewrite pf_bytes_zs. exact B. Qed.

(** A string argument as snprintf reads it: its bytes, its NUL and the slack up to the next 8-byte boundary, apart
    from the stack region [lo, S) and from the destination [D, D + n) inside the slot. *)
Lemma str_ok : forall m S lo Dslot D n r s, Dslot <= D -> D + n <= Dslot + RC_REFUSAL_LEN ->
  va_arg_ok rsegs m [(lo, S); (Dslot, Dslot + RC_REFUSAL_LEN)] r (AS s) -> pf_arg_ok m S lo D n r (APtr s).
Proof.
  intros m S lo Dslot D n r s HD1 HD2 (Hr0 & (bs & sl & B & <- & NZ & SL) & _ & AP).
  pose proof (Forall_inv AP) as AP1. pose proof (Forall_inv (Forall_inv_tail AP)) as AP2.
  cbn [fst snd] in AP1, AP2. unfold apart in AP1, AP2. unfold RC_REFUSAL_LEN in *.
  destruct (bv_unsigned_in_range 64 r) as [R0 _].
  unfold pf_arg_ok.
  set (k := (- (bv_unsigned r + Z.of_nat (length (zs bs)) + 1)) mod 8) in *.
  assert (K8 : 0 <= k < 8) by (apply Z.mod_pos_bound; lia).
  split; [apply rp_zs_pos; exact NZ|].
  exists (firstn (Z.to_nat k) sl).
  assert (LF : Z.of_nat (length (firstn (Z.to_nat k) sl)) = k) by (rewrite length_firstn; lia).
  split; [|split; [lia | split; [lia | split; lia]]].
  rewrite pf_bytes_zs.
  rewrite <- (firstn_skipn (Z.to_nat k) sl) in B.
  replace (bs ++ ZERO :: firstn (Z.to_nat k) sl ++ skipn (Z.to_nat k) sl)
    with ((bs ++ ZERO :: firstn (Z.to_nat k) sl) ++ skipn (Z.to_nat k) sl) in B
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in B. destruct B as [B _].
  replace ((bs ++ [ZERO]) ++ firstn (Z.to_nat k) sl) with (bs ++ ZERO :: firstn (Z.to_nat k) sl)
    by (rewrite <- app_assoc; reflexivity).
  exact B.
Qed.

Lemma va_small : forall m W rs args, va_args_ok rsegs m W rs args -> Forall arg_small args.
Proof.
  intros m W rs args. revert rs. induction args as [|x args IH]; intros rs Hv; [constructor|].
  destruct rs as [|r rs]; [destruct Hv|]. destruct Hv as [Hx Hv]. constructor; [|exact (IH rs Hv)].
  destruct x as [s|z]; cbn [arg_small].
  - destruct Hx as (_ & (bs & sl & _ & _ & NZ & _) & Hl & _). split; [|exact NZ].
    apply Nat2Z.inj_le in Hl. change (Z.of_nat 65535%nat) with 65535 in Hl. exact Hl.
  - destruct Hx as [Hz _]. exact Hz.
Qed.

(** snprintf's arguments (rf_snprintf: a3 .. a7). *)
Lemma va_pf_args : forall m S lo Dslot D n rs args, Dslot <= D -> D + n <= Dslot + RC_REFUSAL_LEN ->
  va_args_ok rsegs m [(lo, S); (Dslot, Dslot + RC_REFUSAL_LEN)] rs args -> pf_args_ok m S lo D n rs (map to_pf args).
Proof.
  intros m S lo Dslot D n rs args HD1 HD2. revert rs.
  induction args as [|x args IH]; intros rs Hv; [destruct rs; exact I|].
  destruct rs as [|r rs]; [destruct Hv|]. destruct Hv as [Hx Hv]. split; [|exact (IH rs Hv)].
  destruct x as [s|z].
  - exact (str_ok m S lo Dslot D n r s HD1 HD2 Hx).
  - destruct Hx as [Hz Hr]. cbn [to_pf pf_arg_ok]. split; [lia|]. rewrite Hr. reflexivity.
Qed.

(** vsnprintf's arguments (rf_vsnprintf: the saved slots), read as sp_pargs gives them. *)
Lemma va_pm_args : forall m S lo Dslot D n args ps rs, Dslot <= D -> D + n <= Dslot + RC_REFUSAL_LEN ->
  Forall2 pa_rel args ps -> va_args_ok rsegs m [(lo, S); (Dslot, Dslot + RC_REFUSAL_LEN)] rs args ->
  pm_args_ok m S lo D n rs ps.
Proof.
  intros m S lo Dslot D n args ps rs HD1 HD2 HR. revert rs.
  induction HR as [|x p args ps Hxp HR IH]; intros rs Hv; [destruct rs; exact I|].
  destruct rs as [|r rs]; [destruct Hv|]. destruct Hv as [Hx Hv]. split; [|exact (IH rs Hv)].
  destruct x as [s|z]; cbn [pa_rel] in Hxp.
  - subst p. cbn [pm_arg_ok].
    pose proof Hx as (_ & (bs & sl & _ & _ & NZ & _) & _). rewrite (cut_nul_id s NZ).
    exact (str_ok m S lo Dslot D n r s HD1 HD2 Hx).
  - destruct Hx as [Hz Hr]. destruct Hxp as [ -> | [ -> | -> ] ]; cbn [pm_arg_ok pf_arg_ok].
    + split; [lia|]. rewrite Hr. reflexivity.
    + split; [lia|]. rewrite Hr. apply Z.mod_small. lia.
    + exact Hr.
Qed.

(** The text of the two address prefixes: pf_parse and pf_text compute SegModel.fmt. *)
Lemma text_ok : forall f a, In f [F_addr_line; F_addr] -> conv_kinds f = map arg_is_s a -> Forall arg_small a ->
  exists ps, pf_parse f = Some ps /\ pf_text ps (map to_pf a) = Some (fmt f a).
Proof.
  intros f a Hin Hk Ha. destruct Hin as [<-|[<-|[]]].
  - assert (K : conv_kinds F_addr_line = [true; false]) by (vm_compute; reflexivity).
    rewrite K in Hk. destruct a as [|[s|z1] [|[s2|z] [|x3 a]]]; cbn in Hk; try discriminate Hk.
    pose proof (Forall_inv Ha) as [_ Hs]. pose proof (Forall_inv (Forall_inv_tail Ha)) as Hz. cbn in Hz.
    exists [Ps; PLit 58; Pd; PLit 58; PLit 32]. split; [vm_compute; reflexivity|].
    rewrite fmt_addr_line, (cut_nul_id s Hs), (dec_pf_dec z Hz). reflexivity.
  - assert (K : conv_kinds F_addr = [true]) by (vm_compute; reflexivity).
    rewrite K in Hk. destruct a as [|[s|z1] [|x2 a]]; cbn in Hk; try discriminate Hk.
    pose proof (Forall_inv Ha) as [_ Hs].
    exists [Ps; PLit 58; PLit 32]. split; [vm_compute; reflexivity|].
    rewrite fmt_addr, (cut_nul_id s Hs). reflexivity.
Qed.

(** The destination: present and writable, one block of junk. *)
Lemma dst_cells : forall m D n junk, wr_at rsegs m D n -> bytes_at rsegs m D junk -> Z.of_nat (length junk) = n ->
  rw_cells rsegs m D [CB (Z.to_nat n) junk].
Proof.
  intros m D n junk W B L. subst n. rewrite Nat2Z.id. apply rw_cells_of_u8arr. split; assumption.
Qed.

Lemma saved_u64s : forall m a ws, saved_at rsegs m a ws -> bytes_at rsegs m a (u64s ws).
Proof. intros m a ws H. unfold saved_at in H. rewrite rp_u64s. exact H. Qed.

(** printf's post is refuse's: the same conjuncts, the text snprintf_s n f args and its NUL. *)
Lemma post_conv : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m lo D n f args ms',
  printf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo D (snprintf_r f args) (snprintf_s n f args) m
    ms' ->
  rf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m lo D n f args ms'.
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m lo D n f args ms' P.
  unfold printf_post in P.
  destruct P as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & Ft & fc' & m'
                 & E & MU & WM & MI & TM & FR & FK & ST & BY).
  unfold rf_post, ret_post_fp.
  exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, Ft, fc', m'.
  split; [exact E|]. split; [exact FR|]. split; [exact FK|]. split; [exact MU|]. split; [exact WM|].
  split; [exact MI|]. split; [exact TM|]. split; [exact ST|].
  unfold pf_bytes in BY. rewrite map_app in BY. exact BY.
Qed.

(** * The two premises *)
Theorem rf_snprintf_of : snprintf_contract -> rf_snprintf.
Proof.
  intros C. unfold rf_snprintf.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo Dslot
    f args FM DS ENV STK MI.
  destruct FM as (Hin & Hk & Hz & Hlo & Hhi & Hva).
  destruct DS as (D0 & Hn1 & HD1 & HD2 & NI & WR & (junk & BJ & LJ) & AP).
  destruct ENV as (FR & TM & (GG & g & GD) & IE & SH).
  destruct STK as (ST & SK & _ & _).
  pose proof (va_small _ _ _ _ Hva) as Hsm.
  destruct (text_ok f args Hin Hk Hsm) as (ps & HP & HT).
  pose proof (rp_fmt_bound _ f args rp_addr_small Hin Hk Hsm) as HB.
  assert (HN : 1 <= bv_unsigned a1 < 2 ^ 31) by (unfold RC_REFUSAL_LEN in HD2; lia).
  assert (HL : Z.of_nat (length (fmt f args)) < 2 ^ 31 - 1) by lia.
  assert (HK : lo <= bv_unsigned sp - SNPRINTF_K) by (unfold SNPRINTF_K; unfold PRINTF_K in SK; lia).
  pose proof (C ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                lo g f ps (map to_pf args) (fmt f args) junk) as CC.
  cbv zeta in CC.
  eapply evt_mono.
  - exact (CC (fmt_bytes _ _ _ Hz) Hlo Hhi HP (va_pf_args _ _ _ _ _ _ _ _ HD1 HD2 Hva) HT
              (dst_cells _ _ _ _ WR BJ LJ) HN HL D0 AP NI ST HK IE SH FR MI TM GG GD).
  - intros ms' P. apply post_conv. exact P.
Qed.

Theorem rf_vsnprintf_of : vsnprintf_contract -> rf_vsnprintf.
Proof.
  intros C. unfold rf_vsnprintf.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo Dslot
    f slots args FM SV HVA HVB DS ENV STK MI.
  destruct FM as (Hin & Hk & Hz & Hlo & Hhi & Hva).
  destruct DS as (D0 & Hn1 & HD1 & HD2 & NI & WR & (junk & BJ & LJ) & AP).
  destruct ENV as (FR & TM & (GG & g & GD) & IE & SH).
  destruct STK as (ST & SK & _ & _).
  pose proof (va_small _ _ _ _ Hva) as Hsm.
  destruct (rp_model f args Hin Hk Hsm) as [PM Hrel].
  destruct (SegPrintfBridge.seg_format_good f (rp_refuse_sub f Hin)) as (_ & P1 & FB).
  assert (HN : 1 <= bv_unsigned a1 < 2 ^ 31) by (unfold RC_REFUSAL_LEN in HD2; lia).
  assert (HK : lo <= bv_unsigned sp - VSNPRINTF_K) by (unfold VSNPRINTF_K; unfold PRINTF_K in SK; lia).
  pose proof (C ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                lo g f slots (SegPrintfBridge.sp_pargs f args) (snprintf_r f args) (fmt f args) junk) as CC.
  cbv zeta in CC.
  eapply evt_mono.
  - exact (CC (fmt_bytes _ _ _ Hz) Hlo Hhi FB P1 (saved_u64s _ _ _ SV) HVA HVB
              (va_pm_args _ _ _ _ _ _ _ _ _ HD1 HD2 Hrel Hva) PM
              (dst_cells _ _ _ _ WR BJ LJ) HN D0 AP NI ST HK IE SH FR MI TM GG GD).
  - intros ms' P. apply post_conv. exact P.
Qed.
