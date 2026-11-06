(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin LxState LxMem LxStep LxCheck LxSem LxWf LxSoundVal LxSoundMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import LXL LXS LXM LXI LXC LXSEM LXWF LXSV LXSM.
Open Scope Z_scope.

Module LXSM2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithU.
  Variable U : uenv.
  Variable G : sym -> Z.
  Variable M0 : word -> option byte.
  Hypothesis UOK : uenv_ok U.
  Hypothesis SCOK : scells_ok U G M0.   (* [comment removed for export] *)
  Let segs := ue_segs U.

  (* [comment removed for export] *)
  Definition lext (rho : valuation) (st : astate) (rho' : valuation) (st' : astate) : Prop :=
    agree (s_next st) rho rho' /\ (s_next st <= s_next st')%nat /\
    s_pc st' = s_pc st /\ s_regs st' = s_regs st /\ s_stk st' = s_stk st /\ s_arrs st' = s_arrs st /\
    s_abs st' = s_abs st /\ s_resv st' = s_resv st /\ s_pay st' = s_pay st /\
    (forall e, In e (s_pcache st) -> In e (s_pcache st')).

  Lemma lext_of_vext : forall rho st rho' st', vext rho st rho' st' -> lext rho st rho' st'.
  Proof.
    intros rho st rho' st' (A & N & P & Rg & S & Ar & Ab & Rv & D & Pc & Py). unfold lext.
    repeat split; auto. intros e He. rewrite Pc. exact He.
  Qed.

  (* [comment removed for export] *)
  Definition load_word (w : Z) (sx : bool) (bs : list byte) : word := ldval w sx bs.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma w64_plus : forall a b, (w64 a + w64 b)%bv = w64 (a + b).
  Proof. intros. apply bv_eq. rewrite bv_add_unsigned, !w64_unsigned, bv_wrap64_mod, <- Z.add_mod by lia. reflexivity. Qed.

  Lemma w64_succ : forall a, (w64 a + 1)%bv = w64 (a + 1).
  Proof.
    intros. apply bv_eq. rewrite bv_add_unsigned, !w64_unsigned, bv_wrap64_mod.
    change (bv_unsigned (1 : word)) with 1. rewrite <- (Z.mod_small 1 (2 ^ 64)) at 1 by lia. rewrite <- Z.add_mod by lia. reflexivity.
  Qed.

  Lemma nat_to_word_w64 : forall k, nat_to_word k = w64 (Z.of_nat k).
  Proof. reflexivity. Qed.

  Lemma rdn_w64_S : forall m a n,
    rdn segs m (w64 a) (S n) =
    match (match m (w64 a) with Some b => Some b | None => seg_rom segs (w64 a) end) with
    | Some b => match rdn segs m (w64 (a + 1)) n with Some r => Some (b :: r) | None => None end
    | None => None
    end.
  Proof. intros. cbn [rdn]. rewrite w64_succ. reflexivity. Qed.

  Lemma rdn_w64_0 : forall m a, rdn segs m (w64 a) 0 = Some [].
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma window_rdn : forall mem sp0 n a,
    window_ok U mem sp0 -> sp0 - ue_fr U <= a -> a + Z.of_nat n <= sp0 ->
    exists bs, rdn segs mem (w64 a) n = Some bs.
  Proof.
    intros mem sp0 n. induction n as [|n IH]; intros a Hwin Hlo Hhi.
    - exists []. apply rdn_w64_0.
    - rewrite rdn_w64_S. destruct (proj1 Hwin a ltac:(lia)) as [b Hb]. rewrite Hb.
      destruct (IH (a + 1) Hwin ltac:(lia) ltac:(lia)) as [bs Hbs]. rewrite Hbs. eexists; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_sub : forall m a n bs i k,
    rdn segs m (w64 a) n = Some bs -> (i + k <= n)%nat ->
    rdn segs m (w64 (a + Z.of_nat i)) k = Some (firstn k (skipn i bs)).
  Proof.
    intros m a n bs i k H Hik.
    pose proof (rdn_skipn segs m n (w64 a) bs i H ltac:(lia)) as H1.
    rewrite nat_to_word_w64, w64_plus in H1.
    exact (rdn_firstn segs m (n - i) _ _ k H1 ltac:(lia)).
  Qed.

  Lemma rd1_rdn : forall mem a b, rd1 U mem a = Some b <-> rdn segs mem (w64 a) 1 = Some [b].
  Proof.
    intros. unfold rd1. fold segs. destruct (rdn segs mem (w64 a) 1) as [[|x [|y r]]|] eqn:E; split; intros H; try discriminate; try (injection H; intros; subst; reflexivity);
      exfalso; pose proof (rdn_length segs mem 1%nat _ _ E); discriminate.
  Qed.

  (* [comment removed for export] *)
  Lemma classify_spec : forall rho av wa n,
    val_ok rho av wa -> aval_below av n = true -> (19 <= n)%nat ->
    match classify av with
    | Some (AStk off) => wa = w64 (rho SYM_SP0 + off)
    | Some (AStkSym off) => wa = w64 (rho SYM_SP0 + evl rho off) /\ lin_below off n = true
    | Some (APay off) => wa = w64 (rho SYM_DATA + evl rho off) /\ lin_below off n = true
    | Some (AAbs a) => wa = w64 a /\ 0 <= a < two64z
    | None => True
    end.
  Proof.
    intros rho av wa n Hv Hb Hn. unfold classify. destruct av as [|l| |]; try exact I. cbn in Hv, Hb.
    destruct (is_const l) as [c|] eqn:K.
    - split; [|rewrite two64z_eq; apply Z.mod_pos_bound; lia].
      rewrite Hv, (is_const_sound rho l c K). apply w64_eq_mod. rewrite two64z_eq, Z.mod_mod by lia. reflexivity.
    - destruct (Z.eqb (lcoef SYM_SP0 l) 1).
      + destruct (Z.eqb (lcoef SYM_DATA (lsub l (lvar SYM_SP0))) 0); [|exact I].
        assert (E : evl rho l = rho SYM_SP0 + evl rho (lsub l (lvar SYM_SP0))) by (rewrite lsub_sound, lvar_sound; lia).
        destruct (is_const (lsub l (lvar SYM_SP0))) as [c|] eqn:K2.
        * rewrite Hv, E, (is_const_sound rho _ c K2). reflexivity.
        * split; [rewrite Hv, E; reflexivity|]. apply lsub_below; [exact Hb | apply lvar_below; unfold SYM_SP0; lia].
      + destruct (Z.eqb (lcoef SYM_DATA l) 1 &&& Z.eqb (lcoef SYM_SP0 l) 0)%bool; [|exact I].
        split; [rewrite Hv, lsub_sound, lvar_sound; f_equal; lia|].
        apply lsub_below; [exact Hb | apply lvar_below; unfold SYM_DATA; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma bytes_le_cons : forall b r, bytes_le_to_Z (b :: r) = bv_unsigned b + 256 * bytes_le_to_Z r.
  Proof.
    intros b r.
    pose proof (bytes_le_firstn 1 (b :: r) ltac:(cbn; lia)) as H1. cbn [firstn] in H1. rewrite bytes_le_single in H1.
    pose proof (bytes_le_skipn 1 (b :: r) ltac:(cbn; lia)) as H2. replace (skipn 1 (b :: r)) with r in H2 by reflexivity.
    change (2 ^ (8 * Z.of_nat 1)) with 256 in H1, H2.
    pose proof (Z.div_mod (bytes_le_to_Z (b :: r)) 256 ltac:(lia)). lia.
  Qed.

  Lemma le_of_bytes_map : forall bs, le_of_bytes (map bv_unsigned bs) = bytes_le_to_Z bs.
  Proof. induction bs as [|b r IH]; [reflexivity|]. cbn [map le_of_bytes]. rewrite bytes_le_cons, IH. reflexivity. Qed.

  Lemma bv_signed_byte : forall b : byte, bv_signed b = (if Z.leb (2 ^ 7) (bv_unsigned b) then bv_unsigned b - 2 ^ 8 else bv_unsigned b).
  Proof.
    intros b. unfold bv_signed, bv_swrap. rewrite bv_wrap8_mod. change (bv_half_modulus 8) with 128.
    pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr. change (2 ^ 7) with 128. change (2 ^ 8) with 256.
    destruct (Z.leb_spec 128 (bv_unsigned b)).
    - replace (bv_unsigned b + 128) with ((bv_unsigned b - 128) + 1 * 256) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia.
    - rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma ldval_1 : forall sx b, ldval 1 sx [b] = w64 (if sx then bv_signed b else bv_unsigned b).
  Proof.
    intros sx b. rewrite (ldval_ext 1 sx [b]) by (cbn; lia). rewrite bytes_le_single. f_equal.
    unfold ext_lit. change (2 ^ (8 * 1)) with 256. change (2 ^ (8 * 1 - 1)) with (2 ^ 7).
    pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
    rewrite Z.mod_small by lia. destruct sx; [|reflexivity]. rewrite bv_signed_byte. change (2 ^ 8) with 256. reflexivity.
  Qed.

  Lemma in_ranges_Z : forall a w rs k, in_ranges a w rs = true -> 0 <= k < w -> in_rangesZ (a + k) rs.
  Proof.
    intros a w rs k H Hk. unfold in_ranges in H. apply existsb_exists in H as (r & Hin & Hr).
    apply andb_prop in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    exists r. split; [exact Hin | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma img_byte_rdn1 : forall mem bm a z,
    abs_ok U mem bm -> in_rangesZ a (ue_ro U) -> img_byte U a = Some z ->
    exists b, (match mem (w64 a) with Some x => Some x | None => seg_rom segs (w64 a) end) = Some b /\ bv_unsigned b = z.
  Proof.
    intros mem bm a z Habs Hro H. unfold img_byte in H. fold segs in H. change (Z_to_bv 64 a) with (w64 a) in H.
    destruct (mem (w64 a)) as [b'|] eqn:Em.
    - pose proof (proj2 (proj2 Habs) a b' Hro Em) as Hmr. fold segs in Hmr. rewrite Hmr in H. injection H; intros <-. exists b'. split; reflexivity.
    - unfold seg_rom. destruct (memory_read segs (w64 a) 1) as [[|b r]|]; try discriminate. injection H; intros <-. exists b. split; reflexivity.
  Qed.

  Lemma img_bytes_rdn : forall mem bm n a zs,
    abs_ok U mem bm -> (forall k, 0 <= k < Z.of_nat n -> in_rangesZ (a + k) (ue_ro U)) ->
    img_bytes U a n = Some zs ->
    exists bs, rdn segs mem (w64 a) n = Some bs /\ map bv_unsigned bs = zs.
  Proof.
    intros mem bm n. induction n as [|n IH]; intros a zs Habs Hro H.
    - cbn in H. injection H; intros <-. exists []. split; [apply rdn_w64_0 | reflexivity].
    - cbn [img_bytes] in H. destruct (img_byte U a) as [z|] eqn:Ez; [|discriminate].
      destruct (img_bytes U (a + 1) n) as [zr|] eqn:Er; [|discriminate]. injection H; intros <-.
      destruct (img_byte_rdn1 mem bm a z Habs ltac:(replace a with (a + 0) by lia; apply Hro; lia) Ez) as (b & Hb & Hbz).
      destruct (IH (a + 1) zr Habs ltac:(intros k Hk; replace (a + 1 + k) with (a + (1 + k)) by lia; apply Hro; lia) Er) as (bs & Hbs & Hm).
      exists (b :: bs). rewrite rdn_w64_S, Hb, Hbs. split; [reflexivity|]. cbn [map]. rewrite Hbz, Hm. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma abs_bytes_rdn : forall mem bm n a zs,
    abs_ok U mem bm -> (forall k, 0 <= k < Z.of_nat n -> in_rangesZ (a + k) (ue_rw U)) ->
    abs_bytes U bm a n = Some zs ->
    exists bs, rdn segs mem (w64 a) n = Some bs /\ map bv_unsigned bs = zs.
  Proof.
    intros mem bm n. induction n as [|n IH]; intros a zs Habs Hrw H.
    - cbn in H. injection H; intros <-. exists []. split; [apply rdn_w64_0 | reflexivity].
    - cbn [abs_bytes] in H.
      assert (Ha : in_rangesZ a (ue_rw U)) by (replace a with (a + 0) by lia; apply Hrw; lia).
      destruct (abs_bytes U bm (a + 1) n) as [zr|] eqn:Er.
      2: { destruct (bm_get bm a); [discriminate|]. destruct (img_byte U a); discriminate. }
      destruct (IH (a + 1) zr Habs ltac:(intros k Hk; replace (a + 1 + k) with (a + (1 + k)) by lia; apply Hrw; lia) Er) as (bs & Hbs & Hm).
      destruct (bm_get bm a) as [z|] eqn:Eg.
      + injection H; intros <-. destruct (proj1 Habs a z Eg) as (_ & Hz & Hmem).
        exists (Z_to_bv 8 z :: bs). rewrite rdn_w64_S, Hmem, Hbs. split; [reflexivity|]. cbn [map]. rewrite Hm, Z_to_bv_unsigned, bv_wrap8_mod, Z.mod_small by lia. reflexivity.
      + destruct (img_byte U a) as [z|] eqn:Ez; [|discriminate]. injection H; intros <-.
        pose proof (proj1 (proj2 Habs) a Ha Eg) as Hnone.
        unfold img_byte in Ez. fold segs in Ez. change (Z_to_bv 64 a) with (w64 a) in Ez.
        destruct (memory_read segs (w64 a) 1) as [[|b r]|] eqn:Emr; try discriminate. injection Ez; intros <-.
        exists (b :: bs). rewrite rdn_w64_S, Hnone. unfold seg_rom. rewrite Emr, Hbs. split; [reflexivity|]. cbn [map]. rewrite Hm. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rows_ok_sound : forall t f n i0 i,
    rows_ok U t f i0 n = true -> i0 <= i < i0 + Z.of_nat n ->
    exists v, field_val U (tb_base t + tb_stride t * i + tf_off f) (tf_w f) (tf_sx f) = Some v /\
      match tf_kind f with TFresh => True | THull lo hi => lo <= v <= hi | TAffine c0 c1 => v = c0 + c1 * i end.
  Proof.
    intros t f n. induction n as [|n IH]; intros i0 i H Hi; [lia|].
    cbn [rows_ok] in H. apply andb_prop in H as [H1 H2].
    destruct (Z.eq_dec i i0) as [->|Hne].
    - destruct (field_val U (tb_base t + tb_stride t * i0 + tf_off f) (tf_w f) (tf_sx f)) as [v|]; [|destruct (tf_kind f); discriminate].
      exists v. split; [reflexivity|]. destruct (tf_kind f); [exact I| |].
      + apply andb_prop in H1 as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
      + apply Z.eqb_eq in H1. exact H1.
    - apply (IH (i0 + 1) i H2). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma R_pcache_cons : forall rho st ms off sxz x b,
    R U G M0 rho st ms ->
    0 <= evl rho off < rho SYM_N ->
    rd1 U (ms_mem ms) (rho SYM_DATA + evl rho off) = Some b ->
    rho x = (if Z.eqb sxz 1 then bv_signed b else bv_unsigned b) ->
    R U G M0 rho (set_pcache st ((off, sxz, x) :: s_pcache st)) ms.
  Proof.
    intros rho st ms off sxz x b HR Hoff Hb Hx.
    destruct HR as [Rglob Rpc Rsvc Rregs Rvs Rstk Rarrs Rwin Rpay Rabs Rresv Rfrm Rframe Rsp0 Ralign Rra Rdata].
    constructor; cbn; try assumption.
    destruct Rpay as (P1 & P2 & P3 & P4). split; [exact P1|]. split; [exact P2|]. split; [|exact P4].
    intros off' sx' x' [E|Hin]; [|apply P3; exact Hin].
    injection E; intros <- <- <-. split; [exact Hoff|]. exists b. split; [exact Hb | exact Hx].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma VOK_R : forall rho st ms p rho' wv,
    wf_state st = true -> R U G M0 rho st ms -> VOK rho st p rho' wv ->
    R U G M0 rho' (snd p) ms /\ lext rho st rho' (snd p) /\ val_ok rho' (fst p) wv /\ aval_below (fst p) (s_next (snd p)) = true.
  Proof.
    intros rho st ms p rho' wv Hwf HR (He & HVS & Hv & Hb).
    split; [eapply R_vext; eauto|]. split; [apply lext_of_vext; exact He|]. split; [exact Hv | exact Hb].
  Qed.

  Lemma R_to_VS : forall rho st ms, R U G M0 rho st ms -> VS rho st.
  Proof. intros rho st ms HR. exact (r_vs _ _ _ _ _ _ HR). Qed.

  Lemma fresh_unk_VOK : forall rho st bs w sx,
    VS rho st -> 0 < w -> w <= 8 -> Z.of_nat (length bs) = w ->
    exists rho', VOK rho st (fresh_val st (unk_itv sx w)) rho' (ldval w sx bs).
  Proof.
    intros rho st bs w sx HVS Hw Hw8 Hl.
    eapply VOK_fresh; [exact HVS | apply unk_itv_sound; lia | apply ldval_ext; lia].
  Qed.

  Lemma cells_find_cover_spec : forall cs off w c,
    cells_find_cover cs off w = Some c -> In c cs /\ c_off c <= off /\ off + w <= c_off c + c_w c.
  Proof.
    induction cs as [|d r IH]; cbn; intros off w c H; [discriminate|].
    destruct (Z.leb (c_off d) off) eqn:E1; [destruct (Z.leb (off + w) (c_off d + c_w d)) eqn:E2|].
    - injection H; intros <-. apply Z.leb_le in E1. apply Z.leb_le in E2. split; [left; reflexivity | lia].
    - destruct (IH _ _ _ H) as [A B]. split; [right; exact A | exact B].
    - destruct (IH _ _ _ H) as [A B]. split; [right; exact A | exact B].
  Qed.

  Lemma arr_find_spec : forall rho ars C off w a,
    ctx_ok rho C -> arr_find ars C off w = Some a ->
    In a ars /\ ar_lo a <= evl rho off /\ evl rho off + w <= ar_hi a.
  Proof.
    intros rho ars C off w a HC H. unfold arr_find in H. apply find_some in H as [Hin Hb].
    apply andb_prop in Hb as [H1 H2].
    pose proof (entails_sound rho C _ None HC H1) as E1. pose proof (entails_sound rho C _ None HC H2) as E2.
    rewrite laddc_sound in E1. rewrite laddc_sound, lneg_sound in E2. split; [exact Hin | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma arr_fact_byte : forall rho mem sp0 a f j,
    arr_ok U rho mem sp0 a -> ar_fact a = Some f -> 0 <= j < evl rho (af_len f) ->
    exists b, rdn segs mem (w64 (sp0 + ar_lo a + j)) 1 = Some [b] /\
              0 <= af_blo f /\ af_blo f <= bv_unsigned b <= af_bhi f /\ af_bhi f <= 127 /\ bv_signed b = bv_unsigned b.
  Proof.
    intros rho mem sp0 a f j (_ & _ & Hf) Ef Hj. rewrite Ef in Hf. destruct Hf as (Hblo & Hbhi & Haf & _).
    destruct (Haf j Hj) as (_ & b & Hrd & Hb). exists b. apply rd1_rdn in Hrd.
    split; [exact Hrd|]. split; [exact Hblo|]. split; [exact Hb|]. split; [exact Hbhi|].
    rewrite bv_signed_byte. destruct (Z.leb_spec (2 ^ 7) (bv_unsigned b)); [change (2 ^ 7) with 128 in *; lia | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma arr_fact_first : forall rho mem sp0 a f,
    arr_ok U rho mem sp0 a -> ar_fact a = Some f -> 1 <= evl rho (af_len f) ->
    exists b, rdn segs mem (w64 (sp0 + ar_lo a)) 1 = Some [b] /\ in_itv (bv_unsigned b) (af_first f).
  Proof.
    intros rho mem sp0 a f (_ & _ & Hf) Ef H1. rewrite Ef in Hf. destruct Hf as (_ & _ & _ & Hfirst).
    destruct (Hfirst H1) as (b & Hrd & Hi). exists b. apply rd1_rdn in Hrd. split; [exact Hrd | exact Hi].
  Qed.

  Lemma lin_eq_ent_sound : forall rho C a b, ctx_ok rho C -> lin_eq_ent C a b = true -> evl rho a = evl rho b.
  Proof.
    intros rho C a b HC H. unfold lin_eq_ent in H. destruct (leqb a b) eqn:E1; [apply leqb_eval; exact E1|].
    apply andb_prop in H as [A B]. pose proof (entails_sound rho C _ None HC A). pose proof (entails_sound rho C _ None HC B).
    rewrite lsub_sound in H, H0. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fact_byte_VOK : forall rho st (sx is_first : bool) (b : byte) f,
    VS rho st -> 0 <= af_blo f -> af_blo f <= bv_unsigned b <= af_bhi f -> af_bhi f <= 127 -> bv_signed b = bv_unsigned b ->
    (is_first = true -> in_itv (bv_unsigned b) (af_first f)) ->
    exists rho', VOK rho st (fresh_val st (fact_itv f is_first)) rho' (ldval 1 sx [b]).
  Proof.
    intros rho st sx is_first b f HVS H0 Hb H127 Hs Hfirst.
    eapply (VOK_fresh rho st _ (bv_unsigned b)); [exact HVS | | rewrite ldval_1; destruct sx; [rewrite Hs|]; reflexivity].
    unfold fact_itv. destruct is_first.
    - apply imeet_sound; [apply Hfirst; reflexivity|]. unfold in_itv; cbn [ilo ihi]. lia.
    - unfold in_itv; cbn [ilo ihi]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma load_stack_lit_sound : forall rho st ms off w sx v st',
    wf_state st = true -> R U G M0 rho st ms -> 0 < w -> w <= 8 ->
    load_stack_lit U st off w sx = Some (v, st') ->
    exists rho' bs,
      rdn segs (ms_mem ms) (w64 (rho SYM_SP0 + off)) (Z.to_nat w) = Some bs
      /\ R U G M0 rho' st' ms /\ lext rho st rho' st' /\ val_ok rho' v (ldval w sx bs) /\ aval_below v (s_next st') = true.
  Proof.
    intros rho st ms off w sx v st' Hwf HR Hw Hw8 H.
    pose proof (wf_parts st Hwf) as (Wregs & Wctx & Wstk & Warrs & Wpc & Wpay & Wdisj & W18 & Wcw & Wad).
    pose proof (R_to_VS _ _ _ HR) as HVS.
    unfold load_stack_lit in H. destruct (in_window U off w) eqn:Win; cbn [negb] in H; [|discriminate].
    unfold in_window in Win. apply andb_prop in Win as [Win1 Win2]. apply Z.leb_le in Win1. apply Z.leb_le in Win2.
    (* [comment removed for export] *)
    destruct (window_rdn (ms_mem ms) (rho SYM_SP0) (Z.to_nat w) (rho SYM_SP0 + off) (r_win _ _ _ _ _ _ HR) ltac:(lia) ltac:(lia)) as [bs0 Hbs0].
    pose proof (rdn_length segs _ _ _ _ Hbs0) as Hlen0.
    assert (GEN : forall p, (exists rho', VOK rho st p rho' (ldval w sx bs0)) -> Some p = Some (v, st') ->
              exists rho' bs, rdn segs (ms_mem ms) (w64 (rho SYM_SP0 + off)) (Z.to_nat w) = Some bs /\ R U G M0 rho' st' ms /\ lext rho st rho' st'
                              /\ val_ok rho' v (ldval w sx bs) /\ aval_below v (s_next st') = true).
    { intros p [rho' HV] E. injection E; intros ->. exists rho', bs0. split; [exact Hbs0|]. exact (VOK_R rho st ms (v, st') rho' _ Hwf HR HV). }
    assert (UNK : Some (fresh_val st (unk_itv sx w)) = Some (v, st') ->
              exists rho' bs, rdn segs (ms_mem ms) (w64 (rho SYM_SP0 + off)) (Z.to_nat w) = Some bs /\ R U G M0 rho' st' ms /\ lext rho st rho' st'
                              /\ val_ok rho' v (ldval w sx bs) /\ aval_below v (s_next st') = true).
    { apply GEN. apply fresh_unk_VOK; [exact HVS | lia | lia | lia]. }
    unfold load_cells in H.
    destruct (cells_find_cover (s_stk st) off w) as [c|] eqn:Ecov.
    - (* [comment removed for export] *)
      destruct (cells_find_cover_spec _ _ _ _ Ecov) as (Hin & Hc1 & Hc2).
      pose proof (proj1 (Forall_forall _ _) (r_stk _ _ _ _ _ _ HR) c Hin) as (B1 & B2 & B3 & cbs & Hcbs & Hvb).
      rewrite forallb_forall in Wstk, Wcw. pose proof (Wstk c Hin) as Wc. pose proof (Wcw c Hin) as Wc8. cbn in Wc.
      apply andb_prop in Wc8 as [_ Wc8]. apply Z.leb_le in Wc8.
      destruct (load_from_cell_sound rho st (c_val c) (c_w c) (off - c_off c) w sx cbs HVS Wc Hvb ltac:(lia) Hw ltac:(lia) Wc8) as [rho' HV].
      injection H; intros E. rewrite E in HV.
      exists rho', (firstn (Z.to_nat w) (skipn (Z.to_nat (off - c_off c)) cbs)). split.
      + pose proof (rdn_sub (ms_mem ms) (rho SYM_SP0 + c_off c) (Z.to_nat (c_w c)) cbs (Z.to_nat (off - c_off c)) (Z.to_nat w) Hcbs ltac:(lia)) as Hr.
        replace (rho SYM_SP0 + c_off c + Z.of_nat (Z.to_nat (off - c_off c))) with (rho SYM_SP0 + off) in Hr by lia. exact Hr.
      + exact (VOK_R rho st ms (v, st') rho' _ Hwf HR HV).
    - destruct (cells_any_overlap (s_stk st) off w); [apply UNK; exact H|].
      destruct (arr_find (s_arrs st) (s_ctx st) (lconst off) w) as [a|] eqn:Efind; [|apply UNK; exact H].
      destruct (arr_find_spec rho _ _ _ _ _ (proj1 HVS) Efind) as (Hina & Hlo & Hhi). rewrite lconst_sound in Hlo, Hhi.
      destruct (ar_fact a) as [f|] eqn:Ef; [|apply UNK; exact H].
      destruct (Z.eqb w 1) eqn:Ew1; [|apply UNK; exact H]. apply Z.eqb_eq in Ew1.
      destruct (entails (s_ctx st) (laddc (lsub (af_len f) (lconst off)) (ar_lo a - 1)) None) eqn:Een; [|apply UNK; exact H].
      pose proof (entails_sound rho _ _ None (proj1 HVS) Een) as Hen. rewrite laddc_sound, lsub_sound, lconst_sound in Hen.
      pose proof (proj1 (Forall_forall _ _) (r_arrs _ _ _ _ _ _ HR) a Hina) as Harr.
      destruct (arr_fact_byte rho (ms_mem ms) (rho SYM_SP0) a f (off - ar_lo a) Harr Ef ltac:(lia)) as (b & Hrd & Hblo & Hb & Hbhi & Hsb).
      replace (rho SYM_SP0 + ar_lo a + (off - ar_lo a)) with (rho SYM_SP0 + off) in Hrd by lia.
      subst w. change (Z.to_nat 1) with 1%nat in Hbs0. rewrite Hrd in Hbs0. injection Hbs0; intros <-.
      refine (GEN _ _ H). apply fact_byte_VOK; try assumption.
      intros Efirst. apply Z.eqb_eq in Efirst. subst off.
      destruct (arr_fact_first rho (ms_mem ms) (rho SYM_SP0) a f Harr Ef ltac:(lia)) as (b' & Hrd' & Hi').
      rewrite Hrd in Hrd'. injection Hrd'; intros <-. exact Hi'.
  Qed.

  (* [comment removed for export] *)
  Lemma load_stack_sym_sound : forall rho st ms off w sx v st',
    wf_state st = true -> R U G M0 rho st ms -> 0 < w -> w <= 8 ->
    load_stack_sym U st off w sx = Some (v, st') ->
    exists rho' bs,
      rdn segs (ms_mem ms) (w64 (rho SYM_SP0 + evl rho off)) (Z.to_nat w) = Some bs
      /\ R U G M0 rho' st' ms /\ lext rho st rho' st' /\ val_ok rho' v (ldval w sx bs) /\ aval_below v (s_next st') = true.
  Proof.
    intros rho st ms off w sx v st' Hwf HR Hw Hw8 H.
    pose proof (R_to_VS _ _ _ HR) as HVS.
    unfold load_stack_sym in H.
    destruct (arr_find (s_arrs st) (s_ctx st) off w) as [a|] eqn:Efind; [|discriminate].
    destruct (arr_find_spec rho _ _ _ _ _ (proj1 HVS) Efind) as (Hina & Hlo & Hhi).
    destruct (in_window U (ar_lo a) (ar_hi a - ar_lo a)) eqn:Win; cbn [negb] in H; [|discriminate].
    unfold in_window in Win. apply andb_prop in Win as [Win1 Win2]. apply Z.leb_le in Win1. apply Z.leb_le in Win2.
    destruct (window_rdn (ms_mem ms) (rho SYM_SP0) (Z.to_nat w) (rho SYM_SP0 + evl rho off) (r_win _ _ _ _ _ _ HR) ltac:(lia) ltac:(lia)) as [bs0 Hbs0].
    pose proof (rdn_length segs _ _ _ _ Hbs0) as Hlen0.
    assert (GEN : forall p, (exists rho', VOK rho st p rho' (ldval w sx bs0)) -> Some p = Some (v, st') ->
              exists rho' bs, rdn segs (ms_mem ms) (w64 (rho SYM_SP0 + evl rho off)) (Z.to_nat w) = Some bs /\ R U G M0 rho' st' ms /\ lext rho st rho' st'
                              /\ val_ok rho' v (ldval w sx bs) /\ aval_below v (s_next st') = true).
    { intros p [rho' HV] E. injection E; intros ->. exists rho', bs0. split; [exact Hbs0|]. exact (VOK_R rho st ms (v, st') rho' _ Hwf HR HV). }
    assert (UNK : Some (fresh_val st (unk_itv sx w)) = Some (v, st') ->
              exists rho' bs, rdn segs (ms_mem ms) (w64 (rho SYM_SP0 + evl rho off)) (Z.to_nat w) = Some bs /\ R U G M0 rho' st' ms /\ lext rho st rho' st'
                              /\ val_ok rho' v (ldval w sx bs) /\ aval_below v (s_next st') = true).
    { apply GEN. apply fresh_unk_VOK; [exact HVS | lia | lia | lia]. }
    destruct (ar_fact a) as [f|] eqn:Ef; [|apply UNK; exact H].
    destruct (Z.eqb w 1) eqn:Ew1; [|apply UNK; exact H]. apply Z.eqb_eq in Ew1.
    destruct (entails (s_ctx st) (laddc (lsub (af_len f) off) (ar_lo a - 1)) None) eqn:Een; [|apply UNK; exact H].
    pose proof (entails_sound rho _ _ None (proj1 HVS) Een) as Hen. rewrite laddc_sound, lsub_sound in Hen.
    pose proof (proj1 (Forall_forall _ _) (r_arrs _ _ _ _ _ _ HR) a Hina) as Harr.
    destruct (arr_fact_byte rho (ms_mem ms) (rho SYM_SP0) a f (evl rho off - ar_lo a) Harr Ef ltac:(lia)) as (b & Hrd & Hblo & Hb & Hbhi & Hsb).
    replace (rho SYM_SP0 + ar_lo a + (evl rho off - ar_lo a)) with (rho SYM_SP0 + evl rho off) in Hrd by lia.
    subst w. change (Z.to_nat 1) with 1%nat in Hbs0. rewrite Hrd in Hbs0. injection Hbs0; intros <-.
    refine (GEN _ _ H). apply fact_byte_VOK; try assumption.
    intros Efirst. pose proof (lin_eq_ent_sound rho _ _ _ (proj1 HVS) Efirst) as Eo. rewrite lconst_sound in Eo.
    destruct (arr_fact_first rho (ms_mem ms) (rho SYM_SP0) a f Harr Ef ltac:(lia)) as (b' & Hrd' & Hi').
    rewrite <- Eo, Hrd in Hrd'. injection Hrd'; intros <-. exact Hi'.
  Qed.

  (* [comment removed for export] *)
  Lemma pcache_find_spec : forall pc off sxz x,
    pcache_find pc off sxz = Some x -> exists o, In (o, sxz, x) pc /\ leqb o off = true.
  Proof.
    induction pc as [|[[o s] y] r IH]; cbn; intros off sxz x H; [discriminate|].
    destruct (leqb o off) eqn:E1.
    - destruct (Z.eqb s sxz) eqn:E2.
      + injection H; intros <-. apply Z.eqb_eq in E2. subst. exists o. split; [left; reflexivity | exact E1].
      + destruct (IH _ _ _ H) as (o' & A & B). exists o'. split; [right; exact A | exact B].
    - destruct (IH _ _ _ H) as (o' & A & B). exists o'. split; [right; exact A | exact B].
  Qed.

  Lemma pay_find_spec : forall rho C ps off i,
    ctx_ok rho C -> pay_find C ps off = Some i -> exists o, In (o, i) ps /\ evl rho o = evl rho off.
  Proof.
    intros rho C ps off i HC. induction ps as [|[o j] r IH]; cbn; intros H; [discriminate|].
    destruct (lin_eq_ent C o off) eqn:E.
    - injection H; intros <-. exists o. split; [left; reflexivity|].
      unfold lin_eq_ent in E. destruct (leqb o off) eqn:E1; [apply leqb_eval; exact E1|].
      apply andb_prop in E as [A B]. pose proof (entails_sound rho C _ None HC A). pose proof (entails_sound rho C _ None HC B).
      rewrite lsub_sound in H0, H1. lia.
    - destruct (IH H) as (o' & A & B). exists o'. split; [right; exact A | exact B].
  Qed.

  Lemma load_pay_sound : forall rho st ms off sx v st',
    wf_state st = true -> R U G M0 rho st ms -> lin_below off (s_next st) = true ->
    load_pay U st off 1 sx = LPOk v st' ->
    exists rho' bs,
      rdn segs (ms_mem ms) (w64 (rho SYM_DATA + evl rho off)) 1 = Some bs
      /\ R U G M0 rho' st' ms /\ lext rho st rho' st' /\ val_ok rho' v (ldval 1 sx bs) /\ aval_below v (s_next st') = true.
  Proof.
    intros rho st ms off sx v st' Hwf HR Hoffb H.
    pose proof (wf_parts st Hwf) as (Wregs & Wctx & Wstk & Warrs & Wpc & Wpay & Wdisj & W18 & Wcw & Wad).
    pose proof (R_to_VS _ _ _ HR) as HVS.
    unfold load_pay in H. cbn [Z.eqb Pos.eqb negb] in H.
    destruct (entails (s_ctx st) off None) eqn:E1; [|discriminate].
    destruct (entails (s_ctx st) (laddc (lsub (lvar SYM_N) off) (-1)) None) eqn:E2; [|discriminate]. cbn [negb] in H.
    pose proof (entails_sound rho _ _ None (proj1 HVS) E1) as Hoff1.
    pose proof (entails_sound rho _ _ None (proj1 HVS) E2) as Hoff2. rewrite laddc_sound, lsub_sound, lvar_sound in Hoff2.
    destruct (r_pay _ _ _ _ _ _ HR) as (P1 & P2 & P3 & P4).
    destruct (P1 (evl rho off) ltac:(lia)) as [b Hb]. pose proof (proj1 (rd1_rdn _ _ _) Hb) as Hrd.
    set (sxz := if sx then 1 else 0) in H.
    assert (Hsxz : Z.eqb sxz 1 = sx) by (destruct sx; reflexivity).
    destruct (pcache_find (s_pcache st) off sxz) as [x|] eqn:Epc.
    - (* [comment removed for export] *)
      injection H; intros <- <-. destruct (pcache_find_spec _ _ _ _ Epc) as (o & Hin & Heq).
      destruct (P3 o sxz x Hin) as (_ & b' & Hb' & Hx). rewrite (leqb_eval rho o off Heq) in Hb'. rewrite Hb in Hb'. injection Hb'; intros <-.
      exists rho, [b]. split; [exact Hrd|]. split; [exact HR|]. split; [apply lext_of_vext; apply vext_refl|]. split.
      + unfold val_ok. rewrite ldval_1, lvar_sound, Hx, Hsxz. reflexivity.
      + rewrite forallb_forall in Wpc. specialize (Wpc _ Hin). cbn in Wpc. apply andb_prop in Wpc as [_ Wx]. apply Nat.ltb_lt in Wx.
        cbn. apply lvar_below. exact Wx.
    - set (bv := if sx then bv_signed b else bv_unsigned b).
      assert (NEW : forall i st1, in_itv bv i -> fresh st i = (s_next st, st1) ->
                LPOk (LV (lvar (s_next st))) (set_pcache st1 ((off, sxz, s_next st) :: s_pcache st1)) = LPOk v st' ->
                exists rho' bs, rdn segs (ms_mem ms) (w64 (rho SYM_DATA + evl rho off)) 1 = Some bs /\ R U G M0 rho' st' ms /\ lext rho st rho' st'
                                /\ val_ok rho' v (ldval 1 sx bs) /\ aval_below v (s_next st') = true).
      { intros i st1 Hi Ef E. injection E; intros <- <-.
        destruct (fresh_sound rho st i bv HVS Hi) as (rho' & Hx & Hext & HVS1 & _ & Hn1). rewrite Ef in Hext, HVS1, Hn1. cbn [snd] in Hext, HVS1, Hn1.
        pose proof (R_vext U G M0 rho st ms rho' st1 Hwf HR Hext HVS1) as HR1.
        destruct Hext as (Hag & Hle & Epc' & Eregs & Estk & Earrs & Eabs & Eresv & Edepth & Epcache & Epay).
        assert (Eoff : evl rho' off = evl rho off) by (eapply evl_agree; [exact Hoffb | exact Hag]).
        assert (ED : rho' SYM_DATA = rho SYM_DATA) by (apply Hag; unfold SYM_DATA; lia).
        assert (EN : rho' SYM_N = rho SYM_N) by (apply Hag; unfold SYM_N; lia).
        exists rho', [b]. split; [exact Hrd|]. split; [|split; [|split]].
        - apply (R_pcache_cons rho' st1 ms off sxz (s_next st) b HR1); rewrite ?Eoff, ?ED, ?EN; [lia | exact Hb |].
          rewrite Hx, Hsxz. reflexivity.
        - unfold lext; cbn. rewrite Epcache. repeat split; auto. all: intros e He; right; exact He.
        - unfold val_ok. rewrite ldval_1, lvar_sound, Hx. reflexivity.
        - cbn -[lin_below]. rewrite Hn1. apply lvar_below. lia. }
      destruct (pay_find (s_ctx st) (s_pay st) off) as [i|] eqn:Epf.
      + destruct (fresh st (itv_meet_byte sx i)) as [x st1] eqn:Ef.
        assert (Hxe : x = s_next st) by (unfold fresh in Ef; injection Ef; intros _ <-; reflexivity). subst x.
        eapply (NEW (itv_meet_byte sx i) st1); [|exact Ef|exact H].
        destruct (pay_find_spec rho _ _ _ _ (proj1 HVS) Epf) as (o & Hin & Heq).
        destruct (P4 o i Hin) as (_ & b' & Hb' & Hbi). rewrite Heq, Hb in Hb'. injection Hb'; intros <-.
        unfold itv_meet_byte. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
        destruct sx; unfold bv.
        * destruct (ilo i) as [lo|] eqn:Elo; [destruct (ihi i) as [hi|] eqn:Ehi|].
          -- destruct (Z.leb 0 lo &&& Z.leb hi 127)%bool eqn:Ec.
             ++ apply andb_prop in Ec as [A B]. apply Z.leb_le in A. apply Z.leb_le in B.
                destruct Hbi as [L1 L2]. rewrite Elo in L1. rewrite Ehi in L2.
                rewrite bv_signed_byte. change (2 ^ 7) with 128. destruct (Z.leb_spec 128 (bv_unsigned b)); [lia|].
                unfold in_itv. rewrite Elo, Ehi. lia.
             ++ unfold in_itv; cbn [ilo ihi]. rewrite bv_signed_byte. change (2 ^ 7) with 128. change (2 ^ 8) with 256. destruct (Z.leb_spec 128 (bv_unsigned b)); lia.
          -- unfold in_itv; cbn [ilo ihi]. rewrite bv_signed_byte. change (2 ^ 7) with 128. change (2 ^ 8) with 256. destruct (Z.leb_spec 128 (bv_unsigned b)); lia.
          -- unfold in_itv; cbn [ilo ihi]. rewrite bv_signed_byte. change (2 ^ 7) with 128. change (2 ^ 8) with 256. destruct (Z.leb_spec 128 (bv_unsigned b)); lia.
        * apply imeet_sound; [exact Hbi|]. unfold in_itv; cbn [ilo ihi]. lia.
      + destruct (pay_split (s_ctx st) (s_pay st) off) as [p|]; [discriminate|].
        destruct (fresh st (if sx then Itv (Some (-128)) (Some 127) else Itv (Some 0) (Some 255))) as [x st1] eqn:Ef.
        assert (Hxe : x = s_next st) by (unfold fresh in Ef; injection Ef; intros _ <-; reflexivity). subst x.
        eapply (NEW _ st1); [|exact Ef|exact H].
        pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
        destruct sx; unfold bv, in_itv; cbn [ilo ihi]; [|lia].
        rewrite bv_signed_byte. change (2 ^ 7) with 128. change (2 ^ 8) with 256. destruct (Z.leb_spec 128 (bv_unsigned b)); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lit_result : forall rho st ms bs w sx (a : Z),
    R U G M0 rho st ms -> 0 < w -> w <= 8 -> length bs = Z.to_nat w ->
    rdn segs (ms_mem ms) (w64 a) (Z.to_nat w) = Some bs ->
    exists rho' bs', rdn segs (ms_mem ms) (w64 a) (Z.to_nat w) = Some bs' /\ R U G M0 rho' st ms /\ lext rho st rho' st
                     /\ val_ok rho' (alit (ext_lit sx w (le_of_bytes (map bv_unsigned bs)))) (ldval w sx bs') /\ aval_below (alit (ext_lit sx w (le_of_bytes (map bv_unsigned bs)))) (s_next st) = true.
  Proof.
    intros rho st ms bs w sx a HR Hw Hw8 Hlen Hrd. exists rho, bs. split; [exact Hrd|]. split; [exact HR|].
    split; [apply lext_of_vext; apply vext_refl|]. split; [|apply alit_below].
    apply alit_ok'. rewrite le_of_bytes_map. apply ldval_ext; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma scell_find_In : forall cs a x, scell_find cs a = Some x -> In (a, x) cs.
  Proof.
    induction cs as [|[b y] r IH]; intros a x H; cbn in H; [discriminate|].
    destruct (Z.eqb_spec a b) as [->|NE]; [injection H; intros <-; left; reflexivity | right; apply IH; exact H].
  Qed.

  Lemma rdn_ext_w64 : forall (m m' : word -> option byte) n a,
    (forall k, (k < n)%nat -> m (w64 (a + Z.of_nat k)) = m' (w64 (a + Z.of_nat k))) ->
    rdn segs m (w64 a) n = rdn segs m' (w64 a) n.
  Proof.
    intros m m' n. induction n as [|n IH]; intros a H; [reflexivity|].
    rewrite !rdn_w64_S. pose proof (H 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0. rewrite H0.
    rewrite (IH (a + 1)); [reflexivity|].
    intros k Hk. replace (a + 1 + Z.of_nat k) with (a + Z.of_nat (S k)) by lia. apply H. lia.
  Qed.

  Lemma scell_rdn : forall rho st ms a x,
    R U G M0 rho st ms -> In (a, x) (ue_scells U) ->
    exists bs, rdn segs (ms_mem ms) (w64 a) 8 = Some bs /\ Z.of_nat (length bs) = 8 /\ (bytes_le_to_Z bs) mod 2 ^ 64 = (rho x) mod 2 ^ 64.
  Proof.
    intros rho st ms a x HR Hin.
    destruct (uo_scells U UOK a x Hin) as (Ex & Ha0 & Ha8 & Hnrw).
    destruct (SCOK a x Hin) as (bs & Hrd0 & Hval). exists bs.
    assert (Hrd : rdn segs (ms_mem ms) (w64 a) 8 = Some bs).
    { rewrite <- Hrd0. apply rdn_ext_w64. intros k Hk.
      destruct (r_frame _ _ _ _ _ _ HR) as [F1 _]. pose proof (r_sp0 _ _ _ _ _ _ HR) as SP. apply F1.
      - rewrite w64_unsigned, Z.mod_small by lia. lia.
      - rewrite w64_unsigned, Z.mod_small by lia. apply Hnrw. lia. }
    split; [exact Hrd|]. split; [rewrite (rdn_length segs _ _ _ _ Hrd); reflexivity|].
    rewrite Hval, <- (r_glob _ _ _ _ _ _ HR x) by (rewrite Ex; unfold SYM_SC0, NGLOB; lia). reflexivity.
  Qed.

  Lemma load_abs_sound : forall rho st ms a w sx v st',
    wf_state st = true -> R U G M0 rho st ms -> 0 < w -> w <= 8 ->
    load_abs U st a w sx = Some (v, st') ->
    exists rho' bs,
      rdn segs (ms_mem ms) (w64 a) (Z.to_nat w) = Some bs
      /\ R U G M0 rho' st' ms /\ lext rho st rho' st' /\ val_ok rho' v (ldval w sx bs) /\ aval_below v (s_next st') = true.
  Proof.
    intros rho st ms a w sx v st' Hwf HR Hw Hw8 H. unfold load_abs in H.
    destruct (scell_find (ue_scells U) a) as [x|] eqn:Esc.
    { (* [comment removed for export] *)
      destruct (Z.eqb w 8 &&& Nat.ltb x (s_next st))%bool eqn:Eb; [|discriminate]. injection H; intros <- <-.
      apply andb_prop in Eb as [Ew Ex]. apply Z.eqb_eq in Ew. apply Nat.ltb_lt in Ex. subst w.
      destruct (scell_rdn rho st ms a x HR (scell_find_In _ _ _ Esc)) as (bs & Hrd & Hlen & Hval).
      exists rho, bs. split; [exact Hrd|]. split; [exact HR|]. split; [apply lext_of_vext; apply vext_refl|]. split.
      - unfold val_ok. rewrite lvar_sound. change (Z.to_nat 8) with 8%nat. rewrite (ldval_8 sx bs Hlen).
        apply w64_eq_mod. rewrite ext_lit8_mod. exact Hval.
      - cbn -[Nat.ltb]. apply lvar_below. exact Ex. }
    destruct (in_ranges a w (ue_rw U)) eqn:Erw.
    - destruct (abs_bytes U (s_abs st) a (Z.to_nat w)) as [zs|] eqn:Eab; [|discriminate]. injection H; intros <- <-.
      destruct (abs_bytes_rdn (ms_mem ms) (s_abs st) (Z.to_nat w) a zs (r_abs _ _ _ _ _ _ HR)
                  ltac:(intros k Hk; eapply in_ranges_Z; [exact Erw | lia]) Eab) as (bs & Hrd & Hmap).
      rewrite <- Hmap. eapply lit_result; eauto. rewrite <- (length_map bv_unsigned), Hmap.
      clear -Eab. revert a zs Eab. induction (Z.to_nat w) as [|n IH]; cbn [abs_bytes]; intros a zs E.
      + injection E; intros <-; reflexivity.
      + destruct (match bm_get (s_abs st) a with Some b => Some b | None => img_byte U a end); [|discriminate].
        destruct (abs_bytes U (s_abs st) (a + 1) n) eqn:E2; [|discriminate]. injection E; intros <-. cbn. f_equal. eapply IH. exact E2.
    - destruct (in_ranges a w (ue_ro U)) eqn:Ero; [|discriminate].
      destruct (img_bytes U a (Z.to_nat w)) as [zs|] eqn:Eib; [|discriminate]. injection H; intros <- <-.
      destruct (img_bytes_rdn (ms_mem ms) (s_abs st) (Z.to_nat w) a zs (r_abs _ _ _ _ _ _ HR)
                  ltac:(intros k Hk; eapply in_ranges_Z; [exact Ero | lia]) Eib) as (bs & Hrd & Hmap).
      rewrite <- Hmap. eapply lit_result; eauto. rewrite <- (length_map bv_unsigned), Hmap.
      clear -Eib. revert a zs Eib. induction (Z.to_nat w) as [|n IH]; cbn [img_bytes]; intros a zs E.
      + injection E; intros <-; reflexivity.
      + destruct (img_byte U a); [|discriminate]. destruct (img_bytes U (a + 1) n) eqn:E2; [|discriminate]. injection E; intros <-. cbn. f_equal. eapply IH. exact E2.
  Qed.

  (* [comment removed for export] *)
  Lemma img_bytes_length : forall n a zs, img_bytes U a n = Some zs -> length zs = n.
  Proof.
    induction n as [|n IH]; cbn [img_bytes]; intros a zs E.
    - injection E; intros <-; reflexivity.
    - destruct (img_byte U a); [|discriminate]. destruct (img_bytes U (a + 1) n) eqn:E2; [|discriminate]. injection E; intros <-. cbn. f_equal. eapply IH. exact E2.
  Qed.

  Lemma find_field_sound : forall rho st ms t fs l w sx v st',
    wf_state st = true -> R U G M0 rho st ms -> 0 < w -> w <= 8 ->
    table_validb U t = true -> (forall f, In f fs -> In f (tb_fields t)) ->
    lin_below l (s_next st) = true ->
    find_field U st t fs l w sx = Some (v, st') ->
    exists rho' bs,
      rdn segs (ms_mem ms) (w64 (evl rho l)) (Z.to_nat w) = Some bs
      /\ R U G M0 rho' st' ms /\ lext rho st rho' st' /\ val_ok rho' v (ldval w sx bs) /\ aval_below v (s_next st') = true.
  Proof.
    intros rho st ms t fs l w sx v st' Hwf HR Hw Hw8 Htv Hsub Hl.
    pose proof (R_to_VS _ _ _ HR) as HVS.
    unfold table_validb in Htv. apply andb_prop in Htv as [Htv Hfs]. apply andb_prop in Htv as [Htv Hro]. apply andb_prop in Htv as [Hst Hct].
    apply Z.ltb_lt in Hst. apply Z.ltb_lt in Hct. rewrite forallb_forall in Hfs.
    induction fs as [|f r IH]; cbn [find_field]; intros H; [discriminate|].
    match type of H with (match ?here with Some rr => Some rr | None => _ end = _) => destruct here as [res|] eqn:Eh end.
    2: { apply IH; [intros g Hg; apply Hsub; right; exact Hg | exact H]. }
    injection H; intros Eres. subst res. clear H IH.
    specialize (Hfs f (Hsub f (or_introl eq_refl))).
    apply andb_prop in Hfs as [Hfs Hrows]. apply andb_prop in Hfs as [Hfs Hoffw]. apply andb_prop in Hfs as [Hfs Hoff0]. apply andb_prop in Hfs as [Hw0 Hw8'].
    apply Z.leb_le in Hoffw. apply Z.leb_le in Hoff0.
    destruct (Z.eqb (tf_w f) w &&& match tf_kind f with TFresh => true | _ => Bool.eqb (tf_sx f) sx end)%bool eqn:Ec; [|discriminate].
    apply andb_prop in Ec as [Ewf Esx]. apply Z.eqb_eq in Ewf.
    set (rr := laddc l (- (tb_base t + tf_off f))) in Eh.
    destruct (ldivisible rr (tb_stride t)) eqn:Ediv; [|discriminate].
    set (idx := ldiv rr (tb_stride t)) in Eh.
    destruct (entails (s_ctx st) idx None) eqn:Ei0; [|discriminate].
    destruct (entails (s_ctx st) (laddc (lneg idx) (tb_count t - 1)) None) eqn:Ei1; [|discriminate].
    pose proof (entails_sound rho _ _ None (proj1 HVS) Ei0) as Hi0.
    pose proof (entails_sound rho _ _ None (proj1 HVS) Ei1) as Hi1. rewrite laddc_sound, lneg_sound in Hi1.
    pose proof (ldiv_sound rho rr (tb_stride t) ltac:(lia) Ediv) as Hdiv. fold idx in Hdiv. unfold rr in Hdiv. rewrite laddc_sound in Hdiv.
    set (i := evl rho idx) in *.
    assert (Hidx_b : lin_below idx (s_next st) = true) by (unfold idx, rr; apply ldiv_below; apply laddc_below; exact Hl).
    destruct (rows_ok_sound t f (Z.to_nat (tb_count t)) 0 i Hrows ltac:(lia)) as (v0 & Hfv & Hkind).
    unfold field_val in Hfv. rewrite Ewf in Hfv.
    destruct (img_bytes U (tb_base t + tb_stride t * i + tf_off f) (Z.to_nat w)) as [zs|] eqn:Eib; [|discriminate]. injection Hfv; intros Hv0.
    assert (Hro' : forall k, 0 <= k < Z.of_nat (Z.to_nat w) -> in_rangesZ (tb_base t + tb_stride t * i + tf_off f + k) (ue_ro U)).
    { intros k Hk. replace (tb_base t + tb_stride t * i + tf_off f + k) with (tb_base t + (tb_stride t * i + tf_off f + k)) by lia.
      eapply in_ranges_Z; [exact Hro|]. split; [nia|].
      assert (tb_stride t * i + tb_stride t <= tb_stride t * tb_count t) by nia. lia. }
    destruct (img_bytes_rdn (ms_mem ms) (s_abs st) (Z.to_nat w) _ zs (r_abs _ _ _ _ _ _ HR) Hro' Eib) as (bs & Hrd & Hmap).
    replace (tb_base t + tb_stride t * i + tf_off f) with (evl rho l) in Hrd by lia.
    assert (Hlen : Z.of_nat (length bs) = w) by (rewrite <- (length_map bv_unsigned), Hmap, (img_bytes_length _ _ _ Eib); lia).
    assert (Hval : ldval w sx bs = w64 (ext_lit sx w (le_of_bytes zs))) by (rewrite <- Hmap, le_of_bytes_map; apply ldval_ext; lia).
    assert (GEN : forall p, (exists rho', VOK rho st p rho' (ldval w sx bs)) -> Some p = Some (v, st') ->
              exists rho' bs0, rdn segs (ms_mem ms) (w64 (evl rho l)) (Z.to_nat w) = Some bs0 /\ R U G M0 rho' st' ms /\ lext rho st rho' st'
                               /\ val_ok rho' v (ldval w sx bs0) /\ aval_below v (s_next st') = true).
    { intros p [rho' HV] E. injection E; intros ->. exists rho', bs. split; [exact Hrd|]. exact (VOK_R rho st ms (v, st') rho' _ Hwf HR HV). }
    destruct (tf_kind f) as [|lo hi|c0 c1].
    - refine (GEN _ _ Eh). apply fresh_unk_VOK; [exact HVS | lia | lia | lia].
    - refine (GEN _ _ Eh). apply Bool.eqb_prop in Esx. subst sx.
      eapply VOK_fresh; [exact HVS | | exact Hval]. rewrite Hv0. unfold in_itv; cbn [ilo ihi]. exact Hkind.
    - refine (GEN _ _ Eh). apply Bool.eqb_prop in Esx. subst sx. exists rho. apply VOK_lv; [exact HVS | |].
      + apply laddc_below. apply lscale_below. exact Hidx_b.
      + rewrite Hval, Hv0, Hkind, laddc_sound, lscale_sound. fold i. f_equal. lia.
  Qed.

  Lemma find_table_sound : forall rho st ms ts l w sx v st',
    wf_state st = true -> R U G M0 rho st ms -> 0 < w -> w <= 8 ->
    (forall t, In t ts -> In t (ue_tabs U)) -> lin_below l (s_next st) = true ->
    find_table U st ts l w sx = Some (v, st') ->
    exists rho' bs,
      rdn segs (ms_mem ms) (w64 (evl rho l)) (Z.to_nat w) = Some bs
      /\ R U G M0 rho' st' ms /\ lext rho st rho' st' /\ val_ok rho' v (ldval w sx bs) /\ aval_below v (s_next st') = true.
  Proof.
    intros rho st ms ts l w sx v st' Hwf HR Hw Hw8 Hsub Hl.
    pose proof (uo_tabs U UOK) as HT. unfold tables_validb in HT. rewrite forallb_forall in HT.
    induction ts as [|t r IH]; cbn [find_table]; intros H; [discriminate|].
    destruct (find_field U st t (tb_fields t) l w sx) as [[v1 st1]|] eqn:Ef.
    - injection H; intros <- <-. eapply find_field_sound; eauto. apply HT. apply Hsub. left; reflexivity.
    - apply IH; [intros t' Ht'; apply Hsub; right; exact Ht' | exact H].
  Qed.

  (* [comment removed for export] *)
  Lemma do_load_sound : forall rho st ms av wa w sx v st',
    wf_state st = true -> R U G M0 rho st ms ->
    val_ok rho av wa -> aval_below av (s_next st) = true ->
    0 < w -> w <= 8 ->
    do_load U st av w sx = LDOk v st' ->
    exists rho' bs,
      rdn segs (ms_mem ms) wa (Z.to_nat w) = Some bs
      /\ R U G M0 rho' st' ms
      /\ lext rho st rho' st'
      /\ val_ok rho' v (ldval w sx bs)
      /\ aval_below v (s_next st') = true.
  Proof.
    intros rho st ms av wa w sx v st' Hwf HR Hav Hbel Hw Hw8 H.
    pose proof (wf_parts st Hwf) as (_ & _ & _ & _ & _ & _ & _ & W18 & _ & _).
    pose proof (classify_spec rho av wa (s_next st) Hav Hbel W18) as HC.
    unfold do_load in H.
    destruct (classify av) as [[off|off|off|a]|] eqn:Ecl.
    - subst wa. destruct (load_stack_lit U st off w sx) as [[v1 st1]|] eqn:E; [|discriminate]. injection H; intros <- <-.
      eapply load_stack_lit_sound; eauto.
    - destruct HC as [-> Hob]. destruct (load_stack_sym U st off w sx) as [[v1 st1]|] eqn:E; [|discriminate]. injection H; intros <- <-.
      eapply load_stack_sym_sound; eauto.
    - destruct HC as [-> Hob]. destruct (load_pay U st off w sx) as [v1 st1|o p|] eqn:E; try discriminate. injection H; intros <- <-.
      destruct (Z.eq_dec w 1) as [->|Hne].
      + eapply load_pay_sound; eauto.
      + exfalso. unfold load_pay in E. rewrite (proj2 (Z.eqb_neq w 1) Hne) in E. discriminate.
    - destruct HC as [-> Ha]. destruct (load_abs U st a w sx) as [[v1 st1]|] eqn:E; [|discriminate]. injection H; intros <- <-.
      eapply load_abs_sound; eauto.
    - destruct av as [|l| |]; try discriminate. cbn in Hav, Hbel. subst wa.
      destruct (load_table U st l w sx) as [[v1 st1]|] eqn:E; [|discriminate]. injection H; intros <- <-.
      unfold load_table in E. eapply find_table_sound; eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma do_load_split_sound : forall rho st av w sx o p,
    do_load U st av w sx = LDSplit o p ->
    evl rho o < evl rho p \/ evl rho p <= evl rho o.
  Proof. intros. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition store_bytes (w : Z) (wv : word) : list byte := Z_to_le_bytes (Z.to_nat w) (bv_unsigned wv).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma w64_unsigned_small : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (w64 a) = a.
  Proof. intros. rewrite w64_unsigned. apply Z.mod_small. lia. Qed.

  (* [comment removed for export] *)
  Lemma wbytes_inside : forall bs m (a : word) k d,
    bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 -> (k < length bs)%nat ->
    wbytes m a bs (a + nat_to_word k)%bv = Some (nth k bs d).
  Proof.
    induction bs as [|b rest IH]; intros m a k d Hnw Hk; cbn [length] in *; [lia|].
    pose proof (u64_range a) as Hua.
    cbn [wbytes]. destruct k as [|k].
    - assert (E0 : (a + nat_to_word 0)%bv = a).
      { apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned (nat_to_word 0)) with 0. rewrite Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range. }
      rewrite E0. cbn [nth]. destruct rest as [|b' r'].
      + cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
      + cbn [length] in Hnw. rewrite wbytes_below; [rewrite bv_eqb_refl; reflexivity | |]; rewrite u_add1 by lia; [cbn [length]; lia | lia].
    - cbn [nth]. assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      assert (E : (a + nat_to_word (S k))%bv = (a + 1 + nat_to_word k)%bv).
      { apply bv_eq. rewrite !bv_add_unsigned. change (bv_unsigned (1 : word)) with 1. unfold nat_to_word. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
        rewrite Nat2Z.inj_succ, Z.add_mod_idemp_l by lia.
        rewrite (Z.mod_small (Z.succ (Z.of_nat k))), (Z.mod_small (Z.of_nat k)) by lia. f_equal. lia. }
      rewrite E. apply IH; [rewrite Hu1; lia | lia].
  Qed.

  Lemma Z_to_le_bytes_nth : forall n z k d, (k < n)%nat ->
    nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
  Proof.
    induction n as [|n IH]; intros z k d Hk; [lia|]. cbn [Z_to_le_bytes]. destruct k as [|k].
    - cbn [nth]. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
    - cbn [nth]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
  Qed.

  Lemma Z_to_bv8_mod : forall y, Z_to_bv 8 (y mod 256) = Z_to_bv 8 y.
  Proof. intros. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod. change (2 ^ 8) with 256. apply Z.mod_mod. lia. Qed.

  (* [comment removed for export] *)
  Lemma store_bytes_ok : forall rho v wv w,
    0 < w -> w <= 8 -> val_ok rho v wv -> val_bytes_ok rho v w (store_bytes w wv).
  Proof.
    intros rho v wv w Hw Hw8 Hv. unfold store_bytes, val_bytes_ok.
    pose proof (u64_range wv) as Hr.
    rewrite length_Z_to_le_bytes, bytes_le_to_Z_of_le_bytes, Z2Nat.id by lia. split; [reflexivity|].
    assert (MM : forall z, (z mod 2 ^ 64) mod 2 ^ (8 * w) = z mod 2 ^ (8 * w)).
    { intros z. apply Z.mod_mod_divide. exists (2 ^ (64 - 8 * w)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    destruct v as [|l|neg k a b|a b]; [exact I| | |]; cbn in Hv; rewrite Hv; rewrite ?w64_unsigned, ?MM; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma bm_get_set : forall bm a b x, bm_get (bm_set bm a b) x = if Z.eqb x a then Some b else bm_get bm x.
  Proof.
    induction bm as [|[y c] r IH]; cbn; intros a b x.
    - destruct (Z.ltb_spec x a), (Z.eqb_spec x a); try reflexivity; lia.
    - destruct (Z.ltb_spec a y).
      + cbn. destruct (Z.ltb_spec x a), (Z.eqb_spec x a), (Z.ltb_spec x y), (Z.eqb_spec x y); try reflexivity; lia.
      + destruct (Z.eqb_spec a y).
        * subst. cbn. destruct (Z.ltb_spec x y), (Z.eqb_spec x y); try reflexivity; lia.
        * cbn. rewrite IH. destruct (Z.ltb_spec x y), (Z.eqb_spec x y), (Z.eqb_spec x a); try reflexivity; lia.
  Qed.

  Lemma bm_get_set_bytes : forall n bm a z x,
    bm_get (bm_set_bytes bm a z n) x =
    if (Z.leb a x &&& Z.ltb x (a + Z.of_nat n))%bool then Some ((z / 2 ^ (8 * (x - a))) mod 256) else bm_get bm x.
  Proof.
    induction n as [|n IH]; intros bm a z x; cbn [bm_set_bytes].
    - destruct (Z.leb_spec a x); [destruct (Z.ltb_spec x (a + Z.of_nat 0)); [lia|]|]; reflexivity.
    - rewrite IH, bm_get_set.
      destruct (Z.leb_spec (a + 1) x); [destruct (Z.ltb_spec x (a + 1 + Z.of_nat n))|]; cbn;
        destruct (Z.eqb_spec x a); destruct (Z.leb_spec a x); try lia; try (destruct (Z.ltb_spec x (a + Z.of_nat (S n))); try lia); try reflexivity.
      + f_equal. f_equal. rewrite Z.div_div by lia. f_equal. change 256 with (2 ^ 8). rewrite <- Z.pow_add_r by lia. f_equal. lia.
      + subst. rewrite Z.sub_diag, Z.mul_0_r, Z.pow_0_r, Z.div_1_r. reflexivity.
  Qed.

  Section StoreFacts.
    Variable m : word -> option byte.
    Variable A : Z.
    Variable bs : list byte.
    Hypothesis HA0 : 0 <= A.
    Hypothesis HA64 : A < 2 ^ 64.
    Hypothesis HAn : A + Z.of_nat (length bs) <= 2 ^ 64.
    Let m' := wbytes m (w64 A) bs.

    Lemma wA : bv_unsigned (w64 A) = A.
    Proof. apply w64_unsigned_small. lia. Qed.

    Lemma st_out_w : forall x : word, ~ (A <= bv_unsigned x < A + Z.of_nat (length bs)) -> m' x = m x.
    Proof.
      intros x Hx. unfold m'. destruct (Z.lt_ge_cases (bv_unsigned x) A).
      - apply wbytes_below; rewrite wA; lia.
      - apply wbytes_above; rewrite wA; lia.
    Qed.

    Lemma st_out : forall x, 0 <= x < 2 ^ 64 -> ~ (A <= x < A + Z.of_nat (length bs)) -> m' (w64 x) = m (w64 x).
    Proof. intros x Hx Hn. apply st_out_w. rewrite w64_unsigned_small by lia. exact Hn. Qed.

    Lemma st_hit : rdn segs m' (w64 A) (length bs) = Some bs.
    Proof. unfold m'. apply rdn_wbytes_hit. rewrite wA. lia. Qed.

    Lemma st_rdn_out : forall x k, 0 <= x -> x + Z.of_nat k <= 2 ^ 64 ->
      (x + Z.of_nat k <= A \/ A + Z.of_nat (length bs) <= x) -> rdn segs m' (w64 x) k = rdn segs m (w64 x) k.
    Proof.
      intros x k Hx Hxk Hd. unfold m'.
      destruct k as [|k]; [reflexivity|].
      apply rdn_wbytes_out; rewrite ?wA, ?w64_unsigned_small; lia.
    Qed.

    Lemma st_grows : forall x b, m x = Some b -> exists b', m' x = Some b'.
    Proof.
      intros x b Hb. destruct (m' x) as [b'|] eqn:E; [exists b'; reflexivity|].
      exfalso. refine (wbytes_grows bs m (w64 A) x _ E). rewrite Hb. discriminate.
    Qed.

    Lemma st_rd1_grows : forall x b, rd1 U m x = Some b -> exists b', rd1 U m' x = Some b'.
    Proof.
      intros x b H. apply rd1_rdn in H. cbn [rdn] in H.
      destruct (m (w64 x)) as [b0|] eqn:E0.
      - destruct (st_grows _ _ E0) as [b' Hb']. exists b'. apply rd1_rdn. cbn [rdn]. fold m'. rewrite Hb'. reflexivity.
      - destruct (seg_rom segs (w64 x)) as [b0|] eqn:Es; [|discriminate].
        destruct (m' (w64 x)) as [b'|] eqn:E'.
        + exists b'. apply rd1_rdn. cbn [rdn]. fold m'. rewrite E'. reflexivity.
        + exists b0. apply rd1_rdn. cbn [rdn]. fold m'. rewrite E'. fold segs. rewrite Es. reflexivity.
    Qed.

    Lemma st_inside : forall k d, (k < length bs)%nat -> m' (w64 (A + Z.of_nat k)) = Some (nth k bs d).
    Proof.
      intros k d Hk. unfold m'. rewrite <- w64_plus, <- nat_to_word_w64. apply wbytes_inside; [rewrite wA; lia | exact Hk].
    Qed.

    Lemma st_rd1_inside : forall k d, (k < length bs)%nat -> rd1 U m' (A + Z.of_nat k) = Some (nth k bs d).
    Proof. intros k d Hk. apply rd1_rdn. cbn [rdn]. fold m'. rewrite (st_inside k d Hk). reflexivity. Qed.

    Lemma st_rd1_out : forall x, 0 <= x -> x + 1 <= 2 ^ 64 -> (x + 1 <= A \/ A + Z.of_nat (length bs) <= x) -> rd1 U m' x = rd1 U m x.
    Proof. intros x Hx Hx1 Hd. unfold rd1. fold segs. fold m'. rewrite (st_rdn_out x 1) by lia. reflexivity. Qed.
  End StoreFacts.


  (* [comment removed for export] *)
  Lemma overlaps_false : forall o1 w1 o2 w2, overlaps o1 w1 o2 w2 = false -> o2 + w2 <= o1 \/ o1 + w1 <= o2.
  Proof.
    intros. unfold overlaps in H. destruct (Z.ltb_spec o1 (o2 + w2)); [destruct (Z.ltb_spec o2 (o1 + w1)); [discriminate|]|]; lia.
  Qed.

  Lemma cells_kill_spec : forall cs off w c, In c (cells_kill cs off w) -> In c cs /\ overlaps (c_off c) (c_w c) off w = false.
  Proof.
    induction cs as [|d r IH]; cbn; intros off w c H; [destruct H|].
    destruct (overlaps (c_off d) (c_w d) off w) eqn:E.
    - destruct (IH _ _ _ H) as [A B]. split; [right; exact A | exact B].
    - destruct H as [<-|H]; [split; [left; reflexivity | exact E]|]. destruct (IH _ _ _ H) as [A B]. split; [right; exact A | exact B].
  Qed.

  Lemma length_store_bytes : forall w wv, length (store_bytes w wv) = Z.to_nat w.
  Proof. intros. unfold store_bytes. apply length_Z_to_le_bytes. Qed.

  (* [comment removed for export] *)
  Lemma stack_cell_ok_store : forall rho m sp0 o bs c,
    0 <= sp0 - ue_fr U -> sp0 < 2 ^ 62 ->
    stack_cell_ok U rho m sp0 c -> (c_off c + c_w c <= o \/ o + Z.of_nat (length bs) <= c_off c) -> - ue_fr U <= o -> o + Z.of_nat (length bs) <= 0 ->
    stack_cell_ok U rho (wbytes m (w64 (sp0 + o)) bs) sp0 c.
  Proof.
    intros rho m sp0 o bs c H0 H62 (A & B & C & cbs & Hrd & Hvb) Hd Ho Ho'.
    split; [exact A|]. split; [exact B|]. split; [exact C|]. exists cbs. split; [|exact Hvb].
    rewrite (st_rdn_out m (sp0 + o) bs); [exact Hrd | lia | lia | lia | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma arr_ok_store : forall rho m sp0 o bs a,
    0 <= sp0 - ue_fr U -> sp0 < 2 ^ 62 ->
    arr_ok U rho m sp0 a -> (ar_hi a <= o \/ o + Z.of_nat (length bs) <= ar_lo a) -> - ue_fr U <= o -> o + Z.of_nat (length bs) <= 0 ->
    arr_ok U rho (wbytes m (w64 (sp0 + o)) bs) sp0 a.
  Proof.
    intros rho m sp0 o bs a H0 H62 (A & B & C) Hd Ho Ho'.
    split; [exact A|]. split; [exact B|]. destruct (ar_fact a) as [f|]; [|exact I].
    destruct C as (C1 & C2 & C3 & C4). split; [exact C1|]. split; [exact C2|]. split.
    - intros j Hj. destruct (C3 j Hj) as (Hlt & b & Hb & Hr). split; [exact Hlt|]. exists b. split; [|exact Hr].
      rewrite (st_rd1_out m (sp0 + o) bs); [exact Hb | lia | lia | lia | lia | lia | lia].
    - intros H1. destruct (C4 H1) as (b & Hb & Hi). destruct (C3 0 ltac:(lia)) as [Hlt0 _]. exists b. split; [|exact Hi].
      rewrite (st_rd1_out m (sp0 + o) bs); [exact Hb | lia | lia | lia | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma R_stack_store : forall rho st ms o w wv stk' ars',
    wf_state st = true -> R U G M0 rho st ms ->
    - ue_fr U <= o -> o + w <= 0 -> 0 < w -> w <= 8 ->
    let m' := wbytes (ms_mem ms) (w64 (rho SYM_SP0 + o)) (store_bytes w wv) in
    Forall (stack_cell_ok U rho m' (rho SYM_SP0)) stk' ->
    Forall (arr_ok U rho m' (rho SYM_SP0)) ars' ->
    store_ok segs (ms_mem ms) (w64 (rho SYM_SP0 + o)) (Z.to_nat w) = true /\
    R U G M0 rho (set_arrs (set_stk st stk') ars') (ms_with_mem ms m').
  Proof.
    intros rho st ms o w wv stk' ars' Hwf HR Ho1 Ho2 Hw Hw8 m' Hstk Hars. subst m'.
    destruct HR as [Rglob Rpc Rsvc Rregs Rvs Rstk Rarrs Rwin Rpay Rabs Rresv Rfrm Rframe Rsp0 Ralign Rra Rdata].
    set (sp0 := rho SYM_SP0) in *. set (A := sp0 + o) in *.
    pose proof (length_store_bytes w wv) as Hlen.
    assert (HA0 : 0 <= A) by lia. assert (HA64 : A < 2 ^ 64) by lia.
    assert (HAn : A + Z.of_nat (length (store_bytes w wv)) <= 2 ^ 64) by lia.
    split.
    { apply store_ok_of_all; rewrite w64_unsigned_small by lia; [lia|].
      intros x Hx. destruct (proj1 Rwin (bv_unsigned x) ltac:(lia)) as [b Hb]. rewrite w64_of_unsigned in Hb.
      unfold wview. rewrite Hb. discriminate. }
    constructor; cbn; try assumption.
    - (* [comment removed for export] *) split; [|exact (proj2 Rwin)]. intros a Ha. destruct (proj1 Rwin a Ha) as [b Hb]. exact (st_grows _ A _ _ _ Hb).
    - (* [comment removed for export] *) destruct Rpay as (P1 & P2 & P3 & P4). split; [|split; [exact P2 | split]].
      + intros i Hi. destruct (P1 i Hi) as [b Hb]. exact (st_rd1_grows _ A _ _ _ Hb).
      + intros off sx x Hin. destruct (P3 off sx x Hin) as (Hr & b & Hb & Hx). split; [exact Hr|]. exists b. split; [|exact Hx].
        rewrite (st_rd1_out _ A _ HA0 HA64 HAn); [exact Hb | lia | lia | lia].
      + intros off i Hin. destruct (P4 off i Hin) as (Hr & b & Hb & Hi). split; [exact Hr|]. exists b. split; [|exact Hi].
        rewrite (st_rd1_out _ A _ HA0 HA64 HAn); [exact Hb | lia | lia | lia].
    - (* [comment removed for export] *) destruct Rabs as (Q1 & Q2 & Q3). split; [|split].
      + intros a b Hg. destruct (Q1 a b Hg) as (Hrw & Hb & Hm). pose proof (uo_small U UOK a (or_introl Hrw)).
        split; [exact Hrw|]. split; [exact Hb|]. rewrite (st_out _ A _ HA0 HA64 HAn) by lia. exact Hm.
      + intros a Hrw Hg. pose proof (uo_small U UOK a (or_introl Hrw)). rewrite (st_out _ A _ HA0 HA64 HAn) by lia. exact (Q2 a Hrw Hg).
      + intros a b Hro Hm. pose proof (uo_small U UOK a (or_intror Hro)). rewrite (st_out _ A _ HA0 HA64 HAn) in Hm by lia. exact (Q3 a b Hro Hm).
    - (* [comment removed for export] *) destruct Rframe as [F1 F2]. split.
      + intros a Hnw Hnrw. rewrite (st_out_w _ A _ HA0 HA64 HAn) by lia. exact (F1 a Hnw Hnrw).
      + intros a b Hb. destruct (F2 a b Hb) as [b' Hb']. exact (st_grows _ A _ _ _ Hb').
  Qed.

  (* [comment removed for export] *)
  Lemma R_abs_store : forall rho st ms a w z v wv,
    wf_state st = true -> R U G M0 rho st ms -> in_ranges a w (ue_rw U) = true -> 0 < w -> w <= 8 ->
    val_ok rho v wv -> aval_lit v = Some z ->
    let m' := wbytes (ms_mem ms) (w64 a) (store_bytes w wv) in
    store_ok segs (ms_mem ms) (w64 a) (Z.to_nat w) = true /\
    R U G M0 rho (set_pay (set_pcache (set_abs st (bm_set_bytes (s_abs st) a (z mod two64z) (Z.to_nat w))) []) []) (ms_with_mem ms m').
  Proof.
    intros rho st ms a w z v wv Hwf HR Hrw Hw Hw8 Hv Hz m'. subst m'.
    pose proof (aval_lit_sound rho v z wv Hz Hv) as Hwv.
    assert (Hu : bv_unsigned wv = z mod two64z) by (rewrite Hwv, w64_unsigned, two64z_eq; reflexivity).
    assert (Hrg : forall k, 0 <= k < w -> in_rangesZ (a + k) (ue_rw U)) by (intros k Hk; eapply in_ranges_Z; eauto).
    assert (Hra : in_rangesZ a (ue_rw U)) by (pose proof (Hrg 0 ltac:(lia)) as H0; rewrite Z.add_0_r in H0; exact H0).
    pose proof (uo_small U UOK a (or_introl Hra)) as Ha0.
    pose proof (uo_small U UOK (a + (w - 1)) (or_introl (Hrg (w - 1) ltac:(lia)))) as Ha1.
    destruct HR as [Rglob Rpc Rsvc Rregs Rvs Rstk Rarrs Rwin Rpay Rabs Rresv Rfrm Rframe Rsp0 Ralign Rra Rdata].
    set (sp0 := rho SYM_SP0) in *.
    pose proof (length_store_bytes w wv) as Hlen.
    assert (HA0 : 0 <= a) by lia. assert (HA64 : a < 2 ^ 64) by lia.
    assert (HAn : a + Z.of_nat (length (store_bytes w wv)) <= 2 ^ 64) by lia.
    split.
    { apply store_ok_of_all; rewrite w64_unsigned_small by lia; [lia|].
      intros x Hx. pose proof (uo_rw_w U UOK (bv_unsigned x) (ms_mem ms) ltac:(replace (bv_unsigned x) with (a + (bv_unsigned x - a)) by lia; apply Hrg; lia)) as So.
      rewrite w64_of_unsigned in So. cbn [store_ok] in So. fold segs in So. destruct (wview segs (ms_mem ms) x); [discriminate | discriminate]. }
    constructor; cbn; try assumption.
    - (* [comment removed for export] *) apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Rstk c Hc) as (A & B & C & cbs & Hrd & Hvb).
      split; [exact A|]. split; [exact B|]. split; [exact C|]. exists cbs. split; [|exact Hvb].
      rewrite (st_rdn_out _ a _ HA0 HA64 HAn); [exact Hrd | lia | lia | lia].
    - (* [comment removed for export] *) apply Forall_forall. intros ar Har. pose proof (proj1 (Forall_forall _ _) Rarrs ar Har) as (A & B & C).
      split; [exact A|]. split; [exact B|]. destruct (ar_fact ar) as [f|]; [|exact I]. destruct C as (C1 & C2 & C3 & C4).
      split; [exact C1|]. split; [exact C2|]. split.
      + intros j Hj. destruct (C3 j Hj) as (Hlt & b & Hb & Hr). split; [exact Hlt|].
        exists b. split; [|exact Hr]. rewrite (st_rd1_out _ a _ HA0 HA64 HAn); [exact Hb | lia | lia | lia].
      + intros H1. destruct (C4 H1) as (b & Hb & Hi). destruct (C3 0 ltac:(lia)) as [Hlt0 _].
        exists b. split; [|exact Hi]. rewrite (st_rd1_out _ a _ HA0 HA64 HAn); [exact Hb | lia | lia | lia].
    - (* [comment removed for export] *) split; [|exact (proj2 Rwin)]. intros x Hx. destruct (proj1 Rwin x Hx) as [b Hb]. exact (st_grows _ a _ _ _ Hb).
    - (* [comment removed for export] *) destruct Rpay as (P1 & P2 & P3 & P4). split; [|split; [exact P2 | split; [intros ? ? ? []|intros ? ? []]]].
      intros i Hi. destruct (P1 i Hi) as [b Hb]. exact (st_rd1_grows _ a _ _ _ Hb).
    - (* [comment removed for export] *) destruct Rabs as (Q1 & Q2 & Q3). split; [|split].
      + intros a' b Hg. rewrite bm_get_set_bytes in Hg.
        destruct (Z.leb_spec a a'); [destruct (Z.ltb_spec a' (a + Z.of_nat (Z.to_nat w)))|]; cbn in Hg.
        * injection Hg; intros <-. split; [replace a' with (a + (a' - a)) by lia; apply Hrg; lia|].
          split; [apply Z.mod_pos_bound; lia|].
          pose proof (st_inside (ms_mem ms) a (store_bytes w wv) HA0 HA64 HAn (Z.to_nat (a' - a)) (Z_to_bv 8 0) ltac:(lia)) as Hin.
          replace (a + Z.of_nat (Z.to_nat (a' - a))) with a' in Hin by lia. rewrite Hin. f_equal.
          unfold store_bytes. rewrite Z_to_le_bytes_nth by lia. rewrite Z.shiftr_div_pow2 by lia.
          rewrite <- Z_to_bv8_mod. f_equal. f_equal. rewrite Hu, two64z_eq. f_equal. f_equal. lia.
        * destruct (Q1 a' b Hg) as (Hrw' & Hb & Hm). pose proof (uo_small U UOK a' (or_introl Hrw')).
          split; [exact Hrw'|]. split; [exact Hb|]. rewrite (st_out _ a _ HA0 HA64 HAn) by lia. exact Hm.
        * destruct (Q1 a' b Hg) as (Hrw' & Hb & Hm). pose proof (uo_small U UOK a' (or_introl Hrw')).
          split; [exact Hrw'|]. split; [exact Hb|]. rewrite (st_out _ a _ HA0 HA64 HAn) by lia. exact Hm.
      + intros a' Hrw' Hg. rewrite bm_get_set_bytes in Hg. pose proof (uo_small U UOK a' (or_introl Hrw')).
        destruct (Z.leb_spec a a'); [destruct (Z.ltb_spec a' (a + Z.of_nat (Z.to_nat w)))|]; cbn in Hg; [discriminate| |];
          rewrite (st_out _ a _ HA0 HA64 HAn) by lia; exact (Q2 a' Hrw' Hg).
      + intros a' b Hro Hm. pose proof (uo_small U UOK a' (or_intror Hro)).
        assert (Hnot : ~ (a <= a' < a + Z.of_nat (length (store_bytes w wv)))).
        { intros Hc. apply (uo_disj U UOK a'); [|exact Hro]. replace a' with (a + (a' - a)) by lia. apply Hrg. lia. }
        rewrite (st_out _ a _ HA0 HA64 HAn) in Hm by lia. exact (Q3 a' b Hro Hm).
    - (* [comment removed for export] *) destruct Rframe as [F1 F2]. split.
      + intros x Hnw Hnrw. rewrite (st_out_w _ a _ HA0 HA64 HAn).
        * exact (F1 x Hnw Hnrw).
        * intros Hc. apply Hnrw. replace (bv_unsigned x) with (a + (bv_unsigned x - a)) by lia. apply Hrg. lia.
      + intros x b Hb. destruct (F2 x b Hb) as [b' Hb']. exact (st_grows _ a _ _ _ Hb').
  Qed.

  (* [comment removed for export] *)
  Definition touch1 (C : ctx) (off : lin) (w : Z) (v : aval) (a : arr) : arr :=
    match ar_fact a with
    | None => a
    | Some f =>
        if negb (Z.eqb w 1) then Arr (ar_lo a) (ar_hi a) None
        else if aval_in C v (af_blo f) (af_bhi f) then
          if lin_eq_ent C off (laddc (af_len f) (ar_lo a)) then
            let first' := if entails C (laddc (af_len f) (-1)) None then af_first f
                          else match v with LV l => ijoin_if (negb (leqb (af_len f) (lconst 0))) (af_first f) (lrange C l) | _ => itop end in
            Arr (ar_lo a) (ar_hi a) (Some (AFact (laddc (af_len f) 1) (af_blo f) (af_bhi f) first'))
          else
            if entails C (laddc off (- ar_lo a - 1)) None then a
            else Arr (ar_lo a) (ar_hi a) (Some (AFact (af_len f) (af_blo f) (af_bhi f)
                                              (match v with LV l => ijoin (af_first f) (lrange C l) | _ => itop end)))
        else if entails C (lsub (laddc off (- ar_lo a)) (af_len f)) None then a else Arr (ar_lo a) (ar_hi a) None
    end.

  Definition touch_test (C : ctx) (off : lin) (w : Z) (a : arr) : bool :=
    (entails C (laddc off (- ar_lo a)) None &&& entails C (laddc (lneg off) (ar_hi a - w)) None)%bool.

  Lemma arrs_touch_split : forall ars C off w v ars',
    arrs_touch ars C off w v = Some ars' ->
    exists pre a post, ars = pre ++ a :: post /\ ars' = pre ++ touch1 C off w v a :: post /\ touch_test C off w a = true.
  Proof.
    induction ars as [|a r IH]; cbn [arrs_touch]; intros C off w v ars' H; [discriminate|].
    fold (touch_test C off w a) in H. destruct (touch_test C off w a) eqn:Et.
    - injection H; intros <-. exists [], a, r. split; [reflexivity|]. split; [|exact Et]. cbn. f_equal.
    - destruct (arrs_touch r C off w v) as [r'|] eqn:Er; [|discriminate]. injection H; intros <-.
      destruct (IH _ _ _ _ _ Er) as (pre & b & post & -> & -> & Hb).
      exists (a :: pre), b, post. split; [reflexivity|]. split; [reflexivity | exact Hb].
  Qed.

  Lemma touch_test_sound : forall rho C off w a, ctx_ok rho C -> touch_test C off w a = true ->
    ar_lo a <= evl rho off /\ evl rho off + w <= ar_hi a.
  Proof.
    intros rho C off w a HC H. unfold touch_test in H. apply andb_prop in H as [H1 H2].
    pose proof (entails_sound rho C _ None HC H1) as E1. pose proof (entails_sound rho C _ None HC H2) as E2.
    rewrite laddc_sound in E1. rewrite laddc_sound, lneg_sound in E2. lia.
  Qed.

  Lemma arrs_disjointb_app : forall pre a post,
    arrs_disjointb (pre ++ a :: post) = true ->
    (forall b, In b pre -> overlaps (ar_lo b) (ar_hi b - ar_lo b) (ar_lo a) (ar_hi a - ar_lo a) = false) /\
    (forall b, In b post -> overlaps (ar_lo a) (ar_hi a - ar_lo a) (ar_lo b) (ar_hi b - ar_lo b) = false) /\
    arrs_disjointb (pre ++ post) = true.
  Proof.
    induction pre as [|c pre IH]; cbn -[overlaps]; intros a post H.
    - apply andb_prop in H as [H1 H2]. rewrite forallb_forall in H1. split; [intros b []|]. split; [|exact H2].
      intros b Hb. specialize (H1 b Hb). destruct (overlaps _ _ _ _); [discriminate | reflexivity].
    - apply andb_prop in H as [H1 H2]. rewrite forallb_forall in H1. destruct (IH a post H2) as (A & B & C).
      split; [|split; [exact B|]].
      + intros b [<-|Hb]; [|apply A; exact Hb]. specialize (H1 a ltac:(apply in_app_iff; right; left; reflexivity)).
        destruct (overlaps _ _ _ _); [discriminate | reflexivity].
      + apply andb_true_intro. split; [|exact C]. rewrite forallb_forall. intros b Hb. apply H1.
        apply in_app_iff in Hb. apply in_app_iff. destruct Hb; [left; assumption | right; right; assumption].
  Qed.

  Lemma store_byte_val : forall rho l wv d, wv = w64 (evl rho l) -> 0 <= evl rho l < 256 ->
    bv_unsigned (nth 0 (store_bytes 1 wv) d) = evl rho l.
  Proof.
    intros rho l wv d Hwv Hr. unfold store_bytes. change (Z.to_nat 1) with 1%nat. cbn [Z_to_le_bytes nth].
    rewrite Z_to_bv_unsigned, bv_wrap8_mod, Hwv, w64_unsigned. change (2 ^ 8) with 256.
    rewrite (Z.mod_small (evl rho l) (2 ^ 64)) by lia. apply Z.mod_small. lia.
  Qed.

  Lemma touch1_ok : forall rho C m sp0 off w v wv a,
    ctx_ok rho C -> val_ok rho v wv -> 0 < w -> w <= 8 ->
    0 <= sp0 - ue_fr U -> sp0 < 2 ^ 62 ->
    arr_ok U rho m sp0 a -> ar_lo a <= evl rho off -> evl rho off + w <= ar_hi a ->
    arr_ok U rho (wbytes m (w64 (sp0 + evl rho off)) (store_bytes w wv)) sp0 (touch1 C off w v a).
  Proof.
    intros rho C m sp0 off w v wv a HC Hv Hw Hw8 H0 H62 (A & B & Cf) Hlo Hhi.
    pose proof (length_store_bytes w wv) as Hlen.
    set (s := evl rho off) in *. set (AA := sp0 + s).
    assert (HA0 : 0 <= AA) by lia. assert (HA64 : AA < 2 ^ 64) by lia.
    assert (HAn : AA + Z.of_nat (length (store_bytes w wv)) <= 2 ^ 64) by lia.
    unfold touch1. destruct (ar_fact a) as [f|] eqn:Ef.
    2: { split; [exact A|]. split; [exact B|]. rewrite Ef. exact I. }
    destruct Cf as (C1 & C2 & C3 & C4).
    destruct (Z.eqb w 1) eqn:Ew; cbn [negb]; [|cbn; repeat split; assumption]. apply Z.eqb_eq in Ew. subst w.
    assert (UNCH : forall j, 0 <= j -> ar_lo a + j < ar_hi a -> sp0 + ar_lo a + j <> AA ->
              rd1 U (wbytes m (w64 AA) (store_bytes 1 wv)) (sp0 + ar_lo a + j) = rd1 U m (sp0 + ar_lo a + j)).
    { intros j Hj Hjh Hne. rewrite Hlen in HAn. change (Z.of_nat (Z.to_nat 1)) with 1 in HAn.
      apply (st_rd1_out m AA (store_bytes 1 wv) HA0 HA64); rewrite ?Hlen; change (Z.of_nat (Z.to_nat 1)) with 1; lia. }
    (* [comment removed for export] *)
    assert (FIRST0 : 1 <= evl rho (af_len f) -> sp0 + ar_lo a <> AA ->
              exists b, rd1 U (wbytes m (w64 AA) (store_bytes 1 wv)) (sp0 + ar_lo a) = Some b /\ in_itv (bv_unsigned b) (af_first f)).
    { intros H1 Hne. destruct (C4 H1) as (b & Hb & Hi). destruct (C3 0 ltac:(lia)) as [Hlt0 _]. exists b. split; [|exact Hi].
      replace (sp0 + ar_lo a) with (sp0 + ar_lo a + 0) by lia. rewrite UNCH by lia. rewrite Z.add_0_r. exact Hb. }
    destruct (aval_in C v (af_blo f) (af_bhi f)) eqn:Ein.
    - destruct v as [|l| |]; try discriminate. cbn in Hv. unfold aval_in in Ein. apply andb_prop in Ein as [E1 E2].
      pose proof (entails_sound rho C _ None HC E1) as V1. pose proof (entails_sound rho C _ None HC E2) as V2.
      rewrite laddc_sound in V1. rewrite laddc_sound, lneg_sound in V2.
      pose proof (store_byte_val rho l wv (Z_to_bv 8 0) Hv ltac:(lia)) as Hbyte.
      pose proof (st_rd1_inside m AA (store_bytes 1 wv) HA0 HA64 HAn 0 (Z_to_bv 8 0) ltac:(rewrite Hlen; cbn; lia)) as Hnew.
      rewrite Z.add_0_r in Hnew.
      pose proof (lrange_ok rho C l HC) as Hlr. rewrite <- Hbyte in Hlr.
      (* [comment removed for export] *)
      assert (FIRST1 : sp0 + ar_lo a = AA ->
                exists b, rd1 U (wbytes m (w64 AA) (store_bytes 1 wv)) (sp0 + ar_lo a) = Some b /\ in_itv (bv_unsigned b) (lrange C l)).
      { intros E. rewrite E. eexists. split; [exact Hnew | exact Hlr]. }
      destruct (lin_eq_ent C off (laddc (af_len f) (ar_lo a))) eqn:El.
      + pose proof (lin_eq_ent_sound rho C _ _ HC El) as Eo. rewrite laddc_sound in Eo. fold s in Eo.
        split; [exact A|]. split; [exact B|]. cbn [ar_fact ar_lo ar_hi]. split; [exact C1|]. split; [exact C2|].
        unfold afact_ok. cbn [af_len af_blo af_bhi af_first]. split.
        * intros j Hj. rewrite laddc_sound in Hj. split; [lia|].
          destruct (Z.eq_dec j (evl rho (af_len f))) as [->|Hne].
          -- exists (nth 0 (store_bytes 1 wv) (Z_to_bv 8 0)). replace (sp0 + ar_lo a + evl rho (af_len f)) with AA by lia. split; [exact Hnew | rewrite Hbyte; lia].
          -- destruct (C3 j ltac:(lia)) as (Hlt & b & Hb & Hr). exists b. split; [|exact Hr]. rewrite UNCH by lia. exact Hb.
        * intros H1. rewrite laddc_sound in H1.
          destruct (entails C (laddc (af_len f) (-1)) None) eqn:Elen1.
          -- pose proof (entails_sound rho C _ None HC Elen1) as L1. rewrite laddc_sound in L1. apply FIRST0; lia.
          -- destruct (leqb (af_len f) (lconst 0)) eqn:Elen0; cbn [negb ijoin_if].
             ++ pose proof (leqb_eval rho _ _ Elen0) as L0. rewrite lconst_sound in L0. apply FIRST1. lia.
             ++ destruct (Z.eq_dec (sp0 + ar_lo a) AA) as [E|Hne].
                ** destruct (FIRST1 E) as (b & Hb & Hi). exists b. split; [exact Hb | apply ijoin_r; exact Hi].
                ** destruct (FIRST0 ltac:(lia) Hne) as (b & Hb & Hi). exists b. split; [exact Hb | apply ijoin_l; exact Hi].
      + assert (KEEP : forall j, 0 <= j < evl rho (af_len f) ->
                  ar_lo a + j < ar_hi a /\ exists b, rd1 U (wbytes m (w64 AA) (store_bytes 1 wv)) (sp0 + ar_lo a + j) = Some b /\ af_blo f <= bv_unsigned b <= af_bhi f).
        { intros j Hj. destruct (C3 j Hj) as (Hlt & b & Hb & Hr). split; [exact Hlt|].
          destruct (Z.eq_dec (sp0 + ar_lo a + j) AA) as [E|Hne].
          * exists (nth 0 (store_bytes 1 wv) (Z_to_bv 8 0)). rewrite E. split; [exact Hnew | rewrite Hbyte; lia].
          * exists b. split; [|exact Hr]. rewrite UNCH by lia. exact Hb. }
        destruct (entails C (laddc off (- ar_lo a - 1)) None) eqn:Egt.
        * pose proof (entails_sound rho C _ None HC Egt) as Lgt. rewrite laddc_sound in Lgt. fold s in Lgt.
          split; [exact A|]. split; [exact B|]. rewrite Ef. split; [exact C1|]. split; [exact C2|]. split; [exact KEEP|].
          intros H1. apply FIRST0; lia.
        * split; [exact A|]. split; [exact B|]. cbn [ar_fact ar_lo ar_hi]. split; [exact C1|]. split; [exact C2|].
          unfold afact_ok. cbn [af_len af_blo af_bhi af_first]. split; [exact KEEP|].
          intros H1. destruct (Z.eq_dec (sp0 + ar_lo a) AA) as [E|Hne].
          -- destruct (FIRST1 E) as (b & Hb & Hi). exists b. split; [exact Hb | apply ijoin_r; exact Hi].
          -- destruct (FIRST0 H1 Hne) as (b & Hb & Hi). exists b. split; [exact Hb | apply ijoin_l; exact Hi].
    - destruct (entails C (lsub (laddc off (- ar_lo a)) (af_len f)) None) eqn:Eb; [|cbn; repeat split; assumption].
      pose proof (entails_sound rho C _ None HC Eb) as Vb. rewrite lsub_sound, laddc_sound in Vb. fold s in Vb.
      split; [exact A|]. split; [exact B|]. rewrite Ef. split; [exact C1|]. split; [exact C2|]. split.
      + intros j Hj. destruct (C3 j Hj) as (Hlt & b & Hb & Hr). split; [exact Hlt|]. exists b. split; [|exact Hr].
        rewrite UNCH by lia. exact Hb.
      + intros H1. apply FIRST0; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma arrs_touch_ok : forall rho C m sp0 ars off w v wv ars',
    ctx_ok rho C -> val_ok rho v wv -> 0 < w -> w <= 8 ->
    0 <= sp0 - ue_fr U -> sp0 < 2 ^ 62 ->
    Forall (arr_ok U rho m sp0) ars -> arrs_disjointb ars = true ->
    arrs_touch ars C off w v = Some ars' ->
    Forall (arr_ok U rho (wbytes m (w64 (sp0 + evl rho off)) (store_bytes w wv)) sp0) ars'
    /\ (exists a, In a ars /\ ar_lo a <= evl rho off /\ evl rho off + w <= ar_hi a /\ - ue_fr U <= ar_lo a /\ ar_hi a <= 0).
  Proof.
    intros rho C m sp0 ars off w v wv ars' HC Hv Hw Hw8 H0 H62 Hars Hdisj H.
    destruct (arrs_touch_split _ _ _ _ _ _ H) as (pre & a & post & -> & -> & Ht).
    destruct (touch_test_sound rho C off w a HC Ht) as [Hlo Hhi].
    destruct (arrs_disjointb_app pre a post Hdisj) as (Dpre & Dpost & _).
    assert (Ha : arr_ok U rho m sp0 a) by (apply (proj1 (Forall_forall _ _) Hars); apply in_app_iff; right; left; reflexivity).
    pose proof Ha as (A & B & _).
    pose proof (length_store_bytes w wv) as Hlen.
    split.
    - apply Forall_forall. intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|[<-|Hb]].
      + apply arr_ok_store; rewrite ?Hlen; [lia|lia| | |lia|lia].
        * apply (proj1 (Forall_forall _ _) Hars). apply in_app_iff. left; exact Hb.
        * destruct (overlaps_false _ _ _ _ (Dpre b Hb)); lia.
      + apply touch1_ok; auto.
      + apply arr_ok_store; rewrite ?Hlen; [lia|lia| | |lia|lia].
        * apply (proj1 (Forall_forall _ _) Hars). apply in_app_iff. right; right; exact Hb.
        * destruct (overlaps_false _ _ _ _ (Dpost b Hb)); lia.
    - exists a. split; [apply in_app_iff; right; left; reflexivity|]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma arrs_overlap_lit_false : forall ars off w b,
    arrs_overlap_lit ars off w = false -> In b ars -> off + w <= ar_lo b \/ ar_hi b <= off.
  Proof.
    intros ars off w b H Hb. unfold arrs_overlap_lit in H.
    destruct (overlaps (ar_lo b) (ar_hi b - ar_lo b) off w) eqn:E.
    - exfalso. assert (existsb (fun a => overlaps (ar_lo a) (ar_hi a - ar_lo a) off w) ars = true); [|congruence].
      apply existsb_exists. exists b. split; [exact Hb | exact E].
    - destruct (overlaps_false _ _ _ _ E); lia.
  Qed.

  Lemma store_stack_lit_sound : forall rho st ms off w v wv st',
    wf_state st = true -> R U G M0 rho st ms -> val_ok rho v wv -> aval_below v (s_next st) = true -> 0 < w -> w <= 8 ->
    store_stack_lit U st off w v = Some st' ->
    store_ok segs (ms_mem ms) (w64 (rho SYM_SP0 + off)) (Z.to_nat w) = true
    /\ R U G M0 rho st' (ms_with_mem ms (wbytes (ms_mem ms) (w64 (rho SYM_SP0 + off)) (store_bytes w wv)))
    /\ (s_next st' = s_next st /\ s_pc st' = s_pc st /\ s_regs st' = s_regs st /\ s_resv st' = s_resv st).
  Proof.
    intros rho st ms off w v wv st' Hwf HR Hv Hvb Hw Hw8 H.
    pose proof (wf_parts st Hwf) as (_ & _ & _ & _ & _ & _ & Wdisj & W18 & _ & Wad).
    pose proof (R_to_VS _ _ _ HR) as HVS. pose proof (r_sp0 _ _ _ _ _ _ HR) as Hsp0. pose proof (uo_fr U UOK) as Hfr.
    pose proof (length_store_bytes w wv) as Hlen.
    unfold store_stack_lit in H. destruct (in_window U off w) eqn:Win; cbn [negb] in H; [|discriminate].
    unfold in_window in Win. apply andb_prop in Win as [Win1 Win2]. apply Z.leb_le in Win1. apply Z.leb_le in Win2.
    assert (CELLS : Forall (stack_cell_ok U rho (wbytes (ms_mem ms) (w64 (rho SYM_SP0 + off)) (store_bytes w wv)) (rho SYM_SP0)) (cells_kill (s_stk st) off w)).
    { apply Forall_forall. intros c Hc. destruct (cells_kill_spec _ _ _ _ Hc) as [Hin Hov].
      apply stack_cell_ok_store; rewrite ?Hlen; [lia | lia | exact (proj1 (Forall_forall _ _) (r_stk _ _ _ _ _ _ HR) c Hin) | | lia | lia].
      destruct (overlaps_false _ _ _ _ Hov); lia. }
    destruct (arrs_overlap_lit (s_arrs st) off w) eqn:Eov.
    - destruct (arrs_touch (s_arrs st) (s_ctx st) (lconst off) w v) as [ars'|] eqn:Et; [|discriminate]. injection H; intros <-.
      destruct (arrs_touch_ok rho (s_ctx st) (ms_mem ms) (rho SYM_SP0) (s_arrs st) (lconst off) w v wv ars' (proj1 HVS) Hv Hw Hw8 ltac:(lia) ltac:(lia)
                  (r_arrs _ _ _ _ _ _ HR) Wad Et) as [ARRS _].
      rewrite lconst_sound in ARRS.
      destruct (R_stack_store rho st ms off w wv (cells_kill (s_stk st) off w) ars' Hwf HR Win1 Win2 Hw Hw8 CELLS ARRS) as [So HR'].
      split; [exact So|]. split; [exact HR'|]. cbn. repeat split; reflexivity.
    - injection H; intros <-.
      assert (CELLS' : Forall (stack_cell_ok U rho (wbytes (ms_mem ms) (w64 (rho SYM_SP0 + off)) (store_bytes w wv)) (rho SYM_SP0)) (cells_store (s_stk st) off w v)).
      { constructor; [|exact CELLS]. unfold stack_cell_ok; cbn [c_off c_w c_val]. split; [lia|]. split; [lia|]. split; [lia|].
        exists (store_bytes w wv). split; [|apply store_bytes_ok; assumption].
        rewrite <- Hlen. apply st_hit; rewrite ?Hlen; lia. }
      assert (ARRS : Forall (arr_ok U rho (wbytes (ms_mem ms) (w64 (rho SYM_SP0 + off)) (store_bytes w wv)) (rho SYM_SP0)) (s_arrs st)).
      { apply Forall_forall. intros b Hb. apply arr_ok_store; rewrite ?Hlen; [lia | lia | exact (proj1 (Forall_forall _ _) (r_arrs _ _ _ _ _ _ HR) b Hb) | | lia | lia].
        destruct (arrs_overlap_lit_false _ _ _ _ Eov Hb); lia. }
      destruct (R_stack_store rho st ms off w wv (cells_store (s_stk st) off w v) (s_arrs st) Hwf HR Win1 Win2 Hw Hw8 CELLS' ARRS) as [So HR'].
      split; [exact So|]. split; [exact HR'|]. cbn. repeat split; reflexivity.
  Qed.

  Lemma store_stack_sym_sound : forall rho st ms off w v wv st',
    wf_state st = true -> R U G M0 rho st ms -> val_ok rho v wv -> aval_below v (s_next st) = true -> 0 < w -> w <= 8 ->
    store_stack_sym U st off w v = Some st' ->
    store_ok segs (ms_mem ms) (w64 (rho SYM_SP0 + evl rho off)) (Z.to_nat w) = true
    /\ R U G M0 rho st' (ms_with_mem ms (wbytes (ms_mem ms) (w64 (rho SYM_SP0 + evl rho off)) (store_bytes w wv)))
    /\ (s_next st' = s_next st /\ s_pc st' = s_pc st /\ s_regs st' = s_regs st /\ s_resv st' = s_resv st).
  Proof.
    intros rho st ms off w v wv st' Hwf HR Hv Hvb Hw Hw8 H.
    pose proof (wf_parts st Hwf) as (_ & _ & _ & _ & _ & _ & Wdisj & W18 & _ & Wad).
    pose proof (R_to_VS _ _ _ HR) as HVS. pose proof (r_sp0 _ _ _ _ _ _ HR) as Hsp0. pose proof (uo_fr U UOK) as Hfr.
    pose proof (length_store_bytes w wv) as Hlen.
    unfold store_stack_sym in H.
    destruct (arrs_touch (s_arrs st) (s_ctx st) off w v) as [ars'|] eqn:Et; [|discriminate].
    destruct (arr_find (s_arrs st) (s_ctx st) off w) as [a0|] eqn:Efind; [|discriminate].
    destruct (in_window U (ar_lo a0) (ar_hi a0 - ar_lo a0)) eqn:Win; [|discriminate]. injection H; intros <-.
    unfold in_window in Win. apply andb_prop in Win as [Win1 Win2]. apply Z.leb_le in Win1. apply Z.leb_le in Win2.
    destruct (arr_find_spec rho _ _ _ _ _ (proj1 HVS) Efind) as (Hina0 & Hlo0 & Hhi0).
    destruct (arrs_touch_ok rho (s_ctx st) (ms_mem ms) (rho SYM_SP0) (s_arrs st) off w v wv ars' (proj1 HVS) Hv Hw Hw8 ltac:(lia) ltac:(lia)
                (r_arrs _ _ _ _ _ _ HR) Wad Et) as [ARRS _].
    assert (CELLS : Forall (stack_cell_ok U rho (wbytes (ms_mem ms) (w64 (rho SYM_SP0 + evl rho off)) (store_bytes w wv)) (rho SYM_SP0)) (s_stk st)).
    { apply Forall_forall. intros c Hc.
      apply stack_cell_ok_store; rewrite ?Hlen; [lia | lia | exact (proj1 (Forall_forall _ _) (r_stk _ _ _ _ _ _ HR) c Hc) | | lia | lia].
      rewrite forallb_forall in Wdisj. specialize (Wdisj c Hc).
      destruct (overlaps (ar_lo a0) (ar_hi a0 - ar_lo a0) (c_off c) (c_w c)) eqn:E.
      { exfalso. assert (X : existsb (fun a => overlaps (ar_lo a) (ar_hi a - ar_lo a) (c_off c) (c_w c)) (s_arrs st) = true)
          by (apply existsb_exists; exists a0; split; [exact Hina0 | exact E]). rewrite X in Wdisj. discriminate. }
      destruct (overlaps_false _ _ _ _ E); lia. }
    destruct (R_stack_store rho st ms (evl rho off) w wv (s_stk st) ars' Hwf HR ltac:(lia) ltac:(lia) Hw Hw8 CELLS ARRS) as [So HR'].
    split; [exact So|]. split; [exact HR'|]. cbn. repeat split; reflexivity.
  Qed.

  Lemma store_abs_sound : forall rho st ms a w v wv st',
    wf_state st = true -> R U G M0 rho st ms -> val_ok rho v wv -> 0 < w -> w <= 8 ->
    store_abs U st a w v = Some st' ->
    store_ok segs (ms_mem ms) (w64 a) (Z.to_nat w) = true
    /\ R U G M0 rho st' (ms_with_mem ms (wbytes (ms_mem ms) (w64 a) (store_bytes w wv)))
    /\ (s_next st' = s_next st /\ s_pc st' = s_pc st /\ s_regs st' = s_regs st /\ s_resv st' = s_resv st).
  Proof.
    intros rho st ms a w v wv st' Hwf HR Hv Hw Hw8 H. unfold store_abs in H.
    destruct (in_ranges a w (ue_rw U)) eqn:Hrw; [|discriminate].
    destruct (aval_lit v) as [z|] eqn:Hz; [|discriminate]. injection H; intros <-.
    destruct (R_abs_store rho st ms a w z v wv Hwf HR Hrw Hw Hw8 Hv Hz) as [So HR'].
    split; [exact So|]. split; [exact HR'|]. cbn. repeat split; reflexivity.
  Qed.

  Lemma do_store_sound : forall rho st ms av wa w v wv st',
    wf_state st = true -> R U G M0 rho st ms ->
    val_ok rho av wa -> aval_below av (s_next st) = true ->
    val_ok rho v wv -> aval_below v (s_next st) = true ->
    0 < w -> w <= 8 ->
    do_store U st av w v = Some st' ->
    store_ok segs (ms_mem ms) wa (Z.to_nat w) = true
    /\ R U G M0 rho st' (ms_with_mem ms (write_to_mem (ms_mem ms) wa (store_bytes w wv)))
    /\ s_next st' = s_next st /\ s_pc st' = s_pc st /\ s_regs st' = s_regs st /\ s_resv st' = s_resv st.
  Proof.
    intros rho st ms av wa w v wv st' Hwf HR Hav Hbel Hv Hvb Hw Hw8 H.
    pose proof (wf_parts st Hwf) as (_ & _ & _ & _ & _ & _ & Wdisj & W18 & _ & Wad).
    pose proof (classify_spec rho av wa (s_next st) Hav Hbel W18) as HC.
    rewrite write_to_mem_wbytes.
    unfold do_store in H.
    destruct (classify av) as [[off|off|off|a]|] eqn:Ecl; try discriminate.
    - subst wa. destruct (store_stack_lit_sound rho st ms off w v wv st' Hwf HR Hv Hvb Hw Hw8 H) as (So & HR' & E). split; [exact So|]. split; [exact HR'|exact E].
    - destruct HC as [-> Hob]. destruct (store_stack_sym_sound rho st ms off w v wv st' Hwf HR Hv Hvb Hw Hw8 H) as (So & HR' & E). split; [exact So|]. split; [exact HR'|exact E].
    - destruct HC as [-> Ha]. destruct (store_abs_sound rho st ms a w v wv st' Hwf HR Hv Hw Hw8 H) as (So & HR' & E). split; [exact So|]. split; [exact HR'|exact E].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma In_filterP : forall {A} (P : A -> Prop) {D : forall x, Decision (P x)} (l : list A) x,
    In x (filter P l) -> In x l /\ P x.
  Proof.
    intros A P D l x H. apply list_elem_of_In in H. apply list_basics.list.list_elem_of_filter in H as [HP Hin].
    split; [apply list_elem_of_In; exact Hin | exact HP].
  Qed.

  Lemma cells_kill_sub : forall cs off w c, In c (cells_kill cs off w) -> In c cs.
  Proof.
    induction cs as [|d r IH]; cbn; intros off w c H; [exact H|].
    destruct (overlaps (c_off d) (c_w d) off w); [right; eapply IH; exact H|].
    destruct H as [H|H]; [left; exact H | right; eapply IH; exact H].
  Qed.

  Lemma declare_array_sound : forall rho st ms lo hi st',
    wf_state st = true -> R U G M0 rho st ms ->
    declare_array U st lo hi = Some st' ->
    R U G M0 rho st' ms /\ s_next st' = s_next st /\ s_pc st' = s_pc st /\ s_regs st' = s_regs st /\ s_resv st' = s_resv st
    /\ s_ctx st' = s_ctx st /\ s_pcache st' = s_pcache st /\ s_pay st' = s_pay st /\ s_abs st' = s_abs st.
  Proof.
    intros rho st ms lo hi st' Hwf HR H. unfold declare_array in H.
    destruct (in_window U lo (hi - lo)) eqn:W; cbn [negb] in H; [|discriminate].
    injection H; intros <-. split; [| cbn; repeat split; reflexivity].
    unfold in_window in W. apply andb_prop in W as [W1 W2]. apply Z.leb_le in W1. apply Z.leb_le in W2.
    destruct HR as [Rglob Rpc Rsvc Rregs Rvs Rstk Rarrs Rwin Rpay Rabs Rresv Rfrm Rframe Rsp0 Ralign Rra Rdata].
    constructor; cbn; try assumption.
    - apply Forall_forall. intros c Hc. apply cells_kill_sub in Hc. exact (proj1 (Forall_forall _ _) Rstk c Hc).
    - constructor.
      + unfold arr_ok; cbn. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
        * intros j Hj. exfalso. revert Hj. unfold evl, lconst; cbn. lia.
        * intros H1. exfalso. revert H1. unfold evl, lconst; cbn. lia.
      + apply Forall_forall. intros a Ha. apply In_filterP in Ha as [Ha _]. exact (proj1 (Forall_forall _ _) Rarrs a Ha).
  Qed.

  Lemma drop_below_sound : forall rho st ms k,
    R U G M0 rho st ms -> R U G M0 rho (drop_below st k) ms.
  Proof.
    intros rho st ms k HR.
    destruct HR as [Rglob Rpc Rsvc Rregs Rvs Rstk Rarrs Rwin Rpay Rabs Rresv Rfrm Rframe Rsp0 Ralign Rra Rdata].
    constructor; cbn; try assumption.
    - unfold cells_drop_below. apply Forall_forall. intros c Hc. apply In_filterP in Hc as [Hc _]. exact (proj1 (Forall_forall _ _) Rstk c Hc).
    - apply Forall_forall. intros a Ha. apply In_filterP in Ha as [Ha _]. exact (proj1 (Forall_forall _ _) Rarrs a Ha).
  Qed.

End WithU.

End LXSM2.
