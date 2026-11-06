(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LaState LaMem LaStep LaCheck LaSem LaWf LaSoundVal LaSoundMem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac clear_ors := repeat match goal with H : context [or] |- _ => clear H end.
Ltac lia_nd := first [ solve [ clear_ors; lia_fast ] | lia_fast ].
#[local] Ltac Lia.lia ::= lia_nd.
Import ListNotations.
Import LXL LAS LAM LAI LAC LASEM LAWF LASV LASM.
Open Scope Z_scope.

Module LASM2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithU.
  Variable U : uenv.
  Variable G : sym -> Z.
  Variable M0 : word -> option byte.
  Variable FS : Z.
  Hypothesis UOK : uenv_ok U.
  Hypothesis SCOK : scells_ok U G M0.   (* [comment removed for export] *)
  Let segs := ue_segs U.

  (* [comment removed for export] *)
  Definition lext (rho : valuation) (st : astate) (rho' : valuation) (st' : astate) : Prop :=
    agree (s_next st) rho rho' /\ (s_next st <= s_next st')%nat /\
    s_pc st' = s_pc st /\ s_regs st' = s_regs st /\ s_stk st' = s_stk st /\ s_arrs st' = s_arrs st /\
    s_abs st' = s_abs st /\ s_resv st' = s_resv st /\ s_pay st' = s_pay st /\
    (forall e, In e (s_pcache st) -> In e (s_pcache st')) /\ s_frames st' = s_frames st.

  #[using="Type"] Lemma lext_of_vext : forall rho st rho' st', vext rho st rho' st' -> lext rho st rho' st'.
  Proof.
    intros rho st rho' st' (A & N & P & Rg & S & Ar & Ab & Rv & D & Pc & Py & Fr). unfold lext.
    repeat split; auto. intros e He. rewrite Pc. exact He.
  Qed.

  (* [comment removed for export] *)
  Definition load_word (w : Z) (sx : bool) (bs : list byte) : word := ldval w sx bs.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma w64_plus : forall a b, (w64 a + w64 b)%bv = w64 (a + b).
  Proof. intros. apply bv_eq. rewrite bv_add_unsigned, !w64_unsigned, bv_wrap64_mod, <- Z.add_mod by lia. reflexivity. Qed.

  #[using="Type"] Lemma w64_succ : forall a, (w64 a + 1)%bv = w64 (a + 1).
  Proof.
    intros. apply bv_eq. rewrite bv_add_unsigned, !w64_unsigned, bv_wrap64_mod.
    change (bv_unsigned (1 : word)) with 1. rewrite <- (Z.mod_small 1 (2 ^ 64)) at 1 by lia. rewrite <- Z.add_mod by lia. reflexivity.
  Qed.

  #[using="Type"] Lemma nat_to_word_w64 : forall k, nat_to_word k = w64 (Z.of_nat k).
  Proof. reflexivity. Qed.

  #[using="Type"] Lemma rdn_w64_S : forall m a n,
    rdn segs m (w64 a) (S n) =
    match (match m (w64 a) with Some b => Some b | None => seg_rom segs (w64 a) end) with
    | Some b => match rdn segs m (w64 (a + 1)) n with Some r => Some (b :: r) | None => None end
    | None => None
    end.
  Proof. intros. cbn [rdn]. rewrite w64_succ. reflexivity. Qed.

  #[using="Type"] Lemma rdn_w64_0 : forall m a, rdn segs m (w64 a) 0 = Some [].
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma window_rdn : forall mem sp0 n a,
    window_ok U mem sp0 -> sp0 - ue_fr U <= a -> a + Z.of_nat n <= sp0 ->
    exists bs, rdn segs mem (w64 a) n = Some bs.
  Proof.
    intros mem sp0 n. induction n as [|n IH]; intros a Hwin Hlo Hhi.
    - exists []. apply rdn_w64_0.
    - rewrite rdn_w64_S. destruct (proj1 Hwin a ltac:(lia)) as [b Hb]. rewrite Hb.
      destruct (IH (a + 1) Hwin ltac:(lia) ltac:(lia)) as [bs Hbs]. rewrite Hbs. eexists; reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma rdn_sub : forall m a n bs i k,
    rdn segs m (w64 a) n = Some bs -> (i + k <= n)%nat ->
    rdn segs m (w64 (a + Z.of_nat i)) k = Some (firstn k (skipn i bs)).
  Proof.
    intros m a n bs i k H Hik.
    pose proof (rdn_skipn segs m n (w64 a) bs i H ltac:(lia)) as H1.
    rewrite nat_to_word_w64, w64_plus in H1.
    exact (rdn_firstn segs m (n - i) _ _ k H1 ltac:(lia)).
  Qed.

  #[using="Type"] Lemma rd1_rdn : forall mem a b, rd1 U mem a = Some b <-> rdn segs mem (w64 a) 1 = Some [b].
  Proof.
    intros. unfold rd1. fold segs. destruct (rdn segs mem (w64 a) 1) as [[|x [|y r]]|] eqn:E; split; intros H; try discriminate; try (injection H; intros; subst; reflexivity);
      exfalso; pose proof (rdn_length segs mem 1%nat _ _ E); discriminate.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma classify_frames_spec : forall rho l wa n fr i0,
    wa = w64 (evl rho l) -> lin_below l n = true -> forallb (frame_wf n) fr = true ->
    match classify_frames fr i0 l with
    | Some (AFrm i off) => exists f, nth_frame fr (i - i0) = Some f /\ (i0 <= i)%nat /\ wa = w64 (64 * rho (f_sym f) + off)
    | Some (AFrmSym i off) => exists f, nth_frame fr (i - i0) = Some f /\ (i0 <= i)%nat /\ wa = w64 (64 * rho (f_sym f) + evl rho off) /\ lin_below off n = true
    | Some (AShFrm i t) => exists f, nth_frame fr (i - i0) = Some f /\ (i0 <= i)%nat /\ wa = w64 (SHB + 8 * rho (f_sym f) + evl rho t) /\ lin_below t n = true
    | Some (AFlag i) => exists f, nth_frame fr (i - i0) = Some f /\ (i0 <= i)%nat /\ wa = w64 (rho (f_flag f))
    | Some _ => False
    | None => True
    end.
  Proof.
    intros rho l wa n fr. induction fr as [|f r IH]; intros i0 Hv Hb HW; [exact I|].
    cbn [classify_frames]. cbn [forallb] in HW. apply andb_prop in HW as [Wf Wr].
    destruct (frame_wf_parts n f Wf) as (S1 & S2 & _).
    destruct (Z.eqb_spec (lcoef (f_sym f) l) 64) as [E64|N64].
    - assert (E : evl rho l = 64 * rho (f_sym f) + evl rho (lsub l (lscale 64 (lvar (f_sym f))))) by (rewrite lsub_sound, lscale_sound, lvar_sound; lia).
      destruct (is_const (lsub l (lscale 64 (lvar (f_sym f))))) as [c|] eqn:K.
      + exists f. rewrite Nat.sub_diag. split; [reflexivity|]. split; [lia|]. rewrite Hv, E, (is_const_sound rho _ c K). reflexivity.
      + exists f. rewrite Nat.sub_diag. split; [reflexivity|]. split; [lia|]. split; [rewrite Hv, E; reflexivity|].
        apply lsub_below; [exact Hb | apply lscale_below; apply lvar_below; exact S1].
    - destruct (Z.eqb_spec (lcoef (f_sym f) l) 8) as [E8|N8].
      + exists f. rewrite Nat.sub_diag. split; [reflexivity|]. split; [lia|]. split.
        * rewrite Hv. f_equal. rewrite laddc_sound, lsub_sound, lscale_sound, lvar_sound. lia.
        * apply laddc_below. apply lsub_below; [exact Hb | apply lscale_below; apply lvar_below; exact S1].
      + destruct (leqb l (lvar (f_flag f))) eqn:EQ.
        * exists f. rewrite Nat.sub_diag. split; [reflexivity|]. split; [lia|]. rewrite Hv, (leqb_eval rho _ _ EQ), lvar_sound. reflexivity.
        * specialize (IH (S i0) Hv Hb Wr).
          destruct (classify_frames r (S i0) l) as [[| | | |i off|i off|i t| | |i]|]; try exact IH;
            destruct IH as (g & Hg & Hle & REST); exists g; (split; [|split; [lia|exact REST]]);
            replace (i - i0)%nat with (S (i - S i0))%nat by lia; cbn [nth_frame]; exact Hg.
  Qed.

  #[using="Type"] Lemma classify_spec : forall rho fr av wa n,
    val_ok rho av wa -> aval_below av n = true -> (NGLOB <= n)%nat -> forallb (frame_wf n) fr = true ->
    match classify fr av with
    | Some (AStk off) => wa = w64 (rho SYM_SP0 + off)
    | Some (AStkSym off) => wa = w64 (rho SYM_SP0 + evl rho off) /\ lin_below off n = true
    | Some (APay off) => wa = w64 (rho SYM_DATA + evl rho off) /\ lin_below off n = true
    | Some (AAbs a) => wa = w64 a /\ 0 <= a < two64z
    | Some (AFrm i off) => exists f, nth_frame fr i = Some f /\ wa = w64 (64 * rho (f_sym f) + off)
    | Some (AFrmSym i off) => exists f, nth_frame fr i = Some f /\ wa = w64 (64 * rho (f_sym f) + evl rho off) /\ lin_below off n = true
    | Some (AShFrm i t) => exists f, nth_frame fr i = Some f /\ wa = w64 (SHB + 8 * rho (f_sym f) + evl rho t) /\ lin_below t n = true
    | Some (AShStk t) => wa = w64 (SHB + 4 * rho SYM_S32 + evl rho t) /\ lin_below t n = true
    | Some (AShPay t) => wa = w64 (SHB + 2 * rho SYM_D16 + evl rho t) /\ lin_below t n = true
    | Some (AFlag i) => exists f, nth_frame fr i = Some f /\ wa = w64 (rho (f_flag f))
    | None => True
    end.
  Proof.
    intros rho fr av wa n Hv Hb Hn HW. unfold classify. destruct av as [|l| |]; try exact I. cbn in Hv, Hb.
    destruct (is_const l) as [c|] eqn:K.
    - split; [|rewrite two64z_eq; apply Z.mod_pos_bound; lia].
      rewrite Hv, (is_const_sound rho l c K). apply w64_eq_mod. rewrite two64z_eq, Z.mod_mod by lia. reflexivity.
    - destruct (Z.eqb (lcoef SYM_SP0 l) 1).
      + destruct (Z.eqb (lcoef SYM_DATA (lsub l (lvar SYM_SP0))) 0); [|exact I].
        assert (E : evl rho l = rho SYM_SP0 + evl rho (lsub l (lvar SYM_SP0))) by (rewrite lsub_sound, lvar_sound; lia).
        destruct (is_const (lsub l (lvar SYM_SP0))) as [c|] eqn:K2.
        * rewrite Hv, E, (is_const_sound rho _ c K2). reflexivity.
        * split; [rewrite Hv, E; reflexivity|]. apply lsub_below; [exact Hb | apply lvar_below; unfold SYM_SP0, NGLOB in *; lia].
      + destruct (Z.eqb (lcoef SYM_DATA l) 1 &&& Z.eqb (lcoef SYM_SP0 l) 0)%bool.
        { split; [rewrite Hv, lsub_sound, lvar_sound; f_equal; lia|].
          apply lsub_below; [exact Hb | apply lvar_below; unfold SYM_DATA, NGLOB in *; lia]. }
        destruct (Z.eqb (lcoef SYM_S32 l) 4).
        { split; [rewrite Hv; f_equal; rewrite laddc_sound, lsub_sound, lscale_sound, lvar_sound; lia|].
          apply laddc_below; apply lsub_below; [exact Hb | apply lscale_below; apply lvar_below; unfold SYM_S32, NGLOB in *; lia]. }
        destruct (Z.eqb (lcoef SYM_D16 l) 2).
        { split; [rewrite Hv; f_equal; rewrite laddc_sound, lsub_sound, lscale_sound, lvar_sound; lia|].
          apply laddc_below; apply lsub_below; [exact Hb | apply lscale_below; apply lvar_below; unfold SYM_D16, NGLOB in *; lia]. }
        pose proof (classify_frames_spec rho l wa n fr 0 Hv Hb HW) as CF.
        destruct (classify_frames fr 0 l) as [[| | | |i off|i off|i t| | |i]|]; try exact CF; try contradiction;
          destruct CF as (f & Hf & _ & REST); exists f; rewrite Nat.sub_0_r in Hf; (split; [exact Hf | exact REST]).
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma bytes_le_cons : forall b r, bytes_le_to_Z (b :: r) = bv_unsigned b + 256 * bytes_le_to_Z r.
  Proof.
    intros b r.
    pose proof (bytes_le_firstn 1 (b :: r) ltac:(cbn; lia)) as H1. cbn [firstn] in H1. rewrite bytes_le_single in H1.
    pose proof (bytes_le_skipn 1 (b :: r) ltac:(cbn; lia)) as H2. replace (skipn 1 (b :: r)) with r in H2 by reflexivity.
    change (2 ^ (8 * Z.of_nat 1)) with 256 in H1, H2.
    pose proof (Z.div_mod (bytes_le_to_Z (b :: r)) 256 ltac:(lia)). lia.
  Qed.

  #[using="Type"] Lemma le_of_bytes_map : forall bs, le_of_bytes (map bv_unsigned bs) = bytes_le_to_Z bs.
  Proof. induction bs as [|b r IH]; [reflexivity|]. cbn [map le_of_bytes]. rewrite bytes_le_cons, IH. reflexivity. Qed.

  #[using="Type"] Lemma bv_signed_byte : forall b : byte, bv_signed b = (if Z.leb (2 ^ 7) (bv_unsigned b) then bv_unsigned b - 2 ^ 8 else bv_unsigned b).
  Proof.
    intros b. unfold bv_signed, bv_swrap. rewrite bv_wrap8_mod. change (bv_half_modulus 8) with 128.
    pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr. change (2 ^ 7) with 128. change (2 ^ 8) with 256.
    destruct (Z.leb_spec 128 (bv_unsigned b)).
    - replace (bv_unsigned b + 128) with ((bv_unsigned b - 128) + 1 * 256) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia.
    - rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="Type"] Lemma ldval_1 : forall sx b, ldval 1 sx [b] = w64 (if sx then bv_signed b else bv_unsigned b).
  Proof.
    intros sx b. rewrite (ldval_ext 1 sx [b]) by (cbn; lia). rewrite bytes_le_single. f_equal.
    unfold ext_lit. change (2 ^ (8 * 1)) with 256. change (2 ^ (8 * 1 - 1)) with (2 ^ 7).
    pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
    rewrite Z.mod_small by lia. destruct sx; [|reflexivity]. rewrite bv_signed_byte. change (2 ^ 8) with 256. reflexivity.
  Qed.

  #[using="Type"] Lemma in_ranges_Z : forall a w rs k, in_ranges a w rs = true -> 0 <= k < w -> in_rangesZ (a + k) rs.
  Proof.
    intros a w rs k H Hk. unfold in_ranges in H. apply existsb_exists in H as (r & Hin & Hr).
    apply andb_prop in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    exists r. split; [exact Hin | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma img_byte_rdn1 : forall mem bm a z,
    abs_ok U mem bm -> in_rangesZ a (ue_ro U) -> img_byte U a = Some z ->
    exists b, (match mem (w64 a) with Some x => Some x | None => seg_rom segs (w64 a) end) = Some b /\ bv_unsigned b = z.
  Proof.
    intros mem bm a z Habs Hro H. unfold img_byte in H. fold segs in H. change (Z_to_bv 64 a) with (w64 a) in H.
    destruct (mem (w64 a)) as [b'|] eqn:Em.
    - pose proof (proj2 (proj2 Habs) a b' Hro Em) as Hmr. fold segs in Hmr. rewrite Hmr in H. injection H; intros <-. exists b'. split; reflexivity.
    - unfold seg_rom. destruct (memory_read segs (w64 a) 1) as [[|b r]|]; try discriminate. injection H; intros <-. exists b. split; reflexivity.
  Qed.

  #[using="Type"] Lemma img_bytes_rdn : forall mem bm n a zs,
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
  #[using="Type"] Lemma abs_bytes_rdn : forall mem bm n a zs,
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
  #[using="Type"] Lemma rows_ok_sound : forall t f n i0 i,
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
  #[using="Type"] Lemma R_pcache_cons : forall rho st ms off sxz x b,
    R U G FS M0 rho st ms ->
    0 <= evl rho off < rho SYM_N ->
    rd1 U (ms_mem ms) (rho SYM_DATA + evl rho off) = Some b ->
    rho x = (if Z.eqb sxz 1 then bv_signed b else bv_unsigned b) ->
    R U G FS M0 rho (set_pcache st ((off, sxz, x) :: s_pcache st)) ms.
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
  #[using="Type"] Lemma VOK_R : forall rho st ms p rho' wv,
    wf_state st = true -> R U G FS M0 rho st ms -> VOK rho st p rho' wv ->
    R U G FS M0 rho' (snd p) ms /\ lext rho st rho' (snd p) /\ val_ok rho' (fst p) wv /\ aval_below (fst p) (s_next (snd p)) = true.
  Proof.
    intros rho st ms p rho' wv Hwf HR (He & HVS & Hv & Hb).
    split; [eapply R_vext; eauto|]. split; [apply lext_of_vext; exact He|]. split; [exact Hv | exact Hb].
  Qed.

  #[using="Type"] Lemma R_to_VS : forall rho st ms, R U G FS M0 rho st ms -> VS rho st.
  Proof. intros rho st ms HR. exact (r_vs _ _ _ _ _ _ _ HR). Qed.

  #[using="Type"] Lemma fresh_unk_VOK : forall rho st bs w sx,
    VS rho st -> 0 < w -> w <= 8 -> Z.of_nat (length bs) = w ->
    exists rho', VOK rho st (fresh_val st (unk_itv sx w)) rho' (ldval w sx bs).
  Proof.
    intros rho st bs w sx HVS Hw Hw8 Hl.
    eapply VOK_fresh; [exact HVS | apply unk_itv_sound; lia | apply ldval_ext; lia].
  Qed.

  #[using="Type"] Lemma cells_find_cover_spec : forall cs off w c,
    cells_find_cover cs off w = Some c -> In c cs /\ c_off c <= off /\ off + w <= c_off c + c_w c.
  Proof.
    induction cs as [|d r IH]; cbn; intros off w c H; [discriminate|].
    destruct (Z.leb (c_off d) off) eqn:E1; [destruct (Z.leb (off + w) (c_off d + c_w d)) eqn:E2|].
    - injection H; intros <-. apply Z.leb_le in E1. apply Z.leb_le in E2. split; [left; reflexivity | lia].
    - destruct (IH _ _ _ H) as [A B]. split; [right; exact A | exact B].
    - destruct (IH _ _ _ H) as [A B]. split; [right; exact A | exact B].
  Qed.

  #[using="Type"] Lemma arr_find_spec : forall rho ars C off w a,
    ctx_ok rho C -> arr_find ars C off w = Some a ->
    In a ars /\ ar_lo a <= evl rho off /\ evl rho off + w <= ar_hi a.
  Proof.
    intros rho ars C off w a HC H. unfold arr_find in H. apply find_some in H as [Hin Hb].
    apply andb_prop in Hb as [H1 H2].
    pose proof (entails_sound rho C _ None HC H1) as E1. pose proof (entails_sound rho C _ None HC H2) as E2.
    rewrite laddc_sound in E1. rewrite laddc_sound, lneg_sound in E2. split; [exact Hin | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma arr_fact_byte_g : forall rho mem b lo hi a f j,
    arr_okg U rho mem b lo hi a -> ar_fact a = Some f -> 0 <= j < evl rho (af_len f) ->
    exists x, rdn segs mem (w64 (b + ar_lo a + j)) 1 = Some [x] /\
              0 <= af_blo f /\ af_blo f <= bv_unsigned x <= af_bhi f /\ af_bhi f <= 127 /\ bv_signed x = bv_unsigned x.
  Proof.
    intros rho mem b lo hi a f j (_ & _ & Hf) Ef Hj. rewrite Ef in Hf. destruct Hf as (Hblo & Hbhi & Haf & _).
    destruct (Haf j Hj) as (_ & x & Hrd & Hb). exists x. apply rd1_rdn in Hrd.
    split; [exact Hrd|]. split; [exact Hblo|]. split; [exact Hb|]. split; [exact Hbhi|].
    rewrite bv_signed_byte. destruct (Z.leb_spec (2 ^ 7) (bv_unsigned x)); [change (2 ^ 7) with 128 in *; lia | reflexivity].
  Qed.
  #[using="Type"] Lemma arr_fact_byte : forall rho mem sp0 a f j,
    arr_ok U rho mem sp0 a -> ar_fact a = Some f -> 0 <= j < evl rho (af_len f) ->
    exists b, rdn segs mem (w64 (sp0 + ar_lo a + j)) 1 = Some [b] /\
              0 <= af_blo f /\ af_blo f <= bv_unsigned b <= af_bhi f /\ af_bhi f <= 127 /\ bv_signed b = bv_unsigned b.
  Proof. intros. eapply arr_fact_byte_g; eauto. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma arr_fact_first_g : forall rho mem b lo hi a f,
    arr_okg U rho mem b lo hi a -> ar_fact a = Some f -> 1 <= evl rho (af_len f) ->
    exists x, rdn segs mem (w64 (b + ar_lo a)) 1 = Some [x] /\ in_itv (bv_unsigned x) (af_first f).
  Proof.
    intros rho mem b lo hi a f (_ & _ & Hf) Ef H1. rewrite Ef in Hf. destruct Hf as (_ & _ & _ & Hfirst).
    destruct (Hfirst H1) as (x & Hrd & Hi). exists x. apply rd1_rdn in Hrd. split; [exact Hrd | exact Hi].
  Qed.
  #[using="Type"] Lemma arr_fact_first : forall rho mem sp0 a f,
    arr_ok U rho mem sp0 a -> ar_fact a = Some f -> 1 <= evl rho (af_len f) ->
    exists b, rdn segs mem (w64 (sp0 + ar_lo a)) 1 = Some [b] /\ in_itv (bv_unsigned b) (af_first f).
  Proof. intros. eapply arr_fact_first_g; eauto. Qed.

  #[using="Type"] Lemma lin_eq_ent_sound : forall rho C a b, ctx_ok rho C -> lin_eq_ent C a b = true -> evl rho a = evl rho b.
  Proof.
    intros rho C a b HC H. unfold lin_eq_ent in H. destruct (leqb a b) eqn:E1; [apply leqb_eval; exact E1|].
    apply andb_prop in H as [A B]. pose proof (entails_sound rho C _ None HC A). pose proof (entails_sound rho C _ None HC B).
    rewrite lsub_sound in H, H0. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fact_byte_VOK : forall rho st (sx is_first : bool) (b : byte) f,
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
  (* [comment removed for export] *)
  Definition space_reads (mem : word -> option byte) (base lo hi : Z) : Prop :=
    forall a n, base + lo <= a -> a + Z.of_nat n <= base + hi -> exists bs, rdn segs mem (w64 a) n = Some bs.

  #[using="Type"] Lemma load_space_lit_sound : forall rho st mem base lo hi cs ars off w sx v st',
    VS rho st -> space_reads mem base lo hi ->
    Forall (cell_ok U rho mem base lo hi) cs -> Forall (arr_okg U rho mem base lo hi) ars ->
    forallb (fun c => aval_below (c_val c) (s_next st)) cs = true ->
    forallb (fun c => (Z.ltb 0 (c_w c) && Z.leb (c_w c) 8)%bool) cs = true ->
    0 < w -> w <= 8 ->
    load_space_lit lo hi cs ars st off w sx = Some (v, st') ->
    exists rho' bs, rdn segs mem (w64 (base + off)) (Z.to_nat w) = Some bs /\ VOK rho st (v, st') rho' (ldval w sx bs).
  Proof.
    intros rho st mem base lo hi cs ars off w sx v st' HVS Hreads Hcs Hars Wcs Wcw Hw Hw8 H.
    unfold load_space_lit in H. destruct (in_win lo hi off w) eqn:Win; cbn [negb] in H; [|discriminate].
    unfold in_win in Win. apply andb_prop in Win as [Win1 Win2]. apply Z.leb_le in Win1. apply Z.leb_le in Win2.
    destruct (Hreads (base + off) (Z.to_nat w) ltac:(lia) ltac:(lia)) as [bs0 Hbs0].
    pose proof (rdn_length segs _ _ _ _ Hbs0) as Hlen0.
    assert (GEN : forall p, (exists rho', VOK rho st p rho' (ldval w sx bs0)) -> Some p = Some (v, st') ->
              exists rho' bs, rdn segs mem (w64 (base + off)) (Z.to_nat w) = Some bs /\ VOK rho st (v, st') rho' (ldval w sx bs)).
    { intros p [rho' HV] E. injection E; intros ->. exists rho', bs0. split; [exact Hbs0 | exact HV]. }
    assert (UNK : Some (fresh_val st (unk_itv sx w)) = Some (v, st') ->
              exists rho' bs, rdn segs mem (w64 (base + off)) (Z.to_nat w) = Some bs /\ VOK rho st (v, st') rho' (ldval w sx bs)).
    { apply GEN. apply fresh_unk_VOK; [exact HVS | lia | lia | lia]. }
    unfold load_cells in H.
    destruct (cells_find_cover cs off w) as [c|] eqn:Ecov.
    - (* [comment removed for export] *)
      destruct (cells_find_cover_spec _ _ _ _ Ecov) as (Hin & Hc1 & Hc2).
      pose proof (proj1 (Forall_forall _ _) Hcs c Hin) as (B1 & B2 & B3 & cbs & Hcbs & Hvb).
      rewrite forallb_forall in Wcs, Wcw. pose proof (Wcs c Hin) as Wc. pose proof (Wcw c Hin) as Wc8. cbn in Wc.
      apply andb_prop in Wc8 as [_ Wc8]. apply Z.leb_le in Wc8.
      destruct (load_from_cell_sound rho st (c_val c) (c_w c) (off - c_off c) w sx cbs HVS Wc Hvb ltac:(lia) Hw ltac:(lia) Wc8) as [rho' HV].
      injection H; intros E. rewrite E in HV.
      exists rho', (firstn (Z.to_nat w) (skipn (Z.to_nat (off - c_off c)) cbs)). split; [|exact HV].
      pose proof (rdn_sub mem (base + c_off c) (Z.to_nat (c_w c)) cbs (Z.to_nat (off - c_off c)) (Z.to_nat w) Hcbs ltac:(lia)) as Hr.
      replace (base + c_off c + Z.of_nat (Z.to_nat (off - c_off c))) with (base + off) in Hr by lia. exact Hr.
    - destruct (cells_any_overlap cs off w); [apply UNK; exact H|].
      destruct (arr_find ars (s_ctx st) (lconst off) w) as [a|] eqn:Efind; [|apply UNK; exact H].
      destruct (arr_find_spec rho _ _ _ _ _ (proj1 HVS) Efind) as (Hina & Hlo & Hhi). rewrite lconst_sound in Hlo, Hhi.
      destruct (ar_fact a) as [f|] eqn:Ef; [|apply UNK; exact H].
      destruct (Z.eqb w 1) eqn:Ew1; [|apply UNK; exact H]. apply Z.eqb_eq in Ew1.
      destruct (entails (s_ctx st) (laddc (lsub (af_len f) (lconst off)) (ar_lo a - 1)) None) eqn:Een; [|apply UNK; exact H].
      pose proof (entails_sound rho _ _ None (proj1 HVS) Een) as Hen. rewrite laddc_sound, lsub_sound, lconst_sound in Hen.
      pose proof (proj1 (Forall_forall _ _) Hars a Hina) as Harr.
      destruct (arr_fact_byte_g rho mem base lo hi a f (off - ar_lo a) Harr Ef ltac:(lia)) as (b & Hrd & Hblo & Hb & Hbhi & Hsb).
      replace (base + ar_lo a + (off - ar_lo a)) with (base + off) in Hrd by lia.
      subst w. change (Z.to_nat 1) with 1%nat in Hbs0. rewrite Hrd in Hbs0. injection Hbs0; intros <-.
      refine (GEN _ _ H). apply fact_byte_VOK; try assumption.
      intros Efirst. apply Z.eqb_eq in Efirst. subst off.
      destruct (arr_fact_first_g rho mem base lo hi a f Harr Ef ltac:(lia)) as (b' & Hrd' & Hi').
      rewrite Hrd in Hrd'. injection Hrd'; intros <-. exact Hi'.
  Qed.

  #[using="Type"] Lemma load_space_sym_sound : forall rho st mem base lo hi ars off w sx v st',
    VS rho st -> space_reads mem base lo hi -> Forall (arr_okg U rho mem base lo hi) ars ->
    0 < w -> w <= 8 ->
    load_space_sym lo hi ars st off w sx = Some (v, st') ->
    exists rho' bs, rdn segs mem (w64 (base + evl rho off)) (Z.to_nat w) = Some bs /\ VOK rho st (v, st') rho' (ldval w sx bs).
  Proof.
    intros rho st mem base lo hi ars off w sx v st' HVS Hreads Hars Hw Hw8 H.
    unfold load_space_sym in H.
    destruct (arr_find ars (s_ctx st) off w) as [a|] eqn:Efind; [|discriminate].
    destruct (arr_find_spec rho _ _ _ _ _ (proj1 HVS) Efind) as (Hina & Hlo & Hhi).
    destruct (in_win lo hi (ar_lo a) (ar_hi a - ar_lo a)) eqn:Win; cbn [negb] in H; [|discriminate].
    unfold in_win in Win. apply andb_prop in Win as [Win1 Win2]. apply Z.leb_le in Win1. apply Z.leb_le in Win2.
    destruct (Hreads (base + evl rho off) (Z.to_nat w) ltac:(lia) ltac:(lia)) as [bs0 Hbs0].
    pose proof (rdn_length segs _ _ _ _ Hbs0) as Hlen0.
    assert (GEN : forall p, (exists rho', VOK rho st p rho' (ldval w sx bs0)) -> Some p = Some (v, st') ->
              exists rho' bs, rdn segs mem (w64 (base + evl rho off)) (Z.to_nat w) = Some bs /\ VOK rho st (v, st') rho' (ldval w sx bs)).
    { intros p [rho' HV] E. injection E; intros ->. exists rho', bs0. split; [exact Hbs0 | exact HV]. }
    assert (UNK : Some (fresh_val st (unk_itv sx w)) = Some (v, st') ->
              exists rho' bs, rdn segs mem (w64 (base + evl rho off)) (Z.to_nat w) = Some bs /\ VOK rho st (v, st') rho' (ldval w sx bs)).
    { apply GEN. apply fresh_unk_VOK; [exact HVS | lia | lia | lia]. }
    destruct (ar_fact a) as [f|] eqn:Ef; [|apply UNK; exact H].
    destruct (Z.eqb w 1) eqn:Ew1; [|apply UNK; exact H]. apply Z.eqb_eq in Ew1.
    destruct (entails (s_ctx st) (laddc (lsub (af_len f) off) (ar_lo a - 1)) None) eqn:Een; [|apply UNK; exact H].
    pose proof (entails_sound rho _ _ None (proj1 HVS) Een) as Hen. rewrite laddc_sound, lsub_sound in Hen.
    pose proof (proj1 (Forall_forall _ _) Hars a Hina) as Harr.
    destruct (arr_fact_byte_g rho mem base lo hi a f (evl rho off - ar_lo a) Harr Ef ltac:(lia)) as (b & Hrd & Hblo & Hb & Hbhi & Hsb).
    replace (base + ar_lo a + (evl rho off - ar_lo a)) with (base + evl rho off) in Hrd by lia.
    subst w. change (Z.to_nat 1) with 1%nat in Hbs0. rewrite Hrd in Hbs0. injection Hbs0; intros <-.
    refine (GEN _ _ H). apply fact_byte_VOK; try assumption.
    intros Efirst. pose proof (lin_eq_ent_sound rho _ _ _ (proj1 HVS) Efirst) as Eo. rewrite lconst_sound in Eo.
    destruct (arr_fact_first_g rho mem base lo hi a f Harr Ef ltac:(lia)) as (b' & Hrd' & Hi').
    rewrite <- Eo, Hrd in Hrd'. injection Hrd'; intros <-. exact Hi'.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma stack_reads : forall mem sp0, window_ok U mem sp0 -> space_reads mem sp0 (- ue_fr U) 0.
  Proof. intros mem sp0 Hwin a n H1 H2. eapply window_rdn; [exact Hwin | lia | lia]. Qed.

  #[using="Type"] Lemma load_stack_lit_sound : forall rho st ms off w sx v st',
    wf_state st = true -> R U G FS M0 rho st ms -> 0 < w -> w <= 8 ->
    load_stack_lit U st off w sx = Some (v, st') ->
    exists rho' bs,
      rdn segs (ms_mem ms) (w64 (rho SYM_SP0 + off)) (Z.to_nat w) = Some bs
      /\ R U G FS M0 rho' st' ms /\ lext rho st rho' st' /\ val_ok rho' v (ldval w sx bs) /\ aval_below v (s_next st') = true.
  Proof.
    intros rho st ms off w sx v st' Hwf HR Hw Hw8 H.
    pose proof (wf_parts st Hwf) as (Wregs & Wctx & Wstk & Warrs & Wpc & Wpay & Wdisj & W18 & Wcw & Wad & Wfr & Wfd & Wfl).
    destruct (load_space_lit_sound rho st (ms_mem ms) (rho SYM_SP0) (- ue_fr U) 0 (s_stk st) (s_arrs st) off w sx v st'
                (R_to_VS _ _ _ HR) (stack_reads _ _ (r_win _ _ _ _ _ _ _ HR)) (r_stk _ _ _ _ _ _ _ HR) (r_arrs _ _ _ _ _ _ _ HR)
                Wstk Wcw Hw Hw8 H) as (rho' & bs & Hrd & HV).
    exists rho', bs. split; [exact Hrd|]. exact (VOK_R rho st ms (v, st') rho' _ Hwf HR HV).
  Qed.

  #[using="Type"] Lemma load_stack_sym_sound : forall rho st ms off w sx v st',
    wf_state st = true -> R U G FS M0 rho st ms -> 0 < w -> w <= 8 ->
    load_stack_sym U st off w sx = Some (v, st') ->
    exists rho' bs,
      rdn segs (ms_mem ms) (w64 (rho SYM_SP0 + evl rho off)) (Z.to_nat w) = Some bs
      /\ R U G FS M0 rho' st' ms /\ lext rho st rho' st' /\ val_ok rho' v (ldval w sx bs) /\ aval_below v (s_next st') = true.
  Proof.
    intros rho st ms off w sx v st' Hwf HR Hw Hw8 H.
    destruct (load_space_sym_sound rho st (ms_mem ms) (rho SYM_SP0) (- ue_fr U) 0 (s_arrs st) off w sx v st'
                (R_to_VS _ _ _ HR) (stack_reads _ _ (r_win _ _ _ _ _ _ _ HR)) (r_arrs _ _ _ _ _ _ _ HR) Hw Hw8 H) as (rho' & bs & Hrd & HV).
    exists rho', bs. split; [exact Hrd|]. exact (VOK_R rho st ms (v, st') rho' _ Hwf HR HV).
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma pcache_find_spec : forall pc off sxz x,
    pcache_find pc off sxz = Some x -> exists o, In (o, sxz, x) pc /\ leqb o off = true.
  Proof.
    induction pc as [|[[o s] y] r IH]; cbn; intros off sxz x H; [discriminate|].
    destruct (leqb o off) eqn:E1.
    - destruct (Z.eqb s sxz) eqn:E2.
      + injection H; intros <-. apply Z.eqb_eq in E2. subst. exists o. split; [left; reflexivity | exact E1].
      + destruct (IH _ _ _ H) as (o' & A & B). exists o'. split; [right; exact A | exact B].
    - destruct (IH _ _ _ H) as (o' & A & B). exists o'. split; [right; exact A | exact B].
  Qed.

  #[using="Type"] Lemma pay_find_spec : forall rho C ps off i,
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

  #[using="Type"] Lemma load_pay_sound : forall rho st ms off sx v st',
    wf_state st = true -> R U G FS M0 rho st ms -> lin_below off (s_next st) = true ->
    load_pay U st off 1 sx = LPOk v st' ->
    exists rho' bs,
      rdn segs (ms_mem ms) (w64 (rho SYM_DATA + evl rho off)) 1 = Some bs
      /\ R U G FS M0 rho' st' ms /\ lext rho st rho' st' /\ val_ok rho' v (ldval 1 sx bs) /\ aval_below v (s_next st') = true.
  Proof.
    intros rho st ms off sx v st' Hwf HR Hoffb H.
    pose proof (wf_parts st Hwf) as (Wregs & Wctx & Wstk & Warrs & Wpc & Wpay & Wdisj & W18 & Wcw & Wad & Wfr & Wfd & Wfl).
    pose proof (R_to_VS _ _ _ HR) as HVS.
    unfold load_pay in H. cbn [Z.eqb Pos.eqb negb] in H.
    destruct (entails (s_ctx st) off None) eqn:E1; [|discriminate].
    destruct (entails (s_ctx st) (laddc (lsub (lvar SYM_N) off) (-1)) None) eqn:E2; [|discriminate]. cbn [negb] in H.
    pose proof (entails_sound rho _ _ None (proj1 HVS) E1) as Hoff1.
    pose proof (entails_sound rho _ _ None (proj1 HVS) E2) as Hoff2. rewrite laddc_sound, lsub_sound, lvar_sound in Hoff2.
    destruct (r_pay _ _ _ _ _ _ _ HR) as (P1 & P2 & P3 & P4).
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
                exists rho' bs, rdn segs (ms_mem ms) (w64 (rho SYM_DATA + evl rho off)) 1 = Some bs /\ R U G FS M0 rho' st' ms /\ lext rho st rho' st'
                                /\ val_ok rho' v (ldval 1 sx bs) /\ aval_below v (s_next st') = true).
      { intros i st1 Hi Ef E. injection E; intros <- <-.
        destruct (fresh_sound rho st i bv HVS Hi) as (rho' & Hx & Hext & HVS1 & _ & Hn1). rewrite Ef in Hext, HVS1, Hn1. cbn [snd] in Hext, HVS1, Hn1.
        pose proof (R_vext U G M0 FS rho st ms rho' st1 Hwf HR Hext HVS1) as HR1.
        destruct Hext as (Hag & Hle & Epc' & Eregs & Estk & Earrs & Eabs & Eresv & Edepth & Epcache & Epay & Eframes).
        assert (Eoff : evl rho' off = evl rho off) by (eapply evl_agree; [exact Hoffb | exact Hag]).
        assert (ED : rho' SYM_DATA = rho SYM_DATA) by (apply Hag; unfold SYM_DATA, NGLOB in *; lia).
        assert (EN : rho' SYM_N = rho SYM_N) by (apply Hag; unfold SYM_N, NGLOB in *; lia).
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
  #[using="Type"] Lemma bm_bytes_rdn : forall mem bm n a zs,
    lits_ok U mem bm -> bm_bytes bm a n = Some zs ->
    exists bs, rdn segs mem (w64 a) n = Some bs /\ map bv_unsigned bs = zs.
  Proof.
    intros mem bm n. induction n as [|n IH]; intros a zs Hl H.
    - cbn in H. injection H; intros <-. exists []. split; [apply rdn_w64_0 | reflexivity].
    - cbn [bm_bytes] in H. destruct (bm_get bm a) as [z|] eqn:Eg; [|discriminate].
      destruct (bm_bytes bm (a + 1) n) as [zr|] eqn:Er; [|discriminate]. injection H; intros <-.
      destruct (Hl a z Eg) as [Hz Hm]. destruct (IH (a + 1) zr Hl Er) as (bs & Hbs & Hmap).
      exists (Z_to_bv 8 z :: bs). rewrite rdn_w64_S. apply rdn_one in Hm. change (ue_segs U) with segs in Hm. rewrite Hm, Hbs. split; [reflexivity|]. cbn [map]. rewrite Hmap. f_equal.
      rewrite Z_to_bv_unsigned. cbn. rewrite bv_wrap_small; [reflexivity|]. cbn. change (bv_modulus 8) with 256. lia.
  Qed.
  #[using="Type"] Lemma lits_ov_rd : forall mem bm, lits_ov mem bm -> lits_ok U mem bm.
  Proof. intros mem bm H a b Hg. destruct (H a b Hg) as [Hb Hm]. split; [exact Hb|]. apply rdn_one. rewrite Hm. reflexivity. Qed.
  #[using="Type"] Lemma bm_bytes_length : forall bm n a zs, bm_bytes bm a n = Some zs -> length zs = n.
  Proof.
    induction n as [|n IH]; cbn [bm_bytes]; intros a zs E.
    - injection E; intros <-; reflexivity.
    - destruct (bm_get bm a); [|discriminate]. destruct (bm_bytes bm (a + 1) n) eqn:E2; [|discriminate]. injection E; intros <-. cbn. f_equal. eapply IH. exact E2.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma lit_result : forall rho st ms bs w sx (a : Z),
    R U G FS M0 rho st ms -> 0 < w -> w <= 8 -> length bs = Z.to_nat w ->
    rdn segs (ms_mem ms) (w64 a) (Z.to_nat w) = Some bs ->
    exists rho' bs', rdn segs (ms_mem ms) (w64 a) (Z.to_nat w) = Some bs' /\ R U G FS M0 rho' st ms /\ lext rho st rho' st
                     /\ val_ok rho' (alit (ext_lit sx w (le_of_bytes (map bv_unsigned bs)))) (ldval w sx bs') /\ aval_below (alit (ext_lit sx w (le_of_bytes (map bv_unsigned bs)))) (s_next st) = true.
  Proof.
    intros rho st ms bs w sx a HR Hw Hw8 Hlen Hrd. exists rho, bs. split; [exact Hrd|]. split; [exact HR|].
    split; [apply lext_of_vext; apply vext_refl|]. split; [|apply alit_below].
    apply alit_ok'. rewrite le_of_bytes_map. apply ldval_ext; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma scell_find_In : forall cs a x, scell_find cs a = Some x -> In (a, x) cs.
  Proof.
    induction cs as [|[b y] r IH]; intros a x H; cbn in H; [discriminate|].
    destruct (Z.eqb_spec a b) as [->|NE]; [injection H; intros <-; left; reflexivity | right; apply IH; exact H].
  Qed.

  #[using="Type"] Lemma rdn_ext_w64 : forall (m m' : word -> option byte) n a,
    (forall k, (k < n)%nat -> m (w64 (a + Z.of_nat k)) = m' (w64 (a + Z.of_nat k))) ->
    rdn segs m (w64 a) n = rdn segs m' (w64 a) n.
  Proof.
    intros m m' n. induction n as [|n IH]; intros a H; [reflexivity|].
    rewrite !rdn_w64_S. pose proof (H 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0. rewrite H0.
    rewrite (IH (a + 1)); [reflexivity|].
    intros k Hk. replace (a + 1 + Z.of_nat k) with (a + Z.of_nat (S k)) by lia. apply H. lia.
  Qed.

  #[using="UOK SCOK"] Lemma scell_rdn : forall rho st ms a x,
    R U G FS M0 rho st ms -> In (a, x) (ue_scells U) ->
    exists bs, rdn segs (ms_mem ms) (w64 a) 8 = Some bs /\ Z.of_nat (length bs) = 8 /\ (bytes_le_to_Z bs) mod 2 ^ 64 = (rho x) mod 2 ^ 64.
  Proof.
    intros rho st ms a x HR Hin.
    destruct (uo_scells U UOK a x Hin) as (Ex & Ha0 & Ha8 & Hnrw).
    destruct (SCOK a x Hin) as (bs & Hrd0 & Hval). exists bs.
    pose proof (fo_lo _ _ (r_fs _ _ _ _ _ _ _ HR)) as FLO. unfold IMGHI_A in FLO.
    assert (Hrd : rdn segs (ms_mem ms) (w64 a) 8 = Some bs).
    { rewrite <- Hrd0. apply rdn_ext_w64. intros k Hk.
      destruct (r_frame _ _ _ _ _ _ _ HR) as [F1 _]. pose proof (r_sp0 _ _ _ _ _ _ _ HR) as SP. apply F1.
      rewrite w64_unsigned, Z.mod_small by lia. unfold priv. intros [P|[P|[P|P]]].
      - lia.
      - apply (Hnrw (Z.of_nat k)); [lia | exact P].
      - lia.
      - unfold sh, SH_A in P. change FS_SHLO with 4608 in P.
        assert (0xcd000 <= FS / 8) by (apply Z.div_le_lower_bound; lia). lia. }
    split; [exact Hrd|]. split; [rewrite (rdn_length segs _ _ _ _ Hrd); reflexivity|].
    rewrite Hval, <- (r_glob _ _ _ _ _ _ _ HR x) by (rewrite Ex; unfold SYM_SC0, NGLOB; lia). reflexivity.
  Qed.

  #[using="UOK SCOK"] Lemma load_abs_sound : forall rho st ms a w sx v st',
    wf_state st = true -> R U G FS M0 rho st ms -> 0 < w -> w <= 8 ->
    load_abs U st a w sx = Some (v, st') ->
    exists rho' bs,
      rdn segs (ms_mem ms) (w64 a) (Z.to_nat w) = Some bs
      /\ R U G FS M0 rho' st' ms /\ lext rho st rho' st' /\ val_ok rho' v (ldval w sx bs) /\ aval_below v (s_next st') = true.
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
      destruct (abs_bytes_rdn (ms_mem ms) (s_abs st) (Z.to_nat w) a zs (r_abs _ _ _ _ _ _ _ HR)
                  ltac:(intros k Hk; eapply in_ranges_Z; [exact Erw | lia]) Eab) as (bs & Hrd & Hmap).
      rewrite <- Hmap. eapply lit_result; eauto. rewrite <- (length_map bv_unsigned), Hmap.
      clear -Eab. revert a zs Eab. induction (Z.to_nat w) as [|n IH]; cbn [abs_bytes]; intros a zs E.
      + injection E; intros <-; reflexivity.
      + destruct (match bm_get (s_abs st) a with Some b => Some b | None => img_byte U a end); [|discriminate].
        destruct (abs_bytes U (s_abs st) (a + 1) n) eqn:E2; [|discriminate]. injection E; intros <-. cbn. f_equal. eapply IH. exact E2.
    - destruct (in_ranges a w (ue_ro U)) eqn:Ero.
      { destruct (img_bytes U a (Z.to_nat w)) as [zs|] eqn:Eib; [|discriminate]. injection H; intros <- <-.
        destruct (img_bytes_rdn (ms_mem ms) (s_abs st) (Z.to_nat w) a zs (r_abs _ _ _ _ _ _ _ HR)
                    ltac:(intros k Hk; eapply in_ranges_Z; [exact Ero | lia]) Eib) as (bs & Hrd & Hmap).
        rewrite <- Hmap. eapply lit_result; eauto. rewrite <- (length_map bv_unsigned), Hmap.
        clear -Eib. revert a zs Eib. induction (Z.to_nat w) as [|n IH]; cbn [img_bytes]; intros a zs E.
        + injection E; intros <-; reflexivity.
        + destruct (img_byte U a); [|discriminate]. destruct (img_bytes U (a + 1) n) eqn:E2; [|discriminate]. injection E; intros <-. cbn. f_equal. eapply IH. exact E2. }
      destruct (bm_bytes (ue_rt U) a (Z.to_nat w)) as [zs|] eqn:Ert.
      { injection H; intros <- <-.
        destruct (bm_bytes_rdn (ms_mem ms) (ue_rt U) (Z.to_nat w) a zs (r_rt _ _ _ _ _ _ _ HR) Ert) as (bs & Hrd & Hmap).
        rewrite <- Hmap. eapply lit_result; eauto. rewrite <- (length_map bv_unsigned), Hmap. eapply bm_bytes_length; exact Ert. }
      destruct (bm_bytes (ue_gsh U) a (Z.to_nat w)) as [zs|] eqn:Egs; [|discriminate].
      injection H; intros <- <-.
      destruct (bm_bytes_rdn (ms_mem ms) (ue_gsh U) (Z.to_nat w) a zs (lits_ov_rd _ _ (r_gsh _ _ _ _ _ _ _ HR)) Egs) as (bs & Hrd & Hmap).
      rewrite <- Hmap. eapply lit_result; eauto. rewrite <- (length_map bv_unsigned), Hmap. eapply bm_bytes_length; exact Egs.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma img_bytes_length : forall n a zs, img_bytes U a n = Some zs -> length zs = n.
  Proof.
    induction n as [|n IH]; cbn [img_bytes]; intros a zs E.
    - injection E; intros <-; reflexivity.
    - destruct (img_byte U a); [|discriminate]. destruct (img_bytes U (a + 1) n) eqn:E2; [|discriminate]. injection E; intros <-. cbn. f_equal. eapply IH. exact E2.
  Qed.

  #[using="Type"] Lemma find_field_sound : forall rho st ms t fs l w sx v st',
    wf_state st = true -> R U G FS M0 rho st ms -> 0 < w -> w <= 8 ->
    table_validb U t = true -> (forall f, In f fs -> In f (tb_fields t)) ->
    lin_below l (s_next st) = true ->
    find_field U st t fs l w sx = Some (v, st') ->
    exists rho' bs,
      rdn segs (ms_mem ms) (w64 (evl rho l)) (Z.to_nat w) = Some bs
      /\ R U G FS M0 rho' st' ms /\ lext rho st rho' st' /\ val_ok rho' v (ldval w sx bs) /\ aval_below v (s_next st') = true.
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
    destruct (img_bytes_rdn (ms_mem ms) (s_abs st) (Z.to_nat w) _ zs (r_abs _ _ _ _ _ _ _ HR) Hro' Eib) as (bs & Hrd & Hmap).
    replace (tb_base t + tb_stride t * i + tf_off f) with (evl rho l) in Hrd by lia.
    assert (Hlen : Z.of_nat (length bs) = w) by (rewrite <- (length_map bv_unsigned), Hmap, (img_bytes_length _ _ _ Eib); lia).
    assert (Hval : ldval w sx bs = w64 (ext_lit sx w (le_of_bytes zs))) by (rewrite <- Hmap, le_of_bytes_map; apply ldval_ext; lia).
    assert (GEN : forall p, (exists rho', VOK rho st p rho' (ldval w sx bs)) -> Some p = Some (v, st') ->
              exists rho' bs0, rdn segs (ms_mem ms) (w64 (evl rho l)) (Z.to_nat w) = Some bs0 /\ R U G FS M0 rho' st' ms /\ lext rho st rho' st'
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

  #[using="UOK"] Lemma find_table_sound : forall rho st ms ts l w sx v st',
    wf_state st = true -> R U G FS M0 rho st ms -> 0 < w -> w <= 8 ->
    (forall t, In t ts -> In t (ue_tabs U)) -> lin_below l (s_next st) = true ->
    find_table U st ts l w sx = Some (v, st') ->
    exists rho' bs,
      rdn segs (ms_mem ms) (w64 (evl rho l)) (Z.to_nat w) = Some bs
      /\ R U G FS M0 rho' st' ms /\ lext rho st rho' st' /\ val_ok rho' v (ldval w sx bs) /\ aval_below v (s_next st') = true.
  Proof.
    intros rho st ms ts l w sx v st' Hwf HR Hw Hw8 Hsub Hl.
    pose proof (uo_tabs U UOK) as HT. unfold tables_validb in HT. rewrite forallb_forall in HT.
    induction ts as [|t r IH]; cbn [find_table]; intros H; [discriminate|].
    destruct (find_field U st t (tb_fields t) l w sx) as [[v1 st1]|] eqn:Ef.
    - injection H; intros <- <-. eapply find_field_sound; eauto. apply HT. apply Hsub. left; reflexivity.
    - apply IH; [intros t' Ht'; apply Hsub; right; exact Ht' | exact H].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fs_consts : FS_LEN = 11571200 /\ FS_FRAMES = 36864 /\ FS_FLAGS = 4096 /\ KHI_A = 0x10007fff8000 /\ HIEND_A = 0x800000000000
                    /\ SH_A = SHB /\ FS_SHLO = 4608 /\ FS_SHHI = 1446400.
  Proof. repeat split; reflexivity. Qed.
  Ltac pow_norm :=
    repeat match goal with
           | |- context [2 ^ ?a] => let v := eval vm_compute in (2 ^ a) in change (2 ^ a) with v
           | H : context [2 ^ ?a] |- _ => let v := eval vm_compute in (2 ^ a) in change (2 ^ a) with v in H
           | |- context [?a / ?b] => let v := eval vm_compute in (a / b) in change (a / b) with v
           end.
  #[using="Type"] Lemma frame_geom : forall k p, (k = 1 \/ k = 4 \/ k = 5) -> 0 <= p < fs_N k ->
    FS + FS_FRAMES <= fs_frame FS k p /\ fs_frame FS k p + fs_fsz k <= FS + FS_LEN /\ 64 <= fs_fsz k <= 2048
    /\ (fs_frame FS k p - FS) mod 64 = 0 /\ fs_fsz k = 2 ^ (6 + k) /\ 8 <= fs_fsz k / 8.
  Proof.
    intros k p Hk Hp. unfold fs_frame, fs_fro, fs_fsz, fs_N, FS_FRAMES, FS_LEN in *.
    destruct Hk as [-> | [-> | ->]]; pow_norm; repeat split; try lia.
    all: apply Z.mod_divide; [lia|]; first [exists (16960 + 2 * p); lia | exists (66112 + 16 * p); lia | exists (82496 + 32 * p); lia].
  Qed.

  #[using="Type"] Lemma w64_same : forall z, LibIfaceA.w64 z = w64 z. Proof. reflexivity. Qed.
  #[using="Type"] Lemma mem_def_rdn : forall mem a n x m, mem_def mem a n -> a <= x -> x + Z.of_nat m <= a + n ->
    exists bs, rdn segs mem (w64 x) m = Some bs.
  Proof.
    intros mem a n x m Hd. revert x. induction m as [|m IH]; intros x H1 H2.
    - exists []. apply rdn_w64_0.
    - rewrite rdn_w64_S. destruct (Hd (x - a) ltac:(lia)) as [b Hb]. replace (a + (x - a)) with x in Hb by lia. rewrite w64_same in Hb. rewrite Hb.
      destruct (IH (x + 1) ltac:(lia) ltac:(lia)) as [bs Hbs]. rewrite Hbs. eexists; reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma frames_nth : forall rho mem frs i f,
    frames_ok U FS rho mem frs -> nth_frame frs i = Some f -> exists p, frame_okR U FS rho mem f p /\ In f frs.
  Proof.
    intros rho mem frs i f ((ps & F2 & _) & _) Hn. revert i Hn. induction F2 as [|g q frs' ps' Hg F2 IH]; intros i Hn; [destruct i; discriminate|].
    destruct i as [|i]; cbn [nth_frame] in Hn.
    - injection Hn; intros <-. exists q. split; [exact Hg | left; reflexivity].
    - destruct (IH i Hn) as (p & Hp & Hin). exists p. split; [exact Hp | right; exact Hin].
  Qed.

  #[using="Type"] Lemma frame_reads : forall rho mem f p, fs_ok FS mem -> frame_okR U FS rho mem f p -> space_reads mem (64 * rho (f_sym f)) 0 (f_size f).
  Proof.
    intros rho mem f p HFS (Hat & Hk & _). destruct Hat as (Hp & Hb & _). intros a n H1 H2.
    pose proof (frame_geom (f_cls f) p Hk Hp) as (G1 & G2 & G3 & _ & G5 & _). unfold f_size in H2. rewrite <- G5 in H2.
    unfold FS_FRAMES, FS_LEN in *.
    eapply (mem_def_rdn mem FS 11571200); [exact (fo_def _ _ HFS) | lia | lia].
  Qed.

  #[using="Type"] Lemma load_frame_lit_sound : forall rho st ms i off w sx v st',
    wf_state st = true -> R U G FS M0 rho st ms -> 0 < w -> w <= 8 ->
    load_frame_lit st i off w sx = Some (v, st') ->
    exists f rho' bs, nth_frame (s_frames st) i = Some f /\
      rdn segs (ms_mem ms) (w64 (64 * rho (f_sym f) + off)) (Z.to_nat w) = Some bs
      /\ R U G FS M0 rho' st' ms /\ lext rho st rho' st' /\ val_ok rho' v (ldval w sx bs) /\ aval_below v (s_next st') = true.
  Proof.
    intros rho st ms i off w sx v st' Hwf HR Hw Hw8 H. unfold load_frame_lit in H.
    destruct (nth_frame (s_frames st) i) as [f|] eqn:Hn; [|discriminate].
    pose proof (wf_parts st Hwf) as (Wregs & Wctx & Wstk & Warrs & Wpc & Wpay & Wdisj & W18 & Wcw & Wad & Wfr & Wfd & Wfl).
    destruct (frames_nth rho (ms_mem ms) (s_frames st) i f (r_frames _ _ _ _ _ _ _ HR) Hn) as (p & Hf & Hin).
    rewrite forallb_forall in Wfr. destruct (frame_wf_parts _ f (Wfr f Hin)) as (_ & _ & _ & _ & _ & Wc & _ & _ & Wcw8 & _).
    destruct Hf as (Hat & Hk & Hcs & Har & Hlen & Hsh).
    destruct (load_space_lit_sound rho st (ms_mem ms) (64 * rho (f_sym f)) 0 (f_size f) (f_cells f) (f_arrs f) off w sx v st'
                (R_to_VS _ _ _ HR) (frame_reads rho (ms_mem ms) f p (r_fs _ _ _ _ _ _ _ HR) (conj Hat (conj Hk (conj Hcs (conj Har (conj Hlen Hsh))))))
                Hcs Har Wc Wcw8 Hw Hw8 H) as (rho' & bs & Hrd & HV).
    exists f, rho', bs. split; [reflexivity|]. split; [exact Hrd|]. exact (VOK_R rho st ms (v, st') rho' _ Hwf HR HV).
  Qed.

  #[using="Type"] Lemma load_frame_sym_sound : forall rho st ms i off w sx v st',
    wf_state st = true -> R U G FS M0 rho st ms -> 0 < w -> w <= 8 ->
    load_frame_sym st i off w sx = Some (v, st') ->
    exists f rho' bs, nth_frame (s_frames st) i = Some f /\
      rdn segs (ms_mem ms) (w64 (64 * rho (f_sym f) + evl rho off)) (Z.to_nat w) = Some bs
      /\ R U G FS M0 rho' st' ms /\ lext rho st rho' st' /\ val_ok rho' v (ldval w sx bs) /\ aval_below v (s_next st') = true.
  Proof.
    intros rho st ms i off w sx v st' Hwf HR Hw Hw8 H. unfold load_frame_sym in H.
    destruct (nth_frame (s_frames st) i) as [f|] eqn:Hn; [|discriminate].
    destruct (frames_nth rho (ms_mem ms) (s_frames st) i f (r_frames _ _ _ _ _ _ _ HR) Hn) as (p & Hf & Hin).
    destruct Hf as (Hat & Hk & Hcs & Har & Hlen & Hsh).
    destruct (load_space_sym_sound rho st (ms_mem ms) (64 * rho (f_sym f)) 0 (f_size f) (f_arrs f) off w sx v st'
                (R_to_VS _ _ _ HR) (frame_reads rho (ms_mem ms) f p (r_fs _ _ _ _ _ _ _ HR) (conj Hat (conj Hk (conj Hcs (conj Har (conj Hlen Hsh))))))
                Har Hw Hw8 H) as (rho' & bs & Hrd & HV).
    exists f, rho', bs. split; [reflexivity|]. split; [exact Hrd|]. exact (VOK_R rho st ms (v, st') rho' _ Hwf HR HV).
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma list_bytes_spec : forall bs t n zs, list_bytes bs t n = Some zs ->
    length zs = n /\ forall k, (k < n)%nat -> nth_error bs (t + k) = nth_error zs k.
  Proof.
    intros bs t n. revert t. induction n as [|n IH]; intros t zs H; cbn [list_bytes] in H.
    - injection H; intros <-. split; [reflexivity | intros k Hk; lia].
    - destruct (nth_error bs t) as [b|] eqn:Eb; [|discriminate]. destruct (list_bytes bs (S t) n) as [r|] eqn:Er; [|discriminate].
      injection H; intros <-. destruct (IH (S t) r Er) as [Hl Hk]. split; [cbn; lia|].
      intros k Hkn. destruct k as [|k]; [rewrite Nat.add_0_r; cbn; exact Eb|]. cbn [nth_error]. rewrite <- Hk by lia. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma shframe_rdn : forall rho mem f p t n zs,
    frame_okR U FS rho mem f p -> list_bytes (f_sh f) t n = Some zs ->
    exists bs, rdn segs mem (w64 (sh (64 * rho (f_sym f)) + Z.of_nat t)) n = Some bs /\ map bv_unsigned bs = zs.
  Proof.
    intros rho mem f p t n zs (Hat & Hk & Hcs & Har & Hlen & Hsh) H. destruct (list_bytes_spec _ _ _ _ H) as [Hl Hnth]. clear H.
    revert t zs Hl Hnth. induction n as [|n IH]; intros t zs Hl Hnth.
    - destruct zs; [|discriminate]. exists []. split; [apply rdn_w64_0 | reflexivity].
    - destruct zs as [|z zr]; [discriminate|]. cbn in Hl.
      pose proof (Hnth 0%nat ltac:(lia)) as H0. rewrite Nat.add_0_r in H0. cbn in H0.
      destruct (Hsh t z H0) as [Hz Hm].
      destruct (IH (S t) zr ltac:(lia) ltac:(intros k Hkk; specialize (Hnth (S k) ltac:(lia)); rewrite Nat.add_succ_r in Hnth; exact Hnth)) as (bs & Hbs & Hmap).
      exists (Z_to_bv 8 z :: bs). rewrite rdn_w64_S, Hm. rewrite Nat2Z.inj_succ in Hbs.
      replace (sh (64 * rho (f_sym f)) + Z.of_nat t + 1) with (sh (64 * rho (f_sym f)) + Z.succ (Z.of_nat t)) by lia. rewrite Hbs.
      split; [reflexivity|]. cbn [map]. rewrite Hmap. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
  Qed.

  #[using="Type"] Lemma list_run_spec : forall bs t n v k, (k < list_run bs t n v)%nat -> nth_error bs (t + k) = Some v.
  Proof.
    intros bs t n. revert t. induction n as [|n IH]; intros t v k Hk; cbn [list_run] in Hk; [lia|].
    destruct (nth_error bs t) as [b|] eqn:Eb; [|lia]. destruct (Z.eqb_spec b v); [|lia]. subst b.
    destruct k as [|k]; [rewrite Nat.add_0_r; exact Eb|]. rewrite Nat.add_succ_r. change (t + S k)%nat with (t + S k)%nat.
    replace (S (t + k))%nat with (S t + k)%nat by lia. apply IH. lia.
  Qed.
  #[using="Type"] Lemma list_run_le : forall bs t n v, (list_run bs t n v <= n)%nat.
  Proof.
    intros bs t n. revert t. induction n as [|n IH]; intros t v; cbn [list_run]; [lia|].
    destruct (nth_error bs t); [|lia]. destruct (Z.eqb _ _); [|lia]. specialize (IH (S t) v). lia.
  Qed.

  #[using="Type"] Lemma load_shframe_sound : forall rho st ms i t wa w sx v st',
    wf_state st = true -> R U G FS M0 rho st ms -> 0 < w -> w <= 8 ->
    (exists f, nth_frame (s_frames st) i = Some f /\ wa = w64 (SHB + 8 * rho (f_sym f) + evl rho t)) -> lin_below t (s_next st) = true ->
    load_shframe st i t w sx = SHOk v st' ->
    exists rho' bs, rdn segs (ms_mem ms) wa (Z.to_nat w) = Some bs
      /\ R U G FS M0 rho' st' ms /\ lext rho st rho' st' /\ val_ok rho' v (ldval w sx bs) /\ aval_below v (s_next st') = true.
  Proof.
    intros rho st ms i t wa w sx v st' Hwf HR Hw Hw8 (f & Hn & Hwa) Htb H. unfold load_shframe in H. rewrite Hn in H.
    destruct (frames_nth rho (ms_mem ms) (s_frames st) i f (r_frames _ _ _ _ _ _ _ HR) Hn) as (p & Hf & Hin).
    pose proof Hf as (Hat & Hk & Hcs & Har & Hlen & Hsh).
    assert (Hsh8 : sh (64 * rho (f_sym f)) = SHB + 8 * rho (f_sym f)).
    { unfold sh. destruct fs_consts as (_ & _ & _ & _ & _ & ESH & _). rewrite ESH. f_equal.
      symmetry. apply Z.div_unique_pos with (r := 0); lia. }
    destruct (is_const t) as [c|] eqn:Kt.
    - destruct (Z.leb 0 c &&& Z.leb (c + w) (f_shn f))%bool eqn:Eb; [|discriminate]. apply andb_prop in Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
      destruct (list_bytes (f_sh f) (Z.to_nat c) (Z.to_nat w)) as [zs|] eqn:Elb; [|discriminate]. injection H; intros <- <-.
      destruct (shframe_rdn rho (ms_mem ms) f p (Z.to_nat c) (Z.to_nat w) zs Hf Elb) as (bs & Hrd & Hmap).
      rewrite Z2Nat.id, Hsh8 in Hrd by lia. rewrite (is_const_sound rho t c Kt) in Hwa. subst wa.
      rewrite <- Hmap. eapply lit_result; eauto. rewrite <- (length_map bv_unsigned), Hmap. exact (proj1 (list_bytes_spec _ _ _ _ Elb)).
    - destruct (Z.eqb w 1) eqn:Ew; cbn [negb] in H; [|discriminate]. apply Z.eqb_eq in Ew. subst w.
      pose proof (lrange_ok rho (s_ctx st) t (proj1 (R_to_VS _ _ _ HR))) as [LO HI].
      destruct (lrange (s_ctx st) t) as [[tlo|] [thi|]]; try discriminate. cbn [ilo ihi] in LO, HI.
      destruct (Z.leb 0 tlo &&& Z.leb tlo thi &&& Z.ltb thi (f_shn f))%bool eqn:Eb; [|discriminate].
      apply andb_prop in Eb as [Eb E3]. apply andb_prop in Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. apply Z.ltb_lt in E3.
      destruct (nth_error (f_sh f) (Z.to_nat tlo)) as [v0|] eqn:Ev0; [|discriminate].
      set (run := list_run (f_sh f) (Z.to_nat tlo) (Z.to_nat (thi - tlo + 1)) v0) in H.
      destruct (Nat.eqb_spec run (Z.to_nat (thi - tlo + 1))) as [Erun|]; [|discriminate]. injection H; intros <- <-.
      (* [comment removed for export] *)
      pose proof (list_run_spec (f_sh f) (Z.to_nat tlo) (Z.to_nat (thi - tlo + 1)) v0 (Z.to_nat (evl rho t - tlo)) ltac:(fold run; rewrite Erun; lia)) as Hnth.
      replace (Z.to_nat tlo + Z.to_nat (evl rho t - tlo))%nat with (Z.to_nat (evl rho t)) in Hnth by lia.
      destruct (shframe_rdn rho (ms_mem ms) f p (Z.to_nat (evl rho t)) 1 [v0] Hf ltac:(cbn [list_bytes]; rewrite Hnth; reflexivity)) as (bs & Hrd & Hmap).
      rewrite Z2Nat.id, Hsh8 in Hrd by lia. subst wa.
      destruct bs as [|b0 [|]]; try discriminate. cbn [map] in Hmap. injection Hmap; intros Hb0.
      exists rho, [b0]. change (Z.to_nat 1) with 1%nat. split; [exact Hrd|]. split; [exact HR|]. split; [apply lext_of_vext; apply vext_refl|].
      split; [|apply alit_below]. apply alit_ok'. rewrite ldval_1. unfold ext_lit. destruct (Hsh _ _ Hnth) as [Hv0 _].
      rewrite <- Hb0. rewrite (Z.mod_small (bv_unsigned b0)) by (change (2 ^ (8 * 1)) with 256; lia).
      destruct sx; [|reflexivity]. rewrite bv_signed_byte. change (2 ^ (8 * 1 - 1)) with (2 ^ 7). change (2 ^ (8 * 1)) with (2 ^ 8).
      destruct (Z.leb (2 ^ 7) (bv_unsigned b0)); reflexivity.
  Qed.

  #[using="Type"] Lemma bytes_le_zero_repeat : forall n, bytes_le_to_Z (repeat (Z_to_bv 8 0) n) = 0.
  Proof. induction n as [|n IH]; [reflexivity|]. cbn [repeat bytes_le_to_Z]. cbn [bytes_le_to_Z] in IH. rewrite IH. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma ent_scaled_sound : forall rho C l, ctx_ok rho C -> ent_scaled C l = true -> 0 <= evl rho l.
  Proof.
    intros rho C l [HF HB] H. unfold ent_scaled in H. apply existsb_exists in H as (f & Hf & H).
    match type of H with (if ?b then _ else _) = true => destruct b; [|discriminate] end.
    apply existsb_exists in H as (k & Hk & H).
    pose proof (itv_nonneg_sound _ _ (litv_sound rho (cb C) (lsub l (lscale k f)) HB) H) as X.
    rewrite lsub_sound, lscale_sound in X. pose proof (proj1 (Forall_forall _ _) HF f Hf) as Y. cbv beta in Y.
    assert (Hk0 : 0 <= k) by (unfold ent_scales in Hk; cbn in Hk; lia). nia.
  Qed.
  #[using="Type"] Lemma entails_sc_sound : forall rho C l, ctx_ok rho C -> entails_sc C l = true -> 0 <= evl rho l.
  Proof.
    intros rho C l HC H. unfold entails_sc in H.
    destruct (entails C l None) eqn:E; [exact (entails_sound rho C l None HC E)|]. exact (ent_scaled_sound rho C l HC H).
  Qed.

  #[using="UOK"] Lemma load_shstack_sound : forall rho st ms t wa w v st',
    wf_state st = true -> R U G FS M0 rho st ms -> 0 < w -> w <= 8 ->
    wa = w64 (SHB + 4 * rho SYM_S32 + evl rho t) -> lin_below t (s_next st) = true ->
    load_shstack U st t w = SHOk v st' ->
    exists rho' bs, rdn segs (ms_mem ms) wa (Z.to_nat w) = Some bs
      /\ R U G FS M0 rho' st' ms /\ lext rho st rho' st' /\ val_ok rho' v (ldval w false bs) /\ aval_below v (s_next st') = true
      /\ (forall sx, ldval w sx bs = ldval w false bs).
  Proof.
    intros rho st ms t wa w v st' Hwf HR Hw Hw8 Hwa Htb H. unfold load_shstack in H.
    match type of H with (if ?b then _ else _) = _ => destruct b eqn:Eb; [|discriminate] end. injection H; intros <- <-.
    apply andb_prop in Eb as [E1 E2]. pose proof (proj1 (R_to_VS _ _ _ HR)) as HC.
    pose proof (entails_sc_sound rho _ _ HC E1) as H1. pose proof (entails_sc_sound rho _ _ HC E2) as H2.
    rewrite laddc_sound, lscale_sound in H1. rewrite lscale_sound, laddc_sound in H2.
    destruct (r_comp _ _ _ _ _ _ _ HR) as (CS & CR & CD). pose proof (uo_sp32 _ UOK) as R32. pose proof (uo_frA _ UOK) as FRA.
    pose proof (r_shstk _ _ _ _ _ _ _ HR) as SS. unfold stack_shadow_ok in SS.
    (* [comment removed for export] *)
    assert (BY : forall j, 0 <= j < w -> (ms_mem ms) (w64 (SHB + 4 * rho SYM_S32 + evl rho t + j)) = Some (Z_to_bv 8 0)).
    { intros j Hj. destruct fs_consts as (_ & _ & _ & _ & _ & ESH & _). rewrite <- ESH.
      replace (SH_A + 4 * rho SYM_S32 + evl rho t + j) with (SH_A + (4 * rho SYM_S32 + evl rho t + j)) by lia. apply SS.
      rewrite FRA in H1. unfold FR_A in *.
      destruct R32 as [R32|R32]; rewrite R32 in *.
      - assert (E1' : rho SYM_SP0 / 8 = 4 * rho SYM_S32) by (rewrite CS; symmetry; apply Z.div_unique_pos with (r := 0); lia).
        assert (E2' : (rho SYM_SP0 - 4096) / 8 = 4 * rho SYM_S32 - 512) by (rewrite CS; symmetry; apply Z.div_unique_pos with (r := 0); lia). lia.
      - assert (E1' : rho SYM_SP0 / 8 = 4 * rho SYM_S32 + 2) by (rewrite CS; symmetry; apply Z.div_unique_pos with (r := 0); lia).
        assert (E2' : (rho SYM_SP0 - 4096) / 8 = 4 * rho SYM_S32 - 510) by (rewrite CS; symmetry; apply Z.div_unique_pos with (r := 0); lia). lia. }
    assert (RD : exists bs, rdn segs (ms_mem ms) wa (Z.to_nat w) = Some bs /\ bs = repeat (Z_to_bv 8 0) (Z.to_nat w)).
    { subst wa. set (base := SHB + 4 * rho SYM_S32 + evl rho t) in *.
      assert (GEN : forall k j, 0 <= j -> j + Z.of_nat k <= w -> rdn segs (ms_mem ms) (w64 (base + j)) k = Some (repeat (Z_to_bv 8 0) k)).
      { induction k as [|k IH]; intros j Hj Hjk; [apply rdn_w64_0|]. rewrite rdn_w64_S, (BY j ltac:(lia)).
        replace (base + j + 1) with (base + (j + 1)) by lia. rewrite (IH (j + 1)) by lia. reflexivity. }
      exists (repeat (Z_to_bv 8 0) (Z.to_nat w)). split; [|reflexivity]. rewrite <- (Z.add_0_r base). apply GEN; lia. }
    destruct RD as (bs & Hrd & Hbs).
    assert (Z0 : bytes_le_to_Z bs = 0).
    { subst bs. apply bytes_le_zero_repeat. }
    assert (LEN : length bs = Z.to_nat w) by (subst bs; apply repeat_length).
    assert (LD : forall sx, ldval w sx bs = w64 0).
    { intros sx. rewrite ldval_ext by lia. rewrite Z0. f_equal. unfold ext_lit. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
      destruct sx; [|reflexivity]. destruct (Z.leb_spec (2 ^ (8 * w - 1)) 0); [|reflexivity]. exfalso. assert (0 < 2 ^ (8 * w - 1)) by (apply Z.pow_pos_nonneg; lia). lia. }
    exists rho, bs. split; [exact Hrd|]. split; [exact HR|]. split; [apply lext_of_vext; apply vext_refl|].
    split; [rewrite LD; apply alit_ok'; reflexivity|]. split; [apply alit_below|]. intros sx. rewrite !LD. reflexivity.
  Qed.

  #[using="Type"] Lemma byte_val_small : forall z sx, 0 <= z < 128 -> ldval 1 sx [Z_to_bv 8 z] = w64 z.
  Proof.
    intros z sx Hz. rewrite ldval_1.
    assert (U8 : bv_unsigned (Z_to_bv 8 z) = z) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 8) with 256; lia).
    destruct sx; [|rewrite U8; reflexivity]. rewrite bv_signed_byte, U8. change (2 ^ 7) with 128. destruct (Z.leb_spec 128 z); [lia | reflexivity].
  Qed.

  #[using="Type"] Lemma load_shpay_sound : forall rho st ms t wa w v st',
    wf_state st = true -> R U G FS M0 rho st ms -> 0 < w -> w <= 8 ->
    wa = w64 (SHB + 2 * rho SYM_D16 + evl rho t) -> lin_below t (s_next st) = true ->
    load_shpay st t w = SHOk v st' ->
    exists rho' bs, rdn segs (ms_mem ms) wa (Z.to_nat w) = Some bs
      /\ R U G FS M0 rho' st' ms /\ lext rho st rho' st' /\ (forall sx, val_ok rho' v (ldval w sx bs)) /\ aval_below v (s_next st') = true.
  Proof.
    intros rho st ms t wa w v st' Hwf HR Hw Hw8 Hwa Htb H. unfold load_shpay in H.
    destruct (Z.eqb w 1) eqn:Ew; cbn [negb] in H; [|discriminate]. apply Z.eqb_eq in Ew. subst w.
    pose proof (proj1 (R_to_VS _ _ _ HR)) as HC.
    match type of H with (if negb ?b then _ else _) = _ => destruct b eqn:Eb; cbn [negb] in H; [|discriminate] end.
    apply andb_prop in Eb as [E1 E2].
    pose proof (entails_sound rho _ _ None HC E1) as H1. pose proof (entails_sound rho _ _ None HC E2) as H2.
    rewrite laddc_sound, lsub_sound, lvar_sound, lscale_sound in H2.
    destruct (r_comp _ _ _ _ _ _ _ HR) as (CS & CR & CD). destruct (r_shpay _ _ _ _ _ _ _ HR) as [P0 P1].
    destruct fs_consts as (_ & _ & _ & _ & _ & ESH & _).
    assert (D8 : rho SYM_DATA / 8 = 2 * rho SYM_D16) by (rewrite CD; symmetry; apply Z.div_unique_pos with (r := 0); lia).
    set (g := evl rho t) in *.
    pose proof (wf_parts st Hwf) as (_ & _ & _ & _ & _ & _ & _ & W18 & _).
    assert (CASES : forall z, (ms_mem ms) wa = Some (Z_to_bv 8 z) -> 0 <= z < 128 -> val_ok rho v (w64 z) -> aval_below v (s_next st) = true -> st' = st ->
              exists rho' bs, rdn segs (ms_mem ms) wa (Z.to_nat 1) = Some bs /\ R U G FS M0 rho' st' ms /\ lext rho st rho' st'
                              /\ (forall sx, val_ok rho' v (ldval 1 sx bs)) /\ aval_below v (s_next st') = true).
    { intros z Hm Hz Hv Hb ->. exists rho, [Z_to_bv 8 z]. change (Z.to_nat 1) with 1%nat. rewrite rdn_one, Hm. split; [reflexivity|].
      split; [exact HR|]. split; [apply lext_of_vext; apply vext_refl|]. split; [|exact Hb]. intros sx. rewrite byte_val_small by exact Hz. exact Hv. }
    destruct (entails (s_ctx st) (laddc (lsub (lvar SYM_N) (lscale 8 t)) (-8)) None) eqn:EF.
    - (* [comment removed for export] *) injection H; intros <- <-.
      pose proof (entails_sound rho _ _ None HC EF) as HF. rewrite laddc_sound, lsub_sound, lvar_sound, lscale_sound in HF. fold g in HF.
      apply (CASES 0); [| lia | apply alit_ok'; reflexivity | apply alit_below | reflexivity].
      subst wa. rewrite <- ESH, <- w64_same. replace (SH_A + 2 * rho SYM_D16 + g) with (SH_A + rho SYM_DATA / 8 + g) by lia. apply P0.
      assert (g + 1 <= rho SYM_N / 8) by (apply Z.div_le_lower_bound; lia). lia.
    - destruct (entails (s_ctx st) (laddc (lsub (lscale 8 t) (lvar SYM_N)) 7) None) eqn:EP; [|discriminate]. injection H; intros <- <-.
      pose proof (entails_sound rho _ _ None HC EP) as HP. rewrite laddc_sound, lsub_sound, lvar_sound, lscale_sound in HP. fold g in HP.
      assert (Hdiv : rho SYM_N / 8 = g) by (symmetry; apply Z.div_unique_pos with (r := rho SYM_N - 8 * g); lia).
      assert (Hmod : rho SYM_N mod 8 = rho SYM_N - 8 * g) by (symmetry; apply Z.mod_unique_pos with (q := g); lia).
      apply (CASES (rho SYM_N - 8 * g)); [| lia | | | reflexivity].
      + subst wa. rewrite <- ESH, <- w64_same. replace (SH_A + 2 * rho SYM_D16 + g) with (SH_A + rho SYM_DATA / 8 + rho SYM_N / 8) by lia.
        rewrite <- Hmod. apply P1. lia.
      + cbn [val_ok]. rewrite lsub_sound, lvar_sound, lscale_sound. reflexivity.
      + cbn [aval_below]. apply lsub_below; [apply lvar_below; unfold SYM_N, NGLOB in *; lia | apply lscale_below; exact Htb].
  Qed.

  #[using="Type"] Lemma bm_const_on_spec : forall bm a n v x, bm_const_on bm a n v = true -> a <= x < a + Z.of_nat n -> bm_get bm x = Some v.
  Proof.
    intros bm a n. revert a. induction n as [|n IH]; intros a v x H Hx; [lia|]. cbn [bm_const_on] in H.
    apply andb_prop in H as [H1 H2]. destruct (Z.eq_dec x a) as [->|Hne].
    - destruct (bm_get bm a); [|discriminate]. apply Z.eqb_eq in H1. subst; reflexivity.
    - apply (IH (a + 1)); [exact H2 | lia].
  Qed.
  #[using="Type"] Lemma load_gsh_sym_sound : forall rho st ms l w sx v st',
    wf_state st = true -> R U G FS M0 rho st ms -> 0 < w -> w <= 8 ->
    load_gsh_sym U st l w sx = SHOk v st' ->
    exists rho' bs, rdn segs (ms_mem ms) (w64 (evl rho l)) (Z.to_nat w) = Some bs
      /\ R U G FS M0 rho' st' ms /\ lext rho st rho' st' /\ val_ok rho' v (ldval w sx bs) /\ aval_below v (s_next st') = true.
  Proof.
    intros rho st ms l w sx v st' Hwf HR Hw Hw8 H. unfold load_gsh_sym in H.
    destruct (Z.eqb w 1) eqn:Ew; cbn [negb] in H; [|discriminate]. apply Z.eqb_eq in Ew. subst w.
    pose proof (lrange2_ok rho (s_ctx st) l (proj1 (R_to_VS _ _ _ HR))) as [LO HI].
    destruct (lrange2 (s_ctx st) l) as [[lo|] [hi|]]; try discriminate. cbn [ilo ihi] in LO, HI.
    destruct (Z.leb lo hi &&& Z.leb (hi - lo) 4096)%bool eqn:Eb; [|discriminate].
    destruct (bm_get (ue_gsh U) lo) as [z|] eqn:Eg; [|discriminate].
    destruct (bm_const_on (ue_gsh U) lo (Z.to_nat (hi - lo + 1)) z) eqn:Ec; [|discriminate]. injection H; intros <- <-.
    pose proof (bm_const_on_spec _ _ _ _ (evl rho l) Ec ltac:(lia)) as Hx.
    destruct (lits_ov_rd _ _ (r_gsh _ _ _ _ _ _ _ HR) (evl rho l) z Hx) as [Hz Hm].
    exists rho, [Z_to_bv 8 z]. change (Z.to_nat 1) with 1%nat. change (ue_segs U) with segs in Hm. rewrite Hm. split; [reflexivity|]. split; [exact HR|].
    split; [apply lext_of_vext; apply vext_refl|]. split; [|apply alit_below]. apply alit_ok'. rewrite ldval_1. unfold ext_lit.
    assert (U8 : bv_unsigned (Z_to_bv 8 z) = z) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 8) with 256; lia).
    rewrite (Z.mod_small z) by (change (2 ^ (8 * 1)) with 256; lia).
    destruct sx; [|rewrite U8; reflexivity]. rewrite bv_signed_byte, U8. change (2 ^ (8 * 1 - 1)) with (2 ^ 7). change (2 ^ (8 * 1)) with (2 ^ 8).
    destruct (Z.leb (2 ^ 7) z); reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="UOK SCOK"] Lemma do_load_sound : forall rho st ms av wa w sx v st',
    wf_state st = true -> R U G FS M0 rho st ms ->
    val_ok rho av wa -> aval_below av (s_next st) = true ->
    0 < w -> w <= 8 ->
    do_load U st av w sx = LDOk v st' ->
    exists rho' bs,
      rdn segs (ms_mem ms) wa (Z.to_nat w) = Some bs
      /\ R U G FS M0 rho' st' ms
      /\ lext rho st rho' st'
      /\ val_ok rho' v (ldval w sx bs)
      /\ aval_below v (s_next st') = true.
  Proof.
    intros rho st ms av wa w sx v st' Hwf HR Hav Hbel Hw Hw8 H.
    pose proof (wf_parts st Hwf) as (_ & _ & _ & _ & _ & _ & _ & W18 & _ & _ & Wfr & _).
    pose proof (classify_spec rho (s_frames st) av wa (s_next st) Hav Hbel W18 Wfr) as HC.
    unfold do_load in H.
    destruct (classify (s_frames st) av) as [[off|off|off|a|i off|i off|i t|t|t|i]|] eqn:Ecl.
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
    - destruct HC as (f & Hf & ->). destruct (load_frame_lit st i off w sx) as [[v1 st1]|] eqn:E; [|discriminate]. injection H; intros <- <-.
      destruct (load_frame_lit_sound rho st ms i off w sx _ _ Hwf HR Hw Hw8 E) as (f' & rho' & bs & Hf' & REST).
      rewrite Hf in Hf'. injection Hf'; intros <-. exists rho', bs. exact REST.
    - destruct HC as (f & Hf & -> & Hob). destruct (load_frame_sym st i off w sx) as [[v1 st1]|] eqn:E; [|discriminate]. injection H; intros <- <-.
      destruct (load_frame_sym_sound rho st ms i off w sx _ _ Hwf HR Hw Hw8 E) as (f' & rho' & bs & Hf' & REST).
      rewrite Hf in Hf'. injection Hf'; intros <-. exists rho', bs. exact REST.
    - destruct HC as (f & Hf & Hwa & Htb). destruct (load_shframe st i t w sx) as [v1 st1|l|] eqn:E; cbn [of_sh] in H; try discriminate. injection H; intros <- <-.
      eapply load_shframe_sound; eauto.
    - destruct HC as [Hwa Htb]. destruct (load_shstack U st t w) as [v1 st1|l|] eqn:E; cbn [of_sh] in H; try discriminate. injection H; intros <- <-.
      destruct (load_shstack_sound rho st ms t wa w _ _ Hwf HR Hw Hw8 Hwa Htb E) as (rho' & bs & A & B & C & D & E' & F').
      exists rho', bs. rewrite (F' sx). split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|exact E'].
    - destruct HC as [Hwa Htb]. destruct (load_shpay st t w) as [v1 st1|l|] eqn:E; cbn [of_sh] in H; try discriminate. injection H; intros <- <-.
      destruct (load_shpay_sound rho st ms t wa w _ _ Hwf HR Hw Hw8 Hwa Htb E) as (rho' & bs & A & B & C & D & E').
      exists rho', bs. split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [apply D|exact E'].
    - discriminate.
    - destruct av as [|l| |]; try discriminate. cbn in Hav, Hbel. subst wa.
      destruct (load_table U st l w sx) as [[v1 st1]|] eqn:E.
      + injection H; intros <- <-. unfold load_table in E. eapply find_table_sound; eauto.
      + destruct (load_gsh_sym U st l w sx) as [v1 st1|l1|] eqn:E2; [| discriminate |].
        * injection H; intros <- <-. eapply load_gsh_sym_sound; eauto.
        * destruct (load_shstack U st (lsub (laddc l (- SHB)) (lscale 4 (lvar SYM_S32))) w) as [v1 st1|l'|] eqn:E3; cbn [of_sh] in H; try discriminate.
          injection H; intros <- <-.
          destruct (load_shstack_sound rho st ms (lsub (laddc l (- SHB)) (lscale 4 (lvar SYM_S32))) (w64 (evl rho l)) w _ _ Hwf HR Hw Hw8
                      ltac:(f_equal; rewrite lsub_sound, laddc_sound, lscale_sound, lvar_sound; lia)
                      ltac:(apply lsub_below; [apply laddc_below; exact Hbel | apply lscale_below; apply lvar_below; unfold SYM_S32, NGLOB in *; lia]) E3)
            as (rho' & bs & A & B & C & D & E' & F').
          exists rho', bs. rewrite (F' sx). split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|exact E'].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma do_load_splitlin_sound : forall rho st av w sx l,
    do_load U st av w sx = LDSplitLin l -> 0 <= evl rho l \/ 0 <= evl rho (laddc (lneg l) (-1)).
  Proof. intros. rewrite laddc_sound, lneg_sound. lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma do_load_split_sound : forall rho st av w sx o p,
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
  #[using="Type"] Lemma w64_unsigned_small : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (w64 a) = a.
  Proof. intros. rewrite w64_unsigned. apply Z.mod_small. lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma wbytes_inside : forall bs m (a : word) k d,
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

  #[using="Type"] Lemma Z_to_le_bytes_nth : forall n z k d, (k < n)%nat ->
    nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
  Proof.
    induction n as [|n IH]; intros z k d Hk; [lia|]. cbn [Z_to_le_bytes]. destruct k as [|k].
    - cbn [nth]. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
    - cbn [nth]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
  Qed.

  #[using="Type"] Lemma Z_to_bv8_mod : forall y, Z_to_bv 8 (y mod 256) = Z_to_bv 8 y.
  Proof. intros. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod. change (2 ^ 8) with 256. apply Z.mod_mod. lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma store_bytes_ok : forall rho v wv w,
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
  #[using="Type"] Lemma bm_get_set : forall bm a b x, bm_get (bm_set bm a b) x = if Z.eqb x a then Some b else bm_get bm x.
  Proof.
    induction bm as [|[y c] r IH]; cbn; intros a b x.
    - destruct (Z.ltb_spec x a), (Z.eqb_spec x a); try reflexivity; lia.
    - destruct (Z.ltb_spec a y).
      + cbn. destruct (Z.ltb_spec x a), (Z.eqb_spec x a), (Z.ltb_spec x y), (Z.eqb_spec x y); try reflexivity; lia.
      + destruct (Z.eqb_spec a y).
        * subst. cbn. destruct (Z.ltb_spec x y), (Z.eqb_spec x y); try reflexivity; lia.
        * cbn. rewrite IH. destruct (Z.ltb_spec x y), (Z.eqb_spec x y), (Z.eqb_spec x a); try reflexivity; lia.
  Qed.

  #[using="Type"] Lemma bm_get_set_bytes : forall n bm a z x,
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

    #[using="bs HA0 HA64"] Lemma wA : bv_unsigned (w64 A) = A.
    Proof. apply w64_unsigned_small. lia. Qed.

    #[using="HA0 HA64 HAn"] Lemma st_out_w : forall x : word, ~ (A <= bv_unsigned x < A + Z.of_nat (length bs)) -> m' x = m x.
    Proof.
      intros x Hx. unfold m'. destruct (Z.lt_ge_cases (bv_unsigned x) A).
      - apply wbytes_below; rewrite wA; lia.
      - apply wbytes_above; rewrite wA; lia.
    Qed.

    #[using="HA0 HA64 HAn"] Lemma st_out : forall x, 0 <= x < 2 ^ 64 -> ~ (A <= x < A + Z.of_nat (length bs)) -> m' (w64 x) = m (w64 x).
    Proof. intros x Hx Hn. apply st_out_w. rewrite w64_unsigned_small by lia. exact Hn. Qed.

    #[using="HA0 HA64 HAn"] Lemma st_hit : rdn segs m' (w64 A) (length bs) = Some bs.
    Proof. unfold m'. apply rdn_wbytes_hit. rewrite wA. lia. Qed.

    #[using="HA0 HA64 HAn"] Lemma st_rdn_out : forall x k, 0 <= x -> x + Z.of_nat k <= 2 ^ 64 ->
      (x + Z.of_nat k <= A \/ A + Z.of_nat (length bs) <= x) -> rdn segs m' (w64 x) k = rdn segs m (w64 x) k.
    Proof.
      intros x k Hx Hxk Hd. unfold m'.
      destruct k as [|k]; [reflexivity|].
      apply rdn_wbytes_out; rewrite ?wA, ?w64_unsigned_small; lia.
    Qed.

    #[using="Type"] Lemma st_grows : forall x b, m x = Some b -> exists b', m' x = Some b'.
    Proof.
      intros x b Hb. destruct (m' x) as [b'|] eqn:E; [exists b'; reflexivity|].
      exfalso. refine (wbytes_grows bs m (w64 A) x _ E). rewrite Hb. discriminate.
    Qed.

    #[using="segs"] Lemma st_rd1_grows : forall x b, rd1 U m x = Some b -> exists b', rd1 U m' x = Some b'.
    Proof.
      intros x b H. apply rd1_rdn in H. cbn [rdn] in H.
      destruct (m (w64 x)) as [b0|] eqn:E0.
      - destruct (st_grows _ _ E0) as [b' Hb']. exists b'. apply rd1_rdn. cbn [rdn]. fold m'. rewrite Hb'. reflexivity.
      - destruct (seg_rom segs (w64 x)) as [b0|] eqn:Es; [|discriminate].
        destruct (m' (w64 x)) as [b'|] eqn:E'.
        + exists b'. apply rd1_rdn. cbn [rdn]. fold m'. rewrite E'. reflexivity.
        + exists b0. apply rd1_rdn. cbn [rdn]. fold m'. rewrite E'. fold segs. rewrite Es. reflexivity.
    Qed.

    #[using="HA0 HA64 HAn"] Lemma st_inside : forall k d, (k < length bs)%nat -> m' (w64 (A + Z.of_nat k)) = Some (nth k bs d).
    Proof.
      intros k d Hk. unfold m'. rewrite <- w64_plus, <- nat_to_word_w64. apply wbytes_inside; [rewrite wA; lia | exact Hk].
    Qed.

    #[using="segs HA0 HA64 HAn"] Lemma st_rd1_inside : forall k d, (k < length bs)%nat -> rd1 U m' (A + Z.of_nat k) = Some (nth k bs d).
    Proof. intros k d Hk. apply rd1_rdn. cbn [rdn]. fold m'. rewrite (st_inside k d Hk). reflexivity. Qed.

    #[using="segs HA0 HA64 HAn"] Lemma st_rd1_out : forall x, 0 <= x -> x + 1 <= 2 ^ 64 -> (x + 1 <= A \/ A + Z.of_nat (length bs) <= x) -> rd1 U m' x = rd1 U m x.
    Proof. intros x Hx Hx1 Hd. unfold rd1. fold segs. fold m'. rewrite (st_rdn_out x 1) by lia. reflexivity. Qed.
  End StoreFacts.


  (* [comment removed for export] *)
  #[using="Type"] Lemma overlaps_false : forall o1 w1 o2 w2, overlaps o1 w1 o2 w2 = false -> o2 + w2 <= o1 \/ o1 + w1 <= o2.
  Proof.
    intros. unfold overlaps in H. destruct (Z.ltb_spec o1 (o2 + w2)); [destruct (Z.ltb_spec o2 (o1 + w1)); [discriminate|]|]; lia.
  Qed.

  #[using="Type"] Lemma cells_kill_spec : forall cs off w c, In c (cells_kill cs off w) -> In c cs /\ overlaps (c_off c) (c_w c) off w = false.
  Proof.
    induction cs as [|d r IH]; cbn; intros off w c H; [destruct H|].
    destruct (overlaps (c_off d) (c_w d) off w) eqn:E.
    - destruct (IH _ _ _ H) as [A B]. split; [right; exact A | exact B].
    - destruct H as [<-|H]; [split; [left; reflexivity | exact E]|]. destruct (IH _ _ _ H) as [A B]. split; [right; exact A | exact B].
  Qed.

  #[using="Type"] Lemma length_store_bytes : forall w wv, length (store_bytes w wv) = Z.to_nat w.
  Proof. intros. unfold store_bytes. apply length_Z_to_le_bytes. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition wr_agree (m m' : word -> option byte) (A n : Z) : Prop :=
    0 <= A /\ A + n <= 2 ^ 64 /\ 0 <= n /\
    (forall x : word, ~ (A <= bv_unsigned x < A + n) -> m' x = m x) /\
    (forall (x : word) b, m x = Some b -> exists b', m' x = Some b').

  #[using="Type"] Lemma wr_out : forall m m' A n x, wr_agree m m' A n -> 0 <= x < 2 ^ 64 -> ~ (A <= x < A + n) -> m' (w64 x) = m (w64 x).
  Proof. intros m m' A n x (HA & HAn & Hn & OUT & GR) Hx Hnot. apply OUT. rewrite w64_unsigned_small by lia. exact Hnot. Qed.
  #[using="Type"] Lemma wr_grows : forall m m' A n x b, wr_agree m m' A n -> m x = Some b -> exists b', m' x = Some b'.
  Proof. intros m m' A n x b (_ & _ & _ & _ & GR). apply GR. Qed.

  #[using="Type"] Lemma wbytes_wr_agree : forall m A bs, 0 <= A -> A < 2 ^ 64 -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
    wr_agree m (wbytes m (w64 A) bs) A (Z.of_nat (length bs)).
  Proof.
    intros m A bs HA HA64 HAn. split; [exact HA|]. split; [exact HAn|]. split; [lia|]. split.
    - intros x Hx. apply (st_out_w m A bs HA HA64 HAn). exact Hx.
    - intros x b Hb. eapply (st_grows m A bs); eauto.
  Qed.

  #[using="Type"] Lemma wr_agree_trans : forall m m' m'' A n A' n' B k,
    wr_agree m m' A n -> wr_agree m' m'' A' n' -> 0 <= B -> B <= A -> B <= A' -> A + n <= B + k -> A' + n' <= B + k -> B + k <= 2 ^ 64 ->
    wr_agree m m'' B k.
  Proof.
    intros m m' m'' A n A' n' B k (HA & HAn & Hn & O1 & G1) (HA' & HAn' & Hn' & O2 & G2) HB H1 H2 H3 H4 H5.
    split; [lia|]. split; [lia|]. split; [lia|]. split.
    - intros x Hx. rewrite O2 by lia. apply O1. lia.
    - intros x b Hb. destruct (G1 x b Hb) as [b' Hb']. apply (G2 x b' Hb').
  Qed.

  #[using="Type"] Lemma rdn_wr_out : forall m m' A n x k, wr_agree m m' A n -> 0 <= x -> x + Z.of_nat k <= 2 ^ 64 ->
    (x + Z.of_nat k <= A \/ A + n <= x) -> rdn segs m' (w64 x) k = rdn segs m (w64 x) k.
  Proof.
    intros m m' A n x k HW. revert x. induction k as [|k IH]; intros x Hx Hxk Hd; [reflexivity|].
    rewrite !rdn_w64_S. rewrite (wr_out m m' A n x HW) by lia. rewrite (IH (x + 1)) by lia. reflexivity.
  Qed.
  #[using="segs"] Lemma rd1_wr_out : forall m m' A n x, wr_agree m m' A n -> 0 <= x -> x + 1 <= 2 ^ 64 -> (x + 1 <= A \/ A + n <= x) ->
    rd1 U m' x = rd1 U m x.
  Proof. intros m m' A n x HW Hx Hx1 Hd. unfold rd1. fold segs. rewrite (rdn_wr_out m m' A n x 1 HW) by lia. reflexivity. Qed.
  #[using="segs"] Lemma rd1_wr_grows : forall m m' A n x b, wr_agree m m' A n -> rd1 U m x = Some b -> exists b', rd1 U m' x = Some b'.
  Proof.
    intros m m' A n x b HW H. apply rd1_rdn in H. cbn [rdn] in H.
    destruct (m (w64 x)) as [b0|] eqn:E0.
    - destruct (wr_grows _ _ _ _ _ _ HW E0) as [b' Hb']. exists b'. apply rd1_rdn. cbn [rdn]. rewrite Hb'. reflexivity.
    - destruct (seg_rom segs (w64 x)) as [b0|] eqn:Es; [|discriminate].
      destruct (m' (w64 x)) as [b'|] eqn:E'.
      + exists b'. apply rd1_rdn. cbn [rdn]. rewrite E'. reflexivity.
      + exists b0. apply rd1_rdn. cbn [rdn]. rewrite E'. fold segs. rewrite Es. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="segs"] Lemma cell_ok_wr : forall rho m m' A n b lo hi c,
    wr_agree m m' A n -> cell_ok U rho m b lo hi c -> 0 <= b + lo -> b + hi <= 2 ^ 64 ->
    (b + c_off c + c_w c <= A \/ A + n <= b + c_off c) -> cell_ok U rho m' b lo hi c.
  Proof.
    intros rho m m' A n b lo hi c HW (C1 & C2 & C3 & cbs & Hrd & Hvb) Hlo Hhi Hd.
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. exists cbs. split; [|exact Hvb].
    rewrite (rdn_wr_out m m' A n) by (try exact HW; lia). exact Hrd.
  Qed.
  #[using="segs"] Lemma arr_okg_wr : forall rho m m' A n b lo hi a,
    wr_agree m m' A n -> arr_okg U rho m b lo hi a -> 0 <= b + lo -> b + hi <= 2 ^ 64 ->
    (b + ar_hi a <= A \/ A + n <= b + ar_lo a) -> arr_okg U rho m' b lo hi a.
  Proof.
    intros rho m m' A n b lo hi a HW (C1 & C2 & C3) Hlo Hhi Hd.
    split; [exact C1|]. split; [exact C2|]. destruct (ar_fact a) as [f|]; [|exact I].
    destruct C3 as (D1 & D2 & D3 & D4). split; [exact D1|]. split; [exact D2|]. split.
    - intros j Hj. destruct (D3 j Hj) as (Hlt & x & Hx & Hr). split; [exact Hlt|]. exists x. split; [|exact Hr].
      rewrite (rd1_wr_out m m' A n) by (try exact HW; lia). exact Hx.
    - intros H1. destruct (D4 H1) as (x & Hx & Hi). destruct (D3 0 ltac:(lia)) as [Hlt0 _]. exists x. split; [|exact Hi].
      rewrite (rd1_wr_out m m' A n) by (try exact HW; lia). exact Hx.
  Qed.
  #[using="segs"] Lemma Forall_cell_ok_wr : forall rho m m' A n b lo hi cs,
    wr_agree m m' A n -> Forall (cell_ok U rho m b lo hi) cs -> 0 <= b + lo -> b + hi <= 2 ^ 64 ->
    (b + hi <= A \/ A + n <= b + lo) -> Forall (cell_ok U rho m' b lo hi) cs.
  Proof.
    intros rho m m' A n b lo hi cs HW H Hlo Hhi Hd. apply Forall_forall. intros c Hc.
    pose proof (proj1 (Forall_forall _ _) H c Hc) as Hcell. pose proof Hcell as (C1 & C2 & _).
    eapply cell_ok_wr; [exact HW | exact Hcell | lia | lia | lia].
  Qed.
  #[using="segs"] Lemma Forall_arr_okg_wr : forall rho m m' A n b lo hi ars,
    wr_agree m m' A n -> Forall (arr_okg U rho m b lo hi) ars -> 0 <= b + lo -> b + hi <= 2 ^ 64 ->
    (b + hi <= A \/ A + n <= b + lo) -> Forall (arr_okg U rho m' b lo hi) ars.
  Proof.
    intros rho m m' A n b lo hi ars HW H Hlo Hhi Hd. apply Forall_forall. intros a Ha.
    pose proof (proj1 (Forall_forall _ _) H a Ha) as Harr. pose proof Harr as (C1 & C2 & _).
    eapply arr_okg_wr; [exact HW | exact Harr | lia | lia | lia].
  Qed.
  #[using="Type"] Lemma window_ok_wr : forall m m' A n sp0, wr_agree m m' A n -> window_ok U m sp0 -> window_ok U m' sp0.
  Proof.
    intros m m' A n sp0 HW [W1 W2]. split; [|exact W2]. intros a Ha. destruct (W1 a Ha) as [b Hb]. eapply wr_grows; [exact HW | exact Hb].
  Qed.
  #[using="segs"] Lemma payload_ok_wr : forall rho m m' A n pc pay,
    wr_agree m m' A n -> payload_ok U rho m pc pay -> 0 <= rho SYM_DATA -> rho SYM_DATA + rho SYM_N <= 2 ^ 62 ->
    (rho SYM_N <= 0 \/ rho SYM_DATA + rho SYM_N <= A \/ A + n <= rho SYM_DATA) -> payload_ok U rho m' pc pay.
  Proof.
    intros rho m m' A n pc pay HW (P1 & P2 & P3 & P4) HD0 HDN Hd. split; [|split; [exact P2 | split]].
    - intros i Hi. destruct (P1 i Hi) as [b Hb]. eapply rd1_wr_grows; [exact HW | exact Hb].
    - intros off sx x Hin. destruct (P3 off sx x Hin) as (Hr & b & Hb & Hx). split; [exact Hr|]. exists b. split; [|exact Hx].
      rewrite (rd1_wr_out m m' A n) by (try exact HW; lia). exact Hb.
    - intros off i Hin. destruct (P4 off i Hin) as (Hr & b & Hb & Hi). split; [exact Hr|]. exists b. split; [|exact Hi].
      rewrite (rd1_wr_out m m' A n) by (try exact HW; lia). exact Hb.
  Qed.
  (* [comment removed for export] *)
  #[using="UOK"] Lemma abs_ok_wr : forall m m' A n bm, wr_agree m m' A n -> abs_ok U m bm -> 0x688000 <= A -> abs_ok U m' bm.
  Proof.
    intros m m' A n bm HW (Q1 & Q2 & Q3) HA. split; [|split].
    - intros a b Hg. destruct (Q1 a b Hg) as (Hrw & Hb & Hm). pose proof (uo_small U UOK a (or_introl Hrw)).
      split; [exact Hrw|]. split; [exact Hb|]. rewrite (wr_out m m' A n) by (try exact HW; lia). exact Hm.
    - intros a Hrw Hg. pose proof (uo_small U UOK a (or_introl Hrw)). rewrite (wr_out m m' A n) by (try exact HW; lia). exact (Q2 a Hrw Hg).
    - intros a b Hro Hm. pose proof (uo_small U UOK a (or_intror Hro)). rewrite (wr_out m m' A n) in Hm by (try exact HW; lia). exact (Q3 a b Hro Hm).
  Qed.
  #[using="UOK segs"] Lemma lits_rt_wr : forall m m' A n, wr_agree m m' A n -> lits_ok U m (ue_rt U) -> 0x688000 <= A -> lits_ok U m' (ue_rt U).
  Proof.
    intros m m' A n HW L HA a b Hg. destruct (L a b Hg) as [Hb Hm]. pose proof (uo_rt_small U UOK a b Hg) as [Ha _].
    split; [exact Hb|]. rewrite (rdn_wr_out m m' A n _ 1 HW) by (cbn; lia). exact Hm.
  Qed.
  #[using="UOK"] Lemma lits_gsh_wr : forall m m' A n, wr_agree m m' A n -> lits_ov m (ue_gsh U) -> (A + n <= 0x7fffa000 \/ 0x800c5000 <= A) -> lits_ov m' (ue_gsh U).
  Proof.
    intros m m' A n HW L HA a b Hg. destruct (L a b Hg) as [Hb Hm]. pose proof (uo_gsh_range U UOK a b Hg) as Ha.
    destruct fs_consts as (_ & _ & _ & _ & _ & ESH & _). rewrite ESH in Ha. unfold SHB in Ha.
    split; [exact Hb|]. rewrite (wr_out m m' A n) by (try exact HW; lia). exact Hm.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma stack_shadow_ok_wr : forall m m' A n sp0, wr_agree m m' A n -> stack_shadow_ok sp0 m ->
    KHI_A <= sp0 - FR_A -> sp0 <= HIEND_A ->
    (SHB + sp0 / 8 <= A \/ A + n <= SHB + (sp0 - FR_A) / 8) -> stack_shadow_ok sp0 m'.
  Proof.
    intros m m' A n sp0 HW SS HK HH Hd g Hg. unfold mem_byte. rewrite w64_same.
    destruct fs_consts as (_ & _ & _ & HKHI & HHI & ESH & _). unfold SHB in *.
    assert (Hg2 : (sp0 - FR_A) / 8 <= g < sp0 / 8) by exact Hg.
    assert (0 <= (sp0 - FR_A) / 8) by (apply Z.div_pos; [rewrite HKHI in HK; lia | lia]).
    assert (sp0 / 8 <= HIEND_A / 8) by (apply Z.div_le_mono; lia). rewrite HHI in *.
    change (0x800000000000 / 8) with 17592186044416 in *.
    rewrite (wr_out m m' A n) by (try exact HW; rewrite ESH; lia). pose proof (SS g Hg) as M. unfold mem_byte in M. rewrite w64_same in M. exact M.
  Qed.
  #[using="Type"] Lemma payload_shadow_ok_wr : forall m m' A n d len, wr_agree m m' A n -> payload_shadow_ok d len m ->
    0 <= d -> (len = 0 \/ d + len <= HIEND_A) -> 0 <= len ->
    (len = 0 \/ SHB + (d + len - 1) / 8 + 1 <= A \/ A + n <= SHB + d / 8) -> payload_shadow_ok d len m'.
  Proof.
    intros m m' A n d len HW [P0 P1] Hd Hdl0 Hl Hdis. destruct fs_consts as (_ & _ & _ & HKHI & HHI & ESH & _). unfold SHB in *.
    destruct (Z.eq_dec len 0) as [->|Hnz].
    { split; [intros g Hg; change (0 / 8) with 0 in Hg; lia | intros Hm; exfalso; apply Hm; reflexivity]. }
    assert (Hdl : d + len <= HIEND_A) by (destruct Hdl0; [lia | assumption]).
    assert (Hdis' : 2147450880 + (d + len - 1) / 8 + 1 <= A \/ A + n <= 2147450880 + d / 8) by (destruct Hdis as [|H]; [lia | exact H]).
    assert (TOP : (d + len - 1) / 8 <= HIEND_A / 8) by (apply Z.div_le_mono; lia). rewrite HHI in TOP. change (0x800000000000 / 8) with 17592186044416 in TOP.
    assert (BOT : 0 <= d / 8) by (apply Z.div_pos; lia).
    pose proof (Z.div_mod d 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound d 8 ltac:(lia)) as MB.
    pose proof (Z.div_mod len 8 ltac:(lia)) as DM2. pose proof (Z.mod_pos_bound len 8 ltac:(lia)) as MB2.
    pose proof (Z.div_mod (d + len - 1) 8 ltac:(lia)) as DM3. pose proof (Z.mod_pos_bound (d + len - 1) 8 ltac:(lia)) as MB3.
    split.
    - intros g Hg. unfold mem_byte. rewrite w64_same.
      assert (d / 8 + g <= (d + len - 1) / 8) by (apply Z.div_le_lower_bound; lia).
      rewrite (wr_out m m' A n) by (try exact HW; rewrite ESH; lia).
      pose proof (P0 g Hg) as M. unfold mem_byte in M. rewrite w64_same in M. exact M.
    - intros Hm. unfold mem_byte. rewrite w64_same.
      assert (d / 8 + len / 8 <= (d + len - 1) / 8) by (apply Z.div_le_lower_bound; lia).
      assert (0 <= len / 8) by (apply Z.div_pos; lia).
      rewrite (wr_out m m' A n) by (try exact HW; rewrite ESH; lia).
      pose proof (P1 Hm) as M. unfold mem_byte in M. rewrite w64_same in M. exact M.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma mem_u64_wr : forall m m' A n a v, wr_agree m m' A n -> mem_u64 m a v -> 0 <= a -> a + 8 <= 2 ^ 64 ->
    (a + 8 <= A \/ A + n <= a) -> mem_u64 m' a v.
  Proof.
    intros m m' A n a v HW H Ha Ha8 Hd i Hi. unfold mem_byte. rewrite w64_same.
    cbn [le_bytes length seq map] in Hi. change (length (le_bytes 8 v)) with 8%nat in Hi.
    rewrite (wr_out m m' A n) by (try exact HW; lia). pose proof (H i Hi) as M. unfold mem_byte in M. rewrite w64_same in M. exact M.
  Qed.
  #[using="Type"] Lemma rdn_wr_out_g : forall sg m m' A n x k, wr_agree m m' A n -> 0 <= x -> x + Z.of_nat k <= 2 ^ 64 ->
    (x + Z.of_nat k <= A \/ A + n <= x) -> rdn sg m' (w64 x) k = rdn sg m (w64 x) k.
  Proof.
    intros sg m m' A n x k HW. revert x. induction k as [|k IH]; intros x Hx Hxk Hd; [reflexivity|].
    cbn [rdn]. rewrite !w64_succ. rewrite (wr_out m m' A n x HW) by lia. rewrite (IH (x + 1)) by lia. reflexivity.
  Qed.
  #[using="Type"] Lemma rd_u64_wr : forall m m' A n a v, wr_agree m m' A n -> rd_u64 m a v -> 0 <= a -> a + 8 <= 2 ^ 64 ->
    (a + 8 <= A \/ A + n <= a) -> rd_u64 m' a v.
  Proof.
    intros m m' A n a v HW (bs & Hrd & Hv) Ha Ha8 Hd. exists bs. split; [|exact Hv].
    change (Z_to_bv 64 a) with (w64 a) in *. rewrite (rdn_wr_out_g SEGS_A m m' A n a 8 HW); [exact Hrd | lia | cbn; lia | cbn; lia].
  Qed.
  #[using="Type"] Lemma mem_byte_wr : forall m m' A n a v, wr_agree m m' A n -> mem_byte m a v -> 0 <= a < 2 ^ 64 ->
    (a + 1 <= A \/ A + n <= a) -> mem_byte m' a v.
  Proof.
    intros m m' A n a v HW H Ha Hd. unfold mem_byte in *. rewrite w64_same in *. rewrite (wr_out m m' A n) by (try exact HW; lia). exact H.
  Qed.
  #[using="Type"] Lemma mem_def_wr : forall m m' A n a k, wr_agree m m' A n -> mem_def m a k -> mem_def m' a k.
  Proof.
    intros m m' A n a k HW H i Hi. destruct (H i Hi) as [b Hb]. rewrite w64_same in *. eapply wr_grows; [exact HW | exact Hb].
  Qed.
  (* [comment removed for export] *)
  Definition wclass (wlo whi A n : Z) : Prop :=
    (wlo <= A /\ A + n <= whi)
    \/ (0x10000 <= A /\ A + n <= 0x666260)          (* [comment removed for export] *)
    \/ (FS + FS_FRAMES <= A /\ A + n <= FS + FS_LEN)
    \/ (FS + FS_FLAGS <= A /\ A + n <= FS + FS_FRAMES)
    \/ (FS + 8 <= A /\ A + n <= FS + 88)
    \/ (sh FS + FS_SHLO <= A /\ A + n <= sh FS + FS_SHHI).
  (* [comment removed for export] *)
  Definition geom_ok (wlo whi : Z) : Prop :=
    KHI_A <= wlo /\ wlo <= whi /\ whi <= HIEND_A /\ (IMGHI_A <= FS /\ app_mem FS FS_LEN) /\ FS + FS_LEN <= HIEND_A /\ FS mod 4096 = 0 /\ (whi <= FS \/ FS + FS_LEN <= wlo).
  (* [comment removed for export] *)
  #[using="Type"] Lemma geom_facts : forall wlo whi, geom_ok wlo whi ->
    0x10007fff8000 <= wlo /\ wlo <= whi /\ whi <= 0x800000000000
    /\ (0x688000 <= FS /\ (FS + 11571200 <= 0x7fff7000 \/ 0x10007fff8000 <= FS)) /\ FS + 11571200 <= 0x800000000000
    /\ (whi <= FS \/ FS + 11571200 <= wlo)
    /\ sh FS = 2147450880 + FS / 8 /\ (0xcd000 <= FS / 8 /\ (FS / 8 + 1446400 <= 0xfffee00 \/ 0x2000ffff000 <= FS / 8))
    /\ FS / 8 + 1446400 <= 0x100000000000 /\ FS = 8 * (FS / 8).
  Proof.
    intros wlo whi (G1 & G2 & G3 & [G4 G4'] & G5 & G6 & G7). destruct fs_consts as (HLEN & _ & _ & HKHI & HHI & ESH & _).
    rewrite HKHI, HHI, HLEN in *. unfold sh, IMGHI_A, app_mem, LOSH_A, KHI_A, FS_LEN in *. rewrite ESH. unfold SHB.
    assert (DFS : exists r, FS = 4096 * r) by (apply Z.mod_divide in G6; [|lia]; destruct G6 as [r Hr]; exists r; lia).
    destruct DFS as [r Hr].
    assert (E : FS / 8 = 512 * r) by (rewrite Hr; replace (4096 * r) with (512 * r * 8) by lia; rewrite Z.div_mul; lia).
    repeat split; try lia. all: rewrite ?E; try lia. all: destruct G7; destruct G4'; lia.
  Qed.

  #[using="Type"] Lemma malloc_ctx_ok_wr : forall m m' A n wlo whi, wr_agree m m' A n -> malloc_ctx_ok wlo whi FS m ->
    geom_ok wlo whi -> wclass wlo whi A n -> malloc_ctx_ok wlo whi FS m'.
  Proof.
    intros m m' A n wlo whi HW (CTX & THR & DT & H1 & H2 & H3 & H4 & H5 & B1 & B2 & B3 & B4 & C1 & C2 & C3) GE Hd.
    pose proof (geom_facts wlo whi GE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    pose proof C1 as D1. pose proof C2 as D2. pose proof C3 as D3.
    unfold ctx_cell_ok, app_mem, LOSH_A, IMGHI_A in D1, D2, D3. rewrite ?HKHI, ?HHI, ?HLEN in D1. rewrite ?HKHI, ?HHI, ?HLEN in D2. rewrite ?HKHI, ?HHI, ?HLEN in D3.
    unfold wclass in Hd. rewrite ?HLEN, ?HFR, ?HFL, ?HSL, ?HSH, F7 in Hd.
    exists CTX, THR, DT. unfold TP_A in *.
    (* [comment removed for export] *)
    split; [eapply rd_u64_wr; [exact HW | exact H1 | clear D1 D2 D3; lia | clear D1 D2 D3; lia | clear D1 D2 D3; lia]|].
    split; [eapply mem_u64_wr; [exact HW | exact H2 | clear D2 D3; lia | clear D2 D3; lia | clear D2 D3; destruct Hd as [Hd|[Hd|[Hd|[Hd|[Hd|Hd]]]]]; lia]|].
    split; [eapply mem_def_wr; [exact HW | exact H3]|].
    split; [eapply rd_u64_wr; [exact HW | exact H4 | clear D1 D2 D3; lia | clear D1 D2 D3; lia | clear D1 D2 D3; lia]|].
    split; [eapply mem_u64_wr; [exact HW | exact H5 | clear D1 D2; lia | clear D1 D2; lia | clear D1 D2; destruct Hd as [Hd|[Hd|[Hd|[Hd|[Hd|Hd]]]]]; lia]|].
    split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
    split; [exact C1|]. split; [exact C2 | exact C3].
  Qed.
  #[using="Type"] Lemma fs_ok_wr : forall m m' A n wlo whi, wr_agree m m' A n -> fs_ok FS m -> geom_ok wlo whi -> wclass wlo whi A n -> fs_ok FS m'.
  Proof.
    intros m m' A n wlo whi HW [T AL LO LOAPP0 HI D SD LG GC] GE Hd.
    pose proof (geom_facts wlo whi GE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    unfold wclass in Hd. rewrite ?HLEN, ?HFR, ?HFL, ?HSL, ?HSH, F7 in Hd. unfold FSTLS_A in *.
    unfold IMGHI_A in LO. unfold app_mem, LOSH_A, KHI_A, FS_LEN in LOAPP0.
    constructor; try assumption.
    - eapply rd_u64_wr; [exact HW | exact T | unfold FSTLS_A; lia | unfold FSTLS_A; lia | unfold FSTLS_A; clear F8 F9 F10; lia].
    - eapply mem_def_wr; [exact HW | exact D].
    - eapply mem_def_wr; [exact HW | exact SD].
    - eapply mem_u64_wr; [exact HW | exact LG | lia | lia | destruct Hd as [Hd|[Hd|[Hd|[Hd|[Hd|Hd]]]]]; lia].
    - eapply mem_byte_wr; [exact HW | exact GC | lia | destruct Hd as [Hd|[Hd|[Hd|[Hd|[Hd|Hd]]]]]; lia].
  Qed.
  #[using="UOK segs"] Lemma lits_rt_wr' : forall m m' A n wlo whi, wr_agree m m' A n -> lits_ok U m (ue_rt U) -> geom_ok wlo whi -> wclass wlo whi A n ->
    (A + n <= 0x666260 -> forall a b, bm_get (ue_rt U) a = Some b -> a + 1 <= A \/ A + n <= a) -> lits_ok U m' (ue_rt U).
  Proof.
    intros m m' A n wlo whi HW L GE Hd Hst a b Hg. destruct (L a b Hg) as [Hb Hm]. pose proof (uo_rt_small U UOK a b Hg) as [Ha _].
    pose proof (geom_facts wlo whi GE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    unfold wclass in Hd. rewrite ?HLEN, ?HFR, ?HFL, ?HSL, ?HSH, F7 in Hd.
    split; [exact Hb|]. rewrite (rdn_wr_out m m' A n _ 1 HW); [exact Hm | lia | cbn; lia |].
    cbn. destruct Hd as [Hd|[Hd|Hd]]; [lia | specialize (Hst (proj2 Hd) a b Hg); lia | lia].
  Qed.
  #[using="UOK"] Lemma lits_gsh_wr' : forall m m' A n wlo whi, wr_agree m m' A n -> lits_ov m (ue_gsh U) -> geom_ok wlo whi -> wclass wlo whi A n ->
    (A + n <= 0x666260 -> forall a b, bm_get (ue_gsh U) a = Some b -> a + 1 <= A \/ A + n <= a) -> lits_ov m' (ue_gsh U).
  Proof.
    intros m m' A n wlo whi HW L GE Hd Hst a b Hg. destruct (L a b Hg) as [Hb Hm]. pose proof (uo_gsh_range U UOK a b Hg) as Ha.
    pose proof (geom_facts wlo whi GE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH). rewrite ESH in Ha. unfold SHB in Ha.
    unfold wclass in Hd. rewrite ?HLEN, ?HFR, ?HFL, ?HSL, ?HSH, F7 in Hd.
    split; [exact Hb|]. rewrite (wr_out m m' A n); [exact Hm | exact HW | lia |].
    destruct Hd as [Hd|[Hd|Hd]]; [lia | specialize (Hst (proj2 Hd) a b Hg); lia | lia].
  Qed.
  #[using="Type"] Lemma frame_ok_wr : forall m m' A n sp0, wr_agree m m' A n -> frame_ok U FS M0 m sp0 ->
    (forall x, A <= x < A + n -> priv U FS sp0 x) -> frame_ok U FS M0 m' sp0.
  Proof.
    intros m m' A n sp0 HW [F1 F2] Hpriv. destruct HW as (HA & HAn & Hn & OUT & GR). split.
    - intros a Hnp. rewrite OUT; [apply F1; exact Hnp|]. intros Hin. apply Hnp. apply Hpriv. exact Hin.
    - intros a b Hb. destruct (F2 a b Hb) as [b' Hb']. apply (GR a b' Hb').
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma sh_frame : forall k p, (k = 1 \/ k = 4 \/ k = 5) -> 0 <= p < fs_N k -> FS mod 4096 = 0 ->
    sh (fs_frame FS k p) = SHB + fs_frame FS k p / 8 /\ sh FS + FS_SHLO <= sh (fs_frame FS k p)
    /\ sh (fs_frame FS k p) + fs_fsz k / 8 <= sh FS + FS_SHHI /\ (fs_frame FS k p) mod 8 = 0
    /\ fs_frame FS k p = 8 * (fs_frame FS k p / 8) /\ fs_fsz k = 8 * (fs_fsz k / 8).
  Proof.
    intros k p Hk Hp HFS. pose proof (frame_geom k p Hk Hp) as (G1 & G2 & G3 & G4 & G5 & G6).
    destruct fs_consts as (HLEN & HFR & _ & _ & _ & ESH & HSL & HSH). unfold sh. rewrite ESH.
    assert (D64 : exists q, fs_frame FS k p - FS = 64 * q) by (apply Z.mod_divide in G4; [|lia]; destruct G4 as [q Hq]; exists q; lia).
    assert (DFS : exists r, FS = 4096 * r) by (apply Z.mod_divide in HFS; [|lia]; destruct HFS as [r Hr]; exists r; lia).
    destruct D64 as [q Hq]. destruct DFS as [r Hr].
    assert (E1 : fs_frame FS k p = 8 * (512 * r + 8 * q)) by lia.
    assert (E2 : fs_frame FS k p / 8 = 512 * r + 8 * q) by (rewrite E1, Z.mul_comm, Z.div_mul; lia).
    assert (E3 : FS / 8 = 512 * r) by (rewrite Hr; replace (4096 * r) with (512 * r * 8) by lia; rewrite Z.div_mul; lia).
    rewrite HFR, HLEN, HSL, HSH in *.
    assert (E5 : exists z, fs_fsz k = 8 * z /\ fs_fsz k / 8 = z).
    { rewrite G5. destruct Hk as [-> | [-> | ->]]; pow_norm; [exists 16 | exists 128 | exists 256]; split; reflexivity. }
    destruct E5 as (z & Ez & Ez8). rewrite Ez8. rewrite E2, E3.
    repeat split; try lia.
    - rewrite E1, Z.mul_comm. apply Z_mod_mult.
  Qed.

  (* [comment removed for export] *)
  Definition frame_untouched (rho : valuation) (A n : Z) (f : frame) : Prop :=
    (64 * rho (f_sym f) + f_size f <= A \/ A + n <= 64 * rho (f_sym f))
    /\ (sh (64 * rho (f_sym f)) + f_shn f <= A \/ A + n <= sh (64 * rho (f_sym f)))
    /\ (rho (f_flag f) + 1 <= A \/ A + n <= rho (f_flag f)).

  #[using="Type"] Lemma nth_error_Some_length' : forall {X} (l : list X) t x, nth_error l t = Some x -> (t < length l)%nat.
  Proof. intros X l t x H. apply (proj1 (nth_error_Some l t)). rewrite H. discriminate. Qed.

  #[using="segs"] Lemma frame_okR_wr : forall rho m m' A n f p, wr_agree m m' A n -> fs_ok FS m -> frame_okR U FS rho m f p ->
    frame_untouched rho A n f -> frame_okR U FS rho m' f p.
  Proof.
    intros rho m m' A n f p HW HFS (Hat & Hk & Hcs & Har & Hlen & Hsh) (U1 & U2 & U3).
    destruct Hat as (Hp & Hb & Hfl). pose proof (frame_geom (f_cls f) p Hk Hp) as (G1 & G2 & G3 & G4 & G5 & G6).
    destruct fs_consts as (HLEN & HFR & _ & HKHI & HHI & ESH & HSL & HSH).
    pose proof (fo_lo _ _ HFS) as LO. pose proof (fo_app _ _ HFS) as LOAPP. pose proof (fo_hi _ _ HFS) as HI. pose proof (fo_align _ _ HFS) as AL.
    pose proof (sh_frame (f_cls f) p Hk Hp AL) as (S1 & S2 & S3 & S4 & S5 & S6).
    unfold IMGHI_A in LO. unfold app_mem, LOSH_A, KHI_A, FS_LEN in LOAPP. rewrite HHI, HLEN in HI. rewrite HFR in G1. rewrite HLEN in G2.
    assert (FSZ : f_size f = fs_fsz (f_cls f)) by (unfold f_size; rewrite G5; reflexivity).
    assert (FSH : f_shn f = fs_fsz (f_cls f) / 8).
    { unfold f_shn. rewrite G5. destruct Hk as [E|[E|E]]; rewrite E; reflexivity. }
    unfold frame_okR. rewrite FSZ, FSH in *. rewrite <- Hb in *.
    split; [split; [exact Hp | split; [exact Hb | exact Hfl]]|]. split; [exact Hk|]. split.
    - eapply Forall_cell_ok_wr; [exact HW | exact Hcs | lia | lia | lia].
    - split.
      + eapply Forall_arr_okg_wr; [exact HW | exact Har | lia | lia | lia].
      + split; [exact Hlen|]. intros t b Ht. destruct (Hsh t b Ht) as [Hb0 Hm]. split; [exact Hb0|].
        assert (Ht' : Z.of_nat t < fs_fsz (f_cls f) / 8).
        { apply nth_error_Some_length' in Ht. lia. }
        rewrite S1 in *. unfold SHB in *.
        rewrite (wr_out m m' A n); [exact Hm | exact HW | lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma f_size_cls : forall f, (f_cls f = 1 \/ f_cls f = 4 \/ f_cls f = 5) -> f_size f = fs_fsz (f_cls f) /\ f_shn f = fs_fsz (f_cls f) / 8.
  Proof. intros f Hk. unfold f_size, f_shn, fs_fsz. destruct Hk as [E|[E|E]]; rewrite E; split; reflexivity. Qed.

  #[using="Type"] Lemma flag_geom : forall k p, (k = 1 \/ k = 4 \/ k = 5) -> 0 <= p < fs_N k ->
    FS + FS_FLAGS <= fs_flag FS k p /\ fs_flag FS k p + 1 <= FS + FS_FRAMES /\ 0 <= fs_flag FS k p - (FS + FS_FLAGS) < 32768.
  Proof.
    intros k p Hk Hp. unfold fs_flag.
    destruct Hk as [-> | [-> | ->]];
    [ change (fs_N 1) with 8192 in Hp; change (fs_flo 1) with 20480
    | change (fs_N 4) with 1024 in Hp; change (fs_flo 4) with 34816
    | change (fs_N 5) with 512 in Hp; change (fs_flo 5) with 35840 ]; unfold FS_FLAGS, FS_FRAMES; lia.
  Qed.

  #[using="Type"] Lemma slot_apart : forall k p k' p', (k = 1 \/ k = 4 \/ k = 5) -> 0 <= p < fs_N k -> (k' = 1 \/ k' = 4 \/ k' = 5) -> 0 <= p' < fs_N k' ->
    (k, p) <> (k', p') ->
    (fs_frame FS k p + fs_fsz k <= fs_frame FS k' p' \/ fs_frame FS k' p' + fs_fsz k' <= fs_frame FS k p)
    /\ fs_flag FS k p <> fs_flag FS k' p'.
  Proof.
    intros k p k' p' Hk Hp Hk' Hp' Hne.
    assert (CASE : k <> k' \/ p <> p').
    { destruct (Z.eq_dec k k') as [E|E]; [right; intros ->; apply Hne; subst; reflexivity | left; exact E]. }
    unfold fs_frame, fs_flag.
    destruct Hk as [-> | [-> | ->]];
    [ change (fs_N 1) with 8192 in Hp; change (fs_flo 1) with 20480; change (fs_fro 1) with 1085440; change (fs_fsz 1) with 128
    | change (fs_N 4) with 1024 in Hp; change (fs_flo 4) with 34816; change (fs_fro 4) with 4231168; change (fs_fsz 4) with 1024
    | change (fs_N 5) with 512 in Hp; change (fs_flo 5) with 35840; change (fs_fro 5) with 5279744; change (fs_fsz 5) with 2048 ];
    (destruct Hk' as [-> | [-> | ->]];
    [ change (fs_N 1) with 8192 in Hp'; change (fs_flo 1) with 20480; change (fs_fro 1) with 1085440; change (fs_fsz 1) with 128
    | change (fs_N 4) with 1024 in Hp'; change (fs_flo 4) with 34816; change (fs_fro 4) with 4231168; change (fs_fsz 4) with 1024
    | change (fs_N 5) with 512 in Hp'; change (fs_flo 5) with 35840; change (fs_fro 5) with 5279744; change (fs_fsz 5) with 2048 ]);
    (split; [|lia]); destruct CASE as [C|C]; try lia.
  Qed.

  #[using="Type"] Lemma sh_apart : forall b s b' s', b = 8 * (b / 8) -> s = 8 * (s / 8) -> b' = 8 * (b' / 8) -> s' = 8 * (s' / 8) ->
    (b + s <= b' \/ b' + s' <= b) -> (sh b + s / 8 <= sh b' \/ sh b' + s' / 8 <= sh b).
  Proof. intros b s b' s' E1 E2 E3 E4 H. unfold sh. lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma nth_frame_error : forall frs i, nth_frame frs i = nth_error frs i.
  Proof. induction frs as [|f r IH]; intros [|i]; cbn; try reflexivity. apply IH. Qed.
  #[using="Type"] Lemma nth_upd_frame : forall frs i g j,
    nth_frame (upd_frame frs i g) j = if Nat.eqb i j then match nth_frame frs j with Some _ => Some g | None => None end else nth_frame frs j.
  Proof.
    induction frs as [|f r IH]; intros [|i] g [|j]; cbn [upd_frame nth_frame Nat.eqb]; try reflexivity.
    - destruct (Nat.eqb i j); reflexivity.
    - apply IH.
  Qed.
  #[using="Type"] Lemma length_upd_frame : forall frs i g, length (upd_frame frs i g) = length frs.
  Proof. induction frs as [|f r IH]; intros [|i] g; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

  #[using="Type"] Lemma Forall2_nth : forall {A B} (P : A -> B -> Prop) l k,
    Forall2 P l k <-> (length l = length k /\ forall i x y, nth_error l i = Some x -> nth_error k i = Some y -> P x y).
  Proof.
    intros A B P l k. split.
    - intros H. induction H as [|x y l' k' Hxy H IH]; [split; [reflexivity | intros [|i] ? ? E; discriminate]|].
      destruct IH as [L IH]. split; [cbn; lia|]. intros [|i] a b Ea Eb; cbn in Ea, Eb; [congruence | eapply IH; eauto].
    - revert k. induction l as [|x l' IH]; intros [|y k'] [L HP]; cbn in L; try discriminate; constructor.
      + apply (HP 0%nat); reflexivity.
      + apply IH. split; [lia|]. intros i a b Ea Eb. apply (HP (S i)); cbn; assumption.
  Qed.
  #[using="Type"] Lemma nth_error_combine : forall {A B} (l : list A) (k : list B) i x y,
    nth_error l i = Some x -> nth_error k i = Some y -> nth_error (combine l k) i = Some (x, y).
  Proof. induction l as [|a l IH]; intros [|b k] [|i] x y Ex Ey; cbn in *; try discriminate; [congruence | eapply IH; eauto]. Qed.
  #[using="Type"] Lemma NoDup_nth_inj : forall {A} (l : list A) i j x, NoDup l -> nth_error l i = Some x -> nth_error l j = Some x -> i = j.
  Proof.
    intros A l. induction l as [|a l IH]; intros i j x ND Ei Ej; [destruct i; discriminate|].
    inversion ND as [|a' l' Hni ND']; subst.
    destruct i as [|i], j as [|j]; cbn in Ei, Ej.
    - reflexivity.
    - exfalso. injection Ei; intros ->. apply Hni. apply list_elem_of_In. eapply nth_error_In; eauto.
    - exfalso. injection Ej; intros ->. apply Hni. apply list_elem_of_In. eapply nth_error_In; eauto.
    - f_equal. eapply IH; eauto.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma frames_slots_ne : forall rho mem frs ps i j f g p q,
    Forall2 (frame_okR U FS rho mem) frs ps -> NoDup (combine (map f_cls frs) ps) ->
    i <> j -> nth_frame frs i = Some f -> nth_error ps i = Some p -> nth_frame frs j = Some g -> nth_error ps j = Some q ->
    (f_cls f, p) <> (f_cls g, q).
  Proof.
    intros rho mem frs ps i j f g p q F2 ND Hij Hf Hp Hg Hq E. rewrite nth_frame_error in Hf, Hg.
    apply Hij. eapply (NoDup_nth_inj _ i j (f_cls f, p) ND).
    - apply nth_error_combine; [rewrite nth_error_map, Hf; reflexivity | exact Hp].
    - rewrite E. apply nth_error_combine; [rewrite nth_error_map, Hg; reflexivity | exact Hq].
  Qed.

  (* [comment removed for export] *)
  Definition fsim (f g : frame) : Prop := f_sym g = f_sym f /\ f_cls g = f_cls f /\ f_flag g = f_flag f.
  #[using="Type"] Lemma live_at_sim : forall rho frs frs' k p, Forall2 fsim frs frs' -> live_at FS rho frs k p <-> live_at FS rho frs' k p.
  Proof.
    intros rho frs frs' k p H. unfold live_at, frame_at. induction H as [|f g frs1 frs2 (E1 & E2 & E3) H IH].
    - split; intros (h & [] & _).
    - split; intros (h & Hin & Hk & Hat).
      + destruct Hin as [<-|Hin].
        * exists g. split; [left; reflexivity|]. rewrite E1, E2, E3. split; [exact Hk | exact Hat].
        * destruct (proj1 IH (ex_intro _ h (conj Hin (conj Hk Hat)))) as (h' & Hin' & R'). exists h'. split; [right; exact Hin' | exact R'].
      + destruct Hin as [<-|Hin].
        * exists f. split; [left; reflexivity|]. rewrite <- E1, <- E2, <- E3. split; [exact Hk | exact Hat].
        * destruct (proj2 IH (ex_intro _ h (conj Hin (conj Hk Hat)))) as (h' & Hin' & R'). exists h'. split; [right; exact Hin' | exact R'].
  Qed.
  #[using="Type"] Lemma map_cls_sim : forall frs frs', Forall2 fsim frs frs' -> map f_cls frs' = map f_cls frs.
  Proof. intros frs frs' H. induction H as [|f g ? ? (E1 & E2 & E3) H IH]; cbn; [reflexivity | rewrite E2, IH; reflexivity]. Qed.
  #[using="Type"] Lemma fsim_refl : forall frs, Forall2 fsim frs frs.
  Proof. induction frs; constructor; [repeat split; reflexivity | assumption]. Qed.
  #[using="Type"] Lemma fsim_upd : forall frs i f g, nth_frame frs i = Some f -> fsim f g -> Forall2 fsim frs (upd_frame frs i g).
  Proof.
    induction frs as [|h r IH]; intros [|i] f g Hn Hs; cbn in Hn; try discriminate; cbn [upd_frame].
    - injection Hn; intros ->. constructor; [exact Hs | apply fsim_refl].
    - constructor; [repeat split; reflexivity | eapply IH; eauto].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="segs"] Lemma frames_ok_wr_apart : forall rho m m' A n frs,
    wr_agree m m' A n -> fs_ok FS m -> frames_ok U FS rho m frs ->
    (A + n <= FS + FS_FLAGS \/ FS + FS_LEN <= A) -> (A + n <= sh FS + FS_SHLO \/ sh FS + FS_SHHI <= A) ->
    frames_ok U FS rho m' frs.
  Proof.
    intros rho m m' A n frs HW HFS ((ps & F2 & ND) & FL & REST) D1 D2.
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    pose proof (fo_lo _ _ HFS) as LO. pose proof (fo_app _ _ HFS) as LOAPP. pose proof (fo_hi _ _ HFS) as HI. unfold IMGHI_A in LO. unfold app_mem, LOSH_A, KHI_A, FS_LEN in LOAPP. rewrite HHI, HLEN in HI. rewrite HLEN, HFL in D1.
    pose proof HW as (WA & WAn & Wn & _).
    split; [|split].
    - exists ps. split; [|exact ND]. clear ND FL REST.
      induction F2 as [|f p frs' ps' Hf F2 IH]; constructor; [|exact IH].
      eapply frame_okR_wr; [exact HW | exact HFS | exact Hf |].
      destruct Hf as ((Hp & Hb & Hfl) & Hk & _).
      pose proof (frame_geom (f_cls f) p Hk Hp) as (G1 & G2 & _). rewrite HFR in G1. rewrite HLEN in G2.
      pose proof (sh_frame (f_cls f) p Hk Hp (fo_align _ _ HFS)) as (S1 & S2 & S3 & _).
      pose proof (flag_geom (f_cls f) p Hk Hp) as (L1 & L2 & _). rewrite HFL in L1. rewrite HFR in L2.
      destruct (f_size_cls f Hk) as [E1 E2]. unfold frame_untouched. rewrite E1, E2, Hb, Hfl. lia.
    - intros k p Hk Hp. pose proof (flag_geom k p Hk Hp) as (L1 & L2 & _). rewrite HFL in L1. rewrite HFR in L2.
      destruct (FL k p Hk Hp) as [X1 X2].
      split; intros HL; (eapply mem_byte_wr; [exact HW | | lia | lia]); [apply X1; exact HL | apply X2; exact HL].
    - intros j Hj Hnf. eapply mem_byte_wr; [exact HW | apply REST; [exact Hj | exact Hnf] | rewrite HFL; lia | rewrite HFL; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma frames_ok_rebuild : forall rho m m' frs frs',
    frames_ok U FS rho m frs -> Forall2 fsim frs frs' ->
    (forall ps, Forall2 (frame_okR U FS rho m) frs ps -> NoDup (combine (map f_cls frs) ps) -> Forall2 (frame_okR U FS rho m') frs' ps) ->
    (forall j, 0 <= j < 32768 -> m' (w64 (FS + FS_FLAGS + j)) = m (w64 (FS + FS_FLAGS + j))) ->
    frames_ok U FS rho m' frs'.
  Proof.
    intros rho m m' frs frs' ((ps & F2 & ND) & FL & REST) SIM NEW FLG. split; [|split].
    - exists ps. split; [apply NEW; [exact F2 | exact ND]|]. rewrite (map_cls_sim frs frs' SIM). exact ND.
    - intros k p Hk Hp. destruct (FL k p Hk Hp) as [X1 X2]. pose proof (flag_geom k p Hk Hp) as (_ & _ & L3).
      assert (E : m' (LibIfaceA.w64 (fs_flag FS k p)) = m (LibIfaceA.w64 (fs_flag FS k p))).
      { rewrite !w64_same. replace (fs_flag FS k p) with (FS + FS_FLAGS + (fs_flag FS k p - (FS + FS_FLAGS))) by lia. apply FLG. lia. }
      unfold mem_byte. rewrite E.
      split; intros HL; [apply X1 | apply X2].
      + apply (proj2 (live_at_sim rho frs frs' k p SIM)). exact HL.
      + intros HL'. apply HL. apply (proj1 (live_at_sim rho frs frs' k p SIM)). exact HL'.
    - intros j Hj Hnf. unfold mem_byte. rewrite w64_same. rewrite FLG by exact Hj.
      pose proof (REST j Hj Hnf) as M. unfold mem_byte in M. rewrite w64_same in M. exact M.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma wclass_shadow : forall wlo whi A n, geom_ok wlo whi -> wclass wlo whi A n -> 0 <= n ->
    (SHB + whi / 8 <= A \/ A + n <= SHB + wlo / 8).
  Proof.
    intros wlo whi A n GE Hd Hn. pose proof (geom_facts wlo whi GE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    unfold wclass in Hd. rewrite ?HLEN, ?HFR, ?HFL, ?HSL, ?HSH, F7 in Hd. unfold SHB.
    assert (whi / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; lia).
    assert (0 <= wlo / 8) by (apply Z.div_pos; lia).
    destruct Hd as [Hd|[Hd|[Hd|[Hd|[Hd|Hd]]]]]; try lia.
    destruct F6 as [F6|F6].
    - assert (whi / 8 <= FS / 8) by (apply Z.div_le_mono; lia). lia.
    - assert (FS / 8 + 1446400 <= wlo / 8) by (apply Z.div_le_lower_bound; lia). lia.
  Qed.
  #[using="Type"] Lemma wclass_pay_shadow : forall wlo whi A n d len, geom_ok wlo whi -> wclass wlo whi A n -> 0 <= n ->
    0 <= d -> 0 <= len -> (len = 0 \/ (IMGHI_A <= d /\ app_mem d len /\ d + len <= HIEND_A)) -> (len = 0 \/ d + len <= FS \/ FS + FS_LEN <= d) ->
    (d + len <= wlo \/ whi <= d) ->
    (len = 0 \/ SHB + (d + len - 1) / 8 + 1 <= A \/ A + n <= SHB + d / 8).
  Proof.
    intros wlo whi A n d len GE Hd Hn Hd0 Hl0 AP1 AP2 AP3.
    pose proof (geom_facts wlo whi GE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH). unfold IMGHI_A, app_mem, LOSH_A in AP1. rewrite HKHI, HHI in AP1. rewrite HLEN in AP2.
    unfold wclass in Hd. rewrite ?HLEN, ?HFR, ?HFL, ?HSL, ?HSH, F7 in Hd. unfold SHB.
    destruct (Z.eq_dec len 0) as [->|Hnz]; [left; reflexivity | right].
    assert (A1 : 0x688000 <= d /\ (d + len <= 0x7fff7000 \/ 17594333495296 <= d) /\ d + len <= 140737488355328) by (destruct AP1; [lia | assumption]).
    assert (0xcd000 <= d / 8) by (apply Z.div_le_lower_bound; lia).
    assert ((d + len - 1) / 8 + 1 <= 17592186044416) by (apply Z.le_trans with ((d + len - 1) / 8 + 1); [lia|]; assert ((d + len - 1) / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia); lia).
    assert (0 <= d / 8) by (apply Z.div_pos; lia).
    destruct Hd as [Hd|[Hd|[Hd|[Hd|[Hd|Hd]]]]]; try lia.
    destruct AP2 as [AP2|[AP2|AP2]]; [lia| |].
    - left. assert ((d + len - 1) / 8 < FS / 8) by (apply Z.div_lt_upper_bound; lia). lia.
    - right. assert (FS / 8 + 1446400 <= d / 8) by (apply Z.div_le_lower_bound; lia). lia.
  Qed.

  #[using="Type"] Lemma R_geom : forall rho st ms, R U G FS M0 rho st ms -> geom_ok (rho SYM_SP0 - FR_A) (rho SYM_SP0).
  Proof.
    intros rho st ms HR. pose proof (r_apart _ _ _ _ _ _ _ HR) as (A1 & A2 & A3 & A4 & A5). pose proof (r_fs _ _ _ _ _ _ _ HR) as HFS.
    pose proof (fo_lo _ _ HFS). pose proof (fo_app _ _ HFS). pose proof (fo_hi _ _ HFS). pose proof (fo_align _ _ HFS). unfold geom_ok, FR_A, IMGHI_A, app_mem, LOSH_A, KHI_A, HIEND_A, FS_LEN in *. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="UOK segs"] Lemma R_wr : forall rho st st' ms m' A n,
    R U G FS M0 rho st ms -> wr_agree (ms_mem ms) m' A n -> wclass (rho SYM_SP0 - FR_A) (rho SYM_SP0) A n ->
    (forall x, A <= x < A + n -> priv U FS (rho SYM_SP0) x) ->
    s_pc st' = s_pc st -> s_regs st' = s_regs st -> s_ctx st' = s_ctx st -> s_next st' = s_next st -> s_resv st' = s_resv st ->
    Forall (stack_cell_ok U rho m' (rho SYM_SP0)) (s_stk st') ->
    Forall (arr_ok U rho m' (rho SYM_SP0)) (s_arrs st') ->
    payload_ok U rho m' (s_pcache st') (s_pay st') ->
    abs_ok U m' (s_abs st') ->
    (A + n <= 0x666260 -> forall a b, bm_get (ue_rt U) a = Some b -> a + 1 <= A \/ A + n <= a) ->
    frames_ok U FS rho m' (s_frames st') ->
    R U G FS M0 rho st' (ms_with_mem ms m').
  Proof.
    intros rho st st' ms m' A n HR HW WC PRIV Epc Eregs Ectx Enext Eresv STK ARRS PAY ABS RT FRS.
    pose proof (R_geom _ _ _ HR) as GE.
    pose proof (geom_facts _ _ GE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    pose proof HW as (WA & WAn & Wn & _).
    destruct HR as [Rglob Rpc Rsvc Rregs Rvs Rstk Rarrs Rwin Rpay Rabs Rresv Rfrm Rframe Rsp0 Ralign Rra Rdata
                    Rcomp Rapart Rrt Rgsh Rshstk Rshpay Rmctx Rfs Rframes].
    pose proof Rapart as (AP1 & AP2 & AP3 & AP4 & AP5).
    constructor; cbn; rewrite ?Epc, ?Eregs, ?Ectx, ?Enext, ?Eresv; try assumption.
    - eapply window_ok_wr; [exact HW | exact Rwin].
    - eapply frame_ok_wr; [exact HW | exact Rframe | exact PRIV].
    - eapply lits_rt_wr'; [exact HW | exact Rrt | exact GE | exact WC | exact RT].
    - eapply lits_gsh_wr'; [exact HW | exact Rgsh | exact GE | exact WC |].
      intros Hlo a b Hg. pose proof (uo_gsh_range U UOK a b Hg) as Ha. rewrite ESH in Ha. unfold SHB in Ha. lia.
    - eapply stack_shadow_ok_wr; [exact HW | exact Rshstk | exact AP1 | exact AP2 |].
      pose proof (wclass_shadow _ _ A n GE WC Wn) as X. unfold FR_A in X |- *. exact X.
    - destruct Rdata as (D1 & D2 & D3). destruct Rpay as (_ & P2 & _). pose proof (uo_frA U UOK) as EFR.
      eapply payload_shadow_ok_wr; [exact HW | exact Rshpay | lia | destruct AP3 as [?|(? & ? & ?)]; [left; assumption | right; assumption] | lia |].
      eapply (wclass_pay_shadow _ _ A n _ _ GE WC Wn); [lia | lia | exact AP3 | exact AP5 | rewrite EFR in P2; unfold FR_A in P2 |- *; lia].
    - eapply malloc_ctx_ok_wr; [exact HW | exact Rmctx | exact GE | exact WC].
    - eapply fs_ok_wr; [exact HW | exact Rfs | exact GE | exact WC].
  Qed.

  (* [comment removed for export] *)
  #[using="segs"] Lemma cell_ok_store : forall rho m b lo hi o bs c,
    0 <= b + lo -> b + hi <= 2 ^ 62 ->
    cell_ok U rho m b lo hi c -> (c_off c + c_w c <= o \/ o + Z.of_nat (length bs) <= c_off c) -> lo <= o -> o + Z.of_nat (length bs) <= hi ->
    cell_ok U rho (wbytes m (w64 (b + o)) bs) b lo hi c.
  Proof.
    intros rho m b lo hi o bs c H0 H62 (A & B & C & cbs & Hrd & Hvb) Hd Ho Ho'.
    split; [exact A|]. split; [exact B|]. split; [exact C|]. exists cbs. split; [|exact Hvb].
    rewrite (st_rdn_out m (b + o) bs); [exact Hrd | lia | lia | lia | lia | lia | lia].
  Qed.
  #[using="segs"] Lemma stack_cell_ok_store : forall rho m sp0 o bs c,
    0 <= sp0 - ue_fr U -> sp0 < 2 ^ 62 ->
    stack_cell_ok U rho m sp0 c -> (c_off c + c_w c <= o \/ o + Z.of_nat (length bs) <= c_off c) -> - ue_fr U <= o -> o + Z.of_nat (length bs) <= 0 ->
    stack_cell_ok U rho (wbytes m (w64 (sp0 + o)) bs) sp0 c.
  Proof. intros rho m sp0 o bs c H0 H62 HC Hd Ho Ho'. unfold stack_cell_ok in *. apply cell_ok_store; try assumption; lia. Qed.

  (* [comment removed for export] *)
  #[using="segs"] Lemma arr_okg_store : forall rho m b lo hi o bs a,
    0 <= b + lo -> b + hi <= 2 ^ 62 ->
    arr_okg U rho m b lo hi a -> (ar_hi a <= o \/ o + Z.of_nat (length bs) <= ar_lo a) -> lo <= o -> o + Z.of_nat (length bs) <= hi ->
    arr_okg U rho (wbytes m (w64 (b + o)) bs) b lo hi a.
  Proof.
    intros rho m b lo hi o bs a H0 H62 (A & B & C) Hd Ho Ho'.
    split; [exact A|]. split; [exact B|]. destruct (ar_fact a) as [f|]; [|exact I].
    destruct C as (C1 & C2 & C3 & C4). split; [exact C1|]. split; [exact C2|]. split.
    - intros j Hj. destruct (C3 j Hj) as (Hlt & x & Hx & Hr). split; [exact Hlt|]. exists x. split; [|exact Hr].
      rewrite (st_rd1_out m (b + o) bs); [exact Hx | lia | lia | lia | lia | lia | lia].
    - intros H1. destruct (C4 H1) as (x & Hx & Hi). destruct (C3 0 ltac:(lia)) as [Hlt0 _]. exists x. split; [|exact Hi].
      rewrite (st_rd1_out m (b + o) bs); [exact Hx | lia | lia | lia | lia | lia | lia].
  Qed.
  #[using="segs"] Lemma arr_ok_store : forall rho m sp0 o bs a,
    0 <= sp0 - ue_fr U -> sp0 < 2 ^ 62 ->
    arr_ok U rho m sp0 a -> (ar_hi a <= o \/ o + Z.of_nat (length bs) <= ar_lo a) -> - ue_fr U <= o -> o + Z.of_nat (length bs) <= 0 ->
    arr_ok U rho (wbytes m (w64 (sp0 + o)) bs) sp0 a.
  Proof. intros rho m sp0 o bs a H0 H62 HA Hd Ho Ho'. unfold arr_ok in *. apply arr_okg_store; try assumption; lia. Qed.

  (* [comment removed for export] *)
  #[using="UOK"] Lemma R_stack_store : forall rho st ms o w wv stk' ars',
    wf_state st = true -> R U G FS M0 rho st ms ->
    - ue_fr U <= o -> o + w <= 0 -> 0 < w -> w <= 8 ->
    let m' := wbytes (ms_mem ms) (w64 (rho SYM_SP0 + o)) (store_bytes w wv) in
    Forall (stack_cell_ok U rho m' (rho SYM_SP0)) stk' ->
    Forall (arr_ok U rho m' (rho SYM_SP0)) ars' ->
    store_ok segs (ms_mem ms) (w64 (rho SYM_SP0 + o)) (Z.to_nat w) = true /\
    R U G FS M0 rho (set_arrs (set_stk st stk') ars') (ms_with_mem ms m').
  Proof.
    intros rho st ms o w wv stk' ars' Hwf HR Ho1 Ho2 Hw Hw8 m' Hstk Hars. subst m'.
    pose proof (r_sp0 _ _ _ _ _ _ _ HR) as Rsp0. pose proof (r_win _ _ _ _ _ _ _ HR) as Rwin. pose proof (uo_frA U UOK) as EFR.
    set (sp0 := rho SYM_SP0) in *. set (A := sp0 + o) in *.
    pose proof (length_store_bytes w wv) as Hlen.
    assert (HA0 : 0 <= A) by lia. assert (HA64 : A < 2 ^ 64) by lia.
    assert (HAn : A + Z.of_nat (length (store_bytes w wv)) <= 2 ^ 64) by lia.
    split.
    { apply store_ok_of_all; rewrite w64_unsigned_small by lia; [lia|].
      intros x Hx. destruct (proj1 Rwin (bv_unsigned x) ltac:(lia)) as [b Hb]. rewrite w64_of_unsigned in Hb.
      unfold wview. rewrite Hb. discriminate. }
    pose proof (wbytes_wr_agree (ms_mem ms) A (store_bytes w wv) HA0 HA64 HAn) as HW. rewrite Hlen, Z2Nat.id in HW by lia.
    pose proof (R_geom _ _ _ HR) as GE. pose proof (geom_facts _ _ GE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    eapply (R_wr rho st _ ms _ A w HR HW); cbn; try reflexivity.
    - left. rewrite EFR in Ho1. lia.
    - intros x Hx. left. lia.
    - exact Hstk.
    - exact Hars.
    - pose proof (r_pay _ _ _ _ _ _ _ HR) as P. pose proof (r_data _ _ _ _ _ _ _ HR) as (D1 & D2 & D3).
      eapply payload_ok_wr; [exact HW | exact P | lia | lia | destruct P as (_ & P2 & _); lia].
    - eapply abs_ok_wr; [exact HW | exact (r_abs _ _ _ _ _ _ _ HR) | lia].
    - intros Hlo. exfalso. lia.
    - eapply frames_ok_wr_apart; [exact HW | exact (r_fs _ _ _ _ _ _ _ HR) | exact (r_frames _ _ _ _ _ _ _ HR) | rewrite EFR in Ho1; unfold FR_A in *; lia |].
      right. rewrite F7, HSH. unfold SHB. rewrite EFR in Ho1. unfold FR_A in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma ro_clear_sound : forall a w a', ro_clear U a w = true -> in_rangesZ a' (ue_ro U) -> ~ (a <= a' < a + w).
  Proof.
    intros a w a' H (r & Hin & Hr) Hc. unfold ro_clear in H. rewrite forallb_forall in H. specialize (H r Hin). cbn in H.
    destruct (Z.leb_spec (snd r) a); [lia|]. destruct (Z.leb_spec (a + w) (fst r)); [lia|]. discriminate.
  Qed.

  #[using="UOK"] Lemma R_abs_store : forall rho st ms a w z v wv,
    wf_state st = true -> R U G FS M0 rho st ms -> in_ranges a w (ue_rw U) = true -> ro_clear U a w = true -> 0 < w -> w <= 8 ->
    val_ok rho v wv -> aval_lit v = Some z ->
    let m' := wbytes (ms_mem ms) (w64 a) (store_bytes w wv) in
    store_ok segs (ms_mem ms) (w64 a) (Z.to_nat w) = true /\
    R U G FS M0 rho (set_pay (set_pcache (set_abs st (bm_set_bytes (s_abs st) a (z mod two64z) (Z.to_nat w))) []) []) (ms_with_mem ms m').
  Proof.
    intros rho st ms a w z v wv Hwf HR Hrw Hroc Hw Hw8 Hv Hz m'. subst m'.
    pose proof (aval_lit_sound rho v z wv Hz Hv) as Hwv.
    assert (Hu : bv_unsigned wv = z mod two64z) by (rewrite Hwv, w64_unsigned, two64z_eq; reflexivity).
    assert (Hrg : forall k, 0 <= k < w -> in_rangesZ (a + k) (ue_rw U)) by (intros k Hk; eapply in_ranges_Z; eauto).
    assert (Hra : in_rangesZ a (ue_rw U)) by (pose proof (Hrg 0 ltac:(lia)) as H0; rewrite Z.add_0_r in H0; exact H0).
    pose proof (uo_small U UOK a (or_introl Hra)) as Ha0.
    pose proof (uo_small U UOK (a + (w - 1)) (or_introl (Hrg (w - 1) ltac:(lia)))) as Ha1.
    pose proof (uo_rw_lo U UOK (a + (w - 1)) (Hrg (w - 1) ltac:(lia))) as Hlo.
    pose proof (r_sp0 _ _ _ _ _ _ _ HR) as Rsp0. pose proof (uo_frA U UOK) as EFR.
    set (sp0 := rho SYM_SP0) in *.
    pose proof (length_store_bytes w wv) as Hlen.
    assert (HA0 : 0 <= a) by lia. assert (HA64 : a < 2 ^ 64) by lia.
    assert (HAn : a + Z.of_nat (length (store_bytes w wv)) <= 2 ^ 64) by lia.
    split.
    { apply store_ok_of_all; rewrite w64_unsigned_small by lia; [lia|].
      intros x Hx. pose proof (uo_rw_w U UOK (bv_unsigned x) (ms_mem ms) ltac:(replace (bv_unsigned x) with (a + (bv_unsigned x - a)) by lia; apply Hrg; lia)) as So.
      rewrite w64_of_unsigned in So. cbn [store_ok] in So. fold segs in So. destruct (wview segs (ms_mem ms) x); [discriminate | discriminate]. }
    pose proof (wbytes_wr_agree (ms_mem ms) a (store_bytes w wv) HA0 HA64 HAn) as HW. rewrite Hlen, Z2Nat.id in HW by lia.
    pose proof (R_geom _ _ _ HR) as GE. pose proof (geom_facts _ _ GE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    eapply (R_wr rho st _ ms _ a w HR HW); cbn; try reflexivity.
    - right; left. lia.
    - intros x Hx. right; left. replace x with (a + (x - a)) by lia. apply Hrg. lia.
    - apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (r_stk _ _ _ _ _ _ _ HR) c Hc) as Hcell. pose proof Hcell as (C1 & C2 & _).
      eapply cell_ok_wr; [exact HW | exact Hcell | lia | lia | lia].
    - apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) (r_arrs _ _ _ _ _ _ _ HR) b Hb) as Harr. pose proof Harr as (C1 & C2 & _).
      eapply arr_okg_wr; [exact HW | exact Harr | lia | lia | lia].
    - destruct (r_pay _ _ _ _ _ _ _ HR) as (P1 & P2 & P3 & P4). split; [|split; [exact P2 | split; [intros ? ? ? []|intros ? ? []]]].
      intros i Hi. destruct (P1 i Hi) as [b Hb]. eapply rd1_wr_grows; [exact HW | exact Hb].
    - destruct (r_abs _ _ _ _ _ _ _ HR) as (Q1 & Q2 & Q3). split; [|split].
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
        { intros Hc. apply (ro_clear_sound a w a' Hroc Hro). rewrite length_store_bytes in Hc. lia. }
        rewrite (st_out _ a _ HA0 HA64 HAn) in Hm by lia. exact (Q3 a' b Hro Hm).
    - intros _ a' b Hg. pose proof (uo_rt_small U UOK a' b Hg) as [_ Hnrw].
      destruct (Z_lt_le_dec a' a); [left; lia|]. destruct (Z_lt_le_dec a' (a + w)); [|right; lia].
      exfalso. apply Hnrw. replace a' with (a + (a' - a)) by lia. apply Hrg. lia.
    - eapply frames_ok_wr_apart; [exact HW | exact (r_fs _ _ _ _ _ _ _ HR) | exact (r_frames _ _ _ _ _ _ _ HR) | lia |].
      left. rewrite F7, HSL. unfold SHB. lia.
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

  #[using="Type"] Lemma arrs_touch_split : forall ars C off w v ars',
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

  #[using="Type"] Lemma touch_test_sound : forall rho C off w a, ctx_ok rho C -> touch_test C off w a = true ->
    ar_lo a <= evl rho off /\ evl rho off + w <= ar_hi a.
  Proof.
    intros rho C off w a HC H. unfold touch_test in H. apply andb_prop in H as [H1 H2].
    pose proof (entails_sound rho C _ None HC H1) as E1. pose proof (entails_sound rho C _ None HC H2) as E2.
    rewrite laddc_sound in E1. rewrite laddc_sound, lneg_sound in E2. lia.
  Qed.

  #[using="Type"] Lemma arrs_disjointb_app : forall pre a post,
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

  #[using="Type"] Lemma store_byte_val : forall rho l wv d, wv = w64 (evl rho l) -> 0 <= evl rho l < 256 ->
    bv_unsigned (nth 0 (store_bytes 1 wv) d) = evl rho l.
  Proof.
    intros rho l wv d Hwv Hr. unfold store_bytes. change (Z.to_nat 1) with 1%nat. cbn [Z_to_le_bytes nth].
    rewrite Z_to_bv_unsigned, bv_wrap8_mod, Hwv, w64_unsigned. change (2 ^ 8) with 256.
    rewrite (Z.mod_small (evl rho l) (2 ^ 64)) by lia. apply Z.mod_small. lia.
  Qed.

  #[using="segs"] Lemma touch1_ok : forall rho C m sp0 lo hi off w v wv a,
    ctx_ok rho C -> val_ok rho v wv -> 0 < w -> w <= 8 ->
    0 <= sp0 + lo -> sp0 + hi <= 2 ^ 62 ->
    arr_okg U rho m sp0 lo hi a -> ar_lo a <= evl rho off -> evl rho off + w <= ar_hi a ->
    arr_okg U rho (wbytes m (w64 (sp0 + evl rho off)) (store_bytes w wv)) sp0 lo hi (touch1 C off w v a).
  Proof.
    intros rho C m sp0 lo hi off w v wv a HC Hv Hw Hw8 H0 H62 (A & B & Cf) Hlo Hhi.
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
  #[using="segs"] Lemma arrs_touch_ok : forall rho C m sp0 lo hi ars off w v wv ars',
    ctx_ok rho C -> val_ok rho v wv -> 0 < w -> w <= 8 ->
    0 <= sp0 + lo -> sp0 + hi <= 2 ^ 62 ->
    Forall (arr_okg U rho m sp0 lo hi) ars -> arrs_disjointb ars = true ->
    arrs_touch ars C off w v = Some ars' ->
    Forall (arr_okg U rho (wbytes m (w64 (sp0 + evl rho off)) (store_bytes w wv)) sp0 lo hi) ars'
    /\ (exists a, In a ars /\ ar_lo a <= evl rho off /\ evl rho off + w <= ar_hi a /\ lo <= ar_lo a /\ ar_hi a <= hi).
  Proof.
    intros rho C m sp0 lo hi ars off w v wv ars' HC Hv Hw Hw8 H0 H62 Hars Hdisj H.
    destruct (arrs_touch_split _ _ _ _ _ _ H) as (pre & a & post & -> & -> & Ht).
    destruct (touch_test_sound rho C off w a HC Ht) as [Hlo Hhi].
    destruct (arrs_disjointb_app pre a post Hdisj) as (Dpre & Dpost & _).
    assert (Ha : arr_okg U rho m sp0 lo hi a) by (apply (proj1 (Forall_forall _ _) Hars); apply in_app_iff; right; left; reflexivity).
    pose proof Ha as (A & B & _).
    pose proof (length_store_bytes w wv) as Hlen.
    split.
    - apply Forall_forall. intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|[<-|Hb]].
      + apply (arr_okg_store rho m sp0 lo hi); rewrite ?Hlen; [lia|lia| | |lia|lia].
        * apply (proj1 (Forall_forall _ _) Hars). apply in_app_iff. left; exact Hb.
        * destruct (overlaps_false _ _ _ _ (Dpre b Hb)); lia.
      + apply touch1_ok; auto.
      + apply (arr_okg_store rho m sp0 lo hi); rewrite ?Hlen; [lia|lia| | |lia|lia].
        * apply (proj1 (Forall_forall _ _) Hars). apply in_app_iff. right; right; exact Hb.
        * destruct (overlaps_false _ _ _ _ (Dpost b Hb)); lia.
    - exists a. split; [apply in_app_iff; right; left; reflexivity|]. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma arrs_overlap_lit_false : forall ars off w b,
    arrs_overlap_lit ars off w = false -> In b ars -> off + w <= ar_lo b \/ ar_hi b <= off.
  Proof.
    intros ars off w b H Hb. unfold arrs_overlap_lit in H.
    destruct (overlaps (ar_lo b) (ar_hi b - ar_lo b) off w) eqn:E.
    - exfalso. assert (existsb (fun a => overlaps (ar_lo a) (ar_hi a - ar_lo a) off w) ars = true); [|congruence].
      apply existsb_exists. exists b. split; [exact Hb | exact E].
    - destruct (overlaps_false _ _ _ _ E); lia.
  Qed.

  (* [comment removed for export] *)
  #[using="segs"] Lemma store_space_lit_ok : forall rho C m b lo hi cs ars off w v wv cs' ars',
    ctx_ok rho C -> val_ok rho v wv -> 0 < w -> w <= 8 -> 0 <= b + lo -> b + hi <= 2 ^ 62 ->
    Forall (cell_ok U rho m b lo hi) cs -> Forall (arr_okg U rho m b lo hi) ars -> arrs_disjointb ars = true ->
    store_space_lit lo hi cs ars C off w v = Some (cs', ars') ->
    lo <= off /\ off + w <= hi /\
    Forall (cell_ok U rho (wbytes m (w64 (b + off)) (store_bytes w wv)) b lo hi) cs' /\
    Forall (arr_okg U rho (wbytes m (w64 (b + off)) (store_bytes w wv)) b lo hi) ars'.
  Proof.
    intros rho C m b lo hi cs ars off w v wv cs' ars' HC Hv Hw Hw8 Hb0 Hb62 Hcs Hars Wad H.
    pose proof (length_store_bytes w wv) as Hlen.
    unfold store_space_lit in H. destruct (in_win lo hi off w) eqn:Win; cbn [negb] in H; [|discriminate].
    unfold in_win in Win. apply andb_prop in Win as [Win1 Win2]. apply Z.leb_le in Win1. apply Z.leb_le in Win2.
    split; [exact Win1|]. split; [exact Win2|].
    assert (CELLS : Forall (cell_ok U rho (wbytes m (w64 (b + off)) (store_bytes w wv)) b lo hi) (cells_kill cs off w)).
    { apply Forall_forall. intros c Hc. destruct (cells_kill_spec _ _ _ _ Hc) as [Hin Hov].
      apply cell_ok_store; rewrite ?Hlen; [lia | lia | exact (proj1 (Forall_forall _ _) Hcs c Hin) | | lia | lia].
      destruct (overlaps_false _ _ _ _ Hov); lia. }
    destruct (arrs_overlap_lit ars off w) eqn:Eov.
    - destruct (arrs_touch ars C (lconst off) w v) as [ars''|] eqn:Et; [|discriminate]. injection H; intros <- <-.
      destruct (arrs_touch_ok rho C m b lo hi ars (lconst off) w v wv ars'' HC Hv Hw Hw8 Hb0 Hb62 Hars Wad Et) as [ARRS _].
      rewrite lconst_sound in ARRS. split; [exact CELLS | exact ARRS].
    - injection H; intros <- <-. split.
      + constructor; [|exact CELLS]. unfold cell_ok; cbn [c_off c_w c_val]. split; [lia|]. split; [lia|]. split; [lia|].
        exists (store_bytes w wv). split; [|apply store_bytes_ok; assumption].
        rewrite <- Hlen. apply st_hit; rewrite ?Hlen; lia.
      + apply Forall_forall. intros a Ha. apply arr_okg_store; rewrite ?Hlen; [lia | lia | exact (proj1 (Forall_forall _ _) Hars a Ha) | | lia | lia].
        destruct (arrs_overlap_lit_false _ _ _ _ Eov Ha); lia.
  Qed.

  #[using="segs"] Lemma store_space_sym_ok : forall rho C m b lo hi cs ars off w v wv cs' ars',
    ctx_ok rho C -> val_ok rho v wv -> 0 < w -> w <= 8 -> 0 <= b + lo -> b + hi <= 2 ^ 62 ->
    Forall (cell_ok U rho m b lo hi) cs -> Forall (arr_okg U rho m b lo hi) ars -> arrs_disjointb ars = true ->
    forallb (fun c => negb (existsb (fun a => overlaps (ar_lo a) (ar_hi a - ar_lo a) (c_off c) (c_w c)) ars)) cs = true ->
    store_space_sym lo hi cs ars C off w v = Some (cs', ars') ->
    lo <= evl rho off /\ evl rho off + w <= hi /\
    Forall (cell_ok U rho (wbytes m (w64 (b + evl rho off)) (store_bytes w wv)) b lo hi) cs' /\
    Forall (arr_okg U rho (wbytes m (w64 (b + evl rho off)) (store_bytes w wv)) b lo hi) ars'.
  Proof.
    intros rho C m b lo hi cs ars off w v wv cs' ars' HC Hv Hw Hw8 Hb0 Hb62 Hcs Hars Wad Wdisj H.
    pose proof (length_store_bytes w wv) as Hlen.
    unfold store_space_sym in H.
    destruct (arrs_touch ars C off w v) as [ars''|] eqn:Et; [|discriminate].
    destruct (arr_find ars C off w) as [a0|] eqn:Efind; [|discriminate].
    destruct (in_win lo hi (ar_lo a0) (ar_hi a0 - ar_lo a0)) eqn:Win; [|discriminate]. injection H; intros <- <-.
    unfold in_win in Win. apply andb_prop in Win as [Win1 Win2]. apply Z.leb_le in Win1. apply Z.leb_le in Win2.
    destruct (arr_find_spec rho _ _ _ _ _ HC Efind) as (Hina0 & Hlo0 & Hhi0).
    destruct (arrs_touch_ok rho C m b lo hi ars off w v wv ars'' HC Hv Hw Hw8 Hb0 Hb62 Hars Wad Et) as [ARRS _].
    split; [lia|]. split; [lia|]. split; [|exact ARRS].
    apply Forall_forall. intros c Hc.
    apply cell_ok_store; rewrite ?Hlen; [lia | lia | exact (proj1 (Forall_forall _ _) Hcs c Hc) | | lia | lia].
    rewrite forallb_forall in Wdisj. specialize (Wdisj c Hc).
    destruct (overlaps (ar_lo a0) (ar_hi a0 - ar_lo a0) (c_off c) (c_w c)) eqn:E.
    { exfalso. assert (X : existsb (fun a => overlaps (ar_lo a) (ar_hi a - ar_lo a) (c_off c) (c_w c)) ars = true)
        by (apply existsb_exists; exists a0; split; [exact Hina0 | exact E]). rewrite X in Wdisj. discriminate. }
    destruct (overlaps_false _ _ _ _ E); lia.
  Qed.

  #[using="UOK"] Lemma store_stack_lit_sound : forall rho st ms off w v wv st',
    wf_state st = true -> R U G FS M0 rho st ms -> val_ok rho v wv -> aval_below v (s_next st) = true -> 0 < w -> w <= 8 ->
    store_stack_lit U st off w v = Some st' ->
    store_ok segs (ms_mem ms) (w64 (rho SYM_SP0 + off)) (Z.to_nat w) = true
    /\ R U G FS M0 rho st' (ms_with_mem ms (wbytes (ms_mem ms) (w64 (rho SYM_SP0 + off)) (store_bytes w wv)))
    /\ (s_next st' = s_next st /\ s_pc st' = s_pc st /\ s_regs st' = s_regs st /\ s_resv st' = s_resv st).
  Proof.
    intros rho st ms off w v wv st' Hwf HR Hv Hvb Hw Hw8 H.
    pose proof (wf_parts st Hwf) as (_ & _ & _ & _ & _ & _ & Wdisj & W18 & _ & Wad & _).
    pose proof (R_to_VS _ _ _ HR) as [HC _]. pose proof (r_sp0 _ _ _ _ _ _ _ HR) as Hsp0. pose proof (uo_fr U UOK) as Hfr.
    unfold store_stack_lit in H.
    destruct (store_space_lit (- ue_fr U) 0 (s_stk st) (s_arrs st) (s_ctx st) off w v) as [[cs' ars']|] eqn:E; [|discriminate].
    injection H; intros <-.
    destruct (store_space_lit_ok rho (s_ctx st) (ms_mem ms) (rho SYM_SP0) (- ue_fr U) 0 (s_stk st) (s_arrs st) off w v wv cs' ars'
                HC Hv Hw Hw8 ltac:(lia) ltac:(lia) (r_stk _ _ _ _ _ _ _ HR) (r_arrs _ _ _ _ _ _ _ HR) Wad E) as (W1 & W2 & CELLS & ARRS).
    destruct (R_stack_store rho st ms off w wv cs' ars' Hwf HR W1 W2 Hw Hw8 CELLS ARRS) as [So HR'].
    split; [exact So|]. split; [exact HR'|]. cbn. repeat split; reflexivity.
  Qed.

  #[using="UOK"] Lemma store_stack_sym_sound : forall rho st ms off w v wv st',
    wf_state st = true -> R U G FS M0 rho st ms -> val_ok rho v wv -> aval_below v (s_next st) = true -> 0 < w -> w <= 8 ->
    store_stack_sym U st off w v = Some st' ->
    store_ok segs (ms_mem ms) (w64 (rho SYM_SP0 + evl rho off)) (Z.to_nat w) = true
    /\ R U G FS M0 rho st' (ms_with_mem ms (wbytes (ms_mem ms) (w64 (rho SYM_SP0 + evl rho off)) (store_bytes w wv)))
    /\ (s_next st' = s_next st /\ s_pc st' = s_pc st /\ s_regs st' = s_regs st /\ s_resv st' = s_resv st).
  Proof.
    intros rho st ms off w v wv st' Hwf HR Hv Hvb Hw Hw8 H.
    pose proof (wf_parts st Hwf) as (_ & _ & _ & _ & _ & _ & Wdisj & W18 & _ & Wad & _).
    pose proof (R_to_VS _ _ _ HR) as [HC _]. pose proof (r_sp0 _ _ _ _ _ _ _ HR) as Hsp0. pose proof (uo_fr U UOK) as Hfr.
    unfold store_stack_sym in H.
    destruct (store_space_sym (- ue_fr U) 0 (s_stk st) (s_arrs st) (s_ctx st) off w v) as [[cs' ars']|] eqn:E; [|discriminate].
    injection H; intros <-.
    destruct (store_space_sym_ok rho (s_ctx st) (ms_mem ms) (rho SYM_SP0) (- ue_fr U) 0 (s_stk st) (s_arrs st) off w v wv cs' ars'
                HC Hv Hw Hw8 ltac:(lia) ltac:(lia) (r_stk _ _ _ _ _ _ _ HR) (r_arrs _ _ _ _ _ _ _ HR) Wad Wdisj E) as (W1 & W2 & CELLS & ARRS).
    destruct (R_stack_store rho st ms (evl rho off) w wv cs' ars' Hwf HR W1 W2 Hw Hw8 CELLS ARRS) as [So HR'].
    split; [exact So|]. split; [exact HR'|]. cbn. repeat split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma frame_set_space_eqs : forall f cs ars,
    f_sym (frame_set_space f cs ars) = f_sym f /\ f_cls (frame_set_space f cs ars) = f_cls f /\ f_flag (frame_set_space f cs ars) = f_flag f
    /\ f_sh (frame_set_space f cs ars) = f_sh f /\ f_cells (frame_set_space f cs ars) = cs /\ f_arrs (frame_set_space f cs ars) = ars
    /\ f_size (frame_set_space f cs ars) = f_size f /\ f_shn (frame_set_space f cs ars) = f_shn f.
  Proof. intros; repeat split; reflexivity. Qed.

  #[using="Type"] Lemma sh64 : forall x, sh (64 * x) = SHB + 8 * x.
  Proof. intros x. unfold sh. destruct fs_consts as (_ & _ & _ & _ & _ & ESH & _). rewrite ESH. replace (64 * x) with (8 * x * 8) by lia. rewrite Z.div_mul by lia. reflexivity. Qed.

  #[using="Type"] Lemma frame_at_inj : forall rho f p q, frame_at FS rho f p -> frame_at FS rho f q -> (f_cls f = 1 \/ f_cls f = 4 \/ f_cls f = 5) -> p = q.
  Proof.
    intros rho f p q (Hp & Hb & _) (Hq & Hb' & _) Hk. rewrite Hb in Hb'. unfold fs_frame in Hb'.
    pose proof (frame_geom (f_cls f) p Hk Hp) as (_ & _ & G3 & _).
    assert (E : p * fs_fsz (f_cls f) = q * fs_fsz (f_cls f)) by lia. apply Z.mul_reg_r in E; [exact E | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="segs"] Lemma frames_ok_upd : forall rho m m' A n frs i f g,
    wr_agree m m' A n -> fs_ok FS m -> frames_ok U FS rho m frs -> nth_frame frs i = Some f -> fsim f g ->
    (forall p, frame_okR U FS rho m f p -> frame_okR U FS rho m' g p) ->
    (forall p q h, frame_at FS rho f p -> frame_okR U FS rho m h q -> (f_cls h, q) <> (f_cls f, p) -> frame_untouched rho A n h) ->
    (A + n <= FS + FS_FLAGS \/ FS + FS_FRAMES <= A) ->
    frames_ok U FS rho m' (upd_frame frs i g).
  Proof.
    intros rho m m' A n frs i f g HW HFS RF Hn SIM UPD OTH FL.
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH). pose proof HW as (WA & WAn & Wn & _).
    pose proof (fo_lo _ _ HFS) as LO. pose proof (fo_app _ _ HFS) as LOAPP. pose proof (fo_hi _ _ HFS) as HI. unfold IMGHI_A in LO. unfold app_mem, LOSH_A, KHI_A, FS_LEN in LOAPP. rewrite HHI, HLEN in HI.
    eapply frames_ok_rebuild; [exact RF | eapply fsim_upd; [exact Hn | exact SIM] | |].
    - intros ps F2 ND. pose proof (proj1 (Forall2_nth _ _ _) F2) as [L F2n].
      assert (Hi : (i < length frs)%nat) by (apply (proj1 (nth_error_Some frs i)); rewrite <- nth_frame_error, Hn; discriminate).
      destruct (nth_error ps i) as [p|] eqn:Ep; [|apply nth_error_None in Ep; lia].
      pose proof (F2n i f p ltac:(rewrite <- nth_frame_error; exact Hn) Ep) as Hf.
      apply Forall2_nth. split; [rewrite length_upd_frame; exact L|].
      intros j x y Hx Hy. rewrite <- nth_frame_error in Hx. rewrite nth_upd_frame in Hx.
      destruct (Nat.eqb_spec i j) as [<-|Hne].
      + rewrite Hn in Hx. injection Hx; intros <-. rewrite Ep in Hy. injection Hy; intros <-. apply UPD. exact Hf.
      + pose proof (F2n j x y ltac:(rewrite <- nth_frame_error; exact Hx) Hy) as Hx'.
        eapply frame_okR_wr; [exact HW | exact HFS | exact Hx' |].
        eapply (OTH p y x); [exact (proj1 Hf) | exact Hx' |].
        intros E. eapply (frames_slots_ne rho m frs ps j i x f y p F2 ND); [congruence | exact Hx | exact Hy | exact Hn | exact Ep | exact E].
    - intros j Hj. rewrite HFL in FL |- *. rewrite HFR in FL. apply (wr_out m m' A n); [exact HW | lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="UOK"] Lemma R_frame_store : forall rho st ms i f o w wv cs' ars',
    wf_state st = true -> R U G FS M0 rho st ms -> nth_frame (s_frames st) i = Some f ->
    0 <= o -> o + w <= f_size f -> 0 < w -> w <= 8 ->
    let m' := wbytes (ms_mem ms) (w64 (64 * rho (f_sym f) + o)) (store_bytes w wv) in
    Forall (cell_ok U rho m' (64 * rho (f_sym f)) 0 (f_size f)) cs' ->
    Forall (arr_okg U rho m' (64 * rho (f_sym f)) 0 (f_size f)) ars' ->
    store_ok segs (ms_mem ms) (w64 (64 * rho (f_sym f) + o)) (Z.to_nat w) = true /\
    R U G FS M0 rho (set_frames st (upd_frame (s_frames st) i (frame_set_space f cs' ars'))) (ms_with_mem ms m').
  Proof.
    intros rho st ms i f o w wv cs' ars' Hwf HR Hn Ho1 Ho2 Hw Hw8 m' Hcs Hars. subst m'.
    pose proof (r_frames _ _ _ _ _ _ _ HR) as RF. pose proof (r_fs _ _ _ _ _ _ _ HR) as HFS.
    destruct (frames_nth rho (ms_mem ms) (s_frames st) i f RF Hn) as (p0 & Hf0 & Hin).
    pose proof Hf0 as ((Hp0 & Hb0 & Hfl0) & Hk & _).
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    pose proof (frame_geom (f_cls f) p0 Hk Hp0) as (G1 & G2 & G3 & G4 & G5 & G6). rewrite HFR in G1. rewrite HLEN in G2.
    destruct (f_size_cls f Hk) as [E1 E2]. rewrite E1 in Ho2, Hcs, Hars.
    pose proof (R_geom _ _ _ HR) as GE. pose proof (geom_facts _ _ GE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (length_store_bytes w wv) as Hlen.
    set (A := 64 * rho (f_sym f) + o) in *.
    assert (HA0 : 0 <= A) by lia. assert (HA64 : A < 2 ^ 64) by lia.
    assert (HAn : A + Z.of_nat (length (store_bytes w wv)) <= 2 ^ 64) by lia.
    split.
    { apply store_ok_of_all; rewrite w64_unsigned_small by lia; [lia|].
      intros x Hx. destruct (fo_def _ _ HFS (bv_unsigned x - FS) ltac:(lia)) as [bb Hbb].
      replace (FS + (bv_unsigned x - FS)) with (bv_unsigned x) in Hbb by lia. rewrite w64_same, w64_of_unsigned in Hbb.
      unfold wview. rewrite Hbb. discriminate. }
    pose proof (wbytes_wr_agree (ms_mem ms) A (store_bytes w wv) HA0 HA64 HAn) as HW. rewrite Hlen, Z2Nat.id in HW by lia.
    pose proof (uo_frA U UOK) as EFR. pose proof (r_sp0 _ _ _ _ _ _ _ HR) as Rsp0.
    eapply (R_wr rho st _ ms _ A w HR HW); cbn; try reflexivity.
    - right; right; left. lia.
    - intros x Hx. right; right; left. lia.
    - apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (r_stk _ _ _ _ _ _ _ HR) c Hc) as Hcell.
      pose proof Hcell as (C1 & C2 & _). eapply cell_ok_wr; [exact HW | exact Hcell | lia | lia | rewrite EFR in *; unfold FR_A in *; lia].
    - apply Forall_forall. intros b Hb'. pose proof (proj1 (Forall_forall _ _) (r_arrs _ _ _ _ _ _ _ HR) b Hb') as Harr.
      pose proof Harr as (C1 & C2 & _). eapply arr_okg_wr; [exact HW | exact Harr | lia | lia | rewrite EFR in *; unfold FR_A in *; lia].
    - pose proof (r_pay _ _ _ _ _ _ _ HR) as P. pose proof (r_data _ _ _ _ _ _ _ HR) as (D1 & D2 & D3).
      pose proof (r_apart _ _ _ _ _ _ _ HR) as (_ & _ & _ & _ & AP5). rewrite HLEN in AP5.
      eapply payload_ok_wr; [exact HW | exact P | lia | lia | lia].
    - eapply abs_ok_wr; [exact HW | exact (r_abs _ _ _ _ _ _ _ HR) | lia].
    - intros Hlo. exfalso. lia.
    - eapply (frames_ok_upd rho (ms_mem ms) _ A w (s_frames st) i f); [exact HW | exact HFS | exact RF | exact Hn | repeat split; reflexivity | | | rewrite HFR; lia].
      + intros p (Hat & _ & _ & _ & Hlen' & Hsh). pose proof (frame_set_space_eqs f cs' ars') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
        unfold frame_okR, frame_at. cbn [f_sym f_cls f_flag f_sh f_cells f_arrs frame_set_space]. rewrite Q7, Q8, E1. split; [exact Hat|]. split; [exact Hk|].
        split; [exact Hcs|]. split; [exact Hars|]. split; [exact Hlen'|].
        intros t b Ht. destruct (Hsh t b Ht) as [Hb Hm]. split; [exact Hb|].
        pose proof (nth_error_Some_length' _ _ _ Ht) as Tl. rewrite E2 in Hlen'.
        pose proof (sh_frame (f_cls f) p Hk (proj1 Hat) (fo_align _ _ HFS)) as (S1 & S2 & S3 & _). rewrite <- (proj1 (proj2 Hat)) in S1, S2, S3.
        rewrite F7, HSH in S3.
        rewrite (wr_out (ms_mem ms) _ A w); [exact Hm | exact HW | lia | lia].
      + intros p q h Hat (Hatq & Hkh & _) Hne. destruct Hat as (Hp & Hb & Hfl). destruct Hatq as (Hq & Hbq & Hflq).
        destruct (slot_apart (f_cls h) q (f_cls f) p Hkh Hq Hk Hp Hne) as [D _].
        pose proof (frame_geom (f_cls h) q Hkh Hq) as (H1 & H2 & _). rewrite HFR in H1. rewrite HLEN in H2.
        pose proof (sh_frame (f_cls h) q Hkh Hq (fo_align _ _ HFS)) as (T1 & T2 & T3 & _). rewrite F7, HSH in T3.
        pose proof (flag_geom (f_cls h) q Hkh Hq) as (L1 & L2 & _). rewrite HFR in L2.
        destruct (f_size_cls h Hkh) as [Eh1 Eh2]. unfold frame_untouched. rewrite Eh1, Eh2, Hbq, Hflq. rewrite <- Hb in D.
        first [ solve [clear - D Ho1 Ho2 Hw Hw8 G1 G2 G3 H1 H2 T2 T3 L1 L2 F4 F7 F8 F10 HSL HSH HFL Hb Hb0; lia] | lia ].   (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma length_list_set : forall {X} (l : list X) n v, length (list_set l n v) = length l.
  Proof. induction l as [|x r IH]; intros [|n] v; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
  #[using="Type"] Lemma nth_list_set_eq : forall {X} (l : list X) n v, (n < length l)%nat -> nth_error (list_set l n v) n = Some v.
  Proof. induction l as [|x r IH]; intros [|n] v H; cbn in *; try lia; [reflexivity | apply IH; lia]. Qed.
  #[using="Type"] Lemma nth_list_set_ne : forall {X} (l : list X) n v u, n <> u -> nth_error (list_set l n v) u = nth_error l u.
  Proof. induction l as [|x r IH]; intros [|n] v [|u] H; cbn; try reflexivity; [lia | apply IH; lia]. Qed.
  #[using="Type"] Lemma length_list_set_bytes : forall n bs t z, length (list_set_bytes bs t z n) = length bs.
  Proof. induction n as [|n IH]; intros; cbn [list_set_bytes]; [reflexivity | rewrite IH, length_list_set; reflexivity]. Qed.
  #[using="Type"] Lemma nth_list_set_bytes_out : forall n bs t z u, (u < t \/ t + n <= u)%nat -> nth_error (list_set_bytes bs t z n) u = nth_error bs u.
  Proof.
    induction n as [|n IH]; intros bs t z u H; cbn [list_set_bytes]; [reflexivity|].
    rewrite IH by lia. apply nth_list_set_ne. lia.
  Qed.
  #[using="Type"] Lemma nth_list_set_bytes_in : forall n bs t z k, (k < n)%nat -> (t + k < length bs)%nat ->
    nth_error (list_set_bytes bs t z n) (t + k) = Some ((z / 2 ^ (8 * Z.of_nat k)) mod 256).
  Proof.
    induction n as [|n IH]; intros bs t z k Hk Hl; [lia|]. cbn [list_set_bytes]. destruct k as [|k].
    - rewrite Nat.add_0_r. rewrite nth_list_set_bytes_out by lia. rewrite nth_list_set_eq by lia. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. reflexivity.
    - replace (t + S k)%nat with (S t + k)%nat by lia. rewrite IH; [| lia | rewrite length_list_set; lia].
      f_equal. rewrite Z.div_div by lia. f_equal. f_equal. change 256 with (2 ^ 8). rewrite <- Z.pow_add_r by lia. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="UOK"] Lemma R_shframe_store : forall rho st ms i f c w z v wv,
    wf_state st = true -> R U G FS M0 rho st ms -> nth_frame (s_frames st) i = Some f ->
    0 <= c -> c + w <= f_shn f -> 0 < w -> w <= 8 -> val_ok rho v wv -> aval_lit v = Some z ->
    let m' := wbytes (ms_mem ms) (w64 (SHB + 8 * rho (f_sym f) + c)) (store_bytes w wv) in
    store_ok segs (ms_mem ms) (w64 (SHB + 8 * rho (f_sym f) + c)) (Z.to_nat w) = true /\
    R U G FS M0 rho (set_frames st (upd_frame (s_frames st) i
         (Frame (f_sym f) (f_cls f) (f_cells f) (f_arrs f) (list_set_bytes (f_sh f) (Z.to_nat c) (z mod two64z) (Z.to_nat w)) (f_flag f))))
      (ms_with_mem ms m').
  Proof.
    intros rho st ms i f c w z v wv Hwf HR Hn Hc1 Hc2 Hw Hw8 Hv Hz m'. subst m'.
    pose proof (aval_lit_sound rho v z wv Hz Hv) as Hwv.
    assert (Hu : bv_unsigned wv = z mod two64z) by (rewrite Hwv, w64_unsigned, two64z_eq; reflexivity).
    pose proof (r_frames _ _ _ _ _ _ _ HR) as RF. pose proof (r_fs _ _ _ _ _ _ _ HR) as HFS.
    destruct (frames_nth rho (ms_mem ms) (s_frames st) i f RF Hn) as (p0 & Hf0 & Hin).
    pose proof Hf0 as ((Hp0 & Hb0 & Hfl0) & Hk & _).
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    pose proof (frame_geom (f_cls f) p0 Hk Hp0) as (G1 & G2 & G3 & G4 & G5 & G6). rewrite HFR in G1. rewrite HLEN in G2.
    pose proof (sh_frame (f_cls f) p0 Hk Hp0 (fo_align _ _ HFS)) as (S1 & S2 & S3 & S4 & S5 & S6). rewrite <- Hb0 in S1, S2, S3, S4, S5.
    destruct (f_size_cls f Hk) as [E1 E2]. rewrite E2 in Hc2.
    pose proof (R_geom _ _ _ HR) as GE. pose proof (geom_facts _ _ GE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    rewrite F7, HSL in S2. rewrite F7, HSH in S3. rewrite sh64 in S1, S2, S3.
    pose proof (length_store_bytes w wv) as Hlen.
    set (A := SHB + 8 * rho (f_sym f) + c) in *.
    assert (HA0 : 0 <= A) by (unfold SHB in *; lia). assert (HA64 : A < 2 ^ 64) by (unfold SHB in *; lia).
    assert (HAn : A + Z.of_nat (length (store_bytes w wv)) <= 2 ^ 64) by (unfold SHB in *; lia).
    split.
    { apply store_ok_of_all; rewrite w64_unsigned_small by lia; [lia|].
      intros x Hx. destruct (fo_shdef _ _ HFS (bv_unsigned x - (sh FS + FS_SHLO)) ltac:(rewrite F7, HSL, HSH; unfold SHB in *; lia)) as [bb Hbb].
      replace (sh FS + FS_SHLO + (bv_unsigned x - (sh FS + FS_SHLO))) with (bv_unsigned x) in Hbb by lia. rewrite w64_same, w64_of_unsigned in Hbb.
      unfold wview. rewrite Hbb. discriminate. }
    pose proof (wbytes_wr_agree (ms_mem ms) A (store_bytes w wv) HA0 HA64 HAn) as HW. rewrite Hlen, Z2Nat.id in HW by lia.
    pose proof (uo_frA U UOK) as EFR. pose proof (r_sp0 _ _ _ _ _ _ _ HR) as Rsp0.
    eapply (R_wr rho st _ ms _ A w HR HW); cbn; try reflexivity.
    - right; right; right; right; right. rewrite F7, HSL, HSH. unfold SHB in *. lia.
    - intros x Hx. right; right; right. rewrite F7, HSL, HSH. unfold SHB in *. lia.
    - apply Forall_forall. intros c' Hc. pose proof (proj1 (Forall_forall _ _) (r_stk _ _ _ _ _ _ _ HR) c' Hc) as Hcell.
      pose proof Hcell as (C1 & C2 & _). eapply cell_ok_wr; [exact HW | exact Hcell | lia | lia | rewrite EFR in *; unfold FR_A, SHB in *; lia].
    - apply Forall_forall. intros b Hb'. pose proof (proj1 (Forall_forall _ _) (r_arrs _ _ _ _ _ _ _ HR) b Hb') as Harr.
      pose proof Harr as (C1 & C2 & _). eapply arr_okg_wr; [exact HW | exact Harr | lia | lia | rewrite EFR in *; unfold FR_A, SHB in *; lia].
    - pose proof (r_pay _ _ _ _ _ _ _ HR) as P. pose proof (r_data _ _ _ _ _ _ _ HR) as (D1 & D2 & D3).
      pose proof (r_apart _ _ _ _ _ _ _ HR) as (_ & _ & AP3 & _). unfold IMGHI_A, app_mem, LOSH_A in AP3. rewrite ?HKHI, ?HHI in AP3.
      eapply payload_ok_wr; [exact HW | exact P | lia | lia | unfold SHB in *; lia].
    - eapply abs_ok_wr; [exact HW | exact (r_abs _ _ _ _ _ _ _ HR) | unfold SHB in *; lia].
    - intros Hlo. exfalso. unfold SHB in *. lia.
    - eapply (frames_ok_upd rho (ms_mem ms) _ A w (s_frames st) i f); [exact HW | exact HFS | exact RF | exact Hn | repeat split; reflexivity | | | rewrite HFL, HFR; unfold SHB in *; destruct (proj2 F4) as [ZLO|ZHI]; [right; lia | left; lia]].   (* [comment removed for export] *)
      + intros p (Hat & _ & Hcs & Hars & Hlen' & Hsh). pose proof (frame_at_inj rho f p p0 Hat (conj Hp0 (conj Hb0 Hfl0)) Hk) as ->.
        unfold frame_okR. cbn [f_sym f_cls f_cells f_arrs f_sh f_flag].
        change (f_size (Frame (f_sym f) (f_cls f) (f_cells f) (f_arrs f) (list_set_bytes (f_sh f) (Z.to_nat c) (z mod two64z) (Z.to_nat w)) (f_flag f))) with (f_size f).
        change (f_shn (Frame (f_sym f) (f_cls f) (f_cells f) (f_arrs f) (list_set_bytes (f_sh f) (Z.to_nat c) (z mod two64z) (Z.to_nat w)) (f_flag f))) with (f_shn f).
        rewrite E1, E2 in *. split; [exact Hat|]. split; [exact Hk|]. split; [|split; [|split]].
        * eapply Forall_cell_ok_wr; [exact HW | exact Hcs | lia | lia | unfold SHB in *; lia].
        * eapply Forall_arr_okg_wr; [exact HW | exact Hars | lia | lia | unfold SHB in *; lia].
        * rewrite length_list_set_bytes. exact Hlen'.
        * intros t b Ht. rewrite sh64.
          assert (Tl : (t < length (f_sh f))%nat) by (pose proof (nth_error_Some_length' _ _ _ Ht) as X; rewrite length_list_set_bytes in X; exact X).
          assert (BND : 0 <= SHB + 8 * rho (f_sym f) + Z.of_nat t < 2 ^ 64) by (clear - Tl Hlen' S2 S3 F8 F9; unfold SHB in *; lia).
          destruct (Nat.lt_ge_cases t (Z.to_nat c)) as [Hlt|Hge]; [|destruct (Nat.lt_ge_cases t (Z.to_nat c + Z.to_nat w)) as [Hin'|Hge2]].
          -- rewrite nth_list_set_bytes_out in Ht by (clear - Hlt; lia). destruct (Hsh t b Ht) as [Hb Hm]. split; [exact Hb|].
             rewrite sh64 in Hm. rewrite (wr_out (ms_mem ms) _ A w); [exact Hm | exact HW | exact BND | clear - Hlt Hc1; lia].
          -- replace t with (Z.to_nat c + (t - Z.to_nat c))%nat in Ht by (clear - Hge; lia). rewrite nth_list_set_bytes_in in Ht by (clear - Hge Hin' Tl; lia).
             injection Ht; intros <-. split; [apply Z.mod_pos_bound; clear - Hw; lia|].
             pose proof (st_inside (ms_mem ms) A (store_bytes w wv) HA0 HA64 HAn (t - Z.to_nat c) (Z_to_bv 8 0) ltac:(clear - Hlen Hin' Hge; rewrite Hlen; lia)) as Hst.
             replace (A + Z.of_nat (t - Z.to_nat c)) with (SHB + 8 * rho (f_sym f) + Z.of_nat t) in Hst by (clear - Hge Hc1; lia). rewrite Hst. f_equal.
             unfold store_bytes. rewrite Z_to_le_bytes_nth by (clear - Hin' Hge; lia). rewrite Z.shiftr_div_pow2 by (clear - Hge; lia).
             rewrite <- Z_to_bv8_mod. f_equal. f_equal. rewrite Hu. reflexivity.
          -- rewrite nth_list_set_bytes_out in Ht by (clear - Hge2; lia). destruct (Hsh t b Ht) as [Hb Hm]. split; [exact Hb|].
             rewrite sh64 in Hm. rewrite (wr_out (ms_mem ms) _ A w); [exact Hm | exact HW | exact BND | clear - Hge2 Hc1 Hw; lia].
      + intros p q h Hat (Hatq & Hkh & _) Hne. destruct Hat as (Hp & Hb & Hfl). destruct Hatq as (Hq & Hbq & Hflq).
        pose proof (frame_at_inj rho f p p0 (conj Hp (conj Hb Hfl)) (conj Hp0 (conj Hb0 Hfl0)) Hk) as ->.
        destruct (slot_apart (f_cls h) q (f_cls f) p0 Hkh Hq Hk Hp0 Hne) as [D _]. rewrite <- Hb0 in D.
        pose proof (frame_geom (f_cls h) q Hkh Hq) as (H1 & H2 & _ & _ & _ & _). rewrite HFR in H1. rewrite HLEN in H2.
        pose proof (sh_frame (f_cls h) q Hkh Hq (fo_align _ _ HFS)) as (T1 & T2 & T3 & T4 & T5 & T6).
        pose proof (flag_geom (f_cls h) q Hkh Hq) as (L1 & L2 & _). rewrite HFR in L2.
        destruct (f_size_cls h Hkh) as [Eh1 Eh2]. unfold frame_untouched. rewrite Eh1, Eh2, Hflq, Hbq, T1.
        unfold SHB in *. split; [|split].
        -- clear - Hc1 Hc2 Hw Hb0 G1 S3 F9 F4 H1 H2. lia.   (* [comment removed for export] *)
        -- destruct D as [D|D]; [left; clear - T5 T6 D Hc1; lia | right; clear - D S6 T5 Hc2; lia].
        -- clear - Hc1 Hc2 Hw Hb0 G1 S3 F9 F4 L1 L2 HFL. lia.
  Qed.

  (* [comment removed for export] *)
  Fixpoint ldel {X} (l : list X) (i : nat) : list X :=
    match l, i with [], _ => [] | _ :: r, O => r | x :: r, S i' => x :: ldel r i' end.
  #[using="Type"] Lemma del_frame_ldel : forall frs i, del_frame frs i = ldel frs i.
  Proof. induction frs as [|f r IH]; intros [|i]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
  #[using="Type"] Lemma nth_ldel : forall {X} (l : list X) i j, nth_error (ldel l i) j = if Nat.ltb j i then nth_error l j else nth_error l (S j).
  Proof.
    induction l as [|x r IH]; intros [|i] [|j]; cbn -[Nat.ltb]; try reflexivity; try (destruct (Nat.ltb _ _); reflexivity).
    rewrite IH. change (Nat.ltb (S j) (S i)) with (Nat.ltb j i). reflexivity.
  Qed.
  #[using="Type"] Lemma length_ldel : forall {X} (l : list X) i, (i < length l)%nat -> length (ldel l i) = (length l - 1)%nat.
  Proof. induction l as [|x r IH]; intros [|i] H; cbn in *; try lia. rewrite IH by lia. lia. Qed.
  #[using="Type"] Lemma In_ldel : forall {X} (l : list X) i x, In x (ldel l i) -> In x l.
  Proof. induction l as [|y r IH]; intros [|i] x H; cbn in *; [exact H | exact H | right; exact H | destruct H as [H|H]; [left; exact H | right; eapply IH; exact H]]. Qed.
  #[using="Type"] Lemma In_ldel_inv : forall {X} (l : list X) i x h, In x l -> nth_error l i = Some h -> x = h \/ In x (ldel l i).
  Proof.
    induction l as [|y r IH]; intros [|i] x h Hin Hn; cbn in *; [destruct Hin | destruct Hin | |].
    - injection Hn; intros ->. destruct Hin as [->|Hin]; [left; reflexivity | right; exact Hin].
    - destruct Hin as [->|Hin]; [right; left; reflexivity|]. destruct (IH i x h Hin Hn) as [E|H]; [left; exact E | right; right; exact H].
  Qed.
  #[using="Type"] Lemma combine_ldel : forall {X Y} (l : list X) (k : list Y) i, combine (ldel l i) (ldel k i) = ldel (combine l k) i.
  Proof. induction l as [|x r IH]; intros [|y k] [|i]; cbn; try reflexivity; [destruct r; reflexivity | rewrite IH; reflexivity]. Qed.
  #[using="Type"] Lemma map_ldel : forall {X Y} (g : X -> Y) l i, map g (ldel l i) = ldel (map g l) i.
  Proof. induction l as [|x r IH]; intros [|i]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
  #[using="Type"] Lemma NoDup_ldel : forall {X} (l : list X) i, NoDup l -> NoDup (ldel l i).
  Proof.
    induction l as [|x r IH]; intros [|i] ND; cbn; [exact ND | exact ND | |]; inversion ND as [|x' r' Hni ND']; subst; [exact ND'|].
    constructor; [|apply IH; exact ND']. intros Hin. apply Hni. apply list_elem_of_In. eapply In_ldel. apply list_elem_of_In. exact Hin.
  Qed.

  #[using="segs"] Lemma frames_ok_del : forall rho m m' frs i f p0,
    fs_ok FS m -> frames_ok U FS rho m frs -> nth_frame frs i = Some f -> frame_at FS rho f p0 ->
    wr_agree m m' (fs_flag FS (f_cls f) p0) 1 -> m' (w64 (fs_flag FS (f_cls f) p0)) = Some (Z_to_bv 8 0) ->
    frames_ok U FS rho m' (del_frame frs i).
  Proof.
    intros rho m m' frs i f p0 HFS ((ps & F2 & ND) & FL & REST) Hn Hat0 HW Hz. rewrite del_frame_ldel.
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    pose proof (fo_lo _ _ HFS) as LO. pose proof (fo_app _ _ HFS) as LOAPP. pose proof (fo_hi _ _ HFS) as HI. unfold IMGHI_A in LO. unfold app_mem, LOSH_A, KHI_A, FS_LEN in LOAPP. rewrite HHI, HLEN in HI.
    pose proof (proj1 (Forall2_nth _ _ _) F2) as [L F2n].
    assert (Hi : (i < length frs)%nat) by (apply (proj1 (nth_error_Some frs i)); rewrite <- nth_frame_error, Hn; discriminate).
    destruct (nth_error ps i) as [p|] eqn:Ep; [|apply nth_error_None in Ep; lia].
    pose proof (F2n i f p ltac:(rewrite <- nth_frame_error; exact Hn) Ep) as Hf. pose proof Hf as (Hat & Hk & _).
    pose proof (frame_at_inj rho f p p0 Hat Hat0 Hk) as <-.
    pose proof (flag_geom (f_cls f) p Hk (proj1 Hat)) as (L1 & L2 & L3). rewrite HFL in L1, L3. rewrite HFR in L2.
    (* [comment removed for export] *)
    assert (UNT : forall h q, frame_okR U FS rho m h q -> (f_cls h, q) <> (f_cls f, p) -> frame_okR U FS rho m' h q).
    { intros h q Hh Hne. eapply frame_okR_wr; [exact HW | exact HFS | exact Hh |]. destruct Hh as ((Hq & Hbq & Hflq) & Kh & _).
      destruct (slot_apart (f_cls h) q (f_cls f) p Kh Hq Hk (proj1 Hat) Hne) as [_ DF].
      pose proof (frame_geom (f_cls h) q Kh Hq) as (H1 & H2 & _). rewrite HFR in H1.
      pose proof (sh_frame (f_cls h) q Kh Hq (fo_align _ _ HFS)) as (T1 & T2 & T3 & _).
      pose proof (flag_geom (f_cls h) q Kh Hq) as (M1 & M2 & _). rewrite HFL in M1. rewrite HFR in M2.
      destruct (f_size_cls h Kh) as [Eh1 Eh2]. unfold frame_untouched. rewrite Eh1, Eh2, Hbq, Hflq, T1.
      assert (FS8 : FS / 8 <= 17592184598016) by (apply Z.div_le_upper_bound; lia).
      unfold sh in T3. rewrite ESH, HSH in T3. unfold SHB in *. lia. }
    (* [comment removed for export] *)
    assert (LIVE1 : forall k q, live_at FS rho (ldel frs i) k q -> live_at FS rho frs k q /\ (k, q) <> (f_cls f, p)).
    { intros k q (h & Hin & Hkq & Hatq). split; [exists h; split; [eapply In_ldel; exact Hin | split; assumption]|].
      apply In_nth_error in Hin. destruct Hin as [j Hj]. rewrite nth_ldel in Hj.
      set (j' := if Nat.ltb j i then j else S j) in *.
      assert (Hj' : nth_error frs j' = Some h /\ j' <> i) by (subst j'; destruct (Nat.ltb_spec j i); split; try exact Hj; lia).
      destruct Hj' as [Hh Hne].
      assert (Hjl : (j' < length ps)%nat) by (rewrite <- L; apply (proj1 (nth_error_Some frs j')); rewrite Hh; discriminate).
      destruct (nth_error ps j') as [q'|] eqn:Eq'; [|apply nth_error_None in Eq'; lia].
      pose proof (F2n j' h q' Hh Eq') as Hh'. pose proof Hh' as (Hatq' & Kh & _).
      pose proof (frame_at_inj rho h q q' Hatq Hatq' Kh) as ->.
      rewrite <- Hkq. eapply (frames_slots_ne rho m frs ps j' i h f q' p F2 ND Hne); [rewrite nth_frame_error; exact Hh | exact Eq' | exact Hn | exact Ep]. }
    assert (LIVE2 : forall k q, live_at FS rho frs k q -> (k, q) <> (f_cls f, p) -> live_at FS rho (ldel frs i) k q).
    { intros k q (h & Hin & Hkq & Hatq) Hne. destruct (In_ldel_inv frs i h f Hin ltac:(rewrite <- nth_frame_error; exact Hn)) as [->|Hin'].
      - exfalso. apply Hne. rewrite <- Hkq. f_equal. eapply frame_at_inj; [exact Hatq | exact Hat | exact Hk].
      - exists h. split; [exact Hin' | split; assumption]. }
    split; [|split].
    - exists (ldel ps i). split.
      + apply Forall2_nth. split; [rewrite !length_ldel by lia; lia|].
        intros j x y Hx Hy. rewrite (nth_ldel frs i j) in Hx. rewrite (nth_ldel ps i j) in Hy.
        set (j' := if Nat.ltb j i then j else S j) in *.
        assert (HH : nth_error frs j' = Some x /\ nth_error ps j' = Some y /\ j' <> i) by (subst j'; destruct (Nat.ltb_spec j i); repeat split; try assumption; lia).
        destruct HH as (Hx2 & Hy2 & Hne).
        pose proof (F2n j' x y Hx2 Hy2) as Hx'. apply UNT; [exact Hx'|].
        eapply (frames_slots_ne rho m frs ps j' i x f y p F2 ND Hne); [rewrite nth_frame_error; exact Hx2 | exact Hy2 | exact Hn | exact Ep].
      + rewrite map_ldel, combine_ldel. apply NoDup_ldel. exact ND.
    - intros k q Hk' Hq. pose proof (flag_geom k q Hk' Hq) as (M1 & M2 & _). rewrite HFL in M1. rewrite HFR in M2.
      destruct (FL k q Hk' Hq) as [X1 X2]. split.
      + intros HL. destruct (LIVE1 k q HL) as [HL' Hne].
        destruct (slot_apart k q (f_cls f) p Hk' Hq Hk (proj1 Hat) Hne) as [_ DF].
        eapply mem_byte_wr; [exact HW | apply X1; exact HL' | lia | lia].
      + intros HNL. destruct (Z.eq_dec (fs_flag FS k q) (fs_flag FS (f_cls f) p)) as [E|NE].
        * unfold mem_byte. rewrite w64_same, E. exact Hz.
        * eapply mem_byte_wr; [exact HW | | lia | lia]. apply X2. intros HL. apply HNL. apply LIVE2; [exact HL|].
          intros EE. apply NE. injection EE; intros -> ->. reflexivity.
    - intros j Hj Hnf. eapply mem_byte_wr; [exact HW | apply REST; [exact Hj | exact Hnf] | lia |].
      specialize (Hnf (f_cls f) p Hk (proj1 Hat)). lia.
  Qed.

  #[using="UOK"] Lemma R_flag_store : forall rho st ms i f,
    wf_state st = true -> R U G FS M0 rho st ms -> nth_frame (s_frames st) i = Some f ->
    let m' := wbytes (ms_mem ms) (w64 (rho (f_flag f))) (store_bytes 1 (w64 0)) in
    store_ok segs (ms_mem ms) (w64 (rho (f_flag f))) 1 = true /\
    R U G FS M0 rho (set_frames st (del_frame (s_frames st) i)) (ms_with_mem ms m').
  Proof.
    intros rho st ms i f Hwf HR Hn m'. subst m'.
    pose proof (r_frames _ _ _ _ _ _ _ HR) as RF. pose proof (r_fs _ _ _ _ _ _ _ HR) as HFS.
    destruct (frames_nth rho (ms_mem ms) (s_frames st) i f RF Hn) as (p0 & Hf0 & Hin).
    pose proof Hf0 as ((Hp0 & Hb0 & Hfl0) & Hk & _).
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    pose proof (flag_geom (f_cls f) p0 Hk Hp0) as (L1 & L2 & L3). rewrite HFL in L1, L3. rewrite HFR in L2. rewrite <- Hfl0 in L1, L2, L3.
    pose proof (R_geom _ _ _ HR) as GE. pose proof (geom_facts _ _ GE) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    set (A := rho (f_flag f)) in *.
    pose proof (length_store_bytes 1 (w64 0)) as Hlen. change (Z.to_nat 1) with 1%nat in Hlen.
    assert (HA0 : 0 <= A) by lia. assert (HA64 : A < 2 ^ 64) by lia.
    assert (HAn : A + Z.of_nat (length (store_bytes 1 (w64 0))) <= 2 ^ 64) by (rewrite Hlen; change (Z.of_nat 1) with 1; lia).
    split.
    { apply store_ok_of_all; rewrite w64_unsigned_small by lia; [change (Z.of_nat 1) with 1; lia|].
      intros x Hx. change (Z.of_nat 1) with 1 in Hx. destruct (fo_def _ _ HFS (bv_unsigned x - FS) ltac:(lia)) as [bb Hbb].
      replace (FS + (bv_unsigned x - FS)) with (bv_unsigned x) in Hbb by lia. rewrite w64_same, w64_of_unsigned in Hbb.
      unfold wview. rewrite Hbb. discriminate. }
    pose proof (wbytes_wr_agree (ms_mem ms) A (store_bytes 1 (w64 0)) HA0 HA64 HAn) as HW. rewrite Hlen in HW. change (Z.of_nat 1) with 1 in HW.
    pose proof (uo_frA U UOK) as EFR. pose proof (r_sp0 _ _ _ _ _ _ _ HR) as Rsp0.
    eapply (R_wr rho st _ ms _ A 1 HR HW); cbn -[store_bytes]; try reflexivity.
    - right; right; right; left. rewrite HFL, HFR. lia.
    - intros x Hx. right; right; left. lia.
    - apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (r_stk _ _ _ _ _ _ _ HR) c Hc) as Hcell.
      pose proof Hcell as (C1 & C2 & _). eapply cell_ok_wr; [exact HW | exact Hcell | lia | lia | rewrite EFR in *; unfold FR_A in *; lia].
    - apply Forall_forall. intros b Hb'. pose proof (proj1 (Forall_forall _ _) (r_arrs _ _ _ _ _ _ _ HR) b Hb') as Harr.
      pose proof Harr as (C1 & C2 & _). eapply arr_okg_wr; [exact HW | exact Harr | lia | lia | rewrite EFR in *; unfold FR_A in *; lia].
    - pose proof (r_pay _ _ _ _ _ _ _ HR) as P. pose proof (r_data _ _ _ _ _ _ _ HR) as (D1 & D2 & D3).
      pose proof (r_apart _ _ _ _ _ _ _ HR) as (_ & _ & _ & _ & AP5). rewrite HLEN in AP5.
      eapply payload_ok_wr; [exact HW | exact P | lia | lia | lia].
    - eapply abs_ok_wr; [exact HW | exact (r_abs _ _ _ _ _ _ _ HR) | lia].
    - intros Hlo. exfalso. lia.
    - eapply (frames_ok_del rho (ms_mem ms) _ (s_frames st) i f p0); [exact HFS | exact RF | exact Hn | exact (conj Hp0 (conj Hb0 Hfl0)) | rewrite <- Hfl0; exact HW |].
      rewrite <- Hfl0. pose proof (st_inside (ms_mem ms) A (store_bytes 1 (w64 0)) HA0 HA64 HAn 0 (Z_to_bv 8 0) ltac:(cbn; lia)) as Hst.
      rewrite Z.add_0_r in Hst. exact Hst.
  Qed.

  #[using="UOK"] Lemma store_abs_sound : forall rho st ms a w v wv st',
    wf_state st = true -> R U G FS M0 rho st ms -> val_ok rho v wv -> 0 < w -> w <= 8 ->
    store_abs U st a w v = Some st' ->
    store_ok segs (ms_mem ms) (w64 a) (Z.to_nat w) = true
    /\ R U G FS M0 rho st' (ms_with_mem ms (wbytes (ms_mem ms) (w64 a) (store_bytes w wv)))
    /\ (s_next st' = s_next st /\ s_pc st' = s_pc st /\ s_regs st' = s_regs st /\ s_resv st' = s_resv st).
  Proof.
    intros rho st ms a w v wv st' Hwf HR Hv Hw Hw8 H. unfold store_abs in H.
    destruct (in_ranges a w (ue_rw U)) eqn:Hrw; [|discriminate]. destruct (ro_clear U a w) eqn:Hroc; [|discriminate]. cbn [andb] in H.
    destruct (aval_lit v) as [z|] eqn:Hz; [|discriminate]. injection H; intros <-.
    destruct (R_abs_store rho st ms a w z v wv Hwf HR Hrw Hroc Hw Hw8 Hv Hz) as [So HR'].
    split; [exact So|]. split; [exact HR'|]. cbn. repeat split; reflexivity.
  Qed.

  #[using="UOK"] Lemma store_frame_lit_sound : forall rho st ms i f off w v wv st',
    wf_state st = true -> R U G FS M0 rho st ms -> val_ok rho v wv -> aval_below v (s_next st) = true -> 0 < w -> w <= 8 ->
    nth_frame (s_frames st) i = Some f ->
    store_frame_lit st i off w v = Some st' ->
    store_ok segs (ms_mem ms) (w64 (64 * rho (f_sym f) + off)) (Z.to_nat w) = true
    /\ R U G FS M0 rho st' (ms_with_mem ms (wbytes (ms_mem ms) (w64 (64 * rho (f_sym f) + off)) (store_bytes w wv)))
    /\ (s_next st' = s_next st /\ s_pc st' = s_pc st /\ s_regs st' = s_regs st /\ s_resv st' = s_resv st).
  Proof.
    intros rho st ms i f off w v wv st' Hwf HR Hv Hvb Hw Hw8 Hn H.
    pose proof (wf_parts st Hwf) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wfr & _).
    pose proof (R_to_VS _ _ _ HR) as [HC _].
    destruct (frames_nth rho (ms_mem ms) (s_frames st) i f (r_frames _ _ _ _ _ _ _ HR) Hn) as (p & Hf & Hin).
    rewrite forallb_forall in Wfr. destruct (frame_wf_parts _ f (Wfr f Hin)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Wad).
    destruct Hf as ((Hp & Hb & Hfl) & Hk & Hcs & Har & _).
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    pose proof (frame_geom (f_cls f) p Hk Hp) as (G1 & G2 & _). rewrite HLEN in G2.
    pose proof (fo_lo _ _ (r_fs _ _ _ _ _ _ _ HR)) as LO. pose proof (fo_app _ _ (r_fs _ _ _ _ _ _ _ HR)) as LOAPP. pose proof (fo_hi _ _ (r_fs _ _ _ _ _ _ _ HR)) as HI. unfold IMGHI_A in LO. unfold app_mem, LOSH_A, KHI_A, FS_LEN in LOAPP. rewrite HHI, HLEN in HI.
    destruct (f_size_cls f Hk) as [E1 _].
    unfold store_frame_lit in H. rewrite Hn in H.
    destruct (store_space_lit 0 (f_size f) (f_cells f) (f_arrs f) (s_ctx st) off w v) as [[cs' ars']|] eqn:E; [|discriminate].
    injection H; intros <-.
    destruct (store_space_lit_ok rho (s_ctx st) (ms_mem ms) (64 * rho (f_sym f)) 0 (f_size f) (f_cells f) (f_arrs f) off w v wv cs' ars'
                HC Hv Hw Hw8 ltac:(lia) ltac:(lia) Hcs Har Wad E) as (W1 & W2 & CELLS & ARRS).
    destruct (R_frame_store rho st ms i f off w wv cs' ars' Hwf HR Hn W1 W2 Hw Hw8 CELLS ARRS) as [So HR'].
    split; [exact So|]. split; [exact HR'|]. cbn. repeat split; reflexivity.
  Qed.

  #[using="UOK"] Lemma store_frame_sym_sound : forall rho st ms i f off w v wv st',
    wf_state st = true -> R U G FS M0 rho st ms -> val_ok rho v wv -> aval_below v (s_next st) = true -> 0 < w -> w <= 8 ->
    nth_frame (s_frames st) i = Some f ->
    store_frame_sym st i off w v = Some st' ->
    store_ok segs (ms_mem ms) (w64 (64 * rho (f_sym f) + evl rho off)) (Z.to_nat w) = true
    /\ R U G FS M0 rho st' (ms_with_mem ms (wbytes (ms_mem ms) (w64 (64 * rho (f_sym f) + evl rho off)) (store_bytes w wv)))
    /\ (s_next st' = s_next st /\ s_pc st' = s_pc st /\ s_regs st' = s_regs st /\ s_resv st' = s_resv st).
  Proof.
    intros rho st ms i f off w v wv st' Hwf HR Hv Hvb Hw Hw8 Hn H.
    pose proof (wf_parts st Hwf) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wfr & _).
    pose proof (R_to_VS _ _ _ HR) as [HC _].
    destruct (frames_nth rho (ms_mem ms) (s_frames st) i f (r_frames _ _ _ _ _ _ _ HR) Hn) as (p & Hf & Hin).
    rewrite forallb_forall in Wfr. destruct (frame_wf_parts _ f (Wfr f Hin)) as (_ & _ & _ & _ & _ & _ & _ & Wdisj & _ & Wad).
    destruct Hf as ((Hp & Hb & Hfl) & Hk & Hcs & Har & _).
    destruct fs_consts as (HLEN & HFR & HFL & HKHI & HHI & ESH & HSL & HSH).
    pose proof (frame_geom (f_cls f) p Hk Hp) as (G1 & G2 & _). rewrite HLEN in G2.
    pose proof (fo_lo _ _ (r_fs _ _ _ _ _ _ _ HR)) as LO. pose proof (fo_app _ _ (r_fs _ _ _ _ _ _ _ HR)) as LOAPP. pose proof (fo_hi _ _ (r_fs _ _ _ _ _ _ _ HR)) as HI. unfold IMGHI_A in LO. unfold app_mem, LOSH_A, KHI_A, FS_LEN in LOAPP. rewrite HHI, HLEN in HI.
    destruct (f_size_cls f Hk) as [E1 _].
    unfold store_frame_sym in H. rewrite Hn in H.
    destruct (store_space_sym 0 (f_size f) (f_cells f) (f_arrs f) (s_ctx st) off w v) as [[cs' ars']|] eqn:E; [|discriminate].
    injection H; intros <-.
    destruct (store_space_sym_ok rho (s_ctx st) (ms_mem ms) (64 * rho (f_sym f)) 0 (f_size f) (f_cells f) (f_arrs f) off w v wv cs' ars'
                HC Hv Hw Hw8 ltac:(lia) ltac:(lia) Hcs Har Wad Wdisj E) as (W1 & W2 & CELLS & ARRS).
    destruct (R_frame_store rho st ms i f (evl rho off) w wv cs' ars' Hwf HR Hn W1 W2 Hw Hw8 CELLS ARRS) as [So HR'].
    split; [exact So|]. split; [exact HR'|]. cbn. repeat split; reflexivity.
  Qed.

  #[using="UOK"] Lemma store_shframe_sound : forall rho st ms i f t w v wv st',
    wf_state st = true -> R U G FS M0 rho st ms -> val_ok rho v wv -> 0 < w -> w <= 8 ->
    nth_frame (s_frames st) i = Some f ->
    store_shframe st i t w v = Some st' ->
    store_ok segs (ms_mem ms) (w64 (SHB + 8 * rho (f_sym f) + evl rho t)) (Z.to_nat w) = true
    /\ R U G FS M0 rho st' (ms_with_mem ms (wbytes (ms_mem ms) (w64 (SHB + 8 * rho (f_sym f) + evl rho t)) (store_bytes w wv)))
    /\ (s_next st' = s_next st /\ s_pc st' = s_pc st /\ s_regs st' = s_regs st /\ s_resv st' = s_resv st).
  Proof.
    intros rho st ms i f t w v wv st' Hwf HR Hv Hw Hw8 Hn H.
    unfold store_shframe in H. rewrite Hn in H.
    destruct (is_const t) as [c|] eqn:Kc; [|discriminate]. destruct (aval_lit v) as [z|] eqn:Hz; [|discriminate].
    destruct (Z.leb 0 c &&& Z.leb (c + w) (f_shn f))%bool eqn:Eb; [|discriminate]. injection H; intros <-.
    apply andb_prop in Eb as [Eb1 Eb2]. apply Z.leb_le in Eb1. apply Z.leb_le in Eb2.
    rewrite (is_const_sound rho t c Kc).
    destruct (R_shframe_store rho st ms i f c w z v wv Hwf HR Hn Eb1 Eb2 Hw Hw8 Hv Hz) as [So HR'].
    split; [exact So|]. split; [exact HR'|]. cbn. repeat split; reflexivity.
  Qed.

  #[using="UOK"] Lemma store_flag_sound : forall rho st ms i f w v wv st',
    wf_state st = true -> R U G FS M0 rho st ms -> val_ok rho v wv ->
    nth_frame (s_frames st) i = Some f ->
    store_flag st i w v = Some st' ->
    store_ok segs (ms_mem ms) (w64 (rho (f_flag f))) (Z.to_nat w) = true
    /\ R U G FS M0 rho st' (ms_with_mem ms (wbytes (ms_mem ms) (w64 (rho (f_flag f))) (store_bytes w wv)))
    /\ (s_next st' = s_next st /\ s_pc st' = s_pc st /\ s_regs st' = s_regs st /\ s_resv st' = s_resv st).
  Proof.
    intros rho st ms i f w v wv st' Hwf HR Hv Hn H.
    unfold store_flag in H. destruct (aval_lit v) as [z|] eqn:Hz; [|discriminate]. destruct z; try discriminate.
    destruct (Z.eqb w 1 &&& Nat.eqb (S i) (length (s_frames st)))%bool eqn:Eb; [|discriminate]. injection H; intros <-.
    apply andb_prop in Eb as [Eb1 _]. apply Z.eqb_eq in Eb1. subst w.
    pose proof (aval_lit_sound rho v 0 wv Hz Hv) as ->.
    destruct (R_flag_store rho st ms i f Hwf HR Hn) as [So HR'].
    split; [exact So|]. split; [exact HR'|]. cbn. repeat split; reflexivity.
  Qed.

  #[using="UOK"] Lemma do_store_sound : forall rho st ms av wa w v wv st',
    wf_state st = true -> R U G FS M0 rho st ms ->
    val_ok rho av wa -> aval_below av (s_next st) = true ->
    val_ok rho v wv -> aval_below v (s_next st) = true ->
    0 < w -> w <= 8 ->
    do_store U st av w v = Some st' ->
    store_ok segs (ms_mem ms) wa (Z.to_nat w) = true
    /\ R U G FS M0 rho st' (ms_with_mem ms (write_to_mem (ms_mem ms) wa (store_bytes w wv)))
    /\ s_next st' = s_next st /\ s_pc st' = s_pc st /\ s_regs st' = s_regs st /\ s_resv st' = s_resv st.
  Proof.
    intros rho st ms av wa w v wv st' Hwf HR Hav Hbel Hv Hvb Hw Hw8 H.
    pose proof (wf_parts st Hwf) as (_ & _ & _ & _ & _ & _ & Wdisj & W18 & _ & Wad & Wfr & _).
    pose proof (classify_spec rho (s_frames st) av wa (s_next st) Hav Hbel W18 Wfr) as HC.
    rewrite write_to_mem_wbytes.
    unfold do_store in H.
    destruct (classify (s_frames st) av) as [[off|off|off|a|i off|i off|i t|t|t|i]|] eqn:Ecl; try discriminate.
    - subst wa. destruct (store_stack_lit_sound rho st ms off w v wv st' Hwf HR Hv Hvb Hw Hw8 H) as (So & HR' & E). split; [exact So|]. split; [exact HR'|exact E].
    - destruct HC as [-> Hob]. destruct (store_stack_sym_sound rho st ms off w v wv st' Hwf HR Hv Hvb Hw Hw8 H) as (So & HR' & E). split; [exact So|]. split; [exact HR'|exact E].
    - destruct HC as [-> Ha]. destruct (store_abs_sound rho st ms a w v wv st' Hwf HR Hv Hw Hw8 H) as (So & HR' & E). split; [exact So|]. split; [exact HR'|exact E].
    - destruct HC as (f & Hn & ->). destruct (store_frame_lit_sound rho st ms i f off w v wv st' Hwf HR Hv Hvb Hw Hw8 Hn H) as (So & HR' & E). split; [exact So|]. split; [exact HR'|exact E].
    - destruct HC as (f & Hn & -> & _). destruct (store_frame_sym_sound rho st ms i f off w v wv st' Hwf HR Hv Hvb Hw Hw8 Hn H) as (So & HR' & E). split; [exact So|]. split; [exact HR'|exact E].
    - destruct HC as (f & Hn & -> & _). destruct (store_shframe_sound rho st ms i f t w v wv st' Hwf HR Hv Hw Hw8 Hn H) as (So & HR' & E). split; [exact So|]. split; [exact HR'|exact E].
    - destruct HC as (f & Hn & ->). destruct (store_flag_sound rho st ms i f w v wv st' Hwf HR Hv Hn H) as (So & HR' & E). split; [exact So|]. split; [exact HR'|exact E].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma In_filterP : forall {A} (P : A -> Prop) {D : forall x, Decision (P x)} (l : list A) x,
    In x (filter P l) -> In x l /\ P x.
  Proof.
    intros A P D l x H. apply list_elem_of_In in H. apply list_basics.list.list_elem_of_filter in H as [HP Hin].
    split; [apply list_elem_of_In; exact Hin | exact HP].
  Qed.

  #[using="Type"] Lemma cells_kill_sub : forall cs off w c, In c (cells_kill cs off w) -> In c cs.
  Proof.
    induction cs as [|d r IH]; cbn; intros off w c H; [exact H|].
    destruct (overlaps (c_off d) (c_w d) off w); [right; eapply IH; exact H|].
    destruct H as [H|H]; [left; exact H | right; eapply IH; exact H].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma R_same_mem : forall rho st st' ms,
    R U G FS M0 rho st ms -> s_pc st' = s_pc st -> s_regs st' = s_regs st -> s_ctx st' = s_ctx st -> s_next st' = s_next st ->
    s_resv st' = s_resv st -> s_pcache st' = s_pcache st -> s_pay st' = s_pay st -> s_abs st' = s_abs st ->
    Forall (stack_cell_ok U rho (ms_mem ms) (rho SYM_SP0)) (s_stk st') ->
    Forall (arr_ok U rho (ms_mem ms) (rho SYM_SP0)) (s_arrs st') ->
    frames_ok U FS rho (ms_mem ms) (s_frames st') ->
    R U G FS M0 rho st' ms.
  Proof.
    intros rho st st' ms HR E1 E2 E3 E4 E5 E6 E7 E8 STK ARRS FRS.
    destruct HR as [Rglob Rpc Rsvc Rregs Rvs Rstk Rarrs Rwin Rpay Rabs Rresv Rfrm Rframe Rsp0 Ralign Rra Rdata
                    Rcomp Rapart Rrt Rgsh Rshstk Rshpay Rmctx Rfs Rframes].
    constructor; rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8; assumption.
  Qed.

  #[using="Type"] Lemma declare_space_array_ok : forall rho m b lo hi cs ars alo ahi,
    Forall (cell_ok U rho m b lo hi) cs -> Forall (arr_okg U rho m b lo hi) ars -> lo <= alo -> ahi <= hi ->
    let (cs', ars') := declare_space_array cs ars alo ahi in
    Forall (cell_ok U rho m b lo hi) cs' /\ Forall (arr_okg U rho m b lo hi) ars'.
  Proof.
    intros rho m b lo hi cs ars alo ahi Hcs Hars H1 H2. cbn. split.
    - apply Forall_forall. intros c Hc. apply cells_kill_sub in Hc. exact (proj1 (Forall_forall _ _) Hcs c Hc).
    - constructor.
      + unfold arr_okg; cbn. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
        * intros j Hj. exfalso. revert Hj. unfold evl, lconst; cbn. lia.
        * intros K1. exfalso. revert K1. unfold evl, lconst; cbn. lia.
      + apply Forall_forall. intros a Ha. apply In_filterP in Ha as [Ha _]. exact (proj1 (Forall_forall _ _) Hars a Ha).
  Qed.

  #[using="Type"] Lemma declare_array_sound : forall rho st ms lo hi st',
    wf_state st = true -> R U G FS M0 rho st ms ->
    declare_array U st lo hi = Some st' ->
    R U G FS M0 rho st' ms /\ s_next st' = s_next st /\ s_pc st' = s_pc st /\ s_regs st' = s_regs st /\ s_resv st' = s_resv st
    /\ s_ctx st' = s_ctx st /\ s_pcache st' = s_pcache st /\ s_pay st' = s_pay st /\ s_abs st' = s_abs st.
  Proof.
    intros rho st ms lo hi st' Hwf HR H. unfold declare_array in H.
    destruct (in_window U lo (hi - lo)) eqn:W; cbn [negb] in H; [|discriminate].
    unfold in_window, in_win in W. apply andb_prop in W as [W1 W2]. apply Z.leb_le in W1. apply Z.leb_le in W2.
    pose proof (declare_space_array_ok rho (ms_mem ms) (rho SYM_SP0) (- ue_fr U) 0 (s_stk st) (s_arrs st) lo hi
                  (r_stk _ _ _ _ _ _ _ HR) (r_arrs _ _ _ _ _ _ _ HR) ltac:(lia) ltac:(lia)) as X.
    destruct (declare_space_array (s_stk st) (s_arrs st) lo hi) as [cs' ars']. destruct X as [CELLS ARRS].
    injection H; intros <-. split; [| cbn; repeat split; reflexivity].
    eapply R_same_mem; [exact HR | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact CELLS | exact ARRS | exact (r_frames _ _ _ _ _ _ _ HR)].
  Qed.

  #[using="segs"] Lemma declare_frame_array_sound : forall rho st ms i lo hi st',
    wf_state st = true -> R U G FS M0 rho st ms ->
    declare_frame_array st i lo hi = Some st' ->
    R U G FS M0 rho st' ms /\ s_next st' = s_next st /\ s_pc st' = s_pc st /\ s_regs st' = s_regs st /\ s_resv st' = s_resv st
    /\ s_ctx st' = s_ctx st /\ s_pcache st' = s_pcache st /\ s_pay st' = s_pay st /\ s_abs st' = s_abs st.
  Proof.
    intros rho st ms i lo hi st' Hwf HR H. unfold declare_frame_array in H.
    destruct (nth_frame (s_frames st) i) as [f|] eqn:Hn; [|discriminate].
    destruct (in_win 0 (f_size f) lo (hi - lo)) eqn:W; cbn [negb] in H; [|discriminate].
    unfold in_win in W. apply andb_prop in W as [W1 W2]. apply Z.leb_le in W1. apply Z.leb_le in W2.
    pose proof (r_frames _ _ _ _ _ _ _ HR) as RF. pose proof (r_fs _ _ _ _ _ _ _ HR) as HFS.
    destruct (frames_nth rho (ms_mem ms) (s_frames st) i f RF Hn) as (p0 & Hf0 & Hin). pose proof Hf0 as (Hat0 & Hk & Hcs & Hars & _).
    pose proof (declare_space_array_ok rho (ms_mem ms) (64 * rho (f_sym f)) 0 (f_size f) (f_cells f) (f_arrs f) lo hi Hcs Hars ltac:(lia) ltac:(lia)) as X.
    destruct (declare_space_array (f_cells f) (f_arrs f) lo hi) as [cs' ars']. destruct X as [CELLS ARRS].
    injection H; intros <-. split; [| cbn; repeat split; reflexivity].
    eapply R_same_mem; [exact HR | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
                       | exact (r_stk _ _ _ _ _ _ _ HR) | exact (r_arrs _ _ _ _ _ _ _ HR) |]. cbn.
    assert (HW : wr_agree (ms_mem ms) (ms_mem ms) 0 0).
    { split; [lia|]. split; [lia|]. split; [lia|]. split; [intros; reflexivity | intros x b Hb; exists b; exact Hb]. }
    eapply (frames_ok_upd rho (ms_mem ms) (ms_mem ms) 0 0 (s_frames st) i f); [exact HW | exact HFS | exact RF | exact Hn | repeat split; reflexivity | | | left; pose proof (fo_lo _ _ HFS); unfold IMGHI_A, app_mem, LOSH_A, KHI_A, FS_FLAGS, FS_LEN in *; lia].
    - intros p (Hat & _ & _ & _ & Hlen' & Hsh). pose proof (frame_at_inj rho f p p0 Hat Hat0 Hk) as ->.
      unfold frame_okR, frame_at. cbn [f_sym f_cls f_flag f_sh f_cells f_arrs frame_set_space].
      pose proof (frame_set_space_eqs f cs' ars') as (_ & _ & _ & _ & _ & _ & Q7 & Q8). rewrite Q7, Q8.
      split; [exact Hat0|]. split; [exact Hk|]. split; [exact CELLS|]. split; [exact ARRS|]. split; [exact Hlen' | exact Hsh].
    - intros p q h _ ((Hq & Hbq & Hflq) & Kh & _) _. pose proof (frame_geom (f_cls h) q Kh Hq) as (H1 & _). pose proof (flag_geom (f_cls h) q Kh Hq) as (L1 & _).
      pose proof (fo_lo _ _ HFS). pose proof (fo_app _ _ HFS). unfold frame_untouched, sh. rewrite Hbq, Hflq.
      assert (0 <= fs_frame FS (f_cls h) q / 8) by (apply Z.div_pos; unfold IMGHI_A, app_mem, LOSH_A, KHI_A, FS_FRAMES, FS_LEN in *; lia). unfold IMGHI_A, app_mem, LOSH_A, KHI_A, FS_LEN, FS_FRAMES, FS_FLAGS, SH_A in *. lia.
  Qed.

  #[using="Type"] Lemma drop_below_sound : forall rho st ms k,
    R U G FS M0 rho st ms -> R U G FS M0 rho (drop_below st k) ms.
  Proof.
    intros rho st ms k HR.
    eapply R_same_mem; [exact HR | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | | | exact (r_frames _ _ _ _ _ _ _ HR)]; cbn.
    - unfold cells_drop_below. apply Forall_forall. intros c Hc. apply In_filterP in Hc as [Hc _]. exact (proj1 (Forall_forall _ _) (r_stk _ _ _ _ _ _ _ HR) c Hc).
    - apply Forall_forall. intros a Ha. apply In_filterP in Ha as [Ha _]. exact (proj1 (Forall_forall _ _) (r_arrs _ _ _ _ _ _ _ HR) a Ha).
  Qed.

End WithU.

End LASM2.
