(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin LxState LxMem LxStep LxCheck LxSem LxWf LxSoundVal.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import LXL LXS LXM LXI LXC LXSEM LXWF LXSV.
Open Scope Z_scope.

Module LXSM.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RDN.
  Variable segs : list Segment.

  Lemma rdn_length : forall m n a bs, rdn segs m a n = Some bs -> length bs = n.
  Proof. apply PropExec.rdn_length. Qed.

  (* [comment removed for export] *)
  Lemma rdn_app : forall m n1 n2 (a : word) bs,
    bv_unsigned a + Z.of_nat (n1 + n2) < 2 ^ 64 ->
    rdn segs m a (n1 + n2) = Some bs ->
    exists bs1 bs2, bs = bs1 ++ bs2 /\ rdn segs m a n1 = Some bs1
                    /\ rdn segs m (w64 (bv_unsigned a + Z.of_nat n1)) n2 = Some bs2.
  Proof.
    intros m n1. induction n1 as [|n1 IH]; intros n2 a bs Hnw H.
    - exists [], bs. split; [reflexivity|]. split; [reflexivity|].
      rewrite Z.add_0_r, w64_of_unsigned. exact H.
    - cbn [rdn Nat.add] in H.
      destruct (match m a with Some b => Some b | None => seg_rom segs a end) as [b|] eqn:Eb; [|discriminate].
      destruct (rdn segs m (a + 1)%bv (n1 + n2)) as [rest|] eqn:Er; [|discriminate]. injection H; intros <-.
      assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      destruct (IH n2 (a + 1)%bv rest ltac:(rewrite Hu1; lia) Er) as (bs1 & bs2 & -> & H1 & H2).
      exists (b :: bs1), bs2. split; [reflexivity|]. split.
      + cbn [rdn]. rewrite Eb, H1. reflexivity.
      + rewrite Hu1 in H2. replace (bv_unsigned a + 1 + Z.of_nat n1) with (bv_unsigned a + Z.of_nat (S n1)) in H2 by lia. exact H2.
  Qed.

  Lemma rdn_one : forall m (a : word) b, rdn segs m a 1 = Some [b] <-> (match m a with Some x => Some x | None => seg_rom segs a end) = Some b.
  Proof.
    intros. cbn [rdn]. destruct (match m a with Some x => Some x | None => seg_rom segs a end); split; intros H; try discriminate.
    - injection H; intros ->; reflexivity.
    - injection H; intros ->; reflexivity.
  Qed.
End RDN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_le_to_Z_range : forall bs, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  intros bs. split; [apply bytes_le_to_Z_nonneg|]. apply bytes_le_to_Z_bound.
Qed.

(* [comment removed for export] *)
Definition ldval (w : Z) (sx : bool) (bs : list byte) : word :=
  if Z.eqb w 8 then le_bytes_to_word bs
  else let z := bytes_le_to_Z bs in
       w64 (if sx then (if Z.leb (2 ^ (8 * w - 1)) z then z - 2 ^ (8 * w) else z) else z).

Lemma ext_lit_spec : forall sx w z, 0 < w ->
  ext_lit sx w z = (let u := z mod 2 ^ (8 * w) in if sx then (if Z.leb (2 ^ (8 * w - 1)) u then u - 2 ^ (8 * w) else u) else u).
Proof. intros. unfold ext_lit. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithU.
  Variable U : uenv.
  Variable G : sym -> Z.
  Variable M0 : word -> option byte.
  Let segs := ue_segs U.

  Lemma wf_parts : forall st, wf_state st = true ->
    let n := s_next st in
    forallb (fun v => aval_below v n) (s_regs st) = true /\
    ctx_below (s_ctx st) n = true /\
    forallb (fun c => aval_below (c_val c) n) (s_stk st) = true /\
    forallb (fun a => afact_below (ar_fact a) n) (s_arrs st) = true /\
    forallb (fun e : lin * Z * sym => let '(o, _, x) := e in (lin_below o n &&& Nat.ltb x n)%bool) (s_pcache st) = true /\
    forallb (fun e : lin * itv => lin_below (fst e) n) (s_pay st) = true /\
    forallb (fun c => negb (existsb (fun a => overlaps (ar_lo a) (ar_hi a - ar_lo a) (c_off c) (c_w c)) (s_arrs st))) (s_stk st) = true /\
    (19 <= n)%nat /\
    forallb (fun c => (Z.ltb 0 (c_w c) && Z.leb (c_w c) 8)%bool) (s_stk st) = true /\
    arrs_disjointb (s_arrs st) = true.
  Proof.
    intros st H. unfold wf_state in H.
    repeat (apply andb_prop in H as [H ?X]).
    cbn zeta. repeat split; try assumption. apply Nat.leb_le. assumption.
  Qed.

  Lemma val_bytes_ok_agree : forall n rho rho' v w bs,
    aval_below v n = true -> agree n rho rho' -> val_bytes_ok rho v w bs -> val_bytes_ok rho' v w bs.
  Proof.
    intros n rho rho' v w bs Hb Ha [Hl Hv]. split; [exact Hl|].
    destruct v as [|l|neg k a b|a b]; cbn in *; [exact I| | |].
    - rewrite (evl_agree n rho rho') by assumption. exact Hv.
    - apply andb_prop in Hb as [B1 B2]. unfold cmp_holds in *. rewrite !(evl_agree n rho rho') by assumption. exact Hv.
    - apply andb_prop in Hb as [B1 B2]. rewrite !(evl_agree n rho rho') by assumption. exact Hv.
  Qed.

  Lemma R_vext : forall rho st ms rho' st',
    wf_state st = true -> R U G M0 rho st ms -> vext rho st rho' st' -> VS rho' st' -> R U G M0 rho' st' ms.
  Proof.
    intros rho st ms rho' st' Hwf HR (Ha & Hn & Hpc & Hregs & Hstk & Harrs & Habs & Hresv & Hdepth & Hpc' & Hpay) HVS.
    destruct (wf_parts st Hwf) as (Wregs & Wctx & Wstk & Warrs & Wpc & Wpay & Wdisj & W18 & Wcw & Wad).
    assert (HG : forall x, (x < NGLOB)%nat -> rho' x = rho x) by (intros x Hx; apply Ha; unfold NGLOB in Hx; lia).
    destruct HR as [Rglob Rpc Rsvc Rregs Rvs Rstk Rarrs Rwin Rpay Rabs Rresv Rfrm Rframe Rsp0 Ralign Rra Rdata]. constructor; try assumption.
    - intros x Hx. rewrite HG by exact Hx. apply Rglob; exact Hx.
    - rewrite Hpc. exact Rpc.
    - rewrite Hregs. intros r Hr. eapply val_ok_agree; [|exact Ha|apply Rregs; exact Hr].
      rewrite forallb_forall in Wregs.
      destruct (Nat.lt_ge_cases r (length (s_regs st))) as [Hlt|Hge].
      + apply Wregs. clear -Hlt. revert r Hlt. induction (s_regs st) as [|v l IH]; intros r Hlt; cbn in Hlt; [lia|].
        destruct r; cbn; [left; reflexivity | right; apply IH; lia].
      + replace (list_get (s_regs st) r Top) with Top; [reflexivity|].
        clear -Hge. revert r Hge. induction (s_regs st) as [|v l IH]; intros r Hge; [destruct r; reflexivity|].
        destruct r; cbn in *; [lia | symmetry; symmetry; apply IH; lia].
    - rewrite Hstk. rewrite (HG SYM_SP0) by (unfold SYM_SP0, NGLOB; lia).
      apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Rstk c Hc) as (A & B & C & bs & Hrd & Hvb).
      split; [exact A|]. split; [exact B|]. split; [exact C|]. exists bs. split; [exact Hrd|].
      eapply val_bytes_ok_agree; [|exact Ha|exact Hvb]. rewrite forallb_forall in Wstk. apply (Wstk c Hc).
    - rewrite Harrs. rewrite (HG SYM_SP0) by (unfold SYM_SP0, NGLOB; lia).
      apply Forall_forall. intros a Hin. pose proof (proj1 (Forall_forall _ _) Rarrs a Hin) as (A & B & C).
      split; [exact A|]. split; [exact B|]. destruct (ar_fact a) as [f|] eqn:Ef; [|exact I].
      destruct C as (C1 & C2 & C & Cf). split; [exact C1|]. split; [exact C2|].
      rewrite forallb_forall in Warrs. specialize (Warrs a Hin). rewrite Ef in Warrs. cbn [afact_below] in Warrs.
      split.
      + intros j Hj. rewrite (evl_agree (s_next st) rho rho') in Hj by first [exact Warrs | exact Ha]. apply C. exact Hj.
      + intros H1. rewrite (evl_agree (s_next st) rho rho') in H1 by first [exact Warrs | exact Ha]. apply Cf. exact H1.
    - rewrite (HG SYM_SP0) by (unfold SYM_SP0, NGLOB; lia). exact Rwin.
    - rewrite Hpc', Hpay. unfold payload_ok. rewrite !(HG SYM_SP0), !(HG SYM_DATA), !(HG SYM_N) by (unfold SYM_SP0, SYM_DATA, SYM_N, NGLOB; lia).
      destruct Rpay as (P1 & P2 & P3 & P4). split; [exact P1|]. split; [exact P2|]. split.
      + intros off sx x Hin. rewrite forallb_forall in Wpc. specialize (Wpc _ Hin). cbn in Wpc. apply andb_prop in Wpc as [Wo Wx].
        apply Nat.ltb_lt in Wx. rewrite (evl_agree (s_next st) rho rho'), (Ha x Wx) by first [exact Wo | exact Ha]. apply P3. exact Hin.
      + intros off i Hin. rewrite forallb_forall in Wpay. specialize (Wpay _ Hin). cbn [fst] in Wpay.
        rewrite (evl_agree (s_next st) rho rho') by first [exact Wpay | exact Ha]. apply P4. exact Hin.
    - rewrite Habs. exact Rabs.
    - rewrite Hresv. exact Rresv.
    - rewrite (HG SYM_SP0) by (unfold SYM_SP0, NGLOB; lia). exact Rframe.
    - rewrite (HG SYM_SP0) by (unfold SYM_SP0, NGLOB; lia). exact Rsp0.
    - rewrite (HG SYM_SP0), (HG SYM_DATA) by (unfold SYM_SP0, SYM_DATA, NGLOB; lia). exact Ralign.
    - rewrite (HG SYM_RA) by (unfold SYM_RA, NGLOB; lia). exact Rra.
    - rewrite (HG SYM_DATA), (HG SYM_N) by (unfold SYM_DATA, SYM_N, NGLOB; lia). exact Rdata.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bytes_le_firstn : forall k bs, (k <= length bs)%nat ->
    bytes_le_to_Z (firstn k bs) = bytes_le_to_Z bs mod 2 ^ (8 * Z.of_nat k).
  Proof.
    intros k bs Hk. rewrite <- (firstn_skipn k bs) at 2. rewrite bytes_le_app.
    rewrite length_firstn, Nat.min_l by exact Hk.
    pose proof (bytes_le_to_Z_range (firstn k bs)) as [H0 H1]. rewrite length_firstn, Nat.min_l in H1 by exact Hk.
    pose proof (bytes_le_to_Z_nonneg (skipn k bs)) as H2.
    rewrite <- Z.lxor_lor by (apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0;
      destruct (Z.lt_ge_cases i (8 * Z.of_nat k)) as [Hl|Hl];
      [ rewrite (Z.shiftl_spec_low _ _ _ Hl); apply andb_false_r
      | rewrite (Z_testbit_high (8 * Z.of_nat k) (bytes_le_to_Z (firstn k bs)) i) by lia; reflexivity ]).
    rewrite <- Z.add_nocarry_lxor by (apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0;
      destruct (Z.lt_ge_cases i (8 * Z.of_nat k)) as [Hl|Hl];
      [ rewrite (Z.shiftl_spec_low _ _ _ Hl); apply andb_false_r
      | rewrite (Z_testbit_high (8 * Z.of_nat k) (bytes_le_to_Z (firstn k bs)) i) by lia; reflexivity ]).
    rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_add by lia.
    symmetry. apply Z.mod_small. lia.
  Qed.

  Lemma bytes_le_skipn : forall k bs, (k <= length bs)%nat ->
    bytes_le_to_Z (skipn k bs) = bytes_le_to_Z bs / 2 ^ (8 * Z.of_nat k).
  Proof.
    intros k bs Hk. rewrite <- (firstn_skipn k bs) at 2. rewrite bytes_le_app.
    rewrite length_firstn, Nat.min_l by exact Hk.
    pose proof (bytes_le_to_Z_range (firstn k bs)) as [H0 H1]. rewrite length_firstn, Nat.min_l in H1 by exact Hk.
    pose proof (bytes_le_to_Z_nonneg (skipn k bs)) as H2.
    rewrite <- Z.lxor_lor by (apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0;
      destruct (Z.lt_ge_cases i (8 * Z.of_nat k)) as [Hl|Hl];
      [ rewrite (Z.shiftl_spec_low _ _ _ Hl); apply andb_false_r
      | rewrite (Z_testbit_high (8 * Z.of_nat k) (bytes_le_to_Z (firstn k bs)) i) by lia; reflexivity ]).
    rewrite <- Z.add_nocarry_lxor by (apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0;
      destruct (Z.lt_ge_cases i (8 * Z.of_nat k)) as [Hl|Hl];
      [ rewrite (Z.shiftl_spec_low _ _ _ Hl); apply andb_false_r
      | rewrite (Z_testbit_high (8 * Z.of_nat k) (bytes_le_to_Z (firstn k bs)) i) by lia; reflexivity ]).
    rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.div_add by lia.
    rewrite Z.div_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma zbytes_spec : forall z i n, 0 <= i -> 0 <= n ->
    zbytes z i n = ((z mod two64z) / 2 ^ (8 * i)) mod 2 ^ (8 * n).
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma slice_mod_stable : forall z a b c, 0 <= b -> 0 <= c -> b + c <= a ->
    ((z mod 2 ^ a) / 2 ^ b) mod 2 ^ c = (z / 2 ^ b) mod 2 ^ c.
  Proof.
    intros z a b c Hb Hc Hle.
    apply Z.bits_inj'. intros i Hi.
    destruct (Z.lt_ge_cases i c) as [Hic|Hic].
    - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.div_pow2_bits by lia.
      rewrite Z.mod_pow2_bits_low by lia. reflexivity.
    - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
  Qed.

  Lemma slice_via_sublist : forall (bs : list byte) i w,
    (i + w <= length bs)%nat ->
    bytes_le_to_Z (firstn w (skipn i bs)) = (bytes_le_to_Z bs / 2 ^ (8 * Z.of_nat i)) mod 2 ^ (8 * Z.of_nat w).
  Proof.
    intros bs i w H. rewrite bytes_le_firstn by (rewrite length_skipn; lia). rewrite bytes_le_skipn by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ldval_small : forall w sx bs, 0 < w -> w < 8 -> Z.of_nat (length bs) = w ->
    ldval w sx bs = w64 (ext_lit sx w (bytes_le_to_Z bs)).
  Proof.
    intros w sx bs Hw Hw8 Hl. unfold ldval, ext_lit.
    assert (Hne : Z.eqb w 8 = false) by (apply Z.eqb_neq; lia). rewrite Hne.
    pose proof (bytes_le_to_Z_range bs) as Hr. rewrite Hl in Hr.
    rewrite (Z.mod_small (bytes_le_to_Z bs)) by lia. reflexivity.
  Qed.

  Lemma ldval_8 : forall sx bs, Z.of_nat (length bs) = 8 -> ldval 8 sx bs = w64 (ext_lit sx 8 (bytes_le_to_Z bs)).
  Proof.
    intros sx bs Hl. unfold ldval, ext_lit. rewrite Z.eqb_refl. unfold le_bytes_to_word. fold w64.
    pose proof (bytes_le_to_Z_range bs) as Hr. rewrite Hl in Hr.
    apply w64_eq_mod. rewrite (Z.mod_small (bytes_le_to_Z bs) (2 ^ (8 * 8))) by lia.
    destruct sx; [|reflexivity]. destruct (Z.leb (2 ^ (8 * 8 - 1)) (bytes_le_to_Z bs)); [|reflexivity].
    replace (bytes_le_to_Z bs - 2 ^ (8 * 8)) with (bytes_le_to_Z bs + (-1) * 2 ^ 64) by (change (2 ^ (8 * 8)) with (2 ^ 64); lia).
    rewrite Z.mod_add by lia. reflexivity.
  Qed.

  Lemma ldval_ext : forall w sx bs, 0 < w -> w <= 8 -> Z.of_nat (length bs) = w ->
    ldval w sx bs = w64 (ext_lit sx w (bytes_le_to_Z bs)).
  Proof.
    intros w sx bs Hw Hw8 Hl. destruct (Z.eq_dec w 8) as [->|Hne]; [apply ldval_8; exact Hl | apply ldval_small; lia].
  Qed.

  Lemma ext_lit_mod : forall sx w z, 0 < w -> ext_lit sx w (z mod 2 ^ (8 * w)) = ext_lit sx w z.
  Proof. intros. unfold ext_lit. rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity. Qed.

  Lemma ext_lit8_mod : forall sx z, (ext_lit sx 8 z) mod 2 ^ 64 = z mod 2 ^ 64.
  Proof.
    intros sx z. unfold ext_lit. cbv zeta. change (2 ^ (8 * 8)) with (2 ^ 64). change (8 * 8 - 1) with 63.
    pose proof (Z.mod_mod z (2 ^ 64) ltac:(lia)) as MM.
    destruct sx; [|exact MM].
    destruct (Z.leb (2 ^ 63) (z mod 2 ^ 64)); [|exact MM].
    replace (z mod 2 ^ 64 - 2 ^ 64) with (z mod 2 ^ 64 + (-1) * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. exact MM.
  Qed.

  (* [comment removed for export] *)
  Lemma ext_lit_range_u : forall w z, 0 < w -> 0 <= ext_lit false w z <= 2 ^ (8 * w) - 1.
  Proof. intros. unfold ext_lit. pose proof (Z.mod_pos_bound z (2 ^ (8 * w)) ltac:(apply Z.pow_pos_nonneg; lia)). lia. Qed.
  Lemma ext_lit_range_s : forall w z, 0 < w -> - 2 ^ (8 * w - 1) <= ext_lit true w z <= 2 ^ (8 * w - 1) - 1.
  Proof.
    intros. unfold ext_lit. pose proof (Z.mod_pos_bound z (2 ^ (8 * w)) ltac:(apply Z.pow_pos_nonneg; lia)).
    assert (2 ^ (8 * w) = 2 * 2 ^ (8 * w - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    destruct (Z.leb_spec (2 ^ (8 * w - 1)) (z mod 2 ^ (8 * w))); lia.
  Qed.
  (* [comment removed for export] *)
  Lemma ext_lit_id_u : forall w z, 0 < w -> 0 <= z < 2 ^ (8 * w) -> ext_lit false w z = z.
  Proof. intros. unfold ext_lit. rewrite Z.mod_small by lia. reflexivity. Qed.
  Lemma ext_lit_id_s : forall w z, 0 < w -> - 2 ^ (8 * w - 1) <= z < 2 ^ (8 * w - 1) -> ext_lit true w z = z.
  Proof.
    intros w z Hw Hz. unfold ext_lit.
    assert (Hp : 2 ^ (8 * w) = 2 * 2 ^ (8 * w - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    destruct (Z.lt_ge_cases z 0) as [Hn|Hn].
    - replace (z mod 2 ^ (8 * w)) with (z + 2 ^ (8 * w)).
      2: { rewrite <- (Z.mod_add z 1) by lia. rewrite Z.mod_small by lia. lia. }
      destruct (Z.leb_spec (2 ^ (8 * w - 1)) (z + 2 ^ (8 * w))); lia.
    - rewrite Z.mod_small by lia. destruct (Z.leb_spec (2 ^ (8 * w - 1)) z); lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma val_bytes_Z : forall rho v cw bs, val_bytes_ok rho v cw bs ->
    Z.of_nat (length bs) = cw /\ exists z, 0 <= z /\ bytes_le_to_Z bs = z mod 2 ^ (8 * cw) /\
      (forall l, v = LV l -> z mod 2 ^ (8 * cw) = (evl rho l) mod 2 ^ (8 * cw)).
  Proof.
    intros rho v cw bs [Hl Hv]. split; [exact Hl|].
    pose proof (bytes_le_to_Z_range bs) as Hr. rewrite Hl in Hr.
    exists (bytes_le_to_Z bs). split; [lia|]. split; [symmetry; apply Z.mod_small; lia|].
    intros l ->. cbn in Hv. rewrite Hv. rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity.
  Qed.

  Lemma unk_itv_sound : forall sx w z, 0 < w -> w <= 8 -> in_itv (ext_lit sx w z) (unk_itv sx w).
  Proof.
    intros sx w z Hw Hw8. unfold unk_itv. destruct (Z.eqb_spec w 8); [apply itop_sound|].
    destruct sx; unfold in_itv; cbn [ilo ihi].
    - pose proof (ext_lit_range_s w z Hw). lia.
    - pose proof (ext_lit_range_u w z Hw). lia.
  Qed.

  Lemma load_from_cell_sound : forall rho st v cw i w sx cbs,
    VS rho st -> aval_below v (s_next st) = true ->
    val_bytes_ok rho v cw cbs ->
    0 <= i -> 0 < w -> i + w <= cw -> cw <= 8 ->
    exists rho', VOK rho st (load_from_cell st v cw i w sx) rho' (ldval w sx (firstn (Z.to_nat w) (skipn (Z.to_nat i) cbs))).
  Proof.
    intros rho st v cw i w sx cbs HVS Hb Hvb Hi Hw Hiw Hcw.
    pose proof (val_bytes_Z rho v cw cbs Hvb) as (Hlen & z & Hz0 & Hz & HzL).
    set (bs := firstn (Z.to_nat w) (skipn (Z.to_nat i) cbs)).
    assert (Hlbs : Z.of_nat (length bs) = w).
    { unfold bs. rewrite length_firstn, length_skipn. lia. }
    assert (Hval : bytes_le_to_Z bs = (z / 2 ^ (8 * i)) mod 2 ^ (8 * w)).
    { unfold bs. rewrite slice_via_sublist by lia. rewrite Hz. rewrite !Z2Nat.id by lia.
      apply slice_mod_stable; lia. }
    rewrite (ldval_ext w sx bs) by lia. rewrite Hval.
    unfold load_from_cell.
    destruct v as [|l|n k a b|a b].
    - (* [comment removed for export] *) eapply VOK_fresh; [exact HVS | | reflexivity]. rewrite ext_lit_mod by lia.
      destruct sx; unfold in_itv; cbn [ilo ihi];
        [pose proof (ext_lit_range_s w (z / 2 ^ (8 * i)) Hw) | pose proof (ext_lit_range_u w (z / 2 ^ (8 * i)) Hw)]; lia.
    - destruct (is_const l) as [c|] eqn:Kc.
      + (* [comment removed for export] *) exists rho. apply VOK_lit; [exact HVS|]. f_equal.
        specialize (HzL l eq_refl). rewrite (is_const_sound rho l c Kc) in HzL.
        assert (E : (z / 2 ^ (8 * i)) mod 2 ^ (8 * w) = zbytes c i w).
        { unfold zbytes. rewrite two64z_eq.
          rewrite <- (slice_mod_stable z (8 * cw) (8 * i) (8 * w)) by lia.
          rewrite HzL. rewrite (slice_mod_stable c (8 * cw) (8 * i) (8 * w)) by lia.
          symmetry. apply slice_mod_stable; lia. }
        rewrite E. reflexivity.
      + destruct (Z.eqb i 0) eqn:Ei0.
        * apply Z.eqb_eq in Ei0. subst i. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
          specialize (HzL l eq_refl).
          assert (Hzw : z mod 2 ^ (8 * w) = evl rho l mod 2 ^ (8 * w)).
          { rewrite <- (Z.mod_mod_divide z (2 ^ (8 * cw)) (2 ^ (8 * w))) by (exists (2 ^ (8 * cw - 8 * w)); rewrite <- Z.pow_add_r by lia; f_equal; lia).
            rewrite HzL. apply Z.mod_mod_divide. exists (2 ^ (8 * cw - 8 * w)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
          rewrite Hzw. rewrite ext_lit_mod by lia.
          destruct (Z.eqb w 8) eqn:Ew8.
          -- apply Z.eqb_eq in Ew8. rewrite Ew8. exists rho. apply VOK_lv; [exact HVS | exact Hb |].
             apply w64_eq_mod. apply ext_lit8_mod.
          -- destruct (Z.eqb cw w ||| Z.ltb w cw)%bool eqn:Ecw.
             2: { eapply VOK_fresh; [exact HVS | | reflexivity]. destruct sx; unfold in_itv; cbn [ilo ihi];
                  [pose proof (ext_lit_range_s w (evl rho l) Hw) | pose proof (ext_lit_range_u w (evl rho l) Hw)]; lia. }
             destruct sx.
             ++ destruct (in_range (s_ctx st) l (- 2 ^ (8 * w - 1)) (2 ^ (8 * w - 1))) eqn:Er.
                ** pose proof (in_range_sound rho _ l _ _ (proj1 HVS) Er) as Hr.
                   exists rho. apply VOK_lv; [exact HVS | exact Hb |]. f_equal. apply ext_lit_id_s; lia.
                ** eapply VOK_fresh; [exact HVS | | reflexivity]. unfold in_itv; cbn [ilo ihi]. pose proof (ext_lit_range_s w (evl rho l) Hw). lia.
             ++ destruct (in_range (s_ctx st) l 0 (2 ^ (8 * w))) eqn:Er.
                ** pose proof (in_range_sound rho _ l _ _ (proj1 HVS) Er) as Hr.
                   exists rho. apply VOK_lv; [exact HVS | exact Hb |]. f_equal. apply ext_lit_id_u; lia.
                ** eapply VOK_fresh; [exact HVS | | reflexivity]. unfold in_itv; cbn [ilo ihi]. pose proof (ext_lit_range_u w (evl rho l) Hw). lia.
        * eapply VOK_fresh; [exact HVS | | reflexivity]. rewrite ext_lit_mod by lia.
          destruct sx; unfold in_itv; cbn [ilo ihi];
            [pose proof (ext_lit_range_s w (z / 2 ^ (8 * i)) Hw) | pose proof (ext_lit_range_u w (z / 2 ^ (8 * i)) Hw)]; lia.
    - eapply VOK_fresh; [exact HVS | | reflexivity]. rewrite ext_lit_mod by lia.
      destruct sx; unfold in_itv; cbn [ilo ihi];
        [pose proof (ext_lit_range_s w (z / 2 ^ (8 * i)) Hw) | pose proof (ext_lit_range_u w (z / 2 ^ (8 * i)) Hw)]; lia.
    - eapply VOK_fresh; [exact HVS | | reflexivity]. rewrite ext_lit_mod by lia.
      destruct sx; unfold in_itv; cbn [ilo ihi];
        [pose proof (ext_lit_range_s w (z / 2 ^ (8 * i)) Hw) | pose proof (ext_lit_range_u w (z / 2 ^ (8 * i)) Hw)]; lia.
  Qed.

End WithU.

End LXSM.
