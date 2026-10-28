(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_unwind_chain RT_iface D_defs GDesc.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxQuery.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HXS Require Import HxsStep HxsStepSound HxsHookSound.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXS Require Import HxsHookCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXA Require Import HxaInit HxaImage HxaInv HxaHooks HxaHk HxaHkDefs HxaHkMemset HxaHkStrlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_bytes_at (m : word -> option byte) : forall (n : nat) (a : Z) (bs : list byte),
  rdn ctasegs m (wa a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> bytes_at ctasegs m a bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros a bs H Ha Hn.
  - cbn [rdn] in H. injection H as <-. split; [|reflexivity]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - rewrite rdn_unfold in H. fold (mrd ctasegs m (wa a)) in H.
    destruct (mrd ctasegs m (wa a)) as [b|] eqn:Eb; [|discriminate].
    rewrite wa_succ in H. destruct (rdn ctasegs m (wa (a + 1)) n) as [r|] eqn:Er; [|discriminate]. injection H as <-.
    destruct (IH (a + 1) r Er ltac:(lia) ltac:(lia)) as [[_ [_ Hr]] Hl]. split; [|cbn; lia].
    split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. destruct i as [|i]; [rewrite Z.add_0_r; exact Eb|].
    cbn [nth_error]. rewrite <- (Hr i ltac:(cbn [length] in Hi; lia)). f_equal. f_equal. lia.
Qed.

Lemma bytes_at_agree (m1 m2 : word -> option byte) (a : Z) (bs : list byte) :
  bytes_at ctasegs m1 a bs -> (forall i, 0 <= i < Z.of_nat (length bs) -> m2 (wa (a + i)) = m1 (wa (a + i))) -> bytes_at ctasegs m2 a bs.
Proof.
  intros (H1 & H2 & H3) Hk. split; [exact H1|]. split; [exact H2|]. intros i Hi. unfold mrd. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H3 i Hi).
Qed.

Lemma bytes_at_inj (m : word -> option byte) (a : Z) : forall (bs1 bs2 : list byte),
  bytes_at ctasegs m a bs1 -> bytes_at ctasegs m a bs2 -> length bs1 = length bs2 -> bs1 = bs2.
Proof.
  intros bs1 bs2 (_ & _ & H1) (_ & _ & H2) Hl. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs1)) as [L|L].
  - rewrite <- (H1 i L), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs1 i)) by lia. rewrite (proj2 (nth_error_None bs2 i)) by lia. reflexivity.
Qed.

Lemma Rmem_memext (rho : valuation) (M : HxMem.mem) (m1 m2 : word -> option byte) :
  (forall x, m2 x = m1 x) -> Rmem ctasegs rho M m1 -> Rmem ctasegs rho M m2.
Proof.
  intros E [HR Hsep]. split; [|exact Hsep]. intros t rg G. pose proof (HR t rg G) as Hok.
  apply (region_ok_frame ctasegs rho t rg m1 m2 Hok). intros i Hi. apply same_byte_kept. apply E.
Qed.

Lemma write_app_pw (m : word -> option byte) (D : Z) (bs0 bs1 : list byte) (x : word) :
  0 <= D -> D + Z.of_nat (length bs0) + Z.of_nat (length bs1) <= 2 ^ 64 ->
  write_to_mem (write_to_mem m (wa D) bs0) (wa (D + Z.of_nat (length bs0))) bs1 x = write_to_mem m (wa D) (bs0 ++ bs1) x.
Proof.
  intros HD Hl. rewrite !write_to_mem_spec by (rewrite ?length_app; lia). rewrite length_app, Nat2Z.inj_add.
  pose proof (bv_unsigned_in_range 64 x) as Bx.
  destruct (Z.leb_spec0 (D + Z.of_nat (length bs0)) (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (D + Z.of_nat (length bs0) + Z.of_nat (length bs1)));
    destruct (Z.leb_spec0 D (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (D + Z.of_nat (length bs0)));
    destruct (Z.ltb_spec0 (bv_unsigned x) (D + (Z.of_nat (length bs0) + Z.of_nat (length bs1)))); cbn [andb]; try reflexivity; try (exfalso; lia).
  - rewrite nth_error_app2 by lia. f_equal. lia.
  - rewrite nth_error_app1 by lia. reflexivity.
Qed.

Lemma write_to_mem_nil (m : word -> option byte) (a : word) : write_to_mem m a [] = m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma le_bytes_roundtrip : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; cbn [Z_to_le_bytes bytes_le_to_Z length]; [reflexivity|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_nonneg bs) as R0.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
    rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.lor_spec, Z.shiftl_spec by lia.
    destruct (Z.ltb_spec k 8) as [L|L].
    + rewrite Z.ones_spec_low by lia. rewrite (Z.testbit_neg_r _ (k - 8)) by lia. rewrite orb_false_r, andb_true_r. reflexivity.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
      destruct (Z.eq_dec (bv_unsigned b) 0) as [->|Hn0]; [rewrite Z.bits_0; reflexivity|]. symmetry. apply Z.bits_above_log2; [lia|].
      apply (Z.lt_le_trans _ 8); [|lia]. apply Z.log2_lt_pow2; lia.
  - transitivity (Z_to_le_bytes (length bs) (bytes_le_to_Z bs)); [|exact IH]. f_equal.
    rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_div_pow2 (bv_unsigned b) 8) by lia. change (2 ^ 8) with 256. rewrite Z.div_small by lia. apply Z.lor_0_l.
Qed.

(* [comment removed for export] *)
Lemma load_store_rt (sz : msize) (bs : list byte) :
  sz = SZ1 \/ sz = SZ8 -> length bs = msz_nat sz -> Z_to_le_bytes (msz_nat sz) (bv_unsigned (load_word sz false bs)) = bs.
Proof.
  intros Hsz Hl. pose proof (bytes_le_to_Z_bound bs) as R. pose proof (bytes_le_to_Z_nonneg bs) as R0. rewrite Hl in R.
  destruct Hsz as [-> | ->]; cbn [msz_nat] in *.
  - destruct bs as [|b [|]]; try discriminate. unfold load_word. rewrite le_word_1. unfold zext.
    rewrite bv_zero_extend_unsigned by lia. rewrite extract_small by (try lia; pose proof (bv_unsigned_in_range 8 b) as Hb; unfold bv_modulus in Hb; lia).
    cbn [Z_to_le_bytes]. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
  - destruct (load_word_ptr bs (Z_to_bv 64 (bytes_le_to_Z bs))) as [E _].
    { rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ (8 * Z.of_nat 8)). lia. }
    rewrite E, Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ (8 * Z.of_nat 8)); lia).
    rewrite <- Hl. apply le_bytes_roundtrip.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CopySound.
Variable rho : valuation.
Variable abs : abstab.
Variable ctx : vctx.
Variable t : int.
Variables (D Sa N : Z).
Variable m : word -> option byte.
Variable M0 : HxMem.mem.
Variable rg0 : region.
Hypothesis Hctx : ctx_ok rho ctx.
Hypothesis HM0t : mget M0 t = Some rg0.
Hypothesis Habs0 : rg_abs rg0 = None.
Hypothesis HDin : rho t <= D /\ D + N <= rho t + to_Z (rg_size rg0).
Hypothesis Hdisj : D + N <= Sa \/ Sa + N <= D.
Hypothesis HSa : 0 <= Sa /\ Sa + N <= 2 ^ 64.
Hypothesis HD : 0 <= D /\ D + N <= 2 ^ 64.

(* [comment removed for export] *)
Definition cinv (M : HxMem.mem) : Prop :=
  (forall t', t' <> t -> mget M t' = mget M0 t') /\ (exists rg, mget M t = Some rg /\ same_dir rg0 rg).

Lemma cinv_refl : cinv M0.
Proof. split; [intros; reflexivity | exists rg0; split; [exact HM0t | apply same_dir_refl]]. Qed.

Theorem copy_sound : forall (fuel : nat) (M : HxMem.mem) (d sv : hval) (n : int) (M' : HxMem.mem) (bs0 : list byte),
  copy ctasegs fuel M abs ctx d sv n = Some M' ->
  cinv M -> Rmem ctasegs rho M (write_to_mem m (wa D) bs0) -> bytes_at ctasegs m Sa bs0 ->
  den rho d (wa (D + Z.of_nat (length bs0))) -> den rho sv (wa (Sa + Z.of_nat (length bs0))) ->
  Z.of_nat (length bs0) + to_Z n = N ->
  exists bs, Z.of_nat (length bs) = N /\ bytes_at ctasegs m Sa bs /\ cinv M' /\ Rmem ctasegs rho M' (write_to_mem m (wa D) bs).
Proof.
  induction fuel as [|f IH]; intros M d sv n M' bs0 H HC HRm Hbs0 Hd Hsv HjN; cbn [copy] in H; [discriminate|].
  pose proof (to_Z_bounded n) as Bn. set (j := Z.of_nat (length bs0)) in *.
  destruct (n =? 0)%uint63 eqn:En.
  { apply Uint63.eqb_spec in En. subst n. change (to_Z 0%uint63) with 0 in HjN. injection H as <-. exists bs0. split; [unfold j in HjN; lia|]. split; [exact Hbs0|]. split; [exact HC | exact HRm]. }
  apply Uint63.eqb_false_spec in En. assert (Hn0 : to_Z n <> 0) by (intros E; apply En; apply to_Z_inj; rewrite E; reflexivity).
  cbv beta zeta in H.
  match type of H with context [hx_load _ _ _ _ ?z false] => set (sz := z) in H end.
  destruct (hx_load ctasegs M abs sv sz false) as [v|] eqn:Eld; [|discriminate].
  destruct (hx_store ctasegs M abs d sz v) as [M1|] eqn:Est; [|discriminate].
  set (kn := msz_nat sz). pose proof (nbytes_Z sz) as Ek. fold kn in Ek.
  assert (Hkn : Z.of_nat kn <= to_Z n /\ (sz = SZ1 \/ sz = SZ8)).
  { subst sz kn. match goal with |- context [msz_nat (if ?c then SZ8 else SZ1)] => destruct c eqn:Ec end; cbn [msz_nat].
    - apply andb_prop in Ec as [_ E8]. apply leb_spec in E8. change (to_Z 8%uint63) with 8 in E8. split; [lia | right; reflexivity].
    - split; [lia | left; reflexivity]. }
  destruct Hkn as [Hkn Hsz].
  assert (Hkn1 : 1 <= Z.of_nat kn) by (destruct Hsz as [E|E]; unfold kn; rewrite E; cbn; lia).
  assert (Hj0 : 0 <= j) by (unfold j; lia).
  set (mvj := write_to_mem m (wa D) bs0) in *.
  (* [comment removed for export] *)
  destruct (hx_load_sound ctasegs rho M abs mvj sv sz false v (wa (Sa + j)) HRm Hsv Eld) as (bsk & Hrd & Hv). fold kn in Hrd.
  rewrite ov_rdn in Hrd. destruct (rdn_bytes_at mvj kn (Sa + j) bsk Hrd ltac:(lia) ltac:(lia)) as [Hbskv Lk].
  assert (Hbsk : bytes_at ctasegs m (Sa + j) bsk).
  { apply (bytes_at_agree mvj m _ _ Hbskv). intros i Hi. unfold mvj. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
    match goal with |- _ = (if ?c then _ else _) => replace c with false; [reflexivity|] end.
    symmetry. apply andb_false_iff. rewrite Z.leb_gt, Z.ltb_ge. fold j. lia. }
  set (bs1 := bs0 ++ bsk).
  assert (Hbs1 : bytes_at ctasegs m Sa bs1) by (apply (proj2 (bytes_at_app ctasegs m Sa bs0 bsk)); split; [exact Hbs0 | exact Hbsk]).
  assert (L1 : Z.of_nat (length bs1) = j + Z.of_nat kn) by (unfold bs1; rewrite length_app; lia).
  (* [comment removed for export] *)
  set (y := load_word sz false bsk).
  destruct (hx_store_sound ctasegs rho M M1 abs mvj d v sz (wa (D + j)) y HRm Hd Hv Est) as (_ & HRm1 & (t1 & rg1 & off1 & G1 & W1 & Ex1 & Hoff1 & rg1' & Hsd1 & EM1)).
  fold kn in HRm1, Hoff1. pose proof (load_store_rt sz bsk Hsz Lk) as RT. fold kn in RT. fold y in RT. rewrite RT in HRm1.
  assert (HRm1' : Rmem ctasegs rho M1 (write_to_mem m (wa D) bs1)).
  { apply (Rmem_memext rho M1 (write_to_mem mvj (wa (D + j)) bsk)); [|exact HRm1]. intros x. unfold mvj, bs1, j. symmetry. apply write_app_pw; lia. }
  (* [comment removed for export] *)
  destruct HC as [HC1 (rgM & GM & HsdM)].
  pose proof (proj1 HRm t1 rg1 G1) as (Q0 & Q1 & Q2 & _). pose proof (to_Z_bounded off1) as Bo1. unfold two63 in Q1.
  assert (EA : D + j = rbase rho t1 rg1 + to_Z off1).
  { pose proof (f_equal bv_unsigned Ex1) as E. rewrite !wa_unsigned in E by lia. exact E. }
  assert (Et1 : t1 = t).
  { destruct (Uint63.eq_dec t1 t) as [E|NE]; [exact E|]. exfalso.
    assert (EBM : rbase rho t rgM = rho t) by (unfold rbase; rewrite (proj1 HsdM), Habs0; reflexivity).
    pose proof (proj1 (proj2 HsdM)) as EsM.
    destruct (proj2 HRm t1 t rg1 rgM G1 GM NE (or_introl W1)) as [X|X]; rewrite EBM in X; rewrite ?EsM in X; lia. }
  subst t1. rewrite GM in G1. injection G1 as <-.
  assert (HC' : cinv M1).
  { split.
    - intros t' Ht'. rewrite EM1, (mget_mset M t t' _ (mget_lt _ _ _ GM)). destruct (Z.eqb_spec (to_Z t) (to_Z t')) as [E|E]; [exfalso; apply Ht'; symmetry; apply to_Z_inj; exact E|]. exact (HC1 t' Ht').
    - exists rg1'. split; [rewrite EM1, (mget_mset M t t _ (mget_lt _ _ _ GM)), Z.eqb_refl; reflexivity | exact (same_dir_trans _ _ _ HsdM Hsd1)]. }
  (* [comment removed for export] *)
  assert (Hk : den rho (VC (W false (nbytes sz))) (Z_to_bv 64 (Z.of_nat kn))).
  { cbn [den]. unfold wbv, wZ. cbn [wh wl]. rewrite Ek. reflexivity. }
  pose proof (v_alu64_ok rho ctx ALU_ADD d _ _ _ Hctx Hd Hk) as Hd'. pose proof (v_alu64_ok rho ctx ALU_ADD sv _ _ _ Hctx Hsv Hk) as Hsv'.
  cbn [alu64 alu] in Hd', Hsv'. rewrite wa_add_nat, wa_unsigned in Hd' by lia. rewrite wa_add_nat, wa_unsigned in Hsv' by lia.
  assert (En' : to_Z (n - nbytes sz)%uint63 = to_Z n - Z.of_nat kn) by (rewrite sub_spec, Ek; apply Z.mod_small; pose proof wB_pos; rewrite wB_eq in *; unfold two63 in *; lia).
  apply (IH M1 _ _ (n - nbytes sz)%uint63 M' bs1 H HC' HRm1' Hbs1); rewrite ?L1; [| |lia].
  - replace (D + (j + Z.of_nat kn)) with (D + j + Z.of_nat kn) by lia. exact Hd'.
  - replace (Sa + (j + Z.of_nat kn)) with (Sa + j + Z.of_nat kn) by lia. exact Hsv'.
Qed.

End CopySound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section HkMemcpy.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis PMc_fdfs : fdfs_only PMc.
Hypothesis PMc_mat : mat_stable PMc.
Variable T : TSet.
Variables (CL : list (Z * Z)) (lo sp0 r : Z) (m0 : word -> option byte) (cr0 anc : Z) (xp : xpar).
Hypothesis H_r : r = 0 \/ r = 16.
Hypothesis XP_stk : stk_okx (xp_stk xp).
Hypothesis XP_ro : rg_wr (xp_rgsh xp) = false.
Hypothesis IMGSH_OK : forall Σ m rho t, ART RT Σ m -> region_ok ctasegs rho t (xp_rgsh xp) m.

Notation FMemA := (FMem RT CL lo sp0 r m0 cr0 anc xp).
Notation FInvA := (FInv RT CL lo sp0 r m0 cr0 anc xp).
Notation JA := (J RT PMc T).
Notation B0A := (B0 sp0 r xp).
Notation XInvA := (XInv ctasegs SHBW (ghost RT) FInvA).
Notation xhook_okA := (xhook_ok ctasegs SHBW (ghost RT) JA FInvA).

Lemma PC_MEMCPY_Z : wbv PC_ASAN_MEMCPY = Z_to_bv 64 e_asan_memcpy. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Local Ltac dlia := repeat match goal with H : _ \/ _ |- _ => clear H | H : forall _, _ |- _ => clear H end; lia.

(* [comment removed for export] *)
Lemma regions_sep_dirs (rho : valuation) (M1 M2 : HxMem.mem) : same_dirs M1 M2 -> regions_sep rho M1 -> regions_sep rho M2.
Proof.
  intros Hd Hsep t1 t2 r1 r2 G1 G2 Hne Hw.
  pose proof (Hd t1) as X1. pose proof (Hd t2) as X2. rewrite G1 in X1. rewrite G2 in X2.
  destruct (mget M1 t1) as [q1|] eqn:E1; [|contradiction]. destruct (mget M1 t2) as [q2|] eqn:E2; [|contradiction].
  rewrite (rbase_same_dir rho t1 q1 r1 X1), (rbase_same_dir rho t2 q2 r2 X2).
  destruct X1 as (_ & Es1 & _ & Ew1 & _). destruct X2 as (_ & Es2 & _ & Ew2 & _). rewrite Es1, Es2. rewrite Ew1, Ew2 in Hw.
  exact (Hsep t1 t2 q1 q2 E1 E2 Hne Hw).
Qed.

Lemma wa_unsigned_id (w : word) : wa (bv_unsigned w) = w.
Proof. unfold wa. apply Z_to_bv_bv_unsigned. Qed.

Lemma hkA_memcpy_ok : xhook_okA hkA_memcpy.
Proof.
  intros g rho cd S cd' S' ms [[HRn Hlaw] [HF (Hro & Hnf)]] Hh K.
  unfold hkA_memcpy, hk_at in Hh. destruct (w_eqb (s_pc S) PC_ASAN_MEMCPY) eqn:Epc; [|discriminate]. apply w_eqb_true_iff in Epc.
  unfold hkx_memcpy in Hh.
  destruct (xtp_ok TPV S && xsp_ok T_STK S && (x_calls cd <? CALLS_MAX)) eqn:Eg; [|discriminate].
  apply andb_prop in Eg as [Eg Ecalls]. apply andb_prop in Eg as [Etp Esp]. apply Z.ltb_lt in Ecalls. unfold CALLS_MAX in Ecalls.
  destruct (rget S X10) as [|t o| |] eqn:Ea10; try discriminate. destruct (rget S X12) as [n| | |] eqn:Ea12; try discriminate.
  destruct (wh o || wh n) eqn:Eh; [discriminate|]. apply orb_false_elim in Eh as [Eho Ehn].
  destruct (mget (s_mem S) t) as [rg|] eqn:Eg0; [|discriminate].
  match type of Hh with (if ?cnd then _ else _) = _ => destruct cnd eqn:Eck; [|discriminate] end.
  apply andb_prop in Eck as [Eck Esrc]. apply andb_prop in Eck as [Eck Eabsb]. apply andb_prop in Eck as [Eck Ec11]. apply andb_prop in Eck as [Eck Ec3].
  apply andb_prop in Eck as [Eck Ec6]. apply andb_prop in Eck as [Eck Ec5]. apply andb_prop in Eck as [Eck Ec4]. apply andb_prop in Eck as [Eck Ewr].
  apply andb_prop in Eck as [Eeven Eexb].
  destruct (rg_abs rg) eqn:Eabs; [discriminate|]. clear Eabsb.
  apply ltb_spec in Ec11. change (to_Z 1099511627776%uint63) with (2 ^ 40) in Ec11. apply ltb_spec in Ec3. change (to_Z 0%uint63) with 0 in Ec3.
  apply leb_spec in Ec4. apply leb_spec in Ec5. apply leb_spec in Ec6.
  apply existsb_exists in Eexb as (t' & Hint & Et'). apply Uint63.eqb_spec in Et'. subst t'.
  destruct (copy ctasegs (Datatypes.S (Z.to_nat (to_Z (wl n)))) (s_mem S) (s_abs S) (ctx_of (s_mem S)) (VP t o) (rget S X11) (wl n)) as [M'|] eqn:Ecp; [|discriminate].
  destruct (xclobber_stack RT_STACK S M') as [Mc|] eqn:Ecl; [|discriminate].
  destruct (xret S (VP t o) Mc (s_next S)) as [S1|] eqn:Ert; [|discriminate]. injection Hh as <- <-.
  destruct (xclobber_inv T_STK RT_STACK S _ _ Ecl Esp) as (os & rgs & Esp2 & Ehos & EgsM' & Eabss & Edfs & Ho16 & Hrt & Hosz & Ewrs & EMc).
  destruct (xret_inv _ _ _ _ _ Ert) as (ra & Era & Erv & ->).
  destruct (ms_nf rho S ms (Rn_R ctasegs rho S ms HRn) Erv Hro Hnf)
    as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
        & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & Ems & HRg).
  set (m := ms_mem ms) in *. set (F := ms_fregs ms) in *. set (fc := ms_fcsr ms) in *. clearbody m F fc. subst ms.
  cbn [ms_mem ms_regs ms_rom MS] in HF, Hro, Hnf.
  destruct (nf_regs rho S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRg) as (D1 & D2 & D4 & D8 & D10 & D11 & D12).
  pose proof D1 as D1'. pose proof D2 as D2'. rewrite Era in D1'. rewrite Esp2 in D2'. rewrite Ea10 in D10. rewrite Ea12 in D12. cbn [den] in D1', D2', D10, D12.
  unfold xtp_ok in Etp. destruct (rget S X4) as [tpw| | |]; try discriminate. apply w_eqb_true_iff in Etp. subst tpw. cbn [den] in D4.
  assert (HRall : forall rho2, agree_below (s_next S) rho rho2 ->
            Rregs rho2 (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (wbv (s_pc S)) fc None)
            /\ Rmem ctasegs rho2 (s_mem S) m).
  { intros rho2 Hag. destruct (HRn rho2 Hag) as (_ & _ & HRg2 & _ & HRm2). exact (conj HRg2 HRm2). }
  pose proof HF as (Hlive & Hfr & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & (Hrs & Hrss & Hrsh & Hr0 & Hroot) & HART & Hmi & Hstk & (Hl1 & Hl2 & Hl3 & Hl4) & (Hc1 & Hc2 & Hc3 & Hc4) & Hagr).
  change (to_Z NEXT0) with 32 in *.
  pose proof (proj2 (HRall rho (agree_below_refl _ _))) as HRm.
  pose proof (af_sp0_range RT AF _ _ HART) as Hsp0r. pose proof XP_stk as (ESTK32 & ESTK0 & ESTK1).
  pose proof (to_Z_bounded (wl o)) as Bo. pose proof (to_Z_bounded (wl n)) as Bn. pose proof (to_Z_bounded (rg_size rg)) as Bs. pose proof (to_Z_bounded (wl os)) as Bos.
  (* [comment removed for export] *)
  destruct (Htl t ltac:(apply in_or_app; left; exact Hint)) as (_ & Tt1 & Tt2).
  assert (Hne : t <> T_STK) by (intros E; rewrite E in Tt1; change (to_Z T_STK) with 2 in Tt1; clear -Tt1; lia).
  pose proof (proj1 HRm t rg Eg0) as Hokt. pose proof Hokt as (Bx0 & Bx1 & Bx2 & Bx3 & Bx4 & Bx5 & Bx6 & Hby).
  unfold two63 in Bx1. unfold rbase in Bx0, Bx1, Bx6, Hby. rewrite Eabs in Bx0, Bx1, Bx6, Hby.
  assert (Eon : to_Z (wl o + wl n)%uint63 = to_Z (wl o) + to_Z (wl n)) by (rewrite add_spec; apply Z.mod_small; rewrite wB_eq; unfold two63; clear -Bo Bn Ec4 Ec5 Bx2; lia).
  rewrite Eon in Ec6.
  assert (EwZo : wZ o = to_Z (wl o)) by (unfold wZ; rewrite Eho; reflexivity).
  assert (EwZn : wZ n = to_Z (wl n)) by (unfold wZ; rewrite Ehn; reflexivity).
  set (A := rho t + to_Z (wl o)). set (nz := to_Z (wl n)) in *.
  assert (HinL : In (rho t, to_Z (rg_size rg)) (rt_live RT (g_S RT g))).
  { rewrite Hlive. apply in_or_app. left. unfold blk_list. apply in_map_iff. exists t. rewrite (rsize_get _ t rg Eg0). auto. }
  destruct (af_acc_live RT AF _ _ _ _ HART HinL) as [HwrL HaccL]. destruct (af_live_range RT AF _ _ _ _ HART HinL) as (P1 & P2 & P3).
  assert (Hwf : forall x, rho t <= x < rho t + to_Z (rg_size rg) ->
            aclient (rt_live RT (g_S RT g)) (rt_frames RT (g_S RT g)) B0A x /\ ~ caller_mem CL sp0 xp x /\ 0 <= x < 2 ^ 47).
  { intros x Hx. apply (wr_facts RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk g rho cd _ _ m t rg x HF Eg0 Ewr). unfold rbase. rewrite Eabs. exact Hx. }
  destruct (Hwf A ltac:(unfold A; clear -Bo Ec3 Ec6; lia)) as (_ & _ & BA).
  (* [comment removed for export] *)
  assert (Hctx : ctx_ok rho (ctx_of (s_mem S))) by exact (ctx_of_ok ctasegs rho (s_mem S) m HRm).
  (* [comment removed for export] *)
  set (Sa := bv_unsigned x11). pose proof (wa_unsigned_id x11) as Ex11. fold Sa in Ex11.
  assert (HSRC : acc ctasegs m Sa nz /\ rng_class RT (g_S RT g) Sa nz /\ Sa + nz <= lo /\ (A + nz <= Sa \/ Sa + nz <= A) /\ 0 <= Sa /\ Sa + nz <= 2 ^ 47).
  { unfold memcpy_src_ok in Esrc. destruct (rget S X11) as [w|ts os2| |] eqn:Esv; try discriminate; cbn [den] in D11.
    - (* [comment removed for export] *)
      apply andb_prop in Esrc as [Ehw Ecov]. apply negb_true_iff in Ehw.
      assert (ESa : Sa = to_Z (wl w)) by (unfold Sa; rewrite D11, wbv_unsigned; unfold wZ; rewrite Ehw; reflexivity).
      destruct (gds_cover_In _ _ Ecov) as (gd & Hgd & Hgd1 & Hgd2). rewrite <- ESa in Hgd1, Hgd2.
      destruct (GDESC_bounds gd Hgd) as (G1 & G2 & G3 & G4 & G5). unfold GD_IMG_END in G5.
      split.
      { apply (acc_sub ctasegs m (gd_beg gd) (gd_size gd)); [|lia|lia].
        apply (acc_ushadow ctasegs m (gd_beg gd) (gd_size gd)); [apply Z.mod_divide; [discriminate|]; apply Z.mod_divide in G1; [|discriminate]; destruct G1 as [q Hq]; exists (4 * q); clear -Hq; lia | clear -G4; lia | clear -G2; lia |].
        exact (af_lib_sh RT AF _ _ gd HART Hgd). }
      split; [right; right; right; clear -Hgd1 Hgd2 G2 G4 G5; unfold SEGTOP_A; lia|].
      split; [clear -Hgd2 G2 G5 Hl1 Hsp0r; unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia|].
      split; [destruct P3 as [X|X]; [left | right]; clear -X Hgd1 Hgd2 G2 G4 G5 Ec3 Ec6 Bo; unfold A, SEGTOP_A in *; lia|]. clear -Hgd1 Hgd2 G2 G4 G5 Ec3; lia.
    - (* [comment removed for export] *)
      apply andb_prop in Esrc as [Eck2 Ematch]. apply andb_prop in Eck2 as [Eck2 E77]. apply andb_prop in Eck2 as [Eck2 Eexf]. apply andb_prop in Eck2 as [Ehw2 Eevs].
      apply negb_true_iff in Ehw2. apply andb_prop in E77 as [Eo7 En7]. apply Uint63.eqb_spec in Eo7. apply Uint63.eqb_spec in En7.
      apply existsb_exists in Eexf as (ts' & Hinf & Ets'). apply Uint63.eqb_spec in Ets'. subst ts'.
      destruct (mget (s_mem S) ts) as [rs|] eqn:Egs2; [|discriminate]. destruct (mget (s_mem S) (sh_tag ts)) as [rss|] eqn:Egss; [|discriminate].
      apply andb_prop in Ematch as [Em Hfz]. apply andb_prop in Em as [Em E6']. apply andb_prop in Em as [Em E5']. apply andb_prop in Em as [Eabs2 E4'].
      destruct (rg_abs rs) eqn:Eabs_s; [discriminate|]. apply leb_spec in E4'. apply leb_spec in E5'. apply leb_spec in E6'.
      pose proof (to_Z_bounded (wl os2)) as Bos2. pose proof (to_Z_bounded (rg_size rs)) as Brs.
      assert (Eon2 : to_Z (wl os2 + wl n)%uint63 = to_Z (wl os2) + nz).
      { rewrite add_spec. apply Z.mod_small. rewrite wB_eq. unfold two63. pose proof (proj1 HRm ts rs Egs2) as (_ & _ & Q2 & _). clear -Q2 E4' E5' Bos2 Bn. dlia. }
      rewrite Eon2 in E6'.
      assert (Eos8 : to_Z (wl os2) mod 8 = 0) by (rewrite <- phi_land7, Eo7; reflexivity).
      assert (En8 : nz mod 8 = 0) by (unfold nz; rewrite <- phi_land7, En7; reflexivity).
      destruct (Htl ts ltac:(apply in_or_app; right; exact Hinf)) as (_ & T1 & T2).
      destruct (proj2 Hlink ts Hinf) as (rgf & Egf & _ & _ & Hfsz). rewrite Egs2 in Egf. injection Egf as <-.
      set (k := fcls (to_Z (rg_size rs))).
      assert (Efk : fs_size k = to_Z (rg_size rs) + 8) by (unfold k; apply fcls_size; exact Hfsz).
      assert (HinF : In (rho ts, k) (rt_frames RT (g_S RT g))).
      { rewrite Hfr. unfold frm_list. apply in_map_iff. exists ts. rewrite (rsize_get _ ts rs Egs2). auto. }
      destruct (Hrsh ts ltac:(apply in_or_app; right; exact Hinf)) as [Hsht Hal8].
      destruct (af_frames_range RT AF _ _ _ _ HART HinF) as (F1 & F2 & F3 & F4).
      pose proof (proj1 HRm ts rs Egs2) as (Cx0 & Cx1 & _). unfold two63 in Cx1. unfold rbase in Cx0, Cx1. rewrite Eabs_s in Cx0, Cx1.
      assert (ESa : Sa = rho ts + to_Z (wl os2)).
      { unfold Sa. rewrite D11. unfold pword. assert (EwZ2 : wZ os2 = to_Z (wl os2)) by (unfold wZ; rewrite Ehw2; reflexivity).
        rewrite EwZ2, Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). clear -Cx0 Cx1 Bos2 E6' Ec3. dlia. }
      (* [comment removed for export] *)
      unfold fshadow_zero in Hfz. apply andb_prop in Hfz as [Hfz Hkb]. apply andb_prop in Hfz as [Hssabs Hssz].
      destruct (rg_abs rss) as [|] eqn:Eass; [discriminate|]. apply leb_spec in Hssz.
      set (ko := to_Z (wl os2) / 8). set (kn := nz / 8).
      assert (Eko : 8 * ko = to_Z (wl os2)) by (pose proof (Z.div_mod (to_Z (wl os2)) 8 ltac:(discriminate)) as DM; clear -DM Eos8; unfold ko; lia).
      assert (Ekn : 8 * kn = nz) by (pose proof (Z.div_mod nz 8 ltac:(discriminate)) as DM; clear -DM En8; unfold kn; lia).
      assert (Eo3 : to_Z (wl os2 >> 3)%uint63 = ko) by apply phi_shr3.
      assert (En3 : to_Z (wl n >> 3)%uint63 = kn) by apply phi_shr3.
      assert (Esum : to_Z ((wl os2 >> 3) + (wl n >> 3))%uint63 = ko + kn).
      { rewrite add_spec, Eo3, En3. apply Z.mod_small. rewrite wB_eq. unfold two63. clear -Eko Ekn Bos2 Bn Ec3 E6' Cx0 Cx1. dlia. }
      rewrite Esum in Hssz. pose proof (to_Z_bounded (rg_size rss)) as Bss.
      assert (Hst : sh_tag ts <> T_STK).
      { intros E. pose proof (f_equal to_Z E) as E'. rewrite sh_tag_Z in E' by lia. change (to_Z T_STK) with 2 in E'. lia. }
      pose proof (proj1 HRm (sh_tag ts) rss Egss) as Hokss.
      rewrite Eo3, En3 in Hkb.
      destruct (kb_check_sound ctasegs rho (sh_tag ts) rss m (repeat (KB 0) (Z.to_nat kn)) ko Hokss Hkb ltac:(clear -Eko Bos2; lia) ltac:(rewrite repeat_length, Z2Nat.id by (clear -Ekn Ec3; lia); clear -Hssz; lia))
        as (bs & HF2 & Hbs & _).
      pose proof (zero_kbs_bytes rho _ bs HF2) as Ebs. rewrite Ebs in Hbs. unfold rbase in Hbs. rewrite Eass, Hsht in Hbs.
      replace ko with (to_Z (wl os2) / 8) in Hbs by reflexivity.
      rewrite <- (shad_aligned_add (rho ts) (to_Z (wl os2)) Hal8 ltac:(clear -Bos2; lia)) in Hbs. rewrite <- ESa in Hbs.
      pose proof (acc_zero_run ctasegs m Sa _ ltac:(rewrite ESa, Z.add_mod, Hal8, Eos8 by discriminate; reflexivity) ltac:(rewrite ESa; clear -Cx0 Bos2; lia) Hbs) as Hacc.
      rewrite Z2Nat.id in Hacc by (clear -Ekn Ec3; lia). rewrite Ekn in Hacc.
      split; [exact Hacc|]. split; [right; left; exists (rho ts), k; split; [exact HinF | clear -ESa Efk E6' Ec3 Bos2; dlia]|].
      split; [clear -ESa Efk E6' F2 Hl1 Bos2 Ec3; unfold STACK_WIN in *; dlia|]. split; [|clear -ESa Efk E6' F2 Hsp0r Cx0 Bos2 Ec3; unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *; dlia].
      destruct (F4 _ _ HinL) as [X|X]; [right | left]; clear -X ESa Efk E6' Ec3 Ec6 Bos2 Bo; unfold A; dlia. }
  destruct HSRC as (HaccS & HrngS & HloS & Hdisj & HSa0 & HSa1).
  (* [comment removed for export] *)
  assert (HD0 : den rho (VP t o) (wa (A + Z.of_nat (@length byte [])))).
  { cbn [den length Z.of_nat]. rewrite Z.add_0_r. unfold pword, wa, A. rewrite EwZo. reflexivity. }
  assert (HS0 : den rho (rget S X11) (wa (Sa + Z.of_nat (@length byte [])))).
  { cbn [length Z.of_nat]. rewrite Z.add_0_r, Ex11. exact D11. }
  assert (Hbs00 : bytes_at ctasegs m Sa []) by (clear -HSa0 HSa1 Ec3; split; [lia | split; [cbn; lia | intros i Hi; cbn in Hi; lia]]).
  assert (HDin : rho t <= A /\ A + nz <= rho t + to_Z (rg_size rg)) by (unfold A; clear -Bo Ec6; lia).
  assert (HSa64 : 0 <= Sa /\ Sa + nz <= 2 ^ 64) by (clear -HSa0 HSa1 Ec3; lia).
  assert (HA64 : 0 <= A /\ A + nz <= 2 ^ 64) by (clear -BA Ec11 Ec3; lia).
  assert (L0 : Z.of_nat (@length byte []) + nz = nz) by (cbn [length Z.of_nat]; apply Z.add_0_l).
  destruct (copy_sound rho (s_abs S) (ctx_of (s_mem S)) t A Sa nz m (s_mem S) rg Hctx Eabs HDin Hdisj HSa64 HA64
              _ (s_mem S) (VP t o) (rget S X11) (wl n) M' [] Ecp (cinv_refl t (s_mem S) rg Eg0) HRm Hbs00 HD0 HS0 L0)
    as (bs & Lbs & Hbs & [HC1 (rg' & EgM't & Hsd')] & _).
  assert (Lbs' : length bs = Z.to_nat nz) by (clear -Lbs; lia).
  (* [comment removed for export] *)
  assert (Egs : mget (s_mem S) T_STK = Some rgs) by (rewrite <- (HC1 T_STK (not_eq_sym Hne)); exact EgsM').
  destruct (stk_class RT CL lo sp0 r m0 cr0 anc xp g rho cd _ _ m rgs HF Egs Eabss) as [Esz _].
  destruct (call_geometry RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk g rho cd _ _ m os x2 HF Ehos Ho16 Hrt ltac:(clear -Hosz Esz; lia) D2') as (Espv & Hcall & Hspc).
  assert (Hos8 : to_Z (wl os) mod 8 = 0).
  { clear -Ho16 Bos. replace (to_Z (wl os)) with (0 + (2 * (to_Z (wl os) / 16)) * 8) by (pose proof (Z.div_mod (to_Z (wl os)) 16 ltac:(discriminate)); lia). rewrite Z.mod_add by discriminate. reflexivity. }
  (* [comment removed for export] *)
  assert (SEP : rho t + to_Z (rg_size rg) <= B0A \/ sp0 <= rho t).
  { destruct (proj2 HRm t T_STK rg rgs Eg0 Egs Hne (or_introl Ewr)) as [X|X]; unfold rbase in X; rewrite Eabs, Eabss, Hrs in X; rewrite ?Esz in X; [left; clear -X; lia | right; clear -X Esz; unfold B0 in *; lia]. }
  (* [comment removed for export] *)
  pose proof Hsd' as (Ea' & Es' & El' & Ew' & Edf' & Ed').
  assert (HdM' : same_dirs (s_mem S) M').
  { intros t3. destruct (Uint63.eq_dec t3 t) as [->|N]; [rewrite Eg0, EgM't; exact Hsd'|]. rewrite (HC1 t3 N). destruct (mget (s_mem S) t3); [apply same_dir_refl | exact I]. }
  assert (Hd : same_dirs (s_mem S) Mc).
  { rewrite EMc. eapply same_dirs_trans; [exact HdM' | exact (same_dirs_mset _ T_STK rgs _ EgsM' (same_dir_drop_below rgs (wl os)))]. }
  assert (Hrs_ : ro_same (s_mem S) Mc).
  { rewrite EMc. intros t3 rg3 G3 W3. rewrite (mget_mset M' T_STK t3 _ (mget_lt _ _ _ EgsM')).
    destruct (Z.eqb_spec (to_Z T_STK) (to_Z t3)) as [E|E]; [apply to_Z_inj in E; subst t3; rewrite Egs in G3; injection G3 as <-; rewrite Ewrs in W3; discriminate|].
    destruct (Uint63.eq_dec t3 t) as [->|N]; [rewrite Eg0 in G3; injection G3 as <-; rewrite Ewr in W3; discriminate|].
    rewrite (HC1 t3 N). exact G3. }
  (* [comment removed for export] *)
  intros cfg Hc. rewrite Epc, PC_MEMCPY_Z in Hc.
  apply (rc_asan_memcpy RT RTC (g_S RT g) PMc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           F fc m A Sa bs lo PMc_fdfs PMc_mat); rewrite ?Lbs; try assumption.
  - rewrite D10. unfold pword, A. rewrite EwZo. reflexivity.
  - rewrite <- Ex11. reflexivity.
  - rewrite D12. unfold wbv. rewrite EwZn. reflexivity.
  - clear -BA. lia.
  - clear -HSa0 HSa1 Bn Ec3. lia.
  - split; [intros _; exact (conj HaccS HrngS) | left; exact HloS].
  - split; [intros _; split|split].
    + apply (acc_sub ctasegs m (rho t) (to_Z (rg_size rg))); [exact HaccL | unfold A; clear -Bo; lia | unfold A; clear -Ec6; dlia].
    + left. exists (rho t), (to_Z (rg_size rg)). split; [exact HinL | unfold A; clear -Bo Ec6; dlia].
    + intros i Hi. rewrite Espv. right; right; left. exists (rho t), (to_Z (rg_size rg)). split; [exact HinL | unfold A; clear -Bo Ec6 Hi; dlia].
    + split; [clear -BA; lia|]. split; [clear -BA Ec3 Ec11; dlia|]. intros i Hi. replace (A + i) with (rho t + (to_Z (wl o) + i)) by (unfold A; clear -Hi; lia).
      destruct (Hby (to_Z (wl o) + i) ltac:(clear -Hi Bo Ec6; dlia)) as (b & _ & _ & W). exact (W Ewr).
  - intros c' Hc'. destruct (ASTA_unpack RT (g_S RT g) PMc _ c' Hc') as (ms' & (m' & Hret & (HART' & MI' & WM & Hstk') & Hpex & Hbytes) & Hc'').
    destruct Hret as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & Ems').
    rewrite Espv in Hstk', Hpex.
    apply (K g rho ms' (agree_below_refl _ _)); [|exact Hc'']. subst ms'.
    (* [comment removed for export] *)
    assert (KEPT : forall x, rho t <= x < rho t + to_Z (rg_size rg) -> ~ (A <= x < A + nz) -> m' (wa x) = m (wa x)).
    { intros x Hx Hnin. destruct (Hwf x Hx) as (_ & _ & Bx). apply Hpex; rewrite wa_unsigned by (clear -Bx; lia); [|exact Hnin].
      right; right; left. exists (rho t), (to_Z (rg_size rg)). split; [exact HinL | exact Hx]. }
    assert (HF' : FMemA g rho (XCD (x_blocks cd) (x_frames cd) (x_calls cd + 1) (x_nb cd)) Mc (s_next S) m').
    { apply (FMem_after_call RT CL lo sp0 r m0 cr0 anc xp XP_ro g rho cd (s_mem S) _ (s_next S) m m' (g_S RT g) (B0A + to_Z (wl os)) HF HART' MI' Hstk'); try reflexivity; try assumption.
      - apply (kept_stack sp0 _ _ _ A nz m m' Hpex); [clear -Hspc Hl2 Hstk; destruct Hstk as (? & _); lia | exact Hl3 |].
        intros a Ha Hin. unfold A in Hin. destruct SEP as [X|X]; clear -X Ha Hin Ec6 Bo Bos Hspc; lia.
      - rewrite Hlive in Hpex. apply (kept_caller CL sp0 xp _ _ _ A nz m m' Hpex); [clear -Hspc; lia|].
        intros a Hca Hin. exact (proj1 (proj2 (Hwf a ltac:(unfold A in Hin; clear -Hin Bo Ec6; lia))) Hca).
      - set (cr := rt_credit RT (g_S RT g)); clearbody cr; clear -cr; lia. }
    split; [split|split; [exact HF' | split; [reflexivity | cbn [ms_regs MS]; do 31 eexists; reflexivity]]].
    + intros rho2 Hag. cbn [s_next] in Hag. destruct (HRall rho2 Hag) as [HRg2 HRm2].
      assert (Et : rho2 t = rho t) by (apply Hag; exact (Htags t rg Eg0)).
      assert (EB : rbase rho2 t rg = rho t) by (unfold rbase; rewrite Eabs; exact Et).
      apply (R_return rho2 S (VP t o) _ (s_abs S) (s_next S) ra x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
               t0' t1' t2' (Z_to_bv 64 A) a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F F' (wbv (s_pc S)) fc fc' None m' (seg_rom ctasegs) HRg2 D1').
      { cbn [den]. unfold pword, A. rewrite Et, EwZo. reflexivity. }
      (* [comment removed for export] *)
      destruct (nf_regs rho2 S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRg2) as (_ & _ & _ & _ & _ & D11_2 & _).
      assert (HD0_2 : den rho2 (VP t o) (wa (A + Z.of_nat (@length byte [])))).
      { cbn [den length Z.of_nat]. rewrite Z.add_0_r. unfold pword, wa, A. rewrite Et, EwZo. reflexivity. }
      assert (HS0_2 : den rho2 (rget S X11) (wa (Sa + Z.of_nat (@length byte [])))).
      { cbn [length Z.of_nat]. rewrite Z.add_0_r, Ex11. exact D11_2. }
      destruct (copy_sound rho2 (s_abs S) (ctx_of (s_mem S)) t A Sa nz m (s_mem S) rg (ctx_of_ok ctasegs rho2 (s_mem S) m HRm2) Eabs ltac:(rewrite Et; exact HDin) Hdisj HSa64 HA64
                  _ (s_mem S) (VP t o) (rget S X11) (wl n) M' [] Ecp (cinv_refl t (s_mem S) rg Eg0) HRm2 Hbs00 HD0_2 HS0_2 L0)
        as (bs2 & Lbs2 & Hbs2 & _ & HRmv2).
      assert (Ebs2 : bs2 = bs) by (apply (bytes_at_inj m Sa bs2 bs Hbs2 Hbs); clear -Lbs Lbs2; lia). subst bs2.
      rewrite EMc. split.
      * intros t3 rg3 G3. destruct (mget_mset_cases M' T_STK t3 _ rg3 (mget_lt _ _ _ EgsM') G3) as [[-> ->]|[Hne3 G3']].
        -- (* [comment removed for export] *)
           apply (regions_after_call_gen RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk IMGSH_OK g rho rho2 cd (s_mem S) (s_next S) m m' (g_S RT g) (rt_live RT (g_S RT g)) os rgs (s_next S) t A nz
                    HF HRm2 Hag Egs Eabss Edfs Ewrs Ho16 Hosz HART' MI' Hstk' Hpex eq_refl); try assumption.
           ++ intros b Hb _. assert (Hin : In (rho b, rsize (s_mem S) b) (rt_live RT (g_S RT g))).
              { rewrite Hlive. apply in_or_app. left. unfold blk_list. apply in_map_iff. exists b. auto. }
              split; exact Hin.
           ++ intros e He. assert (Hin : In e (rt_live RT (g_S RT g))) by (rewrite Hlive; apply in_or_app; right; exact He).
              split; exact Hin.
           ++ intros t4 rg4 G4 Hne4 i Hi Hin.
              destruct (proj2 HRm2 t4 t rg4 rg G4 Eg0 Hne4 (or_intror Ewr)) as [X|X]; rewrite EB in X; unfold A in Hin; clear -X Hin Hi Ec6 Bo; lia.
           ++ rewrite (mget_mset _ T_STK T_STK _ (mget_lt _ _ _ Egs)), Z.eqb_refl. reflexivity.
           ++ intros E. pose proof (Htags _ _ Egs) as X. rewrite E in X. clear -X. lia.
           ++ intros E. pose proof (Htags _ _ Egs) as X. rewrite E in X. rewrite sh_tag_Z in X by (clear -Hnx; lia). clear -X. lia.
           ++ exact (not_eq_sym Hne).
        -- destruct (Uint63.eq_dec t3 t) as [Et3|Nt3].
           ** (* [comment removed for export] *)
              subst t3. rewrite EgM't in G3'. injection G3' as <-.
              pose proof (proj1 HRmv2 t rg' EgM't) as Hokv.
              apply (region_ok_upd ctasegs rho2 t rg' rg' (write_to_mem m (wa A) bs) m' Hokv (same_dir_refl _)). intros i Hi.
              assert (EB' : rbase rho2 t rg' = rho t) by (unfold rbase; rewrite Ea', Eabs; exact Et).
              rewrite EB'. rewrite Es' in Hi. rewrite Ew'.
              destruct Hokv as (_ & _ & _ & _ & _ & _ & _ & Hbyv). rewrite EB', Es' in Hbyv. destruct (Hbyv i Hi) as (b & Eb & Kb & _).
              exists b. split; [|split; [exact Kb | intros _; apply WM; destruct (Hby i Hi) as (b0 & _ & _ & W0); exact (W0 Ewr)]].
              unfold mrd in Eb |- *. rewrite write_to_mem_spec in Eb by (rewrite ?Lbs; clear -BA Ec11 Ec3; lia). rewrite wa_unsigned in Eb by (clear -Bx0 Bx1 Hi; lia).
              rewrite Lbs in Eb.
              destruct ((A <=? rho t + i) && (rho t + i <? A + nz)) eqn:Ein.
              +++ apply andb_prop in Ein as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
                  pose proof (bytes_at_mrd m' A bs (rho t + i - A) Hbytes ltac:(rewrite Lbs; clear -E1 E2; lia)) as X. unfold mrd in X.
                  replace (A + (rho t + i - A)) with (rho t + i) in X by (clear -E1; lia). rewrite X.
                  destruct (nth_error bs (Z.to_nat (rho t + i - A))) as [b'|] eqn:En; [exact Eb | apply nth_error_None in En; rewrite Lbs' in En; clear -En E1 E2 Ec3; lia].
              +++ apply andb_false_iff in Ein. rewrite Z.leb_gt, Z.ltb_ge in Ein.
                  rewrite (KEPT (rho t + i) ltac:(clear -Hi; lia) ltac:(clear -Ein; lia)). exact Eb.
           ** (* [comment removed for export] *)
              rewrite (HC1 t3 Nt3) in G3'.
              assert (Hlt3 : to_Z t3 < to_Z (s_next S)) by exact (Htags _ _ G3').
              apply (regions_after_call_gen RT AF CL lo sp0 r m0 cr0 anc xp H_r XP_stk IMGSH_OK g rho rho2 cd (s_mem S) (s_next S) m m' (g_S RT g) (rt_live RT (g_S RT g)) os rgs (s_next S) t A nz
                       HF HRm2 Hag Egs Eabss Edfs Ewrs Ho16 Hosz HART' MI' Hstk' Hpex eq_refl); try assumption.
              +++ intros b Hb _. assert (Hin : In (rho b, rsize (s_mem S) b) (rt_live RT (g_S RT g))).
                  { rewrite Hlive. apply in_or_app. left. unfold blk_list. apply in_map_iff. exists b. auto. }
                  split; exact Hin.
              +++ intros e He. assert (Hin : In e (rt_live RT (g_S RT g))) by (rewrite Hlive; apply in_or_app; right; exact He).
                  split; exact Hin.
              +++ intros t4 rg4 G4 Hne4 i Hi Hin.
                  destruct (proj2 HRm2 t4 t rg4 rg G4 Eg0 Hne4 (or_intror Ewr)) as [X|X]; rewrite EB in X; unfold A in Hin; clear -X Hin Hi Ec6 Bo; lia.
              +++ rewrite (mget_mset _ T_STK t3 _ (mget_lt _ _ _ Egs)). destruct (Z.eqb_spec (to_Z T_STK) (to_Z t3)) as [E|E]; [exfalso; apply Hne3; apply to_Z_inj; symmetry; exact E | exact G3'].
              +++ intros E. subst t3. clear -Hlt3. lia.
              +++ intros E. subst t3. rewrite sh_tag_Z in Hlt3 by (clear -Hnx; lia). clear -Hlt3. lia.
      * apply (regions_sep_dirs rho2 (s_mem S)); [rewrite <- EMc; exact Hd | exact (proj2 HRm2)].
    + intros rho2 Hag. exact (FMem_law RT CL lo sp0 r m0 cr0 anc xp g rho rho2 _ _ _ m' HF' Hag).
Qed.

End HkMemcpy.
