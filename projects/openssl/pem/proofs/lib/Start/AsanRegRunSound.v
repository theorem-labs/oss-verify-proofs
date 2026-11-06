(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg AgentLib
  AsanAcct AsanAcctShape SpinAlg Hoare.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound
  AsanPlanSoundSums AsanNodesLib AsanNodesLibSound.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanDescs AsanDescsSound AsanRehash AsanRegModel AsanGshModel AsanRegRun AsanRegContract AsanHookKit AsanRehashSound.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module RGNS.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import APSX. Import RGM. Import RGN. Import HKIT.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation W := LBNS.W (only parsing).
#[local] Notation rd_ok := LBNS.rd_ok (only parsing).
#[local] Notation inr := LBNS.inr (only parsing).

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis HULL_le : img_lo A <= img_hi A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable ISP : Z.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Hypothesis NX0_spw : AP.expr_vars_lt nx0 e_spw = true.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.
Variable T : ctab.

#[local] Notation cell := (LBNS.cell SEGS) (only parsing).
#[local] Notation wr_ok := (LBNS.wr_ok SEGS) (only parsing).
#[local] Notation y := (c_lay T) (only parsing).

Hypothesis RGC : RGK.regrun_contract SEGS T.

(* [comment removed for export] *)
Variable HULLS : list (Z * Z).
Variable TAB : list desc.
Hypothesis HTAB : scan SEGS (length TAB) (c_tab T) = Some TAB.
Hypothesis HTABN : c_tab T + 64 * Z.of_nat (length TAB) = c_tabend T.
Hypothesis HSORT : GSM.sortedb (l_ilo y) TAB = true.
Hypothesis HBLOB : forall E M, SINV E M -> forall j lo hi, nth_error HULLS j = Some (lo, hi) ->
  eb E (K_GSH0 + j)%nat = map (Z_to_bv 8) (GSM.gsh_list y TAB lo hi).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma scan_sound : forall (M : word -> option byte) n a ds, scan SEGS n a = Some ds ->
  0 <= a -> a + 64 * Z.of_nat n <= 2 ^ 40 ->
  (forall z, a <= z < a + 64 * Z.of_nat n -> M (Z_to_bv 64 z) = None) ->
  length ds = n /\ forall j, 0 <= j < Z.of_nat n -> RGK.kdesc_at SEGS M (a + 64 * j) (nth (Z.to_nat j) ds (D 0 0 0 0 0)).
Proof.
  intros M n. induction n as [|n IH]; intros a ds H Ha Hn Hnone.
  - cbn [scan] in H. injection H as <-. split; [reflexivity | intros j Hj; cbn in Hj; lia].
  - cbn [scan] in H. rewrite Nat2Z.inj_succ in Hn, Hnone.
    destruct (DSC.rd64 SEGS a) as [b|] eqn:R0; [|discriminate]. destruct (DSC.rd64 SEGS (a + 8)) as [sz|] eqn:R1; [|discriminate].
    destruct (DSC.rd64 SEGS (a + 16)) as [w|] eqn:R2; [|discriminate]. destruct (DSC.rd64 SEGS (a + 40)) as [dy|] eqn:R5; [|discriminate].
    destruct (DSC.rd64 SEGS (a + 56)) as [od|] eqn:R7; [|discriminate]. destruct (scan SEGS n (a + 64)) as [r|] eqn:Hr; [|discriminate].
    injection H as <-.
    destruct (IH (a + 64) r Hr ltac:(lia) ltac:(lia) ltac:(intros z Hz; apply Hnone; lia)) as [Hl Hc].
    split; [cbn [length]; rewrite Hl; reflexivity|]. intros j Hj. rewrite Nat2Z.inj_succ in Hj.
    destruct (Z.eq_dec j 0) as [->|Nj].
    + change (Z.to_nat 0) with 0%nat. cbn [nth]. rewrite Z.mul_0_r, Z.add_0_r. unfold RGK.kdesc_at. cbn [d_beg d_size d_swr d_dyn d_odr].
      assert (X : forall o z, 0 <= o <= 56 -> DSC.rd64 SEGS (a + o) = Some z -> cell M (a + o) 8 (W z)).
      { intros o z Ho Hz. exact (proj1 (DSS.rd64_rdn SEGS M (a + o) z ltac:(lia) ltac:(lia) ltac:(intros q Hq; apply Hnone; lia) Hz)). }
      rewrite <- (Z.add_0_r a) in R0. rewrite <- (Z.add_0_r a) at 1.
      split; [exact (X 0 b ltac:(lia) R0)|]. split; [exact (X 8 sz ltac:(lia) R1)|]. split; [exact (X 16 w ltac:(lia) R2)|].
      split; [exact (X 40 dy ltac:(lia) R5) | exact (X 56 od ltac:(lia) R7)].
    + replace (nth (Z.to_nat j) (D b sz w dy od :: r) (D 0 0 0 0 0)) with (nth (Z.to_nat (j - 1)) r (D 0 0 0 0 0)).
      2:{ replace (Z.to_nat j) with (S (Z.to_nat (j - 1))) by lia. reflexivity. }
      replace (a + 64 * j) with (a + 64 + 64 * (j - 1)) by lia. apply Hc. lia.
Qed.

(* [comment removed for export] *)
Lemma scan_prefix : forall k n a tab, scan SEGS n a = Some tab -> (k <= n)%nat -> scan SEGS k a = Some (firstn k tab).
Proof.
  induction k as [|k IH]; intros n a tab H Hk; [reflexivity|].
  destruct n as [|n]; [lia|]. cbn [scan] in H |- *.
  destruct (DSC.rd64 SEGS a) as [b|]; [|discriminate]. destruct (DSC.rd64 SEGS (a + 8)) as [sz|]; [|discriminate].
  destruct (DSC.rd64 SEGS (a + 16)) as [w|]; [|discriminate]. destruct (DSC.rd64 SEGS (a + 40)) as [dy|]; [|discriminate].
  destruct (DSC.rd64 SEGS (a + 56)) as [od|]; [|discriminate]. destruct (scan SEGS n (a + 64)) as [r|] eqn:Hr; [|discriminate].
  injection H as <-. rewrite (IH n (a + 64) r Hr ltac:(lia)). reflexivity.
Qed.

Lemma scan_skip : forall i n a tab, scan SEGS n a = Some tab -> (i <= n)%nat -> scan SEGS (n - i) (a + 64 * Z.of_nat i) = Some (skipn i tab).
Proof.
  induction i as [|i IH]; intros n a tab H Hi.
  - rewrite Nat.sub_0_r. change (Z.of_nat 0) with 0. rewrite Z.mul_0_r, Z.add_0_r. exact H.
  - destruct n as [|n]; [lia|]. cbn [scan] in H.
    destruct (DSC.rd64 SEGS a) as [b|]; [|discriminate]. destruct (DSC.rd64 SEGS (a + 8)) as [sz|]; [|discriminate].
    destruct (DSC.rd64 SEGS (a + 16)) as [w|]; [|discriminate]. destruct (DSC.rd64 SEGS (a + 40)) as [dy|]; [|discriminate].
    destruct (DSC.rd64 SEGS (a + 56)) as [od|]; [|discriminate]. destruct (scan SEGS n (a + 64)) as [r|] eqn:Hr; [|discriminate].
    injection H as <-. cbn [skipn]. replace (S n - S i)%nat with (n - i)%nat by lia.
    replace (a + 64 * Z.of_nat (S i)) with (a + 64 + 64 * Z.of_nat i) by lia. exact (IH n (a + 64) r Hr ltac:(lia)).
Qed.

Lemma scan_slice : forall i k ds, scan SEGS k (c_tab T + 64 * Z.of_nat i) = Some ds -> (i + k <= length TAB)%nat ->
  TAB = firstn i TAB ++ ds ++ skipn k (skipn i TAB).
Proof.
  intros i k ds H Hik. pose proof (scan_skip i _ _ _ HTAB ltac:(lia)) as H1.
  pose proof (scan_prefix k _ _ _ H1 ltac:(lia)) as H2. rewrite H in H2. injection H2 as ->.
  rewrite firstn_skipn. symmetry. apply firstn_skipn.
Qed.

(* [comment removed for export] *)
Lemma zero_cov_sound : forall E (M : word -> option byte) k lo hi, know_ok SEGS E M k -> zero_cov k lo hi = true ->
  forall z, lo <= z < hi -> M (W z) = Some (Z_to_bv 8 0).
Proof.
  intros E M k lo hi HK H z Hz. unfold zero_cov in H. apply existsb_exists in H as (K & HinK & HKb).
  destruct K as [| [kb a] n | | | | | | | |]; try discriminate HKb. destruct kb as [kb0| | | | | | |]; try discriminate HKb.
  destruct kb0; try discriminate HKb. destruct n as [n| | | | | | |]; try discriminate HKb.
  apply andb_prop in HKb as [HKb C4]. apply andb_prop in HKb as [HKb C3]. apply andb_prop in HKb as [C1 C2].
  apply Z.leb_le in C1, C2, C3. apply Z.ltb_lt in C4.
  pose proof (proj1 (Forall_forall _ _) HK _ HinK) as KO. cbn [kentry_ok] in KO. destruct KO as [_ KO].
  assert (Es : estart E (SA (ELit 0) a) = a) by (unfold estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; lia).
  assert (El : elenZ E (ELit n) = n) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
  specialize (KO (z - a)). rewrite Es, El in KO. replace (a + (z - a)) with z in KO by lia. apply KO. lia.
Qed.

Lemma gsh_extra_sound : forall E E' (M M' : word -> option byte) k ds rest extra i,
  know_ok SEGS E M k -> gsh_extra T HULLS k ds rest = Some extra ->
  scan SEGS (length ds) (c_tab T + 64 * Z.of_nat i) = Some ds -> (i + length ds <= length TAB)%nat ->
  0 <= run_sh_lo y ds -> run_sh_lo y ds <= run_sh_hi y ds -> run_sh_hi y ds < 2 ^ 47 ->
  (forall j lo hi, nth_error HULLS j = Some (lo, hi) -> eb E' (K_GSH0 + j)%nat = map (Z_to_bv 8) (GSM.gsh_list y TAB lo hi)) ->
  (forall x b, run_sh_lo y ds <= x < run_sh_hi y ds -> 0 <= x < 2 ^ 47 -> M (W x) = Some b ->
               M' (W x) = Some (Z_to_bv 8 (GSM.sh_upd y ds x (bv_unsigned b)))) ->
  Forall (kentry_ok SEGS E' M') extra.
Proof.
  intros E E' M M' k ds rest extra i HK Hex Hsc Hik Hlo0 Hlh Hhi Heb Hpost. unfold gsh_extra in Hex.
  destruct rest as [|r0 rest']; [injection Hex as <-; constructor|].
  destruct r0 as [j| | | | | | |]; try discriminate Hex. destruct rest' as [|]; [|discriminate Hex].
  destruct (nth_error HULLS (Z.to_nat j)) as [[hlo hhi]|] eqn:Hnth; [|discriminate Hex].
  match type of Hex with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate Hex] end. injection Hex as <-.
  apply andb_prop in Hc as [Hc Cz]. apply andb_prop in Hc as [Hc C3]. apply andb_prop in Hc as [C1 C2].
  apply Z.eqb_eq in C2, C3. subst hlo hhi.
  set (lo := run_sh_lo y ds) in *. set (hi := run_sh_hi y ds) in *.
  assert (Eb : forall kb, kb = (K_GSH0 + Z.to_nat j)%nat -> eb E' kb = map (Z_to_bv 8) (GSM.gsh_list y TAB lo hi)) by (intros kb ->; exact (Heb _ _ _ Hnth)).
  assert (Es : estart E' (SA (ELit 0) lo) = lo) by (unfold estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; lia).
  assert (El : elenZ E' (ELit (hi - lo)) = hi - lo) by (unfold elenZ; cbn [edenot]; apply u64_lit; lia).
  constructor; [|constructor]. cbv beta iota delta [kentry_ok]. rewrite Es, El.
  split; [unfold flat; rewrite Es; lia|].
  split; [erewrite Eb by reflexivity; rewrite length_map; apply GSM.gsh_list_length; exact Hlh|].
  intros q Hq. erewrite Eb by reflexivity.
  change (Z_to_bv 8 0) with ((fun z => Z_to_bv 8 z) 0). rewrite (map_nth (fun z => Z_to_bv 8 z)). cbv beta.
  rewrite (GSM.gsh_list_nth y TAB lo hi q Hq).
  pose proof (scan_slice i (length ds) ds Hsc Hik) as Hsl.
  rewrite Hsl. rewrite (GSM.gsh_slice y _ ds _ (l_ilo y) (lo + q)) by (first [rewrite <- Hsl; exact HSORT | unfold lo, hi in *; lia]).
  pose proof (zero_cov_sound E M k lo hi HK Cz (lo + q) ltac:(lia)) as Hz.
  pose proof (Hpost (lo + q) (Z_to_bv 8 0) ltac:(unfold lo, hi in *; lia) ltac:(lia) Hz) as Hp. unfold LBNS.W in Hp. rewrite Hp.
  change (bv_unsigned (Z_to_bv 8 0)) with 0. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cell_is_sound : forall E (M : word -> option byte) k a (w : nat) v, know_ok SEGS E M k -> cell_is SEGS k a w v = true ->
  (1 <= w <= 8)%nat -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 -> cell M a w (W v).
Proof.
  intros E M k a w v HK H Hw Ha Hn. unfold cell_is in H. destruct (kreadZ SEGS k (ELit 0) a w) as [z|] eqn:Hz; [|discriminate].
  apply Z.eqb_eq in H. subst z. exact (RHNS.lit_cell SEGS E M k a w v HK Hw Hz Ha Hn).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gap_facts_ok : forall E E' (M M' : word -> option byte) k os wlo whi hlo hhi, know_ok SEGS E M k -> 0 <= wlo -> whi <= 2 ^ 64 ->
  (forall z, wlo <= z < whi -> ~ In z os -> M' (W z) = M (W z)) ->
  Forall (kentry_ok SEGS E' M') (gap_facts k os wlo whi hlo hhi).
Proof.
  intros E E' M M' k os wlo whi hlo hhi HK Hw0 Hw1 Hfr. unfold gap_facts, good_gaps. apply Forall_forall. intros K HK'.
  apply in_map_iff in HK' as (g & <- & Hg). apply filter_In in Hg as [_ Hok]. unfold gap_ok in Hok.
  apply andb_prop in Hok as [Hok Hno]. apply andb_prop in Hok as [Hok Hcov]. apply andb_prop in Hok as [Hok Hhi]. apply andb_prop in Hok as [Hlt Hlo].
  apply Z.ltb_lt in Hlt. apply Z.leb_le in Hlo, Hhi.
  cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros z Hz. change (M' (W z) = None).
  assert (Hnin : ~ In z os).
  { intros Hin. rewrite forallb_forall in Hno. specialize (Hno z Hin). apply orb_prop in Hno as [Y|Y]; [apply Z.ltb_lt in Y | apply Z.leb_le in Y]; lia. }
  rewrite (Hfr z ltac:(lia) Hnin). exact (img_cov_sound SEGS E M k _ _ HK Hcov z Hz).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH ISP FS0) (only parsing).

Lemma reg_get : forall E cs R FULL model (r : nat), CSOK E cs R FULL model -> (0 < r < 32)%nat ->
  getr R (Z_to_bv 5 (Z.of_nat r)) = edenot E (reg cs r).
Proof. intros E cs R FULL model r HC Hr. exact (w_reg_sound SEGS A LIMIT SINV argH ISP FS0 E cs R FULL model r HC Hr). Qed.

Lemma chk_regs_sound : forall E cs R FULL model, CSOK E cs R FULL model -> chk_regs T cs = true ->
  getr R 9%bv = W (c_tab T) /\ getr R 20%bv = W (c_shcell T) /\ getr R 21%bv = W 1 /\ getr R 24%bv = W (c_flags T) /\ getr R 25%bv = W (c_statics T).
Proof.
  intros E cs R FULL model HC H. unfold chk_regs in H.
  destruct (RHN.lit1 (reg cs 9)) as [r9|] eqn:L9; [|discriminate]. destruct (RHN.lit1 (reg cs 20)) as [r20|] eqn:L20; [|discriminate].
  destruct (RHN.lit1 (reg cs 21)) as [r21|] eqn:L21; [|discriminate]. destruct (RHN.lit1 (reg cs 24)) as [r24|] eqn:L24; [|discriminate].
  destruct (RHN.lit1 (reg cs 25)) as [r25|] eqn:L25; [|discriminate].
  apply andb_prop in H as [H E25]. apply andb_prop in H as [H E24]. apply andb_prop in H as [H E21]. apply andb_prop in H as [E9 E20].
  apply Z.eqb_eq in E9, E20, E21, E24, E25. subst.
  split; [change (getr R 9%bv) with (getr R (Z_to_bv 5 (Z.of_nat 9))); rewrite (reg_get E cs R FULL model 9 HC ltac:(lia)); exact (RHNS.lit1_w E _ _ L9)|].
  split; [change (getr R 20%bv) with (getr R (Z_to_bv 5 (Z.of_nat 20))); rewrite (reg_get E cs R FULL model 20 HC ltac:(lia)); exact (RHNS.lit1_w E _ _ L20)|].
  split; [change (getr R 21%bv) with (getr R (Z_to_bv 5 (Z.of_nat 21))); rewrite (reg_get E cs R FULL model 21 HC ltac:(lia)); exact (RHNS.lit1_w E _ _ L21)|].
  split; [change (getr R 24%bv) with (getr R (Z_to_bv 5 (Z.of_nat 24))); rewrite (reg_get E cs R FULL model 24 HC ltac:(lia)); exact (RHNS.lit1_w E _ _ L24)|].
  change (getr R 25%bv) with (getr R (Z_to_bv 5 (Z.of_nat 25))). rewrite (reg_get E cs R FULL model 25 HC ltac:(lia)). exact (RHNS.lit1_w E _ _ L25).
Qed.

(* [comment removed for export] *)
Lemma lit_wr : forall E (M : word -> option byte) k a n, know_ok SEGS E M k -> kwritable_x k k (ELit 0) a (ELit n) = true ->
  0 <= a -> a < 2 ^ 62 -> 0 < n < 2 ^ 62 -> wr_ok M a n.
Proof.
  intros E M k a n HK H Ha Ha1 Hn.
  assert (Es : estart E (SA (ELit 0) a) = a) by (unfold estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; lia).
  destruct (kwr_wr_ok SEGS E M k (ELit 0) a n HK H ltac:(lia) ltac:(rewrite Es; lia)) as (X & _ & _). rewrite Es in X. exact X.
Qed.

Lemma chk_tab_sound : forall E (M : word -> option byte) k i kz n ds N ks ne r, know_ok SEGS E M k ->
  chk_tab SEGS A T k i kz n ds = true -> scan SEGS (Z.to_nat kz) (c_tab T + 64 * i) = Some ds -> run y N ds ks ne = Some r ->
  Z.of_nat (length ds) = kz /\ 1 <= kz <= 2 ^ 20 /\ 0 <= i /\ i + kz < n /\ c_tab T + 64 * n <= c_tabend T /\ 0 <= c_tab T /\ c_tab T + 64 * n < 2 ^ 40
  /\ (forall j, 0 <= j < kz -> RGK.kdesc_at SEGS M (c_tab T + 64 * (i + j)) (nth (Z.to_nat j) ds (D 0 0 0 0 0)))
  /\ List.NoDup (inds ds) /\ (forall o, In o (inds ds) -> cell M o 1 (W 0)) /\ wr_ok M (l_odr_lo y) (l_odr_hi y - l_odr_lo y)
  /\ img_lo A <= l_odr_lo y /\ l_odr_hi y <= img_hi A /\ 0 <= l_odr_lo y.
Proof.
  intros E M k i kz n ds N ks ne r HK H Hscan Hrun. unfold chk_tab in H.
  apply andb_prop in H as [H C16]. apply andb_prop in H as [H C15]. apply andb_prop in H as [H C14]. apply andb_prop in H as [H C13].
  apply andb_prop in H as [H C12]. apply andb_prop in H as [H C11]. apply andb_prop in H as [H C10]. apply andb_prop in H as [H C9].
  apply andb_prop in H as [H C8]. apply andb_prop in H as [H C7]. apply andb_prop in H as [H C6]. apply andb_prop in H as [H C5].
  apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
  apply Z.leb_le in C1, C2, C4, C6, C8, C13, C14, C15. apply Z.eqb_eq in C3. apply Z.ltb_lt in C5, C9, C16.
  pose proof HULL_ok as (HU0 & _ & _ & HU3). unfold KHI in HU3.
  assert (Hnone : forall z, c_tab T + 64 * i <= z < c_tab T + 64 * i + 64 * Z.of_nat (Z.to_nat kz) -> M (Z_to_bv 64 z) = None).
  { intros z Hz. apply (img_cov_sound SEGS E M k _ _ HK C7 z). rewrite Z2Nat.id in Hz by lia. lia. }
  destruct (scan_sound M (Z.to_nat kz) (c_tab T + 64 * i) ds Hscan ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) Hnone) as [Hl Hd].
  split; [exact C3|]. split; [lia|]. split; [exact C4|]. split; [exact C5|]. split; [exact C6|]. split; [exact C8|]. split; [exact C9|].
  split.
  { intros j Hj. specialize (Hd j ltac:(rewrite Z2Nat.id by lia; lia)).
    replace (c_tab T + 64 * (i + j)) with (c_tab T + 64 * i + 64 * j) by lia. exact Hd. }
  split; [exact (RHNS.znodup_sound _ C10)|].
  split.
  { intros o Ho. rewrite forallb_forall in C11. specialize (C11 o Ho).
    pose proof (inds_window y ds (run_ok _ _ _ _ _ _ Hrun) o Ho) as Bo.
    exact (cell_is_sound E M k o 1 0 HK C11 ltac:(lia) ltac:(lia) ltac:(cbn; lia)). }
  split; [exact (lit_wr E M k _ _ HK C12 ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [exact C13|]. split; [exact C14 | exact C15].
Qed.

Lemma chk_consts_sound : forall E (M : word -> option byte) k, know_ok SEGS E M k -> chk_consts SEGS A T k = true ->
  cell M (c_inited T) 1 (W 1) /\ wr_ok M (c_inited T) 1
  /\ cell M (c_flags T + 24) 4 (W 1) /\ cell M (c_flags T + 85) 1 (W 1) /\ cell M (c_flags T + 100) 4 (W 2)
  /\ cell M (c_shcell T) 8 (W (l_shb y)) /\ cell M (c_canpoison T) 1 (W 1) /\ cell M (c_msetcell T) 8 (W (c_memset T)) /\ cell M (c_llaalign T) 8 (W 8)
  /\ Forall (fun a => img_lo A <= a /\ a + 128 <= img_hi A) [c_inited T; c_flags T; c_shcell T; c_canpoison T; c_msetcell T; c_llaalign T; c_lla T; c_statics T; c_map T].
Proof.
  intros E M k HK H. unfold chk_consts in H.
  apply andb_prop in H as [H C10]. apply andb_prop in H as [H C9]. apply andb_prop in H as [H C8]. apply andb_prop in H as [H C7].
  apply andb_prop in H as [H C6]. apply andb_prop in H as [H C5]. apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
  pose proof HULL_ok as (HU0 & _ & _ & HU3). unfold KHI in HU3.
  assert (HB : Forall (fun a => img_lo A <= a /\ a + 128 <= img_hi A) [c_inited T; c_flags T; c_shcell T; c_canpoison T; c_msetcell T; c_llaalign T; c_lla T; c_statics T; c_map T]).
  { apply Forall_forall. intros a Ha. rewrite forallb_forall in C10. specialize (C10 a Ha). apply andb_prop in C10 as [X1 X2].
    apply Z.leb_le in X1, X2. lia. }
  pose proof HB as HB'. repeat (apply Forall_cons_iff in HB' as [? HB']).
  split; [exact (cell_is_sound E M k _ 1 _ HK C1 ltac:(lia) ltac:(lia) ltac:(cbn; lia))|].
  split; [exact (lit_wr E M k _ _ HK C2 ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [exact (cell_is_sound E M k _ 4 _ HK C3 ltac:(lia) ltac:(lia) ltac:(cbn; lia))|].
  split; [exact (cell_is_sound E M k _ 1 _ HK C4 ltac:(lia) ltac:(lia) ltac:(cbn; lia))|].
  split; [exact (cell_is_sound E M k _ 4 _ HK C5 ltac:(lia) ltac:(lia) ltac:(cbn; lia))|].
  split; [exact (cell_is_sound E M k _ 8 _ HK C6 ltac:(lia) ltac:(lia) ltac:(cbn; lia))|].
  split; [exact (cell_is_sound E M k _ 1 _ HK C7 ltac:(lia) ltac:(lia) ltac:(cbn; lia))|].
  split; [exact (cell_is_sound E M k _ 8 _ HK C8 ltac:(lia) ltac:(lia) ltac:(cbn; lia))|].
  split; [exact (cell_is_sound E M k _ 8 _ HK C9 ltac:(lia) ltac:(lia) ltac:(cbn; lia)) | exact HB].
Qed.

(* [comment removed for export] *)
Lemma sym_cell : forall E (M : word -> option byte) k e off (w : nat) z, know_ok SEGS E M k -> (1 <= w <= 8)%nat ->
  kreadZ SEGS k (fst (split_lit e)) (snd (split_lit e) + off) w = Some z ->
  estart E (SA (fst (split_lit e)) (snd (split_lit e))) = bv_unsigned (edenot E e) ->
  0 <= bv_unsigned (edenot E e) + off -> bv_unsigned (edenot E e) + off + Z.of_nat w <= 2 ^ 64 ->
  cell M (bv_unsigned (edenot E e) + off) w (W z).
Proof.
  intros E M k e off w z HK Hw H Hs H0 H1. unfold kreadZ in H.
  destruct (know_lookup SEGS k (fst (split_lit e)) (snd (split_lit e) + off) w false [] []) as [v scs hs|scs hs|] eqn:HL; try discriminate.
  destruct v as [z0| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection H as <-.
  rewrite LBNS.W_mod. change (Z_to_bv 64 z0) with (edenot E (ELit z0)).
  apply (LBNS.lookup_cell SEGS E M k e off w (ELit z0) hs HK Hw HL); [| exact H0 | exact H1].
  unfold estart in *. cbn [a_base a_off] in *. lia.
Qed.

Lemma chk_frame_sound : forall E (M : word -> option byte) k fp sp n, know_ok SEGS E M k ->
  chk_frame SEGS A T k fp sp (eaddz fp (-0x10a8)) (eaddz sp (-32)) (fst (split_lit (eaddz fp (-0x10a8)))) (snd (split_lit (eaddz fp (-0x10a8)))) n = true ->
  let fpz := bv_unsigned (edenot E fp) in
  bv_unsigned (edenot E sp) = fpz - 0x10f0
  /\ cell M (fpz - 0x10b0) 8 (W n) /\ cell M (fpz - 0x10d0) 8 (W (c_msetcell T))
  /\ RGK.rw SEGS M (fpz - 0x10a8) 8 /\ RGK.rw SEGS M (fpz - 0x10f0 - 32) 32
  /\ fpz mod 16 = 0 /\ l_ihi y <= fpz - 0x10f0 - 32 /\ shad y (l_ihi y) <= fpz - 0x10f0 - 32 /\ fpz < 2 ^ 47
  /\ (fpz - 0x10a8 + 8 <= img_lo A \/ img_hi A <= fpz - 0x10a8) /\ (fpz - 0x10f0 - 32 + 32 <= img_lo A \/ img_hi A <= fpz - 0x10f0 - 32)
  /\ estart E (SA (fst (split_lit (eaddz fp (-0x10a8)))) (snd (split_lit (eaddz fp (-0x10a8))))) = fpz - 0x10a8
  /\ estart E (SA (fst (split_lit (eaddz sp (-32)))) (snd (split_lit (eaddz sp (-32))))) = fpz - 0x10f0 - 32.
Proof.
  intros E M k fp sp n HK H fpz. unfold chk_frame in H.
  set (ek := eaddz fp (-0x10a8)) in *. set (es := eaddz sp (-32)) in *.
  destruct (kreadZ SEGS k (fst (split_lit ek)) (snd (split_lit ek) - 8) 8) as [n'|] eqn:Kn; [|discriminate].
  destruct (kreadZ SEGS k (fst (split_lit ek)) (snd (split_lit ek) - 40) 8) as [p|] eqn:Kp; [|discriminate].
  destruct (xlo k (esub fp sp)) as [dlo|] eqn:Hdlo; [|discriminate]. destruct (xhi k (esub fp sp)) as [dhi|] eqn:Hdhi; [|discriminate].
  destruct (xlo k sp) as [splo|] eqn:Hsplo; [|discriminate]. destruct (xhi k fp) as [fphi|] eqn:Hfphi; [|discriminate].
  destruct (xlo k fp) as [fplo|] eqn:Hfplo; [|discriminate].
  apply andb_prop in H as [H C11]. apply Z.leb_le in C11.
  apply andb_prop in H as [H C10]. apply andb_prop in H as [H C9]. apply andb_prop in H as [H C8]. apply andb_prop in H as [H C7].
  apply andb_prop in H as [H C6]. apply andb_prop in H as [H C5]. apply andb_prop in H as [H C4b]. apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
  apply Z.eqb_eq in C1, C2, C3, C4. apply Z.leb_le in C4b, C5, C6, C7. apply Z.ltb_lt in C8. subst n' p dlo dhi.
  set (spz := bv_unsigned (edenot E sp)).
  pose proof (xlo_sound SEGS E M k _ _ HK Hdlo) as X1. pose proof (xhi_sound SEGS E M k _ _ HK Hdhi) as X2. rewrite LBNS.u_esub in X1, X2. fold fpz spz in X1, X2.
  pose proof (xlo_sound SEGS E M k _ _ HK Hsplo) as X3. fold spz in X3. pose proof (xhi_sound SEGS E M k _ _ HK Hfphi) as X4. fold fpz in X4.
  pose proof (xlo_sound SEGS E M k _ _ HK Hfplo) as X5. fold fpz in X5.
  pose proof (u64_range (edenot E fp)) as Rf. fold fpz in Rf. pose proof (u64_range (edenot E sp)) as Rs. fold spz in Rs.
  pose proof HULL_ok as (HU0 & _ & _ & HU3). unfold KHI in HU3.
  assert (Hih : 0 <= l_ihi y \/ True) by (right; exact I).
  assert (Esp : spz = fpz - 0x10f0).
  { clear - X1 X2 Rf Rs X3 X4 X5 C4b C8.
    assert (Hm : (fpz - spz) mod 2 ^ 64 = 0x10f0) by lia.
    assert (Hq : exists q, fpz - spz = 0x10f0 + 2 ^ 64 * q) by (exists ((fpz - spz) / 2 ^ 64); pose proof (Z.div_mod (fpz - spz) (2 ^ 64) ltac:(lia)); lia).
    destruct Hq as [q Hq]. assert (q = 0) by lia. subst q. lia. }
  assert (Hsh0 : 0 <= shad y (l_ihi y) + 32 <= splo \/ True) by (right; exact I).
  assert (Eek : bv_unsigned (edenot E ek) = fpz - 0x10a8).
  { unfold ek. rewrite u_eaddz. fold fpz. apply Z.mod_small. clear - Esp X3 C6 C11 Rf Rs. lia. }
  assert (Ees : bv_unsigned (edenot E es) = fpz - 0x10f0 - 32).
  { unfold es. rewrite u_eaddz. fold spz. rewrite Esp. apply Z.mod_small. clear - Esp X3 C6 C11 Rf Rs. lia. }
  destruct (RHNS.ovl_facts SEGS A SEGS_in_hull HULL_ok HULL_le E M k ek 8 HK C9 ltac:(lia) ltac:(rewrite Eek; clear - Rf; lia)) as (Krd & Kwr & Koff & Kst).
  destruct (RHNS.ovl_facts SEGS A SEGS_in_hull HULL_ok HULL_le E M k es 32 HK C10 ltac:(lia) ltac:(rewrite Ees; clear - Rf; lia)) as (Srd & Swr & Soff & Sst).
  rewrite Eek in Krd, Kwr, Koff, Kst. rewrite Ees in Srd, Swr, Soff, Sst.
  pose proof (sym_cell E M k ek (-8) 8 n HK ltac:(lia) Kn ltac:(rewrite Kst, Eek; reflexivity) ltac:(rewrite Eek; clear - Esp X3 C6 C11; lia)
                ltac:(rewrite Eek; clear - Rf; lia)) as Cn.
  pose proof (sym_cell E M k ek (-40) 8 (c_msetcell T) HK ltac:(lia) Kp ltac:(rewrite Kst, Eek; reflexivity) ltac:(rewrite Eek; clear - Esp X3 C6 C11; lia)
                ltac:(rewrite Eek; clear - Rf; lia)) as Cp.
  rewrite Eek in Cn, Cp. replace (fpz - 0x10a8 + -8) with (fpz - 0x10b0) in Cn by lia. replace (fpz - 0x10a8 + -40) with (fpz - 0x10d0) in Cp by lia.
  pose proof (ealign_sound SEGS E M k fp HK) as [_ Af]. fold fpz in Af. pose proof (RHNS.div_mod16 _ _ C5 Af) as Af16.
  split; [exact Esp|]. split; [exact Cn|]. split; [exact Cp|]. split; [split; [exact Krd | exact Kwr]|]. split; [split; [exact Srd | exact Swr]|].
  split; [exact Af16|]. split; [clear - Esp X3 C6; lia|]. split; [clear - Esp X3 C7; lia|]. split; [clear - X4 C8; lia|].
  split; [exact Koff|]. split; [exact Soff|]. split; [exact Kst | exact Sst].
Qed.

Lemma chk_shadow_sound : forall E (M : word -> option byte) k ds, know_ok SEGS E M k -> chk_shadow A T k ds = true ->
  let wlo := shad y (l_ilo y) in let whi := shad y (l_ihi y) in
  RGK.rw SEGS M wlo (whi - wlo) /\ wlo <= run_sh_lo y ds /\ run_sh_lo y ds <= run_sh_hi y ds /\ run_sh_hi y ds <= whi /\ img_hi A <= wlo /\ wlo < whi < 2 ^ 47
  /\ l_ilo y = img_lo A /\ l_ihi y = img_hi A.
Proof.
  intros E M k ds HK H wlo whi. unfold chk_shadow in H. fold wlo whi in H.
  apply andb_prop in H as [H C9]. apply andb_prop in H as [H C8]. apply andb_prop in H as [H C7]. apply andb_prop in H as [H C6].
  apply andb_prop in H as [H C5]. apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
  apply Z.leb_le in C2, C3, C4, C5. apply Z.ltb_lt in C6, C7. apply Z.eqb_eq in C8, C9.
  pose proof HULL_ok as (HU0 & _ & _ & HU3). unfold KHI in HU3.
  assert (Uw : bv_unsigned (edenot E (ELit wlo)) = wlo) by (cbn [edenot]; apply u64_lit; lia).
  destruct (RHNS.ovl_facts SEGS A SEGS_in_hull HULL_ok HULL_le E M k (ELit wlo) (whi - wlo) HK C1 ltac:(lia) ltac:(rewrite Uw; lia)) as (Wrd & Wwr & _ & _).
  rewrite Uw in Wrd, Wwr.
  split; [split; [exact Wrd | exact Wwr]|]. repeat (split; [assumption|]). split; [lia|]. split; assumption.
Qed.

Lemma chk_list_sound : forall E (M : word -> option byte) k size kz first, know_ok SEGS E M k -> chk_list T k size kz = true ->
  kreadZ SEGS k (ELit 0) (c_statics T + 8) 8 = Some size -> kread8e SEGS k (ELit 0) (c_statics T + 16) = Some first ->
  0 <= c_statics T -> c_statics T + 128 <= 2 ^ 47 ->
  cell M (c_statics T + 8) 8 (W size) /\ cell M (c_statics T + 16) 8 (edenot E first) /\ wr_ok M (c_statics T + 8) 16 /\ 1 <= size /\ size + kz < 2 ^ 62
  /\ (c_statics T + 24 <= l_odr_lo y \/ l_odr_hi y <= c_statics T + 8).
Proof.
  intros E M k size kz first HK H Ksz Kfi Hs0 Hs1. unfold chk_list in H.
  apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
  apply Z.leb_le in C1. apply Z.ltb_lt in C2.
  split; [exact (RHNS.lit_cell SEGS E M k _ 8 _ HK ltac:(lia) Ksz ltac:(lia) ltac:(lia))|].
  split; [exact (RHNS.lit_cell8e SEGS E M k _ _ HK Kfi ltac:(lia) ltac:(lia))|].
  split; [exact (lit_wr E M k _ _ HK C3 ltac:(lia) ltac:(lia) ltac:(lia))|]. split; [exact C1|]. split; [exact C2|].
  apply orb_prop in C4 as [Y|Y]; apply Z.leb_le in Y; [left | right]; exact Y.
Qed.

Lemma lit_start : forall E a, 0 <= a < 2 ^ 64 -> estart E (SA (ELit 0) a) = a.
Proof. intros E a Ha. unfold estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia. Qed.

Lemma chk_lla_sound : forall E (M : word -> option byte) k cur lend sb so na fpz, know_ok SEGS E M k ->
  chk_lla A T k cur lend (fst (split_lit cur)) (snd (split_lit cur)) sb so na = true ->
  kread8e SEGS k (ELit 0) (c_lla T) = Some lend -> kread8e SEGS k (ELit 0) (c_lla T + 8) = Some cur ->
  estart E (SA sb so) = fpz - 0x10f0 - 32 -> 1 <= na <= 2 ^ 22 -> 0 <= c_lla T -> c_lla T + 128 <= 2 ^ 47 ->
  0 <= shad y (l_ilo y) -> shad y (l_ilo y) < shad y (l_ihi y) < 2 ^ 47 ->
  let curz := bv_unsigned (edenot E cur) in let lendz := bv_unsigned (edenot E lend) in
  cell M (c_lla T) 8 (W lendz) /\ cell M (c_lla T + 8) 8 (W curz) /\ wr_ok M (c_lla T) 16
  /\ 0 < curz /\ curz + 16 * na <= lendz /\ lendz < 2 ^ 47 /\ RGK.rw SEGS M curz (16 * na)
  /\ (curz + 16 * na <= img_lo A \/ img_hi A <= curz)
  /\ (curz + 16 * na <= shad y (l_ilo y) \/ shad y (l_ihi y) <= curz)
  /\ (curz + 16 * na <= fpz - 0x10f0 - 32 \/ fpz <= curz)
  /\ estart E (SA (fst (split_lit cur)) (snd (split_lit cur))) = curz
  /\ (c_lla T + 16 <= l_odr_lo y \/ l_odr_hi y <= c_lla T + 8).
Proof.
  intros E M k cur lend sb so na fpz HK H Klend Kcur Sst Hna Hl0 Hl1 Hw0 Hw1 curz lendz. unfold chk_lla in H.
  destruct (xlo k cur) as [curlo|] eqn:H1; [|discriminate]. destruct (xhi k lend) as [lendhi|] eqn:H2; [|discriminate].
  destruct (xlo k (esub lend cur)) as [roomlo|] eqn:H3; [|discriminate]. destruct (xhi k (esub lend cur)) as [roomhi|] eqn:H4; [|discriminate].
  destruct (xhi k cur) as [curhi|] eqn:H5; [|discriminate].
  apply andb_prop in H as [H C10]. apply andb_prop in H as [H C9]. apply andb_prop in H as [H C8]. apply andb_prop in H as [H C7]. apply andb_prop in H as [H C6].
  apply andb_prop in H as [H C5]. apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
  apply Z.ltb_lt in C1, C4, C5. apply Z.leb_le in C2, C3.
  pose proof (xlo_sound SEGS E M k _ _ HK H1) as X1. fold curz in X1. pose proof (xhi_sound SEGS E M k _ _ HK H2) as X2. fold lendz in X2.
  pose proof (xlo_sound SEGS E M k _ _ HK H3) as X3. pose proof (xhi_sound SEGS E M k _ _ HK H4) as X4. rewrite LBNS.u_esub in X3, X4. fold curz lendz in X3, X4.
  pose proof (xhi_sound SEGS E M k _ _ HK H5) as X5. fold curz in X5.
  pose proof (u64_range (edenot E lend)) as Rl. fold lendz in Rl.
  assert (Hroom : curz + 16 * na <= lendz).
  { clear - X1 X2 X3 X4 X5 C1 C2 C3 C4 C5 Rl.
    destruct (Z_lt_ge_dec (lendz - curz) 0) as [Hneg|Hpos].
    - exfalso. assert (Hm : (lendz - curz) mod 2 ^ 64 = lendz - curz + 2 ^ 64).
      { symmetry. apply (Z.mod_unique _ _ (-1)); lia. }
      lia.
    - rewrite Z.mod_small in X3 by lia. lia. }
  destruct (RHNS.ovl_facts SEGS A SEGS_in_hull HULL_ok HULL_le E M k cur (16 * na) HK C6 ltac:(lia) ltac:(fold curz; clear - X5 C4 Hna; lia)) as (Crd & Cwr & Coff & Cst).
  fold curz in Crd, Cwr, Coff, Cst.
  assert (El1 : elenZ E (ELit (16 * na)) = 16 * na) by (apply elenZ_lit; lia).
  pose proof (ranges_apart_x_sound SEGS E M k _ _ _ _ _ _ HK C8) as P1. rewrite Cst, El1, (lit_start E (shad y (l_ilo y)) ltac:(lia)) in P1.
  rewrite (elenZ_lit E (shad y (l_ihi y) - shad y (l_ilo y)) ltac:(lia)) in P1.
  pose proof (ranges_apart_x_sound SEGS E M k _ _ _ _ _ _ HK C9) as P2. rewrite Cst, El1, Sst in P2. rewrite (elenZ_lit E (0x10f0 + 32) ltac:(lia)) in P2.
  pose proof (RHNS.lit_cell8e SEGS E M k _ _ HK Klend ltac:(lia) ltac:(lia)) as CL. rewrite <- (LBNS.W_u (edenot E lend)) in CL. fold lendz in CL.
  pose proof (RHNS.lit_cell8e SEGS E M k _ _ HK Kcur ltac:(lia) ltac:(lia)) as CC. rewrite <- (LBNS.W_u (edenot E cur)) in CC. fold curz in CC.
  split; [exact CL|]. split; [exact CC|]. split; [exact (lit_wr E M k _ _ HK C7 ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [clear - X1 C1; lia|]. split; [exact Hroom|]. split; [clear - X2 C5; lia|]. split; [split; [exact Crd | exact Cwr]|].
  split; [exact Coff|]. split; [clear - P1; lia|]. split; [clear - P2; lia|]. split; [exact Cst|].
  apply orb_prop in C10 as [Y|Y]; apply Z.leb_le in Y; [left | right]; exact Y.
Qed.

Lemma read_map_sound : forall k B N ne ks, read_map SEGS T k = Some (B, N, ne, ks) ->
  kread8e SEGS k (ELit 0) (c_map T) = Some B /\ kreadZ SEGS k (ELit 0) (c_map T + 8) 4 = Some ne /\ kreadZ SEGS k (ELit 0) (c_map T + 16) 4 = Some N
  /\ RHN.keys_of (RHN.collect k (fst (split_lit B))) (snd (split_lit B)) (Z.to_nat N) = Some ks.
Proof.
  intros k B N ne ks H. unfold read_map in H.
  destruct (kread8e SEGS k (ELit 0) (c_map T)) as [B0|] eqn:K1; [|discriminate]. destruct (kreadZ SEGS k (ELit 0) (c_map T + 8) 4) as [ne0|] eqn:K2; [|discriminate].
  destruct (kreadZ SEGS k (ELit 0) (c_map T + 16) 4) as [N0|] eqn:K3; [|discriminate]. destruct (split_lit B0) as [nb no] eqn:Hsp.
  destruct (RHN.keys_of (RHN.collect k nb) no (Z.to_nat N0)) as [ks0|] eqn:K4; [|discriminate]. injection H as <- <- <- <-.
  rewrite Hsp. cbn [fst snd]. repeat split; try reflexivity. exact K4.
Qed.

Lemma chk_map_sound : forall E (M : word -> option byte) cs k B N ne ks cb co sb so na curz fpz, know_ok SEGS E M k ->
  chk_map SEGS A T cs k B N ne ks (fst (split_lit B)) (snd (split_lit B)) cb co sb so na = true ->
  read_map SEGS T k = Some (B, N, ne, ks) ->
  estart E (SA cb co) = curz -> estart E (SA sb so) = fpz - 0x10f0 - 32 -> 1 <= na <= 2 ^ 22 ->
  0 <= c_map T -> c_map T + 128 <= 2 ^ 47 -> 0 <= c_statics T -> c_statics T + 128 <= 2 ^ 47 ->
  0 <= shad y (l_ilo y) -> shad y (l_ilo y) < shad y (l_ihi y) < 2 ^ 47 -> l_ilo y = img_lo A -> l_ihi y = img_hi A ->
  let Bz := bv_unsigned (edenot E B) in
  RGK.kmap_pre SEGS T M Bz N ne ks curz na fpz
  /\ estart E (SA (fst (split_lit B)) (snd (split_lit B))) = Bz /\ (Bz + 32 * N <= img_lo A \/ img_hi A <= Bz)
  /\ AP.expr_vars_lt (nxt cs) B = true
  /\ (c_map T + 12 <= l_odr_lo y \/ l_odr_hi y <= c_map T + 8).
Proof.
  intros E M cs k B N ne ks cb co sb so na curz fpz HK H Hrm Cst Sst Hna Hm0 Hm1 Hs0 Hs1 Hw0 Hw1 Elo Ehi Bz.
  destruct (read_map_sound k B N ne ks Hrm) as (KB & Kne & KN & Kks). unfold chk_map in H.
  destruct (xlo k B) as [blo|] eqn:H1; [| rewrite !andb_false_r in H; discriminate H].
  destruct (xhi k B) as [bhi|] eqn:H2; [| rewrite !andb_false_r in H; discriminate H].
  apply andb_prop in H as [H C16]. apply andb_prop in H as [H C15]. apply andb_prop in H as [H C14]. apply andb_prop in H as [H C13].
  apply andb_prop in H as [H C12]. apply andb_prop in H as [H C11]. apply andb_prop in H as [H C10]. apply andb_prop in H as [H C9].
  apply andb_prop in H as [H C8]. apply andb_prop in H as [H C7]. apply andb_prop in H as [H C6]. apply andb_prop in H as [H C5].
  apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
  apply andb_prop in C10 as [C10a C10b]. apply Z.ltb_lt in C10a. apply Z.leb_le in C10b, C5, C6, C7, C11.
  pose proof (xlo_sound SEGS E M k _ _ HK H1) as X1. fold Bz in X1. pose proof (xhi_sound SEGS E M k _ _ HK H2) as X2. fold Bz in X2.
  destruct (RHNS.ovl_facts SEGS A SEGS_in_hull HULL_ok HULL_le E M k B (32 * N) HK C12 ltac:(lia) ltac:(fold Bz; clear - X2 C10b C5; lia)) as (Brd & Bwr & Boff & Bst).
  fold Bz in Brd, Bwr, Boff, Bst.
  assert (ElN : elenZ E (ELit (32 * N)) = 32 * N) by (apply elenZ_lit; lia).
  assert (Ela : elenZ E (ELit (16 * na)) = 16 * na) by (apply elenZ_lit; lia).
  pose proof (ranges_apart_x_sound SEGS E M k _ _ _ _ _ _ HK C13) as P1. rewrite Bst, ElN, (lit_start E (shad y (l_ilo y)) ltac:(lia)) in P1.
  rewrite (elenZ_lit E (shad y (l_ihi y) - shad y (l_ilo y)) ltac:(lia)) in P1.
  pose proof (ranges_apart_x_sound SEGS E M k _ _ _ _ _ _ HK C14) as P2. rewrite Bst, ElN, Cst, Ela in P2.
  pose proof (ranges_apart_x_sound SEGS E M k _ _ _ _ _ _ HK C15) as P3. rewrite Bst, ElN, Sst in P3. rewrite (elenZ_lit E (0x10f0 + 32) ltac:(lia)) in P3.
  destruct (RHNS.keys_cells SEGS E M k _ _ _ _ HK Kks) as [Hlen Hkeys]. rewrite Bst in Hkeys. rewrite Z2Nat.id in Hkeys by lia.
  pose proof (ealign_sound SEGS E M k B HK) as [_ Ab]. fold Bz in Ab. pose proof (RHNS.div_mod8 _ _ C11 Ab) as Ab8.
  pose proof (RHNS.lit_cell8e SEGS E M k _ _ HK KB ltac:(lia) ltac:(lia)) as CB. rewrite <- (LBNS.W_u (edenot E B)) in CB. fold Bz in CB.
  split; [| split; [exact Bst | split; [exact Boff | split; [exact C9 | apply orb_prop in C16 as [Y|Y]; apply Z.leb_le in Y; [left | right]; exact Y]]]].
  unfold RGK.kmap_pre.
  split; [exact (cell_is_sound E M k _ 8 _ HK C1 ltac:(lia) ltac:(lia) ltac:(cbn; lia))|].
  split; [exact (lit_wr E M k _ _ HK C2 ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [exact CB|].
  split; [exact (RHNS.lit_cell SEGS E M k _ 4 _ HK ltac:(lia) Kne ltac:(lia) ltac:(lia))|].
  split; [exact (cell_is_sound E M k _ 4 _ HK C3 ltac:(lia) ltac:(lia) ltac:(cbn; lia))|].
  split; [exact (RHNS.lit_cell SEGS E M k _ 4 _ HK ltac:(lia) KN ltac:(lia) ltac:(lia))|].
  split; [exact (lit_wr E M k _ _ HK C4 ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [lia|]. split; [exact C7|]. split; [rewrite Hlen; apply Z2Nat.id; lia|].
  split.
  { apply Forall_forall. intros key Hin. rewrite forallb_forall in C8. specialize (C8 key Hin). apply andb_prop in C8 as [Y1 Y2].
    apply Z.leb_le in Y1. apply Z.ltb_lt in Y2. lia. }
  split; [exact Hkeys|]. split; [split; [exact Brd | exact Bwr]|].
  split; [clear - X1 C10a; lia|]. split; [clear - X2 C10b; lia|]. split; [rewrite Elo, Ehi; exact Boff|]. split; [exact Ab8|].
  split; [clear - P1; lia|]. split; [clear - P2; lia|]. clear - P3. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rg_fresh_nodup : List.NoDup rg_fresh.
Proof.
  unfold rg_fresh. repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H|]). apply List.NoDup_nil.
Qed.

Theorem node_regrun_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (fun cs => node_regrun SEGS A nx0 T HULLS cs args).
Proof.
  intros args cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := Mr A argH E cs model FULL) in *.
  unfold node_regrun in Hn.
  destruct args as [|a0 rest]; [discriminate Hn|]. destruct a0 as [kz| | | | | | |]; try discriminate Hn.
  destruct (negb (Z.eqb (pc cs) (c_entry T))) eqn:Hpc0; [discriminate|]. apply negb_false_iff in Hpc0. apply Z.eqb_eq in Hpc0.
  cbv zeta in Hn.
  set (fp := reg cs 8) in *. set (sp := reg cs 2) in *. set (ek := eaddz fp (-0x10a8)) in *. set (es := eaddz sp (-32)) in *.
  rewrite (surjective_pairing (split_lit ek)) in Hn. rewrite (surjective_pairing (split_lit es)) in Hn.
  destruct (RHN.lit1 (reg cs 27)) as [i|] eqn:L27; [|discriminate].
  destruct (kreadZ SEGS (kn cs) (fst (split_lit ek)) (snd (split_lit ek) - 8) 8) as [n|] eqn:Kn; [|discriminate].
  destruct (scan SEGS (Z.to_nat kz) (c_tab T + 64 * i)) as [ds|] eqn:Hscan; [|discriminate].
  destruct (kread8e SEGS (kn cs) (ELit 0) (c_lla T)) as [lend|] eqn:Klend; [|discriminate].
  destruct (kread8e SEGS (kn cs) (ELit 0) (c_lla T + 8)) as [cur|] eqn:Kcur; [|discriminate].
  destruct (kreadZ SEGS (kn cs) (ELit 0) (c_statics T + 8) 8) as [size|] eqn:Ksize; [|discriminate].
  destruct (kread8e SEGS (kn cs) (ELit 0) (c_statics T + 16)) as [first|] eqn:Kfirst; [|discriminate].
  destruct (if 0 <? nind ds then read_map SEGS T (kn cs) else Some (ELit 0, 0, 0, [])) as [[[[B N] ne] ks]|] eqn:Hrm; [|discriminate].
  destruct (run y N ds ks ne) as [[ks' ne']|] eqn:Hrun; [|discriminate].
  destruct (gsh_extra T HULLS (kn cs) ds rest) as [extra|] eqn:Hex; [|discriminate].
  rewrite (surjective_pairing (split_lit cur)) in Hn. rewrite (surjective_pairing (split_lit B)) in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  match type of Hn with Some (with_ss cs (mk_ss _ ?sr ?kf _)) = _ => remember sr as srF eqn:HsrF; remember kf as kF eqn:HkF end.
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Gmap]. apply andb_prop in Hc as [Hc Glist]. apply andb_prop in Hc as [Hc Glla]. apply andb_prop in Hc as [Hc Gsh].
  apply andb_prop in Hc as [Hc Gfr]. apply andb_prop in Hc as [Hc Gco]. apply andb_prop in Hc as [Hc Gtab]. apply andb_prop in Hc as [Hc Greg].
  apply andb_prop in Hc as [Hc Gvcur]. apply andb_prop in Hc as [Hfresh Gro].
  (* [comment removed for export] *)
  destruct (chk_regs_sound E cs R FULL model HC Greg) as (G9 & G20 & G21 & G24 & G25).
  destruct (chk_tab_sound E M (kn cs) i kz n ds N ks ne _ HKN Gtab Hscan Hrun) as (Hlen & Hkz & Hi0 & Hin & Hte & Ht0 & Ht1 & Hdesc & Hnd & Hind & Hodrw & Ho1 & Ho2 & Ho0).
  destruct (chk_consts_sound E M (kn cs) HKN Gco) as (Cin & Win & Cf24 & Cf85 & Cf100 & Csh & Ccp & Cms & Cal & HB).
  apply Forall_cons_iff in HB as [Bin HB]. apply Forall_cons_iff in HB as [Bfl HB]. apply Forall_cons_iff in HB as [Bsh HB].
  apply Forall_cons_iff in HB as [Bcp HB]. apply Forall_cons_iff in HB as [Bms HB]. apply Forall_cons_iff in HB as [Bal HB].
  apply Forall_cons_iff in HB as [Bla HB]. apply Forall_cons_iff in HB as [Bstc HB]. apply Forall_cons_iff in HB as [Bmp _].
  pose proof HULL_ok as (HU0 & _ & _ & HU3). unfold KHI in HU3.
  assert (Ala : 0 <= c_lla T /\ c_lla T + 128 <= 2 ^ 47) by (clear - Bla HU0 HU3; lia).
  assert (Ast : 0 <= c_statics T /\ c_statics T + 128 <= 2 ^ 47) by (clear - Bstc HU0 HU3; lia).
  assert (Amp : 0 <= c_map T /\ c_map T + 128 <= 2 ^ 47) by (clear - Bmp HU0 HU3; lia).
  destruct (chk_frame_sound E M (kn cs) fp sp n HKN Gfr) as (Esp & Cn & Cmp & Rks & Rfr & Hfp16 & Hsp1 & Hsp2 & Hfp & Koff & Soff & Kst & Sst).
  fold ek es in Kst, Sst. set (fpz := bv_unsigned (edenot E fp)) in *.
  destruct (chk_shadow_sound E M (kn cs) ds HKN Gsh) as (Rshw & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Elo & Ehi).
  assert (Hnin0 : 0 <= nind ds) by (unfold nind; lia).
  set (na := kz + nind ds) in *.
  assert (Hna : 1 <= na <= 2 ^ 22) by (unfold na, nind in *; pose proof (filter_length_le is_ind ds) as FL; clear - FL Hkz Hlen; lia).
  assert (Asw : 0 <= shad y (l_ilo y) /\ shad y (l_ilo y) < shad y (l_ihi y) < 2 ^ 47) by (clear - Hs4 Hs5 HU0 HULL_le; lia).
  destruct (chk_lla_sound E M (kn cs) cur lend _ _ na fpz HKN Glla Klend Kcur Sst Hna (proj1 Ala) (proj2 Ala) (proj1 Asw) (proj2 Asw))
    as (Clend & Ccur & Wlla & Hcur0 & Hroom & Hlend & Rlla & Hlla1 & Hlla2 & Hlla3 & Cst & Hlla4).
  set (curz := bv_unsigned (edenot E cur)) in *. set (lendz := bv_unsigned (edenot E lend)) in *.
  destruct (chk_list_sound E M (kn cs) size kz first HKN Glist Ksize Kfirst (proj1 Ast) (proj2 Ast)) as (Csize & Cfirst & Wlist & Hsz1 & Hsz2 & Hlist4).
  rewrite <- (LBNS.W_u (edenot E first)) in Cfirst.
  set (Bz := bv_unsigned (edenot E B)) in *.
  assert (Hmap : 0 < nind ds -> RGK.kmap_pre SEGS T M Bz N ne ks curz na fpz
                               /\ estart E (SA (fst (split_lit B)) (snd (split_lit B))) = Bz /\ (Bz + 32 * N <= img_lo A \/ img_hi A <= Bz)
                               /\ AP.expr_vars_lt (nxt cs) B = true /\ (c_map T + 12 <= l_odr_lo y \/ l_odr_hi y <= c_map T + 8)).
  { intros Hpos. apply Z.ltb_lt in Hpos. rewrite Hpos in Hrm, Gmap. cbn [negb orb] in Gmap.
    exact (chk_map_sound E M cs (kn cs) B N ne ks _ _ _ _ na curz fpz HKN Gmap Hrm Cst Sst Hna (proj1 Amp) (proj2 Amp) (proj1 Ast) (proj2 Ast) (proj1 Asw) (proj2 Asw) Elo Ehi). }
  (* [comment removed for export] *)
  assert (Rg : forall r, (0 < r < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat r)) = edenot E (reg cs r)) by (intros r Hr; exact (reg_get E cs R FULL model r HC Hr)).
  assert (G27 : getr R 27%bv = W i) by (change (getr R 27%bv) with (getr R (Z_to_bv 5 (Z.of_nat 27))); rewrite (Rg 27%nat) by (clear; lia); exact (RHNS.lit1_w E _ _ L27)).
  assert (G8 : getr R 8%bv = W fpz) by (change (getr R 8%bv) with (getr R (Z_to_bv 5 (Z.of_nat 8))); rewrite (Rg 8%nat) by (clear; lia); unfold fpz, fp; symmetry; apply LBNS.W_u).
  assert (G2 : getr R 2%bv = W (fpz - 0x10f0)) by (change (getr R 2%bv) with (getr R (Z_to_bv 5 (Z.of_nat 2))); rewrite (Rg 2%nat) by (clear; lia); rewrite <- Esp; unfold sp; symmetry; apply LBNS.W_u).
  (* [comment removed for export] *)
  assert (RO : forall sg, In sg SEGS -> seg_writable sg = false -> forall z, Z.of_N (seg_base sg) <= z < Z.of_N (seg_base sg) + Z.of_N (seg_size sg) -> M (W z) = None).
  { intros sg Hsg Hw z Hz. unfold RHN.ro_cov in Gro. rewrite forallb_forall in Gro. specialize (Gro sg Hsg). rewrite Hw in Gro. cbn [orb] in Gro.
    exact (img_cov_sound SEGS E M (kn cs) _ _ HKN Gro z Hz). }
  (* [comment removed for export] *)
  rewrite <- Hlen in Hkz, Hin, Hdesc. 
  assert (Hmap' : 0 < nind ds -> RGK.kmap_pre SEGS T M Bz N ne ks curz (Z.of_nat (length ds) + nind ds) fpz) by (intros Hp; rewrite Hlen; exact (proj1 (Hmap Hp))).
  rewrite <- Elo in Hlla1. rewrite <- Ehi in Hlla1.
  destruct (RGC R M i n ds N ne ks ks' ne' Bz curz lendz size (bv_unsigned (edenot E first)) fpz G27 G8 G2 G9 G20 G21 G24 G25 Hrun
              ltac:(clear - Hkz; lia) Hi0 Hin Hte Ht0 Ht1 Hdesc Hnd Hind Hodrw Cin Win Cf24 Cf85 Cf100 Csh Ccp Cms Cal Cn Cmp Rks Rfr Hfp16 Hsp1 Hsp2 Hfp Rshw
              Clend Ccur Wlla Hcur0 ltac:(rewrite Hlen; exact Hroom) Hlend ltac:(rewrite Hlen; exact Rlla) ltac:(rewrite Hlen; exact Hlla1)
              ltac:(rewrite Hlen; exact Hlla2) ltac:(rewrite Hlen; exact Hlla3) Csize Cfirst Wlist Hsz1 ltac:(clear - Hsz2 Hkz Hlen; lia) Hmap' RO)
    as (regs' & M' & Hms & Kkept & K27 & Kcur' & Ksize' & Kfirst' & Kmap' & Hfr & Hg & Hgsh).
  rewrite Hlen in K27, Kcur', Ksize', Kfirst', Hfr. fold na in Kcur', Kfirst', Hfr.
  (* [comment removed for export] *)
  set (nx := nxt cs) in *.
  set (R2 := regupd regs' 27%bv (getr R 27%bv)).
  set (E' := LBNS.ext_regs E nx rg_fresh R2).
  pose proof (LBNS.ext_regs_agree E nx rg_fresh R2) as Hag. fold E' in Hag.
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle). fold nx in Fsr, Fkn, Fle.
  assert (Ag : forall e, expr_vars_lt nx e = true -> edenot E' e = edenot E e).
  { intros e He. symmetry. apply (edenot_agree' nx); assumption. }
  assert (AgS : forall e o, expr_vars_lt nx e = true -> estart E' (SA e o) = estart E (SA e o)).
  { intros e o He. unfold estart. cbn [a_base a_off]. rewrite (Ag e He). reflexivity. }
  assert (Vreg : forall r, (r < 32)%nat -> expr_vars_lt nx (reg cs r) = true) by (intros r Hr; apply nth_sr_vars_lt'; assumption).
  pose proof (know_ok_agree' SEGS nx E E' M (kn cs) Hag Fkn HKN) as HKN'.
  assert (Efp' : bv_unsigned (edenot E' fp) = fpz) by (unfold fp; rewrite (Ag _ (Vreg 8%nat ltac:(clear; lia))); reflexivity).
  destruct (chk_frame_sound E' M (kn cs) fp sp n HKN' Gfr) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kst' & Sst').
  fold ek es in Kst', Sst'. rewrite Efp' in Kst', Sst'.
  assert (Vcb : expr_vars_lt nx (fst (split_lit cur)) = true) by exact (split_lit_vars cur _ _ nx (surjective_pairing _) Gvcur).
  assert (Cst' : estart E' (SA (fst (split_lit cur)) (snd (split_lit cur))) = curz) by (rewrite (AgS _ _ Vcb); exact Cst).
  eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH ISP argH_high NX0_spw argH_agree SINV_frame SINV_agree FS0
            cs E E' R FULL model TT (c_entry T) srF kF (nx + NRG)%nat regs' M' HC Hfresh Hag).
  - rewrite Hpc0. exact Hms.
  - (* [comment removed for export] *)
    rewrite HsrF.
    assert (N27 : (27%bv : bv 5) <> 0%bv) by (intros Y; discriminate Y).
    assert (HR2 : regs_ok E' (sr_fresh (s_regs (a_ss cs)) rg_fresh nx) R2).
    { apply (LBNS.regs_after_region E (s_regs (a_ss cs)) R R2 nx rg_fresh (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) Fsr rg_fresh_nodup).
      intros r Hr0 Hnin. unfold R2. destruct (Nat.eq_dec (ridx r) 27) as [E27|N27'].
      - assert (r = 27%bv) by (apply bv_eq; unfold ridx in E27; pose proof (bv_unsigned_in_range 5 r) as Hb; change (bv_unsigned (27%bv : bv 5)) with 27; clear - E27 Hb; lia).
        subst r. apply getr_same. exact N27.
      - rewrite getr_other by (intros ->; apply N27'; reflexivity). exact (Kkept r Hnin N27'). }
    pose proof (regs_ok_upd E' _ R2 27%bv (W (i + kz)) (ELit (i + kz)) HR2 eq_refl) as HR3.
    change (bv_eqb (27%bv : bv 5) 0) with false in HR3. cbv iota in HR3. change (ridx 27%bv) with 27%nat in HR3.
    intros r. rewrite <- (HR3 r). unfold R2.
    destruct (Nat.eq_dec (ridx r) 27) as [E27|N27'].
    + assert (r = 27%bv) by (apply bv_eq; unfold ridx in E27; pose proof (bv_unsigned_in_range 5 r) as Hb; change (bv_unsigned (27%bv : bv 5)) with 27; clear - E27 Hb; lia).
      subst r. rewrite getr_same by exact N27. exact K27.
    + rewrite !getr_other by (intros ->; apply N27'; reflexivity). reflexivity.
  - (* [comment removed for export] *)
    rewrite HkF.
    assert (Ecur' : forall z, edenot E' (eaddz cur z) = W (curz + z)) by (intros z; rewrite w_eaddz, (Ag cur Gvcur); reflexivity).
    apply Forall_app. split.
    { (* [comment removed for export] *)
      pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as HSI.
      assert (Hi_nat : Z.of_nat (Z.to_nat i) = i) by (apply Z2Nat.id; exact Hi0).
      apply (gsh_extra_sound E E' M M' (kn cs) ds rest extra (Z.to_nat i) HKN Hex).
      - assert (Hkn : Z.to_nat kz = length ds) by (rewrite <- Hlen; apply Nat2Z.id). rewrite Hi_nat, <- Hkn. exact Hscan.
      - clear - Hin Hte HTABN Hi0 Hkz. lia.
      - clear - Hs1 Hs4 HU0 HULL_le Elo. lia.
      - exact Hs2.
      - clear - Hs3 Hs5. lia.
      - intros j lo hi Hj. rewrite <- (proj2 Hag). exact (HBLOB E FULL HSI j lo hi Hj).
      - exact Hgsh. }
    constructor; [| constructor; [| constructor; [| apply Forall_app; split; [| apply Forall_app; split]]]].
    + apply (kword_intro SEGS E' M' (ELit 0) (c_lla T + 8) 8 _ (c_lla T + 8) (W (curz + 16 * na)));
        [clear; lia | apply lit_start; clear - Ala; lia | clear - Ala; lia | clear - Ala; lia | clear - Ala; lia | exact Kcur' | apply Ecur'].
    + apply (kword_intro SEGS E' M' (ELit 0) (c_statics T + 8) 8 _ (c_statics T + 8) (W (size + kz)));
        [clear; lia | apply lit_start; clear - Ast; lia | clear - Ast; lia | clear - Ast; lia | clear - Ast; lia | exact Ksize' | reflexivity].
    + replace (curz + 16 * na - 16) with (curz + (16 * na - 16)) in Kfirst' by (clear; lia).
      apply (kword_intro SEGS E' M' (ELit 0) (c_statics T + 16) 8 _ (c_statics T + 16) (W (curz + (16 * na - 16))));
        [clear; lia | apply lit_start; clear - Ast; lia | clear - Ast; lia | clear - Ast; lia | clear - Ast; lia | exact Kfirst' | apply Ecur'].
    + (* [comment removed for export] *)
      destruct (0 <? nind ds) eqn:Hpos; [| constructor]. apply Z.ltb_lt in Hpos.
      destruct (Hmap Hpos) as (KP & Bst & Boff & VB & _). destruct (Kmap' Hpos) as [Kne' Kkeys'].
      destruct KP as (_ & _ & _ & _ & _ & _ & _ & HN & _ & HlenK & _ & _ & _ & B0 & BT & _).
      assert (Vnb : expr_vars_lt nx (fst (split_lit B)) = true) by exact (split_lit_vars B _ _ nx (surjective_pairing _) VB).
      pose proof (run_length _ _ _ _ _ _ _ Hrun) as HlenK'.
      constructor.
      * apply (kword_intro SEGS E' M' (ELit 0) (c_map T + 8) 4 _ (c_map T + 8) (W ne'));
          [clear; lia | apply lit_start; clear - Amp; lia | clear - Amp; lia | clear - Amp; lia | clear - Amp; lia | exact Kne' | reflexivity].
      * replace (snd (split_lit B)) with (snd (split_lit B) + 0) by (clear; lia).
        apply (RHNS.key_facts_ok SEGS E' M' (fst (split_lit B)) (snd (split_lit B)) Bz ltac:(rewrite (AgS _ _ Vnb); exact Bst) ltac:(clear - B0; lia) ks' 0 ltac:(clear; lia)).
        -- rewrite HlenK'. clear - HlenK BT. lia.
        -- intros b Hb. rewrite Z.add_0_r. apply Kkeys'. rewrite HlenK' in Hb. clear - Hb HlenK. lia.
    + (* [comment removed for export] *)
      apply (gap_facts_ok E E' M M' (kn cs) (inds ds) (l_odr_lo y) (l_odr_hi y) (ind_lo ds) (ind_hi ds) HKN Ho0 ltac:(clear - Ho2 HU3; lia)).
      intros z Hz Hnin. apply Hfr. unfold RGK.rg_FP, LBNS.inr. rewrite LBNS.u_W by (clear - Hz Ho0 Ho2 HU3; lia).
      intros [F|[F|[F|[F|[F|[F|[F|[Hm [F|F]]]]]]]]]; try (clear - F Hz Ho1 Ho2 Koff Soff Hs1 Hs4 Hlist4 Hlla4 Hlla1 Elo Ehi; lia).
      * exact (Hnin F).
      * apply Z.ltb_lt in Hm. destruct (Hmap Hm) as (_ & _ & _ & _ & Hm4). clear - F Hz Hm4. lia.
      * apply Z.ltb_lt in Hm. destruct (Hmap Hm) as (_ & _ & Boff & _). clear - F Hz Boff Ho1 Ho2. lia.
    + (* [comment removed for export] *)
      apply (RHNS.havs_sound SEGS E' M M' _ (kn cs)); [| exact Hg | exact HKN' |].
      { apply Forall_app. split; [repeat constructor; cbn [snd]; clear - Hs1 Hs2 Hs3 Hs4 Hs5 Hna HU0 HULL_le; lia|].
        destruct (0 <? nind ds) eqn:Hpos; [| constructor]. apply Z.ltb_lt in Hpos.
        destruct (Hmap Hpos) as (KP & _). destruct KP as (_ & _ & _ & _ & _ & _ & _ & HN & _).
        assert (Hih : 0 <= ind_hi ds - ind_lo ds < 2 ^ 64).
        { assert (Hne : inds ds <> []) by (intros Ei; unfold nind, inds in *; apply map_eq_nil in Ei; rewrite Ei in Hpos; cbn in Hpos; lia).
          pose proof (ind_hull_window y ds (run_ok _ _ _ _ _ _ Hrun) Hne) as IW. clear - IW Ho0 Ho2 HU3. lia. }
        constructor; [cbn [snd]; exact Hih|]. constructor; [cbn [snd]; clear; lia|]. constructor; [cbn [snd]; clear - HN; lia|]. constructor. }
      intros x Hx. apply Hfr. apply in_rs_false in Hx. apply Forall_app in Hx as [Hx0 Hx1].
      apply Forall_cons_iff in Hx0 as [Y1 Hx0]. apply Forall_cons_iff in Hx0 as [Y2 Hx0]. apply Forall_cons_iff in Hx0 as [Y3 Hx0].
      apply Forall_cons_iff in Hx0 as [Y4 Hx0]. apply Forall_cons_iff in Hx0 as [Y5 Hx0]. apply Forall_cons_iff in Hx0 as [Y6 _].
      cbn [fst snd] in Y1, Y2, Y3, Y4, Y5, Y6.
      rewrite Kst' in Y1. rewrite Sst' in Y2. rewrite (lit_start E' (run_sh_lo y ds) ltac:(clear - Hs1 Hs2 Hs3 Hs4 Hs5 HU0 HULL_le; lia)) in Y3.
      rewrite (lit_start E' (c_statics T + 8) ltac:(clear - Ast; lia)) in Y4.
      rewrite (lit_start E' (c_lla T + 8) ltac:(clear - Ala; lia)) in Y5. rewrite Cst' in Y6.
      unfold RGK.rg_FP. intros [F|[F|[F|[F|[F|[F|[F|[Hm [F|F]]]]]]]]].
      * exact (Y1 F).
      * exact (Y2 F).
      * exact (Y3 F).
      * exact (Y4 F).
      * exact (Y5 F).
      * exact (Y6 F).
      * destruct (0 <? nind ds) eqn:Hpos.
        -- apply Forall_cons_iff in Hx1 as [Z1 _]. cbn [fst snd] in Z1.
           pose proof (ind_hull ds) as IH. rewrite Forall_forall in IH. specialize (IH _ F).
           pose proof (inds_window y ds (run_ok _ _ _ _ _ _ Hrun) _ F) as Bw.
           assert (Hil : 0 <= ind_lo ds < 2 ^ 64).
           { assert (Hne : inds ds <> []) by (intros Ei; rewrite Ei in F; destruct F).
             pose proof (ind_hull_window y ds (run_ok _ _ _ _ _ _ Hrun) Hne) as IW. clear - IW Ho0 Ho2 HU3. lia. }
           rewrite (lit_start E' (ind_lo ds) Hil) in Z1. apply Z1. unfold LBNS.inr. clear - IH. lia.
        -- apply Z.ltb_ge in Hpos. unfold nind, inds in *. destruct (List.filter is_ind ds); [destruct F | cbn [length] in Hpos; lia].
      * rewrite Hm in Hx1. apply Forall_cons_iff in Hx1 as [_ Hx1]. apply Forall_cons_iff in Hx1 as [Z2 _]. cbn [fst snd] in Z2.
        rewrite (lit_start E' (c_map T + 8) ltac:(clear - Amp; lia)) in Z2. exact (Z2 F).
      * rewrite Hm in Hx1. apply Forall_cons_iff in Hx1 as [_ Hx1]. apply Forall_cons_iff in Hx1 as [_ Hx1]. apply Forall_cons_iff in Hx1 as [Z3 _].
        cbn [fst snd] in Z3. apply Z.ltb_lt in Hm. destruct (Hmap Hm) as (_ & Bst & _ & VB & _).
        assert (Vnb : expr_vars_lt nx (fst (split_lit B)) = true) by exact (split_lit_vars B _ _ nx (surjective_pairing _) VB).
        rewrite (AgS _ _ Vnb), Bst in Z3. exact (Z3 F).
  - intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
    split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

End Sound.
End RGNS.
