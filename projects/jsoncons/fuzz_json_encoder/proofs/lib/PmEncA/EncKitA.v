(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5 CutHeapA CutL5A.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module EKA.
Import PMES.
Abbreviation mem := (word -> option byte).
Abbreviation agree := (L5C.agree_on).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kv_s2_pos : forall rep, 1 <= kv_s2 rep.
Proof. intros [s|cap p s]; cbn [kv_s2]; [lia | pose proof (Z.log2_nonneg (2 ^ 47 / cap)); lia]. Qed.
Lemma kv_st_nonneg : forall capb, 0 <= kv_st capb.
Proof. intros capb. unfold kv_st. destruct (capb =? 0); [lia | apply Z.log2_nonneg]. Qed.
Lemma grow_cap_ge : forall cap n, 8 <= cap -> cap mod 8 = 0 -> 0 <= n -> 2 * cap <= PML.grow_cap cap n /\ n < PML.grow_cap cap n /\ PML.grow_cap cap n mod 8 = 0.
Proof.
  intros cap n H0 H8 Hn. unfold PML.grow_cap. set (m := Z.max n (2 * (cap - 1))).
  assert (Hm : 2 * cap - 2 <= m /\ n <= m) by (unfold m; lia).
  rewrite CL5.lor7 by lia. pose proof (Z.div_mod m 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound m 8 ltac:(lia)) as B.
  assert (Hq : (2 * cap - 2) / 8 <= m / 8) by (apply Z.div_le_mono; lia).
  assert (Hc8 : (2 * cap - 2) / 8 = cap / 4 - 1).
  { pose proof (Z.div_mod cap 8 ltac:(lia)) as Dc. rewrite H8 in Dc. set (q := cap / 8) in *.
    replace (2 * cap - 2) with (6 + (2 * q - 1) * 8) by lia. rewrite Z.div_add by lia. replace cap with (0 + (2 * q) * 4) by lia. rewrite Z.div_add by lia. reflexivity. }
  assert (Hc4 : 4 * (cap / 4) = cap).
  { pose proof (Z.div_mod cap 8 ltac:(lia)) as Dc. rewrite H8 in Dc. set (q := cap / 8) in *. replace cap with (0 + (2 * q) * 4) by lia. rewrite Z.div_add by lia. change (0 / 4) with 0. lia. }
  split; [lia|]. split; [lia|].
  replace (8 * (m / 8) + 7 + 1) with (0 + (m / 8 + 1) * 8) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma grow_cap_short : forall n, 0 <= n -> 48 <= PML.grow_cap 23 n /\ n < PML.grow_cap 23 n /\ PML.grow_cap 23 n mod 8 = 0.
Proof.
  intros n Hn. unfold PML.grow_cap. set (m := Z.max n (2 * (23 - 1))). assert (Hm : 44 <= m /\ n <= m) by (unfold m; lia).
  rewrite CL5.lor7 by lia. pose proof (Z.div_mod m 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound m 8 ltac:(lia)) as B.
  assert (Hq : 44 / 8 <= m / 8) by (apply Z.div_le_mono; lia). change (44 / 8) with 5 in Hq.
  split; [lia|]. split; [lia|].
  replace (8 * (m / 8) + 7 + 1) with (0 + (m / 8 + 1) * 8) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma grow_cap_le : forall cap n, 1 <= cap -> 0 <= n -> PML.grow_cap cap n <= Z.max n (2 * (cap - 1)) + 8.
Proof.
  intros cap n Hc Hn. unfold PML.grow_cap. set (m := Z.max n (2 * (cap - 1))). assert (Hm : 0 <= m) by (unfold m; lia).
  rewrite CL5.lor7 by lia. pose proof (Z.mul_div_le m 8 ltac:(lia)). lia.
Qed.
Lemma log2_halves47 : forall cap c, 0 < cap -> 2 * cap <= c -> c <= 2 ^ 47 -> Z.log2 (2 ^ 47 / c) + 1 <= Z.log2 (2 ^ 47 / cap).
Proof.
  intros cap c H24 H2 Hc.
  assert (A : 2 ^ 47 / c <= 2 ^ 47 / (2 * cap)) by (apply Z.div_le_compat_l; lia).
  assert (B : 2 ^ 47 / (2 * cap) = 2 ^ 47 / cap / 2) by (rewrite Z.div_div by lia; f_equal; lia).
  assert (C : 2 <= 2 ^ 47 / cap) by (apply Z.div_le_lower_bound; lia).
  pose proof (Z.log2_le_mono _ _ A) as M. rewrite B in M. set (x := 2 ^ 47 / cap) in *.
  assert (Y : 1 <= x / 2) by (apply Z.div_le_lower_bound; lia).
  pose proof (Z.log2_double (x / 2) ltac:(lia)) as Dd. pose proof (Z.mul_div_le x 2 ltac:(lia)) as Le.
  pose proof (Z.log2_le_mono _ _ Le) as M2. lia.
Qed.
Lemma log2_48 : forall c, 48 <= c -> Z.log2 (2 ^ 47 / c) <= 41.
Proof.
  intros c Hc. assert (A : 2 ^ 47 / c <= 2 ^ 47 / 48) by (apply Z.div_le_compat_l; lia).
  pose proof (Z.log2_le_mono _ _ A) as M. change (Z.log2 (2 ^ 47 / 48)) with 41 in M. exact M.
Qed.
(* [comment removed for export] *)
Definition rep_shape (rep : PML.srep) : Prop := match rep with PML.SShort _ => True | PML.SLong cap _ _ => 48 <= cap /\ cap mod 8 = 0 end.
Lemma rep_shape_of_sink : forall L M o rep, PMESA.sink_atA L M o rep -> rep_shape rep.
Proof. intros L M o [s|cap p s] (H1 & _ & H3 & _); cbn [rep_shape PMES.rep_ok PMSA.str_at PMLA.str_at] in *; [exact I|]. destruct H1 as (_ & H8 & _). lia. Qed.
(* [comment removed for export] *)
Lemma grow_facts : forall rep need, rep_shape rep -> ~ fits rep need -> 0 <= need ->
  let a := alloc_of rep in let c' := PML.grow_cap a need in 2 * a <= c' /\ need < c' /\ c' mod 8 = 0 /\ a <= need /\ c' <= 2 * need + 8 /\ 48 <= c'.
Proof.
  intros [s|cap p s] need Hsh Hnf Hn; cbn [alloc_of fits rep_shape] in *.
  - destruct (grow_cap_short need Hn) as (G1 & G2 & G3). pose proof (grow_cap_le 23 need ltac:(lia) Hn). repeat split; lia.
  - destruct Hsh as [H8 Hm]. destruct (grow_cap_ge cap need ltac:(lia) Hm Hn) as (G1 & G2 & G3). pose proof (grow_cap_le cap need ltac:(lia) Hn).
    assert (cap <= need) by lia. repeat split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithL.
Variable L : asan_layout.
Variable CL : Z.
Variable onmax : Z.
Hypothesis KPM : 0 <= hl_k_per_malloc L.
Hypothesis BLIN : 0 <= hl_b_lin L.
Hypothesis BOV : 0 <= hl_b_overhead L.

Lemma kenc_nonneg : forall eg, 0 <= PMESA.kenc L eg.
Proof. intros eg. unfold PMESA.kenc. pose proof (kv_s2_pos (g_rep eg)). pose proof (kv_st_nonneg (g_scap eg)). nia. Qed.
Lemma bpot_s2_nonneg : forall rep, 0 <= PMESA.bpot_s2 L CL rep.
Proof. intros rep. unfold PMESA.bpot_s2. pose proof (kv_s2_pos rep). pose proof (Z.le_max_l 0 (4 * CL + 16 - 2 * alloc_of rep)). nia. Qed.
Lemma bpot_st_nonneg : forall capb, 0 <= PMESA.bpot_st L capb.
Proof. intros capb. unfold PMESA.bpot_st. pose proof (kv_st_nonneg capb). pose proof (Z.le_max_l 0 (65536 - 2 * capb)). nia. Qed.
(* [comment removed for export] *)
Lemma benc_nonneg : forall eg, 0 <= PMESA.benc L CL eg.
Proof. intros eg. unfold PMESA.benc. pose proof (bpot_s2_nonneg (g_rep eg)). pose proof (bpot_st_nonneg (g_scap eg)). lia. Qed.

(* [comment removed for export] *)
Lemma bpot_s2_grow : forall rep need p', rep_shape rep -> ~ fits rep need -> 0 <= need -> need <= CL ->
  let c' := PML.grow_cap (alloc_of rep) need in
  PML.grow_cap (alloc_of rep) need <= 2 ^ 47 ->
  PMESA.bpot_s2 L CL (PML.SLong c' p' (repeat 0 (Z.to_nat need))) + (hl_b_lin L * c' + hl_b_overhead L) <= PMESA.bpot_s2 L CL rep /\
  (kv_s2 (PML.SLong c' p' []) + 1) * hl_k_per_malloc L <= kv_s2 rep * hl_k_per_malloc L.
Proof.
  intros rep need p' Hsh Hnf Hn Hcl c' Hc. pose proof (grow_facts rep need Hsh Hnf Hn) as GF. cbv zeta in GF. fold c' in GF, Hc |- *.
  destruct GF as (G1 & G2 & G3 & G4 & G5 & G6).
  assert (KV : kv_s2 (PML.SLong c' p' []) + 1 <= kv_s2 rep).
  { destruct rep as [s|cap p s]; cbn [kv_s2 alloc_of] in *.
    - pose proof (log2_48 c' G6). lia.
    - destruct Hsh as [H8 Hm]. pose proof (log2_halves47 cap c' ltac:(lia) G1 Hc). lia. }
  split; [|nia].
  unfold PMESA.bpot_s2. cbn [kv_s2 alloc_of]. cbn [kv_s2] in KV.
  rewrite (Z.max_r 0 (4 * CL + 16 - 2 * c')) by lia. rewrite (Z.max_r 0 (4 * CL + 16 - 2 * alloc_of rep)) by lia.
  nia.
Qed.

(* [comment removed for export] *)
Definition clok : Prop := 8 <= CL /\ 2 * CL + 8 <= onmax /\ 32768 <= onmax /\ onmax <= 2 ^ 47.
Lemma scredit_grow_ok : forall cr rep kx bx need, clok -> PMESA.screditA L CL cr rep kx bx -> rep_shape rep -> 0 <= need -> need <= CL -> ~ fits rep need ->
  acredit_ok L cr (PML.grow_cap (alloc_of rep) need) /\ PML.grow_cap (alloc_of rep) need <= onmax.
Proof.
  intros cr rep kx bx need (C1 & C2 & C3 & C4) (S0 & S1 & S2 & S3) Hsh Hn Hcl Hnf.
  pose proof (grow_facts rep need Hsh Hnf Hn) as GF. cbv zeta in GF. destruct GF as (G1 & G2 & G3 & G4 & G5 & G6).
  assert (Hc : PML.grow_cap (alloc_of rep) need <= 2 ^ 47) by lia.
  destruct (bpot_s2_grow rep need 0 Hsh Hnf Hn Hcl Hc) as [B K]. cbn [kv_s2] in K.
  pose proof (bpot_s2_nonneg (PML.SLong (PML.grow_cap (alloc_of rep) need) 0 (repeat 0 (Z.to_nat need)))) as NN.
  pose proof (Z.log2_nonneg (2 ^ 47 / PML.grow_cap (alloc_of rep) need)) as LN.
  split; [|lia]. unfold acredit_ok. split; nia.
Qed.

(* [comment removed for export] *)
Lemma grown_scredit_same : forall cr rep s' kx bx,
  PMESA.screditA L CL cr rep kx bx -> PMESA.screditA L CL cr (same_rep rep s') kx bx.
Proof. intros cr [s|cap p s] s' kx bx H; exact H. Qed.
Lemma grown_scredit_grow : forall cr rep need p' s' kx bx, rep_shape rep -> ~ fits rep need -> 0 <= need -> need <= CL ->
  PML.grow_cap (alloc_of rep) need <= 2 ^ 47 ->
  PMESA.screditA L CL cr rep kx bx -> PMESA.screditA L CL (adebit L cr (PML.grow_cap (alloc_of rep) need)) (PML.SLong (PML.grow_cap (alloc_of rep) need) p' s') kx bx.
Proof.
  intros cr rep need p' s' kx bx Hsh Hnf Hn Hcl Hc (S0 & S1 & S2 & S3).
  destruct (bpot_s2_grow rep need p' Hsh Hnf Hn Hcl Hc) as [B K].
  unfold PMESA.screditA, adebit. cbn [fst snd]. unfold PMESA.bpot_s2 in *. cbn [kv_s2 alloc_of] in *.
  repeat split; [exact S0 | nia | exact S2 | nia].
Qed.
(* [comment removed for export] *)
Lemma scredit_of_ecredit : forall cr g kx bx, PMESA.ecreditA L CL cr g kx bx ->
  PMESA.screditA L CL cr (g_rep g) (kx + kv_st (g_scap g) * hl_k_per_malloc L) (bx + PMESA.bpot_st L (g_scap g)).
Proof.
  intros cr g kx bx (H0 & H1 & H2 & H3). unfold PMESA.ecreditA, PMESA.kenc, PMESA.benc, PMESA.screditA in *.
  pose proof (kv_st_nonneg (g_scap g)). pose proof (bpot_st_nonneg (g_scap g)). repeat split; nia.
Qed.
Lemma ecredit_of_scredit : forall cr g kx bx rep' g', g_rep g' = rep' -> g_scap g' = g_scap g ->
  PMESA.screditA L CL cr rep' (kx + kv_st (g_scap g) * hl_k_per_malloc L) (bx + PMESA.bpot_st L (g_scap g)) -> 0 <= kx -> 0 <= bx ->
  PMESA.ecreditA L CL cr g' kx bx.
Proof.
  intros cr g kx bx rep' g' E1 E2 (H0 & H1 & H2 & H3) Hk Hb. unfold PMESA.ecreditA, PMESA.kenc, PMESA.benc, PMESA.screditA in *. rewrite E1, E2.
  repeat split; [exact Hk | nia | exact Hb | nia].
Qed.
End WithL.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lb_remove_notin : forall A (LB : list (Z * Z)), ~ In A (map fst LB) -> lb_remove A LB = LB.
Proof.
  intros A LB. induction LB as [|b r IH]; intros H; [reflexivity|]. cbn [lb_remove]. cbn [map In] in H.
  destruct (Z.eqb_spec (fst b) A) as [E|E]; [exfalso; apply H; left; exact E|]. f_equal. apply IH. intros X. apply H. right. exact X.
Qed.
Lemma lb_remove_app : forall A (l1 l2 : list (Z * Z)), ~ In A (map fst l1) -> lb_remove A (l1 ++ l2) = l1 ++ lb_remove A l2.
Proof.
  intros A l1 l2. induction l1 as [|b r IH]; intros H; [reflexivity|]. cbn [app lb_remove]. cbn [map In] in H.
  destruct (Z.eqb_spec (fst b) A) as [E|E]; [exfalso; apply H; left; exact E|]. f_equal. apply IH. intros X. apply H. right. exact X.
Qed.
Lemma nodup_app_l : forall (l1 l2 : list Z) a, List.NoDup (l1 ++ l2) -> In a l2 -> ~ In a l1.
Proof.
  intros l1 l2 a. induction l1 as [|x r IH]; intros H Ha X; [destruct X|]. cbn [app] in H. inversion H as [|? ? N1 N2]; subst.
  destruct X as [->|X]; [apply N1; apply in_or_app; right; exact Ha | exact (IH N2 Ha X)].
Qed.
Lemma nodup_app_l' : forall (l1 l2 : list Z) a, base.NoDup (l1 ++ l2) -> In a l2 -> ~ In a l1.
Proof. intros l1 l2 a H. apply base.NoDup_ListNoDup in H. exact (nodup_app_l l1 l2 a H). Qed.
Lemma drop_lbv : forall LBo rep sb scap, List.NoDup (map fst (LBo ++ PML.srep_blocks rep ++ stack_blocks sb scap)) ->
  lb_drop rep (LBo ++ PML.srep_blocks rep ++ stack_blocks sb scap) = LBo ++ stack_blocks sb scap.
Proof.
  intros LBo rep sb scap ND. destruct rep as [s|cap p s]; cbn [lb_drop PML.srep_blocks app] in *; [reflexivity|].
  rewrite lb_remove_app.
  - cbn [lb_remove fst]. rewrite Z.eqb_refl. reflexivity.
  - rewrite map_app in ND. apply (nodup_app_l _ _ p ND). cbn [map fst In]. left. reflexivity.
Qed.
Lemma perm_lbv_in : forall (LBo st : list (Z * Z)) b, Permutation (b :: LBo ++ st) (LBo ++ b :: st).
Proof. intros. apply Permutation_middle. Qed.
Lemma rep_live_lbv : forall LBo g, rep_live (g_rep g) (LBo ++ g_lbv g).
Proof. intros LBo g. unfold g_lbv. destruct (g_rep g) as [s|cap p s]; cbn [rep_live PML.srep_blocks]; [exact I|]. apply in_or_app. right. left. reflexivity. Qed.
Lemma incl_keep : forall (LBo st : list (Z * Z)), incl LBo (LBo ++ st).
Proof. intros. apply incl_appl, incl_refl. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Frame.
Variable L : asan_layout.
Variable IC : PMLA.consts.
Variable EC : PMESA.econsts.
Abbreviation segs := (hl_segs L).
Abbreviation u8 := (PMSA.u8 L).   Abbreviation u32 := (PMSA.u32 L).   Abbreviation u64 := (PMSA.u64 L).

Lemma u32_agree : forall (M M' : mem) a v, agree M M' a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> u32 M a v -> u32 M' a v.
Proof. intros M M' a v Hag Ha H4 Hu. unfold PMSA.u32, L5.u32_at in *. rewrite (L5C.rdn_agree segs M M' 4%nat a Ha ltac:(cbn; lia)); [exact Hu|]. intros i Hi; apply Hag; cbn in Hi; lia. Qed.
Lemma u64_agree : forall (M M' : mem) a v, agree M M' a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> u64 M a v -> u64 M' a v.
Proof. intros M M' a v Hag Ha H4 Hu. exact (L5C.u64_at_agree segs M M' a v Hag Ha H4 Hu). Qed.
Lemma u8_agree : forall (M M' : mem) a v, agree M M' a 1 -> 0 <= a -> a + 1 <= 2 ^ 64 -> u8 M a v -> u8 M' a v.
Proof. intros M M' a v Hag Ha H4 Hu. exact (L5C.u8_at_agree segs M M' a v Hag Ha H4 Hu). Qed.
Lemma agree_sub : forall (M M' : mem) a n a' n', agree M M' a n -> a <= a' -> a' + n' <= a + n -> agree M M' a' n'.
Proof. intros M M' a n a' n' H H1 H2 i Hi. apply H. lia. Qed.
(* [comment removed for export] *)
Definition shagree (M M' : mem) (p g : Z) : Prop := forall j, 0 <= j < g -> M' (Z_to_bv 64 (S p + j)) = M (Z_to_bv 64 (S p + j)).
Lemma shagree_of_shadow : forall (M M' : mem) p n g, p mod 8 = 0 -> 0 < n -> 0 <= g -> 8 * g <= n + 7 ->
  (forall a, in_shadow_of p n a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> shagree M M' p g.
Proof.
  intros M M' p n g Hp Hn Hg Hgn H j Hj. apply H. unfold in_shadow_of, S.
  pose proof (Z.div_mod p 8 ltac:(lia)) as D. rewrite Hp in D.
  assert (E : (p + n - 1) / 8 >= p / 8 + (n - 1) / 8).
  { replace (p + n - 1) with ((n - 1) + (p / 8) * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert ((n - 1) / 8 >= g - 1) by (apply Z.le_ge; apply Z.div_le_lower_bound; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma str_at_agree : forall (M M' : mem) o rep, 0 <= o -> o + 24 <= 2 ^ 64 -> agree M M' o 24 ->
  (match rep with PML.SShort _ => True | PML.SLong cap p _ => 0 <= p /\ p + cap <= 2 ^ 64 /\ agree M M' p cap end) ->
  PMSA.str_at L M o rep -> PMSA.str_at L M' o rep.
Proof.
  intros M M' o [s|cap p s] Ho H24 Hag Hb Hs; cbn [PMSA.str_at PMLA.str_at] in *.
  - exact (L5C.lstr_short_agree segs M M' o s Hag Ho H24 Hs).
  - destruct Hb as (Hp & Hpc & Hagb). destruct Hs as ((Hbit & Hw0 & Hw8 & Hw16 & Hbs & Hnul) & Hc8 & Hlt).
    split; [|split; assumption]. split; [exact Hbit|].
    split; [apply (u64_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact Hw0]|].
    split; [apply (u64_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact Hw8]|].
    split; [apply (u64_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact Hw16]|].
    split; [apply (L5C.bytes_at_agree segs M M' p s); [apply (agree_sub M M' _ _ _ _ Hagb); lia | lia | lia | exact Hbs]|].
    apply (u8_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hagb); lia | lia | lia | exact Hnul].
Qed.
Lemma sink_at_agree : forall (M M' : mem) o rep, 0 <= o -> o + 24 <= 2 ^ 64 -> agree M M' o 24 ->
  (match rep with PML.SShort _ => True | PML.SLong cap p _ => 0 <= p /\ p + cap <= 2 ^ 64 /\ agree M M' p cap /\ shagree M M' p (cap / 8) end) ->
  PMESA.sink_atA L M o rep -> PMESA.sink_atA L M' o rep.
Proof.
  intros M M' o rep Ho H24 Hag Hb (H1 & H2 & H3 & H4). split; [|split; [exact (L5C.defined_agree M M' o 24 Hag H2) | split; [exact H3|]]].
  - apply (str_at_agree M M' o rep Ho H24 Hag); [|exact H1]. destruct rep as [s|cap p s]; [exact I|]. destruct Hb as (B0 & B1 & B2 & _). exact (conj B0 (conj B1 B2)).
  - destruct rep as [s|cap p s]; cbn [PMLA.srep_sh] in *; [exact I|]. destruct Hb as (B0 & B1 & B2 & B3). destruct H4 as [Z0 PT].
    split; [exact (CL5A.shadow_zero_same M M' p (cap / 8) B3 Z0)|].
    intros Hm. exfalso. destruct H1 as (_ & H8 & _). exact (Hm H8).
Qed.
Lemma ctx_at_agree : forall (M M' : mem) a c, 0 <= a -> a + 32 <= 2 ^ 64 -> agree M M' a 32 -> PMESA.ctx_at L M a c -> PMESA.ctx_at L M' a c.
Proof.
  intros M M' a c Ha H32 Hag (C1 & C2 & C3 & C4 & C5 & C6). unfold PMESA.ctx_at.
  split; [apply (u32_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact C1]|].
  split; [apply (u8_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact C2]|].
  split; [apply (u8_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact C3]|].
  split; [apply (u64_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact C4]|].
  split; [exact C5 | exact (L5C.defined_agree M M' a 32 Hag C6)].
Qed.
Lemma depth_nonneg : forall es, 0 <= depth es.
Proof. intros es. unfold depth. lia. Qed.
Lemma depth_cons : forall (c : ectx) r, depth (c :: r) = depth r + 1.
Proof. intros. unfold depth. cbn [length]. lia. Qed.
(* [comment removed for export] *)
Lemma stack_at_agree : forall (M M' : mem) V es b capb, 0 <= V -> V + ENC_SIZE <= 2 ^ 64 -> agree M M' (V + O_STACK) 24 ->
  (capb <> 0 -> 0 <= b /\ b + capb <= 2 ^ 64 /\ agree M M' b capb) ->
  PMESA.stack_at L M V es b capb -> PMESA.stack_at L M' V es b capb.
Proof.
  intros M M' V es b capb HV HV2 Hag Hb (S1 & S2 & S3 & S4 & S5 & S6). unfold PMESA.stack_at, ENC_SIZE, O_STACK in *.
  split; [apply (u64_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact S1]|].
  split; [apply (u64_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact S2]|].
  split; [apply (u64_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact S3]|].
  split; [exact S4|]. split; [exact S5|].
  intros i Hi. specialize (S6 i Hi).
  assert (Hd : Z.of_nat i < depth es) by (unfold depth; lia).
  assert (Hne : capb <> 0) by lia. destruct (Hb Hne) as (B0 & B1 & B2).
  apply (ctx_at_agree M M' (b + 32 * Z.of_nat i)); [lia | lia | apply (agree_sub M M' _ _ _ _ B2); lia | exact S6].
Qed.
Lemma mul32_mod8 : forall k, 0 <= k -> (32 * 2 ^ k) mod 8 = 0.
Proof. intros k Hk. replace (32 * 2 ^ k) with ((4 * 2 ^ k) * 8) by lia. apply Z_mod_mult. Qed.
(* [comment removed for export] *)
Lemma stack_sh_agree : forall (M M' : mem) es b capb, (capb <> 0 -> b mod 8 = 0 /\ capb mod 8 = 0 /\ 0 <= 32 * depth es <= capb /\ shagree M M' b (capb / 8)) ->
  PMESA.stack_sh M es b capb -> PMESA.stack_sh M' es b capb.
Proof.
  intros M M' es b capb Hb [->|SC]; [left; reflexivity|]. destruct (Z.eq_dec capb 0) as [->|Hne]; [left; reflexivity|]. right.
  destruct (Hb Hne) as (B8 & C8 & Bd & BA). apply (CL5A.shadow_cont_same M M' b capb (32 * depth es) Bd B8); [|exact SC].
  intros a Ha. unfold in_shadow_of, S in Ha.
  apply Z.mod_divide in B8; [|lia]. destruct B8 as [q Hq]. apply Z.mod_divide in C8; [|lia]. destruct C8 as [r Hr].
  assert (E1 : b / 8 = q) by (rewrite Hq; apply Z.div_mul; lia).
  assert (E2 : (b + capb - 1) / 8 = q + r - 1) by (rewrite Hq, Hr; replace (q * 8 + r * 8 - 1) with (7 + (q + r - 1) * 8) by lia; rewrite Z.div_add by lia; reflexivity).
  assert (E3 : capb / 8 = r) by (rewrite Hr; apply Z.div_mul; lia).
  rewrite E1, E2 in Ha. replace a with (S b + (a - S b)) by lia. apply BA. unfold S. rewrite E1, E3. lia.
Qed.
(* [comment removed for export] *)
Lemma enc_obj_agree : forall (M M' : mem) V S2 d, 0 <= V -> V + ENC_SIZE <= 2 ^ 64 ->
  agree M M' V O_COLUMN -> agree M M' (V + O_COLON) (ENC_SIZE - O_COLON) -> L5.defined M' (V + O_COLUMN) 8 ->
  PMESA.enc_objA L IC EC M V S2 d -> PMESA.enc_objA L IC EC M' V S2 d.
Proof.
  intros M M' V S2 d HV HV2 A1 A2 Hcol H. unfold PMESA.enc_objA, PMESA.sv_at, ENC_SIZE, O_COLUMN, O_COLON, O_SINK, O_OPT_VPTR, O_FLAGS, O_BIGNUM_FMT, O_SPLITS, O_INDENT_SIZE, O_LINE_LIMIT,
    O_NL_CHARS, O_COMMON_VPTR, O_ENABLE, O_MAX_DEPTH, O_INDENT_CHAR, O_FP, O_INDENT, O_COMMA, O_OBRACE, O_CBRACE, O_OBRACKET, O_CBRACKET, O_DEPTH in *.
  assert (X8 : forall a v, V <= a -> a + 8 <= V + 296 -> u64 M a v -> u64 M' a v).
  { intros a v H1 H2. apply u64_agree; [apply (agree_sub _ _ _ _ _ _ A1); lia | lia | lia]. }
  assert (X4 : forall a v, V <= a -> a + 4 <= V + 296 -> u32 M a v -> u32 M' a v).
  { intros a v H1 H2. apply u32_agree; [apply (agree_sub _ _ _ _ _ _ A1); lia | lia | lia]. }
  assert (X1 : forall a v, V <= a -> a + 1 <= V + 296 -> u8 M a v -> u8 M' a v).
  { intros a v H1 H2. apply u8_agree; [apply (agree_sub _ _ _ _ _ _ A1); lia | lia | lia]. }
  assert (Y8 : forall a v, V + 304 <= a -> a + 8 <= V + 408 -> u64 M a v -> u64 M' a v).
  { intros a v H1 H2. apply u64_agree; [apply (agree_sub _ _ _ _ _ _ A2); lia | lia | lia]. }
  assert (Y4 : forall a v, V + 304 <= a -> a + 4 <= V + 408 -> u32 M a v -> u32 M' a v).
  { intros a v H1 H2. apply u32_agree; [apply (agree_sub _ _ _ _ _ _ A2); lia | lia | lia]. }
  assert (DEF : L5.defined M' V 408).
  { intros i Hi. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HD).
    destruct (Z_lt_le_dec i 296) as [Hl|Hge]; [rewrite (A1 (V + i)) by lia; apply HD; lia|].
    destruct (Z_lt_le_dec i 304) as [Hl2|Hge2]; [| rewrite (A2 (V + i)) by lia; apply HD; lia].
    replace (V + i) with (V + 296 + (i - 296)) by lia. apply Hcol. lia. }
  destruct H as (H1 & H2 & H3 & (fl & H4 & H4') & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & (en & H18 & H18') & H19 & H20 & H21 & H22 & (dp & H23) &
                 H24 & H25 & H26 & (H27 & H27') & (H28 & H28') & (H29 & H29') & (H30 & H30') & (H31 & H31') & (H32 & H32') & HD).
  split; [replace V with (V + 0) by lia; apply X8; [lia | lia | replace (V + 0) with V by lia; exact H1]|].
  split; [apply X8; [lia | lia | exact H2]|]. split; [apply X8; [lia | lia | exact H3]|].
  split; [exists fl; split; [apply X1; [lia | lia | exact H4] | exact H4']|].
  split; [apply X1; [lia | lia | exact H5]|].
  split; [apply X1; [lia | lia | exact H6]|]. split; [apply X1; [lia | lia | exact H7]|]. split; [apply X1; [lia | lia | exact H8]|].
  split; [apply X1; [lia | lia | exact H9]|]. split; [apply X1; [lia | lia | exact H10]|].
  split; [apply X1; [lia | lia | exact H11]|]. split; [apply X8; [lia | lia | exact H12]|].
  split; [apply X8; [lia | lia | exact H13]|]. split; [apply X8; [lia | lia | exact H14]|]. split; [apply X8; [lia | lia | exact H15]|].
  split; [apply (L5C.defined_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ A1); lia | exact H16]|].
  split; [apply X8; [lia | lia | exact H17]|].
  split; [exists en; split; [apply X1; [lia | lia | exact H18] | split; [exact (proj1 H18') | apply (L5C.defined_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ A1); lia | exact (proj2 H18')]]]|].
  split; [apply X4; [lia | lia | exact H19]|]. split; [apply X1; [lia | lia | exact H20]|].
  split; [apply X1; [lia | lia | exact H21]|]. split; [apply X4; [lia | lia | exact H22]|].
  split; [exists dp; apply X1; [lia | lia | exact H23]|].
  split; [apply X4; [lia | lia | exact H24]|]. split; [exact Hcol|]. split; [apply Y4; [lia | lia | exact H26]|].
  split; [split; apply Y8; try lia; assumption|]. split; [split; apply Y8; try lia; assumption|]. split; [split; apply Y8; try lia; assumption|].
  split; [split; apply Y8; try lia; assumption|]. split; [split; apply Y8; try lia; assumption|]. split; [split; apply Y8; try lia; assumption|].
  exact DEF.
Qed.

(* [comment removed for export] *)
Lemma enc_invA_agree : forall (M M' : mem) V S2 g,
  agree M M' V O_COLUMN -> agree M M' (V + O_COLON) (ENC_SIZE - O_COLON) -> L5.defined M' (V + O_COLUMN) 8 -> agree M M' S2 24 ->
  (forall b, In b (g_lbv g) -> agree M M' (fst b) (snd b) /\ shagree M M' (fst b) (snd b / 8)) ->
  PMESA.enc_invA L IC EC M V S2 g -> PMESA.enc_invA L IC EC M' V S2 g.
Proof.
  intros M M' V S2 g A1 A2 Hcol A3 HB (I1 & I2 & I3 & I4 & I5 & I6 & (R1 & R2 & R3 & R4 & RB)).
  assert (HV : 0 <= V) by exact R1. assert (HV2 : V + ENC_SIZE <= 2 ^ 64) by lia. assert (HS : 0 <= S2) by exact R3. assert (HS2 : S2 + 24 <= 2 ^ 64) by lia.
  split; [exact (enc_obj_agree M M' V S2 _ HV HV2 A1 A2 Hcol I1)|].
  assert (STB : g_scap g <> 0 -> In (g_sb g, g_scap g) (g_lbv g)).
  { intros Hne. unfold g_lbv, stack_blocks. apply in_or_app. right. destruct (Z.eqb_spec (g_scap g) 0) as [E|E]; [contradiction | left; reflexivity]. }
  split; [|split; [|split; [|split; [exact I5 | split; [exact I6 | exact (conj R1 (conj R2 (conj R3 (conj R4 RB))))]]]]].
  - apply (stack_at_agree M M' V _ _ _ HV HV2); [unfold O_STACK, O_COLUMN in *; apply (agree_sub _ _ _ _ _ _ A1); lia | | exact I2].
    intros Hne. destruct (HB _ (STB Hne)) as (B2 & _). destruct (RB _ (STB Hne)) as (B0 & _ & _ & B1). cbn [fst snd] in *. split; [exact B0 | split; [lia | exact B2]].
  - apply (stack_sh_agree M M'); [|exact I3]. intros Hne. destruct (HB _ (STB Hne)) as (B2 & B3). destruct (RB _ (STB Hne)) as (B0 & B16 & _ & B1). cbn [fst snd] in *.
    destruct I2 as (_ & _ & _ & S4 & S5 & _). split; [exact (CHA.mod8_of_16 _ B16)|].
    split; [destruct S5 as [[E _]|(k & Hk & E)]; [contradiction | rewrite E; apply mul32_mod8; lia] |].
    split; [split; [pose proof (depth_nonneg (g_es g)); lia | exact S4] | exact B3].
  - apply (sink_at_agree M M' S2 _ HS HS2 A3); [|exact I4].
    destruct (g_rep g) as [s|cap p s] eqn:Er; [exact I|].
    assert (Hin : In (p, cap) (g_lbv g)) by (unfold g_lbv; rewrite Er; cbn [PML.srep_blocks app]; left; reflexivity).
    destruct (HB _ Hin) as (B2 & B3). destruct (RB _ Hin) as (B0 & _ & _ & B1). cbn [fst snd] in *. split; [exact B0 | split; [lia | exact (conj B2 B3)]].
Qed.

(* [comment removed for export] *)
Lemma enc_agree_ok : PMESA.enc_agreeP L IC EC.
Proof.
  intros M M' V S2 g HI HA. pose proof HI as (I1 & _ & _ & _ & _ & _ & (R1 & R2 & R3 & R4 & RB)).
  assert (AV : agree M M' V ENC_SIZE) by (intros i Hi; apply HA; left; exact Hi).
  apply (enc_invA_agree M M' V S2 g); [apply (agree_sub _ _ _ _ _ _ AV); unfold O_COLUMN, ENC_SIZE; lia | apply (agree_sub _ _ _ _ _ _ AV); unfold O_COLON, ENC_SIZE; lia | | | | exact HI].
  - unfold PMESA.enc_objA in I1. repeat (destruct I1 as [_ I1]). apply (L5C.defined_agree M M'); [apply (agree_sub _ _ _ _ _ _ AV); unfold O_COLUMN, ENC_SIZE; lia|].
    intros i Hi. replace (V + O_COLUMN + i) with (V + (O_COLUMN + i)) by lia. apply I1. unfold O_COLUMN, ENC_SIZE in *. lia.
  - intros i Hi. apply HA. right. left. exact Hi.
  - intros b Hb. destruct (RB b Hb) as (B0 & B16 & Bn & B1). split.
    + intros i Hi. apply HA. right. right. left. exists b. exact (conj Hb Hi).
    + apply (shagree_of_shadow M M' (fst b) (snd b) (snd b / 8)); [| exact Bn | apply Z.div_pos; lia | pose proof (Z.mul_div_le (snd b) 8 ltac:(lia)); lia |].
      * exact (CHA.mod8_of_16 _ B16).
      * intros a Ha. apply HA. right. right. right. left. exists b. exact (conj Hb Ha).
Qed.
End Frame.
End EKA.
