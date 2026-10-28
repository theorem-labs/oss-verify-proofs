(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapIfaceU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5.
Import ListNotations.
Import PML.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module EK.
Import PMES.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kv_s2_pos : forall rep, 1 <= kv_s2 rep.
Proof. intros [s|cap p s]; cbn [kv_s2]; [lia | pose proof (Z.log2_nonneg (2 ^ 47 / cap)); lia]. Qed.
Lemma kv_st_nonneg : forall capb, 0 <= kv_st capb.
Proof. intros capb. unfold kv_st. destruct (capb =? 0); [lia | apply Z.log2_nonneg]. Qed.
(* [comment removed for export] *)
Lemma grow_cap_ge : forall cap n, 8 <= cap -> cap mod 8 = 0 -> 0 <= n -> 2 * cap <= grow_cap cap n /\ n < grow_cap cap n /\ grow_cap cap n mod 8 = 0.
Proof.
  intros cap n H0 H8 Hn. unfold grow_cap. set (m := Z.max n (2 * (cap - 1))).
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
Lemma grow_cap_short : forall n, 0 <= n -> 48 <= grow_cap 23 n /\ n < grow_cap 23 n /\ grow_cap 23 n mod 8 = 0.
Proof.
  intros n Hn. unfold grow_cap. set (m := Z.max n (2 * (23 - 1))). assert (Hm : 44 <= m /\ n <= m) by (unfold m; lia).
  rewrite CL5.lor7 by lia. pose proof (Z.div_mod m 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound m 8 ltac:(lia)) as B.
  assert (Hq : 44 / 8 <= m / 8) by (apply Z.div_le_mono; lia). change (44 / 8) with 5 in Hq.
  split; [lia|]. split; [lia|].
  replace (8 * (m / 8) + 7 + 1) with (0 + (m / 8 + 1) * 8) by lia. rewrite Z.mod_add by lia. reflexivity.
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

Section WithL.
Variable L : heap_layout.
Hypothesis KPM : 0 <= hl_k_per_malloc L.
Hypothesis CEIL : hl_sptop L <= 2 ^ 47.

(* [comment removed for export] *)

(* [comment removed for export] *)
End WithL.

Lemma grow_cap_le : forall cap n, 1 <= cap -> 0 <= n -> grow_cap cap n <= Z.max n (2 * (cap - 1)) + 8.
Proof.
  intros cap n Hc Hn. unfold grow_cap. set (m := Z.max n (2 * (cap - 1))). assert (Hm : 0 <= m) by (unfold m; lia).
  rewrite CL5.lor7 by lia. pose proof (Z.mul_div_le m 8 ltac:(lia)). lia.
Qed.

Definition rep8 (rep : srep) : Prop := match rep with SShort _ => True | SLong cap _ _ => 8 <= cap /\ cap mod 8 = 0 end.
Lemma rep8_of_sink : forall M o rep, sink_at M o rep -> rep8 rep.
Proof.
  intros M o [s|cap p s] (H1 & _ & H3); cbn [rep8]; [exact I|]. cbn [rep_ok str_at] in *. destruct H1 as (_ & Hm & _). split; [lia | exact Hm].
Qed.

Lemma grow_req_facts : forall rep need, rep8 rep -> ~ fits rep need -> 0 <= need ->
  2 * alloc_of rep <= grow_req rep need /\ need < grow_req rep need /\ grow_req rep need mod 8 = 0 /\ alloc_of rep <= need /\
  grow_req rep need <= 2 * need + 8.
Proof.
  intros [s|cap p s] need Hsh Hnf Hn; unfold grow_req; cbn [alloc_of fits rep8] in *.
  - destruct (grow_cap_short need Hn) as (G1 & G2 & G3). pose proof (grow_cap_le 23 need ltac:(lia) Hn). repeat split; lia.
  - destruct Hsh as [H8 Hm]. destruct (grow_cap_ge cap need H8 Hm Hn) as (G1 & G2 & G3). pose proof (grow_cap_le cap need ltac:(lia) Hn).
    assert (cap <= need) by lia. repeat split; lia.
Qed.

Definition stack_shape (capb : Z) : Prop := capb = 0 \/ exists k, 0 <= k <= 10 /\ capb = 32 * 2 ^ k.
Lemma stack_shape_of_at : forall M V es b capb, stack_at M V es b capb -> stack_shape capb.
Proof. intros M V es b capb (_ & _ & _ & _ & [(-> & _)|S] & _); [left; reflexivity | right; exact S]. Qed.
Definition st_caps : list Z := [0; 32; 64; 128; 256; 512; 1024; 2048; 4096; 8192; 16384].
Lemma st_caps_of : forall capb, stack_shape capb -> capb < 32768 -> In capb st_caps.
Proof.
  intros capb [->|(k & Hk & ->)] Hlt; [left; reflexivity|].
  assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
  destruct Hk' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
    [(vm_compute; lia) .. | (exfalso; vm_compute in Hlt; discriminate Hlt)].
Qed.
Lemma st_tab : forall capb, In capb st_caps ->
  kv_st (stack_grow capb) + 1 = kv_st capb /\
  Z.max 0 (65536 - 2 * stack_grow capb) + stack_grow capb + (if capb =? 0 then 32 else 0) = Z.max 0 (65536 - 2 * capb) /\
  (Z.leb 1 (stack_grow capb) && Z.leb (stack_grow capb) 32768)%bool = true.
Proof. intros capb H. repeat (destruct H as [<- | H]; [split; [reflexivity | split; reflexivity] |]). destruct H. Qed.

Section WithLU.
Variable L : heap_layout.
Hypothesis KPM : 0 <= hl_k_per_malloc L.
Hypothesis BOV : 0 <= hl_b_overhead L.
Local Set Default Proof Using "All".

Lemma kenc_nonneg : forall g, 0 <= kenc L g.
Proof. intros g. unfold kenc. pose proof (kv_s2_pos (g_rep g)). pose proof (kv_st_nonneg (g_scap g)). nia. Qed.
Lemma bpot_s2_nonneg : forall rep, 0 <= bpot_s2 L rep.
Proof. intros rep. unfold bpot_s2. pose proof (kv_s2_pos rep). pose proof (Z.le_max_l 0 (4 * CLU + 16 - 2 * alloc_of rep)). nia. Qed.
Lemma bpot_st_nonneg : forall capb, 0 <= bpot_st L capb.
Proof. intros capb. unfold bpot_st. pose proof (kv_st_nonneg capb). pose proof (Z.le_max_l 0 (65536 - 2 * capb)). nia. Qed.
Lemma benc_nonneg : forall g, 0 <= benc L g.
Proof. intros g. unfold benc. pose proof (bpot_s2_nonneg (g_rep g)). pose proof (bpot_st_nonneg (g_scap g)). lia. Qed.

Lemma bpot_s2_grow : forall rep need p' s', rep8 rep -> ~ fits rep need -> 0 <= need -> need <= CLU ->
  bpot_s2 L (SLong (grow_req rep need) p' s') + (grow_req rep need + hl_b_overhead L) <= bpot_s2 L rep /\
  (kv_s2 (SLong (grow_req rep need) p' s') + 1) * hl_k_per_malloc L <= kv_s2 rep * hl_k_per_malloc L.
Proof.
  intros rep need p' s' Hsh Hnf Hn Hcl.
  destruct (grow_req_facts rep need Hsh Hnf Hn) as (G1 & G2 & G3 & G4 & G5).
  assert (Hc : grow_req rep need <= 2 ^ 47) by (unfold CLU in Hcl; lia).
  assert (KV : kv_s2 (SLong (grow_req rep need) p' s') + 1 <= kv_s2 rep).
  { destruct rep as [s|cap p s]; unfold grow_req in *; cbn [kv_s2 alloc_of rep8] in *.
    - destruct (grow_cap_short need Hn) as (A1 & _ & _). pose proof (log2_48 _ A1). lia.
    - destruct Hsh as [H8 Hm]. pose proof (log2_halves47 cap (grow_cap cap need) ltac:(lia) G1 Hc). lia. }
  split; [|nia].
  unfold bpot_s2. cbn [alloc_of].
  rewrite (Z.max_r 0 (4 * CLU + 16 - 2 * grow_req rep need)) by lia.
  pose proof (Z.le_max_r 0 (4 * CLU + 16 - 2 * alloc_of rep)). nia.
Qed.

Lemma grow_okU : forall cr rep kx bx need, screditU L cr rep kx bx -> rep8 rep -> 0 <= need -> need <= CLU -> ~ fits rep need ->
  credit_ok L cr (grow_req rep need) /\ grow_req rep need <= NBU.
Proof.
  intros cr rep kx bx need (S0 & S1 & S2 & S3) Hsh Hn Hcl Hnf.
  destruct (grow_req_facts rep need Hsh Hnf Hn) as (G1 & G2 & G3 & G4 & G5).
  destruct (bpot_s2_grow rep need 0 [] Hsh Hnf Hn Hcl) as [B K].
  pose proof (bpot_s2_nonneg (SLong (grow_req rep need) 0 [])) as NN.
  pose proof (kv_s2_pos (SLong (grow_req rep need) 0 [])) as KP.
  split; [unfold credit_ok; split; nia | unfold NBU, CLU in *; lia].
Qed.

Lemma grown_screditU : forall LB cr M' o rep s' LB' cr' LBk rep' kx bx,
  x_grownU L LB cr M' o rep s' LB' cr' LBk rep' -> rep8 rep -> len s' <= CLU ->
  screditU L cr rep kx bx -> screditU L cr' rep' kx bx.
Proof.
  intros LB cr M' o rep s' LB' cr' LBk rep' kx bx [(F & -> & _ & _ & -> & _)|(NF & p' & G)] Hrep Hcl HS.
  - destruct rep; exact HS.
  - cbv zeta in G. destruct G as (-> & _ & _ & _ & -> & _).
    assert (HL : 0 <= len s') by (unfold len; lia).
    destruct (bpot_s2_grow rep (len s') p' s' Hrep NF HL Hcl) as [B K]. change (grow_cap (alloc_of rep) (len s')) with (grow_req rep (len s')).
    destruct HS as (S0 & S1 & S2 & S3). unfold screditU, debit. cbn [fst snd].
    repeat split; [exact S0 | nia | exact S2 | lia].
Qed.

Lemma scredit_of_ecreditU : forall cr g kx bx, ecreditU L cr g kx bx ->
  screditU L cr (g_rep g) (kx + kv_st (g_scap g) * hl_k_per_malloc L) (bx + bpot_st L (g_scap g)).
Proof.
  intros cr g kx bx (H0 & H1 & H2 & H3). unfold ecreditU, kenc, benc, screditU in *.
  pose proof (kv_st_nonneg (g_scap g)). pose proof (bpot_st_nonneg (g_scap g)). repeat split; nia.
Qed.
Lemma ecredit_of_screditU : forall cr g kx bx rep' g', g_rep g' = rep' -> g_scap g' = g_scap g ->
  screditU L cr rep' (kx + kv_st (g_scap g) * hl_k_per_malloc L) (bx + bpot_st L (g_scap g)) -> 0 <= kx -> 0 <= bx ->
  ecreditU L cr g' kx bx.
Proof.
  intros cr g kx bx rep' g' E1 E2 (H0 & H1 & H2 & H3) Hk Hb. unfold ecreditU, kenc, benc, screditU in *. rewrite E1, E2.
  repeat split; [exact Hk | nia | exact Hb | nia].
Qed.

Lemma ecredit_grow_okU : forall cr g kx bx need, ecreditU L cr g kx bx -> rep8 (g_rep g) -> 0 <= need -> need <= CLU -> ~ fits (g_rep g) need ->
  credit_ok L cr (grow_req (g_rep g) need) /\ grow_req (g_rep g) need <= NBU.
Proof. intros cr g kx bx need HC. exact (grow_okU cr (g_rep g) _ _ need (scredit_of_ecreditU cr g kx bx HC)). Qed.
Lemma grown_ecreditU : forall LB cr M' o s' LB' cr' LBk rep' kx bx g,
  x_grownU L LB cr M' o (g_rep g) s' LB' cr' LBk rep' -> rep8 (g_rep g) -> len s' <= CLU ->
  ecreditU L cr g kx bx -> forall g', g_rep g' = rep' -> g_scap g' = g_scap g -> ecreditU L cr' g' kx bx.
Proof.
  intros LB cr M' o s' LB' cr' LBk rep' kx bx g HG Hrep Hcl HC g' E1 E2.
  pose proof (scredit_of_ecreditU cr g kx bx HC) as HS.
  pose proof (grown_screditU _ _ _ _ _ _ _ _ _ _ _ _ HG Hrep Hcl HS) as HS'.
  exact (ecredit_of_screditU cr' g kx bx rep' g' E1 E2 HS' (proj1 HC) (proj1 (proj2 (proj2 HC)))).
Qed.

Lemma bpot_st_grow : forall capb, stack_shape capb -> capb < 32768 ->
  0 < stack_grow capb <= 32768 /\ (kv_st (stack_grow capb) + 1) * hl_k_per_malloc L <= kv_st capb * hl_k_per_malloc L /\
  bpot_st L (stack_grow capb) + (stack_grow capb + hl_b_overhead L) <= bpot_st L capb.
Proof.
  intros capb Hsh Hlt. destruct (st_tab capb (st_caps_of capb Hsh Hlt)) as (A & B & C).
  apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1, C2.
  assert (X : 0 <= (if capb =? 0 then 32 else 0)) by (destruct (capb =? 0); lia).
  unfold bpot_st. rewrite <- A. split; [lia|]. split; nia.
Qed.
Lemma ecredit_stack_growU : forall cr g kx bx, ecreditU L cr g kx bx -> stack_shape (g_scap g) ->
  32 * depth (g_es g) = g_scap g -> depth (g_es g) < MAX_DEPTH ->
  (credit_ok L cr (stack_grow (g_scap g)) /\ stack_grow (g_scap g) <= NBU) /\
  forall g', g_rep g' = g_rep g -> g_scap g' = stack_grow (g_scap g) -> ecreditU L (debit L cr (stack_grow (g_scap g))) g' kx bx.
Proof.
  intros cr g kx bx (H0 & H1 & H2 & H3) Hsh Hd Hmax. unfold MAX_DEPTH in Hmax.
  destruct (bpot_st_grow (g_scap g) Hsh ltac:(lia)) as (S1 & S2 & S3).
  pose proof (bpot_s2_nonneg (g_rep g)). pose proof (bpot_st_nonneg (stack_grow (g_scap g))).
  pose proof (kv_s2_pos (g_rep g)). pose proof (kv_st_nonneg (stack_grow (g_scap g))).
  unfold ecreditU, kenc, benc in *. split.
  - split; [unfold credit_ok; split; nia | unfold NBU; lia].
  - intros g' E1 E2. unfold debit. cbn [fst snd]. rewrite E1, E2. repeat split; [exact H0 | nia | exact H2 | lia].
Qed.
End WithLU.

Lemma eroom_null : forall g, eroomU g EvNull -> g_len g + fst (pre_scalar (g_es g)) + 4 <= CLU.
Proof. intros g H. unfold eroomU, kmax in H. cbn [ev_ind pay_hi quotes] in H. lia. Qed.
Lemma pre_scalar_arr : forall c r, ec_arr c = true -> fst (pre_scalar (c :: r)) = bs_delta (c :: r).
Proof. intros c r H. cbn [pre_scalar]. rewrite H. reflexivity. Qed.

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
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nodup_app_l' : forall (l1 l2 : list Z) a, base.NoDup (l1 ++ l2) -> In a l2 -> ~ In a l1.
Proof. intros l1 l2 a H. apply base.NoDup_ListNoDup in H. exact (nodup_app_l l1 l2 a H). Qed.
Lemma drop_lbv : forall LBo rep sb scap, List.NoDup (map fst (LBo ++ srep_blocks rep ++ stack_blocks sb scap)) ->
  lb_drop rep (LBo ++ srep_blocks rep ++ stack_blocks sb scap) = LBo ++ stack_blocks sb scap.
Proof.
  intros LBo rep sb scap ND. destruct rep as [s|cap p s]; cbn [lb_drop srep_blocks app] in *; [reflexivity|].
  rewrite lb_remove_app.
  - cbn [lb_remove fst]. rewrite Z.eqb_refl. reflexivity.
  - rewrite map_app in ND. apply (nodup_app_l _ _ p ND). cbn [map fst In]. left. reflexivity.
Qed.
Lemma perm_lbv_in : forall (LBo st : list (Z * Z)) b, Permutation (b :: LBo ++ st) (LBo ++ b :: st).
Proof. intros. apply Permutation_middle. Qed.
Lemma rep_live_lbv : forall LBo g, rep_live (g_rep g) (LBo ++ g_lbv g).
Proof. intros LBo g. unfold g_lbv. destruct (g_rep g) as [s|cap p s]; cbn [rep_live srep_blocks]; [exact I|]. apply in_or_app. right. left. reflexivity. Qed.
Lemma incl_keep : forall (LBo st : list (Z * Z)), incl LBo (LBo ++ st).
Proof. intros. apply incl_appl, incl_refl. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation agree := (L5C.agree_on).
Lemma u32_agree : forall (M M' : mem) a v, agree M M' a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> u32 M a v -> u32 M' a v.
Proof. intros M M' a v Hag Ha H4 Hu. unfold u32, L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M M' 4%nat a Ha ltac:(cbn; lia)); [exact Hu|]. intros i Hi; apply Hag; cbn in Hi; lia. Qed.
Lemma u64_agree : forall (M M' : mem) a v, agree M M' a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> u64 M a v -> u64 M' a v.
Proof. intros M M' a v Hag Ha H4 Hu. exact (L5C.u64_at_agree RSEGS M M' a v Hag Ha H4 Hu). Qed.
Lemma u8_agree : forall (M M' : mem) a v, agree M M' a 1 -> 0 <= a -> a + 1 <= 2 ^ 64 -> u8 M a v -> u8 M' a v.
Proof. intros M M' a v Hag Ha H4 Hu. exact (L5C.u8_at_agree RSEGS M M' a v Hag Ha H4 Hu). Qed.
Lemma agree_sub : forall (M M' : mem) a n a' n', agree M M' a n -> a <= a' -> a' + n' <= a + n -> agree M M' a' n'.
Proof. intros M M' a n a' n' H H1 H2 i Hi. apply H. lia. Qed.

(* [comment removed for export] *)
Lemma str_at_agree : forall (M M' : mem) o rep, 0 <= o -> o + 24 <= 2 ^ 64 -> agree M M' o 24 ->
  (match rep with SShort _ => True | SLong cap p _ => 0 <= p /\ p + cap <= 2 ^ 64 /\ agree M M' p cap end) ->
  str_at M o rep -> str_at M' o rep.
Proof.
  intros M M' o [s|cap p s] Ho H24 Hag Hb Hs; cbn [str_at] in *.
  - exact (L5C.lstr_short_agree RSEGS M M' o s Hag Ho H24 Hs).
  - destruct Hb as (Hp & Hpc & Hagb). destruct Hs as ((Hbit & Hw0 & Hw8 & Hw16 & Hbs & Hnul) & Hc8 & Hlt).
    split; [|split; assumption]. split; [exact Hbit|].
    split; [apply (u64_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact Hw0]|].
    split; [apply (u64_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact Hw8]|].
    split; [apply (u64_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact Hw16]|].
    split; [apply (L5C.bytes_at_agree RSEGS M M' p s); [apply (agree_sub M M' _ _ _ _ Hagb); lia | lia | lia | exact Hbs]|].
    apply (u8_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hagb); lia | lia | lia | exact Hnul].
Qed.
Lemma sink_at_agree : forall (M M' : mem) o rep, 0 <= o -> o + 24 <= 2 ^ 64 -> agree M M' o 24 ->
  (match rep with SShort _ => True | SLong cap p _ => 0 <= p /\ p + cap <= 2 ^ 64 /\ agree M M' p cap end) ->
  sink_at M o rep -> sink_at M' o rep.
Proof.
  intros M M' o rep Ho H24 Hag Hb (H1 & H2 & H3). split; [exact (str_at_agree M M' o rep Ho H24 Hag Hb H1)|]. split; [|exact H3].
  exact (L5C.defined_agree M M' o 24 Hag H2).
Qed.
Lemma ctx_at_agree : forall (M M' : mem) a c, 0 <= a -> a + 32 <= 2 ^ 64 -> agree M M' a 32 -> ctx_at M a c -> ctx_at M' a c.
Proof.
  intros M M' a c Ha H32 Hag (C1 & C2 & C3 & C4 & C5 & C6). unfold ctx_at.
  split; [apply (u32_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact C1]|].
  split; [apply (u8_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact C2]|].
  split; [apply (u8_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact C3]|].
  split; [apply (u64_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact C4]|].
  split; [exact C5 | exact (L5C.defined_agree M M' a 32 Hag C6)].
Qed.
(* [comment removed for export] *)
Lemma stack_at_agree : forall (M M' : mem) V es b capb, 0 <= V -> V + ENC_SIZE <= 2 ^ 64 -> agree M M' (V + O_STACK) 24 ->
  (capb <> 0 -> 0 <= b /\ b + capb <= 2 ^ 64 /\ agree M M' b capb) ->
  stack_at M V es b capb -> stack_at M' V es b capb.
Proof.
  intros M M' V es b capb HV HV2 Hag Hb (S1 & S2 & S3 & S4 & S5 & S6). unfold stack_at, ENC_SIZE, O_STACK in *.
  split; [apply (u64_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact S1]|].
  split; [apply (u64_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact S2]|].
  split; [apply (u64_agree M M' _ _); [apply (agree_sub M M' _ _ _ _ Hag); lia | lia | lia | exact S3]|].
  split; [exact S4|]. split; [exact S5|].
  intros i Hi. specialize (S6 i Hi).
  assert (Hd : Z.of_nat i < depth es) by (unfold depth; lia).
  assert (Hne : capb <> 0) by lia. destruct (Hb Hne) as (B0 & B1 & B2).
  apply (ctx_at_agree M M' (b + 32 * Z.of_nat i)); [lia | lia | apply (agree_sub M M' _ _ _ _ B2); lia | exact S6].
Qed.
(* [comment removed for export] *)
Lemma enc_obj_agree : forall (M M' : mem) V S2 d, 0 <= V -> V + ENC_SIZE <= 2 ^ 64 ->
  agree M M' V O_COLUMN -> agree M M' (V + O_COLON) (ENC_SIZE - O_COLON) -> L5.defined M' (V + O_COLUMN) 8 ->
  enc_obj M V S2 d -> enc_obj M' V S2 d.
Proof.
  intros M M' V S2 d HV HV2 A1 A2 Hcol H. unfold enc_obj, sv_at, ENC_SIZE, O_COLUMN, O_COLON, O_SINK, O_OPT_VPTR, O_FLAGS, O_BIGNUM_FMT, O_SPLITS, O_INDENT_SIZE, O_LINE_LIMIT, O_NL_CHARS,
    O_COMMON_VPTR, O_ENABLE, O_MAX_DEPTH, O_INDENT_CHAR, O_FP, O_INDENT, O_COMMA, O_OBRACE, O_CBRACE, O_OBRACKET, O_CBRACKET, O_DEPTH in *.
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
  destruct H as (H1 & H2 & H3 & (fl & H4 & H4') & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & (en & H18 & H18') & H19 & H20 & H21 & H22 & (dp & H23) &
                 H24 & H25 & H26 & (H27 & H27') & (H28 & H28') & (H29 & H29') & (H30 & H30') & (H31 & H31') & (H32 & H32')).
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
  repeat split; apply Y8; try lia; assumption.
Qed.

(* [comment removed for export] *)
Lemma enc_inv_agree : forall (M M' : mem) V S2 g, 0 <= V -> V + ENC_SIZE <= 2 ^ 64 -> 0 <= S2 -> S2 + 24 <= 2 ^ 64 ->
  agree M M' V O_COLUMN -> agree M M' (V + O_COLON) (ENC_SIZE - O_COLON) -> L5.defined M' (V + O_COLUMN) 8 -> agree M M' S2 24 ->
  (forall b, In b (g_lbv g) -> 0 <= fst b /\ fst b + snd b <= 2 ^ 64 /\ agree M M' (fst b) (snd b)) ->
  enc_inv M V S2 g -> enc_inv M' V S2 g.
Proof.
  intros M M' V S2 g HV HV2 HS HS2 A1 A2 Hcol A3 HB (I1 & I2 & I3 & I4 & I5).
  split; [exact (enc_obj_agree M M' V S2 _ HV HV2 A1 A2 Hcol I1)|].
  split; [|split; [|split; assumption]].
  - apply (stack_at_agree M M' V _ _ _ HV HV2); [unfold O_STACK, O_COLUMN in *; apply (agree_sub _ _ _ _ _ _ A1); lia | | exact I2].
    intros Hne. apply (HB (g_sb g, g_scap g)). unfold g_lbv, stack_blocks. apply in_or_app. right. destruct (Z.eqb_spec (g_scap g) 0) as [E|E]; [contradiction | left; reflexivity].
  - apply (sink_at_agree M M' S2 _ HS HS2 A3); [|exact I3].
    destruct (g_rep g) as [s|cap p s] eqn:Er; [exact I|]. apply (HB (p, cap)). unfold g_lbv. rewrite Er. cbn [srep_blocks app]. left. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lit_bytes : forall (M : mem) a (bs : list Z), img_ro M -> 0x10000 <= a -> a + len bs <= IMG_RO_HI ->
  L5.bytes_at RSEGS (fun _ => None) a bs -> L5.bytes_at RSEGS M a bs.
Proof.
  intros M a bs Hro Ha Hb H. unfold len, IMG_RO_HI in *.
  apply (L5C.bytes_at_agree RSEGS (fun _ => None) M a bs); [|lia | lia | exact H].
  intros i Hi. apply Hro. unfold IMG_RO_HI. lia.
Qed.
Ltac lit_tac := intros i Hi; cbn [length] in Hi; repeat (destruct i as [|i]; [vm_compute; reflexivity|]); exfalso; lia.
Lemma txt_comma : L5.bytes_at RSEGS (fun _ => None) TXT_COMMA [44; 32].      Proof. lit_tac. Qed.
Lemma txt_colon : L5.bytes_at RSEGS (fun _ => None) TXT_COLON [58; 32].      Proof. lit_tac. Qed.
Lemma txt_obrace : L5.bytes_at RSEGS (fun _ => None) TXT_OBRACE [123].       Proof. lit_tac. Qed.
Lemma txt_cbrace : L5.bytes_at RSEGS (fun _ => None) TXT_CBRACE [125].       Proof. lit_tac. Qed.
Lemma txt_obracket : L5.bytes_at RSEGS (fun _ => None) TXT_OBRACKET [91].    Proof. lit_tac. Qed.
Lemma txt_cbracket : L5.bytes_at RSEGS (fun _ => None) TXT_CBRACKET [93].    Proof. lit_tac. Qed.
Lemma img_ro_agree : forall (M M' : mem), (forall a, 0x10000 <= a < IMG_RO_HI -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> img_ro M -> img_ro M'.
Proof. intros M M' H Hro i Hi. rewrite (H i Hi). exact (Hro i Hi). Qed.
(* [comment removed for export] *)
Lemma img_ro_hpres : forall L LBk sp scr W (M M' : mem), PmLayout.pm0_layout L -> L5C.hpres L LBk sp scr W M M' ->
  (forall w a, In w W -> L5.in_rng w a -> IMG_RO_HI <= a) -> img_ro M -> img_ro M'.
Proof.
  intros L LBk sp scr W M M' LAY HP HW Hro. apply (img_ro_agree M M'); [|exact Hro]. intros a Ha. unfold IMG_RO_HI in *.
  apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP).
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_errno L LAY) as LE.
  apply L5C.kept_static; [rewrite ILO, IHI; lia | intros X; pose proof (PmLayout.ly_static L LAY a X); lia | rewrite ILO; lia | rewrite IHI; lia | rewrite LE; lia|].
  intros w Hw Hin. pose proof (HW w a Hw Hin). lia.
Qed.
End EK.
