(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmModel PmModelFacts.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8 PnModel PnModelFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia := try match goal with H : PNM.bvec_at _ _ _ _ _ _ _ _ |- _ => clear H end; Stdlib.micromega.Lia.lia.
Local Ltac nia := try match goal with H : PNM.bvec_at _ _ _ _ _ _ _ _ |- _ => clear H end; Stdlib.micromega.Lia.nia.

Module PNOFA.
Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.
Definition apart (p k q m : Z) : Prop := p + k <= q \/ q + m <= p.

Lemma outside_app W1 W2 a : L5.outside W1 a -> L5.outside W2 a -> L5.outside (W1 ++ W2) a.
Proof. intros H1 H2 r Hr. apply in_app_or in Hr. destruct Hr as [Hr|Hr]; [exact (H1 r Hr)| exact (H2 r Hr)]. Qed.
Lemma outside_cons r W a : ~ L5.in_rng r a -> L5.outside W a -> L5.outside (r :: W) a.
Proof. intros H1 H2 r' [<-|Hr]; [exact H1| exact (H2 r' Hr)]. Qed.
Lemma outside_nil a : L5.outside [] a.
Proof. intros r []. Qed.
Lemma outside_Forall W a : Forall (fun r => ~ L5.in_rng r a) W -> L5.outside W a.
Proof. intros H r Hr. rewrite Forall_forall in H. exact (H r Hr). Qed.

(* [comment removed for export] *)
Lemma S_rng a : 0 <= a < 2 ^ 47 -> SB <= S a < BIGSHADOW_HI /\ 0 <= S a < 2 ^ 64.
Proof. intros Ha. unfold S, SB, BIGSHADOW_HI. pose proof (Z.div_pos a 8). pose proof (Z.div_lt_upper_bound a 8 (2 ^ 44)). lia. Qed.
Lemma S_mono a b : a <= b -> S a <= S b.
Proof. intros H. unfold S. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.
Lemma app_mem_not_S p k a : app_mem p k -> 0 <= a < 2 ^ 47 -> ~ L5.in_rng (p, k) (S a).
Proof.
  intros (H0 & H1 & H2) Ha. pose proof (S_rng a Ha) as [R _]. unfold L5.in_rng. cbn [fst snd].
  unfold SB, BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
Qed.
Lemma app_mem_sub p n q m : app_mem p n -> p <= q -> 0 <= m -> q + m <= p + n -> app_mem q m.
Proof. intros (H0 & H1 & H2) A B C. unfold app_mem. lia. Qed.
(* [comment removed for export] *)
Lemma gspan_shadow b m i : b mod 8 = 0 -> 0 < m -> b <= i < b + PNBOA.gspan m -> in_shadow_of b m (S i).
Proof.
  intros Hb Hm Hi. unfold in_shadow_of. split; [apply S_mono; lia|]. unfold S, PNBOA.gspan in *.
  set (q := b / 8) in *. pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite Hb, Z.add_0_r in Db. fold q in Db.
  assert (Q : (m + 7) / 8 = (m - 1) / 8 + 1). { replace (m + 7) with (m - 1 + 1 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  rewrite Q in Hi.
  assert (E : (b + m - 1) / 8 = q + (m - 1) / 8). { rewrite Db. replace (8 * q + m - 1) with (m - 1 + q * 8) by lia. rewrite Z.div_add by lia. lia. }
  rewrite E. assert (X : i / 8 < q + (m - 1) / 8 + 1); [|lia]. apply Z.div_lt_upper_bound; [lia|]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Keep.
Variable segs : list Segment.
Variable A : pm_addrs.
Variables (L : asan_layout) (ar : asan_run).
Variables (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (W : list L5.range) (M M' : word -> option byte).
Variables (lo hi : Z).
Hypothesis HP : L5CA.ahpres L ar LB FF sp scr W M M'.
Hypothesis HWA : Forall (fun r => app_mem (fst r) (snd r)) W.
Hypothesis HFR : forall a, lo <= a < hi -> aclient L ar LB FF sp scr a /\ aclient L ar LB FF sp scr (S a).
Hypothesis HFA : app_mem lo (hi - lo).
Hypothesis HBA : forall b, In b LB -> 0 < snd b /\ fst b mod 16 = 0 /\ app_mem (fst b) (snd b).

Definition NT (a : Z) : Prop := L5CA.akept L ar LB FF sp scr W a.
Definition Y (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ aclient L ar LB FF sp scr a.
Definition NS (i : Z) : Prop := L5CA.akept L ar LB FF sp scr W (S i).

Lemma AGX a n : 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> NT i) -> L5C.agree_on M M' a n.
Proof. intros _ _ H i Hi. exact (proj1 HP i (H i Hi)). Qed.
Lemma DKY i : Y i -> M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None.
Proof. intros [R C] D. exact (proj2 (proj2 HP) i R C D). Qed.
Lemma SHX a n : (forall i, a <= i < a + n -> NS i) -> PMFA.agsh M M' a n.
Proof. intros H x Hx. exact (proj1 HP (S x) (H x Hx)). Qed.

Lemma sh_outside a : 0 <= a < 2 ^ 47 -> L5.outside W (S a).
Proof. intros Ha r Hr. rewrite Forall_forall in HWA. destruct r as (p & k). exact (app_mem_not_S p k a (HWA _ Hr) Ha). Qed.

(* [comment removed for export] *)
Lemma frame_Y a : lo <= a < hi -> Y a.
Proof. intros Ha. split; [destruct HFA as (F0 & _ & F2); lia| exact (proj1 (HFR a Ha))]. Qed.
Lemma frame_NS a : lo <= a < hi -> NS a.
Proof.
  intros Ha. destruct HFA as (F0 & _ & F2). pose proof (S_rng a ltac:(lia)) as [_ R].
  split; [exact R|]. split; [exact (proj2 (HFR a Ha))| apply sh_outside; lia].
Qed.
Lemma frame_NT a : lo <= a < hi -> L5.outside W a -> NT a.
Proof. intros Ha Ho. destruct HFA as (F0 & _ & F2). split; [lia|]. split; [exact (proj1 (HFR a Ha))| exact Ho]. Qed.
(* [comment removed for export] *)
Lemma blk_Y b a : In b LB -> fst b <= a < fst b + snd b -> Y a.
Proof.
  intros Hin Ha. destruct (HBA b Hin) as (_ & _ & (B0 & _ & B2)). split; [lia|]. left. exists b. split; [exact Hin| exact Ha].
Qed.
Lemma blk_NT b a : In b LB -> fst b <= a < fst b + snd b -> L5.outside W a -> NT a.
Proof.
  intros Hin Ha Ho. destruct (HBA b Hin) as (_ & _ & (B0 & _ & B2)). split; [lia|]. split; [| exact Ho]. left. exists b. split; [exact Hin| exact Ha].
Qed.
Lemma blk_NS b i : In b LB -> fst b <= i < fst b + PNBOA.gspan (snd b) -> NS i.
Proof.
  intros Hin Hi. destruct (HBA b Hin) as (Bn & B16 & (B0 & B1 & B2)).
  pose proof (PNBOA.gspan_ge (snd b) ltac:(lia)) as G.
  assert (SH : in_shadow_of (fst b) (snd b) (S i)).
  { apply gspan_shadow; [| exact Bn| exact Hi]. pose proof (Z.mod_divide (fst b) 16 ltac:(lia)) as [X _].
    destruct (X B16) as (q & Hq). rewrite Hq. replace (q * 16) with ((q * 2) * 8) by lia. apply Z_mod_mult. }
  unfold NS, L5CA.akept. pose proof (S_rng (fst b) ltac:(lia)) as [R1 R2]. pose proof (S_rng (fst b + snd b - 1) ltac:(lia)) as [R3 R4].
  destruct SH as [S1 S2].
  split; [lia|]. split.
  - unfold aclient, aclient_g. do 6 right. exists b. split; [exact Hin|]. split; [exact S1| exact S2].
  - intros r Hr X. rewrite Forall_forall in HWA. destruct r as (p & k). pose proof (HWA _ Hr) as (_ & AP & _). cbn [fst snd] in AP.
    unfold L5.in_rng in X. cbn [fst snd] in X. unfold SB, BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
Qed.
Lemma blk_NS' b i : In b LB -> fst b <= i < fst b + snd b -> NS i.
Proof. intros Hin Hi. apply (blk_NS b i Hin). destruct (HBA b Hin) as (Bn & _). pose proof (PNBOA.gspan_ge (snd b) ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Lemma vstr_keep_w o x : 0 <= o -> o + 24 <= 2 ^ 64 ->
  (forall i, o <= i < o + (match x with PM.VShort _ => 1 | PM.VLong _ _ _ => 24 end) -> NT i) ->
  (forall i, o <= i < o + 24 -> Y i) -> (forall i, o <= i < o + 24 -> NS i) ->
  (forall B m, In (B, m) (PM.vs_own x) -> forall i, B <= i < B + m -> Y i) ->
  (forall B m, In (B, m) (PM.vs_own x) -> forall i, B <= i < B + m -> NS i) ->
  PM.vstr_at segs accA M o x -> PM.vstr_at segs accA M' o x.
Proof.
  intros H1 H2 N YO NSo YB SB (D & C & R).
  split; [exact (PNMF.defined_dkr M M' o 24 (fun i Hi Di => DKY i (YO i Hi) Di) D)|].
  split; [exact (PMFA.accA_agree M M' o 24 (SHX o 24 NSo) C)|].
  destruct x as [n|c n p].
  - destruct R as (Hn & U). split; [exact Hn|]. apply (L5C.u8_at_agree segs M M'); [apply AGX; [lia|lia|exact N]|lia|lia|exact U].
  - pose proof (AGX o 24 H1 H2 N) as AG.
    destruct R as (W0 & W8 & W16 & Hn & Hc & Hev & DB & CB).
    assert (IB : In (p, c) (PM.vs_own (PM.VLong c n p))) by (cbn; auto).
    split; [apply (L5C.u64_at_agree segs M M'); [eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]|lia|lia|exact W0]|].
    split; [apply (L5C.u64_at_agree segs M M'); [eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]|lia|lia|exact W8]|].
    split; [apply (L5C.u64_at_agree segs M M'); [eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]|lia|lia|exact W16]|].
    split; [exact Hn|]. split; [exact Hc|]. split; [exact Hev|].
    split; [exact (PNMF.defined_dkr M M' p c (fun i Hi Di => DKY i (YB p c IB i Hi) Di) DB)|].
    exact (PMFA.accA_agree M M' p c (SHX p c (SB p c IB)) CB).
Qed.
End Keep.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Upd.
Local Ltac lu := unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *; lia.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable vp : Z.
Abbreviation bparser_at := (PNM.bparser_at segs A accA annA vp).
Variables (L : asan_layout) (ar : asan_run).
Variables (LBX : list (Z * Z)) (FF : list fframe) (sp scr : Z) (Wx : list L5.range) (M M' : word -> option byte).
Variables (op ois lo hi : Z) (s : PNM.bpst) (src src' : PM.srcst).
Let X : list (Z * Z) := PM.src_own src ++ PNM.brest_own s.
Let LB : list (Z * Z) := X ++ LBX.
Let W : list L5.range := PGS.W_srcG (op + PNM.OFF_SRC) ois src ++ Wx.

Hypothesis Hlay : lo <= op /\ op + PNM.PSIZE <= hi /\ lo <= ois /\ ois + 272 <= hi /\ hi <= 2 ^ 47 /\ 0 <= lo.
Hypothesis Hdis : op + PNM.PSIZE <= ois \/ ois + 272 <= op.
Hypothesis HFA : app_mem lo (hi - lo).
Hypothesis HFR : forall a, lo <= a < hi -> aclient L ar LB FF sp scr a /\ aclient L ar LB FF sp scr (S a).
Hypothesis HBA : forall b, In b LB -> 0 < snd b /\ fst b mod 16 = 0 /\ app_mem (fst b) (snd b).
Hypothesis HA : forall b, In b X -> apart (fst b) (snd b) lo (hi - lo).
Hypothesis HN : List.NoDup (map fst X).
Hypothesis HE : forall b1 b2, In b1 X -> In b2 X -> fst b1 <> fst b2 -> apart (fst b1) (snd b1) (fst b2) (snd b2).
Hypothesis HC : Forall (fun r => (apart (fst r) (snd r) lo (hi - lo) /\ (forall b, In b (PNM.brest_own s) -> apart (fst r) (snd r) (fst b) (snd b)) /\ app_mem (fst r) (snd r))
                                 \/ PNM.bwin op s (fst r) (snd r)) Wx.
Hypothesis HP : L5CA.ahpres L ar LB FF sp scr W M M'.
Hypothesis HOW : bparser_at M op ois (PNM.with_srcB s src).
Hypothesis HSRC : PM.src_fields_at segs accA M' (op + PNM.OFF_SRC) ois (ois + 16) src'.

Lemma chunk_in : In (PM.sr_qc src, PM.CHUNK) X.
Proof. unfold X, PM.src_own. left. reflexivity. Qed.
Lemma rest_in b : In b (PNM.brest_own s) -> In b X.
Proof. intros H. unfold X. apply in_or_app. right. exact H. Qed.
Lemma X_in b : In b X -> In b LB.
Proof. intros H. unfold LB. apply in_or_app. left. exact H. Qed.
Lemma bb_in b n c : PNM.b_bb s = PGV8.V8Blk b n c -> In (b, c) (PNM.brest_own s).
Proof. intros Eb. unfold PNM.brest_own. apply in_or_app. right. apply in_or_app. left. rewrite Eb. left. reflexivity. Qed.
Lemma nb_in c n p : PNM.b_nb s = PM.VLong c n p -> In (p, c) (PNM.brest_own s).
Proof. intros Eb. unfold PNM.brest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. rewrite Eb. left. reflexivity. Qed.
Lemma tb_in c n p : PNM.b_tb s = PM.VLong c n p -> In (p, c) (PNM.brest_own s).
Proof. intros Eb. unfold PNM.brest_own. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. rewrite Eb. left. reflexivity. Qed.
Lemma stk_in : In (PNM.b_sb s, PNM.BSZ * 2 ^ PNM.b_sk s) (PNM.brest_own s).
Proof. unfold PNM.brest_own, PNM.bvec_own. apply in_or_app. left. left. reflexivity. Qed.

(* [comment removed for export] *)
Lemma win_blk B m : In (B, m) (PGV8.v8_own (PNM.b_bb s) ++ PM.vs_own (PNM.b_nb s) ++ PM.vs_own (PNM.b_tb s)) -> In (B, m) (PNM.brest_own s) /\ B <> PNM.b_sb s.
Proof.
  intros Hin. assert (IR : In (B, m) (PNM.brest_own s)) by (unfold PNM.brest_own; apply in_or_app; right; exact Hin).
  split; [exact IR|]. intros E. subst B.
  unfold X, PM.src_own, PNM.brest_own, PNM.bvec_own in HN. cbn [map app] in HN.
  apply NoDup_cons_iff in HN as [_ ND]. apply NoDup_cons_iff in ND as [NI _]. apply NI. apply in_map_iff. exists (PNM.b_sb s, m). split; [reflexivity| exact Hin].
Qed.

(* [comment removed for export] *)
Lemma W_app : Forall (fun r => app_mem (fst r) (snd r)) W.
Proof.
  destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6).
  unfold W, PGS.W_srcG. apply Forall_app. split; [apply Forall_app; split|].
  - unfold PGS.W_srcfG. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (eapply app_mem_sub; [exact HFA| lu| lu| lu]).
  - apply Forall_cons; [| apply Forall_nil]. exact (proj2 (proj2 (HBA _ (X_in _ chunk_in)))).
  - eapply Forall_impl; [| exact HC]. intros r [(_ & _ & AP)|Hw]; [exact AP|].
    unfold PNM.bwin, PNM.sso_win, PNM.blk_win in Hw. destruct Hw as [(_ & K0 & W1 & W2)|[(_ & K0 & W1 & W2)|(B & m & Hin & K0 & W1 & W2)]].
    + eapply app_mem_sub; [exact HFA| lu| lu| lu].
    + eapply app_mem_sub; [exact HFA| lu| lu| lu].
    + destruct (win_blk B m Hin) as [IR _]. pose proof (HBA _ (X_in _ (rest_in _ IR))) as (_ & _ & AP). cbn [fst snd] in AP.
      eapply app_mem_sub; [exact AP| lia| lia| lia].
Qed.
Let NT := NT L ar LB FF sp scr W.
Let Y := Y L ar LB FF sp scr.
Let NS := NS L ar LB FF sp scr W.
Let AGXi := AGX L ar LB FF sp scr W M M' HP.
Let DKYi := DKY L ar LB FF sp scr W M M' HP.
Let SHXi := SHX L ar LB FF sp scr W M M' HP.

(* [comment removed for export] *)
Definition named (a : Z) : Prop :=
  op <= a < op + PNM.PSIZE /\ ~ (op + 272 <= a < op + 312)
  /\ ((exists n, PNM.b_nb s = PM.VShort n) -> ~ (op + PNM.OFF_NB + 1 <= a < op + PNM.OFF_NB + 24))
  /\ ((exists n, PNM.b_tb s = PM.VShort n) -> ~ (op + PNM.OFF_TB + 1 <= a < op + PNM.OFF_TB + 24)).
Lemma named_NT a : named a -> NT a.
Proof.
  intros (Ha & Hs & Hnb & Htb). destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6). unfold PNM.PSIZE, PNM.OFF_NB, PNM.OFF_TB in *.
  apply (frame_NT L ar LB FF sp scr W lo hi HFR HFA a ltac:(lia)).
  unfold W, PGS.W_srcG. apply outside_app; [apply outside_app|].
  - intros r Hr. pose proof Hr as Hr'. unfold PGS.W_srcfG, PNM.OFF_SRC in Hr'. unfold L5.in_rng.
    destruct Hr' as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia.
  - apply outside_cons; [|apply outside_nil]. unfold L5.in_rng. cbn [fst snd].
    pose proof (HA _ chunk_in) as Hap. unfold apart in Hap. cbn [fst snd] in Hap. lia.
  - apply outside_Forall. eapply Forall_impl; [|exact HC]. intros r [(Hap & _)|Hw]; unfold L5.in_rng.
    + unfold apart in Hap. lia.
    + unfold PNM.bwin, PNM.sso_win, PNM.blk_win in Hw. destruct Hw as [((n & En) & W0 & W1 & W2)|[((n & En) & W0 & W1 & W2)|(B & m & Hin & W0 & W1 & W2)]].
      * specialize (Hnb (ex_intro _ n En)). unfold PNM.OFF_NB in *. lia.
      * specialize (Htb (ex_intro _ n En)). unfold PNM.OFF_TB in *. lia.
      * destruct (win_blk B m Hin) as [IR _]. pose proof (HA _ (rest_in _ IR)) as Hap. unfold apart in Hap. cbn [fst snd] in Hap. lia.
Qed.
Lemma named_rng a0 b0 : op <= a0 -> b0 <= op + PNM.PSIZE -> (b0 <= op + 272 \/ op + 312 <= a0) -> b0 <= op + PNM.OFF_NB ->
  forall i, a0 <= i < b0 -> NT i.
Proof. intros A1 A2 A3 A4 i Hi. apply named_NT. unfold named. unfold PNM.PSIZE, PNM.OFF_NB, PNM.OFF_TB in *. repeat split; try lia; intros _; lia. Qed.

(* [comment removed for export] *)
Lemma stk_NT a : PNM.b_sb s <= a < PNM.b_sb s + PNM.BSZ * 2 ^ PNM.b_sk s -> NT a.
Proof.
  intros Ha. pose proof (rest_in _ stk_in) as SX. apply (blk_NT L ar LB FF sp scr W HBA _ a (X_in _ SX) Ha).
  destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6). pose proof (HA _ SX) as Hapf. cbn [fst snd] in Hapf. unfold apart in Hapf.
  assert (HQ : PM.sr_qc src <> PNM.b_sb s).
  { unfold X, PM.src_own, PNM.brest_own, PNM.bvec_own in HN. cbn [map app] in HN. apply NoDup_cons_iff in HN as [NI _]. intros E0. apply NI. left. symmetry. exact E0. }
  unfold W, PGS.W_srcG. apply outside_app; [apply outside_app|].
  - intros r Hr. pose proof Hr as Hr'. unfold PGS.W_srcfG, PNM.OFF_SRC in Hr'. unfold L5.in_rng. unfold PNM.PSIZE in *.
    destruct Hr' as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia.
  - apply outside_cons; [|apply outside_nil]. unfold L5.in_rng. cbn [fst snd].
    pose proof (HE _ _ chunk_in SX HQ) as Hap. unfold apart in Hap. cbn [fst snd] in Hap. lia.
  - apply outside_Forall. eapply Forall_impl; [|exact HC]. intros r [(_ & Hapb & _)|Hw]; unfold L5.in_rng.
    + pose proof (Hapb _ stk_in) as H'. unfold apart in H'. cbn [fst snd] in H'. lia.
    + unfold PNM.PSIZE in *. unfold PNM.bwin, PNM.sso_win, PNM.blk_win in Hw.
      destruct Hw as [(_ & W0 & W1 & W2)|[(_ & W0 & W1 & W2)|(B & m & Hin & W0 & W1 & W2)]].
      * unfold PNM.OFF_NB in *. lia.
      * unfold PNM.OFF_TB in *. lia.
      * destruct (win_blk B m Hin) as [IR HB]. pose proof (HE _ _ (rest_in _ IR) SX HB) as H'. unfold apart in H'. cbn [fst snd] in H'. lia.
Qed.

(* [comment removed for export] *)
Theorem src_owner_upd : bparser_at M' op ois (PNM.with_srcB s src').
Proof.
  destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6).
  pose proof HOW as PA. pose proof HOW as (_ & _ & _ & M8 & M9 & _ & _ & _ & _ & _ & _ & BB & NB & TB & STK & M01 & D01).
  cbn [PNM.with_srcB PNM.b_more PNM.b_done PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk] in M8, M9, BB, NB, TB, STK, M01, D01.
  pose proof (HBA _ (X_in _ (rest_in _ stk_in))) as (_ & _ & (Sb0 & _ & Sb2)). cbn [fst snd] in Sb0, Sb2.
  apply (PNBOA.bparser_at_xfer segs A vp M M' NT Y NS AGXi DKYi SHXi op ois (PNM.with_srcB s src));
    cbn [PNM.with_srcB PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
  - lia.
  - lu.
  - exact PA.
  - intros i Hi. apply (frame_Y L ar LB FF sp scr lo hi HFR HFA). lu.
  - intros i Hi. apply (frame_NS L ar LB FF sp scr W lo hi W_app HFR HFA). lu.
  - apply named_rng; lu.
  - apply named_rng; lu.
  - apply named_rng; lu.
  - apply named_rng; lu.
  - apply (L5C.u8_at_agree segs M M'); [apply AGXi; [lu|lu| apply named_rng; lu]|lu|lu| exact M8].
  - apply (L5C.u8_at_agree segs M M'); [apply AGXi; [lu|lu| apply named_rng; lu]|lu|lu| exact M9].
  - exact M01.
  - exact D01.
  - exact HSRC.
  - apply (PNBOA.v8_keep_x segs M M' NT Y NS AGXi DKYi SHXi); [lu|lu| | | | | exact BB].
    + intros i Hi. apply named_NT. unfold named. unfold PNM.PSIZE, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB in *. repeat split; try lia; intros _; lia.
    + intros i Hi. apply (frame_NS L ar LB FF sp scr W lo hi W_app HFR HFA). lu.
    + intros B m Hin i Hi. destruct (PNM.b_bb s) as [|b0 n0 c0] eqn:Eb; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as <- <-.
      apply (blk_Y L ar LB FF sp scr HBA (b0, c0) i (X_in _ (rest_in _ (bb_in _ _ _ Eb)))). cbn [fst snd]. lia.
    + intros B m Hin i Hi. destruct (PNM.b_bb s) as [|b0 n0 c0] eqn:Eb; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as <- <-.
      apply (blk_NS L ar LB FF sp scr W W_app HBA (b0, c0) i (X_in _ (rest_in _ (bb_in _ _ _ Eb)))). cbn [fst snd]. exact Hi.
  - apply (vstr_keep_w segs L ar LB FF sp scr W M M' HP); [lu|lu| | | | | | exact NB].
    + intros i Hi. apply named_NT. unfold named. unfold PNM.PSIZE, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB in *.
      destruct (PNM.b_nb s) as [n0|c0 n0 p0] eqn:Enb.
      * split; [lia|]. split; [lia|]. split; intros _; lia.
      * split; [lia|]. split; [lia|]. split; [intros (n1 & En1); discriminate En1| intros _; lia].
    + intros i Hi. apply (frame_Y L ar LB FF sp scr lo hi HFR HFA). lu.
    + intros i Hi. apply (frame_NS L ar LB FF sp scr W lo hi W_app HFR HFA). lu.
    + intros B m Hin i Hi. destruct (PNM.b_nb s) as [n0|c0 n0 p0] eqn:Eb; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as <- <-.
      apply (blk_Y L ar LB FF sp scr HBA (p0, c0) i (X_in _ (rest_in _ (nb_in _ _ _ Eb)))). cbn [fst snd]. lia.
    + intros B m Hin i Hi. destruct (PNM.b_nb s) as [n0|c0 n0 p0] eqn:Eb; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as <- <-.
      apply (blk_NS' L ar LB FF sp scr W W_app HBA (p0, c0) i (X_in _ (rest_in _ (nb_in _ _ _ Eb)))). cbn [fst snd]. exact Hi.
  - apply (vstr_keep_w segs L ar LB FF sp scr W M M' HP); [lu|lu| | | | | | exact TB].
    + intros i Hi. apply named_NT. unfold named. unfold PNM.PSIZE, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB in *.
      destruct (PNM.b_tb s) as [n0|c0 n0 p0] eqn:Etb.
      * split; [lia|]. split; [lia|]. split; intros _; lia.
      * split; [lia|]. split; [lia|]. split; [intros _; lia| intros (n1 & En1); discriminate En1].
    + intros i Hi. apply (frame_Y L ar LB FF sp scr lo hi HFR HFA). lu.
    + intros i Hi. apply (frame_NS L ar LB FF sp scr W lo hi W_app HFR HFA). lu.
    + intros B m Hin i Hi. destruct (PNM.b_tb s) as [n0|c0 n0 p0] eqn:Eb; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as <- <-.
      apply (blk_Y L ar LB FF sp scr HBA (p0, c0) i (X_in _ (rest_in _ (tb_in _ _ _ Eb)))). cbn [fst snd]. lia.
    + intros B m Hin i Hi. destruct (PNM.b_tb s) as [n0|c0 n0 p0] eqn:Eb; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as <- <-.
      apply (blk_NS' L ar LB FF sp scr W W_app HBA (p0, c0) i (X_in _ (rest_in _ (tb_in _ _ _ Eb)))). cbn [fst snd]. exact Hi.
  - apply (PNBOA.bvec_keep_x segs M M' NT NS AGXi SHXi); [lu|lu| lia| lia| | | | exact STK].
    + intros i Hi. apply named_NT. unfold named. unfold PNM.PSIZE, PNM.OFF_STK, PNM.OFF_NB, PNM.OFF_TB in *. repeat split; try lia; intros _; lia.
    + intros i Hi. apply stk_NT. exact Hi.
    + intros i Hi. apply (blk_NS' L ar LB FF sp scr W W_app HBA _ i (X_in _ (rest_in _ stk_in))). cbn [fst snd]. exact Hi.
Qed.
End Upd.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BUpd.
Local Ltac lu := unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *; lia.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable vp : Z.
Abbreviation bparser_at := (PNM.bparser_at segs A accA annA vp).
Variables (L : asan_layout) (ar : asan_run).
Variables (LBX OB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (Wx : list L5.range) (M M' : word -> option byte).
Variables (op ois lo hi ob : Z) (s : PNM.bpst).
(* [comment removed for export] *)
Let LB : list (Z * Z) := OB ++ LBX.
Let W : list L5.range := PGS.W_srcfG (op + PNM.OFF_SRC) ois ++ [(ob, 24)] ++ Wx.

Hypothesis Hlay : lo <= op /\ op + PNM.PSIZE <= hi /\ lo <= ois /\ ois + 272 <= hi /\ hi <= 2 ^ 47 /\ 0 <= lo.
Hypothesis Hdis : op + PNM.PSIZE <= ois \/ ois + 272 <= op.
Hypothesis Hob : ob = op + PNM.OFF_TB \/ ob = op + PNM.OFF_BB.
Hypothesis HFA : app_mem lo (hi - lo).
Hypothesis HFR : forall a, lo <= a < hi -> aclient L ar LB FF sp scr a /\ aclient L ar LB FF sp scr (S a).
Hypothesis HBA : forall b, In b LB -> 0 < snd b /\ fst b mod 16 = 0 /\ app_mem (fst b) (snd b).
Hypothesis HA : forall b, In b OB -> apart (fst b) (snd b) lo (hi - lo).
Hypothesis HC : Forall (fun r => apart (fst r) (snd r) lo (hi - lo) /\ (forall b, In b OB -> apart (fst r) (snd r) (fst b) (snd b)) /\ app_mem (fst r) (snd r)) Wx.
Hypothesis HP : L5CA.ahpres L ar LB FF sp scr W M M'.

Lemma OB_in b : In b OB -> In b LB.
Proof. intros H. unfold LB. apply in_or_app. left. exact H. Qed.
Lemma W_appB : Forall (fun r => app_mem (fst r) (snd r)) W.
Proof.
  destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6).
  unfold W. apply Forall_app. split; [| apply Forall_app; split].
  - unfold PGS.W_srcfG. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (eapply app_mem_sub; [exact HFA| lu| lu| lu]).
  - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold PNM.OFF_TB, PNM.OFF_BB in Hob. eapply app_mem_sub; [exact HFA| lu| lu| lu].
  - eapply Forall_impl; [| exact HC]. intros r (_ & _ & AP). exact AP.
Qed.
Let NT := NT L ar LB FF sp scr W.
Let Y := Y L ar LB FF sp scr.
Let NS := NS L ar LB FF sp scr W.
Let AGXi := AGX L ar LB FF sp scr W M M' HP.
Let DKYi := DKY L ar LB FF sp scr W M M' HP.
Let SHXi := SHX L ar LB FF sp scr W M M' HP.

(* [comment removed for export] *)
Lemma cellB_NT a : op <= a < op + PNM.PSIZE -> ~ (op + 272 <= a < op + 312) -> ~ (ob <= a < ob + 24) -> NT a.
Proof.
  intros Ha Hs Hb. destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6). unfold PNM.PSIZE in *.
  apply (frame_NT L ar LB FF sp scr W lo hi HFR HFA a ltac:(lia)).
  unfold W. apply outside_app; [|apply outside_app].
  - intros r Hr. pose proof Hr as Hr'. unfold PGS.W_srcfG, PNM.OFF_SRC in Hr'. unfold L5.in_rng.
    destruct Hr' as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia.
  - apply outside_cons; [|apply outside_nil]. unfold L5.in_rng. cbn [fst snd]. lia.
  - apply outside_Forall. eapply Forall_impl; [|exact HC]. intros r (Hap & _). unfold L5.in_rng. unfold apart in Hap. lia.
Qed.
Lemma cellB_rng a0 b0 : op <= a0 -> b0 <= op + PNM.PSIZE -> (b0 <= op + 272 \/ op + 312 <= a0) -> (b0 <= ob \/ ob + 24 <= a0) ->
  forall i, a0 <= i < b0 -> NT i.
Proof. intros B1 B2 B3 B4 i Hi. apply cellB_NT; lia. Qed.
Lemma blkB_NT b a : In b OB -> fst b <= a < fst b + snd b -> NT a.
Proof.
  intros Hin Ha. apply (blk_NT L ar LB FF sp scr W HBA b a (OB_in _ Hin) Ha).
  pose proof (HA _ Hin) as Hapf. unfold apart in Hapf. destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6). unfold PNM.PSIZE in *.
  unfold W. apply outside_app; [|apply outside_app].
  - intros r Hr. pose proof Hr as Hr'. unfold PGS.W_srcfG, PNM.OFF_SRC in Hr'. unfold L5.in_rng.
    destruct Hr' as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia.
  - apply outside_cons; [|apply outside_nil]. unfold L5.in_rng. cbn [fst snd]. unfold PNM.OFF_TB, PNM.OFF_BB in Hob. lia.
  - apply outside_Forall. eapply Forall_impl; [|exact HC]. intros r (_ & Hapb & _). unfold L5.in_rng.
    pose proof (Hapb _ Hin) as H'. unfold apart in H'. lia.
Qed.

(* [comment removed for export] *)
Theorem txt_owner_upd (src src' : PM.srcst) (tb tb' : PM.vstr) (tg tg' : Z) :
  ob = op + PNM.OFF_TB -> OB = PNM.txt_rest_own s ->
  PGS.tw_at (PNM.txt_owner segs A accA annA vp op ois lo hi s) M src tb tg OB ->
  PM.src_fields_at segs accA M' (op + PNM.OFF_SRC) ois (ois + 16) src' ->
  PM.vstr_at segs accA M' (op + PNM.OFF_TB) tb' -> PM.tb_ok tb' tg' ->
  PGS.tw_at (PNM.txt_owner segs A accA annA vp op ois lo hi s) M' src' tb' tg' OB.
Proof.
  intros Eob EOB (PA & _ & _) SRC' TB' TBOK. cbn [PNM.txt_owner PGS.tw_at].
  split; [|split; [exact TBOK| exact EOB]].
  destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6).
  assert (HBB : forall b n c, PNM.b_bb s = PGV8.V8Blk b n c -> In (b, c) OB).
  { intros b n c Eb. rewrite EOB. unfold PNM.txt_rest_own. apply in_or_app. right. apply in_or_app. left. rewrite Eb. left. reflexivity. }
  assert (HNB : forall c n p, PNM.b_nb s = PM.VLong c n p -> In (p, c) OB).
  { intros c n p Eb. rewrite EOB. unfold PNM.txt_rest_own. apply in_or_app. right. apply in_or_app. right. rewrite Eb. left. reflexivity. }
  assert (HSB : In (PNM.b_sb s, PNM.BSZ * 2 ^ PNM.b_sk s) OB).
  { rewrite EOB. unfold PNM.txt_rest_own, PNM.bvec_own. apply in_or_app. left. left. reflexivity. }
  pose proof (HBA _ (OB_in _ HSB)) as (_ & _ & (Sb0 & _ & Sb2)). cbn [fst snd] in Sb0, Sb2.
  pose proof PA as (_ & _ & _ & M8 & M9 & _ & _ & _ & _ & _ & _ & BB & NB & _ & STK & M01 & D01).
  cbn [PNM.with_src_tb PNM.b_more PNM.b_done PNM.b_bb PNM.b_nb PNM.b_sb PNM.b_sk PNM.b_stk] in M8, M9, BB, NB, STK, M01, D01.
  apply (PNBOA.bparser_at_xfer segs A vp M M' NT Y NS AGXi DKYi SHXi op ois (PNM.with_src_tb s src tb tg));
    cbn [PNM.with_src_tb PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk PNM.b_tg].
  - lia.
  - lu.
  - exact PA.
  - intros i Hi. apply (frame_Y L ar LB FF sp scr lo hi HFR HFA). lu.
  - intros i Hi. apply (frame_NS L ar LB FF sp scr W lo hi W_appB HFR HFA). lu.
  - apply cellB_rng; lu.
  - apply cellB_rng; lu.
  - apply cellB_rng; lu.
  - apply cellB_rng; lu.
  - apply (L5C.u8_at_agree segs M M'); [apply AGXi; [lu|lu| apply cellB_rng; lu]|lu|lu| exact M8].
  - apply (L5C.u8_at_agree segs M M'); [apply AGXi; [lu|lu| apply cellB_rng; lu]|lu|lu| exact M9].
  - exact M01.
  - exact D01.
  - exact SRC'.
  - apply (PNBOA.v8_keep_x segs M M' NT Y NS AGXi DKYi SHXi); [lu|lu| apply cellB_rng; lu| | | | exact BB].
    + intros i Hi. apply (frame_NS L ar LB FF sp scr W lo hi W_appB HFR HFA). lu.
    + intros B m Hin i Hi. destruct (PNM.b_bb s) as [|b0 n0 c0] eqn:Eb; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as <- <-.
      apply (blk_Y L ar LB FF sp scr HBA (b0, c0) i (OB_in _ (HBB _ _ _ ltac:(first [exact Eb | reflexivity])))). cbn [fst snd]. lia.
    + intros B m Hin i Hi. destruct (PNM.b_bb s) as [|b0 n0 c0] eqn:Eb; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as <- <-.
      apply (blk_NS L ar LB FF sp scr W W_appB HBA (b0, c0) i (OB_in _ (HBB _ _ _ ltac:(first [exact Eb | reflexivity])))). cbn [fst snd]. exact Hi.
  - apply (vstr_keep_w segs L ar LB FF sp scr W M M' HP); [lu|lu| | | | | | exact NB].
    + destruct (PNM.b_nb s) as [n0|c0 n0 p0]; apply cellB_rng; lu.
    + intros i Hi. apply (frame_Y L ar LB FF sp scr lo hi HFR HFA). lu.
    + intros i Hi. apply (frame_NS L ar LB FF sp scr W lo hi W_appB HFR HFA). lu.
    + intros B m Hin i Hi. destruct (PNM.b_nb s) as [n0|c0 n0 p0] eqn:Eb; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as <- <-.
      apply (blk_Y L ar LB FF sp scr HBA (p0, c0) i (OB_in _ (HNB _ _ _ ltac:(first [exact Eb | reflexivity])))). cbn [fst snd]. lia.
    + intros B m Hin i Hi. destruct (PNM.b_nb s) as [n0|c0 n0 p0] eqn:Eb; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as <- <-.
      apply (blk_NS' L ar LB FF sp scr W W_appB HBA (p0, c0) i (OB_in _ (HNB _ _ _ ltac:(first [exact Eb | reflexivity])))). cbn [fst snd]. exact Hi.
  - exact TB'.
  - apply (PNBOA.bvec_keep_x segs M M' NT NS AGXi SHXi); [lu|lu| lia| lia| apply cellB_rng; lu| | | exact STK].
    + intros i Hi. apply (blkB_NT _ i HSB). cbn [fst snd]. exact Hi.
    + intros i Hi. apply (blk_NS' L ar LB FF sp scr W W_appB HBA _ i (OB_in _ HSB)). cbn [fst snd]. exact Hi.
Qed.

(* [comment removed for export] *)
Theorem vec_owner_upd (src src' : PM.srcst) (x x' : PGV8.v8) (g g' : Z) :
  ob = op + PNM.OFF_BB -> OB = PNM.vec_rest_own s ->
  PGV8.vw_at (PNM.vec_owner segs A accA annA vp op ois lo hi s) M src x g OB ->
  PM.src_fields_at segs accA M' (op + PNM.OFF_SRC) ois (ois + 16) src' ->
  PGV8.v8_at segs accA annA M' (op + PNM.OFF_BB) x' -> PGV8.v8_ok x' g' ->
  PGV8.vw_at (PNM.vec_owner segs A accA annA vp op ois lo hi s) M' src' x' g' OB.
Proof.
  intros Eob EOB (PA & _ & _) SRC' BB' V8OK. cbn [PNM.vec_owner PGV8.vw_at].
  split; [|split; [exact V8OK| exact EOB]].
  destruct Hlay as (H1 & H2 & H3 & H4 & H5 & H6).
  assert (HNB : forall c n p, PNM.b_nb s = PM.VLong c n p -> In (p, c) OB).
  { intros c n p Eb. rewrite EOB. unfold PNM.vec_rest_own. apply in_or_app. right. apply in_or_app. left. rewrite Eb. left. reflexivity. }
  assert (HTB : forall c n p, PNM.b_tb s = PM.VLong c n p -> In (p, c) OB).
  { intros c n p Eb. rewrite EOB. unfold PNM.vec_rest_own. apply in_or_app. right. apply in_or_app. right. rewrite Eb. left. reflexivity. }
  assert (HSB : In (PNM.b_sb s, PNM.BSZ * 2 ^ PNM.b_sk s) OB).
  { rewrite EOB. unfold PNM.vec_rest_own, PNM.bvec_own. apply in_or_app. left. left. reflexivity. }
  pose proof (HBA _ (OB_in _ HSB)) as (_ & _ & (Sb0 & _ & Sb2)). cbn [fst snd] in Sb0, Sb2.
  pose proof PA as (_ & _ & _ & M8 & M9 & _ & _ & _ & _ & _ & _ & _ & NB & TB & STK & M01 & D01).
  cbn [PNM.with_src_bb PNM.b_more PNM.b_done PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk] in M8, M9, NB, TB, STK, M01, D01.
  apply (PNBOA.bparser_at_xfer segs A vp M M' NT Y NS AGXi DKYi SHXi op ois (PNM.with_src_bb s src x g));
    cbn [PNM.with_src_bb PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk PNM.b_bg].
  - lia.
  - lu.
  - exact PA.
  - intros i Hi. apply (frame_Y L ar LB FF sp scr lo hi HFR HFA). lu.
  - intros i Hi. apply (frame_NS L ar LB FF sp scr W lo hi W_appB HFR HFA). lu.
  - apply cellB_rng; lu.
  - apply cellB_rng; lu.
  - apply cellB_rng; lu.
  - apply cellB_rng; lu.
  - apply (L5C.u8_at_agree segs M M'); [apply AGXi; [lu|lu| apply cellB_rng; lu]|lu|lu| exact M8].
  - apply (L5C.u8_at_agree segs M M'); [apply AGXi; [lu|lu| apply cellB_rng; lu]|lu|lu| exact M9].
  - exact M01.
  - exact D01.
  - exact SRC'.
  - exact BB'.
  - apply (vstr_keep_w segs L ar LB FF sp scr W M M' HP); [lu|lu| | | | | | exact NB].
    + destruct (PNM.b_nb s) as [n0|c0 n0 p0]; apply cellB_rng; lu.
    + intros i Hi. apply (frame_Y L ar LB FF sp scr lo hi HFR HFA). lu.
    + intros i Hi. apply (frame_NS L ar LB FF sp scr W lo hi W_appB HFR HFA). lu.
    + intros B m Hin i Hi. destruct (PNM.b_nb s) as [n0|c0 n0 p0] eqn:Eb; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as <- <-.
      apply (blk_Y L ar LB FF sp scr HBA (p0, c0) i (OB_in _ (HNB _ _ _ ltac:(first [exact Eb | reflexivity])))). cbn [fst snd]. lia.
    + intros B m Hin i Hi. destruct (PNM.b_nb s) as [n0|c0 n0 p0] eqn:Eb; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as <- <-.
      apply (blk_NS' L ar LB FF sp scr W W_appB HBA (p0, c0) i (OB_in _ (HNB _ _ _ ltac:(first [exact Eb | reflexivity])))). cbn [fst snd]. exact Hi.
  - apply (vstr_keep_w segs L ar LB FF sp scr W M M' HP); [lu|lu| | | | | | exact TB].
    + destruct (PNM.b_tb s) as [n0|c0 n0 p0]; apply cellB_rng; lu.
    + intros i Hi. apply (frame_Y L ar LB FF sp scr lo hi HFR HFA). lu.
    + intros i Hi. apply (frame_NS L ar LB FF sp scr W lo hi W_appB HFR HFA). lu.
    + intros B m Hin i Hi. destruct (PNM.b_tb s) as [n0|c0 n0 p0] eqn:Eb; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as <- <-.
      apply (blk_Y L ar LB FF sp scr HBA (p0, c0) i (OB_in _ (HTB _ _ _ ltac:(first [exact Eb | reflexivity])))). cbn [fst snd]. lia.
    + intros B m Hin i Hi. destruct (PNM.b_tb s) as [n0|c0 n0 p0] eqn:Eb; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as <- <-.
      apply (blk_NS' L ar LB FF sp scr W W_appB HBA (p0, c0) i (OB_in _ (HTB _ _ _ ltac:(first [exact Eb | reflexivity])))). cbn [fst snd]. exact Hi.
  - apply (PNBOA.bvec_keep_x segs M M' NT NS AGXi SHXi); [lu|lu| lia| lia| apply cellB_rng; lu| | | exact STK].
    + intros i Hi. apply (blkB_NT _ i HSB). cbn [fst snd]. exact Hi.
    + intros i Hi. apply (blk_NS' L ar LB FF sp scr W W_appB HBA _ i (OB_in _ HSB)). cbn [fst snd]. exact Hi.
Qed.
End BUpd.
End PNOFA.
