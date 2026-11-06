(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmSpecs PmStep PmKeep PmFrame PmParSpecs PmParKit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMPK2.

Definition lp_w (p : PM.pstate) : Z :=
  if (Z.eqb (PM.ps_mode p) 3 || Z.eqb (PM.ps_mode p) 9 || Z.eqb (PM.ps_mode p) 10)%bool then - 1 - PM.ps_idx p
  else if (Z.eqb (PM.ps_mode p) 0 || Z.eqb (PM.ps_mode p) 1)%bool then 0
  else PM.ps_len p - PM.ps_idx p.
Definition lp_W (stk : list PM.pstate) : Z := fold_right (fun p w => lp_w p + w) 0 stk.
Definition lp_X (stk : list PM.pstate) : Z := (lp_W stk + 2 ^ 35) * 4096 + 2 * Z.of_nat (length stk) + PM.top_flag stk.
Definition lp_mu (s : PM.pst) (sm : PM.strm) : Z := PM.unread (PM.p_src s) sm * 2 ^ 50 + lp_X (PM.p_stk s).

Lemma lp_w_bound p : PM.pstate_ok p -> - 2 ^ 24 - 1 <= lp_w p <= 2 ^ 24.
Proof.
  unfold PM.pstate_ok, lp_w, PM.MAX_ITEMS, PM.mode_counted, PM.mode_indef, PM.mode_bottom.
  intros (_ & [(Hm & H1 & H2)|[(Hm & H1 & H2)|(Hm & H1 & H2)]]).
  - destruct Hm as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn; lia.
  - destruct Hm as [ -> | [ -> | -> ] ]; cbn; lia.
  - destruct Hm as [ -> | -> ]; cbn; lia.
Qed.
Lemma lp_W_app l1 l2 : lp_W (l1 ++ l2) = lp_W l1 + lp_W l2.
Proof. induction l1 as [|x l1 IH]; cbn; [reflexivity|]. unfold lp_W in IH |- *. cbn in IH |- *. rewrite IH. lia. Qed.
Lemma lp_W_one p : lp_W [p] = lp_w p.
Proof. unfold lp_W. cbn. lia. Qed.
Lemma lp_W_bound stk : Forall PM.pstate_ok stk -> (- 2 ^ 24 - 1) * Z.of_nat (length stk) <= lp_W stk <= 2 ^ 24 * Z.of_nat (length stk).
Proof.
  induction 1 as [|x l Hx Hl IH]; [cbn; lia|].
  pose proof (lp_w_bound x Hx). unfold lp_W in IH |- *. cbn [fold_right length]. rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma mode_flag_01 m : 0 <= PM.mode_flag m <= 1.
Proof. unfold PM.mode_flag. destruct (_ || _ || _ || _)%bool; lia. Qed.
Lemma top_flag_01 stk : 0 <= PM.top_flag stk <= 1.
Proof. unfold PM.top_flag. apply mode_flag_01. Qed.
Lemma shape_forall stk : PM.stack_shape stk -> Forall PM.pstate_ok stk.
Proof.
  intros (_ & _ & _ & _ & H). apply Forall_nth. intros i d Hi.
  rewrite (nth_indep stk d PM.ps_root Hi). apply H. exact Hi.
Qed.
Lemma lp_X_bound stk : PM.stack_shape stk -> 0 <= lp_X stk < 2 ^ 50.
Proof.
  intros SH. pose proof (lp_W_bound stk (shape_forall stk SH)) as B. pose proof SH as (_ & L2 & _).
  unfold PM.MAX_DEPTH in L2. pose proof (top_flag_01 stk). unfold lp_X. nia.
Qed.

Lemma lp_mu_lt_U s sm s' sm' :
  PM.stack_shape (PM.p_stk s) -> PM.stack_shape (PM.p_stk s') -> 0 <= PM.unread (PM.p_src s') sm' ->
  PM.unread (PM.p_src s') sm' < PM.unread (PM.p_src s) sm -> lp_mu s' sm' < lp_mu s sm.
Proof.
  intros S1 S2 U0 U1. pose proof (lp_X_bound _ S1). pose proof (lp_X_bound _ S2). unfold lp_mu. nia.
Qed.

Lemma lp_mu_pop s sm s' sm' top :
  PM.p_stk s = PM.p_stk s' ++ [top] -> lp_w top = 0 -> PM.unread (PM.p_src s') sm' <= PM.unread (PM.p_src s) sm -> lp_mu s' sm' < lp_mu s sm.
Proof.
  intros E W0 U1. unfold lp_mu, lp_X. rewrite E, lp_W_app, lp_W_one, W0, length_app. cbn [length].
  pose proof (top_flag_01 (PM.p_stk s' ++ [top])). pose proof (top_flag_01 (PM.p_stk s')). rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. nia.
Qed.

Lemma lp_mu_pushv s1 sm1 s2 sm2 s3 sm3 :
  PM.stack_shape (PM.p_stk s1) -> PM.stack_shape (PM.p_stk s3) ->
  lp_X (PM.p_stk s2) < lp_X (PM.p_stk s1) -> PM.unread (PM.p_src s2) sm2 <= PM.unread (PM.p_src s1) sm1 ->
  0 <= PM.unread (PM.p_src s3) sm3 -> PM.unread (PM.p_src s3) sm3 <= PM.unread (PM.p_src s2) sm2 ->
  PMSP.push_rel s2 s3 sm2 sm3 -> lp_mu s3 sm3 < lp_mu s1 sm1.
Proof.
  intros S1 S3 X21 U21 U30 U32 [E|(c & E & OK & I0 & NB & CT)].
  - unfold lp_mu. rewrite E. nia.
  - destruct (Z_lt_le_dec (PM.unread (PM.p_src s3) sm3) (PM.unread (PM.p_src s2) sm2)) as [LT|GE].
    + apply (lp_mu_lt_U s1 sm1 s3 sm3 S1 S3 U30). lia.
    + assert (NC : ~ PM.mode_counted (PM.ps_mode c)) by (intros X; specialize (CT X); lia).
      assert (WC : lp_w c = - 1).
      { pose proof OK as (_ & [(Hm & _)|[(Hm & _)|(Hm & _)]]); [contradiction| |contradiction].
        unfold lp_w, PM.mode_indef in *. rewrite I0. destruct Hm as [ -> | [ -> | -> ] ]; cbn; lia. }
      unfold lp_mu, lp_X in *. rewrite E, lp_W_app, lp_W_one, WC, length_app in *. cbn [length] in *. rewrite Nat2Z.inj_add in *.
      pose proof (top_flag_01 (PM.p_stk s2 ++ [c])). pose proof (top_flag_01 (PM.p_stk s2)). cbn [Z.of_nat Pos.of_succ_nat] in *. nia.
Qed.

Lemma lp_X_set_top pre p p' :
  lp_X (pre ++ [p']) = lp_X (pre ++ [p]) + 4096 * (lp_w p' - lp_w p) + PM.mode_flag (PM.ps_mode p') - PM.mode_flag (PM.ps_mode p).
Proof.
  unfold lp_X, PM.top_flag. rewrite !lp_W_app, !lp_W_one, !length_app, !last_last. cbn [length]. lia.
Qed.

Lemma nth_app_last (pre : list PM.pstate) p i d : (i < length (pre ++ [p]))%nat -> i <> length pre -> nth i (pre ++ [p]) d = nth i pre d.
Proof. intros H N. rewrite length_app in H. cbn in H. rewrite app_nth1 by lia. reflexivity. Qed.
Lemma nth_app_at (pre : list PM.pstate) p d : nth (length pre) (pre ++ [p]) d = p.
Proof. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.
Lemma stack_shape_set_top pre p p' :
  PM.stack_shape (pre ++ [p]) -> PM.pstate_ok p' -> (PM.mode_bottom (PM.ps_mode p) <-> PM.mode_bottom (PM.ps_mode p')) ->
  PM.stack_shape (pre ++ [p']).
Proof.
  intros (H1 & H2 & H3 & H4 & H5) OK' EB. unfold PM.stack_shape. rewrite !length_app in *. cbn [length] in *.
  split; [lia|]. split; [exact H2|].
  split.
  { destruct pre as [|x pre]; cbn in *; [apply EB; exact H3| exact H3]. }
  split.
  { intros i Hi. destruct (Nat.eq_dec i (length pre)) as [->|N].
    - rewrite nth_app_at. intros B. apply EB in B. specialize (H4 (length pre) ltac:(lia)). rewrite nth_app_at in H4. exact (H4 B).
    - rewrite nth_app_last by (try rewrite length_app; cbn; lia). specialize (H4 i ltac:(lia)). rewrite nth_app_last in H4 by (try rewrite length_app; cbn; lia). exact H4. }
  intros i Hi. destruct (Nat.eq_dec i (length pre)) as [->|N].
  - rewrite nth_app_at. exact OK'.
  - rewrite nth_app_last by (try rewrite length_app; cbn; lia). specialize (H5 i ltac:(lia)). rewrite nth_app_last in H5 by (try rewrite length_app; cbn; lia). exact H5.
Qed.
Lemma top_of_shape pre p : PM.stack_shape (pre ++ [p]) -> PM.pstate_ok p /\ ((pre = [] /\ PM.mode_bottom (PM.ps_mode p)) \/ (pre <> [] /\ ~ PM.mode_bottom (PM.ps_mode p))).
Proof.
  intros (H1 & H2 & H3 & H4 & H5). rewrite length_app in *. cbn [length] in *.
  split; [specialize (H5 (length pre) ltac:(lia)); rewrite nth_app_at in H5; exact H5|].
  destruct pre as [|x pre]; [left; split; [reflexivity| exact H3]|].
  right. split; [discriminate|]. specialize (H4 (length (x :: pre)) ltac:(cbn; lia)). rewrite nth_app_at in H4. exact H4.
Qed.

Section Kit.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.

Section Upd.
Variables M M' : word -> option byte.
Abbreviation ag := (L5C.agree_on M M').
Local Ltac u64x AG H := apply (L5C.u64_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact H].
Local Ltac u32x AG H := apply (PMF.u32_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact H].
Local Ltac u8x AG H := apply (L5C.u8_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact H].

Lemma vec_at_set_top v b k pre p p' :
  PM.vec_at segs T3 T4 M v b k (pre ++ [p]) -> 0 <= v -> v + 24 <= 2 ^ 64 -> 0 <= b -> b + 32 * 2 ^ k <= 2 ^ 64 ->
  ag v 24 -> ag b (32 * Z.of_nat (length pre)) ->
  ag (b + 32 * Z.of_nat (length pre) + 32) (32 * 2 ^ k - 32 * Z.of_nat (length pre) - 32) ->
  PMPK.dkr M M' (b + 32 * Z.of_nat (length pre)) 32 -> PM.pstate_at segs M' (b + 32 * Z.of_nat (length pre)) p' ->
  PM.vec_at segs T3 T4 M' v b k (pre ++ [p']).
Proof.
  intros (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL) Hv Hv' Hb Hb' AG0 AGL AGH DKT PT.
  unfold PM.vec_at. rewrite !length_app in *. cbn [length] in *. rewrite !Nat2Z.inj_add in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
  split; [u64x AG0 V0|]. split; [u64x AG0 V8|]. split; [u64x AG0 V16|].
  split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hal|].
  split.
  { intros i Hi. destruct (Z_lt_le_dec i (32 * Z.of_nat (length pre))) as [X|X]; [rewrite AGL by lia; apply DB; lia|].
    destruct (Z_lt_le_dec i (32 * Z.of_nat (length pre) + 32)) as [Y|Y].
    - replace (b + i) with (b + 32 * Z.of_nat (length pre) + (i - 32 * Z.of_nat (length pre))) by lia.
      apply DKT; [lia|]. replace (b + 32 * Z.of_nat (length pre) + (i - 32 * Z.of_nat (length pre))) with (b + i) by lia. apply DB; lia.
    - rewrite AGH by lia. apply DB; lia. }
  split; [exact I|]. split; [exact I|].
  intros i Hi.
  destruct (Nat.eq_dec i (length pre)) as [->|N]; [rewrite nth_app_at; exact PT|].
  rewrite nth_app_last by (try rewrite length_app; cbn; lia).
  specialize (EL i ltac:(lia)). rewrite nth_app_last in EL by (try rewrite length_app; cbn; lia).
  apply (PMF.pstate_at_agree segs M M'); [lia|lia| |exact EL].
  apply (L5C.agree_on_sub M M' b (32 * Z.of_nat (length pre))); [exact AGL|lia|lia].
Qed.

Lemma parser_top_upd op ois s pre p p' :
  PM.parser_at segs A T3 T4 M op ois s -> PM.p_stk s = pre ++ [p] -> 0 <= op -> op + 384 <= 2 ^ 64 -> ag op 384 ->
  PMPK.dkr M M' (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  0 <= PM.p_b s -> PM.p_b s + 32 * 2 ^ PM.p_k s <= 2 ^ 64 ->
  ag (PM.p_b s) (32 * Z.of_nat (length pre)) ->
  ag (PM.p_b s + 32 * Z.of_nat (length pre) + 32) (32 * 2 ^ PM.p_k s - 32 * Z.of_nat (length pre) - 32) ->
  PMPK.dkr M M' (PM.p_b s + 32 * Z.of_nat (length pre)) 32 -> PM.pstate_at segs M' (PM.p_b s + 32 * Z.of_nat (length pre)) p' ->
  (forall c n q, PM.p_tb s = PM.VLong c n q -> PMPK.dkr M M' q c) ->
  PM.parser_at segs A T3 T4 M' op ois
    (PM.PST (PM.p_more s) (PM.p_done s) (PM.p_depth s) (PM.p_src s) (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (pre ++ [p'])).
Proof.
  intros (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3) ES Ho Ho' AG DKC Hb Hb' AGL AGH DKT PT AGT.
  destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _).
  rewrite ES in VEC.
  unfold PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
  split; [u64x AG H0|].
  split; [intros i Hi; rewrite AG by lia; apply D; lia|].
  split; [exact I|]. split; [u8x AG H8|]. split; [u8x AG H9|]. split; [u32x AG H12|]. split; [u8x AG H16|]. split; [u32x AG H20|].
  split. { apply (PMF.nullis_at_agree segs A M M'); [lia| lia| eapply L5C.agree_on_sub; [exact AG|lia|lia]| exact NI]. }
  split.
  { split; [u64x AG F1|]. split; [u64x AG F2|].
    split. { apply (L5C.defined_agree M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]| exact F3]. }
    split; [u64x AG F4|]. split; [u64x AG F5|]. split; [u64x AG F6|]. split; [u64x AG F7|].
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [apply (PMPK.defined_dkr M M' _ _ DKC DC)|]. split; exact I. }
  split; [u32x AG H320|]. split; [u64x AG H328|]. split; [exact I|].
  split. { apply (PMPK.vstr_at_keep segs M M'); [lia| lia| eapply L5C.agree_on_sub; [exact AG|lia|lia]| exact AGT| exact TB]. }
  split. { apply (vec_at_set_top (op + 360) (PM.p_b s) (PM.p_k s) pre p p' VEC); [lia|lia|exact Hb|exact Hb'| eapply L5C.agree_on_sub; [exact AG|lia|lia]| exact AGL| exact AGH| exact DKT| exact PT]. }
  split; [exact B1|]. split; [exact B2| exact B3].
Qed.

Lemma parser_accept_upd op ois s :
  PM.parser_at segs A T3 T4 M op ois s -> 0 <= op -> op + 384 <= 2 ^ 64 ->
  ag op 8 -> ag (op + 10) 358 -> ag (op + 376) 8 -> PMPK.dkr M M' (op + 8) 2 -> PMPK.dkr M M' (op + 368) 8 ->
  L5.u8_at segs M' (op + 8) 0 -> L5.u8_at segs M' (op + 9) 1 -> L5.u64_at segs M' (op + 368) (PM.p_b s) ->
  PMPK.dkr M M' (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  0 <= PM.p_b s -> PM.p_b s + 32 * 2 ^ PM.p_k s <= 2 ^ 64 -> ag (PM.p_b s) (32 * 2 ^ PM.p_k s) ->
  (forall c n q, PM.p_tb s = PM.VLong c n q -> PMPK.dkr M M' q c) ->
  PM.parser_at segs A T3 T4 M' op ois (PM.PST 0 1 (PM.p_depth s) (PM.p_src s) (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) []).
Proof.
  intros (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3) Ho Ho' AG1 AG2 AG3 DK8 DK368 C8 C9 C368 DKC Hb Hb' AGV AGT.
  destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _).
  unfold PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
  assert (AG4 : forall a n, op + 10 <= a -> a + n <= op + 368 -> ag a n) by (intros a n X1 X2; eapply L5C.agree_on_sub; [exact AG2|lia|lia]).
  split; [u64x AG1 H0|].
  split. { intros i Hi. destruct (Z_lt_le_dec i 8) as [X|X]; [rewrite AG1 by lia; apply D; lia|].
           destruct (Z_lt_le_dec i 10) as [Y|Y]; [apply DK8; [lia| apply D; lia]|].
           destruct (Z_lt_le_dec i 368) as [Y2|Y2]; [rewrite AG2 by lia; apply D; lia|].
           destruct (Z_lt_le_dec i 376) as [Y3|Y3]; [apply DK368; [lia| apply D; lia]| rewrite AG3 by lia; apply D; lia]. }
  split; [exact I|]. split; [exact C8|]. split; [exact C9|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H12]|].
  split; [apply (L5C.u8_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H16]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H20]|].
  split. { apply (PMF.nullis_at_agree segs A M M'); [lia| lia| apply AG4; lia| exact NI]. }
  split.
  { split; [u64x AG2 F1|]. split; [u64x AG2 F2|].
    split. { apply (L5C.defined_agree M M'); [apply AG4; lia| exact F3]. }
    split; [u64x AG2 F4|]. split; [u64x AG2 F5|]. split; [u64x AG2 F6|]. split; [u64x AG2 F7|].
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [apply (PMPK.defined_dkr M M' _ _ DKC DC)|]. split; exact I. }
  split; [apply (PMF.u32_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H320]|]. split; [u64x AG2 H328|]. split; [exact I|].
  split. { apply (PMPK.vstr_at_keep segs M M'); [lia| lia| apply AG4; lia| exact AGT| exact TB]. }
  split.
  { destruct VEC as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL).
    split; [u64x AG2 V0|]. split; [replace (op + 360 + 8) with (op + 368) by lia; match goal with |- L5.u64_at _ _ _ ?x => replace x with (PM.p_b s) by (cbn; lia) end; exact C368|].
    split; [u64x AG3 V16|]. split; [exact Hk|]. split; [cbn [length Z.of_nat]; pose proof (PM.pow2_pos (PM.p_k s) ltac:(lia)); lia|].
    split; [exact Hal|]. split; [apply (L5C.defined_agree M M' _ _ AGV DB)|]. split; [exact I|]. split; [exact I|].
    intros i Hi. cbn in Hi. lia. }
  split; [left; reflexivity|]. split; [right; reflexivity| exact B3].
Qed.
End Upd.

Lemma pot_parser_nonneg (L : heap_layout) M op ois s :
  PM.parser_at segs A T3 T4 M op ois s -> PM.tb_ok (PM.p_tb s) (PM.p_tg s) -> 0 <= hl_k_per_malloc L -> 0 <= hl_b_overhead L ->
  0 <= fst (PM.pot_parser L s) /\ 0 <= snd (PM.pot_parser L s).
Proof.
  intros PA (T0 & T1 & T2) K0 B0.
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TB & VEC & _).
  pose proof VEC as (_ & _ & _ & Hk & _).
  unfold PM.pot_parser, PM.credit_add, PM.pot_stack, PM.pot_text. cbn [fst snd].
  assert (P2 : 2 ^ (PM.p_k s + 1) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
  assert (CAP : PM.vs_cap (PM.p_tb s) <= 2 ^ 27 - 1).
  { destruct (PM.p_tb s) as [n|c n q]; cbn [PM.vs_cap]; [lia|]. destruct TB as (_ & _ & _ & _ & _ & _ & (_ & C2) & _). lia. }
  split; nia.
Qed.
Lemma credit_keep_final cr cr1 p p1 : PMSP.credit_keep cr cr1 p p1 -> 0 <= fst p1 -> 0 <= snd p1 -> PMSP.credit_keep cr cr1 p PMSP.cr0.
Proof. unfold PMSP.credit_keep, PMSP.cr0. cbn [fst snd]. lia. Qed.
End Kit.

End PMPK2.
