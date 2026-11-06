(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

(* [comment removed for export] *)
Definition vsb_fresh (b : Z) : vsb_rec := VSBR 0 b 16 0 VSB_FLAGS_LIVE 0.

(* [comment removed for export] *)
Definition EXT_MAX : Z := 2^30 - 4096.

(* [comment removed for export] *)
Lemma vsb_extendsize_tight : forall sz, vsb_extendsize sz <= Z.max 4096 (sz + 4095).
Proof.
  intros sz. unfold vsb_extendsize. destruct (Z.ltb_spec sz 4096) as [Hlt|Hge].
  - cbn [vsb_dbl Z.mul Pos.mul].
    repeat (match goal with |- context [if ?a <? ?b then _ else _] => destruct (Z.ltb_spec a b); [|lia] end). lia.
  - pose proof (Z.div_mod (sz + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (sz + 4095) 4096 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)

Lemma vsb_extendsize_cap : forall sz, sz <= EXT_MAX -> vsb_extendsize sz < 2^30.
Proof. intros sz H. unfold EXT_MAX in H. pose proof (vsb_extendsize_tight sz). lia. Qed.

(* [comment removed for export] *)
Definition vsb_pot (x : vsb_rec) : Z := (Z.max (vb_size x) 61440 - 61440) / 4096.

(* [comment removed for export] *)

Lemma vsb_pot_mono : forall x y, vb_size x <= vb_size y -> vsb_pot x <= vsb_pot y.
Proof. intros x y H. unfold vsb_pot. apply Z.div_le_mono; lia. Qed.

Lemma vsb_pot_le : forall x, 0 <= vb_size x -> vsb_pot x <= vb_size x / 4096.
Proof. intros x H. unfold vsb_pot. apply Z.div_le_mono; lia. Qed.

Lemma vsb_pot_small : forall x, vb_size x <= 65535 -> vsb_pot x = 0.
Proof. intros x H. unfold vsb_pot. apply Z.div_small. lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vsb_pot_diff : forall x y, vb_size x <= vb_size y -> vsb_pot y - vsb_pot x <= (vb_size y - vb_size x) / 4096 + 1.
Proof.
  intros x y H. unfold vsb_pot.
  set (a := Z.max (vb_size x) 61440 - 61440). set (b := Z.max (vb_size y) 61440 - 61440).
  assert (AB : 0 <= a <= b /\ b - a <= vb_size y - vb_size x) by (subst a b; lia).
  pose proof (Z.div_mod a 4096 ltac:(lia)). pose proof (Z.mod_pos_bound a 4096 ltac:(lia)).
  pose proof (Z.div_mod b 4096 ltac:(lia)). pose proof (Z.mod_pos_bound b 4096 ltac:(lia)).
  pose proof (Z.div_mod (vb_size y - vb_size x) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (vb_size y - vb_size x) 4096 ltac:(lia)).
  nia.
Qed.

(* [comment removed for export] *)
Lemma vsb_extendsize_page : forall sz, 4096 <= sz -> exists k, vsb_extendsize sz = 4096 * k /\ sz <= 4096 * k.
Proof.
  intros sz H. unfold vsb_extendsize. destruct (Z.ltb_spec sz 4096) as [Hlt|Hge]; [lia|].
  exists ((sz + 4095) / 4096). pose proof (Z.div_mod (sz + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (sz + 4095) 4096 ltac:(lia)). lia.
Qed.

Lemma vsb_extendsize_small : forall sz, sz < 4096 -> vsb_extendsize sz <= 4096.
Proof.
  intros sz H. unfold vsb_extendsize. destruct (Z.ltb_spec sz 4096) as [Hlt|Hge]; [|lia].
  cbn [vsb_dbl Z.mul Pos.mul].
  repeat (match goal with |- context [if ?a <? ?b then _ else _] => destruct (Z.ltb_spec a b); [|lia] end). lia.
Qed.

(* [comment removed for export] *)
Lemma vsb_pot_secondary : forall vr nb addlen,
  0 <= vb_size vr -> 1 <= addlen -> kMaxPrimaryUser < vsb_extendsize (vb_size vr + addlen) ->
  vsb_pot vr + 1 <= vsb_pot (vsb_set_buf_size vr nb (vsb_extendsize (vb_size vr + addlen))).
Proof.
  intros vr nb addlen S0 A1 SEC. unfold kMaxPrimaryUser in SEC. unfold vsb_pot. cbn [vb_size vsb_set_buf_size].
  set (ns := vsb_extendsize (vb_size vr + addlen)) in *.
  destruct (Z.lt_ge_cases (vb_size vr + addlen) 4096) as [SM|PG].
  { exfalso. pose proof (vsb_extendsize_small _ SM). lia. }
  (first [ pose proof ((vsb_extendsize_page _ PG)) as dR_1; dex1 dR_1 as k; destruct dR_1 as [Ek Gk] | pose proof ((vsb_extendsize_page _ PG)) as dR_1; dand3 dR_1 as k Ek Gk | destruct (vsb_extendsize_page _ PG) as (k & Ek & Gk) ]). fold ns in Ek. rewrite Ek.
  assert (K16 : 16 <= k) by lia.
  replace (Z.max (4096 * k) 61440 - 61440) with (4096 * (k - 15)) by lia.
  rewrite Z.mul_comm, Z.div_mul by lia.
  destruct (Z.le_gt_cases (vb_size vr) 61440) as [LE|GT].
  - replace (Z.max (vb_size vr) 61440 - 61440) with 0 by lia. change (0 / 4096) with 0. lia.
  - replace (Z.max (vb_size vr) 61440) with (vb_size vr) by lia.
    assert ((vb_size vr - 61440) / 4096 < k - 15); [|lia].
    apply Z.div_lt_upper_bound; lia.
Qed.

(* [comment removed for export] *)
Lemma vsb_pot_credit : forall (c c' : Z) vr nb addlen,
  0 <= vb_size vr -> 1 <= addlen ->
  c' = c - (if Z.ltb kMaxPrimaryUser (vsb_extendsize (vb_size vr + addlen)) then 1 else 0) ->
  c - (vsb_pot (vsb_set_buf_size vr nb (vsb_extendsize (vb_size vr + addlen))) - vsb_pot vr) <= c' <= c.
Proof.
  intros c c' vr nb addlen S0 A1 E.
  pose proof (vsb_pot_mono vr (vsb_set_buf_size vr nb (vsb_extendsize (vb_size vr + addlen)))) as MO.
  cbn [vb_size vsb_set_buf_size] in MO.
  pose proof (vsb_extendsize_tight (vb_size vr + addlen)) as T0.
  assert (GE : vb_size vr <= vsb_extendsize (vb_size vr + addlen)).
  { unfold vsb_extendsize. destruct (Z.ltb_spec (vb_size vr + addlen) 4096) as [Hlt|Hge].
    - destruct (vsb_dbl_ge 9 16 (vb_size vr + addlen) ltac:(lia) ltac:(cbn; lia)). lia.
    - pose proof (Z.div_mod (vb_size vr + addlen + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (vb_size vr + addlen + 4095) 4096 ltac:(lia)). lia. }
  specialize (MO GE).
  destruct (Z.ltb_spec kMaxPrimaryUser (vsb_extendsize (vb_size vr + addlen))) as [SEC|PRI].
  - pose proof (vsb_pot_secondary vr nb addlen S0 A1 SEC). lia.
  - lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pvb_tab : list (Z * Z) :=
  [(16,32); (32,64); (64,96); (128,192); (256,320); (512,768); (1024,1536); (2048,3072); (4096,6144);
   (8192,12288); (12288,16384); (16384,24576); (20480,24576); (24576,32768); (28672,32768); (32768,49152);
   (36864,49152); (40960,49152); (45056,49152); (49152,65536); (53248,65536); (57344,65536); (61440,65536)].
Fixpoint pvb_sum (l : list (Z * Z)) (s : Z) : Z :=
  match l with [] => 0 | (t, c) :: l' => (if t <=? s then c else 0) + pvb_sum l' s end.
Definition PVB (s : Z) : Z := pvb_sum pvb_tab s.
Definition PVB_MAX : Z := 614336.
Definition vsb_ppot (x : vsb_rec) : Z := 64 + PVB (vb_size x).
Definition PPOT_CAP : Z := 64 + PVB_MAX.
Definition PRIM_ROOM : Z := 65536.
(* [comment removed for export] *)
Definition is_ladder (t : Z) : Prop := (exists k : nat, (k <= 8)%nat /\ t = 16 * 2 ^ Z.of_nat k) \/ (4096 <= t /\ t mod 4096 = 0).

Lemma pvb_sum_mono : forall l s s', s <= s' -> Forall (fun tc => 0 <= snd tc) l -> pvb_sum l s <= pvb_sum l s'.
Proof.
  induction l as [|[t c] l IH]; intros s s' LE NN; cbn; [lia|].
  inversion NN as [|x l0 C NN']; subst. cbn in C. specialize (IH s s' LE NN').
  destruct (Z.leb_spec t s), (Z.leb_spec t s'); lia.
Qed.
Lemma pvb_tab_nonneg : Forall (fun tc => 0 <= snd tc) pvb_tab.
Proof. unfold pvb_tab. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.
Lemma PVB_mono : forall s s', s <= s' -> PVB s <= PVB s'.
Proof. intros. unfold PVB. apply pvb_sum_mono; [lia| apply pvb_tab_nonneg]. Qed.
Lemma pvb_sum_nonneg : forall l s, Forall (fun tc => 0 <= snd tc) l -> 0 <= pvb_sum l s.
Proof.
  induction l as [|[t c] l IH]; intros s NN; cbn; [lia|].
  inversion NN as [|x l0 C NN']; subst. cbn in C. specialize (IH s NN'). destruct (Z.leb t s); lia.
Qed.
Lemma pvb_sum_above : forall l m s, Forall (fun tc => fst tc <= m) l -> m <= s -> pvb_sum l s = pvb_sum l m.
Proof.
  induction l as [|[t c] l IH]; intros m s BM LE; cbn; [reflexivity|].
  inversion BM as [|x l0 C BM']; subst. cbn in C. rewrite (IH m s BM' LE).
  destruct (Z.leb_spec t s), (Z.leb_spec t m); lia.
Qed.
Lemma pvb_tab_bounded : Forall (fun tc => fst tc <= 61440) pvb_tab.
Proof. unfold pvb_tab. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.
Lemma PVB_61440 : PVB 61440 = PVB_MAX.
Proof. vm_compute. reflexivity. Qed.
Lemma PVB_range : forall s, 0 <= PVB s <= PVB_MAX.
Proof.
  intros s. split.
  - unfold PVB. apply pvb_sum_nonneg. apply pvb_tab_nonneg.
  - destruct (Z.le_gt_cases s 61440) as [LE|GT].
    + rewrite <- PVB_61440. apply PVB_mono. exact LE.
    + unfold PVB. rewrite (pvb_sum_above pvb_tab 61440 s pvb_tab_bounded ltac:(lia)). fold (PVB 61440). rewrite PVB_61440. lia.
Qed.
Lemma PVB_16 : forall s, s <= 16 -> PVB s <= 32.
Proof. intros s H. eapply Z.le_trans; [apply (PVB_mono s 16 H)|]. replace (PVB 16) with 32 by reflexivity. lia. Qed.
Lemma vsb_ppot_fresh : forall b, vsb_ppot (vsb_fresh b) = 96.
Proof. intros b. reflexivity. Qed.
Lemma vsb_ppot_mono : forall x y, vb_size x <= vb_size y -> vsb_ppot x <= vsb_ppot y.
Proof. intros x y H. unfold vsb_ppot. pose proof (PVB_mono _ _ H). lia. Qed.
Lemma vsb_ppot_range : forall x, 64 <= vsb_ppot x <= PPOT_CAP.
Proof. intros x. unfold vsb_ppot, PPOT_CAP. pose proof (PVB_range (vb_size x)). lia. Qed.
Lemma vsb_ppot_set_len : forall x l, vsb_ppot (vsb_set_len x l) = vsb_ppot x.
Proof. intros. reflexivity. Qed.
Lemma vsb_ppot_set_flags : forall x f, vsb_ppot (vsb_set_flags x f) = vsb_ppot x.
Proof. intros. reflexivity. Qed.
Lemma vsb_ppot_size : forall x y, vb_size x = vb_size y -> vsb_ppot x = vsb_ppot y.
Proof. intros x y E. unfold vsb_ppot. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Lemma prim_cost_40 : prim_cost 40 = 64.
Proof. rewrite prim_cost_primary by (unfold kMaxPrimaryUser; lia). vm_compute. reflexivity. Qed.
Lemma prim_cost_16 : prim_cost 16 = 32.
Proof. rewrite prim_cost_primary by (unfold kMaxPrimaryUser; lia). vm_compute. reflexivity. Qed.
Lemma prim_cost_312 : prim_cost 312 = 384.
Proof. rewrite prim_cost_primary by (unfold kMaxPrimaryUser; lia). vm_compute. reflexivity. Qed.
Lemma pvb_tab_cost : Forall (fun tc => prim_cost (fst tc) = snd tc) pvb_tab.
Proof.
  unfold pvb_tab. repeat (apply Forall_cons; [cbn [fst snd]; rewrite prim_cost_primary by (unfold kMaxPrimaryUser; lia); vm_compute; reflexivity|]).
  apply Forall_nil.
Qed.

(* [comment removed for export] *)
Lemma vsb_dbl_pow : forall k ns sz, (exists j : nat, ns = 16 * 2 ^ Z.of_nat j /\ (j + k <= 9)%nat) ->
  exists j : nat, vsb_dbl k ns sz = 16 * 2 ^ Z.of_nat j /\ (j <= 9)%nat.
Proof.
  induction k as [|k IH]; intros ns sz (j & E & B); cbn.
  - exists j. split; [exact E| lia].
  - destruct (Z.ltb ns sz).
    + apply IH. exists (S j). split; [| lia]. rewrite E. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
    + exists j. split; [exact E| lia].
Qed.
Lemma vsb_extendsize_ladder : forall sz, 1 <= sz -> is_ladder (vsb_extendsize sz).
Proof.
  intros sz H. unfold vsb_extendsize. destruct (Z.ltb_spec sz 4096) as [LT|GE].
  - destruct (vsb_dbl_pow 9 16 sz ltac:(exists 0%nat; split; [reflexivity| lia])) as (j & E & B).
    assert (J : (j <= 8)%nat \/ j = 9%nat) by lia. destruct J as [J|J].
    + left. exists j. split; [exact J| exact E].
    + right. rewrite E, J. cbn. split; [lia| reflexivity].
  - right. pose proof (Z.div_mod (sz + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (sz + 4095) 4096 ltac:(lia)).
    split; [nia|]. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Lemma pvb_sum_step : forall l s ns, 0 <= s < ns -> Forall (fun tc => 0 <= snd tc) l ->
  Forall (fun tc => prim_cost (fst tc) = snd tc) l ->
  pvb_sum l s + (if existsb (fun tc => fst tc =? ns) l then prim_cost ns else 0) <= pvb_sum l ns.
Proof.
  induction l as [|[t c] l IH]; intros s ns LT NN CC; cbn; [lia|].
  inversion NN as [|x l0 C0 NN']; subst. inversion CC as [|x l0 C1 CC']; subst. cbn in C0, C1.
  pose proof (proj1 (prim_cost_range ns ltac:(lia))) as PR.
  specialize (IH s ns LT NN' CC').
  destruct (Z.eqb_spec t ns) as [E|NE].
  - subst t. cbn. rewrite C1 in *. destruct (Z.leb_spec ns s); [lia|]. rewrite Z.leb_refl.
    destruct (existsb _ l); lia.
  - cbn. destruct (Z.leb_spec t s), (Z.leb_spec t ns); try lia.
Qed.
Lemma ladder_cases : forall t, is_ladder t -> t < 65536 ->
  existsb (fun tc => fst tc =? t) pvb_tab = true.
Proof.
  intros t [(k & K & E)|(GE & MD)] LT.
  - subst t. destruct k as [|[|[|[|[|[|[|[|[|k]]]]]]]]]; try reflexivity. lia.
  - pose proof (Z.div_mod t 4096 ltac:(lia)) as D. rewrite MD, Z.add_0_r in D.
    assert (R : 1 <= t / 4096 <= 15) by lia.
    assert (C : forall q, 1 <= q <= 15 -> existsb (fun tc => fst tc =? 4096 * q) pvb_tab = true).
    { intros q Hq. assert (Q : q = 1 \/ q = 2 \/ q = 3 \/ q = 4 \/ q = 5 \/ q = 6 \/ q = 7 \/ q = 8 \/ q = 9 \/ q = 10 \/ q = 11 \/ q = 12 \/ q = 13 \/ q = 14 \/ q = 15) by lia.
      repeat (destruct Q as [->|Q]; [reflexivity|]). rewrite Q. reflexivity. }
    rewrite D. apply C. exact R.
Qed.
Lemma PVB_step : forall s ns, 0 <= s < ns -> is_ladder ns -> PVB s + prim_cost ns <= PVB ns.
Proof.
  intros s ns R LD. unfold PVB.
  pose proof (pvb_sum_step pvb_tab s ns ltac:(lia) pvb_tab_nonneg pvb_tab_cost) as ST.
  destruct (Z.lt_ge_cases ns 65536) as [LT|GE].
  - rewrite (ladder_cases ns LD LT) in ST. exact ST.
  - assert (Z0 : prim_cost ns = 0) by (apply prim_cost_secondary; unfold kMaxPrimaryUser; lia).
    rewrite Z0 in *. pose proof (pvb_sum_mono pvb_tab s ns ltac:(lia) pvb_tab_nonneg). lia.
Qed.
(* [comment removed for export] *)
Lemma vsb_ppot_credit : forall (c c' : Z) vr nb addlen,
  0 <= vb_size vr -> 1 <= addlen ->
  c' = c - prim_cost (vsb_extendsize (vb_size vr + addlen)) ->
  c - (vsb_ppot (vsb_set_buf_size vr nb (vsb_extendsize (vb_size vr + addlen))) - vsb_ppot vr) <= c' <= c.
Proof.
  intros c c' vr nb addlen S0 A1 E. unfold vsb_ppot. cbn [vb_size vsb_set_buf_size].
  assert (GE : vb_size vr < vsb_extendsize (vb_size vr + addlen)).
  { unfold vsb_extendsize. destruct (Z.ltb_spec (vb_size vr + addlen) 4096) as [Hlt|Hge].
    - destruct (vsb_dbl_ge 9 16 (vb_size vr + addlen) ltac:(lia) ltac:(cbn; lia)). lia.
    - pose proof (Z.div_mod (vb_size vr + addlen + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (vb_size vr + addlen + 4095) 4096 ltac:(lia)). lia. }
  pose proof (PVB_step (vb_size vr) (vsb_extendsize (vb_size vr + addlen)) ltac:(lia) (vsb_extendsize_ladder (vb_size vr + addlen) ltac:(lia))) as ST.
  pose proof (proj1 (prim_cost_range (vsb_extendsize (vb_size vr + addlen)) ltac:(lia))). lia.
Qed.
(* [comment removed for export] *)
Lemma prim_cost_room : forall n, 0 <= n -> prim_cost n <= PRIM_ROOM.
Proof. intros n H. unfold PRIM_ROOM. pose proof (proj1 (prim_cost_range n H)). lia. Qed.
Lemma vsb_extendsize_ge : forall sz, 1 <= sz -> sz <= vsb_extendsize sz.
Proof.
  intros sz H. unfold vsb_extendsize. destruct (Z.ltb_spec sz 4096) as [Hlt|Hge].
  - destruct (vsb_dbl_ge 9 16 sz ltac:(lia) ltac:(cbn; lia)). lia.
  - pose proof (Z.div_mod (sz + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (sz + 4095) 4096 ltac:(lia)). lia.
Qed.
Lemma prim_room_ext : forall c sz, 1 <= sz -> PRIM_ROOM <= c -> prim_cost (vsb_extendsize sz) <= c.
Proof. intros c sz H R. pose proof (vsb_extendsize_ge sz H). pose proof (prim_cost_room (vsb_extendsize sz) ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Definition vsb_phi (x : vsb_rec) : Prop := vsb_ppot x <= 12 * vb_len x + 96.
Lemma PVB_ext_step_fin : zall 0 70000 (fun s => PVB (vsb_extendsize (s + 1)) <=? 12 * s + 32) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma PVB_ext_step : forall s, 0 <= s -> PVB (vsb_extendsize (s + 1)) <= 12 * s + 32.
Proof.
  intros s H. destruct (Z.le_gt_cases s 70000) as [LE|GT].
  - apply Z.leb_le. apply (zall_spec _ _ _ PVB_ext_step_fin s). lia.
  - pose proof (PVB_range (vsb_extendsize (s + 1))). unfold PVB_MAX in *. lia.
Qed.
Lemma vsb_phi_fresh : forall b, vsb_phi (vsb_fresh b).
Proof. intros b. unfold vsb_phi. rewrite vsb_ppot_fresh. cbn. lia. Qed.
(* [comment removed for export] *)
Lemma vsb_phi_putc : forall x y,
  vsb_phi x -> 0 <= vb_len x -> 0 <= vb_size x -> vb_len y = vb_len x + 1 ->
  (vb_size y = vb_size x \/ (vb_size x <= vb_len x + 1 /\ vb_size y = vsb_extendsize (vb_size x + 1))) ->
  vsb_phi y.
Proof.
  intros x y PH L0 S0 EL [ES|[FULL ES]]; unfold vsb_phi, vsb_ppot in *; rewrite EL, ES.
  - lia.
  - pose proof (PVB_ext_step (vb_size x) S0). lia.
Qed.
(* [comment removed for export] *)
Lemma vsb_phi_eq : forall x y, vb_size y = vb_size x -> vb_len y = vb_len x -> vsb_phi x -> vsb_phi y.
Proof. intros x y ES EL PH. unfold vsb_phi, vsb_ppot in *. rewrite ES, EL. exact PH. Qed.
(* [comment removed for export] *)
Lemma vsb_phi_refund : forall x, vsb_phi x -> vsb_ppot x - 12 * vb_len x <= 96.
Proof. intros x PH. unfold vsb_phi in PH. lia. Qed.

(* [comment removed for export] *)
Lemma land_pagemask : forall x, 0 <= x < 2^63 ->
  Z.land x 9223372036854771712 = x / 4096 * 4096.
Proof.
  intros x Hx.
  assert (E : 9223372036854771712 = Z.ldiff (Z.ones 63) (Z.ones 12)) by reflexivity.
  rewrite E. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  replace (x / 4096 * 4096) with (Z.shiftl (Z.shiftr x 12) 12).
  2:{ rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. }
  destruct (Z.ltb_spec i 12) as [Hlt|Hge].
  - rewrite Z.shiftl_spec_low by lia.
    destruct (Z.testbit x i); cbn; rewrite ?Bool.andb_false_r; reflexivity.
  - rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - 12 + 12) with i by lia.
    destruct (Z.ltb_spec i 63) as [Hlt2|Hge2].
    + cbn. rewrite Bool.andb_true_r. reflexivity.
    + cbn. rewrite Bool.andb_false_r. symmetry. apply Z.bits_above_log2; [lia|].
      destruct (Z.eq_dec x 0) as [->|Hnz]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|].
      eapply Z.lt_le_trans; [apply (proj2 Hx)|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma roundup_pagemask : forall sz, 0 <= sz -> sz + 4095 < 2^63 ->
  Z.land (sz + 4095) 9223372036854771712 = (sz + 4095) / 4096 * 4096.
Proof. intros. apply land_pagemask. lia. Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context (L : clayout) {AI : AsanAlloc L}.
  Let segs := cl_segs L.

  Definition vsb_buf_ok (v : mem) (vr : vsb_rec) (fin : bool) : Prop :=
    exists bs, u8arr segs v (vb_buf vr) bs /\ Z.of_nat (length bs) = vb_size vr /\
               (fin = true -> nth_error bs (Z.to_nat (vb_len vr)) = Some (Z_to_bv 8 0)).

  Definition vsb_obj (A : AS) (v : mem) (S : Z) (vr : vsb_rec) (fin : bool) : Prop :=
    rw_cells segs v S (vsb_cells vr) /\ vsb_inv vr fin /\
    a_live A S = Some 40 /\ a_live A (vb_buf vr) = Some (vb_size vr) /\ S <> vb_buf vr /\
    vsb_buf_ok v vr fin.

  (* [comment removed for export] *)
  Lemma vsb_obj_geom : forall A m md S vr fin,
    ainv A m md -> vsb_obj A (aview A m) S vr fin ->
    S mod 16 = 0 /\ kHighMemBeg <= S /\ S + 40 <= alloc_ceiling /\ off_image L S 40 /\
    vb_buf vr mod 16 = 0 /\ app_range L (vb_buf vr) (vb_size vr) (* [comment removed for export] *) /\ vb_buf vr + vb_size vr <= alloc_ceiling /\
    off_image L (vb_buf vr) (vb_size vr) /\
    (S + 40 <= vb_buf vr \/ vb_buf vr + vb_size vr <= S) /\
    mapped (aview A m) S 40 /\ mapped (aview A m) (vb_buf vr) (vb_size vr).
  Proof.
    (intros A m md S vr fin AI0; (first [ intro dR_5; dand6 dR_5 as VC VI LS LB NE _ | intros (VC & VI & LS & LB & NE & _) ])).
    (first [ pose proof ((live_geom L A m md _ _ AI0 LS)) as dR_2; dand7 dR_2 as _ a1 a2 a3 a4 a5 _ | destruct (live_geom L A m md _ _ AI0 LS) as (_ & a1 & a2 & a3 & a4 & a5 & _) ]).
    (first [ pose proof ((live_geom L A m md _ _ AI0 LB)) as dR_3; dand7 dR_3 as _ b1 b2 b3 b4 b5 _ | destruct (live_geom L A m md _ _ AI0 LB) as (_ & b1 & b2 & b3 & b4 & b5 & _) ]).
    pose proof (as_live_disjoint L A m md _ _ _ _ AI0 LS LB NE).
    pose proof (live_high L A m md _ _ AI0 LS ltac:(lia)).   (* [comment removed for export] *)
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto.
  Qed.

  (* [comment removed for export] *)
  Lemma vsb_shadows : forall A m md S vr fin,
    ainv A m md -> vsb_obj A (aview A m) S vr fin ->
    bytes_at segs (aview A m) (sh S) (shpat 40)
    /\ bytes_at segs (aview A m) (sh (vb_buf vr)) (shpat (vb_size vr)).
  Proof.
    (intros A m md S vr fin AI0; (first [ intro dR_6; dand6 dR_6 as VC VI LS LB NE _ | intros (VC & VI & LS & LB & NE & _) ])).
    split; [exact (as_live_shadow L A m md _ _ AI0 LS) | exact (as_live_shadow L A m md _ _ AI0 LB)].
  Qed.

  (* [comment removed for export] *)
  Lemma vsb_buf_ok_ccall : forall A A' m (v v' : mem) (sp win : Z) victim newb vr fin md,
    ainv A m md -> v = aview A m -> a_live A (vb_buf vr) = Some (vb_size vr) ->
    cframe L (owned A) (owned A') sp win victim newb v v' ->
    (vb_buf vr + vb_size vr <= sp - win) ->
    (forall a, vb_buf vr <= a < vb_buf vr + vb_size vr -> ~ victim a) ->
    vsb_buf_ok v vr fin -> vsb_buf_ok v' vr fin.
  Proof.
    (intros A A' m v v' sp win victim newb vr fin md AI0 -> LB FR Hw Hv; (first [ intro dR_7; dex1 dR_7 as bs; dand3 dR_7 as U Hlen Hnul | intro dR_7; dand4 dR_7 as bs U Hlen Hnul | intros (bs & U & Hlen & Hnul) ])).
    exists bs. split; [|split; [exact Hlen| exact Hnul]].
    destruct (live_geom L A m md _ _ AI0 LB) as (N0 & _).
    eapply (u8arr_ccall L A A' sp win victim newb _ v' FR); [| | exact U].
    - eapply crange_block; [exact AI0 | exact LB | lia | lia | lia].
    - split; [left; lia|]. intros i Hi. apply Hv. lia.
  Qed.
End S.

(* [comment removed for export] *)
Ltac vsb_open H :=
  let VSBC := fresh "VSBC" in let VINV := fresh "VINV" in let VLS := fresh "VLS" in
  let VLB := fresh "VLB" in let VNE := fresh "VNE" in let VBUF := fresh "VBUF" in
  (first [ dand6 H as VSBC VINV VLS VLB VNE VBUF | destruct H as (VSBC & VINV & VLS & VLB & VNE & VBUF) ]).
