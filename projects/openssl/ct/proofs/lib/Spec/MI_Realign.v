(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Read MI_TF2 MI_WGroup MI_WEnframe MAlign.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma extras_eta_pend (X : extras) : x_pend X = None -> mkX (x_idle X) (x_zomb X) None (x_orph X) (x_fresh X) = X.
Proof. destruct X; cbn; intros ->; reflexivity. Qed.

Section REALIGN.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off0 n0 : Z) (g : aptr) (idx n adj : Z).
Let k0 : blk := ((c, off0), n0).
Hypothesis INV : INVL X st L BL LS.
Hypothesis NP : x_pend X = None.
Hypothesis Hk : In k0 BL.
Hypothesis Hs : s_slots st !! c = Some (g, idx).
(* [comment removed for export] *)
Hypothesis Hq20 : idx = 0 \/ get_stride (MR st g) * (idx + 1) < 2 ^ 20.
Hypothesis Hres32 : get_stride (MR st g) - UNIT * off0 - n < 2 ^ 32.
Hypothesis Hadj : 0 <= adj /\ adj mod UNIT = 0.
Hypothesis Hn : 0 <= n /\ adj + n <= n0.
Let off : Z := off0 + adj / UNIT.
Hypothesis Hoff : off <= 258.

Let IM := proj1 (proj2 (proj2 INV)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let bg : aptr := gbase (MR st g).
Let stride : Z := get_stride (MR st g).

(* [comment removed for export] *)
Lemma ra_blk : 0 <= off0 <= 258 /\ 0 <= n0 /\ UNIT * off0 + n0 <= stride - IB.
Proof.
  destruct (is_blocks _ _ _ IS k0 Hk) as (m & i & Hs' & Ho & Hz & Hf). cbn [bslot boff bsize fst snd k0] in Hs', Ho, Hz, Hf.
  rewrite Hs in Hs'. inversion Hs'. subst m i. fold stride in Hf. auto.
Qed.
Lemma ra_hosts : hosts st bg g.
Proof. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & _). unfold bg. rewrite (hosts_gbase _ _ _ IM _ _ Hb). exact Hb. Qed.
Lemma ra_idx : 0 <= idx <= m_last_idx (MR st g).
Proof. destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & Hi & _). exact Hi. Qed.
Lemma ra_c : c = (fst bg, sstart (MR st g) idx).
Proof. destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & _ & E). rewrite E. apply (slot_start'_eq _ _ _ IM). apply ra_hosts. Qed.
Lemma ra_stride : 16 <= stride /\ stride mod 16 = 0.
Proof. pose proof (stride_ge _ _ _ IG _ _ ra_hosts) as [A B]. unfold UNIT in *. split; assumption. Qed.
Lemma ra_c16 : snd c mod 16 = 0.
Proof.
  pose proof (sstart_res X st L BL LS INV bg g idx ra_hosts) as R. rewrite ra_c. cbn [snd]. unfold IB in R.
  pose proof (Z.div_mod (sstart (MR st g) idx - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR st g) idx) 16 ltac:(lia)).
  pose proof (Z.mod_pos_bound (sstart (MR st g) idx) 16 ltac:(lia)). lia.
Qed.
Lemma ra_adj16 : UNIT * (adj / UNIT) = adj.
Proof. destruct Hadj as [A B]. unfold UNIT in *. pose proof (Z.div_mod adj 16 ltac:(lia)). lia. Qed.
Lemma ra_off : 0 <= off <= 258 /\ UNIT * off + n <= stride - IB.
Proof.
  pose proof ra_blk as (Ho & Hz & Hf). pose proof ra_adj16 as E. destruct Hadj as [A B]. destruct Hn as [N1 N2]. unfold off.
  split; [split; [| exact Hoff]|]; [unfold UNIT in *; pose proof (Z.div_pos adj 16 ltac:(lia) ltac:(lia)); lia|].
  rewrite Z.mul_add_distr_l, E. lia.
Qed.
 
(* [comment removed for export] *)
Definition pp : aptr := aadd c (UNIT * off0 + adj).
Definition ee : aptr := aadd c (stride - IB).
Definition resv : Z := snd ee - snd pp - n.
Definition qv : Z := (snd pp - (snd bg + UNIT)) / UNIT.
Definition SS : list (aptr * Z) :=
  (if negb (resv =? 0) then [(aadd ee (- resv), 0)] else [])
  ++ (if 5 <=? resv then [(aadd ee (-5), 0); (aadd ee (-4), resv); (aadd (aadd ee (-4)) 1, Z.shiftr resv 8); (aadd (aadd ee (-4)) 2, Z.shiftr resv 16); (aadd (aadd ee (-4)) 3, Z.shiftr resv 24)] else [])
  ++ [(aadd pp (-3), Z.land idx 31 + Z.shiftl (if 5 <=? resv then 5 else resv) 5)].
Definition RL : list (aptr * Z) :=
  if adj =? 0 then SS
  else [(aadd pp (-4), 0); (aadd pp (-3), idx); (aadd pp (-2), qv); (aadd (aadd pp (-2)) 1, Z.shiftr qv 8)]
       ++ SS ++ [(aadd c (-3), 224); (aadd c (-2), off); (aadd (aadd c (-2)) 1, Z.shiftr off 8)].

Lemma ra_pp : snd pp = snd c + UNIT * off.
Proof. unfold pp, aadd, off. cbn [snd]. rewrite Z.mul_add_distr_l, ra_adj16. reflexivity. Qed.
Lemma ra_res : resv = stride - IB - UNIT * off - n.
Proof. unfold resv, ee. rewrite ra_pp. unfold aadd. cbn [snd]. lia. Qed.
Lemma ra_pp16 : snd pp mod 16 = 0.
Proof. rewrite ra_pp. unfold UNIT. rewrite Z.add_mod, ra_c16, Z.mul_comm, Z_mod_mult by lia. reflexivity. Qed.

Lemma set_size_m_eq p e m b3 s : set_size_m p e m b3 s =
  wrs ((if negb (snd e - snd p - m =? 0) then [(aadd e (- (snd e - snd p - m)), 0)] else [])
       ++ (if 5 <=? snd e - snd p - m then [(aadd e (-5), 0); (aadd e (-4), snd e - snd p - m); (aadd (aadd e (-4)) 1, Z.shiftr (snd e - snd p - m) 8);
                                           (aadd (aadd e (-4)) 2, Z.shiftr (snd e - snd p - m) 16); (aadd (aadd e (-4)) 3, Z.shiftr (snd e - snd p - m) 24)] else [])
       ++ [(aadd p (-3), Z.land b3 31 + Z.shiftl (if 5 <=? snd e - snd p - m then 5 else snd e - snd p - m) 5)]) s.
Proof.
  assert (B1 : forall b : bool, b = true \/ b = false) by (intros []; auto).
  unfold set_size_m.
  destruct (B1 (snd e - snd p - m =? 0)) as [H2|H2]; destruct (B1 (5 <=? snd e - snd p - m)) as [H3|H3];
    rewrite H2, H3; cbn beta iota zeta delta [negb app wrs wr32]; reflexivity.
Qed.

Lemma realign_at_RL : realign_at st g idx n off0 adj = (wrs RL st, pp).
Proof.
  unfold realign_at, RL, SS, resv, qv, ee, pp. fold (MR st g). fold stride.
  change (default (0%N, 0) (m_mem (MR st g))) with (gbase (MR st g)). fold bg.
  assert (EC : aadd bg (UNIT + stride * idx) = c).
  { rewrite ra_c. unfold sstart, aadd. fold bg. f_equal. fold stride. lia. }
  rewrite EC.
  destruct (Z.eqb_spec adj 0) as [A0|A0].
  - rewrite A0, Z.add_0_r. rewrite set_size_m_eq. reflexivity.
  - rewrite set_size_m_eq. rewrite !wrs_app. cbn [wrs app]. unfold wr16.
    replace (aadd c (UNIT * off0 + adj)) with (aadd (aadd c (UNIT * off0)) adj) by (unfold aadd; cbn; f_equal; lia).
    replace ((snd (aadd (aadd c (UNIT * off0)) adj) - snd c) / UNIT) with off; [reflexivity|].
    unfold aadd, off. cbn [snd]. replace (snd c + UNIT * off0 + adj - snd c) with ((off0 + adj / UNIT) * UNIT) by (pose proof ra_adj16; lia).
    unfold UNIT. rewrite Z.div_mul by lia. reflexivity.
Qed.

Definition stw : mstate := wrs RL st.

Lemma stw_eq : fst (realign_at st g idx n off0 adj) = stw. Proof. rewrite realign_at_RL. reflexivity. Qed.
Lemma stw_TKS : TKS stw (s_tick st).
Proof. apply wrs_TKS; [lia| exact (TKS_of _ _ _ _ _ INV)]. Qed.
Lemma stw_tick : s_tick stw = s_tick st. Proof. exact (proj2 (wrs_ctrl RL st)). Qed.
Lemma stw_ctrl : ctrl_eq st stw. Proof. exact (proj1 (wrs_ctrl RL st)). Qed.

(* [comment removed for export] *)
Lemma RL_addrs a : In a (map fst RL) ->
  fst a = fst bg /\ snd c - 3 <= snd a < snd c + stride - 4 /\ ~ (snd pp <= snd a < snd pp + n).
Proof.
  intros Hin. pose proof ra_stride as [S16 _]. pose proof ra_off as [[O0 _] Hf]. pose proof ra_pp as PP. destruct Hn as [N0 _]. destruct Hadj as [A0 _].
  pose proof ra_res as RE. pose proof ra_adj16 as A16. assert (EO : off = off0 + adj / UNIT) by reflexivity. pose proof ra_blk as ([Ho0 _] & _ & _).
  assert (R : 0 <= resv) by (rewrite RE; unfold IB, UNIT in *; lia).
  assert (FC : fst c = fst bg) by (rewrite ra_c; reflexivity).
  assert (FP : fst pp = fst bg) by (unfold pp, aadd; exact FC).
  assert (FE : fst ee = fst bg) by (unfold ee, aadd; exact FC).
  assert (SE : snd ee = snd c + stride - IB) by (unfold ee, aadd; cbn [snd]; lia).
  unfold RL, SS in Hin.
  destruct (Z.eqb_spec adj 0) as [Z0|Z0]; destruct (Z.eqb_spec resv 0) as [R0|R0]; destruct (Z.leb_spec 5 resv) as [R5|R5];
    cbn [negb app map fst In] in Hin;
    repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
    unfold aadd; cbn [fst snd]; rewrite ?FP, ?FE, ?FC; (split; [reflexivity|]); unfold IB, UNIT in *; lia.
Qed.

Lemma RL_not_in a : snd pp <= a < snd pp + n -> ~ In (fst bg, a) (map fst RL).
Proof. intros Ha Hin. destruct (RL_addrs _ Hin) as (_ & _ & NR). apply NR. exact Ha. Qed.

(* [comment removed for export] *)
Lemma stw_known_w x w : lastw RL (fst bg, x) None = Some w -> known stw (fst bg, x) (Z.land w 255).
Proof.
  intros HL. unfold known, SHd. cbn [fst snd]. unfold stw. rewrite (wrs_lastw RL st (fst bg, x) (TKS_of _ _ _ _ _ INV)). rewrite HL. reflexivity.
Qed.
Lemma stw_known_old x v : lastw RL (fst bg, x) None = None -> known st (fst bg, x) v -> known stw (fst bg, x) v.
Proof.
  intros HL K. unfold known, SHd in *. cbn [fst snd] in *. unfold stw. rewrite (wrs_lastw RL st (fst bg, x) (TKS_of _ _ _ _ _ INV)). rewrite HL. exact K.
Qed.
Lemma stw_unknown a : snd pp <= a < snd pp + n -> unknown stw (fst bg, a).
Proof.
  intros Ha. pose proof ra_pp as PP. pose proof ra_blk as (Ho & Hz & Hf0). destruct Hn as [N0 N1]. destruct Hadj as [A0 _].
  destruct (ish_blk _ _ ISH k0 g idx Hk Hs) as (_ & _ & _ & _ & _ & _ & _ & U). cbn [bslot boff bsize fst snd k0] in U.
  assert (FC : fst c = fst bg) by (rewrite ra_c; reflexivity).
  destruct (U a ltac:(unfold pp, aadd in Ha; cbn [snd] in Ha; lia)) as [h Hh]. rewrite FC in Hh.
  exists h. unfold SHd, stw. cbn [fst snd]. change (fst bg) with (fst (fst bg, a)). change a with (snd (fst bg, a)) at 2.
  rewrite wrs_read_other; [exact Hh|]. apply RL_not_in. exact Ha.
Qed.

(* [comment removed for export] *)
Ltac raeq :=
  match goal with
  | |- context [aptr_eqb ?a ?b] =>
      first [ rewrite (aptr_eqb_neq a b) by (unfold pp, ee, aadd; cbn [fst snd]; intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold IB, UNIT in *; lia)
            | rewrite (proj2 (aptr_eqb_eq a b)) by (unfold pp, ee, aadd; cbn [fst snd]; unfold IB, UNIT in *; f_equal; lia) ]
  end.

Lemma ra_q_range : 0 <= qv < 2 ^ 16.
Proof.
  pose proof Hq20 as LT. fold stride in LT. pose proof ra_off as [[O0 O1] Hf]. pose proof ra_stride as [S16 SM]. pose proof ra_idx as [I0 _].
  unfold qv. rewrite ra_pp. rewrite ra_c. cbn [snd]. unfold sstart. fold bg. fold stride.
  replace (snd bg + UNIT + stride * idx + UNIT * off - (snd bg + UNIT)) with ((stride / 16 * idx + off) * 16)
    by (unfold UNIT; pose proof (Z.div_mod stride 16 ltac:(lia)) as DM__; set (q__ := stride / 16) in *; assert (E16__ : stride = 16 * q__) by lia; rewrite E16__; ring).
  unfold UNIT. rewrite Z.div_mul by lia.
  assert (0 <= stride / 16 * idx) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
  split; [lia|].
  pose proof (Z.div_mod stride 16 ltac:(lia)). unfold IB, UNIT in Hf.
  assert (E__ : stride * idx = 16 * (stride / 16 * idx)) by (assert (E16__ : stride = 16 * (stride / 16)) by lia; rewrite E16__ at 1; ring).
  destruct LT as [-> | LT]; [rewrite Z.mul_0_r; lia| lia].
Qed.

Lemma blk_ok_realign : blk_shadow_ok stw ((c, off), n) g idx.
Proof.
  pose proof ra_stride as [S16 SM]. pose proof ra_off as [[O0 O1] Hf]. pose proof ra_blk as (Ho0 & Hz0 & Hf0). destruct Hn as [N0 N1]. destruct Hadj as [A0 AM].
  pose proof stw_ctrl as CE. pose proof stw_tick as TK.
  assert (MRE : MR stw g = MR st g) by (apply MR_ext; exact (ce_metas _ _ CE)).
  pose proof ra_res as RE. pose proof ra_pp as PP. pose proof ra_adj16 as A16. assert (EO : off = off0 + adj / UNIT) by reflexivity.
  destruct ra_hosts as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)) as LI. pose proof ra_idx as [I0 I1].
  assert (FC : fst c = fst bg) by (rewrite ra_c; reflexivity).
  unfold blk_shadow_ok. cbn [bslot boff bsize fst snd]. rewrite MRE. fold bg. fold stride. rewrite FC.
  replace (snd c + stride - IB - (snd c + UNIT * off) - n) with resv by (rewrite RE; lia).
  replace ((snd c + UNIT * off - snd bg - UNIT) / UNIT) with qv by (unfold qv; rewrite PP; f_equal; lia).
  pose proof ra_q_range as QR.
  assert (R0 : 0 <= resv) by (rewrite RE; unfold IB, UNIT in *; lia).
  assert (RS : resv < 2 ^ 32) by (rewrite RE; pose proof Hres32 as R32; fold stride in R32; unfold off in *; pose proof A16; unfold IB, UNIT in *; lia).
  assert (NPp : forall x, x < snd pp \/ snd pp + n <= x -> ~ (snd pp <= x < snd pp + n)) by (intros; lia).
  (* [comment removed for export] *)
  destruct (ish_blk _ _ ISH k0 g idx Hk Hs) as (K4 & _ & K2 & K1 & _ & _ & _ & _). cbn [bslot boff bsize fst snd k0] in K4, K2, K1. rewrite FC in K4, K2, K1. fold bg in K2, K1.
  split; [| split; [| split; [| split; [| split; [exact QR| split; [| split]]]]]].
  - (* [comment removed for export] *) destruct (Z.eqb_spec adj 0) as [Z0|Z0].
    + apply stw_known_old.
      * unfold RL, SS. replace (adj =? 0) with true by (symmetry; apply Z.eqb_eq; exact Z0).
        destruct (negb (resv =? 0)); destruct (5 <=? resv); cbn [lastw app]; rewrite ?RE, ?PP; try (exfalso; lia); repeat raeq; reflexivity.
      * replace (snd c + UNIT * off - 4) with (snd c + UNIT * off0 - 4) by (unfold off; rewrite Z.mul_add_distr_l, A16, Z0; lia). exact K4.
    + apply (stw_known_w _ 0).
      unfold RL, SS. replace (adj =? 0) with false by (symmetry; apply Z.eqb_neq; exact Z0). cbn [negb app lastw].
      destruct (negb (resv =? 0)); destruct (5 <=? resv); cbn [lastw app]; rewrite ?RE, ?PP; try (exfalso; lia); repeat raeq; reflexivity.
  - (* [comment removed for export] *)
    replace (idx + 32 * Z.min resv 5) with (Z.land (Z.land idx 31 + Z.shiftl (if 5 <=? resv then 5 else resv) 5) 255).
    2:{ replace (Z.land idx 31) with idx by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; rewrite Z.mod_small; lia). rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
        destruct (Z.leb_spec 5 resv).
        - rewrite Z.min_r by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia.
        - rewrite Z.min_l by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia. }
    apply stw_known_w.
    unfold RL, SS. destruct (Z.eqb_spec adj 0) as [?Z0|?Z0]; destruct (negb (resv =? 0)); destruct (5 <=? resv); cbn [negb lastw app]; rewrite ?RE, ?PP; try (exfalso; lia); repeat raeq; reflexivity.
  - (* [comment removed for export] *) unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r.
    destruct (Z.eqb_spec adj 0) as [Z0|Z0].
    + replace (Z.land qv 255) with (byte_of qv 0) by (unfold byte_of; rewrite Z.mul_0_r, Z.shiftr_0_r; reflexivity).
      apply stw_known_old.
      * unfold RL, SS. replace (adj =? 0) with true by (symmetry; apply Z.eqb_eq; exact Z0).
        destruct (negb (resv =? 0)); destruct (5 <=? resv); cbn [lastw app]; rewrite ?RE, ?PP; try (exfalso; lia); repeat raeq; reflexivity.
      * replace qv with ((snd c + UNIT * off0 - snd bg - UNIT) / UNIT) by (unfold qv; rewrite PP; unfold off; rewrite Z.mul_add_distr_l, A16, Z0; f_equal; lia).
        replace (snd c + UNIT * off - 2) with (snd c + UNIT * off0 - 2) by (unfold off; rewrite Z.mul_add_distr_l, A16, Z0; lia). exact K2.
    + apply stw_known_w.
      unfold RL, SS. replace (adj =? 0) with false by (symmetry; apply Z.eqb_neq; exact Z0).
      destruct (negb (resv =? 0)); destruct (5 <=? resv); cbn [negb lastw app]; rewrite ?RE, ?PP; try (exfalso; lia); repeat raeq; reflexivity.
  - (* [comment removed for export] *) unfold byte_of. rewrite Z.mul_1_r.
    destruct (Z.eqb_spec adj 0) as [Z0|Z0].
    + replace (Z.land (Z.shiftr qv 8) 255) with (byte_of qv 1) by (unfold byte_of; rewrite Z.mul_1_r; reflexivity).
      apply stw_known_old.
      * unfold RL, SS. replace (adj =? 0) with true by (symmetry; apply Z.eqb_eq; exact Z0).
        destruct (negb (resv =? 0)); destruct (5 <=? resv); cbn [lastw app]; rewrite ?RE, ?PP; try (exfalso; lia); repeat raeq; reflexivity.
      * replace qv with ((snd c + UNIT * off0 - snd bg - UNIT) / UNIT) by (unfold qv; rewrite PP; unfold off; rewrite Z.mul_add_distr_l, A16, Z0; f_equal; lia).
        replace (snd c + UNIT * off - 1) with (snd c + UNIT * off0 - 1) by (unfold off; rewrite Z.mul_add_distr_l, A16, Z0; lia). exact K1.
    + apply stw_known_w.
      unfold RL, SS. replace (adj =? 0) with false by (symmetry; apply Z.eqb_neq; exact Z0).
      destruct (negb (resv =? 0)); destruct (5 <=? resv); cbn [negb lastw app]; rewrite ?RE, ?PP; try (exfalso; lia); repeat raeq; reflexivity.
  - (* [comment removed for export] *) intros R5. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r.
    assert (E5 : (5 <=? resv) = true) by (apply Z.leb_le; exact R5).
    assert (EZ : (resv =? 0) = false) by (apply Z.eqb_neq; lia).
    split; [| split; [| split; [| split; [| split; [| exact RS]]]]].
    1-4: apply stw_known_w; unfold RL, SS; rewrite E5, EZ; destruct (Z.eqb_spec adj 0) as [?Z0|?Z0]; cbn [negb lastw app]; rewrite ?RE, ?PP; repeat raeq; try reflexivity.
    all: try (change (8 * 2) with 16; reflexivity). all: try (change (8 * 3) with 24; reflexivity).
    apply (stw_known_w _ 0). unfold RL, SS; rewrite E5, EZ; destruct (Z.eqb_spec adj 0) as [?Z0|?Z0]; cbn [negb lastw app]; rewrite ?RE, ?PP; try (exfalso; lia); repeat raeq; reflexivity.
  - (* [comment removed for export] *) intros RP.
    replace (snd c + stride - IB - resv) with (snd pp + n) by (rewrite RE, PP; lia).
    apply (stw_known_w _ 0).
    assert (EZ : (resv =? 0) = false) by (apply Z.eqb_neq; lia).
    unfold RL, SS; rewrite EZ. destruct (Z.eqb_spec adj 0) as [?Z0|?Z0]; destruct (Z.leb_spec 5 resv); cbn [negb lastw app]; rewrite ?RE, ?PP;
      try (destruct (Z.eq_dec resv 5)); try (exfalso; lia); repeat raeq; reflexivity.
  - (* [comment removed for export] *) intros a Ha. rewrite <- PP in Ha. exact (stw_unknown a Ha).
Qed.

Theorem INVL_realign_core :
  INVL X stw L (((c, off), n) :: bl_remove c BL) LS /\ ctrl_eq st stw /\ s_tick stw = s_tick st.
Proof.
  pose proof stw_ctrl as CE. pose proof stw_tick as TK. pose proof ra_off as [[O0 O1] Hf]. pose proof ra_stride as [S16 _]. destruct Hn as [N0 N1].
  destruct ra_hosts as [ai Hb] eqn:EH.
  assert (REG : exists r, s_regions st !! fst bg = Some r /\ r_kind r = RKGroup) by exact (ig_region _ _ _ IG _ _ Hb).
  assert (FC : fst c = fst bg) by (rewrite ra_c; reflexivity).
  (* [comment removed for export] *)
  set (X1 := mkX (x_idle X) (x_zomb X) (Some (bslot k0)) (x_orph X) (x_fresh X)).
  assert (INV1 : INVL X1 st L (bl_remove (bslot k0) BL) LS).
  { apply (INVL_remove_block X st st L BL LS k0 INV Hk NP (ctrl_eq_refl st) eq_refl).
    - intros; reflexivity.
    - exact (DOMS_of _ _ _ _ _ INV).
    - exact (TKS_of _ _ _ _ _ INV). }
  cbn [bslot fst snd k0] in INV1.
  (* [comment removed for export] *)
  assert (EX : mkX (x_idle X1) (x_zomb X1) None (x_orph X1) (x_fresh X1) = X) by (subst X1; cbn; apply extras_eta_pend; exact NP).
  split; [| split; [exact CE| exact TK]].
  rewrite <- EX.
  apply (INVL_add_block X1 st stw L (bl_remove c BL) LS c off n INV1 eq_refl CE TK).
  - intros m i Hs' q Hq. rewrite Hs in Hs'. inversion Hs'. subst m i.
    unfold stw. apply wrs_read_other. intros Hin. destruct (RL_addrs q Hin) as (F & R & _). apply Hq. unfold inT. split; [rewrite FC; exact F|].
    rewrite sstart_succ. fold stride. rewrite ra_c in R. cbn [snd] in R. lia.
  - change (DOMS st stw). unfold stw. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV)|]. intros q Hin. destruct (RL_addrs q Hin) as (F & _). rewrite F. exact REG.
  - change (TKS stw (s_tick st)). exact stw_TKS.
  - intros m i Hs'. rewrite Hs in Hs'. inversion Hs'. subst m i. split; [split; [exact O0| exact O1]|]. split; [exact N0|]. split; [exact Hf|].
    exact blk_ok_realign.
Qed.
End REALIGN.

(* [comment removed for export] *)
Theorem INVL_realign X st L BL LS c off0 n0 g idx n adj :
  INVL X st L BL LS -> x_pend X = None -> In ((c, off0), n0) BL -> s_slots st !! c = Some (g, idx) ->
  (idx = 0 \/ get_stride (MR st g) * (idx + 1) < 2 ^ 20) -> get_stride (MR st g) - UNIT * off0 - n < 2 ^ 32 ->
  0 <= adj -> adj mod UNIT = 0 -> 0 <= n -> adj + n <= n0 -> off0 + adj / UNIT <= 258 ->
  let st' := fst (realign_at st g idx n off0 adj) in
  INVL X st' L (((c, off0 + adj / UNIT), n) :: bl_remove c BL) LS
  /\ ctrl_eq st st' /\ s_tick st' = s_tick st
  /\ snd (realign_at st g idx n off0 adj) = aadd c (UNIT * off0 + adj).
Proof.
  intros INV NP Hk Hs Hq20 Hres32 A0 AM N0 N1 HO. cbv zeta.
  rewrite (stw_eq X st L BL LS c off0 g idx n adj INV Hs (conj A0 AM)).
  destruct (INVL_realign_core X st L BL LS c off0 n0 g idx n adj INV NP Hk Hs Hq20 Hres32 (conj A0 AM) (conj N0 N1) HO) as (I & C & T).
  split; [exact I|]. split; [exact C|]. split; [exact T|].
  rewrite (realign_at_RL X st L BL LS c off0 g idx n adj INV Hs (conj A0 AM)). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma realign_at_snd st g idx n off0 adj :
  snd (realign_at st g idx n off0 adj) = aadd (aadd (default (0%N, 0) (m_mem (get_meta_rec st g))) (UNIT + get_stride (get_meta_rec st g) * idx)) (UNIT * off0 + (if adj =? 0 then 0 else adj)).
Proof. apply realign_snd. Qed.
