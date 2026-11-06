(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallkgx Mall1es W_rejt8.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_rejt8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls6g Mallx0l.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_S421 MI_Pres4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_W2ig.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree MI_Ws22 MI_Wp9i MI_Cnt.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_W2ig Instbka.

Module MI_Wezf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require W_rejt8.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_rejt8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree MI_Ws22 MI_Wp9i MI_Cnt.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Instbka.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wp9i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_TF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wj0q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_W9kq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wkfj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Instbka.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)

Section ADDBLK.
Context {Clg : Ceiling} {Rr : MRep.RunRandom}.  (* [comment removed for export] *)
Variables (X : extras) (sP : mstate) (L : mled) (BLp : list blk) (LS : lhead -> list aptr).
Variables (c : cptr) (off : Z) (g bm : aptr) (i : Z) (n' b3 : Z).
Hypothesis INV1 : INVL X sP L BLp LS.
Hypothesis XP : x_pend X = Some c.
Hypothesis SL : s_slots sP !! c = Some (g, i).
Hypothesis Hg : hosts sP bm g.
Hypothesis Hi : 0 <= i <= m_last_idx (MR sP g).
Hypothesis Ec : c = (fst bm, sstart (MR sP g) i).
Hypothesis Hoff : 0 <= off <= 255.
Hypothesis Hn : 0 <= n'.
Let stride := get_stride (MR sP g).
Hypothesis Hfit : UNIT * off + n' <= stride - IB.
Hypothesis Hres : stride - IB - UNIT * off - n' < 2 ^ 32.
Hypothesis B3 : Z.land b3 31 = i.
Hypothesis B3R : 0 <= b3 < 256.
Let pp : aptr := aadd c (UNIT * off).
Let ee : aptr := aadd c (stride - IB).
Let q : Z := (snd pp - (snd bm + UNIT)) / UNIT.
Hypothesis K4 : known sP (fst c, snd pp - 4) 0.
Hypothesis K2 : known sP (fst c, snd pp - 2) (byte_of q 0).
Hypothesis K1 : known sP (fst c, snd pp - 1) (byte_of q 1).
Hypothesis QR : 0 <= q < 2 ^ 16.
Hypothesis OLDC : forall o v t, snd pp <= o < snd pp + n' -> r_cells (get_shadow sP (fst c)) !! o = Some (v, t) -> (t < s_tick sP)%N.

Let IM := proj1 (proj2 (proj2 INV1)).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV1)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV1))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV1))))).

Definition aresv : Z := snd ee - snd pp - n'.
Definition ar5 : Z := if 5 <=? aresv then 5 else aresv.
Definition ARL : list (aptr * Z) :=
  (if negb (aresv =? 0) then [(aadd ee (- aresv), 0)] else [])
  ++ (if 5 <=? aresv then [(aadd ee (-5), 0); (aadd ee (-4), aresv); (aadd (aadd ee (-4)) 1, Z.shiftr aresv 8);
                         (aadd (aadd ee (-4)) 2, Z.shiftr aresv 16); (aadd (aadd ee (-4)) 3, Z.shiftr aresv 24)] else [])
  ++ [(aadd pp (-3), Z.land b3 31 + Z.shiftl ar5 5)].
Definition abw : mstate := wrs ARL sP.
Definition abf : mstate := havoc pp n' abw.

#[using="IG Hg INV1 bm LS BLp L X Clg"] Lemma ab_stride : 16 <= stride /\ stride mod 16 = 0.
Proof. pose proof (stride_ge _ _ _ IG _ _ Hg) as [A B]. unfold UNIT in *. split; assumption. Qed.
#[using="IM Hg INV1 LS BLp L X Clg"] Lemma ab_gbase : gbase (MR sP g) = bm. Proof. exact (hosts_gbase _ _ _ IM _ _ Hg). Qed.
#[using="q bm"] Lemma aresv_eq : aresv = stride - IB - UNIT * off - n'.
Proof. unfold aresv, ee, pp, aadd. cbn [snd]. lia. Qed.
#[using="q Hfit bm"] Lemma aresv_nonneg : 0 <= aresv. Proof. rewrite aresv_eq. unfold UNIT, IB in *. lia. Qed.
#[using="q stride Ec Hg INV1 i bm g LS BLp L sP X Clg"] Lemma ab_pp16 : snd pp mod 16 = 0.
Proof.
  pose proof (sstart_res X sP L BLp LS INV1 bm g i Hg) as R. unfold pp, aadd. rewrite Ec. cbn [snd]. unfold IB, UNIT in *.
  pose proof (Z.div_mod (sstart (MR sP g) i - 4) 16 ltac:(lia)). pose proof (Z.div_mod (sstart (MR sP g) i) 16 ltac:(lia)).
  pose proof (Z.mod_pos_bound (sstart (MR sP g) i) 16 ltac:(lia)).
  replace (sstart (MR sP g) i + 16 * off) with ((sstart (MR sP g) i / 16 + off) * 16) by lia. apply Z_mod_mult.
Qed.
#[using="IS IM Ec Hi Hg XP INV1 i bm g LS BLp L X Clg"] Lemma ab_NH : s_groups sP !! c = None.
Proof.
  destruct Hg as [ai Hb]. pose proof (is_part _ _ _ IS _ _ _ i Hb Hi) as P5. cbn zeta in P5.
  rewrite (slot_start'_eq _ _ _ IM _ _ i (ex_intro _ ai Hb)), <- Ec, XP in P5.
  destruct (s_groups sP !! c) eqn:E; [| reflexivity]. exfalso.
  destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & nDE). apply nDE. split; [rewrite E; discriminate| reflexivity].
Qed.

#[using="q INV1 bm LS BLp L X Clg"] Lemma abw_TKS : TKS abw (s_tick sP).
Proof. unfold abw. apply wrs_TKS; [lia| exact (TKS_of _ _ _ _ _ INV1)]. Qed.
Lemma abw_tick : s_tick abw = s_tick sP. Proof. exact (proj2 (wrs_ctrl ARL sP)). Qed.
Lemma abw_ctrl : ctrl_eq sP abw. Proof. exact (proj1 (wrs_ctrl ARL sP)). Qed.
#[using="q INV1 bm LS BLp L X Clg"] Lemma abw_hav u hl : r_hav (get_shadow abw (fst pp)) !! u = Some hl -> hl_ticks hl (s_tick abw).
Proof. intros Hu ch Hch. rewrite abw_tick. pose proof abw_TKS as TK. rewrite <- abw_tick in TK. rewrite <- abw_tick. exact (proj1 (sh_ticks_of _ _ TK) u hl ch Hu Hch). Qed.
Lemma abf_ctrl : ctrl_eq sP abf /\ s_tick abf = s_tick sP.
Proof.
  destruct (havoc_ctrl pp n' abw) as [C T]. split; [exact (ctrl_eq_trans _ _ _ abw_ctrl C)| rewrite T; apply abw_tick].
Qed.
#[using="q Hn Ec Hg INV1 i bm LS BLp L X Clg"] Lemma abf_read_out r : ~ (fst r = fst c /\ snd pp <= snd r < snd pp + n') ->
  cell_read (get_shadow abf (fst r)) (snd r) = cell_read (get_shadow abw (fst r)) (snd r).
Proof.
  intros Hr. unfold abf. destruct (Z.eq_dec n' 0) as [N0|NZ]; [rewrite havoc_le0 by lia; reflexivity|].
  apply (cell_read_havoc_out pp n' abw ab_pp16 ltac:(lia) abw_hav). exact Hr.
Qed.

#[using="IG q Hfit Hn Hoff Hg INV1 bm LS BLp L X Clg"] Lemma ARL_addrs a : In a (map fst ARL) ->
  fst a = fst c /\ snd c - 3 <= snd a < snd c + stride - 4 /\ ~ (snd pp <= snd a < snd pp + n').
Proof.
  intros Hin. pose proof ab_stride as [S16 _]. pose proof aresv_nonneg as R.
  unfold ARL in Hin.
  destruct (Z.eqb_spec aresv 0) as [R0|R0]; destruct (Z.leb_spec 5 aresv) as [R5|R5];
    cbn [negb app map fst In] in Hin; unfold aresv, ee, pp, aadd in *; cbn [fst snd] in *; unfold IB, UNIT in *;
    repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end; cbn [fst snd]; (split; [reflexivity| lia]).
Qed.

#[using="QR q B3R Hn Hoff Ec Hi Hg INV1 i bm LS BLp L X Clg"] Lemma abf_known_w x w : ~ (snd pp <= x < snd pp + n') ->
  lastw ARL (fst c, x) None = Some w -> known abf (fst c, x) (Z.land w 255).
Proof.
  intros Hx HL. unfold known, SHd. cbn [fst snd].
  rewrite (abf_read_out (fst c, x)) by (cbn [fst snd]; tauto).
  unfold abw. rewrite (wrs_lastw ARL sP (fst c, x) (TKS_of _ _ _ _ _ INV1)). rewrite HL. reflexivity.
Qed.

#[using="QR q B3R Hn Hoff Ec Hi Hg INV1 i bm LS BLp L X Clg"] Lemma abf_known_old x v : ~ (snd pp <= x < snd pp + n') ->
  lastw ARL (fst c, x) None = None -> known sP (fst c, x) v -> known abf (fst c, x) v.
Proof.
  intros Hx HL K. unfold known, SHd in *. cbn [fst snd] in *.
  rewrite (abf_read_out (fst c, x)) by (cbn [fst snd]; tauto).
  unfold abw. rewrite (wrs_lastw ARL sP (fst c, x) (TKS_of _ _ _ _ _ INV1)). rewrite HL. exact K.
Qed.

#[using="IG q Hfit Hn Hoff Hg INV1 bm LS BLp L X Clg"] Lemma ARL_not_in a : snd pp <= a < snd pp + n' -> ~ In (fst c, a) (map fst ARL).
Proof. intros Ha Hin. destruct (ARL_addrs _ Hin) as (_ & _ & NR). apply NR. exact Ha. Qed.

#[using="IG OLDC q Hfit Hn Hoff Ec Hg INV1 i bm LS BLp L X Clg"] Lemma abf_unknown a : snd pp <= a < snd pp + n' -> unknown abf (fst c, a).
Proof.
  intros Ha. unfold unknown, SHd, abf. cbn [fst snd].
  destruct (cell_read_havoc_in pp n' abw ab_pp16 ltac:(lia) abw_hav (fst c, a) eq_refl Ha) as [h Hh]; [| exists h; exact Hh].
  cbn [snd]. intros v tk Hc. unfold abw in Hc. change (fst pp) with (fst c) in Hc. rewrite wrs_cells_other in Hc by (apply ARL_not_in; exact Ha).
  rewrite abw_tick. exact (OLDC a v tk Ha Hc).
Qed.

Ltac aeq :=
  match goal with
  | |- context [aptr_eqb ?a ?b] =>
      first [ rewrite (aptr_eqb_neq a b) by (unfold pp, ee, aadd; cbn [fst snd]; intros E; apply (f_equal snd) in E; cbn [snd] in E; unfold IB, UNIT in *; lia)
            | rewrite (proj2 (aptr_eqb_eq a b)) by (unfold pp, ee, aadd; cbn [fst snd]; unfold IB, UNIT in *; f_equal; lia) ]
  end.

#[using="IG IM OLDC QR K1 K2 K4 q B3R B3 Hres Hfit Hn Hoff Ec Hi Hg INV1 bm LS BLp L X Clg"] Lemma ab_blk_ok : blk_shadow_ok abf ((c, off), n') g i.
Proof.
  pose proof ab_stride as [S16 SM]. pose proof aresv_eq as RE. pose proof aresv_nonneg as R0.
  pose proof (Z.div_mod stride 16 ltac:(lia)) as SD. rewrite SM, Z.add_0_r in SD.
  destruct abf_ctrl as [CE TK].
  assert (MRE : MR abf g = MR sP g).
  { rewrite (MR_ext sP abf (ce_metas _ _ CE)). reflexivity. }
  destruct Hg as [ai Hb]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)) as LI.
  unfold blk_shadow_ok. cbn [bslot boff bsize fst snd]. rewrite MRE, ab_gbase. fold stride.
  replace (snd c + stride - IB - (snd c + UNIT * off) - n') with aresv by (rewrite RE; lia).
  replace ((snd c + UNIT * off - snd bm - UNIT) / UNIT) with q by (unfold q, pp, aadd; cbn [snd]; f_equal; lia).
  assert (NP : forall x, x < snd pp \/ snd pp + n' <= x -> ~ (snd pp <= x < snd pp + n')) by (intros; lia).
  assert (PP : snd pp = snd c + UNIT * off) by reflexivity.
  assert (EE : snd ee = snd c + stride - IB) by (unfold ee, aadd; cbn [snd]; lia).
  split; [| split; [| split; [| split; [| split; [exact QR| split; [| split]]]]]].
  - rewrite <- PP. apply abf_known_old; [apply NP; lia| | exact K4].
    unfold ARL. destruct (Z.eqb_spec aresv 0); destruct (Z.leb_spec 5 aresv); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - replace (i + 32 * Z.min aresv 5) with (Z.land (Z.land b3 31 + Z.shiftl ar5 5) 255).
    2:{ rewrite B3. unfold ar5. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
        destruct (Z.leb_spec 5 aresv).
        - rewrite Z.min_r by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia.
        - rewrite Z.min_l by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small; lia. }
    rewrite <- PP. apply abf_known_w; [apply NP; lia|].
    unfold ARL. destruct (Z.eqb_spec aresv 0); destruct (Z.leb_spec 5 aresv); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - rewrite <- PP. apply abf_known_old; [apply NP; lia| | exact K2].
    unfold ARL. destruct (Z.eqb_spec aresv 0); destruct (Z.leb_spec 5 aresv); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - rewrite <- PP. apply abf_known_old; [apply NP; lia| | exact K1].
    unfold ARL. destruct (Z.eqb_spec aresv 0); destruct (Z.leb_spec 5 aresv); cbn [negb lastw app]; try (exfalso; lia); repeat aeq; reflexivity.
  - intros R5. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.mul_1_r.
    assert (RS : aresv < 2 ^ 32) by (rewrite RE; exact Hres).
    assert (E5 : (5 <=? aresv) = true) by (apply Z.leb_le; exact R5).
    assert (EZ : (aresv =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite <- EE.
    split; [| split; [| split; [| split; [| split; [| exact RS]]]]].
    1-4: apply abf_known_w; [apply NP; rewrite ?EE, ?PP, ?RE; unfold IB, UNIT in *; lia|];
         unfold ARL; rewrite E5, EZ; cbn [negb lastw app]; repeat aeq; try reflexivity.
    all: try (change (8 * 2) with 16; reflexivity). all: try (change (8 * 3) with 24; reflexivity).
    apply (abf_known_w _ 0); [apply NP; rewrite ?EE, ?PP, ?RE; unfold IB, UNIT in *; lia|].
    unfold ARL; rewrite E5, EZ; cbn [negb lastw app]; repeat aeq; reflexivity.
  - intros RP.
    replace (snd c + stride - IB - aresv) with (snd pp + n') by (rewrite RE, PP; lia).
    apply (abf_known_w _ 0); [apply NP; lia|].
    assert (EZ : (aresv =? 0) = false) by (apply Z.eqb_neq; lia).
    unfold ARL; rewrite EZ. destruct (Z.leb_spec 5 aresv); cbn [negb lastw app];
      try (destruct (Z.eq_dec aresv 5)); try (exfalso; lia); repeat aeq; reflexivity.
  - intros a Ha. apply abf_unknown. rewrite PP. exact Ha.
Qed.

#[using="IG IM OLDC QR K1 K2 K4 q B3R B3 Hres Hfit Hn Hoff Ec Hi Hg SL XP INV1 i bm"] Theorem ab_INVL : INVL (mkX (x_idle X) (x_zomb X) None (x_orph X) (x_fresh X)) abf L (((c, off), n') :: BLp) LS.
Proof.
  destruct abf_ctrl as [CE TK]. pose proof ab_stride as [S16 _].
  assert (SL0 : s_slots sP !! c = Some (g, i)) by exact SL.
  apply (INVL_add_block X sP abf L BLp LS c off n' INV1 XP CE TK).
  - intros m j Hs r Hr. rewrite SL0 in Hs. inversion Hs. subst m j.
    assert (SC : snd c = sstart (MR sP g) i) by (rewrite Ec; reflexivity).
    rewrite sstart_succ in Hr. fold stride in Hr. rewrite <- SC in Hr.
    assert (NQ : ~ (fst r = fst c /\ snd pp <= snd r < snd pp + n')).
    { intros [F R]. apply Hr. unfold inT. split; [exact F|]. unfold pp, aadd in R. cbn [snd] in R. try (generalize alloc_ceiling_val); clear - R Hfit Hn Hoff S16; try pose proof alloc_ceiling_val. unfold IB, UNIT in *. lia. }
    rewrite (abf_read_out r NQ). unfold abw. rewrite wrs_read_other; [reflexivity|].
    intros Hin. destruct (ARL_addrs r Hin) as (F & R & _). apply Hr. unfold inT. split; [exact F|]. try (generalize alloc_ceiling_val); clear - R; try pose proof alloc_ceiling_val. unfold IB in *. lia.
  - intros rid sh Hsh. assert (REG' : exists r, s_regions sP !! fst c = Some r /\ r_kind r = RKGroup).
    { rewrite Ec. cbn [fst]. destruct Hg as [ai Hb]. exact (ig_region _ _ _ IG _ _ Hb). }
    revert rid sh Hsh. change (DOMS sP abf). unfold abf. destruct (Z.eq_dec n' 0) as [N0|NZ].
    + rewrite havoc_le0 by lia. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV1)|]. intros r Hin. destruct (ARL_addrs r Hin) as (F & _). rewrite F. exact REG'.
    + apply DOMS_havoc; [lia| | exact REG']. apply wrs_DOMS; [exact (DOMS_of _ _ _ _ _ INV1)|]. intros r Hin. destruct (ARL_addrs r Hin) as (F & _). rewrite F. exact REG'.
  - change (TKS abf (s_tick sP)). unfold abf. destruct (Z.eq_dec n' 0) as [N0|NZ].
    + rewrite havoc_le0 by lia. apply abw_TKS.
    + rewrite <- abw_tick. apply TKS_havoc; [apply ab_pp16| lia| rewrite abw_tick; apply abw_TKS].
  - intros m j Hs. rewrite SL0 in Hs. inversion Hs. subst m j. split; [exact Hoff|]. split; [exact Hn|]. split; [exact Hfit|].
    apply ab_blk_ok.
Qed.

(* [comment removed for export] *)
Variables (m : word -> option byte) (r : region).
Hypothesis MRP : mrep sP m.
Hypothesis TKst : ticks_ok sP.
Hypothesis Hr : s_regions sP !! (fst bm) = Some r.
Hypothesis Hkr : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd bm.
Hypothesis SPAN : snd bm + UNIT + stride * (m_last_idx (MR sP g) + 1) <= round_up_pg (r_len r).

#[using="IS IG IM Ec Hi Hg XP INV1 i LS BLp L X Clg"] Lemma ab_NOGRP b' gh : s_groups sP !! b' = Some gh -> fst b' = fst bm ->
  snd b' + 16 <= snd c \/ snd c + stride <= snd b' + 4.
Proof.
  intros Hb' Hf.
  assert (HO : exists m', hosts sP b' m').
  { destruct gh as [[m'|] ai']; [exists m'; exists ai'; exact Hb'| exfalso; exact (ig_nometa _ _ _ IG _ _ Hb')]. }
  destruct HO as [m' Hm'].
  assert (NH : s_groups sP !! (fst bm, sstart (MR sP g) i) = None) by (rewrite <- Ec; apply ab_NH).
  pose proof (sep_ghdr X sP BLp LS IM IG IS g bm i Hg Hi NH m' b' Hm' Hf) as SG.
  rewrite sstart_succ in SG. fold stride in SG. rewrite Ec. cbn [snd]. exact SG.
Qed.

#[using="SPAN B0 Hkr Hr TKst MRP IS IG IM q B3 Hres Hfit Hn Hoff Ec Hi Hg XP INV1 i bm LS BLp L X"] Lemma ab_mrep :
  mrep abf (set_size_mem m (r_base r + snd pp) (r_base r + snd ee) n' b3) /\ ticks_ok abf.
Proof.
  pose proof ab_stride as [S16 SM]. pose proof aresv_eq as RE. pose proof aresv_nonneg as R0.
  pose proof (Z.div_mod stride 16 ltac:(lia)) as SD. rewrite SM, Z.add_0_r in SD.
  assert (SC : snd c = snd bm + 16 + stride * i) by (rewrite Ec; cbn [snd]; unfold sstart; rewrite ab_gbase; reflexivity).
  assert (FC : fst c = fst bm) by (rewrite Ec; reflexivity).
  assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SIL : stride * (i + 1) <= stride * (m_last_idx (MR sP g) + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (EHI : snd c + stride <= round_up_pg (r_len r)) by (rewrite SC; unfold UNIT in SPAN; lia).
  pose proof MRP as MR0. pose proof TKst as TK0.
  assert (W8 : forall stx mx o v, mrep stx mx -> ticks_ok stx -> s_regions stx = s_regions sP -> s_groups stx = s_groups sP ->
            snd c - 4 <= o < snd c + stride - 4 -> 0 <= v < 256 ->
            mrep (wr8 (fst c, o) v stx) (write_to_mem mx (wa (r_base r + o)) [b8 v]) /\ ticks_ok (wr8 (fst c, o) v stx)).
  { intros stx mx o v MX TX ER EG Ho Hv. split; [| apply ticks_ok_wr8; exact TX].
    apply (mrep_wr8 stx mx (fst c, o) v r MX TX); cbn [fst snd]; [rewrite ER, FC; exact Hr| exact Hkr| lia| | exact Hv].
    intros b' gh Hb' Hf. rewrite EG in Hb'. rewrite FC in Hf. destruct (ab_NOGRP b' gh Hb' Hf); lia. }
  assert (W32 : forall stx mx o v, mrep stx mx -> ticks_ok stx -> s_regions stx = s_regions sP -> s_groups stx = s_groups sP ->
            snd c - 4 <= o -> o + 4 <= snd c + stride - 4 -> 0 <= v < 2^32 ->
            mrep (wr32 (fst c, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le4 (wz v))) /\ ticks_ok (wr32 (fst c, o) v stx)).
  { intros stx mx o v MX TX ER EG Ho Ho4 Hv.
    apply (mrep_wr32 stx mx (fst c, o) v r MX TX); cbn [fst snd]; [rewrite ER, FC; exact Hr| exact Hkr| lia| lia| | exact Hv].
    intros b' gh Hb' Hf. rewrite EG in Hb'. rewrite FC in Hf. destruct (ab_NOGRP b' gh Hb' Hf); lia. }
  unfold set_size_mem. cbv zeta.
  replace (r_base r + snd ee - (r_base r + snd pp) - n') with aresv by (unfold aresv; lia).
  unfold abf, abw, ARL.
  assert (PPE : snd pp = snd c + UNIT * off) by reflexivity.
  assert (EEE : snd ee = snd c + (stride - IB)) by reflexivity.
  replace (aadd ee (- aresv)) with (fst c, snd ee - aresv) by (unfold ee, aadd; cbn [fst snd]; f_equal; lia).
  replace (aadd ee (-5)) with (fst c, snd ee - 5) by (unfold ee, aadd; cbn [fst snd]; f_equal; lia).
  replace (aadd ee (-4)) with (fst c, snd ee - 4) by (unfold ee, aadd; cbn [fst snd]; f_equal; lia).
  replace (aadd pp (-3)) with (fst c, snd pp - 3) by (unfold pp, aadd; cbn [fst snd]; f_equal; lia).
  replace (r_base r + snd ee - aresv) with (r_base r + (snd ee - aresv)) by lia.
  replace (r_base r + snd ee - 5) with (r_base r + (snd ee - 5)) by lia.
  replace (r_base r + snd ee - 4) with (r_base r + (snd ee - 4)) by lia.
  replace (r_base r + snd pp - 3) with (r_base r + (snd pp - 3)) by lia.
  assert (LI : 0 <= m_last_idx (MR sP g) <= 31).
  { destruct Hg as [ai Hb]. exact (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)). }
  assert (V3 : forall r5v, 0 <= r5v <= 5 -> 0 <= Z.land b3 31 + Z.shiftl r5v 5 < 256).
  { intros r5v Hr5. rewrite B3, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. try (generalize alloc_ceiling_val); clear - Hr5 Hi LI; try pose proof alloc_ceiling_val. lia. }
  assert (FIN : forall stx mx, mrep stx mx -> ticks_ok stx ->
            mrep (havoc pp n' stx) mx /\ ticks_ok (havoc pp n' stx)).
  { intros stx mx MX TX. destruct (Z.eq_dec n' 0) as [N0|NZ]; [rewrite havoc_le0 by lia; split; assumption| exact (mrep_havoc _ _ pp n' MX TX)]. }
  destruct (Z.eqb_spec aresv 0) as [RZ|RZ]; destruct (Z.leb_spec 5 aresv) as [R5|R5]; try (exfalso; lia); cbn [negb app wrs]; unfold ar5.
  - rewrite (proj2 (Z.leb_gt 5 aresv) ltac:(try (generalize alloc_ceiling_val); clear - RZ R5; try pose proof alloc_ceiling_val; lia)).
    destruct (W8 sP m (snd pp - 3) (Z.land b3 31 + Z.shiftl aresv 5) MR0 TK0 eq_refl eq_refl ltac:(rewrite PPE; unfold IB, UNIT in *; lia) ltac:(apply V3; lia)) as [M3 T3].
    exact (FIN _ _ M3 T3).
  - rewrite (proj2 (Z.leb_le 5 aresv) R5).
    assert (RS : aresv < 2 ^ 32) by (rewrite RE; exact Hres).
    destruct (W8 sP m (snd ee - aresv) 0 MR0 TK0 eq_refl eq_refl ltac:(rewrite EEE; unfold IB, UNIT in *; lia) ltac:(lia)) as [M1 T1].
    destruct (W8 _ _ (snd ee - 5) 0 M1 T1 ltac:(reflexivity) ltac:(reflexivity) ltac:(rewrite EEE; unfold IB, UNIT in *; lia) ltac:(lia)) as [M2 T2].
    destruct (W32 _ _ (snd ee - 4) aresv M2 T2 ltac:(reflexivity) ltac:(reflexivity)
                ltac:(rewrite EEE; unfold IB, UNIT in *; lia) ltac:(rewrite EEE; unfold IB; lia) ltac:(lia)) as [M4 T4].
    set (stX := wr8 (fst c, snd ee - 5) 0 (wr8 (fst c, snd ee - aresv) 0 sP)) in *.
    change (wr8 (aadd (fst c, snd ee - 4) 3) (Z.shiftr aresv 24) (wr8 (aadd (fst c, snd ee - 4) 2) (Z.shiftr aresv 16)
              (wr8 (aadd (fst c, snd ee - 4) 1) (Z.shiftr aresv 8) (wr8 (fst c, snd ee - 4) aresv stX))))
      with (wr32 (fst c, snd ee - 4) aresv stX).
    destruct (W8 _ _ (snd pp - 3) (Z.land b3 31 + Z.shiftl 5 5) M4 T4 ltac:(reflexivity) ltac:(reflexivity) ltac:(rewrite PPE; unfold IB, UNIT in *; lia) ltac:(apply V3; lia)) as [M3 T3].
    exact (FIN _ _ M3 T3).
  - rewrite (proj2 (Z.leb_gt 5 aresv) ltac:(try (generalize alloc_ceiling_val); clear - RZ R5; try pose proof alloc_ceiling_val; lia)).
    destruct (W8 sP m (snd ee - aresv) 0 MR0 TK0 eq_refl eq_refl ltac:(rewrite EEE; unfold IB, UNIT in *; lia) ltac:(lia)) as [M1 T1].
    destruct (W8 _ _ (snd pp - 3) (Z.land b3 31 + Z.shiftl aresv 5) M1 T1 ltac:(reflexivity) ltac:(reflexivity) ltac:(rewrite PPE; unfold IB, UNIT in *; lia) ltac:(apply V3; lia)) as [M3 T3].
    exact (FIN _ _ M3 T3).
Qed.

End ADDBLK.
End MI_Wezf.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Ext2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W2ig.MI_Lsjc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wp9i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Cnt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_TF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wj0q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_W9kq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ccma.MI_Wkfj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W2ig OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Instbka OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wje4.MI_Wezf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@ND0; @NB0; @O4096; @B0; @RB0; @H; @Sa0; @Hi; @Ho; @Hkk; @Sa0'; @Ca'; @MLg; @ML0; @NEa; @H2; @H0; @H1; @BR1; @HG; @MLR; @NR1; @Sa1; @LRa'; @D; @ACV; @LO; @L0; @MLE; @L1; @Sa1'; @DD; @E; @Hoff; @Hx; @NEa'; @Hk0; @HN; @A0; @AC; @S2; @S3; @LQ; @Hk'; @NEk; @SC; @FITn; @LEN; @NE; @LRa; @NBC; @Hf; @NDX; @LE; @HA; @A4; @PG'; @NEo; @HI; @Q0; @Hft; @SCp; @Fb; @Hv; @e; @R; @ML; @F; @Hml; @NDT; @Hn; @HA1; @HN2; @l; @n0; @XA; @W0; @W1; @XA'; @E1; @E2; @LRr; @S1; @LO0; @S4; @S5; @QC; @H3; @H4; @NBA; @BAL; @Sb0; @Sb1; @BC; @LT])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)

Definition isG (kr : N * region) : bool := match r_kind (snd kr) with RKGroup => true | _ => false end.
Definition isM (kr : N * region) : bool := match r_kind (snd kr) with RKMeta => true | _ => false end.
Definition gpair (kr : N * region) : Z * Z := (r_base (snd kr), r_len (snd kr)).

Section REMAP.
Context {Clg : Ceiling} {Rr : MRep.RunRandom}.  (* [comment removed for export] *)
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Variables (rid : N) (r : region) (g : aptr) (off old n NB ND : Z).
Let bm : aptr := (rid, 0).
Let c : cptr := (rid, 16).
Let k : blk := ((c, off), old).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis Hk : In k BL.
Hypothesis Hg : hosts st bm g.
Hypothesis SC63 : m_sizeclass (MR st g) = 63.
Hypothesis Hr : s_regions st !! rid = Some r.
(* [comment removed for export] *)
Hypothesis ND0 : 4096 <= ND.
Hypothesis NDA : ND mod 4096 = 0.
Hypothesis NDX : ND < 2 ^ 40.
Hypothesis NB0 : 0 < NB.
Hypothesis NBA : NB mod 4096 = 0.
Hypothesis NBC : NB + ND <= alloc_ceiling.
Hypothesis FITn : UNIT + UNIT * off + n + IB <= ND.
Hypothesis NDT : ND < UNIT + UNIT * off + n + IB + 4096.
Hypothesis Hoff : 0 <= off <= 255.
Hypothesis Hn : 0 <= n.
Hypothesis DISJ : forall rid2 r2, rid2 <> rid -> s_regions st !! rid2 = Some r2 ->
  let '(b2, l2) := region_live_range r2 in NB + ND <= b2 \/ b2 + l2 <= NB.

Let IR := proj1 INV.
Let IA := proj1 (proj2 INV).
Let IM := proj1 (proj2 (proj2 INV)).
Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

(* [comment removed for export] *)
Definition OLDL : Z := m_maplen (MR st g) * 4096.

#[using="IG SC63 Hg INV bm ND NB rid BL L Clg"] Lemma rm_gfacts : m_last_idx (MR st g) = 0 /\ m_maplen (MR st g) <> 0 /\ ~ in_list LS g /\ 0 <= m_maplen (MR st g).
Proof.
  destruct Hg as [ai Hb]. pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO.
  destruct (g_sc _ _ _ _ _ _ GO) as [[SC _]|(E & L0 & ML & NIL)]; [rewrite SC63 in SC; lia|].
  pose proof (g_maplen _ _ _ _ _ _ GO). auto.
Qed.
#[using="IG Hr Hg INV bm g rid LS BL L st Clg"] Lemma rm_kind : r_kind r = RKGroup.
Proof. destruct Hg as [ai Hb]. (first [ pose proof ((ig_region _ _ _ IG _ _ Hb)) as dR_1; dex1 dR_1 as r0; destruct dR_1 as [Hr0 K] | pose proof ((ig_region _ _ _ IG _ _ Hb)) as dR_1; dand3 dR_1 as r0 Hr0 K | destruct (ig_region _ _ _ IG _ _ Hb) as (r0 & Hr0 & K) ]). cbn in Hr0. rewrite Hr in Hr0. inversion Hr0. subst. exact K. Qed.
#[using="IG Hr SC63 Hg INV bm ND NB rid LS BL L Clg"] Lemma rm_top : OLDL = round_up_pg (r_len r) /\ gend (MR st g) <= OLDL.
Proof.
  destruct Hg as [ai Hb]. pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO. (first [ dand3 rm_gfacts as _ ML _ | destruct rm_gfacts as (_ & ML & _) ]).
  (first [ pose proof ((g_top _ _ _ _ _ _ GO ML)) as dR_3; dand6 dR_3 as _ r0 Hr0 _ E GE | destruct (g_top _ _ _ _ _ _ GO ML) as (_ & r0 & Hr0 & _ & E & GE) ]). cbn in Hr0. rewrite Hr in Hr0. inversion Hr0. subst. unfold OLDL. auto.
Qed.
(* [comment removed for export] *)
#[using="IM Hg INV LS BL L Clg"] Lemma rm_gbase : gbase (MR st g) = bm. Proof. exact (hosts_gbase _ _ _ IM _ _ Hg). Qed.
#[using="IM Hg INV ND NB LS BL L Clg"] Lemma rm_c : c = (fst bm, sstart (MR st g) 0).
Proof. unfold c, sstart. rewrite rm_gbase. cbn. unfold UNIT. f_equal. lia. Qed.
#[using="IS IG IM NB0 ND0 SC63 Hg INV bm ND NB LS BL L Clg"] Lemma rm_slot : s_slots st !! c = Some (g, 0).
Proof. rewrite rm_c, <- (slot_start'_eq _ _ _ IM _ _ 0 Hg). apply (is_total _ _ _ IS _ _ _ Hg). pose proof rm_gfacts; lia. Qed.
#[using="IS IG IM Hoff NB0 ND0 SC63 Hg Hk INV k bm ND NB old off g LS BL L Clg"] Lemma rm_NH : s_groups st !! c = None.
Proof.
  destruct Hg as [ai Hb]. pose proof rm_gfacts as (L0 & _).
  pose proof (is_part _ _ _ IS _ _ _ 0 Hb ltac:(lia)) as P5. cbn zeta in P5.
  rewrite (slot_start'_eq _ _ _ IM _ _ 0 (ex_intro _ ai Hb)), <- rm_c in P5.
  destruct (s_groups st !! c) eqn:E; [| reflexivity]. exfalso.
  assert (U : In c (map bslot BL)) by (change c with (bslot k); apply in_map; exact Hk).
  assert (H : s_groups st !! c <> None) by congruence. unfold one5 in P5. tauto.
Qed.
(* [comment removed for export] *)
#[using="IS IG IM SC63 Hg INV ND NB g LS BL L Clg"] Lemma rm_only_group b h : s_groups st !! b = Some h -> fst b = rid -> b = bm.
Proof.
  intros Hb Hf. (first [ pose proof ((im_hdr _ _ _ IM _ _ Hb)) as dR_5; dex1 dR_5 as m; dand3 dR_5 as Hm Hmem Hai | pose proof ((im_hdr _ _ _ IM _ _ Hb)) as dR_5; dand4 dR_5 as m Hm Hmem Hai | destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Hm & Hmem & Hai) ]).
  assert (HO : hosts st b m) by (exists (g_active_idx h); destruct h as [hm hai]; cbn in Hm |- *; subst hm; exact Hb).
  (first [ dand3 rm_gfacts as L0 MLg _ | destruct rm_gfacts as (L0 & MLg & _) ]).
  destruct (Z.eq_dec (m_maplen (MR st m)) 0) as [ML0|ML0].
  - exfalso. (first [ pose proof ((top_chain _ _ _ _ IM IG IS m b HO ML0)) as dR_7; dex4 dR_7 as t i c0 bt; dand4 dR_7 as Ha Ht Htop Hft | pose proof ((top_chain _ _ _ _ IM IG IS m b HO ML0)) as dR_7; dand8 dR_7 as t i c0 bt Ha Ht Htop Hft | destruct (top_chain _ _ _ _ IM IG IS m b HO ML0) as (t & i & c0 & bt & Ha & Ht & Htop & Hft) ]).
    assert (Et : t = g) by (apply (top_unique _ _ _ IG t g bt bm Ht Hg Htop MLg); rewrite Hft, Hf; reflexivity). subst t.
    (first [ pose proof ((anc_facts _ _ _ _ IM IG IS _ _ _ _ Ha)) as dR_8; dex2 dR_8 as bm' bp; dand10 dR_8 as _ _ _ _ _ _ _ _ _ SCp | pose proof ((anc_facts _ _ _ _ IM IG IS _ _ _ _ Ha)) as dR_8; dand12 dR_8 as bm' bp _ _ _ _ _ _ _ _ _ SCp | destruct (anc_facts _ _ _ _ IM IG IS _ _ _ _ Ha) as (bm' & bp & _ & _ & _ & _ & _ & _ & _ & _ & _ & SCp) ]). rewrite SC63 in SCp. lia.
  - pose proof (top_unique _ _ _ IG m g b bm HO Hg ML0 MLg Hf) as ->. exact (hosts_inj _ _ _ IM _ _ _ HO Hg).
Qed.
(* [comment removed for export] *)
#[using="IS IG IM NB0 ND0 SC63 Hg INV bm ND NB LS BL L Clg"] Lemma rm_only_slot s m i : s_slots st !! s = Some (m, i) -> fst s = rid -> s = c /\ m = g /\ i = 0.
Proof.
  intros Hs Hf. (first [ pose proof ((is_valid _ _ _ IS _ _ _ Hs)) as dR_9; dand3 dR_9 as [b Hb] Hi Es | destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hi & Es) ]).
  rewrite (slot_start'_eq _ _ _ IM _ _ i Hb) in Es.
  assert (Fb : fst b = rid) by (rewrite Es in Hf; exact Hf).
  destruct Hb as [ai Hb']. pose proof (rm_only_group b _ Hb' Fb) as ->.
  pose proof (hosts_fun st bm m g (ex_intro _ ai Hb') Hg) as ->.
  pose proof rm_gfacts as (L0 & _). assert (i = 0) by lia. subst i. rewrite <- rm_c in Es. auto.
Qed.
#[using="IS IG IM NB0 ND0 SC63 Hg Hk INV bm ND NB g LS L st Clg"] Lemma rm_only_block k' : In k' BL -> fst (bslot k') = rid -> k' = k.
Proof.
  intros Hk' Hf. (first [ pose proof ((is_blocks _ _ _ IS k' Hk')) as dR_10; dex2 dR_10 as m i; destruct dR_10 as [Hs _] | pose proof ((is_blocks _ _ _ IS k' Hk')) as dR_10; dand4 dR_10 as m i Hs _ | destruct (is_blocks _ _ _ IS k' Hk') as (m & i & Hs & _) ]).
  (first [ pose proof ((rm_only_slot _ _ _ Hs Hf)) as dR_11; dand3 dR_11 as Es _ _ | destruct (rm_only_slot _ _ _ Hs Hf) as (Es & _ & _) ]).
  assert (EQ : bslot k' = bslot k) by exact Es.
  (first [ pose proof ((bl_remove_split BL k (is_nodup _ _ _ IS) Hk)) as dR_12; dex2 dR_12 as l1 l2; dand4 dR_12 as EBL _ M1 M2 | pose proof ((bl_remove_split BL k (is_nodup _ _ _ IS) Hk)) as dR_12; dand6 dR_12 as l1 l2 EBL _ M1 M2 | destruct (bl_remove_split BL k (is_nodup _ _ _ IS) Hk) as (l1 & l2 & EBL & _ & M1 & M2) ]).
  rewrite EBL in Hk'. apply in_app_iff in Hk'. destruct Hk' as [H|[H|H]]; [exfalso; apply M1| symmetry; exact H| exfalso; apply M2];
    rewrite <- EQ; apply in_map; exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition X1 : extras := mkX [] [] (Some c) None None.
Definition BL1 : list blk := bl_remove c BL.
Definition st0 : mstate := set_tick (N.succ (s_tick st)) st.
Definition r' : region := mkRegion RKGroup NB ND.
Definition ML' : Z := ND / 4096.
Definition stR : mstate := set_regions (<[rid := r']> (s_regions st0)) st0.
Definition stM : mstate := upd_meta g (m_set_maplen ML') stR.
Definition stH : mstate := if OLDL <? ND then havoc (rid, OLDL) (ND - OLDL) stM else stM.
Definition stE : mstate := wr8 (rid, ND - 4) 0 stH.
Definition G0 : list (Z * Z) := map gpair (List.filter isG (map_to_list (delete rid (s_regions st)))).
Definition L' : mled := KInv.set_groups ((NB, ND) :: G0) L.

#[using="NB0 NDX NDA ND0 NB"] Lemma ML'_eq : ML' * 4096 = ND /\ 1 <= ML' < 2 ^ 28.
Proof. unfold ML'. pose proof (Z.div_mod ND 4096 ltac:(lia)). rewrite NDA in H. split; [lia|]. split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia]. Qed.
#[using="ND NB"] Lemma land52 v : 0 <= v < 2 ^ 52 -> Z.land v (2 ^ 52 - 1) = v.
Proof. intros Hv. change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
#[using="INV ND NB"] Lemma rm_I0 : INVL x0 st0 L BL LS.
Proof. apply INVL_set_tick; [cbn; lia| exact INV]. Qed.
#[using="Hk INV k ND NB old off"] Lemma rm_I1 : INVL X1 st0 L BL1 LS.
Proof.
  pose proof rm_I0 as I0.
  apply (INVL_remove_block x0 st0 st0 L BL LS k I0 Hk eq_refl (ctrl_eq_refl _) eq_refl).
  - intros; reflexivity.
  - exact (DOMS_of _ _ _ _ _ I0).
  - exact (TKS_of _ _ _ _ _ I0).
Qed.

(* [comment removed for export] *)
Lemma E_ctx : s_ctx stE = s_ctx st.
Proof. unfold stE, stH. rewrite s_ctx_wr8. destruct (OLDL <? ND); rewrite ?s_ctx_havoc; reflexivity. Qed.
Lemma E_regions : s_regions stE = <[rid := r']> (s_regions st).
Proof. unfold stE, stH. rewrite s_regions_wr8. destruct (OLDL <? ND); rewrite ?s_regions_havoc; reflexivity. Qed.
Lemma E_metas : s_metas stE = s_metas stM.
Proof. unfold stE, stH. rewrite s_metas_wr8. destruct (OLDL <? ND); rewrite ?s_metas_havoc; reflexivity. Qed.
Lemma E_areas : s_areas stE = s_areas st.
Proof. unfold stE, stH. rewrite s_areas_wr8. destruct (OLDL <? ND); rewrite ?s_areas_havoc; reflexivity. Qed.
Lemma E_groups : s_groups stE = s_groups st.
Proof. unfold stE, stH. rewrite s_groups_wr8. destruct (OLDL <? ND); rewrite ?s_groups_havoc; reflexivity. Qed.
Lemma E_slots : s_slots stE = s_slots st.
Proof. unfold stE, stH. rewrite s_slots_wr8. destruct (OLDL <? ND); rewrite ?s_slots_havoc; reflexivity. Qed.
Lemma E_secret : s_secret stE = s_secret st.
Proof. unfold stE, stH. rewrite s_secret_wr8. destruct (OLDL <? ND); rewrite ?s_secret_havoc; reflexivity. Qed.
Lemma E_reserved : s_reserved stE = s_reserved st.
Proof. unfold stE, stH. rewrite s_reserved_wr8. destruct (OLDL <? ND); rewrite ?s_reserved_havoc; reflexivity. Qed.
Lemma E_next_rid : s_next_rid stE = s_next_rid st.
Proof. unfold stE, stH. rewrite s_next_rid_wr8. destruct (OLDL <? ND); rewrite ?s_next_rid_havoc; reflexivity. Qed.
Lemma E_tick : s_tick stE = N.succ (s_tick st).
Proof. unfold stE, stH. rewrite s_tick_wr8. destruct (OLDL <? ND); rewrite ?s_tick_havoc; reflexivity. Qed.

Lemma E_MR x : MR stE x = if aptr_eqb x g then m_set_maplen ML' (MR st g) else MR st x.
Proof.
  unfold MR, get_meta_rec. rewrite E_metas. unfold stM. rewrite lookup_metas_upd.
  destruct (aptr_eqb x g); reflexivity.
Qed.
Lemma E_MR_other x : x <> g -> MR stE x = MR st x.
Proof. intros NE. rewrite E_MR, aptr_eqb_neq by exact NE. reflexivity. Qed.
Lemma E_MR_g : MR stE g = m_set_maplen ML' (MR st g).
Proof. rewrite E_MR, aptr_eqb_refl. reflexivity. Qed.
#[using="NB0 NDX NDA ND0"] Lemma E_maplen_g : m_maplen (MR stE g) = ML'.
Proof. rewrite E_MR_g. cbn. apply land52. pose proof ML'_eq. lia. Qed.
Lemma E_fields x : m_mem (MR stE x) = m_mem (MR st x) /\ m_prev (MR stE x) = m_prev (MR st x) /\ m_next (MR stE x) = m_next (MR st x)
  /\ m_avail (MR stE x) = m_avail (MR st x) /\ m_freed (MR stE x) = m_freed (MR st x) /\ m_last_idx (MR stE x) = m_last_idx (MR st x)
  /\ m_freeable (MR stE x) = m_freeable (MR st x) /\ m_sizeclass (MR stE x) = m_sizeclass (MR st x).
Proof. rewrite E_MR. destruct (aptr_eqb_spec x g) as [->|NE]; cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.
Lemma E_mem x : m_mem (MR stE x) = m_mem (MR st x). Proof. apply E_fields. Qed.
Lemma E_last x : m_last_idx (MR stE x) = m_last_idx (MR st x). Proof. apply E_fields. Qed.
Lemma E_sc x : m_sizeclass (MR stE x) = m_sizeclass (MR st x). Proof. apply E_fields. Qed.
Lemma E_gbase x : gbase (MR stE x) = gbase (MR st x). Proof. unfold gbase. rewrite E_mem. reflexivity. Qed.
Lemma E_maplen_other x : x <> g -> m_maplen (MR stE x) = m_maplen (MR st x).
Proof. intros NE. rewrite E_MR_other by exact NE. reflexivity. Qed.
Lemma E_stride_other x : x <> g -> get_stride (MR stE x) = get_stride (MR st x).
Proof. intros NE. rewrite E_MR_other by exact NE. reflexivity. Qed.
#[using="IG NB0 NDX NDA ND0 SC63 Hg INV bm LS BL L Clg"] Lemma E_stride_g : get_stride (MR stE g) = ND - UNIT.
Proof.
  pose proof rm_gfacts as (L0 & _). pose proof ML'_eq as [E _]. unfold get_stride. rewrite E_last, L0, E_maplen_g. cbn [Z.eqb andb].
  destruct (Z.eqb_spec ML' 0); [lia|]. cbn. lia.
Qed.
Lemma E_sstart_other x i : x <> g -> sstart (MR stE x) i = sstart (MR st x) i.
Proof. intros NE. unfold sstart. rewrite E_gbase, E_stride_other by exact NE. reflexivity. Qed.
#[using="IG IM NB0 NDX NDA ND0 SC63 Hg INV bm LS BL L Clg"] Lemma E_sstart_g i : sstart (MR stE g) i = UNIT + (ND - UNIT) * i.
Proof. unfold sstart. rewrite E_gbase, rm_gbase, E_stride_g. cbn. lia. Qed.
#[using="IG IM NB0 NDX NDA ND0 SC63 Hg INV bm LS BL L Clg"] Lemma E_sstart_g0 : sstart (MR stE g) 0 = sstart (MR st g) 0.
Proof. rewrite E_sstart_g. unfold sstart. rewrite rm_gbase. cbn. lia. Qed.
Lemma E_slot_start' x i : x <> g -> slot_start' (MR stE x) i = slot_start' (MR st x) i.
Proof. intros NE. rewrite !slot_start'_sstart, E_gbase, E_sstart_other by exact NE. reflexivity. Qed.
#[using="IG IM NB0 NDX NDA ND0 SC63 Hg INV bm LS BL L Clg"] Lemma E_slot_start'_g0 : slot_start' (MR stE g) 0 = slot_start' (MR st g) 0.
Proof. rewrite !slot_start'_sstart, E_gbase, E_sstart_g0. reflexivity. Qed.
Lemma E_cnt x : cnt_of (MR stE x) = cnt_of (MR st x). Proof. unfold cnt_of. rewrite E_last. reflexivity. Qed.

Lemma E_lookup q : s_regions stE !! q = if (q =? rid)%N then Some r' else s_regions st !! q.
Proof. rewrite E_regions. destruct (N.eqb_spec q rid) as [->|NE]; [apply lookup_insert_eq| rewrite lookup_insert_ne by congruence; reflexivity]. Qed.
Lemma E_some q rq : s_regions stE !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ s_regions st !! q = Some rq).
Proof. rewrite E_lookup. destruct (N.eqb_spec q rid) as [->|NE]; [intros H; inversion H; auto| auto]. Qed.
Lemma E_keep q rq : q <> rid -> s_regions st !! q = Some rq -> s_regions stE !! q = Some rq.
Proof. intros NE H. rewrite E_lookup. destruct (N.eqb_spec q rid) as [->|]; [congruence| exact H]. Qed.
Lemma E_rid : s_regions stE !! rid = Some r'.
Proof. rewrite E_lookup, N.eqb_refl. reflexivity. Qed.
Lemma E_hosts b m : hosts stE b m <-> hosts st b m.
Proof. apply hosts_ext. apply E_groups. Qed.
Lemma E_frontier q rq : frontier stE q rq = frontier st q rq.
Proof. unfold frontier. rewrite E_ctx. reflexivity. Qed.

(* [comment removed for export] *)
#[using="IG NB0 ND0 SC63 Hg INV bm ND NB rid LS BL L Clg"] Lemma OLDL16 : OLDL mod 16 = 0 /\ 4096 <= OLDL.
Proof.
  unfold OLDL. (first [ pose proof (rm_gfacts) as dR_13; dand4 dR_13 as _ ML _ ML0 | pose proof rm_gfacts as (_ & ML & _ & ML0) ]). split; [| nia].
  replace (m_maplen (MR st g) * 4096) with ((m_maplen (MR st g) * 256) * 16) by lia. apply Z_mod_mult.
Qed.
#[using="INV LS BL L Clg"] Lemma M_TKS : TKS stM (s_tick st0).
Proof.
  intros q sh Hq. unfold stM, stR in Hq. rewrite s_shadow_upd_meta in Hq. cbn [s_shadow set_regions] in Hq.
  exact (TKS_of _ _ _ _ _ rm_I0 q sh Hq).
Qed.
Lemma M_tick : s_tick stM = s_tick st0. Proof. reflexivity. Qed.
Lemma M_read q : cell_read (get_shadow stM (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof. reflexivity. Qed.
Lemma H_tick : s_tick stH = s_tick st0. Proof. unfold stH. destruct (OLDL <? ND); [rewrite s_tick_havoc|]; reflexivity. Qed.
#[using="IG NB0 ND0 SC63 Hg INV bm LS BL L Clg"] Lemma H_TKS : TKS stH (s_tick st0).
Proof.
  unfold stH. destruct (Z.ltb_spec OLDL ND); [| exact M_TKS].
  rewrite <- M_tick. apply TKS_havoc; [cbn [snd]; exact (proj1 OLDL16)| lia| rewrite M_tick; exact M_TKS].
Qed.
#[using="INV LS BL L Clg"] Lemma M_hav u hl : r_hav (get_shadow stM rid) !! u = Some hl -> hl_ticks hl (s_tick stM).
Proof. intros Hu ch Hch. exact (proj1 (sh_ticks_of _ _ M_TKS) u hl ch Hu Hch). Qed.
#[using="IG NB0 ND0 SC63 Hg INV bm LS BL L Clg"] Lemma H_read q : ~ (fst q = rid /\ OLDL <= snd q < ND) ->
  cell_read (get_shadow stH (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
  intros Hq. unfold stH. destruct (Z.ltb_spec OLDL ND); [| apply M_read].
  rewrite (cell_read_havoc_out (rid, OLDL) (ND - OLDL) stM (proj1 OLDL16) ltac:(lia) M_hav q).
  - apply M_read.
  - cbn [fst snd]. intros [F R]. apply Hq. split; [exact F| lia].
Qed.
(* [comment removed for export] *)
#[using="IG NB0 ND0 SC63 Hg INV bm LS BL L Clg"] Lemma E_TKS : TKS stE (s_tick st0).
Proof. unfold stE. apply TKS_wr8; [rewrite H_tick; lia| exact H_TKS]. Qed.
#[using="IG NB0 ND0 SC63 Hg INV bm LS BL L Clg"] Lemma E_read q : ~ (fst q = rid /\ OLDL <= snd q < ND) -> q <> (rid, ND - 4) ->
  cell_read (get_shadow stE (fst q)) (snd q) = cell_read (get_shadow st (fst q)) (snd q).
Proof.
  intros H1 H2. unfold stE. rewrite cell_read_wr8_other by (destruct q; cbn; congruence). apply H_read. exact H1.
Qed.
#[using="IG NB0 ND0 SC63 Hg INV bm LS BL L Clg"] Lemma E_known_end : known stE (rid, ND - 4) 0.
Proof.
  unfold known, SHd, stE. cbn [fst snd]. rewrite (cell_read_wr8_same (rid, ND - 4) 0 stH); [reflexivity|].
  cbn [fst]. apply sh_ticks_of. pose proof H_TKS as TK. rewrite <- H_tick in TK. exact TK.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hr"] Lemma perm_regions_old : Permutation (map_to_list (s_regions st)) ((rid, r) :: map_to_list (delete rid (s_regions st))).
Proof. apply Permutation_sym. apply map_to_list_delete. exact Hr. Qed.
Lemma perm_regions_new : Permutation (map_to_list (s_regions stE)) ((rid, r') :: map_to_list (delete rid (s_regions st))).
Proof. rewrite E_regions, <- insert_delete_eq. apply map_to_list_insert. apply lookup_delete_eq. Qed.
#[using="IG IR Hr Hg INV bm g LS BL Clg"] Lemma groups_old_perm : Permutation (ld_groups L) ((r_base r, r_len r) :: G0).
Proof.
  eapply Permutation_trans; [exact (ir_groups _ _ _ IR)|].
  change (Permutation (map gpair (List.filter isG (map_to_list (s_regions st)))) (gpair (rid, r) :: G0)). unfold G0.
  rewrite <- map_cons. apply Permutation_map.
  eapply Permutation_trans; [apply perm_filter; exact perm_regions_old|]. cbn [List.filter]. unfold isG at 1. cbn [snd]. rewrite rm_kind. apply Permutation_refl.
Qed.

#[using="IG IR DISJ NBC NBA NB0 NDX NDA ND0 Hr SC63 Hg Hk INV k bm old off r LS BL"] Lemma A_inv_R : inv_R X1 stE L'.
Proof.
  pose proof (proj1 rm_I1) as IR1. pose proof ML'_eq as [MLE MLR]. pose proof rm_top as [OT _].
  (first [ pose proof ((ir_shape _ _ _ IR _ _ Hr)) as dR_14; dand6 dR_14 as RB0 RBA RL0 RLM RCE _ | pose proof (ir_shape _ _ _ IR _ _ Hr) as (RB0 & RBA & RL0 & RLM & RCE & _) ]).
  destruct IR1; constructor; rewrite ?E_ctx, ?E_next_rid, ?E_reserved.
  - intros q rq Hq. apply E_some in Hq as [[-> _]|[_ Hq]]; [exact (ir_ids _ _ Hr)| exact (ir_ids q rq Hq)].
  - intros q rq Hq. apply E_some in Hq as [[-> ->]|[_ Hq]]; [| exact (ir_shape q rq Hq)]. cbn [r_base r_len r_kind r'].
    rewrite (MI_W2ig.round_up_pg_id ND NDA). unfold LEN_MAX, PGSZ. split; [lia|]. split; [exact NBA|]. split; [lia|]. split; [lia|]. split; [exact NBC|].
    intros [K|K]; discriminate.
  - intros q1 q2 r1 r2 H1 H2 NE.
    apply E_some in H1 as [[-> ->]|[N1 H1]]; apply E_some in H2 as [[-> ->]|[N2 H2]]; [congruence| | | exact (ir_disj q1 q2 r1 r2 H1 H2 NE)].
    + unfold region_live_range at 1. cbn [r_kind r_base r_len r']. rewrite (MI_W2ig.round_up_pg_id ND NDA).
      pose proof (DISJ q2 r2 ltac:(congruence) H2) as D. destruct (region_live_range r2) as [b2 l2]. lia.
    + pose proof (DISJ q1 r1 ltac:(congruence) H1) as D. destruct (region_live_range r1) as [b1 l1].
      unfold region_live_range. cbn [r_kind r_base r_len r']. rewrite (MI_W2ig.round_up_pg_id ND NDA). lia.
  - exact ir_resv.
  - unfold L'. cbn [ld_groups KInv.set_groups].
    change (Permutation ((NB, ND) :: G0) (map gpair (List.filter isG (map_to_list (s_regions stE))))).
    eapply Permutation_trans; [| apply Permutation_map; apply perm_filter; apply Permutation_sym; exact perm_regions_new].
    cbn [List.filter isG snd r_kind r' map gpair r_base r_len]. apply Permutation_refl.
  - unfold L'. cbn [ld_metas KInv.set_groups]. eapply Permutation_trans; [exact ir_metas|].
    eapply Permutation_trans; [apply Permutation_map; apply perm_filter; exact perm_regions_old|].
    eapply Permutation_trans; [| apply Permutation_map; apply perm_filter; apply Permutation_sym; exact perm_regions_new].
    cbn [List.filter snd r_kind r']. rewrite rm_kind.
    erewrite map_ext; [apply Permutation_refl|]. intros [q rq]. cbn. rewrite E_frontier. reflexivity.
  - intros q rq Hq K. apply E_some in Hq as [[-> ->]|[_ Hq]]; [discriminate|]. rewrite E_frontier. exact (ir_metalen q rq Hq K).
  - intros q rq Hq K. apply E_some in Hq as [[-> ->]|[_ Hq]]; [discriminate|]. rewrite E_frontier. exact (ir_brkfront q rq Hq K).
  - destruct ir_shift as [S1 [S2|(q & rq & Hq & K & E)]]; split; [exact S1| left; exact S2| exact S1|].
    right. exists q, rq. split; [apply E_keep; [intros ->; rewrite Hr in Hq; assert (rq = r) by congruence; subst rq; rewrite rm_kind in K; discriminate| exact Hq]| auto].
  - intros b l. unfold L'. cbn [ld_brkreg KInv.set_groups]. rewrite ir_brkreg. split; ((first [ intro dR_69; dex2 dR_69 as q rq; dand4 dR_69 as Hq K E1 E2 | intro dR_69; dand6 dR_69 as q rq Hq K E1 E2 | intros (q & rq & Hq & K & E1 & E2) ])); exists q, rq.
    + split; [apply E_keep; [intros ->; rewrite Hr in Hq; assert (rq = r) by congruence; subst rq; rewrite rm_kind in K; discriminate| exact Hq]| auto].
    + apply E_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| auto].
  - intros q1 q2 r1 r2 H1 H2 K1 K2. apply E_some in H1 as [[-> ->]|[_ H1]]; [discriminate|]. apply E_some in H2 as [[-> ->]|[_ H2]]; [discriminate|].
    exact (ir_brk1 q1 q2 r1 r2 H1 H2 K1 K2).
  - unfold L'. cbn [ld_brk ld_brkreg KInv.set_groups]. revert ir_brk. unfold st0. rewrite s_ctx_set_tick.
    destruct (c_brk (s_ctx st)) as [| |brid boff]; intros IBK.
    + destruct IBK as [B NBK]. split; [exact B|]. intros q rq Hq. apply E_some in Hq as [[-> ->]|[_ Hq]]; [discriminate| exact (NBK q rq Hq)].
    + exact IBK.
    + destruct IBK as [B (rq & Hq & K & E)]. split; [exact B|]. exists rq.
      split; [apply E_keep; [intros ->; unfold st0 in Hq; rewrite s_regions_set_tick, Hr in Hq; assert (rq = r) by congruence; subst rq; rewrite rm_kind in K; discriminate| exact Hq]| auto].
  - (first [ dand3 ir_cursor as C1 C2 C3 | destruct ir_cursor as (C1 & C2 & C3) ]). split; [exact C1|]. split; [exact C2|].
    intros q off0 E. (first [ pose proof ((C3 q off0 E)) as dR_16; dex1 dR_16 as rq; dand3 dR_16 as Hq K B | pose proof ((C3 q off0 E)) as dR_16; dand4 dR_16 as rq Hq K B | destruct (C3 q off0 E) as (rq & Hq & K & B) ]). exists rq.
    split; [apply E_keep; [intros ->; unfold st0 in Hq; rewrite s_regions_set_tick, Hr in Hq; assert (rq = r) by congruence; subst rq; destruct K as [K|K]; rewrite rm_kind in K; discriminate| exact Hq]| auto].
  - intros q Hq. cbn in Hq. discriminate.
Qed.
#[using="IG Hoff Hg INV bm off LS BL L Clg"] Lemma E_keys x : s_metas stE !! x <> None <-> s_metas st !! x <> None.
Proof.
  rewrite E_metas. unfold stM. rewrite lookup_metas_upd. cbn [s_metas stR set_regions st0 set_tick].
  destruct (aptr_eqb_spec x g) as [->|NE]; [| tauto].
  split; [| intros; discriminate]. intros _. destruct Hg as [ai Hb]. exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)).
Qed.
#[using="IG IA Hr Hg INV bm g r LS BL L Clg"] Lemma E_area_region a ar : s_areas st !! a = Some ar -> fst a <> rid.
Proof.
  intros Ha E. destruct (ia_areas _ IA a ar Ha) as ((rq & Hq & K & _) & _). rewrite E, Hr in Hq.
  assert (rq = r) by congruence. subst rq. destruct K as [K|K]; rewrite rm_kind in K; discriminate.
Qed.

#[using="IG IA Hoff Hr Hg Hk INV k c bm old off r LS BL L Clg"] Lemma A_inv_A : inv_A stE.
Proof.
  pose proof (proj1 (proj2 rm_I1)) as IA1.
  assert (Gpres : s_metas st !! g <> None) by (destruct Hg as [ai Hb]; exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb))).
  destruct IA1; constructor; rewrite ?E_ctx, ?E_areas, ?E_secret; try assumption.
  - intros a ar Ha. destruct (ia_areas a ar Ha) as ((rq & Hq & K & M & P & F) & rest). split; [| exact rest].
    exists rq. rewrite E_frontier. split; [apply E_keep; [exact (E_area_region a ar Ha)| exact Hq]| auto].
  - intros m mr Hm. assert (K : s_metas stE !! m <> None) by congruence. apply E_keys in K.
    destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
  - destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & ? & ? & Hk0). exists a. split; [assumption|]. split; [assumption|].
    intros k0 Hk2. destruct (s_metas stE !! mslot a k0) eqn:E; [| reflexivity]. exfalso.
    assert (K : s_metas stE !! mslot a k0 <> None) by congruence. apply E_keys in K. apply K. apply Hk0. exact Hk2.
  - intros q Hq. (first [ pose proof ((ia_availptr q Hq)) as dR_17; dex1 dR_17 as rq; destruct dR_17 as [Hrq K] | pose proof ((ia_availptr q Hq)) as dR_17; dand3 dR_17 as rq Hrq K | destruct (ia_availptr q Hq) as (rq & Hrq & K) ]). exists rq. split; [| exact K].
    apply E_keep; [| exact Hrq]. intros E. rewrite E in Hrq. cbn [s_regions st0 set_tick] in Hrq. rewrite Hr in Hrq.
    assert (rq = r) by congruence. subst rq. destruct K as [K|K]; rewrite rm_kind in K; discriminate.
  - intros sc Hsc. unfold usage, ctx. rewrite E_ctx. change (s_ctx st) with (s_ctx st0). fold (ctx st0). fold (usage st0 sc). rewrite (ia_usage sc Hsc).
    unfold gcnt. rewrite E_groups. change (s_groups st) with (s_groups st0). f_equal. apply map_ext. intros [bb h]. cbn. destruct (g_meta h); [| reflexivity].
    rewrite E_sc, E_cnt. reflexivity.
Qed.

#[using="IM Hg Hk INV k bm old off BL L Clg"] Lemma A_inv_M : inv_M X1 stE LS.
Proof.
  pose proof (proj1 (proj2 (proj2 rm_I1))) as IM1.
  destruct IM1 as [M1 M2 M3 M4 M5]; constructor.
  - intros m Hm. rewrite E_mem in Hm. rewrite E_MR. destruct (aptr_eqb_spec m g) as [->|NE].
    + exfalso. pose proof (hosts_mem _ _ _ IM _ _ Hg). change (MR st0 g) with (MR st g) in Hm. congruence.
    + apply M1. exact Hm.
  - intros m bb Hm. rewrite E_mem in Hm. setoid_rewrite E_hosts. apply M2. exact Hm.
  - intros bb h Hb. rewrite E_groups in Hb. destruct (M3 bb h Hb) as (m & ? & ? & ?). exists m. rewrite E_mem, E_last. auto.
  - intros m Hm. cbn in Hm. destruct Hm.
  - intros z Hz. cbn in Hz. destruct Hz.
Qed.

#[using="IM Hg Hk INV k c bm old off BL L Clg"] Lemma A_inv_L : inv_L stE LS.
Proof.
  pose proof (proj1 (proj2 (proj2 (proj2 rm_I1)))) as IL1.
  destruct IL1 as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor.
  - intros h. rewrite <- (L1 h). apply (get_head_ext st0 stE). exact E_ctx.
  - intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l]; [exact I|]. cbn [dll] in D |- *.
    eapply linked_ext; [| | exact D]; intros; [apply (proj1 (proj2 (proj2 (E_fields _))))| apply (proj1 (proj2 (E_fields _)))].
  - exact L3.
  - exact L4.
  - intros m. rewrite (proj1 (proj2 (proj2 (E_fields m)))), (proj1 (proj2 (E_fields m))). apply L5.
  - intros m Hm. rewrite E_MR. destruct (aptr_eqb_spec m g) as [->|NE]; [| apply L6; exact Hm].
    exfalso. pose proof (L6 g Hm) as Z0. pose proof (hosts_mem _ _ _ IM _ _ Hg) as Hmem. change (MR st0 g) with (MR st g) in Z0. rewrite Z0 in Hmem. cbn in Hmem. discriminate.
  - intros sc m Hm. rewrite (live_group_ext st0 stE E_groups), E_sc. apply L7. exact Hm.
  - exact L9.
Qed.

#[using="IS IG IM Hoff NB0 NDX NDA ND0 SC63 Hg Hk INV k bm old off BL L Clg"] Lemma A_inv_G : inv_G X1 stE LS.
Proof.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 rm_I1))))) as IG1. pose proof ML'_eq as [MLE MLR]. (first [ pose proof (rm_gfacts) as dR_18; dand4 dR_18 as L0 MLg NIL ML0 | pose proof rm_gfacts as (L0 & MLg & NIL & ML0) ]).
  destruct IG1 as [G1 G2 G3 G4 G5]. constructor.
  - intros m b ai Hb. rewrite E_groups in Hb. pose proof (G1 m b ai Hb) as GO.
    destruct (aptr_eqb_spec m g) as [->|NE].
    + (* [comment removed for export] *)
      pose proof (hosts_inj _ _ _ IM _ _ _ (ex_intro _ ai Hb) Hg) as Ebb. subst b.
      destruct GO as [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 Q16]; constructor;
        rewrite ?E_MR_g; cbn [m_last_idx m_sizeclass m_maplen m_freeable m_avail m_freed m_mem m_set_maplen]; rewrite ?land52 by lia;
        change (MR st0 g) with (MR st g) in *; try assumption.
      * apply E_keys. exact Q1.
      * right. rewrite SC63. split; [reflexivity|]. split; [exact L0|]. split; [lia| exact NIL].
      * lia.
      * intros SC. exfalso. rewrite SC63 in SC. lia.
      * intros NF SC. exfalso. rewrite SC63 in SC. lia.
      * intros _. split; [reflexivity|]. exists r'. split; [exact E_rid|]. split; [reflexivity|]. cbn [r_len r'].
        rewrite (MI_W2ig.round_up_pg_id ND NDA). split; [lia|].
        pose proof (E_sstart_g 1) as ES. unfold gend, cnt_of. rewrite E_MR_g in ES. cbn [m_last_idx m_set_maplen]. rewrite L0. change (0 + 1) with 1. rewrite ES. unfold UNIT. lia.
      * intros ML. exfalso. lia.
    + assert (Fb : fst b <> rid).
      { intros F. apply NE. pose proof (rm_only_group b _ Hb F) as ->. exact (hosts_fun st bm m g (ex_intro _ ai Hb) Hg). }
      destruct GO as [Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 Q16]; constructor; rewrite ?(E_MR_other m NE), ?E_slots; change (MR st0 m) with (MR st m) in *; try assumption.
      * apply E_keys. exact Q1.
      * intros ML. (first [ pose proof ((Q14 ML)) as dR_19; dand6 dR_19 as H0 rq Hq Kq E1 E2 | destruct (Q14 ML) as (H0 & rq & Hq & Kq & E1 & E2) ]). split; [exact H0|]. exists rq. split; [apply E_keep; [exact Fb| exact Hq]| auto].
      * intros ML. (first [ pose proof ((Q15 ML)) as dR_20; dex2 dR_20 as p i; dand5 dR_20 as Hs Hf GE SCC STR | pose proof ((Q15 ML)) as dR_20; dand7 dR_20 as p i Hs Hf GE SCC STR | destruct (Q15 ML) as (p & i & Hs & Hf & GE & SCC & STR) ]). exists p, i.
        assert (NP : p <> g).
        { intros ->. (first [ pose proof ((rm_only_slot b g i Hs ltac:(rewrite <- Hf, rm_gbase; reflexivity))) as dR_21; dand3 dR_21 as -> _ _ | destruct (rm_only_slot b g i Hs ltac:(rewrite <- Hf, rm_gbase; reflexivity)) as (-> & _ & _) ]). rewrite rm_NH in Hb. discriminate. }
        rewrite E_gbase, (E_MR_other p NP). change (s_slots st0) with (s_slots st) in Hs. auto 10.
  - intros bb aim H. rewrite E_groups in H. eapply G2. exact H.
  - intros m1 m2 b1 b2 ai1 ai2 H1 H2. rewrite E_groups in H1, H2. rewrite !E_last, !E_sc. eapply G3; eassumption.
  - intros q rq Hq Kq Ho. apply E_some in Hq as [[-> ->]|[NEq Hq]].
    + exists g. split; [apply E_hosts; exact Hg| rewrite E_maplen_g; lia].
    + (first [ pose proof ((G4 q rq Hq Kq Ho)) as dR_22; dex1 dR_22 as m; destruct dR_22 as [Hm Hml] | pose proof ((G4 q rq Hq Kq Ho)) as dR_22; dand3 dR_22 as m Hm Hml | destruct (G4 q rq Hq Kq Ho) as (m & Hm & Hml) ]). exists m.
      assert (NE : m <> g).
      { intros ->. apply NEq. destruct Hm as [aix Hbx]. pose proof (hosts_inj _ _ _ IM _ _ _ (ex_intro _ aix Hbx) Hg) as E. apply (f_equal fst) in E. cbn in E. exact E. }
      rewrite E_hosts, E_maplen_other by exact NE. auto.
  - intros b h H. rewrite E_groups in H. (first [ pose proof ((G5 b h H)) as dR_23; dex1 dR_23 as rq; destruct dR_23 as [Hq K] | pose proof ((G5 b h H)) as dR_23; dand3 dR_23 as rq Hq K | destruct (G5 b h H) as (rq & Hq & K) ]).
    destruct (N.eq_dec (fst b) rid) as [E|NE].
    + exists r'. rewrite E, E_rid. auto.
    + exists rq. split; [apply E_keep; [exact NE| exact Hq]| exact K].
Qed.
#[using="IS Hoff Hk INV k old off LS L st Clg"] Lemma BL1_in k' : In k' BL1 -> In k' BL /\ bslot k' <> c.
Proof.
  intros H. unfold BL1 in H.
  (first [ pose proof ((bl_remove_split BL k (is_nodup _ _ _ IS) Hk)) as dR_24; dex2 dR_24 as l1 l2; dand4 dR_24 as EBL EBL' M1 M2 | pose proof ((bl_remove_split BL k (is_nodup _ _ _ IS) Hk)) as dR_24; dand6 dR_24 as l1 l2 EBL EBL' M1 M2 | destruct (bl_remove_split BL k (is_nodup _ _ _ IS) Hk) as (l1 & l2 & EBL & EBL' & M1 & M2) ]). cbn [bslot fst] in EBL', M1, M2.
  rewrite EBL' in H. rewrite EBL. apply in_app_iff in H. split.
  - apply in_app_iff. cbn. tauto.
  - intros E. change c with (bslot k) in E. destruct H as [H|H]; [apply M1| apply M2]; rewrite <- E; apply in_map; exact H.
Qed.
#[using="IS IG IM Hoff NB0 ND0 SC63 Hg Hk INV k bm ND NB old off LS L Clg"] Lemma BL1_region k' m i : In k' BL1 -> s_slots st !! bslot k' = Some (m, i) -> fst (bslot k') <> rid /\ m <> g.
Proof.
  intros Hk' Hs. destruct (BL1_in k' Hk') as [Hin NE].
  destruct (N.eq_dec (fst (bslot k')) rid) as [F|F].
  - exfalso. destruct (rm_only_slot _ _ _ Hs F) as (E & _). exact (NE E).
  - split; [exact F|]. intros ->. apply F. (first [ pose proof ((is_valid _ _ _ IS _ _ _ Hs)) as dR_25; dand3 dR_25 as [b Hb] Hi Es | destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hi & Es) ]).
    rewrite (slot_start'_eq _ _ _ IM _ _ i Hb) in Es. pose proof (hosts_inj _ _ _ IM _ _ _ Hb Hg) as ->. rewrite Es. reflexivity.
Qed.
#[using="IS IG IM NB0 ND0 SC63 Hg INV bm ND NB LS BL L Clg"] Lemma slot_g_i0 s i : s_slots st !! s = Some (g, i) -> i = 0 /\ s = c.
Proof.
  intros Hs. (first [ pose proof ((is_valid _ _ _ IS _ _ _ Hs)) as dR_26; dand3 dR_26 as [b Hb] Hi Es | destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & Hi & Es) ]). pose proof rm_gfacts as (L0 & _).
  assert (i = 0) by lia. subst i. split; [reflexivity|]. rewrite Es, (slot_start'_eq _ _ _ IM _ _ 0 Hg), <- rm_c. reflexivity.
Qed.

#[using="IS IG IM Hoff NB0 NDX NDA ND0 SC63 Hg Hk INV k bm old off LS L Clg"] Lemma A_inv_S : inv_S X1 stE BL1.
Proof.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 rm_I1)))))) as IS1. pose proof rm_gfacts as (L0 & _).
  destruct IS1 as [S1 S2 S3 S4 S5 S6]; constructor.
  - intros s m i Hs. rewrite E_slots in Hs. (first [ pose proof ((S1 s m i Hs)) as dR_27; dand3 dR_27 as LV Hi Es | destruct (S1 s m i Hs) as (LV & Hi & Es) ]). change (MR st0 m) with (MR st m) in *.
    rewrite (live_group_ext st0 stE E_groups), E_last. split; [exact LV|]. split; [exact Hi|].
    destruct (aptr_eqb_spec m g) as [->|NE]; [| rewrite E_slot_start' by exact NE; exact Es].
    destruct (slot_g_i0 s i Hs) as [-> ->]. rewrite E_slot_start'_g0. exact Es.
  - intros b m i Hb Hi. rewrite E_slots. rewrite E_last in Hi. apply E_hosts in Hb. change (MR st0 m) with (MR st m) in *.
    destruct (aptr_eqb_spec m g) as [->|NE]; [| rewrite E_slot_start' by exact NE; exact (S2 b m i Hb Hi)].
    assert (i = 0) by lia. subst i. rewrite E_slot_start'_g0. exact (S2 b g 0 Hb Hi).
  - intros b m ai i Hb Hi. rewrite E_groups in Hb. rewrite E_last in Hi. cbn zeta. rewrite E_groups. change (MR st0 m) with (MR st m) in *.
    pose proof (S3 b m ai i Hb Hi) as P. cbn zeta in P.
    rewrite (proj1 (proj2 (proj2 (proj2 (E_fields m))))), (proj1 (proj2 (proj2 (proj2 (proj2 (E_fields m)))))).
    destruct (aptr_eqb_spec m g) as [->|NE]; [| rewrite E_slot_start' by exact NE; exact P].
    assert (i = 0) by lia. subst i. rewrite E_slot_start'_g0. exact P.
  - intros s Hs. rewrite E_slots. exact (S4 s Hs).
  - exact S5.
  - intros k' Hk'. (first [ pose proof ((S6 k' Hk')) as dR_28; dex2 dR_28 as m i; destruct dR_28 as [Hs REST] | pose proof ((S6 k' Hk')) as dR_28; dand4 dR_28 as m i Hs REST | destruct (S6 k' Hk') as (m & i & Hs & REST) ]). exists m, i. rewrite E_slots. split; [exact Hs|].
    change (s_slots st0) with (s_slots st) in Hs. destruct (BL1_region k' m i Hk' Hs) as [_ NE]. rewrite E_stride_other by exact NE. exact REST.
Qed.

#[using="IS IG IM Hoff NB0 NDX NDA ND0 SC63 Hg Hk INV k bm old off LS L Clg"] Lemma A_inv_SH : inv_SH stE BL1.
Proof.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 rm_I1)))))) as ISH1. pose proof rm_gfacts as (L0 & _). pose proof OLDL16 as [O16 O4096].
  assert (KE : forall q v, ~ (fst q = rid /\ OLDL <= snd q < ND) -> q <> (rid, ND - 4) -> known st q v -> known stE q v).
  { intros q v H1 H2 K. unfold known, SHd in *. rewrite (E_read q H1 H2). exact K. }
  assert (UE : forall q, ~ (fst q = rid /\ OLDL <= snd q < ND) -> q <> (rid, ND - 4) -> unknown st q -> unknown stE q).
  { intros q H1 H2 K. unfold unknown, SHd in *. rewrite (E_read q H1 H2). exact K. }
  assert (KEo : forall q v, fst q <> rid -> known st q v -> known stE q v) by (intros q v F K; apply KE; [tauto| intros E; apply F; rewrite E; reflexivity| exact K]).
  assert (UEo : forall q, fst q <> rid -> unknown st q -> unknown stE q) by (intros q F K; apply UE; [tauto| intros E; apply F; rewrite E; reflexivity| exact K]).
  destruct ISH1 as [D1 D2 D3 D4 D5 D6]; constructor.
  - intros q sh Hq.
    assert (OLD : forall q' sh', s_shadow st !! q' = Some sh' -> exists rq, s_regions stE !! q' = Some rq /\ r_kind rq = RKGroup).
    { intros q' sh' H. (first [ pose proof ((D1 q' sh' H)) as dR_29; dex1 dR_29 as rq; destruct dR_29 as [Hrq K] | pose proof ((D1 q' sh' H)) as dR_29; dand3 dR_29 as rq Hrq K | destruct (D1 q' sh' H) as (rq & Hrq & K) ]). change (s_regions st0) with (s_regions st) in Hrq.
      destruct (N.eq_dec q' rid) as [->|NE]; [exists r'; split; [exact E_rid| reflexivity]|]. exists rq. split; [apply E_keep; assumption| exact K]. }
    unfold stE, wr8, upd_shadow in Hq. cbn [s_shadow set_shadow fst snd] in Hq.
    destruct (N.eq_dec q rid) as [->|NE]; [exists r'; split; [exact E_rid| reflexivity]|].
    rewrite lookup_insert_ne in Hq by congruence.
    unfold stH in Hq. destruct (Z.ltb_spec OLDL ND).
    + rewrite (s_shadow_havoc (rid, OLDL) (ND - OLDL) stM) in Hq by lia. cbn [fst] in Hq. rewrite lookup_insert_ne in Hq by congruence. exact (OLD q sh Hq).
    + exact (OLD q sh Hq).
  - rewrite E_tick. exact E_TKS.
  - intros b m i Hb Hi. apply E_hosts in Hb. rewrite E_cnt in Hi. change (MR st0 m) with (MR st m) in *.
    destruct (aptr_eqb_spec m g) as [->|NE].
    + pose proof (hosts_inj _ _ _ IM _ _ _ Hb Hg) as ->. cbn [fst]. unfold cnt_of in Hi. rewrite L0 in Hi.
      assert (CS : i = 0 \/ i = 1) by lia. destruct CS as [-> | ->].
      * rewrite E_sstart_g0. apply KE; [| | exact (D3 bm g 0 Hb ltac:(unfold cnt_of; change (MR st0 g) with (MR st g); lia))]; cbn [fst snd]; unfold sstart; rewrite rm_gbase; cbn; unfold UNIT, IB; [lia| intros E; inversion E; lia].
      * rewrite E_sstart_g. replace (UNIT + (ND - UNIT) * 1 - IB) with (ND - 4) by (unfold UNIT, IB; lia). exact E_known_end.
    + rewrite E_sstart_other by exact NE. apply KEo; [| exact (D3 b m i Hb Hi)]. cbn [fst].
      intros F. apply NE. destruct Hb as [aix Hbx]. pose proof (rm_only_group b _ Hbx F) as ->. exact (hosts_fun st bm m g (ex_intro _ aix Hbx) Hg).
  - intros b m o Hb Ho. apply E_hosts in Hb.
    destruct (N.eq_dec (fst b) rid) as [F|F].
    + destruct Hb as [aix Hbx]. pose proof (rm_only_group b _ Hbx F) as ->. apply UE; [cbn; lia| cbn; intros E; inversion E; lia| exact (D4 bm m o (ex_intro _ aix Hbx) Ho)].
    + apply UEo; [exact F| exact (D4 b m o Hb Ho)].
  - intros b m p i Hb Hml Hs. apply E_hosts in Hb. rewrite E_slots in Hs. change (s_slots st0) with (s_slots st) in Hs.
    assert (NE : m <> g) by (intros ->; rewrite E_maplen_g in Hml; pose proof ML'_eq; lia).
    rewrite E_maplen_other in Hml by exact NE. change (MR st0 m) with (MR st m) in Hml.
    assert (F : fst b <> rid).
    { intros F. apply NE. destruct Hb as [aix Hbx]. pose proof (rm_only_group b _ Hbx F) as ->. exact (hosts_fun st bm m g (ex_intro _ aix Hbx) Hg). }
    rewrite E_gbase. change (MR st0 p) with (MR st p).
    (first [ pose proof ((D5 b m p i Hb Hml Hs)) as dR_30; dand4 dR_30 as (v3 & K3 & E3 & R3) K2 K1 Q | destruct (D5 b m p i Hb Hml Hs) as ((v3 & K3 & E3 & R3) & K2 & K1 & Q) ]).
    split; [exists v3; split; [apply KEo; [exact F| exact K3]| auto]|]. split; [apply KEo; [exact F| exact K2]|]. split; [apply KEo; [exact F| exact K1]| exact Q].
  - intros k' m i Hk' Hs. rewrite E_slots in Hs. change (s_slots st0) with (s_slots st) in Hs.
    destruct (BL1_region k' m i Hk' Hs) as [F NE].
    rewrite (E_stride_other m NE), E_gbase. change (MR st0 m) with (MR st m).
    (first [ pose proof ((D6 k' m i Hk' Hs)) as dR_31; dand8 dR_31 as A1 A2 A3 A4 A5 A6 A7 A8 | destruct (D6 k' m i Hk' Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) ]).
    split; [apply KEo; [exact F| exact A1]|]. split; [apply KEo; [exact F| exact A2]|]. split; [apply KEo; [exact F| exact A3]|]. split; [apply KEo; [exact F| exact A4]|].
    split; [exact A5|]. split.
    + intros Hr5. (first [ pose proof ((A6 Hr5)) as dR_32; dand6 dR_32 as B1 B2 B3 B4 B5 B6 | destruct (A6 Hr5) as (B1 & B2 & B3 & B4 & B5 & B6) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try (apply KEo; [exact F|]); assumption.
    + split; [intros Hr0; apply KEo; [exact F| apply A7; exact Hr0]|]. intros a Ha. apply UEo; [exact F| apply A8; exact Ha].
Qed.

#[using="IS IG IM IA IR DISJ Hoff NBC NBA NB0 NDX NDA ND0 Hr SC63 Hg Hk INV k bm old off r"] Theorem remap_A : INVL X1 stE L' BL1 LS.
Proof.
  split; [exact A_inv_R|]. split; [exact A_inv_A|]. split; [exact A_inv_M|]. split; [exact A_inv_L|].
  split; [exact A_inv_G|]. split; [exact A_inv_S| exact A_inv_SH].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Variable b3 : Z.
Hypothesis B3 : Z.land b3 31 = 0.
Hypothesis B3R : 0 <= b3 < 256.
(* [comment removed for export] *)
Hypothesis OK4 : known st (rid, 16 + UNIT * off - 4) 0.
Hypothesis OK2 : known st (rid, 16 + UNIT * off - 2) (byte_of off 0).
Hypothesis OK1 : known st (rid, 16 + UNIT * off - 1) (byte_of off 1).

Definition stF : mstate := abf stE c off g n b3.

#[using="IG IM NB0 NDX NDA ND0 SC63 Hg INV LS BL L Clg"] Lemma E_Ec : c = (fst bm, sstart (MR stE g) 0).
Proof. rewrite E_sstart_g0. exact rm_c. Qed.
#[using="ND NB"] Lemma E_q : (snd (aadd c (UNIT * off)) - (snd bm + UNIT)) / UNIT = off.
Proof. cbn [aadd snd]. unfold UNIT. replace (16 + 16 * off - (0 + 16)) with (off * 16) by lia. apply Z.div_mul. lia. Qed.
#[using="FITn NB0 ND0 INV LS BL L Clg"] Lemma E_OLDC o v t : snd (aadd c (UNIT * off)) <= o < snd (aadd c (UNIT * off)) + n ->
  r_cells (get_shadow stE (fst c)) !! o = Some (v, t) -> (t < s_tick stE)%N.
Proof.
  unfold c. cbn [aadd fst snd]. intros Ho Hc. rewrite E_tick.
  unfold stE, wr8 in Hc. rewrite get_shadow_upd_shadow in Hc. cbn [fst snd] in Hc. rewrite N.eqb_refl in Hc. cbn [r_cells] in Hc.
  rewrite lookup_insert_ne in Hc by (unfold UNIT, IB in *; lia).
  assert (HC' : r_cells (get_shadow stM rid) !! o = Some (v, t)).
  { unfold stH in Hc. revert Hc. destruct (Z.ltb_spec OLDL ND); [rewrite havoc_cells by lia| ]; intros Hc; exact Hc. }
  change (get_shadow stM rid) with (get_shadow st rid) in HC'.
  (first [ pose proof ((get_shadow_cells_some st rid o (v, t) HC')) as dR_33; dex1 dR_33 as sh; destruct dR_33 as [Hs Hc'] | pose proof ((get_shadow_cells_some st rid o (v, t) HC')) as dR_33; dand3 dR_33 as sh Hs Hc' | destruct (get_shadow_cells_some st rid o (v, t) HC') as (sh & Hs & Hc') ]).
  (first [ pose proof ((TKS_of _ _ _ _ _ INV rid sh Hs)) as dR_34; dand3 dR_34 as C _ _ | destruct (TKS_of _ _ _ _ _ INV rid sh Hs) as (C & _ & _) ]). destruct (C o v t Hc') as [_ LE]. unfold st0. cbn. lia.
Qed.

#[using="OK1 OK2 OK4 B3R B3 IS IG IM IA IR DISJ Hn Hoff NDT FITn NBC NBA NB0 NDX NDA ND0 Hr SC63 Hg Hk INV k bm old r"] Theorem remap_B : INVL x0 stF L' (bl_resize c n BL) LS.
Proof.
  (first [ pose proof (rm_gfacts) as dR_35; dand4 dR_35 as L0 MLg NIL ML0 | pose proof rm_gfacts as (L0 & MLg & NIL & ML0) ]). pose proof ML'_eq as [MLE MLR].
  assert (I2 : INVL x0 stF L' (((c, off), n) :: BL1) LS).
  { unfold stF. change x0 with (mkX (x_idle X1) (x_zomb X1) None (x_orph X1) (x_fresh X1)).
    apply (ab_INVL X1 stE L' BL1 LS c off g bm 0 n b3 remap_A eq_refl).
    - rewrite E_slots. exact rm_slot.
    - apply E_hosts. exact Hg.
    - rewrite E_last, L0. lia.
    - exact E_Ec.
    - exact Hoff.
    - exact Hn.
    - rewrite E_stride_g. unfold UNIT, IB in *. lia.
    - rewrite E_stride_g. unfold UNIT, IB in *. lia.
    - exact B3.
    - exact B3R.
    - cbn [aadd fst snd]. unfold known, SHd. cbn [fst snd]. rewrite (E_read (rid, 16 + UNIT * off - 4)); [exact OK4| cbn; pose proof OLDL16; unfold UNIT; lia| cbn; intros E; inversion E; unfold UNIT, IB in *; lia].
    - rewrite E_q. cbn [aadd fst snd]. unfold known, SHd. cbn [fst snd]. rewrite (E_read (rid, 16 + UNIT * off - 2)); [exact OK2| cbn; pose proof OLDL16; unfold UNIT; lia| cbn; intros E; inversion E; unfold UNIT, IB in *; lia].
    - rewrite E_q. cbn [aadd fst snd]. unfold known, SHd. cbn [fst snd]. rewrite (E_read (rid, 16 + UNIT * off - 1)); [exact OK1| cbn; pose proof OLDL16; unfold UNIT; lia| cbn; intros E; inversion E; unfold UNIT, IB in *; lia].
    - rewrite E_q. lia.
    - exact E_OLDC. }
  eapply INVL_perm; [| exact I2]. unfold BL1. apply (bl_resize_perm BL c off old n (is_nodup _ _ _ IS) Hk).
Qed.

(* [comment removed for export] *)
Definition stC : mstate := upd_meta g (m_set_maplen ML') (set_regions (<[rid := r']> (s_regions st)) st).
Lemma stF_ctrl : ctrl_eq stC stF /\ s_tick stF = N.succ (s_tick st).
Proof.
  destruct (abf_ctrl stE c off g n b3) as [C T]. fold stF in C, T.
  split; [| rewrite T; exact E_tick].
  eapply ctrl_eq_trans; [| exact C].
  constructor; rewrite ?E_ctx, ?E_regions, ?E_metas, ?E_areas, ?E_groups, ?E_slots, ?E_secret, ?E_reserved, ?E_next_rid; reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition onin (p : optr) : Prop := match p with Some q => fst q <> rid | None => True end.

#[using="IG IA Hr Hg INV bm g r LS BL L Clg"] Lemma rm_area_nrid a : s_areas st !! a <> None -> fst a <> rid.
Proof.
  intros Ha E. destruct (s_areas st !! a) as [ar|] eqn:Ea; [| congruence].
  destruct (ia_areas _ IA _ _ Ea) as ((ra & Hra & MK & _) & _). rewrite E, Hr in Hra. inversion Hra. subst ra.
  pose proof rm_kind as K. unfold is_metakind in MK. destruct MK as [MK|MK]; rewrite MK in K; discriminate.
Qed.
#[using="IG Hr Hg INV bm g r LS BL L Clg"] Lemma rm_metakind_nrid q rq : s_regions st !! q = Some rq -> is_metakind rq -> q <> rid.
Proof.
  intros Hq MK ->. rewrite Hr in Hq. inversion Hq. subst rq. pose proof rm_kind as K.
  destruct MK as [MK|MK]; rewrite MK in K; discriminate.
Qed.
#[using="IG IA Hr Hg INV bm g r LS BL L Clg"] Lemma rm_present_nrid x : s_metas st !! x <> None -> fst x <> rid.
Proof.
  intros Hx. destruct (s_metas st !! x) as [mr|] eqn:E; [| congruence].
  (first [ pose proof ((ia_metas _ IA _ _ E)) as dR_36; dex3 dR_36 as a ar kk; dand3 dR_36 as Ha Hkk -> | pose proof ((ia_metas _ IA _ _ E)) as dR_36; dand6 dR_36 as a ar kk Ha Hkk -> | destruct (ia_metas _ IA _ _ E) as (a & ar & kk & Ha & Hkk & ->) ]). unfold mslot, aadd. cbn [fst].
  apply rm_area_nrid. rewrite Ha. discriminate.
Qed.
#[using="IG IA Hr Hg INV bm g r BL L st Clg"] Lemma rm_listed_nrid x h : In x (LS h) -> fst x <> rid.
Proof. intros H. apply rm_present_nrid. exact (listed_present _ _ _ _ _ INV x h H). Qed.
#[using="IS IG IM SC63 Hg INV bm ND NB LS BL L Clg"] Lemma rm_hosts_nrid b x : hosts st b x -> x <> g -> fst b <> rid.
Proof.
  intros Hb NE E. destruct Hb as [ai Hb']. pose proof (rm_only_group b _ Hb' E) as ->.
  apply NE. exact (hosts_fun st bm x g (ex_intro _ ai Hb') Hg).
Qed.
#[using="IM INV LS BL L Clg"] Lemma rm_mem_hosts x b : m_mem (MR st x) = Some b -> hosts st b x.
Proof. intros H. destruct (im_group _ _ _ IM x b H) as [Hh|Hz]; [exact Hh| destruct Hz]. Qed.
#[using="IM Hg INV LS BL L Clg"] Lemma rm_g_mem : m_mem (MR st g) = Some bm.
Proof.
  destruct Hg as [ai Hb]. (first [ pose proof ((im_hdr _ _ _ IM _ _ Hb)) as dR_37; dex1 dR_37 as m'; dand3 dR_37 as Eg Hmem _ | pose proof ((im_hdr _ _ _ IM _ _ Hb)) as dR_37; dand4 dR_37 as m' Eg Hmem _ | destruct (im_hdr _ _ _ IM _ _ Hb) as (m' & Eg & Hmem & _) ]). cbn in Eg. inversion Eg. subst m'. exact Hmem.
Qed.
#[using="IM Hg INV bm rid LS BL L Clg"] Lemma rm_g_present : s_metas st !! g <> None.
Proof. intros E. pose proof rm_g_mem as M. unfold MR, get_meta_rec in M. rewrite E in M. cbn in M. discriminate. Qed.
(* [comment removed for export] *)

#[using="IS IG IL IM IA IR Hr SC63 Hg INV bm ND NB r LS BL L Clg"] Lemma rm_ptrs :
  let cx := ctx st in
  onin (c_free_meta_head cx) /\ onin (c_avail_meta cx) /\ onin (c_meta_area_head cx) /\ onin (c_meta_area_tail cx)
  /\ onin (c_avail_meta_areas cx)
  /\ (forall sc, onin (active st sc))
  /\ match c_brk cx with BrkLive q _ => q <> rid | _ => True end
  /\ (forall x, onin (m_prev (MR st x)) /\ onin (m_next (MR st x)) /\ (x <> g -> onin (m_mem (MR st x))))
  /\ (forall a ar, s_areas st !! a = Some ar -> fst a <> rid /\ onin (a_next ar))
  /\ (forall b h, s_groups st !! b = Some h -> onin (g_meta h)).
Proof.
  cbv zeta.
  assert (HD : forall h, onin (get_head st h)).
  { intros h. destruct (get_head st h) as [a|] eqn:E; cbn; [| exact I]. exact (rm_listed_nrid _ _ (head_listed _ _ _ _ _ INV h a E)). }
  split; [exact (HD LFree)|].
  split. { destruct (c_avail_meta (ctx st)) as [q|] eqn:E; cbn; [| exact I]. (first [ pose proof ((ia_availptr _ IA q E)) as dR_38; dex1 dR_38 as rq; destruct dR_38 as [Hq MK] | pose proof ((ia_availptr _ IA q E)) as dR_38; dand3 dR_38 as rq Hq MK | destruct (ia_availptr _ IA q E) as (rq & Hq & MK) ]). exact (rm_metakind_nrid _ _ Hq MK). }
  split. { destruct (c_meta_area_head (ctx st)) as [q|] eqn:E; cbn; [| exact I]. exact (rm_area_nrid _ (ia_head _ IA q E)). }
  split. { destruct (c_meta_area_tail (ctx st)) as [q|] eqn:E; cbn; [| exact I]. exact (rm_area_nrid _ (ia_tail _ IA q E)). }
  split. { destruct (c_avail_meta_areas (ctx st)) as [[q off0]|] eqn:E; cbn; [| exact I].
           (first [ pose proof ((ir_cursor _ _ _ IR)) as dR_39; dand3 dR_39 as _ _ CU | destruct (ir_cursor _ _ _ IR) as (_ & _ & CU) ]). (first [ pose proof ((CU q off0 E)) as dR_40; dex1 dR_40 as rq; dand3 dR_40 as Hq MK _ | pose proof ((CU q off0 E)) as dR_40; dand4 dR_40 as rq Hq MK _ | destruct (CU q off0 E) as (rq & Hq & MK & _) ]). exact (rm_metakind_nrid _ _ Hq MK). }
  split; [intros sc; exact (HD (LActive sc))|].
  split. { pose proof (ir_brk _ _ _ IR) as BR. unfold ctx. destruct (c_brk (s_ctx st)) as [| |q off0]; try exact I.
           (first [ dand5 BR as _ rq Hq Kq _ | destruct BR as (_ & rq & Hq & Kq & _) ]). apply (rm_metakind_nrid _ _ Hq). left. exact Kq. }
  split.
  { intros x. pose proof (il_link _ _ IL x) as [[L1 L2] L3].
    split. { destruct (m_prev (MR st x)) as [p|] eqn:Ep; cbn; [| exact I].
             destruct (m_next (MR st x)) as [y|] eqn:Ex; [| discriminate (L3 eq_refl)].
             destruct (L2 ltac:(discriminate)) as [h Hh]. exact (rm_listed_nrid _ _ (prev_listed _ _ _ _ _ INV h x p Hh Ep)). }
    split. { destruct (m_next (MR st x)) as [y|] eqn:Ex; cbn; [| exact I].
             destruct (L2 ltac:(discriminate)) as [h Hh]. exact (rm_listed_nrid _ _ (next_listed _ _ _ _ _ INV h x y Hh Ex)). }
    intros NE. destruct (m_mem (MR st x)) as [b|] eqn:Eb; cbn; [| exact I]. exact (rm_hosts_nrid _ _ (rm_mem_hosts _ _ Eb) NE). }
  split.
  { intros a ar Ha. split; [apply rm_area_nrid; congruence|]. destruct (a_next ar) as [a'|] eqn:E; cbn; [| exact I].
    (first [ pose proof ((ia_areas _ IA _ _ Ha)) as dR_42; dand4 dR_42 as _ _ _ NXT | destruct (ia_areas _ IA _ _ Ha) as (_ & _ & _ & NXT) ]). exact (rm_area_nrid _ (NXT a' E)). }
  intros b gh Hb. (first [ pose proof ((im_hdr _ _ _ IM _ _ Hb)) as dR_43; dex1 dR_43 as m'; dand3 dR_43 as Eg Hmem _ | pose proof ((im_hdr _ _ _ IM _ _ Hb)) as dR_43; dand4 dR_43 as m' Eg Hmem _ | destruct (im_hdr _ _ _ IM _ _ Hb) as (m' & Eg & Hmem & _) ]). rewrite Eg. cbn.
  apply rm_present_nrid. intros E. unfold MR, get_meta_rec in Hmem. rewrite E in Hmem. cbn in Hmem. discriminate.
Qed.

(* [comment removed for export] *)
Lemma C_conc q : conc stE q = if (fst q =? rid)%N then NB + snd q else conc st q.
Proof.
  unfold conc, get_region. rewrite E_lookup. destruct (N.eqb_spec (fst q) rid) as [E|NE]; [reflexivity|]. reflexivity.
Qed.
Lemma C_conc_other q : fst q <> rid -> conc stE q = conc st q.
Proof. intros NE. rewrite C_conc. destruct (N.eqb_spec (fst q) rid); [congruence| reflexivity]. Qed.
Lemma C_conc_rid o : conc stE (rid, o) = NB + o.
Proof. rewrite C_conc. cbn [fst snd]. rewrite N.eqb_refl. reflexivity. Qed.
Lemma C_pw p : onin p -> pw stE p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite C_conc_other by exact H. reflexivity. Qed.
Lemma C_rec x : get_meta_rec stE x = MR stE x. Proof. reflexivity. Qed.

Section THM_C.
Variables (m mE : word -> option byte).
Hypothesis MRP : mrep st m.
Hypothesis TKst : ticks_ok st.
Hypothesis NBRF : ranges_free p0_reserved NB ND = true.
Let Bo : Z := r_base r.
Let Gc : Z := conc st g.
Hypothesis COPY : forall o, 0 <= o < OLDL -> o < ND -> o <> ND - 4 -> mE (wa (NB + o)) = m (wa (Bo + o)).
Hypothesis GM : rw_cells rsegs mE (Gc + 16) [C8 (wz NB)].
Hypothesis GW : rw_cells rsegs mE (Gc + 32) [C8 (wz (meta_word (m_set_maplen ML' (MR st g))))].
Hypothesis ENDB : bytes_at rsegs mE (NB + ND - 4) [b8 0].
Hypothesis MAPPED : wr_at rsegs mE NB ND.
Hypothesis OUT : forall a, 0 <= a < alloc_ceiling -> ~ (NB <= a < NB + ND) -> ~ (Bo <= a < Bo + OLDL) ->
  ~ (Gc + 16 <= a < Gc + 24) -> ~ (Gc + 32 <= a < Gc + 40) -> mE (wa a) = m (wa a).


(* [comment removed for export] *)
#[using="Gc Bo NB0 ND0 ND NB g r st"] Lemma rw_cells_app' (mm : word -> option byte) A cs1 cs2 :
  rw_cells rsegs mm A (cs1 ++ cs2) <-> rw_cells rsegs mm A cs1 /\ rw_cells rsegs mm (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    (first [ dand3 WR as HA HN HW | destruct WR as (HA & HN & HW) ]).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed.

#[using="Gc Bo NB0 ND0 ND NB g r st"] Lemma rw_cells_shift (mm mm' : word -> option byte) A A' cs :
  rw_cells rsegs mm A cs ->
  0 <= A' -> (A + Z.of_nat (cells_size cs) <= 0x10000 \/ 0x63000 <= A) -> (A' + Z.of_nat (cells_size cs) <= 0x10000 \/ 0x63000 <= A') ->
  A' + Z.of_nat (cells_size cs) <= alloc_ceiling ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> mm' (wa (A' + i)) = mm (wa (A + i))) ->
  rw_cells rsegs mm' A' cs.
Proof.
  intros [[Hwf (H0 & H1 & HB)] (W0 & W1 & HW)] A0 XA XA' AC AG.
  pose proof (cells_bytes_length cs Hwf) as LEN. rewrite LEN in H1, HB. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  assert (SM : forall i, 0 <= i < Z.of_nat (cells_size cs) -> exists v, mm (wa (A + i)) = Some v).
  { intros i Hi. specialize (HW i Hi). rewrite p0_wview_overlay in HW by (unfold wa; rewrite unsigned_lit; lia).
    destruct (mm (wa (A + i))); [eauto| congruence]. }
  split; [split; [exact Hwf|]|].
  - split; [lia|]. rewrite LEN. split; [lia|]. intros i Hi. specialize (HB i Hi).
    destruct (SM (Z.of_nat i) ltac:(lia)) as [v Hv].
    unfold mrd in HB |- *. rewrite Hv in HB. rewrite AG, Hv by lia. exact HB.
  - split; [lia|]. split; [lia|]. intros i Hi. destruct (SM i Hi) as [v Hv].
    rewrite p0_wview_overlay by (unfold wa; rewrite unsigned_lit; lia). rewrite AG, Hv by lia. discriminate.
Qed.

#[using="Gc Bo NB0 ND0 ND NB g r st"] Lemma bytes_at1_shift (mm mm' : word -> option byte) a a' v :
  bytes_at rsegs mm a [v] -> 0 <= a' -> a' + 1 <= alloc_ceiling ->
  (a + 1 <= 0x10000 \/ 0x63000 <= a) -> (a' + 1 <= 0x10000 \/ 0x63000 <= a') ->
  mm (wa a) <> None -> mm' (wa a') = mm (wa a) -> bytes_at rsegs mm' a' [v].
Proof.
  ((first [ intro dR_70; dand3 dR_70 as H0 H1 HB | intros (H0 & H1 & HB) ]); intros A0 AC XA XA' NN AG). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. assert (i = 0%nat) by lia. subst i.
  specialize (HB 0%nat ltac:(cbn; lia)). cbn [Z.of_nat nth_error] in HB |- *. rewrite Z.add_0_r in HB |- *.
  unfold mrd in HB |- *. rewrite AG. destruct (mm (wa a)); [exact HB| congruence].
Qed.

#[using="Gc Bo ND NB g r st"] Lemma live_range_lr rq : let '(b2, l2) := region_live_range rq in b2 = lr_lo rq /\ b2 + l2 = r_base rq + round_up_pg (r_len rq).
Proof. unfold region_live_range, lr_lo. destruct (r_kind rq); cbn zeta iota beta; unfold PGSZ; split; lia. Qed.

Lemma TKS_ticks_ok' stx : TKS stx (s_tick stx) -> ticks_ok stx.
Proof.
  intros T. split.
  - intros q sh u hl ch Hq Hu Hch. (first [ pose proof ((T q sh Hq)) as dR_45; dand3 dR_45 as _ B _ | destruct (T q sh Hq) as (_ & B & _) ]). exact (B u hl ch Hu Hch).
  - intros q sh pg t Hq Hp. (first [ pose proof ((T q sh Hq)) as dR_46; dand3 dR_46 as _ _ C | destruct (T q sh Hq) as (_ & _ & C) ]). exact (C pg t Hp).
Qed.

Let WF := proj1 MRP.

#[using="OUT MAPPED ENDB GW GM COPY Gc Bo NBRF MRP m IS IG IL IM IA IR DISJ NBC NBA NB0 NDX NDA ND0 Hr SC63 Hg INV bm r LS BL L"] Theorem remap_C : mrep stE mE /\ ticks_ok stE.
Proof.
  pose proof MRP as (WF0 & CX & GL & AR & GR & SH). (first [ pose proof (WF0) as dR_47; dand5 dR_47 as Hres WR DJ WA WG | pose proof WF0 as (Hres & WR & DJ & WA & WG) ]).
  pose proof rm_kind as Kr. pose proof rm_top as [OT _]. pose proof OLDL16 as [O16 O4096]. pose proof ML'_eq as [MLE MLR].
  (first [ pose proof (rm_gfacts) as dR_48; dand4 dR_48 as L0 MLg NIL ML0 | pose proof rm_gfacts as (L0 & MLg & NIL & ML0) ]).
  (first [ pose proof ((WR rid r Hr)) as dR_49; dand5 dR_49 as B0 BAL _ BC BRF | destruct (WR rid r Hr) as (B0 & BAL & _ & BC & BRF) ]). rewrite <- OT in BC, BRF.
  pose proof (reserved_disjoint1 _ _ BRF ltac:(lia)) as BR1. pose proof (reserved_disjoint1 _ _ NBRF ltac:(lia)) as NR1.
  assert (ACL : alloc_ceiling < 2^63) by ((let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia).
  assert (LRr : lr_lo r = Bo) by (apply lr_lo_group; exact Kr).
  (first [ pose proof (rm_ptrs) as dR_50; dand10 dR_50 as P1 P2 P3 P4 P5 PA PB PM PAR PG | pose proof rm_ptrs as (P1 & P2 & P3 & P4 & P5 & PA & PB & PM & PAR & PG) ]).
  (* [comment removed for export] *)
  destruct (s_metas st !! g) as [gr|] eqn:Eg; [| exfalso; exact (rm_g_present Eg)].
  (first [ pose proof ((ia_metas _ IA _ _ Eg)) as dR_51; dex3 dR_51 as a ar kk; dand3 dR_51 as Ha Hkk Egk | pose proof ((ia_metas _ IA _ _ Eg)) as dR_51; dand6 dR_51 as a ar kk Ha Hkk Egk | destruct (ia_metas _ IA _ _ Eg) as (a & ar & kk & Ha & Hkk & Egk) ]).
  (first [ pose proof ((area_conc st a ar WF0 Ha)) as dR_52; dex1 dR_52 as ra; dand9 dR_52 as Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | pose proof ((area_conc st a ar WF0 Ha)) as dR_52; dand10 dR_52 as ra Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | destruct (area_conc st a ar WF0 Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC) ]).
  pose proof (area_lr_lo st a ar ra WF0 Ha Hra) as LRa.
  assert (HG : Gc = conc st a + (AREA_HDR + META_SIZE * kk)).
  { unfold Gc. rewrite Egk. unfold mslot. rewrite conc_aadd by (rewrite Hra; eauto). reflexivity. }
  unfold AREA_HDR, META_SIZE, NSLOTS in HG, Hkk.
  assert (NEa : fst a <> rid) by (apply rm_area_nrid; rewrite Ha; discriminate).
  (* [comment removed for export] *)
  assert (DISJ' : forall q rq, q <> rid -> s_regions st !! q = Some rq -> NB + ND <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= NB).
  { intros q rq NE Hq. pose proof (DISJ q rq NE Hq) as D. pose proof (live_range_lr rq) as LR.
    destruct (region_live_range rq) as [b2 l2]. destruct LR as [E1 E2]. lia. }
  assert (OLDJ : forall q rq, q <> rid -> s_regions st !! q = Some rq -> Bo + OLDL <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= Bo).
  { intros q rq NE Hq. rewrite <- LRr. unfold Bo. rewrite OT. destruct (DJ q rq rid r Hq Hr NE); lia. }
  (* [comment removed for export] *)
  set (stable := fun lo hi => hi <= alloc_ceiling /\ (hi <= NB \/ NB + ND <= lo) /\ (hi <= Bo \/ Bo + OLDL <= lo)
                               /\ (hi <= Gc + 16 \/ Gc + 24 <= lo) /\ (hi <= Gc + 32 \/ Gc + 40 <= lo)).
  assert (AGs : forall lo hi, stable lo hi -> 0 <= lo -> agree_on m mE lo (hi - lo)).
  { (intros lo hi; (first [ intro dR_71; dand5 dR_71 as S1 S2 S3 S4 S5 | intros (S1 & S2 & S3 & S4 & S5) ]); intros LO0 x Hx). apply OUT; lia. }
  assert (TC : forall A cs, rw_cells rsegs m A cs -> stable A (A + Z.of_nat (cells_size cs)) -> rw_cells rsegs mE A cs).
  { intros A cs H HS. pose proof (rw_cells_bound rsegs m A cs H). eapply rw_cells_agree'; [exact H|].
    replace (Z.of_nat (cells_size cs)) with (A + Z.of_nat (cells_size cs) - A) by lia. apply AGs; [exact HS| lia]. }
  (* [comment removed for export] *)
  assert (IMG : forall lo hi, 0x10000 <= lo -> hi <= 0x63000 -> lo <= hi -> stable lo hi).
  { intros lo hi H1 H2 H3. unfold stable. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    (first [ pose proof ((WR _ _ Hra)) as dR_53; dand5 dR_53 as _ _ _ _ RFa | destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa) ]). pose proof (round_up_pg_ge (r_len ra)).
    pose proof (reserved_disjoint1 _ _ RFa ltac:(lia)) as A4. pose proof (lr_lo_ge ra). rewrite HG, Ca. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
  (* [comment removed for export] *)
  assert (REG : forall q rq lo hi, q <> rid -> s_regions st !! q = Some rq -> lr_lo rq <= lo -> hi <= r_base rq + round_up_pg (r_len rq) ->
            (hi <= Gc + 16 \/ Gc + 24 <= lo) -> (hi <= Gc + 32 \/ Gc + 40 <= lo) -> stable lo hi).
  { intros q rq lo hi NE Hq H1 H2 H3 H4. (first [ pose proof ((WR _ _ Hq)) as dR_54; dand5 dR_54 as _ _ _ QC _ | destruct (WR _ _ Hq) as (_ & _ & _ & QC & _) ]).
    pose proof (DISJ' q rq NE Hq). pose proof (OLDJ q rq NE Hq). unfold stable. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
  (* [comment removed for export] *)
  assert (GREG : forall q rq lo hi, q <> rid -> s_regions st !! q = Some rq -> r_kind rq = RKGroup -> r_base rq <= lo -> hi <= r_base rq + round_up_pg (r_len rq) ->
            stable lo hi).
  { intros q rq lo hi NE Hq Kq H1 H2. pose proof (lr_lo_group rq Kq) as LQ.
    assert (NEq : q <> fst a) by (intros ->; rewrite Hra in Hq; inversion Hq; subst; congruence).
    destruct (DJ q rq (fst a) ra Hq Hra NEq) as [D|D]; (eapply REG; [exact NE| exact Hq| lia| lia| rewrite HG, Ca; lia| rewrite HG, Ca; lia]). }
  split.
  2:{ (* [comment removed for export] *) apply TKS_ticks_ok'. rewrite E_tick. pose proof E_TKS as T. unfold st0 in T. cbn [s_tick set_tick] in T. exact T. }
  split; [|split; [|split; [|split; [|split]]]].
  - (* [comment removed for export] *)
    split; [rewrite E_reserved; exact Hres|]. split; [|split; [|split]].
    + intros q rq Hq. destruct (E_some q rq Hq) as [[-> ->]|[NE Hq']]; [| exact (WR q rq Hq')].
      cbn [r_base r_len r']. rewrite (round_up_pg_id ND NDA). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia. exact NBRF.
    + intros q1 r1 q2 r2 H1 H2 NE.
      destruct (E_some q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (E_some q2 r2 H2) as [[-> ->]|[NE2 H2']]; [congruence| | | exact (DJ q1 r1 q2 r2 H1' H2' NE)].
      * cbn [r_base r_len r']. rewrite (round_up_pg_id ND NDA). unfold lr_lo at 2. cbn [r_kind r' r_base]. destruct (DISJ' q2 r2 NE2 H2'); lia.
      * cbn [r_base r_len r']. rewrite (round_up_pg_id ND NDA). unfold lr_lo at 1. cbn [r_kind r' r_base]. destruct (DISJ' q1 r1 NE1 H1'); lia.
    + intros a' ar' Ha'. rewrite E_areas in Ha'. (first [ pose proof ((WA a' ar' Ha')) as dR_55; dex1 dR_55 as rq; destruct dR_55 as [Hq REST] | pose proof ((WA a' ar' Ha')) as dR_55; dand3 dR_55 as rq Hq REST | destruct (WA a' ar' Ha') as (rq & Hq & REST) ]). exists rq. split; [| exact REST].
      apply E_keep; [apply rm_area_nrid; rewrite Ha'; discriminate| exact Hq].
    + intros b gh Hb. rewrite E_groups in Hb. destruct (N.eq_dec (fst b) rid) as [E|NE].
      * pose proof (rm_only_group b gh Hb E) as ->. exists r'. split; [exact E_rid|]. cbn. rewrite (round_up_pg_id ND NDA). split; [reflexivity|]. split; [lia|]. split; [lia| reflexivity].
      * (first [ pose proof ((WG b gh Hb)) as dR_56; dex1 dR_56 as rq; destruct dR_56 as [Hq REST] | pose proof ((WG b gh Hb)) as dR_56; dand3 dR_56 as rq Hq REST | destruct (WG b gh Hb) as (rq & Hq & REST) ]). exists rq. split; [apply E_keep; [exact NE| exact Hq]| exact REST].
  - (* [comment removed for export] *)
    assert (HC : ctx_head_cells stE = ctx_head_cells st).
    { unfold ctx_head_cells, ctx. rewrite E_ctx. fold (ctx st). rewrite !C_pw by assumption. reflexivity. }
    assert (HA' : actives stE = actives st).
    { unfold actives. apply map_ext. intros i. unfold active, ctx. rewrite E_ctx. apply C_pw. apply PA. }
    assert (HU : usages stE = usages st) by (unfold usages, usage, ctx; rewrite E_ctx; reflexivity).
    assert (HUS : unmap_seqs stE = unmap_seqs st) by (unfold unmap_seqs, unmap_seq, ctx; rewrite E_ctx; reflexivity).
    assert (HBO : bouncess stE = bouncess st) by (unfold bouncess, bounces, ctx; rewrite E_ctx; reflexivity).
    assert (HT : ctx_tail_cells stE = ctx_tail_cells st).
    { unfold ctx_tail_cells, brk_word, ctx. rewrite E_ctx. fold (ctx st). destruct (c_brk (ctx st)) as [| |q off0] eqn:EB; try reflexivity.
      try rewrite EB in PB. cbn iota beta in PB. rewrite (C_conc_other (q, off0)) by exact PB. reflexivity. }
    unfold mrep_ctx. rewrite HC, HA', HU, HUS, HBO, HT.
    (first [ dand6 CX as C1 C2 C3 C4 C5 C6 | destruct CX as (C1 & C2 & C3 & C4 & C5 & C6) ]).
    pose proof (u64arr_bound rsegs m _ _ C2) as B2. pose proof (u64arr_bound rsegs m _ _ C3) as B3'.
    pose proof (u8arr_bound rsegs m _ _ C4) as B4. pose proof (u8arr_bound rsegs m _ _ C5) as B5.
    rewrite actives_length in B2. rewrite usages_length in B3'. rewrite unmap_seqs_length in B4. rewrite bouncess_length in B5.
    unfold CTX in *.
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1|]. cbn [cells_size csize ctx_head_cells Nat.add length]. apply IMG; lia.
    + eapply u64arr_agree'; [exact C2|]. rewrite actives_length. replace (8 * Z.of_nat 48) with ((402528 + 80 + 384) - (402528 + 80)) by lia. apply AGs; [apply IMG; lia| lia].
    + eapply u64arr_agree'; [exact C3|]. rewrite usages_length. replace (8 * Z.of_nat 48) with ((402528 + 464 + 384) - (402528 + 464)) by lia. apply AGs; [apply IMG; lia| lia].
    + eapply u8arr_agree'; [exact C4|]. rewrite unmap_seqs_length. replace (Z.of_nat 32) with ((402528 + 848 + 32) - (402528 + 848)) by lia. apply AGs; [apply IMG; lia| lia].
    + eapply u8arr_agree'; [exact C5|]. rewrite bouncess_length. replace (Z.of_nat 32) with ((402528 + 880 + 32) - (402528 + 880)) by lia. apply AGs; [apply IMG; lia| lia].
    + apply TC; [exact C6|]. cbn [cells_size csize ctx_tail_cells Nat.add length]. apply IMG; lia.
  - (* [comment removed for export] *)
    (first [ dand5 GL as G1 G2 G3 G4 G5 | destruct GL as (G1 & G2 & G3 & G4 & G5) ]). unfold mrep_globals, MLOCK, NEED_LOCKS, PAGE_SIZE_A, GOT_SSP, SSP_GUARD in *.
    split; [|split; [|split; [|split]]]; (apply TC; [assumption | cbn; apply IMG; lia]).
  - (* [comment removed for export] *)
    intros a' ar' Ha'. rewrite E_areas in Ha'.
    (first [ pose proof ((area_conc st a' ar' WF0 Ha')) as dR_59; dex1 dR_59 as ra'; dand9 dR_59 as Hra' Ca' Sa0' Sa1' SaL' NK' _ _ RBC' | pose proof ((area_conc st a' ar' WF0 Ha')) as dR_59; dand10 dR_59 as ra' Hra' Ca' Sa0' Sa1' SaL' NK' _ _ RBC' | destruct (area_conc st a' ar' WF0 Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _ & _ & RBC') ]).
    pose proof (area_lr_lo st a' ar' ra' WF0 Ha' Hra') as LRa'.
    assert (NEa' : fst a' <> rid) by (apply rm_area_nrid; rewrite Ha'; discriminate).
    destruct (PAR a' ar' Ha') as [_ Pn].
    (first [ pose proof ((AR a' ar' Ha')) as dR_60; dand3 dR_60 as HD SL PD | destruct (AR a' ar' Ha') as (HD & SL & PD) ]). unfold area_rep.
    rewrite (C_conc_other a') by exact NEa'. rewrite C_pw by exact Pn.
    destruct (decide (a' = a)) as [->|NEaa].
    + rewrite Ha in Ha'. inversion Ha'; subst ar'. rewrite Hra in Hra'. inversion Hra'; subst ra'.
      split; [|split].
      * apply TC; [exact HD|]. cbn [cells_size csize Nat.add length]. eapply REG; [exact NEa| exact Hra| lia| lia| lia| lia].
      * intros k' Hk'. rewrite C_rec, E_MR.
        destruct (Z.eq_dec k' kk) as [->|NEk].
        -- replace (aadd a (AREA_HDR + META_SIZE * kk)) with g by (rewrite Egk; reflexivity). rewrite aptr_eqb_refl.
           unfold AREA_HDR, META_SIZE. replace (conc st a + 24 + 40 * kk) with Gc by (rewrite HG; lia).
           specialize (SL kk Hkk). unfold AREA_HDR, META_SIZE in SL. replace (conc st a + 24 + 40 * kk) with Gc in SL by (rewrite HG; lia).
           replace (get_meta_rec st (aadd a (24 + 40 * kk))) with (MR st g) in SL by (rewrite Egk; reflexivity).
           unfold meta_cells in SL |- *. cbn [m_prev m_next m_mem m_avail m_freed m_set_maplen].
           (first [ pose proof ((PM g)) as dR_61; dand3 dR_61 as Pp Px _ | destruct (PM g) as (Pp & Px & _) ]). rewrite !C_pw by assumption.
           rewrite rm_g_mem. unfold pw at 3. cbn [oconc]. unfold bm. rewrite C_conc_rid, Z.add_0_r.
           apply (proj1 (rw_cells_app' m Gc [C8 (pw st (m_prev (MR st g))); C8 (pw st (m_next (MR st g)))] _)) in SL as [SL1 SL2].
           apply (proj1 (rw_cells_app' m _ [C8 (pw st (m_mem (MR st g)))] _)) in SL2 as [_ SL3].
           apply (proj1 (rw_cells_app' m _ [C4 (wz (m_avail (MR st g))); C4 (wz (m_freed (MR st g)))] _)) in SL3 as [SL4 _].
           cbn [cells_size csize Nat.add] in SL4.
           apply (proj2 (rw_cells_app' mE Gc [C8 (pw st (m_prev (MR st g))); C8 (pw st (m_next (MR st g)))] _)). split.
           { apply TC; [exact SL1|]. cbn [cells_size csize Nat.add]. eapply REG; [exact NEa| exact Hra| lia| lia| lia| lia]. }
           apply (proj2 (rw_cells_app' mE _ [C8 (wz NB)] _)). cbn [cells_size csize Nat.add]. split; [exact GM|].
           apply (proj2 (rw_cells_app' mE _ [C4 (wz (m_avail (MR st g))); C4 (wz (m_freed (MR st g)))] _)). cbn [cells_size csize Nat.add]. split.
           { replace (Gc + 16 + 8) with (Gc + 24) by lia. apply TC; [replace (Gc + 24) with (Gc + Z.of_nat 16 + Z.of_nat 8) by lia; exact SL4|].
             cbn [cells_size csize Nat.add]. eapply REG; [exact NEa| exact Hra| lia| lia| lia| lia]. }
           replace (Gc + 16 + 8 + 8) with (Gc + 32) by lia. exact GW.
        -- replace (aptr_eqb (aadd a (AREA_HDR + META_SIZE * k')) g) with false.
           2:{ symmetry. rewrite Egk. unfold aptr_eqb, aadd, mslot. cbn. rewrite N.eqb_refl. cbn. apply Z.eqb_neq. unfold AREA_HDR, META_SIZE. lia. }
           assert (NEx : aadd a (AREA_HDR + META_SIZE * k') <> g).
           { rewrite Egk. unfold mslot, aadd. intros E. inversion E. unfold AREA_HDR, META_SIZE in *. lia. }
           (first [ pose proof ((PM (aadd a (AREA_HDR + META_SIZE * k')))) as dR_62; dand3 dR_62 as Pp Px Pmm | destruct (PM (aadd a (AREA_HDR + META_SIZE * k'))) as (Pp & Px & Pmm) ]). specialize (Pmm NEx).
           unfold meta_cells. fold (MR st (aadd a (AREA_HDR + META_SIZE * k'))). rewrite !C_pw by assumption.
           apply TC; [apply SL; exact Hk'|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE, NSLOTS in *.
           eapply REG; [exact NEa| exact Hra| first [lia | nia]| first [lia | nia]| first [lia | nia]| first [lia | nia]].   (* [comment removed for export] *)
      * apply TC; [exact PD|]. cbn [cells_size csize Nat.add length]. eapply REG; [exact NEa| exact Hra| lia| lia| lia| lia].
    + assert (PGD : fst a' <> fst a \/ (fst a' = fst a /\ (snd a' + 4096 <= snd a \/ snd a + 4096 <= snd a'))).
      { destruct (N.eq_dec (fst a') (fst a)) as [E|NE]; [right|left; exact NE]. split; [exact E|].
        assert (snd a' <> snd a) by (intros E2; apply NEaa; destruct a, a'; cbn in *; congruence).
        Z.div_mod_to_equations. nia. }
      assert (DD : conc st a' + 4096 <= Gc \/ Gc + 40 <= conc st a').
      { rewrite Ca', HG, Ca. destruct PGD as [NE|[E PG']].
        - destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NE); lia.
        - rewrite E, Hra in Hra'. inversion Hra'; subst ra'. lia. }
      assert (MX : forall k0, 0 <= k0 < NSLOTS -> aadd a' (AREA_HDR + META_SIZE * k0) <> g).
      { intros k0 Hk0. rewrite Egk. unfold mslot, aadd, AREA_HDR, META_SIZE, NSLOTS in *. intros E. inversion E. destruct PGD as [NE|[_ PG']]; [exact (NE H0)| lia]. }
      split; [|split].
      * apply TC; [exact HD|]. cbn [cells_size csize Nat.add length]. eapply REG; [exact NEa'| exact Hra'| lia| lia| lia| lia].
      * intros k0 Hk0. rewrite C_rec, (E_MR_other _ (MX k0 Hk0)).
        (first [ pose proof ((PM (aadd a' (AREA_HDR + META_SIZE * k0)))) as dR_63; dand3 dR_63 as Pp Px Pmm | destruct (PM (aadd a' (AREA_HDR + META_SIZE * k0))) as (Pp & Px & Pmm) ]). specialize (Pmm (MX k0 Hk0)).
        unfold meta_cells. fold (MR st (aadd a' (AREA_HDR + META_SIZE * k0))). rewrite !C_pw by assumption.
        apply TC; [apply SL; exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE, NSLOTS in *.
        eapply REG; [exact NEa'| exact Hra'| try (generalize alloc_ceiling_val); clear - LRa' Ca' Hk0; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - Ca' Sa1' Hk0; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - DD Hk0; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - DD Hk0; try pose proof alloc_ceiling_val; lia].
      * apply TC; [exact PD|]. cbn [cells_size csize Nat.add length]. eapply REG; [exact NEa'| exact Hra'| lia| lia| lia| lia].
  - (* [comment removed for export] *)
    intros b gh Hb. rewrite E_groups in Hb. pose proof (PG b gh Hb) as Pgm.
    (first [ pose proof ((GR b gh Hb)) as dR_64; dex1 dR_64 as w8; destruct dR_64 as [R Hw8] | pose proof ((GR b gh Hb)) as dR_64; dand3 dR_64 as w8 R Hw8 | destruct (GR b gh Hb) as (w8 & R & Hw8) ]). exists w8. split; [| exact Hw8]. rewrite C_pw by exact Pgm.
    destruct (N.eq_dec (fst b) rid) as [E|NE].
    + pose proof (rm_only_group b gh Hb E) as ->. unfold bm. rewrite C_conc_rid, Z.add_0_r.
      unfold bm in R. rewrite (conc_region st rid 0 r Hr), Z.add_0_r in R. fold Bo in R.
      eapply (rw_cells_shift m mE Bo NB); [exact R| lia| cbn; lia| cbn; lia| cbn; lia|].
      cbn [cells_size csize Nat.add]. intros i Hi. apply COPY; lia.
    + (first [ pose proof ((group_conc st b gh WF0 Hb)) as dR_65; dex1 dR_65 as rb; dand6 dR_65 as Hrb Cb Kb Sb0 Sb1 _ | pose proof ((group_conc st b gh WF0 Hb)) as dR_65; dand7 dR_65 as rb Hrb Cb Kb Sb0 Sb1 _ | destruct (group_conc st b gh WF0 Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _) ]).
      rewrite (C_conc_other b) by exact NE. apply TC; [exact R|]. cbn [cells_size csize Nat.add]. rewrite Cb. eapply GREG; [exact NE| exact Hrb| exact Kb| lia| lia].
  - (* [comment removed for export] *)
    intros q rq Hq Kq. destruct (E_some q rq Hq) as [[-> ->]|[NE Hq']].
    + (* [comment removed for export] *)
      cbn [r_base r_len r' Malloc.r_base Malloc.r_len]. split; [rewrite (round_up_pg_id ND NDA); exact MAPPED|].
      rewrite (round_up_pg_id ND NDA). intros o v Ho Hc. change (Malloc.r_base r') with NB.
      destruct (Z.eq_dec o (ND - 4)) as [->|NEo].
      { pose proof E_known_end as KE. unfold known, SHd in KE. cbn [fst snd] in KE. rewrite KE in Hc. inversion Hc. subst v. split; [replace (NB + (ND - 4)) with (NB + ND - 4) by lia; exact ENDB| lia]. }
      destruct (Z.lt_ge_cases o OLDL) as [LO|HI].
      * rewrite (E_read (rid, o)) in Hc by (cbn; first [intros [_ ?]; lia | congruence]). cbn [fst snd] in Hc.
        destruct (SH rid r Hr Kr) as [HWr HBr]. rewrite <- OT in HBr, HWr. destruct (HBr o v ltac:(lia) Hc) as [Bt Hv]. split; [| exact Hv].
        fold Bo in Bt. (first [ dand3 HWr as _ _ HWr | destruct HWr as (_ & _ & HWr) ]). specialize (HWr o ltac:(lia)). fold Bo in HWr.
        rewrite p0_wview_overlay in HWr by (unfold wa; rewrite unsigned_lit; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia).
        eapply (bytes_at1_shift m mE (Bo + o) (NB + o)); [exact Bt| lia| lia| lia| lia| exact HWr| apply COPY; lia].
      * exfalso. (* [comment removed for export] *)
        assert (LT : OLDL < ND) by lia.
        unfold stE in Hc. rewrite (cell_read_wr8_other (rid, ND - 4) 0 stH (rid, o)) in Hc by (cbn; intros E; inversion E; lia). cbn [fst snd] in Hc.
        unfold stH in Hc. rewrite (proj2 (Z.ltb_lt _ _) LT) in Hc.
        destruct (cell_read_havoc_in (rid, OLDL) (ND - OLDL) stM O16 ltac:(lia) M_hav (rid, o) eq_refl ltac:(cbn; lia)) as [h Hh].
        { cbn [fst snd]. intros v0 tk Hcell. change (get_shadow stM rid) with (get_shadow st rid) in Hcell.
          (first [ pose proof ((get_shadow_cells_some st rid o (v0, tk) Hcell)) as dR_67; dex1 dR_67 as sh; destruct dR_67 as [Hs Hc'] | pose proof ((get_shadow_cells_some st rid o (v0, tk) Hcell)) as dR_67; dand3 dR_67 as sh Hs Hc' | destruct (get_shadow_cells_some st rid o (v0, tk) Hcell) as (sh & Hs & Hc') ]).
          (first [ pose proof ((TKS_of _ _ _ _ _ INV rid sh Hs)) as dR_68; dand3 dR_68 as C _ _ | destruct (TKS_of _ _ _ _ _ INV rid sh Hs) as (C & _ & _) ]). destruct (C o v0 tk Hc') as [_ LE]. rewrite M_tick. unfold st0. cbn. lia. }
        cbn [fst snd] in Hh. rewrite Hh in Hc. discriminate.
    + (* [comment removed for export] *)
      destruct (SH q rq Hq' Kq) as [HWq HBq]. split.
      * eapply wr_at_agree; [exact HWq|]. replace (round_up_pg (r_len rq)) with (r_base rq + round_up_pg (r_len rq) - r_base rq) by lia.
        destruct (WR _ _ Hq') as (Q0 & _). apply AGs; [eapply GREG; eauto; lia| lia].
      * intros o v Ho Hc. rewrite (E_read (q, o)) in Hc by (cbn; first [intros [? _]; congruence | congruence]). cbn [fst snd] in Hc.
        destruct (HBq o v Ho Hc) as [Bt Hv]. split; [| exact Hv].
        eapply bytes_at_agree; [exact Bt|]. destruct (WR _ _ Hq') as (Q0 & _).
        replace (Z.of_nat (length [b8 v])) with (r_base rq + o + 1 - (r_base rq + o)) by (cbn; lia).
        apply AGs; [eapply GREG; eauto; lia| lia].
Qed.
End THM_C.
End REMAP.
