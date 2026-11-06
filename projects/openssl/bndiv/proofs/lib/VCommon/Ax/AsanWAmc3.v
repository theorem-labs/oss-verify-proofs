(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec CatExec SeqExec StoreOk ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanSBase AsanSLibc AsanSMat AsanSMiz AsanSRipA AsanWMemcpy AsanWMemcpyF1 AsanWMcStep AsanWMat AsanWMcM3 AsanWAmc1 AsanWAmc2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

(* [comment removed for export] *)
Record RipCode (segs : list Segment) (b' z gK gMB gME gHE : Z) : Prop := {
  rc_W : words_ok segs b' RIP_WORDS = true;
  rc_Wh : words_ok segs (b' - 0x48c) HLP_WORDS = true;
  rc_Wz : words_ok segs z MIZ_WORDS = true;
  rc_Jz : jal_ok segs b' 0x170 1 z = true;
  rc_h0 : pair_ok segs (b' - 0x48c) 0x0 11 11 gK = true;
  rc_h20 : pair_ok segs (b' - 0x48c) 0x20 13 13 gMB = true;
  rc_h28 : pair_ok segs (b' - 0x48c) 0x28 14 14 gME = true;
  rc_h44 : pair_ok segs (b' - 0x48c) 0x44 14 14 gHE = true;
  rc_2c : pair_ok segs b' 0x2c 10 21 gK = true;
  rc_4c : pair_ok segs b' 0x4c 13 13 gMB = true;
  rc_54 : pair_ok segs b' 0x54 14 14 gME = true;
  rc_70 : pair_ok segs b' 0x70 14 14 gHE = true;
  rc_94 : pair_ok segs b' 0x94 12 12 gMB = true;
  rc_9c : pair_ok segs b' 0x9c 13 13 gME = true;
  rc_b8 : pair_ok segs b' 0xb8 13 13 gHE = true
}.

(* [comment removed for export] *)
Definition rp (n : Z) : Z := if (n <=? 64)%Z then 2%Z else (n + 2)%Z.
Definition amc_pages (n : Z) : Z := (2 * rp n + mc_pages n)%Z.

(* [comment removed for export] *)
Definition BCL : list reg := [5; 6; 7; 28; 10; 11; 12; 13; 14; 15; 16; 17; 1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24].

Lemma MCR_trans : forall CL CL' ms0 S S', MCRc CL ms0 S -> MCRc CL' S S' -> (forall r, In r CL' -> In r CL) -> MCRc CL ms0 S'.
Proof.
  intros CL CL' ms0 S S' [H1 H2 H3 H4 H5 H6] [G1 G2 G3 G4 G5 G6] Hinc.
  constructor; [exact G1 | congruence | congruence | congruence | |].
  - destruct G5 as [G5|G5]; [rewrite G5; exact H5 | right; exact G5].
  - intros r Hr. rewrite (G6 r) by (intros X; exact (Hr (Hinc r X))). exact (H6 r Hr).
Qed.

Ltac in_bcl := cbn [In BCL]; repeat first [ left; reflexivity | right ].
Ltac bcl_chain HS :=
  repeat first
   [ (eapply MCR_store; [ | rewrite ?resv_setx; reflexivity ])
   | (eapply MCR_setx; [ | first [ left; reflexivity | right; solve [ in_bcl ] ]
                      | rewrite ?resv_setx; reflexivity | rewrite ?mem_setx; reflexivity ]) ];
  exact HS.

(* [comment removed for export] *)
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac lz := nodisj; lia.

(* [comment removed for export] *)
Ltac notin := let X := fresh "X" in cbn [In HCLOB MCF_CLOB BCL]; intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X.

Lemma pcw_even : forall b o, (0 <= b)%Z -> (0 <= o)%Z -> (b + o < 2 ^ 64)%Z -> (b mod 4 = 0)%Z -> (o mod 4 = 0)%Z ->
  (bv_unsigned (pcw b o) mod 2 = 0)%Z.
Proof.
  intros b o Hb Ho Hbo Hb4 Ho4. unfold pcw. rewrite bvu_z by lia.
  pose proof (Z.div_mod b 4 ltac:(lia)). pose proof (Z.div_mod o 4 ltac:(lia)).
  replace (b + o)%Z with ((2 * (b / 4) + 2 * (o / 4)) * 2)%Z by lia. apply Z.mod_mul. lia.
Qed.

Lemma pcw_base : forall b o, pcw b o = pcw (b + o) 0.
Proof. intros b o. unfold pcw. f_equal. lia. Qed.

Section Amc.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variables b gI aI gK aK gMB aMB gME aME gHE aHE gR e : Z.
Variables rb mz : Z.   (* [comment removed for export] *)
Hypothesis HA : AmcCode segs b gI gK gR.
Hypothesis HRC : RipCode segs rb mz gK gMB gME gHE.
Hypothesis HJ1 : jal_ok segs b 0x3ac 1 rb = true.
Hypothesis HJ2 : jal_ok segs b 0x4a8 1 rb = true.
Hypothesis Hrb : (0x10000 <= rb /\ rb + 0x20000 < 2 ^ 47 /\ rb mod 4 = 0)%Z.
Hypothesis HMC : MCFCode segs e.
Hypothesis Hb : (0x10000 <= b /\ b + 0x30000 < 2 ^ 47 /\ b mod 4 = 0)%Z.
Hypothesis He : (0 <= e /\ e + 0x1000 < 2 ^ 47 /\ e mod 4 = 0)%Z.
Hypothesis Hgb : (0 <= gK < 2 ^ 40 /\ 0 <= gMB < 2 ^ 40 /\ 0 <= gME < 2 ^ 40 /\ 0 <= gHE < 2 ^ 40 /\
                  0 <= aK < 2 ^ 40 /\ 0 <= aMB < 2 ^ 40 /\ 0 <= aME < 2 ^ 40 /\ 0 <= aHE < 2 ^ 40 /\
                  0 <= gI < 2 ^ 40 /\ 0 <= aI < 2 ^ 40 /\ 0 <= gR < 2 ^ 40)%Z.

Variable model0 : Model.
Variable T : TSet.
Variable ms0 : machine_state.
Variables (sp dst src n : Z) (bs : list byte) (vI : byte).
Hypothesis Hh0 : m_halted model0 = None.
Hypothesis Hsp : (0x10007fff8000 + 2232 <= sp <= 2 ^ 47)%Z.
Hypothesis Hspok : store_ok segs (ms_mem ms0) (Z_to_bv 64 (sp - 2232)) 2232 = true.
Hypothesis Hspnl : no_lazy model0 (sp - 2232) sp.
Hypothesis Hn : (0 <= n <= 2 ^ 40)%Z.
Hypothesis Hd0 : (0 <= dst)%Z.
Hypothesis Hs0 : (0 <= src)%Z.
Hypothesis Hdn : (dst + n <= 2 ^ 47)%Z.
Hypothesis Hsn : (src + n <= 2 ^ 47)%Z.
Hypothesis Hbig : (65 <= n)%Z ->
  (src + n + 8 <= 2 ^ 47 /\ (0x10007fff8000 <= src \/ src + n + 8 <= 0x7fff8000))%Z /\
  (dst + n + 8 <= 2 ^ 47 /\ (0x10007fff8000 <= dst \/ dst + n + 8 <= 0x7fff8000))%Z.
Hypothesis Hdisj : (src + n <= dst \/ dst + n <= src)%Z.
Hypothesis Hdfr : (dst + n <= sp - 2232 \/ sp <= dst)%Z.
Hypothesis Hsfr : (src + n <= sp - 2232 \/ sp <= src)%Z.
Hypothesis Hbs : rdn segs (ms_mem ms0) (Z_to_bv 64 src) (Z.to_nat n) = Some bs.
Hypothesis Hsok : store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Z.to_nat n) = true.
(* [comment removed for export] *)
Hypothesis HgI : cell8 segs (ms_mem ms0) gI aI.
Hypothesis HvI : bat segs (ms_mem ms0) (Z_to_bv 64 aI) = Some vI.
Hypothesis HvI0 : bv_unsigned vI <> 0%Z.
Hypothesis HgR : cell8 segs (ms_mem ms0) gR e.
Hypothesis Hg0 : globals segs gK gMB gME gHE aK aMB aME aHE (ms_mem ms0).
Hypothesis HgN : globals_nl gK gMB gME gHE aK aMB aME aHE model0.
Hypothesis HnlI : no_lazy model0 gI (gI + 8).
Hypothesis HnlaI : no_lazy model0 aI (aI + 1).
Hypothesis HnlR : no_lazy model0 gR (gR + 8).
(* [comment removed for export] *)
Hypothesis Hshs : (1 <= n)%Z -> forall q, (0x7fff8000 + src / 8 - 7 <= q <= 0x7fff8000 + (src + n - 1) / 8 + 7)%Z ->
  (0x7fff8000 <= q < 0x10007fff8000)%Z -> bat segs (ms_mem ms0) (Z_to_bv 64 q) = Some (Z_to_bv 8 0).
Hypothesis Hshd : (1 <= n)%Z -> forall q, (0x7fff8000 + dst / 8 - 7 <= q <= 0x7fff8000 + (dst + n - 1) / 8 + 7)%Z ->
  (0x7fff8000 <= q < 0x10007fff8000)%Z -> bat segs (ms_mem ms0) (Z_to_bv 64 q) = Some (Z_to_bv 8 0).
Hypothesis Hbud : (vm_backing_used model0 + 4096 * amc_pages n <= vm_limit (m_vmmaps model0))%Z.
Hypothesis Hra : (bv_unsigned (rg ms0 1) mod 2 = 0)%Z.
Hypothesis H2 : rg ms0 2 = Z_to_bv 64 sp.
Hypothesis H10 : rg ms0 10 = Z_to_bv 64 dst.
(* [comment removed for export] *)
Definition AMEM (m' : word -> option byte) : Prop :=
  exists mf, (forall x : word, ~ (sp - 2232 <= bv_unsigned x < sp)%Z -> mf x = ms_mem ms0 x) /\
             mem_grows (ms_mem ms0) mf /\ copied m' mf dst n bs.
Hypothesis HK : forall ms' model', MCRc MCF_CLOB ms0 ms' -> AMEM (ms_mem ms') -> ms_pc_val ms' = rg ms0 1 ->
  mat_of model0 model' (amc_pages n) -> realizes_cfg segs cfg (mkCfg ms' model') T.

(* [comment removed for export] *)
Set Default Proof Using "All".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition SB (o : Z) (v : word) (m : word -> option byte) : word -> option byte :=
  write_to_mem m (Z_to_bv 64 (sp + o)) (store_bytes SZ8 v).

(* [comment removed for export] *)
Definition Mf : word -> option byte :=
  SB (-80) (rg ms0 24) (SB (-72) (rg ms0 23) (SB (-64) (rg ms0 22) (SB (-56) (rg ms0 21) (SB (-48) (rg ms0 20)
  (SB (-40) (rg ms0 19) (SB (-32) (rg ms0 18) (SB (-24) (rg ms0 9) (SB (-16) (rg ms0 8) (SB (-8) (rg ms0 1) (ms_mem ms0)))))))))).

(* [comment removed for export] *)
Definition MEMI (m : word -> option byte) : Prop :=
  (forall x : word, ~ (sp - 2232 <= bv_unsigned x < sp - 2160)%Z -> m x = Mf x) /\ mem_grows Mf m.

Definition BI (S : machine_state) : Prop := MCRc BCL ms0 S /\ MEMI (ms_mem S).

Lemma grows_w : forall m1 m2 a l, mem_grows m1 m2 -> mem_grows m1 (write_to_mem m2 a l).
Proof. intros m1 m2 a l H. apply (mem_grows_trans m1 m2); [exact H | apply write_to_mem_grows]. Qed.

Lemma SB_out : forall o v m (x : word), (-80 <= o <= -8)%Z -> ~ (sp + o <= bv_unsigned x < sp + o + 8)%Z -> SB o v m x = m x.
Proof. intros o v m x Ho Hx. unfold SB. apply w2m_outside; rewrite store_bytes8_len, bvu_z by lia; lia. Qed.

Lemma Mf_out : forall x : word, ~ (sp - 80 <= bv_unsigned x < sp)%Z -> Mf x = ms_mem ms0 x.
Proof. intros x Hx. unfold Mf. rewrite !SB_out by lia. reflexivity. Qed.

Lemma Mf_grows : mem_grows (ms_mem ms0) Mf.
Proof. unfold Mf, SB. repeat apply grows_w. apply mem_grows_refl. Qed.

Lemma MEMI_Mf : MEMI Mf.
Proof. split; [reflexivity | apply mem_grows_refl]. Qed.

Lemma MEMI_out : forall m (x : word), MEMI m -> ~ (sp - 2232 <= bv_unsigned x < sp)%Z -> m x = ms_mem ms0 x.
Proof. intros m x [H _] Hx. rewrite H by lia. apply Mf_out. lia. Qed.

Lemma MEMI_grows : forall m, MEMI m -> mem_grows (ms_mem ms0) m.
Proof. intros m [_ H]. exact (mem_grows_trans _ _ _ Mf_grows H). Qed.

(* [comment removed for export] *)
Lemma rdn_MEMI : forall m (a : Z) (k : nat), MEMI m -> (0 <= a)%Z -> (a + Z.of_nat k < 2 ^ 64)%Z ->
  (a + Z.of_nat k <= sp - 2232 \/ sp <= a)%Z ->
  rdn segs m (Z_to_bv 64 a) k = rdn segs (ms_mem ms0) (Z_to_bv 64 a) k.
Proof.
  intros m a k HM Ha Hk Hd. apply rdn_ext; rewrite bvu_z by lia; [lia|].
  intros x Hx. apply MEMI_out; [exact HM | lia].
Qed.

Lemma cell8_MEMI : forall m a v, MEMI m -> (0 <= a < 2 ^ 40)%Z -> cell8 segs (ms_mem ms0) a v -> cell8 segs m a v.
Proof.
  intros m a v HM Ha (l & Hl & Hv). exists l. split; [|exact Hv].
  rewrite (rdn_MEMI m a 8 HM) by lia. exact Hl.
Qed.

Lemma bat_MEMI : forall m (q : Z) v, MEMI m -> (0 <= q < 0x10007fff8000)%Z ->
  bat segs (ms_mem ms0) (Z_to_bv 64 q) = Some v -> bat segs m (Z_to_bv 64 q) = Some v.
Proof.
  intros m q v HM Hq H. unfold bat in *. rewrite (MEMI_out m _ HM) by (rewrite bvu_z by lia; lia). exact H.
Qed.

Lemma globals_MEMI : forall m, MEMI m -> globals segs gK gMB gME gHE aK aMB aME aHE m.
Proof.
  intros m HM. destruct Hg0 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  repeat split; apply cell8_MEMI; try assumption; lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_SB_same : forall o v m, (-80 <= o <= -8)%Z ->
  rdn segs (SB o v m) (Z_to_bv 64 (sp + o)) 8 = Some (store_bytes SZ8 v).
Proof.
  intros o v m Ho. unfold SB. rewrite write_to_mem_wbytes.
  exact (rdn_wbytes_hit segs (store_bytes SZ8 v) m (Z_to_bv 64 (sp + o)) ltac:(rewrite store_bytes8_len, bvu_z by lia; lia)).
Qed.

Lemma rdn_SB_other : forall o o' v m, (-80 <= o <= -8)%Z -> (-80 <= o' <= -8)%Z -> (o + 8 <= o' \/ o' + 8 <= o)%Z ->
  rdn segs (SB o v m) (Z_to_bv 64 (sp + o')) 8 = rdn segs m (Z_to_bv 64 (sp + o')) 8.
Proof.
  intros o o' v m Ho Ho' Hd. apply rdn_ext; rewrite bvu_z by lia; [lia|].
  intros x Hx. apply SB_out; lia.
Qed.

Lemma rdn_slot : forall m o, MEMI m -> (-80 <= o <= -8)%Z ->
  rdn segs m (Z_to_bv 64 (sp + o)) 8 = rdn segs Mf (Z_to_bv 64 (sp + o)) 8.
Proof.
  intros m o [HM _] Ho. apply rdn_ext; rewrite bvu_z by lia; [lia|]. intros x Hx. apply HM. lia.
Qed.

Local Ltac rdf := unfold Mf;
  repeat first [ rewrite rdn_SB_same by lia; reflexivity | rewrite rdn_SB_other by lia ].

Lemma Mf_rd1 : rdn segs Mf (Z_to_bv 64 (sp + -8)) 8 = Some (store_bytes SZ8 (rg ms0 1)). Proof. rdf. Qed.
Lemma Mf_rd8 : rdn segs Mf (Z_to_bv 64 (sp + -16)) 8 = Some (store_bytes SZ8 (rg ms0 8)). Proof. rdf. Qed.
Lemma Mf_rd9 : rdn segs Mf (Z_to_bv 64 (sp + -24)) 8 = Some (store_bytes SZ8 (rg ms0 9)). Proof. rdf. Qed.
Lemma Mf_rd18 : rdn segs Mf (Z_to_bv 64 (sp + -32)) 8 = Some (store_bytes SZ8 (rg ms0 18)). Proof. rdf. Qed.
Lemma Mf_rd19 : rdn segs Mf (Z_to_bv 64 (sp + -40)) 8 = Some (store_bytes SZ8 (rg ms0 19)). Proof. rdf. Qed.
Lemma Mf_rd20 : rdn segs Mf (Z_to_bv 64 (sp + -48)) 8 = Some (store_bytes SZ8 (rg ms0 20)). Proof. rdf. Qed.
Lemma Mf_rd21 : rdn segs Mf (Z_to_bv 64 (sp + -56)) 8 = Some (store_bytes SZ8 (rg ms0 21)). Proof. rdf. Qed.
Lemma Mf_rd22 : rdn segs Mf (Z_to_bv 64 (sp + -64)) 8 = Some (store_bytes SZ8 (rg ms0 22)). Proof. rdf. Qed.
Lemma Mf_rd23 : rdn segs Mf (Z_to_bv 64 (sp + -72)) 8 = Some (store_bytes SZ8 (rg ms0 23)). Proof. rdf. Qed.
Lemma Mf_rd24 : rdn segs Mf (Z_to_bv 64 (sp + -80)) 8 = Some (store_bytes SZ8 (rg ms0 24)). Proof. rdf. Qed.

Lemma ld_st8 : forall v : word, load_word SZ8 true (store_bytes SZ8 v) = v.
Proof. intros v. exact (load8 true v). Qed.

(* [comment removed for export] *)
Lemma nl_mat : forall m k lo hi, mat_of model0 m k -> no_lazy model0 lo hi -> no_lazy m lo hi.
Proof. intros m k lo hi Hm H. exact (no_lazy_mat model0 m k lo hi Hm H). Qed.

Lemma acc_fr : forall m k (a : Z) (c : nat), mat_of model0 m k -> (sp - 2232 <= a)%Z -> (a + Z.of_nat c <= sp)%Z ->
  acc_ok m [(Z_to_bv 64 a, c)].
Proof.
  intros m k a c Hm Ha Hc. apply acc_ok_one; rewrite bvu_z by lia; [lia|].
  apply (nl_mat m k _ _ Hm). apply (no_lazy_sub model0 _ _ _ _ Hspnl); lia.
Qed.

Lemma acc_cell : forall m k (a : Z) (c : nat), mat_of model0 m k -> (0 <= a < 2 ^ 40)%Z -> (Z.of_nat c <= 8)%Z ->
  no_lazy model0 a (a + Z.of_nat c) -> acc_ok m [(Z_to_bv 64 a, c)].
Proof.
  intros m k a c Hm Ha Hc Hnl. apply acc_ok_one; rewrite bvu_z by lia; [lia|]. exact (nl_mat m k _ _ Hm Hnl).
Qed.

Lemma halted_mat : forall m k, mat_of model0 m k -> m_halted m = None.
Proof. intros m k Hm. rewrite (mat_of_halted model0 m k Hm). exact Hh0. Qed.

Lemma pages_nonneg : (0 <= rp n /\ 0 <= mc_pages n)%Z.
Proof.
  unfold rp, mc_pages. destruct (n <=? 64)%Z; pose proof (Z.div_pos n 4096 ltac:(lia) ltac:(lia)); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Abbreviation FA x := (x segs b gI gK gR HA).

Lemma MCR_restore : forall S, MCRc BCL ms0 S ->
  rg S 1 = rg ms0 1 -> rg S 2 = rg ms0 2 -> rg S 8 = rg ms0 8 -> rg S 9 = rg ms0 9 -> rg S 10 = rg ms0 10 ->
  rg S 18 = rg ms0 18 -> rg S 19 = rg ms0 19 -> rg S 20 = rg ms0 20 -> rg S 21 = rg ms0 21 -> rg S 22 = rg ms0 22 ->
  rg S 23 = rg ms0 23 -> rg S 24 = rg ms0 24 -> MCRc MCF_CLOB ms0 S.
Proof.
  intros S [G1 G2 G3 G4 G5 G6] E1 E2 E8 E9 E10 E18 E19 E20 E21 E22 E23 E24.
  constructor; try assumption. intros r Hr.
  destruct (decide (r = 1)) as [->|N1]; [exact E1|]. destruct (decide (r = 2)) as [->|N2]; [exact E2|].
  destruct (decide (r = 8)) as [->|N8]; [exact E8|]. destruct (decide (r = 9)) as [->|N9]; [exact E9|].
  destruct (decide (r = 10)) as [->|N10]; [exact E10|]. destruct (decide (r = 18)) as [->|N18]; [exact E18|].
  destruct (decide (r = 19)) as [->|N19]; [exact E19|]. destruct (decide (r = 20)) as [->|N20]; [exact E20|].
  destruct (decide (r = 21)) as [->|N21]; [exact E21|]. destruct (decide (r = 22)) as [->|N22]; [exact E22|].
  destruct (decide (r = 23)) as [->|N23]; [exact E23|]. destruct (decide (r = 24)) as [->|N24]; [exact E24|].
  apply G6. intros X. apply Hr. cbn [In BCL] in X. cbn [In MCF_CLOB].
  repeat (destruct X as [X|X];
          [subst r; first [ solve [repeat first [left; reflexivity | right]]
                          | match goal with N : ?c <> ?c |- _ => exact (False_ind _ (N eq_refl)) end ] |]).
  contradiction.
Qed.

Lemma s_epi : forall S m, MCRc BCL ms0 S -> ms_pc_val S = pcw b 0x100 ->
  rg S 2 = Z_to_bv 64 (sp - 2160) -> rg S 10 = Z_to_bv 64 dst ->
  (forall o, (-80 <= o <= -8)%Z -> rdn segs (ms_mem S) (Z_to_bv 64 (sp + o)) 8 = rdn segs Mf (Z_to_bv 64 (sp + o)) 8) ->
  AMEM (ms_mem S) -> mat_of model0 m (amc_pages n) -> realizes_cfg segs cfg (mkCfg S m) T.
Proof.
  intros S m HS Hpc HS2 HS10 Hsl HM Hmat. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  pose proof (halted_mat m _ Hmat) as Hh.
  Local Ltac ldslot F D o L Hsl Hmat :=
    wl F D ltac:(cbn [msz_n]; match goal with |- rdn _ _ (Z_to_bv 64 ?a) 8 = _ => replace a with (sp + o)%Z by lia end;
                 rewrite Hsl by lia; exact L)
           ltac:(cbn [msz_n]; eapply acc_fr; [exact Hmat | lia | change (Z.of_nat 8) with 8%Z; lia]).
  wr wacc_OpImm (FA FA_100) DA_08010113 valX.
  ldslot (FA FA_104) DA_7e813083 (-8)%Z Mf_rd1 Hsl Hmat.
  ldslot (FA FA_108) DA_7e013403 (-16)%Z Mf_rd8 Hsl Hmat.
  ldslot (FA FA_10c) DA_7d813483 (-24)%Z Mf_rd9 Hsl Hmat.
  ldslot (FA FA_110) DA_7d013903 (-32)%Z Mf_rd18 Hsl Hmat.
  ldslot (FA FA_114) DA_7c813983 (-40)%Z Mf_rd19 Hsl Hmat.
  ldslot (FA FA_118) DA_7c013a03 (-48)%Z Mf_rd20 Hsl Hmat.
  ldslot (FA FA_11c) DA_7b813a83 (-56)%Z Mf_rd21 Hsl Hmat.
  ldslot (FA FA_120) DA_7b013b03 (-64)%Z Mf_rd22 Hsl Hmat.
  ldslot (FA FA_124) DA_7a813b83 (-72)%Z Mf_rd23 Hsl Hmat.
  ldslot (FA FA_128) DA_7a013c03 (-80)%Z Mf_rd24 Hsl Hmat.
  wr wacc_OpImm (FA FA_12c) DA_7f010113 valX.
  eapply xs_jalr; [ exact Hh | reflexivity | rewrite pc_setx; exact (FA FA_130) | reflexivity | exact DA_00008067
                  | regX | reflexivity | rewrite ld_st8; apply ret_even; exact Hra | resvX | memX | ].
  apply HK.
  - apply MCR_restore; [ bcl_chain HS | .. ]; rgn; rewrite ?ld_st8; try reflexivity.
    + rewrite H2. f_equal. lia.
    + rewrite HS10, H10. reflexivity.
  - rewrite ?mem_setx. exact HM.
  - reflexivity.
  - exact Hmat.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma MCF_in_BCL : forall r, In r MCF_CLOB -> In r BCL.
Proof.
  intros r Hr. cbn [In MCF_CLOB] in Hr.
  repeat (destruct Hr as [Hr|Hr]; [subst r; cbn [In BCL]; solve [repeat first [left; reflexivity | right]] |]). contradiction.
Qed.

Lemma s_mc : forall S m, BI S -> mat_of model0 m (2 * rp n) -> ms_pc_val S = pcw b 0xf4 ->
  rg S 2 = Z_to_bv 64 (sp - 2160) -> rg S 10 = Z_to_bv 64 dst -> rg S 11 = Z_to_bv 64 src -> rg S 12 = Z_to_bv 64 n ->
  realizes_cfg segs cfg (mkCfg S m) T.
Proof.
  intros S m [HS HM] Hmat Hpc HS2 HS10 HS11 HS12. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  pose proof (halted_mat m _ Hmat) as Hh.
  eapply xs_got; [ exact (amc_pR _ _ _ _ _ HA) | reflexivity | lia | lia | exact Hh | exact Hsvc | exact Hpc
                 | apply cell8_MEMI; [exact HM | lia | exact HgR] | eapply nl_mat; [exact Hmat | exact HnlR] | ].
  intros X r0 m1 -> ->.
  eapply xs_jalr; [ exact Hh | reflexivity | rewrite pc_setx; exact (FA FA_fc) | reflexivity | exact DA_000680e7
                  | regX | pcX
                  | replace (Z_to_bv 64 e) with (pcw e 0) by (unfold pcw; f_equal; lia); apply ret_pcw; first [lia | reflexivity]
                  | resvX | memX | ].
  match goal with |- realizes_cfg _ _ (mkCfg ?S' _) _ => remember S' as Sc eqn:ESc end.
  assert (HSc : MCRc BCL ms0 Sc) by (subst Sc; bcl_chain HS).
  assert (Hm : ms_mem Sc = ms_mem S) by (subst Sc; reflexivity).
  assert (Hc1 : rg Sc 1 = pcw b 0x100) by (subst Sc; regX).
  assert (Hc2 : rg Sc 2 = Z_to_bv 64 (sp - 2160)) by (subst Sc; regX).
  assert (Hc10 : rg Sc 10 = Z_to_bv 64 dst) by (subst Sc; regX).
  assert (Hc11 : rg Sc 11 = Z_to_bv 64 src) by (subst Sc; regX).
  assert (Hc12 : rg Sc 12 = Z_to_bv 64 n) by (subst Sc; regX).
  assert (Hcpc : ms_pc_val Sc = pcw e 0) by (subst Sc; reflexivity).
  assert (Hcsvc : ms_svc_pending Sc = None) by (subst Sc; reflexivity).
  clear ESc. pose proof pages_nonneg as [Hp1 Hp2].
  apply (memcpy_sum_mat segs cfg e HMC Sc m T dst src n bs Hcsvc Hcpc Hh Hc10 Hc11 Hc12 Hd0 Hs0 (proj1 Hn) Hdn Hsn Hdisj).
  - rewrite Hm. rewrite (rdn_MEMI _ src (Z.to_nat n) HM) by lia. exact Hbs.
  - rewrite Hm. exact (store_ok_mono segs _ _ _ _ (MEMI_grows _ HM) Hsok).
  - pose proof Hmat as [_ Hu]. rewrite (mat_of_vmmaps model0 m _ Hmat). unfold amc_pages, page_size in *. lia.
  - rewrite Hc1. apply pcw_even; first [lia | reflexivity].
  - intros S' m' HMCR Hcp Hpc' Hmat'.
    apply (s_epi S' m').
    + exact (MCR_trans _ _ _ _ _ HSc HMCR MCF_in_BCL).
    + rewrite Hpc'. exact Hc1.
    + rewrite (mcr_regs _ _ _ HMCR 2) by notin. exact Hc2.
    + rewrite (mcr_regs _ _ _ HMCR 10) by notin. exact Hc10.
    + intros o Ho. rewrite <- (rdn_slot (ms_mem S) o HM Ho). rewrite <- Hm.
      apply rdn_ext; rewrite bvu_z by lia; [lia|]. intros x Hx. apply (proj2 (Hcp x)). lia.
    + exists (ms_mem Sc). rewrite Hm. split; [intros x Hx; exact (MEMI_out _ x HM Hx)|]. split; [exact (MEMI_grows _ HM)|].
      rewrite <- Hm. exact Hcp.
    + replace (amc_pages n) with (2 * rp n + mc_pages n)%Z by reflexivity. exact (mat_of_trans _ _ _ _ _ Hmat Hmat').
Qed.

End Amc.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
