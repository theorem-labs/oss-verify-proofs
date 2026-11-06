(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PmModel PmModelFacts PmStatics PmSpecs PmStep PmKeep PmFrame PmParSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMPK.

(* [comment removed for export] *)
Definition dkr (M M' : word -> option byte) (a n : Z) : Prop :=
  forall i, a <= i < a + n -> M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) <> None.
Lemma dkr_grows M M' a n : mem_grows M M' -> dkr M M' a n.
Proof. intros G i _ D. apply G. exact D. Qed.
Lemma dkr_agree M M' a n : L5C.agree_on M M' a n -> dkr M M' a n.
Proof. intros AG i Hi D. rewrite AG by exact Hi. exact D. Qed.
Lemma dkr_sub M M' a n a' n' : dkr M M' a n -> a <= a' -> a' + n' <= a + n -> dkr M M' a' n'.
Proof. intros D H1 H2 i Hi. apply D. lia. Qed.
Lemma dkr_trans M1 M2 M3 a n : dkr M1 M2 a n -> dkr M2 M3 a n -> dkr M1 M3 a n.
Proof. intros D1 D2 i Hi D. apply (D2 i Hi). apply (D1 i Hi). exact D. Qed.
Lemma defined_dkr M M' a n : dkr M M' a n -> L5.defined M a n -> L5.defined M' a n.
Proof. intros D Df i Hi. apply D; [lia| apply Df; exact Hi]. Qed.
Lemma agree_of_frz M M' (P : Z -> Prop) a n :
  (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + n <= 2 ^ 64 ->
  (forall i, a <= i < a + n -> ~ P i) -> L5C.agree_on M M' a n.
Proof. intros F H1 H2 N i Hi. apply F; [lia| apply N; exact Hi]. Qed.

(* [comment removed for export] *)
Lemma cs_in (KS : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) PMK.cs_all = true -> forall k, In k PMK.cs_all -> In k KS.
Proof. intros H k Hk. apply L5K.In_of_mem. rewrite forallb_forall in H. apply H. exact Hk. Qed.
Lemma sub_in (KS ks : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) ks = true -> forall k, In k ks -> In k KS.
Proof. intros H k Hk. apply L5K.In_of_mem. rewrite forallb_forall in H. apply H. exact Hk. Qed.
Lemma word_id (w : word) : Z_to_bv 64 (bv_unsigned w) = w.
Proof. apply Z_to_bv_bv_unsigned. Qed.
Lemma m16_8 x : x mod 16 = 0 -> x mod 8 = 0.
Proof. intros H. apply Z.mod_divide in H; [|lia]. destruct H as (q & ->). replace (q * 16) with ((q * 2) * 8) by lia. apply Z.mod_mul. lia. Qed.
Lemma m8_add x k : x mod 8 = 0 -> (x + 8 * k) mod 8 = 0.
Proof. intros H. rewrite Z.mul_comm, Z.mod_add by lia. exact H. Qed.

Section Kit.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis KL : PMK.klayout segs L.

Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Along.
Variables (LBc : list (Z * Z)) (sp' scr' : Z) (W' : list L5.range) (M M' : word -> option byte).
Hypothesis E : PMK.ek L LBc sp' scr' W' M M'.
Hypothesis STKc : L5C.stk (hl_sptop L) M sp' scr'.
Hypothesis SCR0 : 0 <= scr'.
Hypothesis BR : PMFR.brange L LBc.

Lemma ag_hi a n : sp' <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ PMK.inW W' i) -> L5C.agree_on M M' a n.
Proof.
  intros H1 H2 N. apply (PMKP.ek_agree_stack segs L KL LBc sp' scr' W' M M' a n E STKc SCR0 H1 H2). intros i Hi.
  apply PMFR.outside_of_not_inW. apply N. exact Hi.
Qed.
Lemma ag_sub_blk B m a n : In (B, m) LBc -> B <= a -> a + n <= B + m -> (forall i, a <= i < a + n -> ~ PMK.inW W' i) -> L5C.agree_on M M' a n.
Proof.
  intros Hin H1 H2 N. destruct (BR B m Hin) as (Q0 & Q1 & Q4).
  pose proof STKc as (_ & SLO & SHI & STOP & _).
  apply (PMKP.ek_agree L LBc sp' scr' W' M M' a n E). intros i Hi.
  apply (PMKP.kept_block segs L KL LBc sp' scr' W' B m i Hin); [lia| lia| exact Q4| exact Q1| lia|].
  apply PMFR.outside_of_not_inW. apply N. exact Hi.
Qed.
Lemma ag_blk B m : In (B, m) LBc -> (forall i, B <= i < B + m -> ~ PMK.inW W' i) -> L5C.agree_on M M' B m.
Proof. intros Hin N. apply (ag_sub_blk B m B m Hin); [lia| lia| exact N]. Qed.
End Along.

(* [comment removed for export] *)
Lemma ek_drop_own OWN LBX sp' scr' W W2 M M' :
  PMK.ek L (OWN ++ LBX) sp' scr' W2 M M' ->
  (forall B m, In (B, m) OWN -> B + m <= hl_ceil L /\ (B + m <= hl_img_lo L \/ hl_img_hi L <= B) /\
                               forall B' m', In (B', m') LBX -> B + m <= B' \/ B' + m' <= B) ->
  (forall a, L5.outside W a -> L5.outside W2 a \/ exists B m, In (B, m) OWN /\ B <= a < B + m) ->
  PMK.ek L LBX sp' scr' W M M'.
Proof.
  intros E HOWN HW a (Ha & Hc & He & Ho). apply E. split; [exact Ha|]. split; [|split; [exact He|]].
  - destruct Hc as [(b & Hb & Hr)|Hc]; [left; exists b; split; [apply in_or_app; right; exact Hb| exact Hr]| right; exact Hc].
  - destruct (HW a Ho) as [O|(B & m & Hin & HB)]; [exact O|]. exfalso. destruct (HOWN B m Hin) as (Z1 & Z2 & Z3).
    destruct Hc as [((B', m') & Hb & Hr)|[(S1 & S2)|(I1 & I2)]].
    + cbn in Hr. destruct (Z3 B' m' Hb); lia.
    + lia.
    + lia.
Qed.
Lemma dk_incl LB LB2 sp' scr' M M' : PMK.dk L LB2 sp' scr' M M' -> incl LB LB2 -> PMK.dk L LB sp' scr' M M'.
Proof.
  intros D I a Ha Hc He HM. apply (D a Ha); [|exact He| exact HM].
  destruct Hc as [(b & Hb & Hr)|Hc]; [left; exists b; split; [apply I; exact Hb| exact Hr]| right; exact Hc].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma elem_of_In (x : Z) (l : list Z) : In x l -> x ∈ l.
Proof. induction l as [|a l IH]; intros H; [destruct H|]. destruct H as [<-|H]; [constructor| constructor; apply IH; exact H]. Qed.
Lemma fst_neq_app (l1 l2 : list (Z * Z)) B1 m1 B2 m2 :
  NoDup (map fst (l1 ++ l2)) -> In (B1, m1) l1 -> In (B2, m2) l2 -> B1 <> B2.
Proof.
  induction l1 as [|a l1 IH]; intros ND H1 H2; [destruct H1|]. cbn [app map] in ND. inversion ND as [|x l NI ND']. subst x l.
  destruct H1 as [->|H1].
  - cbn [fst] in NI. intros E. subst B2. apply NI. apply elem_of_In. rewrite map_app. apply in_or_app. right. apply (in_map fst l2 (B1, m2) H2).
  - apply IH; assumption.
Qed.
Lemma blocks_apart_heap (HIok : heap_iface_ok L SCFG HI) LB cr M VM B1 m1 B2 m2 :
  hi_heap HI LB cr M VM -> In (B1, m1) LB -> In (B2, m2) LB -> B1 <> B2 -> B1 + m1 <= B2 \/ B2 + m2 <= B1.
Proof.
  intros HH H1 H2 NE. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M VM HH) (B1, m1) H1) as (_ & _ & AP). cbn [fst snd] in AP.
  apply (L5C.blocks_apart_in B1 m1 (lb_remove B1 LB) B2 m2 AP). apply L5C.in_lb_remove_neq; [exact H2| intros E; apply NE; symmetry; exact E].
Qed.
Lemma heap_nodup (HIok : heap_iface_ok L SCFG HI) LB cr M VM : hi_heap HI LB cr M VM -> NoDup (map fst LB).
Proof. intros HH. exact (proj1 (proj2 (hio_wf L SCFG HI HIok LB cr M VM HH))). Qed.
Lemma heap_block_defined (HIok : heap_iface_ok L SCFG HI) LB cr M VM B m : hi_heap HI LB cr M VM -> In (B, m) LB -> L5.defined M B m.
Proof. intros HH H1. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M VM HH) (B, m) H1) as (_ & D & _). exact D. Qed.

Lemma dkr_hpres_blk LBc sp' scr' W' M M' B m :
  L5C.hpres L LBc sp' scr' W' M M' -> In (B, m) LBc -> PMFR.brange L LBc -> hl_sptop L <= 2 ^ 47 -> dkr M M' B m.
Proof.
  intros HP Hin BRc TOP i Hi D. destruct (BRc B m Hin) as (Q0 & Q1 & Q4). pose proof (PMK.kl_errno segs L KL) as KE. pose proof (PMK.kl_img segs L KL) as KI.
  apply (L5C.hpres_cdef L LBc sp' scr' W' M M' i HP); [unfold hl_ceil in Q4; lia| left; exists (B, m); split; [exact Hin| cbn; lia]| unfold in_errno; lia| exact D].
Qed.
(* [comment removed for export] *)
Lemma dkr_hpres_hi LBc sp' scr' W' M M' a n :
  L5C.hpres L LBc sp' scr' W' M M' -> L5C.stk (hl_sptop L) M sp' scr' -> 0 <= scr' -> sp' <= a -> a + n <= 2 ^ 64 -> dkr M M' a n.
Proof.
  intros HP (_ & SLO & SHI & STOP & _) S0 H1 H2 i Hi D. pose proof (PMK.kl_errno segs L KL) as KE. pose proof (PMK.kl_img segs L KL) as KI.
  apply (L5C.hpres_cdef L LBc sp' scr' W' M M' i HP); [lia| right; left; unfold hl_ceil; split; [lia| lia]| unfold in_errno; lia| exact D].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma iss_unread_defined M ois str sm :
  PM.iss_at segs A T3 M ois str sm -> L5.defined M (PM.sm_g sm) (PM.sm_eg sm - PM.sm_g sm).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _ & _ & _ & E1 & E2).
  destruct VS as (D & _ & H). destruct str as [n|c n p]; cbn [PM.vs_data PM.vs_size] in *.
  - destruct H as (Hn & _). apply (L5.defined_sub M (ois + 80) 24); [exact D| lia| lia].
  - destruct H as (_ & _ & _ & Hn & _ & _ & DB & _). apply (L5.defined_sub M p c); [exact DB| lia| lia].
Qed.
(* [comment removed for export] *)
Lemma iss_unread_where M ois str sm :
  PM.iss_at segs A T3 M ois str sm ->
  (ois + 81 <= PM.sm_g sm /\ PM.sm_eg sm <= ois + 104)
  \/ (exists c n p, str = PM.VLong c n p /\ p <= PM.sm_g sm /\ PM.sm_eg sm <= p + c).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _ & _ & _ & E1 & E2).
  destruct VS as (D & _ & H). destruct str as [n|c n p]; cbn [PM.vs_data PM.vs_size] in *.
  - destruct H as (Hn & _). left. lia.
  - destruct H as (_ & _ & _ & Hn & _). right. exists c, n, p. split; [reflexivity| lia].
Qed.
Lemma iss_size_lt M ois str sm : PM.iss_at segs A T3 M ois str sm -> 0 <= PM.sm_eg sm - PM.sm_g sm < 2 ^ 27.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _ & _ & _ & E1 & E2).
  destruct VS as (D & _ & H). destruct str as [n|c n p]; cbn [PM.vs_data PM.vs_size] in *.
  - destruct H as (Hn & _). lia.
  - destruct H as (_ & _ & _ & Hn & Hc & _). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Upd.
Variables M M' : word -> option byte.
Abbreviation ag := (L5C.agree_on M M').
Local Ltac u64x AG H := apply (L5C.u64_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact H].
Local Ltac u32x AG H := apply (PMF.u32_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact H].
Local Ltac u8x AG H := apply (L5C.u8_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact H].

(* [comment removed for export] *)
Lemma vstr_at_keep o s : 0 <= o -> o + 24 <= 2 ^ 64 -> ag o 24 -> (forall c n p, s = PM.VLong c n p -> dkr M M' p c) ->
  PM.vstr_at segs T3 M o s -> PM.vstr_at segs T3 M' o s.
Proof.
  intros Ho Ho' AG DKB (D & _ & H). split; [apply (L5C.defined_agree M M' o 24 AG D)|]. split; [exact I|].
  destruct s as [n|c n p].
  - destruct H as (Hn & B0). split; [exact Hn|]. u8x AG B0.
  - destruct H as (W0 & W8 & W16 & Hn & Hc & He & DB & _).
    split; [u64x AG W0|]. split; [u64x AG W8|]. split; [u64x AG W16|]. split; [exact Hn|]. split; [exact Hc|]. split; [exact He|].
    split; [apply (defined_dkr M M' p c (DKB c n p eq_refl) DB)| exact I].
Qed.

(* [comment removed for export] *)
Lemma iss_upd ois str sm g' st' :
  PM.iss_at segs A T3 M ois str sm -> 0 <= ois -> ois + 272 <= 2 ^ 64 ->
  ag ois 40 -> ag (ois + 48) 104 -> ag (ois + 156) 116 -> dkr M M' (ois + 40) 8 -> dkr M M' (ois + 152) 4 ->
  (forall c n p, str = PM.VLong c n p -> dkr M M' p c) ->
  L5.u64_at segs M' (ois + 40) g' -> L5.u32_at segs M' (ois + 152) st' ->
  PM.vs_data (ois + 80) str <= g' <= PM.sm_eg sm -> (st' = 0 \/ st' = 2) ->
  PM.iss_at segs A T3 M' ois str (PM.STRM g' (PM.sm_eg sm) st').
Proof.
  intros (H0 & D & _ & H16 & H24 & H32 & H40 & H48 & H64 & VS & H104 & H112 & IOS & E1 & E2) Ho Ho' AG1 AG2 AG3 DK1 DK2 AGB G' ST' GR STR.
  destruct IOS as (J0 & J32 & J36 & J40 & J48 & Z & JD & _ & _).
  cbn [PM.sm_g PM.sm_eg PM.sm_st].
  split; [u64x AG1 H0|].
  split. { intros i Hi. destruct (Z_lt_le_dec i 40) as [X|X]; [rewrite AG1 by lia; apply D; lia|].
           destruct (Z_lt_le_dec i 48) as [Y|Y]; [apply DK1; [lia| apply D; lia]| rewrite AG2 by lia; apply D; lia]. }
  split; [exact I|]. split; [u64x AG1 H16|]. split; [u64x AG1 H24|]. split; [u64x AG1 H32|].
  split; [exact G'|]. split; [u64x AG2 H48|]. split; [u64x AG2 H64|].
  split. { apply vstr_at_keep; [lia| lia| eapply L5C.agree_on_sub; [exact AG2|lia|lia]| exact AGB| exact VS]. }
  split; [u64x AG2 H104|]. split; [u32x AG2 H112|].
  split.
  { split; [u64x AG2 J0|]. split; [replace (ois + 120 + 32) with (ois + 152) by lia; exact ST'|]. split; [u32x AG3 J36|]. split; [u64x AG3 J40|].
    split; [u64x AG3 J48|].
    split. { apply (PMF.zeros_at_agree M M'); [eapply L5C.agree_on_sub; [exact AG3|lia|lia]| exact Z]. }
    split. { intros i Hi. destruct (Z_lt_le_dec i 32) as [X|X]; [rewrite AG2 by lia; apply JD; lia|].
             destruct (Z_lt_le_dec i 36) as [Y|Y]; [apply DK2; [lia| apply JD; lia]| rewrite AG3 by lia; apply JD; lia]. }
    split; [exact I| exact STR]. }
  split; [exact E1| exact GR].
Qed.

(* [comment removed for export] *)
Lemma parser_src_upd op ois s de' rem' :
  PM.parser_at segs A T3 T4 M op ois s -> 0 <= op -> op + 384 <= 2 ^ 64 ->
  ag op 280 -> ag (op + 320) 64 -> dkr M M' (op + 280) 40 ->
  dkr M M' (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  0 <= PM.p_b s -> PM.p_b s + 32 * 2 ^ PM.p_k s <= 2 ^ 64 -> ag (PM.p_b s) (32 * 2 ^ PM.p_k s) ->
  (forall c n p, PM.p_tb s = PM.VLong c n p -> dkr M M' p c) ->
  L5.u64_at segs M' (op + 288) (PM.sr_qc (PM.p_src s)) -> L5.u64_at segs M' (op + 296) PM.CHUNK ->
  L5.u64_at segs M' (op + 304) de' -> L5.u64_at segs M' (op + 312) rem' ->
  PM.sr_qc (PM.p_src s) <= de' -> 0 <= rem' -> de' + rem' <= PM.sr_qc (PM.p_src s) + PM.CHUNK ->
  PM.parser_at segs A T3 T4 M' op ois (PMPS.with_src s (PM.SRC (PM.sr_qc (PM.p_src s)) de' rem')).
Proof.
  intros (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3) Ho Ho' AG1 AG2 DK DKC Hb Hb' AGV AGT C1 C2 C3 C4 Q1 Q2 Q3.
  destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _).
  unfold PMPS.with_src. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.sr_qc PM.sr_de PM.sr_rem].
  split; [u64x AG1 H0|].
  split. { intros i Hi. destruct (Z_lt_le_dec i 280) as [X|X]; [rewrite AG1 by lia; apply D; lia|].
           destruct (Z_lt_le_dec i 320) as [Y|Y]; [apply DK; [lia| apply D; lia]| rewrite AG2 by lia; apply D; lia]. }
  split; [exact I|]. split; [u8x AG1 H8|]. split; [u8x AG1 H9|]. split; [u32x AG1 H12|]. split; [u8x AG1 H16|]. split; [u32x AG1 H20|].
  split. { apply (PMF.nullis_at_agree segs A M M'); [lia| lia| eapply L5C.agree_on_sub; [exact AG1|lia|lia]| exact NI]. }
  split.
  { split; [u64x AG1 F1|]. split; [u64x AG1 F2|].
    split. { apply (defined_dkr M M'); [eapply dkr_sub; [exact DK|lia|lia]| exact F3]. }
    split; [replace (op + 24 + 264) with (op + 288) by lia; exact C1|]. split; [replace (op + 24 + 272) with (op + 296) by lia; exact C2|].
    split; [replace (op + 24 + 280) with (op + 304) by lia; exact C3|]. split; [replace (op + 24 + 288) with (op + 312) by lia; exact C4|].
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact G4|].
    split; [apply (defined_dkr M M' _ _ DKC DC)|]. split; exact I. }
  split; [u32x AG2 H320|]. split; [u64x AG2 H328|]. split; [exact I|].
  split. { apply vstr_at_keep; [lia| lia| eapply L5C.agree_on_sub; [exact AG2|lia|lia]| exact AGT| exact TB]. }
  split. { apply (PMF.vec_at_agree segs M M'); [lia| lia| exact Hb| exact Hb'| eapply L5C.agree_on_sub; [exact AG2|lia|lia]| exact AGV| exact VEC]. }
  split; [exact B1|]. split; [exact B2| exact B3].
Qed.
(* [comment removed for export] *)
Lemma vstr_short_keep o n : 0 <= o -> o + 24 <= 2 ^ 64 -> ag o 1 -> dkr M M' (o + 1) 23 ->
  PM.vstr_at segs T3 M o (PM.VShort n) -> PM.vstr_at segs T3 M' o (PM.VShort n).
Proof.
  intros Ho Ho' AG DK (D & _ & Hn & B0). split.
  { intros i Hi. destruct (Z_lt_le_dec i 1) as [X|X]; [rewrite AG by lia; apply D; lia| apply DK; [lia| apply D; lia]]. }
  split; [exact I|]. split; [exact Hn|]. u8x AG B0.
Qed.
(* [comment removed for export] *)
Lemma parser_src_tb_upd op ois s de' rem' :
  PM.parser_at segs A T3 T4 M op ois s -> 0 <= op -> op + 384 <= 2 ^ 64 ->
  ag op 280 -> ag (op + 320) 16 -> ag (op + 360) 24 -> dkr M M' (op + 280) 40 -> dkr M M' (op + 336) 24 ->
  PM.vstr_at segs T3 M' (op + 336) (PM.p_tb s) ->
  dkr M M' (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  0 <= PM.p_b s -> PM.p_b s + 32 * 2 ^ PM.p_k s <= 2 ^ 64 -> ag (PM.p_b s) (32 * 2 ^ PM.p_k s) ->
  L5.u64_at segs M' (op + 288) (PM.sr_qc (PM.p_src s)) -> L5.u64_at segs M' (op + 296) PM.CHUNK ->
  L5.u64_at segs M' (op + 304) de' -> L5.u64_at segs M' (op + 312) rem' ->
  PM.sr_qc (PM.p_src s) <= de' -> 0 <= rem' -> de' + rem' <= PM.sr_qc (PM.p_src s) + PM.CHUNK ->
  PM.parser_at segs A T3 T4 M' op ois (PMPS.with_src s (PM.SRC (PM.sr_qc (PM.p_src s)) de' rem')).
Proof.
  intros (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3) Ho Ho' AG1 AG2 AG3 DK DKT TB' DKC Hb Hb' AGV C1 C2 C3 C4 Q1 Q2 Q3.
  destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _).
  unfold PMPS.with_src. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk PM.sr_qc PM.sr_de PM.sr_rem].
  split; [u64x AG1 H0|].
  split. { intros i Hi. destruct (Z_lt_le_dec i 280) as [X|X]; [rewrite AG1 by lia; apply D; lia|].
           destruct (Z_lt_le_dec i 320) as [Y|Y]; [apply DK; [lia| apply D; lia]|].
           destruct (Z_lt_le_dec i 336) as [Y2|Y2]; [rewrite AG2 by lia; apply D; lia|].
           destruct (Z_lt_le_dec i 360) as [Y3|Y3]; [apply DKT; [lia| apply D; lia]| rewrite AG3 by lia; apply D; lia]. }
  split; [exact I|]. split; [u8x AG1 H8|]. split; [u8x AG1 H9|]. split; [u32x AG1 H12|]. split; [u8x AG1 H16|]. split; [u32x AG1 H20|].
  split. { apply (PMF.nullis_at_agree segs A M M'); [lia| lia| eapply L5C.agree_on_sub; [exact AG1|lia|lia]| exact NI]. }
  split.
  { split; [u64x AG1 F1|]. split; [u64x AG1 F2|].
    split. { apply (defined_dkr M M'); [eapply dkr_sub; [exact DK|lia|lia]| exact F3]. }
    split; [replace (op + 24 + 264) with (op + 288) by lia; exact C1|]. split; [replace (op + 24 + 272) with (op + 296) by lia; exact C2|].
    split; [replace (op + 24 + 280) with (op + 304) by lia; exact C3|]. split; [replace (op + 24 + 288) with (op + 312) by lia; exact C4|].
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact G4|].
    split; [apply (defined_dkr M M' _ _ DKC DC)|]. split; exact I. }
  split; [u32x AG2 H320|]. split; [u64x AG2 H328|]. split; [exact I|].
  split; [exact TB'|].
  split. { apply (PMF.vec_at_agree segs M M'); [lia| lia| exact Hb| exact Hb'| exact AG3| exact AGV| exact VEC]. }
  split; [exact B1|]. split; [exact B2| exact B3].
Qed.
(* [comment removed for export] *)
Lemma parser_at_keep op ois s :
  PM.parser_at segs A T3 T4 M op ois s -> 0 <= op -> op + 384 <= 2 ^ 64 -> ag op 384 ->
  dkr M M' (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  0 <= PM.p_b s -> PM.p_b s + 32 * 2 ^ PM.p_k s <= 2 ^ 64 -> ag (PM.p_b s) (32 * 2 ^ PM.p_k s) ->
  (forall c n p, PM.p_tb s = PM.VLong c n p -> dkr M M' p c) ->
  PM.parser_at segs A T3 T4 M' op ois s.
Proof.
  intros PA Ho Ho' AG DKC Hb Hb' AGV DKT.
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _). destruct SRC as (_ & _ & _ & F4 & F5 & F6 & F7 & G1 & G2 & G3 & _).
  destruct s as [mo dn dp src tb tg vb vk stk]. destruct src as [qc de rem]. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc PM.sr_de PM.sr_rem] in *.
  apply (parser_src_upd op ois (PM.PST mo dn dp (PM.SRC qc de rem) tb tg vb vk stk) de rem PA Ho Ho'); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc]; try assumption.
  - eapply L5C.agree_on_sub; [exact AG|lia|lia].
  - eapply L5C.agree_on_sub; [exact AG|lia|lia].
  - apply dkr_agree. eapply L5C.agree_on_sub; [exact AG|lia|lia].
  - replace (op + 288) with (op + 24 + 264) by lia. u64x AG F4.
  - replace (op + 296) with (op + 24 + 272) by lia. u64x AG F5.
  - replace (op + 304) with (op + 24 + 280) by lia. u64x AG F6.
  - replace (op + 312) with (op + 24 + 288) by lia. u64x AG F7.
Qed.
(* [comment removed for export] *)
Definition set_more (s : PM.pst) (v : Z) : PM.pst :=
  PM.PST v (PM.p_done s) (PM.p_depth s) (PM.p_src s) (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (PM.p_stk s).
Lemma parser_more_upd op ois s v :
  PM.parser_at segs A T3 T4 M op ois s -> 0 <= op -> op + 384 <= 2 ^ 64 ->
  ag op 8 -> ag (op + 9) 375 -> dkr M M' (op + 8) 1 -> L5.u8_at segs M' (op + 8) v -> (v = 0 \/ v = 1) ->
  dkr M M' (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  0 <= PM.p_b s -> PM.p_b s + 32 * 2 ^ PM.p_k s <= 2 ^ 64 -> ag (PM.p_b s) (32 * 2 ^ PM.p_k s) ->
  (forall c n p, PM.p_tb s = PM.VLong c n p -> dkr M M' p c) ->
  PM.parser_at segs A T3 T4 M' op ois (set_more s v).
Proof.
  intros (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3) Ho Ho' AG1 AG2 DK V8 Hv DKC Hb Hb' AGV AGT.
  destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _).
  unfold set_more. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
  assert (AG3 : forall a n, op + 9 <= a -> a + n <= op + 384 -> ag a n) by (intros a n X1 X2; eapply L5C.agree_on_sub; [exact AG2|lia|lia]).
  split; [u64x AG1 H0|].
  split. { intros i Hi. destruct (Z_lt_le_dec i 8) as [X|X]; [rewrite AG1 by lia; apply D; lia|].
           destruct (Z_lt_le_dec i 9) as [Y|Y]; [apply DK; [lia| apply D; lia]| rewrite AG2 by lia; apply D; lia]. }
  split; [exact I|]. split; [exact V8|]. split; [apply (L5C.u8_at_agree segs M M'); [apply AG3; lia|lia|lia|exact H9]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply AG3; lia|lia|lia|exact H12]|].
  split; [apply (L5C.u8_at_agree segs M M'); [apply AG3; lia|lia|lia|exact H16]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply AG3; lia|lia|lia|exact H20]|].
  split. { apply (PMF.nullis_at_agree segs A M M'); [lia| lia| apply AG3; lia| exact NI]. }
  split.
  { split; [u64x AG2 F1|]. split; [u64x AG2 F2|].
    split. { apply (L5C.defined_agree M M'); [apply AG3; lia| exact F3]. }
    split; [u64x AG2 F4|]. split; [u64x AG2 F5|]. split; [u64x AG2 F6|]. split; [u64x AG2 F7|].
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [apply (defined_dkr M M' _ _ DKC DC)|]. split; exact I. }
  split; [apply (PMF.u32_at_agree segs M M'); [apply AG3; lia|lia|lia|exact H320]|]. split; [u64x AG2 H328|]. split; [exact I|].
  split. { apply vstr_at_keep; [lia| lia| apply AG3; lia| exact AGT| exact TB]. }
  split. { apply (PMF.vec_at_agree segs M M'); [lia| lia| exact Hb| exact Hb'| apply AG3; lia| exact AGV| exact VEC]. }
  split; [exact Hv|]. split; [exact B2| exact B3].
Qed.
(* [comment removed for export] *)
Lemma removelast_len (l : list PM.pstate) : (1 <= length l)%nat -> length (removelast l) = (length l - 1)%nat.
Proof.
  intros H. destruct l as [|x l]; [cbn in H; lia|]. rewrite (app_removelast_last x (l := x :: l)) at 2 by discriminate.
  rewrite length_app. cbn. lia.
Qed.
Lemma nth_removelast_lt (l : list PM.pstate) i d : (i < length (removelast l))%nat -> nth i (removelast l) d = nth i l d.
Proof.
  intros H. destruct l as [|x l]; [cbn in H; lia|]. rewrite (app_removelast_last x (l := x :: l)) at 2 by discriminate.
  rewrite app_nth1 by exact H. reflexivity.
Qed.
Lemma vec_at_pop v b k stk :
  PM.vec_at segs T3 T4 M v b k stk -> (1 <= length stk)%nat -> 0 <= v -> v + 24 <= 2 ^ 64 -> 0 <= b -> b + 32 * 2 ^ k <= 2 ^ 64 ->
  ag v 8 -> ag (v + 16) 8 -> ag b (32 * 2 ^ k) ->
  L5.u64_at segs M' (v + 8) (b + 32 * Z.of_nat (length stk) - 32) ->
  PM.vec_at segs T3 T4 M' v b k (removelast stk).
Proof.
  intros (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL) H1 Hv Hv' Hb Hb' AG0 AG16 AGB C8.
  pose proof (PM.pow2_pos k ltac:(lia)) as P2. pose proof (removelast_len stk H1) as RL.
  split; [u64x AG0 V0|].
  split; [rewrite RL; rewrite Nat2Z.inj_sub by lia; replace (b + 32 * (Z.of_nat (length stk) - Z.of_nat 1)) with (b + 32 * Z.of_nat (length stk) - 32) by lia; exact C8|].
  split; [u64x AG16 V16|].
  split; [exact Hk|]. split; [rewrite RL; lia|]. split; [exact Hal|].
  split; [apply (L5C.defined_agree M M' b _ AGB DB)|]. split; [exact I|]. split; [exact I|].
  intros n Hn. rewrite (nth_removelast_lt stk n PM.ps_root Hn). rewrite RL in Hn.
  apply (PMF.pstate_at_agree segs M M'); [lia|lia| |apply EL; lia].
  apply (L5C.agree_on_sub M M' b (32 * 2 ^ k)); [exact AGB|lia|lia].
Qed.
Lemma parser_pop_upd op ois s :
  PM.parser_at segs A T3 T4 M op ois s -> 0 <= op -> op + 384 <= 2 ^ 64 -> (1 <= length (PM.p_stk s))%nat ->
  ag op 8 -> ag (op + 9) 3 -> ag (op + 16) 352 -> ag (op + 376) 8 -> dkr M M' (op + 8) 1 -> dkr M M' (op + 12) 4 -> dkr M M' (op + 368) 8 ->
  L5.u8_at segs M' (op + 8) 1 -> L5.u32_at segs M' (op + 12) (PM.p_depth s - 1) -> 0 <= PM.p_depth s - 1 ->
  L5.u64_at segs M' (op + 368) (PM.p_b s + 32 * Z.of_nat (length (PM.p_stk s)) - 32) ->
  dkr M M' (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  0 <= PM.p_b s -> PM.p_b s + 32 * 2 ^ PM.p_k s <= 2 ^ 64 -> ag (PM.p_b s) (32 * 2 ^ PM.p_k s) ->
  (forall c n p, PM.p_tb s = PM.VLong c n p -> dkr M M' p c) ->
  PM.parser_at segs A T3 T4 M' op ois
    (PM.PST 1 (PM.p_done s) (PM.p_depth s - 1) (PM.p_src s) (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (removelast (PM.p_stk s))).
Proof.
  intros (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3) Ho Ho' HL AG1 AG9 AG2 AG3 DK8 DK12 DK368 C8 C12 Hd C368 DKC Hb Hb' AGV AGT.
  destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _).
  cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
  assert (AG4 : forall a n, op + 16 <= a -> a + n <= op + 368 -> ag a n) by (intros a n X1 X2; eapply L5C.agree_on_sub; [exact AG2|lia|lia]).
  split; [u64x AG1 H0|].
  split. { intros i Hi. destruct (Z_lt_le_dec i 8) as [X|X]; [rewrite AG1 by lia; apply D; lia|].
           destruct (Z_lt_le_dec i 9) as [Y|Y]; [apply DK8; [lia| apply D; lia]|].
           destruct (Z_lt_le_dec i 12) as [Y1|Y1]; [rewrite AG9 by lia; apply D; lia|].
           destruct (Z_lt_le_dec i 16) as [Y0|Y0]; [apply DK12; [lia| apply D; lia]|].
           destruct (Z_lt_le_dec i 368) as [Y2|Y2]; [rewrite AG2 by lia; apply D; lia|].
           destruct (Z_lt_le_dec i 376) as [Y3|Y3]; [apply DK368; [lia| apply D; lia]| rewrite AG3 by lia; apply D; lia]. }
  split; [exact I|]. split; [exact C8|].
  split; [apply (L5C.u8_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG9|lia|lia]|lia|lia|exact H9]|].
  split; [exact C12|].
  split; [apply (L5C.u8_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H16]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H20]|].
  split. { apply (PMF.nullis_at_agree segs A M M'); [lia| lia| apply AG4; lia| exact NI]. }
  split.
  { split; [u64x AG2 F1|]. split; [u64x AG2 F2|].
    split. { apply (L5C.defined_agree M M'); [apply AG4; lia| exact F3]. }
    split; [u64x AG2 F4|]. split; [u64x AG2 F5|]. split; [u64x AG2 F6|]. split; [u64x AG2 F7|].
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [apply (defined_dkr M M' _ _ DKC DC)|]. split; exact I. }
  split; [apply (PMF.u32_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H320]|]. split; [u64x AG2 H328|]. split; [exact I|].
  split. { apply vstr_at_keep; [lia| lia| apply AG4; lia| exact AGT| exact TB]. }
  split. { apply (vec_at_pop (op + 360) (PM.p_b s) (PM.p_k s) (PM.p_stk s) VEC HL); [lia|lia|exact Hb|exact Hb'| apply AG4; lia| eapply L5C.agree_on_sub; [exact AG3|lia|lia] | exact AGV|].
           replace (op + 360 + 8) with (op + 368) by lia. exact C368. }
  split; [right; reflexivity|]. split; [exact B2| cbn [PM.p_depth]; unfold PM.MAX_DEPTH in *; lia].
Qed.
End Upd.

End Kit.

(* [comment removed for export] *)
Lemma pot_text_le_parser L s cr : 0 <= hl_k_per_malloc L -> 0 <= hl_b_overhead L -> 0 <= PM.p_k s <= 11 ->
  PMSP.credit_le (PM.pot_parser L s) cr -> PMSP.credit_le (PM.pot_text L (PM.p_tb s) (PM.p_tg s)) cr.
Proof.
  intros HK HB Hk. unfold PMSP.credit_le, PM.pot_parser, PM.credit_add, PM.pot_stack. cbn [fst snd].
  assert (P : 2 ^ (PM.p_k s + 1) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
  assert (Q : 0 <= hl_k_per_malloc L * (11 - PM.p_k s)) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Q2 : 0 <= (11 - PM.p_k s) * hl_b_overhead L) by (apply Z.mul_nonneg_nonneg; lia).
  intros (C1 & C2). split; lia.
Qed.
Lemma credit_keep_text L cr cr1 cr2 s s1 s2 :
  PMSP.credit_keep cr cr1 (PM.pot_parser L s) (PM.pot_parser L s1) ->
  PMSP.credit_keep cr1 cr2 (PM.pot_text L (PM.p_tb s1) (PM.p_tg s1)) (PM.pot_text L (PM.p_tb s2) (PM.p_tg s2)) -> PM.p_k s2 = PM.p_k s1 ->
  PMSP.credit_keep cr cr2 (PM.pot_parser L s) (PM.pot_parser L s2).
Proof.
  unfold PMSP.credit_keep, PM.pot_parser, PM.credit_add. cbn [fst snd]. intros (A1 & A2) (B1 & B2) E. rewrite E. lia.
Qed.
Lemma credit_le_keep cr cr1 p p1 : PMSP.credit_le p cr -> PMSP.credit_keep cr cr1 p p1 -> PMSP.credit_le p1 cr1.
Proof. unfold PMSP.credit_le, PMSP.credit_keep. intros (A1 & A2) (B1 & B2). split; lia. Qed.

(* [comment removed for export] *)
Lemma src_step_trans src1 src2 src3 sm1 sm2 sm3 :
  PMSP.src_step src1 src2 sm1 sm2 -> PMSP.src_step src2 src3 sm2 sm3 -> PMSP.src_step src1 src3 sm1 sm3.
Proof.
  unfold PMSP.src_step. intros (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5).
  split; [congruence|]. split; [congruence|]. split; [lia|]. split; [intros X; apply B4; apply A4; exact X| lia].
Qed.
(* [comment removed for export] *)
Lemma stack_shape_pop (stk : list PM.pstate) : PM.stack_shape stk -> (2 <= length stk)%nat -> PM.stack_shape (removelast stk).
Proof.
  intros (H1 & H2 & H3 & H4 & H5) HL. pose proof (removelast_len stk ltac:(lia)) as RL.
  split; [rewrite RL; lia|]. split; [rewrite RL; lia|].
  split; [rewrite (nth_removelast_lt stk 0 PM.ps_root) by (rewrite RL; lia); exact H3|].
  split.
  - intros i Hi. rewrite RL in Hi. rewrite (nth_removelast_lt stk i PM.ps_root) by (rewrite RL; lia). apply H4. lia.
  - intros i Hi. rewrite RL in Hi. rewrite (nth_removelast_lt stk i PM.ps_root) by (rewrite RL; lia). apply H5. lia.
Qed.
End PMPK.
