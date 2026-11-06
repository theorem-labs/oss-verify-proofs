(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bj X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0qm X0pc X0p9 X0pj X0qn X0px X0qc X0q2 X0q3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qh X0qi X0qk X0qj X0q4 X0pk X0p0 X0p1 X0p2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0p3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Definition DROPPED (st st' : mstate) (a : Z) : Prop :=
exists rid r, (s_regions st) !! rid = Some r /\ (s_regions st') !! rid = None /\ r_kind r = RKGroup
/\ r_base r <= a < r_base r + round_up_pg (r_len r).

Definition lbrm (LB : list block) (blk : block) : list block :=
filter (fun b' => negb (aptr_eqb (blk_slot b') (blk_slot blk))) LB.

Definition free_end {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (LB' : list block) (m : mem) (errv : word) (s : PState)
(st' : mstate) (s' : PState) : machine_state -> Prop :=
fun ms' => s' = s /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (errno_addr tp) [C4 errv]
/\ mrep st' m'
/\ pres_except (fun a => free_fp st lo (bv_unsigned sp) a \/ DROPPED st st' a \/ 107900 <= a < 107904) m m'
/\ (forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r')
/\ (forall blk', In blk' LB' -> exists r', (s_regions st') !! (fst (blk_slot blk')) = Some r')
/\ c_brk (ctx st') = c_brk (ctx st)
/\ (forall brid boff, c_brk (ctx st) = BrkLive brid boff -> (s_regions st') !! brid = (s_regions st) !! brid).

Lemma oracle_ok_refl m st : oracle_ok m m st.
Proof. intros rid r q h _ _ _ _ _. reflexivity. Qed.

Lemma oracle_ok_hdr_st o m st pf : ticks_ok st -> oracle_ok o m st -> oracle_ok o m (hdr_st st pf).
Proof.
intros TK OK rid r q h Hr Hk Hq M8 Hc. change (s_regions (hdr_st st pf)) with (s_regions st) in Hr.
rewrite hdr_st_cell_read in Hc by exact TK.
destruct (N.eqb rid (fst pf) && ((q =? snd pf - 1) || (q =? snd pf - 2) || (q =? snd pf - 3)))%bool; [discriminate|].
exact (OK rid r q h Hr Hk Hq M8 Hc).
Qed.

Lemma errno_not_free_fp {RCEIL : RunCeiling} st m lo (sp : Z) a : mrep st m -> alloc_ceiling <= lo -> 107900 <= a < 107904 -> ~ free_fp st lo sp a.
Proof.
intros MR LO Ha. pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as Hres WR DJ WA WG | sf_fb; destruct sfP_ as (Hres & WR & DJ & WA & WG) ]. unfold alloc_ceiling in LO.
intros [[A|[A|A]]|[A|A]].
- lia.
- unfold CTX in A. lia.
- first [ sf_destruct 5%nat A as rid r Hr _ Hin | sf_fb; destruct A as (rid & r & Hr & _ & Hin) ]. first [ pose proof (WR _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF) ]. destruct (reserved_disjoint _ _ RF). pose proof (lr_lo_ge r). lia.
- first [ sf_destruct 4%nat A as b gh Hb Hin | sf_fb; destruct A as (b & gh & Hb & Hin) ]. first [ pose proof (group_conc st b gh WF Hb) as sfP_; sf_destruct 7%nat sfP_ as rb Hrb Cb _ Sb0 Sb1 _ | sf_fb; destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _) ].
first [ pose proof (WR _ _ Hrb) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF) ]. destruct (reserved_disjoint _ _ RF). lia.
- first [ sf_destruct 7%nat A as rid r v Hr _ Hin _ | sf_fb; destruct A as (rid & r & v & Hr & _ & Hin & _) ]. first [ pose proof (WR _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF) ]. destruct (reserved_disjoint _ _ RF). lia.
Qed.

Lemma munmap_ok_range_val a : match a with RgErr e => 1 <= e <= 4095 | _ => True end -> munmap_answer_ok (range_val a) = true.
Proof.
destruct a as [e|c]; cbn [range_val]; intros He; unfold munmap_answer_ok, is_errno_form, neg_errno, TWO64.
- apply orb_true_intro. right. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
- reflexivity.
Qed.

Lemma round_up_pg_mod x : round_up_pg x mod 4096 = 0.
Proof. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. Z.div_mod_to_equations. lia. Qed.

Lemma mmap_len_round x : mmap_len (round_up_pg x) = round_up_pg x.
Proof.
pose proof (round_up_pg_mod x) as M. unfold mmap_len, page_round_up_Z, page_size.
set (y := round_up_pg x) in *. Z.div_mod_to_equations. nia.
Qed.

Lemma mrep_after_munmap {RCEIL : RunCeiling} st2 rid r2 m4 m5 (slo shi : Z) :
mrep (drop_region rid st2) m4 -> mrep st2 m4 ->
(s_regions st2) !! rid = Some r2 -> r_kind r2 = RKGroup ->
munch [(slo, shi); (107900, 107904); (r_base r2, r_base r2 + round_up_pg (r_len r2))]%Z m4 m5 ->
alloc_ceiling <= slo ->
mrep (drop_region rid st2) m5.
Proof.
intros MRd MR Hr Kr MU LO. pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as Hres WR DJ WA WG | sf_fb; destruct sfP_ as (Hres & WR & DJ & WA & WG) ]. unfold alloc_ceiling in LO.
pose proof (WR _ _ Hr) as sfP_; first [ sf_destruct 5%nat sfP_ as RB0 RBAL RL0 RBC RF | sf_fb; destruct sfP_ as (RB0 & RBAL & RL0 & RBC & RF) ]. destruct (reserved_disjoint _ _ RF) as [D1 D2]. unfold alloc_ceiling in RBC.
eapply mrep_transport_agree'; [exact MRd|]. intros a Ha HF. apply MU. rewrite wa_unsigned by lia.
assert (LOW : a < alloc_ceiling /\ ~ (107900 <= a < 107904) /\ ~ (r_base r2 <= a < r_base r2 + round_up_pg (r_len r2))).
{ destruct HF as [HF|HF].
- split; [| split].
+ destruct HF as [C|[C|[C|[C|[C|[C|C]]]]]].
* unfold CTX in C; lia. * unfold MLOCK in C; lia. * unfold NEED_LOCKS in C; lia. * unfold X0qm.PAGE_SIZE_A in C; lia.
* first [ sf_destruct 4%nat C as ak ar Hak Hin | sf_fb; destruct C as (ak & ar & Hak & Hin) ]. first [ pose proof (area_conc (drop_region rid st2) ak ar (proj1 MRd) Hak) as sfP_; sf_destruct 10%nat sfP_ as ra Hra Ca Sa0 Sa1 _ _ _ _ RC | sf_fb; destruct (area_conc (drop_region rid st2) ak ar (proj1 MRd) Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & _ & _ & _ & RC) ]. unfold alloc_ceiling in RC. lia.
* first [ sf_destruct 4%nat C as b gh Hb Hin | sf_fb; destruct C as (b & gh & Hb & Hin) ]. first [ pose proof (group_conc (drop_region rid st2) b gh (proj1 MRd) Hb) as sfP_; sf_destruct 9%nat sfP_ as rb Hrb Cb _ _ Sb1 _ _ RC | sf_fb; destruct (group_conc (drop_region rid st2) b gh (proj1 MRd) Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC) ]. unfold alloc_ceiling in RC. lia.
* first [ sf_destruct 7%nat C as k rk v Hk _ Hin _ | sf_fb; destruct C as (k & rk & v & Hk & _ & Hin & _) ]. cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [_ Hk].
first [ pose proof (WR _ _ Hk) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RC _ | sf_fb; destruct (WR _ _ Hk) as (_ & _ & _ & RC & _) ]. unfold alloc_ceiling in RC. lia.
+ intros Hea. exact (errno_avoids_repfoot _ _ a MRd Hea HF).
+ intros Hin. destruct HF as [C|[C|[C|[C|[C|[C|C]]]]]].
* unfold CTX in C; lia. * unfold MLOCK in C; lia. * unfold NEED_LOCKS in C; lia. * unfold X0qm.PAGE_SIZE_A in C; lia.
* first [ sf_destruct 4%nat C as ak ar Hak Ha' | sf_fb; destruct C as (ak & ar & Hak & Ha') ]. cbn [drop_region s_areas set_shadow set_regions] in Hak.
first [ pose proof (WA ak ar Hak) as sfP_; sf_destruct 7%nat sfP_ as ra Hra Sa0 Sa1 _ NK ALR | sf_fb; destruct (WA ak ar Hak) as (ra & Hra & Sa0 & Sa1 & _ & NK & ALR) ].
assert (NE : fst ak <> rid) by (intros E; rewrite E, Hr in Hra; assert (ra = r2) by congruence; subst; exact (NK Kr)).
rewrite (conc_drop st2 rid ak NE) in Ha'. rewrite (conc_region' st2 ak ra Hra) in Ha'.
pose proof (lr_lo_group r2 Kr). destruct (DJ _ _ _ _ Hra Hr NE); lia.
* first [ sf_destruct 4%nat C as b gh Hb Ha' | sf_fb; destruct C as (b & gh & Hb & Ha') ]. cbn [drop_region s_groups set_shadow set_regions] in Hb.
first [ pose proof (WG b gh Hb) as sfP_; sf_destruct 6%nat sfP_ as rb Hrb Krb Sb0 Sb1 _ | sf_fb; destruct (WG b gh Hb) as (rb & Hrb & Krb & Sb0 & Sb1 & _) ].
assert (NE : fst b <> rid).
{ intros E. pose proof (proj1 MRd) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ _ WG' | sf_fb; destruct sfP_ as (_ & _ & _ & _ & WG') ]. destruct (WG' b gh Hb) as (rb' & Hrb' & _).
cbn [drop_region s_regions set_shadow set_regions] in Hrb'. rewrite E, lookup_delete_eq in Hrb'. discriminate. }
rewrite (conc_drop st2 rid b NE) in Ha'. rewrite (conc_region' st2 b rb Hrb) in Ha'.
pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
* first [ sf_destruct 7%nat C as k rk v Hk Kk Ha' _ | sf_fb; destruct C as (k & rk & v & Hk & Kk & Ha' & _) ]. cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia.
- first [ sf_destruct 5%nat HF as k rk Hk Kk Ha' | sf_fb; destruct HF as (k & rk & Hk & Kk & Ha') ]. cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
first [ pose proof (WR _ _ Hk) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RC RFk | sf_fb; destruct (WR _ _ Hk) as (_ & _ & _ & RC & RFk) ]. destruct (reserved_disjoint _ _ RFk). unfold alloc_ceiling in RC.
split; [lia|]. split; [lia|].
pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia. }
destruct LOW as (L1 & L2 & L3). cbn [outside]. split; [lia|]. split; [exact L2|]. split; [exact L3| exact I].
Qed.

Ltac cover_intervals tac :=
let lo0 := fresh "ilo" in let hi0 := fresh "ihi" in let HW := fresh "HinW" in let y := fresh "y" in let Hy := fresh "Hy" in
intros lo0 hi0 HW y Hy; cbn [In] in HW;
repeat (destruct HW as [HW|HW]); try contradiction;
injection HW; intros; subst lo0 hi0; tac y Hy.

Section FREE.
Context {RCEIL : RunCeiling}.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis GP : gp = Z_to_bv 64 0x1a800.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.

End FREE.

Lemma NoDup_map_inj_in {A B} (f : A -> B) (l : list A) :
List.NoDup (map f l) -> forall x y, In x l -> In y l -> f x = f y -> x = y.
Proof.
induction l as [|a l IH]; intros ND x y Hx Hy E; [destruct Hx|].
cbn [map] in ND. inversion ND; subst.
destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; assumption].
- exfalso. apply H1. rewrite E. apply in_map. exact Hy.
- exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

Lemma filter_ext_in {A} (P1 P2 : A -> Prop) `{forall x, Decision (P1 x)} `{forall x, Decision (P2 x)} (l : list A) :
(forall x, In x l -> (P1 x <-> P2 x)) -> filter P1 l = filter P2 l.
Proof.
induction l as [|a l IH]; intros HE; [reflexivity|]. rewrite !filter_cons.
rewrite IH by (intros x Hx; apply HE; right; exact Hx).
destruct (decide (P1 a)) as [Y|N]; destruct (decide (P2 a)) as [Y'|N']; try reflexivity; exfalso;
pose proof (HE a (or_introl eq_refl)); tauto.
Qed.
