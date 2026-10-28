(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmFrame PgV8 PnModel PnStatics PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u
     PnSResetBP_u Bs0_code_35eb4_35eb8_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSRB.
Import PMS.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)
Local Ltac cdisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

Lemma elem_of_In (x : Z) (l : list Z) : In x l -> x ∈ l.
Proof. induction l as [|a l IH]; intros H; [destruct H|]. destruct H as [<-|H]; [constructor| constructor; apply IH; exact H]. Qed.
Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma v8_data_at segs acc ann M v x : PGV8.v8_at segs acc ann M v x -> L5.u64_at segs M v (PGV8.v8_data x).
Proof. destruct x as [|b n c]; cbn; intros (_ & _ & H); [exact (proj1 H)| exact (proj1 H)]. Qed.

(* [comment removed for export] *)
Lemma brs_post segs A vp M M1 op ois (s : PNM.bpst) (P : Z -> Prop) :
  PNM.bparser_at segs A PMSP.T3 PMSP.T4 vp M op ois s ->
  0 <= op -> op + 416 <= 2 ^ 64 -> 0 <= PM.sr_qc (PNM.b_src s) -> PM.sr_qc (PNM.b_src s) + PM.CHUNK <= 2 ^ 64 ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> mem_grows M M1 ->
  (forall i, (op <= i < op + 8 \/ op + 10 <= i < op + 328 \/ op + 336 <= i < op + 344 \/ op + 392 <= i < op + 400 \/ op + 408 <= i < op + 416
              \/ PM.sr_qc (PNM.b_src s) <= i < PM.sr_qc (PNM.b_src s) + PM.CHUNK) -> ~ P i) ->
  L5.u8_at segs M1 (op + 8) 1 -> L5.u8_at segs M1 (op + 8 + 1) 0 ->
  L5.u64_at segs M1 (op + 328) (PGV8.v8_data (PNM.b_bb s)) ->
  L5.u64_at segs M1 (op + 400) (PNM.b_sb s + 40) ->
  L5.u32_at segs M1 (PNM.b_sb s) 0 -> L5.u64_at segs M1 (PNM.b_sb s + 8) 0 -> L5.u64_at segs M1 (PNM.b_sb s + 16) 0 ->
  L5.u8_at segs M1 (PNM.b_sb s + 24) 0 -> L5.u64_at segs M1 (PNM.b_sb s + 32) 0 ->
  PM.vstr_at segs PMSP.T3 M1 (op + 344) (PNR.vs_clear (PNM.b_nb s)) ->
  PM.vstr_at segs PMSP.T3 M1 (op + 368) (PNR.vs_clear (PNM.b_tb s)) ->
  PNM.bparser_at segs A PMSP.T3 PMSP.T4 vp M1 op ois (PNR.bpst_reset s).
Proof.
  intros (H0 & D & _ & H8 & H9 & H10 & H12 & NI & SRC & H312 & _ & BB & NB & TB & VEC & B1 & B2) Ho Ho' Hq Hq' FRZ MG AV
         C8 C9 C328 C400 E0 E8 E16 E24 E32 NB1 TB1.
  assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ P i) -> L5C.agree_on M M1 a n).
  { intros a n Ha Hn X i Hi. apply FRZ; [lia| apply X; exact Hi]. }
  assert (DG : forall a n, L5.defined M a n -> L5.defined M1 a n) by (intros a n Dn i Hi; apply MG; apply Dn; exact Hi).
  unfold PNM.bparser_at. unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  cbn [PNR.bpst_reset PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk].
  split; [apply (L5C.u64_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact H0]|].
  split; [apply DG; exact D|]. split; [exact I|]. split; [exact C8|]. split; [replace (op + 9) with (op + 8 + 1) by lia; exact C9|].
  split; [apply (L5C.u8_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact H10]|].
  split; [apply (PMF.u32_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact H12]|].
  split; [apply (PMF.nullis_at_agree segs A M M1); [lia|lia| apply AG; [lia|lia| intros i Hi; apply AV; lia]| exact NI]|].
  split; [apply (PMF.src_fields_at_agree segs M M1 (op + 16) ois (ois + 16) (PNM.b_src s)); [lia|lia|exact Hq|exact Hq'| apply AG; [lia|lia| intros i Hi; apply AV; lia]
                                                    | apply AG; [lia|lia| intros i Hi; apply AV; lia]| exact SRC]|].
  split; [apply (PMF.u32_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact H312]|].
  split; [exact I|].
  (* [comment removed for export] *)
  split.
  { destruct BB as (BD & _ & BX). split; [apply DG; exact BD|]. split; [exact I|].
    destruct (PNM.b_bb s) as [|b n c] eqn:EBB; cbn [PGV8.v8_clear PGV8.v8_data] in *.
    - destruct BX as (W0 & W8 & W16).
      split; [apply (L5C.u64_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact W0]|].
      split; [replace (op + 320 + 8) with (op + 328) by lia; exact C328|]. apply (L5C.u64_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact W16].
    - destruct BX as (W0 & W8 & W16 & Hn & Hc & Hb & Hal & DB & _ & _).
      split; [apply (L5C.u64_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact W0]|].
      split; [replace (op + 320 + 8) with (op + 328) by lia; rewrite Z.add_0_r; exact C328|].
      split; [apply (L5C.u64_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact W16]|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [apply DG; exact DB|]. split; exact I. }
  split; [exact NB1|]. split; [exact TB1|].
  split; [| split; [right; reflexivity| left; reflexivity]].
  destruct VEC as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL).
  pose proof (PM.pow2_pos (PNM.b_sk s) ltac:(lia)) as P2k.
  split; [apply (L5C.u64_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact V0]|].
  split; [cbn [length]; unfold PNM.BSZ; replace (PNM.b_sb s + 40 * Z.of_nat 1) with (PNM.b_sb s + 40) by lia; replace (op + 392 + 8) with (op + 400) by lia; exact C400|].
  split; [apply (L5C.u64_at_agree segs M M1); [apply AG; [lia|lia| intros i Hi; apply AV; lia]|lia|lia|exact V16]|].
  split; [exact Hk|]. split; [cbn [length]; lia|]. split; [exact Hal|].
  split; [apply DG; exact DB|]. split; [exact I|]. split; [exact I|].
  intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia]. cbn [nth Z.of_nat].
  unfold PNM.bstate_at, PNM.bs_root. cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx]. unfold PNM.BSZ. rewrite Z.mul_0_r, Z.add_0_r.
  split; [exact E0|]. split; [exact E8|]. split; [exact E16|]. split; [exact E24| exact E32].
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.

Lemma blocks_apart_heap LB cr M VM B1 m1 B2 m2 :
  hi_heap HI LB cr M VM -> In (B1, m1) LB -> In (B2, m2) LB -> B1 <> B2 -> B1 + m1 <= B2 \/ B2 + m2 <= B1.
Proof.
  intros HH H1 H2 NE. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M VM HH) (B1, m1) H1) as (_ & _ & AP). cbn [fst snd] in AP.
  apply (L5C.blocks_apart_in B1 m1 (lb_remove B1 LB) B2 m2 AP). apply L5C.in_lb_remove_neq; [exact H2| intros E; apply NE; symmetry; exact E].
Qed.
Lemma heap_nodup LB cr M VM : hi_heap HI LB cr M VM -> NoDup (map fst LB).
Proof. intros HH. exact (proj1 (proj2 (hio_wf L SCFG HI HIok LB cr M VM HH))). Qed.
Lemma fst_neq_app (l1 l2 : list (Z * Z)) B1 m1 B2 m2 :
  NoDup (map fst (l1 ++ l2)) -> In (B1, m1) l1 -> In (B2, m2) l2 -> B1 <> B2.
Proof.
  induction l1 as [|a l1 IH]; intros ND H1 H2; [destruct H1|]. cbn [app map] in ND. inversion ND as [|x l NI ND']. subst x l.
  destruct H1 as [->|H1].
  - cbn [fst] in NI. intros E. subst B2. apply NI. apply elem_of_In. rewrite map_app. apply in_or_app. right. apply (in_map fst l2 (B1, m2) H2).
  - apply IH; assumption.
Qed.
(* [comment removed for export] *)
Lemma own_not_in LB1 LB2 cr M VM B m a : hi_heap HI (LB1 ++ LB2) cr M VM -> In (B, m) LB1 -> B <= a < B + m -> ~ in_block LB2 a.
Proof.
  intros HH Hin Ha ((B2 & m2) & HX & Hr). cbn [fst snd] in Hr.
  assert (NE : B <> B2) by (apply (fst_neq_app LB1 LB2 B m B2 m2 (heap_nodup _ _ _ _ HH) Hin HX)).
  destruct (blocks_apart_heap _ _ _ _ B m B2 m2 HH (in_or_app _ _ _ (or_introl Hin)) (in_or_app _ _ _ (or_intror HX)) NE); lia.
Qed.
(* [comment removed for export] *)
Lemma own_not_client LB1 LB2 cr M VM B m a sp scr :
  hi_heap HI (LB1 ++ LB2) cr M VM -> In (B, m) LB1 -> B <= a < B + m -> ~ client_addr L LB2 sp scr a.
Proof.
  intros HH Hin Ha [IB|[[S1 _]|[IM _]]].
  - exact (own_not_in LB1 LB2 cr M VM B m a HH Hin Ha IB).
  - destruct (PMFR.brange_of_heap L HI HIok _ LB1 cr M VM HH (fun x H => in_or_app _ _ _ (or_introl H)) B m Hin) as (_ & _ & Q4). lia.
  - destruct (PMFR.brange_of_heap L HI HIok _ LB1 cr M VM HH (fun x H => in_or_app _ _ _ (or_introl H)) B m Hin) as (_ & Q1 & _). lia.
Qed.

(* [comment removed for export] *)
Lemma bown_split (s : PNM.bpst) LBX :
  PNM.bparser_own s ++ LBX = [(PM.sr_qc (PNM.b_src s), PM.CHUNK)] ++ [(PNM.b_sb s, PNM.BSZ * 2 ^ PNM.b_sk s)]
                             ++ (PGV8.v8_own (PNM.b_bb s) ++ PM.vs_own (PNM.b_nb s) ++ PM.vs_own (PNM.b_tb s)) ++ LBX.
Proof. unfold PNM.bparser_own, PNM.brest_own, PM.src_own, PNM.bvec_own. rewrite <- !app_assoc. reflexivity. Qed.

Theorem reset_ok : PNRS.reset_spec L HI.
Proof.
  unfold PNRS.reset_spec.
  intros fx R M model K LBX cr sp r fb s HH MOK K0 ENT FR A10 PA BBz SK1 KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK).
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & (STOP1 & STOP2) & SDEF). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  change (PMSP.pm_scr 1) with 14336 in *.
  destruct FR as (Fsp & Ftop & Fal). change (pa_frame AD) with 784 in Ftop.
  set (op := PNR.o_p AD fb) in *. assert (Eop : op = fb + 40) by reflexivity.
  set (ois := PNR.o_is AD fb) in *.
  assert (HO : bv_unsigned (getr R (reg 10)) = op) by (rewrite A10; apply L5.unsigned_lit; lia).
  (* [comment removed for export] *)
  set (src := PNM.b_src s) in *. set (b := PNM.b_sb s) in *. set (k := PNM.b_sk s) in *.
  assert (INO : incl (PNM.bparser_own s) (PNM.bparser_own s ++ LBX)) by (intros x Hx; apply in_or_app; left; exact Hx).
  pose proof (PMFR.brange_of_heap L HI HIok _ _ cr M _ HH INO) as BR.
  assert (Iq : In (PM.sr_qc src, PM.CHUNK) (PNM.bparser_own s)) by (unfold PNM.bparser_own; left; reflexivity).
  assert (Ib : In (b, PNM.BSZ * 2 ^ k) (PNM.bparser_own s)) by (unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own; right; left; reflexivity).
  destruct (BR _ _ Iq) as (Q0 & Q1 & Q4). destruct (BR _ _ Ib) as (Pb0 & Pb1 & Pb4).
  pose proof (heap_nodup _ _ _ _ HH) as ND.
  assert (NDs : NoDup (map fst (PNM.bparser_own s ++ LBX))) by exact ND.
  rewrite bown_split in ND.
  assert (Nqb : PM.sr_qc src <> b).
  { apply (fst_neq_app [(PM.sr_qc src, PM.CHUNK)] _ (PM.sr_qc src) PM.CHUNK b (PNM.BSZ * 2 ^ k) ND); [left; reflexivity| apply in_or_app; left; left; reflexivity]. }
  (* [comment removed for export] *)
  assert (NPAY : forall B m, In (B, m) (PGV8.v8_own (PNM.b_bb s) ++ PM.vs_own (PNM.b_nb s) ++ PM.vs_own (PNM.b_tb s)) -> PM.sr_qc src <> B /\ b <> B).
  { intros B m Hin. split.
    - apply (fst_neq_app [(PM.sr_qc src, PM.CHUNK)] _ (PM.sr_qc src) PM.CHUNK B m ND); [left; reflexivity| apply in_or_app; right; apply in_or_app; left; exact Hin].
    - cbn [app] in ND. inversion ND as [|x l _ ND1]. subst x l.
      apply (fst_neq_app [(b, PNM.BSZ * 2 ^ k)] _ b (PNM.BSZ * 2 ^ k) B m ND1); [left; reflexivity| apply in_or_app; left; exact Hin]. }
  pose proof (blocks_apart_heap _ _ _ _ _ _ _ _ HH (INO _ Iq) (INO _ Ib) Nqb) as Aqb.
  pose proof PA as (P0 & PD & _ & P8 & P9 & P10 & P12 & PNI & PSRC & P312 & _ & PBB & PNB & PTB & PVEC & PB1 & PB2).
  pose proof PVEC as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL).
  pose proof (PM.pow2_pos k ltac:(lia)) as P2k.
  assert (P2kh : 2 ^ k <= 2 ^ 11) by (apply Z.pow_le_mono_r; lia). change (2 ^ 11) with 2048 in P2kh.
  unfold PNM.BSZ in *.
  assert (Cb : forall i, PM.sr_qc src <= i < PM.sr_qc src + PM.CHUNK -> ~ (b <= i < b + 40)) by (intros i Hi X; destruct Aqb; lia).
  pose proof (L5C.stk_writable RSEGS _ M sp 14336 STK) as WR.
  assert (WRop : L5.writable RSEGS M op 416) by (apply (L5C.writable_of_defined RSEGS M op 416 PD); lia).
  assert (WRb : L5.writable RSEGS M b 40) by (apply (L5C.writable_of_defined RSEGS M b 40); [apply (L5.defined_sub M b (40 * 2 ^ k) b 40 DB); lia|lia|lia]).
  assert (BRX : PMFR.brange L LBX) by (apply (PMFR.brange_of_heap L HI HIok _ LBX cr M _ HH); intros x Hx; apply in_or_app; right; exact Hx).
  pose proof (ly_img_hi L LY) as Himg.
  assert (HSP : 0x7fff80000000 <= hl_sptop L) by exact STOP1.
  pose proof (v8_data_at RSEGS _ _ M (op + 320) (PNM.b_bb s) PBB) as BB0.
  set (bb0 := PGV8.v8_data (PNM.b_bb s)) in *.
  assert (Hbb0 : 0 <= bb0 < 2 ^ 64).
  { unfold bb0. destruct (PNM.b_bb s) as [|bq bn bc] eqn:EBB; cbn; [lia|]. destruct PBB as (_ & _ & _ & _ & _ & _ & Hbc & Hbq & _).
    assert (Ibq : In (bq, bc) (PNM.bparser_own s)) by (unfold PNM.bparser_own, PNM.brest_own; rewrite EBB; right; right; left; reflexivity).
    destruct (BR _ _ Ibq) as (X0 & _ & X4). lia. }
  assert (V0' : L5.u64_at RSEGS M (op + 392) b) by exact V0.
  assert (V16' : L5.u64_at RSEGS M (op + 408) (b + 40 * 2 ^ k)) by (replace (op + 408) with (op + 392 + 16) by lia; exact V16).
  assert (BB0' : L5.u64_at RSEGS M (op + 320) bb0) by exact BB0.
  assert (C328i : L5.u64_at RSEGS M (op + 328) bb0).
  { unfold bb0. replace (op + 328) with (op + 320 + 8) by lia.
    destruct (PNM.b_bb s) as [|bq bn bc] eqn:EBB; cbn [PGV8.v8_size PGV8.v8_data] in *.
    - destruct PBB as (_ & _ & _ & X8 & _). exact X8.
    - destruct PBB as (_ & _ & _ & X8 & _). rewrite BBz, Z.add_0_r in X8. exact X8. }
  assert (C400i : L5.u64_at RSEGS M (op + 400) (b + 40)).
  { rewrite SK1 in V8. replace (op + 400) with (op + 392 + 8) by lia. replace (b + 40) with (b + 40 * Z.of_nat 1) by lia. exact V8. }
  (* [comment removed for export] *)
  assert (HLop : 0 <= op /\ op + 416 <= 2 ^ 64) by lia.
  unfold PMSP.cfg. cbn [PNL.pn_reset PnLayoutS_u.NADDR_S].
  destruct (PNM.b_nb s) as [nn|nc nn pn] eqn:NBe; destruct (PNM.b_tb s) as [tn|tc tn pt] eqn:TBe.
  - (* [comment removed for export] *)
    destruct PNB as (NBD & _ & Hnn & NB0). pose proof (PMF.even_byte nn) as EVN.
    destruct PTB as (TBD & _ & Htn & TB0). pose proof (PMF.even_byte tn) as EVT.
    pose proof (PNSRBP.rbSS_conc fx R M (fun j => match j with 2%nat => sp | 35%nat => bb0 | 36%nat => b | 39%nat => 40 * 2 ^ k | 33%nat => 2 * nn | 34%nat => 2 * tn | _ => 0 end)) as PP.
    cbn beta iota in PP. rewrite HO in PP.
    PMK.feed PP ltac:(first [PMK.sc]).
    PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
      destruct pvzP as (MG & _ & FRZ0 & MS & KS & _ & _ & _ & C400 & E24 & E16 & E8 & E0 & E32 & (T0 & T1) & (N0 & N1) & C328 & (C8 & C9) & _)); PMK.pvz_clrT.
    set (P := fun a => (sp - 40 <= a < sp - 40 + 40) \/ (op + 8 <= a < op + 8 + 2) \/ (op + 328 <= a < op + 328 + 8) \/ (op + 400 <= a < op + 400 + 8) \/ (b <= a < b + 40) \/ (op + 344 <= a < op + 344 + 2) \/ (op + 368 <= a < op + 368 + 2)).
    assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; unfold P; lia ..]. }
    apply (PMK.spiece RSEGS L HI KL HIok (PNM.bparser_own s ++ LBX) cr M model fx fx1 R 0x36a90 R1 0x36bb8 M1 P K HH Mh Ml HSP MS MG FRZ).
    { intros a Pa. unfold P in Pa. destruct Pa as [X|[X|[X|[X|[X|[X|X]]]]]].
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_block L (PNM.bparser_own s ++ LBX) b (40 * 2 ^ k) a (INO _ Ib)); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
    }
    { intros a. unfold P. repeat apply PMK.or_dec; apply PMK.rng_dec. }
    intros HH1.
    assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS 1%nat) by PMK.inl; exact Rra).
    unfold PMK.cfg.
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x36bb8 W_35f58 r F_35f58 ltac:(reflexivity) D_35f58 RA1 Hr1 Hr2)|].
    apply (KONT fx1 R1 M1); [| | |exact HH1].
    + apply PMK.preserved_by_index. intros x Hx. apply KS. revert x Hx. apply sub_in. vm_compute. reflexivity.
    + apply (brs_post RSEGS AD (pa_vp_parser AD) M M1 op ois s P PA).
      all: try change (PNM.b_src s) with src; try change (PNM.b_sb s) with b; try change (PGV8.v8_data (PNM.b_bb s)) with bb0.
      1-4: lia. 1: exact FRZ. 1: exact MG. 2-10: assumption.
      * intros i Hi X. unfold P in X. destruct Hi as [Hi|[Hi|[Hi|[Hi|[Hi|Hi]]]]]; [destruct X as [X|[X|[X|[X|[X|[X|X]]]]]]; cdisj; lia ..|].
        destruct X as [X|[X|[X|[X|[X|[X|X]]]]]]; [cdisj; lia| cdisj; lia| cdisj; lia| cdisj; lia| exact (Cb i Hi X)| cdisj; lia| cdisj; lia].
      * rewrite NBe. cbn [PNR.vs_clear]. split; [intros i Hi; apply MG; apply NBD; exact Hi|]. split; [exact I|]. split; [lia| exact N0].
      * rewrite TBe. cbn [PNR.vs_clear]. split; [intros i Hi; apply MG; apply TBD; exact Hi|]. split; [exact I|]. split; [lia| exact T0].
    + change (PNR.o_bb AD fb) with (op + 320). change (PNR.o_nb AD fb) with (op + 344). change (PNR.o_tb AD fb) with (op + 368).
      change (PNR.o_stk AD fb) with (op + 392).
      apply (PMK.hpres_of L LBX sp 14336 _ M M1).
      * apply (PMK.ek_piece L LBX sp 14336 _ M M1 P FRZ). intros a Ha CA NE OW Pa. unfold P in Pa. destruct Pa as [X|[X|[X|[X|[X|[X|X]]]]]].
        -- destruct CA as [((bq & mq) & Hbq & Hr)|[[S1 S2]|[IM _]]]; [destruct (BRX bq mq Hbq) as (_ & _ & Y); cbn [fst snd] in Hr; lia| lia| lia].
        -- apply (OW (op + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        -- apply (OW (op + 320, 24)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        -- apply (OW (op + 392, 24)); [right; right; right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        -- exact (own_not_client (PNM.bparser_own s) LBX cr M _ b (40 * 2 ^ k) a sp 14336 HH Ib ltac:(lia) CA).
        -- apply (OW (op + 344, 24)); [right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        -- apply (OW (op + 368, 24)); [right; right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
      * destruct (PMK.stk_grows L M M1 sp 14336 MG STK) as (_ & _ & _ & _ & D1). exact D1.
      * apply PMK.dk_grows. exact MG.
  - (* [comment removed for export] *)
    destruct PNB as (NBD & _ & Hnn & NB0). pose proof (PMF.even_byte nn) as EVN.
    destruct PTB as (TBD & _ & TB0 & TB8 & TB16 & Htnc & Htc & Htce & TBDp & _).
    assert (Ipt : In (pt, tc) (PGV8.v8_own (PNM.b_bb s) ++ PM.vs_own (PM.VShort nn) ++ PM.vs_own (PM.VLong tc tn pt))) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
    assert (Ipto : In (pt, tc) (PNM.bparser_own s)) by (unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own; rewrite NBe, TBe; right; right; exact Ipt).
    destruct (BR _ _ Ipto) as (Ppt0 & Ppt1 & Ppt4). destruct (NPAY _ _ Ipt) as (Nqpt & Nbpt).
    pose proof (blocks_apart_heap _ _ _ _ _ _ _ _ HH (INO _ Iq) (INO _ Ipto) Nqpt) as Aqpt.
    pose proof (blocks_apart_heap _ _ _ _ _ _ _ _ HH (INO _ Ib) (INO _ Ipto) Nbpt) as Abpt.
    assert (Cpt : forall i, PM.sr_qc src <= i < PM.sr_qc src + PM.CHUNK -> ~ (pt <= i < pt + 1)) by (intros i Hi X; destruct Aqpt; lia).
    pose proof (PMF.u8_of_u64 RSEGS M (op + 368) (tc + 1) ltac:(lia) TB0) as TB0b. pose proof (PMF.odd_byte tc Htce ltac:(lia)) as ODT.
    assert (TB16' : L5.u64_at RSEGS M (op + 384) pt) by (replace (op + 384) with (op + 368 + 16) by lia; exact TB16).
    assert (Dptb : pt + 1 <= b \/ b + 40 <= pt) by (destruct Abpt as [X|X]; [right|left]; lia).
    assert (Dptf : (sp - 80) + 80 <= pt \/ pt + 1 <= sp - 80) by (right; lia).
    assert (Dpto : pt + 1 <= op \/ op + 416 <= pt) by (left; lia).
    assert (H34 : 0 <= (tc + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (tc + 1) 256 ltac:(lia)); lia).
    assert (WRpt : L5.writable RSEGS M pt 1) by (apply (L5C.writable_of_defined RSEGS M pt 1); [apply (L5.defined_sub M pt tc pt 1 TBDp); lia|lia|lia]).
    pose proof (PNSRBP.rbSL_conc fx R M (fun j => match j with 2%nat => sp | 35%nat => bb0 | 36%nat => b | 39%nat => 40 * 2 ^ k | 33%nat => 2 * nn | 34%nat => (tc + 1) mod 256 | 38%nat => pt | _ => 0 end)) as PP.
    cbn beta iota in PP. rewrite HO in PP.
    PMK.feed PP ltac:(first [PMK.sc]).
    PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
      destruct pvzP as (MG & _ & FRZ0 & MS & KS & _ & _ & _ & C400 & E24 & E16 & E8 & E0 & E32 & T376 & TP & (N0 & N1) & C328 & (C8 & C9) & _)); PMK.pvz_clrT.
    set (P := fun a => (sp - 40 <= a < sp - 40 + 40) \/ (op + 8 <= a < op + 8 + 2) \/ (op + 328 <= a < op + 328 + 8) \/ (op + 400 <= a < op + 400 + 8) \/ (b <= a < b + 40) \/ (op + 344 <= a < op + 344 + 2) \/ (pt <= a < pt + 1) \/ (op + 376 <= a < op + 376 + 8)).
    assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; unfold P; lia ..]. }
    apply (PMK.spiece RSEGS L HI KL HIok (PNM.bparser_own s ++ LBX) cr M model fx fx1 R 0x36a90 R1 0x36bb8 M1 P K HH Mh Ml HSP MS MG FRZ).
    { intros a Pa. unfold P in Pa. destruct Pa as [X|[X|[X|[X|[X|[X|[X|X]]]]]]].
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_block L (PNM.bparser_own s ++ LBX) b (40 * 2 ^ k) a (INO _ Ib)); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_block L (PNM.bparser_own s ++ LBX) pt tc a (INO _ Ipto)); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
    }
    { intros a. unfold P. repeat apply PMK.or_dec; apply PMK.rng_dec. }
    intros HH1.
    assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS 1%nat) by PMK.inl; exact Rra).
    unfold PMK.cfg.
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x36bb8 W_35f58 r F_35f58 ltac:(reflexivity) D_35f58 RA1 Hr1 Hr2)|].
    apply (KONT fx1 R1 M1); [| | |exact HH1].
    + apply PMK.preserved_by_index. intros x Hx. apply KS. revert x Hx. apply sub_in. vm_compute. reflexivity.
    + apply (brs_post RSEGS AD (pa_vp_parser AD) M M1 op ois s P PA).
      all: try change (PNM.b_src s) with src; try change (PNM.b_sb s) with b; try change (PGV8.v8_data (PNM.b_bb s)) with bb0.
      1-4: lia. 1: exact FRZ. 1: exact MG. 2-10: assumption.
      * intros i Hi X. unfold P in X. destruct Hi as [Hi|[Hi|[Hi|[Hi|[Hi|Hi]]]]]; [destruct X as [X|[X|[X|[X|[X|[X|[X|X]]]]]]]; cdisj; lia ..|].
        destruct X as [X|[X|[X|[X|[X|[X|[X|X]]]]]]]; [cdisj; lia| cdisj; lia| cdisj; lia| cdisj; lia| exact (Cb i Hi X)| cdisj; lia| exact (Cpt i Hi X)| cdisj; lia].
      * rewrite NBe. cbn [PNR.vs_clear]. split; [intros i Hi; apply MG; apply NBD; exact Hi|]. split; [exact I|]. split; [lia| exact N0].
      * rewrite TBe. cbn [PNR.vs_clear]. split; [intros i Hi; apply MG; apply TBD; exact Hi|]. split; [exact I|].
        assert (AGL : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ P i) -> L5C.agree_on M M1 a n).
        { intros a0 n0 Ha Hn X i Hi. apply FRZ; [lia| apply X; exact Hi]. }
        split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AGL; [lia|lia| intros i Hi X; unfold P in X; destruct X as [X|[X|[X|[X|[X|[X|[X|X]]]]]]]; cdisj; lia]|lia|lia|exact TB0]|].
        split; [replace (op + 368 + 8) with (op + 376) by lia; exact T376|].
        split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AGL; [lia|lia| intros i Hi X; unfold P in X; destruct X as [X|[X|[X|[X|[X|[X|[X|X]]]]]]]; cdisj; lia]|lia|lia|exact TB16]|].
        split; [lia|]. split; [lia|]. split; [exact Htce|]. split; [intros i Hi; apply MG; apply TBDp; exact Hi| exact I].
    + change (PNR.o_bb AD fb) with (op + 320). change (PNR.o_nb AD fb) with (op + 344). change (PNR.o_tb AD fb) with (op + 368).
      change (PNR.o_stk AD fb) with (op + 392).
      apply (PMK.hpres_of L LBX sp 14336 _ M M1).
      * apply (PMK.ek_piece L LBX sp 14336 _ M M1 P FRZ). intros a Ha CA NE OW Pa. unfold P in Pa. destruct Pa as [X|[X|[X|[X|[X|[X|[X|X]]]]]]].
        -- destruct CA as [((bq & mq) & Hbq & Hr)|[[S1 S2]|[IM _]]]; [destruct (BRX bq mq Hbq) as (_ & _ & Y); cbn [fst snd] in Hr; lia| lia| lia].
        -- apply (OW (op + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        -- apply (OW (op + 320, 24)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        -- apply (OW (op + 392, 24)); [right; right; right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        -- exact (own_not_client (PNM.bparser_own s) LBX cr M _ b (40 * 2 ^ k) a sp 14336 HH Ib ltac:(lia) CA).
        -- apply (OW (op + 344, 24)); [right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        -- exact (own_not_client (PNM.bparser_own s) LBX cr M _ pt tc a sp 14336 HH Ipto ltac:(lia) CA).
        -- apply (OW (op + 368, 24)); [right; right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
      * destruct (PMK.stk_grows L M M1 sp 14336 MG STK) as (_ & _ & _ & _ & D1). exact D1.
      * apply PMK.dk_grows. exact MG.
  - (* [comment removed for export] *)
    destruct PNB as (NBD & _ & NB0 & NB8 & NB16 & Hnnc & Hnc & Hnce & NBDp & _).
    assert (Ipn : In (pn, nc) (PGV8.v8_own (PNM.b_bb s) ++ PM.vs_own (PM.VLong nc nn pn) ++ PM.vs_own (PM.VShort tn))) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
    assert (Ipno : In (pn, nc) (PNM.bparser_own s)) by (unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own; rewrite NBe, TBe; right; right; exact Ipn).
    destruct (BR _ _ Ipno) as (Ppn0 & Ppn1 & Ppn4). destruct (NPAY _ _ Ipn) as (Nqpn & Nbpn).
    pose proof (blocks_apart_heap _ _ _ _ _ _ _ _ HH (INO _ Iq) (INO _ Ipno) Nqpn) as Aqpn.
    pose proof (blocks_apart_heap _ _ _ _ _ _ _ _ HH (INO _ Ib) (INO _ Ipno) Nbpn) as Abpn.
    assert (Cpn : forall i, PM.sr_qc src <= i < PM.sr_qc src + PM.CHUNK -> ~ (pn <= i < pn + 1)) by (intros i Hi X; destruct Aqpn; lia).
    pose proof (PMF.u8_of_u64 RSEGS M (op + 344) (nc + 1) ltac:(lia) NB0) as NB0b. pose proof (PMF.odd_byte nc Hnce ltac:(lia)) as ODN.
    assert (NB16' : L5.u64_at RSEGS M (op + 360) pn) by (replace (op + 360) with (op + 344 + 16) by lia; exact NB16).
    assert (Dpnb : pn + 1 <= b \/ b + 40 <= pn) by (destruct Abpn as [X|X]; [right|left]; lia).
    assert (Dpnf : (sp - 80) + 80 <= pn \/ pn + 1 <= sp - 80) by (right; lia).
    assert (Dpno : pn + 1 <= op \/ op + 416 <= pn) by (left; lia).
    assert (H33 : 0 <= (nc + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (nc + 1) 256 ltac:(lia)); lia).
    assert (WRpn : L5.writable RSEGS M pn 1) by (apply (L5C.writable_of_defined RSEGS M pn 1); [apply (L5.defined_sub M pn nc pn 1 NBDp); lia|lia|lia]).
    destruct PTB as (TBD & _ & Htn & TB0). pose proof (PMF.even_byte tn) as EVT.
    pose proof (PNSRBP.rbLS_conc fx R M (fun j => match j with 2%nat => sp | 35%nat => bb0 | 36%nat => b | 39%nat => 40 * 2 ^ k | 33%nat => (nc + 1) mod 256 | 37%nat => pn | 34%nat => 2 * tn | _ => 0 end)) as PP.
    cbn beta iota in PP. rewrite HO in PP.
    PMK.feed PP ltac:(first [PMK.sc]).
    PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
      destruct pvzP as (MG & _ & FRZ0 & MS & KS & _ & _ & _ & C400 & E24 & E16 & E8 & E0 & E32 & (T0 & T1) & N352 & NP & C328 & (C8 & C9) & _)); PMK.pvz_clrT.
    set (P := fun a => (sp - 40 <= a < sp - 40 + 40) \/ (op + 8 <= a < op + 8 + 2) \/ (op + 328 <= a < op + 328 + 8) \/ (op + 400 <= a < op + 400 + 8) \/ (b <= a < b + 40) \/ (pn <= a < pn + 1) \/ (op + 352 <= a < op + 352 + 8) \/ (op + 368 <= a < op + 368 + 2)).
    assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; unfold P; lia ..]. }
    apply (PMK.spiece RSEGS L HI KL HIok (PNM.bparser_own s ++ LBX) cr M model fx fx1 R 0x36a90 R1 0x36bb8 M1 P K HH Mh Ml HSP MS MG FRZ).
    { intros a Pa. unfold P in Pa. destruct Pa as [X|[X|[X|[X|[X|[X|[X|X]]]]]]].
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_block L (PNM.bparser_own s ++ LBX) b (40 * 2 ^ k) a (INO _ Ib)); lia.
      - apply (PMK.cwr_block L (PNM.bparser_own s ++ LBX) pn nc a (INO _ Ipno)); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
    }
    { intros a. unfold P. repeat apply PMK.or_dec; apply PMK.rng_dec. }
    intros HH1.
    assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS 1%nat) by PMK.inl; exact Rra).
    unfold PMK.cfg.
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x36bb8 W_35f58 r F_35f58 ltac:(reflexivity) D_35f58 RA1 Hr1 Hr2)|].
    apply (KONT fx1 R1 M1); [| | |exact HH1].
    + apply PMK.preserved_by_index. intros x Hx. apply KS. revert x Hx. apply sub_in. vm_compute. reflexivity.
    + apply (brs_post RSEGS AD (pa_vp_parser AD) M M1 op ois s P PA).
      all: try change (PNM.b_src s) with src; try change (PNM.b_sb s) with b; try change (PGV8.v8_data (PNM.b_bb s)) with bb0.
      1-4: lia. 1: exact FRZ. 1: exact MG. 2-10: assumption.
      * intros i Hi X. unfold P in X. destruct Hi as [Hi|[Hi|[Hi|[Hi|[Hi|Hi]]]]]; [destruct X as [X|[X|[X|[X|[X|[X|[X|X]]]]]]]; cdisj; lia ..|].
        destruct X as [X|[X|[X|[X|[X|[X|[X|X]]]]]]]; [cdisj; lia| cdisj; lia| cdisj; lia| cdisj; lia| exact (Cb i Hi X)| exact (Cpn i Hi X)| cdisj; lia| cdisj; lia].
      * rewrite NBe. cbn [PNR.vs_clear]. split; [intros i Hi; apply MG; apply NBD; exact Hi|]. split; [exact I|].
        assert (AGL : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ P i) -> L5C.agree_on M M1 a n).
        { intros a0 n0 Ha Hn X i Hi. apply FRZ; [lia| apply X; exact Hi]. }
        split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AGL; [lia|lia| intros i Hi X; unfold P in X; destruct X as [X|[X|[X|[X|[X|[X|[X|X]]]]]]]; cdisj; lia]|lia|lia|exact NB0]|].
        split; [replace (op + 344 + 8) with (op + 352) by lia; exact N352|].
        split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AGL; [lia|lia| intros i Hi X; unfold P in X; destruct X as [X|[X|[X|[X|[X|[X|[X|X]]]]]]]; cdisj; lia]|lia|lia|exact NB16]|].
        split; [lia|]. split; [lia|]. split; [exact Hnce|]. split; [intros i Hi; apply MG; apply NBDp; exact Hi| exact I].
      * rewrite TBe. cbn [PNR.vs_clear]. split; [intros i Hi; apply MG; apply TBD; exact Hi|]. split; [exact I|]. split; [lia| exact T0].
    + change (PNR.o_bb AD fb) with (op + 320). change (PNR.o_nb AD fb) with (op + 344). change (PNR.o_tb AD fb) with (op + 368).
      change (PNR.o_stk AD fb) with (op + 392).
      apply (PMK.hpres_of L LBX sp 14336 _ M M1).
      * apply (PMK.ek_piece L LBX sp 14336 _ M M1 P FRZ). intros a Ha CA NE OW Pa. unfold P in Pa. destruct Pa as [X|[X|[X|[X|[X|[X|[X|X]]]]]]].
        -- destruct CA as [((bq & mq) & Hbq & Hr)|[[S1 S2]|[IM _]]]; [destruct (BRX bq mq Hbq) as (_ & _ & Y); cbn [fst snd] in Hr; lia| lia| lia].
        -- apply (OW (op + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        -- apply (OW (op + 320, 24)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        -- apply (OW (op + 392, 24)); [right; right; right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        -- exact (own_not_client (PNM.bparser_own s) LBX cr M _ b (40 * 2 ^ k) a sp 14336 HH Ib ltac:(lia) CA).
        -- exact (own_not_client (PNM.bparser_own s) LBX cr M _ pn nc a sp 14336 HH Ipno ltac:(lia) CA).
        -- apply (OW (op + 344, 24)); [right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        -- apply (OW (op + 368, 24)); [right; right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
      * destruct (PMK.stk_grows L M M1 sp 14336 MG STK) as (_ & _ & _ & _ & D1). exact D1.
      * apply PMK.dk_grows. exact MG.
  - (* [comment removed for export] *)
    destruct PNB as (NBD & _ & NB0 & NB8 & NB16 & Hnnc & Hnc & Hnce & NBDp & _).
    assert (Ipn : In (pn, nc) (PGV8.v8_own (PNM.b_bb s) ++ PM.vs_own (PM.VLong nc nn pn) ++ PM.vs_own (PM.VLong tc tn pt))) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
    assert (Ipno : In (pn, nc) (PNM.bparser_own s)) by (unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own; rewrite NBe, TBe; right; right; exact Ipn).
    destruct (BR _ _ Ipno) as (Ppn0 & Ppn1 & Ppn4). destruct (NPAY _ _ Ipn) as (Nqpn & Nbpn).
    pose proof (blocks_apart_heap _ _ _ _ _ _ _ _ HH (INO _ Iq) (INO _ Ipno) Nqpn) as Aqpn.
    pose proof (blocks_apart_heap _ _ _ _ _ _ _ _ HH (INO _ Ib) (INO _ Ipno) Nbpn) as Abpn.
    assert (Cpn : forall i, PM.sr_qc src <= i < PM.sr_qc src + PM.CHUNK -> ~ (pn <= i < pn + 1)) by (intros i Hi X; destruct Aqpn; lia).
    pose proof (PMF.u8_of_u64 RSEGS M (op + 344) (nc + 1) ltac:(lia) NB0) as NB0b. pose proof (PMF.odd_byte nc Hnce ltac:(lia)) as ODN.
    assert (NB16' : L5.u64_at RSEGS M (op + 360) pn) by (replace (op + 360) with (op + 344 + 16) by lia; exact NB16).
    assert (Dpnb : pn + 1 <= b \/ b + 40 <= pn) by (destruct Abpn as [X|X]; [right|left]; lia).
    assert (Dpnf : (sp - 80) + 80 <= pn \/ pn + 1 <= sp - 80) by (right; lia).
    assert (Dpno : pn + 1 <= op \/ op + 416 <= pn) by (left; lia).
    assert (H33 : 0 <= (nc + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (nc + 1) 256 ltac:(lia)); lia).
    assert (WRpn : L5.writable RSEGS M pn 1) by (apply (L5C.writable_of_defined RSEGS M pn 1); [apply (L5.defined_sub M pn nc pn 1 NBDp); lia|lia|lia]).
    destruct PTB as (TBD & _ & TB0 & TB8 & TB16 & Htnc & Htc & Htce & TBDp & _).
    assert (Ipt : In (pt, tc) (PGV8.v8_own (PNM.b_bb s) ++ PM.vs_own (PM.VLong nc nn pn) ++ PM.vs_own (PM.VLong tc tn pt))) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
    assert (Ipto : In (pt, tc) (PNM.bparser_own s)) by (unfold PNM.bparser_own, PNM.brest_own, PNM.bvec_own; rewrite NBe, TBe; right; right; exact Ipt).
    destruct (BR _ _ Ipto) as (Ppt0 & Ppt1 & Ppt4). destruct (NPAY _ _ Ipt) as (Nqpt & Nbpt).
    pose proof (blocks_apart_heap _ _ _ _ _ _ _ _ HH (INO _ Iq) (INO _ Ipto) Nqpt) as Aqpt.
    pose proof (blocks_apart_heap _ _ _ _ _ _ _ _ HH (INO _ Ib) (INO _ Ipto) Nbpt) as Abpt.
    assert (Cpt : forall i, PM.sr_qc src <= i < PM.sr_qc src + PM.CHUNK -> ~ (pt <= i < pt + 1)) by (intros i Hi X; destruct Aqpt; lia).
    pose proof (PMF.u8_of_u64 RSEGS M (op + 368) (tc + 1) ltac:(lia) TB0) as TB0b. pose proof (PMF.odd_byte tc Htce ltac:(lia)) as ODT.
    assert (TB16' : L5.u64_at RSEGS M (op + 384) pt) by (replace (op + 384) with (op + 368 + 16) by lia; exact TB16).
    assert (Dptb : pt + 1 <= b \/ b + 40 <= pt) by (destruct Abpt as [X|X]; [right|left]; lia).
    assert (Dptf : (sp - 80) + 80 <= pt \/ pt + 1 <= sp - 80) by (right; lia).
    assert (Dpto : pt + 1 <= op \/ op + 416 <= pt) by (left; lia).
    assert (H34 : 0 <= (tc + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (tc + 1) 256 ltac:(lia)); lia).
    assert (WRpt : L5.writable RSEGS M pt 1) by (apply (L5C.writable_of_defined RSEGS M pt 1); [apply (L5.defined_sub M pt tc pt 1 TBDp); lia|lia|lia]).
    assert (ND2 : NoDup (map fst (((PM.sr_qc src, PM.CHUNK) :: (b, PNM.BSZ * 2 ^ k) :: PGV8.v8_own (PNM.b_bb s) ++ [(pn, nc)]) ++ ([(pt, tc)] ++ LBX)))).
    { clear -NDs NBe TBe. unfold PNM.bparser_own, PNM.brest_own, PM.src_own, PNM.bvec_own in NDs. rewrite NBe, TBe in NDs. cbn [PM.vs_own] in NDs.
      cbn [app] in NDs |- *. repeat rewrite <- app_assoc in NDs. repeat rewrite <- app_assoc. cbn [app] in NDs |- *. exact NDs. }
    assert (Npnt : pn <> pt) by (apply (fst_neq_app _ _ pn nc pt tc ND2); [right; right; apply in_or_app; right; left; reflexivity| left; reflexivity]).
    pose proof (blocks_apart_heap _ _ _ _ _ _ _ _ HH (INO _ Ipno) (INO _ Ipto) Npnt) as Apnt.
    assert (Dpnt : pn + 1 <= pt \/ pt + 1 <= pn) by (destruct Apnt as [X|X]; [left|right]; lia).
    pose proof (PNSRBP.rbLL_conc fx R M (fun j => match j with 2%nat => sp | 35%nat => bb0 | 36%nat => b | 39%nat => 40 * 2 ^ k | 33%nat => (nc + 1) mod 256 | 37%nat => pn | 34%nat => (tc + 1) mod 256 | 38%nat => pt | _ => 0 end)) as PP.
    cbn beta iota in PP. rewrite HO in PP.
    PMK.feed PP ltac:(first [PMK.sc]).
    PMK.pvz_hg ltac:(idtac; destruct PP as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
      destruct pvzP as (MG & _ & FRZ0 & MS & KS & _ & _ & _ & C400 & E24 & E16 & E8 & E0 & E32 & T376 & TP & N352 & NP & C328 & (C8 & C9) & _)); PMK.pvz_clrT.
    set (P := fun a => (sp - 40 <= a < sp - 40 + 40) \/ (op + 8 <= a < op + 8 + 2) \/ (op + 328 <= a < op + 328 + 8) \/ (op + 400 <= a < op + 400 + 8) \/ (b <= a < b + 40) \/ (pn <= a < pn + 1) \/ (op + 352 <= a < op + 352 + 8) \/ (pt <= a < pt + 1) \/ (op + 376 <= a < op + 376 + 8)).
    assert (FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N. apply FRZ0; [exact Ha| intro X; apply N; unfold P; lia ..]. }
    apply (PMK.spiece RSEGS L HI KL HIok (PNM.bparser_own s ++ LBX) cr M model fx fx1 R 0x36a90 R1 0x36bb8 M1 P K HH Mh Ml HSP MS MG FRZ).
    { intros a Pa. unfold P in Pa. destruct Pa as [X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]].
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_block L (PNM.bparser_own s ++ LBX) b (40 * 2 ^ k) a (INO _ Ib)); lia.
      - apply (PMK.cwr_block L (PNM.bparser_own s ++ LBX) pn nc a (INO _ Ipno)); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
      - apply (PMK.cwr_block L (PNM.bparser_own s ++ LBX) pt tc a (INO _ Ipto)); lia.
      - apply (PMK.cwr_stack L (PNM.bparser_own s ++ LBX) M sp 14336 a STK); lia.
    }
    { intros a. unfold P. repeat apply PMK.or_dec; apply PMK.rng_dec. }
    intros HH1.
    assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS 1%nat) by PMK.inl; exact Rra).
    unfold PMK.cfg.
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x36bb8 W_35f58 r F_35f58 ltac:(reflexivity) D_35f58 RA1 Hr1 Hr2)|].
    apply (KONT fx1 R1 M1); [| | |exact HH1].
    + apply PMK.preserved_by_index. intros x Hx. apply KS. revert x Hx. apply sub_in. vm_compute. reflexivity.
    + apply (brs_post RSEGS AD (pa_vp_parser AD) M M1 op ois s P PA).
      all: try change (PNM.b_src s) with src; try change (PNM.b_sb s) with b; try change (PGV8.v8_data (PNM.b_bb s)) with bb0.
      1-4: lia. 1: exact FRZ. 1: exact MG. 2-10: assumption.
      * intros i Hi X. unfold P in X. destruct Hi as [Hi|[Hi|[Hi|[Hi|[Hi|Hi]]]]]; [destruct X as [X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]; cdisj; lia ..|].
        destruct X as [X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]; [cdisj; lia| cdisj; lia| cdisj; lia| cdisj; lia| exact (Cb i Hi X)| exact (Cpn i Hi X)| cdisj; lia| exact (Cpt i Hi X)| cdisj; lia].
      * rewrite NBe. cbn [PNR.vs_clear]. split; [intros i Hi; apply MG; apply NBD; exact Hi|]. split; [exact I|].
        assert (AGL : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ P i) -> L5C.agree_on M M1 a n).
        { intros a0 n0 Ha Hn X i Hi. apply FRZ; [lia| apply X; exact Hi]. }
        split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AGL; [lia|lia| intros i Hi X; unfold P in X; destruct X as [X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]; cdisj; lia]|lia|lia|exact NB0]|].
        split; [replace (op + 344 + 8) with (op + 352) by lia; exact N352|].
        split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AGL; [lia|lia| intros i Hi X; unfold P in X; destruct X as [X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]; cdisj; lia]|lia|lia|exact NB16]|].
        split; [lia|]. split; [lia|]. split; [exact Hnce|]. split; [intros i Hi; apply MG; apply NBDp; exact Hi| exact I].
      * rewrite TBe. cbn [PNR.vs_clear]. split; [intros i Hi; apply MG; apply TBD; exact Hi|]. split; [exact I|].
        assert (AGL : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ P i) -> L5C.agree_on M M1 a n).
        { intros a0 n0 Ha Hn X i Hi. apply FRZ; [lia| apply X; exact Hi]. }
        split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AGL; [lia|lia| intros i Hi X; unfold P in X; destruct X as [X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]; cdisj; lia]|lia|lia|exact TB0]|].
        split; [replace (op + 368 + 8) with (op + 376) by lia; exact T376|].
        split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AGL; [lia|lia| intros i Hi X; unfold P in X; destruct X as [X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]; cdisj; lia]|lia|lia|exact TB16]|].
        split; [lia|]. split; [lia|]. split; [exact Htce|]. split; [intros i Hi; apply MG; apply TBDp; exact Hi| exact I].
    + change (PNR.o_bb AD fb) with (op + 320). change (PNR.o_nb AD fb) with (op + 344). change (PNR.o_tb AD fb) with (op + 368).
      change (PNR.o_stk AD fb) with (op + 392).
      apply (PMK.hpres_of L LBX sp 14336 _ M M1).
      * apply (PMK.ek_piece L LBX sp 14336 _ M M1 P FRZ). intros a Ha CA NE OW Pa. unfold P in Pa. destruct Pa as [X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]].
        -- destruct CA as [((bq & mq) & Hbq & Hr)|[[S1 S2]|[IM _]]]; [destruct (BRX bq mq Hbq) as (_ & _ & Y); cbn [fst snd] in Hr; lia| lia| lia].
        -- apply (OW (op + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        -- apply (OW (op + 320, 24)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        -- apply (OW (op + 392, 24)); [right; right; right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        -- exact (own_not_client (PNM.bparser_own s) LBX cr M _ b (40 * 2 ^ k) a sp 14336 HH Ib ltac:(lia) CA).
        -- exact (own_not_client (PNM.bparser_own s) LBX cr M _ pn nc a sp 14336 HH Ipno ltac:(lia) CA).
        -- apply (OW (op + 344, 24)); [right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
        -- exact (own_not_client (PNM.bparser_own s) LBX cr M _ pt tc a sp 14336 HH Ipto ltac:(lia) CA).
        -- apply (OW (op + 368, 24)); [right; right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
      * destruct (PMK.stk_grows L M M1 sp 14336 MG STK) as (_ & _ & _ & _ & D1). exact D1.
      * apply PMK.dk_grows. exact MG.
Qed.


End WithHeap.
End PNSRB.
