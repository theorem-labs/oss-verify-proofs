(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRepAux MRepAux RF_m8yt RF_egfy MTree Mallwlb Mallj6y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallkgx Malls02 Malluin Mallkgx Mall17y.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallj6y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlh4s RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASl8dw.

Module RASltfw.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRepAux MRepAux RF_m8yt RF_egfy MTree Mallwlb Mallj6y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallkgx Malls02 Malluin Mallkgx Mall17y.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallj6y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlh4s RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASl8dw.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlh4s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASl8dw.RASldlz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Malls02 Mallmv3 RAlllfc RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require ASlot_M4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.RASlz6s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.RASlh1b OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASl8dw.RASldlz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASljm5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall8ro.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require F_sy88u MRep MRepAux F_mm4hw RAlllfc RF_mx3o Malllim RF_muly.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASla24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASla24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require ASlot_M4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.F_sy88u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.F_mm4hw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mx3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malllim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_muly OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RF_m79e OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.ASlooxi OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASla24.RASlico OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASlku2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASla24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASl8dw.RASl99y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASljm5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASlxag OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.ASlojxo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.ASlo1am.

Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma slot_ok_N st g b r idx n N :
  slot_ok st g b r idx n -> get_stride (get_meta_rec st g) = N + 4 -> 0 <= N -> slot_ok st g b r idx N.
Proof.
  intros SO STR N0. destruct SO. constructor; try assumption; try lia.
  intros off O0 OF. apply so_q16; lia.
Qed.
Lemma outside_app' W1 W2 a : outside (W1 ++ W2) a <-> outside W1 a /\ outside W2 a.
Proof. induction W1 as [|[lo hi] W1 IH]; cbn; [tauto|]. rewrite IH. tauto. Qed.

End CEIL.
Lemma meta_slot_mono stA stB g :
  (forall a, is_Some ((s_areas stA) !! a) -> is_Some ((s_areas stB) !! a)) -> meta_slot stA g -> meta_slot stB g.
Proof.
  (intros HA; (first [ intro dR_5; dex3 dR_5 as ar arr kk; dand3 dR_5 as Ha Hk E | intro dR_5; dand6 dR_5 as ar arr kk Ha Hk E | intros (ar & arr & kk & Ha & Hk & E) ])). destruct (HA ar ltac:(rewrite Ha; eexists; reflexivity)) as [arr' Ha'].
  exists ar, arr', kk. auto.
Qed.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma arith_prog_dec a c s n : 0 < s ->
  (exists j, 0 <= j <= n /\ a = c + s * j) \/ (forall j, 0 <= j <= n -> a <> c + s * j).
Proof.
  intros Hs. destruct (Z.eq_dec ((a - c) mod s) 0) as [M0|M1].
  - pose proof (Z.div_mod (a - c) s ltac:(lia)) as DM. rewrite M0, Z.add_0_r in DM.
    destruct (Z_le_dec 0 ((a - c) / s)) as [L0|L0]; [destruct (Z_le_dec ((a - c) / s) n) as [L1|L1]|].
    + left. exists ((a - c) / s). split; [lia|]. lia.
    + right. intros j Hj E. assert ((a - c) / s = j) by (subst a; replace (c + s * j - c) with (j * s) by lia; rewrite Z_div_mult by lia; lia). lia.
    + right. intros j Hj E. assert ((a - c) / s = j) by (subst a; replace (c + s * j - c) with (j * s) by lia; rewrite Z_div_mult by lia; lia). lia.
  - right. intros j Hj E. apply M1. subst a. replace (c + s * j - c) with (j * s) by lia. apply Z_mod_mult.
Qed.
Section CEIL2.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Definition nreq (sc cnt1 : Z) : Z := UNIT + cnt1 * (UNIT * size_class sc) - IB.
Definition ncls (sc cnt1 : Z) : Z := size_to_class (nreq sc cnt1).
Lemma nest_class sc (SC : 0 <= sc < 48) cnt1 : 1 <= cnt1 <= 32 -> size_class sc * UNIT * cnt1 + UNIT <= 2048 ->
  nreq sc cnt1 = size_class sc * 16 * cnt1 + 12 /\ 0 <= ncls sc cnt1 <= 26 /\ 16 * size_class sc * cnt1 + 16 <= UNIT * size_class (ncls sc cnt1)
  /\ sc < ncls sc cnt1 /\ 0 <= nreq sc cnt1 < 2^32 /\ nreq sc cnt1 + 4 <= 16 * size_class (ncls sc cnt1).
Proof.
  intros C1 SM. pose proof (size_class_range sc SC) as SZR.
  assert (E : nreq sc cnt1 = size_class sc * 16 * cnt1 + 12) by (unfold nreq, UNIT, IB; lia).
  assert (QR : 1 <= size_class sc * cnt1 <= 127) by (unfold UNIT in SM; nia).
  pose proof (stc_q_eq (size_class sc) cnt1 SZR C1 ltac:(unfold UNIT in SM; lia)) as EJ.
  assert (EJ' : ncls sc cnt1 = stc_q (size_class sc * cnt1)) by (unfold ncls; rewrite E; exact EJ).
  destruct (nest_class_props (size_class sc * cnt1) QR) as [J1 J2]. rewrite <- EJ' in J1, J2.
  split; [exact E|]. split; [exact J1|]. split; [unfold UNIT; nia|].
  split.
  { destruct (Z_lt_le_dec sc (ncls sc cnt1)) as [L|GE]; [exact L|]. exfalso.
    destruct (Z.eq_dec (ncls sc cnt1) sc) as [EQ|NE]; [rewrite EQ in J2; nia|].
    pose proof (size_class_mono (ncls sc cnt1) sc ltac:(lia) ltac:(lia)). nia. }
  split; [lia|]. nia.
Qed.
Lemma conc_meta_stable' st stE m q : mrep st m -> mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof.
  (intros MR REL; (first [ intro dR_6; dex3 dR_6 as ar arr kk; dand3 dR_6 as Ha Hk -> | intro dR_6; dand6 dR_6 as ar arr kk Ha Hk -> | intros (ar & arr & kk & Ha & Hk & ->) ])). pose proof MR as (WF & _). (first [ pose proof (WF) as dR_1; dand5 dR_1 as _ _ _ WA _ | pose proof WF as (_ & _ & _ & WA & _) ]).
  (first [ pose proof ((WA ar arr Ha)) as dR_2; dex1 dR_2 as r; destruct dR_2 as [Hr _] | pose proof ((WA ar arr Ha)) as dR_2; dand3 dR_2 as r Hr _ | destruct (WA ar arr Ha) as (r & Hr & _) ]). (first [ pose proof ((mrel_regions _ _ REL _ _ Hr)) as dR_3; dex1 dR_3 as r'; dand4 dR_3 as Hr' _ B' _ | pose proof ((mrel_regions _ _ REL _ _ Hr)) as dR_3; dand5 dR_3 as r' Hr' _ B' _ | destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _) ]).
  unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

Lemma malloc_fp_widen st0 stA stB lo sp sp' a :
  sp' <= sp ->
  (forall rid r, (s_regions stA) !! rid = Some r ->
     exists r', (s_regions stB) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  malloc_fp st0 stA lo sp' a -> malloc_fp st0 stB lo sp a.
Proof.
  intros LE HR H. apply (malloc_fp_mono st0 stA stB lo sp a HR).
  destruct H as [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

(* [comment removed for export] *)
Lemma region_byte_raw st m rid r off v :
  mrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
  cell_read (get_shadow st rid) off = Known v -> m (wa (r_base r + off)) = Some (b8 v).
Proof.
  intros MR Hr Hk Ho Hc.
  destruct (mrep_shadow_read st m rid r off v MR Hr Hk Ho Hc) as [RD _].
  (first [ pose proof ((rregion_facts st m rid r MR Hr)) as dR_4; dand5 dR_4 as R4 RAL RC RI1 RI2 | destruct (rregion_facts st m rid r MR Hr) as (R4 & RAL & RC & RI1 & RI2) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
  cbn [ov_read_bytes] in RD.
  destruct (m (wa (r_base r + off))) as [b|] eqn:E.
  - cbn in RD. inversion RD. reflexivity.
  - rewrite p0_memory_read_none in RD; [discriminate| cbn; lia|]. rewrite wa_unsigned by lia. cbn. lia.
Qed.

End CEIL2.

Lemma errno_lit5 (tp : word) : tp = Z_to_bv 64 PTP -> errno_addr tp = 0x42454.
Proof. intros ->. unfold PTP. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section LEVEL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_okd (c_init_done (ctx st0)) m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK sc.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 PTP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  as_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  implT o (k st1 idx) s' Q ms'.
Let F0 : ISTF st LB := Mall8ro.ist_facts_proof st0 LB st AR IS.
(* [comment removed for export] *)
Definition rnest_regs (st2 : mstate) (mm : aptr) (cnt1 : Z) (a0v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) :=
  mkR (Z_to_bv 64 0x24444) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) (Z_to_bv 64 (conc st2 mm))
      a0v a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (ncls sc cnt1)) (wz cnt1)
      (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 (CTX + 80 + 8 * sc)) (Z_to_bv 64 MLOCK) (Z_to_bv 64 (MLOCK + 8 * sc))
      (wz (size_class sc * UNIT)) (Z_to_bv 64 SIZE_CLASSES) s10 s11 t3' t4' t5' t6'.

(* [comment removed for export] *)
Definition nest_ctx (st1 st2 : mstate) (mm : aptr) (cnt1 : Z) (st3 : mstate) (idx : Z)
    (m4 m'' : mem) (s' s'' : PState) (errv'' : word) (junk : list byte) (oo o3 : mem) : Prop :=
  ta_fail sc st st1 /\ ta_rel sc st st1 /\ active st1 sc = None /\
  leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) /\
  IST st0 st2 /\ ENTRY_REL st0 st2 /\ ALLC st2 /\
  am_rel st1 st2 (Some mm) /\ get_meta_rec st2 mm = meta0 /\ meta_slot st2 mm /\
  1 <= cnt1 <= 32 /\ size_class sc * UNIT * cnt1 + UNIT <= 2048 /\
  leaf_of o3 (alloc_slot full_lay f st2 (ncls sc cnt1) (nreq sc cnt1) kS bS) (Some (st3, idx)) /\
  mem_inv rsegs m'' /\ stk rsegs m'' lo (bv_unsigned sp - 144) /\
  rw_cells rsegs m'' (errno_addr tp) [C4 errv''] /\ auxv_okd (c_init_done (ctx st0)) m'' (bv_unsigned sp - 144) /\
  mrep st3 m'' /\ ticks_ok st3 /\ unk_agree st3 o m'' /\
  pres_except (malloc_fp st0 st3 lo (bv_unsigned sp - 144)) m4 m'' /\
  mrel st2 st3 /\ brk_link_ps st3 s'' /\ ps_m s'' = ps_m s /\ ps_fa s'' = ps_fa s /\ ps_so s'' = ps_so s /\
  as_inv2 st0 st2 st3 (ncls sc cnt1) idx /\ 0 <= c_mmap_counter (ctx st3) < 2^32 /\
  rw_cells rsegs m'' (bv_unsigned sp - 144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk) /\
  pres_except (malloc_fp st0 st2 lo (bv_unsigned sp)) m m4 /\ mrep st2 m4.

Definition NFAIL_stmt : Prop :=
  forall st1 st2 mm cnt1 st3 m4 m'' s' s'' errv'' junk oo o3 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  nest_ctx st1 st2 mm cnt1 st3 (-1) m4 m'' s' s'' errv'' junk oo o3 ->
  implT o (free_meta mm st3 (fun st4 => as_kq sc k bail st4 None) bail) s'' Q
    (MS (rnest_regs st2 mm cnt1 (Z_to_bv 64 (-1)) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6')
        F (Z_to_bv 64 0x244bc) fc None m'' (seg_rom rsegs)).

Definition NSUCC_stmt : Prop :=
  forall st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' junk oo o3 g3 b3 r3 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  nest_ctx st1 st2 mm cnt1 st3 idx m4 m'' s' s'' errv'' junk oo o3 ->
  0 <= idx -> active st3 (ncls sc cnt1) = Some g3 -> slot_ok st3 g3 b3 r3 idx (nreq sc cnt1) ->
  (forall a, r_base r3 + snd b3 + 16 + get_stride (get_meta_rec st3 g3) * idx - 4 <= a
             < r_base r3 + snd b3 + 16 + get_stride (get_meta_rec st3 g3) * idx + get_stride (get_meta_rec st3 g3) - 4 ->
     malloc_fp st0 st3 lo (bv_unsigned sp - 144) a) ->
  (s_regions st0 = ∅ -> rdv pans_mem o st3 (fst b3, snd b3 + (16 + get_stride (get_meta_rec st3 g3) * idx) + -3) = 0) ->
  implT o (ag_tail full_lay (upd_meta mm (m_set_maplen 0) (nest_layout st3 g3 idx (ncls sc cnt1) (UNIT * size_class sc) cnt1))
              sc mm (slot_of st3 g3 idx) cnt1 (cnt1 - 1) (as_kq sc k bail)) s'' Q
    (MS (rnest_regs st2 mm cnt1 (Z_to_bv 64 idx) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6')
        F (Z_to_bv 64 0x24448) fc None m'' (seg_rom rsegs)).
End LEVEL.
End RASltfw.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlh4s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASl8dw.RASldlz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlfjn.RASltfw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Malls02 Mallmv3 RAlllfc RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASla24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require ASlot_M4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.RASlz6s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.RASlh1b OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASla24.RASlico OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASl8dw.RASldlz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASljm5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASlxag OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlfjn.RASltfw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require F_sy88u MRep MRepAux F_mm4hw RAlllfc RF_mx3o Malllim RF_muly.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASla24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASla24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require ASlot_M4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require ASlot_M4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.F_sy88u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.F_mm4hw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mx3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malllim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_muly OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RF_m79e OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.ASlooxi OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASla24.RASlico OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASlku2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASla24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASl8dw.RASl99y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASljm5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASlxag OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.ASlojxo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.ASlo1am.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

Section LEVEL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_okd (c_init_done (ctx st0)) m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK sc.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 PTP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  as_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  implT o (k st1 idx) s' Q ms'.
Hypothesis IHf : alloc_slot_stmt2 f.

Hypothesis NFAIL : NFAIL_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Hypothesis NSUCC : NSUCC_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.

#[using="NSUCC NFAIL IHf TP LO CLO MR SC ER AR LB"] Lemma hnest_ok : HNEST_stmt f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Proof.
  clear A0 FIT RQ.
  intros st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CT C1R SMc.
  (first [ dand23 CT as TF TR ACT0 LF IS2 ER2 AC2 REL G0 MSL MR3 TK3 UA3 MI3 ST3 FR3 ERR3 AUX3 PE03 BL2 PSM PSF PSO | destruct CT as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & MR3 & TK3 & UA3 & MI3 & ST3 & FR3 & ERR3 & AUX3 & PE03 & BL2 & PSM & PSF & PSO) ]).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (AS_STACK_ge sc) as ASG. pose proof CLO as CLO'. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  pose proof (errno_lit5 tp TP) as EA.
  pose proof (size_class_range sc SC) as SZR.
  (first [ pose proof ((nest_class sc SC cnt1 C1R SMc)) as dR_2; dand6 dR_2 as ENR JR FITN SCJ NRR NFIT | destruct (nest_class sc SC cnt1 C1R SMc) as (ENR & JR & FITN & SCJ & NRR & NFIT) ]).
  pose proof (RAS_STACK_nest sc (ncls sc cnt1) SCJ ltac:(lia)) as RSN. pose proof (AS_STACK_ge (ncls sc cnt1)) as ASGj.
  unfold ag_nest. cbv zeta. fold (nreq sc cnt1). fold (ncls sc cnt1).
  (first [ pose proof ((meta_slot_bounds st2 m3 mm MR3 MSL)) as dR_3; dand4 dR_3 as Gpos GC GI _ | pose proof (meta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & GI & _) ]).
  unfold rcnt_state.
  (* [comment removed for export] *)
  iprefixT.
  eapply evt_cut.
  { replace (wz (size_class sc * UNIT * cnt1)) with (wz (size_class sc * 16 * cnt1)) by (unfold UNIT; reflexivity).
    eapply (nest_call_walk (size_class sc) cnt1 SZR C1R ltac:(unfold UNIT in SMc; lia)). exact MI3. }
  cbv beta. (intros ms'; (first [ intro dR_5; dand4 dR_5 as a2x a3x a4x -> | intros (a2x & a3x & a4x & ->) ])).
  replace (size_to_class (size_class sc * 16 * cnt1 + 12)) with (ncls sc cnt1) by (unfold ncls; rewrite ENR; reflexivity).
  replace (wz (size_class sc * 16 * cnt1 + 12)) with (wz (nreq sc cnt1)) by (rewrite ENR; reflexivity).
  apply evt_done.
  assert (AUX4 : auxv_okd (c_init_done (ctx st0)) m3 (bv_unsigned sp - 144)).
  { eapply auxv_okd_weaken; [exact AUX3| split; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia| lia]]. }
  set (sp' := Z_to_bv 64 (bv_unsigned sp + -144)).
  assert (SP' : bv_unsigned sp' = bv_unsigned sp - 144) by (subst sp'; rewrite unsigned_lit by lia; lia).
  eapply (alloc_slot_stmtL f IHf R _ bail o s' Q (Z_to_bv 64 0x24444) sp' gp tp) with (st0 := st0) (lo := lo) (sc := ncls sc cnt1) (req := nreq sc cnt1);
    rewrite ?SP'.
  - (* [comment removed for export] *) split; [exists LB; split; [exact AR| exact IS2]|]. split; [exact ER2|]. split; [exact AC2|]. split; [lia|]. split; [lia|]. exact NFIT.
  - exact MR3.
  - exact TK3.
  - exact UA3.
  - exact BL2.
  - exact AUX4.
  - replace (bv_unsigned sp - 144) with (bv_unsigned sp + -144) by lia. exact ST3.
  - exact CLO.
  - lia.
  - exact ERR3.
  - exact MI3.
  - exact TP.
  - reflexivity.
  - unfold wz. reflexivity.
  - (* [comment removed for export] *)
    intros st3 idx s'' ms'' PO LEAF.
    (first [ dex16 PO as u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 ut3 ut4 ut5 ut6 m'' errv''; dand17 PO as -> MI'' ST'' ERR'' AUX'' MR'' TK'' UA'' PE'' MREL'' BL'' PSM'' PSF'' PSO'' AI'' CTR'' RES | dand33 PO as u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 ut3 ut4 ut5 ut6 m'' errv'' -> MI'' ST'' ERR'' AUX'' MR'' TK'' UA'' PE'' MREL'' BL'' PSM'' PSF'' PSO'' AI'' CTR'' RES | destruct PO as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & ut3 & ut4 & ut5 & ut6 & m'' & errv'' & -> & MI'' & ST'' & ERR'' & AUX'' & MR'' & TK'' & UA'' & PE'' & MREL'' & BL'' & PSM'' & PSF'' & PSO'' & AI'' & CTR'' & RES) ]).
    rewrite ?SP' in *.
    (* [comment removed for export] *)
    assert (FR'' : rw_cells rsegs m'' (bv_unsigned sp - 144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk)).
    { eapply (frame_keep_ER st0 st m MR ER st3 m'' lo (bv_unsigned sp - 144) m3 m''); [exact MR''| exact PE''| | lia| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia].
      replace (bv_unsigned sp - 144) with (bv_unsigned sp + -144) by lia. exact FR3. }
    assert (PSM2 : ps_m s'' = ps_m s) by (etransitivity; [exact PSM''| exact PSM]).
    assert (PSF2 : ps_fa s'' = ps_fa s) by (etransitivity; [exact PSF''| exact PSF]).
    assert (PSO2 : ps_so s'' = ps_so s) by (etransitivity; [exact PSO''| exact PSO]).
    assert (NCX : nest_ctx f o s ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m st0 st lo sc st1 st2 mm cnt1 st3 idx m3 m'' s' s'' errv'' junk oo o) by (repeat (split; [assumption|]); assumption).
    cbv beta.
    assert (IR : -1 <= idx < 32).
    { destruct RES as [->|(I0 & g3 & b3 & r3 & HA3 & SO3 & _)]; [lia|]. pose proof (so_idx _ _ _ _ _ _ SO3). pose proof (so_li _ _ _ _ _ _ SO3). lia. }
    replace (ret_pc (Z_to_bv 64 0x24444)) with (Z_to_bv 64 0x24444) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    iprefixT. eapply evt_cut.
    { eapply (nest_ret_walk (Z_to_bv 64 0x24444) sp' gp tp) with (idx := idx); [exact IR| exact MI'']. }
    cbv beta. intros ms' ->. apply evt_done.
    replace sp' with (Z_to_bv 64 (bv_unsigned sp + -144)) by reflexivity.
    destruct RES as [->|(I0 & g3 & b3 & r3 & HA3 & SO3 & SPAN3 & RDV3)].
    + change (-1 <? 0) with true. change (-1 =? -1) with true. cbv iota.
      apply (NFAIL st1 st2 mm cnt1 st3 m3 m'' s' s'' errv'' junk oo o). exact NCX.
    + replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (idx =? -1) with false by (symmetry; apply Z.eqb_neq; lia). rewrite HA3. cbv iota beta.
      apply (NSUCC st1 st2 mm cnt1 st3 idx m3 m'' s' s'' errv'' junk oo o g3 b3 r3); [exact NCX| exact I0| exact HA3| exact SO3| exact SPAN3| exact RDV3].
Qed.
End LEVEL.