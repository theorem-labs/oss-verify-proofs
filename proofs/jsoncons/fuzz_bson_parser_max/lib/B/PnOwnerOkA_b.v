(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA HeapIfaceABx L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmModel PmModelFacts.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnModelFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnOwnerFactsA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia := try match goal with H : PNM.bvec_at _ _ _ _ _ _ _ _ |- _ => clear H end; Stdlib.micromega.Lia.lia.
Local Ltac mod8 H := match goal with |- (?o + ?c) mod 8 = 0 => let q := eval vm_compute in (Z.div c 8) in
  replace (o + c) with (o + q * 8) by lia; rewrite Z_mod_plus_full; exact H end.

Module PNOKA.
Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.

Lemma in_pre {T} (l1 l2 : list T) b : In b l1 -> In b (l1 ++ l2).
Proof. intros H. apply in_or_app. left. exact H. Qed.
Lemma in_mid4 {T} (l1 l2 l3 l4 : list T) b : In b l3 -> In b (l1 ++ l2 ++ l3 ++ l4).
Proof. intros H. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact H. Qed.
Lemma aacc_sub (M : word -> option byte) a k a' k' : aacc M a k -> a <= a' -> a' + k' <= a + k -> aacc M a' k'.
Proof. intros H H1 H2 x Hx. apply H. lia. Qed.

Section OK.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable vp : Z.
Variables (L : asan_layout) (ar : asan_run) (HI : asan_iface).
Variables (op ois lo hi : Z) (s : PNM.bpst).
Abbreviation bparser_at := (PNM.bparser_at segs A accA annA vp).

Hypothesis WF : HAJ.rt_wfR L ar HI.
Hypothesis LAY : lo <= op /\ op + PNM.PSIZE <= hi /\ lo <= ois /\ ois + 272 <= hi /\ hi <= ar_sptop ar /\ hi <= 2 ^ 47
                 /\ op mod 8 = 0 /\ ois mod 8 = 0 /\ 4096 <= lo.
Hypothesis DIS : op + PNM.PSIZE <= ois \/ ois + 272 <= op.

(* [comment removed for export] *)
Definition src_ownerA : PGS.owner :=
  {| PGS.ow_at := fun M src OB => bparser_at M op ois (PNM.with_srcB s src) /\ OB = PNM.brest_own s;
     PGS.ow_os := op + PNM.OFF_SRC; PGS.ow_ois := ois; PGS.ow_lo := lo; PGS.ow_hi := hi;
     PGS.ow_win := fun M src OB p k => PNM.sso_win (op + PNM.OFF_NB) (PNM.b_nb s) p k \/ PNM.sso_win (op + PNM.OFF_TB) (PNM.b_tb s) p k
                                       \/ PNM.blk_win (PM.vs_own (PNM.b_nb s) ++ PM.vs_own (PNM.b_tb s)) p k |}.
Lemma winA_bwin M src OB p k : PGS.ow_win src_ownerA M src OB p k -> PNM.bwin op s p k.
Proof.
  cbn [src_ownerA PGS.ow_win]. intros [H|[H|(B & m & Hin & R)]]; [left; exact H| right; left; exact H|].
  right; right. exists B, m. split; [apply in_or_app; right; exact Hin| exact R].
Qed.

(* [comment removed for export] *)
Section Call.
Variables (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (Aw : list (Z * Z)) (M : word -> option byte) (V : vml) (sp scr : Z).
Hypothesis HH : ri_inv HI LB FF LK cr Aw M V.
Hypothesis OFR : PGSA.ofr FF lo hi.
Let WFB := proj1 (WF LB FF LK cr Aw M V HH).
Let WFF := proj1 (proj2 (WF LB FF LK cr Aw M V HH)).
Let WFS := proj1 (proj2 (proj2 (WF LB FF LK cr Aw M V HH))).

Lemma blk_factsA b : In b LB -> 0 < snd b /\ fst b mod 16 = 0 /\ app_mem (fst b) (snd b).
Proof. intros Hin. destruct (WFB b Hin) as ((R0 & R1 & R2 & R3 & R4 & R5) & _). split; [exact R3|]. split; [exact R2| exact R5]. Qed.
Lemma frame_factsA : app_mem lo (hi - lo) /\ (forall b, In b LB -> PNOFA.apart (fst b) (snd b) lo (hi - lo))
  /\ (forall LB' a, lo <= a < hi -> aclient L ar LB' FF sp scr a /\ aclient L ar LB' FF sp scr (S a)).
Proof.
  destruct OFR as (f & Hf & F1 & F2). destruct (WFF f Hf) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6). pose proof WFS as APP.
  destruct LAY as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). unfold PNM.PSIZE in *.
  split; [| split].
  - destruct APP as (P0 & P1 & P2). unfold app_mem. lia.
  - intros b Hb. destruct (WFB b Hb) as (_ & _ & _ & _ & _ & _ & FS). unfold PNOFA.apart. lia.
  - intros LB' a Ha. split.
    + unfold aclient, aclient_g. right; right; right; left. exists f. split; [exact Hf|]. lia.
    + unfold aclient, aclient_g. do 5 right. left. exists f. split; [exact Hf|]. unfold in_shadow_of. split; apply PNOFA.S_mono; lia.
Qed.
Lemma blk_apartA b1 b2 : In b1 LB -> In b2 LB -> fst b1 <> fst b2 -> PNOFA.apart (fst b1) (snd b1) (fst b2) (snd b2).
Proof.
  intros H1 H2 NE. destruct (WFB b1 H1) as (_ & _ & _ & _ & BA & _).
  destruct b2 as (B2 & m2). cbn [fst snd] in *. unfold PNOFA.apart.
  pose proof (BA (B2, m2) (L5C.in_lb_remove_neq (fst b1) B2 m2 LB H2 ltac:(lia))) as H. cbn [fst snd] in H. lia.
Qed.
Lemma nodup_preA (l1 l2 : list (Z * Z)) : LB = l1 ++ l2 -> List.NoDup (map fst l1).
Proof.
  intros E. pose proof (WF LB FF LK cr Aw M V HH) as X. do 10 apply proj2 in X. destruct X as (ND & _). rewrite E, map_app in ND.
  apply NoDup_ListNoDup in ND. exact (NoDup_app_remove_r _ _ ND).
Qed.
End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem src_owner_ok : PGSA.owner_ok segs A L ar HI src_ownerA.
Proof.
  destruct LAY as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
  constructor.
  - intros M src OB ((_ & D & _ & _ & _ & _ & _ & NI & SRC & _) & _). cbn [src_ownerA PGS.ow_os PGS.ow_ois].
    cbn [PNM.with_srcB PNM.b_src] in SRC. split; [exact SRC|]. split; [exact NI|].
    intros i Hi. unfold PNM.PSIZE, PNM.OFF_SRC in *. replace (op + 16 + i) with (op + (16 + i)) by lia. apply D. lia.
  - cbn [src_ownerA PGS.ow_lo PGS.ow_os PGS.ow_ois PGS.ow_hi]. unfold PNM.OFF_SRC, PNM.PSIZE in *.
    repeat split; try lia; mod8 L6.
  - intros LBX sp scr Wx M M' src src' OB FF LK Aw cr VM OFR HOW HH FA FB FC HP HSRC HQC.
    cbn [src_ownerA PGS.ow_at PGS.ow_lo PGS.ow_os PGS.ow_ois PGS.ow_hi PGS.ow_win] in *.
    destruct HOW as (HPA & EOB). subst OB. split; [|reflexivity].
    pose proof (frame_factsA _ FF LK cr Aw M VM sp scr HH OFR) as (FAPP & FAB & FFR).
    eapply (PNOFA.src_owner_upd segs A vp L ar LBX FF sp scr Wx M M' op ois lo hi s src src'); try eassumption.
    + repeat split; lia.
    + intros a Ha. exact (FFR _ a Ha).
    + intros b Hb. exact (blk_factsA _ FF LK cr Aw M VM HH b Hb).
    + intros b Hin. apply FAB. rewrite app_assoc. apply in_pre. exact Hin.
    + eapply nodup_preA; [exact HH|]. apply app_assoc.
    + intros b1 b2 H1 H2 NE. eapply (blk_apartA _ FF LK cr Aw M VM HH); [| |exact NE]; rewrite app_assoc; apply in_pre; assumption.
    + eapply Forall_impl; [|exact FC]. intros r Hr. unfold PNOFA.apart.
      destruct Hr as [(Ha & Hb & Hc)|Hw]; [left| right; exact (winA_bwin M src [] _ _ Hw)]. split; [lia|]. split; [| exact Hc].
      intros b Hin. destruct b as (B & m). cbn [fst snd]. exact (Hb B m Hin).
  - intros M src OB p k ((_ & D & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & NB & TB & _) & EOB) Hw.
    cbn [src_ownerA PGS.ow_win PGS.ow_os PGS.ow_ois PGS.ow_lo PGS.ow_hi] in *.
    cbn [PNM.with_srcB PNM.b_bb PNM.b_nb PNM.b_tb] in BB, NB, TB.
    unfold PNM.sso_win, PNM.blk_win in Hw. unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_NB, PNM.OFF_TB in *.
    destruct Hw as [((n & En) & K0 & W1 & W2)|[((n & En) & K0 & W1 & W2)|(B & m & Hin & K0 & W1 & W2)]].
    + split; [exact K0|]. split; [| split].
      * intros i Hi. replace (p + i) with (op + (p - op + i)) by lia. apply D. lia.
      * right. unfold PM.CHUNK. repeat split; lia.
      * destruct NB as (_ & C & _). apply (aacc_sub M _ _ p k C); lia.
    + split; [exact K0|]. split; [| split].
      * intros i Hi. replace (p + i) with (op + (p - op + i)) by lia. apply D. lia.
      * right. unfold PM.CHUNK. repeat split; lia.
      * destruct TB as (_ & C & _). apply (aacc_sub M _ _ p k C); lia.
    + split; [exact K0|]. split; [| split].
      * apply in_app_or in Hin. destruct Hin as [Hin|Hin].
        -- destruct (PNM.b_nb s) as [n0|c0 n0 q0]; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as E1 E2. subst q0 c0.
           destruct NB as (_ & _ & _ & _ & _ & _ & _ & _ & DB & _). intros i Hi. replace (p + i) with (B + (p - B + i)) by lia. apply DB. lia.
        -- destruct (PNM.b_tb s) as [n0|c0 n0 q0]; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as E1 E2. subst q0 c0.
           destruct TB as (_ & _ & _ & _ & _ & _ & _ & _ & DB & _). intros i Hi. replace (p + i) with (B + (p - B + i)) by lia. apply DB. lia.
      * left. subst OB. exists B, m. split; [|lia]. unfold PNM.brest_own. apply in_or_app. right. apply in_or_app. right. exact Hin.
      * apply in_app_or in Hin. destruct Hin as [Hin|Hin].
        -- destruct (PNM.b_nb s) as [n0|c0 n0 q0]; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as E1 E2. subst q0 c0.
           destruct NB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB). apply (aacc_sub M _ _ p k CB); lia.
        -- destruct (PNM.b_tb s) as [n0|c0 n0 q0]; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as E1 E2. subst q0 c0.
           destruct TB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB). apply (aacc_sub M _ _ p k CB); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem txt_owner_ok : PGSA.towner_ok segs A L ar HI (PNM.txt_owner segs A accA annA vp op ois lo hi s).
Proof.
  destruct LAY as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
  constructor.
  - intros M src tb tg OB ((_ & D & _ & _ & _ & _ & _ & NI & SRC & _ & _ & _ & _ & TB & _) & TOK & EOB).
    cbn [PNM.txt_owner PGS.tw_os PGS.tw_ois PGS.tw_otb]. cbn [PNM.with_src_tb PNM.b_src PNM.b_tb] in SRC, TB.
    split; [exact SRC|]. split; [exact NI|]. split; [|split; [exact TB| exact TOK]].
    intros i Hi. unfold PNM.PSIZE, PNM.OFF_SRC in *. replace (op + 16 + i) with (op + (16 + i)) by lia. apply D. lia.
  - cbn [PNM.txt_owner PGS.tw_lo PGS.tw_os PGS.tw_ois PGS.tw_otb PGS.tw_hi]. unfold PNM.OFF_SRC, PNM.OFF_TB, PNM.PSIZE in *.
    repeat split; try lia; mod8 L6.
  - intros LBX sp scr Wx M M' src src' tb tb' tg tg' OB FF LK Aw cr VM OFR HAT HH FA FB FC HP HSRC HQC HTB HTOK.
    cbn [PNM.txt_owner PGS.tw_at PGS.tw_lo PGS.tw_os PGS.tw_ois PGS.tw_otb PGS.tw_hi] in OFR, HH, FA, FB, FC, HP, HSRC, HQC, HTB.
    pose proof HAT as (_ & _ & EOB).
    pose proof (frame_factsA _ FF LK cr Aw M VM sp scr HH OFR) as (FAPP & FAB & FFR).
    eapply (PNOFA.txt_owner_upd segs A vp L ar LBX OB FF sp scr Wx M M' op ois lo hi (op + PNM.OFF_TB) s); try eassumption.
    + repeat split; lia.
    + left; reflexivity.
    + intros a Ha. exact (FFR _ a Ha).
    + intros b Hb. apply (blk_factsA _ FF LK cr Aw M VM HH b). apply in_or_app; right; apply in_or_app; right; exact Hb.
    + intros b Hin. apply FAB. apply in_mid4. exact Hin.
    + eapply Forall_impl; [|exact FC]. intros r (Ha & Hb & Hc). unfold PNOFA.apart. split; [lia|]. split; [| exact Hc].
      intros b Hin. destruct b as (B & m). cbn [fst snd]. exact (Hb B m Hin).
    + reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem vec_owner_ok : PGV8A.vowner_ok segs A L ar HI (PNM.vec_owner segs A accA annA vp op ois lo hi s).
Proof.
  destruct LAY as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
  constructor.
  - intros M src x g OB ((_ & D & _ & _ & _ & _ & _ & NI & SRC & _ & _ & BB & _ & _ & _) & VOK & EOB).
    cbn [PNM.vec_owner PGV8.vw_os PGV8.vw_ois PGV8.vw_ov]. cbn [PNM.with_src_bb PNM.b_src PNM.b_bb] in SRC, BB.
    split; [exact SRC|]. split; [exact NI|]. split; [|split; [exact BB| exact VOK]].
    intros i Hi. unfold PNM.PSIZE, PNM.OFF_SRC in *. replace (op + 16 + i) with (op + (16 + i)) by lia. apply D. lia.
  - cbn [PNM.vec_owner PGV8.vw_lo PGV8.vw_os PGV8.vw_ois PGV8.vw_ov PGV8.vw_hi]. unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.PSIZE in *.
    repeat split; try lia; mod8 L6.
  - intros LBX sp scr Wx M M' src src' x x' g g' OB FF LK Aw cr VM OFR HAT HH FA FB FC HP HSRC HQC HBB HVOK.
    cbn [PNM.vec_owner PGV8.vw_at PGV8.vw_lo PGV8.vw_os PGV8.vw_ois PGV8.vw_ov PGV8.vw_hi] in OFR, HH, FA, FB, FC, HP, HSRC, HQC, HBB.
    pose proof HAT as (_ & _ & EOB).
    pose proof (frame_factsA _ FF LK cr Aw M VM sp scr HH OFR) as (FAPP & FAB & FFR).
    eapply (PNOFA.vec_owner_upd segs A vp L ar LBX OB FF sp scr Wx M M' op ois lo hi (op + PNM.OFF_BB) s); try eassumption.
    + repeat split; lia.
    + right; reflexivity.
    + intros a Ha. exact (FFR _ a Ha).
    + intros b Hb. apply (blk_factsA _ FF LK cr Aw M VM HH b). apply in_or_app; right; apply in_or_app; right; exact Hb.
    + intros b Hin. apply FAB. apply in_mid4. exact Hin.
    + eapply Forall_impl; [|exact FC]. intros r (Ha & Hb & Hc). unfold PNOFA.apart. split; [lia|]. split; [| exact Hc].
      intros b Hin. destruct b as (B & m). cbn [fst snd]. exact (Hb B m Hin).
    + reflexivity.
Qed.

End OK.
End PNOKA.
