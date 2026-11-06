(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PmModel PmSpecs PgSrc PgV8
     PnModel PnModelFacts PnOwnerFacts.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNOK.

Lemma in_mid {T} (l1 l2 l3 : list T) b : In b l2 -> In b (l1 ++ l2 ++ l3).
Proof. intros H. apply in_or_app. right. apply in_or_app. left. exact H. Qed.
Lemma in_pre {T} (l1 l2 : list T) b : In b l1 -> In b (l1 ++ l2).
Proof. intros H. apply in_or_app. left. exact H. Qed.
Lemma in_mid4 {T} (l1 l2 l3 l4 : list T) b : In b l3 -> In b (l1 ++ l2 ++ l3 ++ l4).
Proof. intros H. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact H. Qed.

Section OK.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable vp : Z.
Variable L : heap_layout.
Variable HI : heap_iface.
Variables (op ois lo hi : Z) (s : PNM.bpst).

Hypothesis WF : heap_blocks_wf L HI.
Hypothesis ERR : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L /\ hl_img_hi L <= hl_ceil L.
Hypothesis TOP : hl_sptop L <= 2 ^ 47.
Hypothesis LAY : hl_ceil L <= lo /\ lo <= op /\ op + PNM.PSIZE <= hi /\ lo <= ois /\ ois + 272 <= hi /\ hi <= hl_sptop L
                 /\ op mod 8 = 0 /\ ois mod 8 = 0 /\ 4096 <= lo.
Hypothesis DIS : op + PNM.PSIZE <= ois \/ ois + 272 <= op.

(* [comment removed for export] *)
Lemma blk_facts LB cr M VM b : hi_heap HI LB cr M VM -> In b LB ->
  PNOF.apart (fst b) (snd b) lo (hi - lo) /\ (fst b + snd b <= hl_errno L \/ hl_errno L + 4 <= fst b)
  /\ 0 <= fst b /\ 0 <= snd b /\ fst b + snd b <= 2 ^ 64.
Proof.
  intros HH Hin. pose proof (proj1 (WF LB cr M VM HH) b Hin) as ((R0 & R1 & R2 & R3 & R4) & _ & _).
  unfold PNOF.apart. destruct LAY as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). destruct ERR as (E0 & E1 & E2).
  repeat split; lia.
Qed.

Lemma blk_apart LB cr M VM b1 b2 : hi_heap HI LB cr M VM -> In b1 LB -> In b2 LB -> fst b1 <> fst b2 ->
  PNOF.apart (fst b1) (snd b1) (fst b2) (snd b2).
Proof.
  intros HH H1 H2 NE. pose proof (proj1 (WF LB cr M VM HH) b1 H1) as (_ & _ & BA).
  destruct b2 as (B2 & m2). cbn [fst snd] in *. unfold PNOF.apart.
  pose proof (BA (B2, m2) (L5C.in_lb_remove_neq (fst b1) B2 m2 LB H2 ltac:(lia))) as H. cbn [fst snd] in H. lia.
Qed.

Lemma nodup_pre (l1 l2 : list (Z * Z)) LB cr M VM : hi_heap HI LB cr M VM -> LB = l1 ++ l2 -> List.NoDup (map fst l1).
Proof.
  intros HH E. pose proof (proj1 (proj2 (WF LB cr M VM HH))) as ND. rewrite E, map_app in ND.
  apply NoDup_ListNoDup in ND. exact (NoDup_app_remove_r _ _ ND).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem src_owner_ok : PGS.owner_ok segs A L HI (PNM.src_owner segs A PMSP.T3 PMSP.T4 vp op ois lo hi s).
Proof.
  destruct LAY as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
  constructor.
  - intros M src OB H. exact (PNOF.src_owner_src segs A vp op ois lo hi s M src OB H).
  - cbn [PNM.src_owner PGS.ow_lo PGS.ow_os PGS.ow_ois PGS.ow_hi]. unfold PNM.OFF_SRC, PNM.PSIZE in *.
    repeat split; try lia.
  - intros LBX sp scr Wx M M' src src' OB cr VM Hsp HOW HH FA FB FC HP HSRC HQC.
    cbn [PNM.src_owner PGS.ow_at PGS.ow_lo PGS.ow_os PGS.ow_ois PGS.ow_hi PGS.ow_win] in *.
    destruct HOW as (HPA & EOB). subst OB. split; [|reflexivity].
    eapply (PNOF.src_owner_upd segs A vp L LBX sp scr Wx M M' op ois lo hi s src src'); try eassumption; try lia.
    + intros b Hin. eapply blk_facts; [exact HH|]. rewrite app_assoc. apply in_pre. exact Hin.
    + eapply nodup_pre; [exact HH|]. apply app_assoc.
    + intros b1 b2 H1 H2 NE. eapply blk_apart; [exact HH| | |exact NE]; rewrite app_assoc; apply in_pre; assumption.
    + eapply Forall_impl; [|exact FC]. intros r Hr. unfold PNOF.apart.
      destruct Hr as [(Ha & Hb)|Hw]; [left|right; exact Hw]. split; [lia|].
      intros b Hin. destruct b as (B & m). cbn [fst snd]. exact (Hb B m Hin).
  - intros M src OB p k HAT HW. eapply PNOF.src_owner_win; [| exact DIS| exact HAT| exact HW]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem txt_owner_ok : PGS.towner_ok segs A L HI (PNM.txt_owner segs A PMSP.T3 PMSP.T4 vp op ois lo hi s).
Proof.
  destruct LAY as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
  constructor.
  - intros M src tb tg OB ((_ & D & _ & _ & _ & _ & _ & NI & SRC & _ & _ & _ & _ & TB & _) & TOK & EOB).
    cbn [PNM.txt_owner PGS.tw_os PGS.tw_ois PGS.tw_otb]. cbn [PNM.with_src_tb PNM.b_src PNM.b_tb] in SRC, TB.
    split; [exact SRC|]. split; [exact NI|]. split; [|split; [exact TB| exact TOK]].
    intros i Hi. unfold PNM.PSIZE, PNM.OFF_SRC in *. replace (op + 16 + i) with (op + (16 + i)) by lia. apply D. lia.
  - cbn [PNM.txt_owner PGS.tw_lo PGS.tw_os PGS.tw_ois PGS.tw_otb PGS.tw_hi]. unfold PNM.OFF_SRC, PNM.OFF_TB, PNM.PSIZE in *.
    repeat split; try lia.
  - intros LBX sp scr Wx M M' src src' tb tb' tg tg' OB cr VM Hsp HAT HH FA FB FC HP HSRC HQC HTB HTOK.
    cbn [PNM.txt_owner PGS.tw_at PGS.tw_lo PGS.tw_os PGS.tw_ois PGS.tw_otb PGS.tw_hi] in Hsp, HH, FA, FB, FC, HP, HSRC, HQC, HTB.
    pose proof HAT as (_ & _ & EOB).
    eapply (PNOF.txt_owner_upd segs A vp L LBX OB sp scr Wx M M' op ois lo hi (op + PNM.OFF_TB) s); try eassumption; try lia.
    + intros b Hin. eapply blk_facts; [exact HH|]. apply in_mid4. exact Hin.
    + eapply Forall_impl; [|exact FC]. intros r (Ha & Hb). unfold PNOF.apart. split; [lia|].
      intros b Hin. destruct b as (B & m). cbn [fst snd]. exact (Hb B m Hin).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem vec_owner_ok : PGV8.vowner_ok segs A L HI (PNM.vec_owner segs A PMSP.T3 PMSP.T4 vp op ois lo hi s).
Proof.
  destruct LAY as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
  constructor.
  - intros M src x g OB ((_ & D & _ & _ & _ & _ & _ & NI & SRC & _ & _ & BB & _ & _ & _) & VOK & EOB).
    cbn [PNM.vec_owner PGV8.vw_os PGV8.vw_ois PGV8.vw_ov]. cbn [PNM.with_src_bb PNM.b_src PNM.b_bb] in SRC, BB.
    split; [exact SRC|]. split; [exact NI|]. split; [|split; [exact BB| exact VOK]].
    intros i Hi. unfold PNM.PSIZE, PNM.OFF_SRC in *. replace (op + 16 + i) with (op + (16 + i)) by lia. apply D. lia.
  - cbn [PNM.vec_owner PGV8.vw_lo PGV8.vw_os PGV8.vw_ois PGV8.vw_ov PGV8.vw_hi]. unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.PSIZE in *.
    repeat split; try lia.
  - intros LBX sp scr Wx M M' src src' x x' g g' OB cr VM Hsp HAT HH FA FB FC HP HSRC HQC HBB HVOK.
    cbn [PNM.vec_owner PGV8.vw_at PGV8.vw_lo PGV8.vw_os PGV8.vw_ois PGV8.vw_ov PGV8.vw_hi] in Hsp, HH, FA, FB, FC, HP, HSRC, HQC, HBB.
    pose proof HAT as (_ & _ & EOB).
    eapply (PNOF.vec_owner_upd segs A vp L LBX OB sp scr Wx M M' op ois lo hi (op + PNM.OFF_BB) s); try eassumption; try lia.
    + intros b Hin. eapply blk_facts; [exact HH|]. apply in_mid4. exact Hin.
    + eapply Forall_impl; [|exact FC]. intros r (Ha & Hb). unfold PNOF.apart. split; [lia|].
      intros b Hin. destruct b as (B & m). cbn [fst snd]. exact (Hb B m Hin).
Qed.

End OK.
End PNOK.
