(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RRealloc_iface RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG PrintfModel PrintfModelX CtSizes CtWire CtTime.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib F_memcpy F_vsnprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac F_strlen W_bio_push W_bio_write W_bio_printf W_prefix_create W_asn1_string W_crypto_realloc.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import PrnTimeIface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeDefs TimeKit TimeKit2 TimeFmtPure TimeToTmDefs W_crypto_realloc3 W_asn1_string_copy
     W_time_to_tm_A W_time_to_tm.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

Ltac klia := try match goal with K : forall p s' ms', _ -> implM _ _ _ _ _ |- _ => clear K end; lia.

(* [comment removed for export] *)
Definition GENTIME_SETSTR_STACK : Z := 64 + ASN1_STRING_COPY_STACK.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma ro_of_rw : forall m A cs, rw_cells ctusegs m A cs -> ro_cells ctusegs m A cs.
Proof. intros m A cs [H _]. exact H. Qed.
Lemma agree_of_heap_pres_but : forall LB SP X m m',
  rheap_pres_but LB SP X m m' -> agree_on (fun a => rclient_addr LB SP a /\ ~ (fst X <= a < snd X)) m m'.
Proof. intros LB SP X m m' H a Ha [Hc NX]. exact (H a Ha Hc NX). Qed.

Lemma genstr_len : forall ts, length (zb (genstr ts)) = if printable ts then 19%nat else 11%nat.
Proof. intros ts. unfold zb. rewrite length_map. apply genstr_length. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gentime_setstr_fail : gentime_setstr_fail_stmt GENTIME_SETSTR_STACK.
Proof.
  unfold gentime_setstr_fail_stmt. intros until canary. intros ST MI GLO LO SP16 SP63 SSP TP FRM PR TSR HGS GSLO GSHI -> ->. subst tp.
  unfold GENTIME_SETSTR_STACK, ASN1_STRING_COPY_STACK, CRYPTO_REALLOC_NN_STACK, RREALLOC_STACK, GENTIME_SET_STRING, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  unfold GLOBALS_TOP in GLO. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (genstr_len ts) as GL. rewrite PR in GL.
  assert (TL : length gtail = 8%nat).
  { destruct HGS as [[[WF _] _] _]. cbn in WF. rewrite length_app in WF. cbn [length] in WF. rewrite GL in WF. lia. }
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  (* [comment removed for export] *)
  carve_frame 64%nat ST. do 6 step. do 5 step.
  name_mem m1. eapply evt_cut.
  { eapply strlen_spec with (str := zb (genstr ts)) (slack := gtail); rewrite ?unsigned_lit by lia;
      [ destruct HGS as [[_ B] _]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B; exact B
      | apply genstr_nonul
      | rewrite GL, TL; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; pose proof (Z.mod_pos_bound (- (GS + 11 + 1)) 8 ltac:(lia)); lia
      | exact MI ]. }
  intros ms' PO; unfold strlen_post in PO; revert ms' PO. post_call ctusegs m1. rewrite GL. cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  name_mem m2.
  (* [comment removed for export] *)
  step. zstep. step. if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia]. try clear K0.
  do 5 step. step. step. step.
  (* [comment removed for export] *)
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST2 end.
  lazymatch type of FR with rw_cells _ ?mx _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
    pose proof (proj1 (rw_cells_app mx _ [c0] (c1 :: c2 :: c3 :: rest)) FR) as [FRa FRb];
    pose proof (proj1 (rw_cells_app mx _ [c1; c2; c3] rest) FRb) as [FRt FRc] end.
  cbn [cells_size csize Nat.add] in FRt, FRc.
  replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) in FRt by lia.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  name_mem m3. eapply evt_cut.
  { eapply (t2t_reject _ (Z_to_bv 64 (bv_unsigned sp + -64))) with (lo := lo) (l := 11) (DA := bv_unsigned sp + -56) (GS := GS) (tm := 0); rewrite ?ESP;
      [ exact ST2 | assumption | unfold GLOBALS_TOP; lia | unfold TIME_TO_TM_STACK; lia | lia
      | apply ro_of_rw; exact FRt | lia | lia | lia | clear - SP16; Z.div_mod_to_equations; lia | lia | lia | reflexivity | reflexivity ]. }
  clear FRt. intros ms' PO; unfold t2t_leaf_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctusegs m3. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST4 end.
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; [| exfalso; apply K1; reflexivity]. try clear K1.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    replace (bv_unsigned sp + -56) with (bv_unsigned sp + -64 + Z.of_nat (cells_size [CB 8%nat (firstn 8 (firstn 16 (firstn 24 (firstn 32 junk))))])) in FRb by (cbn; lia);
    pose proof (proj2 (rw_cells_app mx _ _ _) (conj FRa FRb)) as FR2 end.
  clear FRa FRb FRc. cbn [app] in FR2.
  do 4 step. step. release_frame FR2 ST4 (bv_unsigned sp). step.
  name_mem m5. apply evt_done. unfold gentime_leaf_post, MallocRep.wz.
  do 14 eexists. exists m5. split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [assumption| exact ST4].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ASN1_STRING_COPY_eq : ASN1_STRING_COPY = 0xfde44. Proof. reflexivity. Qed.

Lemma gentime_setstr_ok : gentime_setstr_ok_stmt GENTIME_SETSTR_STACK.
Proof.
  unfold gentime_setstr_ok_stmt. intros until Q.
  intros HEAP AUX SPB B63 ST CEIL GLO LO SP16 ERR MI TP CS RS FRM HGIN HDIN NE HG HD PR TSR HGS GSLO GSB GSAL -> -> KN K. subst tp.
  unfold GENTIME_SETSTR_STACK, ASN1_STRING_COPY_STACK, CRYPTO_REALLOC_NN_STACK, RREALLOC_STACK, GENTIME_SET_STRING, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
  unfold GLOBALS_TOP in GLO. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
  pose proof (LH_block_range _ _ _ _ HEAP HGIN) as (BB0 & BB1 & BB2 & BB3 & BB4). cbn [blk_addr blk_size fst snd] in BB0, BB1, BB2, BB3, BB4.
  pose proof (LH_block_range _ _ _ _ HEAP HDIN) as (BD0 & BD1 & BD2 & BD3 & BD4). cbn [blk_addr blk_size fst snd] in BD0, BD1, BD2, BD3, BD4.
  pose proof (genstr_len ts) as GL. rewrite PR in GL.
  assert (TL : gtail = []).
  { destruct HGS as [[[WF _] _] _]. cbn in WF. rewrite length_app in WF. cbn [length] in WF. rewrite GL in WF. destruct gtail; [reflexivity| cbn in WF; lia]. }
  subst gtail.
  destruct (gentime_adj ts) as [t|] eqn:GA; [| unfold printable in PR; rewrite GA in PR; discriminate].
  pose proof (gentime_adj_valid ts t GA) as TV. pose proof (ts_ms_range ts) as MSR.
  unfold asn1_string_cells, MallocRep.wz in HG.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  unfold implM. iprefix.
  (* [comment removed for export] *)
  carve_frame 64%nat ST. do 6 step. do 5 step.
  name_mem m1. eapply evt_cut.
  { eapply strlen_spec with (str := zb (genstr ts)) (slack := []); rewrite ?unsigned_lit by klia;
      [ destruct HGS as [[_ BY] _]; cbn [cells_bytes cbytes app] in BY; rewrite app_nil_r in BY; exact BY
      | apply genstr_nonul
      | rewrite GL; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; replace (- (GS + 19 + 1)) with ((- (GS + 20) / 8) * 8) by (clear - GSAL; Z.to_euclidean_division_equations; lia);
        rewrite Z.mod_mul by lia; lia
      | exact MI ]. }
  intros ms' PO; unfold strlen_post in PO; revert ms' PO. post_call ctusegs m1. rewrite GL. cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  name_mem m2.
  (* [comment removed for export] *)
  step. zstep. step. if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by klia; klia]. try clear K0.
  do 5 step. step. step. step.
  (* [comment removed for export] *)
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST2 end.
  lazymatch type of FR with rw_cells _ ?mx _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
    pose proof (proj1 (rw_cells_app mx _ [c0] (c1 :: c2 :: c3 :: rest)) FR) as [FRa FRb];
    pose proof (proj1 (rw_cells_app mx _ [c1; c2; c3] rest) FRb) as [FRt FRc] end.
  cbn [cells_size csize Nat.add] in FRt, FRc.
  replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) in FRt by klia.
  replace (bv_unsigned sp + -64 + Z.of_nat 8 + Z.of_nat 16) with (bv_unsigned sp + -40) in FRc by klia.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (HGC : rw_cells ctusegs mx GS (gcells t (ts_ms ts) ++ [C1 (Z_to_bv 8 0)])) end.
  { eapply rw_cells_recast; [exact HGS| |].
    - unfold gcells, zb8. cbn. tauto.
    - rewrite cells_bytes_app, <- (genstr_gcells ts t GA). unfold zb. cbn [cells_bytes cbytes app map]. rewrite app_nil_r. reflexivity. }
  pose proof (proj1 (rw_cells_app _ _ _ _) HGC) as [HGC1 _].
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; klia).
  name_mem m3. eapply evt_cut.
  { eapply (time_to_tm_check_spec _ (Z_to_bv 64 (bv_unsigned sp + -64))) with (lo := lo) (DA := bv_unsigned sp + -56) (GS := GS) (t := t) (ms := ts_ms ts); rewrite ?ESP;
      [ exact ST2 | assumption | unfold GLOBALS_TOP; klia | unfold TIME_TO_TM_STACK; klia | klia
      | apply ro_of_rw; exact FRt | klia | klia | klia | clear - SP16; Z.div_mod_to_equations; lia | apply ro_of_rw; exact HGC1 | klia | klia | klia | exact TV | klia | reflexivity | reflexivity ]. }
  clear HGC HGC1. intros ms' PO; unfold t2t_leaf_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctusegs m3. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST4 end. name_mem m4.
  (* [comment removed for export] *)
  lazymatch type of FRc with rw_cells _ ?mx _ (?c0 :: ?rest) =>
    pose proof (proj1 (rw_cells_app mx _ [c0] rest) FRc) as [FRf FRs] end.
  cbn [cells_size csize Nat.add] in FRs. replace (bv_unsigned sp + -40 + Z.of_nat 8) with (bv_unsigned sp + -32) in FRs by klia.
  replace (bv_unsigned sp + -40) with (bv_unsigned sp + -56 + Z.of_nat (cells_size [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS)])) in FRf by (cbn; klia).
  pose proof (proj2 (rw_cells_app m4 _ _ _) (conj FRt FRf)) as FRst. cbn [app] in FRst. clear FRt FRf FRc.
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by klia; klia|]. try clear K1.
  step. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by klia; klia|]. try clear K2.
  step. step. step.
  (* [comment removed for export] *)
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG4.
  assert (HEAP4 : RHEAP s L m4).
  { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; klia| constructor]. }
  assert (AUX4 : rauxv_ok m4 B).
  { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. klia. }
  assert (RS4 : realloc_statics m4).
  { destruct RS as [RSa RSb]. unfold realloc_statics, CR_GOT_MALLOC, CR_REALLOC_IMPL in *.
    split; (eapply ro_cells_agree; [exact AG4| eassumption| intros a Ha; cbn; cbn in Ha; split; [klia| exact I]]). }
  rename ERR into ERR4. rename HD into HD4.
  assert (HG4 : rw_cells ctusegs m4 G (asn1_string_cells 15 V_ASN1_GENERALIZEDTIME D 0)) by (unfold asn1_string_cells, MallocRep.wz; exact HG).
  assert (HGS4 : bytes_at ctusegs m4 GS (zb (genstr ts))).
  { destruct HGS as [[_ BY] _]. cbn [cells_bytes cbytes app] in BY. rewrite app_nil_r in BY. apply bytes_at_app in BY. destruct BY as [BY _]. exact BY. }
  clear AG4 CS RS HG HGS.
  ihere.
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
  eapply ASN1_STRING_copy_walk with (B := B) (lo := lo) (errv := errv) (gb := gb) (dl := 15) (ty0 := V_ASN1_GENERALIZEDTIME) (n0 := 20)
                                    (ty := 24) (GS := GS) (STR := bv_unsigned sp + -56) (old := djunk) (src := zb (genstr ts));
    rewrite ?ESP;
    [ exact HEAP4 | exact AUX4 | klia | exact ST4 | exact CEIL | unfold GLOBALS_TOP; klia
    | unfold ASN1_STRING_COPY_STACK, CRYPTO_REALLOC_NN_STACK, RREALLOC_STACK; klia
    | unfold LX_ERRNO, RATP; exact ERR4 | assumption | reflexivity | exact RS4
    | exact HGIN | exact HDIN | exact NE
    | exact HG4 | klia | klia | exact HD4 | klia | klia
    | unfold asn1_string_cells, MallocRep.wz; apply ro_of_rw; exact FRst | klia | klia | clear - SP16; Z.div_mod_to_equations; lia | unfold V_ASN1_GENERALIZEDTIME; klia
    | exact HGS4 | rewrite GL; reflexivity | klia | klia
    | reflexivity | reflexivity | exact KN | ].
  intros st1 ms1 PO. unfold ascopy_post in PO. rewrite ?ESP in PO.
  destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m5 & errv5
                  & -> & MI5 & ST5 & ERR5 & AUX5 & HP5 & FA5 & SO5 & ES5 & HEAP5 & HG5 & HD5). subst st1.
  replace (ret_pc (Z_to_bv 64 1233992)) with (Z_to_bv 64 1233992) by (symmetry; apply ret_pc_even; [klia| reflexivity]).
  pose proof (agree_of_heap_pres_but _ _ _ _ _ HP5) as AG5.
  apply (rw_cells_agree _ _ _ _ _ AG5) in FRa; [| intros a Ha; cbn [fst snd]; cbn in Ha; split; [left; klia| klia]].
  apply (rw_cells_agree _ _ _ _ _ AG5) in FRst; [| intros a Ha; cbn [fst snd]; cbn in Ha; split; [left; klia| klia]].
  apply (rw_cells_agree _ _ _ _ _ AG5) in FRs; [| intros a Ha; cbn [fst snd]; cbn in Ha; split; [left; klia| klia]].
  (* [comment removed for export] *)
  replace (bv_unsigned sp + -32) with (bv_unsigned sp + -56 + Z.of_nat (cells_size [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 GS); C8 (Z_to_bv 64 0)])) in FRs by (cbn; klia).
  pose proof (proj2 (rw_cells_app m5 _ _ _) (conj FRst FRs)) as FRb2. cbn [app] in FRb2. clear FRst FRs.
  lazymatch type of FRa with rw_cells _ _ _ ?ca =>
    replace (bv_unsigned sp + -56) with (bv_unsigned sp + -64 + Z.of_nat (cells_size ca)) in FRb2 by (cbn; klia) end.
  pose proof (proj2 (rw_cells_app m5 _ _ _) (conj FRa FRb2)) as FR5. clear FRa FRb2. cbn [app] in FR5.
  eapply implM_evt with (P := gentime_setstr_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L lo B m G D dp ts dp s);
    [| intros ms' PO'; apply K; exact PO'].
  clear K.
  (* [comment removed for export] *)
  unfold MallocRep.wz.
  step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. try clear K3.
  step. do 4 step. step. release_frame FR5 ST5 (bv_unsigned sp). step.
  name_mem m6. apply evt_done. unfold gentime_setstr_post, MallocRep.wz.
  do 14 eexists. exists m6, errv5. split; [reflexivity|].
  split; [exact MI5|]. split; [exact ST5|]. split; [unfold LX_ERRNO, RATP; change (3355176 - 164) with 3355012; exact ERR5|]. split; [exact AUX5|].
  split. { intros a Ha Hc NX. cbn [fst snd] in NX.
           assert (E1 : m4 (wa a) = m (wa a) /\ (wview ctusegs m (wa a) <> None -> wview ctusegs m4 (wa a) <> None)).
           { split; [| intros Hv; apply WM; exact Hv]. apply MU. unfold wa. rewrite unsigned_lit by lia. cbn. split; [| exact I].
             apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
             apply lb_remove_incl in Hb'. pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). lia. }
           assert (E2 : m6 (wa a) = m4 (wa a) /\ (wview ctusegs m4 (wa a) <> None -> wview ctusegs m6 (wa a) <> None)).
           { apply (HP5 a Ha); [| cbn [fst snd]; exact NX]. destruct Hc as [Hc|Hc]; [left; lia| right; exact Hc]. }
           destruct E1 as [E1 V1], E2 as [E2 V2]. split; [congruence| auto]. }
  split; [exact FA5|]. split; [exact SO5|]. split; [exact HEAP5|]. split; [exact HG5|]. change (Z.to_nat 19) with 19%nat in HD5. exact HD5.
Qed.

End WithCeiling0.
