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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG PrintfModel PrintfModelX CtSizes CtWire CtTime.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac W_bio_push W_bio_write W_bio_printf W_prefix_create W_asn1_string.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import PrnTimeIface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeDefs TimeKit TimeKit2 W_posix_to_tm W_gmtime W_tm_to_posix W_gmtime_adj W_time_from_tm.
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

Ltac klia := try match goal with K : forall q s' ms', _ -> implM _ _ _ _ _ |- _ => clear K end; lia.

(* [comment removed for export] *)
Definition GENTIME_ADJ_STACK : Z := 112 + FROM_TM_STACK.

Lemma p2tm_cells_size : forall v, cells_size (p2tm_cells v) = 56%nat.
Proof. intros v. unfold p2tm_cells. destruct (utc_from_posix v); reflexivity. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition adj_front_post (sp gp tp s0 s1 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (G ts : Z) (ra x9 x18 x19 x20 : word) : machine_state -> Prop :=
  fun ms' => exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 sp (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 (ts_sec ts)) (Z_to_bv 64 (bv_unsigned sp + -112)) (Z_to_bv 64 (ts_day ts)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 (match gentime_adj ts with Some _ => 0x12d4c8 | None => 0x12d4d8 end)) fc None m' (seg_rom ctusegs)
    /\ (gentime_adj ts = None -> a0 = Z_to_bv 64 0)
    /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp + -112)
    /\ rw_cells ctusegs m' (bv_unsigned sp + -112)
         (match gentime_adj ts with Some t => tm_cells t | None => p2tm_cells (ts_day ts * SECS_PER_DAY + ts_sec ts) end
          ++ [C8 (Z_to_bv 64 0); C8 x20; C8 x19; C8 x18; C8 x9; C8 s0; C8 ra]).

Lemma gentime_adj_front : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo G ts : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 192 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < 2^63 ->
  0 <= ts < 2^64 -> 0 <= G < 2^64 ->
  a0 = Z_to_bv 64 G -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 (ts_day ts) -> a3 = Z_to_bv 64 (ts_sec ts) ->
  evt ctusegs (adj_front_post sp gp tp s0 s1 s5 s6 s7 s8 s9 s10 s11 F fc lo m G ts ra s1 s2 s3 s4)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 GENTIME_ADJ) fc None m (seg_rom ctusegs)).
Proof.
  intros until ts. intros ST MI GLO LO SP16 SP63 TSR GR -> -> -> ->.
  unfold GENTIME_ADJ, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (ts_day_range ts) as DR. pose proof (ts_sec_range ts) as SR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  (* [comment removed for export] *)
  carve_frame 112%nat ST. do 8 step. do 3 step. step. do 3 step.
  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) =>
    pose proof (proj1 (rw_cells_app _ _ [c0] (c1 :: rest)) FR) as [HD FR1]; clear FR;
    pose proof (proj1 (rw_cells_app _ _ [c1] rest) FR1) as [HT FRH]; clear FR1 end.
  cbn [cells_size csize Nat.add] in HT, FRH.
  replace (bv_unsigned sp + -112 + Z.of_nat 56) with (bv_unsigned sp + -56) in HT by lia.
  replace (bv_unsigned sp + -112 + Z.of_nat 56 + Z.of_nat 8) with (bv_unsigned sp + -48) in FRH by lia.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; lia).
  name_mem m1. eapply evt_cut.
  { lazymatch type of HD with rw_cells _ _ _ [CB _ ?j] =>
    eapply (OPENSSL_gmtime_spec _ (Z_to_bv 64 (bv_unsigned sp + -112))) with (lo := lo) (tv := 0) (D := bv_unsigned sp + -112) (TP := bv_unsigned sp + -56) (junk := j) end;
      rewrite ?ESP; [exact ST| exact MI| unfold GLOBALS_TOP; lia| unfold OPENSSL_GMTIME_STACK; lia| lia| lia| exact HD| lia| lia
                    | clear - SP16; Z.div_mod_to_equations; lia| apply ro_of_rw; exact HT| lia| reflexivity| reflexivity]. }
  intros ms' PO; unfold gmtime_post, OPENSSL_GMTIME_STACK in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctusegs m1. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -112) |- _ => rename H into ST2 end.
  match goal with H : rw_cells ctusegs _ (bv_unsigned sp + -112) (p2tm_cells 0) |- _ => rename H into HD2 end.
  unfold p2tm_ret in *. rewrite utc_from_posix_0 in *. cbn [Z.eqb] in *. unfold p2tm_cells in HD2. rewrite utc_from_posix_0 in HD2.
  name_mem m2.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. try clear K0.
  step.
  (* [comment removed for export] *)
  Local Ltac fin GA HDx HT FRH :=
    apply evt_done; unfold adj_front_post; rewrite GA;
    do 16 eexists; eexists; split; [reflexivity|];
    split; [first [discriminate | intros _; reflexivity]|];
    split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
    lazymatch goal with |- rw_cells _ ?mx _ _ =>
      apply (proj2 (rw_cells_app mx _ _ _)); split; [exact HDx|];
      lazymatch goal with |- rw_cells _ _ ?A (?c :: ?rest) =>
        apply (proj2 (rw_cells_app mx A [c] rest)); split;
        [ lazymatch type of HT with rw_cells _ _ ?AH _ => replace A with AH by (rewrite ?p2tm_cells_size; cbn; lia) end; exact HT
        | lazymatch type of FRH with rw_cells _ _ ?AF _ => lazymatch goal with |- rw_cells _ _ ?A2 _ => replace A2 with AF by (rewrite ?p2tm_cells_size; cbn; lia) end end; exact FRH ] end end.
  (* [comment removed for export] *)
  Local Ltac adj_call dv sv HD2 ESP :=
    do 3 step; step;
    lazymatch type of ESP with bv_unsigned (Z_to_bv 64 ?q) = _ =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      eapply evt_cut;
      [ eapply (OPENSSL_gmtime_adj_spec _ (Z_to_bv 64 q)) with (d := dv) (sec := sv) (A := q);
        rewrite ?ESP; [eassumption| eassumption| unfold GLOBALS_TOP; lia| unfold OPENSSL_GMTIME_ADJ_STACK; lia
                      | lazymatch goal with H : bv_unsigned _ mod 16 = 0 |- _ => clear - H; Z.div_mod_to_equations; lia end| lia| lia| lia
                      | lazymatch goal with H : bv_unsigned _ mod 16 = 0 |- _ => clear - H; Z.div_mod_to_equations; lia end
                      | exact HD2| lia| lia| reflexivity| first [reflexivity| congruence]| reflexivity]
      | intros ms'' PO'; unfold OPENSSL_GMTIME_ADJ_STACK in PO'; rewrite ?ESP in PO'; revert ms'' PO'; post_call ctusegs mx; rewrite ?ESP in * ]
    end end.
  destruct (Z.eq_dec (ts_day ts) 0) as [D0|DN].
  - (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1; [exfalso; first [apply K1; rewrite D0; reflexivity | lia]|]. try clear K1.
    destruct (Z.eq_dec (ts_sec ts) 0) as [S0|SN].
    + (* [comment removed for export] *)
      step. if_cases K2; zify_cond K2; [| exfalso; first [apply K2; rewrite S0; reflexivity | lia]]. try clear K2.
      assert (GA : gentime_adj ts = Some epoch_tm) by (unfold gentime_adj; rewrite D0, S0; reflexivity).
      fin GA HD2 HT FRH.
    + step. if_cases K2; zify_cond K2; [exfalso; first [rewrite ?unsigned_lit in K2 by lia; lia | lia]|]. try clear K2.
      adj_call 0 (ts_sec ts) HD2 ESP.
      match goal with H : rw_cells ctusegs _ (bv_unsigned sp + -112) (p2tm_cells _) |- _ => rename H into HD3 end.
      assert (GA : gentime_adj ts = utc_from_posix (0 * 86400 + ts_sec ts)).
      { unfold gentime_adj, SECS_PER_DAY. rewrite D0. replace (ts_sec ts =? 0) with false by (symmetry; apply Z.eqb_neq; exact SN). reflexivity. }
      unfold p2tm_ret. unfold p2tm_cells in HD3.
      destruct (utc_from_posix (0 * 86400 + ts_sec ts)) as [t|] eqn:UV.
      * step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. try clear K3. fin GA HD3 HT FRH.
      * step. if_cases K3; zify_cond K3; [| exfalso; apply K3; reflexivity]. try clear K3.
        lazymatch type of HD3 with rw_cells _ ?mm ?A _ =>
          assert (HD3' : rw_cells ctusegs mm A (p2tm_cells (ts_day ts * SECS_PER_DAY + ts_sec ts)))
            by (unfold p2tm_cells, SECS_PER_DAY; rewrite D0, UV; exact HD3) end.
        fin GA HD3' HT FRH.
  - (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1; [| exfalso; revert K1; clear - DR DN; intros K1; rewrite ?land64 in K1; Z.to_euclidean_division_equations; lia]. try clear K1.
    adj_call (ts_day ts) (ts_sec ts) HD2 ESP.
    match goal with H : rw_cells ctusegs _ (bv_unsigned sp + -112) (p2tm_cells _) |- _ => rename H into HD3 end.
    assert (GA : gentime_adj ts = utc_from_posix (ts_day ts * 86400 + ts_sec ts)).
    { unfold gentime_adj, SECS_PER_DAY. replace (ts_day ts =? 0) with false by (symmetry; apply Z.eqb_neq; exact DN). reflexivity. }
    unfold p2tm_ret. unfold p2tm_cells in HD3.
    destruct (utc_from_posix (ts_day ts * 86400 + ts_sec ts)) as [t|] eqn:UV.
    * step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|]. try clear K3. fin GA HD3 HT FRH.
    * step. if_cases K3; zify_cond K3; [| exfalso; apply K3; reflexivity]. try clear K3.
      lazymatch type of HD3 with rw_cells _ ?mm ?A _ =>
        assert (HD3' : rw_cells ctusegs mm A (p2tm_cells (ts_day ts * SECS_PER_DAY + ts_sec ts)))
          by (unfold p2tm_cells, SECS_PER_DAY; rewrite UV; exact HD3) end.
      fin GA HD3' HT FRH.
Qed.

(* [comment removed for export] *)
Lemma agree_of_heap_pres_but : forall LB SP X m m',
  rheap_pres_but LB SP X m m' -> agree_on (fun a => rclient_addr LB SP a /\ ~ (fst X <= a < snd X)) m m'.
Proof. intros LB SP X m m' H a Ha [Hc NX]. exact (H a Ha Hc NX). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gentime_adj_fail : gentime_adj_fail_stmt GENTIME_ADJ_STACK.
Proof.
  unfold gentime_adj_fail_stmt. intros until canary. intros ST MI GLO LO SP16 SP63 SSP TP FRM HG SEPG TSR GA -> -> -> ->. subst tp.
  unfold GENTIME_ADJ_STACK, FROM_TM_STACK, ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, GENTIME_ADJ, MallocRep.wz in *.
  pose proof (rw_cells_bound _ _ _ _ HG) as GB. cbn [cells_size csize Nat.add asn1_string_cells] in GB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  eapply evt_cut.
  { eapply gentime_adj_front with (lo := lo) (G := G) (ts := ts); [exact ST| exact MI| exact GLO| lia| exact SP16| lia| lia| lia| reflexivity| reflexivity| reflexivity| reflexivity]. }
  intros ms' PO. unfold adj_front_post in PO. rewrite GA in PO.
  destruct PO as (x1 & r5 & r6 & r7 & a0' & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m1 & -> & A0 & MU & WM & MI1 & ST1 & FR).
  rewrite (A0 eq_refl). clear A0.
  (* [comment removed for export] *)
  pose proof (proj1 (rw_cells_app m1 _ _ _) FR) as [HD FRS]. clear FR. rewrite p2tm_cells_size in FRS.
  destruct (rw_cells_forget _ _ _ _ HD) as [junk HDJ]. clear HD. rewrite p2tm_cells_size in HDJ.
  replace (bv_unsigned sp + -112 + Z.of_nat 56) with (bv_unsigned sp + -112 + Z.of_nat (cells_size [CB 56%nat junk])) in FRS by reflexivity.
  pose proof (proj2 (rw_cells_app m1 _ _ _) (conj HDJ FRS)) as FR. clear HDJ FRS. cbn [app] in FR.
  (* [comment removed for export] *)
  do 6 step. step. release_frame FR ST1 (bv_unsigned sp).
  step. apply evt_done. unfold gentime_leaf_post, MallocRep.wz.
  do 14 eexists. exists m1. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1| exact ST1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Proofs.
  Hypothesis HM : rmalloc_stmt.

  Lemma gentime_adj_ok : gentime_adj_ok_stmt GENTIME_ADJ_STACK.
  Proof using HM.
    unfold gentime_adj_ok_stmt. intros until Q.
    intros HEAP AUX SPB SP63 ST CEIL GLO LO SP16 ERR MI TP CS RS SSP FRM HGIN HG TSR GA -> -> -> -> KN K. subst tp.
    unfold GENTIME_ADJ_STACK, FROM_TM_STACK, ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, GENTIME_ADJ, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    pose proof (LH_block_range _ _ _ _ HEAP HGIN) as (BB0 & BB1 & BB2 & BB3 & BB4). cbn [blk_addr blk_size fst snd] in BB0, BB1, BB2, BB3, BB4.
    unfold GLOBALS_TOP in GLO.
    unfold implM. iprefix.
    eapply evt_cut.
    { eapply gentime_adj_front with (lo := lo) (G := G) (ts := ts);
        [exact ST| exact MI| unfold GLOBALS_TOP; klia| klia| exact SP16| klia| klia| klia
        | reflexivity| reflexivity| reflexivity| reflexivity]. }
    intros ms' PO. unfold adj_front_post in PO. rewrite GA in PO.
    destruct PO as (x1 & r5 & r6 & r7 & a0' & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m1 & -> & _ & MU & WM & MI1 & ST1 & FR).
    pose proof (proj1 (rw_cells_app m1 _ _ _) FR) as [HD FRS]. clear FR. cbn [cells_size csize Nat.add tm_cells] in FRS.
    replace (bv_unsigned sp + -112 + Z.of_nat 56) with (bv_unsigned sp + -56) in FRS by klia.
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG1.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; klia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. klia. }
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [exact AG1| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. klia. }
    assert (RS1 : realloc_statics m1).
    { destruct RS as [RSa RSb]. unfold realloc_statics, CR_GOT_MALLOC, CR_REALLOC_IMPL in *.
      split; (eapply ro_cells_agree; [exact AG1| eassumption| intros a Ha; cbn; cbn in Ha; split; [klia| exact I]]). }
    assert (SSP1 : ssp_cells m1 canary).
    { eapply ssp_cells_agree; [exact AG1| | exact SSP]. intros a Ha. unfold ssp_addr, got_ssp, ssp_guard in Ha. cbn. split; [klia| exact I]. }
    assert (ERR1 : rw_cells ctusegs m1 LX_ERRNO [C4 errv]).
    { eapply rw_cells_agree; [exact AG1| exact ERR|]. intros a Ha. unfold LX_ERRNO, RATP in Ha. cbn in Ha |- *. split; [klia| exact I]. }
    assert (HG1 : rw_cells ctusegs m1 G (asn1_string_cells 0 V_ASN1_GENERALIZEDTIME 0 0)).
    { eapply rw_cells_agree; [exact AG1| exact HG|]. intros a Ha. unfold asn1_string_cells in Ha. cbn in Ha |- *. split; [klia| exact I]. }
    clear AG1 CS RS SSP ERR HG.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -112)) = bv_unsigned sp + -112) by (apply unsigned_lit; klia).
    (* [comment removed for export] *)
    do 3 step. step.
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (ossl_asn1_time_from_tm_walk HM) with (B := B) (lo := lo) (errv := errv) (canary := canary) (gb := gb) (t := t) (TS := bv_unsigned sp + -112);
      rewrite ?ESP;
      [ exact HEAP1 | exact AUX1 | klia | klia | exact ST1 | exact CEIL | unfold GLOBALS_TOP; klia
      | unfold FROM_TM_STACK, ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; klia
      | exact ERR1 | exact MI1 | reflexivity | exact CS1 | exact RS1 | exact SSP1 | exact FRM
      | exact HGIN | exact HG1
      | apply ro_of_rw; exact HD | exact (gentime_adj_valid _ _ GA) | klia | klia | clear - SP16; Z.div_mod_to_equations; lia
      | reflexivity | reflexivity | reflexivity | exact KN | ].
    intros p st1 ms1 PO. unfold gentime_adj_post in PO. rewrite ?ESP in PO.
    destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & Ft & fc' & m2 & D & errv2 & junk4
                    & -> & FRM2 & FREG & MI2 & ST2 & SSP2 & ERR2 & AUX2 & HP & FA & SO & BR & HEAP2 & HG2 & HD2 & JL).
    replace (ret_pc (Z_to_bv 64 1234136)) with (Z_to_bv 64 1234136) by (symmetry; apply ret_pc_even; [klia| reflexivity]).
    (* [comment removed for export] *)
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres_but _ _ _ _ _ HP)) in FRS;
      [| intros a Ha; cbn [fst snd]; cbn in Ha; split; [left; klia| klia]].
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres_but _ _ _ _ _ HP)) in HD;
      [| intros a Ha; cbn [fst snd]; cbn in Ha; split; [left; klia| klia]].
    replace (bv_unsigned sp + -56) with (bv_unsigned sp + -112 + Z.of_nat (cells_size (tm_cells t))) in FRS by (cbn; klia).
    pose proof (proj2 (rw_cells_app m2 _ _ _) (conj HD FRS)) as FR. clear HD FRS. cbn [app tm_cells] in FR.
    eapply implM_evt with (P := gentime_adj_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F canary s L lo B m G t p st1);
      [| intros ms' PO'; apply K; exact PO'].
    clear K.
    (* [comment removed for export] *)
    do 6 step. step. release_frame FR ST2 (bv_unsigned sp).
    step. apply evt_done. unfold gentime_adj_post, MallocRep.wz.
    do 14 eexists. exists Ft, fc', m2, D, errv2, junk4. split; [reflexivity|].
    split; [exact FRM2|]. split; [exact FREG|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact SSP2|].
    split; [exact ERR2|]. split; [exact AUX2|].
    split. { intros a Ha Hc NX. cbn [fst snd] in NX.
             assert (E1 : m1 (wa a) = m (wa a) /\ (wview ctusegs m (wa a) <> None -> wview ctusegs m1 (wa a) <> None)).
             { split; [| intros Hv; apply WM; exact Hv]. apply MU. unfold wa. rewrite unsigned_lit by klia. cbn. split; [| exact I].
               apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [klia| klia|].
               pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). klia. }
             assert (E2 : m2 (wa a) = m1 (wa a) /\ (wview ctusegs m1 (wa a) <> None -> wview ctusegs m2 (wa a) <> None)).
             { apply (HP a Ha); [| cbn [fst snd]; exact NX]. destruct Hc as [Hc|Hc]; [left; klia| right; exact Hc]. }
             destruct E1 as [E1 V1], E2 as [E2 V2]. split; [congruence| auto]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact BR|]. split; [exact HEAP2|]. split; [exact HG2|]. split; [exact HD2| exact JL].
  Qed.
End Proofs.

End WithCeiling0.
