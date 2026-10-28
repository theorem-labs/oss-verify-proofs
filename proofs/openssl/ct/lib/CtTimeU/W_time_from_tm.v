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
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_ctfmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib F_pop_arg F_printf_iface F_vsnprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac W_bio_push W_bio_write W_bio_printf W_prefix_create W_asn1_string W_snprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import PrnTimeIface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeDefs TimeKit TimeKit2 W_posix_to_tm TimeFmtPure TimeFmt W_snprintf6.
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

(* [comment removed for export] *)
Ltac klia := try match goal with K : forall q s' ms', _ -> implM _ _ _ _ _ |- _ => clear K end; lia.
Ltac nchk := let C := fresh "C" in if_cases C; [exfalso; zify_cond C; rewrite ?land64, ?Z.mod_small in C by klia; klia | clear C].
Ltac achk H := let C := fresh "C" in if_cases C;
  [exfalso; zify_cond C; change 7 with (Z.ones 3) in C; rewrite Z.land_ones in C by lia; change (2^3) with 8 in C; apply C; clear - H; Z.div_mod_to_equations; lia
  | clear C].

(* [comment removed for export] *)
Definition FROM_TM_STACK : Z := 64 + ASN1_STRING_SET_STACK.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.

  (* [comment removed for export] *)
  Lemma rheap_pres_but_of_remove : forall s L m0 m m' (gb : bptr) G q q',
    RHEAP s L m0 -> In (gb, G, 24) L -> rheap_pres (lb_remove gb L) q m m' -> q <= q' ->
    rheap_pres_but L q' (G, G + 24) m m'.
  Proof.
    intros s L m0 m m' gb G q q' HEAP HG HP LE a Ha Hc NX. cbn [fst snd] in NX. apply (HP a Ha).
    destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
    exists b. split; [| exact Hr]. apply lb_remove_In. split; [exact Hb|]. intros E.
    pose proof (LH_nodup _ _ _ HEAP) as ND. destruct b as [[p A] n]. cbn [blk_id fst snd] in E. subst p.
    pose proof (RH_addr_unique L gb A n G 24 ltac:(exact ND) Hb HG) as [-> ->]. cbn [blk_addr blk_size fst snd] in Hr. lia.
  Qed.

  Lemma ossl_asn1_time_from_tm_walk : forall {X : Type}
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv canary : word)
      (G TS : Z) (gb : bptr) (t : tm6)
      (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B -> bv_unsigned sp < 2^63 ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - FROM_TM_STACK ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP -> crypto_statics m -> realloc_statics m ->
    ssp_cells m canary -> frm0 fc ->
    In (gb, G, 24) L -> rw_cells ctusegs m G (asn1_string_cells 0 V_ASN1_GENERALIZEDTIME 0 0) ->
    ro_cells ctusegs m TS (tm_cells t) -> tm_valid t -> bv_unsigned sp <= TS -> TS + 56 <= 2^63 -> TS mod 8 = 0 ->
    a0 = wz G -> a1 = wz TS -> a2 = wz V_ASN1_GENERALIZEDTIME ->
    k None = LUnr ->
    (forall p s' ms', gentime_adj_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F canary s L lo B m G t p s' ms' ->
                     implM ctusegs (interp (k (Some p))) s' Q ms') ->
    implM ctusegs (interp (LMalloc 20 k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz OSSL_ASN1_TIME_FROM_TM) fc None m (seg_rom ctusegs)).
  Proof.
    intros until Q. intros HEAP AUX SPB SP63 ST CEIL GLO LO ERR MI -> CS RS SSP FRM HGIN HG HTM TV TSLO TSHI TSAL -> -> -> KN K.
    unfold FROM_TM_STACK, ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK, OSSL_ASN1_TIME_FROM_TM, GLOBALS_TOP, MallocRep.wz,
      V_ASN1_GENERALIZEDTIME in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. pose proof alloc_ceiling_range as ACR.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    pose proof (LH_block_range _ _ _ _ HEAP HGIN) as (BB0 & BB1 & BB2 & BB3 & BB4). cbn [blk_addr blk_size fst snd] in BB0, BB1, BB2, BB3, BB4.
    assert (SEPG : G + 24 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= G) by klia.
    assert (SEPT : TS + 56 <= bv_unsigned sp - 64 \/ bv_unsigned sp - 64 + 64 <= TS) by klia.
    unfold asn1_string_cells, MallocRep.wz in HG. unfold tm_cells in HTM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 64%nat ST. do 9 step. do 4 step.
    step. if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity]. try clear K0.
    do 3 step.
    step. if_cases K1; zify_cond K1; [| exfalso; klia]. try clear K1.
    (* [comment removed for export] *)
    do 4 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s L m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; klia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. klia. }
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG1.
    assert (CS1 : crypto_statics m1).
    { eapply crypto_statics_agree; [exact AG1| | exact CS].
      intros a Ha. cbn. split; [|exact I]. revert Ha. unfold libw, LIBW_bn. cbn [rin_ivs fst snd]. klia. }
    assert (RS1 : realloc_statics m1).
    { destruct RS as [RSa RSb]. unfold realloc_statics, CR_GOT_MALLOC, CR_REALLOC_IMPL in *.
      split; (eapply ro_cells_agree; [exact AG1| eassumption| intros a Ha; cbn; cbn in Ha; split; [klia| exact I]]). }
    assert (SSP1 : ssp_cells m1 canary).
    { eapply ssp_cells_agree; [exact AG1| | exact SSP]. intros a Ha. unfold ssp_addr, got_ssp, ssp_guard in Ha. cbn. split; [klia| exact I]. }
    clear CS RS SSP AG1.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; klia).
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr L (bv_unsigned sp) a -> outside [(bv_unsigned sp - 64, bv_unsigned sp)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [klia| klia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _). klia. }
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (ASN1_STRING_set1_data_nosrc_walk HM) with (B := B) (lo := lo) (errv := errv) (n := 20) (pblk := gb) (ty := 24);
      [exact HEAP1 | exact AUX1 | rewrite ESP; klia | rewrite ESP; exact ST | exact CEIL | unfold GLOBALS_TOP; klia
      | rewrite ESP; unfold ASN1_STRING_SET_STACK, CRYPTO_MALLOC_STACK, RMALLOC_STACK; klia
      | unfold LX_ERRNO, RATP; exact ERR | exact MI | reflexivity | exact CS1 | exact RS1
      | exact HGIN | unfold asn1_string_cells, MallocRep.wz; exact HG | klia | klia
      | reflexivity | reflexivity | reflexivity | klia | exact KN | ].
    intros p st1 ms1 PO. unfold oalloc_post in PO. rewrite ?ESP in PO.
    destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & C & errv2
                    & -> & MI2 & ST2 & ERR2 & AUX2 & HP & FA & SO & BR & HEAP2 & ((junkC & BLK) & HG2)).
    replace (ret_pc (Z_to_bv 64 1231352)) with (Z_to_bv 64 1231352) by (symmetry; apply ret_pc_even; [klia| reflexivity]).
    pose proof (agree_of_heap_pres _ _ _ _ HP) as AG2.
    apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; left; cbn in Ha; klia].
    apply (ro_cells_agree _ _ _ _ _ AG2) in HTM; [| intros a Ha; left; cbn in Ha; klia].
    assert (CAN : canary = rr_guard) by (eapply ssp_canary_0; [exact HEAP1| exact SSP1]).
    assert (SSP2 : ssp_cells m2 canary) by (rewrite CAN; eapply RHEAP_ssp; exact HEAP2).
    clear AG2 SSP1 CS1 RS1 AUX1 HEAP1 HG ST MI ERR.
    assert (JL : length junkC = 20%nat) by (destruct BLK as [[[WF _] _] _]; exact WF).
    pose proof (munch_refl [(lo, bv_unsigned sp); (G, G + 24); (C, C + 20)]%Z m2) as MU2. pose proof (wmono_refl ctusegs m2) as WM2.
    pose proof BR as (BC0 & BC16 & _ & BCC & BCI).
    assert (ND : List.NoDup (map blk_id ((p, C, 20) :: L))) by (eapply LH_nodup; exact HEAP2).
    assert (NEB : p <> gb).
    { intros E. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite E. apply in_map_iff. exists (gb, G, 24). split; [reflexivity| exact HGIN]. }
    pose proof (LH_disjoint _ _ _ (p, C, 20) (gb, G, 24) HEAP2 ltac:(left; reflexivity) ltac:(right; exact HGIN) NEB) as DJB.
    cbn [blk_addr blk_size blk_id fst snd] in DJB.
    assert (SEPC : C + 20 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= C) by klia.
    assert (SEPCT : C + 20 <= TS \/ TS + 56 <= C) by klia.
    unfold LX_ERRNO, RATP in ERR2. change (3355176 - 164) with 3355012 in ERR2.
    unfold asn1_string_cells, MallocRep.wz in HG2. change (Z.to_nat 20) with 20%nat in BLK.
    eapply implM_evt with (P := gentime_adj_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F canary s L lo B m G t p st1);
      [| intros ms' PO'; apply K; exact PO'].
    clear K.
    pose proof TV as (VY & VMO & VMD & VHH & VMI & VSS). pose proof (days_in_month_le31 (t_year t) (t_mon t)) as DM.
    (* [comment removed for export] *)
    unfold MallocRep.wz.
    step. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by klia; klia|]. try clear K2.
    step. step. achk BB1. step. step. nchk. step. step. achk TSAL.
    step. rewrite (sx32_small (t_mon t - 1)) by klia.
    step. step.
    step. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by klia; klia|]. try clear K3.
    (* [comment removed for export] *)
    step. step. rewrite (sx32_signed (t_year t - 1900)) by klia.
    step. if_cases K4; zify_cond K4; [exfalso; rewrite ?unsigned_lit in K4 by klia; klia|]. try clear K4.
    step. step. step. brF ltsz.
    (* [comment removed for export] *)
    step. rewrite (sx32_small (t_sec t)) by klia.
    step. rewrite (sx32_small (t_min t)) by klia.
    step. rewrite (sx32_small (t_hour t)) by klia.
    step. rewrite (sx32_small (t_mday t)) by klia.
    step. setreg 13%Z (Z_to_bv 64 (t_year t)) ltac:(f_equal; rewrite addiw_small by klia; klia).
    step. setreg 14%Z (Z_to_bv 64 (t_mon t)) ltac:(f_equal; rewrite addiw_small by klia; klia).
    step. step. step.
    (* [comment removed for export] *)
    step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?rest) =>
      pose proof (proj1 (rw_cells_app m3 _ [c0] rest) FR) as [HST FRH]; clear FR end.
    cbn [cells_size csize Nat.add] in FRH.
    assert (SSP3 : ssp_cells m3 canary).
    { eapply ssp_cells_agree; [apply (agree_on_of_munch _ _ _ MU2 WM2)| | exact SSP2].
      intros a Ha. unfold ssp_addr, got_ssp, ssp_guard in Ha. cbn. split; [klia|]. split; [klia|]. split; [klia| exact I]. }
    eapply evt_cut.
    { eapply (snprintf_gen_spec6 _ (Z_to_bv 64 (bv_unsigned sp + -64))) with (lo := lo) (D := C) (n := 20) (A := A_C17) (dn := 20%nat)
        (junkd := junkC) (canary := canary) (fmt := FMT_C17) (o := gen15 t)
        (args := [PA_i (t_year t); PA_i (t_mon t); PA_i (t_mday t); PA_i (t_hour t); PA_i (t_min t); PA_i (t_sec t)]);
      rewrite ?ESP;
      [ exact ST2 | exact MI2 | unfold GLOBALS_TOP; klia | unfold SNPRINTF_STACK, VSN_DEPTH; klia | klia
      | exact SSP3 | exact FRM
      | exact BLK | klia | unfold GLOBALS_TOP; klia | klia
      | rewrite gen15_zlength; klia | klia
      | exact HST
      | apply sng_C17; [exact MI2| unfold STATIC_SPLIT; klia| exact TV| rewrite unsigned_lit by klia; apply Z.mod_small; klia ..]
      | reflexivity | reflexivity | unfold A_C17; reflexivity ]. }
    post_call_esp ESP m3. rewrite ?ESP in *.
    match goal with H : stk ctusegs _ lo (bv_unsigned sp + -64) |- _ => rename H into ST4 end.
    match goal with H : frm0 _ |- _ => rename H into FRM4 end.
    match goal with H : forall k : reg, _ -> reg_get _ k = reg_get F k |- _ => rename H into FREG end.
    match goal with H : rw_cells ctusegs _ C _ |- _ => rename H into BLK4 end.
    match goal with H : mem_inv ctusegs _ |- _ => rename H into MI4 end.
    rewrite gen15_zlength. rewrite gen15_length in BLK4.
    (* [comment removed for export] *)
    step. step. if_cases K5; zify_cond K5; [| exfalso; klia]. try clear K5.
    step. step. step.
    (* [comment removed for export] *)
    replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -64 + Z.of_nat (cells_size [C8 (Z_to_bv 64 (t_sec t))])) in FRH by (cbn; klia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (proj2 (rw_cells_app mx _ [C8 (Z_to_bv 64 (t_sec t))] _) (conj HST FRH)) as FR end.
    clear HST FRH. cbn [app] in FR.
    do 7 step. step. release_frame FR ST4 (bv_unsigned sp). step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    apply evt_done. unfold gentime_adj_post, MallocRep.wz.
    assert (HEAP5 : RHEAP st1 ((p, C, 20) :: L) m5).
    { eapply LH_frame; [exact HEAP2| exact MU2| exact WM2|].
      constructor; [apply W_ok_stack; cbn; klia|].
      constructor; [eapply (W_ok_block _ (gb, G, 24)); [right; exact HGIN| cbn; klia| cbn; klia]|].
      constructor; [eapply (W_ok_block _ (p, C, 20)); [left; reflexivity| cbn; klia| cbn; klia]| constructor]. }
    do 14 eexists. eexists. eexists. exists m5, C. eexists. exists (skipn 16 junkC). split; [reflexivity|].
    split; [exact FRM4|]. split; [exact FREG|]. split; [exact MI4|]. split; [assumption|].
    split; [rewrite CAN; eapply RHEAP_ssp; exact HEAP5|].
    split; [unfold LX_ERRNO, RATP; change (3355176 - 164) with 3355012; eassumption|].
    split. { eapply rauxv_ok_frame; [exact AUX2| exact MU2| exact WM2|].
             constructor; [cbn; unfold RAUXV_CELL; klia|]. constructor; [cbn; unfold RAUXV_CELL; klia|]. constructor; [cbn; unfold RAUXV_CELL; klia| constructor]. }
    split. { (* [comment removed for export] *)
      intros a Ha Hc NX. cbn [fst snd] in NX.
      assert (E1 : m1 (wa a) = m (wa a) /\ (wview ctusegs m (wa a) <> None -> wview ctusegs m1 (wa a) <> None)).
      { apply (heap_pres_of_munch _ _ _ _ _ MU WM CLI a Ha Hc). }
      assert (E2 : m2 (wa a) = m1 (wa a) /\ (wview ctusegs m1 (wa a) <> None -> wview ctusegs m2 (wa a) <> None)).
      { apply (rheap_pres_but_of_remove _ _ _ _ _ _ _ _ (bv_unsigned sp) HEAP HGIN HP ltac:(klia) a Ha Hc). cbn [fst snd]. exact NX. }
      assert (E3 : m5 (wa a) = m2 (wa a) /\ (wview ctusegs m2 (wa a) <> None -> wview ctusegs m5 (wa a) <> None)).
      { split; [| intros Hv; apply WM2; exact Hv]. apply MU2. unfold wa. rewrite unsigned_lit by klia.
        apply rclient_addr_cases in Hc. cbn. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]].
        - split; [klia|]. split; [klia|]. split; [klia| exact I].
        - split; [klia|]. split; [klia|]. split; [klia| exact I].
        - pose proof (LH_block_range _ _ _ _ HEAP Hb') as (B0' & _ & _ & B3' & _).
          assert (NE : p <> blk_id b').
          { intros E. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. apply (proj1 ND). rewrite E. apply in_map. exact Hb'. }
          pose proof (LH_disjoint _ _ _ (p, C, 20) b' HEAP2 ltac:(left; reflexivity) ltac:(right; exact Hb') NE) as DJ.
          cbn [blk_addr blk_size blk_id fst snd] in DJ. split; [klia|]. split; [klia|]. split; [klia| exact I]. }
      destruct E1 as [E1 V1], E2 as [E2 V2], E3 as [E3 V3]. split; [congruence| auto]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact BR|]. split; [exact HEAP5|].
    split; [unfold asn1_string_cells, MallocRep.wz; assumption|].
    split; [| rewrite length_skipn, JL; reflexivity].
    change (S 15) with 16%nat in BLK4. exact BLK4.
  Qed.
End Proofs.
End WithCeiling0.
