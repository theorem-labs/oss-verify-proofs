(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_MILB LbB_HKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_HStDtL.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HMvaT.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Fixpoint nodes_okG (NS : Z) (LBn : list block) (m : mem) (ns : list (Z * list byte)) : Prop :=
  match LBn, ns with
  | [], [] => True
  | b :: LBn', (q, tl) :: ns' =>
      blk_addr b = q /\ blk_size b = NS
      /\ rw_cells asegs m q [C8 (Z_to_bv 64 (match ns' with [] => 0 | (q', _) :: _ => q' end)); CB (Z.to_nat (NS - 8)) tl]
      /\ addressable m q NS
      /\ (match ns' with [] => True | (q', _) :: _ => 0x6e8000 <= q' < 2 ^ 47 end)
      /\ nodes_okG NS LBn' m ns'
  | _, _ => False
  end.

Lemma nodes_existG : forall (NS : Z) (V : Type) (ents : list (Z * (Z * V))) (LBn : list block) (m : mem),
  8 <= NS ->
  lbl LBn = map (fun e => (fst e, NS)) ents ->
  HRep.chain ASEGS m ents -> lb_own LBn m ->
  (forall p k v, In (p, (k, v)) ents -> addressable m p NS /\ AIMG_TOP <= p /\ p + NS <= 2 ^ 47) ->
  exists ns, nodes_okG NS LBn m ns /\ map fst ns = map fst ents.
Proof.
  intros NS V. induction ents as [|[p [k v]] ents IH]; intros LBn m HNS EL CH OWN ND.
  - destruct LBn as [|b LBn]; [|discriminate EL]. exists []. split; [exact I | reflexivity].
  - destruct LBn as [|b LBn]; [discriminate EL|].
    cbn [map Datatypes.fst] in EL. destruct (LbB_HMvaT.lbl_cons_inv b LBn p NS _ EL) as (BA & BS & EL').
    cbn [HRep.chain] in CH. destruct CH as (C0 & CH').
    pose proof (Forall_inv OWN) as W. pose proof (Forall_inv_tail OWN) as OWN'. cbn beta in W.
    rewrite BA, BS in W.
    destruct (ND p k v (or_introl eq_refl)) as (ADP & P0 & P1).
    assert (ND' : forall p' k' v', In (p', (k', v')) ents -> addressable m p' NS /\ AIMG_TOP <= p' /\ p' + NS <= 2 ^ 47)
      by (intros p' k' v' Hin; exact (ND p' k' v' (or_intror Hin))).
    destruct (IH LBn m HNS EL' CH' OWN' ND') as (ns & NO & FS).
    pose proof P0 as P0'. unfold AIMG_TOP in P0'.
    destruct (rw_cells_of_wr_hi m (p + 8) (NS - 8) (LbB_HMvaT.wr_at_sub m p NS (p + 8) (NS - 8) W ltac:(lia) ltac:(lia) ltac:(lia))
                ltac:(unfold AIMG_TOP; lia) ltac:(lia)) as (tl & TL).
    exists ((p, tl) :: ns). split; [|cbn [map Datatypes.fst]; rewrite FS; reflexivity].
    destruct b as [[id q] n]. cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in BA, BS. subst q n.
    assert (NX : match ns with [] => 0 | (q', _) :: _ => q' end = hdaddr ents).
    { destruct ns as [|[q' tl'] ns'], ents as [|[p' [k' v']] ents']; cbn [map Datatypes.fst] in FS;
        [reflexivity | discriminate FS | discriminate FS | injection FS as -> _; reflexivity]. }
    cbn [nodes_okG blk_addr blk_size Datatypes.fst Datatypes.snd].
    split; [reflexivity|]. split; [reflexivity|]. split.
    { rewrite NX. change [C8 (Z_to_bv 64 (hdaddr ents)); CB (Z.to_nat (NS - 8)) tl]
        with ([C8 (Z_to_bv 64 (hdaddr ents))] ++ [CB (Z.to_nat (NS - 8)) tl]).
      apply rw_cells_app. split; [apply rw_cells_of_cellw8; [exact C0 | exact P0 | lia]|].
      eapply rw_cells_addr; [exact TL | cbn [cells_size csize]; lia]. }
    split; [exact ADP|]. split; [|exact NO].
    destruct ns as [|[q' tl'] ns']; [exact I|].
    destruct ents as [|[p' [k' v']] ents']; [discriminate FS|]. cbn [map Datatypes.fst] in FS. injection FS as -> _.
    destruct (ND' p' k' v' (or_introl eq_refl)) as (_ & Q0 & Q1). unfold AIMG_TOP in Q0. lia.
Qed.

Section Dt.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis HCF : forall n, as_Cf H n = 0.

  Lemma apres_shrink : forall LB1 LB2 SP m m', apres H LB1 SP m m' -> (forall b, In b LB2 -> In b LB1) -> apres H LB2 SP m m'.
  Proof.
    intros LB1 LB2 SP m m' AP INC a Ha Hc. apply AP; [exact Ha|]. eapply (aclient_addr_weaken H); [exact Hc | lia | exact INC].
  Qed.

  Lemma nodes_okG_apres : forall NS LBn ns LB' SP m m', 8 <= NS ->
    nodes_okG NS LBn m ns -> apres H LB' SP m m' -> (forall b, In b LBn -> In b LB') -> nodes_okG NS LBn m' ns.
  Proof.
    intros NS. induction LBn as [|b LBn IH]; intros ns LB' SP m m' HNS NO AP INC; destruct ns as [|[q tl] ns];
      cbn [nodes_okG] in NO |- *; try tauto.
    destruct b as [[id A] n]. destruct NO as (BA & BS & CQ & ADQ & NXR & NO').
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in BA, BS |- *. subst A n.
    split; [reflexivity|]. split; [reflexivity|]. split.
    - eapply (apres_rw_cells H); [exact AP | exact CQ |]. right; right; left. exists (id, q, NS).
      split; [apply INC; left; reflexivity | cbn [blk_addr blk_size Datatypes.fst Datatypes.snd cells_size csize]].
      rewrite ?Nat2Z.inj_add, ?Z2Nat.id by lia. cbn [Z.of_nat]. lia.
    - split; [eapply (apres_addressable H); [exact AP | exact ADQ | apply INC; left; reflexivity]|].
      split; [exact NXR|]. eapply IH; [exact HNS | exact NO' | exact AP | intros b Hb; apply INC; right; exact Hb].
  Qed.

  Lemma dtl3_loop : forall (Q : config -> Prop) (ns : list (Z * list byte)) (q : Z) (tl : list byte) (LBn LB LBr : list block)
      (x1 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (spf lo B : Z) (errv : word) (mo : Model),
    as_VIS H s msF = MS (mkR x1 (Z_to_bv 64 spf) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 q) x11 x12 x13 x14 x15 x16 x17 x18 x19
                             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 DTL3_LOOP) fc None m (seg_rom asegs) ->
    nodes_okG 24 LBn m ((q, tl) :: ns) -> Permutation LB (LBr ++ LBn) ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    as_rauxv_ok H m B -> spf <= B ->
    stk asegs m lo spf -> aceil <= lo -> lo <= spf - AFREE_STACK ->
    rw_cells asegs m (errno_addr x4) [C4 errv] -> mem_inv asegs m -> x4 = Z_to_bv 64 ATP ->
    spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 -> ACONST m ->
    (bv_unsigned x8 <= aceil \/ bv_unsigned x8 mod 8 <> 0) ->
    trace_ok (as_TR H) APC0_FREE [DTL3_DRET] ->
    (forall (msF' : machine_state) (mo' : Model) (m' : mem) (s' : as_St H) (LBr' : list block)
            (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
       as_VIS H s' msF' = MS (mkR (Z_to_bv 64 DTL3_DRET) (Z_to_bv 64 spf) x3 x4 t0 t1 t2 x8 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0)
                                 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                             F (Z_to_bv 64 DTL3_EXIT) fc None m' (seg_rom asegs) ->
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       mem_inv asegs m' -> stk asegs m' lo spf -> rw_cells asegs m' (errno_addr x4) [C4 errv] -> as_rauxv_ok H m' B ->
       Permutation LBr' LBr -> apres H LBr' spf m m' -> as_RHEAP H s' LBr' m' -> ACONST m' -> as_AL H s' >= as_AL H s ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    induction ns as [|[q' tl'] ns IH];
      intros q tl LBn LB LBr x1 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
        F fc msF m s spf lo B errv mo VIS NO PERM RH KR AL0 RA SPB ST CE LO ERR MI TP SP16 SPR AC S0LOW TRK K;
      destruct LBn as [|[[id q0] n0] LBn]; cbn [nodes_okG] in NO; try contradiction;
      destruct NO as (BA & BS & CQ & ADQ & NXR & NO'); cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in BA, BS; subst q0 n0;
      assert (INQ : In (id, q, 24) LB) by (apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app; right; left; reflexivity);
      assert (ND : List.NoDup (map blk_id LB)) by exact (ah_nodup H HH _ _ _ RH);
      pose proof (lb_remove_perm_app H HH LB LBr LBn id q 24 ND PERM) as PERM';
      assert (CF0 : as_Cf H 24 <= as_AL H s) by (rewrite HCF; lia).
    -
      destruct LBn as [|b LBn]; [|cbn [nodes_okG] in NO'; destruct NO'].
      eapply (dtl3_step H HH Q x1 x3 x4 x5 x6 x7 x8 x25 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x20 x26 x27 x28 x29 x30 x31
                F fc msF m s LB q tl [] spf lo B errv mo id);
        [exact VIS | exact INQ | exact CQ | exact ADQ | exact RH | exact KR | exact CF0 | exact RA | exact SPB | exact ST | exact CE
        | exact LO | exact ERR | exact MI | exact TP | exact SP16 | exact SPR | exact AC | exact S0LOW | exact TRK | exact I |].
      intros msF' mo' m' s' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 VIS' KR' MP' MI' ST' ERR' RA' AP' RH' AC' AL'.
      rewrite app_nil_r in PERM'.
      apply (K msF' mo' m' s' (as_lb_remove H id LB) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6);
        [exact VIS' | exact KR' | exact MP' | exact MI' | exact ST' | exact ERR' | exact RA' | exact PERM' | exact AP' | exact RH'
        | exact AC' | rewrite HCF in AL'; lia].
    -
      eapply (dtl3_step H HH Q x1 x3 x4 x5 x6 x7 x8 x25 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x20 x26 x27 x28 x29 x30 x31
                F fc msF m s LB q tl ((q', tl') :: ns) spf lo B errv mo id);
        [exact VIS | exact INQ | exact CQ | exact ADQ | exact RH | exact KR | exact CF0 | exact RA | exact SPB | exact ST | exact CE
        | exact LO | exact ERR | exact MI | exact TP | exact SP16 | exact SPR | exact AC | exact S0LOW | exact TRK | exact NXR |].
      intros msF' mo' m' s' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 VIS' KR' MP' MI' ST' ERR' RA' AP' RH' AC' AL'.
      assert (NO1 : nodes_okG 24 LBn m' ((q', tl') :: ns)).
      { eapply (nodes_okG_apres 24 LBn _ (as_lb_remove H id LB) spf m m'); [lia | exact NO' | exact AP' |].
        intros b Hb. apply (Permutation_in _ (Permutation_sym PERM')). apply in_or_app; right; exact Hb. }
      eapply (IH q' tl' LBn (as_lb_remove H id LB) LBr (Z_to_bv 64 DTL3_DRET) x3 x4 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 q') x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F fc msF' m' s' spf lo B errv mo');
        [exact VIS' | exact NO1 | exact PERM' | exact RH' | exact KR' | rewrite HCF in AL'; lia | exact RA' | exact SPB | exact ST'
        | exact CE | exact LO | exact ERR' | exact MI' | exact TP | exact SP16 | exact SPR | exact AC' | exact S0LOW | exact TRK |].
      intros msF'' mo'' m'' s'' LBr' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
        VIS'' KR'' MP'' MI'' ST'' ERR'' RA'' PE'' AP'' RH'' AC'' AL''.
      apply (K msF'' mo'' m'' s'' LBr' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6');
        [exact VIS'' | exact KR'' | eapply (ah_mpres_trans H HH); [exact MP' | exact MP''] | exact MI'' | exact ST'' | exact ERR''
        | exact RA'' | exact PE'' | | exact RH'' | exact AC'' | rewrite HCF in AL'; lia].
      eapply (apres_trans H); [| exact AP''].
      eapply apres_shrink; [exact AP' |]. intros b Hb.
      apply (Permutation_in _ (Permutation_sym PERM')). apply (Permutation_in _ PE'') in Hb. apply in_or_app; left; exact Hb.
  Qed.

  Lemma dtl2_loop : forall (Q : config -> Prop) (ns : list (Z * list byte)) (q : Z) (tl : list byte) (LBn LB LBr : list block)
      (x1 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (spf lo B : Z) (errv : word) (mo : Model),
    as_VIS H s msF = MS (mkR x1 (Z_to_bv 64 spf) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 q) x11 x12 x13 x14 x15 x16 x17 x18 x19
                             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 DTL2_LOOP) fc None m (seg_rom asegs) ->
    nodes_okG 32 LBn m ((q, tl) :: ns) -> Permutation LB (LBr ++ LBn) ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    as_rauxv_ok H m B -> spf <= B ->
    stk asegs m lo spf -> aceil <= lo -> lo <= spf - AFREE_STACK ->
    rw_cells asegs m (errno_addr x4) [C4 errv] -> mem_inv asegs m -> x4 = Z_to_bv 64 ATP ->
    spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 -> ACONST m ->
    (bv_unsigned x8 <= aceil \/ bv_unsigned x8 mod 8 <> 0) ->
    trace_ok (as_TR H) APC0_FREE [DTL2_DRET] ->
    (forall (msF' : machine_state) (mo' : Model) (m' : mem) (s' : as_St H) (LBr' : list block)
            (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
       as_VIS H s' msF' = MS (mkR (Z_to_bv 64 DTL2_DRET) (Z_to_bv 64 spf) x3 x4 t0 t1 t2 x8 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0)
                                 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                             F (Z_to_bv 64 DTL2_EXIT) fc None m' (seg_rom asegs) ->
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       mem_inv asegs m' -> stk asegs m' lo spf -> rw_cells asegs m' (errno_addr x4) [C4 errv] -> as_rauxv_ok H m' B ->
       Permutation LBr' LBr -> apres H LBr' spf m m' -> as_RHEAP H s' LBr' m' -> ACONST m' -> as_AL H s' >= as_AL H s ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    induction ns as [|[q' tl'] ns IH];
      intros q tl LBn LB LBr x1 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
        F fc msF m s spf lo B errv mo VIS NO PERM RH KR AL0 RA SPB ST CE LO ERR MI TP SP16 SPR AC S0LOW TRK K;
      destruct LBn as [|[[id q0] n0] LBn]; cbn [nodes_okG] in NO; try contradiction;
      destruct NO as (BA & BS & CQ & ADQ & NXR & NO'); cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in BA, BS; subst q0 n0;
      assert (INQ : In (id, q, 32) LB) by (apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app; right; left; reflexivity);
      assert (ND : List.NoDup (map blk_id LB)) by exact (ah_nodup H HH _ _ _ RH);
      pose proof (lb_remove_perm_app H HH LB LBr LBn id q 32 ND PERM) as PERM';
      assert (CF0 : as_Cf H 32 <= as_AL H s) by (rewrite HCF; lia).
    -
      destruct LBn as [|b LBn]; [|cbn [nodes_okG] in NO'; destruct NO'].
      eapply (dtl2_step H HH Q x1 x3 x4 x5 x6 x7 x8 x26 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x21 x23 x24 x20 x25 x27 x28 x29 x30 x31
                F fc msF m s LB q tl [] spf lo B errv mo id);
        [exact VIS | exact INQ | exact CQ | exact ADQ | exact RH | exact KR | exact CF0 | exact RA | exact SPB | exact ST | exact CE
        | exact LO | exact ERR | exact MI | exact TP | exact SP16 | exact SPR | exact AC | exact S0LOW | exact TRK | exact I |].
      intros msF' mo' m' s' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 VIS' KR' MP' MI' ST' ERR' RA' AP' RH' AC' AL'.
      rewrite app_nil_r in PERM'.
      apply (K msF' mo' m' s' (as_lb_remove H id LB) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6);
        [exact VIS' | exact KR' | exact MP' | exact MI' | exact ST' | exact ERR' | exact RA' | exact PERM' | exact AP' | exact RH'
        | exact AC' | rewrite HCF in AL'; lia].
    -
      eapply (dtl2_step H HH Q x1 x3 x4 x5 x6 x7 x8 x26 x11 x12 x13 x14 x15 x16 x17 x18 x19 x22 x21 x23 x24 x20 x25 x27 x28 x29 x30 x31
                F fc msF m s LB q tl ((q', tl') :: ns) spf lo B errv mo id);
        [exact VIS | exact INQ | exact CQ | exact ADQ | exact RH | exact KR | exact CF0 | exact RA | exact SPB | exact ST | exact CE
        | exact LO | exact ERR | exact MI | exact TP | exact SP16 | exact SPR | exact AC | exact S0LOW | exact TRK | exact NXR |].
      intros msF' mo' m' s' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 VIS' KR' MP' MI' ST' ERR' RA' AP' RH' AC' AL'.
      assert (NO1 : nodes_okG 32 LBn m' ((q', tl') :: ns)).
      { eapply (nodes_okG_apres 32 LBn _ (as_lb_remove H id LB) spf m m'); [lia | exact NO' | exact AP' |].
        intros b Hb. apply (Permutation_in _ (Permutation_sym PERM')). apply in_or_app; right; exact Hb. }
      eapply (IH q' tl' LBn (as_lb_remove H id LB) LBr (Z_to_bv 64 DTL2_DRET) x3 x4 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 q') x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F fc msF' m' s' spf lo B errv mo');
        [exact VIS' | exact NO1 | exact PERM' | exact RH' | exact KR' | rewrite HCF in AL'; lia | exact RA' | exact SPB | exact ST'
        | exact CE | exact LO | exact ERR' | exact MI' | exact TP | exact SP16 | exact SPR | exact AC' | exact S0LOW | exact TRK |].
      intros msF'' mo'' m'' s'' LBr' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
        VIS'' KR'' MP'' MI'' ST'' ERR'' RA'' PE'' AP'' RH'' AC'' AL''.
      apply (K msF'' mo'' m'' s'' LBr' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6');
        [exact VIS'' | exact KR'' | eapply (ah_mpres_trans H HH); [exact MP' | exact MP''] | exact MI'' | exact ST'' | exact ERR''
        | exact RA'' | exact PE'' | | exact RH'' | exact AC'' | rewrite HCF in AL'; lia].
      eapply (apres_trans H); [| exact AP''].
      eapply apres_shrink; [exact AP' |]. intros b Hb.
      apply (Permutation_in _ (Permutation_sym PERM')). apply (Permutation_in _ PE'') in Hb. apply in_or_app; left; exact Hb.
  Qed.

  Lemma dtl1_loop : forall (Q : config -> Prop) (ns : list (Z * list byte)) (q : Z) (tl : list byte) (LBn LB LBr : list block)
      (x1 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (spf lo B : Z) (errv : word) (mo : Model),
    as_VIS H s msF = MS (mkR x1 (Z_to_bv 64 spf) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 q) x11 x12 x13 x14 x15 x16 x17 x18 x19
                             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 DTL1_LOOP) fc None m (seg_rom asegs) ->
    nodes_okG 24 LBn m ((q, tl) :: ns) -> Permutation LB (LBr ++ LBn) ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    as_rauxv_ok H m B -> spf <= B ->
    stk asegs m lo spf -> aceil <= lo -> lo <= spf - AFREE_STACK ->
    rw_cells asegs m (errno_addr x4) [C4 errv] -> mem_inv asegs m -> x4 = Z_to_bv 64 ATP ->
    spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 -> ACONST m ->
    (bv_unsigned x8 <= aceil \/ bv_unsigned x8 mod 8 <> 0) ->
    trace_ok (as_TR H) APC0_FREE [DTL1_DRET] ->
    (forall (msF' : machine_state) (mo' : Model) (m' : mem) (s' : as_St H) (LBr' : list block)
            (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
       as_VIS H s' msF' = MS (mkR (Z_to_bv 64 DTL1_DRET) (Z_to_bv 64 spf) x3 x4 t0 t1 t2 x8 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 0)
                                 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                             F (Z_to_bv 64 DTL1_EXIT) fc None m' (seg_rom asegs) ->
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       mem_inv asegs m' -> stk asegs m' lo spf -> rw_cells asegs m' (errno_addr x4) [C4 errv] -> as_rauxv_ok H m' B ->
       Permutation LBr' LBr -> apres H LBr' spf m m' -> as_RHEAP H s' LBr' m' -> ACONST m' -> as_AL H s' >= as_AL H s ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    induction ns as [|[q' tl'] ns IH];
      intros q tl LBn LB LBr x1 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
        F fc msF m s spf lo B errv mo VIS NO PERM RH KR AL0 RA SPB ST CE LO ERR MI TP SP16 SPR AC S0LOW TRK K;
      destruct LBn as [|[[id q0] n0] LBn]; cbn [nodes_okG] in NO; try contradiction;
      destruct NO as (BA & BS & CQ & ADQ & NXR & NO'); cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in BA, BS; subst q0 n0;
      assert (INQ : In (id, q, 24) LB) by (apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app; right; left; reflexivity);
      assert (ND : List.NoDup (map blk_id LB)) by exact (ah_nodup H HH _ _ _ RH);
      pose proof (lb_remove_perm_app H HH LB LBr LBn id q 24 ND PERM) as PERM';
      assert (CF0 : as_Cf H 24 <= as_AL H s) by (rewrite HCF; lia).
    -
      destruct LBn as [|b LBn]; [|cbn [nodes_okG] in NO'; destruct NO'].
      eapply (dtl1_step H HH Q x1 x3 x4 x5 x6 x7 x8 x25 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x20 x26 x27 x28 x29 x30 x31
                F fc msF m s LB q tl [] spf lo B errv mo id);
        [exact VIS | exact INQ | exact CQ | exact ADQ | exact RH | exact KR | exact CF0 | exact RA | exact SPB | exact ST | exact CE
        | exact LO | exact ERR | exact MI | exact TP | exact SP16 | exact SPR | exact AC | exact S0LOW | exact TRK | exact I |].
      intros msF' mo' m' s' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 VIS' KR' MP' MI' ST' ERR' RA' AP' RH' AC' AL'.
      rewrite app_nil_r in PERM'.
      apply (K msF' mo' m' s' (as_lb_remove H id LB) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6);
        [exact VIS' | exact KR' | exact MP' | exact MI' | exact ST' | exact ERR' | exact RA' | exact PERM' | exact AP' | exact RH'
        | exact AC' | rewrite HCF in AL'; lia].
    -
      eapply (dtl1_step H HH Q x1 x3 x4 x5 x6 x7 x8 x25 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x20 x26 x27 x28 x29 x30 x31
                F fc msF m s LB q tl ((q', tl') :: ns) spf lo B errv mo id);
        [exact VIS | exact INQ | exact CQ | exact ADQ | exact RH | exact KR | exact CF0 | exact RA | exact SPB | exact ST | exact CE
        | exact LO | exact ERR | exact MI | exact TP | exact SP16 | exact SPR | exact AC | exact S0LOW | exact TRK | exact NXR |].
      intros msF' mo' m' s' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 VIS' KR' MP' MI' ST' ERR' RA' AP' RH' AC' AL'.
      assert (NO1 : nodes_okG 24 LBn m' ((q', tl') :: ns)).
      { eapply (nodes_okG_apres 24 LBn _ (as_lb_remove H id LB) spf m m'); [lia | exact NO' | exact AP' |].
        intros b Hb. apply (Permutation_in _ (Permutation_sym PERM')). apply in_or_app; right; exact Hb. }
      eapply (IH q' tl' LBn (as_lb_remove H id LB) LBr (Z_to_bv 64 DTL1_DRET) x3 x4 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 q') x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F fc msF' m' s' spf lo B errv mo');
        [exact VIS' | exact NO1 | exact PERM' | exact RH' | exact KR' | rewrite HCF in AL'; lia | exact RA' | exact SPB | exact ST'
        | exact CE | exact LO | exact ERR' | exact MI' | exact TP | exact SP16 | exact SPR | exact AC' | exact S0LOW | exact TRK |].
      intros msF'' mo'' m'' s'' LBr' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
        VIS'' KR'' MP'' MI'' ST'' ERR'' RA'' PE'' AP'' RH'' AC'' AL''.
      apply (K msF'' mo'' m'' s'' LBr' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6');
        [exact VIS'' | exact KR'' | eapply (ah_mpres_trans H HH); [exact MP' | exact MP''] | exact MI'' | exact ST'' | exact ERR''
        | exact RA'' | exact PE'' | | exact RH'' | exact AC'' | rewrite HCF in AL'; lia].
      eapply (apres_trans H); [| exact AP''].
      eapply apres_shrink; [exact AP' |]. intros b Hb.
      apply (Permutation_in _ (Permutation_sym PERM')). apply (Permutation_in _ PE'') in Hb. apply in_or_app; left; exact Hb.
  Qed.

End Dt.
