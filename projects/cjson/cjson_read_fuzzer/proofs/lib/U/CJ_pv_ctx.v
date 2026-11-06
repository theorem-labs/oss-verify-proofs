(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface CJ_tree CJ_print_iface CJ_ensure CJ_pv_common CJ_pv_update CJ_pstr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma CJST_magree_hole : forall mm m2 (SPF PB : Z) LR,
  CJST mm ->
  (forall a, 0 <= a < 2^64 -> (SPF <= a /\ (a < PB \/ PB + 64 <= a)) \/ (in_cblock LR a \/ (PDATA_LO <= a < PIMG_HI /\ ~ palloc_static a)) ->
      m2 (wa a) = mm (wa a) /\ (wview usegs mm (wa a) <> None -> wview usegs m2 (wa a) <> None)) ->
  CJST m2.
Proof.
  intros mm m2 SPF PB LR (HK & (e1 & e2 & GE) & LC) AGR.
  split; [|split; [exists e1, e2|]].
  all: eapply rw_cells_magree; [exact AGR| eassumption|].
  all: cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; intros a Ha; right; right;
       unfold palloc_static; unfold PHOOKS, PGERROR, PLCONV, PDATA_LO, PIMG_HI, PLIBC, PCTX_END, PERRNO, PSSP, PGOT_SSP in *; lia.
Qed.

Section S.
  Variable HI : cj_heap_iface.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
            (m : word -> option byte)
            (SPB : Z) (LR B : list cblock) (n : nat) (p PB dep : Z) (fw : word) (lo : Z).

  Notation SPF := (bv_unsigned sp + -128).
  Notation PVFRAME mm loc := (rw_cells usegs mm (bv_unsigned sp + -128)
     [CB 40 loc; C8 (reg_get F (Z_to_bv 5 9)); C8 (reg_get F (Z_to_bv 5 8)); C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation PBSd mm b l o d := (rw_cells usegs mm PB [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 l); C8 (Z_to_bv 64 o); C8 (Z_to_bv 64 d);
                                               C4 (Z_to_bv 64 0); C4 fw; C8 (Z_to_bv 64 91236); C8 (Z_to_bv 64 90916); C8 (Z_to_bv 64 97488)]).

  Definition actx (depc : Z) (mm : word -> option byte) (mo : Model) (loc : list byte) (Fc : bvmap 5 word) (fcc : bv 32) (errv : word)
      (LB : list cblock) (buf len off : Z) (bs : list byte) : Prop :=
    LHEAP HI SPB LB mm mo /\ Permutation ((buf, len) :: LR) LB /\ PBSd mm buf len off depc /\ u8arr usegs mm buf bs /\ Z.of_nat (length bs) = len
    /\ pb_nums len off depc /\ PVFRAME mm loc /\ stk usegs mm lo SPF /\ rw_cells usegs mm PERRNO [C4 errv] /\ mem_inv usegs mm /\ CJST mm
    /\ frm0 fcc /\ FAG18 F Fc /\ pv_agree LR (bv_unsigned sp) PB m mm.

  Hypothesis PL : pb_place (bv_unsigned sp) PB SPB.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - PV_STACK n.
  Hypothesis BLR : forall b, In b B -> In b LR.

  (* [comment removed for export] *)
  Lemma actx_magree : forall depc mm mo loc Fc fcc errv LB buf len off bs,
    actx depc mm mo loc Fc fcc errv LB buf len off bs -> magree (in_cblock B) m mm.
  Proof.
    intros until bs. intros nelH_; (nelim nelH_ 14%nat; intros HL HP _ _ _ _ _ _ _ _ _ _ _ PVA).
    pose proof CEIL as C. try rewrite alloc_ceiling_eq in C. unfold PV_STACK, PV_BASE in LO. (nelimp PL 4%nat; intros PL1 PL2 PL3 PL4).
    eapply magree_mono; [exact PVA|]. cbv beta. intros a nelH_; (nelim nelH_ 4%nat; intros A' n' Hin Hr). split; [right; right; exists A', n'; split; [apply BLR; exact Hin| exact Hr]|].
    (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; apply BLR; exact Hin])) 5%nat; intros _ _ _ R _).
    try rewrite alloc_ceiling_eq in R. lia.
  Qed.

  Lemma actx_chain : forall depc mm mo loc Fc fcc errv LB buf len off bs T d q Bq,
    actx depc mm mo loc Fc fcc errv LB buf len off bs -> cj_chain T m d q Bq -> (forall b, In b Bq -> In b B) -> cj_chain T mm d q Bq.
  Proof.
    intros until Bq. intros CTX CH SUB. eapply cj_chain_magree; [exact CH| eapply actx_magree; exact CTX|].
    intros a Ha. eapply in_cblock_mono; [exact SUB| exact Ha].
  Qed.

  Lemma actx_str : forall depc mm mo loc Fc fcc errv LB buf len off bs s Bs,
    actx depc mm mo loc Fc fcc errv LB buf len off bs -> cj_str m s Bs -> (forall b, In b Bs -> In b B) -> cj_str mm s Bs.
  Proof.
    intros until Bs. intros CTX SV SUB. eapply cj_str_magree; [eapply actx_magree; exact CTX| exact SV|].
    intros a Ha. eapply in_cblock_mono; [exact SUB| exact Ha].
  Qed.

  Lemma actx_node : forall depc mm mo loc Fc fcc errv LB buf len off bs q cells,
    actx depc mm mo loc Fc fcc errv LB buf len off bs -> rw_cells usegs m q cells -> cells_size cells = 64%nat -> In (q, 64) B ->
    rw_cells usegs mm q cells.
  Proof.
    intros until cells. intros CTX ND SZ HIN. eapply rw_cells_magree; [eapply actx_magree; exact CTX| exact ND|].
    rewrite SZ. intros a Ha. exists q, 64. split; [exact HIN| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma actx_tree : forall depc mm mo loc Fc fcc errv LB buf len off bs,
    actx depc mm mo loc Fc fcc errv LB buf len off bs -> cj_chain CJ_PRINTABLE m n p B -> cj_chain CJ_PRINTABLE mm n p B.
  Proof. intros. eapply actx_chain; eauto. Qed.

  Hypothesis TP : tp = wz PTP.
  Hypothesis N1 : (1 <= n)%nat.
  Hypothesis CH0 : cj_chain CJ_PRINTABLE m n p B.

  (* [comment removed for export] *)
  Definition fctx (mm : word -> option byte) (loc : list byte) (Fc : bvmap 5 word) (fcc : bv 32) (errv : word) : Prop :=
    PVFRAME mm loc /\ stk usegs mm lo SPF /\ rw_cells usegs mm PERRNO [C4 errv] /\ mem_inv usegs mm /\ CJST mm
    /\ frm0 fcc /\ FAG18 F Fc /\ pv_agree LR (bv_unsigned sp) PB m mm /\ cj_chain CJ_PRINTABLE mm n p B.

  Definition ens_post (depc : Z) (loc : list byte) (Fc : bvmap 5 word) (fcc : bv 32) (off needed : Z)
      (x1 x8 x9 x18 x19 x20 x21 x22 x23 : word) : machine_state -> Model -> Prop :=
    fun ms' mo' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (errv' : word) (LB' : list cblock) (buf' len' : Z),
      ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
               Fc (ret_pc x1) fcc None m' (seg_rom usegs)
      /\ LHEAP HI SPB LB' m' mo' /\ fctx m' loc Fc fcc errv' /\ PBSd m' buf' len' off depc
      /\ ( (a0 = Z_to_bv 64 0 /\ ((buf' = 0 /\ Permutation LR LB') \/ (buf' <> 0 /\ Permutation ((buf', len') :: LR) LB')))
        \/ (exists bs', a0 = Z_to_bv 64 (buf' + off) /\ actx depc m' mo' loc Fc fcc errv' LB' buf' len' off bs' /\ needed + off + 1 <= len') ).

  (* [comment removed for export] *)
  Lemma actx_ensure : forall depc mm mo loc Fc fcc errv LB buf len off bs needed
      (x1 t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word),
    actx depc mm mo loc Fc fcc errv LB buf len off bs -> 0 <= needed < 2^64 ->
    SCPS usegs (ens_post depc loc Fc fcc off needed x1 x8 x9 x18 x19 x20 x21 x22 x23)
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 PB) (Z_to_bv 64 needed) a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
          Fc (wz ENSURE_ENTRY) fcc None mm (seg_rom usegs)) mo.
  Proof.
    intros until t6. intros CTX ND.
    pose proof (actx_tree _ _ _ _ _ _ _ _ _ _ _ _ CTX CH0) as CHn.
    (nelim CTX 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA).
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. unfold PV_STACK, PV_BASE in LO.
    (nelimp PL 4%nat; intros PL1 PL2 PL3 PL4). (nelimp PN 3%nat; intros PN1 PN2 PN3).
    assert (E1 : bv_unsigned (Z_to_bv 64 SPF) = SPF) by (apply unsigned_lit; lia).
    eapply scps_mono.
    { eapply (ensure_spec HI) with (lo := lo) (LR := LR) (bs := bs) (needed := needed); rewrite ?E1;
        first [ exact HL | exact HP | exact PBS0 | split; [exact ARR| exact LEN] | exact PN | exact ST | exact ERR | exact MI | exact TP | reflexivity
              | split; [lia| split; [lia| split; [lia| exact PL4]]] | unfold ENSURE_STACK, RMALLOC_STACK; lia | lia ]. }
    cbv beta. intros ms2 mo2 PO.
    (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 errv2 LB2 -> MI2 ST2 ERR2 PVE HL2 OUT)
.
    rewrite E1 in ST2, PVE.
    (* [comment removed for export] *)
    assert (AGR : forall a, 0 <= a < 2^64 -> (SPF <= a /\ (a < PB \/ PB + 64 <= a)) \/ (in_cblock LR a \/ (PDATA_LO <= a < PIMG_HI /\ ~ palloc_static a)) ->
                    m2 (wa a) = mm (wa a) /\ (wview usegs mm (wa a) <> None -> wview usegs m2 (wa a) <> None)).
    { intros a Ha Hc. apply PVE; [exact Ha|]. unfold cj_client_addr.
      destruct Hc as [[H1 H2]|[H1|H1]]; [split; [left; lia| lia]| |].
      - split; [right; right; exact H1|]. (nelim H1 4%nat; intros A' n' Hin Hr).
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; exact Hin])) 5%nat; intros _ _ _ X4 _).
        try rewrite alloc_ceiling_eq in X4. lia.
      - split; [right; left; exact H1|]. unfold PDATA_LO, PIMG_HI in H1. lia. }
    assert (FR2 : PVFRAME m2 loc) by (eapply (rw_cells_magree _ mm m2); [exact AGR| exact FR| cbn; intros a Ha; left; lia]).
    assert (CJ2 : CJST m2) by (eapply (CJST_magree_hole mm m2); [exact CJ| exact AGR]).
    assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
    { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_weaken; [exact PVE| lia| intros b Hb; exact Hb]. }
    assert (CH2 : cj_chain CJ_PRINTABLE m2 n p B).
    { eapply cj_chain_magree; [exact CHn| exact AGR|]. intros a nelH_; (nelim nelH_ 4%nat; intros A' n' Hin Hr). right; left. exists A', n'. split; [apply BLR; exact Hin| exact Hr]. }
    assert (FC2 : fctx m2 loc Fc fcc errv2).
    { split; [exact FR2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact CJ2|]. split; [exact FRM|]. split; [exact FA|]. split; [exact PVA2| exact CH2]. }
    unfold ens_post. unfold wz in OUT.
    destruct OUT as [(-> & HPn & PBSn) | [(-> & HPn & PBSn & PDn) | (buf' & len' & bs' & -> & HPn & PBSn & PDn & ROOM & L31)]].
    - nexists 20%nat. split; [reflexivity|]. split; [exact HL2|]. split; [exact FC2|]. split; [exact PBSn|]. left. split; [reflexivity| left; split; [reflexivity| exact HPn]].
    - nexists 20%nat. split; [reflexivity|]. split; [exact HL2|]. split; [exact FC2|]. split; [exact PBSn|]. left. split; [reflexivity| right; split; [|exact HPn]].
      pose proof (lh_block_range HI _ _ _ _ _ _ HL2 (perm_in_head _ _ _ HPn)) as (Y1 & _). lia.
    - nexists 20%nat. split; [reflexivity|]. split; [exact HL2|]. split; [exact FC2|]. split; [exact PBSn|]. right. exists bs'. split; [reflexivity|]. split; [| exact ROOM].
      destruct PDn as [ARRn LENn].
      split; [exact HL2|]. split; [exact HPn|]. split; [exact PBSn|]. split; [exact ARRn|]. split; [exact LENn|]. split; [split; [lia| split; [exact L31| lia]]|].
      split; [exact FR2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact CJ2|]. split; [exact FRM|]. split; [exact FA| exact PVA2].
  Qed.

  (* [comment removed for export] *)
  Definition rec_post (depc : Z) (loc : list byte) (Fc : bvmap 5 word) (d : nat) (c : Z) (Bc : list cblock)
      (x1 x8 x9 x18 x19 x20 x21 x22 x23 : word) : machine_state -> Model -> Prop :=
    fun ms' mo' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Fc' : bvmap 5 word) (fcc' : bv 32) (m' : word -> option byte) (errv' : word)
                          (LB' : list cblock) (buf' len' off' : Z),
      ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
               Fc' (ret_pc x1) fcc' None m' (seg_rom usegs)
      /\ LHEAP HI SPB LB' m' mo' /\ fctx m' loc Fc' fcc' errv'
      /\ ( (a0 = Z_to_bv 64 0 /\ exists dep', PBSd m' buf' len' off' dep' /\ ((buf' = 0 /\ Permutation LR LB') \/ (buf' <> 0 /\ Permutation ((buf', len') :: LR) LB')))
        \/ (a0 = Z_to_bv 64 1 /\ exists bs', actx depc m' mo' loc Fc' fcc' errv' LB' buf' len' off' bs' /\ pb_nul bs' len' off') ).

  Hypothesis SPAL : bv_unsigned sp mod 16 = 0.

  Lemma actx_rec : forall depc mm mo loc Fc fcc errv LB buf len off bs (d : nat) (c : Z) (Bc : list cblock)
      (x1 t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word),
    pvalue_spec_at HI d -> (d < n)%nat ->
    actx depc mm mo loc Fc fcc errv LB buf len off bs -> depc + Z.of_nat d <= 2^40 ->
    cj_chain CJ_PRINTABLE m d c Bc -> c <> 0 -> (forall b, In b Bc -> In b B) ->
    SCPS usegs (rec_post depc loc Fc d c Bc x1 x8 x9 x18 x19 x20 x21 x22 x23)
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 c) (Z_to_bv 64 PB) a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
          Fc (wz PVALUE_ENTRY) fcc None mm (seg_rom usegs)) mo.
  Proof.
    intros until t6. intros RECd Dlt CTX DEP CHc CNZ SUB.
    pose proof (actx_tree _ _ _ _ _ _ _ _ _ _ _ _ CTX CH0) as CHn.
    pose proof (actx_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX CHc SUB) as CHcn.
    (nelim CTX 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA).
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. unfold PV_STACK, PV_BASE in LO.
    (nelimp PL 4%nat; intros PL1 PL2 PL3 PL4). (nelimp PN 3%nat; intros PN1 PN2 PN3).
    assert (E1 : bv_unsigned (Z_to_bv 64 SPF) = SPF) by (apply unsigned_lit; lia).
    eapply scps_mono.
    { eapply RECd with (lo := lo) (LR := LR) (bs := bs) (B := Bc); rewrite ?E1;
        first [ exact HL | exact HP | exact PBS0 | split; [exact ARR| exact LEN] | exact PN | exact DEP | exact CHcn | exact CNZ | exact CJ | exact ST | exact ERR | exact MI | exact TP | exact FRM | reflexivity
              | intros b Hb; apply BLR, SUB, Hb
              | split; [lia| split; [lia| split; [lia| exact PL4]]]
              | rewrite <- Zminus_mod_idemp_l, SPAL; reflexivity
              | unfold PV_STACK, PV_BASE; lia | lia ]. }
    cbv beta. intros ms2 mo2 PO.
    (nelim PO 29%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Fc' fcc' m2 errv2 -> MI2 FRM2 FA2 ST2 ERR2 CJ2 PVE CHc2 OUT)
.
    rewrite E1 in ST2, PVE.
    assert (AGR : forall a, 0 <= a < 2^64 -> (SPF <= a /\ (a < PB \/ PB + 64 <= a)) \/ (in_cblock LR a \/ (PDATA_LO <= a < PIMG_HI /\ ~ palloc_static a)) ->
                    m2 (wa a) = mm (wa a) /\ (wview usegs mm (wa a) <> None -> wview usegs m2 (wa a) <> None)).
    { intros a Ha Hc. apply PVE; [exact Ha|]. unfold cj_client_addr.
      destruct Hc as [[H1 H2]|[H1|H1]]; [split; [left; lia| lia]| |].
      - split; [right; right; exact H1|]. (nelim H1 4%nat; intros A' n' Hin Hr).
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; exact Hin])) 5%nat; intros _ _ _ X4 _).
        try rewrite alloc_ceiling_eq in X4. lia.
      - split; [right; left; exact H1|]. unfold PDATA_LO, PIMG_HI in H1. lia. }
    assert (FR2 : PVFRAME m2 loc) by (eapply (rw_cells_magree _ mm m2); [exact AGR| exact FR| cbn; intros a Ha; left; lia]).
    assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
    { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_weaken; [exact PVE| lia| intros b Hb; exact Hb]. }
    assert (CH2 : cj_chain CJ_PRINTABLE m2 n p B).
    { eapply cj_chain_magree; [exact CHn| exact AGR|]. intros a nelH_; (nelim nelH_ 4%nat; intros A' n' Hin Hr). right; left. exists A', n'. split; [apply BLR; exact Hin| exact Hr]. }
    assert (FA2' : FAG18 F Fc'). { intros k Hk. rewrite (FA2 k ltac:(unfold fp_callee_saved; lia)). apply FA. exact Hk. }
    assert (FC2 : fctx m2 loc Fc' fcc' errv2).
    { split; [exact FR2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact CJ2|]. split; [exact FRM2|]. split; [exact FA2'|]. split; [exact PVA2| exact CH2]. }
    unfold rec_post. unfold wz in OUT.
    destruct OUT as (LB' & buf' & len' & off' & HL' & [(-> & dep' & PBS' & HB) | (-> & bs' & HP' & PBS' & PD' & PN' & NUL)]).
    - nexists 23%nat. split; [reflexivity|]. split; [exact HL'|]. split; [exact FC2|]. left. split; [reflexivity|]. exists dep'. split; [exact PBS'| exact HB].
    - nexists 23%nat. split; [reflexivity|]. split; [exact HL'|]. split; [exact FC2|]. right. split; [reflexivity|]. exists bs'. split; [| exact NUL].
      destruct PD' as [ARR' LEN'].
      split; [exact HL'|]. split; [exact HP'|]. split; [exact PBS'|]. split; [exact ARR'|]. split; [exact LEN'|]. split; [exact PN'|].
      split; [exact FR2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact CJ2|]. split; [exact FRM2|]. split; [exact FA2'| exact PVA2].
  Qed.

  (* [comment removed for export] *)
  Definition upd_post (depc : Z) (mo : Model) (loc : list byte) (Fc : bvmap 5 word) (fcc : bv 32) (LB : list cblock) (buf len off : Z) (bs : list byte)
      (x1 x8 x9 x18 x19 x20 x21 x22 x23 : word) : machine_state -> Prop :=
    fun ms' => exists (k : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (errv' : word),
      ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
               Fc (ret_pc x1) fcc None m' (seg_rom usegs)
      /\ actx depc m' mo loc Fc fcc errv' LB buf len off bs /\ 0 <= k /\ off + k < len /\ nth_error bs (Z.to_nat (off + k)) = Some (wb 0).

  Lemma actx_strlen : forall depc mm mo loc Fc fcc errv LB buf len off bs
      (x1 t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word),
    actx depc mm mo loc Fc fcc errv LB buf len off bs -> pb_nul bs len off ->
    evt usegs (upd_post depc mo loc Fc fcc LB buf len off bs x1 x8 x9 x18 x19 x20 x21 x22 x23)
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 (buf + off)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
          Fc (Z_to_bv 64 0x22028) fcc None mm (seg_rom usegs)).
  Proof.
    intros until t6. intros CTX NUL.
    (nelim CTX 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    eapply evt_cut.
    { eapply (strlen_upd HI) with (off := off); [exact HL| eapply perm_in_head; exact HP| exact ARR| exact LEN| lia| exact NUL| exact MI| reflexivity]. }
    cbv beta. intros ms' PO.
    (nelim PO 23%nat; intros k t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MU WM MI' K0 K1 KN).
    apply evt_done. unfold upd_post. exists k. nexists 16%nat. split; [reflexivity|]. split; [| split; [exact K0| split; [exact K1| exact KN]]].
    split. { eapply (lh_frame HI); [exact HL| exact MU| exact WM| constructor]. }
    split; [exact HP|]. split; [eapply rw_cells_transport; [exact PBS0| exact MU| exact WM| exact I]|].
    split; [eapply u8arr_transport; [exact ARR| exact MU| exact WM| exact I]|]. split; [exact LEN|]. split; [exact PN|].
    split; [eapply rw_cells_transport; [exact FR| exact MU| exact WM| exact I]|].
    split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| exact I]|].
    split; [eapply rw_cells_transport; [exact ERR| exact MU| exact WM| exact I]|]. split; [exact MI'|].
    split; [eapply CJST_frame; [exact CJ| exact MU| exact WM| intros lo' hi' []]|]. split; [exact FRM|]. split; [exact FA|].
    eapply pv_agree_trans; [exact PVA|]. eapply magree_of_munch; [exact MU| exact WM| intros; exact I].
  Qed.

  (* [comment removed for export] *)
  Hypothesis SPRU : F_printf_iface.sprintf_u04x_stmt.

  Lemma actx_pstr : forall depc mm mo loc Fc fcc errv LB buf len off bs (ky : Z) (Bk : list cblock)
      (x1 t0 t1 t2 x8 x9 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word),
    actx depc mm mo loc Fc fcc errv LB buf len off bs ->
    cj_str m ky Bk -> (forall b, In b Bk -> In b B) ->
    SCPS usegs (rec_post depc loc Fc 0%nat 0 [] x1 x8 x9 x18 x19 x20 x21 x22 x23)
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 ky) (Z_to_bv 64 PB) a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
          Fc (wz PSTR_ENTRY) fcc None mm (seg_rom usegs)) mo.
  Proof.
    intros until t6. intros CTX SK SUB.
    pose proof (actx_tree _ _ _ _ _ _ _ _ _ _ _ _ CTX CH0) as CHn.
    pose proof (actx_str _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX SK SUB) as SKn.
    (nelim CTX 14%nat; intros HL HP PBS0 ARR LEN PN FR ST ERR MI CJ FRM FA PVA).
    pose proof CEIL as CEIL'. try rewrite alloc_ceiling_eq in CEIL'. unfold PV_STACK, PV_BASE in LO.
    (nelimp PL 4%nat; intros PL1 PL2 PL3 PL4). (nelimp PN 3%nat; intros PN1 PN2 PN3).
    assert (E1 : bv_unsigned (Z_to_bv 64 SPF) = SPF) by (apply unsigned_lit; lia).
    eapply scps_mono.
    { eapply (pstr_spec HI SPRU) with (lo := lo) (LR := LR) (bs := bs) (Bv := Bk); rewrite ?E1;
        first [ exact HL | exact HP | exact PBS0 | split; [exact ARR| exact LEN] | exact PN | exact SKn | exact CJ | exact ST | exact ERR | exact MI | exact TP | exact FRM | reflexivity
              | intros b Hb; apply BLR, SUB, Hb
              | split; [lia| split; [lia| split; [lia| exact PL4]]]
              | unfold PSTR_STACK, ENSURE_STACK, RMALLOC_STACK; lia | lia ]. }
    cbv beta. intros ms2 mo2 PO.
    (nelim PO 28%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Fc' fcc' m2 errv2 -> MI2 FRM2 FA2 ST2 ERR2 CJ2 PVE OUT)
.
    rewrite E1 in ST2, PVE.
    assert (AGR : forall a, 0 <= a < 2^64 -> (SPF <= a /\ (a < PB \/ PB + 64 <= a)) \/ (in_cblock LR a \/ (PDATA_LO <= a < PIMG_HI /\ ~ palloc_static a)) ->
                    m2 (wa a) = mm (wa a) /\ (wview usegs mm (wa a) <> None -> wview usegs m2 (wa a) <> None)).
    { intros a Ha Hc. apply PVE; [exact Ha|]. unfold cj_client_addr.
      destruct Hc as [[H1 H2]|[H1|H1]]; [split; [left; lia| lia]| |].
      - split; [right; right; exact H1|]. (nelim H1 4%nat; intros A' n' Hin Hr).
        (nelimp (lh_block_range HI _ _ _ _ _ _ HL ltac:(eapply Permutation_in; [exact HP| right; exact Hin])) 5%nat; intros _ _ _ X4 _).
        try rewrite alloc_ceiling_eq in X4. lia.
      - split; [right; left; exact H1|]. unfold PDATA_LO, PIMG_HI in H1. lia. }
    assert (FR2 : PVFRAME m2 loc) by (eapply (rw_cells_magree _ mm m2); [exact AGR| exact FR| cbn; intros a Ha; left; lia]).
    assert (PVA2 : pv_agree LR (bv_unsigned sp) PB m m2).
    { eapply pv_agree_trans; [exact PVA|]. eapply pv_agree_weaken; [exact PVE| lia| intros b Hb; exact Hb]. }
    assert (CH2 : cj_chain CJ_PRINTABLE m2 n p B).
    { eapply cj_chain_magree; [exact CHn| exact AGR|]. intros a nelH_; (nelim nelH_ 4%nat; intros A' n' Hin Hr). right; left. exists A', n'. split; [apply BLR; exact Hin| exact Hr]. }
    assert (FA2' : FAG18 F Fc'). { intros k Hk. rewrite (FA2 k ltac:(lia)). apply FA. exact Hk. }
    assert (FC2 : fctx m2 loc Fc' fcc' errv2).
    { split; [exact FR2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact CJ2|]. split; [exact FRM2|]. split; [exact FA2'|]. split; [exact PVA2| exact CH2]. }
    unfold rec_post. unfold wz in OUT.
    destruct OUT as (LB' & buf' & len' & off' & HL' & [(-> & dep' & PBS' & HB) | (-> & bs' & HP' & PBS' & PD' & PN' & NUL)]).
    - nexists 23%nat. split; [reflexivity|]. split; [exact HL'|]. split; [exact FC2|]. left. split; [reflexivity|]. exists dep'. split; [exact PBS'| exact HB].
    - nexists 23%nat. split; [reflexivity|]. split; [exact HL'|]. split; [exact FC2|]. right. split; [reflexivity|]. exists bs'. split; [| exact NUL].
      destruct PD' as [ARR' LEN'].
      split; [exact HL'|]. split; [exact HP'|]. split; [exact PBS'|]. split; [exact ARR'|]. split; [exact LEN'|]. split; [exact PN'|].
      split; [exact FR2|]. split; [exact ST2|]. split; [exact ERR2|]. split; [exact MI2|]. split; [exact CJ2|]. split; [exact FRM2|]. split; [exact FA2'| exact PVA2].
  Qed.
End S.


End CeilWrap.
