(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5 PmLibSpecsW_u5 PmRef_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RelLeaf.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5 ParseBridges3_u5 ParseNumberChk_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmall Require Import SmallWin_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmallW Require Import SmallPtW_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseW Require Import ParseNumberKW_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PNCW.
Import PNC PNKW.
(* [comment removed for export] *)
Inductive wkind : Set := WEntry | WGo | WFin | WErr | WApp | WSetEc | WEnd | WNone.
Definition wkind_eqb (a b : wkind) : bool :=
  match a, b with WEntry, WEntry | WGo, WGo | WFin, WFin | WErr, WErr | WApp, WApp | WSetEc, WSetEc | WEnd, WEnd | WNone, WNone => true | _, _ => false end.
Lemma wkind_eqb_eq : forall a b, wkind_eqb a b = true -> a = b.
Proof. intros [] [] H; try reflexivity; discriminate H. Qed.
Definition WK (i : nat) : wkind :=
  if Nat.eqb i 0 then WEntry
  else if Nat.leb i 12 then WGo
  else if Nat.leb i 16 then WFin
  else if Nat.leb i 21 then WErr
  else if Nat.leb i 28 then WGo
  else match kind_of i with KApp => WApp | KSetEc => WSetEc | KEnd => WEnd | KPre => WNone end.
(* [comment removed for export] *)
Definition NST (i : nat) : Z := nth i [-1; 0; 1; 2; 3; 4; 5; 6; 7; 3; 4; 2; 7; 1; 4; 2; 7; 0; 1; 3; 5; 6; 1; 2; 3; 4; 5; 6; 7] (-1).
(* [comment removed for export] *)
Definition ERRC (i : nat) : Z := nth i [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 19; 18; 19; 19; 19] 0.
Definition cutn (i : nat) : CC.cutpoint := nth i G.CPS CA.dummy_cp.
(* [comment removed for export] *)
Definition ECODE (i : nat) : Z := match CAX.cell_at (CC.cp_know (cutn i)) Eb 0 4 with Some (ELit z) => z | _ => -1 end.
(* [comment removed for export] *)
Definition NLIT (i : nat) : option Z := match nstc_of (cutn i) with Some (ELit c) => Some c | _ => None end.

(* [comment removed for export] *)
Definition cls (cells : list kentry) (f : Z -> bool) : bool :=
  match named_at cells CURJ with Some (_, EVar v, lo, hi) => PB.has cells (KBlob (SA SEG 0) WLEN 1) && SPTW.adm_all v cells lo (Z.to_nat (hi - lo + 1)) f | _ => false end%bool.
Definition acte (k : Z) (a : pact) (b : Z) : bool := pact_eqb (pn_act k b) a.
(* [comment removed for export] *)
Definition jpos (cells : list kentry) : bool := (lo_ge cells JV 1 || (rng_is cells (APC.esub WLEN JV) 0 && lo_ge cells WLEN 1))%bool.
(* [comment removed for export] *)
Definition jzero (cells : list kentry) : bool := rng_is cells JV 0.

Definition goto_chkw (i : nat) (nx : nat) (cells : list kentry) (j : nat) (s : CC.subst) : bool :=
  let jj := CC.esubstL GT.NF s JV in let tgt := APC.esub WEND jj in
  let d0 := rng_is cells (APC.esub tgt CURJ) 0 in
  let d1 := (rng_is cells (APC.esub tgt CURJ) 1 && jpos cells)%bool in
  if Nat.eqb i 0 then
    (wkind_eqb (WK j) WGo && rng_is cells (APC.esub WLEN jj) 0 && match CX.range3 cells NST0 with Some (cn, cn') => Z.eqb cn cn' && Z.eqb cn (NST j) | None => false end)%bool
  else
    (wkind_eqb (WK i) WGo && Nat.ltb 53 nx &&
     match WK j with
     | WGo => (d0 && Z.eqb (NST j) (NST i)) || (d1 && cls cells (acte (NST i) (PGo (NST j))))
     | WFin => d0 && Z.eqb (NST j) (NST i) && jpos cells && cls cells (acte (NST i) PEnd)
     | WErr => jpos cells && cls cells (acte (NST i) (PErr (ERRC j)))
     | _ => false
     end)%bool.
Definition call_chkw (i : nat) (nx : nat) (cells : list kentry) (regs : list expr) (pc : Z) (j : nat) : bool :=
  if Z.eqb pc APPR then
    match WK i, NLIT j with
    | WFin, None => (wkind_eqb (WK j) WApp && Nat.ltb 53 nx && Nat.ltb 53 (CC.cp_nx (cutn j) - APC.NCS - 2))%bool
    | WGo, Some c => (wkind_eqb (WK j) WApp && Nat.leb 22 i && Nat.ltb 53 nx && jzero cells && Z.eqb c (fixnst (NST i)))%bool
    | _, _ => false
    end
  else if Z.eqb pc SETEC then
    (wkind_eqb (WK j) WSetEc && match nth 11 regs (ELit 0) with ELit z => Z.eqb (ECODE j) z | _ => false end &&
     match WK i with
     | WErr => Z.eqb (ECODE j) (ERRC i)
     | WGo => Nat.ltb 53 nx && jpos cells && cls cells (acte (NST i) (PErr (ECODE j)))
     | _ => false
     end)%bool
  else if (Z.eqb pc ENDI || Z.eqb pc ENDF)%bool then
    (wkind_eqb (WK i) WApp && wkind_eqb (WK j) WEnd && match NLIT i with None => true | Some _ => false end && Nat.ltb 53 nx && PB.has cells (KBlob (SA SEG 0) WLEN 1))%bool
  else false.
Definition exit_chkw (i : nat) (nx : nat) (cells : list kentry) (regs : list expr) : bool :=
  match WK i with
  | WGo => Nat.leb i 12 && Nat.ltb 53 nx && rng_is cells (APC.esub WLEN JV) 0 && rng_is cells (APC.esub (nth 10 regs (ELit 0)) SEG) 0 && match view_chk 1 cells (nth i G.BLS []) with Some (_, _, pv) => match PB2.pv_nst pv with ELit cn => Z.eqb cn (fixnst (NST i)) | _ => false end | None => false end
  | WApp => match NLIT i with Some _ => true | None => false end
  | WSetEc => (negb (Z.eqb (ECODE i) 0) && match CAX.cell_at (cells16 cells) Eb 0 4 with Some (ELit z) => Z.eqb z (ECODE i) | _ => false end)%bool
  | WEnd => PB.has cells (KBlob (SA SEG 0) WLEN 1)
  | _ => false
  end%bool.
Definition wl_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  match t with
  | CC.TGoto j s => goto_chkw i (CC.cp_nx c) cells j s
  | CC.TOther pc => if Z.eqb pc RETPC then exit_chkw i (CC.cp_nx c) cells (CA.ps_reglist ps) else match CH2.ret_of G.RETS i k with Some j => call_chkw i (CC.cp_nx c) cells (CA.ps_reglist ps) pc j | None => false end
  end.
(* [comment removed for export] *)
Lemma wl_ok : CH2.leaves_all G.CPS G.TAGS wl_chk = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma WK_pre : forall i, kind_of i = KPre -> WK i = WEntry \/ WK i = WGo \/ WK i = WFin \/ WK i = WErr \/ WK i = WNone.
Proof.
  intros i H. unfold WK. destruct (Nat.eqb i 0); [left; reflexivity|]. destruct (Nat.leb i 12); [right; left; reflexivity|]. destruct (Nat.leb i 16); [right; right; left; reflexivity|].
  destruct (Nat.leb i 21); [right; right; right; left; reflexivity|]. destruct (Nat.leb i 28); [right; left; reflexivity|]. rewrite H. right; right; right; right; reflexivity.
Qed.
Lemma WK_ret : forall i, kind_of i <> KPre -> WK i = match kind_of i with KApp => WApp | KSetEc => WSetEc | KEnd => WEnd | KPre => WNone end.
Proof. intros i H. unfold WK. do 29 (destruct i as [|i]; [exfalso; apply H; reflexivity|]). cbn [Nat.eqb Nat.leb]. reflexivity. Qed.
Lemma wl_setec : forall i c k ps j, wl_chk i c k ps (CC.TOther SETEC) = true -> CH2.ret_of G.RETS i k = Some j ->
  WK j = WSetEc /\ (exists z, nth 11 (CA.ps_reglist ps) (ELit 0) = ELit z /\ ECODE j = z) /\ ((WK i = WErr /\ ECODE j = ERRC i) \/ (WK i = WGo /\ (53 < CC.cp_nx c)%nat /\ jpos (SR.ps_cells ps) = true /\ cls (SR.ps_cells ps) (acte (NST i) (PErr (ECODE j))) = true)).
Proof.
  intros i c k ps j H Hr. unfold wl_chk in H. replace (SETEC =? RETPC) with false in H by reflexivity. rewrite Hr in H. unfold call_chkw in H.
  replace (SETEC =? APPR) with false in H by reflexivity. rewrite Z.eqb_refl in H. apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [H1 HZ]. apply wkind_eqb_eq in H1. split; [exact H1|].
  split; [destruct (nth 11 (CA.ps_reglist ps) (ELit 0)) as [z| | | | | | |]; try discriminate HZ; exists z; apply Z.eqb_eq in HZ; split; [reflexivity | exact HZ]|].
  destruct (WK i); try discriminate H2; [right | left; split; [reflexivity | apply Z.eqb_eq in H2; exact H2]].
  apply andb_prop in H2 as [H2 HC]. apply andb_prop in H2 as [HN HJ]. apply Nat.ltb_lt in HN. split; [reflexivity|]. split; [exact HN|]. exact (conj HJ HC).
Qed.
Lemma wl_appr : forall i c k ps j, wl_chk i c k ps (CC.TOther APPR) = true -> CH2.ret_of G.RETS i k = Some j ->
  WK j = WApp /\ (53 < CC.cp_nx c)%nat /\
  ((WK i = WFin /\ NLIT j = None /\ (53 < CC.cp_nx (cutn j) - APC.NCS - 2)%nat) \/
   (exists cn, WK i = WGo /\ NLIT j = Some cn /\ (22 <= i)%nat /\ jzero (SR.ps_cells ps) = true /\ cn = fixnst (NST i))).
Proof.
  intros i c k ps j H Hr. unfold wl_chk in H. replace (APPR =? RETPC) with false in H by reflexivity. rewrite Hr in H. unfold call_chkw in H. rewrite Z.eqb_refl in H.
  destruct (WK i); try discriminate H; destruct (NLIT j) as [cn|] eqn:HL; try discriminate H.
  - apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply wkind_eqb_eq in H1. apply Nat.leb_le in H2. apply Nat.ltb_lt in H3. apply Z.eqb_eq in H5. split; [exact H1|]. split; [exact H3|]. right. exists cn. split; [reflexivity|]. split; [reflexivity|]. split; [exact H2|]. split; [exact H4 | exact H5].
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply wkind_eqb_eq in H1. apply Nat.ltb_lt in H2, H3. split; [exact H1|]. split; [exact H2|]. left. split; [reflexivity|]. split; [reflexivity | exact H3].
Qed.
Lemma wl_end : forall i c k ps pc j, pc = ENDI \/ pc = ENDF -> wl_chk i c k ps (CC.TOther pc) = true -> CH2.ret_of G.RETS i k = Some j ->
  WK i = WApp /\ WK j = WEnd /\ NLIT i = None /\ (53 < CC.cp_nx c)%nat /\ PB.has (SR.ps_cells ps) (KBlob (SA SEG 0) WLEN 1) = true.
Proof.
  intros i c k ps pc j Hpc H Hr. unfold wl_chk in H. destruct Hpc as [-> | ->].
  - replace (ENDI =? RETPC) with false in H by reflexivity. rewrite Hr in H. unfold call_chkw in H. replace (ENDI =? APPR) with false in H by reflexivity. replace (ENDI =? SETEC) with false in H by reflexivity.
    rewrite Z.eqb_refl in H. cbn [orb] in H. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply wkind_eqb_eq in H1, H2. apply Nat.ltb_lt in H4.
    destruct (NLIT i); [discriminate H3|]. split; [exact H1|]. split; [exact H2|]. split; [reflexivity|]. exact (conj H4 H5).
  - replace (ENDF =? RETPC) with false in H by reflexivity. rewrite Hr in H. unfold call_chkw in H. replace (ENDF =? APPR) with false in H by reflexivity. replace (ENDF =? SETEC) with false in H by reflexivity.
    replace (ENDF =? ENDI) with false in H by reflexivity. rewrite Z.eqb_refl in H. cbn [orb] in H. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply wkind_eqb_eq in H1, H2. apply Nat.ltb_lt in H4.
    destruct (NLIT i); [discriminate H3|]. split; [exact H1|]. split; [exact H2|]. split; [reflexivity|]. exact (conj H4 H5).
Qed.
Lemma wl_exit : forall i c k ps, wl_chk i c k ps (CC.TOther RETPC) = true -> exit_chkw i (CC.cp_nx c) (SR.ps_cells ps) (CA.ps_reglist ps) = true.
Proof. intros i c k ps H. unfold wl_chk in H. rewrite Z.eqb_refl in H. exact H. Qed.
Lemma wl_exit_go : forall i nx cells regs, exit_chkw i nx cells regs = true -> WK i = WGo ->
  (53 < nx)%nat /\ rng_is cells (APC.esub WLEN JV) 0 = true /\ rng_is cells (APC.esub (nth 10 regs (ELit 0)) SEG) 0 = true /\
  exists pe ce pv cn, view_chk 1 cells (nth i G.BLS []) = Some (pe, ce, pv) /\ PB2.pv_nst pv = ELit cn /\ cn = fixnst (NST i).
Proof.
  intros i nx cells regs H HW. unfold exit_chkw in H. rewrite HW in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3']. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Nat.ltb_lt in H2.
  split; [exact H2|]. split; [exact H3|]. split; [exact H3'|]. destruct (view_chk 1 cells (nth i G.BLS [])) as [[[pe ce] pv]|]; [|discriminate H4]. destruct (PB2.pv_nst pv) as [cn| | | | | | |] eqn:Hn; try discriminate H4.
  exists pe, ce, pv, cn. apply Z.eqb_eq in H4. split; [reflexivity|]. split; [exact Hn | exact H4].
Qed.
Lemma wl_exit_app : forall i nx cells regs, exit_chkw i nx cells regs = true -> WK i = WApp -> exists cn, NLIT i = Some cn.
Proof. intros i nx cells regs H HW. unfold exit_chkw in H. rewrite HW in H. destruct (NLIT i) as [cn|]; [exists cn; reflexivity | discriminate H]. Qed.
Lemma wl_exit_setec : forall i nx cells regs, exit_chkw i nx cells regs = true -> WK i = WSetEc -> ECODE i <> 0 /\ exists z, CAX.cell_at (cells16 cells) Eb 0 4 = Some (ELit z) /\ z = ECODE i.
Proof.
  intros i nx cells regs H HW. unfold exit_chkw in H. rewrite HW in H. apply andb_prop in H as [H1 H2]. apply negb_true_iff in H1. apply Z.eqb_neq in H1. split; [exact H1|].
  destruct (CAX.cell_at (cells16 cells) Eb 0 4) as [[z| | | | | | |]|]; try discriminate H2. exists z. apply Z.eqb_eq in H2. split; [reflexivity | exact H2].
Qed.
Lemma wl_exit_other : forall i nx cells regs, exit_chkw i nx cells regs = true -> WK i <> WEntry /\ WK i <> WFin /\ WK i <> WErr /\ WK i <> WNone.
Proof. intros i nx cells regs H. unfold exit_chkw in H. destruct (WK i); repeat split; try discriminate. Qed.
Lemma wl_exit_end : forall i nx cells regs, exit_chkw i nx cells regs = true -> WK i = WEnd -> PB.has cells (KBlob (SA SEG 0) WLEN 1) = true.
Proof. intros i nx cells regs H HW. unfold exit_chkw in H. rewrite HW in H. exact H. Qed.
End PNCW.
