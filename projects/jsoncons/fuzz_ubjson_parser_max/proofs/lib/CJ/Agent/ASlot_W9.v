(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W2 ASlot_W3 ASlot_W4 ASlot_W5 ASlot_W6 ASlot_W7 ASlot_W8.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_ASlot_W9 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W9.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocFacts_AS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.RunP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["0A"; "1list"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2or"; "3Z"; "0RUNp"; "4ta_rel"; "5gmf"; "6mw_ok"; "7meta_slot"; "8disjoint_from"; "9alloc_ceiling"]; [":active"; ":aptr"; ":conc"; ":decay_bounces"; ":get_meta_rec"; ":m_avail"; ":m_freeable"; ":m_freed"; ":m_last_idx"; ":m_mem"; ":m_sizeclass"; ":meta"; ":mstate"; ":optr"; ":set_bounce"; ":upd_meta"]; [";In"; "<le"; "<lt"; "<pow"; "<sub"; "0W"; "0c"; "0f"; "0g"; "0hi"; "0i"; "0lo"; "0n"; "0q"; "0sc"; "0st"]; ["0st1"; "0v"]]).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Record gmf (st : mstate) (sc : Z) (g : aptr) : Prop := mkGMF {
gmf_slot : meta_slot st g;
gmf_avail : 0 <= m_avail (get_meta_rec st g) < 2^32;
gmf_freed : 0 <= m_freed (get_meta_rec st g) < 2^32;
gmf_mw : mw_ok (get_meta_rec st g);
gmf_sc48 : m_sizeclass (get_meta_rec st g) < 48;
gmf_cls : m_sizeclass (get_meta_rec st g) = sc;
gmf_grp : exists b gh, m_mem (get_meta_rec st g) = Some b /\ (s_groups st) !! b = Some gh /\ g_meta gh = Some g
/\ 0 <= g_active_idx gh <= m_last_idx (get_meta_rec st g)
/\ (m_sizeclass (get_meta_rec st g) = 0 -> g_active_idx gh = m_last_idx (get_meta_rec st g))
/\ (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h);
gmf_fbits : forall i, 0 <= i -> Z.testbit (m_freed (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g);
gmf_abits : forall i, 0 <= i -> Z.testbit (m_avail (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g);
gmf_links : exists n p, m_next (get_meta_rec st g) = Some n /\ m_prev (get_meta_rec st g) = Some p
}.
Record taf (st : mstate) (sc : Z) : Prop := mkTAF {
taf_head : forall g, active st sc = Some g -> gmf st sc g /\ m_sizeclass (get_meta_rec st g) = sc;
taf_next : forall g n, gmf st sc g -> m_next (get_meta_rec st g) = Some n ->
gmf st sc n /\ m_sizeclass (get_meta_rec st n) = m_sizeclass (get_meta_rec st g) /\ m_prev (get_meta_rec st n) = Some g;
taf_prev : forall g p, gmf st sc g -> m_prev (get_meta_rec st g) = Some p ->
gmf st sc p /\ m_next (get_meta_rec st p) = Some g;
taf_bnc : forall i, 0 <= bounces st i < 256
}.
Lemma gmf_geom : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W9 "R9'L'8&A':r2r4r3%43321';r5%23146'4&=%1247&Q1z&E&D%129<%311%6251&Q2&Q3+2+Q0%3221%5271%@271&G%11;%@2?1%:226%E221&<%11@'5&M&I%11Dr6%G21Q2%411%73641&H%11J%215%;3Q=21&J%11N%219%?3QA21&F%11Q2%21=%C3QE21&B%12Q?QB%22BQC%G3QI21%Q@251%QA2:1%QB2?1%QC2D1%QD2M1%QE2Q01%QF2Q61%QG2QE1p0QI1p0QM1pRBR31pRNR51pS2R71pS0R81").
Proof. intros st st1 sc g.
intros TR GM. destruct (tr_geom _ _ _ TR g) as (E1 & E2 & E3 & E4 & E5).
destruct (tr_mrange _ _ _ TR g (gmf_avail _ _ _ GM) (gmf_freed _ _ _ GM)) as [RA RF].
pose proof (gmf_mw _ _ _ GM) as MW. unfold mw_ok in *. rewrite E2, E3, E4, E5.
split; [eapply meta_slot_same_areas; [apply (tr_areas _ _ _ TR)| apply (gmf_slot _ _ _ GM)]|].
repeat (split; [first [assumption| lia| reflexivity]|]).
unfold conc, get_region. rewrite (tr_regions _ _ _ TR). reflexivity.
Qed.
Lemma disjoint_high : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W9 "N'1'3'8%2211%411&Q0(2r2r1%347721r5%63821&Q1&?v9%211%4291p061pRD@1pRHA1r3%9261&>r4%23>14p041p071pRJI1p2J1pR<I1").
Proof. intros W A n.
induction W as [|[lo hi] W IH]; intros HW HA; cbn; [exact I|].
split; [pose proof (HW lo hi ltac:(left; reflexivity)); lia|]. apply IH; [|exact HA]. intros lo' hi' Hin. apply (HW lo' hi'). right. exact Hin.
Qed.
Lemma decay_cases : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W9 "G'8'L'7'5&Cr2r1%3221%53712'6r3%7216&N&Q4+7%2251%431:;%>3@61qS4B1%:2C1%B2<1pS0D1pR>F1").
Proof. intros c st. unfold decay_bounces. destruct (_ && _); [right; eexists; reflexivity| left; reflexivity]. Qed.
Lemma active_decay : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W9 "@'8'L'5&M&@&Cr3r2%3221r1%6221%7242%:3921pRF=1pS0=1pR>?1").
Proof. intros c st i. destruct (decay_cases c st) as [-> | [v ->]]; reflexivity. Qed.
Lemma rec_decay : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W9 "A'8'L&A'5'K&D&Cr3r2%3221r1%6221%7242%:3921pRL<1pS0>1pR>@1").
Proof. intros c st q. destruct (decay_cases c st) as [-> | [v ->]]; reflexivity. Qed.
Lemma active_upd_meta : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W9 "E&A'Kp011'L'8'5&M&@&Or4r3r2%43321r1%7221%8242%;3:21pRF=1pS0?1pR@A1pRBD1").
Proof. intros g f st i. reflexivity. Qed.
Section PHASE.
Context {R : Type}.
Variables (K : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Variables (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (st : mstate) (m : mem) (sc lo : Z).
Variables (ra sp gp tp t0 t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis TAF : taf st sc.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 96.
Let spv := bv_unsigned sp.
Definition nclosed (stX : mstate) (P : aptr -> Prop) : Prop :=
forall q, P q -> gmf st sc q /\ exists t, m_next (get_meta_rec stX q) = Some t /\ P t.
End PHASE.
End CEIL_WRAP_1.
