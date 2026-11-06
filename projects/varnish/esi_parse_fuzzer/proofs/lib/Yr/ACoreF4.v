(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs AMTac AMalmys AMaly5g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AFreeB1 ATransp AFreeB5 ACoresk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ACoreF2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ACoreF2.

Module ACoreF3.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs AMTac AMalmys AMaly5g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AFreeB1 ATransp AFreeB5 ACoresk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ACoreF2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ACoreF2 AFre9ly AFreo3f.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMaly5g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeT.AFreeN OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoreF2.ACoreF OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoreF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFre9ly OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreo3f.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pasan).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).

Section CoreF3.
Context {Clg : Ceiling}.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition restF1R_stmt : Prop :=
    forall (rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (p n0 stkobj lo hi : Z) (key : list Z) (T : TSet),
      dealloc_core_pre rac spd tp m md A p n0 stkobj lo hi key ->
      p <> 0 -> n0 <= kQuarantineMaxSize ->
      a_cache_inited A = true -> pk_chunks (a_cache A kQuarantineBatchClass) = [] ->
      1 <= Z.of_nat (length (rg_free (a_reg A kQuarantineBatchClass))) ->
      (   (a_qthread A = [] /\ ~ ctail_covered A (n0 + kQuarantineBatchBytes))
       \/ (a_qthread A <> [] /\ Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 [])))) = kQuarantineBatchCount /\
           ~ ctail_covered A (q_bytes (a_qthread A) + n0 + kQuarantineBatchBytes))) ->
      dealloc_core_K rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 lo hi T ->
      srealizes (cl_segs LPA) (mkCfg (dealloc_entry_ms rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p stkobj) md) T.
  (* [comment removed for export] *)
  Definition restF2_stmt : Prop :=
    forall (rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (p n0 stkobj lo hi : Z) (key : list Z) (T : TSet),
      dealloc_core_pre rac spd tp m md A p n0 stkobj lo hi key ->
      p <> 0 -> n0 <= kQuarantineMaxSize ->
      a_cache_inited A = true -> pk_chunks (a_cache A kQuarantineBatchClass) = [] ->
      Z.of_nat (length (rg_free (a_reg A kQuarantineBatchClass))) = 0 ->
      (   a_qthread A = []
       \/ (a_qthread A <> [] /\ Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 [])))) = kQuarantineBatchCount)) ->
      dealloc_core_K rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 lo hi T ->
      srealizes (cl_segs LPA) (mkCfg (dealloc_entry_ms rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p stkobj) md) T.
  (* [comment removed for export] *)
  Definition restF0_stmt : Prop :=
    forall (rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (p n0 stkobj lo hi : Z) (key : list Z) (T : TSet),
      dealloc_core_pre rac spd tp m md A p n0 stkobj lo hi key ->
      p <> 0 -> n0 <= kQuarantineMaxSize ->
      a_cache_inited A = false -> a_qthread A = [] ->
      dealloc_core_K rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 lo hi T ->
      srealizes (cl_segs LPA) (mkCfg (dealloc_entry_ms rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p stkobj) md) T.

  (* [comment removed for export] *)
  Lemma qthread_cache_inited : forall A, WF A -> a_qthread A <> [] -> a_cache_inited A = true.
  Proof.
    intros A W QNE.
    destruct (a_qthread A) as [|b r] eqn:EQ; [congruence|].
    assert (INb : In b (a_qthread A)) by (rewrite EQ; left; reflexivity).
    destruct (wfQ A W) as (WQ1 & _). pose proof (proj1 (Forall_forall _ _) WQ1 b INb) as WB.
    unfold wf_batch_ in WB. (first [ dand3 WB as _ KB _ | destruct WB as (_ & KB & _) ]).
    (first [ pose proof ((wfR A W)) as dR_2; dand3 dR_2 as WR _ R3 | destruct (wfR A W) as (WR & _ & R3) ]). apply R3. exists kQuarantineBatchClass. split; [unfold kQuarantineBatchClass; lia|].
    destruct (WR kQuarantineBatchClass ltac:(unfold kQuarantineBatchClass; lia)) as (B1 & _). destruct B1 as [[AU1 AU2] _].
    unfold carved_count_ in KB. rewrite class_size_24 in KB. unfold kQuarantineBatchBytes in KB. intros E0. rewrite E0 in AU2.
    assert (rg_allocated_user (a_reg A kQuarantineBatchClass) / 8192 <= 0) by (apply Z.div_le_upper_bound; lia). lia.
  Qed.

  Theorem dealloc_core_restF_of : restF1R_stmt -> restF2_stmt -> restF0_stmt -> dealloc_core_restF.
  Proof.
    intros RF1R RF2 RF0. unfold dealloc_core_restF.
    intros rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T PRE NCOV KK.
    pose proof PRE as PRE'. unfold dealloc_core_pre in PRE'. cbv zeta in PRE'.
    (first [ dand19 PRE' as AI MI LV IAT TP CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR | destruct PRE' as (AI & MI & LV & IAT & TP & CEIL & LOW & SPHI & HISP & SPA & RA2 & ST & SMH & STLO & STHI & STO & TRW & KEYU & KR) ]).
    pose proof KK as KK0. subst tp. unfold dealloc_core_K in KK. cbv zeta in KK.
    cbn [cl_segs cl_free_pc LPA] in MI, KK |- *.
    assert (PNZ : p <> 0) by (intros E; apply NCOV; left; exact E).
    assert (HL : as_live A p = Some n0) by (destruct LV as [[E _]|LV]; [exfalso; exact (PNZ E)| exact LV]).
    destruct (Z.le_gt_cases n0 kQuarantineMaxSize) as [NQ|BIG]; [| exfalso; apply NCOV; right; left; exact BIG].
    pose proof (ai_wf _ _ _ _ _ _ _ AI) as WF0.
    (* [comment removed for export] *)
    assert (E24 : pk_chunks (a_cache A kQuarantineBatchClass) = [] /\
                  (a_qthread A = [] \/ (a_qthread A <> [] /\ Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 [])))) = kQuarantineBatchCount))).
    { destruct (a_qthread A) as [|b r] eqn:EQ.
      - split; [| left; reflexivity]. destruct (pk_chunks (a_cache A kQuarantineBatchClass)) eqn:EC; [reflexivity|].
        exfalso. apply NCOV. right; right. split; [exact NQ|]. right; left. split; [exact EQ| rewrite EC; discriminate].
      - rewrite <- EQ in *.
        assert (QNE : a_qthread A <> []) by (rewrite EQ; discriminate).
        (* [comment removed for export] *)
        assert (INl : In (last (a_qthread A) (BA 0 [])) (a_qthread A)).
        { rewrite <- (removelast_last_app (a_qthread A) (BA 0 []) QNE) at 2. apply in_or_app. right. left. reflexivity. }
        destruct (wfQ A WF0) as (WQ1 & _). pose proof (proj1 (Forall_forall _ _) WQ1 _ INl) as WB. unfold wf_batch_ in WB. (first [ dand3 WB as LB _ _ | destruct WB as (LB & _ & _) ]).
        assert (FULL : Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 [])))) = kQuarantineBatchCount).
        { destruct (Z.lt_ge_cases (Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 []))))) kQuarantineBatchCount) as [LT|GE]; [| clear -LB GE; lia].
          exfalso. apply NCOV. right; right. split; [exact NQ|]. left. exact (conj QNE LT). }
        split; [| right; exact (conj QNE FULL)].
        destruct (pk_chunks (a_cache A kQuarantineBatchClass)) eqn:EC; [reflexivity|].
        exfalso. apply NCOV. right; right. split; [exact NQ|]. right; right. split; [exact QNE|]. split; [exact FULL| rewrite EC; discriminate]. }
    destruct E24 as [E24 SHAPE].
    unfold kQuarantineMaxSize in NQ.
    destruct (a_cache_inited A) eqn:CI.
    - (* [comment removed for export] *)
      destruct (Z.le_gt_cases 1 (Z.of_nat (length (rg_free (a_reg A kQuarantineBatchClass))))) as [NF1|NF0].
      + (* [comment removed for export] *)
        destruct SHAPE as [QTE|[QNE FULL]].
        * destruct (classic (ctail_covered A (n0 + kQuarantineBatchBytes))) as [TC|NTC].
          -- apply ctail_pick in TC. destruct TC as [C|[C|C]].
             ++ exact (dealloc_new0GF rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                        AI MI HL IAT CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK TN QTE CI E24 NF1 C).
             ++ exact (dealloc_new0GF rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                        AI MI HL IAT CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK T0 QTE CI E24 NF1 C).
             ++ exact (dealloc_new0GF rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                        AI MI HL IAT CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK TA QTE CI E24 NF1 C).
          -- exact (RF1R rac spd gp _ t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                     PRE PNZ ltac:(unfold kQuarantineMaxSize; exact NQ) CI E24 NF1 (or_introl (conj QTE NTC)) KK0).
        * destruct (classic (ctail_covered A (q_bytes (a_qthread A) + n0 + kQuarantineBatchBytes))) as [TC|NTC].
          -- apply ctail_pick in TC. destruct TC as [C|[C|C]].
             ++ exact (dealloc_newfullGF rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                        AI MI HL IAT CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK TN QNE FULL CI E24 NF1 C).
             ++ exact (dealloc_newfullGF rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                        AI MI HL IAT CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK T0 QNE FULL CI E24 NF1 C).
             ++ exact (dealloc_newfullGF rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                        AI MI HL IAT CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK TA QNE FULL CI E24 NF1 C).
          -- exact (RF1R rac spd gp _ t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                     PRE PNZ ltac:(unfold kQuarantineMaxSize; exact NQ) CI E24 NF1 (or_intror (conj QNE (conj FULL NTC))) KK0).
      + (* [comment removed for export] *)
        exact (RF2 rac spd gp _ t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                 PRE PNZ ltac:(unfold kQuarantineMaxSize; exact NQ) CI E24 ltac:(clear -NF0; lia) SHAPE KK0).
    - (* [comment removed for export] *)
      destruct SHAPE as [QTE|[QNE _]]; [| exfalso; rewrite (qthread_cache_inited A WF0 QNE) in CI; discriminate].
      exact (RF0 rac spd gp _ t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
               PRE PNZ ltac:(unfold kQuarantineMaxSize; exact NQ) CI QTE KK0).
  Qed.
End CoreF3.
End ACoreF3.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARtSnjd AFreeR AFreeRC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRE.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFre1om AFreldj.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMaly5g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeT.AFreeN OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoreF2.ACoreF OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoreF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoreF4.ACoreF3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRE.AFreeRL OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFre1om OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreldj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pasan).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).

Section CoreF4.
Context {Clg : Ceiling}.
  Hypothesis SPDM : step_pdm_stmt.
  Hypothesis SSEC : step_sec_stmt.
  Hypothesis SBDM : step_bdm_stmt.

  Theorem restF1R_ok : restF1R_stmt.
  Proof.
    unfold restF1R_stmt.
    intros rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T PRE PNZ NQ CI E24 NF1 SHAPE KK.
    pose proof PRE as PRE'. unfold dealloc_core_pre in PRE'. cbv zeta in PRE'.
    (first [ dand19 PRE' as AI MI LV IAT TP CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR | destruct PRE' as (AI & MI & LV & IAT & TP & CEIL & LOW & SPHI & HISP & SPA & RA2 & ST & SMH & STLO & STHI & STO & TRW & KEYU & KR) ]).
    subst tp. unfold dealloc_core_K in KK. cbv zeta in KK.
    cbn [cl_segs cl_free_pc LPA] in MI, KK |- *.
    assert (HL : as_live A p = Some n0) by (destruct LV as [[E _]|LV]; [exfalso; exact (PNZ E)| exact LV]).
    (* [comment removed for export] *)
    assert (VB : forall a, newblk p n0 a -> a < alloc_ceiling).
    { intros a Ha. pose proof alloc_ceiling_val as CE. (first [ pose proof ((free_geom A m md p n0 AI HL)) as dR_2; dand4 dR_2 as PAL PLO PCE PHI | destruct (free_geom A m md p n0 AI HL) as (PAL & PLO & PCE & PHI) ]). destruct (free_n0 A m md p n0 AI HL) as [NR _].
      unfold newblk, blk in Ha. destruct Ha as [Ha|[_ Ha]].
      - clear -Ha PHI CE NR. lia.
      - unfold sh in Ha. clear -Ha PHI CE NR. kung_all.
        assert (p / 8 <= 2^44) by (apply Z.div_le_upper_bound; lia).
        assert ((n0 + 7) / 8 <= n0) by (apply Z.div_le_upper_bound; lia). unfold REQ_MAX in NR. lia. }
    unfold kQuarantineMaxSize in NQ.
    set (SP := fun A1 m1 md1 b0 i more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' c k n =>
                 SPDM rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T (Z_to_bv 64 n0) (Z_to_bv 64 (p + -16))
                      A1 m1 md1 b0 i more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' c k n CEIL LOW SPHI HISP SPA VB).
    set (SS := fun A1 m1 md1 b0 i more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s n =>
                 SSEC rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T (Z_to_bv 64 n0) (Z_to_bv 64 (p + -16))
                      A1 m1 md1 b0 i more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s n CEIL LOW SPHI HISP SPA VB).
    set (SB := fun A1 m1 md1 b0 more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' =>
                 SBDM rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T (Z_to_bv 64 n0) (Z_to_bv 64 (p + -16))
                      A1 m1 md1 b0 more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' CEIL LOW SPHI HISP SPA VB).
    (* [comment removed for export] *)
    assert (TKE : forall qb', ~ ctail_covered A qb' ->
              (a_qglobal A = [] /\ kQuarantineCacheSize < qb' /\ kQuarantineMaxSize < qb') \/
              (a_qglobal A <> [] /\ kQuarantineCacheSize < qb' /\ kQuarantineMaxSize < q_bytes (a_qglobal A) + qb')).
    { intros qb' NC. unfold ctail_covered in NC.
      destruct (a_qglobal A) as [|g r] eqn:EG.
      - left. split; [reflexivity|]. cbn in NC. clear -NC. lia.
      - right. split; [discriminate|]. rewrite <- EG in NC |- *. clear -NC. lia. }
    destruct SHAPE as [(QTE & NTC)|(QNE & FULL & NTC)].
    - destruct (TKE _ NTC) as [(QGE & C1 & C2)|(QGN & C1 & C2)].
      + exact (dealloc_new0RF rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                 AI MI HL IAT CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK VB SP SS SB T0 QTE CI E24 NF1 (conj C1 (conj QGE C2))).
      + exact (dealloc_new0RF rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                 AI MI HL IAT CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK VB SP SS SB TA QTE CI E24 NF1 (conj C1 (conj QGN C2))).
    - destruct (TKE _ NTC) as [(QGE & C1 & C2)|(QGN & C1 & C2)].
      + exact (dealloc_newfullRF rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                 AI MI HL IAT CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK VB SP SS SB T0 QNE FULL CI E24 NF1 (conj C1 (conj QGE C2))).
      + exact (dealloc_newfullRF rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                 AI MI HL IAT CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK VB SP SS SB TA QNE FULL CI E24 NF1 (conj C1 (conj QGN C2))).
  Qed.
End CoreF4.
