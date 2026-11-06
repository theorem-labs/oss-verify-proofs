(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState LayoutPA AInv ALogic1 ALogic.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require APopP.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB1F ACoresk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ACoreF2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ACoreF2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ACoreF4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ACoreF5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFPopEnd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFPopEnd.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APopP.APopK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1F OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoreF2.ACoreF OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoreF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoreF4.ACoreF3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoreF5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFPopEnd.AFPopT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFPopEnd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pasan).

Notation wz z := (Z_to_bv 64 z) (only parsing).

Section CoreF6.
Context {Clg : Ceiling}.

  (* [comment removed for export] *)
  Theorem fpop_core : forall (rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (md : Model) (A : AState) (p n0 stkobj lo hi : Z) (key : list Z) (T : TSet) (t0 t1 t2 a2 a3 a6 a7 t3 t4 t5 t6 : word),
    dealloc_core_pre rac spd (cl_tp LPA) m md A p n0 stkobj lo hi key ->
    as_live A p = Some n0 -> n0 <= 2^28 ->
    pk_chunks (a_cache A 24) = [] -> Z.of_nat (length (rg_free (a_reg A 24))) < refill_count 24 ->
    (a_qthread A = [] \/ (a_qthread A <> [] /\ Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 [])))) = kQuarantineBatchCount)) ->
    dealloc_core_K rac spd gp (cl_tp LPA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 lo hi T ->
    srealizes (cl_segs LPA) (mkCfg (dealloc_entry_ms rac spd gp (cl_tp LPA) t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p stkobj) md) T.
  Proof.
    intros rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 stkobj lo hi key T t0 t1 t2 a2 a3 a6 a7 t3 t4 t5 t6 PRE HL NQ EMP SHORT SHAPE KK.
    unfold dealloc_entry_ms.
    exact (fpop_core_gen rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT SHAPE T
             (fun Mk mdk md' v5 junk0 pad scr ksc tq0 tq1 tq2 aq1 aq2 aq3 aq4 aq5 aq6 aq7 tq3 tq4 tq5 tq6 a0g na MSH PM HI5 SB5 CL5 GPK =>
                kend_all rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 stkobj lo hi key PRE HL NQ EMP SHORT SHAPE T KK
                         Mk mdk md' v5 junk0 pad scr ksc na MSH PM HI5 SB5 CL5 GPK tq0 tq1 tq2 aq1 aq2 aq3 aq4 aq5 aq6 aq7 tq3 tq4 tq5 tq6 a0g)
             t0 t1 t2 a2 a3 a6 a7 t3 t4 t5 t6).
  Qed.

  Theorem restF2_ok : restF2_stmt.
  Proof.
    unfold restF2_stmt.
    intros rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T PRE PNZ NQ CI E24 NF0 SHAPE KK.
    assert (TPE : tp = cl_tp LPA) by ((first [ dand6 PRE as _ _ _ _ X _ | destruct PRE as (_ & _ & _ & _ & X & _) ]); exact X). subst tp.
    assert (HL : as_live A p = Some n0) by ((first [ dand4 PRE as _ _ [[E _]|LV] _ | destruct PRE as (_ & _ & [[E _]|LV] & _) ]); [exfalso; exact (PNZ E)| exact LV]).
    apply (fpop_core rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 stkobj lo hi key T t0 t1 t2 a2 a3 a6 a7 t3 t4 t5 t6 PRE HL).
    - unfold kQuarantineMaxSize in NQ. exact NQ.
    - exact E24.
    - change 24 with kQuarantineBatchClass. rewrite NF0, refill_count_24. lia.
    - exact SHAPE.
    - exact KK.
  Qed.

  Theorem restF0_ok : restF0_stmt.
  Proof.
    unfold restF0_stmt.
    intros rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T PRE PNZ NQ CI QTE KK.
    assert (TPE : tp = cl_tp LPA) by ((first [ dand6 PRE as _ _ _ _ X _ | destruct PRE as (_ & _ & _ & _ & X & _) ]); exact X). subst tp.
    assert (HL : as_live A p = Some n0) by ((first [ dand4 PRE as _ _ [[E _]|LV] _ | destruct PRE as (_ & _ & [[E _]|LV] & _) ]); [exfalso; exact (PNZ E)| exact LV]).
    pose proof (ai_wf _ _ _ _ _ _ _ (proj1 PRE)) as W0.
    assert (CR : 1 <= 24 <= 30) by lia.
    apply (fpop_core rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 stkobj lo hi key T t0 t1 t2 a2 a3 a6 a7 t3 t4 t5 t6 PRE HL).
    - unfold kQuarantineMaxSize in NQ. exact NQ.
    - (* [comment removed for export] *)
      (first [ pose proof ((wfC A W0)) as dR_5; dand3 dR_5 as WC _ _ | destruct (wfC A W0) as (WC & _ & _) ]). (first [ pose proof ((WC 24 ltac:(lia))) as dR_6; dand4 dR_6 as _ _ _ EC | destruct (WC 24 ltac:(lia)) as (_ & _ & _ & EC) ]). cbv zeta in EC. exact (EC CI).
    - (* [comment removed for export] *)
      pose proof (ar_nfcc A 24 W0 CR) as NFC. pose proof (ar_reg A 24 W0 CR) as ((R1 & _) & _). pose proof (ar_csr 24 CR) as CSR.
      (first [ pose proof ((wfR A W0)) as dR_7; dand3 dR_7 as _ _ R3 | destruct (wfR A W0) as (_ & _ & R3) ]).
      assert (MU0 : rg_mapped_user (a_reg A 24) = 0).
      { destruct (Z.eq_dec (rg_mapped_user (a_reg A 24)) 0) as [E|NE]; [exact E|]. exfalso.
        assert (X : a_cache_inited A = true) by (apply R3; exists 24; split; [lia| exact NE]). rewrite CI in X. discriminate X. }
      assert (AU0 : rg_allocated_user (a_reg A 24) = 0) by lia. rewrite AU0 in NFC. rewrite Z.div_0_l in NFC by lia.
      change 24 with kQuarantineBatchClass at 2. rewrite refill_count_24. lia.
    - left. exact QTE.
    - exact KK.
  Qed.
End CoreF6.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
