(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free MallocModel_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Export MallocKit_B3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.


Ltac rctx_same := intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RMallocKit_B3 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.set_usage"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.upd_ctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.set_seq"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.b8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.set_unmap_seq_map"; "stdpp.base.insert"; "stdpp.gmap.gmap"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.Z_countable"; "stdpp.fin_maps.map_insert"; "stdpp.gmap.gmap_partial_alter"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_unmap_seq"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.N"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.eq"; "stdpp.base.lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cellval"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cell_read"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_shadow"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.Unknown"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.del_group"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"].


(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
#[using="Type"] Lemma rmrep_set_usage : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B3 ()) "Pst,$0.Pm,P,(1.&40.)(2.(1.&8.))Psc,$3.Pv,$3.P,(4.VhRP,R4.R3.)P,(5.(6.=R3.)(7.R3.+30.))(4.VhRP,(8.R4.R3.R6.)(9.R5.(:.(;.(;.$<.+1=0.)(=.+8.R4.)))(>.(?.R3.))))")
(* [comment removed for export] *).
Proof.
  intros st m sc v MR Hsc. dpose MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (length_le8 (wz v)) as L8.
  pose proof (munch_write [(RCTX + 464 + 8 * sc, RCTX + 464 + 8 * sc + 8)] m m (RCTX + 464 + 8 * sc) (le8 (wz v)) (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(rewrite L8; unfold RCTX; lia) ltac:(rewrite L8; cbn [inside]; lia)) as MU.
  pose proof (wmono_write rsegs m m (wa (RCTX + 464 + 8 * sc)) (le8 (wz v)) (wmono_refl rsegs m)) as WM.
  eapply (rmrep_ctx_frameW st (set_usage sc v st) m _ _ MR MU WM); try reflexivity.
  - rctx_same.
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - left. rewrite usages_set_usage by lia. replace (RCTX + 464 + 8 * sc) with ((RCTX + 464) + 8 * sc) by lia.
    apply u64arr_write; [exact X3| rewrite usages_length; lia].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [| rctx_same].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx set_usage upd_ctx c_seq c_brk set_usage_map]. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_set_seq : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B3 ()) "Pst,$0.Pm,P,(1.&40.)(2.(1.&8.))Pv,$3.P,(4.VhRP,R3.R2.)P,(5.(6.=R2.)(7.R2.+100.))(4.VhRP,(10.(11.R3.)R5.)(9.R4.(:.(;.$<.+390.))(12.(1.&8.)(13.R3.)(14.(1.&8.)))))")
(* [comment removed for export] *).
Proof.
  intros st m v MR Hv. dpose MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (munch_write [(RCTX + 912, RCTX + 913)] m m (RCTX + 912) [b8 v] (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
  pose proof (wmono_write rsegs m m (wa (RCTX + 912)) [b8 v] (wmono_refl rsegs m)) as WM.
  eapply (rmrep_ctx_frameW st (upd_ctx (set_seq v) st) m _ _ MR MU WM); try reflexivity.
  - rctx_same.
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - left.
    pose proof (rw_cells_write rsegs m (RCTX + 912) (ctx_tail_cells st) 0 (C1 (b8 (c_seq (ctx st)))) (C1 (b8 v)) X6 eq_refl eq_refl I) as W.
    rewrite Z.add_0_r in W. cbn [cbytes cell_upd ctx_tail_cells Nat.eqb] in W.
    unfold ctx_tail_cells, brk_word, ctx in *. cbn [s_ctx upd_ctx set_seq c_seq c_brk]. exact W.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_set_unmap_seq : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B3 ()) "Pst,$0.Pm,P,(1.&40.)(2.(1.&8.))Pi,$3.Pv,$3.P,(4.VhRP,R4.R3.)P,(5.(6.=R3.)(7.R3.+20.))(4.VhRP,(10.Lc,$15.(16.(17.$3.$3.(18.$3.$19.$1:.$3.)(1;.$3.$3.(18.$3.$19.$1:.$3.)(1<.$3.$19.$1:.$3.))R5.R4.(1=.R1.))R1.)R6.)(9.R5.(:.(;.(;.$<.+350.)R4.))(12.(1.&8.)(13.R3.)(14.(1.&8.)))))")
(* [comment removed for export] *).
Proof.
  intros st m i v MR Hi. dpose MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (munch_write [(RCTX + 848 + i, RCTX + 848 + i + 1)] m m (RCTX + 848 + i) [b8 v] (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
  pose proof (wmono_write rsegs m m (wa (RCTX + 848 + i)) [b8 v] (wmono_refl rsegs m)) as WM.
  eapply (rmrep_ctx_frameW st _ m _ _ MR MU WM); try reflexivity.
  - rctx_same.
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - left. rewrite unmap_seqs_set by lia. replace (RCTX + 848 + i) with ((RCTX + 848) + i) by lia.
    apply (u8arr_write rsegs m (RCTX + 848) (unmap_seqs st) i (b8 v)); [exact X4| rewrite unmap_seqs_length; lia].
  - right. split; [reflexivity| rctx_same].
  - right. split; [| rctx_same].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_group_hdr_zero : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B3 ()) "Pst,$0.Pm,P,(1.&40.)(2.(1.&8.))Pp,(1>.$1?.$3.)Pgh,$20.Pbs,(21.(1.&8.))P,(4.VhRP,R5.R4.)P,(22.(2.$20.)(23.(1>.$1?.$3.)$20.(18.$24.(25.$1?.$26.$3.$19.)(27.$1?.$26.$28.$3.$19.$1:.)$20.)(29.$24.(25.$1?.$26.$3.$19.)(27.$1?.$26.$28.$3.$19.$1:.)$20.)R4.(2:.R6.))(2;.$20.R3.))P,Po,$3.P,(5.(6.=R1.)(7.R1.+<.))(2<.$3.Lh,$3.(22.$2=.(2>.(2?.R:.(30.$1?.$3.R8.))(;.(31.$1?.$3.R8.)R3.))(32.R1.)))P,(22.$33.(34.(1.&8.)R4.)#8.)(4.VhRP,(35.R7.R9.)(9.R8.(:.(36.R9.R7.))R5.))")
(* [comment removed for export] *).
Proof.
  intros st m p gh bs MR Hp UNK L8.
  pose proof MR as (WF & _). dpose WF as ((Hres & RPHres) & WR & DJ & WA & WG).
  ddestruct (rgroup_conc st p gh WF Hp) as (r & Hr & Cp & Kr & Sp0 & Sp1 & SpA & RB0 & RBC).
  destruct (WR _ r Hr) as (_ & RBAL & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
  pose proof (round_up_pg_ge (r_len r)) as RU. rceilb.
  eapply rmrep_transport_unowned.
  - apply rmrep_del_group. exact MR.
  - apply (munch_write [(conc st p, conc st p + 8)] m m (conc st p) bs (munch_refl _ m)); [lia| rewrite L8; cbn; lia| rewrite L8; cbn [inside]; lia].
  - apply wmono_write. apply wmono_refl.
  - intros lo hi a [E|[]] Ha. inversion E; subst lo hi. clear E.
    intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
    + unfold RCTX in C. lia.
    + unfold RMLOCK in C. lia.
    + unfold RNEED_LOCKS in C. lia.
    + unfold RPAGE_SIZE in C. lia.
    + ddestruct C as (ak & ar & Hak & Hin). cbn in Hak.
      ddestruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
      assert (NE : fst ak <> fst p) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
      change (conc (del_group p st) ak) with (conc st ak) in Hin.
      pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Kr).
      destruct (DJ (fst ak) ra (fst p) r Hra Hr NE); lia.
    + ddestruct C as (b & gh' & Hb & Hin). cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [NEb Hb].
      change (conc (del_group p st) b) with (conc st b) in Hin.
      ddestruct (rgroup_conc st b gh' WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & _).
      destruct (N.eq_dec (fst b) (fst p)) as [E|NE].
      * rewrite E, Hr in Hrb. inversion Hrb; subst rb.
        assert (snd b <> snd p) by (intros E2; apply NEb; destruct b, p; cbn in *; congruence).
        Z.div_mod_to_equations. lia.
      * pose proof (lr_lo_group rb Krb). pose proof (lr_lo_group r Kr). destruct (DJ (fst b) rb (fst p) r Hrb Hr NE); lia.
    + ddestruct C as (rid & r' & v & Hr' & Hk' & Hin & HC). cbn in Hr'. change (get_shadow (del_group p st) rid) with (get_shadow st rid) in HC.
      destruct (N.eq_dec rid (fst p)) as [E|NE].
      * subst rid. rewrite Hr in Hr'. inversion Hr'; subst r'.
        destruct (UNK (a - r_base r - snd p) ltac:(lia)) as [h Hh].
        replace (snd p + (a - r_base r - snd p)) with (a - r_base r) in Hh by lia. rewrite Hh in HC. discriminate.
      * pose proof (lr_lo_group r' Hk'). pose proof (lr_lo_group r Kr). destruct (DJ rid r' (fst p) r Hr' Hr NE); lia.
    + unfold RGOT_SSP in C. lia.
    + unfold RSSP_GUARD in C. lia.
Qed.

#[using="Type"] Lemma rmrep_grp_del_eq : forall st m g p, rmrep (del_group p st) m -> rmrep (grp_del st g p) m.
Proof. intros. unfold grp_del. apply rmrep_del_slots. exact H. Qed.

End RP_1.
