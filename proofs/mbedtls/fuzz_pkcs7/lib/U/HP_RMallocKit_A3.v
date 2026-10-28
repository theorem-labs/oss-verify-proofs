(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast MallocTree MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B3 HP_RMallocKit_A HP_RMallocKit_A2 HP_RMalloc_fp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RMallocKit_A3 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.set_bounce"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.b8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.N"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.N.eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cellval"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cell_read"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_shadow"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.Unknown"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.pw"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Stdlib.ZArith.BinInt.Z.land"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.put_group"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mkGhdr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.set_group_active_idx"].



Section RP_1. Context {hRP : run_params}.
#[using="Type"] Lemma rmrep_set_bounce : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_A3 ()) "Pst,$0.Pm,P,(1.&40.)(2.(1.&8.))Pi,$3.Pv,$3.P,(4.VhRP,R4.R3.)P,(5.(6.=R3.)(7.R3.+20.))(4.VhRP,(8.R4.R3.R6.)(9.R5.(:.(;.(;.$<.+370.)R4.))(=.(1.&8.)(>.R3.)(?.(1.&8.)))))")
(* [comment removed for export] *).
Proof.
  intros st m i v MR Hi. dpose MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (munch_write [(RCTX + 880 + i, RCTX + 880 + i + 1)] m m (RCTX + 880 + i) [b8 v] (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
  pose proof (wmono_write rsegs m m (wa (RCTX + 880 + i)) [b8 v] (wmono_refl rsegs m)) as WM.
  eapply (rmrep_ctx_frameW st _ m _ _ MR MU WM); try reflexivity.
  - rctx_same.
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - left. rewrite bouncess_set by lia. replace (RCTX + 880 + i) with ((RCTX + 880) + i) by lia.
    apply (u8arr_write rsegs m (RCTX + 880) (bouncess st) i (b8 v)); [exact X5| rewrite bouncess_length; lia].
  - right. split; [| rctx_same].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx c_seq c_brk set_bounces_map]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
End RP_1.
Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame rsegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write rsegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write rsegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv rsegs mX |- _ =>
      apply (mem_inv_store rsegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

(* [comment removed for export] *)
Ltac rraw_store_finish0 A bs' MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write rsegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv rsegs mX |- _ =>
      apply (mem_inv_store rsegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RP_2. Context {hRP : run_params}.
#[using="Type"] Lemma rconc_meta_inj : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_A3 ()) "Pst,$0.Pm,P,(1.&40.)(2.(1.&8.))Pg,$10.Pq,$10.P,(4.VhRP,R4.R3.)P,(11.R5.R3.)P,(11.R6.R3.)P,(12.$3.(13.R7.R4.)(13.R7.R5.))(12.$10.R5.R6.)")
(* [comment removed for export] *).
Proof.
  (intros st m g q MR dd_H; ddestruct dd_H as (a & ar & k & Ha & Hk & Eg); intros dd_H; ddestruct dd_H as (a' & ar' & k' & Ha' & Hk' & Eqq); intros E).
  pose proof MR as (WF & _). dpose WF as (_ & WR & DJ & _).
  ddestruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
  ddestruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  assert (HQ : conc st q = conc st a' + (AREA_HDR + META_SIZE * k')) by (rewrite Eqq, conc_aadd by (rewrite Hra'; eauto); reflexivity).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  destruct (N.eq_dec (fst a') (fst a)) as [Ef|NEf].
  - rewrite Ef, Hra in Hra'. inversion Hra'; subst ra'.
    assert (snd a' = snd a /\ k' = k) as [E1 E2] by (Z.div_mod_to_equations; nia).
    rewrite Eqq, Eg. unfold aadd. rewrite Ef, E1, E2. reflexivity.
  - exfalso. pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra'). destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NEf); lia.
Qed.

End RP_2.
Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRnew : rmrep st' mX)
      by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
          eapply rw_cells_congr; [ | | | exact CH];
          [ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
            unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
          | reflexivity | cbn; tauto]);
    clear MUq WMq CH end.

(* [comment removed for export] *)
Ltac rmchunk MR MSq CH :=
  pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
  rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
  rewrite ?get_meta_rec_put_same in CH;
  rewrite ?conc_put_meta, ?pw_put_meta in CH;
  cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
       m_set_prev m_set_next m_set_mem m_set_avail m_set_freed] in CH;
  unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

Section RP_3. Context {hRP : run_params}.
#[using="Type"] Lemma rmrep_regroup : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_A3 ()) "Pst,$0.Pm,P,(1.&40.)(2.(1.&8.))Pm',P,(1.&40.)(2.(1.&8.))Pb,(14.$15.$3.)Pgh,$16.Pg,$10.Pai,$3.Pw8',(1.&8.)P,(4.VhRP,R8.R7.)P,(12.(2.$16.)(17.(14.$15.$3.)$16.(18.$10.(19.$15.$1:.$3.$1;.)(1<.$15.$1:.$1=.$3.$1;.$1>.)$16.)(1?.$10.(19.$15.$1:.$3.$1;.)(1<.$15.$1:.$1=.$3.$1;.$1>.)$16.)R6.(20.R9.))(21.$16.R5.))P,Po,$3.P,(5.(6.=R1.)(7.R1.+9.))(22.$3.Lh,$3.(12.$23.(24.(25.R=.(26.$15.$3.R:.))(;.(27.$15.$3.R:.)R3.))(28.R1.)))P,(29.(=.(14.$3.$3.)(2:.$3.$3.(13.R;.R8.)(;.(13.R;.R8.)+9.))(?.(14.$3.$3.)))R:.R9.)P,(2;.$2<.R;.R:.)P,(2=.$2<.R;.(13.R=.R:.)(=.$2>.(2?.(30.R=.(21.$10.R8.)))(=.$2>.(31.R6.)(?.$2>.))))P,(12.$3.(32.(33.&8.R7.)+1?.)(32.R8.+1?.))(4.VhRP,(34.R<.(21.$10.R:.)R9.R?.)R=.)")
(* [comment removed for export] *).
Proof.
  intros st m m' b gh g ai w8' MR Hb UNK MU WM RC Hw8.
  pose proof MR as (WF & _). dpose WF as ((RS & RPRS) & WR & DJ & WA & WG).
  ddestruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & B0 & B16 & BA & RB0 & RC0).
  pose proof (rmrep_del_group st m b MR) as MR1.
  assert (MR2 : rmrep (del_group b st) m').
  { eapply (rmrep_transport_unowned _ _ _ _ MR1 MU WM). apply ivs_avoid_cons; [|apply ivs_avoid_nil].
    intros a Ha RF. ddestruct (WR (fst b) r Hr) as (_ & _ & _ & _ & RFr). destruct (rreserved_disjoint _ _ RFr) as (I1 & _ & I23 & I2).
    pose proof (round_up_pg_ge (r_len r)).
    destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b2 & gh2 & Hb2 & Rb2)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
    - unfold RCTX in R1. lia.
    - unfold RMLOCK in R2. lia.
    - unfold RNEED_LOCKS in R3. lia.
    - unfold RPAGE_SIZE in R4. lia.
    - change (s_areas (del_group b st)) with (s_areas st) in Hak. change (conc (del_group b st) ak) with (conc st ak) in Rak.
      ddestruct (rarea_conc st ak ar WF Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NE : fst ak <> fst b) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
      pose proof (rarea_lr_lo st ak ar rga WF Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr) in D; lia.
    - unfold del_group in Hb2. cbn [s_groups set_groups] in Hb2. change (conc (del_group b st) b2) with (conc st b2) in Rb2.
      destruct (decide (b2 = b)) as [->|NE2]; [rewrite lookup_delete_eq in Hb2; discriminate|].
      rewrite lookup_delete_ne in Hb2 by congruence.
      ddestruct (rgroup_conc st b2 gh2 WF Hb2) as (r2 & Hr2 & Cb2 & Kr2 & B20 & B216 & B2A & _).
      destruct (N.eq_dec (fst b2) (fst b)) as [E|NE].
      + rewrite E, Hr in Hr2. inversion Hr2; subst r2.
        assert (snd b2 <> snd b) by (intros E2; apply NE2; destruct b, b2; cbn in *; congruence).
        assert (snd b2 + 16 <= snd b \/ snd b + 16 <= snd b2) by (Z.div_mod_to_equations; lia). lia.
      + destruct (DJ _ _ _ _ Hr2 Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr), ?(lr_lo_group r2 Kr2) in D; lia.
    - change (s_regions (del_group b st)) with (s_regions st) in Hq. change (get_shadow (del_group b st) q) with (get_shadow st q) in Cq.
      destruct (N.eq_dec q (fst b)) as [->|NE].
      + rewrite Hr in Hq. inversion Hq; subst rq.
        destruct (UNK (a - r_base r - snd b) ltac:(lia)) as [h Hh]. replace (snd b + (a - r_base r - snd b)) with (a - r_base r) in Hh by lia.
        rewrite Hh in Cq. discriminate.
      + pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr) in D; lia.
    - unfold RGOT_SSP in R8. lia.
    - unfold RSSP_GUARD in R9. lia. }
  rewrite <- put_group_del.
  eapply (rmrep_put_group_new _ _ b _ ai r w8' MR2); [ | exact Hr | exact Kr | exact B0 | exact B16 | exact BA | exact RC | exact Hw8].
  unfold del_group. cbn [s_groups set_groups]. apply lookup_delete_eq.
Qed.

#[using="Type"] Lemma rmrep_set_group_ai : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_A3 ()) "Pst,$0.Pm,P,(1.&40.)(2.(1.&8.))Pm',P,(1.&40.)(2.(1.&8.))Pb,(14.$15.$3.)Pg,$10.Pai0,$3.Pai,$3.Pw8',(1.&8.)P,(4.VhRP,R8.R7.)P,(12.(2.$16.)(17.(14.$15.$3.)$16.(18.$10.(19.$15.$1:.$3.$1;.)(1<.$15.$1:.$1=.$3.$1;.$1>.)$16.)(1?.$10.(19.$15.$1:.$3.$1;.)(1<.$15.$1:.$1=.$3.$1;.$1>.)$16.)R6.(20.R9.))(21.$16.(35.(21.$10.R5.)R4.)))P,Po,$3.P,(5.(6.=R1.)(7.R1.+9.))(22.$3.Lh,$3.(12.$23.(24.(25.R=.(26.$15.$3.R:.))(;.(27.$15.$3.R:.)R3.))(28.R1.)))P,(29.(=.(14.$3.$3.)(2:.$3.$3.(13.R;.R8.)(;.(13.R;.R8.)+9.))(?.(14.$3.$3.)))R:.R9.)P,(2;.$2<.R;.R:.)P,(2=.$2<.R;.(13.R=.R:.)(=.$2>.(2?.(30.R=.(21.$10.R9.)))(=.$2>.(31.R6.)(?.$2>.))))P,(12.$3.(32.(33.&8.R7.)+1?.)(32.R8.+1?.))(4.VhRP,(36.R<.R9.R?.)R=.)")
(* [comment removed for export] *).
Proof.
  intros st m m' b g ai0 ai w8' MR Hb UNK MU WM RC Hw8. rewrite (set_group_ai_eq st b _ ai Hb), put_group_del. cbn [g_meta].
  eapply rmrep_regroup; eauto.
Qed.

(* [comment removed for export] *)


End RP_3.
