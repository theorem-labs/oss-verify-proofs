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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_free_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B3 HP_RF_get_meta HP_RF_mm_syscalls.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RF_free_C () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RATP"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RP_1.rffin_post"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.sx32"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmunmap_entry"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RP_1.rfmun_post"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le4"].


(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Definition rffin_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (W : list (Z * Z)) (m : word -> option byte) (st : mstate) (errv : word) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_free_C ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R11.(6.(7.O17.O16.O15.O14.R10.R?.R>.O13.O12.R=.R<.R;.R:.R9.R8.R7.R6.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R5.R4.R3.R2.)O7.(8.O17.)O6.(9.(2.&40.))R1.(:.$;.)))(4.(<.O4.O3.R1.)(4.(=.$;.O3.R1.)(4.(>.$;.R1.)(4.(?.$;.R1.O5.(10.&40.O16.))(4.(11.$;.R1.(12.(10.&40.O14.)-:4.)(13.$14.(15.O1.)(16.$14.)))(17.VhRP,O2.R1.)))))))))))))))))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma rfree_fin0 : ltac2:(CDefT.buildp (gd_tbl_HP_RF_free_C ()) "Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Px1,(2.&40.)Pra,(2.&40.)Pbw,(2.&40.)Pq0,(2.&40.)Pq1,(2.&40.)PF,(18.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pjunk,(19.(2.&8.))Plo,$1:.Pst,$1;.Perrv,(2.&40.)P,(5.(2.&40.)R26.(1<.&40.$1=.))P,(17.VhRP,R3.R6.)P,(>.$;.R7.)P,(11.$;.R8.(12.(10.&40.R2;.)-30.)(13.$14.(1>.#8.R7.)(13.$14.(1?.R1<.)(13.$14.(1?.R1=.)(13.$14.(1?.R24.)(13.$14.(1?.R25.)(13.$14.(1?.R>.)(16.$14.))))))))P,(11.$;.R9.(12.(10.&40.R2:.)-:4.)(13.$14.(15.R5.)(16.$14.)))P,(?.$;.R:.R8.(12.(10.&40.R2=.)-30.))P,(20.(21.VhRP,)R9.)P,(20.R:.(22.(10.&40.R2?.)+30.))(23.$;.(24.R13.R30.R2?.R2>.R2:.R29.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R?.R>.R;.(13.(25.$1:.$1:.)(26.$1:.$1:.(22.(10.&40.R30.)+30.)(10.&40.R30.))(16.(25.$1:.$1:.)))R=.R:.R9.)(6.(7.R14.(1<.&40.(12.(10.&40.R30.)-30.))R2?.R2>.R2=.R2<.R2;.R11.R10.R12.(27.=)R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)R?.(1<.&40.+3?=50.)R>.(9.(2.&40.))R=.(:.$;.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until errv. intros TP MR MI FR ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  dpose MR as (WF & CX & GL & AR & GR & SH). ddestruct GL as (LK & NL & _).
  rceilb; unfold RMLOCK, RNEED_LOCKS, RATP in *. subst tp.
  rewrite (unsigned_lit 381128) in ERR by lia. change (381128 + -164) with 380964 in ERR.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x3fd64)) with (Z_to_bv 64 0x3fd64) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; rceilb; lia]) end.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold rffin_post. deexists 16. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
  rewrite (unsigned_lit 381128) by lia. change (381128 + -164) with 380964. exact ERR.
Qed.

(* [comment removed for export] *)
Definition rfmun_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (junk : list byte) (m : word -> option byte) (st : mstate) (errv bw lw : word) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_free_C ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R?.(6.(7.(1<.&40.+3?=80.)(1<.&40.(12.(10.&40.O18.)-30.))O17.O16.R>.R=.R<.O2.O1.O2.O1.R;.R:.R9.R8.R7.R6.(1<.&40.(12.(10.&40.O16.)-:4.))(28.O3.)O11.O10.O?.O>.O=.O<.O;.O:.R5.R4.R3.R2.)O9.(1<.&40.$29.)O8.(9.(2.&40.))R1.(:.$;.)))(4.(<.(13.(25.$1:.$1:.)(26.$1:.$1:.(22.(10.&40.O18.)+30.)(10.&40.O18.))(16.(25.$1:.$1:.)))O5.R1.)(4.(=.$;.O5.R1.)(4.(>.$;.R1.)(4.(?.$;.R1.O7.(12.(10.&40.O18.)-30.))(4.(11.$;.R1.(12.(10.&40.O18.)-30.)(13.$14.(1>.#8.O6.)(13.$14.(1?.O12.)(13.$14.(1?.O13.)(13.$14.(1?.O14.)(13.$14.(1?.O15.)(13.$14.(1?.O19.)(16.$14.))))))))(4.(11.$;.R1.(12.(10.&40.O16.)-:4.)(13.$14.(15.O3.)(16.$14.)))(17.VhRP,O4.R1.))))))))))))))))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma rfree_tomunmap : ltac2:(CDefT.buildp (gd_tbl_HP_RF_free_C ()) "Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Px1,(2.&40.)Pra,(2.&40.)Pbw,(2.&40.)Pq0,(2.&40.)Pq1,(2.&40.)PF,(18.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pjunk,(19.(2.&8.))Plo,$1:.Plen,$1:.Pst,$1;.Perrv,(2.&40.)P,(5.(2.&40.)R27.(1<.&40.$1=.))P,(17.VhRP,R3.R7.)P,(>.$;.R8.)P,(4.(2:.=R6.)(2:.R6.(2;.+2.+40.)))P,(11.$;.R:.(12.(10.&40.R2=.)-30.)(13.$14.(1>.#8.R9.)(13.$14.(1?.R1>.)(13.$14.(1?.R1?.)(13.$14.(1?.R26.)(13.$14.(1?.R27.)(13.$14.(1?.R10.)(16.$14.))))))))P,(11.$;.R;.(12.(10.&40.R2<.)-:4.)(13.$14.(15.R6.)(16.$14.)))P,(?.$;.R<.R:.(12.(10.&40.R2?.)-30.))P,(20.(21.VhRP,)R;.)P,(20.R<.(22.(10.&40.R31.)+30.))(23.$;.(2<.R15.R32.R31.R30.R2<.R2;.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R11.R10.R=.R>.R?.R;.R:.R14.(27.R<.))(6.(7.R16.(1<.&40.(12.(10.&40.R32.)-30.))R31.R30.R2?.R2>.R2=.R13.R12.R14.(27.R<.)R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)R11.(1<.&40.+3?=50.)R10.(9.(2.&40.))R?.(:.$;.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until errv. intros TP MR MI HL FR ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  dpose MR as (WF & CX & GL & AR & GR & SH). ddestruct GL as (LK & NL & _).
  rceilb; unfold RMLOCK, RNEED_LOCKS, RATP in *. subst tp.
  rewrite (unsigned_lit 381128) in ERR by lia. change (381128 + -164) with 380964 in ERR.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x3fd64)) with (Z_to_bv 64 0x3fd64) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K. { exfalso. rewrite wz_unsigned in K by lia. lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  replace (ret_pc (Z_to_bv 64 0x3fd6c)) with (Z_to_bv 64 0x3fd6c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; rceilb; lia]) end.
  apply evt_done. unfold rfmun_post. deexists 14. split; [rewrite (unsigned_lit 381128) by lia; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
  split; [rewrite (unsigned_lit 381128) by lia; change (381128 + -164) with 380964; exact ERR| exact MR2].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rerrno_avoids_repfoot : forall st m a, rmrep st m -> 380964 <= a < 380968 -> ~ rrepfoot st a.
Proof. rceilb.
  intros st m a MR Ha. pose proof MR as (WF & _). dpose WF as ((Hres & RPHres) & WR & DJ & WA & WG).
  intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
  - unfold RCTX in C. lia.
  - unfold RMLOCK in C. lia.
  - unfold RNEED_LOCKS in C. lia.
  - unfold RPAGE_SIZE in C. lia.
  - ddestruct C as (ak & ar & Hak & Hin).
    ddestruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len ra)). lia.
  - ddestruct C as (b & gh & Hb & Hin).
    ddestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len rb)). lia.
  - ddestruct C as (rid & r & v & Hr & Hk & Hin & HC).
    destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. lia.
  - unfold RGOT_SSP in C. lia.
  - unfold RSSP_GUARD in C. lia.
Qed.

#[using="Type"] Lemma rmrep_transport_frame_errno : ltac2:(CDefT.buildp (gd_tbl_HP_RF_free_C ()) "Pst,$1;.Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))Psp,$1:.P,(17.VhRP,R4.R3.)P,(<.(13.(25.$1:.$1:.)(26.$1:.$1:.(22.R2.+30.)R2.)(13.(25.$1:.$1:.)(26.$1:.$1:.+5=024.+5=028.)(16.(25.$1:.$1:.))))R4.R3.)P,(=.$;.R5.R4.)P,(20.(21.VhRP,)(22.R4.+30.))(17.VhRP,R8.R6.)")
(* [comment removed for export] *).
Proof. rceilb.
  intros st m m' sp MR MU WM HS. eapply rmrep_transport_unowned; [exact MR | exact MU | exact WM |].
  apply ivs_avoid_cons; [| apply ivs_avoid_cons; [| apply ivs_avoid_nil]].
  - intros a Ha. pose proof MR as (WF & _). dpose WF as ((Hres & RPHres) & WR & DJ & WA & WG). rceilb.
    intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
    + unfold RCTX in C. lia.
    + unfold RMLOCK in C. lia.
    + unfold RNEED_LOCKS in C. lia.
    + unfold RPAGE_SIZE in C. lia.
    + ddestruct C as (ak & ar & Hak & Hin).
      ddestruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). rceilb. lia.
    + ddestruct C as (b & gh & Hb & Hin).
      ddestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC). rceilb. lia.
    + ddestruct C as (rid & r & v & Hr & Hk & Hin & HC).
      destruct (WR _ _ Hr) as (_ & _ & _ & RBC & _). rceilb. lia.
    + unfold RGOT_SSP in C. lia.
    + unfold RSSP_GUARD in C. lia.
  - intros a Ha. eapply rerrno_avoids_repfoot; [exact MR | exact Ha].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rfree_fin1 : ltac2:(CDefT.buildp (gd_tbl_HP_RF_free_C ()) "Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Px1,(2.&40.)Pra,(2.&40.)Pew,(2.&40.)Pbw,(2.&40.)Plw,(2.&40.)Pe',(2.&40.)PF,(18.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pjunk,(19.(2.&8.))Plo,$1:.Pst,$1;.Perrv,(2.&40.)P,(5.(2.&40.)R29.(1<.&40.$1=.))P,(17.VhRP,R3.R6.)P,(>.$;.R7.)P,(11.$;.R8.(12.(10.&40.R2>.)-30.)(13.$14.(1>.#8.R7.)(13.$14.(1?.R1=.)(13.$14.(1?.R1>.)(13.$14.(1?.R27.)(13.$14.(1?.R28.)(13.$14.(1?.R?.)(16.$14.))))))))P,(5.(19.(2.&8.))(2=.R?.)(2=.R5.))P,(11.$;.R:.(12.(10.&40.R2>.)-:4.)(13.$14.(15.R=.)(16.$14.)))P,(?.$;.R;.R9.(12.(10.&40.R31.)-30.))P,(20.(21.VhRP,)R:.)P,(20.R;.(22.(10.&40.R33.)+30.))(23.$;.(24.R15.R34.R33.R32.R2>.R2=.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R10.R?.R<.(13.(25.$1:.$1:.)(26.$1:.$1:.(22.(10.&40.R34.)+30.)(10.&40.R34.))(13.(25.$1:.$1:.)(26.$1:.$1:.+5=024.+5=028.)(16.(25.$1:.$1:.))))R>.R;.R:.)(6.(7.R16.(1<.&40.(12.(10.&40.R34.)-30.))R33.R32.R31.R30.R2?.R13.R12.R2<.R2;.R2:.R29.R28.R27.R26.R25.(1<.&40.(12.(10.&40.R32.)-:4.))R14.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)R10.(1<.&40.+3?=80.)R?.(9.(2.&40.))R>.(:.$;.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until errv. intros TP MR MI FR EW ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (380964, 380968)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  rceilb; unfold RATP in *. subst tp.
  rewrite (unsigned_lit 381128) in ERR by lia. change (381128 + -164) with 380964 in ERR.
  rewrite (unsigned_lit 381128) by lia. change (381128 + -164) with 380964.
  (* [comment removed for export] *)
  st1.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX) by (eapply (rmrep_transport_frame_errno st m mX (bv_unsigned sp)); [exact MR | exact MU | exact WM | rceilb; lia]) end.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold rffin_post. deexists 16. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
  rewrite (unsigned_lit 381128) by lia. change (381128 + -164) with 380964.
  eapply rw_cells_congr; [| | | exact ERR]; [cbn [cells_bytes cbytes app]; rewrite EW; reflexivity| reflexivity| cbn; tauto].
Qed.

End RP_1.
