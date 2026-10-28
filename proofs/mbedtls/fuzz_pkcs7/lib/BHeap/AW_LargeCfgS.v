(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AJ AKinvS AKinvM ASpinS AW_Unwind AW_Unwind2 AW_MmapFixed AW_MmapAnon AW_MmapDie AW_Poison AW_DepotCfg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_CfgS AW_ClassId AW_Combined AW_Refill AW_GetFrom AW_Populate AW_CfgDefs AW_Large AW_MapOrDie.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AW_LargeCfgS () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Numbers.BinNums.Z"; "Corelib.Lists.ListDef.Forall"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_base"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_size"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment"; "Corelib.Init.Datatypes.None"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.true"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_commit"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_fresh"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.die_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.A_SPIN_MMAPDIE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MapOrDie.mod_answered"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Large.large_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.thr_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CfgDefs.mwc_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "ARUN_1.LargeCfgS.img_static_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "ARUN_1.LargeCfgS.lstat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.length"; "ARUN_1.LargeCfgS.limg"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "ARUN_1.shadow_wr"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Large.map_size"; "ARUN_1.LargeCfgS.large_cpostS"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Combined.A_LARGE_ALLOC"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "ARUN_1.LargeCfgS.combsec_cpostS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Combined.A_COMBINED"].

Section ARUN_1. Context {hAR : arun}.
Set Printing Width 250.

(* [comment removed for export] *)
#[using="Type"] Lemma find_segment_none_above : ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "Pl,(0.$1.)Pz,$2.Pn,$2.P,(3.$1.Ls,$1.(4.(5.(6.(7.R1.))(6.(8.R1.)))+65?000.)R3.)P,(4.+65?000.R3.)P,(9.=R3.)(:.(;.$1.)(<.R6.R5.R4.)(=.$1.))")
(* [comment removed for export] *).
Proof.
  induction l as [|s l IH]; intros z n HF Hz Hn; cbn; [reflexivity|].
  apply Forall_cons_iff in HF. destruct HF as [HS HL].
  destruct ((Z.of_N (seg_base s) <=? z) && (z + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E2. exfalso. clear - E2 HS Hz Hn. lia.
  - apply IH; assumption.
Qed.
#[using="Type"] Lemma asegs_end : Forall (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 0x65f000) asegs.
Proof.
  assert (E : List.map (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s)) asegs = [286720; 987136; 1011712; 6680576]) by (vm_compute; reflexivity).
  assert (G : forall l, List.map (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s)) l = [286720; 987136; 1011712; 6680576] ->
              Forall (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 0x65f000) l).
  { intros l H. destruct l as [|s1 [|s2 [|s3 [|s4 [|s5 l]]]]]; cbn in H; try discriminate.
    injection H as E1 E2 E3 E4. repeat constructor; lia. }
  exact (G _ E).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wr_at_cells : ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "Pm,P,(>.&40.)(;.(>.&8.))PA,$2.Pn,$?.P,(4.+65?000.R2.)P,(10.$11.R4.R3.(12.R2.))(13.(0.(>.&8.))Lbs,(0.(>.&8.))(14.$11.R6.R5.(15.$16.(17.R4.R1.)(18.$16.))))")
(* [comment removed for export] *).
Proof.
  (intros m A n HA dd_H; ddestruct dd_H as (H0 & H1 & HW)).
  set (f := fun i : nat => match m (wa (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end).
  exists (List.map f (seq 0 n)).
  assert (LEN : length (List.map f (seq 0 n)) = n) by (rewrite map_length, seq_length; reflexivity).
  split; [split; [cbn; rewrite LEN; tauto|]|].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [exact H0|]. split; [rewrite LEN; exact H1|].
    intros i Hi. rewrite LEN in Hi. rewrite (nth_error_map f), nth_error_seq. replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
    cbn [option_map Nat.add].
    unfold mrd, f. specialize (HW (Z.of_nat i) ltac:(lia)). unfold wview in HW.
    destruct (m (wa (A + Z.of_nat i))) as [b|] eqn:E; [reflexivity|]. exfalso. apply HW.
    rewrite wa_unsigned by lia. rewrite (find_segment_none_above asegs) by (first [apply asegs_end | lia]). reflexivity.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. split; [exact H0|]. split; [exact H1| exact HW].
Qed.

(* [comment removed for export] *)
Definition shadow_wr (m : mem) : Prop :=
  wr_at asegs m 0x7fff8000 0xffff000 /\ wr_at asegs m 0x2008fff7000 0xdfff0001000.
#[using="Type"] Lemma shadow_wr_mono : forall m m', shadow_wr m -> wmono asegs m m' -> shadow_wr m'.
Proof.
  (intros m m' dd_H; ddestruct dd_H as [(A0 & A1 & HA) (B0 & B1 & HB)]; intros WM). split; (split; [assumption| split; [assumption|]]); intros i Hi; apply WM; auto.
Qed.

#[using="Type"] Lemma disjoint_from_sub : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> disjoint_from W A' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros A n A' n' H H1 H2; cbn in *; [exact I|].
  destruct H as [H HW]. split; [clear - H H1 H2; lia| eapply IH; eauto].
Qed.

#[using="Type"] Lemma wr_at_sub : forall m A n A' n', wr_at asegs m A n -> A <= A' -> A' + n' <= A + n -> wr_at asegs m A' n'.
Proof.
  (intros m A n A' n' dd_H; ddestruct dd_H as (H0 & H1 & H); intros L1 L2). split; [lia|]. split; [lia|]. intros i Hi.
  replace (A' + i) with (A + (A' - A + i)) by lia. apply H. lia.
Qed.

#[using="Type"] Lemma u64s_zeros : forall n, u64s (repeat (Z_to_bv 64 0) n) = repeat (Z_to_bv 8 0) (8 * n).
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat u64s flat_map]. change (flat_map le8 (repeat (Z_to_bv 64 0) n)) with (u64s (repeat (Z_to_bv 64 0) n)).
  rewrite IH. replace (8 * S n)%nat with (S (S (S (S (S (S (S (S (8 * n)))))))))%nat by lia. reflexivity.
Qed.
#[using="Type"] Lemma u64arr_zeros : ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "Pm,P,(>.&40.)(;.(>.&8.))PA,$2.Pn,$2.P,(4.=R1.)P,(14.$11.R4.R3.(15.$16.(17.(19.(1:.+8.R2.))(1;.(>.&8.)(1<.&8.=)(19.(1:.+8.R2.))))(18.$16.)))(1=.$11.R5.R4.(1;.(>.&40.)(1<.&40.=)(19.R3.)))")
(* [comment removed for export] *).
Proof.
  intros m A n Hn RC. pose proof (u8arr_of_rw_cells asegs m A _ _ RC) as [HB HW].
  split. { rewrite u64s_zeros. replace (8 * Z.to_nat n)%nat with (Z.to_nat (8 * n)) by lia. exact HB. }
  rewrite repeat_length in HW |- *. replace (8 * Z.of_nat (Z.to_nat n)) with (Z.of_nat (Z.to_nat (8 * n))) by lia. exact HW.
Qed.

#[using="Type"] Lemma u64arr_nil_any : forall m m' A, u64arr asegs m A [] -> u64arr asegs m' A [].
Proof.
  (intros m m' A dd_H; ddestruct dd_H as [[B0 [B1 _]] [W0 [W1 _]]]). cbn in *.
  split; [split; [exact B0| split; [exact B1| intros i Hi; cbn in Hi; exfalso; clear - Hi; lia]] | split; [exact W0| split; [exact W1| intros i Hi; exfalso; clear - Hi; cbn in Hi; lia]]].
Qed.

Section LargeCfgS.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  (* [comment removed for export] *)
  Variable CSf : list (Z * Z) -> Z -> Z -> Prop.
  Variable K : list (Z * Z) -> Z -> Model -> Prop.
  Hypothesis CSOKf : forall sc r, cs_ok AL (CSf sc r).
  Hypothesis KL : forall sc r, kinv AL (CSf sc r) (K sc r).
  Hypothesis CSmono_l : forall sc r p y, CSf sc r y -> CSf (sc ++ [p]) r y.
  Hypothesis CSmono_p : forall sc r y, CSf sc r y -> CSf sc (r + 1) y.
  (* [comment removed for export] *)
  Variable Gl : list (Z * Z) -> Z -> Z -> Prop.
  Variable Gp : list (Z * Z) -> Z -> Prop.
  (* [comment removed for export] *)
  Variables (PA T CTX : Z).
  Let U (r : Z) := PA + 0x20000 * r.
  Hypothesis GPA : (0x65f000 <= PA /\ Pband PA 0x800000) /\ PA + 0x800000 <= ACEIL /\ PA mod 4096 = 0.
  Hypothesis GT : (Timg T /\ Tband T) /\ T + 4096 <= ACEIL /\ T mod 4096 = 0.
  Hypothesis GCTX : (0x65f000 <= CTX /\ Pband CTX 0x10000) /\ CTX + 0x10000 <= ACEIL.
  Hypothesis GSEP : ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "(1>.(1?.(4.(5.VT,+1000.)VPA,)(4.(5.VPA,+800000.)VT,))(1>.(1?.(4.(5.VCTX,+10000.)VT,)(4.(5.VT,+1000.)VCTX,))(1?.(4.(5.VCTX,+10000.)VPA,)(4.(5.VPA,+800000.)VCTX,))))")
(* [comment removed for export] *).
  Hypothesis CST : forall sc r, crange (CSf sc r) T 4096.
  Hypothesis CSCTX : forall sc r, crange (CSf sc r) CTX 0x10000.
  Hypothesis CSPA : forall sc r, 0 <= r -> 0x20000 * r <= 0x800000 -> crange (CSf sc r) PA (0x20000 * r).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis K_apart : ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "Psc,(0.(20.$2.$2.))Pr,$2.Pmo,$21.Pa,(>.&40.)Pn,(>.&40.)P,A3.VK,R5.R4.R3.P,(:.$22.(23.(24.(20.(>.&40.)(>.&40.))(25.(26.R4.))(27.(26.R4.)))R3.R2.)$28.)P,(4.+10000.(29.&40.R3.))P,(4.(5.(29.&40.R5.)(29.&40.R4.))(2:.VhAR,))Py,$2.P,(1?.A3.VCSf,R:.R9.R1.(1?.(1>.(4.(2;.VAL,)R1.)(9.R1.(2<.VAL,)))(1?.(1>.(4.+7???7000.R1.)(9.R1.+10007???8000.))(1>.(4.VPA,R1.)(9.R1.(5.VPA,+800000.))))))(2=.(1>.(4.(29.&40.R8.)R2.)(9.R2.(5.(29.&40.R8.)(29.&40.R7.)))))")
(* [comment removed for export] *).
  Hypothesis T_large : ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "Psc,(0.(20.$2.$2.))Pr,$2.Pms,$2.Pmo,$21.Pa,(>.&40.)P,A3.VGl,R5.R4.R3.P,A3.VK,R6.R5.R3.P,(:.$2.(2>.(29.&40.R3.)+1000.)=)P,(9.=(29.&40.R4.))P,(4.(5.(29.&40.R5.)R7.)(2:.VhAR,))P,(:.$22.(23.(24.(20.(>.&40.)(>.&40.))(25.(26.R7.))(27.(26.R7.)))R6.(1<.&40.R8.))$28.)(1>.A3.VK,(24.(20.$2.$2.)R;.(15.(20.$2.$2.)(2?.$2.$2.(29.&40.R7.)R9.)(18.(20.$2.$2.))))R:.(30.+22.R7.R9.R8.)(31.A2.VCSf,(24.(20.$2.$2.)R;.(15.(20.$2.$2.)(2?.$2.$2.(29.&40.R7.)R9.)(18.(20.$2.$2.))))R:.(29.&40.R7.)R9.))")
(* [comment removed for export] *).
  (* [comment removed for export] *)
  Hypothesis LEDGER_P : ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "Psc,(0.(20.$2.$2.))Pr,$2.Pmo,$21.P,A2.VGp,R3.R2.P,A3.VK,R4.R3.R2.(1>.(:.$22.(23.(25.(26.R3.))(1<.&40.A1.VU,R4.)(1<.&40.+20000.))$28.)(1?.(:.$22.(32.(27.(26.R3.))(1<.&40.A1.VU,R4.)(1<.&40.+20000.))$28.)(:.$22.(23.(24.(20.(>.&40.)(>.&40.))(25.(26.R3.))(27.(26.R3.)))(1<.&40.A1.VU,R4.)(1<.&40.+20000.))$28.)))")
(* [comment removed for export] *).
  Hypothesis TP_commit : ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "Psc,(0.(20.$2.$2.))Pr,$2.Pmo,$21.P,A2.VGp,R3.R2.P,A3.VK,R4.R3.R2.P,(:.$22.(32.(27.(26.R3.))(1<.&40.A1.VU,R4.)(1<.&40.+20000.))$28.)(1>.A3.VK,R6.(5.R5.+1.)(33.+32.A1.VU,R5.+20000.R4.)(31.A2.VCSf,R6.(5.R5.+1.)A1.VU,R5.+20000.))")
(* [comment removed for export] *).
  Hypothesis TP_fresh : ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "Psc,(0.(20.$2.$2.))Pr,$2.Pmo,$21.P,A2.VGp,R3.R2.P,A3.VK,R4.R3.R2.P,(:.$22.(23.(24.(20.(>.&40.)(>.&40.))(25.(26.R3.))(27.(26.R3.)))(1<.&40.A1.VU,R4.)(1<.&40.+20000.))$28.)(1>.A3.VK,R6.(5.R5.+1.)(34.+32.A1.VU,R5.+20000.R4.)(31.A2.VCSf,R6.(5.R5.+1.)A1.VU,R5.+20000.))")
(* [comment removed for export] *).
  Hypothesis ROOM_P : forall sc r mo, Gp sc r -> K sc r mo -> fixrw_grantable 0x32 (U r) 0x20000 mo.
  (* [comment removed for export] *)
  Hypothesis SCAR_P : forall sc r, Gp sc r -> hole_site AL (CSf sc r) (K sc r) (U r) 0x20000.
  (* [comment removed for export] *)
  Variable die_statics : mem -> Prop.
  (* [comment removed for export] *)
  Definition img_static_ok (W : list (Z * Z)) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "PA,$2.Pn,$2.P,(1>.(4.+10000.R2.)(4.(5.R2.R1.)+65?000.))P,(1?.(4.(5.R3.R2.)(5.$35.+70.))(4.(5.$35.+2=0.)R3.))(36.O1.R4.R3.)")
(* [comment removed for export] *).
  Hypothesis die_statics_transport : forall W m m', die_statics m -> munch W m m' -> img_static_ok W -> die_statics m'.
  Variable DIE_NEED : Z.
  Hypothesis DIE_NEED_ge : 368 <= DIE_NEED.
  Hypothesis MOD_DIE : ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "PCS,P,$2.SpPgp,(>.&40.)Ptp,(>.&40.)Pt0,(>.&40.)Pt1,(>.&40.)Pt2,(>.&40.)Ps0,(>.&40.)Ps1,(>.&40.)Ps2,(>.&40.)Ps3,(>.&40.)Ps4,(>.&40.)Ps5,(>.&40.)Ps6,(>.&40.)Ps7,(>.&40.)Ps8,(>.&40.)Ps9,(>.&40.)Ps10,(>.&40.)Ps11,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)Pa6,(>.&40.)Pra,(>.&40.)PSP,$2.PF,(37.&5.(>.&40.))Pfc,(>.&20.)Pm0,P,(>.&40.)(;.(>.&8.))Pmm,P,(>.&40.)(;.(>.&8.))Paddr,$2.Psize,$2.Plo,$2.Pfr,(0.(>.&8.))P,(38.VAL,R21.)P,(1>.(4.=R5.)(9.R5.(39.+2.+2?.)))P,(1>.(9.=R5.)(4.R5.(39.+2.+28.)))P,(14.$11.R8.(5.R<.-60.)(15.$16.(3:.(1<.&40.+32.))(15.$16.(17.#2<.R4.)(15.$16.(3;.R1:.)(15.$16.(3;.R1;.)(15.$16.(3;.R1<.)(15.$16.(3;.R1=.)(15.$16.(3;.R1>.)(15.$16.(3;.R=.)(18.$16.))))))))))P,A1.Vdie_statics,R9.P,(3<.$11.R:.R7.(5.R>.-60.))P,(4.+65?000.R8.)P,(4.R9.(3=.R10.VDIE_NEED,))P,(4.R11.(39.+2.+3?.))P,(3>.(15.(20.$2.$2.)(2?.$2.$2.R;.R12.)(18.(20.$2.$2.)))R?.R>.)P,(3?.$11.R10.R?.)P,(40.$11.R10.)P,(31.R2=.R>.(3=.R15.R>.))(41.$11.VAL,R2>.(42.R14.$43.)(44.(1<.&40.(3=.(39.+2.+40.)+<.))R16.R2=.R2<.R2;.R2:.R29.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R15.R14.R11.R10.R12.))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition lstat (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "(1>.(45.O1.VPA,)(1>.(46.O1.VCTX,VT,)(1>.(47.O1.)(1>.(48.O1.)A1.Vdie_statics,O1.))))")
(* [comment removed for export] *).
  #[using="Type"] Lemma ro_img : ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "PW,(0.$49.)Pm,P,(>.&40.)(;.(>.&8.))Pm',P,(>.&40.)(;.(>.&8.))PA,$2.Pcs,(0.$16.)P,(4:.$11.R4.R2.R1.)P,(3>.R6.R5.R4.)P,(4;.R7.)P,(1>.(4.+10000.R5.)(4.(5.R5.(12.(4<.R4.)))+65?000.))P,(1?.(4.(5.R6.(12.(4<.R5.)))(5.$35.+70.))(4.(5.$35.+2=0.)R6.))(4:.$11.R8.R7.R6.)")
(* [comment removed for export] *).
  Proof. intros W m m' A cs H MU DJ H1 H2. eapply ro_cells_transport; [exact H| exact MU| apply DJ; [exact H1| exact H2]]. Qed.
  #[using="die_statics_transport"] Lemma lstat_transport : ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "PW,(0.$49.)Pm,P,(>.&40.)(;.(>.&8.))Pm',P,(>.&40.)(;.(>.&8.))P,(4=.R2.)P,(3>.R4.R3.R2.)P,(4;.R5.)P,(36.R6.(5.VCTX,+98.)+8.)(4=.R5.)")
(* [comment removed for export] *).
  Proof.
    (intros W m m' dd_H; ddestruct dd_H as ((L1 & L2 & L3) & (T1 & T2 & T3 & T4) & (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13) & (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8) & S5); intros MU DJ DJC).
    unfold lstat, large_statics, thr_statics, poison_statics, mwc_statics.
    unfold A_INSTANCE, A_GOT_LNAME, A_LNAME_CELL, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR, A_CANPOISON, A_GOT_SB, A_SBCELL, A_GOT_MIDBEG, A_MIDBEG, A_GOT_MIDEND, A_MIDEND,
      A_GOT_HIGHEND, A_HIGHEND, A_GOT_RMEMSET, A_RMEMSET, A_GOT_CFLAGS, A_CF_CSMT, A_GOT_PAGESZ, A_PAGESZ_CELL, A_DECORATE, A_MMAP_LIMIT,
      A_GOT_SEALED2, A_GOT_DYING, A_DYING in *.
    Ltac tr H MU DJ := eapply (ro_img _ _ _ _ _ H MU DJ); unfold A_INSTANCE; cbn; clear; lia.
    repeat match goal with |- _ /\ _ => split end.
    all: first [ tr L1 MU DJ | tr L2 MU DJ | tr L3 MU DJ | tr T1 MU DJ | tr T2 MU DJ | tr T3 MU DJ
               | (eapply ro_cells_transport; [exact T4| exact MU| exact DJC])
               | tr P1 MU DJ | tr P2 MU DJ | tr P3 MU DJ | tr P4 MU DJ | tr P5 MU DJ | tr P6 MU DJ | tr P7 MU DJ | tr P8 MU DJ | tr P9 MU DJ | tr P10 MU DJ
               | tr P11 MU DJ | tr P12 MU DJ | tr P13 MU DJ | tr W1 MU DJ | tr W2 MU DJ | tr W3 MU DJ | tr W4 MU DJ | tr W5 MU DJ | tr W6 MU DJ | tr W7 MU DJ | tr W8 MU DJ
               | (eapply die_statics_transport; [exact S5| exact MU| exact DJ]) ].
  Qed.

  (* [comment removed for export] *)
  Definition limg (m : mem) (nres ncks : Z) (srt : byte) (mx : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "(1>.(14.$11.O5.(5.$35.+70.)(15.$16.(3;.(1<.&40.O4.))(15.$16.(3;.(1<.&40.O3.))(15.$16.(4>.O2.)(18.$16.)))))(1>.(13.(0.(>.&40.))Lst,(0.(>.&40.))(1>.(14.$11.O5.(5.$35.+88.)(4?.(>.&40.)$16.$3;.R1.))(:.$?.(50.(>.&40.)R1.)#4.)))(1>.(13.(0.(>.&40.))Lbsl,(0.(>.&40.))(1>.(1=.$11.O5.(5.$35.+:8.)R1.)(:.$?.(50.(>.&40.)R1.)#40.)))(1>.(14.$11.O5.(5.$35.+2:8.)(15.$16.(3:.(1<.&40.O1.))(18.$16.)))(13.(>.&40.)Lg0,(>.&40.)(13.(>.&40.)Lg1,(>.&40.)(14.$11.O5.(5.$35.+2<0.)(15.$16.(3;.R2.)(15.$16.(3;.R1.)(18.$16.))))))))))")
(* [comment removed for export] *).
  #[using="hAR PA T"] Lemma limg_transport : ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "PW,(0.$49.)Pm,P,(>.&40.)(;.(>.&8.))Pm',P,(>.&40.)(;.(>.&8.))Pnres,$2.Pncks,$2.Psrt,(>.&8.)Pmx,$2.P,(51.R6.R4.R3.R2.R1.)P,(3>.R8.R7.R6.)P,(3?.$11.R8.R7.)P,(36.R:.(5.$35.+70.)+260.)(51.R9.R8.R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    (intros W m m' nres ncks srt mx dd_H; ddestruct dd_H as (S1 & (st & S2 & L2) & (bsl & S3 & L3) & S4 & (g0 & g1 & S5)); intros MU WM DJ). unfold limg.
    assert (DJ' : forall A n, A_INSTANCE + 112 <= A -> A + n <= A_INSTANCE + 720 -> disjoint_from W A n).
    { intros A n H1 H2. eapply disjoint_from_sub; [exact DJ| exact H1| exact H2]. }
    destruct st as [|st0 [|st1 [|st2 [|st3 [|]]]]]; try discriminate L2.
    split. { eapply rw_cells_transport; [exact S1| exact MU| exact WM| apply DJ'; cbn; lia]. }
    split. { exists [st0; st1; st2; st3]. split; [| reflexivity]. eapply rw_cells_transport; [exact S2| exact MU| exact WM| apply DJ'; cbn; lia]. }
    split. { exists bsl. split; [| exact L3]. eapply u64arr_transport; [exact S3| exact MU| exact WM| apply DJ'; rewrite ?L3; cbn; unfold A_INSTANCE; lia]. }
    split. { eapply rw_cells_transport; [exact S4| exact MU| exact WM| apply DJ'; cbn; lia]. }
    exists g0, g1. eapply rw_cells_transport; [exact S5| exact MU| exact WM| apply DJ'; cbn; lia].
  Qed.

  #[using="Type"] Lemma limg_parts : ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "Pm,P,(>.&40.)(;.(>.&8.))Pnres,$2.Pncks,$2.Psrt,(>.&8.)Pmx,$2.P,(51.R5.R4.R3.R2.R1.)(1>.(14.$11.R6.(5.$35.+70.)(15.$16.(3;.(1<.&40.R5.))(15.$16.(3;.(1<.&40.R4.))(15.$16.(4>.R3.)(18.$16.)))))(1>.(13.(0.(>.&40.))Lst,(0.(>.&40.))(1>.(14.$11.R7.(5.$35.+88.)(4?.(>.&40.)$16.$3;.R1.))(:.$?.(50.(>.&40.)R1.)#4.)))(1>.(13.(0.(>.&40.))Lbsl,(0.(>.&40.))(1>.(1=.$11.R7.(5.$35.+:8.)R1.)(:.$?.(50.(>.&40.)R1.)#40.)))(1>.(14.$11.R6.(5.$35.+2:8.)(15.$16.(3:.(1<.&40.R2.))(18.$16.)))(13.(>.&40.)Lg0,(>.&40.)(13.(>.&40.)Lg1,(>.&40.)(14.$11.R8.(5.$35.+2<0.)(15.$16.(3;.R2.)(15.$16.(3;.R1.)(18.$16.))))))))))")
(* [comment removed for export] *).
  Proof. intros m nres ncks srt mx H. exact H. Qed.
  (* [comment removed for export] *)
  #[using="hAR PA T"] Lemma limg_set_mutex : ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "PW,(0.$49.)Pm,P,(>.&40.)(;.(>.&8.))Pm',P,(>.&40.)(;.(>.&8.))Pnres,$2.Pncks,$2.Psrt,(>.&8.)Pmx,$2.Pmx',$2.P,(51.R7.R5.R4.R3.R2.)P,(3>.R9.R8.R7.)P,(3?.$11.R9.R8.)P,(36.R;.(5.$35.+70.)+238.)P,(36.R<.(5.$35.+2<0.)+10.)P,(14.$11.R;.(5.$35.+2:8.)(15.$16.(3:.(1<.&40.R6.))(18.$16.)))(51.R<.R;.R:.R9.R7.)")
(* [comment removed for export] *).
  Proof.
    (intros W m m' nres ncks srt mx mx' dd_H; ddestruct dd_H as (S1 & (st & S2 & L2) & (bsl & S3 & L3) & S4 & (g0 & g1 & S5)); intros MU WM DJ1 DJ2 MX). unfold limg.
    assert (DJ' : forall A n, A_INSTANCE + 112 <= A -> A + n <= A_INSTANCE + 680 -> disjoint_from W A n).
    { intros A n H1 H2. eapply disjoint_from_sub; [exact DJ1| exact H1| exact H2]. }
    destruct st as [|st0 [|st1 [|st2 [|st3 [|]]]]]; try discriminate L2.
    split. { eapply rw_cells_transport; [exact S1| exact MU| exact WM| apply DJ'; cbn; lia]. }
    split. { exists [st0; st1; st2; st3]. split; [| reflexivity]. eapply rw_cells_transport; [exact S2| exact MU| exact WM| apply DJ'; cbn; lia]. }
    split. { exists bsl. split; [| exact L3]. eapply u64arr_transport; [exact S3| exact MU| exact WM| apply DJ'; rewrite ?L3; cbn; unfold A_INSTANCE; lia]. }
    split. { exact MX. }
    exists g0, g1. eapply rw_cells_transport; [exact S5| exact MU| exact WM| exact DJ2].
  Qed.

  Ltac facts :=
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition large_cpostS (ok : bool) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra : word) (F : bvmap 5 word) (fc : bv 32)
      (sc : list (Z * Z)) (r x ncks lo : Z) (j1 j2 : word) (ps : list word) (m0 : mem) : config -> Prop :=
    fun cf => exists ms' mo' (res : Z) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem),
      let ms := map_size x in
      cf = mkCfg ms' mo'
      /\ ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None mm (seg_rom asegs)
      /\ mem_inv asegs mm /\ stk asegs mm lo SP /\ wmono asegs m0 mm /\ shadow_wr mm /\ lstat mm
      /\ if ok then
           exists (a r' : Z) (rest' : list word),
             res = a + 4096 /\ K (sc ++ [(a, ms)]) r' mo' /\ J mm mo' /\ (r' = r \/ (r' = r + 1 /\ ncks = 0x4000 * r)) /\ ncks + 1 <= 0x4000 * r'
             /\ 0x65f000 <= a /\ a mod 4096 = 0 /\ a + ms <= ACEIL /\ (a + ms <= 0x7fff7000 \/ 0x10007fff8000 <= a)
             /\ (a + ms <= PA \/ PA + 0x800000 <= a)
             /\ crange (CSf (sc ++ [(a, ms)]) r') a ms /\ (forall y, CSf sc r y -> ~ (a <= y < a + ms))
             /\ munch [(lo, SP); (a, a + ms); (0x7fff8000 + a / 8, 0x7fff8000 + a / 8 + ms / 8); (T + 2872, T + 2888);
                       (A_INSTANCE + 112, A_INSTANCE + 720); (PA + 8 * ncks, PA + 8 * (0x4000 * r'))] m0 mm
             /\ rw_cells asegs mm a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 x); C8 (Z_to_bv 64 ncks)]
             /\ rw_cells asegs mm (a + 32) [CB (Z.to_nat (ms - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (ms - 32)))]
             /\ rw_cells asegs mm (0x7fff8000 + a / 8) [CB 512%nat (repeat (Z_to_bv 8 0xfa) 512%nat)]
             /\ rw_cells asegs mm (0x7fff8000 + (a + 4096 + x) / 8) [CB (Z.to_nat ((ms - 4096 - x) / 8)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat ((ms - 4096 - x) / 8)))]
             /\ rw_cells asegs mm (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned j1 + 1)); C8 (Z_to_bv 64 (bv_unsigned j2 + ms))]
             /\ limg mm (0x4000 * r') (ncks + 1) (Z_to_bv 8 0) 0
             /\ u64arr asegs mm PA (ps ++ [Z_to_bv 64 a]) /\ u64arr asegs mm (PA + 8 * (ncks + 1)) rest' /\ Z.of_nat (length rest') = 0x4000 * r' - ncks - 1
         else
           res = 0 /\ K sc r mo' /\ J mm mo' /\ munch [(lo, SP)] m0 mm
           /\ rw_cells asegs mm (T + 2872) [C8 j1; C8 j2].

  #[using="AL IMG ALWF ASB CSOKf KL CSmono_l CSmono_p U GPA GT GCTX GSEP CST CSCTX CSPA K_apart T_large LEDGER_P TP_commit TP_fresh ROOM_P SCAR_P die_statics_transport DIE_NEED_ge MOD_DIE"] Lemma large_cfgS : ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "PQ,P,$52.SpPra,(>.&40.)Pgp,(>.&40.)Ptp,(>.&40.)Pt0,(>.&40.)Pt1,(>.&40.)Pt2,(>.&40.)Ps0,(>.&40.)Ps1,(>.&40.)Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)Ps2,(>.&40.)Ps3,(>.&40.)Ps4,(>.&40.)Ps5,(>.&40.)Ps6,(>.&40.)Ps7,(>.&40.)Ps8,(>.&40.)Ps9,(>.&40.)Ps10,(>.&40.)Ps11,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)Pj1,(>.&40.)Pj2,(>.&40.)Psrt,(>.&8.)Pps,(0.(>.&40.))Prest,(0.(>.&40.))Psc,(0.(20.$2.$2.))PSP,$2.PF,(37.&5.(>.&40.))Pfc,(>.&20.)Pm,P,(>.&40.)(;.(>.&8.))Pmo,$21.Pr,$2.Px,$2.Pncks,$2.Plo,$2.P,(1>.(9.+10000.R3.)(4.R3.(39.+2.+20.)))P,(:.$2.(2>.R4.+8.)=)P,(4.=R6.)P,(1>.(4.=R5.)(4.R5.(1:.+4000.R7.)))P,(4.(5.(1:.+4000.R8.)+4000.)(39.+2.+14.))P,(:.$2.(12.(50.(>.&40.)R11.))R7.)P,(:.$2.(12.(50.(>.&40.)R11.))(3=.(1:.+4000.R:.)R8.))P,(4=.R=.)P,(:.(>.&40.)R2?.(1<.&40.$53.))P,(54.R?.)P,(14.$11.R10.(5.VT,+;38.)(15.$16.(3;.R19.)(15.$16.(3;.R18.)(18.$16.))))P,(51.R11.(1:.+4000.R?.)R=.R18.=)P,(1=.$11.R12.VPA,R18.)P,(1=.$11.R13.(5.VPA,(1:.+8.R?.))R18.)P,(3<.$11.R14.R?.R17.)P,(4.(2:.VhAR,)R10.)P,(4.R11.(3=.(3=.R19.+<0.)VDIE_NEED,))P,(4.R1:.(39.+2.+3?.))P,(:.$2.(2>.R1;.+10.)=)P,(31.A2.VCSf,R1=.R17.R14.(3=.R1<.R14.))P,(40.$11.R1:.)P,A3.VK,R1?.R19.R1:.P,(55.R1<.R1;.)P,A3.VGl,R21.R1;.(56.R1:.)P,Pp,(20.$2.$2.)A2.VGp,(24.(20.$2.$2.)R23.(15.(20.$2.$2.)R1.(18.(20.$2.$2.))))R1=.P,Pok,$22.Pc',$52.P,(57.R2.R24.R43.R42.R3>.R3=.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R44.R23.R22.R25.R1?.R1>.R1=.R1<.R2:.R29.R27.R21.R1.)(58.$11.R46.R2.)(58.$11.R44.(59.(5:.(5;.R43.(1<.&40.R23.)R42.R41.R40.R3?.R3>.R3=.R3<.(1<.&40.(5.$35.+40.))(1<.&40.(5.$35.+2;0.))(1<.&40.R1=.)(1<.&40.+8.)R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.)R22.(1<.&40.$5<.)R21.(=.(>.&40.))R20.(5=.$11.))R1?.))")
(* [comment removed for export] *).
  Proof.
    intros Q ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 j1 j2 srt ps rest sc SP F fc m mo r x ncks lo
      Hx XAL HR HNC HNR LPS LREST LS TP SHW TJ LI HPS HREST ST LOIMG SPL SPH SPA SCS MI HK HJ HGl HGp HC.
    facts. assert (Hx40 : 0x10000 < x <= 2^40) by (clear - Hx; lia).
    dpose GPA as (PA0 & PA1 & PAL). dpose GT as (T0 & T1 & TAL). pose proof GCTX as (CX0 & CX1). dpose GSEP as (SEP1 & SEP2 & SEP3).
    assert (MSZ : x + 4096 <= map_size x < x + 8192).
    { unfold map_size. clear - Hx. pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)). lia. }
    assert (MSAL : map_size x mod 4096 = 0).
    { unfold map_size. clear. rewrite <- Z.mul_succ_l. apply Z_mod_mult. }
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL (CSf sc r) (K sc r) _ Q _ mo (KL sc r) HK); [exact HJ| |].
    { eapply (large_A AL IMG ALWF (CSf sc r) (CSOKf sc r)) with (lo := lo) (PA := PA); try exact ST; try exact SCS; try exact MI;
        [clear - Hx; lia| clear - PA0 PA1; lia| exact (proj1 LS)| exact LOIMG| clear - SPL DIE_NEED_ge; lia| exact SPH| exact SPA]. }
    cbn beta. (intros ms1 mo1 dd_H; ddestruct dd_H as (j0 & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1); intros HK1 MM1 HJ1).
    assert (LO1 : forall A n, A + n <= lo -> disjoint_from [(lo, SP)] A n) by (intros A n H; cbn; split; [left; exact H| exact I]).
    assert (LS1 : lstat m1) by (eapply lstat_transport; [exact LS| exact MU1| intros A n H _; apply LO1; clear - H LOIMG; lia| apply LO1; clear - CX1 LOIMG; lia]).
    assert (TJ1 : rw_cells asegs m1 (T + 2872) [C8 j1; C8 j2]) by (eapply rw_cells_transport; [exact TJ| exact MU1| exact WM1| apply LO1; cbn; clear - T1 LOIMG; lia]).
    assert (LI1 : limg m1 (0x4000 * r) ncks srt 0) by (eapply limg_transport; [exact LI| exact MU1| exact WM1| apply LO1; unfold A_INSTANCE; clear - LOIMG; lia]).
    assert (HPS1 : u64arr asegs m1 PA ps) by (eapply u64arr_transport; [exact HPS| exact MU1| exact WM1| apply LO1; clear - LPS HNC HNR PA1 LOIMG; lia]).
    assert (HREST1 : u64arr asegs m1 (PA + 8 * ncks) rest) by (eapply u64arr_transport; [exact HREST| exact MU1| exact WM1| apply LO1; clear - LREST HNC HNR PA1 LOIMG; lia]).
    pose proof (shadow_wr_mono _ _ SHW WM1) as SHW1.
    clear LS TJ LI HPS HREST ST MI SHW.
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL (CSf sc r) (K sc r) _ Q _ mo1 (KL sc r) HK1); [exact HJ1| |].
    { ddestruct LS1 as (_ & _ & _ & (W1 & W2 & W3 & W4 & W5 & _) & _).
      eapply (mmapanon_pre AL IMG ALWF (CSf sc r) (CSOKf sc r)) with (lo := lo); try exact W1; try exact W2; try exact W3; try exact W4; try exact ST1; try exact MI1.
      - clear - MSZ Hx; lia. - unfold A_LNAME; clear; lia. - clear - LOIMG; lia. - clear - SPL DIE_NEED_ge; lia. - clear - SPH; lia.
      - eapply crange_sub; [exact SCS| clear; lia| clear - SPL; lia]. }
    cbn beta. (intros ms2 mo2 dd_H; ddestruct dd_H as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & ua6 & m2 & fr & -> & MU2 & WM2 & MI2 & FR2 & ST2); intros HK2 MM2 HJ2).
    cbn [ms_mem MS MSsvc] in HJ2.
    assert (LO2 : forall A n, A + n <= lo -> disjoint_from [(lo, SP + -96)] A n) by (intros A n H; cbn; split; [left; exact H| exact I]).
    assert (LS2 : lstat m2) by (eapply lstat_transport; [exact LS1| exact MU2| intros A n H _; apply LO2; clear - H LOIMG; lia| apply LO2; clear - CX1 LOIMG; lia]).
    assert (TJ2 : rw_cells asegs m2 (T + 2872) [C8 j1; C8 j2]) by (eapply rw_cells_transport; [exact TJ1| exact MU2| exact WM2| apply LO2; cbn; clear - T1 LOIMG; lia]).
    assert (LI2 : limg m2 (0x4000 * r) ncks srt 0) by (eapply limg_transport; [exact LI1| exact MU2| exact WM2| apply LO2; unfold A_INSTANCE; clear - LOIMG; lia]).
    assert (HPS2 : u64arr asegs m2 PA ps) by (eapply u64arr_transport; [exact HPS1| exact MU2| exact WM2| apply LO2; clear - LPS HNC HNR PA1 LOIMG; lia]).
    assert (HREST2 : u64arr asegs m2 (PA + 8 * ncks) rest) by (eapply u64arr_transport; [exact HREST1| exact MU2| exact WM2| apply LO2; clear - LREST HNC HNR PA1 LOIMG; lia]).
    assert (FR12 : large_frame m2 SP j0 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra).
    { unfold large_frame in FR1 |- *. eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. cbn. split; [right; clear; lia| exact I]. }
    pose proof (shadow_wr_mono _ _ SHW1 WM2) as SHW2.
    assert (MU12 : munch [(lo, SP)] m m2).
    { eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear; intros; lia. }
    pose proof (wmono_trans _ _ _ _ WM1 WM2) as WM12.
    clear LS1 TJ1 LI1 HPS1 HREST1 ST1 MI1 SHW1 FR1 MU2 WM2 LO1 LO2.
    (* [comment removed for export] *)
    assert (PRU : (map_size x + 4095) / 4096 * 4096 = map_size x).
    { pose proof (Z.div_mod (map_size x) 4096 ltac:(clear; lia)) as DM. rewrite MSAL, Z.add_0_r in DM.
      replace ((map_size x + 4095) / 4096) with (map_size x / 4096); [clear - DM; lia|].
      apply Z.div_unique with (r := 4095); clear - DM MSZ Hx; lia. }
    lazymatch goal with |- aevtS _ _ (mkCfg ?MS2 _) =>
    eapply aevtS_of_aevt_bind;
      [ eapply (aevt_mmap_anon asegs (fun c => exists eff mo', anon_outcome 0x22 (map_size x) mo2 eff mo' /\ c = mkCfg (nret MS2 eff) mo')) with (nZ := map_size x) (flags := 0x22);
        [ exact (ki_halted (KL sc r) mo2 HK2)
        | exact (ki_top (KL sc r) mo2 HK2)
        | unfold mmap_anon_args, areg, MSsvc; cbn [ms_regs]; simp_regs
        | intros eff mo' OUT; dexists eff, mo'; split; [exact OUT| reflexivity] ]
      | ]
    end.
    { pose proof aceil_bounds as AC.
      rewrite !PRU. repeat split; try reflexivity.
      - rewrite unsigned_lit by (clear - MSZ Hx; lia). unfold page_round_up_Z, page_size.
        pose proof (Z.div_mod (map_size x) 4096 ltac:(clear; lia)) as DM. rewrite MSAL, Z.add_0_r in DM.
        replace ((map_size x + 4096 - 1) / 4096) with (map_size x / 4096); [clear - DM; lia|].
        apply Z.div_unique with (r := 4095); clear - DM MSZ Hx; lia.
      - intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by (clear - MSZ Hx; lia). clear - E MSZ Hx; lia.
      - clear - MSZ Hx; lia.
      - left. reflexivity. }
    (intros c3 dd_H; ddestruct dd_H as (eff & mo3 & OUT & ->)).
    destruct OUT as [e HIn | aw AAL A0 ACE RF].
    - (* [comment removed for export] *)
      destruct HIn as [<-|[]].
      rewrite nret_MSsvc, mkR_set_a0, apply_mem_none.
      replace (errno_ret ENOMEM) with (Z_to_bv 64 (2^64 - 12)) by (apply bv_eq; vm_compute; reflexivity).
      change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
      eapply (evtA_aevtS_KJ AL (CSf sc r) (K sc r)
                (fun ms' => exists (z0 z1 z2 za1 za2 za3 za4 za5 za6 za7 z3 z4 z5 z6 : word) (m' : mem),
                   ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp z0 z1 z2 s0 s1 (Z_to_bv 64 0) za1 za2 za3 za4 za5 za6 za7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z3 z4 z5 z6)
                            F (ret_pc ra) fc None m' (seg_rom asegs)
                   /\ munch [(lo, SP)] m2 m' /\ wmono asegs m2 m' /\ mem_inv asegs m' /\ stk asegs m' lo SP)
                Q _ mo2 (KL sc r) HK2); [exact HJ2| |].
      { eapply evtA_cut.
        { eapply (mmapanon_post_enomem AL IMG ALWF (CSf sc r) (CSOKf sc r)) with (m0 := m2) (lo := lo); try exact FR2; try exact ST2; try exact MI2.
          - clear - MSZ Hx; lia. - clear - LOIMG; lia. - clear - SPL DIE_NEED_ge; lia. - clear - SPH; lia.
          - apply munch_refl. - apply wmono_refl. - eapply crange_sub; [exact SCS| clear; lia| clear - SPL; lia]. }
        cbn beta. (intros ms4 dd_H; ddestruct dd_H as (z0 & z1 & z2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m4 & -> & MU4 & WM4 & MI4 & ST4)).
        replace (ret_pc (Z_to_bv 64 0x4c39c)) with (Z_to_bv 64 0x4c39c) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
        eapply evtA_mono.
        { eapply (large_null AL IMG ALWF (CSf sc r) (CSOKf sc r)) with (m0 := m2) (W := []).
          - unfold large_frame in FR12 |- *. eapply rw_cells_transport; [exact FR12| exact MU4| exact WM4|]. cbn. split; [right; clear; lia| exact I].
          - exact ST4. - exact LOIMG. - clear - SPL DIE_NEED_ge; lia. - exact SPH. - exact SPA. - exact SCS.
          - eapply munch_weaken; [| exact MU4]. unfold sub_fp; cbn [outside]; clear; intros; lia.
          - exact WM4. - exact MI4. }
        cbv beta. (intros ms5 dd_H; ddestruct dd_H as (m5 & -> & MU5 & WM5 & MI5 & ST5)). deexists 15. split; [reflexivity|]. split; [exact MU5|]. split; [exact WM5|]. split; [exact MI5| exact ST5]. }
      cbn beta. (intros ms5 mo5 dd_H; ddestruct dd_H as (z0 & z1 & z2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m5 & -> & MU5 & WM5 & MI5 & ST5); intros HK5 MM5 HJ5).
      apply (HC false). unfold large_cpostS. deexists 18. split; [reflexivity|]. split; [reflexivity|].
      split; [exact MI5|]. split; [exact ST5|]. split; [exact (wmono_trans _ _ _ _ WM12 WM5)|]. split; [exact (shadow_wr_mono _ _ SHW2 WM5)|].
      split. { eapply lstat_transport; [exact LS2| exact MU5| |]; cbn; [intros A n H _; split; [left; clear - H LOIMG; lia| exact I] | split; [left; clear - CX1 LOIMG; lia| exact I]]. }
      split; [reflexivity|]. split; [exact HK5|]. split; [exact HJ5|].
      split. { eapply munch_trans; [exact MU12|]. eapply munch_weaken; [| exact MU5]. unfold sub_fp; cbn [outside]; clear; intros; lia. }
      eapply rw_cells_transport; [exact TJ2| exact MU5| exact WM5| cbn; split; [left; clear - T1 LOIMG; lia| exact I]].
    - (* [comment removed for export] *)
      rewrite nret_MSsvc, mkR_set_a0, apply_mem_zeros.
      change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
      pose proof (bv_unsigned_in_range 64 aw) as AR. unfold bv_modulus in AR. change (2 ^ Z.of_N 64) with (2^64) in AR.
      set (a := bv_unsigned aw) in *.
      pose proof aceil_bounds as AC.
      pose proof (K_apart sc r mo2 aw (Z_to_bv 64 (map_size x)) HK2 RF) as AP. fold a in AP.
      rewrite (unsigned_lit (map_size x)) in AP by (clear - MSZ Hx; lia).
      specialize (AP ltac:(clear - MSZ Hx; lia) ltac:(exact ACE)).
      assert (AHI : 0x65f000 <= a).
      { destruct (Z.le_gt_cases 0x65f000 a) as [H|H]; [exact H|]. exfalso. destruct (Z.le_gt_cases 0x10000 a) as [H'|H'].
        - apply (AP a); [right; left; clear - IMG' H H'; lia| clear - MSZ Hx; lia].
        - apply (AP 0x10000); [right; left; clear - IMG'; lia| clear - H' A0 MSZ Hx; lia]. }
      assert (ABAND : a + map_size x <= 0x7fff7000 \/ 0x10007fff8000 <= a).
      { destruct (Z.le_gt_cases (a + map_size x) 0x7fff7000) as [H|H]; [left; exact H|]. right.
        destruct (Z.le_gt_cases 0x10007fff8000 a) as [H'|H']; [exact H'|]. exfalso.
        destruct (Z.le_gt_cases a 0x7fff7000) as [H2|H2].
        - apply (AP 0x7fff7000); [right; right; clear; lia| clear - H H2 MSZ Hx; lia].
        - apply (AP a); [right; right; clear - H2 H'; lia| clear - MSZ Hx; lia]. }
      assert (APCS : forall y, CSf sc r y -> ~ (a <= y < a + map_size x)) by (intros y Hy; apply AP; left; exact Hy).
      assert (SEPA' : PA + 0x800000 <= a \/ a + map_size x <= PA).
      { eapply (apart_of (fun y => PA <= y < PA + 0x800000)); [intros y Hy; apply AP; right; right; right; exact Hy| intros y Hy; exact Hy| clear; lia| clear - MSZ Hx; lia]. }
      assert (SEPA : a + map_size x <= PA \/ PA + 0x800000 <= a) by (clear - SEPA'; lia). clear SEPA'.
      destruct (T_large sc r (map_size x) mo2 aw HGl HK2 AAL A0 ACE RF) as [HK3 CR3]. fold a in HK3, CR3.
      pose proof (J_anon_grant m2 mo2 0x22 aw (map_size x) HJ2 ltac:(clear - MSZ Hx; lia) ltac:(fold a; clear - ACE AC; lia) RF) as HJ3.
      rewrite <- (Z_to_bv_bv_unsigned aw) in HK3 |- *. fold a in HK3 |- *.
      change (Z_to_bv 64 a, Z_to_bv 64 (map_size x)) with (wa a, Z_to_bv 64 (map_size x)).
      rewrite <- (Z_to_bv_bv_unsigned aw) in HJ3. fold a in HJ3. change (Z_to_bv 64 a, Z_to_bv 64 (map_size x)) with (wa a, Z_to_bv 64 (map_size x)) in HJ3.
      set (sc' := sc ++ [(a, map_size x)]) in *. clearbody a.
      assert (Ha : 0 <= a < 2^64) by (clear - AR; lia). assert (Hn : 0 <= map_size x < 2^64) by (clear - MSZ Hx; lia). assert (Han : a + map_size x <= 2^64) by (clear - ACE; lia).
      (* [comment removed for export] *)
      assert (APstk : forall A sz, lo <= A -> A + sz <= SP -> 0 < sz -> A + sz <= a \/ a + map_size x <= A).
      { intros A sz H1 H2 H3. eapply (apart_of (CSf sc r)); [exact APCS| | exact H3| clear - MSZ Hx; lia]. intros y Hy. apply SCS. clear - H1 H2 Hy; lia. }
      assert (APT : T + 4096 <= a \/ a + map_size x <= T).
      { eapply (apart_of (CSf sc r)); [exact APCS| apply CST| clear; lia| clear - MSZ Hx; lia]. }
      assert (APCTX : CTX + 0x10000 <= a \/ a + map_size x <= CTX).
      { eapply (apart_of (CSf sc r)); [exact APCS| apply CSCTX| clear; lia| clear - MSZ Hx; lia]. }
      assert (APPA : PA + 0x20000 * r <= a \/ a + map_size x <= PA) by (clear - SEPA HNR HR; lia).
      (* [comment removed for export] *)
      pose proof (rw_cells_zeros_new asegs m2 a (map_size x) Ha Hn Han) as NEWz.
      assert (MUz : munch [(lo, SP); (a, a + map_size x)] m (apply_zeros m2 [(wa a, Z_to_bv 64 (map_size x))])).
      { eapply (munch_zeros m2 a (map_size x) Ha Hn Han). 2:{ cbn. right. left. clear; lia. }
        eapply munch_weaken; [| exact MU12]. unfold sub_fp; cbn [outside]; clear; intros; lia. }
      pose proof (wmono_zeros asegs m2 a (map_size x) Ha Hn Han m WM12) as WMz.
      assert (MIz : mem_inv asegs (apply_zeros m2 [(wa a, Z_to_bv 64 (map_size x))])).
      { eapply (mem_inv_zeros asegs m2 a (map_size x) Ha Hn Han MI2). intros y Hy.
        destruct (ro_addr asegs y) eqn:E; [| reflexivity]. exfalso. pose proof (asegs_ro_lt y E). clear - H Hy AHI. lia. }
      assert (FR2z : rw_cells asegs (apply_zeros m2 [(wa a, Z_to_bv 64 (map_size x))]) (SP + -96 + -48) [CB 12 fr; C4 (Z_to_bv 64 0x22); C8 (Z_to_bv 64 (map_size x)); C8 (Z_to_bv 64 (A_INSTANCE + 64)); C8 (Z_to_bv 64 (A_INSTANCE + 688)); C8 (Z_to_bv 64 0x4c39c)]).
      { eapply (rw_cells_zeros_other asegs m2 a (map_size x) Ha Hn Han); [exact FR2|]. cbn. apply APstk; clear - SPL DIE_NEED_ge; lia. }
      assert (FR12z : large_frame (apply_zeros m2 [(wa a, Z_to_bv 64 (map_size x))]) SP j0 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra).
      { unfold large_frame in FR12 |- *. eapply (rw_cells_zeros_other asegs m2 a (map_size x) Ha Hn Han); [exact FR12|]. cbn. apply APstk; clear - SPL DIE_NEED_ge; lia. }
      pose proof (stk_zeros asegs m2 a (map_size x) Ha Hn Han _ _ ST2) as STz.
      assert (MU2z : munch [(a, a + map_size x)] m2 (apply_zeros m2 [(wa a, Z_to_bv 64 (map_size x))])).
      { eapply (munch_zeros m2 a (map_size x) Ha Hn Han); [apply munch_refl| cbn; left; clear; lia]. }
      pose proof (wmono_zeros asegs m2 a (map_size x) Ha Hn Han m2 (wmono_refl asegs m2)) as WM2z.
      assert (DJa : forall A n, (A + n <= a \/ a + map_size x <= A) -> disjoint_from [(a, a + map_size x)] A n) by (intros A n H; cbn; split; [exact H| exact I]).
      assert (LSz : lstat (apply_zeros m2 [(wa a, Z_to_bv 64 (map_size x))])).
      { eapply lstat_transport; [exact LS2| exact MU2z| intros A n H _; apply DJa; left; clear - H AHI; lia| apply DJa; clear - APCTX CX0 CX1; lia]. }
      assert (TJz : rw_cells asegs (apply_zeros m2 [(wa a, Z_to_bv 64 (map_size x))]) (T + 2872) [C8 j1; C8 j2]).
      { eapply rw_cells_transport; [exact TJ2| exact MU2z| exact WM2z| apply DJa; cbn; clear - APT; lia]. }
      assert (LIz : limg (apply_zeros m2 [(wa a, Z_to_bv 64 (map_size x))]) (0x4000 * r) ncks srt 0).
      { eapply limg_transport; [exact LI2| exact MU2z| exact WM2z| apply DJa; left; unfold A_INSTANCE; clear - AHI; lia]. }
      assert (HPSz : u64arr asegs (apply_zeros m2 [(wa a, Z_to_bv 64 (map_size x))]) PA ps).
      { destruct ps as [|p0 ps']; [eapply u64arr_nil_any; exact HPS2|].
        eapply u64arr_transport; [exact HPS2| exact MU2z| exact WM2z| apply DJa].
        cbn [length] in LPS |- *. clear - APPA LPS HNC HNR; lia. }
      assert (HRESTz : u64arr asegs (apply_zeros m2 [(wa a, Z_to_bv 64 (map_size x))]) (PA + 8 * ncks) rest).
      { destruct rest as [|r0 rest']; [eapply u64arr_nil_any; exact HREST2|].
        eapply u64arr_transport; [exact HREST2| exact MU2z| exact WM2z| apply DJa].
        cbn [length] in LREST |- *. clear - APPA LREST HNC HNR; lia. }
      pose proof (shadow_wr_mono _ _ SHW2 WM2z) as SHWz.
      set (mz := apply_zeros m2 [(wa a, Z_to_bv 64 (map_size x))]) in *. clearbody mz.
      clear FR2 FR12 ST2 MI2 LS2 TJ2 LI2 HPS2 HREST2 SHW2 AP RF MU2z WM2z DJa.
      (* [comment removed for export] *)
      assert (SHa : exists junk1, rw_cells asegs mz (0x7fff8000 + a / 8) [CB 512%nat junk1]).
      { destruct SHWz as [SL SH]. destruct ABAND as [LOW|HIGH].
        - eapply wr_at_cells; [clear - AHI; lia|]. eapply wr_at_sub; [exact SL| clear - AHI; lia| clear - LOW MSZ Hx; cbn; lia].
        - eapply wr_at_cells; [clear - HIGH; lia|]. eapply wr_at_sub; [exact SH| clear - HIGH; lia| clear - ACE MSZ Hx HIGH; cbn; lia]. }
      destruct SHa as [junk1 SHa].
      assert (SHb : exists junk2, rw_cells asegs mz (0x7fff8000 + (a + 4096 + x) / 8) [CB (Z.to_nat ((map_size x - 4096 - x) / 8)) junk2]).
      { destruct SHWz as [SL SH]. destruct ABAND as [LOW|HIGH].
        - eapply wr_at_cells; [clear - AHI Hx; lia|]. eapply wr_at_sub; [exact SL| clear - AHI Hx; lia| rewrite Z2Nat.id by (clear - MSZ; lia); clear - LOW MSZ Hx; lia].
        - eapply wr_at_cells; [clear - HIGH Hx; lia|]. eapply wr_at_sub; [exact SH| clear - HIGH Hx; lia| rewrite Z2Nat.id by (clear - MSZ; lia); clear - ACE MSZ Hx HIGH; lia]. }
      destruct SHb as [junk2 SHb].
      (* [comment removed for export] *)
      assert (A8 : a mod 8 = 0).
      { clear - AAL. pose proof (Z.div_mod a 4096 ltac:(lia)). rewrite AAL in *. replace a with ((512 * (a / 4096)) * 8) by lia. apply Z_mod_mult. }
      pose proof (Z.div_mod a 8 ltac:(clear; lia)) as DA8. rewrite A8, Z.add_0_r in DA8.
      pose proof (Z.div_mod x 8 ltac:(clear; lia)) as DX8. rewrite XAL, Z.add_0_r in DX8.
      assert (MS8 : map_size x mod 8 = 0).
      { clear - MSAL. pose proof (Z.div_mod (map_size x) 4096 ltac:(lia)). rewrite MSAL in *. replace (map_size x) with ((512 * (map_size x / 4096)) * 8) by lia. apply Z_mod_mult. }
      pose proof (Z.div_mod (map_size x) 8 ltac:(clear; lia)) as DM8. rewrite MS8, Z.add_0_r in DM8.
      assert (E8 : (a + 4096 + x) / 8 = a / 8 + 512 + x / 8) by (symmetry; apply (Z.div_unique _ 8 _ 0); clear - DA8 DX8; lia).
      assert (E8b : (map_size x - 4096 - x) / 8 = map_size x / 8 - 512 - x / 8) by (symmetry; apply (Z.div_unique _ 8 _ 0); clear - DM8 DX8; lia).
      assert (SHTOP : 0x7fff8000 + (a + map_size x) / 8 <= 0x10007fff0000) by (clear - ACE AHI MSZ Hx; lia).
      (* [comment removed for export] *)
      assert (HDR0 : rw_cells asegs mz a ([C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ++ [CB (Z.to_nat (map_size x - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (map_size x - 32)))])).
      { eapply rw_cells_zeros; [exact NEWz| cbn; repeat split; reflexivity| cbn [cells_size csize app Nat.add]; clear - MSZ Hx; lia]. }
      apply rw_cells_app in HDR0 as [HDRz ZBz]. cbn [cells_size csize Nat.add] in ZBz. change (Z.of_nat 32) with 32 in ZBz.
      pose proof HDRz as HDRz3. change [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] with ([C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 0)]) in HDRz3.
      apply rw_cells_app in HDRz3 as [HDRz3 H3z]. cbn [cells_size csize Nat.add] in H3z. change (Z.of_nat 24) with 24 in H3z.
      assert (SCS' : crange (CSf sc' r) lo (SP - lo)) by (intros y Hy; unfold sc'; apply CSmono_l; apply SCS; exact Hy).
      assert (K16 : 16 <= Z.log2 (map_size x) <= 41).
      { split. - apply Z.log2_le_pow2; clear - MSZ Hx; lia. - apply Z.lt_succ_r. apply Z.log2_lt_pow2; clear - MSZ Hx; lia. }
      (* [comment removed for export] *)
      eapply (evtA_aevtS_KJ AL (CSf sc' r) (K sc' r)
                (fun ms' => exists (z0 z1 z2 za1 za7 z3 z4 z5 z6 : word) (m6 : mem),
                   ms' = MS (mkR (Z_to_bv 64 0x4c408) (Z_to_bv 64 (SP + -96)) gp tp z0 z1 z2 (Z_to_bv 64 (A_INSTANCE + 688)) (Z_to_bv 64 (A_INSTANCE + 64))
                                (Z_to_bv 64 (a + 4096)) za1 (Z_to_bv 64 0x0101010101010101) (Z_to_bv 64 ncks) (Z_to_bv 64 (0x4000 * r)) (Z_to_bv 64 0x0f0f0f0f0f0f0f0f) (Z_to_bv 64 0x1010101) za7
                                (Z_to_bv 64 (map_size x)) (Z_to_bv 64 (63 - Z.log2 (map_size x))) (Z_to_bv 64 a) (Z_to_bv 64 a) (Z_to_bv 64 (a + map_size x)) (Z_to_bv 64 (a + 4096 + x))
                                (Z_to_bv 64 7) (Z_to_bv 64 (a + 4096)) s10 s11 z3 z4 z5 z6) F (Z_to_bv 64 0x4c540) fc None m6 (seg_rom asegs)
                   /\ munch [(lo, SP + -96); (0x7fff8000 + a / 8, 0x7fff8000 + a / 8 + 512); (0x7fff8000 + (a + 4096 + x) / 8, 0x7fff8000 + (a + 4096 + x) / 8 + (map_size x - 4096 - x) / 8);
                             (T + 2872, T + 2888); (a, a + 24); (A_INSTANCE + 680, A_INSTANCE + 684)] mz m6
                   /\ wmono asegs mz m6 /\ mem_inv asegs m6 /\ stk asegs m6 lo (SP + -96)
                   /\ rw_cells asegs m6 (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned j1 + 1)); C8 (Z_to_bv 64 (bv_unsigned j2 + map_size x))]
                   /\ rw_cells asegs m6 a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 (map_size x)); C8 (Z_to_bv 64 x)]
                   /\ rw_cells asegs m6 (A_INSTANCE + 680) [C4 (Z_to_bv 64 1)]
                   /\ rw_cells asegs m6 (0x7fff8000 + a / 8) [CB 512%nat (repeat (Z_to_bv 8 0xfa) 512%nat)]
                   /\ rw_cells asegs m6 (0x7fff8000 + (a + 4096 + x) / 8) [CB (Z.to_nat ((map_size x - 4096 - x) / 8)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat ((map_size x - 4096 - x) / 8)))])
                Q _ _ (KL sc' r) HK3); [exact HJ3| |].
      { pose proof LSz as LSzc. ddestruct LSzc as (LST & TS & PS & (W1 & W2 & W3 & W4 & W5 & _) & DS).
        (* [comment removed for export] *)
        eapply evtA_cut.
        { eapply (mmapanon_post_ok AL IMG ALWF (CSf sc' r) (CSOKf sc' r)) with (m0 := mz) (lo := lo) (a := Z_to_bv 64 a); try exact FR2z; try exact W3; try exact W5; try exact STz; try exact MIz.
          - clear - MSZ Hx; lia. - rewrite unsigned_lit by (clear - AR; lia); clear - AHI; lia. - rewrite unsigned_lit by (clear - AR; lia); exact ACE.
          - clear - LOIMG; lia. - clear - SPL DIE_NEED_ge; lia. - clear - SPH; lia. - apply munch_refl. - apply wmono_refl.
          - eapply crange_sub; [exact SCS'| clear; lia| clear - SPL; lia]. }
        cbv beta. (intros ms4 dd_H; ddestruct dd_H as (z0 & z1 & z2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m4 & -> & MU4 & WM4 & MI4 & ST4)).
        replace (ret_pc (Z_to_bv 64 0x4c39c)) with (Z_to_bv 64 0x4c39c) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
        assert (LO4 : forall A n, A + n <= lo -> disjoint_from [(lo, SP + -96)] A n) by (intros A n H; cbn; split; [left; exact H| exact I]).
        assert (LST4 : large_statics m4 PA) by (eapply large_statics_transport; [exact LST| exact MU4| | |]; apply LO4; unfold A_INSTANCE, A_GOT_LNAME, A_LNAME_CELL; cbn; clear - LOIMG; lia).
        (* [comment removed for export] *)
        eapply evtA_cut.
        { eapply (large_B AL IMG ALWF (CSf sc' r) (CSOKf sc' r)) with (PA := PA); [exact Hx40| exact XAL| clear - AHI; lia| exact AAL| exact ACE| clear - PA0 PA1; lia| exact LST4| exact MI4]. }
        cbv beta. (intros ms5 dd_H; ddestruct dd_H as (y3 & y4 & y5 & y6 & y7 & ->)).
        (* [comment removed for export] *)
        eapply evtA_cut.
        { eapply (poison_spec AL IMG ALWF (CSf sc' r) (CSOKf sc' r) ASB) with (m0 := m4) (W := []) (lo := lo) (junk := junk1).
          - clear - AAL; pose proof (Z.div_mod a 4096 ltac:(lia)); rewrite AAL in *; replace a with ((512 * (a / 4096)) * 8) by lia; apply Z_mod_mult.
          - reflexivity. - clear; lia. - clear; lia.
          - destruct ABAND as [LOW|HIGH]; [left; clear - LOW AHI MSZ Hx; lia| right; clear - HIGH ACE MSZ Hx; lia].
          - left; clear; lia.
          - eapply crange_sub; [exact CR3| clear; lia| clear - MSZ Hx; lia].
          - change (Z.to_nat (4096 / 8)) with 512%nat. eapply rw_cells_transport; [exact SHa| exact MU4| exact WM4| apply LO4]. cbn. clear - LOIMG ACE AHI MSZ Hx; lia.
          - eapply poison_statics_transport; [exact PS| exact MU4|]. intros A n H; apply LO4; clear - H LOIMG; lia.
          - exact ST4. - exact LOIMG. - clear - SPL DIE_NEED_ge; lia. - clear - SPH; lia. - clear - SPA; pose proof (Z.div_mod SP 16 ltac:(lia)) as D16; rewrite SPA in D16; replace (SP + -96) with ((SP / 16 - 6) * 16) by lia; apply Z_mod_mult.
          - eapply crange_sub; [exact SCS'| clear; lia| clear - SPL; lia]. - apply munch_refl. - apply wmono_refl. - exact MI4. }
        cbv beta. (intros ms6 dd_H; ddestruct dd_H as (p0 & p1 & p2 & pa0 & pa1 & pa2 & pa3 & pa4 & pa5 & pa6 & pa7 & p3 & p4 & p5 & p6 & m5 & -> & MU5 & WM5 & MI5 & SHA5 & ST5)).
        replace (ret_pc (Z_to_bv 64 0x4c3f4)) with (Z_to_bv 64 0x4c3f4) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
        change (4096 / 8) with 512 in MU5, SHA5. change (Z.to_nat 512) with 512%nat in SHA5.
        assert (LO5 : forall A n, A + n <= lo -> (A + n <= 0x7fff8000 + a / 8 \/ 0x7fff8000 + a / 8 + 512 <= A) -> disjoint_from [(lo, SP + -96); (0x7fff8000 + a / 8, 0x7fff8000 + a / 8 + 512)] A n).
        { intros A n H1 H2; cbn; split; [left; exact H1| split; [exact H2| exact I]]. }
        assert (LST5 : large_statics m5 PA) by (eapply large_statics_transport; [exact LST4| exact MU5| | |]; apply LO5; unfold A_INSTANCE, A_GOT_LNAME, A_LNAME_CELL; cbn; clear - LOIMG AHI; lia).
        assert (MU45 : munch [(lo, SP + -96); (0x7fff8000 + a / 8, 0x7fff8000 + a / 8 + 512)] mz m5).
        { eapply munch_trans; [| exact MU5]. eapply munch_weaken; [| exact MU4]. unfold sub_fp; cbn [outside]; clear; intros; lia. }
        assert (PS5 : poison_statics m5).
        { eapply poison_statics_transport; [exact PS| exact MU45|]. intros A n H; apply LO5; clear - H LOIMG AHI; lia. }
        assert (SHb5 : rw_cells asegs m5 (0x7fff8000 + (a + 4096 + x) / 8) [CB (Z.to_nat ((map_size x - 4096 - x) / 8)) junk2]).
        { eapply rw_cells_transport; [exact SHb| exact MU45 | eapply wmono_trans; [exact WM4| exact WM5] |].
          - apply LO5; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - MSZ DM8 DX8; lia); rewrite E8; clear - LOIMG SHTOP MSZ Hx DA8 DX8 DM8 AHI; lia. }
        (* [comment removed for export] *)
        eapply evtA_cut.
        { eapply (large_C AL IMG ALWF (CSf sc' r) (CSOKf sc' r)); [exact Hx40| clear - AHI; lia| exact ACE| exact MI5]. }
        cbv beta. intros ms7 ->.
        (* [comment removed for export] *)
        eapply evtA_cut.
        { eapply (poison_spec AL IMG ALWF (CSf sc' r) (CSOKf sc' r) ASB) with (m0 := m5) (W := []) (lo := lo) (junk := junk2).
          - clear - DA8 DX8. replace (a + 4096 + x) with ((a / 8 + 512 + x / 8) * 8) by lia. apply Z_mod_mult.
          - clear - DM8 DX8. replace (map_size x - 4096 - x) with ((map_size x / 8 - 512 - x / 8) * 8) by lia. apply Z_mod_mult.
          - clear - MSZ; lia. - clear; lia.
          - destruct ABAND as [LOW|HIGH]; [left; clear - LOW AHI MSZ Hx; lia| right; clear - HIGH ACE MSZ Hx; lia].
          - left; clear; lia.
          - eapply crange_sub; [exact CR3| clear - Hx; lia| clear; lia].
          - exact SHb5.
          - exact PS5.
          - exact ST5. - exact LOIMG. - clear - SPL DIE_NEED_ge; lia. - clear - SPH; lia.
          - clear - SPA; pose proof (Z.div_mod SP 16 ltac:(lia)) as D16; rewrite SPA in D16; replace (SP + -96) with ((SP / 16 - 6) * 16) by lia; apply Z_mod_mult.
          - eapply crange_sub; [exact SCS'| clear; lia| clear - SPL; lia]. - apply munch_refl. - apply wmono_refl. - exact MI5. }
        cbv beta. (intros ms8 dd_H; ddestruct dd_H as (q0 & q1 & q2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m6 & -> & MU6 & WM6 & MI6 & SHB6 & ST6)).
        replace (ret_pc (Z_to_bv 64 0x4c404)) with (Z_to_bv 64 0x4c404) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
        (* [comment removed for export] *)
        assert (MU46 : munch [(lo, SP + -96); (0x7fff8000 + a / 8, 0x7fff8000 + a / 8 + 512); (0x7fff8000 + (a + 4096 + x) / 8, 0x7fff8000 + (a + 4096 + x) / 8 + (map_size x - 4096 - x) / 8)] m4 m6).
        { eapply munch_trans. { eapply munch_weaken; [| exact MU5]. unfold sub_fp; cbn [outside]; clear; intros; lia. }
          eapply munch_weaken; [| exact MU6]. unfold sub_fp; cbn [outside]; clear; intros; lia. }
        pose proof (wmono_trans _ _ _ _ WM5 WM6) as WM46.
        assert (MUz6 : munch [(lo, SP + -96); (0x7fff8000 + a / 8, 0x7fff8000 + a / 8 + 512); (0x7fff8000 + (a + 4096 + x) / 8, 0x7fff8000 + (a + 4096 + x) / 8 + (map_size x - 4096 - x) / 8)] mz m6).
        { eapply munch_trans; [| exact MU46]. eapply munch_weaken; [| exact MU4]. unfold sub_fp; cbn [outside]; clear; intros; lia. }
        pose proof (wmono_trans _ _ _ _ WM4 WM46) as WMz6.
        assert (LO6 : forall A n, A + n <= lo -> A + n <= 0x7fff8000 + a / 8 -> disjoint_from [(lo, SP + -96); (0x7fff8000 + a / 8, 0x7fff8000 + a / 8 + 512); (0x7fff8000 + (a + 4096 + x) / 8, 0x7fff8000 + (a + 4096 + x) / 8 + (map_size x - 4096 - x) / 8)] A n).
        { intros A n H1 H2; cbn. split; [left; exact H1|]. split; [left; exact H2|]. split; [left; rewrite E8; clear - H2 DX8 Hx; lia| exact I]. }
        assert (HI6 : forall A n, 0x10007fff0000 <= A -> A + n <= lo -> disjoint_from [(lo, SP + -96); (0x7fff8000 + a / 8, 0x7fff8000 + a / 8 + 512); (0x7fff8000 + (a + 4096 + x) / 8, 0x7fff8000 + (a + 4096 + x) / 8 + (map_size x - 4096 - x) / 8)] A n).
        { intros A n H1 H2; cbn. split; [left; exact H2|]. split; [right; clear - H1 SHTOP MSZ Hx DA8 DM8; lia|]. split; [right; rewrite E8; clear - H1 SHTOP MSZ Hx DA8 DX8 DM8; lia| exact I]. }
        destruct (limg_parts _ _ _ _ _ LIz) as (LIa & _ & _ & LImx & _).
        pose proof LIa as NRC. change [C8 (Z_to_bv 64 (0x4000 * r)); C8 (Z_to_bv 64 ncks); C1 srt] with ([C8 (Z_to_bv 64 (0x4000 * r)); C8 (Z_to_bv 64 ncks)] ++ [C1 srt]) in NRC.
        apply rw_cells_app in NRC as [NRC _].
        assert (LS6 : lstat m6).
        { eapply lstat_transport; [exact LSz| exact MUz6 | intros A n H _; apply LO6; clear - H LOIMG AHI; lia|].
          (* [comment removed for export] *)
          destruct (proj2 CX0) as [CXL|CXH]; [apply LO6; clear - CXL CX1 LOIMG AHI; lia| apply HI6; clear - CXH CX1 LOIMG; lia]. }
        ddestruct LS6 as (LST6 & TS6 & PS6 & MW6 & DS6).
        assert (TJ6 : rw_cells asegs m6 (T + 2872) [C8 j1; C8 j2]).
        { eapply rw_cells_transport; [exact TJz| exact MUz6| exact WMz6|].
          destruct (proj2 T0) as [TLW|THG]; [apply LO6; cbn; clear - TLW T1 LOIMG AHI; lia| apply HI6; cbn; clear - THG T1 LOIMG; lia]. }   (* [comment removed for export] *)
        assert (HDR6 : rw_cells asegs m6 a [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
        { eapply rw_cells_transport; [exact HDRz3| exact MUz6| exact WMz6|].
          destruct ABAND as [LOW|HIGH]; [apply LO6; cbn; clear - LOW LOIMG AHI MSZ Hx; lia| apply HI6; cbn; clear - HIGH ACE LOIMG MSZ Hx; lia]. }
        assert (MX6 : rw_cells asegs m6 (A_INSTANCE + 680) [C4 (Z_to_bv 64 0)]).
        { eapply rw_cells_transport; [exact LImx| exact MUz6| exact WMz6| apply LO6; unfold A_INSTANCE; cbn; clear - LOIMG AHI; lia]. }
        assert (NRC6 : rw_cells asegs m6 (A_INSTANCE + 112) [C8 (Z_to_bv 64 (0x4000 * r)); C8 (Z_to_bv 64 ncks)]).
        { eapply rw_cells_transport; [exact NRC| exact MUz6| exact WMz6| apply LO6; unfold A_INSTANCE; cbn; clear - LOIMG AHI; lia]. }
        assert (ST6' : stk asegs m6 lo (SP + -96)) by exact ST6.
        (* [comment removed for export] *)
        eapply evtA_mono.
        { eapply (large_D AL IMG ALWF (CSf sc' r) (CSOKf sc' r)) with (m := m6) (PA := PA) (T := T) (CTX := CTX) (nres := 0x4000 * r) (ncks := ncks) (lo := lo).
          all: lazymatch goal with
               | |- large_statics _ _ => exact LST6
               | |- thr_statics _ _ _ => exact TS6
               | |- _ = Z_to_bv 64 A_TP => exact TP
               | |- rw_cells _ _ (T + 2872) _ => exact TJ6
               | |- rw_cells _ _ (A_INSTANCE + 680) _ => exact MX6
               | |- rw_cells _ _ (A_INSTANCE + 112) _ => exact NRC6
               | |- rw_cells _ _ _ _ => exact HDR6
               | |- stk _ _ _ _ => exact ST6'
               | |- mem_inv _ _ => exact MI6
               | |- crange _ CTX _ => apply CSCTX
               | |- crange _ T _ => apply CST
               | |- crange _ _ (_ - _) => exact SCS'
               | |- crange _ _ 24 => eapply crange_sub; [exact CR3| clear; lia| clear - MSZ Hx; lia]
               | |- _ => idtac end.
          all: first [sassumption | cassumption | exact Hx40 | exact XAL | exact AHI | exact AAL | exact ACE | exact LOIMG | exact SPH | exact SPA
                     | (clear - PA0 PA1; lia) | (clear - HNC HNR HR; lia) | (clear - CX0 CX1; lia) | (clear - T0 T1; lia) | (clear - APT; lia) | (clear - SPL DIE_NEED_ge; lia) ]. }
        cbv beta. (intros ms9 dd_H; ddestruct dd_H as (w0 & w1 & w2 & wa1 & wa7 & w3 & w4 & w5 & w6 & m7 & -> & MU7 & WM7 & MI7 & TJ7 & HDR7 & MX7 & ST7)).
        deexists 10. split; [reflexivity|].
        split. { eapply munch_trans. { eapply munch_weaken; [| exact MUz6]. unfold sub_fp; cbn [outside]; clear; intros; lia. }
                 eapply munch_weaken; [| exact MU7]. unfold A_INSTANCE; unfold sub_fp; cbn [outside]; clear; intros; lia. }
        split; [exact (wmono_trans _ _ _ _ WMz6 WM7)|]. split; [exact MI7|]. split; [exact ST7|].
        split; [exact TJ7|]. split; [exact HDR7|]. split; [exact MX7|].
        assert (MU57 : munch [(lo, SP + -96); (T + 2872, T + 2888); (a, a + 24); (A_INSTANCE + 680, A_INSTANCE + 684); (0x7fff8000 + (a + 4096 + x) / 8, 0x7fff8000 + (a + 4096 + x) / 8 + (map_size x - 4096 - x) / 8)] m5 m7).
        { eapply munch_trans. { eapply munch_weaken; [| exact MU6]. unfold sub_fp; cbn [outside]; clear; intros; lia. }
          eapply munch_weaken; [| exact MU7]. unfold sub_fp; cbn [outside]; clear; intros; lia. }
        split. { eapply rw_cells_transport; [exact SHA5| exact MU57 | exact (wmono_trans _ _ _ _ WM6 WM7)|].
                 cbn [disjoint_from cells_size csize]. rewrite Nat.add_0_r. change (Z.of_nat 512) with 512. unfold A_INSTANCE. rewrite E8.
                 split. { left. clear - LOIMG SHTOP MSZ Hx DA8 DM8 AHI ACE. lia. }
                 split; [destruct (proj2 T0) as [TLW|THG]; [right; clear - TLW MSZ Hx DA8 DM8 AHI; lia| left; clear - SHTOP MSZ Hx DA8 DM8 AHI ACE THG; lia]|].   (* [comment removed for export] *)
                 split; [destruct ABAND as [LOW|HIGH]; [right; clear - LOW AHI MSZ Hx; lia| left; clear - HIGH SHTOP MSZ Hx AHI DA8 DM8; lia]|].
                 split; [right; clear - AHI; lia|]. split; [left; clear - Hx DX8; lia| exact I]. }
        eapply rw_cells_transport; [exact SHB6| exact MU7| exact WM7|].
        cbn [disjoint_from cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - MSZ Hx DM8 DX8 E8b; lia). unfold A_INSTANCE. rewrite E8, E8b.
        split; [left; clear - LOIMG SHTOP MSZ Hx DA8 DX8 DM8 AHI ACE; lia|].
        split; [destruct (proj2 T0) as [TLW|THG]; [right; clear - TLW MSZ Hx DA8 DX8 DM8 AHI; lia| left; clear - SHTOP MSZ Hx DA8 DX8 DM8 AHI ACE THG; lia]|].
        split; [destruct ABAND as [LOW|HIGH]; [right; clear - LOW AHI MSZ Hx DA8 DX8; lia| left; clear - HIGH SHTOP MSZ Hx AHI DA8 DX8 DM8 ACE; lia]|].
        split; [right; clear - AHI Hx DA8 DX8; lia| exact I].
      }
      cbn beta. (intros ms9 mo6 dd_H; ddestruct dd_H as (w0 & w1 & w2 & wa1 & wa7 & w3 & w4 & w5 & w6 & m7 & -> & MU47 & WM47 & MI7 & ST7 & TJ7 & HDR7 & MX7 & SHA7 & SHB7); intros HK6 MM6 HJ6).
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (IMG7 : img_static_ok [(lo, SP + -96); (0x7fff8000 + a / 8, 0x7fff8000 + a / 8 + 512); (0x7fff8000 + (a + 4096 + x) / 8, 0x7fff8000 + (a + 4096 + x) / 8 + (map_size x - 4096 - x) / 8);
                                    (T + 2872, T + 2888); (a, a + 24); (A_INSTANCE + 680, A_INSTANCE + 684)]).
      { intros A n H1 H2; cbn. unfold A_INSTANCE in *. split; [left; clear - H1 LOIMG; lia|]. split; [left; clear - H1 AHI; lia|]. split; [left; rewrite E8; clear - H1 AHI Hx; lia|].
        split; [clear - H1 T0; lia|]. split; [left; clear - H1 AHI; lia|]. split; [clear - H2; lia| exact I]. }
      assert (LS7 : lstat m7).
      { eapply lstat_transport; [exact LSz| exact MU47| exact IMG7|]. cbn. unfold A_INSTANCE.
        split; [left; clear - CX1 LOIMG; lia|]. split; [clear - CX0 SHTOP MSZ Hx AHI DA8 DM8; lia|]. split; [rewrite E8, E8b; clear - CX0 SHTOP MSZ Hx AHI ACE DA8 DX8 DM8; lia|].
        split; [clear - SEP2; lia|]. split; [clear - APCTX MSZ Hx; lia|]. split; [right; clear - CX0; lia| exact I]. }
      (* [comment removed for export] *)
      assert (HIW : forall A n, (0x65f000 <= A /\ (A + n <= 0x7fff7000 \/ 0x10007fff0000 <= A)) -> A + n <= lo -> (A + n <= T + 2872 \/ T + 2888 <= A) -> (A + n <= a \/ a + 24 <= A) ->
                disjoint_from [(lo, SP + -96); (0x7fff8000 + a / 8, 0x7fff8000 + a / 8 + 512); (0x7fff8000 + (a + 4096 + x) / 8, 0x7fff8000 + (a + 4096 + x) / 8 + (map_size x - 4096 - x) / 8);
                               (T + 2872, T + 2888); (a, a + 24); (A_INSTANCE + 680, A_INSTANCE + 684)] A n).
      { intros A n H1 H2 H3 H4; cbn. unfold A_INSTANCE. split; [left; exact H2|]. split; [clear - H1 SHTOP MSZ Hx AHI DA8 DM8; lia|].
        split; [rewrite E8, E8b; clear - H1 SHTOP MSZ Hx AHI ACE DA8 DX8 DM8; lia|]. split; [exact H3|]. split; [exact H4|]. split; [right; clear - H1; lia| exact I]. }
      assert (BLKW : forall A n, a + 24 <= A -> A + n <= a + map_size x ->
                disjoint_from [(lo, SP + -96); (0x7fff8000 + a / 8, 0x7fff8000 + a / 8 + 512); (0x7fff8000 + (a + 4096 + x) / 8, 0x7fff8000 + (a + 4096 + x) / 8 + (map_size x - 4096 - x) / 8);
                               (T + 2872, T + 2888); (a, a + 24); (A_INSTANCE + 680, A_INSTANCE + 684)] A n).
      { intros A n H1 H2; cbn. unfold A_INSTANCE. split; [left; clear - H2 ACE LOIMG; lia|].
        split. { destruct ABAND as [LOW|HIGH]; [left; clear - H2 LOW AHI; lia| right; clear - H1 HIGH SHTOP MSZ Hx AHI DA8 DM8; lia]. }
        split. { destruct ABAND as [LOW|HIGH]; [left; rewrite E8; clear - H2 LOW AHI Hx DX8; lia| right; rewrite E8, E8b; clear - H1 HIGH SHTOP MSZ Hx AHI ACE DA8 DX8 DM8; lia]. }
        split; [clear - H1 H2 APT; lia|]. split; [right; exact H1|]. split; [right; clear - H1 AHI; lia| exact I]. }
      assert (FR7 : large_frame m7 SP j0 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra).
      { unfold large_frame in FR12z |- *. eapply rw_cells_transport; [exact FR12z| exact MU47| exact WM47|]. cbn; unfold A_INSTANCE.
        split; [right; clear; lia|]. split; [right; clear - SHTOP LOIMG SPL DIE_NEED_ge MSZ Hx AHI DA8 DM8; lia|]. split; [right; rewrite E8, E8b; clear - SHTOP LOIMG SPL DIE_NEED_ge MSZ Hx AHI DA8 DM8 DX8 ACE; lia|].
        split; [right; clear - T1 LOIMG SPL DIE_NEED_ge; lia|]. split; [right; clear - ACE LOIMG SPL DIE_NEED_ge MSZ Hx; lia|]. split; [right; clear - LOIMG SPL DIE_NEED_ge; lia| exact I]. }
      assert (LI7 : limg m7 (0x4000 * r) ncks srt 1).
      { eapply limg_set_mutex; [exact LIz| exact MU47| exact WM47| | | exact MX7]; cbn; unfold A_INSTANCE.
        - split; [left; clear - LOIMG; lia|]. split; [left; clear - AHI; lia|]. split; [left; rewrite E8; clear - AHI Hx; lia|]. split; [clear - T0; lia|]. split; [left; clear - AHI; lia|]. split; [left; clear; lia| exact I].
        - split; [left; clear - LOIMG; lia|]. split; [left; clear - AHI; lia|]. split; [left; rewrite E8; clear - AHI Hx; lia|]. split; [clear - T0; lia|]. split; [left; clear - AHI; lia|]. split; [right; clear; lia| exact I]. }
      assert (HPS7 : u64arr asegs m7 PA ps).
      { destruct ps as [|p0 ps']; [eapply u64arr_nil_any; exact HPSz|].
        eapply u64arr_transport; [exact HPSz| exact MU47| exact WM47| apply HIW]; cbn [length] in LPS |- *.
        - clear - PA0 PA1 LPS HNC HNR; lia. - clear - PA1 LOIMG LPS HNC HNR; lia. - clear - SEP1 LPS HNC HNR; lia.
        - clear - APPA LPS HNC HNR MSZ Hx; lia. }
      assert (HREST7 : u64arr asegs m7 (PA + 8 * ncks) rest).
      { destruct rest as [|r0 rest']; [eapply u64arr_nil_any; exact HRESTz|].
        eapply u64arr_transport; [exact HRESTz| exact MU47| exact WM47| apply HIW]; cbn [length] in LREST |- *.
        - clear - PA0 PA1 LREST HNC HNR; lia. - clear - PA1 LOIMG LREST HNC HNR; lia. - clear - SEP1 LREST HNC HNR; lia.
        - clear - APPA LREST HNC HNR MSZ Hx; lia. }
      assert (H37 : rw_cells asegs m7 (a + 24) [C8 (Z_to_bv 64 0)]).
      { eapply rw_cells_transport; [exact H3z| exact MU47| exact WM47| apply BLKW; cbn; clear - MSZ Hx; lia]. }
      assert (ZB7 : rw_cells asegs m7 (a + 32) [CB (Z.to_nat (map_size x - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (map_size x - 32)))]).
      { eapply rw_cells_transport; [exact ZBz| exact MU47| exact WM47| apply BLKW; cbn; rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - MSZ Hx; lia); clear - MSZ Hx; lia]. }
      pose proof (shadow_wr_mono _ _ SHWz WM47) as SHW7.
      assert (MU07 : munch [(lo, SP); (a, a + map_size x); (0x7fff8000 + a / 8, 0x7fff8000 + a / 8 + 512); (0x7fff8000 + (a + 4096 + x) / 8, 0x7fff8000 + (a + 4096 + x) / 8 + (map_size x - 4096 - x) / 8);
                            (T + 2872, T + 2888); (A_INSTANCE + 680, A_INSTANCE + 684)] m m7).
      { eapply munch_trans. { eapply munch_weaken; [| exact MUz]. unfold sub_fp; cbn [outside]; clear; intros; lia. }
        eapply munch_weaken; [| exact MU47]. unfold A_INSTANCE; unfold sub_fp; cbn [outside]; clear - MSZ Hx; intros; lia. }
      pose proof (wmono_trans _ _ _ _ WMz WM47) as WM07.
      clear FR12z LIz HPSz HRESTz H3z ZBz SHWz HDRz HDRz3 NEWz LSz TJz STz MIz FR2z IMG7 HIW BLKW MU47 WM47.
      destruct (limg_parts _ _ _ _ _ LI7) as (LIa7 & (st7 & STC7 & LST7) & (bsl7 & BSL7 & LBSL7) & _ & (g07 & g17 & GS7)).
      pose proof LIa7 as NC7. change [C8 (Z_to_bv 64 (0x4000 * r)); C8 (Z_to_bv 64 ncks); C1 srt] with ([C8 (Z_to_bv 64 (0x4000 * r))] ++ [C8 (Z_to_bv 64 ncks); C1 srt]) in NC7.
      apply rw_cells_app in NC7 as [NR7 NC7]. cbn [cells_size csize Nat.add] in NC7. replace (A_INSTANCE + 112 + Z.of_nat 8) with (A_INSTANCE + 120) in NC7 by (clear; lia).
      destruct (Z.eq_dec ncks (0x4000 * r)) as [EQ|NE].
      2:{ (* [comment removed for export] *)
        destruct rest as [|r0 rest']. { exfalso. cbn [length] in LREST. clear - LREST HNC NE; lia. }
        eapply (evtA_aevtS_KJ AL (CSf sc' r) (K sc' r) (largeE_post SP gp tp s10 s11 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra F fc a x ncks PA T lo ps rest' m7) Q _ _ (KL sc' r) HK6); [exact HJ6| |].
        { eapply evtA_cut.
          { eapply (large_E0 AL IMG ALWF (CSf sc' r) (CSOKf sc' r)); [clear - HNC HNR HR; lia| clear - HNC HNR HR; lia| exact NE| exact MI7]. }
          cbv beta. intros ms10 ->.
          eapply (large_E2 AL IMG ALWF (CSf sc' r) (CSOKf sc' r)) with (bsl := bsl7) (st := st7) (g0 := g07) (g1 := g17) (srt := srt) (h3 := Z_to_bv 64 0) (r0 := r0).
          all: lazymatch goal with
               | |- large_statics _ _ => exact (proj1 LS7)
               | |- large_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact FR7
               | |- rw_cells _ _ (_ + 24) _ => exact H37
               | |- u64arr _ _ PA _ => exact HPS7
               | |- u64arr _ _ (PA + _) _ => exact HREST7
               | |- u64arr _ _ _ _ => exact BSL7
               | |- rw_cells _ _ (A_INSTANCE + 120) _ => exact NC7
               | |- rw_cells _ _ (A_INSTANCE + 136) _ => exact STC7
               | |- rw_cells _ _ (A_INSTANCE + 680) _ => exact MX7
               | |- rw_cells _ _ (A_INSTANCE + 704) _ => exact GS7
               | |- stk _ _ _ _ => exact ST7
               | |- mem_inv _ _ => exact MI7
               | |- crange _ _ (_ - _) => exact SCS'
               | |- crange _ _ 32 => eapply crange_sub; [exact CR3| clear; lia| clear - MSZ Hx; lia]
               | |- crange _ _ 8 => eapply crange_sub; [apply CSPA; clear - HR HNC HNR; lia| clear - HNC; lia| clear - HNC NE; lia]
               | |- _ => idtac end.
          all: first [sassumption | cassumption | exact Hx40 | exact AHI | exact AAL | exact ACE | exact PAL | exact LPS | exact K16 | exact LST7 | exact LBSL7 | exact LOIMG | exact SPH | exact SPA
                     | (clear - PA0; lia) | (clear - PA1; lia) | exact SEPA | (clear - HNC HNR HR; lia)
                     | (cbn [length] in LREST; clear - LREST HNC HNR; lia) | (clear - SPL DIE_NEED_ge; lia) ]. }
        cbn beta. intros ms11 mo7 PO HK7 MM7 HJ7. unfold largeE_post in PO.
        ddestruct PO as (v0 & v1 & v2 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m8 & st8 & bsl8 & g08 & g18 & -> & MU8 & WM8 & MI8 & H38 & HPS8 & HREST8 & NC8 & STC8 & LST8 & BSL8 & LBSL8 & MX8 & GS8 & ST8).
        apply (HC true). unfold large_cpostS. deexists 18. split; [reflexivity|]. split; [reflexivity|].
        split; [exact MI8|]. split; [exact ST8|]. split; [exact (wmono_trans _ _ _ _ WM07 WM8)|]. split; [exact (shadow_wr_mono _ _ SHW7 WM8)|].
        assert (IMG8 : img_static_ok [(lo, SP); (a + 24, a + 32); (PA + 8 * ncks, PA + 8 * ncks + 8); (A_INSTANCE + 120, A_INSTANCE + 680 + 4); (A_INSTANCE + 704, A_INSTANCE + 720)]).
        { intros A n H1 H2; cbn; unfold A_INSTANCE in *. split; [left; clear - H1 LOIMG; lia|]. split; [left; clear - H1 AHI; lia|]. split; [left; clear - H1 PA0 HNC; lia|].
          split; [clear - H2; lia|]. split; [clear - H2; lia| exact I]. }
        split. { eapply lstat_transport; [exact LS7| exact MU8| exact IMG8|]. cbn; unfold A_INSTANCE. split; [left; clear - CX1 LOIMG; lia|]. split; [clear - APCTX MSZ Hx; lia|].
                 split; [clear - SEP3 HNC HNR; lia|]. split; [right; clear - CX0; lia|]. split; [right; clear - CX0; lia| exact I]. }
        exists a, r, rest'.
        split; [reflexivity|]. split; [exact HK7|]. split; [exact HJ7|]. split; [left; reflexivity|]. split; [clear - HNC NE; lia|].
        split; [exact AHI|]. split; [exact AAL|]. split; [exact ACE|]. split; [exact ABAND|]. split; [exact SEPA|]. split; [exact CR3|]. split; [exact APCS|].
        split. { eapply munch_trans. { eapply munch_weaken; [| exact MU07]. unfold A_INSTANCE; unfold sub_fp; cbn [outside]; rewrite E8, E8b; clear - DA8 DX8 DM8 MSZ Hx; intros; lia. }
                 eapply munch_weaken; [| exact MU8]. unfold A_INSTANCE; unfold sub_fp; cbn [outside]; clear - HNC NE MSZ Hx; intros; lia. }
        pose proof APPA as APPA'.
        split. { change [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 (map_size x)); C8 (Z_to_bv 64 x); C8 (Z_to_bv 64 ncks)] with ([C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 (map_size x)); C8 (Z_to_bv 64 x)] ++ [C8 (Z_to_bv 64 ncks)]).
                 apply rw_cells_app. split; [| cbn [cells_size csize Nat.add]; replace (a + Z.of_nat 24) with (a + 24) by (clear; lia); exact H38].
                 eapply rw_cells_transport; [exact HDR7| exact MU8| exact WM8|]. cbn; unfold A_INSTANCE.
                 split; [left; clear - ACE LOIMG MSZ Hx; lia|]. split; [left; clear; lia|]. split; [clear - APPA' HNC NE MSZ Hx; lia|]. split; [right; clear - AHI; lia|]. split; [right; clear - AHI; lia| exact I]. }
        split. { eapply rw_cells_transport; [exact ZB7| exact MU8| exact WM8|]. cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - MSZ Hx; lia); unfold A_INSTANCE.
                 split; [left; clear - ACE LOIMG; lia|]. split; [right; clear; lia|]. split; [clear - APPA' HNC NE MSZ Hx; lia|]. split; [right; clear - AHI; lia|]. split; [right; clear - AHI; lia| exact I]. }
        split. { eapply rw_cells_transport; [exact SHA7| exact MU8| exact WM8|]. cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r; change (Z.of_nat 512) with 512; unfold A_INSTANCE.
                 split; [left; clear - SHTOP LOIMG MSZ Hx AHI DA8 DM8; lia|]. split; [destruct ABAND as [LOW|HIGH]; [right; clear - LOW AHI MSZ Hx; lia| left; clear - HIGH SHTOP MSZ Hx AHI DA8 DM8; lia]|].
                 split; [clear - PA0 HNC HNR SHTOP MSZ Hx AHI DA8 DM8; lia|]. split; [right; clear - AHI; lia|]. split; [right; clear - AHI; lia| exact I]. }
        split. { eapply rw_cells_transport; [exact SHB7| exact MU8| exact WM8|]. cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - MSZ Hx DM8 DX8 E8b; lia); rewrite E8, E8b; unfold A_INSTANCE.
                 split; [left; clear - SHTOP LOIMG MSZ Hx AHI DA8 DM8 DX8 ACE; lia|]. split; [destruct ABAND as [LOW|HIGH]; [right; clear - LOW AHI MSZ Hx DX8 DA8; lia| left; clear - HIGH SHTOP MSZ Hx AHI DA8 DM8 DX8 ACE; lia]|].
                 split; [clear - PA0 HNC HNR SHTOP MSZ Hx AHI DA8 DM8 DX8 ACE; lia|]. split; [right; clear - AHI Hx DA8 DX8; lia|]. split; [right; clear - AHI Hx DA8 DX8; lia| exact I]. }
        split. { eapply rw_cells_transport; [exact TJ7| exact MU8| exact WM8|]. cbn; unfold A_INSTANCE.
                 split; [left; clear - T1 LOIMG; lia|]. split; [clear - APT MSZ Hx; lia|]. split; [clear - SEP1 HNC HNR; lia|]. split; [clear - T0; lia|]. split; [clear - T0; lia| exact I]. }
        split. { split. { change [C8 (Z_to_bv 64 (0x4000 * r)); C8 (Z_to_bv 64 (ncks + 1)); C1 (Z_to_bv 8 0)] with ([C8 (Z_to_bv 64 (0x4000 * r))] ++ [C8 (Z_to_bv 64 (ncks + 1)); C1 (Z_to_bv 8 0)]).
                          apply rw_cells_app. split; [| cbn [cells_size csize Nat.add]; replace (A_INSTANCE + 112 + Z.of_nat 8) with (A_INSTANCE + 120) by (clear; lia); exact NC8].
                          eapply rw_cells_transport; [exact NR7| exact MU8| exact WM8|]. cbn; unfold A_INSTANCE.
                          split; [left; clear - LOIMG; lia|]. split; [left; clear - AHI; lia|]. split; [left; clear - PA0 HNC; lia|]. split; [left; clear; lia|]. split; [left; clear; lia| exact I]. }
                 split; [exists st8; split; [exact STC8| exact LST8]|]. split; [exists bsl8; split; [exact BSL8| exact LBSL8]|]. split; [exact MX8|]. dexists g08, g18; exact GS8. }
        split; [exact HPS8|]. split; [exact HREST8|]. cbn [length] in LREST. clear - LREST; lia.
      }
      (* [comment removed for export] *)
      assert (EU : PA + 8 * ncks = U r) by (unfold U; clear - EQ; lia).
      assert (USL : PA <= U r /\ U r + 0x20000 <= PA + 0x800000) by (unfold U; clear - HR HNR EQ HNC; lia).
      eapply (evtA_aevtS_KJ AL (CSf sc' r) (K sc' r)
                (fun ms' => exists (u0 u1 u2 u3 u4 u5 u6 ua6 : word) (mm : mem) (fr : list byte),
                   ms' = MSsvc (mkR (Z_to_bv 64 0x7d01c) (Z_to_bv 64 (SP + -96 + -96)) gp tp u0 u1 u2
                                    (Z_to_bv 64 ((0x20000 + 4095) / 4096 * 4096)) (Z_to_bv 64 0)
                                    (Z_to_bv 64 (U r)) (Z_to_bv 64 ((0x20000 + 4095) / 4096 * 4096)) (Z_to_bv 64 3) (Z_to_bv 64 0x32)
                                    (Z_to_bv 64 (-1)) (Z_to_bv 64 0) ua6 (Z_to_bv 64 222)
                                    (Z_to_bv 64 (U r)) (Z_to_bv 64 0) (Z_to_bv 64 A_PAGESZ_CELL)
                                    (Z_to_bv 64 a) (Z_to_bv 64 (a + map_size x)) (Z_to_bv 64 (a + 4096 + x)) (Z_to_bv 64 7) (Z_to_bv 64 (a + 4096)) s10 s11 u3 u4 u5 u6)
                               F (Z_to_bv 64 A_MMAP_ECALL) (Z_to_bv 64 222) fc None mm (seg_rom asegs)
                   /\ munch [(lo, SP + -96)] m7 mm /\ wmono asegs m7 mm /\ mem_inv asegs mm
                   /\ rw_cells asegs mm (SP + -96 + -96) [C4 (Z_to_bv 64 0x32); CB 44 fr; C8 (Z_to_bv 64 (a + 4096)); C8 (Z_to_bv 64 (63 - Z.log2 (map_size x))); C8 (Z_to_bv 64 (map_size x));
                                                        C8 (Z_to_bv 64 (A_INSTANCE + 64)); C8 (Z_to_bv 64 (A_INSTANCE + 688)); C8 (Z_to_bv 64 0x4c73c)]
                   /\ stk asegs mm lo (SP + -96 + -96))
                Q _ _ (KL sc' r) HK6); [exact HJ6| |].
      { ddestruct LS7 as (LST7' & _ & _ & (W1 & W2 & W3 & W4 & W5 & _) & _).
        eapply evtA_cut.
        { pattern (Z_to_bv 64 (16384 * r)) at 1. rewrite <- EQ.
          eapply (large_E1 AL IMG ALWF (CSf sc' r) (CSOKf sc' r)) with (PA := PA); [clear - HNC HNR HR; lia| clear - PA0; lia| clear - PA1; lia| exact LST7'| exact MI7]. }
        cbv beta. intros ms10 ->. rewrite EU.
        eapply evtA_mono.
        { eapply (mapordie_pre AL IMG ALWF (CSf sc' r) (CSOKf sc' r)) with (lo := lo); try exact W1; try exact W2; try exact ST7; try exact MI7.
          - unfold U; clear - PA0 PA1 HR HNR; lia.
          - unfold U. clear - PAL HR. pose proof (Z.div_mod PA 4096 ltac:(lia)) as DP. rewrite PAL, Z.add_0_r in DP. replace (PA + 131072 * r) with ((PA / 4096 + 32 * r) * 4096) by lia. apply Z_mod_mult.
          - clear; lia. - clear - LOIMG; lia. - clear - SPL DIE_NEED_ge; lia. - clear - SPH; lia.
          - eapply crange_sub; [exact SCS'| clear; lia| clear - SPL; lia]. }
        cbv beta. intros ms11 HH; exact HH. }
      cbn beta. intros ms12 mo8 PO9 HK8 MM8 HJ8. ddestruct PO9 as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & za6 & m9 & fr9 & E12 & MU9 & WM9 & MI9 & FR9 & ST9). subst ms12.
      cbn [ms_mem MS MSsvc] in HJ8.
      (* [comment removed for export] *)
      assert (LO9 : forall A n, A + n <= lo \/ SP + -96 <= A -> disjoint_from [(lo, SP + -96)] A n) by (intros A n H; cbn; split; [exact H| exact I]).
      assert (LS9 : lstat m9) by (eapply lstat_transport; [exact LS7| exact MU9| intros A n H _; apply LO9; left; clear - H LOIMG; lia| apply LO9; left; clear - CX1 LOIMG; lia]).
      assert (FR79 : large_frame m9 SP j0 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) by (unfold large_frame in FR7 |- *; eapply rw_cells_transport; [exact FR7| exact MU9| exact WM9| apply LO9; right; clear; lia]).
      assert (TJ9 : rw_cells asegs m9 (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned j1 + 1)); C8 (Z_to_bv 64 (bv_unsigned j2 + map_size x))])
        by (eapply rw_cells_transport; [exact TJ7| exact MU9| exact WM9| apply LO9; left; cbn; clear - T1 LOIMG; lia]).
      assert (HDR9 : rw_cells asegs m9 a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 (map_size x)); C8 (Z_to_bv 64 x)])
        by (eapply rw_cells_transport; [exact HDR7| exact MU9| exact WM9| apply LO9; left; cbn; clear - ACE LOIMG MSZ Hx; lia]).
      assert (H39 : rw_cells asegs m9 (a + 24) [C8 (Z_to_bv 64 0)]) by (eapply rw_cells_transport; [exact H37| exact MU9| exact WM9| apply LO9; left; cbn; clear - ACE LOIMG MSZ Hx; lia]).
      assert (ZB9 : rw_cells asegs m9 (a + 32) [CB (Z.to_nat (map_size x - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (map_size x - 32)))]).
      { eapply rw_cells_transport; [exact ZB7| exact MU9| exact WM9| apply LO9; left; cbn; rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - MSZ Hx; lia); clear - ACE LOIMG MSZ Hx; lia]. }
      assert (SHA9 : rw_cells asegs m9 (0x7fff8000 + a / 8) [CB 512%nat (repeat (Z_to_bv 8 0xfa) 512%nat)]).
      { eapply rw_cells_transport; [exact SHA7| exact MU9| exact WM9| apply LO9; left; cbn; clear - SHTOP LOIMG MSZ Hx AHI DA8 DM8; lia]. }
      assert (SHB9 : rw_cells asegs m9 (0x7fff8000 + (a + 4096 + x) / 8) [CB (Z.to_nat ((map_size x - 4096 - x) / 8)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat ((map_size x - 4096 - x) / 8)))]).
      { eapply rw_cells_transport; [exact SHB7| exact MU9| exact WM9| apply LO9; left; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - MSZ Hx DM8 DX8 E8b; lia); rewrite E8, E8b; clear - SHTOP LOIMG MSZ Hx AHI DA8 DM8 DX8 ACE; lia]. }
      assert (LI9 : limg m9 (0x4000 * r) ncks srt 1) by (eapply limg_transport; [exact LI7| exact MU9| exact WM9| apply LO9; left; unfold A_INSTANCE; clear - LOIMG; lia]).
      assert (HPS9 : u64arr asegs m9 PA ps).
      { destruct ps as [|p0 ps']; [eapply u64arr_nil_any; exact HPS7|]. eapply u64arr_transport; [exact HPS7| exact MU9| exact WM9| apply LO9; left; clear - PA1 LOIMG LPS HNC HNR; lia]. }
      pose proof (shadow_wr_mono _ _ SHW7 WM9) as SHW9.
      assert (MU09 : munch [(lo, SP); (a, a + map_size x); (0x7fff8000 + a / 8, 0x7fff8000 + a / 8 + 512); (0x7fff8000 + (a + 4096 + x) / 8, 0x7fff8000 + (a + 4096 + x) / 8 + (map_size x - 4096 - x) / 8);
                           (T + 2872, T + 2888); (A_INSTANCE + 680, A_INSTANCE + 684)] m m9).
      { eapply munch_trans; [exact MU07|]. eapply munch_weaken; [| exact MU9]. unfold sub_fp; cbn [outside]; clear; intros; lia. }
      pose proof (wmono_trans _ _ _ _ WM07 WM9) as WM09.
      clear LS7 FR7 TJ7 HDR7 H37 ZB7 SHA7 SHB7 LI7 HPS7 HREST7 SHW7 MU07 WM07 MU9 WM9 ST7 MI7 MX7 LIa7 STC7 BSL7 GS7 NR7 NC7.
      (* [comment removed for export] *)
      destruct (LEDGER_P sc' r mo8 (HGp _) HK8) as [RFP CASESP].
      assert (Hu : 0 <= U r < 2^64) by (clear - USL PA0 PA1; lia). assert (Hn' : 0 <= 0x20000 < 2^64) by (clear; lia). assert (Hun : U r + 0x20000 <= 2^64) by (clear - USL PA1; lia).
      lazymatch goal with |- aevtS _ _ (mkCfg ?MS1 _) =>
      assert (SUCC : forall mo9, fixrw_outcome 0x32 (U r) 0x20000 mo8 (mkEffect (Z_to_bv 64 (U r)) [] [(Z_to_bv 64 (U r), Z_to_bv 64 0x20000)]) mo9 ->
                     aevtS asegs Q (mkCfg (nret MS1 (mkEffect (Z_to_bv 64 (U r)) [] [(Z_to_bv 64 (U r), Z_to_bv 64 0x20000)])) mo9))
      end.
      { intros mo9 OUT.
        assert (HK9 : K sc' (r + 1) mo9).
        { inversion OUT; subst; [eapply proj1; apply TP_commit; [apply HGp| exact HK8| assumption] | eapply proj1; apply TP_fresh; [apply HGp| exact HK8| assumption]]. }
        assert (HJ9 : J (apply_zeros m9 [(wa (U r), Z_to_bv 64 0x20000)]) mo9).
        { inversion OUT; subst;
            [ apply (J_fixrw_commit m9 mo8 HJ8 (U r) 0x20000); [clear - Hu; lia| clear; lia| clear - USL PA1 AC; lia]
            | apply (J_fixrw_fresh m9 mo8 HJ8 (U r) 0x20000); [clear - Hu; lia| clear; lia| clear - USL PA1 AC; lia| assumption] ]. }
        clear OUT.
        rewrite nret_MSsvc, mkR_set_a0, apply_mem_zeros.
        change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
        change (Z_to_bv 64 (U r), Z_to_bv 64 0x20000) with (wa (U r), Z_to_bv 64 0x20000).
        pose proof (rw_cells_zeros_new asegs m9 (U r) 0x20000 Hu Hn' Hun) as SLz.
        assert (DJu : forall A n, (A + n <= U r \/ U r + 0x20000 <= A) -> disjoint_from [(U r, U r + 0x20000)] A n) by (intros A n H; cbn; split; [exact H| exact I]).
        pose proof (munch_zeros m9 (U r) 0x20000 Hu Hn' Hun [(U r, U r + 0x20000)] m9 (munch_refl _ m9) ltac:(cbn; left; clear; lia)) as MUu.
        pose proof (wmono_zeros asegs m9 (U r) 0x20000 Hu Hn' Hun m9 (wmono_refl asegs m9)) as WMu.
        assert (MIu : mem_inv asegs (apply_zeros m9 [(wa (U r), Z_to_bv 64 0x20000)])).
        { eapply (mem_inv_zeros asegs m9 (U r) 0x20000 Hu Hn' Hun MI9). intros y Hy. destruct (ro_addr asegs y) eqn:E; [| reflexivity]. exfalso. pose proof (asegs_ro_lt y E). clear - H Hy USL PA0; lia. }
        set (mu := apply_zeros m9 [(wa (U r), Z_to_bv 64 0x20000)]) in *.
        (* [comment removed for export] *)
        assert (LSu : lstat mu).
        { eapply lstat_transport; [exact LS9| exact MUu| intros A n H _; apply DJu; left; clear - H USL PA0; lia| apply DJu; clear - USL SEP3 CX0; lia]. }
        assert (FR9u : rw_cells asegs mu (SP + -96 + -96) [C4 (Z_to_bv 64 0x32); CB 44 fr9; C8 (Z_to_bv 64 (a + 4096)); C8 (Z_to_bv 64 (63 - Z.log2 (map_size x))); C8 (Z_to_bv 64 (map_size x)); C8 (Z_to_bv 64 (A_INSTANCE + 64)); C8 (Z_to_bv 64 (A_INSTANCE + 688)); C8 (Z_to_bv 64 0x4c73c)]).
        { eapply rw_cells_transport; [exact FR9| exact MUu| exact WMu| apply DJu; right; cbn; clear - USL PA1 LOIMG SPL DIE_NEED_ge; lia]. }
        assert (FR7u : large_frame mu SP j0 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra).
        { unfold large_frame in FR79 |- *. eapply rw_cells_transport; [exact FR79| exact MUu| exact WMu| apply DJu; right; cbn; clear - USL PA1 LOIMG SPL DIE_NEED_ge; lia]. }
        pose proof (stk_zeros asegs m9 (U r) 0x20000 Hu Hn' Hun _ _ ST9) as STu. fold mu in STu.
        assert (TJu : rw_cells asegs mu (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned j1 + 1)); C8 (Z_to_bv 64 (bv_unsigned j2 + map_size x))])
          by (eapply rw_cells_transport; [exact TJ9| exact MUu| exact WMu| apply DJu; cbn; clear - USL SEP1; lia]).
        assert (HDRu : rw_cells asegs mu a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 (map_size x)); C8 (Z_to_bv 64 x)])
          by (eapply rw_cells_transport; [exact HDR9| exact MUu| exact WMu| apply DJu; cbn; clear - USL SEPA MSZ Hx; lia]).
        assert (H3u : rw_cells asegs mu (a + 24) [C8 (Z_to_bv 64 0)]) by (eapply rw_cells_transport; [exact H39| exact MUu| exact WMu| apply DJu; cbn; clear - USL SEPA MSZ Hx; lia]).
        assert (ZBu : rw_cells asegs mu (a + 32) [CB (Z.to_nat (map_size x - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (map_size x - 32)))]).
        { eapply rw_cells_transport; [exact ZB9| exact MUu| exact WMu| apply DJu; cbn; rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - MSZ Hx; lia); clear - USL SEPA MSZ Hx; lia]. }
        assert (SHAu : rw_cells asegs mu (0x7fff8000 + a / 8) [CB 512%nat (repeat (Z_to_bv 8 0xfa) 512%nat)]).
        { eapply rw_cells_transport; [exact SHA9| exact MUu| exact WMu| apply DJu; cbn; clear - SHTOP USL PA0 MSZ Hx AHI DA8 DM8; lia]. }
        assert (SHBu : rw_cells asegs mu (0x7fff8000 + (a + 4096 + x) / 8) [CB (Z.to_nat ((map_size x - 4096 - x) / 8)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat ((map_size x - 4096 - x) / 8)))]).
        { eapply rw_cells_transport; [exact SHB9| exact MUu| exact WMu| apply DJu; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - MSZ Hx DM8 DX8 E8b; lia); rewrite E8, E8b; clear - SHTOP USL PA0 MSZ Hx AHI DA8 DM8 DX8 ACE; lia]. }
        assert (LIu : limg mu (0x4000 * r) ncks srt 1) by (eapply limg_transport; [exact LI9| exact MUu| exact WMu| apply DJu; left; unfold A_INSTANCE; clear - USL PA0; lia]).
        assert (HPSu : u64arr asegs mu PA ps).
        { destruct ps as [|p0 ps']; [eapply u64arr_nil_any; exact HPS9|]. eapply u64arr_transport; [exact HPS9| exact MUu| exact WMu| apply DJu; left; unfold U; clear - LPS EQ; lia]. }
        assert (SLu : u64arr asegs mu (PA + 8 * ncks) (repeat (Z_to_bv 64 0) (Z.to_nat 0x4000))).
        { rewrite EU. apply u64arr_zeros; [clear; lia|]. exact SLz. }
        pose proof (shadow_wr_mono _ _ SHW9 WMu) as SHWu.
        assert (MU0u : munch [(lo, SP); (a, a + map_size x); (0x7fff8000 + a / 8, 0x7fff8000 + a / 8 + 512); (0x7fff8000 + (a + 4096 + x) / 8, 0x7fff8000 + (a + 4096 + x) / 8 + (map_size x - 4096 - x) / 8);
                             (T + 2872, T + 2888); (A_INSTANCE + 680, A_INSTANCE + 684); (U r, U r + 0x20000)] m mu).
        { eapply munch_trans. { eapply munch_weaken; [| exact MU09]. unfold sub_fp; cbn [outside]; clear; intros; lia. }
          eapply munch_weaken; [| exact MUu]. unfold sub_fp; cbn [outside]; clear; intros; lia. }
        pose proof (wmono_trans _ _ _ _ WM09 WMu) as WM0u.
        clearbody mu. clear LS9 FR9 FR79 ST9 TJ9 HDR9 H39 ZB9 SHA9 SHB9 LI9 HPS9 SHW9 MUu WMu MI9 SLz.
        assert (SCS1 : crange (CSf sc' (r + 1)) lo (SP - lo)) by (eapply crange_imp; [| exact SCS']; intros y Hy; apply CSmono_p; exact Hy).
        assert (CR1 : crange (CSf sc' (r + 1)) a (map_size x)) by (eapply crange_imp; [| exact CR3]; intros y Hy; apply CSmono_p; exact Hy).
        (* [comment removed for export] *)
        destruct (limg_parts _ _ _ _ _ LIu) as (LIau & (stu & STCu & LSTu) & (bslu & BSLu & LBSLu) & MXu & (g0u & g1u & GSu)).
        eapply (evtA_aevtS_KJ AL (CSf sc' (r + 1)) (K sc' (r + 1))
                  (fun ms' => exists (v0 v1 v2 va1 va2 va3 va4 va5 va6 va7 v3 v4 v5 v6 : word) (m' : mem) (st : list word) (bsl' : list word) (g0' g1' : word),
                     ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp v0 v1 v2 s0 s1 (Z_to_bv 64 (a + 4096)) va1 va2 va3 va4 va5 va6 va7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6)
                              F (ret_pc ra) fc None m' (seg_rom asegs)
                     /\ munch [(lo, SP); (a + 24, a + 32); (PA + 8 * ncks, PA + 8 * ncks + 8); (A_INSTANCE + 112, A_INSTANCE + 680 + 4); (A_INSTANCE + 704, A_INSTANCE + 720)] mu m'
                     /\ wmono asegs mu m' /\ mem_inv asegs m'
                     /\ rw_cells asegs m' (a + 24) [C8 (Z_to_bv 64 ncks)]
                     /\ u64arr asegs m' PA (ps ++ [Z_to_bv 64 a]) /\ u64arr asegs m' (PA + 8 * (ncks + 1)) (repeat (Z_to_bv 64 0) (Z.to_nat (0x4000 - 1)))
                     /\ rw_cells asegs m' (A_INSTANCE + 112) [C8 (Z_to_bv 64 (0x4000 * r + 0x4000)); C8 (Z_to_bv 64 (ncks + 1)); C1 (Z_to_bv 8 0)]
                     /\ rw_cells asegs m' (A_INSTANCE + 136) (List.map C8 st) /\ length st = 4%nat
                     /\ u64arr asegs m' (A_INSTANCE + 168) bsl' /\ length bsl' = 64%nat
                     /\ rw_cells asegs m' (A_INSTANCE + 680) [C4 (Z_to_bv 64 0)]
                     /\ rw_cells asegs m' (A_INSTANCE + 704) [C8 g0'; C8 g1']
                     /\ stk asegs m' lo SP)
                  Q _ _ (KL sc' (r + 1)) HK9); [exact HJ9| |].
        { dpose LSu as (LSTu' & _ & _ & (W1 & W2 & W3 & W4 & W5 & _) & _).
          eapply evtA_cut.
          { eapply (mapordie_post_ok AL IMG ALWF (CSf sc' (r + 1)) (CSOKf sc' (r + 1))) with (m0 := mu) (lo := lo); try exact FR9u; try exact W3; try exact W5; try exact STu; try exact MIu.
            - clear - USL PA0 PA1; lia. - clear; lia. - clear - LOIMG; lia. - clear - SPL DIE_NEED_ge; lia. - clear - SPH; lia.
            - apply munch_refl. - apply wmono_refl. - eapply crange_sub; [exact SCS1| clear; lia| clear - SPL; lia]. }
          cbv beta. (intros ms13 dd_H; ddestruct dd_H as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m10 & -> & MU10 & WM10 & MI10 & ST10)).
          replace (ret_pc (Z_to_bv 64 0x4c73c)) with (Z_to_bv 64 0x4c73c) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
          replace (SP + -96 + -96 + 96) with (SP + -96) in ST10 by (clear; lia).
          assert (LO10 : forall A n, A + n <= lo \/ SP + -96 <= A -> disjoint_from [(lo, SP + -96)] A n) by (intros A n H; cbn; split; [exact H| exact I]).
          assert (LIau' : rw_cells asegs m10 (A_INSTANCE + 112) [C8 (Z_to_bv 64 (0x4000 * r)); C8 (Z_to_bv 64 ncks); C1 srt]).
          { eapply rw_cells_transport; [exact LIau| exact MU10| exact WM10| apply LO10; left; unfold A_INSTANCE; cbn; clear - LOIMG; lia]. }
          (* [comment removed for export] *)
          eapply evtA_cut.
          { eapply (large_E1b AL IMG ALWF (CSf sc' (r + 1)) (CSOKf sc' (r + 1))) with (m0 := m10) (W := []) (ncks := ncks) (nres := 0x4000 * r); [clear - HNC HNR HR; lia| clear - HR; lia| clear - HNR; lia| exact LIau'| apply munch_refl| apply wmono_refl| exact MI10]. }
          cbv beta. (intros ms14 dd_H; ddestruct dd_H as (m11 & -> & MU11 & WM11 & MI11 & NR11)).
          (* [comment removed for export] *)
          pose proof NR11 as NC11. change [C8 (Z_to_bv 64 (16384 * r + 16384)); C8 (Z_to_bv 64 ncks); C1 srt] with ([C8 (Z_to_bv 64 (16384 * r + 16384))] ++ [C8 (Z_to_bv 64 ncks); C1 srt]) in NC11.
          apply rw_cells_app in NC11 as [NR11' NC11]. cbn [cells_size csize Nat.add] in NC11. replace (A_INSTANCE + 112 + Z.of_nat 8) with (A_INSTANCE + 120) in NC11 by (clear; lia).
          assert (MU1011 : munch [(lo, SP + -96); (A_INSTANCE + 112, A_INSTANCE + 120)] mu m11).
          { eapply munch_trans. { eapply munch_weaken; [| exact MU10]. unfold sub_fp; cbn [outside]; clear; intros; lia. }
            eapply munch_weaken; [| exact MU11]. unfold sub_fp; cbn [outside]; clear; intros; lia. }
          pose proof (wmono_trans _ _ _ _ WM10 WM11) as WM1011.
          assert (LO11 : forall A n, A + n <= lo \/ SP + -96 <= A -> (A + n <= A_INSTANCE + 112 \/ A_INSTANCE + 120 <= A) -> disjoint_from [(lo, SP + -96); (A_INSTANCE + 112, A_INSTANCE + 120)] A n).
          { intros A n H1 H2; cbn; split; [exact H1| split; [exact H2| exact I]]. }
          ddestruct LSu as (_ & TSu & PSu & MWu & DSu). destruct stu as [|su0 [|su1 [|su2 [|su3 [|]]]]]; try discriminate LSTu.
          eapply evtA_mono.
          { eapply (large_E2 AL IMG ALWF (CSf sc' (r + 1)) (CSOKf sc' (r + 1))) with (m := m11) (bsl := bslu) (st := [su0; su1; su2; su3]) (g0 := g0u) (g1 := g1u) (srt := srt) (h3 := Z_to_bv 64 0)
                     (r0 := Z_to_bv 64 0) (rest := repeat (Z_to_bv 64 0) (Z.to_nat (0x4000 - 1))) (ps := ps) (k := Z.log2 (map_size x)) (PA := PA) (T := T) (lo := lo).
            all: lazymatch goal with
                 | |- large_statics _ _ => eapply large_statics_transport; [exact LSTu'| exact MU1011| | |]; apply LO11; unfold A_INSTANCE, A_GOT_LNAME, A_LNAME_CELL; cbn; clear - LOIMG; lia
                 | |- large_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold large_frame in FR7u |- *; eapply rw_cells_transport; [exact FR7u| exact MU1011| exact WM1011| apply LO11; cbn; unfold A_INSTANCE; clear - LOIMG SPL DIE_NEED_ge; lia]
                 | |- rw_cells _ _ (_ + 24) _ => eapply rw_cells_transport; [exact H3u| exact MU1011| exact WM1011| apply LO11; cbn; unfold A_INSTANCE; clear - ACE LOIMG MSZ Hx AHI; lia]
                 | |- u64arr _ _ PA _ => destruct ps as [|p0 ps']; [eapply u64arr_nil_any; exact HPSu| eapply u64arr_transport; [exact HPSu| exact MU1011| exact WM1011| apply LO11; unfold A_INSTANCE; clear - PA0 PA1 LOIMG LPS HNC HNR; lia]]
                 | |- u64arr _ _ (PA + _) _ => change (Z_to_bv 64 0 :: repeat (Z_to_bv 64 0) (Z.to_nat (16384 - 1))) with (repeat (Z_to_bv 64 0) (Z.to_nat 16384));
                                               eapply u64arr_transport; [exact SLu| exact MU1011| exact WM1011| apply LO11; rewrite repeat_length; unfold A_INSTANCE; clear - PA0 PA1 LOIMG EQ USL EU; lia]
                 | |- u64arr _ _ _ _ => eapply u64arr_transport; [exact BSLu| exact MU1011| exact WM1011| apply LO11; rewrite LBSLu; unfold A_INSTANCE; clear - LOIMG; lia]
                 | |- rw_cells _ _ (A_INSTANCE + 120) _ => exact NC11
                 | |- rw_cells _ _ (A_INSTANCE + 136) _ => eapply rw_cells_transport; [exact STCu| exact MU1011| exact WM1011| apply LO11; cbn; unfold A_INSTANCE; clear - LOIMG; lia]
                 | |- rw_cells _ _ (A_INSTANCE + 680) _ => eapply rw_cells_transport; [exact MXu| exact MU1011| exact WM1011| apply LO11; cbn; unfold A_INSTANCE; clear - LOIMG; lia]
                 | |- rw_cells _ _ (A_INSTANCE + 704) _ => eapply rw_cells_transport; [exact GSu| exact MU1011| exact WM1011| apply LO11; cbn; unfold A_INSTANCE; clear - LOIMG; lia]
                 | |- stk _ _ _ _ => eapply stk_transport_disjoint; [exact ST10| exact MU11| exact WM11| cbn; unfold A_INSTANCE; split; [right; clear - LOIMG; lia| exact I]]
                 | |- mem_inv _ _ => exact MI11
                 | |- crange _ _ (_ - _) => exact SCS1
                 | |- crange _ _ 32 => eapply crange_sub; [exact CR1| clear; lia| clear - MSZ Hx; lia]
                 | |- crange _ _ 8 => eapply crange_sub; [apply CSPA; clear - HR HNC HNR EQ; lia| clear - HNC; lia| clear - HNC HNR EQ; lia]
                 | |- _ => idtac end.
            all: first [sassumption | cassumption | exact Hx40 | exact AHI | exact AAL | exact ACE | exact PAL | exact LPS | exact K16 | exact LSTu | exact LBSLu | exact LOIMG | exact SPH | exact SPA | exact SEPA
                       | (clear - PA0; lia) | (clear - PA1; lia) | (clear - HNC HNR HR; lia)
                       | (rewrite repeat_length; clear - HNC HNR EQ; lia) | (clear; reflexivity) | (clear - SPL DIE_NEED_ge; lia) ]. }
          cbv beta. intros ms15 PO. unfold largeE_post in PO.
          ddestruct PO as (v0 & v1 & v2 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m12 & st12 & bsl12 & g012 & g112 & -> & MU13 & WM13' & MI12 & H312 & HPS12 & HREST12 & NC12 & STC12 & LST12 & BSL12 & LBSL12 & MX12 & GS12 & ST12).
          deexists 19. split; [reflexivity|].
          split. { eapply munch_trans. { eapply munch_weaken; [| exact MU1011]. unfold A_INSTANCE; unfold sub_fp; cbn [outside]; clear; intros; lia. }
                   eapply munch_weaken; [| exact MU13]. unfold A_INSTANCE; unfold sub_fp; cbn [outside]; clear; intros; lia. }
          split; [exact (wmono_trans _ _ _ _ WM1011 WM13')|]. split; [exact MI12|]. split; [exact H312|]. split; [exact HPS12|]. split; [exact HREST12|].
          split. { change [C8 (Z_to_bv 64 (16384 * r + 16384)); C8 (Z_to_bv 64 (ncks + 1)); C1 (Z_to_bv 8 0)] with ([C8 (Z_to_bv 64 (16384 * r + 16384))] ++ [C8 (Z_to_bv 64 (ncks + 1)); C1 (Z_to_bv 8 0)]).
                   apply rw_cells_app. split; [| cbn [cells_size csize Nat.add]; replace (A_INSTANCE + 112 + Z.of_nat 8) with (A_INSTANCE + 120) by (clear; lia); exact NC12].
                   eapply rw_cells_transport; [exact NR11'| exact MU13| exact WM13'|]. cbn; unfold A_INSTANCE.
                   split; [left; clear - LOIMG; lia|]. split; [left; clear - AHI; lia|]. split; [left; clear - PA0 HNC; lia|]. split; [left; clear; lia|]. split; [left; clear; lia| exact I]. }
          split; [exact STC12|]. split; [exact LST12|]. split; [exact BSL12|]. split; [exact LBSL12|]. split; [exact MX12|]. split; [exact GS12| exact ST12]. }
        (* [comment removed for export] *)
        cbn beta. (intros ms16 mo10 dd_H; ddestruct dd_H as (v0 & v1 & v2 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m12 & st12 & bsl12 & g012 & g112 & -> & MU13 & WM13 & MI12 & H312 & HPS12 & HREST12 & NRC12 & STC12 & LST12 & BSL12 & LBSL12 & MX12 & GS12 & ST12); intros HK10 MM10 HJ10).
        apply (HC true). unfold large_cpostS. deexists 18. split; [reflexivity|]. split; [reflexivity|].
        split; [exact MI12|]. split; [exact ST12|]. split; [exact (wmono_trans _ _ _ _ WM0u WM13)|]. split; [exact (shadow_wr_mono _ _ SHWu WM13)|].
        assert (IMG12 : img_static_ok [(lo, SP); (a + 24, a + 32); (PA + 8 * ncks, PA + 8 * ncks + 8); (A_INSTANCE + 112, A_INSTANCE + 680 + 4); (A_INSTANCE + 704, A_INSTANCE + 720)]).
        { intros A n H1 H2; cbn; unfold A_INSTANCE in *. split; [left; clear - H1 LOIMG; lia|]. split; [left; clear - H1 AHI; lia|]. split; [left; clear - H1 PA0 HNC; lia|].
          split; [clear - H2; lia|]. split; [clear - H2; lia| exact I]. }
        split. { eapply lstat_transport; [exact LSu| exact MU13| exact IMG12|]. cbn; unfold A_INSTANCE. split; [left; clear - CX1 LOIMG; lia|]. split; [clear - APCTX MSZ Hx; lia|].
                 split; [clear - SEP3 HNC HNR; lia|]. split; [right; clear - CX0; lia|]. split; [right; clear - CX0; lia| exact I]. }
        exists a, (r + 1), (repeat (Z_to_bv 64 0) (Z.to_nat (0x4000 - 1))).
        split; [reflexivity|]. split; [exact HK10|]. split; [exact HJ10|]. split; [right; split; [reflexivity| exact EQ]|]. split; [clear - HNC HNR EQ; lia|].
        split; [exact AHI|]. split; [exact AAL|]. split; [exact ACE|]. split; [exact ABAND|]. split; [exact SEPA|]. split; [exact CR1|]. split; [exact APCS|].
        split. { eapply munch_trans. { eapply munch_weaken; [| exact MU0u]. unfold U, A_INSTANCE; unfold sub_fp; cbn [outside]; rewrite E8, E8b; clear - EQ DA8 DX8 DM8 MSZ Hx; intros; lia. }
                 eapply munch_weaken; [| exact MU13]. unfold A_INSTANCE; unfold sub_fp; cbn [outside]; clear - HNC EQ MSZ Hx; intros; lia. }
        split. { change [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 (map_size x)); C8 (Z_to_bv 64 x); C8 (Z_to_bv 64 ncks)] with ([C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 (map_size x)); C8 (Z_to_bv 64 x)] ++ [C8 (Z_to_bv 64 ncks)]).
                 apply rw_cells_app. split; [| cbn [cells_size csize Nat.add]; replace (a + Z.of_nat 24) with (a + 24) by (clear; lia); exact H312].
                 eapply rw_cells_transport; [exact HDRu| exact MU13| exact WM13|]. cbn; unfold A_INSTANCE.
                 split; [left; clear - ACE LOIMG MSZ Hx; lia|]. split; [left; clear; lia|]. split; [clear - SEPA EQ HNC HNR MSZ Hx; lia|]. split; [right; clear - AHI; lia|]. split; [right; clear - AHI; lia| exact I]. }
        split. { eapply rw_cells_transport; [exact ZBu| exact MU13| exact WM13|]. cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - MSZ Hx; lia); unfold A_INSTANCE.
                 split; [left; clear - ACE LOIMG; lia|]. split; [right; clear; lia|]. split; [clear - SEPA EQ HNC HNR MSZ Hx; lia|]. split; [right; clear - AHI; lia|]. split; [right; clear - AHI; lia| exact I]. }
        split. { eapply rw_cells_transport; [exact SHAu| exact MU13| exact WM13|]. cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r; change (Z.of_nat 512) with 512; unfold A_INSTANCE.
                 split; [left; clear - SHTOP LOIMG MSZ Hx AHI DA8 DM8; lia|]. split; [destruct ABAND as [LOW|HIGH]; [right; clear - LOW AHI MSZ Hx; lia| left; clear - HIGH SHTOP MSZ Hx AHI DA8 DM8; lia]|].
                 split; [clear - PA0 HNC HNR SHTOP MSZ Hx AHI DA8 DM8; lia|]. split; [right; clear - AHI; lia|]. split; [right; clear - AHI; lia| exact I]. }
        split. { eapply rw_cells_transport; [exact SHBu| exact MU13| exact WM13|]. cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - MSZ Hx DM8 DX8 E8b; lia); rewrite E8, E8b; unfold A_INSTANCE.
                 split; [left; clear - SHTOP LOIMG MSZ Hx AHI DA8 DM8 DX8 ACE; lia|]. split; [destruct ABAND as [LOW|HIGH]; [right; clear - LOW AHI MSZ Hx DX8 DA8; lia| left; clear - HIGH SHTOP MSZ Hx AHI DA8 DM8 DX8 ACE; lia]|].
                 split; [clear - PA0 HNC HNR SHTOP MSZ Hx AHI DA8 DM8 DX8 ACE; lia|]. split; [right; clear - AHI Hx DA8 DX8; lia|]. split; [right; clear - AHI Hx DA8 DX8; lia| exact I]. }
        split. { eapply rw_cells_transport; [exact TJu| exact MU13| exact WM13|]. cbn; unfold A_INSTANCE.
                 split; [left; clear - T1 LOIMG; lia|]. split; [clear - APT MSZ Hx; lia|]. split; [clear - SEP1 HNC HNR; lia|]. split; [clear - T0; lia|]. split; [clear - T0; lia| exact I]. }
        split. { split; [replace (16384 * (r + 1)) with (16384 * r + 16384) by (clear; lia); exact NRC12|].
                 split; [exists st12; split; [exact STC12| exact LST12]|]. split; [exists bsl12; split; [exact BSL12| exact LBSL12]|]. split; [exact MX12|]. dexists g012, g112; exact GS12. }
        split; [exact HPS12|]. split; [exact HREST12|]. rewrite repeat_length. clear - EQ; lia. }
      eapply (aevtS_mmap_fixrw asegs Q) with (addr := U r) (nZ := 0x20000) (flags := 0x32).
      { exact (ki_halted (KL sc' r) mo8 HK8). }
      { exact (ki_top (KL sc' r) mo8 HK8). }
      { unfold mmap_fixrw_args, areg, MSsvc. cbn [ms_regs]. simp_regs.
        pose proof aceil_bounds as AC2.
        repeat split; try reflexivity.
        - intros E. apply (f_equal bv_unsigned) in E. change ((131072 + 4095) / 4096 * 4096) with 131072 in E. rewrite !unsigned_lit in E by (clear; lia). clear - E; lia.
        - unfold U. clear - PAL HR. pose proof (Z.div_mod PA 4096 ltac:(lia)) as DP. rewrite PAL, Z.add_0_r in DP. replace (PA + 131072 * r) with ((PA / 4096 + 32 * r) * 4096) by lia. apply Z_mod_mult.
        - clear - USL PA0; lia. - clear - USL PA1; lia.
        - left. reflexivity. }
      { exact RFP. } { exact CASESP. } { apply (ROOM_P sc' r mo8 (HGp _) HK8). }
      { exact SUCC. }
      intros eff mo9 OUT. destruct OUT as [e HIn | e HIn MC | MC | FRE].
      + (* [comment removed for export] *)
        right. destruct HIn as [<-|[]].
        rewrite nret_MSsvc, mkR_set_a0, apply_mem_none.
        replace (errno_ret ENOMEM) with (Z_to_bv 64 (2^64 - 12)) by (apply bv_eq; vm_compute; reflexivity).
        change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
        ddestruct LS9 as (_ & _ & _ & _ & DS9).
        eapply (evtA_spinJ_K asegs AL (CSf sc' r) (K sc' r) _ _ mo8 (KL sc' r) HK8).
        { eapply (MOD_DIE (CSf sc' r)) with (m0 := m9) (lo := lo); try exact (CSOKf sc' r); try exact FR9; try exact DS9; try exact ST9; try exact MI9.
          - clear - USL PA0 PA1; lia. - clear; lia. - clear - LOIMG; lia. - clear - SPL; lia. - clear - SPH; lia.
          - apply munch_refl. - apply wmono_refl. - eapply crange_sub; [exact SCS'| clear; lia| clear - SPL; lia]. }
        cbn beta. (intros ms17 mo11 dd_H; ddestruct dd_H as (rr & FF & mm' & ->); intros HK11 _). apply spinningJ_at; [cbn; right; right; right; left; reflexivity| exact (ki_halted (KL sc' r) _ HK11)].
      + (* [comment removed for export] *)
        right. destruct HIn as [<-|[]].
        rewrite nret_MSsvc, mkR_set_a0, apply_mem_unmaps.
        replace (errno_ret ENOMEM) with (Z_to_bv 64 (2^64 - 12)) by (apply bv_eq; vm_compute; reflexivity).
        change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
        change (Z_to_bv 64 (U r), Z_to_bv 64 0x20000) with (wa (U r), Z_to_bv 64 0x20000).
        destruct (SCAR_P sc' r (HGp _)) as (Kh & KhL & TD).
        ddestruct LS9 as (_ & _ & _ & _ & DS9).
        pose proof (rw_cells_unmaps_other asegs m9 (U r) 0x20000 Hu Hn' Hun _ _ FR9 ltac:(right; clear - USL PA1 LOIMG SPL DIE_NEED_ge; lia)) as FR9u.
        pose proof (stk_unmaps_other asegs m9 (U r) 0x20000 Hu Hn' Hun _ _ ST9 ltac:(right; clear - USL PA1 LOIMG SPL DIE_NEED_ge; lia)) as ST9u.
        pose proof (mem_inv_unmaps asegs m9 (U r) 0x20000 Hu Hn' Hun MI9) as MI9u.
        assert (DS9u : die_statics (apply_unmaps m9 [(wa (U r), Z_to_bv 64 0x20000)])).
        { eapply die_statics_transport; [exact DS9| eapply (munch_unmaps m9 (U r) 0x20000 Hu Hn' Hun [(U r, U r + 0x20000)]); [apply munch_refl| cbn; left; clear; lia]|].
          intros A n H _. cbn [disjoint_from]. split; [left; clear - H USL PA0; lia| exact I]. }
        set (mu := apply_unmaps m9 [(wa (U r), Z_to_bv 64 0x20000)]) in *. clearbody mu.
        eapply (evtA_spinJ_K asegs AL (CSf sc' r) Kh _ _ _ KhL (TD mo8 HK8 MC)).
        { eapply (MOD_DIE (CSf sc' r)) with (m0 := mu) (lo := lo); try exact (CSOKf sc' r); try exact FR9u; try exact DS9u; try exact ST9u; try exact MI9u.
          - clear - USL PA0 PA1; lia. - clear; lia. - clear - LOIMG; lia. - clear - SPL; lia. - clear - SPH; lia.
          - apply munch_refl. - apply wmono_refl. - eapply crange_sub; [exact SCS'| clear; lia| clear - SPL; lia]. }
        cbn beta. (intros ms17 mo11 dd_H; ddestruct dd_H as (rr & FF & mm' & ->); intros HK11 _). apply spinningJ_at; [cbn; right; right; right; left; reflexivity| exact (ki_halted KhL _ HK11)].
      + left. apply SUCC. apply FO_commit. exact MC.
      + left. apply SUCC. apply FO_fresh. exact FRE.
  Qed.

  (* [comment removed for export] *)
  Definition combsec_cpostS (ok : bool) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra : word) (F : bvmap 5 word) (fc : bv 32)
      (sc : list (Z * Z)) (r x ncks lo : Z) (j1 j2 : word) (ps : list word) (m0 : mem) : config -> Prop :=
    fun cf => exists ms' mo' (res : Z) (t0 t1 t2 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem),
      let ms := map_size x in
      cf = mkCfg ms' mo'
      /\ ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) (Z_to_bv 64 9) a2 (Z_to_bv 64 8) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None mm (seg_rom asegs)
      /\ mem_inv asegs mm /\ stk asegs mm lo SP /\ wmono asegs m0 mm /\ shadow_wr mm /\ lstat mm
      /\ if ok then
           exists (a r' : Z) (rest' : list word),
             res = a + 4096 /\ K (sc ++ [(a, ms)]) r' mo' /\ J mm mo' /\ (r' = r \/ (r' = r + 1 /\ ncks = 0x4000 * r)) /\ ncks + 1 <= 0x4000 * r'
             /\ 0x65f000 <= a /\ a mod 4096 = 0 /\ a + ms <= ACEIL /\ (a + ms <= 0x7fff7000 \/ 0x10007fff8000 <= a)
             /\ (a + ms <= PA \/ PA + 0x800000 <= a)
             /\ crange (CSf (sc ++ [(a, ms)]) r') a ms /\ (forall y, CSf sc r y -> ~ (a <= y < a + ms))
             /\ munch [(lo, SP); (a, a + ms); (0x7fff8000 + a / 8, 0x7fff8000 + a / 8 + ms / 8); (T + 2872, T + 2888);
                       (A_INSTANCE + 112, A_INSTANCE + 720); (PA + 8 * ncks, PA + 8 * (0x4000 * r'))] m0 mm
             /\ rw_cells asegs mm a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 x); C8 (Z_to_bv 64 ncks)]
             /\ rw_cells asegs mm (a + 32) [CB (Z.to_nat (ms - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (ms - 32)))]
             /\ rw_cells asegs mm (0x7fff8000 + a / 8) [CB 512%nat (repeat (Z_to_bv 8 0xfa) 512%nat)]
             /\ rw_cells asegs mm (0x7fff8000 + (a + 4096 + x) / 8) [CB (Z.to_nat ((ms - 4096 - x) / 8)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat ((ms - 4096 - x) / 8)))]
             /\ rw_cells asegs mm (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned j1 + 1)); C8 (Z_to_bv 64 (bv_unsigned j2 + ms))]
             /\ limg mm (0x4000 * r') (ncks + 1) (Z_to_bv 8 0) 0
             /\ u64arr asegs mm PA (ps ++ [Z_to_bv 64 a]) /\ u64arr asegs mm (PA + 8 * (ncks + 1)) rest' /\ Z.of_nat (length rest') = 0x4000 * r' - ncks - 1
         else
           res = 0 /\ K sc r mo' /\ J mm mo' /\ munch [(lo, SP)] m0 mm
           /\ rw_cells asegs mm (T + 2872) [C8 j1; C8 j2].

  #[using="AL IMG ALWF ASB CSOKf KL CSmono_l CSmono_p U GPA GT GCTX GSEP CST CSCTX CSPA K_apart T_large LEDGER_P TP_commit TP_fresh ROOM_P SCAR_P die_statics_transport DIE_NEED_ge MOD_DIE"] Lemma combined_sec_cfgS : ltac2:(CDefT.buildp (gd_tbl_AW_LargeCfgS ()) "PQ,P,$52.SpPra,(>.&40.)Pgp,(>.&40.)Ptp,(>.&40.)Pt0,(>.&40.)Pt1,(>.&40.)Pt2,(>.&40.)Ps0,(>.&40.)Ps1,(>.&40.)Pa1,(>.&40.)Pa4,(>.&40.)Pa5,(>.&40.)Pa6,(>.&40.)Pa7,(>.&40.)Ps2,(>.&40.)Ps3,(>.&40.)Ps4,(>.&40.)Ps5,(>.&40.)Ps6,(>.&40.)Ps7,(>.&40.)Ps8,(>.&40.)Ps9,(>.&40.)Ps10,(>.&40.)Ps11,(>.&40.)Pt3,(>.&40.)Pt4,(>.&40.)Pt5,(>.&40.)Pt6,(>.&40.)Pj1,(>.&40.)Pj2,(>.&40.)Psrt,(>.&8.)Pps,(0.(>.&40.))Prest,(0.(>.&40.))Psc,(0.(20.$2.$2.))PSP,$2.PF,(37.&5.(>.&40.))Pfc,(>.&20.)Pm,P,(>.&40.)(;.(>.&8.))Pmo,$21.Pr,$2.Px,$2.Pncks,$2.Plo,$2.P,(1>.(9.+10000.R3.)(4.R3.(39.+2.+20.)))P,(:.$2.(2>.R4.+8.)=)P,(4.=R6.)P,(1>.(4.=R5.)(4.R5.(1:.+4000.R7.)))P,(4.(5.(1:.+4000.R8.)+4000.)(39.+2.+14.))P,(:.$2.(12.(50.(>.&40.)R11.))R7.)P,(:.$2.(12.(50.(>.&40.)R11.))(3=.(1:.+4000.R:.)R8.))P,(4=.R=.)P,(:.(>.&40.)R30.(1<.&40.$53.))P,(54.R?.)P,(14.$11.R10.(5.VT,+;38.)(15.$16.(3;.R19.)(15.$16.(3;.R18.)(18.$16.))))P,(51.R11.(1:.+4000.R?.)R=.R18.=)P,(1=.$11.R12.VPA,R18.)P,(1=.$11.R13.(5.VPA,(1:.+8.R?.))R18.)P,(3<.$11.R14.R?.R17.)P,(4.(2:.VhAR,)R10.)P,(4.R11.(3=.(3=.R19.+?0.)VDIE_NEED,))P,(4.R1:.(39.+2.+3?.))P,(:.$2.(2>.R1;.+10.)=)P,(31.A2.VCSf,R1=.R17.R14.(3=.R1<.R14.))P,(40.$11.R1:.)P,A3.VK,R1?.R19.R1:.P,(55.R1<.R1;.)P,A3.VGl,R21.R1;.(56.R1:.)P,Pp,(20.$2.$2.)A2.VGp,(24.(20.$2.$2.)R23.(15.(20.$2.$2.)R1.(18.(20.$2.$2.))))R1=.P,Pok,$22.Pc',$52.P,(5>.R2.R24.R44.R43.R3?.R3>.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R45.R23.R22.R25.R1?.R1>.R1=.R1<.R2:.R29.R27.R21.R1.)(58.$11.R47.R2.)(58.$11.R45.(59.(5:.(5;.R44.(1<.&40.R23.)R43.R42.R41.R40.R3?.R3>.R3=.(1<.&40.$35.)R3<.(1<.&40.R1=.)(1<.&40.+8.)R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.)R22.(1<.&40.$5?.)R21.(=.(>.&40.))R20.(5=.$11.))R1?.))")
(* [comment removed for export] *).
  Proof.
    intros Q ra gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 j1 j2 srt ps rest sc SP F fc m mo r x ncks lo
      Hx XAL HR HNC HNR LPS LREST LS TP SHW TJ LI HPS HREST ST LOIMG SPL SPH SPA SCS MI HK HJ HGl HGp HC.
    facts.
    dpose GPA as (PA0 & PA1 & PAL). dpose GT as (T0 & T1 & TAL). pose proof GCTX as (CX0 & CX1). dpose GSEP as (SEP1 & SEP2 & SEP3).
    assert (MSZ : x + 4096 <= map_size x < x + 8192).
    { unfold map_size. clear - Hx. pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)). lia. }
    assert (SPA' : (SP + -48) mod 16 = 0).
    { clear - SPA. apply Z.mod_divide in SPA; [| lia]. apply Z.mod_divide; [lia|]. destruct SPA as [q Hq]. exists (q - 3). lia. }
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL (CSf sc r) (K sc r) _ Q _ mo (KL sc r) HK); [exact HJ| |].
    { eapply (comb_sec_A AL IMG ALWF (CSf sc r) (CSOKf sc r)) with (lo := lo); try exact ST; try exact SCS; try exact MI;
        [clear - Hx; lia| exact LOIMG| clear - SPL DIE_NEED_ge; lia| exact SPH| exact SPA]. }
    cbn beta. intros ms1 mo1 PO HK1 MM1 HJ1. unfold combS_post in PO. ddestruct PO as (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1).
    assert (LO1 : forall A n, A + n <= lo -> disjoint_from [(lo, SP)] A n) by (intros A n H; cbn; split; [left; exact H| exact I]).
    assert (LS1 : lstat m1) by (eapply lstat_transport; [exact LS| exact MU1| intros A n H _; apply LO1; clear - H LOIMG; lia| apply LO1; clear - CX1 LOIMG; lia]).
    assert (TJ1 : rw_cells asegs m1 (T + 2872) [C8 j1; C8 j2]) by (eapply rw_cells_transport; [exact TJ| exact MU1| exact WM1| apply LO1; cbn; clear - T1 LOIMG; lia]).
    assert (LI1 : limg m1 (0x4000 * r) ncks srt 0) by (eapply limg_transport; [exact LI| exact MU1| exact WM1| apply LO1; unfold A_INSTANCE; clear - LOIMG; lia]).
    assert (HPS1 : u64arr asegs m1 PA ps) by (eapply u64arr_transport; [exact HPS| exact MU1| exact WM1| apply LO1; clear - LPS HNC HNR PA1 LOIMG; lia]).
    assert (HREST1 : u64arr asegs m1 (PA + 8 * ncks) rest) by (eapply u64arr_transport; [exact HREST| exact MU1| exact WM1| apply LO1; clear - LREST HNC HNR PA1 LOIMG; lia]).
    pose proof (shadow_wr_mono _ _ SHW WM1) as SHW1.
    (* [comment removed for export] *)
    eapply (large_cfgS Q (Z_to_bv 64 0x4c0b0)) with (lo := lo) (srt := srt) (rest := rest) (ps := ps) (j1 := j1) (j2 := j2) (sc := sc) (r := r) (ncks := ncks).
    all: lazymatch goal with
         | |- forall ok c', _ => idtac
         | |- lstat _ => exact LS1
         | |- _ = Z_to_bv 64 A_TP => exact TP
         | |- shadow_wr _ => exact SHW1
         | |- rw_cells _ _ _ _ => exact TJ1
         | |- limg _ _ _ _ _ => exact LI1
         | |- u64arr _ _ PA _ => exact HPS1
         | |- u64arr _ _ _ _ => exact HREST1
         | |- stk _ _ _ _ => exact ST1
         | |- mem_inv _ _ => exact MI1
         | |- K _ _ _ => exact HK1
         | |- J _ _ => exact HJ1
         | |- Gl _ _ _ => exact HGl
         | |- forall p, Gp _ _ => exact HGp
         | |- crange _ _ _ => eapply crange_sub; [exact SCS| clear; lia| clear - SPL; lia]
         | |- (_ + -48) mod 16 = 0 => exact SPA'
         | |- _ => first [exact Hx| exact XAL| exact HR| exact HNC| exact HNR| exact LPS| exact LREST| exact LOIMG
                         | (clear - SPL DIE_NEED_ge; lia) | (clear - SPH; lia) ]
         end.
    (* [comment removed for export] *)
    intros ok cf PO. unfold large_cpostS in PO.
    ddestruct PO as (ms2 & mo2 & res & v0 & v1 & v2 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & mm & -> & -> & MI2 & ST2 & WM2 & SHW2 & LS2 & REST).
    replace (ret_pc (Z_to_bv 64 0x4c0b0)) with (Z_to_bv 64 0x4c0b0) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
    assert (LO3 : forall A n, A + n <= lo -> disjoint_from [(lo, SP)] A n) by (intros A n H; cbn; split; [left; exact H| exact I]).
    destruct ok.
    - ddestruct REST as (a & r' & rest' & ERES & HK2 & HJ2 & HR' & HNC' & AHI & AAL & ACE & ABAND & ABP & CR & APCS & MU2 & HDR & ZB & SHA & SHB & TJ2 & LI2 & HPS2 & HREST2 & LREST2).
      assert (FR2 : comb_frame mm SP s4 s3 s2 s1 s0 ra).
      { unfold comb_frame in FR1 |- *. eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. cbn; unfold A_INSTANCE.
        split; [right; clear; lia|]. split; [right; clear - ACE LOIMG SPL DIE_NEED_ge MSZ Hx; lia|]. split; [right; clear - ACE LOIMG SPL DIE_NEED_ge MSZ Hx AHI; lia|].
        split; [right; clear - T1 LOIMG SPL DIE_NEED_ge; lia|]. split; [right; clear - LOIMG SPL DIE_NEED_ge; lia|]. split; [right; clear - PA1 HNC HNC' HR' HR HNR LOIMG SPL DIE_NEED_ge; lia| exact I]. }
      assert (KL2 : kinv AL (CSf sc r) (K (sc ++ [(a, map_size x)]) r')).
      { eapply kinv_mono; [| exact (KL (sc ++ [(a, map_size x)]) r')]. intros y Hy. apply CSmono_l. destruct HR' as [-> | [-> _]]; [exact Hy| apply CSmono_p; exact Hy]. }
      eapply (evtA_aevtS_KJ AL (CSf sc r) (K (sc ++ [(a, map_size x)]) r') _ Q _ mo2 KL2 HK2); [exact HJ2| |].
      { eapply (comb_sec_B AL IMG ALWF (CSf sc r) (CSOKf sc r)) with (m0 := mm) (W := []) (lo := lo); try exact FR2; try exact ST2; try exact MI2;
          [exact LOIMG| clear - SPL DIE_NEED_ge; lia| exact SPH| exact SPA| exact SCS| apply munch_refl| apply wmono_refl]. }
      cbn beta. (intros ms3 mo3 dd_H; ddestruct dd_H as (m3 & -> & MU3 & WM3 & MI3 & ST3); intros HK3 MM3 HJ3).
      apply (HC true). unfold combsec_cpostS.
      deexists 16. split; [reflexivity|]. split; [reflexivity|].
      split; [exact MI3|]. split; [exact ST3|]. split; [exact (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WM1 WM2) WM3)|]. split; [exact (shadow_wr_mono _ _ SHW2 WM3)|].
      split; [eapply lstat_transport; [exact LS2| exact MU3| intros A n H _; apply LO3; clear - H LOIMG; lia| apply LO3; clear - CX1 LOIMG; lia]|].
      dexists a, r', rest'.
      split; [exact ERES|]. split; [exact HK3|]. split; [exact HJ3|]. split; [exact HR'|]. split; [exact HNC'|].
      split; [exact AHI|]. split; [exact AAL|]. split; [exact ACE|]. split; [exact ABAND|]. split; [exact ABP|]. split; [exact CR|]. split; [exact APCS|].
      split. { eapply munch_trans. { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; clear; intros; lia. }
               eapply munch_trans. { eapply munch_weaken; [| exact MU2]. unfold A_INSTANCE; unfold sub_fp; cbn [outside]; clear; intros; lia. }
               eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; clear; intros; lia. }
      split; [eapply rw_cells_transport; [exact HDR| exact MU3| exact WM3| apply LO3; cbn; clear - ACE LOIMG MSZ Hx; lia]|].
      split; [eapply rw_cells_transport; [exact ZB| exact MU3| exact WM3| apply LO3; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear - MSZ Hx; lia); clear - ACE LOIMG MSZ Hx; lia]|].
      split; [eapply rw_cells_transport; [exact SHA| exact MU3| exact WM3| apply LO3; cbn [cells_size csize]; rewrite Nat.add_0_r; change (Z.of_nat 512) with 512; clear - ACE LOIMG MSZ Hx AHI; lia]|].
      split. { eapply rw_cells_transport; [exact SHB| exact MU3| exact WM3| apply LO3; cbn [cells_size csize]; rewrite Nat.add_0_r].
               pose proof (Z.div_pos (map_size x - 4096 - x) 8 ltac:(clear - MSZ; lia) ltac:(clear; lia)) as D0.
               rewrite Z2Nat.id by exact D0.
               pose proof (Z.mul_div_le (map_size x - 4096 - x) 8 ltac:(clear; lia)) as D1.
               pose proof (Z.mul_div_le (a + 4096 + x) 8 ltac:(clear; lia)) as D2.
               clear - ACE LOIMG MSZ Hx AHI D0 D1 D2; lia. }
      split; [eapply rw_cells_transport; [exact TJ2| exact MU3| exact WM3| apply LO3; cbn; clear - T1 LOIMG; lia]|].
      split; [eapply limg_transport; [exact LI2| exact MU3| exact WM3| apply LO3; unfold A_INSTANCE; clear - LOIMG; lia]|].
      split. { eapply u64arr_transport; [exact HPS2| exact MU3| exact WM3| apply LO3]. rewrite length_app; cbn [length]. clear - LPS HNC HNC' HR' HR HNR PA1 LOIMG; lia. }
      split; [| exact LREST2].
      destruct rest' as [|r0 rest'']; [eapply u64arr_nil_any; exact HREST2|].
      eapply u64arr_transport; [exact HREST2| exact MU3| exact WM3| apply LO3]. clear - LREST2 HNC HNC' HR' HR HNR PA1 LOIMG; lia.
    - ddestruct REST as (ERES & HK2 & HJ2 & MU2 & TJ2).
      assert (FR2 : comb_frame mm SP s4 s3 s2 s1 s0 ra).
      { unfold comb_frame in FR1 |- *. eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. cbn. split; [right; clear; lia| exact I]. }
      eapply (evtA_aevtS_KJ AL (CSf sc r) (K sc r) _ Q _ mo2 (KL sc r) HK2); [exact HJ2| |].
      { eapply (comb_sec_B AL IMG ALWF (CSf sc r) (CSOKf sc r)) with (m0 := mm) (W := []) (lo := lo); try exact FR2; try exact ST2; try exact MI2;
          [exact LOIMG| clear - SPL DIE_NEED_ge; lia| exact SPH| exact SPA| exact SCS| apply munch_refl| apply wmono_refl]. }
      cbn beta. (intros ms3 mo3 dd_H; ddestruct dd_H as (m3 & -> & MU3 & WM3 & MI3 & ST3); intros HK3 MM3 HJ3).
      apply (HC false). unfold combsec_cpostS.
      deexists 16. split; [reflexivity|]. split; [reflexivity|].
      split; [exact MI3|]. split; [exact ST3|]. split; [exact (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WM1 WM2) WM3)|]. split; [exact (shadow_wr_mono _ _ SHW2 WM3)|].
      split; [eapply lstat_transport; [exact LS2| exact MU3| intros A n H _; apply LO3; clear - H LOIMG; lia| apply LO3; clear - CX1 LOIMG; lia]|].
      split; [exact ERES|]. split; [exact HK3|]. split; [exact HJ3|].
      split. { eapply munch_trans; [exact MU1|]. eapply munch_trans; [| exact MU3]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear; intros; lia. }
      eapply rw_cells_transport; [exact TJ2| exact MU3| exact WM3| apply LO3; cbn; clear - T1 LOIMG; lia].
  Qed.
End LargeCfgS.

End ARUN_1.
