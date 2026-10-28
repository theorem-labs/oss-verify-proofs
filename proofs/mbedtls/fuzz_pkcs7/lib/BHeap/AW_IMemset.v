(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AW_IMemset () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "ARUN_1.zfill"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le1"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.nil"; "ARUN_1.izeros"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.IMemset.ims_post"; "ARUN_1.A_IMEMSET_RET"; "ARUN_1.A_IMEMSET_BLOOP"; "Stdlib.ZArith.BinInt.Z.mul"; "ARUN_1.A_IMEMSET_WLOOP"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "ARUN_1.A_IMEMSET"].

Section ARUN_1. Context {hAR : arun}.
Definition A_IMEMSET : Z := 0x7aa58.
Definition A_IMEMSET_BLOOP : Z := 0x7aa70.
Definition A_IMEMSET_WLOOP : Z := 0x7aaa4.
Definition A_IMEMSET_RET : Z := 0x7aab4.

(* [comment removed for export] *)
Definition zfill (m : mem) (DST i n : Z) : Prop :=
  bytes_at asegs m DST (repeat (Z_to_bv 8 0) (Z.to_nat i)) /\ wr_at asegs m DST n /\ 0 <= i <= n.

#[using="Type"] Lemma zfill_start : forall m DST n cs,
  rw_cells asegs m DST cs -> Z.of_nat (cells_size cs) = n -> zfill m DST 0 n.
Proof.
  intros m DST n cs [[Hwf Hb] Hw] E. unfold zfill. rewrite <- E. split; [|split; [exact Hw| lia]].
  cbn [Z.to_nat repeat]. apply bytes_at_nil. ddestruct Hw as (H1 & H2 & _). lia.
Qed.

#[using="Type"] Lemma zfill_store_ok : ltac2:(CDefT.buildp (gd_tbl_AW_IMemset ()) "Pm,P,(0.&40.)(1.(0.&8.))PDST,$2.Pi,$2.Pn,$2.Pk,$3.P,(4.R5.R4.R3.R2.)P,(5.(6.R4.(7.R2.))R3.)(8.$9.(:.$;.R7.(<.(6.R6.R5.))R3.)$=.)")
(* [comment removed for export] *).
Proof.
  (intros m DST i n k dd_H; ddestruct dd_H as (HB & HW & HI); intros Hk). eapply wr_at_store_ok; [exact HW| lia| lia].
Qed.

#[using="Type"] Lemma repeat_app_nat : forall {X} (x : X) a b, repeat x (a + b) = repeat x a ++ repeat x b.
Proof. intros X x a b. rewrite repeat_app. reflexivity. Qed.

#[using="Type"] Lemma zfill_write : ltac2:(CDefT.buildp (gd_tbl_AW_IMemset ()) "Pm,P,(0.&40.)(1.(0.&8.))PDST,$2.Pi,$2.Pn,$2.Pbs,(>.(0.&8.))P,(4.R5.R4.R3.R2.)P,(5.(6.R4.(7.(?.(0.&8.)R2.)))R3.)P,(8.(>.(0.&8.))R3.(10.(0.&8.)(11.&8.=)(?.(0.&8.)R3.)))(4.(12.R8.(<.(6.R7.R6.))R4.)R7.(6.R6.(7.(?.(0.&8.)R4.)))R5.)")
(* [comment removed for export] *).
Proof.
  (intros m DST i n bs dd_H; ddestruct dd_H as (HB & HW & HI); intros Hn E). unfold zfill.
  dpose HW as (W0 & W1 & _).
  split; [| split; [apply wr_at_write; exact HW| lia]].
  replace (Z.to_nat (i + Z.of_nat (length bs))) with (Z.to_nat i + length bs)%nat by lia.
  rewrite repeat_app_nat. apply bytes_at_app. split.
  - apply bytes_at_write_other; [exact HB| lia| lia|]. left. rewrite repeat_length. lia.
  - rewrite repeat_length. replace (DST + Z.of_nat (Z.to_nat i)) with (DST + i) by lia.
    rewrite <- E. apply bytes_at_write_same; lia.
Qed.

#[using="Type"] Lemma zfill_write1 : ltac2:(CDefT.buildp (gd_tbl_AW_IMemset ()) "Pm,P,(0.&40.)(1.(0.&8.))PDST,$2.Pi,$2.Pn,$2.P,(4.R4.R3.R2.R1.)P,(5.(6.R3.+1.)R2.)(4.(12.R6.(<.(6.R5.R4.))(13.(11.&40.=)))R5.(6.R4.+1.)R3.)")
(* [comment removed for export] *).
Proof.
  intros m DST i n Z1 Hn. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
  change (i + 1) with (i + Z.of_nat (length [Z_to_bv 8 0])). apply zfill_write; [exact Z1| cbn; lia| reflexivity].
Qed.

#[using="Type"] Lemma zfill_write8 : ltac2:(CDefT.buildp (gd_tbl_AW_IMemset ()) "Pm,P,(0.&40.)(1.(0.&8.))PDST,$2.Pi,$2.Pn,$2.P,(4.R4.R3.R2.R1.)P,(5.(6.R3.+8.)R2.)(4.(12.R6.(<.(6.R5.R4.))(14.(11.&40.=)))R5.(6.R4.+8.)R3.)")
(* [comment removed for export] *).
Proof.
  intros m DST i n Z1 Hn.
  change (le8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 8).
  change (i + 8) with (i + Z.of_nat (length (repeat (Z_to_bv 8 0) 8))). apply zfill_write; [exact Z1| cbn; lia| reflexivity].
Qed.

(* [comment removed for export] *)
Definition izeros (m : mem) (a n : Z) : Prop := rw_cells asegs m a [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
#[using="Type"] Lemma izeros_i : ltac2:(CDefT.buildp (gd_tbl_AW_IMemset ()) "Pm,P,(0.&40.)(1.(0.&8.))Pa,$2.Pn,$2.P,(15.$;.R3.R2.(16.$17.(18.(19.R1.)(10.(0.&8.)(11.&8.=)(19.R1.)))(1:.$17.)))(1;.R4.R3.R2.)")
(* [comment removed for export] *).
Proof. intros; assumption. Qed.
#[using="Type"] Lemma izeros_e : ltac2:(CDefT.buildp (gd_tbl_AW_IMemset ()) "Pm,P,(0.&40.)(1.(0.&8.))Pa,$2.Pn,$2.P,(1;.R3.R2.R1.)(15.$;.R4.R3.(16.$17.(18.(19.R2.)(10.(0.&8.)(11.&8.=)(19.R2.)))(1:.$17.)))")
(* [comment removed for export] *).
Proof. intros; assumption. Qed.
#[using="Type"] Lemma izeros_transport : ltac2:(CDefT.buildp (gd_tbl_AW_IMemset ()) "PW,(>.$1<.)Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))Pa,$2.Pn,$2.P,(1;.R4.R2.R1.)P,(5.=R2.)P,(1=.R7.R6.R5.)P,(1>.$;.R7.R6.)P,(1?.R9.R6.R5.)(1;.R8.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros W m m' a n ZB Hn MU WM DJ. unfold izeros in *. eapply rw_cells_transport; [exact ZB| exact MU| exact WM|].
  cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact Hn. exact DJ.
Qed.
#[using="Type"] Lemma izeros_ex : ltac2:(CDefT.buildp (gd_tbl_AW_IMemset ()) "Pm,P,(0.&40.)(1.(0.&8.))Pa,$2.Pn,$2.P,(5.=R1.)P,(1;.R4.R3.R2.)(20.(>.$17.)Lcs,(>.$17.)(21.(15.$;.R6.R5.R1.)(8.$2.(7.(22.R1.))R4.)))")
(* [comment removed for export] *).
Proof. intros m a n Hn H. eexists. split; [exact H|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact Hn. reflexivity. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma izeros_split16 : ltac2:(CDefT.buildp (gd_tbl_AW_IMemset ()) "Pm,P,(0.&40.)(1.(0.&8.))Pa,$2.Pn,$2.P,(1;.R3.R2.R1.)P,(5.+10.R2.)(21.(15.$;.R5.R4.(16.$17.(23.(11.&40.=))(16.$17.(23.(11.&40.=))(1:.$17.))))(1;.R5.(6.R4.+10.)(24.R3.+10.)))")
(* [comment removed for export] *).
Proof.
  intros m a n H Hn. unfold izeros in *.
  assert (R : rw_cells asegs m a ([C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ++ [CB (Z.to_nat (n - 16)) (repeat (Z_to_bv 8 0) (Z.to_nat (n - 16)))])).
  { eapply rw_cells_reshape; [exact H| |].
    - cbn. rewrite repeat_length. auto.
    - cbn [cells_bytes cbytes app]. rewrite !app_nil_r.
      change (le8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 8). rewrite <- !repeat_app. f_equal. lia. }
  apply rw_cells_app in R. destruct R as [R1 R2]. split; [exact R1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in R2. exact R2.
Qed.

#[using="Type"] Lemma zfill_done : ltac2:(CDefT.buildp (gd_tbl_AW_IMemset ()) "Pm,P,(0.&40.)(1.(0.&8.))PDST,$2.Pn,$2.P,(4.R3.R2.R1.R1.)(15.$;.R4.R3.(16.$17.(18.(19.R2.)(10.(0.&8.)(11.&8.=)(19.R2.)))(1:.$17.)))")
(* [comment removed for export] *).
Proof.
  (intros m DST n dd_H; ddestruct dd_H as (HB & HW & HI)). split.
  - split. { cbn. rewrite repeat_length. auto. } cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. replace (Z.of_nat (Z.to_nat n)) with n by lia. exact HW.
Qed.

Section IMemset.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition ims_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (PC : word) (fc : bv 32) (m0 : mem) (DST n : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_IMemset ()) "Lms',$25.(20.(0.&40.)Lx3,(0.&40.)(20.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(21.(8.$25.R3.(26.(27.O24.O23.O22.O21.O20.O1?.O1>.O1=.O1<.O1;.O1:.O19.R2.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.)O6.O5.O4.(28.(0.&40.))R1.(29.$;.)))(21.(1=.(16.(2:.$2.$2.)(2;.$2.$2.O2.(6.O2.O1.))(1:.(2:.$2.$2.)))O3.R1.)(21.(1>.$;.O3.R1.)(21.(2<.$;.R1.)(1;.R1.O2.O1.)))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma imemset_bloop : ltac2:(CDefT.buildp (gd_tbl_AW_IMemset ()) "Pk,$3.Pi,$2.Pn,$2.PDST,$2.Pcd,$2.Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(2=.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(1.(0.&8.))Pm,P,(0.&40.)(1.(0.&8.))P,(8.$2.R24.(24.R23.(7.R25.)))P,(21.(5.=R25.)(2>.R25.R24.))P,(8.$2.R23.(6.R24.R26.))P,(4.R4.R25.R27.R26.)P,(5.+10000.R26.)P,(5.(6.R27.R28.)+65?000.)P,(1=.(16.(2:.$2.$2.)(2;.$2.$2.R28.(6.R28.R29.))(1:.(2:.$2.$2.)))R8.R7.)P,(1>.$;.R9.R8.)P,(2<.$;.R9.)(2?.$;.VAL,VCS,(30.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.(11.&40.=)(11.&40.(6.R2;.R2<.))R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.(11.&40.$31.)R<.R;.R2;.R2<.)(26.(27.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.(11.&40.=)(11.&40.(6.R2;.R2<.))(11.&40.R2:.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)R=.(11.&40.$32.)R<.(28.(0.&40.))R:.(29.$;.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i n DST cd ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
      Hi Hin -> ZF D0 D1 MU WM MI; [lia|].
    facts. unfold A_IMEMSET_BLOOP, A_IMEMSET_RET in *.
    (* [comment removed for export] *)
    pose proof (zfill_store_ok m DST i n 1 ZF ltac:(cbn; lia)) as SOK.
    zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem ?mx ?a _) _) =>
      pose proof (zfill_write1 mx DST i n ZF ltac:(lia)) as ZF'
    end.
    store_done. try clear ZF. rename ZF' into ZF.
    (* [comment removed for export] *)
    zstep. zstep. if_cases Kne; zify_cond Kne.
    - eapply (IH (i + 1) n DST); try eassumption; try lia.
    - (* [comment removed for export] *)
      zstep. apply evtA_done. unfold ims_post. replace (DST + i + 1) with (DST + n) by lia.
      deexists 2. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      apply izeros_i. apply zfill_done. replace (i + 1) with n in ZF by lia. exact ZF.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma imemset_wloop : ltac2:(CDefT.buildp (gd_tbl_AW_IMemset ()) "Pk,$3.Pi,$2.Pn,$2.PDST,$2.Pcd,$2.Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(2=.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(1.(0.&8.))Pm,P,(0.&40.)(1.(0.&8.))P,(8.$2.R24.(24.R23.(33.+10.(7.R25.))))P,(21.(5.=R25.)(2>.R25.R24.))P,(8.$2.R23.(6.R24.R26.))P,(4.R4.R25.R27.R26.)P,(5.+10000.R26.)P,(5.(6.R27.R28.)+65?000.)P,(1=.(16.(2:.$2.$2.)(2;.$2.$2.R28.(6.R28.R29.))(1:.(2:.$2.$2.)))R8.R7.)P,(1>.$;.R9.R8.)P,(2<.$;.R9.)(2?.$;.VAL,VCS,(30.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.(11.&40.=)(11.&40.(6.R2;.R2<.))R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.(11.&40.$31.)R<.R;.R2;.R2<.)(26.(27.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.(11.&40.=)(11.&40.(6.R2;.R2<.))(11.&40.R2:.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)R=.(11.&40.$34.)R<.(28.(0.&40.))R:.(29.$;.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i n DST cd ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
      Hi Hin -> ZF D0 D1 MU WM MI; [lia|].
    facts. unfold A_IMEMSET_WLOOP, A_IMEMSET_RET in *.
    (* [comment removed for export] *)
    pose proof (zfill_store_ok m DST i n 8 ZF ltac:(cbn; lia)) as SOK.
    zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem ?mx ?a _) _) =>
      pose proof (zfill_write8 mx DST i n ZF ltac:(lia)) as ZF'
    end.
    store_done. try clear ZF. rename ZF' into ZF.
    (* [comment removed for export] *)
    pose proof (zfill_store_ok _ DST (i + 8) n 8 ZF ltac:(cbn; lia)) as SOK.
    replace (DST + (i + 8)) with (DST + i + 8) in SOK by lia.
    zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem ?mx ?a _) _) =>
      pose proof (zfill_write8 mx DST (i + 8) n ZF ltac:(lia)) as ZF';
      replace (DST + (i + 8)) with (DST + i + 8) in ZF' by lia
    end.
    store_done. try clear ZF. rename ZF' into ZF.
    (* [comment removed for export] *)
    zstep. zstep. if_cases Klt; zify_cond Klt.
    - eapply (IH (i + 16) n DST); try eassumption; try lia. replace (i + 16) with (i + 8 + 8) by lia. exact ZF.
    - apply evtA_done. unfold ims_post. replace (DST + i + 16) with (DST + n) by lia.
      deexists 2. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      apply izeros_i. apply zfill_done. replace (i + 8 + 8) with n in ZF by lia. exact ZF.
  Qed.


  #[using="Type"] Lemma land15_lor_zero : forall a b, 0 <= a -> 0 <= b -> Z.land (Z.lor a b) 15 = 0 -> a mod 16 = 0 /\ b mod 16 = 0.
  Proof.
    intros a b Ha Hb H. rewrite Z.land_lor_distr_l in H. apply Z.lor_eq_0_iff in H. destruct H as [H1 H2].
    change 15 with (Z.ones 4) in H1, H2. rewrite Z.land_ones in H1, H2 by lia. change (2^4) with 16 in H1, H2. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma imemset_spec : ltac2:(CDefT.buildp (gd_tbl_AW_IMemset ()) "Pn,$2.PDST,$2.Pcs,(>.$17.)Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(2=.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))P,(2>.=R22.)P,(15.$;.R2.R22.R21.)P,(8.$2.(7.(22.R22.))R24.)P,(5.+10000.R24.)P,(5.(6.R25.R26.)+65?000.)P,(2<.$;.R6.)(2?.$;.VAL,VCS,(30.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.(11.&40.R27.)(11.&40.=)(11.&40.(6.R27.R28.))R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.(35.R25.)R8.R7.R27.R28.)(26.(27.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.(11.&40.R27.)(11.&40.=)(11.&40.R28.)R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)R9.(11.&40.$36.)R8.(28.(0.&40.))R7.(29.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros n DST cs ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      N0 HC HSZ D0 D1 MI.
    facts. unfold A_IMEMSET. pose proof (munch_refl [(DST, DST + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (zfill_start m DST n cs HC HSZ) as ZF. clear HC.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
    - (* [comment removed for export] *)
      destruct (land15_lor_zero n DST ltac:(lia) ltac:(lia) Kal) as [Mn Md].
      zstep. if_cases Kz; zify_cond Kz. { exfalso. lia. }
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      eapply evtA_cut.
      { eapply (imemset_wloop (Z.to_nat (n / 16)) 0 n DST); try eassumption;
          pose proof (Z.div_mod n 16 ltac:(lia)); lia. }
      cbn beta. (intros ms1 dd_H; ddestruct dd_H as (x3 & m' & -> & MU' & WM' & MI' & HC')).
      unfold A_IMEMSET_RET. zstep. apply evtA_done. unfold ims_post. deexists 2.
      split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|exact HC'].
    - (* [comment removed for export] *)
      zstep. if_cases Kz; zify_cond Kz. { exfalso. lia. }
      zstep. zstep.
      eapply evtA_cut.
      { eapply (imemset_bloop (Z.to_nat n) 0 n DST); try eassumption; try lia. }
      cbn beta. (intros ms1 dd_H; ddestruct dd_H as (x3 & m' & -> & MU' & WM' & MI' & HC')).
      unfold A_IMEMSET_RET. zstep. apply evtA_done. unfold ims_post. deexists 2.
      split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|exact HC'].
  Qed.
End IMemset.
End ARUN_1.
#[global] Opaque izeros.
