(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AJ AKinvS AKinvM ASpin ASpinS AW_Unwind AW_Unwind2 AW_MmapFixed AW_MmapDie AW_MmapFixedNR AW_Poison AW_DepotCfg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_CfgS AW_ClassId AW_Combined AW_Refill AW_GetFrom AW_Populate AW_Populate2 AW_CfgDefs AW_PopulateCfgS.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Dealloc AW_QPut AW_Enqueue AW_CbRecycle AW_LCDealloc AW_RTA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AW_RecLC () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CfgDefs.pop_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_RI_CELL"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CfgDefs.mwc_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.thr_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_SEALED2"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_DYING"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DYING"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "ARUN_1.rl_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.add"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.skipn"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_commit"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_fresh"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.max_count"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_LCDealloc.pcl_cells"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "ARUN_1.RecLC.rl_post"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CbRecycle.A_LC_DEALLOC"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].

Section ARUN_1. Context {hAR : arun}.
Definition rl_statics (m : mem) (SB RI CTX T : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_RecLC ()) "(0.(1.O5.O4.)(0.(2.$3.O5.$4.(5.$6.(7.(8.&40.O3.))(9.$6.)))(0.(:.O5.)(0.(;.O5.O2.O1.)(0.(<.O5.)(0.(2.$3.O5.$=.(5.$6.(7.(8.&40.+1.))(9.$6.)))(0.(2.$3.O5.$>.(5.$6.(7.(8.&40.$?.))(9.$6.)))(2.$3.O5.$?.(5.$6.(10.(8.&40.=))(9.$6.))))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma rl_statics_transport : ltac2:(CDefT.buildp (gd_tbl_AW_RecLC ()) "PW,(11.$12.)Pm,P,(13.&40.)(14.(13.&8.))Pm',P,(13.&40.)(14.(13.&8.))PSB,$15.PRI,$15.PCTX,$15.PT,$15.P,(16.R6.R4.R3.R2.R1.)P,(17.R8.R7.R6.)P,PA,$15.Pn,$15.P,(0.(18.+10000.R2.)(18.(19.R2.R1.)+65?000.))(1:.R<.R3.R2.)P,(1:.R:.(19.R5.+98.)+8.)(16.R9.R8.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  (intros W m m' SB RI CTX T dd_H; ddestruct dd_H as (PS & RIC & MW & TS & POI & GS & GD & DY); intros MU DJ DC).
  assert (DJ' : forall A n, 0x10000 <= A /\ A + n <= 0x1db8c8 -> disjoint_from W A n) by (intros A n H; apply DJ; lia).
  split; [exact (pop_statics_transport _ _ _ _ PS MU DJ')|].
  split; [eapply ro_cells_transport; [exact RIC| exact MU| apply DJ; unfold A_RI_CELL, A_INSTANCE; cbn; lia]|].
  split; [exact (mwc_statics_transport _ _ _ MW MU DJ')|].
  split. { eapply thr_statics_transport; [exact TS| exact MU| | | | exact DC]; apply DJ; unfold A_TSD_INITED, A_TSD_PTR, A_TSD_ARR; cbn; lia. }
  split; [exact (poison_statics_transport _ _ _ POI MU DJ')|].
  unfold A_GOT_SEALED2, A_GOT_DYING, A_DYING in *.
  split; [eapply ro_cells_transport; [exact GS| exact MU| apply DJ; cbn; lia]|].
  split; [eapply ro_cells_transport; [exact GD| exact MU| apply DJ; cbn; lia]|].
  eapply ro_cells_transport; [exact DY| exact MU| apply DJ; cbn; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ro_cells_join : ltac2:(CDefT.buildp (gd_tbl_AW_RecLC ()) "Pm,P,(13.&40.)(14.(13.&8.))PA,$15.Pcs1,(11.$6.)Pcs2,(11.$6.)P,(2.$3.R4.R3.R2.)P,(2.$3.R5.(19.R4.(1;.(1<.R3.)))R2.)(2.$3.R6.R5.(1=.$6.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros m A cs1 cs2 [W1 B1] [W2 B2]. unfold ro_cells, cells_at. rewrite cells_wf_app, cells_bytes_app.
  refine (conj (conj W1 W2) _). apply bytes_at_app. rewrite cells_bytes_length by exact W1. auto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma u32arr_window : ltac2:(CDefT.buildp (gd_tbl_AW_RecLC ()) "Pm,P,(13.&40.)(14.(13.&8.))PA,$15.Pl,(11.(13.&40.))Pi,$1>.Pn,$1>.P,(1?.$3.R5.R4.R3.)P,(20.(21.R3.R2.)(22.(13.&40.)R4.))(1?.$3.R7.(19.R6.(23.+4.(1;.R4.)))(24.(13.&40.)R3.(25.(13.&40.)R4.R5.)))")
(* [comment removed for export] *).
Proof.
  intros m A l i n U H.
  rewrite <- (firstn_skipn i l) in U. apply u32arr_app in U. destruct U as [_ U]. rewrite firstn_length_le in U by lia.
  rewrite <- (firstn_skipn n (skipn i l)) in U. apply u32arr_app in U. destruct U as [U _]. exact U.
Qed.


Section RecLC.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  (* [comment removed for export] *)
  Variable CSf : option bool -> option bool -> Z -> Prop.
  Hypothesis CSOKf : forall u f, cs_ok AL (CSf u f).
  Hypothesis CSmono_f : forall u b y, CSf u None y -> CSf u (Some b) y.
  Hypothesis ASB : al_sb AL = 0x7fff8000.

  (* [comment removed for export] *)
  Variables (T CTX SB RI c : Z).
  Let R := RI + 128 * c.
  Let RB := SB + c * 2^32.
  Let FA := RB + 0xE0000000.
  Let PC := T + 208 + 80 * c.
  Hypothesis GSB : 0x10007fff9000 <= SB /\ SB mod 4096 = 0 /\ RI = SB + 2^37 /\ RI + 4096 <= ACEIL.
  Hypothesis GC : 1 <= c <= 30.
  Hypothesis GT : (Timg T /\ Tband T) /\ T + 4096 <= ACEIL /\ T mod 4096 = 0.
  Hypothesis GCTX : (0x65f000 <= CTX /\ Pband CTX 0x10000) /\ CTX + 0x10000 <= ACEIL.
  Hypothesis GSEP : ltac2:(CDefT.buildp (gd_tbl_AW_RecLC ()) "(0.(26.(18.(19.VT,+1000.)VSB,)(18.(19.(19.VSB,(27.+2.+25.))+1000.)VT,))(0.(26.(18.(19.VCTX,+10000.)VT,)(18.(19.VT,+1000.)VCTX,))(26.(18.(19.VCTX,+10000.)VSB,)(18.(19.(19.VSB,(27.+2.+25.))+1000.)VCTX,))))")
(* [comment removed for export] *).
  Hypothesis CST : forall u f, crange (CSf u f) T 4096.
  Hypothesis CSCTX : forall u f, crange (CSf u f) CTX 0x10000.
  Hypothesis CSRI : forall u f, crange (CSf u f) RI 4096.

  Variable K : option bool -> option bool -> Model -> Prop.
  Hypothesis KL : forall u f, kinv AL (CSf u f) (K u f).
  Variable mfa : Z.
  Let FAA := FA + mfa.
  Hypothesis LEDGER_F : ltac2:(CDefT.buildp (gd_tbl_AW_RecLC ()) "Pu,(14.$28.)Pmo,$29.P,(26.(2:.(14.$28.)R2.(2;.$28.))(2:.(14.$28.)R2.(2<.$28.$2=.)))P,A3.VK,R3.(2;.$28.)R2.(0.(2:.$28.(2>.(2?.(30.R3.))(8.&40.VFAA,)(8.&40.(27.+2.+12.)))$2=.)(26.(2:.$28.(31.(32.(30.R3.))(8.&40.VFAA,)(8.&40.(27.+2.+12.)))$2=.)(2:.$28.(2>.(1=.(33.(13.&40.)(13.&40.))(2?.(30.R3.))(32.(30.R3.)))(8.&40.VFAA,)(8.&40.(27.+2.+12.)))$2=.)))")
(* [comment removed for export] *).
  Hypothesis TF_commit : ltac2:(CDefT.buildp (gd_tbl_AW_RecLC ()) "Pu,(14.$28.)Pmo,$29.P,(26.(2:.(14.$28.)R2.(2;.$28.))(2:.(14.$28.)R2.(2<.$28.$2=.)))P,A3.VK,R3.(2;.$28.)R2.P,(2:.$28.(31.(32.(30.R3.))(8.&40.VFAA,)(8.&40.(27.+2.+12.)))$2=.)A3.VK,R5.(2<.$28.$2=.)(34.+32.VFAA,(27.+2.+12.)R4.)")
(* [comment removed for export] *).
  Hypothesis TF_fresh : ltac2:(CDefT.buildp (gd_tbl_AW_RecLC ()) "Pu,(14.$28.)Pmo,$29.P,(26.(2:.(14.$28.)R2.(2;.$28.))(2:.(14.$28.)R2.(2<.$28.$2=.)))P,A3.VK,R3.(2;.$28.)R2.P,(2:.$28.(2>.(1=.(33.(13.&40.)(13.&40.))(2?.(30.R3.))(32.(30.R3.)))(8.&40.VFAA,)(8.&40.(27.+2.+12.)))$2=.)A3.VK,R5.(2<.$28.$2=.)(35.+32.VFAA,(27.+2.+12.)R4.)")
(* [comment removed for export] *).
  Hypothesis GMFA : 0 <= mfa /\ mfa mod 2^18 = 0 /\ mfa + 2^18 <= 2^29.
  Hypothesis CSFz : forall u, crange (CSf u (Some true)) FAA (2^18).
  Hypothesis ROOM_F : forall u mo, (u = None \/ u = Some true) -> K u None mo -> fixrw_grantable 0x32 FAA (2^18) mo.
  Hypothesis SCAR_F : forall u, (u = None \/ u = Some true) -> scar_site AL (CSf u None) (K u None) FAA (2^18).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis CSFA : forall u f, crange (CSf u f) FA mfa.

  Ltac facts :=
    pose proof (cs_ok_sb _ _ (CSOKf None None)) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition top_half (cks : list word) (mx cnt : Z) : list word := firstn (Z.to_nat cnt) (skipn (Z.to_nat (mx - cnt)) cks).

  (* [comment removed for export] *)
  Definition rl_post (SP : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (AB count mx cnt csz nf lo : Z) (cks js : list word) (st80 st88 : word) (shF : list byte) (m0 : mem) : config -> Prop :=
    fun cf => exists ms' mo' (f : option bool) (count' nf' : Z) (cks' js' : list word) (stj' j1' j2' st80' : word)
                     (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      cf = mkCfg ms' mo'
      /\ ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ K None f mo' /\ J m' mo' /\ (f = None \/ f = Some true)
      (* [comment removed for export] *)
      /\ munch [(lo, SP); (PC, PC + 4); (PC + 16, PC + 80); (T + 2784, T + 2792); (T + 2872, T + 2888);
                (R, R + 8); (R + 16, R + 32); (R + 80, R + 88); (FA + 4 * nf, FA + 4 * nf + 4 * cnt);
                (FAA, FAA + 2^18); (0x7fff8000 + FAA / 8, 0x7fff8000 + FAA / 8 + 32768)] m0 m'
      /\ wmono asegs m0 m' /\ mem_inv asegs m' /\ stk asegs m' lo SP
      /\ rl_statics m' SB RI CTX T
      (* [comment removed for export] *)
      /\ rw_cells asegs m' PC (pcl_cells count' mx csz) /\ u32arr asegs m' (PC + 16) cks' /\ length cks' = 16%nat
      /\ rw_cells asegs m' (T + 2784) [C8 stj'] /\ rw_cells asegs m' (T + 2872) [C8 j1'; C8 j2']
      (* [comment removed for export] *)
      /\ rw_cells asegs m' R [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m' (R + 16) [C8 (Z_to_bv 64 nf')]
      /\ rw_cells asegs m' (R + 24) [C8 (Z_to_bv 64 (mfa + unit_if f))] /\ rw_cells asegs m' (R + 80) [C8 st80'; C8 st88]
      /\ u32arr asegs m' (FA + 4 * nf') js' /\ 4 * (nf' + Z.of_nat (length js')) = mfa + unit_if f
      /\ (f = Some true -> rw_cells asegs m' (0x7fff8000 + FAA / 8) [CB (Z.to_nat 32768) (repeat (Z_to_bv 8 0xfa) (Z.to_nat 32768))])
      /\ (f <> Some true -> rw_cells asegs m' (0x7fff8000 + FAA / 8) [CB (Z.to_nat 32768) shF])
      /\ (f = Some true -> mfa < 4 * (nf + cnt))                        (* [comment removed for export] *)
      (* [comment removed for export] *)
      /\ (exists (dr : bool) (dn : nat),
            (if dr then count = mx /\ Z.of_nat dn = cnt else count < mx /\ f = None /\ dn = 0%nat)
            /\ count' = count - Z.of_nat dn + 1 /\ nf' = nf + Z.of_nat dn
            /\ cks' = upd cks (Z.to_nat (count - Z.of_nat dn)) (Z_to_bv 64 ((AB - RB) / 16))
            /\ (dr = true -> st80' = Z_to_bv 64 (bv_unsigned st80 + cnt) /\ u32arr asegs m' (FA + 4 * nf) (map sx32 (top_half cks mx cnt)))
            /\ (dr = false -> st80' = st80 /\ js' = js)
            /\ Z.of_nat (length js') + Z.of_nat dn = Z.of_nat (length js) + unit_if f / 4).

  #[using="AL IMG ALWF CSOKf CSmono_f ASB GSB GC GT GCTX GSEP CST CSCTX CSRI KL LEDGER_F TF_commit TF_fresh GMFA CSFz ROOM_F SCAR_F CSFA"] Theorem lc_dealloc_cfgS : ltac2:(CDefT.buildp (gd_tbl_AW_RecLC ()) "PQ,P,$36.SpPra,(13.&40.)Pgp,(13.&40.)Ptp,(13.&40.)Pt0,(13.&40.)Pt1,(13.&40.)Pt2,(13.&40.)Ps0,(13.&40.)Ps1,(13.&40.)Pa4,(13.&40.)Pa5,(13.&40.)Pa6,(13.&40.)Pa7,(13.&40.)Ps2,(13.&40.)Ps3,(13.&40.)Ps4,(13.&40.)Ps5,(13.&40.)Ps6,(13.&40.)Ps7,(13.&40.)Ps8,(13.&40.)Ps9,(13.&40.)Ps10,(13.&40.)Ps11,(13.&40.)Pt3,(13.&40.)Pt4,(13.&40.)Pt5,(13.&40.)Pt6,(13.&40.)Pstj,(13.&40.)Pj1,(13.&40.)Pj2,(13.&40.)Pst80,(13.&40.)Pst88,(13.&40.)PSP,$15.PAB,$15.Pcount,$15.Pcsz,$15.Pnf,$15.Plo,$15.Pcks,(11.(13.&40.))Pjs,(11.(13.&40.))PshF,(11.(13.&8.))PF,(37.&5.(13.&40.))Pfc,(13.&20.)Pm,P,(13.&40.)(14.(13.&8.))Pmo,$29.Zmx,$15.(38.Vc,)P,(18.VRB,R=.)P,(39.R>.(19.VRB,(27.+2.+20.)))P,(2:.$15.(3:.(3;.R?.VRB,)+10.)=)P,(0.(18.=R?.)(18.R?.R4.))P,(0.(18.=R?.)(39.R?.(27.+2.+20.)))P,(2:.$1>.(22.(13.&40.)R=.)#10.)P,(3<.$3.R9.VPC,(3=.R12.R7.R11.))P,(1?.$3.R:.(19.VPC,+10.)R?.)P,(3<.$3.R;.(19.VT,+:>0.)(5.$6.(7.R1;.)(9.$6.)))P,(3<.$3.R<.(19.VT,+;38.)(5.$6.(7.R1;.)(5.$6.(7.R1:.)(9.$6.))))P,(18.=R14.)P,(39.(19.R15.+10.)(27.+2.+1;.))P,(2:.$15.(23.+4.(19.R16.(1;.(22.(13.&40.)R13.))))Vmfa,)P,(3<.$3.R10.VR,(5.$6.(7.(8.&40.=))(9.$6.)))P,(3<.$3.R11.(19.VR,+10.)(5.$6.(7.(8.&40.R18.))(9.$6.)))P,(3<.$3.R12.(19.VR,+18.)(5.$6.(7.(8.&40.Vmfa,))(9.$6.)))P,(3<.$3.R13.(19.VR,+50.)(5.$6.(7.R20.)(5.$6.(7.R1?.)(9.$6.))))P,(1?.$3.R14.(19.VFA,(23.+4.R1;.))R18.)P,(3<.$3.R15.(19.+7???8000.(3>.VFAA,+8.))(5.$6.(3?.(40.+8000.)R18.)(9.$6.)))P,(16.R16.VSB,VRI,VCTX,VT,)P,(41.$3.R17.R1=.R22.)P,(18.(42.VhAR,)R1>.)P,(18.R1?.(3;.R24.+2<0.))P,(18.R25.(27.+2.+3>.))P,(2:.$15.(3:.R26.+10.)=)P,(26.(18.R27.VT,)(18.(19.VT,+1000.)R22.))P,(43.A2.VCSf,(2;.$28.)(2;.$28.)R23.(3;.R28.R23.))P,(44.$3.R1>.)P,(2:.(13.&40.)R47.(8.&40.$45.))P,A3.VK,(2;.$28.)(2;.$28.)R1?.P,(46.R21.R20.)P,Pc',$36.P,(47.R2>.R4=.R4<.R4;.R47.R46.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R25.R24.R2=.R2<.R21.(3>.R21.+2.)R2;.R2:.R29.R28.R27.R30.R2?.R26.R23.R1.)(48.$3.R4?.R2.)(48.$3.R4>.(49.(4:.(4;.R4=.(8.&40.R2>.)R4<.R4;.R4:.R49.R48.R47.R46.(8.&40.(19.VT,+=0.))(8.&40.$4<.)(8.&40.Vc,)(8.&40.R2=.)R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.)R25.(8.&40.$4=.)R24.(2;.(13.&40.))R23.(4>.$3.))R22.))")
(* [comment removed for export] *).
  Proof.
    intros Q ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 stj j1 j2 st80 st88
      SP AB count csz nf lo cks js shF F fc m mo mx ABL ABH AB16 CNT CSZ LCK PCL CKS STJ TJ NF0 NFB JSL RMX RNF RMFA RST FAJ SHF RLS
      ST LOIMG SPL SPH SPA AST SCS MI TP HK HJ HC.
    facts.
    dpose GSB as (SB0 & SBAL & HRI & RI1). dpose GT as (T0 & T1 & TAL). pose proof GCTX as (CX0 & CX1).
    dpose GSEP as (SEP1 & SEP2 & SEP3). dpose GMFA as (MF0 & MFAL & MF1).
    pose proof (max_count_range c ltac:(clear -GC; lia)) as MCR. subst mx.
    assert (HPC : PC = T + 208 + 80 * c) by reflexivity.
    assert (HR : R = RI + 128 * c) by reflexivity. assert (HRB : RB = SB + c * 2^32) by reflexivity.
    assert (HFA : FA = RB + 0xE0000000) by reflexivity. assert (HFAA : FAA = FA + mfa) by reflexivity.
    destruct (Z.lt_ge_cases count (max_count c)) as [FAST | FULL].
    - (* [comment removed for export] *)
      eapply (evtA_aevtS_KJ AL (CSf None None) (K None None)
                (lcd_push_post SP ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 T PC SB c count (max_count c) csz AB lo cks F fc m) Q _ mo (KL None None) HK); [exact HJ| |].
      { eapply evtA_cut.
        { eapply (lcd_fast AL IMG ALWF (CSf None None) (CSOKf None None)) with (T := T) (PC := PC) (c := c) (count := count) (max := max_count c) (lo := lo);
            first [exact PCL | exact ST | exact LOIMG | exact MI | exact HPC | apply CST
                  | eapply (crange_sub _ lo (SP - lo)); [exact SCS| clear -SPL; lia| clear -SPL; lia]
                  | clear -T0; lia | clear -T1; lia | exact GC | clear -CNT FAST; lia | clear -MCR; lia | clear -ABL ABH SB0 GC HRI RI1 HRB; lia
                  | clear -SPL; lia | exact SPH | exact AST
                  | match goal with |- ?G => idtac "RLF1-LEFTOVER" G end ]. }
        cbv beta. (intros ms1 dd_H; ddestruct dd_H as (x9 & a5' & m1 & LP & MU1 & WM1 & MI1 & PCL1 & FR1 & ST1)). red in LP. subst ms1.
        assert (DJ1 : forall A j, (A + j <= lo \/ SP <= A) -> disjoint_from [(lo, SP)] A j) by (intros A j H; cbn; clear -H; lia).
        eapply evtA_mono.
        { eapply (lcd_push AL IMG ALWF (CSf None None) (CSOKf None None)) with (T := T) (PC := PC) (SB := SB) (c := c) (count := count) (max := max_count c) (AB := AB) (lo := lo) (m0 := m);
            first [exact PCL1 | exact FR1 | exact ST1 | exact LOIMG | exact MI1 | exact HPC | exact LCK | apply CST | exact WM1
                  | eapply munch_weaken; [| exact MU1]; unfold sub_fp; cbn [outside]; clear; intros y Hy; lia
                  | eapply u32arr_transport; [exact CKS| exact MU1| exact WM1| rewrite LCK; apply DJ1; clear -T1 LOIMG GC HPC; lia]
                  | eapply rw_cells_transport; [exact STJ| exact MU1| exact WM1| apply DJ1; cbn; clear -T1 LOIMG; lia]
                  | ddestruct RLS as ((_ & _ & SBC) & _); eapply ro_cells_transport; [exact SBC| exact MU1| apply DJ1; unfold A_SPACEBEG_CELL, A_INSTANCE; cbn; clear -LOIMG; lia]
                  | exact (Z_to_bv 64 0)
                  | eapply (crange_sub _ lo (SP - lo)); [exact SCS| clear -SPL; lia| clear -SPL; lia]
                  | clear -T0; lia | clear -T1; lia | exact TAL | exact GC | clear -CNT FAST; lia | clear -MCR; lia | exact CSZ
                  | clear -SB0; lia | clear -SB0 HRI RI1; lia | clear -ABL HRB; lia | clear -ABH HRB; lia
                  | clear -SPL; lia | exact SPH | exact AST
                  | match goal with |- ?G => idtac "RLF-LEFTOVER" G end ]. }
        cbv beta. intros ms2 P2. exact P2. }
      cbn beta. intros ms2 mo2 P2 HK2 MM2 HJ2.
      ddestruct P2 as (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & m2 & stj' & -> & MU2 & WM2 & MI2 & PCL2 & CKS2 & STJ2 & ST2).
      apply HC. unfold rl_post. cbv beta.
      assert (DJ2 : forall A j, (A + j <= lo \/ SP <= A) -> (A + j <= PC \/ PC + 80 <= A) -> (A + j <= T + 2784 \/ T + 2792 <= A) ->
                    disjoint_from [(lo, SP); (PC, PC + 4); (PC + 16, PC + 80); (T + 2784, T + 2792)] A j) by (intros A j H1 H2 H3; cbn; clear -H1 H2 H3; repeat split; lia).
      assert (LO2 : forall A j, 0x10000 <= A /\ A + j <= 0x65f000 -> disjoint_from [(lo, SP); (PC, PC + 4); (PC + 16, PC + 80); (T + 2784, T + 2792)] A j)
        by (intros A j H; apply DJ2; clear -H LOIMG T0 HPC GC; lia).   (* [comment removed for export] *)
      eexists _, mo2, None, (count + 1), nf, _, js, stj', j1, j2, st80. deexists 16.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact HK2|]. split; [exact HJ2|]. split; [left; reflexivity|].
      split. { eapply munch_weaken; [| exact MU2]. clear. solve_sub_fp. }
      split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
      split. { eapply rl_statics_transport; [exact RLS| exact MU2| exact LO2| apply DJ2; clear -CX0 CX1 SEP2 LOIMG HPC GC; lia]. }
      split; [exact PCL2|]. split; [exact CKS2|]. split; [rewrite upd_length; exact LCK|]. split; [exact STJ2|].
      split. { eapply rw_cells_transport; [exact TJ| exact MU2| exact WM2| apply DJ2; cbn; clear -T1 LOIMG HPC GC; lia]. }
      assert (RD : forall A j, RI <= A -> A + j <= RI + 4096 -> disjoint_from [(lo, SP); (PC, PC + 4); (PC + 16, PC + 80); (T + 2784, T + 2792)] A j).
      { intros A j H1 H2. apply DJ2; clear -H1 H2 RI1 LOIMG SEP1 HRI HPC GC; lia. }
      split. { eapply rw_cells_transport; [exact RMX| exact MU2| exact WM2| apply RD; cbn; clear -HR GC; lia]. }
      split. { eapply rw_cells_transport; [exact RNF| exact MU2| exact WM2| apply RD; cbn; clear -HR GC; lia]. }
      split. { cbn [unit_if]. rewrite Z.add_0_r. eapply rw_cells_transport; [exact RMFA| exact MU2| exact WM2| apply RD; cbn; clear -HR GC; lia]. }
      split. { eapply rw_cells_transport; [exact RST| exact MU2| exact WM2| apply RD; cbn; clear -HR GC; lia]. }
      assert (FAD : forall A j, FA <= A -> A + j <= FA + 2^29 -> disjoint_from [(lo, SP); (PC, PC + 4); (PC + 16, PC + 80); (T + 2784, T + 2792)] A j).
      { intros A j H1 H2. apply DJ2; clear -H1 H2 HFA HRB HRI RI1 SEP1 LOIMG HPC GC SB0; lia. }
      split. { eapply u32arr_transport; [exact FAJ| exact MU2| exact WM2| apply FAD; clear -NF0 JSL MF1; lia]. }
      split. { cbn [unit_if]. rewrite Z.add_0_r. exact JSL. }
      split. { intros E; discriminate E. }
      assert (SHB : 0x20008fff000 <= 0x7fff8000 + FAA / 8 /\ 0x7fff8000 + FAA / 8 + 32768 <= 0x10007fff8000).
      { pose proof (Z.div_mod FAA 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound FAA 8 ltac:(clear; lia)). clear -H H0 HFAA HFA HRB HRI RI1 SB0 GC MF0 MF1. lia. }
      split. { intros _. cbn [unit_if] in *. eapply rw_cells_transport; [exact SHF| exact MU2| exact WM2| apply DJ2; cbn; clear -SHB LOIMG T0 HPC GC; lia]. }
      split. { intros E; discriminate E. }
      exists false, 0%nat. split; [split; [exact FAST| split; reflexivity]|]. split; [clear; lia|]. split; [clear; lia|].
      split; [rewrite Z.sub_0_r, HRB; change (2^32) with 4294967296; reflexivity|].
      split; [intros E; discriminate E|]. split; [intros _; split; reflexivity|]. cbn [unit_if]. clear; lia.
    - (* [comment removed for export] *)
      assert (CEQ : count = max_count c) by (clear -CNT FULL; lia). subst count. clear CNT FULL.
      set (mx := max_count c) in *. set (cnt := mx / 2) in *.
      assert (CNTB : 1 <= cnt <= 8 /\ 2 * cnt <= mx + 1 /\ cnt <= mx - cnt) by (subst cnt; clear -MCR; split; [| split]; [apply Z.div_le_lower_bound || idtac| |]; lia).
      (* [comment removed for export] *)
      eapply (evtA_aevtS_KJ AL (CSf None None) (K None None)
                (fun ms' => exists (a4' a5' a6' a7' x14 : word) (m' : mem) (j0 jr : list byte),
                   ms' = MS (rta_regs (SP + -112) (Z_to_bv 64 A_RTA_BACK) gp tp t0 t1 t2
                                      (Z_to_bv 64 A_INSTANCE) (Z_to_bv 64 R) (Z_to_bv 64 (SB + c * 4294967296)) (Z_to_bv 64 (nf + cnt)) a4' a5' a6' a7' t3 t4 t5 t6
                                      R c (SP + -104) (T + 2768) (PC + 16 + 4 * (mx - cnt)) nf cnt (SB + c * 4294967296 + 3758096384))
                            F (Z_to_bv 64 A_EFS) fc None m' (seg_rom asegs)
                   /\ munch [(lo, SP); (PC, PC + 4); (R, R + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                   /\ rw_cells asegs m' PC (pcl_cells (mx - cnt) mx csz) /\ lcd_frame m' SP s4 s3 s2 s1 s0 ra /\ lcdr_frame m' (SP + -48) j0 (Z_to_bv 64 A_LCD_BACK)
                   /\ rw_cells asegs m' R [C8 (Z_to_bv 64 kWriterLock)] /\ rw_cells asegs m' (R + 16) [C8 (Z_to_bv 64 nf)]
                   /\ rta_frame m' (SP + -112) jr R s11 s10 s9 s8 s7 s6 s5 (Z_to_bv 64 AB) (Z_to_bv 64 c) (Z_to_bv 64 A_INSTANCE) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 PC) (Z_to_bv 64 A_LCDR_BACK)
                   /\ stk asegs m' lo (SP + -112 + -128))
                Q _ mo (KL None None) HK); [exact HJ| |].
      { eapply evtA_cut.
        { eapply (lcd_drain AL IMG ALWF (CSf None None) (CSOKf None None)) with (T := T) (PC := PC) (c := c) (max := mx) (lo := lo);
            first [exact PCL | exact ST | exact LOIMG | exact MI | exact HPC | apply CST
                  | eapply (crange_sub _ lo (SP - lo)); [exact SCS| clear -SPL; lia| clear -SPL; lia]
                  | clear -T0; lia | clear -T1; lia | exact GC | clear -MCR; lia | clear -ABL ABH SB0 GC HRI RI1 HRB; lia
                  | clear -SPL; lia | exact SPH | exact AST
                  | match goal with |- ?G => idtac "RLD1-LEFTOVER" G end ]. }
        cbv beta. (intros ms1 dd_H; ddestruct dd_H as (x14 & m1 & -> & MU1 & WM1 & MI1 & PCL1 & FR1 & ST1)).
        assert (DJ1 : forall A j, (A + j <= lo \/ SP <= A) -> (A + j <= PC \/ PC + 4 <= A) -> disjoint_from [(lo, SP); (PC, PC + 4)] A j) by (intros A j H1 H2; cbn; clear -H1 H2; lia).
        (* [comment removed for export] *)
        eapply evtA_cut.
        { eapply (lcdr_A AL IMG ALWF (CSf None None) (CSOKf None None)) with (T := T) (PC := PC) (c := c) (max := mx) (lo := lo);
            first [exact PCL1 | exact ST1 | exact LOIMG | exact MI1 | exact HPC | apply CST
                  | eapply (crange_sub _ lo (SP - lo)); [exact SCS| clear -SPL; lia| clear -SPL; lia]
                  | clear -T0; lia | clear -T1; lia | exact GC | exact MCR
                  | clear -SPL; lia | clear -SPH; lia | clear -AST SPL; lia
                  | match goal with |- ?G => idtac "RLD2-LEFTOVER" G end ]. }
        cbv beta. (intros ms2 dd_H; ddestruct dd_H as (a6x & m2 & j0 & -> & MU2 & WM2 & MI2 & PCL2 & LFR2 & ST2)).
        replace (SP + -48 + -64) with (SP + -112) in * by (clear; lia). replace (SP + -48 + -56) with (SP + -104) in * by (clear; lia).
        assert (DJ2 : forall A j, (A + j <= lo \/ SP + -48 <= A) -> (A + j <= PC \/ PC + 4 <= A) -> disjoint_from [(lo, SP + -48); (PC, PC + 4)] A j) by (intros A j H1 H2; cbn; clear -H1 H2; lia).
        assert (MU12 : munch [(lo, SP); (PC, PC + 4)] m m2).
        { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; clear; intros y Hy; lia. }
        pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WM12.
        assert (RD2 : forall A j, RI <= A -> A + j <= RI + 4096 -> disjoint_from [(lo, SP); (PC, PC + 4)] A j) by (intros A j H1 H2; apply DJ1; clear -H1 H2 RI1 LOIMG SEP1 HRI HPC GC; lia).
        assert (RMX2 : rw_cells asegs m2 R [C8 (Z_to_bv 64 0)]) by (eapply rw_cells_transport; [exact RMX| exact MU12| exact WM12| apply RD2; cbn; clear -HR GC; lia]).
        assert (RNF2 : rw_cells asegs m2 (R + 16) [C8 (Z_to_bv 64 nf)]) by (eapply rw_cells_transport; [exact RNF| exact MU12| exact WM12| apply RD2; cbn; clear -HR GC; lia]).
        dpose RLS as ((INTV & PREM & SBC) & RIC & MWS & THS & POI & GS & GD & DY).
        assert (SBI : ro_cells asegs m A_SPACEBEG_CELL [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 4294967295)]).
        { change [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 4294967295)] with ([C8 (Z_to_bv 64 SB)] ++ [C4 (Z_to_bv 64 4294967295)]).
          apply ro_cells_join; [exact SBC|]. cbn [cells_size csize Nat.add]. unfold A_SPACEBEG_CELL. replace (A_INSTANCE + 32 + Z.of_nat 8) with A_INTERVAL by reflexivity. exact INTV. }
        assert (LO12 : forall A j, 0x10000 <= A /\ A + j <= 0x65f000 -> disjoint_from [(lo, SP); (PC, PC + 4)] A j) by (intros A j H; apply DJ1; clear -H LOIMG T0 HPC GC; lia).
        assert (SBI2 : ro_cells asegs m2 A_SPACEBEG_CELL [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 4294967295)]) by (eapply ro_cells_transport; [exact SBI| exact MU12| apply LO12; unfold A_SPACEBEG_CELL, A_INSTANCE; cbn; clear; lia]).
        assert (RIC2 : ro_cells asegs m2 A_RI_CELL [C8 (Z_to_bv 64 RI)]) by (eapply ro_cells_transport; [exact RIC| exact MU12| apply LO12; unfold A_RI_CELL, A_INSTANCE; cbn; clear; lia]).
        (* [comment removed for export] *)
        eapply evtA_mono.
        { eapply (rta_A AL IMG ALWF (CSf None None) (CSOKf None None)) with (SB := SB) (RI := RI) (R := R) (c := c) (nf := nf) (cnt := cnt) (lo := lo);
            first [exact SBI2 | exact RIC2 | exact RMX2 | exact RNF2 | exact ST2 | exact LOIMG | exact MI2 | exact SBAL | exact HRI | exact RI1 | exact GC | exact HR | exact NF0 | apply CSRI
                  | eapply (crange_sub _ lo (SP - lo)); [exact SCS| clear -SPL; lia| clear -SPL; lia]
                  | clear -SB0; lia | clear -NFB CNTB; lia | clear -CNTB; lia | clear -SPL LOIMG SPH; lia | clear -T0 T1 HPC GC MCR CNTB; lia
                  | clear -SPL; lia | clear -SPH; lia
                  | rewrite <- Zplus_mod_idemp_l, SPA; reflexivity
                  | match goal with |- ?G => idtac "RLD3-LEFTOVER" G end ]. }
        cbv beta. (intros ms3 dd_H; ddestruct dd_H as (a4' & a5' & a6' & a7' & m3 & jr & -> & MU3 & WM3 & MI3 & RMX3 & RNF3 & RFR3 & ST3)).
        assert (DJ3 : forall A j, (A + j <= lo \/ SP + -112 <= A) -> (A + j <= R \/ R + 8 <= A) -> disjoint_from [(lo, SP + -112); (R, R + 8)] A j) by (intros A j H1 H2; cbn; clear -H1 H2; lia).
        dexists a4', a5', a6', a7', x14, m3, j0, jr.
        split; [subst mx cnt; reflexivity|].
        split. { eapply munch_trans; [eapply munch_weaken; [| exact MU12]| eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; clear; intros y Hy; lia. }
        split; [eapply wmono_trans; [exact WM12| exact WM3]|]. split; [exact MI3|].
        split. { eapply rw_cells_transport; [exact PCL2| exact MU3| exact WM3| apply DJ3; cbn; clear -T0 T1 LOIMG HPC GC SEP1 HR HRI; lia]. }
        split. { unfold lcd_frame in *. eapply rw_cells_transport; [| exact MU3| exact WM3| apply DJ3; cbn; clear -SPL LOIMG HR HRI RI1 GC; lia].
                 eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2| apply DJ2; cbn; clear -T1 LOIMG HPC GC SPL; lia]. }
        split. { unfold lcdr_frame in *. eapply rw_cells_transport; [exact LFR2| exact MU3| exact WM3| apply DJ3; cbn; clear -SPL LOIMG HR HRI RI1 GC; lia]. }
        split; [exact RMX3|]. split; [exact RNF3|]. split; [exact RFR3| exact ST3]. }
      (* [comment removed for export] *)
      cbn beta. intros ms3 mo3 P3 HK3 MM3 HJ3.
      ddestruct P3 as (a4' & a5' & a6' & a7' & x14 & m3 & j0 & jr & -> & MU3 & WM3 & MI3 & PCL3 & FR3 & LFR3 & RMX3 & RNF3 & RFR3 & ST3).
      assert (DJ3 : forall A j, (A + j <= lo \/ SP <= A) -> (A + j <= PC \/ PC + 4 <= A) -> (A + j <= R \/ R + 8 <= A) -> disjoint_from [(lo, SP); (PC, PC + 4); (R, R + 8)] A j)
        by (intros A j H1 H2 H3; cbn; clear -H1 H2 H3; lia).
      assert (LO3 : forall A j, 0x10000 <= A /\ A + j <= 0x65f000 -> disjoint_from [(lo, SP); (PC, PC + 4); (R, R + 8)] A j) by (intros A j H; apply DJ3; clear -H LOIMG T0 HPC GC HR HRI SB0; lia).
      assert (RLS3 : rl_statics m3 SB RI CTX T) by (eapply rl_statics_transport; [exact RLS| exact MU3| exact LO3| apply DJ3; clear -CX0 CX1 LOIMG SEP2 SEP3 HPC GC HR HRI; lia]).
      dpose RLS3 as ((INTV3 & PREM3 & SBC3) & RIC3 & MWS3 & THS3 & POI3 & GS3 & GD3 & DY3).
      assert (RD3 : forall A j, RI <= A -> A + j <= RI + 4096 -> (A + j <= R \/ R + 8 <= A) -> disjoint_from [(lo, SP); (PC, PC + 4); (R, R + 8)] A j)
        by (intros A j H1 H2 H3; apply DJ3; clear -H1 H2 H3 RI1 LOIMG SEP1 HRI HPC GC; lia).
      assert (RMFA3 : rw_cells asegs m3 (R + 24) [C8 (Z_to_bv 64 mfa)]) by (eapply rw_cells_transport; [exact RMFA| exact MU3| exact WM3| apply RD3; cbn; clear -HR GC; lia]).
      assert (RST3 : rw_cells asegs m3 (R + 80) [C8 st80; C8 st88]) by (eapply rw_cells_transport; [exact RST| exact MU3| exact WM3| apply RD3; cbn; clear -HR GC; lia]).
      assert (SHB : 0x20008fff000 <= 0x7fff8000 + FAA / 8 /\ 0x7fff8000 + FAA / 8 + 32768 <= 0x10007fff8000).
      { pose proof (Z.div_mod FAA 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound FAA 8 ltac:(clear; lia)). clear -H H0 HFAA HFA HRB HRI RI1 SB0 GC MF0 MF1. lia. }
      assert (SHF3 : rw_cells asegs m3 (0x7fff8000 + FAA / 8) [CB (Z.to_nat 32768) shF]) by (eapply rw_cells_transport; [exact SHF| exact MU3| exact WM3| apply DJ3; cbn; clear -SHB LOIMG T0 HPC GC HR HRI SB0; lia]).
      assert (TJ3 : rw_cells asegs m3 (T + 2872) [C8 j1; C8 j2]) by (eapply rw_cells_transport; [exact TJ| exact MU3| exact WM3| apply DJ3; cbn; clear -T1 LOIMG HPC GC SEP1 HR HRI; lia]).
      assert (FAD3 : forall A j, FA <= A -> A + j <= FA + 2^29 -> disjoint_from [(lo, SP); (PC, PC + 4); (R, R + 8)] A j).
      { intros A j H1 H2. apply DJ3; clear -H1 H2 HFA HRB HR HRI RI1 SEP1 LOIMG HPC GC SB0; lia. }
      assert (FAJ3 : u32arr asegs m3 (FA + 4 * nf) js) by (eapply u32arr_transport; [exact FAJ| exact MU3| exact WM3| apply FAD3; clear -NF0 JSL MF1; lia]).
      assert (CKS3 : u32arr asegs m3 (PC + 16) cks) by (eapply u32arr_transport; [exact CKS| exact MU3| exact WM3| rewrite LCK; apply DJ3; clear -T1 LOIMG HPC GC SEP1 HR HRI; lia]).
      assert (STJ3 : rw_cells asegs m3 (T + 2784) [C8 stj]) by (eapply rw_cells_transport; [exact STJ| exact MU3| exact WM3| apply DJ3; cbn; clear -T1 LOIMG HPC GC SEP1 HR HRI; lia]).
      clear RMX RNF RMFA RST SHF TJ FAJ CKS STJ PCL ST MI RLS.
      assert (GC31 : 1 <= c <= 31) by (clear -GC; lia).
      eapply (efs_cfgS AL IMG ALWF CSf CSOKf CSmono_f ASB T CTX SB RI c GSB GC31 GT GCTX GSEP CST CSCTX CSRI K KL 0 mfa
                LEDGER_F TF_commit TF_fresh GMFA CSFz ROOM_F SCAR_F Q None) with (tot := nf + cnt) (lo := lo);
        first [exact RMFA3 | exact SHF3 | exact TJ3 | exact POI3 | exact THS3 | exact MWS3 | exact PREM3 | exact ST3 | exact LOIMG | exact MI3 | exact TP | exact HK3 | exact HJ3
              | left; reflexivity
              | eapply (crange_sub _ lo (SP - lo)); [exact SCS| clear -SPL; lia| clear -SPL; lia]
              | clear -NF0 CNTB; lia | clear -JSL CNTB; lia | clear -SPL; lia | clear -SPH; lia
              | replace (SP + -112 + -128) with (SP + (-15) * 16) by (clear; lia); rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by (clear; lia); exact SPA
              | idtac ].
      (* [comment removed for export] *)
      intros ok c4 P4.
      ddestruct P4 as (ms4 & mo4 & res & f & y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m4 & j1' & j2' & -> & -> &
                      MU4 & WM4 & MI4 & ST4 & HK4 & HJ4 & POI4 & THS4 & MWS4 & PREM4 & RMFA4 & TJ4 & NEWF & OLDF & ZLT & RES).
      change (SB + c * 2 ^ 32 + 3758096384 + mfa) with FAA in MU4. change (SB + c * 2 ^ 32 + 3758096384 + mfa) with FAA in NEWF.
      change (SB + c * 2 ^ 32 + 3758096384 + mfa) with FAA in OLDF.
      change (RI + 128 * c) with R in MU4. change (RI + 128 * c) with R in RMFA4.
      change (2 ^ 18) with 262144 in MU4. change (2 ^ 18) with 262144 in NEWF.
      replace (ret_pc (Z_to_bv 64 A_RTA_BACK)) with (Z_to_bv 64 A_RTA_BACK) by (symmetry; apply ret_pc_even; [clear; unfold A_RTA_BACK; lia | reflexivity]).
      replace (Z_to_bv 64 (SB + c * 4294967296 + 3758096384)) with (Z_to_bv 64 FA) by (rewrite HFA, HRB; f_equal; clear; lia).
      assert (INCf : forall y, CSf None None y -> CSf None f y) by (destruct f as [b|]; [intros y Hy; apply CSmono_f; exact Hy| intros y Hy; exact Hy]).
      assert (SCSf : crange (CSf None f) lo (SP - lo)) by (eapply crange_imp; [exact INCf| exact SCS]).
      assert (DJ4 : forall A n, (A + n <= lo \/ SP + -112 + -128 <= A) -> (A + n <= FAA \/ FAA + 262144 <= A) ->
                    (A + n <= 0x7fff8000 + FAA / 8 \/ 0x7fff8000 + FAA / 8 + 32768 <= A) -> (A + n <= T + 2872 \/ T + 2888 <= A) -> (A + n <= R + 24 \/ R + 32 <= A) ->
                    disjoint_from [(lo, SP + -112 + -128); (FAA, FAA + 262144); (0x7fff8000 + FAA / 8, 0x7fff8000 + FAA / 8 + 32768); (T + 2872, T + 2888); (R + 24, R + 32)] A n)
        by (intros A n H1 H2 H3 H4 H5; cbn; clear -H1 H2 H3 H4 H5; repeat split; lia).
      assert (TR4 : forall A cs0, rw_cells asegs m3 A cs0 ->
                (A + Z.of_nat (cells_size cs0) <= lo \/ SP + -112 + -128 <= A) -> (A + Z.of_nat (cells_size cs0) <= FAA \/ FAA + 262144 <= A) ->
                (A + Z.of_nat (cells_size cs0) <= 0x7fff8000 + FAA / 8 \/ 0x7fff8000 + FAA / 8 + 32768 <= A) ->
                (A + Z.of_nat (cells_size cs0) <= T + 2872 \/ T + 2888 <= A) -> (A + Z.of_nat (cells_size cs0) <= R + 24 \/ R + 32 <= A) ->
                rw_cells asegs m4 A cs0)
        by (intros A cs0 H H1 H2 H3 H4 H5; eapply rw_cells_munch; [exact H| exact MU4| apply DJ4; assumption]).
      assert (LO4 : forall A j, 0x10000 <= A /\ A + j <= 0x65f000 -> disjoint_from [(lo, SP + -112 + -128); (FAA, FAA + 262144); (0x7fff8000 + FAA / 8, 0x7fff8000 + FAA / 8 + 32768); (T + 2872, T + 2888); (R + 24, R + 32)] A j)
        by (intros A j H; apply DJ4; clear -H LOIMG T0 HR HRI SB0 HFAA HFA HRB GC MF0 SHB; lia).
      (* [comment removed for export] *)
      assert (GS4 : ro_cells asegs m4 A_GOT_SEALED2 [C8 (Z_to_bv 64 1)]) by (eapply ro_cells_transport; [exact GS3| exact MU4| apply LO4; unfold A_GOT_SEALED2; cbn; clear; lia]).
      assert (GD4 : ro_cells asegs m4 A_GOT_DYING [C8 (Z_to_bv 64 A_DYING)]) by (eapply ro_cells_transport; [exact GD3| exact MU4| apply LO4; unfold A_GOT_DYING; cbn; clear; lia]).
      assert (DY4 : ro_cells asegs m4 A_DYING [C4 (Z_to_bv 64 0)]) by (eapply ro_cells_transport; [exact DY3| exact MU4| apply LO4; unfold A_DYING; cbn; clear; lia]).
      destruct ok; hnf in RES.
      + (* [comment removed for export] *)
        ddestruct RES as (-> & Hf & HTOT).
        assert (HF2 : f = None \/ f = Some true) by (destruct f as [[|]|]; [right; reflexivity| exfalso; apply Hf; reflexivity| left; reflexivity]).
        assert (UF : 0 <= unit_if f <= 262144 /\ unit_if f mod 4 = 0) by (destruct f as [[|]|]; cbn [unit_if]; clear; (split; [lia| reflexivity])).
        destruct UF as [UF UF4].
        assert (CSFAf : crange (CSf None f) (FA + 4 * nf) (mfa + unit_if f - 4 * nf)).
        { intros y Hy. destruct f as [[|]|]; cbn [unit_if] in Hy.
          - destruct (Z_lt_le_dec y (FA + mfa)); [apply INCf; apply CSFA; clear - Hy l NF0; lia| apply (CSFz None); rewrite HFAA; clear - Hy l NF0; lia].
          - apply INCf; apply CSFA; clear - Hy NF0; lia.
          - apply CSFA; clear - Hy NF0; lia. }
        (* [comment removed for export] *)
        assert (FAJ4 : u32arr asegs m4 (FA + 4 * nf) js).
        { eapply u32arr_munch; [exact FAJ3| exact MU4|]. apply DJ4; clear - SPL LOIMG HFAA HFA HRB JSL SB0 GC MF0 MF1 NF0 T0 T1 HR HRI RI1 SEP1 SHB; lia. }
        assert (ALL : exists all, u32arr asegs m4 (FA + 4 * nf) all /\ 4 * (nf + Z.of_nat (length all)) = mfa + unit_if f).
        { destruct f as [[|]|].
          - destruct (NEWF eq_refl) as [ZB _]. exists (js ++ repeat (Z_to_bv 64 0) (Z.to_nat 65536)). split.
            + apply u32arr_app. split; [exact FAJ4|]. replace (FA + 4 * nf + 4 * Z.of_nat (length js)) with FAA by (rewrite HFAA; clear -JSL; lia).
              apply u32arr_zeros; [clear; lia|]. exact ZB.
            + rewrite app_length, repeat_length. cbn [unit_if]. clear -JSL; lia.
          - exfalso; apply Hf; reflexivity.
          - exists js. split; [exact FAJ4|]. cbn [unit_if]. clear -JSL; lia. }
        clear FAJ4. ddestruct ALL as (all & HALL & LALL).
        assert (LCNT : (Z.to_nat cnt <= length all)%nat) by (clear - LALL HTOT NF0 NFB CNTB UF; lia).
        (* [comment removed for export] *)
        assert (CKS4 : u32arr asegs m4 (PC + 16) cks).
        { eapply u32arr_munch; [exact CKS3| exact MU4|]. rewrite LCK. apply DJ4; clear - AST LOIMG HPC GC T0 T1 SEP1 HR HRI RI1 SB0 HFAA HFA HRB MF0 MF1 SHB; lia. }
        pose proof (u32arr_window m4 (PC + 16) cks (Z.to_nat (mx - cnt)) (Z.to_nat cnt) CKS4 ltac:(rewrite LCK; clear -CNTB MCR; lia)) as WS4.
        replace (PC + 16 + 4 * Z.of_nat (Z.to_nat (mx - cnt))) with (PC + 16 + 4 * (mx - cnt)) in WS4 by (clear -CNTB; lia).
        fold (top_half cks mx cnt) in WS4.
        assert (LWS : length (top_half cks mx cnt) = Z.to_nat cnt) by (unfold top_half; rewrite firstn_length_le; [reflexivity| rewrite skipn_length, LCK; clear -CNTB MCR; lia]).
        assert (SBI4 : ro_cells asegs m4 A_SPACEBEG_CELL [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 4294967295)]).
        { change [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 4294967295)] with ([C8 (Z_to_bv 64 SB)] ++ [C4 (Z_to_bv 64 4294967295)]).
          apply ro_cells_join.
          - eapply ro_cells_transport; [exact SBC3| exact MU4| apply LO4; unfold A_SPACEBEG_CELL, A_INSTANCE; cbn; clear; lia].
          - cbn [cells_size csize Nat.add]. replace (A_SPACEBEG_CELL + Z.of_nat 8) with A_INTERVAL by reflexivity.
            eapply ro_cells_transport; [exact INTV3| exact MU4| apply LO4; unfold A_INTERVAL, A_INSTANCE; cbn; clear; lia]. }
        assert (RIC4 : ro_cells asegs m4 A_RI_CELL [C8 (Z_to_bv 64 RI)]) by (eapply ro_cells_transport; [exact RIC3| exact MU4| apply LO4; unfold A_RI_CELL, A_INSTANCE; cbn; clear; lia]).
        pose proof RFR3 as RFR4. unfold rta_frame in RFR4.
        apply TR4 in RFR4; [| cbn; clear; lia | cbn; clear -SPL LOIMG HFAA HFA HRB SB0 GC MF0 MF1 HRI RI1; lia | cbn; clear -SPL LOIMG SHB; lia
                           | cbn; clear -SPL AST HPC GC; lia | cbn; clear -SPL LOIMG HR HRI RI1 GC; lia ].
        (* [comment removed for export] *)
        eapply (evtA_aevtS_KJ AL (CSf None f) (K None f)
                  (fun ms' => exists (e0 e1 e2 e3 e4 e5 e6 : word) (m6 : mem),
                     munch [(lo, SP + -48); (R, R + 8); (R + 16, R + 24); (R + 80, R + 88); (FA + 4 * nf, FA + 4 * nf + 4 * cnt)] m4 m6
                     /\ wmono asegs m4 m6
                     /\ rw_cells asegs m6 R [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m6 (R + 16) [C8 (Z_to_bv 64 (nf + cnt))]
                     /\ rw_cells asegs m6 (R + 80) [C8 (Z_to_bv 64 (bv_unsigned st80 + cnt)); C8 st88]
                     /\ u32arr asegs m6 (FA + 4 * nf) (cpy (Z.to_nat cnt) (top_half cks mx cnt) all)
                     /\ lcd_push_post SP ra gp tp e0 e1 e2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 e3 e4 e5 e6 T PC SB c (mx - cnt) mx csz AB lo cks F fc m6 ms')
                  Q _ mo4 (KL None f) HK4); [exact HJ4| |].
        { eapply evtA_cut.
          { eapply (rta_B AL IMG ALWF (CSf None f) (CSOKf None f)) with (SB := SB) (RI := RI) (nf := nf) (cnt := cnt) (STK := 0) (lo := lo)
                     (ws := top_half cks mx cnt) (ds := all) (m0 := m4) (st80 := st80) (st88 := st88) (j0 := jr).
            all: lazymatch goal with
                 | |- evtA _ _ _ _ _ => idtac
                 | |- _ mod 4096 = 0 => exact SBAL
                 | |- RI = _ => clear -HRI; lia
                 | |- RI + 4096 <= _ => exact RI1
                 | |- 1 <= c <= 30 => exact GC
                 | |- R = _ => exact HR
                 | |- FA = _ => clear -HFA HRB; lia
                 | |- length _ = _ => exact LWS
                 | |- crange _ RI _ => apply CSRI
                 | |- crange _ (PC + 16 + _) _ => eapply crange_sub; [apply CST| clear -HPC GC CNTB MCR; lia| clear -HPC GC CNTB MCR; lia]
                 | |- crange _ (FA + 4 * _) _ => eapply crange_sub; [exact CSFAf| clear; lia| clear -HTOT CNTB NF0; lia]
                 | |- crange _ _ _ => eapply crange_sub; [exact SCSf| clear; lia| clear -SPL; lia]
                 | |- u32arr _ _ (PC + 16 + _) _ => exact WS4
                 | |- u32arr _ _ (FA + _) _ => exact HALL
                 | |- rw_cells _ _ R _ => apply (TR4 _ _ RMX3); cbn; clear -SPL LOIMG HFAA HFA HRB SB0 GC MF0 MF1 T0 T1 HR HRI RI1 SEP1 SHB; lia
                 | |- rw_cells _ _ (R + 16) _ => apply (TR4 _ _ RNF3); cbn; clear -SPL LOIMG HFAA HFA HRB SB0 GC MF0 MF1 T0 T1 HR HRI RI1 SEP1 SHB; lia
                 | |- rw_cells _ _ (R + 80) _ => apply (TR4 _ _ RST3); cbn; clear -SPL LOIMG HFAA HFA HRB SB0 GC MF0 MF1 T0 T1 HR HRI RI1 SEP1 SHB; lia
                 | |- rw_cells _ _ _ _ => exact RFR4
                 | |- ro_cells _ _ A_GOT_PAGESZ _ => exact (proj1 MWS4)
                 | |- ro_cells _ _ A_PAGESZ_CELL _ => exact (proj1 (proj2 MWS4))
                 | |- ro_cells _ _ A_SPACEBEG_CELL _ => exact SBI4
                 | |- ro_cells _ _ A_RI_CELL _ => exact RIC4
                 | |- rta_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold rta_frame; exact RFR4
                 | |- stk _ _ _ _ => exact ST4
                 | |- _ mod 16 = 0 => replace (SP + -112) with (SP + (-7) * 16) by (clear; lia); rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by (clear; lia); exact SPA
                 | |- munch _ _ _ => apply munch_refl
                 | |- wmono _ _ _ => apply wmono_refl
                 | |- mem_inv _ _ => exact MI4
                 | |- _ => clear - SPL SPH LOIMG AST HPC GC T0 T1 SEP1 HR HRI RI1 SB0 HFAA HFA HRB MF0 MF1 NF0 NFB CNTB MCR LALL LCNT UF HTOT; lia
                 end. }
          cbv beta. (intros ms5 dd_H; ddestruct dd_H as (e0 & e1 & e2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & e3 & e4 & e5 & e6 & m5 & -> & MU5 & WM5 & MI5 & RMX5 & RNF5 & RST5 & CPY5 & ST5)).
          replace (ret_pc (Z_to_bv 64 A_LCDR_BACK)) with (Z_to_bv 64 A_LCDR_BACK) by (symmetry; apply ret_pc_even; [clear; unfold A_LCDR_BACK; lia | reflexivity]).
          replace (Z_to_bv 64 (SP + -112)) with (Z_to_bv 64 (SP + -48 + -64)) by (f_equal; clear; lia).
          assert (DJ5 : forall A n, (A + n <= lo \/ SP + -112 <= A) -> (A + n <= R \/ R + 88 <= A) -> (A + n <= FA + 4 * nf \/ FA + 4 * nf + 4 * cnt <= A) ->
                        disjoint_from [(lo, SP + -112); (R, R + 8); (R + 16, R + 24); (R + 80, R + 88); (FA + 4 * nf, FA + 4 * nf + 4 * cnt)] A n)
            by (intros A n H1 H2 H3; cbn; clear -H1 H2 H3; repeat split; lia).
          (* [comment removed for export] *)
          eapply evtA_cut.
          { eapply (lcdr_B AL IMG ALWF (CSf None f) (CSOKf None f)) with (lo := lo) (m0 := m5) (W := []) (j0 := j0).
            all: lazymatch goal with
                 | |- evtA _ _ _ _ _ => idtac
                 | |- lcdr_frame _ _ _ _ => unfold lcdr_frame in LFR3 |- *; eapply rw_cells_munch; [apply (TR4 _ _ LFR3)| exact MU5| apply DJ5]; cbn;
                                              clear -SPL LOIMG HFAA HFA HRB SB0 GC MF0 MF1 NF0 NFB CNTB T0 T1 HR HRI RI1 SEP1 SHB AST HPC; lia
                 | |- stk _ _ _ _ => replace (SP + -48 + -64) with (SP + -112) by (clear; lia); exact ST5
                 | |- munch _ _ _ => apply munch_refl
                 | |- wmono _ _ _ => apply wmono_refl
                 | |- mem_inv _ _ => exact MI5
                 | |- crange _ _ _ => eapply crange_sub; [exact SCSf| clear; lia| clear -SPL; lia]
                 | |- _ => clear - SPL SPH LOIMG; lia
                 end. }
          cbv beta. (intros ms6 dd_H; ddestruct dd_H as (g0 & g1 & g2 & m6 & -> & MU6 & WM6 & MI6 & ST6)).
          replace (ret_pc (Z_to_bv 64 A_LCD_BACK)) with (Z_to_bv 64 A_LCD_BACK) by (symmetry; apply ret_pc_even; [clear; unfold A_LCD_BACK; lia | reflexivity]).
          assert (MU46 : munch [(lo, SP + -48); (R, R + 8); (R + 16, R + 24); (R + 80, R + 88); (FA + 4 * nf, FA + 4 * nf + 4 * cnt)] m4 m6).
          { eapply munch_trans; [eapply munch_weaken; [| exact MU5]| eapply munch_weaken; [| exact MU6]]; clear; solve_sub_fp. }
          assert (DJ6 : forall A n, (A + n <= lo \/ SP + -48 <= A) -> disjoint_from [(lo, SP + -48)] A n) by (intros A n H1; cbn; clear -H1; lia).
          assert (PCL6 : rw_cells asegs m6 PC (pcl_cells (mx - cnt) mx csz)).
          { eapply rw_cells_munch; [| exact MU46|]. { apply (TR4 _ _ PCL3); cbn; clear -SPL LOIMG HFAA HFA HRB SB0 GC MF0 MF1 T0 T1 HR HRI RI1 SEP1 SHB AST HPC; lia. }
            cbn. clear -SPL LOIMG HFAA HFA HRB SB0 GC MF0 MF1 NF0 NFB CNTB T0 T1 HR HRI RI1 SEP1 AST HPC. repeat split; lia. }
          (* [comment removed for export] *)
          eapply evtA_cut.
          { eapply (lcd_back AL IMG ALWF (CSf None f) (CSOKf None f)) with (T := T) (c := c) (count := mx - cnt) (max := mx) (csz := csz);
              first [exact PCL6 | exact MI6 | exact HPC | exact GC | apply CST | clear -T0; lia | clear -T1; lia | clear -CNTB MCR; lia
                    | match goal with |- ?G => idtac "RLD6-LEFTOVER" G end ]. }
          cbv beta. intros ms7 LP. red in LP. subst ms7.
          (* [comment removed for export] *)
          eapply evtA_mono.
          { eapply (lcd_push AL IMG ALWF (CSf None f) (CSOKf None f)) with (T := T) (PC := PC) (SB := SB) (c := c) (count := mx - cnt) (max := mx) (AB := AB) (lo := lo) (m0 := m6) (cks := cks) (stj := stj).
            all: lazymatch goal with
                 | |- evtA _ _ _ _ _ => idtac
                 | |- T mod 4096 = 0 => exact TAL
                 | |- 1 <= c <= 30 => exact GC
                 | |- PC = _ => exact HPC
                 | |- length _ = _ => exact LCK
                 | |- rw_cells _ _ PC _ => exact PCL6
                 | |- u32arr _ _ _ _ => eapply u32arr_munch; [exact CKS4| exact MU46|]; rewrite LCK; cbn;
                                           clear -SPL LOIMG HFAA HFA HRB SB0 GC MF0 MF1 NF0 NFB CNTB T0 T1 HR HRI RI1 SEP1 AST HPC; repeat split; lia
                 | |- rw_cells _ _ (T + 2784) _ => eapply rw_cells_munch; [apply (TR4 _ _ STJ3)| exact MU46|]; cbn;
                                           clear -SPL LOIMG HFAA HFA HRB SB0 GC MF0 MF1 NF0 NFB CNTB T0 T1 HR HRI RI1 SEP1 SHB AST HPC; repeat split; lia
                 | |- crange _ T _ => apply CST
                 | |- ro_cells _ _ A_SPACEBEG_CELL _ => eapply ro_cells_transport; [| exact MU46|];
                                           [ eapply ro_cells_transport; [exact SBC3| exact MU4| apply LO4; unfold A_SPACEBEG_CELL, A_INSTANCE; cbn; clear; lia]
                                           | cbn; unfold A_SPACEBEG_CELL, A_INSTANCE; clear -LOIMG HR HRI SB0 HFA HRB GC NF0; repeat split; lia ]
                 | |- lcd_frame _ _ _ _ _ _ _ _ => unfold lcd_frame in FR3 |- *; eapply rw_cells_munch; [apply (TR4 _ _ FR3)| exact MU46|]; cbn;
                                           clear -SPL LOIMG HFAA HFA HRB SB0 GC MF0 MF1 NF0 NFB CNTB T0 T1 HR HRI RI1 SEP1 SHB AST HPC; repeat split; lia
                 | |- stk _ _ _ _ => exact ST6
                 | |- munch _ _ _ => apply munch_refl
                 | |- wmono _ _ _ => apply wmono_refl
                 | |- mem_inv _ _ => exact MI6
                 | |- crange _ _ _ => exact SCSf
                 | |- word => exact (Z_to_bv 64 0)
                 | |- _ => first [exact CSZ | exact AST | clear - SPL SPH LOIMG AST HPC GC T0 T1 SEP1 HR HRI RI1 SB0 HFAA HFA HRB MF0 MF1 NF0 NFB CNTB MCR ABL ABH; lia]
                 end. }
          cbv beta. intros ms8 P8. dexists e0, e1, e2, e3, e4, e5, e6, m6.
          split; [exact MU46|]. split; [exact (wmono_trans asegs _ _ _ WM5 WM6)|].
          split. { eapply rw_cells_munch; [exact RMX5| exact MU6| apply DJ6; cbn; clear -SPL LOIMG HR HRI RI1 GC; lia]. }
          split. { eapply rw_cells_munch; [exact RNF5| exact MU6| apply DJ6; cbn; clear -SPL LOIMG HR HRI RI1 GC; lia]. }
          split. { eapply rw_cells_munch; [exact RST5| exact MU6| apply DJ6; cbn; clear -SPL LOIMG HR HRI RI1 GC; lia]. }
          split. { eapply u32arr_munch; [exact CPY5| exact MU6| apply DJ6]. rewrite cpy_length by (rewrite ?LWS; clear -LCNT; lia).
                   clear -SPL LOIMG HFA HRB HRI RI1 SB0 GC NF0 LALL MF1 UF; lia. }
          exact P8. }
        (* [comment removed for export] *)
        cbn beta. intros ms8 mo8 P8 HK8 MM8 HJ8.
        ddestruct P8 as (e0 & e1 & e2 & e3 & e4 & e5 & e6 & m6 & MU46 & WM46 & RMX6 & RNF6 & RST6 & CPY6
                        & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & m7 & stj' & -> & MU7 & WM7 & MI7 & PCL7 & CKS7 & STJ7 & ST7).
        assert (DJ7 : forall A n, (A + n <= lo \/ SP <= A) -> (A + n <= PC \/ PC + 80 <= A) -> (A + n <= T + 2784 \/ T + 2792 <= A) ->
                      disjoint_from [(lo, SP); (PC, PC + 4); (PC + 16, PC + 80); (T + 2784, T + 2792)] A n)
          by (intros A n H1 H2 H3; cbn; clear -H1 H2 H3; repeat split; lia).
        assert (MU47 : munch [(lo, SP); (PC, PC + 4); (PC + 16, PC + 80); (T + 2784, T + 2792); (R, R + 8); (R + 16, R + 24); (R + 80, R + 88); (FA + 4 * nf, FA + 4 * nf + 4 * cnt)] m4 m7).
        { eapply munch_trans; [eapply munch_weaken; [| exact MU46]| eapply munch_weaken; [| exact MU7]]; clear; solve_sub_fp. }
        assert (DJ47 : forall A n, (A + n <= lo \/ SP <= A) -> (A + n <= PC \/ PC + 80 <= A) -> (A + n <= T + 2784 \/ T + 2792 <= A) ->
                       (A + n <= R \/ R + 88 <= A) -> (A + n <= FA + 4 * nf \/ FA + 4 * nf + 4 * cnt <= A) ->
                       disjoint_from [(lo, SP); (PC, PC + 4); (PC + 16, PC + 80); (T + 2784, T + 2792); (R, R + 8); (R + 16, R + 24); (R + 80, R + 88); (FA + 4 * nf, FA + 4 * nf + 4 * cnt)] A n)
          by (intros A n H1 H2 H3 H4 H5; cbn; clear -H1 H2 H3 H4 H5; repeat split; lia).
        assert (MU37 : munch [(lo, SP); (PC, PC + 4); (PC + 16, PC + 80); (T + 2784, T + 2792); (T + 2872, T + 2888);
                              (R, R + 8); (R + 16, R + 32); (R + 80, R + 88); (FA + 4 * nf, FA + 4 * nf + 4 * cnt);
                              (FAA, FAA + 262144); (0x7fff8000 + FAA / 8, 0x7fff8000 + FAA / 8 + 32768)] m3 m7).
        { eapply munch_trans; [eapply munch_weaken; [| exact MU4]| eapply munch_weaken; [| exact MU47]]; clear; solve_sub_fp. }
        apply HC. unfold rl_post. cbv beta.
        eexists _, mo8, f, (mx - cnt + 1), (nf + cnt), _, (skipn (Z.to_nat cnt) all), stj', j1', j2', (Z_to_bv 64 (bv_unsigned st80 + cnt)). deexists 16.
        split; [reflexivity|]. split; [reflexivity|]. split; [exact HK8|]. split; [exact HJ8|]. split; [exact HF2|].
        split. { change (2^18) with 262144. eapply munch_trans; [eapply munch_weaken; [| exact MU3]| exact MU37]. clear; solve_sub_fp. }
        split; [exact (wmono_trans asegs _ _ _ WM3 (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM46 WM7)))|].
        split; [exact MI7|]. split; [exact ST7|].
        split. { eapply rl_statics_transport; [exact RLS3| exact MU37| |].
                 - intros A n H. cbn. clear -H LOIMG T0 HPC GC HR HRI SB0 HFAA HFA HRB MF0 NF0 SHB. repeat split; lia.
                 - cbn. clear -CX0 CX1 LOIMG SEP2 SEP3 HPC GC HR HRI RI1 SB0 HFAA HFA HRB MF0 MF1 NF0 NFB CNTB SHB. repeat split; lia. }
        split; [exact PCL7|]. split; [exact CKS7|]. split; [rewrite upd_length; exact LCK|]. split; [exact STJ7|].
        split. { eapply rw_cells_munch; [apply TJ4| exact MU47|]. cbn. clear -SPL LOIMG T1 HPC GC SEP1 HR HRI RI1 SB0 HFA HRB NF0 NFB CNTB MF1 LALL HTOT UF; repeat split; lia. }
        split. { eapply rw_cells_munch; [exact RMX6| exact MU7| apply DJ7; cbn; clear -LOIMG HPC GC T1 SEP1 HR HRI RI1; lia]. }
        split. { eapply rw_cells_munch; [exact RNF6| exact MU7| apply DJ7; cbn; clear -LOIMG HPC GC T1 SEP1 HR HRI RI1; lia]. }
        split. { eapply rw_cells_munch; [apply RMFA4| exact MU47|]. cbn. clear -SPL LOIMG T1 HPC GC SEP1 HR HRI RI1 SB0 HFA HRB NF0 NFB CNTB MF1 LALL HTOT UF; repeat split; lia. }
        split. { eapply rw_cells_munch; [exact RST6| exact MU7| apply DJ7; cbn; clear -LOIMG HPC GC T1 SEP1 HR HRI RI1; lia]. }
        (* [comment removed for export] *)
        pose proof CPY6 as CP. unfold cpy in CP. apply u32arr_app in CP. destruct CP as [CP1 CP2].
        rewrite firstn_all2 in CP1, CP2 by (rewrite LWS; clear; lia). rewrite map_length, LWS, Z2Nat.id in CP2 by (clear -CNTB; lia).
        split. { replace (FA + 4 * (nf + cnt)) with (FA + 4 * nf + 4 * cnt) by (clear; lia).
                 eapply u32arr_munch; [exact CP2| exact MU7| apply DJ7]; rewrite skipn_length; clear -LOIMG HPC GC T1 SEP1 HR HRI RI1 SB0 HFA HRB NF0 NFB CNTB LALL LCNT MF1 UF; lia. }
        split. { rewrite skipn_length. clear -LALL LCNT CNTB; lia. }
        split. { intros ->. destruct (NEWF eq_refl) as [_ SHN]. eapply rw_cells_munch; [exact SHN| exact MU47|]. cbn.
                 clear -SPL LOIMG T0 HPC GC HR HRI SB0 HFA HRB NF0 SHB. repeat split; lia. }
        split. { intros Hn. eapply rw_cells_munch; [exact (OLDF Hn)| exact MU47|]. cbn.
                 clear -SPL LOIMG T0 HPC GC HR HRI SB0 HFA HRB NF0 SHB. repeat split; lia. }
        split. { exact ZLT. }
        exists true, (Z.to_nat cnt). rewrite Z2Nat.id by (clear -CNTB; lia).
        split; [split; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [rewrite HRB; change (2^32) with 4294967296; reflexivity|].
        split. { intros _. split; [reflexivity|].
                 eapply u32arr_munch; [exact CP1| exact MU7| apply DJ7]; rewrite map_length, LWS; clear -LOIMG HPC GC T1 SEP1 HR HRI RI1 SB0 HFA HRB NF0 NFB CNTB MF1 UF; lia. }
        split; [intros E; discriminate E|].
        rewrite skipn_length. clear -LALL LCNT CNTB JSL UF UF4; nia.
      + (* [comment removed for export] *)
        destruct RES as (-> & ->). cbn [orS]. right.
        eapply (evtA_spinJ_K asegs AL (CSf None None) (K None None) _ _ mo4 (KL None None) HK4).
        { eapply (rta_spin AL IMG ALWF (CSf None None) (CSOKf None None)) with (lo := lo);
            first [exact GS4 | exact GD4 | exact DY4 | exact ST4 | exact LOIMG | exact MI4
                  | eapply crange_sub; [exact SCS| clear; lia| clear -SPL; lia]
                  | clear -SPL SPH LOIMG; lia ]. }
        cbn beta. (intros ms5 mo5 dd_H; ddestruct dd_H as (r' & F' & mm' & ->); intros HK5 _). apply spinningJ_at; [cbn; repeat (first [left; reflexivity | right])| exact (ki_halted (KL None None) mo5 HK5)].   (* [comment removed for export] *)
  Qed.
End RecLC.

End ARUN_1.
