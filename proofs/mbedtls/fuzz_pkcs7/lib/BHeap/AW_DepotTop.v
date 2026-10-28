(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Arr Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import DivergeSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed AKinv AJ AKinvS ASpinS AW_MmapAnon AW_MmapDie ASpin
     AW_DepotA AW_DepotB AW_DepotC AW_DepotD AW_DepotE AW_DepotF AW_DepotCfg AW_DepotInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_DepotTop () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotF.dstatics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotCfg.cstatics"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_MUR1"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_MUR2"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_MUR3"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dblk"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotC.sblk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_DEP_N"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dtab"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dmap1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dnodes"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dwf"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_DEP_NODES"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_SS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotC.dblocks"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotInv.sblks"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.sub"; "ARUN_1.blocks_apart"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "stdpp.bitvector.definitions.bv_unsigned"; "ARUN_1.A_DEP_END"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_DEP"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "ARUN_1.dtab_but"; "ARUN_1.dkeep"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "ARUN_1.depot_statics"; "Corelib.Init.Datatypes.app"; "ARUN_1.depot_cs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dnode"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "ARUN_1.depot_inv"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dput_frame"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "ARUN_1.DepotTop.dput_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_DEP_MAP1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_STACK_DEPOT_PUT"].

Section ARUN_1. Context {hAR : arun}.
Definition A_DEP_END : Z := 0x62b8e8.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition depot_statics (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "(0.(1.O1.)(0.(2.O1.)(3.(4.&40.)Lc1,(4.&40.)(3.(4.&40.)Lc2,(4.&40.)(3.(4.&40.)Lc3,(4.&40.)(0.(5.$6.O1.$7.(8.$9.(:.R3.)(;.$9.)))(0.(5.$6.O1.$<.(8.$9.(:.R2.)(;.$9.)))(5.$6.O1.$=.(8.$9.(:.R1.)(;.$9.))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition blocks_apart (nb bl : list Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "(0.Pk1,$>.Pk2,$>.P,(0.(?.=R2.)(10.R2.(11.(12.$>.O2.))))P,(0.(?.=R2.)(10.R2.(11.(12.$>.O2.))))P,(13.(14.$>.R4.R3.))(15.(?.(16.(17.O2.R5.)(18.+2.+14.))(17.O2.R4.))(?.(16.(17.O2.R4.)(18.+2.+14.))(17.O2.R5.)))(0.Pj1,$>.Pj2,$>.P,(0.(?.=R2.)(10.R2.(11.(12.$>.O1.))))P,(0.(?.=R2.)(10.R2.(11.(12.$>.O1.))))P,(13.(14.$>.R4.R3.))(15.(?.(16.(19.O1.R5.)(18.+2.+17.))(19.O1.R4.))(?.(16.(19.O1.R4.)(18.+2.+17.))(19.O1.R5.)))Pk,$>.Pj,$>.P,(0.(?.=R2.)(10.R2.(11.(12.$>.O2.))))P,(0.(?.=R2.)(10.R2.(11.(12.$>.O1.))))(15.(?.(16.(17.O2.R4.)(18.+2.+14.))(19.O1.R3.))(?.(16.(19.O1.R3.)(18.+2.+17.))(17.O2.R4.)))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition depot_inv (m : mem) (N : Z) (nb : list Z) (tf : Z) (bl : list Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "(0.(1:.$6.O5.$1;.(8.$9.(1<.(1=.&40.O4.))(;.$9.)))(0.(1>.O5.O4.)(0.(1?.VhAR,O5.O3.)(0.(20.O5.O3.O4.)(0.(21.O3.O4.)(0.(1:.$6.O5.$22.(8.$9.(1<.(1=.&40.=))(;.$9.)))(0.(3.(4.&40.)Lalloc,(4.&40.)(1:.$6.O5.$23.(8.$9.(:.(1=.&40.O2.))(8.$9.(:.R1.)(;.$9.)))))(0.(24.VhAR,O5.O1.)(0.(25.O5.O1.)(0.(?.=O2.)(0.(14.$>.(11.(12.$>.O1.))(26.(27.(16.O2.(18.+2.+14.))+1.)(18.+2.+14.)))(28.O3.O1.))))))))))))")
(* [comment removed for export] *).

Definition depot_cs (CS : Z -> Prop) (nb bl : list Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "(0.Pk,$>.P,(0.(?.=R1.)(10.R1.(11.(12.$>.O2.))))(29.O3.(17.O2.R2.)(18.+2.+14.))Pj,$>.P,(0.(?.=R1.)(10.R1.(11.(12.$>.O1.))))(29.O3.(19.O1.R2.)(18.+2.+17.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition dkeep (m m' : mem) (lo SP : Z) (nb bl : list Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "Px,(4.&40.)P,(13.(0.(?.O4.(2:.&40.R1.))(10.(2:.&40.R1.)O3.)))P,(13.(0.(?.$23.(2:.&40.R2.))(10.(2:.&40.R2.)$2;.)))P,Pk,$>.P,(0.(?.=R1.)(10.R1.(11.(12.$>.O2.))))(13.(0.(?.(17.O2.R2.)(2:.&40.R5.))(10.(2:.&40.R5.)(16.(17.O2.R2.)(18.+2.+14.)))))P,Pj,$>.P,(0.(?.=R1.)(10.R1.(11.(12.$>.O1.))))(13.(0.(?.(19.O1.R2.)(2:.&40.R6.))(10.(2:.&40.R6.)(16.(19.O1.R2.)(18.+2.+17.)))))(14.(2<.(4.&8.))A1.O5.R5.A1.O6.R5.)")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition dtab_but (m : mem) (N bi : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "Pi,$>.P,(0.(?.=R1.)(10.R1.(18.+2.+14.)))P,(13.(14.$>.R2.O1.))(3.$>.Lv,$>.(0.(1:.$6.O3.(16.$2=.(2>.+4.R4.))(8.$9.(1<.(1=.&40.R1.))(;.$9.)))(0.(?.=R1.)(?.R1.O2.))))")
(* [comment removed for export] *).
#[using="Type"] Lemma dtab_but_of : ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "PW,(2?.$30.)Pm,P,(4.&40.)(2<.(4.&8.))Pm',P,(4.&40.)(2<.(4.&8.))PN,$>.Pbi,$>.P,(1>.R4.R2.)P,(31.R6.R5.R4.)P,(32.$6.R6.R5.)P,Pi,$>.P,(0.(?.=R1.)(10.R1.(18.+2.+14.)))P,(13.(14.$>.R2.R6.))(33.R;.(16.$2=.(2>.+4.R3.))+4.)(34.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros W m m' N bi DT MU WM DJ i Hi NE. ddestruct (DT i Hi) as (v & C & VB). exists v. split; [|exact VB].
  eapply rw_cells_transport; [exact C| exact MU| exact WM| cbn [cells_size csize Nat.add]; apply DJ; assumption].
Qed.
#[using="Type"] Lemma dtab_but_transport : ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "PW,(2?.$30.)Pm,P,(4.&40.)(2<.(4.&8.))Pm',P,(4.&40.)(2<.(4.&8.))PN,$>.Pbi,$>.P,(34.R4.R2.R1.)P,(31.R6.R5.R4.)P,(32.$6.R6.R5.)P,Pi,$>.P,(0.(?.=R1.)(10.R1.(18.+2.+14.)))P,(13.(14.$>.R2.R6.))(33.R;.(16.$2=.(2>.+4.R3.))+4.)(34.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros W m m' N bi DT MU WM DJ i Hi NE. ddestruct (DT i Hi NE) as (v & C & VB). exists v. split; [|exact VB].
  eapply rw_cells_transport; [exact C| exact MU| exact WM| cbn [cells_size csize Nat.add]; apply DJ; assumption].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L52519758418.1700000>S1N2N'2LE1v2VB". (* [comment removed for export] *)
#[using="Type"] Lemma dtab_of_but : ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "Pm,P,(4.&40.)(2<.(4.&8.))PN,$>.PN',$>.Pbi,$>.Pid,$>.P,(34.R5.R4.R2.)P,(0.(?.=R3.)(10.R3.(18.+2.+14.)))P,(1:.$6.R7.(16.$2=.(2>.+4.R4.))(8.$9.(1<.(1=.&40.R3.))(;.$9.)))P,(0.(?.=R4.)(?.R4.R6.))P,(?.R8.R7.)(1>.R:.R8.)")
(* [comment removed for export] *).
Proof.
  intros m N N' bi id DT BI TC ID LE i Hi.
  destruct (Z.eq_dec i bi) as [->|NE]; [exists id; split; [exact TC| exact ID]|].
  ddestruct (DT i Hi NE) as (v & C & VB). exists v. split; [exact C| lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma dkeep_refl : forall m lo SP nb bl, dkeep m m lo SP nb bl.
Proof. intros m lo SP nb bl x _ _ _ _. reflexivity. Qed.
#[using="Type"] Lemma dkeep_munch : ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "PW,(2?.$30.)Pm0,P,(4.&40.)(2<.(4.&8.))Pm,P,(4.&40.)(2<.(4.&8.))Pm',P,(4.&40.)(2<.(4.&8.))Plo,$>.PSP,$>.Pnb,(2?.$>.)Pbl,(2?.$>.)P,(35.R7.R6.R4.R3.R2.R1.)P,(31.R9.R7.R6.)P,Px,$>.P,(13.(0.(?.R7.R1.)(10.R1.R6.)))P,(13.(0.(?.$23.R2.)(10.R2.$2;.)))P,Pk,$>.P,(0.(?.=R1.)(10.R1.(11.(12.$>.R8.))))(13.(0.(?.(17.R9.R2.)R5.)(10.R5.(16.(17.R9.R2.)(18.+2.+14.)))))P,Pj,$>.P,(0.(?.=R1.)(10.R1.(11.(12.$>.R8.))))(13.(0.(?.(19.R9.R2.)R6.)(10.R6.(16.(19.R9.R2.)(18.+2.+17.)))))(36.R?.R5.)(35.R:.R8.R7.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros W m0 m m' lo SP nb bl DK MU OUT x H1 H2 H3 H4. rewrite (MU x (OUT _ H1 H2 H3 H4)). apply DK; assumption.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L40398868765.16L51969720716.1600000900BS2nb1k2HkS2nb1k2Hk". (* [comment removed for export] *)
#[using="Type"] Lemma dkeep_app_n : forall m0 m lo SP nb bl a, dkeep m0 m lo SP nb bl -> dkeep m0 m lo SP (nb ++ [a]) bl.
Proof.
  intros m0 m lo SP nb bl a DK x H1 H2 H3 H4. apply DK; try assumption.
  intros k Hk. replace (dblk nb k) with (dblk (nb ++ [a]) k) by (unfold dblk; rewrite app_nth1 by lia; reflexivity).
  apply H3. rewrite app_length; cbn [length]; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L65067388567.16000009S2bl1j2Hj". (* [comment removed for export] *)
#[using="hAR"] Lemma dkeep_app_s : forall m0 m lo SP nb bl a, dkeep m0 m lo SP nb bl -> dkeep m0 m lo SP nb (bl ++ [a]).
Proof.
  intros m0 m lo SP nb bl a DK x H1 H2 H3 H4. apply DK; try assumption.
  intros j Hj. rewrite <- (sblk_app_old bl a j Hj). apply H4. rewrite app_length; cbn [length]; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L15546790972.15L18496299836.14L19678642919.15L51774333756.14L62843817532.14000001002003004005SSSSS". (* [comment removed for export] *)
#[using="Type"] Lemma depot_statics_transport : ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "PW,(2?.$30.)Pm,P,(4.&40.)(2<.(4.&8.))Pm',P,(4.&40.)(2<.(4.&8.))P,(37.R2.)P,(31.R4.R3.R2.)P,PA,$>.Pn,$>.P,(0.(?.+10000.R2.)(?.(16.R2.R1.)+1=;8<8.))(33.R8.R3.R2.)(37.R4.)")
(* [comment removed for export] *).
Proof.
  (intros W m m' dd_H; ddestruct dd_H as (DS & CS & c1 & c2 & c3 & M1 & M2 & M3); intros MU DJ). split; [|split].
  - destruct DS as [G1 G2]. split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ]); unfold A_GOT_CFLAGS, A_CFLAGS; cbn; lia.
  - eapply cstatics_transport; [exact CS| exact MU| exact DJ].
  - dexists c1, c2, c3. unfold A_MUR1, A_MUR2, A_MUR3 in *.
    repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ]); cbn; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L39871521455.3000004S2nb". (* [comment removed for export] *)
#[using="Type"] Lemma dblk_app_new : forall nb a, dblk (nb ++ [a]) (Z.of_nat (length nb)) = a.
Proof. intros. unfold dblk. rewrite Nat2Z.id, app_nth2, Nat.sub_diag by lia. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L40392573944.5000008S2nb1k1H". (* [comment removed for export] *)
#[using="Type"] Lemma dblk_app_old : forall nb a k, 0 <= k < Z.of_nat (length nb) -> dblk (nb ++ [a]) k = dblk nb k.
Proof. intros. unfold dblk. rewrite app_nth1 by lia. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L16080212298.14L16080212427.16L17734031723.15L22561392175.14L22561392175.16L23625569716.15L31640961642.13L51969699538.14L53446007031.16L57274660029.12L59488775553.14L63359312009.14L65067295310.14L67893083020.1600000C00Y00j01=01P01a02102E02^02m02n02o03@03AS2nb2k12H12NE2H22N1S2nb2k12k22H12H22N12N2S2nb1a2k12H12H21HS2nb2k22H12H22NE2N2S2nb2k12k22H12H22N2S2nb1a2k22H12H21HS2nb2bl1a1j2Hk1HS2nb2bl1k1j2Hk2Hj2N1S2nb2k12k22H12H22NE2N12N2S2nb1a2H12NE2H2FFS2nb2bl1k1j2Hk2HjF". (* [comment removed for export] *)
#[using="Type"] Lemma blocks_apart_app_n : ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "Pnb,(2?.$>.)Pbl,(2?.$>.)Pa,$>.P,(28.R3.R2.)P,Pk,$>.P,(0.(?.=R1.)(10.R1.(11.(12.$>.R5.))))(15.(?.(16.(17.R6.R2.)(18.+2.+14.))R4.)(?.(16.R4.(18.+2.+14.))(17.R6.R2.)))P,Pj,$>.P,(0.(?.=R1.)(10.R1.(11.(12.$>.R5.))))(15.(?.(16.(19.R6.R2.)(18.+2.+17.))R5.)(?.(16.R5.(18.+2.+14.))(19.R6.R2.)))(28.(38.$>.R6.(8.$>.R4.(;.$>.)))R5.)")
(* [comment removed for export] *).
Proof.
  (intros nb bl a dd_H; ddestruct dd_H as (B1 & B2 & B3); intros AN AS). split; [|split; [exact B2|]].
  - intros k1 k2 H1 H2 NE. rewrite app_length in H1, H2. cbn [length] in H1, H2.
    destruct (Z.eq_dec k1 (Z.of_nat (length nb))) as [->|N1]; destruct (Z.eq_dec k2 (Z.of_nat (length nb))) as [->|N2]; try lia.
    + rewrite dblk_app_new, dblk_app_old by lia. destruct (AN k2 ltac:(lia)); lia.
    + rewrite dblk_app_old, dblk_app_new by lia. destruct (AN k1 ltac:(lia)); lia.
    + rewrite !dblk_app_old by lia. apply B1; lia.
  - intros k j Hk Hj. rewrite app_length in Hk. cbn [length] in Hk.
    destruct (Z.eq_dec k (Z.of_nat (length nb))) as [->|N1].
    + rewrite dblk_app_new. destruct (AS j Hj); lia.
    + rewrite dblk_app_old by lia. apply B3; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L18701237132.16L33271226914.15L38168600713.14L42902425930.14L42902426059.16L43723713921.14L51969699538.14L549949121.13  L5664430327.16 L57274660029.12L58335473353.15L63101208111.14L63101208111.16L65067295310.1400000100B00C00V00l00m01>01N01g02602G02Z02m03AFS2bl1a2j22H12H21HFS2bl2j12H12NE2H22N1S2bl2j12j22H12H22N12N2FS2nb2bl1k1j2Hk2HjS2nb2bl1a1k2Hj1HS2bl2j12j22H12H22NE2N12N2S2bl1a2H12NE2H2S2bl1a2j12H12H21HS2bl2j22H12H22NE2N2S2bl2j12j22H12H22N2S2nb2bl1k1j2Hk2Hj2N1". (* [comment removed for export] *)
#[using="hAR"] Lemma blocks_apart_app_s : ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "Pnb,(2?.$>.)Pbl,(2?.$>.)Pa,$>.P,(28.R3.R2.)P,Pk,$>.P,(0.(?.=R1.)(10.R1.(11.(12.$>.R5.))))(15.(?.(16.(17.R6.R2.)(18.+2.+14.))R4.)(?.(16.R4.(18.+2.+17.))(17.R6.R2.)))P,Pj,$>.P,(0.(?.=R1.)(10.R1.(11.(12.$>.R5.))))(15.(?.(16.(19.R6.R2.)(18.+2.+17.))R5.)(?.(16.R5.(18.+2.+17.))(19.R6.R2.)))(28.R6.(38.$>.R5.(8.$>.R4.(;.$>.))))")
(* [comment removed for export] *).
Proof.
  (intros nb bl a dd_H; ddestruct dd_H as (B1 & B2 & B3); intros AN AS). split; [exact B1| split].
  - intros j1 j2 H1 H2 NE. rewrite app_length in H1, H2. cbn [length] in H1, H2.
    destruct (Z.eq_dec j1 (Z.of_nat (length bl))) as [->|N1]; destruct (Z.eq_dec j2 (Z.of_nat (length bl))) as [->|N2]; try lia.
    + rewrite sblk_app_new, sblk_app_old by lia. destruct (AS j2 ltac:(lia)); lia.
    + rewrite sblk_app_old, sblk_app_new by lia. destruct (AS j1 ltac:(lia)); lia.
    + rewrite !sblk_app_old by lia. apply B2; lia.
  - intros k j Hk Hj. rewrite app_length in Hj. cbn [length] in Hj.
    destruct (Z.eq_dec j (Z.of_nat (length bl))) as [->|N1].
    + rewrite sblk_app_new. destruct (AN k Hk); lia.
    + rewrite sblk_app_old by lia. apply B3; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L36579050554.15L51969699538.13L51969723161.15L65067386757.1400000>00J00[00dS2nb1k2Hk1x2HxS2nb1k2Hk2N1S2nb1k2Hk2N11x2HxS2bl1j2Hj". (* [comment removed for export] *)
#[using="Type"] Lemma depot_cs_app_n : ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "PCS,P,$>.SpPCS',P,$>.SpPnb,(2?.$>.)Pbl,(2?.$>.)Pa,$>.P,(39.R5.R3.R2.)P,Px,$>.P,A1.R7.R1.A1.R7.R2.P,(29.R6.R3.(18.+2.+14.))(39.R7.(38.$>.R6.(8.$>.R4.(;.$>.)))R5.)")
(* [comment removed for export] *).
Proof.
  intros CS CS' nb bl a [D1 D2] MO CR. split.
  - intros k Hk. rewrite app_length in Hk. cbn [length] in Hk.
    destruct (Z.eq_dec k (Z.of_nat (length nb))) as [->|N1]; [rewrite dblk_app_new; exact CR|].
    rewrite dblk_app_old by lia. intros x Hx. apply MO. apply (D1 k); lia.
  - intros j Hj x Hx. apply MO. apply (D2 j); [lia| exact Hx].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L35991266291.15L51969723161.14L65067295310.13L65067386757.1500000>00G00S00dS2bl1j2Hj1x2HxS2nb1k2HkS2bl1j2Hj2N1S2bl1j2Hj2N11x2Hx". (* [comment removed for export] *)
#[using="hAR"] Lemma depot_cs_app_s : ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "PCS,P,$>.SpPCS',P,$>.SpPnb,(2?.$>.)Pbl,(2?.$>.)Pa,$>.P,(39.R5.R3.R2.)P,Px,$>.P,A1.R7.R1.A1.R7.R2.P,(29.R6.R3.(18.+2.+17.))(39.R7.R6.(38.$>.R5.(8.$>.R4.(;.$>.))))")
(* [comment removed for export] *).
Proof.
  intros CS CS' nb bl a [D1 D2] MO CR. split.
  - intros k Hk x Hx. apply MO. apply (D1 k); [lia| exact Hx].
  - intros j Hj. rewrite app_length in Hj. cbn [length] in Hj.
    destruct (Z.eq_dec j (Z.of_nat (length bl))) as [->|N1]; [rewrite sblk_app_new; exact CR|].
    rewrite sblk_app_old by lia. intros x Hx. apply MO. apply (D2 j); lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L16911228653.7L18620093518.8L18620093647.6L51049978564.7L67790688286.7L67790727722.700000A00X00l01F01G01TS2tf5count3CNT2TFS2tf5count3CNT2TF2LT2M2S2tf5count3CNT2TF2M1S2tf5start5count3CNT2TF2SESS2tf5count2TF". (* [comment removed for export] *)
#[using="Type"] Lemma tf_potential : ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "Ptf,$>.Pstart,$>.Pcount,$>.P,(0.(?.+2.R1.)(?.R1.+1?.))P,(?.=R4.)P,(15.(14.$>.R4.R5.)(0.(14.$>.R4.(16.R5.R3.))(10.(26.R5.(18.+2.+14.))(26.(27.(16.R5.R3.)+1.)(18.+2.+14.)))))(0.(0.(?.R6.(16.R5.R4.))(?.(16.R5.R4.)(16.R6.(2>.+2.R4.))))(?.(27.(16.R5.R4.)(2>.+1?.(26.(16.R5.R4.)(18.+2.+14.))))(16.(27.R6.(2>.+1?.(26.R6.(18.+2.+14.))))R4.)))")
(* [comment removed for export] *).
Proof.
  intros tf start count CNT TF SE.
  pose proof (Z.div_le_mono tf (start + count) (2^20) ltac:(lia) ltac:(lia)) as M1.
  destruct SE as [-> | [-> LT]]; [lia|].
  pose proof (Z.div_le_mono (tf + count - 1) (tf + count + count) (2^20) ltac:(lia) ltac:(lia)) as M2. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L23513526952.10L36982110602.12L55162210279.13L60357226429.10L60357449484.11L63703881729.10L67790688923.10L67790727722.11L67792869265.1200000C00`01501E01U01e02502E02US2tf5start5count2TSS2tf5start5count1L2HL2JL2M11HS2tf5start5count1H2H0S2tf5start5countS2tf5start5countS2tf5start5countS2tf5start5countS2tf5start5countS2tf5start5count". (* [comment removed for export] *)
#[using="Type"] Lemma len_fin : ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "Ptf,$>.Pstart,$>.Pcount,$>.PL,$>.P,(?.+2.R2.)P,(0.(?.=R5.)(?.R5.R4.))P,(14.$>.R3.(26.(27.(16.R6.(18.+2.+14.))+1.)(18.+2.+14.)))P,(10.(26.R6.(18.+2.+14.))R4.)P,(14.$>.(26.R7.(18.+2.+14.))(26.(27.(16.R7.R6.)+1.)(18.+2.+14.)))(14.$>.R6.(26.(27.(16.(16.R8.R7.)(18.+2.+14.))+1.)(18.+2.+14.)))")
(* [comment removed for export] *).
Proof.
  intros tf start count L CNT TS HL JL SB.
  replace (start + count + 2^20 - 1) with ((start + count - 1) + 1 * 2^20) by lia. rewrite Z.div_add, <- SB by lia.
  pose proof (Z.div_le_mono (tf + 2^20 - 1) (start + 2^20 - 1) (2^20) ltac:(lia) ltac:(lia)) as M1.
  assert ((start + 2^20 - 1) / 2^20 < start / 2^20 + 2); [| lia].
  apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod start (2^20) ltac:(lia)). pose proof (Z.mod_pos_bound start (2^20) ltac:(lia)). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L16075870183.5L18928853355.400000;00<S2nb1s2Hs1HS". (* [comment removed for export] *)
#[using="Type"] Lemma dnode_in_blk : ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "Pnb,(2?.$>.)Ps,$>.P,(?.=R1.)(0.(?.(17.R3.(26.R2.+10000.))(3:.R3.R2.))(?.(16.(3:.R3.R2.)+10.)(16.(17.R3.(26.R2.+10000.))(18.+2.+14.))))")
(* [comment removed for export] *).
Proof. intros nb s Hs. unfold dnode. pose proof (Z.mod_pos_bound s 65536 ltac:(lia)). lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L11865776948.16L18928812589.16L18932831555.16L18933043916.17L38411416615.18L39685231728.16L57877123455.1700000@00P00`01001J01Z02:S2nb1s2s'2Hs3Hs'S2nb1s2s'2Hs3Hs'S2nb1s2s'2Hs3Hs'S2nb1s2s'2Hs3Hs'S2nb1s2s'2Hs3Hs'2NE1E1H2H0S2nb1s2s'2Hs3Hs'S2nb1s2s'2Hs3Hs'2I23I1'1H2I13I2'". (* [comment removed for export] *)
#[using="Type"] Lemma dnode_apart : ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "Pnb,(2?.$>.)Pbl,(2?.$>.)Ps,$>.Ps',$>.P,(28.R4.R3.)P,(?.=R3.)P,(?.=R3.)P,(13.(14.$>.R5.R4.))P,(10.(26.R6.+10000.)(11.(12.$>.R8.)))P,(10.(26.R6.+10000.)(11.(12.$>.R9.)))(15.(?.(16.(3:.R:.R8.)+10.)(3:.R:.R7.))(?.(16.(3:.R:.R7.)+10.)(3:.R:.R8.)))")
(* [comment removed for export] *).
Proof.
  (intros nb bl s s' dd_H; ddestruct dd_H as (B1 & _ & _); intros Hs Hs' NE L L').
  pose proof (dnode_in_blk nb s Hs) as [I1 I2]. pose proof (dnode_in_blk nb s' Hs') as [I1' I2'].
  destruct (Z.eq_dec (s / 65536) (s' / 65536)) as [E|N1].
  - unfold dnode. rewrite <- E. pose proof (Z.div_mod s 65536 ltac:(lia)). pose proof (Z.div_mod s' 65536 ltac:(lia)). lia.
  - destruct (B1 (s / 65536) (s' / 65536) ltac:(split; [apply Z.div_pos; lia| exact L]) ltac:(split; [apply Z.div_pos; lia| exact L']) N1); lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section DepotTop.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CSf : list Z -> list Z -> Z -> Prop.
  Variable K : list Z -> list Z -> Model -> Prop.
  Hypothesis CSOKf : forall nb bl, cs_ok AL (CSf nb bl).
  Hypothesis KL : forall nb bl, kinv AL (CSf nb bl) (K nb bl).
  Hypothesis CSmono_n : forall nb bl a x, CSf nb bl x -> CSf (nb ++ [a]) bl x.
  Hypothesis CSmono_s : forall nb bl a x, CSf nb bl x -> CSf nb (bl ++ [a]) x.
  Hypothesis K_apart : ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "Pnb,(2?.$>.)Pbl,(2?.$>.)Pmo,$3;.Pa,(4.&40.)Pn,(4.&40.)P,A3.VK,R5.R4.R3.P,(14.$3<.(3=.(38.(3>.(4.&40.)(4.&40.))(3?.(40.R4.))(41.(40.R4.)))R3.R2.)$42.)P,(?.+10000.(2:.&40.R3.))P,(?.(16.(2:.&40.R5.)(2:.&40.R4.))(43.VhAR,))Px,$>.P,(15.A3.VCSf,R:.R9.R1.(0.(?.(44.VAL,)R1.)(10.R1.(45.VAL,))))(13.(0.(?.(2:.&40.R8.)R2.)(10.R2.(16.(2:.&40.R8.)(2:.&40.R7.)))))")
(* [comment removed for export] *).
  Variables (Gn Gs : list Z -> list Z -> Prop).   (* [comment removed for export] *)
  Hypothesis T_node : ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "Pnb,(2?.$>.)Pbl,(2?.$>.)Pmo,$3;.Pa,(4.&40.)P,A2.VGn,R4.R3.P,A3.VK,R5.R4.R3.P,(14.$>.(46.(2:.&40.R3.)+1000.)=)P,(10.=(2:.&40.R4.))P,(?.(16.(2:.&40.R5.)(18.+2.+14.))(43.VhAR,))P,(14.$3<.(3=.(38.(3>.(4.&40.)(4.&40.))(3?.(40.R7.))(41.(40.R7.)))R6.(1=.&40.(18.+2.+14.)))$42.)(0.A3.VK,(38.$>.R:.(8.$>.(2:.&40.R7.)(;.$>.)))R9.(47.+22.R7.(18.+2.+14.)R8.)(29.A2.VCSf,(38.$>.R:.(8.$>.(2:.&40.R7.)(;.$>.)))R9.(2:.&40.R7.)(18.+2.+14.)))")
(* [comment removed for export] *).
  Hypothesis T_store : ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "Pnb,(2?.$>.)Pbl,(2?.$>.)Pmo,$3;.Pa,(4.&40.)P,A2.VGs,R4.R3.P,A3.VK,R5.R4.R3.P,(14.$>.(46.(2:.&40.R3.)+1000.)=)P,(10.=(2:.&40.R4.))P,(?.(16.(2:.&40.R5.)(18.+2.+17.))(43.VhAR,))P,(14.$3<.(3=.(38.(3>.(4.&40.)(4.&40.))(3?.(40.R7.))(41.(40.R7.)))R6.(1=.&40.(18.+2.+17.)))$42.)(0.A3.VK,R:.(38.$>.R9.(8.$>.(2:.&40.R7.)(;.$>.)))(47.+4022.R7.(18.+2.+17.)R8.)(29.A2.VCSf,R:.(38.$>.R9.(8.$>.(2:.&40.R7.)(;.$>.)))(2:.&40.R7.)(18.+2.+17.)))")
(* [comment removed for export] *).
  Hypothesis ROOM_n : forall nb bl mo, Gn nb bl -> K nb bl mo -> exists a, anon_grantable 0x22 (2^20) mo a.
  Hypothesis ROOM_s : forall nb bl mo, Gs nb bl -> K nb bl mo -> exists a, anon_grantable 0x4022 (2^23) mo a.

  Ltac facts :=
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition dput_post (SP : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo N TR tf size : Z) (nb bl : list Z) (ws : list word) (m0 : mem) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "Lc,$48.(3.$49.Lms',$49.(3.$3;.Lmo',$3;.(3.(2?.$>.)Lnb',(2?.$>.)(3.(2?.$>.)Lbl',(2?.$>.)(3.$>.LN',$>.(3.$>.Ltf',$>.(3.$>.Lid,$>.(3.(4.&40.)Lx5,(4.&40.)(3.(4.&40.)Lx6,(4.&40.)(3.(4.&40.)Lx7,(4.&40.)(3.(4.&40.)Lx11,(4.&40.)(3.(4.&40.)Lx12,(4.&40.)(3.(4.&40.)Lx13,(4.&40.)(3.(4.&40.)Lx14,(4.&40.)(3.(4.&40.)Lx15,(4.&40.)(3.(4.&40.)Lx16,(4.&40.)(3.(4.&40.)Lx17,(4.&40.)(3.(4.&40.)Lx28,(4.&40.)(3.(4.&40.)Lx29,(4.&40.)(3.(4.&40.)Lx30,(4.&40.)(3.(4.&40.)Lx31,(4.&40.)(3.P,(4.&40.)(2<.(4.&8.))Lm',P,(4.&40.)(2<.(4.&8.))(0.(14.$48.R17.(4:.R16.R15.))(0.(14.$49.R16.(4;.(4<.O1:.(1=.&40.O1;.)O19.O18.R?.R>.R=.O17.O16.(1=.&40.R10.)R<.R;.R:.R9.R8.R7.R6.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.R5.R4.R3.R2.)O;.(4=.O1:.)O:.(4>.(4.&40.))R1.(4?.$6.)))(0.A3.VK,R14.R13.R15.(0.(50.R1.R15.)(0.(51.R1.R12.R14.R11.R13.)(0.(39.A2.VCSf,R14.R13.R14.R13.)(0.(37.R1.)(0.(0.(?.+1.R10.)(?.R10.R12.))(0.(0.(?.O8.R12.)(?.R12.(16.O8.+1.)))(0.(0.(?.O6.R11.)(?.R11.(16.O6.(2>.+2.(16.O5.+1.)))))(0.(?.(27.R11.(2>.+1?.(26.R11.(18.+2.+14.))))(16.(27.O6.(2>.+1?.(26.O6.(18.+2.+14.))))(16.O5.+1.)))(0.Px,$>.P,A3.VCSf,O4.O3.R1.A3.VCSf,R16.R15.R2.(0.(3.(2?.$>.)Lsn,(2?.$>.)(3.(2?.$>.)Lsb,(2?.$>.)(0.(14.(2?.$>.)R16.(38.$>.O4.R2.))(0.(14.(2?.$>.)R15.(38.$>.O3.R1.))(0.(52.$>.Lb,$>.Px,$>.P,A3.VCSf,O4.O3.R1.(13.(0.(?.R3.R2.)(10.R2.(16.R3.(18.+2.+14.)))))R2.)(52.$>.Lb,$>.Px,$>.P,A3.VCSf,O4.O3.R1.(13.(0.(?.R3.R2.)(10.R2.(16.R3.(18.+2.+17.)))))R1.))))))(0.(35.O1.R1.O9.O1;.R14.R13.)(0.(32.$6.O1.R1.)(0.(53.$6.R1.O9.O1;.)(0.(54.$6.R1.)(55.$6.R1.O7.O2.))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "03W0@L10130626271.188L10130724975.278L1121256019.191 L1123401559.184 L11388733925.2  L11573422672.143L11816578494.246L11865774336.191L11865774336.281L11865989940.196L11865989940.286L11865990069.197L11865990069.287L1233844652.20  L12436666760.12 L14144836158.194L14756846704.246L15055809849.188L15055905673.278L15550555041.283L1604723725.18  L1604723725.20  L16182025039.14 L16188076006.13 L16194106566.135L1685717371.0   L17069138670.14 L17833539672.12 L1789740686.2   L18165219041.246L18567694503.20 L18926664235.129L18928474025.133L18928566829.196L18928566829.286L18928829100.193L18928829100.283L18930958230.134L19663319820.1  L19665592045.278L19665686621.188L21361060448.201L21662802831.18 L21662802831.20 L22188072562.19 L2301147920.188 L2301310368.278 L23480290099.20 L23500818241.14 L24636534866.17 L24642955195.19 L24680454668.1  L25387111935.19 L25691021708.1  L25763266701.14 L25763267338.18 L25769292836.20 L26043710162.8  L26165915938.12 L26220076261.2  L26530540841.246L2658965821.5   L26685281686.129L26685347366.139L26687827217.197L26687827217.287L27093401618.246L27744624267.14 L27746445858.13 L28198747148.1  L28573892092.10 L29231843173.17 L29238057125.13 L29242462348.19 L2978961816.0   L29908084250.193L29908084250.283L30260538970.3  L30940121149.2  L31122149423.5  L31516630904.246L31609234122.197L31609234122.287L31949173134.2  L32132320707.14 L32132320836.18 L32134150506.20 L32745426256.5  L33116218422.246L3456365119.246 L34908194115.2  L34923369981.246L3506104929.1   L35153024950.182L35153484464.193L36572734103.17 L37053275572.278L37053502212.188L37622514645.16 L37622514645.18 L37849879351.18 L37887504981.246L38313764574.17 L38411308944.14 L38715000780.19 L39142223495.246L39476841698.5  L39531177305.188L39531211753.278L39583376481.1  L39756333319.246L40434153058.246L4057190548.9   L41471914648.19 L4167354298.246 L42156658785.1  L42174825013.186L4232352724.246 L4234356847.152 L42744976268.1  L43063012174.16 L43063012174.18 L43158545413.246L44557183201.1  L44878700685.131L4499880843.246 L45082835408.18 L45082835543.13 L45084643070.14 L4561257253.18  L4561257253.20  L46632863170.19 L4751875318.246 L47616093674.19 L47620433347.13 L47622519299.17 L47866976955.17 L48219737782.9  L48710004321.246L48973238392.186L49187778629.16 L49187778629.18 L49353242566.8  L50150627460.235L50161236188.239L50163324096.238L50163324736.239L50168477957.20 L5071277292.246 L50745847470.14 L51023005601.6  L51967516436.238L51967623752.154L51969682900.152L51969723161.248L51969731925.193L51969731925.283L51970010707.194L51970010707.284L52031317262.20 L52417109053.2  L5253045470.246 L5302396531.235 L53528290349.20 L5407934953.246 L54132128924.16 L54132128924.18 L54205227745.1  L54600445031.8  L54720799623.246L54928322635.12 L54928322635.17 L55343735104.20 L55345550825.14 L55345550958.18 L55598617942.3  L55598617942.8  L55946758243.152L55976884588.9  L56309281125.3  L56309281125.8  L57491806509.5  L57553464512.16 L57765061761.152L58054023405.198L58486878746.13 L58492880563.14 L58583566608.20 L58591499740.246L58593701479.152L58598055654.201L59090160779.9  L59311120877.246L60106130471.135L60353210249.277L60673740194.201L60675573400.246L60677717283.152L60959241334.246L61642061087.19 L61669218265.4  L631402240.152  L63621479665.17 L63627897624.19 L63631876913.13 L63716380725.277L64958712479.17 L65406737761.1  L66551059490.195L66551059490.285L66566358642.241L67788479403.193L67788479403.194L67788670256.238L67788674733.182L68329661222.2  L68365544765.2  L7626369036.1   L7910098149.2   L7921710478.2   L8209540890.18  L8209540890.20  L8309204096.154 L8311015450.283 L8311015579.284 L8311403054.281 L8806423751.10  L8806423751.14  L951548579.20   L953355661.18   L9934402114.246 00001502?03C04G04N05D05E06O07^08h0:70;A0<P0=90=\0?40@>0AF0BS0C]0DC0E20EV0F00F`0Fa0GD0G]0G^0G_0HB0Hn0IV0J]0Ki0M00N<0Nd0Nh0P50Q=0RO0Rl0SR0T60U;0VE0W40WR0X@0Y70Y;0Z10Z50ZU0[50[^0[o0\U0\\0\]0\c0]R0^?0_I0`X0`Y0a30aS0aW0b60b^0cF0d70d80eB0fQ0f[0f\0fn0fo0h:0iJ0iK0j00jU0kC0kR0kS0ld0lk0ll0m00nc0oh10U11b12k13D13l14R14S15?15_16F16G16M17W18f18j18k18l19919T1:i1:m1<j1>71>m1?11?P1@81@91@=1A31B@1B`1C;1CT1Cn1DQ1E:1FH1G@1Go1H^1I?1IO1IP1JX1K11KS1L01M:1ND1ON1PX1Q?1Q@1QW1Qo1SA1T<1U71VI1WV1Xh1Z51[N1\=1\>1\?1]I1^:1^;1^\1_F1_J1_e1_f1`A1`d1aI1ae1bA1bH1bS1cJ1cc1cj1d51dE1da1db1el1fF1fm1gV1hi1ie1k51kI1lS1mB1nL1oZ20k21e23623W23f23g24E24l25J26T27827<28N29e2;B2<G2=N2>X2?V2?]2?^2?b2?i2?j2@J2A32Am2D62F?2HH2Hg2IQ2J92JX2JYS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start2j0S3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S02uaS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2SZ2HL3DML3DBL4NODE3TRB5start2S0S3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2SZ2HL3DML3DBL4NODE3TRB5start2j0S2bi2BIS3hAR2SP2TR1N2tf2nb3nb'2bl2ws1k2T12HL3DML3DBL4NODE3TRBFS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start2j01s2HsS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S02ua1s2HsS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start2j01s2HsS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S02ua1s2HsS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start2j01s2HsS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S02ua1s2HsS3hAR1N2bi3nb'2bl1k2BI4NODE5start2j01j2Y2S3hAR2SP2TR2lo2T05LOIMG3SPL5start1jS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2SZ2HL3TF03TFB2BL3DML3DBL4NODE3TRB5start1j2JE2S03TP2S3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S02uaS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF02WN3DML3DBL4NODE3TRB5start2j0S3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF02WN3DML3DBL4NODE3TRB5start1j2S02uaS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF02ua3DML3DBL4NODE3TRB5start1j2S0S3hAR2SP1N2lo3nb'1k5LOIMG4NODE1s2I22Y1S3hAR2SP1N2lo3nb'1k5LOIMG4NODE5start2j01s2I22Y1S3hAR2SP2lo5LOIMG3SPL5start1j1A1n2H1S3hAR5start1j2J41A1n2H12H2S3hAR2SP2TR1N2tf2nb3nb'2bl2ws2HL2WN3DML3DBL1H2H0SS3hAR2SP2lo2bl5LOIMG5start1j2j'3Hj'S3hAR2SP2TR2lo2T05start1jSFS3hAR1N3nb'2bl1k4NODE5start2j01j2Y0S3hAR2SP2TR1N2tf2nb3nb'2bl2ws3blk2HL3DML3DBLS3hAR2SP2TR1N2tf2nb3nb'2bl2ws2HL3DML3DBLS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start2j01sS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S02ua1sS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start2j01sS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S02ua1sS3hAR2SP2TR1N2tf2nb3nb'2bl2ws2HL3DML3DBLS2SPS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF02WN3DML3DBL4NODE3TRB5start1j2S02uaS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF02WN3DML3DBL4NODE3TRB5start2j0S3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2SZ2HL3TF03TFB3DML3DBL4NODE3TRB5start1j2S03TP1S3hAR1N2bi3nb'1k2BI4NODE1s2Y3S3hAR1N2bi3nb'1k2BI4NODE5start2j01s2Y3S3hAR1N2bi3nb'2bl1k2BI4NODE2ua2j'2Y2S3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start2j0S3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S02uaS3hAR2SP1N2lo3nb'2bl1k5LOIMG4NODE5start2j01j2Y1S3hAR2bl5start1j2ua3UA02j'3Hj'S3hAR2SP2TR1N2lo2bi3nb'1k2T02BI5LOIMG3SPL4NODES3hAR2SP2TR1N2lo2bi3nb'1k2T02BI5LOIMG3SPL4NODE5start2j0S2SPS3hAR2SP2TR1N2lo3nb'2bl1k2T05LOIMG3SPL4NODE5start2j01YS2SPS3hAR1N3nb'1k2K04NODE3NI11A1n2H1S3hAR1N3nb'1k2K04NODE3NI11A1n2H1S3hAR1N3nb'1k2K04NODE3NI15start2j01A1n2H1S3hAR2bi2BI1A1n1HS3hAR2SP2TR2lo2T05LOIMG3SPL5start1j2J4S2bi2BIFS1i2HiS3hAR2SP2TR1N2tf2nb3nb'2bl2ws3blk2HL2WN3DML3DBLS3hAR2SP2TR1N2tf2nb3nb'2bl2ws1k2HL2WN3DML3DBLS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF02WN3DML3DBL4NODE3TRB5start2j01sS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF02WN3DML3DBL4NODE3TRB5start1j2S02ua1sFS3hAR2SP2lo5start1j1A1n2H1S3hAR2SP2lo5LOIMG5start1j1A1n2H1S2SPS2SP1N2lo2bi3nb'1k4NODE2ua1x2HxS3hAR2SP2TR1N2lo3nb'1k2T05LOIMG3SPL4NODES3hAR2SP2TR1N2lo3nb'1k2T05LOIMG3SPL4NODES3hAR2SP2TR1N2lo3nb'1k2T05LOIMG3SPL4NODE5start2j0SS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start2j01s2HsS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S02ua1s2HsS1N3NB22WNSS2bl5start1j2JE2J4FS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03LNB3DML3DBL4NODE3TRB5start2j01sS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03LNB3DML3DBL4NODE3TRB5start1j2S02ua1sSS3hAR2SP1N2lo3nb'1k5LOIMG4NODE1A1n2H1S3hAR2SP1N2lo3nb'1k5LOIMG4NODE1A1n2H1S3hAR2SP1N2lo3nb'1k5LOIMG4NODE5start2j01A1n2H1S2bi2BI1i2Hi2NEFS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL2K04NODE3NI13TRB5start1j2S02uaS2bi2BIFS2SPS3hAR2AL2SP2TR4size3tag1N2tf1h1v2bi2nb3nb'2bl2ws1k2SZ2TG2HL3TF02VB2BI2HR5ALWF'4IMG'2WN3DML3DBL2SN4NODE3TRB5start2SES3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start2S0S3hAR2SP1N2lo3nb'1k5LOIMG2K14NODE3NI25start1jS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2SZ2HL3TF03DML3DBL4NODE3TRB5start1j2S02uaS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start2j03TP1S1N2bi3nb'1k2BI4NODE1x2H2S1N2bi3nb'2bl1k2BI4NODE5start2j01x2H42H2S3hAR1N2bi3nb'1k2BI4NODE2ua1s2I12I22Y2FS3hAR1N3nb'1k4NODE3NI13NI25start1j2J42ua3APkS3hAR2bl5start1j2JE2J42j'3Hj'2NES3hAR2SP1N2lo3nb'2bl1k5LOIMG4NODE2j'2Y1FS1i2HiS3hAR2SP2TR4size1N2tf1v2nb3nb'2bl2ws1k2HL3TF02VB3DML3DBL4NODE3TRB5start2j0S3hAR2SP2TR4size1N2tf1v2nb3nb'2bl2ws1k2HL3TF02VB3DML3DBL4NODE3TRB5start1j2S02uaS2SPFFS3hAR5start1jS3hAR1N3nb'2bl1k4NODE2j'2Y0S3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2SZ2HL3TF03TFB3DML3DBL4NODE3TRB5start1j2S03TP12uaS2SPS3hAR2AL2SP2TR4size3tag1N2tf1h1v2bi2nb3nb'2bl2ws1k2SZ2TG2HL3TF02VB2BI2HR5ALWF'4IMG'2WN3DML3DBL2SN4NODE3TRB5start2SE2j02J03TP1S3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2T12HL3TF03DML3DBL4NODE3TRB5start1j2S02uaS3hAR2SP2TR1N2tf2nb3nb'2bl2ws1k2T12HL3DML3DBL4NODE3TRBS2SPS2SP1N2lo2bi3nb'1k2BI4NODE1x2H1S2SP1N2lo2bi3nb'1k2BI4NODE5start2j01x2H1FS2SPS3hAR2SP2TR1N2tf2nb3nb'2bl2ws1k3blk2HL3LNB3DML3DBL3HK0S3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2SZ2HL3TF03DML3DBL4NODE3TRB5start1j2S02uaS3hAR1N3nb'1k4NODE2ua3UA01A1n2H1S3hAR5start1j2ua3UA01A1n2H1S3hAR5start1j2J42ua1A1n1YS3hAR1N3nb'1k4NODE1s2I12Y0S3hAR1N3nb'1k4NODE5start2j01s2I12Y0S3hAR1N2bi3nb'2bl1k2BI4NODE3NI13NI22j'2Y3S3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL3KAL4NODE3TRB5start1j2S02uaS3hAR2SP2TR1N2lo3nb'1k2T05LOIMG3SPL2K14NODE3NI25start2j0S3hAR2SP2TR1N2lo3nb'1k2T05LOIMG3SPL2K14NODE3NI2S3hAR2SP2TR1N2lo3nb'1k2T05LOIMG3SPL2K14NODE3NI2S3hAR1N3nb'1k2K04NODE3NI15start1jS3hAR5start1j2J4FS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2SZ2HL3TF03DML3DBL4NODE3TRB5start2j0S1N2bi3nb'1k2BI4NODE1x2H2S1N2bi3nb'1k2BI4NODE5start2j01x2H2S1N3nb'1k4NODE3NI13NI22ua3APkS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S02uaS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S02uaS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S02uaS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S02uaS3hAR1N3nb'2bl1k4NODE5start2j01A1n2H11YFS3hAR2bl5start1j2j'3Hj'S4size2bl5start1j3SBE2JES3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03KLT3DML3DBL3HK04NODE3TRB5start1j2S02uaS3hAR2SP2TR1N2tf2nb3nb'2bl2ws1k2HL3KLT3DML3DBL3HK04NODE3TRBS3hAR2SP2TR1N2tf2nb3nb'2bl2ws1k2HL3KLT3DML3DBL3HK04NODE3TRBS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03KLT3DML3DBL3HK04NODE3TRB5start1j2S02uaS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03KLT3DML3DBL3HK04NODE3TRB5start2j0S3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03KLT2ua3DML3DBL3HK04NODE3TRB5start1j2S0S3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03KLT3DML3DBL3HK04NODE3TRB5start2j0S3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03KLT3DML3DBL3HK04NODE3TRB5start1j2S02ua2j'3Hj'S3hAR1N2bi3nb'2bl1k2BI4NODE5start2j01s2I12I22Y2SFS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S02uaS3hAR1N2bi3nb'2bl1k2BI4NODE3NI13NI25start2j01j2Y3FS1N2bi3nb'1k2BI4NODE3NI13NI21x2H3S1N2bi3nb'1k2BI4NODE3NI13NI25start2j01x2H3S2SPS1N3nb'1k4NODE3NI13NI21x2HxFS3hAR2TR5start1j2J42ua4APtrS3hAR2TR1N2bi3nb'1k2BI4NODE2ua4APtrS3hAR1N3nb'1k4NODE5start2j01A1n2H12H2S3hAR1N3nb'1k4NODE1A1n2H12H2S3hAR1N3nb'1k4NODE1A1n2H12H2S1A1n1HS3hAR1A1n1HS3hAR2SP2TR1N2tf2nb3nb'2bl2ws1k2HL3TFB3DML3DBL4NODE3TRBS3hAR2SP2lo5LOIMG5start1jS1A1n1HS3hAR1A1n1HS2SP2lo3SPL1A2H1S1N2bi3nb'1k2BI2ua4NODE1x2H4FS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2JE2S0S3hAR5start1j2J41A1n2H12H2S3hAR2SP2lo5LOIMG3SPL5start1j2J41A1n2H1S3hAR1N2bi3nb'2bl1k2BI4NODE5start2j01j2Y0S3hAR2SP2TR4size1N2tf1v2nb3nb'2bl2ws1k2HL3TF03NB22VB3DML3DBL4NODE3TRB5start1j2S02uaS3hAR2SP2TR1N2tf1v2nb3nb'2bl2ws1k2HL3NB22VB3DML3DBL4NODE3TRBS3hAR2SP2TR4size1N2tf1v2nb3nb'2bl2ws1k2HL3TF03NB22VB3DML3DBL4NODE3TRB5start1j2S0S3hAR5start1j2ua3UA0S3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S02uaS3hAR2SP2TR1N2tf2nb3nb'2bl2ws1k2HL3DML3DBL1j2HjS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S02uaS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03NB22WN3DML3DBL4NODE3TRB5start1j2S0S3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03NB22WN3DML3DBL4NODE3TRB5start1j2S02uaS3hAR2SP2TR1N2tf2nb3nb'2bl2ws1k2HL3NB22WN3DML3DBL4NODE3TRBS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL2K14NODE3NI23TRB5start1j2S02uaS3hAR1N2bi3nb'2bl1k2BI4NODE2j'2Y0S2bl5start1j2JEFS3hAR2SP2TR1N2lo3nb'1k2T04NODES3hAR2SP2TR1N2lo3nb'1k2T04NODE5start2j0S3hAR2SP2TR1N2lo3nb'1k2T04NODES3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S02uaS3hAR1N3nb'1k2K04NODE3NI15start1j2J4S2SPS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03LNB3DML3DBL3HK04NODE3TRB5start2j01s2SLS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03LNB3DML3DBL3HK04NODE3TRB5start1j2S02ua1s2SLS3hAR2SP2TR4size1N2tf2lo2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S02ua1A2sz2H12H21x2HxS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start2S0S3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S0S3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3TF03DML3DBL4NODE3TRB5start1j2S02uaS3hAR2SP2TR4size1N2tf2nb3nb'2bl2ws1k2HL3DML3DBL4NODE3TRB5startS2bi2BISS2SPS2bi2BISS3hAR1N2bi3nb'1k2BI4NODE1s2I12Y0S3hAR1N2bi3nb'1k2BI4NODE5start2j01s2I12Y0S3hAR2SP2TR1N2tf2nb3nb'2bl2ws1k2HL3DML3DBL4NODE3TRB2j'3Hj'S3hAR2AL2SP2TR4size3tag1N2tf1h1v2bi2nb3nb'2bl2ws1k2SZ2TG2HL3TF02VB2BI2HR5ALWF'4IMG'2WN3DML3DBL2SN4NODE3TRB5start1j2S03TP12J42ua2j'3Hj'2NES3hAR2AL2SP2TR4size3tag1N2tf1h1v2bi2nb3nb'2bl2ws1k2SZ2TG2HL3TF02VB2BI2HR5ALWF'4IMG'2WN3DML3DBL2SN4NODE3TRB5start1j2S03TP12J42ua2j'3Hj'2NES3hAR2AL2SP2TR4size3tag1N2tf1h1v2bi2nb3nb'2bl2ws1k2SZ2TG2HL3TF02VB2BI2HR5ALWF'4IMG'2WN3DML3DBL2SN4NODE3TRB5start1j2S03TP12J42ua2j'3Hj'2NES2SP1N2lo2bi3nb'1k4NODE2ua1x2HxS2SP1N2lo2bi3nb'1k4NODE5start1j2J42ua1x2HxS3hAR1N2bi3nb'1k4NODE5start2j01A1n2H12H3S3hAR1N2bi3nb'1k4NODE1A1n2H12H3F". (* [comment removed for export] *)
  #[using="AL IMG ALWF CSOKf KL CSmono_s K_apart T_store ROOM_s"] Lemma put_mid_cfg : ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "Pra,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pr1,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Palloc,(4.&40.)Plockw,(4.&40.)PSP,$>.PF,(56.&5.(4.&40.))Pfc,(4.&20.)Pm0,P,(4.&40.)(2<.(4.&8.))Pm2,P,(4.&40.)(2<.(4.&8.))Pmo2,$3;.PTR,$>.Psize,$>.Ptag,$>.PN,$>.Ptf,$>.Plo,$>.Ph,$>.Pv,$>.Pbi,$>.Pnb,(2?.$>.)Pnb',(2?.$>.)Pbl,(2?.$>.)Pws,(2?.(4.&40.))Pfr,(2?.(4.&8.))Zk,$>.(26.(16.R;.+1.)+10000.)Zblk,$>.(17.R5.R1.)P,(0.(?.+1.R?.)(?.R?.+1>.))P,(0.(?.=R?.)(10.R?.+100.))P,(?.R18.R12.)P,(?.(16.R13.+100.)(18.+2.+3?.))P,(14.$>.(46.R14.+8.)=)P,(14.$57.(12.(4.&40.)R9.)#1>.)P,(?.=R12.)P,(?.(16.R13.+80.)(18.+2.+20.))P,(14.$>.(11.(12.$>.R=.))(26.(27.(16.R14.(18.+2.+14.))+1.)(18.+2.+14.)))P,(21.R10.R16.)P,(?.(16.R17.+2.)(27.(18.+2.+1?.)(18.+2.+1<.)))P,(0.(?.=R14.)(?.R14.R18.))P,(0.(?.=R14.)(10.R14.(18.+2.+14.)))P,(0.(?.=R17.)(10.R17.(18.+2.+40.)))P,(10.R10.(11.(12.$>.R14.)))P,(14.$>.(11.(12.$>.R15.))(16.(26.(16.R1<.+1.)+10000.)+1.))P,(15.(14.(2?.$>.)R16.R17.)(3.$>.Lua,$>.(0.(14.(2?.$>.)R17.(38.$>.R18.(8.$>.R1.(;.$>.))))Px,$>.P,A3.VCSf,R19.R17.R1.(13.(0.(?.R3.R2.)(10.R2.(16.R3.(18.+2.+14.))))))))P,Px,$>.P,A3.VCSf,R19.R17.R1.A3.VCSf,R19.R18.R2.P,(28.R18.R17.)P,(?.(43.VhAR,)R1>.)P,(?.R1?.(27.R2:.+240.))P,(?.R2;.(18.+2.+3>.))P,(14.$>.(46.R2<.+10.)=)P,(58.R29.R2=.R1:.R27.(16.R26.(2>.R25.(18.+2.+20.)))R4=.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.)P,(1:.$6.R2:.$23.(8.$9.(:.(1=.&40.R24.))(8.$9.(:.R30.)(;.$9.))))P,(24.VhAR,R2;.R1>.)P,(25.R2<.R1?.)P,(1:.$6.R2=.(16.$2=.(2>.+4.R23.))(8.$9.(1<.R32.)(;.$9.)))P,(1:.$6.R2>.$1;.(8.$9.(1<.(1=.&40.(16.R29.+1.)))(;.$9.)))P,(1:.$6.R2?.$22.(8.$9.(1<.(1=.&40.=))(;.$9.)))P,(1?.VhAR,R30.R24.)P,(20.R31.R25.R2<.)P,(34.R32.R2=.R28.)P,(55.$6.R33.R31.R25.)P,(37.R34.)P,(53.$6.R35.R2>.(16.R39.-70.))P,(54.$6.R36.)P,A3.VK,R2;.R2:.R36.P,(50.R38.R37.)P,A2.VGs,R2=.R2<.P,(39.A2.VCSf,R2>.R2=.R2>.R2=.)P,(29.A2.VCSf,R2?.R2>.R39.+?0.)P,(29.A2.VCSf,R30.R2?.R35.(27.R40.R35.))P,(35.R3>.R3=.R36.R41.R31.R30.)P,(32.$6.R3?.R3>.)(59.$6.(5:.R43.R63.R62.R61.R60.R5?.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R42.R41.R38.R3:.R3=.R39.R3<.R34.R32.R31.R40.)(4:.(4;.(4<.R50.(1=.&40.(16.R43.-70.))R62.R61.R4?.R4>.R4=.(1=.&40.=)(1=.&40.(16.R3:.+1.))(1=.&40.R2>.)R4<.R4;.R4:.R49.R48.R47.R46.(1=.&40.(16.$2=.(2>.+4.R35.)))(1=.&40.R37.)(1=.&40.$22.)(1=.&40.R36.)(1=.&40.+????.)(1=.&40.(16.R3:.+1.))(1=.&40.$5;.)(1=.&40.R36.)R56.R55.R54.R53.R52.R51.)R42.(1=.&40.+897:8.)R41.(4>.(4.&40.))R3?.(4?.$6.))R3>.))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 r1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 alloc lockw SP F fc m0 m2 mo2
      TR size tag N tf lo h v bi nb nb' bl ws fr k blk
      SZ TG T0 T1 TAL HL TF0 TFB BL WF NB2 VB BI HR KLT LNB NBC MONO BA LOIMG SPL SPH SPA
      FRP SSX DB SB TC NC MX DM DN DT HTR DST ST MI HK HJ GS DCS TCS SCS DK WM0.
    facts. pose proof WF as [WN WL]. dpose DM as (DM1 & DMF & DML). dpose DB as (DB1 & DBF & DBL).
    destruct DCS as [NBCS BLCS]. dpose BA as (BA1 & BA2 & BA3).
    assert (HK0 : 0 <= k) by (subst k; apply Z.div_pos; lia).
    pose proof (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb') DMF (Z.to_nat k) 0 ltac:(lia)) as KF.
    change (nth (Z.to_nat k) nb' 0) with (dblk nb' k) in KF. ddestruct KF as (K0 & K1 & KAL). subst blk.
    assert (SBk : forall j, 0 <= j < Z.of_nat (length bl) -> 0x65f000 <= sblk bl j /\ sblk bl j + 2^23 <= ACEIL).
    { intros j Hj. dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl) DBF (Z.to_nat j) 0 ltac:(lia)) as (X0 & X & _).
      unfold sblk. split; assumption. }
    (* [comment removed for export] *)
    assert (SN : 0 <= N + 1 < 65536 * Z.of_nat (length nb')).
    { rewrite LNB. subst k. pose proof (Z.div_mod (N + 1) 65536 ltac:(lia)). pose proof (Z.mod_pos_bound (N + 1) 65536 ltac:(lia)). lia. }
    ddestruct (DN (N + 1) SN) as (hsh & sid & lnk & NDC & _ & _). unfold dnode in NDC. fold k in NDC.
    pose proof (dnode_in_blk nb' (N + 1) ltac:(lia)) as [NI1 NI2]. unfold dnode in NI1, NI2. fold k in NI1, NI2.
    set (NODE := dblk nb' k + 16 * ((N + 1) mod 65536)) in *.
    pose proof (u64arr_bound _ _ _ _ HTR) as TRB. rewrite HL in TRB. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in TRB.
    pose proof (args_view m2 SP fr TR size tag ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 SZ TG ltac:(lia) FRP) as ARGS.
    dpose DST as (DS & CST & c1 & c2 & c3 & M1 & M2 & M3).
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL (CSf nb' bl) (K nb' bl) _ _ _ mo2 (KL nb' bl) HK); [exact HJ| |].
    {
      eapply (seg_mid AL IMG ALWF (CSf nb' bl) (CSOKf nb' bl) r1 gp tp s10 s11 t0 t1 t2 t3 t4 t5 t6 a1 a2 a3 a4 a5 a6 a7 alloc lockw hsh sid
                (Z_to_bv 64 lnk) lnk s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ra SP F fc m2 TR size tag tf lo h v bi (N + 1) (dblk nb' k) bl ws fr);
        try eassumption; try lia.
      all: first [ apply NBCS; lia
                 | intros j' Hj'; apply (BA3 k j'); lia
                 | intros j' Hj'; split; [apply SB; exact Hj'| apply BLCS; exact Hj']
                 | match goal with |- ?G => idtac "SM" G end ]. }
    cbn beta. intros ms4 mo4 PO HK4 MM4 HJ4.
    ddestruct PO as (start & SE & [(JL & SBE & FIN) | ASC]).
    + (* [comment removed for export] *)
      ddestruct FIN as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & sidw & m4 & -> & MU4 & WM4 & MI4 & NODE4 & BKT4 & SS4 & DB4 & STB4 & ST4).
      cbn [ms_mem MS MSsvc] in HJ4.
      fold NODE in MU4, NODE4.
      set (j0 := start / 2^20) in *.
      assert (J0 : 0 <= j0 < Z.of_nat (length bl)) by (split; [subst j0; apply Z.div_pos; lia| exact JL]).
      pose proof (tf_potential tf start (size + 1) ltac:(lia) TF0 SE) as [TP1 TP2].
      pose proof (len_fin tf start (size + 1) _ ltac:(lia) ltac:(lia) BL JL SBE) as BL'.
      (* [comment removed for export] *)
      assert (LOW : forall A n, 0x10000 <= A /\ A + n <= 0x65f000 -> (A + n <= A_SS \/ A_SS + 16 + 16 * 4096 <= A) -> (A + n <= A_DEP + 4 * bi \/ A_DEP + 4 * bi + 4 <= A) ->
                 disjoint_from [(lo, SP); (A_SS, A_SS + 16 + 16 * 4096); (sblk bl j0, sblk bl j0 + 2^23); (NODE, NODE + 16); (A_DEP + 4 * bi, A_DEP + 4 * bi + 4)] A n).
      { intros A n H1 H2 H3. pose proof (SBk j0 J0) as [Y _]. cbn [disjoint_from]. clear - H1 H2 H3 Y LOIMG K0 NI1. repeat split; lia. }
      apply aevtS_now.
      eexists. dexists mo4, nb', bl, (N + 1), (start + (size + 1)), (N + 1). deexists 14. exists m4.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact HK4|]. split; [exact HJ4|].
      split.
      { (* [comment removed for export] *)
        split. { eapply rw_cells_transport; [exact NC| exact MU4| exact WM4| apply LOW; unfold A_DEP_N, A_SS, A_DEP; cbn; clear -BI; lia]. }
        split. { eapply (dtab_of_but m4 N (N + 1) bi (N + 1)); [| exact BI| exact BKT4| lia| lia].
                 eapply (dtab_but_transport _ m2 m4 N bi DT MU4 WM4). intros i Hi NE. apply LOW; unfold A_DEP, A_SS; clear -Hi NE BI; lia. }
        split. { eapply (dmap1_transport _ m2 m4 nb' DM MU4 WM4). apply LOW; unfold A_DEP_MAP1, A_SS, A_DEP; clear -BI; lia. }
        split. { eapply (dnodes_reest _ m2 m4 nb' N (Z_to_bv 64 h) sidw v DN MU4 WM4); [| exact SN| | lia].
                 - intros s Hs NE. pose proof (dnode_in_blk nb' s ltac:(lia)) as [I1 I2].
                   assert (SL : s / 65536 < Z.of_nat (length nb')) by (apply Z.div_lt_upper_bound; lia).
                   dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb') DMF (Z.to_nat (s / 65536)) 0 ltac:(pose proof (Z.div_pos s 65536); lia)) as (Y0 & Y1 & _).
                   change (nth (Z.to_nat (s / 65536)) nb' 0) with (dblk nb' (s / 65536)) in Y0, Y1.
                   pose proof (BA3 (s / 65536) j0 ltac:(split; [apply Z.div_pos; lia| exact SL]) J0) as Y2.
                   pose proof (dnode_apart nb' bl s (N + 1) BA ltac:(lia) ltac:(lia) NE SL ltac:(lia)) as Y3. change (dnode nb' (N + 1)) with NODE in Y3.
                   cbn [disjoint_from]. unfold A_SS, A_DEP. clear - I1 I2 Y0 Y1 Y2 Y3 LOIMG BI. repeat split; lia.
                 - unfold dnode. fold k NODE. exact NODE4. }
        split. { split; [clear -WN NB2; lia| exact LNB]. }
        split. { eapply rw_cells_transport; [exact MX| exact MU4| exact WM4| apply LOW; unfold A_DEP_NODES, A_SS, A_DEP; cbn; clear -BI; lia]. }
        split. { exists alloc. exact SS4. }
        split; [exact DB4|].
        split. { eapply (sblks_set m2 m4 bl j0 SB J0 STB4). intros j Hj NE.
                 eapply stk_transport_disjoint; [exact (SB j Hj)| exact MU4| exact WM4|].
                 pose proof (SBk j Hj) as [Y0 Y1]. pose proof (BA2 j j0 Hj J0 NE) as Y2. pose proof (BA3 k j ltac:(lia) Hj) as Y3.
                 cbn [disjoint_from]. unfold A_SS, A_DEP. clear - Y0 Y1 Y2 Y3 LOIMG BI NI1 NI2. repeat split; lia. }
        split; [lia|]. split; [exact BL'| exact BA]. }
      split; [split; [exact NBCS| exact BLCS]|].
      split. { eapply (depot_statics_transport _ m2 m4 DST MU4). intros A n H. apply LOW; unfold A_SS, A_DEP; clear -H LOIMG BI; lia. }
      split; [lia|]. split; [lia|]. split; [exact TP1|]. split; [exact TP2|].
      split; [exact MONO|].
      split. { destruct NBC as [-> | (ua & -> & APu)].
               - dexists [], []. rewrite !app_nil_r. repeat split; constructor.
               - dexists [ua], []. rewrite app_nil_r. repeat split; constructor; [exact APu| constructor]. }
      split. { eapply (dkeep_munch _ m0 m2 m4); [exact DK| exact MU4|]. intros x H1 H2 H3 H4. cbn [outside].
               specialize (H3 k ltac:(lia)). specialize (H4 j0 J0). unfold A_SS, A_DEP_END, A_DEP in *. clear - H1 H2 H3 H4 BI NI1 NI2. repeat split; lia. }
      split; [eapply wmono_trans; [exact WM0| exact WM4]|]. split; [exact ST4|]. split; [exact MI4|].
      eapply u64arr_transport; [exact HTR| exact MU4| exact WM4|]. replace (8 * Z.of_nat (length ws)) with 240 by (rewrite HL; reflexivity).
      pose proof (SBk j0 J0) as [_ Y]. cbn [disjoint_from]. unfold A_SS, A_DEP. clear - T0 SPL LOIMG BI Y NI2 K1. repeat split; lia.
    + (* [comment removed for export] *)
      ddestruct ASC as (x5 & x6 & x7 & x12 & x14 & x16 & x17 & x28 & pk & sid' & lnkw' & bk & fr1 & m4 & -> &
                       MU4 & WM4 & MI4 & FRA4 & IX4 & FRS4 & F14 & PK4 & F34 & FRP4 & ARGS4 & NODE4 & BK4 & SS4 & DB4 & ST4 & SBE & JE & S0).
      cbn [ms_mem MS MSsvc] in HJ4.
      fold NODE in MU4, NODE4, FRS4.
      pose proof (tf_potential tf start (size + 1) ltac:(lia) TF0 SE) as [TP1 TP2].
      set (j := start / 2^20) in *.
      assert (J4 : 0 <= j < 4096).
      { split; [subst j; apply Z.div_pos; lia|]. rewrite JE, BL. apply Z.div_lt_upper_bound; lia. }
      dpose DB4 as (DB41 & _ & _). destruct (DB41 j J4) as (stored & BX4).
      unfold sptr in BX4. replace (j <? Z.of_nat (length bl)) with false in BX4 by (symmetry; apply Z.ltb_ge; lia).
      assert (LOW4 : forall A n, 0x10000 <= A /\ A + n <= 0x65f000 -> (A + n <= A_SS \/ A_SS + 16 + 16 * 4096 <= A) ->
                 disjoint_from [(lo, SP); (A_SS, A_SS + 16 + 16 * 4096); (NODE, NODE + 16)] A n).
      { intros A n H1 H2. cbn [disjoint_from]. clear - H1 H2 LOIMG NI1 K0. repeat split; lia. }
      assert (DST4 : depot_statics m4) by (eapply (depot_statics_transport _ m2 m4 DST MU4); intros A n H; apply LOW4; unfold A_SS; clear - H; lia).
      dpose DST4 as (_ & CST4 & _).
      (* [comment removed for export] *)
      eapply aevtS_bind.
      { eapply (store_create_cfg AL IMG ALWF CSf K CSOKf KL CSmono_s K_apart Gs T_store ROOM_s gp tp s10 s11 t4 t5 t6 x5 x6 x7 x12 x14 x16 x17 x28 stored alloc
                  SP F fc m4 mo4 lo (N + 1) v size tag start (start + (size + 1)) nb' bl); try eassumption; try lia.
        all: match goal with |- ?G => idtac "SC" G end. }
      intros c5 SCP. ddestruct SCP as (a & mo5 & ms5 & -> & SMP & HK5 & HJ5 & CR5 & UAL & UA0 & UA1 & APu).
      ddestruct SMP as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & alloc' & m5 & -> & MU5 & WM5 & MI5 & BX5 & AX5 & ZB5 & ST5).
      set (ua := bv_unsigned a) in *. clearbody ua. fold j in MU5, BX5 |- *.
      (* [comment removed for export] *)
      assert (APstk : forall A sz, lo <= A -> A + sz <= SP -> 0 < sz -> A + sz <= ua \/ ua + 2^23 <= A).
      { intros A sz H1 H2 H3. eapply (apart_of (CSf nb' bl)); [exact APu| | exact H3| lia]. intros x Hx. apply SCS. lia. }
      assert (APtr : TR + 240 <= ua \/ ua + 2^23 <= TR).
      { eapply (apart_of (CSf nb' bl)); [exact APu| | lia| lia]. intros x Hx. apply TCS. exact Hx. }
      assert (APn : forall k', 0 <= k' < Z.of_nat (length nb') -> dblk nb' k' + 2^20 <= ua \/ ua + 2^23 <= dblk nb' k').
      { intros k' Hk'. eapply (apart_of (CSf nb' bl)); [exact APu| | lia| lia]. intros x Hx. apply (NBCS k' Hk'). exact Hx. }
      assert (APs : forall j', 0 <= j' < Z.of_nat (length bl) -> sblk bl j' + 2^23 <= ua \/ ua + 2^23 <= sblk bl j').
      { intros j' Hj'. eapply (apart_of (CSf nb' bl)); [exact APu| | lia| lia]. intros x Hx. apply (BLCS j' Hj'). exact Hx. }
      pose proof (APn k ltac:(lia)) as APk.
      assert (LOW5 : forall A n, 0x10000 <= A /\ A + n <= 0x65f000 -> (A + n <= A_SS \/ A_SS + 16 + 16 * 4096 <= A) ->
                 disjoint_from [(lo, SP + -208); (A_SS + 16 + 16 * j, A_SS + 16 + 16 * j + 16); (A_SS + 8, A_SS + 16); (ua, ua + 2 ^ 23)] A n).
      { intros A n H1 H2. unfold A_SS in *. cbn [disjoint_from]. clear - H1 H2 LOIMG J4 UA0. repeat split; lia. }
      assert (HI5 : forall A n, SP + -208 <= A -> A + n <= SP -> 0 < n ->
                 disjoint_from [(lo, SP + -208); (A_SS + 16 + 16 * j, A_SS + 16 + 16 * j + 16); (A_SS + 8, A_SS + 16); (ua, ua + 2 ^ 23)] A n).
      { intros A n H1 H2 H3. pose proof (APstk A n ltac:(clear - H1 SPL; lia) H2 H3) as Y. unfold A_SS in *. cbn [disjoint_from]. clear - H1 H2 Y LOIMG J4 SPL. repeat split; lia. }
      assert (HTR5 : u64arr asegs m5 TR ws).
      { eapply u64arr_transport; [| exact MU5| exact WM5|].
        { eapply u64arr_transport; [exact HTR| exact MU4| exact WM4|]. replace (8 * Z.of_nat (length ws)) with 240 by (rewrite HL; reflexivity).
          cbn [disjoint_from]. unfold A_SS. clear - T0 SPL LOIMG NI2 K1. repeat split; lia. }
        replace (8 * Z.of_nat (length ws)) with 240 by (rewrite HL; reflexivity).
        cbn [disjoint_from]. unfold A_SS. clear - T0 SPL LOIMG J4 APtr. repeat split; lia. }
      assert (DST5 : depot_statics m5) by (eapply (depot_statics_transport _ m4 m5 DST4 MU5); intros A n H; apply LOW5; unfold A_SS; clear - H; lia).
      dpose DST5 as (DS5 & _ & _).
      assert (SCS5 : crange (CSf nb' (bl ++ [ua])) lo (SP - lo)) by (intros x Hx; apply CSmono_s; apply SCS; exact Hx).
      assert (SBN : sblk (bl ++ [ua]) j = ua) by (rewrite JE; apply sblk_app_new).
      replace (Z_to_bv 64 (ua + 8 * (start mod 2 ^ 20))) with (Z_to_bv 64 (sblk (bl ++ [ua]) (start / 2^20) + 8 * (start mod 2^20))) by (fold j; rewrite SBN; reflexivity).
      (* [comment removed for export] *)
      eapply (evtA_aevtS_KJ AL (CSf nb' (bl ++ [ua])) (K nb' (bl ++ [ua])) _ _ _ mo5 (KL nb' (bl ++ [ua])) HK5); [exact HJ5| |].
      {
        eapply (seg_tail AL IMG ALWF (CSf nb' (bl ++ [ua])) (CSOKf nb' (bl ++ [ua])) gp tp s10 s11 y5 y6 y7 y28 y29 y30 y31 y12 y14 y16 y17 y11 y13 y15
                  alloc' pk sid' bk lnkw' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ra SP F fc m5 TR size tag start lo h v bi (N + 1) NODE (bl ++ [ua])
                  (firstn (Z.to_nat (8 * size)) (u64s ws)) fr fr1); try hassumption; try lia. (* [comment removed for export] *)
        all: change (start / 2^20) with j; rewrite ?SBN.
        * rewrite app_length. cbn [length]. clear - JE. lia.
        * intros x Hx. apply CSmono_s. apply (NBCS k); [lia|]. clear - Hx NI1 NI2. lia.
        * clear - APk NI1 NI2. lia.
        * assert (FRS : rw_cells asegs m4 (SP + -208) [C8 (Z_to_bv 64 start); C8 (Z_to_bv 64 v); C8 (Z_to_bv 64 A_DEP_NODES); C8 (Z_to_bv 64 h);
                                                     C8 (Z_to_bv 64 (A_DEP + 4 * bi)); C8 (Z_to_bv 64 NODE); C8 (Z_to_bv 64 NODE); C8 (Z_to_bv 64 0x0892e4)]).
          { apply (proj2 (rw_cells_app asegs m4 (SP + -208) [C8 (Z_to_bv 64 start)] _)). split; [exact IX4|].
            cbn [cells_size csize Nat.add]. replace (SP + -208 + Z.of_nat 8) with (SP + -200) by lia. exact FRS4. }
          eapply rw_cells_transport; [exact FRS| exact MU5| exact WM5| apply HI5; cbn; clear; lia].
        * eapply rw_cells_transport; [exact F14| exact MU5| exact WM5| apply HI5; cbn; clear; lia].
        * eapply rw_cells_transport; [exact PK4| exact MU5| exact WM5| apply HI5; cbn; clear; lia].
        * eapply rw_cells_transport; [exact F34| exact MU5| exact WM5| apply HI5; cbn; clear; lia].
        * unfold dput_frame in *. eapply rw_cells_transport; [exact FRP4| exact MU5| exact WM5| apply HI5; cbn; clear; lia].
        * eapply ro_cells_transport; [exact ARGS4| exact MU5| apply HI5; cbn; clear; lia].
        * apply (proj1 (rw_cells_app asegs m4 A_SS [C8 (Z_to_bv 64 (start + (size + 1)))] _)) in SS4. destruct SS4 as [SS40 _].
          apply (proj2 (rw_cells_app asegs m5 A_SS [C8 (Z_to_bv 64 (start + (size + 1)))] _)). split.
          -- eapply rw_cells_transport; [exact SS40| exact MU5| exact WM5|]. unfold A_SS in *. cbn [disjoint_from cells_size csize Nat.add]. clear - LOIMG J4 UA0. repeat split; lia.
          -- cbn [cells_size csize Nat.add]. exact AX5.
        * eapply (dblocks_app _ m4 m5 bl ua stored DB4 MU5 WM5); try hassumption. (* [comment removed for export] *)
          -- intros j' Hj' NE. unfold A_SS in *. cbn [disjoint_from]. clear - Hj' NE J4 JE LOIMG UA0. repeat split; lia.
          -- rewrite <- JE. exact BX5.
          -- apply Nat2Z.inj_lt. change (Z.of_nat (Init.Nat.of_num_uint _)) with 4096%Z. clear - J4 JE. lia.
        * eapply rw_cells_transport; [exact NODE4| exact MU5| exact WM5|]. unfold A_SS in *. cbn [disjoint_from cells_size csize Nat.add]. clear - LOIMG J4 APk NI1 NI2 K0 K1. repeat split; lia.
        * eapply rw_cells_transport; [exact BK4| exact MU5| exact WM5| apply LOW5; unfold A_DEP, A_SS; cbn; clear - BI; lia].
        * destruct HTR5 as [HB _].
          destruct (bytes_at_app asegs m5 TR (firstn (Z.to_nat (8 * size)) (u64s ws)) (skipn (Z.to_nat (8 * size)) (u64s ws))) as [X _].
          rewrite firstn_skipn in X. exact (proj1 (X HB)).
        * rewrite length_firstn, u64s_length, HL. lia.
        * apply zblock_stk; [exact ZB5| clear; lia].
        * exact CR5.
        * intros x Hx. apply CSmono_s. apply TCS. exact Hx. }
      cbn beta. intros ms6 mo6 PO6 HK6 MM6 HJ6.
      ddestruct PO6 as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & sidw & m6 & -> & MU6 & WM6 & MI6 & NODE6 & BKT6 & SS6 & DB6 & STB6 & ST6).
      change (start / 2^20) with j in MU6, STB6. rewrite SBN in MU6, STB6.
      (* [comment removed for export] *)
      set (W6 := [(lo, SP); (A_SS, A_SS + 16 + 16 * 4096); (ua, ua + 2^23); (NODE, NODE + 16); (A_DEP + 4 * bi, A_DEP + 4 * bi + 4)]).
      assert (MU26 : munch W6 m2 m6).
      { eapply munch_trans. { eapply munch_weaken; [| exact MU4]. unfold sub_fp, W6; cbn [outside]. clear. intros x Hx. lia. }
        eapply munch_trans. { eapply munch_weaken; [| exact MU5]. unfold sub_fp, W6, A_SS; cbn [outside]. clear - J4 SPL. intros x Hx. lia. }
        eapply munch_weaken; [| exact MU6]. unfold sub_fp, W6; cbn [outside]. clear. intros x Hx. lia. }
      assert (WM26 : wmono asegs m2 m6) by (eapply wmono_trans; [exact WM4| eapply wmono_trans; [exact WM5| exact WM6]]).
      assert (LOW6 : forall A n, 0x10000 <= A /\ A + n <= 0x65f000 -> (A + n <= A_SS \/ A_SS + 16 + 16 * 4096 <= A) -> (A + n <= A_DEP + 4 * bi \/ A_DEP + 4 * bi + 4 <= A) ->
                 disjoint_from W6 A n).
      { intros A n H1 H2 H3. unfold W6. cbn [disjoint_from]. clear - H1 H2 H3 LOIMG K0 NI1 UA0. repeat split; lia. }
      assert (HTR6 : u64arr asegs m6 TR ws).
      { eapply u64arr_transport; [exact HTR| exact MU26| exact WM26|]. replace (8 * Z.of_nat (length ws)) with 240 by (rewrite HL; reflexivity).
        unfold W6, A_SS, A_DEP. cbn [disjoint_from]. clear - T0 SPL LOIMG BI APtr NI2 K1. repeat split; lia. }
      assert (BL' : Z.of_nat (length (bl ++ [ua])) = (start + (size + 1) + 2^20 - 1) / 2^20).
      { rewrite app_length. cbn [length]. replace (start + (size + 1) + 2^20 - 1) with ((start + (size + 1) - 1) + 1 * 2^20) by lia.
        rewrite Z.div_add by lia. clear - SBE JE. lia. }
      apply aevtS_now.
      eexists. dexists mo6, nb', (bl ++ [ua]), (N + 1), (start + (size + 1)), (N + 1). deexists 14. exists m6.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact HK6|]. split; [exact HJ6|].
      split.
      { (* [comment removed for export] *)
        split. { eapply rw_cells_transport; [exact NC| exact MU26| exact WM26| apply LOW6; unfold A_DEP_N, A_SS, A_DEP; cbn; clear -BI; lia]. }
        split. { eapply (dtab_of_but m6 N (N + 1) bi (N + 1)); [| exact BI| exact BKT6| lia| lia].
                 eapply (dtab_but_transport _ m2 m6 N bi DT MU26 WM26). intros i Hi NE. apply LOW6; unfold A_DEP, A_SS; clear -Hi NE BI; lia. }
        split. { eapply (dmap1_transport _ m2 m6 nb' DM MU26 WM26). apply LOW6; unfold A_DEP_MAP1, A_SS, A_DEP; clear -BI; lia. }
        split. { eapply (dnodes_reest _ m2 m6 nb' N (Z_to_bv 64 h) sidw v DN MU26 WM26); [| exact SN| | lia].
                 - intros s Hs NE. pose proof (dnode_in_blk nb' s ltac:(lia)) as [I1 I2].
                   assert (SL : s / 65536 < Z.of_nat (length nb')) by (apply Z.div_lt_upper_bound; lia).
                   dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb') DMF (Z.to_nat (s / 65536)) 0 ltac:(pose proof (Z.div_pos s 65536); lia)) as (Y0 & Y1 & _).
                   change (nth (Z.to_nat (s / 65536)) nb' 0) with (dblk nb' (s / 65536)) in Y0, Y1.
                   pose proof (APn (s / 65536) ltac:(split; [apply Z.div_pos; lia| exact SL])) as Y2.
                   pose proof (dnode_apart nb' bl s (N + 1) BA ltac:(lia) ltac:(lia) NE SL ltac:(lia)) as Y3. change (dnode nb' (N + 1)) with NODE in Y3.
                   unfold W6. cbn [disjoint_from]. unfold A_SS, A_DEP. clear - I1 I2 Y0 Y1 Y2 Y3 LOIMG BI. repeat split; lia.
                 - unfold dnode. fold k NODE. exact NODE6. }
        split. { split; [clear -WN NB2; lia| exact LNB]. }
        split. { eapply rw_cells_transport; [exact MX| exact MU26| exact WM26| apply LOW6; unfold A_DEP_NODES, A_SS, A_DEP; cbn; clear -BI; lia]. }
        split. { exists alloc'. exact SS6. }
        split; [exact DB6|].
        split. { intros j' Hj'. rewrite app_length in Hj'. cbn [length] in Hj'.
                 destruct (Z.eq_dec j' (Z.of_nat (length bl))) as [->|NE]; [rewrite sblk_app_new; exact STB6|].
                 rewrite sblk_app_old by lia.
                 eapply stk_transport_disjoint; [exact (SB j' ltac:(lia))| exact MU26| exact WM26|].
                 pose proof (SBk j' ltac:(lia)) as [Y0 Y1]. pose proof (APs j' ltac:(lia)) as Y2. pose proof (BA3 k j' ltac:(lia) ltac:(lia)) as Y3.
                 unfold W6. cbn [disjoint_from]. unfold A_SS, A_DEP. clear - Y0 Y1 Y2 Y3 LOIMG BI NI1 NI2. repeat split; lia. }
        split; [lia|]. split; [exact BL'|]. apply blocks_apart_app_s; [exact BA| exact APn| exact APs]. }
      split; [eapply depot_cs_app_s; [split; [exact NBCS| exact BLCS]| intros x Hx; apply CSmono_s; exact Hx| exact CR5]|].
      split. { eapply (depot_statics_transport _ m2 m6 DST MU26). intros A n H. apply LOW6; unfold A_SS, A_DEP; clear -H LOIMG BI; lia. }
      split; [lia|]. split; [lia|]. split; [exact TP1|]. split; [exact TP2|].
      split; [intros x Hx; apply CSmono_s; apply MONO; exact Hx|].
      split. { assert (APu0 : forall x, CSf nb bl x -> ~ (ua <= x < ua + 2^23)) by (intros x Hx; apply APu; apply MONO; exact Hx).
               destruct NBC as [-> | (ua0 & -> & APu1)].
               - dexists [], [ua]. rewrite app_nil_r. repeat split; constructor; [exact APu0| constructor].
               - dexists [ua0], [ua]. repeat split; constructor; [exact APu1| constructor| exact APu0| constructor]. }
      split. { apply (dkeep_app_s _ _ _ _ _ _ ua) in DK. eapply (dkeep_munch _ m0 m2 m6); [exact DK| exact MU26|]. intros x H1 H2 H3 H4. unfold W6. cbn [outside].
               specialize (H3 k ltac:(lia)). specialize (H4 (Z.of_nat (length bl))). rewrite app_length, sblk_app_new in H4. cbn [length] in H4. specialize (H4 ltac:(lia)).
               unfold A_SS, A_DEP_END, A_DEP in *. clear - H1 H2 H3 H4 BI NI1 NI2. repeat split; lia. }
      split; [eapply wmono_trans; [exact WM0| exact WM26]|]. split; [exact ST6|]. split; [exact MI6|].
      exact HTR6.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0220@L10469396132.198L10645720270.160L1120798417.198 L11388733925.5  L11662295497.198L11730861363.12 L11813486156.6  L13266555807.5  L13282201623.143L14082356371.3  L15038746642.12 L15365318980.12 L16489652470.198L17457240616.13 L18394537852.198L19004860963.156L19236835972.198L20516116035.7  L20777950878.198L21182865027.156L21498147548.9  L21674702615.198L22958115045.5  L23440988032.5  L23882044159.4  L24420784062.2  L25874386346.8  L26043710162.8  L26220076261.5  L26255031327.198L27183294911.5  L27189815741.3  L2738772588.198 L27611534642.198L28444717224.3  L28839814202.198L29001690053.198L29787979728.5  L32132320836.9  L32745426256.8  L33349343266.13 L33670951324.3  L33977671396.160L34195014240.13 L34389606463.198L34588976019.3  L3504007805.3   L35078138783.5  L35078138783.8  L35554535166.198L35586271019.13 L35633449176.198L36007300691.13 L37533639489.6  L37533639489.8  L37622513875.7  L37622514516.12 L38465438810.203L38623496502.13 L38867643427.9  L40202040220.5  L40212493214.3  L41149365743.13 L41789703549.13 L42333736447.12 L43063011400.7  L43244765774.198L44045981755.13 L44660010038.3  L4501636134.7   L45082835543.13 L45156159888.3  L45937034112.5  L46395999815.8  L46560011780.5  L46690244143.8  L48660839635.198L50161227523.198L51627111274.4  L52379386197.198L5302396531.194 L53601101470.3  L53657259608.12 L54197329704.5  L54928322635.12 L55356842776.3  L55708476389.5  L5586622171.8   L55944264660.119L56307104881.143L56897096256.5  L56897133612.8  L56998682637.4  L57553464385.12 L57769346761.143L58591604064.160L58815186712.9  L5952703498.13  L60106130471.145L60106130471.160L60106130471.200L60654138832.13 L60844587925.5  L61703264049.198L62513266742.13 L629415095.119  L63027414623.13 L63169161138.6  L63169161138.9  L63178178455.198L65092012984.5  L65874334313.13 L66544438742.9  L66566358642.200L66756799127.156L67784624500.194L67788670256.197L67790767859.198L67790776620.198L68247675864.156L68617541248.5  L68639557404.5  L68650207006.3  L8794502284.3   L8805086350.5   L9185353252.198 L9403698362.13  L953355661.9    L9586000409.5   L9593940499.8   00000100b00c00n00o01N01Y01f02Z02_03A03Q03R03e03f03g03h04404504d05105205=05B05O05V05f06706B06C06Q06_06`06a06l06m06n07907G07Z08008108_09309409909=09O09a09b0::0:;0:L0:`0;40;@0;T0<F0<b0=50=C0=Q0=g0>70>M0>_0>`0?40?B0?V0?m0@20@70@B0@M0@W0@X0AE0AQ0AR0B?0BM0Bb0C70CN0CX0Cb0D>0Dj0ER0Ee0F80FD0FT0GD0H60HW0Hh0IU0JB0K40KO0Kc0Kd0LA0LB0LS0Lh0M=0M>0MM0Mi0N10O10O20O_0PL0Q90Qf0Qg0Ql0R:0RH0RV0Rd0Re0S;0SF0SK0SUFS3hAR2SP2TR1N2tf2nb2bl2ws2HL3NB22WN3DML3DBL3TRB1kFS3hAR2bi2BIFS3hAR2SP2TR1N2lo2T05LOIMG3SPL1kS3hAR1A1n1HS2SP2lo1A1n1HS3hAR2SP2TR4size1N2tf2nb2bl2ws2SZ2HL3TF03DML3DBL3TRBS3hARS3hAR2SP2TR1N2lo2T05LOIMG3SPL1k2KBS1N2nb1k2KB1x2H2FS3hAR1N1k2KB1A1n2H2FFFS2bi2BI1x2H2FS3hAR2SP2TR1N2tf2nb2bl2ws2HL2WL3DML3DBL3TRB3KLTS3hAR2bl1j2X0FS3hAR2bi2BIS3hARS1N2nb3KEQ2KBS2SP2loS3hAR2bi2BI1b2X0S3hAR2bi2BI1A1n1HS3hAR2bi2BIFS3hAR2lo5LOIMGS3hAR2lo5LOIMGFFS2SP2lo3SPLFFS3hAR2bi2BIS2SP2lo1A1n2H1S3hAR2bi2BI1i2Hi2NES3hAR2SP1N2lo1k1A1n2H1SS3hAR2SP2TR1N2tf2nb2bl2ws2HL3DML3DBL3TRB1k3KEQS3hAR1N2bl1k2KB1j2X0FS3hARS2SPS3hAR2lo5LOIMG1b1XS3hAR2lo5LOIMG1b1XFS3hAR1N2nb2ua3UA02k'3Hk'FS3hAR1N2nb2k'3Hk'S3hAR2lo5LOIMG1A1n1HS3hAR2lo5LOIMG1A1n1HS2bi2BI1x2H2S1N2nb1k3KEQ2KB1x2H2S3hAR2SP2TR1N2tf2nb2bl2ws2HL3DML3DBL3TRB1k2ua1i2HiS3hAR2SP1N2lo2bl5LOIMG1k1j1XS3hAR2bl2bi2BI1j2X0S3hAR2lo5LOIMGS3hAR2lo5LOIMGS3hAR1N2bl1k2KB2ua1j1YS3hAR1N1k1A1n2H2S2SP1N2lo2nb1k2KB1x2H1S2SP2lo2bi2BI1x2H1FS3hAR1N2nb1k2KB1i2X0S3hAR2lo5LOIMGS1N2nb2WN3DML3KEQ2NKS3hAR1N1k2ua3UA01A1n2H2S3hARS3hARS3hAR1A1n1HS3hAR2bi2BIS3hAR1b2X0FS3hAR2SP2TR1N2tf2nb2bl2ws2HL3DML3DBL3TRB1k2uaS1N2nb1k3KEQFS3hAR2SP2TR1N2tf2nb2bl2ws2HL3DML3DBL3TRB1k2uaS3hAR2lo5LOIMGS3hAR2SP2TR1N2lo2T01kS3hAR2SP2lo5LOIMG3SPLS3hAR2TR1N1k2KB2ua4APtrS2SP2TR2T0S3hAR1i2HiS3hAR2SP1N2lo5LOIMG3SPL1k2KBS3hAR2SP2TR1N2tf2nb2bl2ws2HL3TFB3DML3DBL3TRBS3hAR2SP2TR1N2tf2nb2bl2ws2HL3DML3DBL3TRBS3hAR2lo5LOIMG1i2HiS3hAR2lo5LOIMG1i2HiS1N2nb1k3KEQS1N2nb1k2ua1x2H3S3hAR2SP2TR4size1N2tf2nb2bl2ws2SZ2HL3DML3DBL3TRBS3hAR2SP2TR1N2tf2nb2bl2ws2HL2WN3DML3DBL3TRB1v2VB1kS3hAR2SP2TR2lo2T05LOIMG3SPL2bi2BIS3hAR1N2nb1k1i2X0S3hAR2SP2TR1N2tf2nb2bl2ws2HL3DML3DBL3TRB1j2HjS3hAR2SP2TR1N2tf2nb2bl2ws2HL3DML3DBL3TRB1j2HjS3hAR2SP2TR1N2tf2nb2bl2ws2HL3DML3DBL3TRB1k2ua1j2HjS3hAR1N2nb3KEQ2KB2k'3Hk'2NES3hAR2lo5LOIMG2bi2BIFS3hAR2SP1N2lo2nb5LOIMG2k'3Hk'FS3hAR1N2bl1k1j2X0S3hAR2lo2bl5LOIMG1j1XS3hAR2lo2bl5LOIMG1j1XFS1N2nb1k3KEQ2NKS3hAR2SP1N2lo2nb5LOIMG1k1i1XS1A1n2H3S3hAR2SP2TR1N2tf2lo2nb2bl2ws2HL3DML3DBL3TRB1k2ua1A2sz2H12H21x2HxFS3hAR2SP2TR1N2tf2nb2bl2ws2HL3DML3DBL3TRB1k2uaS3hAR2SP2TR1N2tf2nb2bl2ws2HL3DML3DBL3TRB1k2uaS3hAR2SP2TR1N2tf2nb2bl2ws2HL3DML3DBL3TRB1k2uaS3hAR2SP2TR1N2tf2nb2bl2ws2HL3DML3DBL3TRB1k2uaFS3hARS3hAR2lo5LOIMGS3hAR2lo5LOIMGS3hAR2lo5LOIMGS3hAR2lo5LOIMGFS3hAR1N2nb1k2KB2ua1i1YS2bi1A1n2H2S3hARS3hAR1i2Hi". (* [comment removed for export] *)
  #[using="AL IMG ALWF CSOKf KL CSmono_n CSmono_s K_apart T_node T_store ROOM_n ROOM_s"] Theorem depot_put_cfg : ltac2:(CDefT.buildp (gd_tbl_AW_DepotTop ()) "Pra,(4.&40.)Pgp,(4.&40.)Ptp,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Ps5,(4.&40.)Ps6,(4.&40.)Ps7,(4.&40.)Ps8,(4.&40.)Ps9,(4.&40.)Ps10,(4.&40.)Ps11,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)PSP,$>.PF,(56.&5.(4.&40.))Pfc,(4.&20.)Pm,P,(4.&40.)(2<.(4.&8.))Pmo,$3;.PTR,$>.Psize,$>.Ptag,$>.PN,$>.Ptf,$>.Plo,$>.Pnb,(2?.$>.)Pbl,(2?.$>.)Pws,(2?.(4.&40.))P,(0.(?.+1.R8.)(?.R8.+1>.))P,(0.(?.=R8.)(10.R8.+100.))P,(?.R10.R;.)P,(?.(16.R<.+100.)(18.+2.+3?.))P,(14.$>.(46.R=.+8.)=)P,(55.$6.R10.R>.R6.)P,(14.$57.(12.(4.&40.)R7.)#1>.)P,(29.A2.VCSf,R:.R9.R10.+?0.)P,(51.R13.R>.R;.R=.R:.)P,(39.A2.VCSf,R<.R;.R<.R;.)P,(37.R15.)P,(?.(16.R10.+80.)(18.+2.+20.))P,(?.(16.R12.+2.)(27.(18.+2.+1?.)(18.+2.+1<.)))P,(53.$6.R18.R11.R1;.)P,(?.(43.VhAR,)R12.)P,(?.R13.(27.R1=.+240.))P,(?.R1>.(18.+2.+3>.))P,(14.$>.(46.R1?.+10.)=)P,(29.A2.VCSf,R15.R14.R16.(27.R20.R16.))P,(54.$6.R1>.)P,A3.VK,R17.R16.R1>.P,(50.R20.R1?.)P,A2.VGn,R19.R18.P,A2.VGs,R1:.R19.P,Px,$>.A2.VGs,(38.$>.R1<.(8.$>.R1.(;.$>.)))R1;.(59.$6.(5:.R27.R43.R42.R41.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R26.R25.R1=.R1?.R22.R1>.R21.R1<.R1;.R1:.R24.)(4:.(4;.(4<.R43.(1=.&40.R27.)R42.R41.R40.R3?.R3>.R3=.R3<.(1=.&40.R22.)(1=.&40.(16.R21.(2>.R20.(18.+2.+20.))))R2=.R2<.R2;.R2:.R29.R28.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.)R26.(1=.&40.$5<.)R25.(4>.(4.&40.))R24.(4?.$6.))R23.))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a2 a3 a4 a5 a6 a7 SP F fc m mo TR size tag N tf lo nb bl ws
      SZ TG T0 T1 TAL HTR HL TCS DI DCS DST TFB NB2 ST LOIMG SPL SPH SPA SCS MI HK HJ GN GS GSX.
    facts.
    ddestruct DI as (NC & DT & DM & DN & WF & MX & (alloc & SSX) & DB & SB & TF0 & BL & BA).
    destruct DCS as [NBCS BLCS]. dpose DST as (DS & CST & c1 & c2 & c3 & M1 & M2 & M3).
    pose proof WF as [WN WL]. dpose BA as (BA1 & BA2 & BA3). dpose DM as (DM1 & DMF & DML). dpose DB as (DB1 & DBF & DBL).
    pose proof (u64arr_bound _ _ _ _ HTR) as TRB. rewrite HL in TRB. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in TRB.
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL (CSf nb bl) (K nb bl) _ _ _ mo (KL nb bl) HK); [exact HJ| |].
    {
      eapply (seg_head AL IMG ALWF (CSf nb bl) (CSOKf nb bl)); try eassumption; try lia.
      all: first [ intros j' Hj'; split; [apply SB; exact Hj'| apply BLCS; exact Hj']
                 | match goal with |- ?G => idtac "SH" G end ]. }
    cbn beta. intros ms1 mo1 PO HK1 MM1 HJ1.
    destruct PO as [HIT | HA].
    - (* [comment removed for export] *)
      ddestruct HIT as (s & x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & m1 & -> & MU1 & WM1 & MI1 & ST1 & SB1).
      assert (LO : forall A n, A + n <= lo -> disjoint_from [(lo, SP)] A n) by (intros A n H; cbn [disjoint_from]; clear - H; lia).
      assert (HI : forall A n, SP <= A -> disjoint_from [(lo, SP)] A n) by (intros A n H; cbn [disjoint_from]; clear - H; lia).
      apply aevtS_now.
      eexists. dexists mo1, nb, bl, N, tf, s. deexists 14. exists m1.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact HK1|]. split; [exact HJ1|].
      split.
      { (* [comment removed for export] *)
        split. { eapply rw_cells_transport; [exact NC| exact MU1| exact WM1| apply LO; unfold A_DEP_N; cbn; clear -LOIMG; lia]. }
        split. { eapply (dtab_transport _ m m1 N DT MU1 WM1). apply LO. unfold A_DEP; clear -LOIMG; lia. }
        split. { eapply (dmap1_transport _ m m1 nb DM MU1 WM1). apply LO. unfold A_DEP_MAP1; clear -LOIMG; lia. }
        split. { eapply (dnodes_transport _ m m1 nb N DN MU1 WM1 DMF). intros b Hb. apply LO.
                 pose proof (proj1 (Forall_forall _ _) DMF b Hb) as (_ & X & _). clear - X LOIMG. lia. }
        split; [exact WF|].
        split. { eapply rw_cells_transport; [exact MX| exact MU1| exact WM1| apply LO; unfold A_DEP_NODES; cbn; clear -LOIMG; lia]. }
        split. { exists alloc. eapply rw_cells_transport; [exact SSX| exact MU1| exact WM1| apply LO; unfold A_SS; cbn; clear -LOIMG; lia]. }
        split. { eapply (dblocks_transport _ m m1 bl DB MU1 WM1). apply LO. unfold A_SS; clear -LOIMG; lia. }
        split. { eapply (sblks_transport _ m m1 bl SB MU1 WM1). intros j Hj. apply LO.
                 dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl) DBF (Z.to_nat j) 0 ltac:(lia)) as (_ & X & _).
                 unfold sblk. clear - X LOIMG. lia. }
        split; [exact TF0|]. split; [exact BL| exact BA]. }
      split; [split; assumption|].
      split. { eapply (depot_statics_transport _ m m1 DST MU1). intros A n H. apply LO. clear -H LOIMG; lia. }
      split; [exact SB1|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [intros x Hx; exact Hx|].
      split. { dexists [], []. rewrite !app_nil_r. repeat split; constructor. }
      split. { eapply (dkeep_munch _ m m m1); [apply dkeep_refl| exact MU1|]. intros x H1 _ _ _. cbn [outside]. split; [exact H1| exact I]. }
      split; [exact WM1|]. split; [exact ST1|]. split; [exact MI1|].
      eapply u64arr_transport; [exact HTR| exact MU1| exact WM1| apply HI; clear -T0; lia].
    - (* [comment removed for export] *)
      ddestruct HA as (h & bi & v & pc & r1 & r10 & r11 & x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & lockw & fr & m2 & -> &
                      MU2 & WM2 & MI2 & FRP2 & TC2 & NC2 & ST2 & HR & BI & VB & CASES).
      cbn [ms_mem MS MSsvc] in HJ1.
      set (W2 := [(lo, SP); (A_DEP + 4 * bi, A_DEP + 4 * bi + 4); (A_DEP_N, A_DEP_N + 4)]) in MU2.
      assert (LO : forall A n, A + n <= lo -> (A + n <= A_DEP + 4 * bi \/ A_DEP + 4 * bi + 4 <= A) -> (A + n <= A_DEP_N \/ A_DEP_N + 4 <= A) -> disjoint_from W2 A n)
        by (intros A n H1 H2 H3; cbn [disjoint_from]; clear - H1 H2 H3; repeat split; lia).
      (* [comment removed for export] *)
      assert (MX2 : rw_cells asegs m2 A_DEP_NODES [C4 (Z_to_bv 64 0)]).
      { eapply rw_cells_transport; [exact MX| exact MU2| exact WM2| apply LO; unfold A_DEP_NODES, A_DEP, A_DEP_N; cbn; clear -LOIMG BI; lia]. }
      assert (SSX2 : rw_cells asegs m2 A_SS [C8 (Z_to_bv 64 tf); C8 alloc]).
      { eapply rw_cells_transport; [exact SSX| exact MU2| exact WM2| apply LO; unfold A_SS, A_DEP, A_DEP_N; cbn; clear -LOIMG BI; lia]. }
      assert (DB2 : dblocks m2 bl).
      { eapply (dblocks_transport _ m m2 bl DB MU2 WM2). apply LO; unfold A_SS, A_DEP, A_DEP_N; clear -LOIMG BI; lia. }
      assert (SB2 : sblks m2 bl).
      { eapply (sblks_transport _ m m2 bl SB MU2 WM2). intros j Hj.
        dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl) DBF (Z.to_nat j) 0 ltac:(lia)) as (X0 & X & _).
        apply LO; unfold sblk, A_DEP, A_DEP_N; clear - X0 X LOIMG BI; lia. }
      assert (DM2 : dmap1 m2 nb).
      { eapply (dmap1_transport _ m m2 nb DM MU2 WM2). apply LO; unfold A_DEP_MAP1, A_DEP, A_DEP_N; clear -LOIMG BI; lia. }
      assert (DN2 : dnodes m2 nb N).
      { eapply (dnodes_transport _ m m2 nb N DN MU2 WM2 DMF). intros b Hb.
        pose proof (proj1 (Forall_forall _ _) DMF b Hb) as (X0 & X & _). apply LO; unfold A_DEP, A_DEP_N; clear - X0 X LOIMG BI; lia. }
      assert (DT2 : dtab_but m2 N bi).
      { eapply (dtab_but_of _ m m2 N bi DT MU2 WM2). intros i Hi NE. apply LO; unfold A_DEP, A_DEP_N; clear -LOIMG BI Hi NE; lia. }
      assert (HTR2 : u64arr asegs m2 TR ws).
      { eapply u64arr_transport; [exact HTR| exact MU2| exact WM2|]. replace (8 * Z.of_nat (length ws)) with 240 by (rewrite HL; reflexivity).
        unfold W2. cbn [disjoint_from]. unfold A_DEP, A_DEP_N. clear - T0 SPL LOIMG BI. lia. }
      assert (DST2 : depot_statics m2).
      { eapply (depot_statics_transport _ m m2 DST MU2). intros A n H. apply LO; unfold A_DEP, A_DEP_N; clear -H LOIMG BI; lia. }
      assert (DK2 : dkeep m m2 lo SP nb bl).
      { eapply (dkeep_munch _ m m m2); [apply dkeep_refl| exact MU2|]. intros x H1 H2 _ _. subst W2. cbn [outside].
        unfold A_SS, A_DEP_END, A_DEP, A_DEP_N in *. clear - H1 H2 BI. repeat split; lia. }
      clearbody W2. clear MX SSX DB SB DM DN HTR.
      destruct CASES as [(-> & KLT & ->) | (-> & -> & KEQ & NK & -> & ->)].
      + (* [comment removed for export] *)
        eapply (put_mid_cfg ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 r1 x5 x6 x7 r11 x12 x13 x14 x15 x16 x17 alloc lockw
                  SP F fc m m2 mo1 TR size tag N tf lo h v bi nb nb bl ws fr); try eassumption; try lia.
        all: first [ left; reflexivity | intros x Hx; exact Hx | split; assumption | match goal with |- ?G => idtac "PM1" G end ].
      + (* [comment removed for export] *)
        dpose DST2 as (_ & CST2 & _). dpose DM2 as (DM1' & _ & _).
        set (k := (N + 1) / 65536) in *.
        assert (KB : 0 <= k < 32768) by (subst k; clear - KEQ NK NB2 WN DML; lia).
        assert (M12 : rw_cells asegs m2 (A_DEP_MAP1 + 8 * k) [C8 (Z_to_bv 64 0)]).
        { pose proof (DM1' k KB) as X. unfold dmap1v in X. replace (k <? Z.of_nat (length nb)) with false in X by (symmetry; apply Z.ltb_ge; lia). exact X. }
        eapply aevtS_bind.
        { eapply (node_create_cfg AL IMG ALWF CSf K CSOKf KL CSmono_n K_apart Gn T_node ROOM_n gp tp s10 s11 t3 t4 t5 t6 x5 x6 x7 x12 x13 x14 x15 x16 x17 SP F fc m2 mo1 lo N h bi v nb bl);
            try eassumption; try lia. }
        intros cc3 NCP. ddestruct NCP as (a & mo3 & x1 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 & -> &
                                         HK3 & HJ3 & CR3 & UAL & UA0 & UA1 & APu & MU3 & WM3 & MI3 & MX3 & M13 & ZB3 & ST3).
        fold k in MU3, M13. set (ua := bv_unsigned a) in *. clearbody ua.
        (* [comment removed for export] *)
        assert (APstk : forall A sz, lo <= A -> A + sz <= SP -> 0 < sz -> A + sz <= ua \/ ua + 2^20 <= A).
        { intros A sz H1 H2 H3. eapply (apart_of (CSf nb bl)); [exact APu| | exact H3| lia]. intros x Hx. apply SCS. lia. }
        assert (APtr : TR + 240 <= ua \/ ua + 2^20 <= TR).
        { eapply (apart_of (CSf nb bl)); [exact APu| | lia| lia]. intros x Hx. apply TCS. exact Hx. }
        assert (APn : forall k', 0 <= k' < Z.of_nat (length nb) -> dblk nb k' + 2^20 <= ua \/ ua + 2^20 <= dblk nb k').
        { intros k' Hk'. eapply (apart_of (CSf nb bl)); [exact APu| | lia| lia]. intros x Hx. apply (NBCS k' Hk'). exact Hx. }
        assert (APs : forall j, 0 <= j < Z.of_nat (length bl) -> sblk bl j + 2^23 <= ua \/ ua + 2^20 <= sblk bl j).
        { intros j Hj. eapply (apart_of (CSf nb bl)); [exact APu| | lia| lia]. intros x Hx. apply (BLCS j Hj). exact Hx. }
        assert (LO3 : forall A n, A + n <= lo -> A + n <= 0x5eb8e0 -> disjoint_from [(lo, SP + -112); (A_DEP_NODES, A_DEP_NODES + 4); (A_DEP_MAP1 + 8 * k, A_DEP_MAP1 + 8 * k + 8); (ua, ua + 2 ^ 20)] A n).
        { intros A n H1 H2. unfold A_DEP_NODES, A_DEP_MAP1. cbn [disjoint_from]. clear - H1 H2 KB UA0 LOIMG. repeat split; lia. }
        replace (Z_to_bv 64 ua) with (Z_to_bv 64 (dblk (nb ++ [ua]) ((N + 1) / 65536)))
          by (f_equal; fold k; rewrite KEQ; apply dblk_app_new).
        eapply (put_mid_cfg ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31 x1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 alloc lockw
                  SP F fc m m3 mo3 TR size tag N tf lo h v bi nb (nb ++ [ua]) bl ws fr); try hassumption; try lia; try (apply GSX). (* [comment removed for export] *)
        all: try (rewrite app_length; cbn [length]; fold k; clear - KEQ; lia).
        * right. exists ua. split; [reflexivity| exact APu].
        * intros x Hx. apply CSmono_n. exact Hx.
        * apply blocks_apart_app_n; [exact BA| exact APn| exact APs].
        * eapply rw_cells_transport; [exact FRP2| exact MU3| exact WM3|]. unfold A_DEP_NODES, A_DEP_MAP1. cbn [disjoint_from cells_size csize Nat.add].
          split; [clear; lia|]. split; [clear -LOIMG SPL; lia|]. split; [clear -LOIMG SPL KB; lia|]. split; [|exact I]. apply APstk; clear - SPL; lia.
        * eapply rw_cells_transport; [exact SSX2| exact MU3| exact WM3| apply LO3; unfold A_SS; cbn; clear -LOIMG; lia].
        * eapply (dblocks_transport _ m2 m3 bl DB2 MU3 WM3). apply LO3; unfold A_SS; clear -LOIMG; lia.
        * intros j Hj. eapply stk_transport_disjoint; [exact (SB2 j Hj)| exact MU3| exact WM3|].
          dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl) DBF (Z.to_nat j) 0 ltac:(lia)) as (X0 & X & _).
          pose proof (APs j Hj) as Y. unfold sblk in Y |- *. unfold A_DEP_NODES, A_DEP_MAP1. cbn [disjoint_from]. clear - X0 X Y LOIMG KB. repeat split; lia.
        * eapply rw_cells_transport; [exact TC2| exact MU3| exact WM3| apply LO3; unfold A_DEP; cbn; clear -LOIMG BI; lia].
        * eapply rw_cells_transport; [exact NC2| exact MU3| exact WM3| apply LO3; unfold A_DEP_N; cbn; clear -LOIMG; lia].
        * eapply (dmap1_app _ m2 m3 nb ua DM2 MU3 WM3); try hassumption. (* [comment removed for export] *)
          -- intros k' Hk' NE. unfold A_DEP_NODES, A_DEP_MAP1. cbn [disjoint_from]. clear - Hk' NE KB KEQ LOIMG UA0. subst k. repeat split; lia.
          -- fold k. rewrite <- KEQ. exact M13.
          -- apply Nat2Z.inj_lt. change (Z.of_nat (Init.Nat.of_num_uint _)) with 32768%Z. clear - KB KEQ. subst k. lia.
        * eapply dnodes_app; [| exact ZB3| clear - KEQ NK; lia| exact DMF].
          eapply (dnodes_transport _ m2 m3 nb N DN2 MU3 WM3 DMF). intros b Hb.
          pose proof (proj1 (Forall_forall _ _) DMF b Hb) as (X0 & X & _).
          ddestruct (In_nth nb b 0 Hb) as (i & Hi & <-).
          pose proof (APn (Z.of_nat i) ltac:(lia)) as Y. unfold dblk in Y. rewrite Nat2Z.id in Y.
          unfold A_DEP_NODES, A_DEP_MAP1. cbn [disjoint_from]. clear - X0 X Y LOIMG KB. repeat split; lia.
        * eapply (dtab_but_transport _ m2 m3 N bi DT2 MU3 WM3). intros i Hi NE. apply LO3; unfold A_DEP; clear -LOIMG Hi; lia.
        * eapply u64arr_transport; [exact HTR2| exact MU3| exact WM3|]. replace (8 * Z.of_nat (length ws)) with 240 by (rewrite HL; reflexivity).
          unfold A_DEP_NODES, A_DEP_MAP1. cbn [disjoint_from]. clear - T0 SPL LOIMG KB APtr. repeat split; lia.
        * eapply (depot_statics_transport _ m2 m3 DST2 MU3). intros A n H. apply LO3; clear -H LOIMG; lia.
        * eapply depot_cs_app_n; [split; [exact NBCS| exact BLCS]| intros x Hx; apply CSmono_n; exact Hx| exact CR3].
        * intros x Hx. apply CSmono_n. apply TCS. exact Hx.
        * intros x Hx. apply CSmono_n. apply SCS. exact Hx.
        * apply (dkeep_app_n _ _ _ _ _ _ ua) in DK2. eapply (dkeep_munch _ m m2 m3); [exact DK2| exact MU3|].
          intros x H1 H2 H3 H4. cbn [outside]. unfold A_SS, A_DEP_END, A_DEP_NODES, A_DEP_MAP1 in *.
          specialize (H3 k). rewrite app_length in H3. cbn [length] in H3. fold k in H3. rewrite KEQ, dblk_app_new in H3.
          clear - H1 H2 H3 KB KEQ. repeat split; try lia; apply H3; lia.
        * eapply wmono_trans; [exact WM2| exact WM3].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End DepotTop.

End ARUN_1.
