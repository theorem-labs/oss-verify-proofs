(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Arr Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import DivergeSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed AKinv AJ AKinvS ASpinS AW_MmapAnon AW_MmapDie ASpin
     AW_DepotA AW_DepotB AW_DepotC AW_DepotD AW_DepotE AW_DepotF.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_DepotCfg () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_GOT_PAGESZ"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_PAGESZ_CELL"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DECORATE"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_LIMIT"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_SEALED2"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DYING"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "ARUN_1.cstatics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_writable"; "Corelib.Init.Datatypes.false"; "Corelib.Lists.ListDef.Forall"; "Stdlib.ZArith.BinInt.Z.of_N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_base"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_size"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.or"; "ARUN_1.zblock"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.true"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "Stdlib.ZArith.BinInt.Z.div"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_DEP"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_DEP_NODES"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_DEP_MAP1"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "zblock"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MSsvc"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_ECALL"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.sub"; "cstatics"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "ARUN_2.DepotCfg.nc_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_TLM_CREATE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_SS"; "ARUN_2.DepotCfg.sc_ms_post"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "ARUN_2.DepotCfg.sc_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_BI_CREATE"].

Section ARUN_1. Context {hAR : arun}.
Definition cstatics (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotCfg ()) "(0.(1.$2.O1.$3.(4.$5.(6.(7.&40.$8.))(9.$5.)))(0.(1.$2.O1.$8.(4.$5.(6.(7.&40.+1000.))(9.$5.)))(0.(1.$2.O1.$:.(4.$5.(6.(7.&40.$;.))(9.$5.)))(0.(1.$2.O1.$<.(4.$5.(=.(7.&8.=))(9.$5.)))(0.(1.$2.O1.$>.(4.$5.(6.(7.&40.=))(9.$5.)))(0.(1.$2.O1.$?.(4.$5.(6.(7.&40.+1.))(9.$5.)))(1.$2.O1.$10.(4.$5.(11.(7.&40.=))(9.$5.)))))))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L13809576380.13L15546790972.13L19101983292.13L24769815612.13L3243602876.13 L62516867900.13L9915340348.13 000001002003004005006007SSSSSSS". (* [comment removed for export] *)
#[using="Type"] Lemma cstatics_transport : ltac2:(CDefT.buildp (gd_tbl_AW_DepotCfg ()) "PW,(12.$13.)Pm,P,(14.&40.)(15.(14.&8.))Pm',P,(14.&40.)(15.(14.&8.))P,(16.R2.)P,(17.R4.R3.R2.)P,PA,$18.Pn,$18.P,(0.(19.+10000.R2.)(19.(1:.R2.R1.)+1=;8<8.))(1;.R8.R3.R2.)(16.R4.)")
(* [comment removed for export] *).
Proof.
  (intros W m m' dd_H; ddestruct dd_H as (C1 & C2 & C3 & C4 & C5 & C6 & C7); intros MU DJ). unfold cstatics.
  unfold A_GOT_PAGESZ, A_PAGESZ_CELL, A_GOT_CFLAGS, A_CFLAGS, A_DECORATE, A_MMAP_LIMIT, A_GOT_SEALED2, A_DYING in *.
  split; [|split; [|split; [|split; [|split; [|split]]]]];
    (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L50961051414.600000@S1s1z1n2E22HS2Hn". (* [comment removed for export] *)
#[using="Type"] Lemma find_segment_ro_lt : ltac2:(CDefT.buildp (gd_tbl_AW_DepotCfg ()) "Pl,(12.$1<.)Pz,$18.Pn,$18.Pseg,$1<.P,(1=.(15.$1<.)(1>.R4.R3.R2.)(1?.$1<.R1.))P,(1=.$20.(21.R2.)$22.)P,(23.$1<.Ls,$1<.P,(1=.$20.(21.R1.)$22.)(19.(1:.(24.(25.R2.))(24.(26.R2.)))+?1000.)R6.)P,(27.=R5.)(27.R7.+?1000.)")
(* [comment removed for export] *).
Proof.
  induction l as [|s l IH]; intros z n seg Hf Hw HF Hn; cbn in Hf; [discriminate|].
  apply Forall_cons_iff in HF. destruct HF as [HS HL].
  destruct ((Z.of_N (seg_base s) <=? z) && (z + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool eqn:E.
  - injection Hf as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E2. specialize (HS Hw).
    clear - E2 HS Hn. lia.
  - eapply IH; eauto.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L26731542034.1500000CS2s12s22s32s42E12E2". (* [comment removed for export] *)
#[using="Type"] Lemma asegs_shape : ltac2:(CDefT.buildp (gd_tbl_AW_DepotCfg ()) "(23.$1<.Ls,$1<.P,(1=.$20.(21.R1.)$22.)(19.(1:.(24.(25.R2.))(24.(26.R2.)))+?1000.)$2.)")
(* [comment removed for export] *).
Proof.
  assert (E : List.map (fun s => (Z.of_N (seg_base s) + Z.of_N (seg_size s), seg_writable s)) asegs
              = [(286720, false); (987136, false); (1011712, true); (6680576, true)]) by (vm_compute; reflexivity).
  assert (G : forall l, List.map (fun s => (Z.of_N (seg_base s) + Z.of_N (seg_size s), seg_writable s)) l
              = [(286720, false); (987136, false); (1011712, true); (6680576, true)] ->
              Forall (fun s => seg_writable s = false -> Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 0x0f1000) l).
  { intros l H. destruct l as [|s1 [|s2 [|s3 [|s4 [|s5 l]]]]]; cbn in H; try discriminate.
    injection H as E1 W1 E2 W2 E3 W3 E4 W4.
    repeat constructor; intros HW; try (rewrite HW in *; discriminate); lia. }
  exact (G _ E).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L6758013062.5000001S". (* [comment removed for export] *)
#[using="Type"] Lemma asegs_ro_lt : forall x, ro_addr asegs x = true -> bv_unsigned x < 0x0f1000.
Proof.
  intros x H. unfold ro_addr in H. destruct (find_segment asegs (bv_unsigned x) 1) as [seg|] eqn:E; [|discriminate].
  apply negb_true_iff in H. eapply (find_segment_ro_lt _ _ _ _ E H asegs_shape). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L20866131589.12L45468828601.12L51111759257.12L53064279717.1200000900D00M00XS1A2sz2SZS2ua1n1A2H0S2ua1n2NZS2ua1A2sz1H". (* [comment removed for export] *)
#[using="Type"] Lemma apart_of : ltac2:(CDefT.buildp (gd_tbl_AW_DepotCfg ()) "PP,P,$18.SpPua,$18.Pn,$18.PA,$18.Psz,$18.P,Px,$18.P,A1.R6.R1.(28.(0.(19.R6.R2.)(27.R2.(1:.R6.R5.))))P,Px,$18.P,(0.(19.R4.R1.)(27.R1.(1:.R4.R3.)))A1.R8.R2.P,(27.=R3.)P,(27.=R6.)(29.(19.(1:.R6.R5.)R8.)(19.(1:.R8.R7.)R6.))")
(* [comment removed for export] *).
Proof.
  intros P ua n A sz AP COV SZ NZ.
  destruct (Z.le_gt_cases (A + sz) ua); [left; assumption|].
  destruct (Z.le_gt_cases (ua + n) A); [right; assumption|].
  exfalso. apply (AP (Z.max A ua)). { apply COV. split; [apply Z.le_max_l|]. apply Z.max_lub_lt; lia. }
  split; [apply Z.le_max_r|]. apply Z.max_lub_lt; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition zblock (m : mem) (a n : Z) : Prop := rw_cells asegs m a [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
#[using="Type"] Lemma zblock_transport : ltac2:(CDefT.buildp (gd_tbl_AW_DepotCfg ()) "PW,(12.$13.)Pm,P,(14.&40.)(15.(14.&8.))Pm',P,(14.&40.)(15.(14.&8.))Pa,$18.Pn,$18.P,(2:.R4.R2.R1.)P,(19.=R2.)P,(17.R7.R6.R5.)P,(2;.$2.R7.R6.)P,(1;.R9.R6.R5.)(2:.R8.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros W m m' a n ZB Hn MU WM DJ. unfold zblock in *. eapply rw_cells_transport; [exact ZB| exact MU| exact WM|].
  cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact Hn. exact DJ.
Qed.
#[using="Type"] Lemma zblock_stk : forall m a n, zblock m a n -> 0 <= n -> stk asegs m a (a + n).
Proof.
  intros m a n ZB Hn. pose proof (stk_of_rw_cells asegs m a _ ZB) as ST. cbn [cells_size csize] in ST.
  rewrite Nat.add_0_r, Z2Nat.id in ST by exact Hn. exact ST.
Qed.
End ARUN_1.
#[global] Opaque zblock.

Section ARUN_2. Context {hAR : arun}.
Section DepotCfg.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CSf : list Z -> list Z -> Z -> Prop.
  Variable K : list Z -> list Z -> Model -> Prop.
  Hypothesis CSOKf : forall nb bl, cs_ok AL (CSf nb bl).
  Hypothesis KL : forall nb bl, kinv AL (CSf nb bl) (K nb bl).
  Hypothesis CSmono_n : forall nb bl a x, CSf nb bl x -> CSf (nb ++ [a]) bl x.
  Hypothesis CSmono_s : forall nb bl a x, CSf nb bl x -> CSf nb (bl ++ [a]) x.
  Hypothesis K_apart : ltac2:(CDefT.buildp (gd_tbl_AW_DepotCfg ()) "Pnb,(12.$18.)Pbl,(12.$18.)Pmo,$2<.Pa,(14.&40.)Pn,(14.&40.)P,A3.VK,R5.R4.R3.P,(1=.$20.(2=.(2>.(2?.(14.&40.)(14.&40.))(30.(31.R4.))(32.(31.R4.)))R3.R2.)$33.)P,(19.+10000.(34.&40.R3.))P,(19.(1:.(34.&40.R5.)(34.&40.R4.))(35.VhAR,))Px,$18.P,(29.A3.VCSf,R:.R9.R1.(0.(19.(36.VAL,)R1.)(27.R1.(37.VAL,))))(28.(0.(19.(34.&40.R8.)R2.)(27.R2.(1:.(34.&40.R8.)(34.&40.R7.)))))")
(* [comment removed for export] *).
  Variables (Gn Gs : list Z -> list Z -> Prop).   (* [comment removed for export] *)
  Hypothesis T_node : ltac2:(CDefT.buildp (gd_tbl_AW_DepotCfg ()) "Pnb,(12.$18.)Pbl,(12.$18.)Pmo,$2<.Pa,(14.&40.)P,A2.VGn,R4.R3.P,A3.VK,R5.R4.R3.P,(1=.$18.(38.(34.&40.R3.)+1000.)=)P,(27.=(34.&40.R4.))P,(19.(1:.(34.&40.R5.)(39.+2.+14.))(35.VhAR,))P,(1=.$20.(2=.(2>.(2?.(14.&40.)(14.&40.))(30.(31.R7.))(32.(31.R7.)))R6.(7.&40.(39.+2.+14.)))$33.)(0.A3.VK,(2>.$18.R:.(4.$18.(34.&40.R7.)(9.$18.)))R9.(3:.+22.R7.(39.+2.+14.)R8.)(3;.A2.VCSf,(2>.$18.R:.(4.$18.(34.&40.R7.)(9.$18.)))R9.(34.&40.R7.)(39.+2.+14.)))")
(* [comment removed for export] *).
  Hypothesis T_store : ltac2:(CDefT.buildp (gd_tbl_AW_DepotCfg ()) "Pnb,(12.$18.)Pbl,(12.$18.)Pmo,$2<.Pa,(14.&40.)P,A2.VGs,R4.R3.P,A3.VK,R5.R4.R3.P,(1=.$18.(38.(34.&40.R3.)+1000.)=)P,(27.=(34.&40.R4.))P,(19.(1:.(34.&40.R5.)(39.+2.+17.))(35.VhAR,))P,(1=.$20.(2=.(2>.(2?.(14.&40.)(14.&40.))(30.(31.R7.))(32.(31.R7.)))R6.(7.&40.(39.+2.+17.)))$33.)(0.A3.VK,R:.(2>.$18.R9.(4.$18.(34.&40.R7.)(9.$18.)))(3:.+4022.R7.(39.+2.+17.)R8.)(3;.A2.VCSf,R:.(2>.$18.R9.(4.$18.(34.&40.R7.)(9.$18.)))(34.&40.R7.)(39.+2.+17.)))")
(* [comment removed for export] *).
  Hypothesis ROOM_n : forall nb bl mo, Gn nb bl -> K nb bl mo -> exists a, anon_grantable 0x22 (2^20) mo a.
  Hypothesis ROOM_s : forall nb bl mo, Gs nb bl -> K nb bl mo -> exists a, anon_grantable 0x4022 (2^23) mo a.

  Ltac facts :=
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition nc_post (SP : Z) (gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo N h bi v : Z) (nb bl : list Z) (m1 : mem) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotCfg ()) "Lc,$3<.(3=.(14.&40.)La,(14.&40.)(3=.$2<.Lmo',$2<.(3=.(14.&40.)Lx1,(14.&40.)(3=.(14.&40.)Lx5,(14.&40.)(3=.(14.&40.)Lx6,(14.&40.)(3=.(14.&40.)Lx7,(14.&40.)(3=.(14.&40.)Lx11,(14.&40.)(3=.(14.&40.)Lx12,(14.&40.)(3=.(14.&40.)Lx13,(14.&40.)(3=.(14.&40.)Lx14,(14.&40.)(3=.(14.&40.)Lx15,(14.&40.)(3=.(14.&40.)Lx16,(14.&40.)(3=.(14.&40.)Lx17,(14.&40.)(3=.(14.&40.)Lx28,(14.&40.)(3=.(14.&40.)Lx29,(14.&40.)(3=.(14.&40.)Lx30,(14.&40.)(3=.(14.&40.)Lx31,(14.&40.)(3=.P,(14.&40.)(15.(14.&8.))Lm',P,(14.&40.)(15.(14.&8.))Zua,$18.(34.&40.R12.)Zk,$18.(3>.(1:.O7.+1.)+10000.)(0.(1=.$3<.R15.(3?.(40.(41.R12.(7.&40.(1:.O?.-70.))O>.O=.R11.R10.R?.(7.&40.=)(7.&40.(1:.O7.+1.))(7.&40.R2.)R>.R=.R<.R;.R:.R9.R8.(7.&40.(1:.$42.(43.+4.O5.)))(7.&40.O6.)(7.&40.$44.)(7.&40.O4.)(7.&40.+????.)(7.&40.(1:.O7.+1.))(7.&40.$45.)(7.&40.O4.)O<.O;.R7.R6.R5.R4.)O:.(7.&40.+897:8.)O9.(46.(14.&40.))R3.(47.$2.))R13.))(0.A3.VK,(2>.$18.O3.(4.$18.R2.(9.$18.)))O2.R13.(0.(48.R3.R13.)(0.(3;.A2.VCSf,(2>.$18.O3.(4.$18.R2.(9.$18.)))O2.R2.(39.+2.+14.))(0.(1=.$18.(38.R2.+1000.)=)(0.(19.+65?000.R2.)(0.(19.(1:.R2.(39.+2.+14.))(35.VhAR,))(0.Px,$18.P,A3.VCSf,O3.O2.R1.(28.(0.(19.R4.R2.)(27.R2.(1:.R4.(39.+2.+14.)))))(0.(17.(4.(2?.$18.$18.)(49.$18.$18.O8.(1:.O?.-70.))(4.(2?.$18.$18.)(49.$18.$18.$44.(1:.$44.+4.))(4.(2?.$18.$18.)(49.$18.$18.(1:.$45.(43.+8.R1.))(1:.(1:.$45.(43.+8.R1.))+8.))(4.(2?.$18.$18.)(49.$18.$18.R2.(1:.R2.(39.+2.+14.)))(9.(2?.$18.$18.))))))O1.R3.)(0.(2;.$2.O1.R3.)(0.(4:.$2.R3.)(0.(4;.$2.R3.$44.(4.$5.(11.(7.&40.=))(9.$5.)))(0.(4;.$2.R3.(1:.$45.(43.+8.R1.))(4.$5.(6.(7.&40.R2.))(9.$5.)))(0.(4<.R3.R2.(39.+2.+14.))(4=.$2.R3.O8.(1:.O?.-70.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition anc_svc_post (SP : Z) (gp tp s10 s11 t3' t4' t5' t6' : word) (F : bvmap 5 word) (fc : bv 32)
      (lo N h bi v : Z) (m1 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotCfg ()) "Lms',$4>.(3=.(14.&40.)Lt0,(14.&40.)(3=.(14.&40.)Lt1,(14.&40.)(3=.(14.&40.)Lt2,(14.&40.)(3=.(14.&40.)Lt3,(14.&40.)(3=.(14.&40.)Lt4,(14.&40.)(3=.(14.&40.)Lt5,(14.&40.)(3=.(14.&40.)Lt6,(14.&40.)(3=.(14.&40.)La6,(14.&40.)(3=.P,(14.&40.)(15.(14.&8.))Lmm,P,(14.&40.)(15.(14.&8.))(3=.(12.(14.&8.))Lfr,(12.(14.&8.))Zk,$18.(3>.(1:.O5.+1.)+10000.)(0.(1=.$4>.R<.(4?.(41.(7.&40.+7<9;8.)(7.&40.(1:.(1:.O11.-90.)-30.))O10.O?.R;.R:.R9.(7.&40.=)(7.&40.+240;:.)(7.&40.=)(7.&40.+100000.)(7.&40.+3.)(7.&40.+22.)(7.&40.-1.)(7.&40.=)R4.(7.&40.+=>.)(7.&40.+100000.)(7.&40.$8.)(7.&40.$44.)(7.&40.O2.)(7.&40.+????.)(7.&40.(1:.O5.+1.))(7.&40.$45.)(7.&40.O2.)O>.O=.R8.R7.R6.R5.)O8.(7.&40.$50.)(7.&40.+=>.)O7.(46.(14.&40.))R3.(47.$2.)))(0.(17.(4.(2?.$18.$18.)(49.$18.$18.O6.(1:.O11.-70.))(4.(2?.$18.$18.)(49.$18.$18.$44.(1:.$44.+4.))(9.(2?.$18.$18.))))O1.R3.)(0.(2;.$2.O1.R3.)(0.(4:.$2.R3.)(0.(4;.$2.R3.(1:.O11.-90.)(4.$5.(6.(7.&40.(1:.$42.(43.+4.O3.))))(4.$5.(6.(7.&40.(1:.O5.+1.)))(4.$5.(6.(7.&40.=))(4.$5.(6.(7.&40.+89840.))(9.$5.))))))(0.(4;.$2.R3.$44.(4.$5.(11.(7.&40.+1.))(9.$5.)))(0.(4;.$2.R3.(1:.$45.(43.+8.R1.))(4.$5.(6.(7.&40.=))(9.$5.)))(0.(4;.$2.R3.(1:.(1:.O11.-90.)-30.)(4.$5.(51.#4.R2.)(4.$5.(11.(7.&40.+22.))(4.$5.(6.(7.&40.O4.))(4.$5.(6.(7.&40.$8.))(4.$5.(6.(7.&40.(1:.$44.(43.+8.R1.))))(4.$5.(6.(7.&40.$44.))(4.$5.(6.(7.&40.+89>68.))(9.$5.)))))))))(4=.$2.R3.O6.(1:.(1:.O11.-90.)-30.))))))))))))))))))))")
(* [comment removed for export] *).

  Definition nc_ms_post (SP : Z) (gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo N h bi v ua : Z) (m1 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotCfg ()) "Lms',$4>.(3=.(14.&40.)Lx1,(14.&40.)(3=.(14.&40.)Lx5,(14.&40.)(3=.(14.&40.)Lx6,(14.&40.)(3=.(14.&40.)Lx7,(14.&40.)(3=.(14.&40.)Lx11,(14.&40.)(3=.(14.&40.)Lx12,(14.&40.)(3=.(14.&40.)Lx13,(14.&40.)(3=.(14.&40.)Lx14,(14.&40.)(3=.(14.&40.)Lx15,(14.&40.)(3=.(14.&40.)Lx16,(14.&40.)(3=.(14.&40.)Lx17,(14.&40.)(3=.(14.&40.)Lx28,(14.&40.)(3=.(14.&40.)Lx29,(14.&40.)(3=.(14.&40.)Lx30,(14.&40.)(3=.(14.&40.)Lx31,(14.&40.)(3=.P,(14.&40.)(15.(14.&8.))Lm',P,(14.&40.)(15.(14.&8.))Zk,$18.(3>.(1:.O6.+1.)+10000.)(0.(1=.$4>.R12.(40.(41.R11.(7.&40.(1:.O>.-70.))O=.O<.R10.R?.R>.(7.&40.=)(7.&40.(1:.O6.+1.))(7.&40.O2.)R=.R<.R;.R:.R9.R8.R7.(7.&40.(1:.$42.(43.+4.O4.)))(7.&40.O5.)(7.&40.$44.)(7.&40.O3.)(7.&40.+????.)(7.&40.(1:.O6.+1.))(7.&40.$45.)(7.&40.O3.)O;.O:.R6.R5.R4.R3.)O9.(7.&40.+897:8.)O8.(46.(14.&40.))R2.(47.$2.)))(0.(17.(4.(2?.$18.$18.)(49.$18.$18.O7.(1:.O>.-70.))(4.(2?.$18.$18.)(49.$18.$18.$44.(1:.$44.+4.))(4.(2?.$18.$18.)(49.$18.$18.(1:.$45.(43.+8.R1.))(1:.(1:.$45.(43.+8.R1.))+8.))(4.(2?.$18.$18.)(49.$18.$18.O2.(1:.O2.(39.+2.+14.)))(9.(2?.$18.$18.))))))O1.R2.)(0.(2;.$2.O1.R2.)(0.(4:.$2.R2.)(0.(4;.$2.R2.$44.(4.$5.(11.(7.&40.=))(9.$5.)))(0.(4;.$2.R2.(1:.$45.(43.+8.R1.))(4.$5.(6.(7.&40.O2.))(9.$5.)))(0.(4<.R2.O2.(39.+2.+14.))(4=.$2.R2.O7.(1:.O>.-70.)))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01[0@L10450802925.125L11439171860.148L15570669577.148L1685717371.0   L18928845099.122L18928845099.123L19663018383.74 L19675720065.148L20706231372.5  L20706382247.111L20711535332.98 L21566014263.156L21566014266.109L21567736999.129L22209052120.98 L22400252526.108L2252154983.96  L22706556809.4  L22706556809.6  L22706556809.8  L25432523821.7  L26129418698.148L27835731415.148L27835812809.129L27846114761.93 L27846114761.98 L27848211929.74 L28165445704.93 L28573892092.8  L29172923528.148L29230279457.0  L30314016857.3  L31179887929.106L32129704361.0  L32633637257.148L32987986967.129L33669249170.3  L33670951324.3  L34765882236.93 L34903592768.129L3560269315.112 L36690522898.10 L36841451887.5  L37229909125.129L37242789033.5  L38236185789.74 L38237949960.3  L38238282925.93 L38238282925.98 L38248436397.129L38248879283.148L3852058568.74  L39231752993.0  L39585473661.3  L40549122971.93 L40561472789.155L41599022925.2  L41600592437.7  L42149032142.74 L42151129310.93 L42151129310.98 L42152888030.129L42153099456.148L45287350246.74 L45291433960.148L45638961737.107L47161390829.3  L47922842274.107L48537706372.93 L49607210629.107L50115393895.74 L50128111977.148L50186906489.12 L50688752264.8  L50850525385.0  L52029284603.3  L52231120023.6  L52771474835.3  L53512949285.97 L54434536137.0  L54485064723.4  L55588686165.0  L57628700040.4  L57628700040.6  L57637444663.3  L58421828776.129L59314873579.118L59314955108.97 L59537881768.3  L59576973665.110L59577082002.105L59583441669.97 L59760603398.107L60409382626.98 L61708234742.98 L61723236854.129L63202750327.98 L63212902775.129L6430849802.129 L66566358642.124L66772699762.93 L68370421578.96 L68650207006.3  L7781518090.3   L8826417067.129 L8841419179.93  L8841419179.98  00000Y00j00k00l01=01N01^02302A02V02W02n03E03\03]03i03j04604G04\05305D05X05l06;06J06Y06Z06o07C07D07L07a07b08:08;08@08A08Q08e09609U09b0:70:E0:T0:X0:g0;60;J0;^0;_0;`0;d0<00<A0<H0<`0=50=J0=_0>90>S0>f0?>0?\0?g0@80@K0@d0A40AI0Am0BD0BE0BP0Be0Bi0C50C60CG0CH0CT0Ce0Cm0Cn0DI0DW0Db0E30ED0EP0Eg0Eh0F;0FS0Fc0G80G90G]0Gi0Gj0H80H?0HP0H\0HhS3hAR2AL2SP1N1k4IMG'1a2ua1A2sz2H12H21x2HxS3hAR2SP1N1k1a2uaFSS3hAR2SP1N1k1a2uaS3hAR2SP1N1k1a2uaS3hAR2SP1N1k3SPAS3hAR2SP1N1k3SPA1a2uaS3hAR1a2ua3ACES3hAR2SP1N1k1a2ua3ACEFS3hAR2SP1N1k1a2ua2A02ARS3hAR2SP1N1k1a2ua2A02ARS3hAR2SP1N1k1a2ua2A02ARFS3hAR2SP1N1kFS2SP2lo1x2HxS2SP2lo1a2ua1x2HxS2SP2lo1N1k1a2ua1x2HxS3hAR2SP2lo5LOIMG1A1n1HS3hAR2SP1N1k1a2uaS3hAR2SP2lo1N1k1a2uaS3hAR2SP2lo1N1k1a2uaS3hAR2SP2lo1N1kS3hAR2SP2lo1N1kS3hAR2SP2lo1N1kFS2SP2lo1N1k1a2ua1x2HxS3hAR2SP1N1k2KB1a2uaSS1N1k2KBS3hAR2SP1N1k1a2ua3ACESS3hAR2SP1N1k1a2ua2A03ACEFS1N1kSS3hAR2SP1N1k3SPHS3hAR2SP1N1k1a2ua2A0S3hAR2SP1N1k1a2uaS3hAR2SP2lo5LOIMG1a2ua2UA1A1n1HS2SP2lo1A1n1HS3hAR2SP1N1k1a2ua3ACES3hAR1a2ua3ACES3hAR2SP2lo1N1kS2loS3hAR2SP2lo1N1kS3hAR2SP2lo1N1kS3hAR2SP2lo1N1k1a2uaS3hAR2SP2lo1N1k1a2uaFSS2SPS3hAR2SP1N1kS3hAR2SP1N1k1a2uaS2SP2loS3hAR2SP2lo1N1k2KB5LOIMGS3hAR2SP2lo1N1k5LOIMGS3hAR2SP2lo1N1k5LOIMGS3hAR2SP2lo1N1k5LOIMGS3hAR2SP2lo1N1k5LOIMG1a2uaS3hAR2SP2lo1N1k5LOIMG1a2uaS3hAR2SP2lo1N1k3SPLS3hAR2SP2lo1N1k3SPL1a2uaS3hAR2AL2SP1N1k4IMG'1a2ua1H2H0S2SP2lo3SPLS3hAR2SP1N1k1a2uaS3hAR2SP2lo1N1k3SPLS3hAR2AL2SP1N1k4IMG'1a2uaS3hAR2SP1N1k3SPHS3hAR2SP1N1k3SPH1a2uaS3hAR2SP2lo1N1k2KB5LOIMG1a2ua3ACE2UAS3hAR2lo5LOIMG1a2ua3ACESS2SP2lo3SPLS3hAR2lo1N1k2KB5LOIMGS2SPS3hAR2SP1N1kSS3hAR2SP2lo5LOIMGSS2SP2lo1x2HxS2SP2lo1a2ua1x2HxS1N1k2KBFS3hAR2SP1N1k1a2ua2UA1x2Hx1HS3hAR2SP1N1k1ES2SP2lo3SPLS3hAR2SP1N1k1a2uaS3hAR2SP1N1k1a2uaS3hAR2SP1N1kS3hAR2SP1N1k1a2ua2A02H0FS3hAR2SP2lo1N1k3SPLS3hAR2SP2lo1N1k3SPL1a2uaS3hAR2SP1N1k3SPHS3hAR2SP1N1k3SPH1a2uaFS3hAR2SP2lo1N1k1a2ua1A2sz2H12H21x2HxS3hAR2SP1N1kFS3hAR2lo5LOIMGS2SP2loS3hAR2SP1N1k1a2uaS3hAR2SP1N1kS3hAR2SP1N1k". (* [comment removed for export] *)
  #[using="AL IMG ALWF CSOKf KL CSmono_n K_apart T_node ROOM_n"] Lemma node_create_cfg : ltac2:(CDefT.buildp (gd_tbl_AW_DepotCfg ()) "Pgp,(14.&40.)Ptp,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)Px5,(14.&40.)Px6,(14.&40.)Px7,(14.&40.)Px12,(14.&40.)Px13,(14.&40.)Px14,(14.&40.)Px15,(14.&40.)Px16,(14.&40.)Px17,(14.&40.)PSP,$18.PF,(52.&5.(14.&40.))Pfc,(14.&20.)Pm1,P,(14.&40.)(15.(14.&8.))Pmo,$2<.Plo,$18.PN,$18.Ph,$18.Pbi,$18.Pv,$18.Pnb,(12.$18.)Pbl,(12.$18.)Zk,$18.(3>.(1:.R6.+1.)+10000.)P,(0.(19.=R1.)(27.R1.+8000.))P,(0.(19.=R6.)(27.R6.(39.+2.+14.)))P,(0.(19.=R8.)(27.R8.(39.+2.+40.)))P,(0.(19.=R7.)(27.R7.(39.+2.+1?.)))P,(0.(19.=R;.)(27.R;.(53.(39.+2.+1?.)+1.)))P,(4;.$2.R?.$44.(4.$5.(11.(7.&40.=))(9.$5.)))P,(4;.$2.R10.(1:.$45.(43.+8.R7.))(4.$5.(6.(7.&40.=))(9.$5.)))P,(54.R11.)P,(4=.$2.R12.R10.(1:.R15.-70.))P,(19.(35.VhAR,)R11.)P,(19.R12.(53.R17.+240.))P,(19.R18.(39.+2.+3>.))P,(1=.$18.(38.R19.+10.)=)P,(3;.A2.VCSf,R10.R?.R15.(53.R1:.R15.))P,(4:.$2.R18.)P,A3.VK,R12.R11.R18.P,(48.R1:.R19.)P,A2.VGn,R14.R13.(55.$2.(56.R1?.R30.R2?.R2>.R2=.R1>.R1=.R1:.R19.R18.R17.R16.R15.R14.R1<.)(3?.(40.(41.(7.&40.+89840.)(7.&40.(1:.R1?.-70.))R30.R2?.R28.R27.R26.(7.&40.=)(7.&40.(1:.R19.+1.))(7.&40.$44.)(7.&40.R13.)R25.R24.R23.R22.R21.R20.(7.&40.(1:.$42.(43.+4.R17.)))(7.&40.R18.)(7.&40.$44.)(7.&40.R16.)(7.&40.+????.)(7.&40.(1:.R19.+1.))(7.&40.$45.)(7.&40.R16.)R2>.R2=.R2<.R2;.R2:.R29.)R1>.(7.&40.$57.)R1=.(46.(14.&40.))R1<.(47.$2.))R1;.))")
(* [comment removed for export] *).
  Proof.
    intros gp tp s10 s11 t3 t4 t5 t6 x5 x6 x7 x12 x13 x14 x15 x16 x17 SP F fc m1 mo lo N h bi v nb bl k
      KB BI HR VB NB MX M1 CST ST LOIMG SPL SPH SPA SCS MI HK HJ GN.
    facts. dpose CST as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL (CSf nb bl) (K nb bl) (anc_svc_post SP gp tp s10 s11 t3 t4 t5 t6 F fc lo N h bi v m1) _ _ mo (KL nb bl) HK); [exact HJ| |].
    {
      eapply evtA_cut.
      { eapply (tc_A AL IMG ALWF (CSf nb bl) (CSOKf nb bl)); try eassumption; try lia.
        all: first [eapply (crange_sub (CSf nb bl) lo (SP - lo)); [exact SCS| lia| lia] | match goal with |- ?G => idtac "TCA" G end]. }
      cbn beta. (intros ms1 dd_H; ddestruct dd_H as (y3 & y4 & y5 & m2 & -> & MU2 & WM2 & MI2 & FR2 & MX2 & M12 & ST2)).
      assert (CST2 : cstatics m2).
      { eapply (cstatics_transport _ m1 m2 CST MU2). intros A n H. unfold A_DEP_NODES. cbn [disjoint_from]. clear - H LOIMG. lia. }
      dpose CST2 as (G1' & G2' & G3' & G4' & G5' & G6' & G7').
      eapply evtA_mono.
      { eapply (mmapdie_pre AL IMG ALWF (CSf nb bl) (CSOKf nb bl)); try eassumption; try lia.
        eapply (crange_sub (CSf nb bl) lo (SP - lo)); [exact SCS| lia| lia]. }
      cbn beta. (intros ms1 dd_H; ddestruct dd_H as (t0' & t1' & t2' & t3' & t4' & t5' & t6' & a6' & mm & fr & -> & MU3 & WM3 & MI3 & FR3 & ST3)).
      unfold anc_svc_post. deexists 10.
      replace (SP + -112 + -32) with (SP + -144) in * by lia.
      split; [reflexivity|].
      split. { eapply munch_trans. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]. clear. intros x Hx. lia. }
               eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]. clear. intros x Hx. lia. }
      split; [eapply wmono_trans; [exact WM2| exact WM3]|]. split; [exact MI3|].
      split. { eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize Nat.add]. clear; lia. }
      split. { eapply rw_cells_transport; [exact MX2| exact MU3| exact WM3|]. unfold A_DEP_NODES; cbn [disjoint_from cells_size csize Nat.add]. clear -LOIMG; lia. }
      split. { eapply rw_cells_transport; [exact M12| exact MU3| exact WM3|]. unfold A_DEP_MAP1; cbn [disjoint_from cells_size csize Nat.add]. clear -LOIMG KB; lia. }
      split; [exact FR3| exact ST3]. }
    (* [comment removed for export] *)
    cbn beta. intros ms3 mo3 PRE HK3 MM3 HJ3.
    ddestruct PRE as (t0' & t1' & t2' & t3' & t4' & t5' & t6' & a6' & mm & fr & -> & MU3 & WM3 & MI3 & FR2 & MX3 & M13 & FR3 & ST3).
    eapply (aevtS_mmap_anon asegs _) with (nZ := 1048576) (flags := 0x22).
    { exact (ki_halted (KL nb bl) mo3 HK3). }
    { exact (ki_top (KL nb bl) mo3 HK3). }
    { unfold mmap_anon_args, areg, MSsvc. cbn [ms_regs]. simp_regs.
      repeat split; try reflexivity; try lia.
      - intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia.
      - left. reflexivity. }
    { change 1048576 with (2^20). apply (ROOM_n nb bl mo3 GN HK3). }
    - (* [comment removed for export] *)
      intros e HIn. right. destruct HIn as [<-|[]].
      rewrite nret_MSsvc, mkR_set_a0, apply_mem_none.
      replace (errno_ret ENOMEM) with (Z_to_bv 64 (2^64 - 12)) by (apply bv_eq; vm_compute; reflexivity).
      change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
      pose proof (cstatics_transport _ m1 mm CST MU3 ltac:(intros A n H; unfold A_DEP_NODES; cbn [disjoint_from]; clear - H LOIMG; lia)) as (_ & _ & _ & _ & _ & G6' & G7').
      change (Z_to_bv 64 1048576) with (Z_to_bv 64 ((1048576 + 4095) / 4096 * 4096)).
      eapply (evtA_spinJ_K asegs AL (CSf nb bl) (K nb bl) _ _ mo3 (KL nb bl) HK3).
      {
        eapply (mmapdie_post_die AL IMG ALWF (CSf nb bl) (CSOKf nb bl)) with (m0 := mm); try eassumption; try lia.
        apply munch_refl. apply wmono_refl. eapply (crange_sub (CSf nb bl) lo (SP - lo)); [exact SCS| lia| lia]. }
      cbn beta. intros ms5 mo5 PO HK5 _. ddestruct PO as (r' & F' & mm' & ->).
      apply spinningJ_at; [cbn; tauto| exact (ki_halted (KL nb bl) mo5 HK5)].
    - (* [comment removed for export] *)
      intros a AAL A0 ACE RF.
      rewrite nret_MSsvc, mkR_set_a0, apply_mem_zeros.
      change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
      pose proof (bv_unsigned_in_range 64 a) as AR. unfold bv_modulus in AR. change (2 ^ Z.of_N 64) with (2^64) in AR.
      set (ua := bv_unsigned a) in *.
      pose proof aceil_bounds as AC.
      pose proof (K_apart nb bl mo3 a (Z_to_bv 64 1048576) HK3 RF) as AP. fold ua in AP.
      replace (bv_unsigned (Z_to_bv 64 1048576)) with 1048576 in AP by (symmetry; apply unsigned_lit; lia).
      specialize (AP ltac:(clear; lia) ltac:(clear - ACE AC; lia)).
      assert (UA : 0x65f000 <= ua).
      { destruct (Z.le_gt_cases 0x65f000 ua); [assumption|]. exfalso.
        destruct (Z.le_gt_cases 0x10000 ua).
        - apply (AP ua). right; lia. lia.
        - apply (AP 0x10000). right; lia. lia. }
      destruct (T_node nb bl mo3 a GN HK3 AAL A0 ltac:(change (2^20) with 1048576; lia) RF) as [HK4 CR4]. fold ua in HK4, CR4.
      pose proof (J_anon_grant mm mo3 0x22 a 1048576 HJ3 ltac:(clear; lia) ltac:(fold ua; clear - ACE AC; lia) RF) as HJ4.
      (* [comment removed for export] *)
      rewrite <- (Z_to_bv_bv_unsigned a). fold ua. change (Z_to_bv 64 ua, Z_to_bv 64 1048576) with (wa ua, Z_to_bv 64 1048576).
      rewrite <- (Z_to_bv_bv_unsigned a) in HK4. fold ua in HK4. change (2 ^ 20) with 1048576 in HK4, CR4.
      rewrite <- (Z_to_bv_bv_unsigned a) in HJ4. fold ua in HJ4. change (Z_to_bv 64 ua, Z_to_bv 64 1048576) with (wa ua, Z_to_bv 64 1048576) in HJ4.
      assert (Ha : 0 <= ua < 2^64) by lia. assert (Hn : 0 <= 1048576 < 2^64) by lia. assert (Han : ua + 1048576 <= 2^64) by lia.
      pose proof (munch_zeros mm ua 1048576 Ha Hn Han [(ua, ua + 1048576)] mm (munch_refl _ mm) ltac:(cbn; lia)) as MUz.
      pose proof (wmono_zeros asegs mm ua 1048576 Ha Hn Han mm (wmono_refl asegs mm)) as WMz.
      assert (MIz : mem_inv asegs (apply_zeros mm [(wa ua, Z_to_bv 64 1048576)])).
      { eapply (mem_inv_zeros asegs mm ua 1048576 Ha Hn Han MI3). intros x Hx.
        destruct (ro_addr asegs x) eqn:E; [|reflexivity]. exfalso. pose proof (asegs_ro_lt x E). lia. }
      pose proof (rw_cells_zeros_new asegs mm ua 1048576 Ha Hn Han : zblock _ ua 1048576) as NEWz.
      set (mz := apply_zeros mm [(wa ua, Z_to_bv 64 1048576)]) in *. clearbody mz.
      (* [comment removed for export] *)
      assert (APstk : forall A sz, lo <= A -> A + sz <= SP -> 0 < sz -> A + sz <= ua \/ ua + 1048576 <= A).
      { intros A sz H1 H2 H3. eapply (apart_of (fun x => CSf nb bl x \/ al_img_lo AL <= x < al_img_hi AL)); [exact AP| | exact H3| lia].
        intros x Hx. left. apply SCS. lia. }
      assert (APimg : forall A sz, 0x10000 <= A -> A + sz <= 0x65f000 -> 0 < sz -> A + sz <= ua \/ ua + 1048576 <= A).
      { intros A sz H1 H2 H3. eapply (apart_of (fun x => CSf nb bl x \/ al_img_lo AL <= x < al_img_hi AL)); [exact AP| | exact H3| lia].
        intros x Hx. right. lia. }
      (* [comment removed for export] *)
      assert (FR2z : rw_cells asegs mz (SP + -144) [C8 (Z_to_bv 64 (A_DEP + 4 * bi)); C8 (Z_to_bv 64 (N + 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x089840)]).
      { eapply rw_cells_transport; [exact FR2| exact MUz| exact WMz|]. cbn [disjoint_from cells_size csize Nat.add]. split; [|exact I]. apply APstk; clear -SPL; lia. }
      assert (FR3z : rw_cells asegs mz (SP + -144 + -48) [CB 4 fr; C4 (Z_to_bv 64 0x22); C8 (Z_to_bv 64 h); C8 (Z_to_bv 64 A_PAGESZ_CELL);
                                     C8 (Z_to_bv 64 (A_DEP_NODES + 8 * k)); C8 (Z_to_bv 64 A_DEP_NODES); C8 (Z_to_bv 64 0x089e68)]).
      { eapply rw_cells_transport; [exact FR3| exact MUz| exact WMz|]. cbn [disjoint_from cells_size csize Nat.add]. split; [|exact I]. apply APstk; clear -SPL; lia. }
      assert (MXz : rw_cells asegs mz A_DEP_NODES [C4 (Z_to_bv 64 1)]).
      { eapply rw_cells_transport; [exact MX3| exact MUz| exact WMz|]. unfold A_DEP_NODES; cbn [disjoint_from cells_size csize Nat.add]. split; [|exact I]. apply APimg; clear; lia. }
      assert (M1z : rw_cells asegs mz (A_DEP_MAP1 + 8 * k) [C8 (Z_to_bv 64 0)]).
      { eapply rw_cells_transport; [exact M13| exact MUz| exact WMz|]. unfold A_DEP_MAP1; cbn [disjoint_from cells_size csize Nat.add]. split; [|exact I]. apply APimg; clear -KB; lia. }
      assert (STz : stk asegs mz lo (SP + -144 + -48)).
      { eapply stk_transport_disjoint; [exact ST3| exact MUz| exact WMz|]. cbn [disjoint_from]. split; [|exact I]. apply APstk; clear -SPL; lia. }
      assert (MU1z : munch [(lo, SP + -112); (A_DEP_NODES, A_DEP_NODES + 4); (ua, ua + 1048576)] m1 mz).
      { eapply munch_trans; [eapply munch_weaken; [|exact MU3] | eapply munch_weaken; [|exact MUz]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
      assert (CSTz : cstatics mz).
      { eapply (cstatics_transport _ m1 mz CST MU1z). intros A n H. unfold A_DEP_NODES; cbn [disjoint_from]. clear -H LOIMG UA. lia. }
      dpose CSTz as (G1z & G2z & G3z & G4z & G5z & G6z & G7z).
      clear FR2 FR3 MX3 M13 ST3.
      (* [comment removed for export] *)
      assert (SCS' : crange (CSf (nb ++ [ua]) bl) lo (SP - lo)) by (intros x Hx; apply CSmono_n; apply SCS; exact Hx).
      eapply (evtA_aevtS_KJ AL (CSf (nb ++ [ua]) bl) (K (nb ++ [ua]) bl) (nc_ms_post SP gp tp s10 s11 F fc lo N h bi v ua m1) _ _ _ (KL (nb ++ [ua]) bl) HK4); [exact HJ4| |].
      {
        change (Z_to_bv 64 1048576) with (Z_to_bv 64 ((1048576 + 4095) / 4096 * 4096)).
        eapply evtA_cut.
        { eapply (mmapdie_post_ok AL IMG ALWF (CSf (nb ++ [ua]) bl) (CSOKf (nb ++ [ua]) bl)) with (m0 := mz) (a := Z_to_bv 64 ua);
            try eassumption; try (rewrite unsigned_lit by lia); try lia; try apply munch_refl; try apply wmono_refl.
          all: first [eapply (crange_sub (CSf (nb ++ [ua]) bl) lo (SP - lo)); [exact SCS'| lia| lia] | match goal with |- ?G => idtac "PO" G end]. }
        cbn beta. (intros ms1 dd_H; ddestruct dd_H as (z0 & z1 & z2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m5 & -> & MU5 & WM5 & MI5 & ST5)).
        replace (ret_pc (Z_to_bv 64 0x089e68)) with (Z_to_bv 64 0x089e68) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
        replace (SP + -144 + -48 + 48) with (SP + -144) in * by lia.
        (* [comment removed for export] *)
        assert (LO5 : forall A n, A + n <= lo -> disjoint_from [(lo, SP + -144)] A n) by (intros A n H; cbn [disjoint_from]; clear - H; lia).
        assert (FR25 : rw_cells asegs m5 (SP + -144) [C8 (Z_to_bv 64 (A_DEP + 4 * bi)); C8 (Z_to_bv 64 (N + 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x089840)])
          by (eapply rw_cells_transport; [exact FR2z| exact MU5| exact WM5| cbn [disjoint_from cells_size csize Nat.add]; clear; lia]).
        assert (MX5 : rw_cells asegs m5 A_DEP_NODES [C4 (Z_to_bv 64 1)])
          by (eapply rw_cells_transport; [exact MXz| exact MU5| exact WM5| apply LO5; unfold A_DEP_NODES; cbn; clear -LOIMG; lia]).
        assert (M15 : rw_cells asegs m5 (A_DEP_MAP1 + 8 * k) [C8 (Z_to_bv 64 0)])
          by (eapply rw_cells_transport; [exact M1z| exact MU5| exact WM5| apply LO5; unfold A_DEP_MAP1; cbn; clear -LOIMG KB; lia]).
        assert (NEW5 : zblock m5 ua 1048576)
          by (eapply zblock_transport; [exact NEWz| clear; lia| exact MU5| exact WM5| apply LO5; clear -UA ACE AC LOIMG; lia]).
        clear FR2z MXz M1z NEWz STz.
        replace (SP + -144) with (SP + -112 + -32) in * by lia.
        eapply evtA_cut.
        { eapply (tc_B AL IMG ALWF (CSf (nb ++ [ua]) bl) (CSOKf (nb ++ [ua]) bl)) with (m0 := m5);
            [ | | exact FR25 | exact MX5 | exact M15 | exact ST5 | | | | | apply munch_refl | apply wmono_refl | exact MI5 | ]; try lia.
          eapply (crange_sub (CSf (nb ++ [ua]) bl) lo (SP - lo)); [exact SCS'| lia| lia]. }
        cbn beta. (intros ms1 dd_H; ddestruct dd_H as (m6 & -> & MU6 & WM6 & MI6 & MX6 & M16 & ST6)).
        replace (ret_pc (Z_to_bv 64 0x089840)) with (Z_to_bv 64 0x089840) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
        eapply evtA_mono. { eapply (dput_j AL IMG ALWF (CSf (nb ++ [ua]) bl) (CSOKf (nb ++ [ua]) bl)). exact MI6. }
        cbn beta. intros ms1 ->.
        unfold nc_ms_post. deexists 16. fold k. change (2^20) with 1048576.
        replace (SP + -112 + -32 + 32) with (SP + -112) in * by lia.
        split; [reflexivity|].
        split. { eapply munch_trans. { eapply munch_weaken; [| exact MU1z]. unfold sub_fp; cbn [outside]. clear. intros x Hx. lia. }
                 eapply munch_trans. { eapply munch_weaken; [| exact MU5]. unfold sub_fp; cbn [outside]. clear. intros x Hx. lia. }
                 eapply munch_weaken; [| exact MU6]. unfold sub_fp; cbn [outside]. clear. intros x Hx. lia. }
        split. { eapply wmono_trans. 2: { eapply wmono_trans; [exact WM5| exact WM6]. } eapply wmono_trans; [exact WM3| exact WMz]. }
        split; [exact MI6|]. split; [exact MX6|]. split; [exact M16|].
        split. { eapply zblock_transport; [exact NEW5| clear; lia| exact MU6| exact WM6|]. unfold A_DEP_NODES, A_DEP_MAP1; cbn [disjoint_from].
                 clear -UA ACE AC LOIMG KB. lia. }
        exact ST6. }
      (* [comment removed for export] *)
      cbn beta. intros ms7 mo7 PO HK7 MM7 HJ7. apply aevtS_now.
      ddestruct PO as (x1 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m7 & -> & MU7 & WM7 & MI7 & MX7 & M17 & NEW7 & ST7).
      dexists (Z_to_bv 64 ua), mo7. deexists 16. rewrite unsigned_lit by lia. fold k. change (2^20) with 1048576.
      split; [reflexivity|]. split; [exact HK7|]. split; [exact HJ7|]. split; [exact CR4|].
      split; [exact AAL|]. split; [exact UA|]. split; [clear -ACE AC; lia|].
      split. { intros x Hx. apply AP. left. exact Hx. }
      split; [exact MU7|]. split; [exact WM7|]. split; [exact MI7|]. split; [exact MX7|]. split; [exact M17|]. split; [exact NEW7| exact ST7].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L45993720998.23L60111963937.23L61667541554.2300000?00M00YS3hAR2bl1j2NE1nS3hAR2bl1j1H1lS3hAR2bl1j1l". (* [comment removed for export] *)
  #[using="hAR"] Lemma sptr_app_old : forall bl a j, 0 <= j -> j <> Z.of_nat (length bl) -> sptr (bl ++ [a]) j = sptr bl j.
  Proof.
    intros bl a j H NE. unfold sptr, sblk. rewrite app_length. cbn [length].
    destruct (Z.ltb_spec0 j (Z.of_nat (length bl))).
    - replace (j <? Z.of_nat (length bl + 1)) with true by (symmetry; apply Z.ltb_lt; lia). rewrite app_nth1 by lia. reflexivity.
    - replace (j <? Z.of_nat (length bl + 1)) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L11172880392.19L7992048299.19 00000800@S3hAR2blS3hAR2bl". (* [comment removed for export] *)
  #[using="hAR"] Lemma sptr_app_new : forall bl a, sptr (bl ++ [a]) (Z.of_nat (length bl)) = a.
  Proof.
    intros bl a. unfold sptr, sblk. rewrite app_length. cbn [length].
    replace (Z.of_nat (length bl) <? Z.of_nat (length bl + 1)) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite Nat2Z.id, app_nth2, Nat.sub_diag by lia. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L7992048299.19000008S3hAR2bl". (* [comment removed for export] *)
  #[using="hAR"] Lemma sblk_app_new : forall bl a, sblk (bl ++ [a]) (Z.of_nat (length bl)) = a.
  Proof. intros. unfold sblk. rewrite Nat2Z.id, app_nth2, Nat.sub_diag by lia. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L60112426309.2100000<S3hAR2bl1j1H". (* [comment removed for export] *)
  #[using="hAR"] Lemma sblk_app_old : forall bl a j, 0 <= j < Z.of_nat (length bl) -> sblk (bl ++ [a]) j = sblk bl j.
  Proof. intros. unfold sblk. rewrite app_nth1 by lia. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition asc_svc_post (SP : Z) (gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo id v size tag start : Z) (stored : word) (m1 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotCfg ()) "Lms',$4>.(3=.(14.&40.)Lt0,(14.&40.)(3=.(14.&40.)Lt1,(14.&40.)(3=.(14.&40.)Lt2,(14.&40.)(3=.(14.&40.)Lt3,(14.&40.)(3=.(14.&40.)Lt4,(14.&40.)(3=.(14.&40.)Lt5,(14.&40.)(3=.(14.&40.)Lt6,(14.&40.)(3=.(14.&40.)La6,(14.&40.)(3=.(14.&40.)Lalloc',(14.&40.)(3=.P,(14.&40.)(15.(14.&8.))Lmm,P,(14.&40.)(15.(14.&8.))(3=.(12.(14.&8.))Lfr,(12.(14.&8.))Zcount,$18.(1:.O5.+1.)Zj,$18.(3>.O3.(39.+2.+14.))ZSSB,$18.(1:.(1:.$58.+10.)(43.+10.R1.))(0.(1=.$4>.R?.(4?.(41.(7.&40.+7<>><.)(7.&40.(1:.(1:.O?.-100.)-30.))O>.O=.R>.R=.R<.(7.&40.+2424:.)(7.&40.+800000.)(7.&40.=)(7.&40.+800000.)(7.&40.+3.)(7.&40.+4022.)(7.&40.-1.)(7.&40.=)R7.(7.&40.+=>.)(7.&40.$8.)(7.&40.(1:.O?.-68.))(7.&40.O5.)(7.&40.O4.)(7.&40.+????.)(7.&40.O7.)(7.&40.$45.)(7.&40.O6.)O<.O;.R;.R:.R9.R8.)O:.(7.&40.$50.)(7.&40.+=>.)O9.(46.(14.&40.))R5.(47.$2.)))(0.(17.(4.(2?.$18.$18.)(49.$18.$18.O8.(1:.O?.->0.))(4.(2?.$18.$18.)(49.$18.$18.R1.(1:.R1.+10.))(4.(2?.$18.$18.)(49.$18.$18.(1:.$58.+8.)(1:.$58.+10.))(9.(2?.$18.$18.)))))O1.R5.)(0.(2;.$2.O1.R5.)(0.(4:.$2.R5.)(0.(4;.$2.R5.(1:.O?.-100.)(4.$5.(6.(7.&40.R3.))(4.$5.(6.(7.&40.$58.))(4.$5.(6.(7.&40.O3.))(4.$5.(6.(7.&40.+871=<.))(9.$5.))))))(0.(4;.$2.R5.R1.(4.$5.(6.(7.&40.=))(4.$5.(11.O2.)(4.$5.(11.(7.&40.+1.))(9.$5.)))))(0.(4;.$2.R5.(1:.$58.+8.)(4.$5.(6.R6.)(9.$5.)))(0.(4;.$2.R5.(1:.(1:.O?.-100.)-30.)(4.$5.(51.#<.R4.)(4.$5.(11.(7.&40.+4022.))(4.$5.(6.(7.&40.R3.))(4.$5.(6.(7.&40.R1.))(4.$5.(6.(7.&40.(1:.R1.+<.)))(4.$5.(6.(7.&40.+87;20.))(9.$5.))))))))(4=.$2.R5.O8.(1:.(1:.O?.-100.)-30.)))))))))))))))))))))")
(* [comment removed for export] *).

  Definition sc_ms_post (SP : Z) (gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo id v size tag start ua : Z) (stored : word) (m1 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotCfg ()) "Lms',$4>.(3=.(14.&40.)Lx5,(14.&40.)(3=.(14.&40.)Lx6,(14.&40.)(3=.(14.&40.)Lx7,(14.&40.)(3=.(14.&40.)Lx11,(14.&40.)(3=.(14.&40.)Lx12,(14.&40.)(3=.(14.&40.)Lx13,(14.&40.)(3=.(14.&40.)Lx14,(14.&40.)(3=.(14.&40.)Lx15,(14.&40.)(3=.(14.&40.)Lx16,(14.&40.)(3=.(14.&40.)Lx17,(14.&40.)(3=.(14.&40.)Lx28,(14.&40.)(3=.(14.&40.)Lx29,(14.&40.)(3=.(14.&40.)Lx30,(14.&40.)(3=.(14.&40.)Lx31,(14.&40.)(3=.(14.&40.)Lalloc',(14.&40.)(3=.P,(14.&40.)(15.(14.&8.))Lm',P,(14.&40.)(15.(14.&8.))Zcount,$18.(1:.O6.+1.)Zj,$18.(3>.O4.(39.+2.+14.))ZSSB,$18.(1:.(1:.$58.+10.)(43.+10.R1.))(0.(1=.$4>.R14.(40.(41.(7.&40.+8701<.)(7.&40.(1:.O10.-=0.))O?.O>.R13.R12.R11.(7.&40.(1:.O10.-88.))(7.&40.$58.)(7.&40.(1:.O3.(43.+8.(38.O4.(39.+2.+14.)))))R10.R?.R>.R=.R<.R;.R:.(7.&40.R3.)(7.&40.(1:.O10.-68.))(7.&40.O6.)(7.&40.O5.)(7.&40.+????.)(7.&40.O8.)(7.&40.$45.)(7.&40.O7.)O=.O<.R9.R8.R7.R6.)O;.(7.&40.+8701<.)O:.(46.(14.&40.))R4.(47.$2.)))(0.(17.(4.(2?.$18.$18.)(49.$18.$18.O9.(1:.O10.-=0.))(4.(2?.$18.$18.)(49.$18.$18.R1.(1:.R1.+10.))(4.(2?.$18.$18.)(49.$18.$18.(1:.$58.+8.)(1:.$58.+10.))(4.(2?.$18.$18.)(49.$18.$18.O3.(1:.O3.(39.+2.+17.)))(9.(2?.$18.$18.))))))O1.R4.)(0.(2;.$2.O1.R4.)(0.(4:.$2.R4.)(0.(4;.$2.R4.R1.(4.$5.(6.(7.&40.O3.))(4.$5.(11.O2.)(4.$5.(11.(7.&40.=))(9.$5.)))))(0.(4;.$2.R4.(1:.$58.+8.)(4.$5.(6.R5.)(9.$5.)))(0.(4<.R4.O3.(39.+2.+17.))(4=.$2.R4.O9.(1:.O10.-=0.)))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition sc_post (SP : Z) (gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo id v size tag start : Z) (stored : word) (nb bl : list Z) (m1 : mem) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotCfg ()) "Lc,$3<.(3=.(14.&40.)La,(14.&40.)(3=.$2<.Lmo',$2<.(3=.$4>.Lms',$4>.Zua,$18.(34.&40.R3.)(0.(1=.$3<.R5.(3?.R2.R3.))(0.(59.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.R1.O4.O1.R2.)(0.A3.VK,O3.(2>.$18.O2.(4.$18.R1.(9.$18.)))R3.(0.(48.(5:.R2.)R3.)(0.(3;.A2.VCSf,O3.(2>.$18.O2.(4.$18.R1.(9.$18.)))R1.(39.+2.+17.))(0.(1=.$18.(38.R1.+1000.)=)(0.(19.+65?000.R1.)(0.(19.(1:.R1.(39.+2.+17.))(35.VhAR,))Px,$18.P,A3.VCSf,O3.O2.R1.(28.(0.(19.R3.R2.)(27.R2.(1:.R3.(39.+2.+17.))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0210@L10450802925.136L12030434098.168L1221399369.10  L13082802807.8  L13390990976.168L15705862633.168L1685717371.0   L17726094674.5  L18259764001.0  L18928845099.133L18928845099.134L18994852257.0  L19611395117.15 L20706231372.5  L20706382247.122L20711535332.109L21566014262.146L21566014266.120L21567736999.140L21872102637.167L2252154983.107 L22706556809.5  L22706556809.7  L24646060050.5  L25119104203.168L27835597014.168L27835731415.159L27835812809.140L27846114761.105L27846114761.109L27846298584.84 L28165445704.105L28573892092.5  L28573892092.7  L29603613565.3  L30932029636.10 L31093097181.14 L31097375196.20 L31179887929.117L32536031514.173L32633767048.168L32646038717.20 L33461716904.3  L33656615698.5  L33670951324.3  L3451333718.10  L3451333718.9   L34903592768.140L35304476264.168L3560269315.123 L36690522898.12 L36841451887.5  L36901663178.159L37229909125.140L37242789033.5  L37636168117.20 L37640540852.14 L37775525245.3  L38034391150.120L38237949960.3  L38237950652.84 L38238282925.105L38238282925.109L38248436397.140L38248749490.168L38248879283.159L38277021303.109L38278908023.140L38415221037.140L41596053424.5  L41599022925.2  L41600592437.4  L42148793844.20 L42151129310.105L42151129310.109L42152888030.140L42153068277.14 L42153233857.168L43981602216.3  L44132461375.14 L44136177726.20 L45638961737.118L46269956903.3  L46405638542.0  L47534785782.109L47541285622.140L47599687292.105L47922842274.118L48537706372.105L49607210629.118L50688752264.8  L50850525385.0  L51644041780.20 L51656966453.14 L52029284603.3  L52150340519.20 L52154089638.14 L52771474835.3  L53512949285.108L55588686165.0  L567271841.0    L56735376283.105L57061183981.3  L57628700040.7  L58421828776.140L58817380240.10 L59314873579.129L59314955108.108L59576973665.121L59577082002.116L59583441669.108L59760603398.118L60409382626.109L60614818520.109L61111704085.165L63565201236.168L6430849802.140 L65919309516.0  L66566358642.135L67705739082.107L7439011206.15  L7781518090.3   L8210306397.20  L8214027868.14  L8533527060.159 L8806423751.7   L8826417067.140 L8841419179.105 L8841419179.109 00000n00o01X02:02d03Q03R03g03h04N05405505h06606`06a07M08908e09K09L09\0:10:F0:l0;U0<>0<g0=K0=o0>S0>T0>d0?90?=0?W0@10@P0A:0A`0BM0Bl0C70C@0CA0Cf0DK0E40E^0FD0Fo0G<0Gb0HL0HZ0I60IM0IQ0J20J60JZ0K>0Kb0LK0M40M]0NB0Nl0Nm0O>0OE0OV0P70Pa0QK0R:0RV0SE0SP0Sl0TM0U@0UN0UO0V70Vd0WI0Wo0XW0YE0Y\0Y]0Z>0ZZ0Ze0[I0[h0[l0\M0\N0\O0]00];0]P0]Q0^:0^j0_M0`30`Y0a:0af0ag0ah0bN0c70c80c90d20d30dd0dk0eG0e^0fD0fY0g?0g`0hAS3hAR2AL2SP4size5start2bl5count1j2S04IMG'1a2ua1A2sz2H12H21x2HxFS3hAR2SP2lo5start1j3SSB2JB5LOIMG3SPL4HSSBS3hAR2lo5start1j3SSB2JB5LOIMG4HSSBS3hAR2SP4size5start2bl5count1j2S03SPA1a2uaS3hAR2SP2lo4size5start2bl5count1j2S03SPL1a2uaSS5start1j3SSB2JB4HSSBSS3hAR2SP4size5start2bl5count1j2S01a2uaS3hAR2SP4size5start2bl5count1j2S01a2uaSS3hAR2SP2lo5start1j3SSB2JB5LOIMG4HSSB1a2ua2UA1A1n1HS3hAR1a2ua3ACES3hAR2SP4size5start2bl5count1j2S01a2ua3ACEFS3hAR2SP4size5start2bl5count1j2S01a2ua2A02ARS3hAR2SP4size5start2bl5count1j2S01a2ua2A02ARS3hAR2SP4size5start2bl5count1j2S01a2ua2A02ARS3hAR2SP4size5start2bl5count1j2S01a2uaFS2SP2lo3SSB1x2HxS2SP2lo3SSB1a2ua1x2HxS5start1j3SSB2JB4HSSBS3hAR2SP4size5start2bl5count1j2S01a2uaS3hAR2SP2lo4size5start2bl5count1j2S01a2uaS3hAR2SP2lo4size5start2bl5count1j2S01a2uaS3hAR2SP2lo4size5start2bl5count1j2S01a2uaS3hAR2SP2lo4size5start2bl5count1j2S0S3hAR2SP2lo4size5start2bl5count1j2S0S3hAR2SP2lo4size5start2bl5count1j2S0FS2SP2lo3SSB1x2HxS2SP2lo3SSB1a2ua1x2HxS2SPS3hAR2SP2lo5LOIMG1a2ua3ACES3hAR2SP2lo5start1j2S03SPLS3hAR2SP2lo5start1j2S03SPL1a2uaS3hAR2SP4size5start2bl5count1j2S01a2ua3ACES3hAR2SP4size5start2bl5count1j2S01a2uaS3hAR2SP4size5start2bl5count1j2S01a2ua2A03ACES3hAR2SP5start1j2S01a2ua3ACE2UAS2SP2lo3SPLS5start1jSS3hAR2SP2lo5start1j3SSB2JB5LOIMG4HSSBS3hAR2SP2lo5start1j3SSB2JB5LOIMG4HSSBS3hAR2SP4size5start2bl5count1j2S01a2ua2A0S3hAR2SP4size5start2bl5count1j2S03SPH1a2uaS3hAR2SP4size5start2bl5count1j2S01a2uaS3hAR2SP2lo5start1j3SSB2JB5LOIMG4HSSB1A1n1HS2SP2lo1A1n1HS3hAR2SP4size5start2bl5count1j2S01a2uaS3hAR2SP4size5start2bl5count1j2S01a2ua3ACES3hAR1a2ua3ACES3hAR2SP5start1j2S03SPA1a2uaS3hAR2SP5start1j2S03SPAS2SPS3hAR2SP4size5start2bl5count1j2S0S2loS3hAR2SP2lo4size5start2bl5count1j2S0S3hAR2SP2lo4size5start2bl5count1j2S0S3hAR2SP2lo4size5start2bl5count1j2S0S3hAR2SP2lo4size5start2bl5count1j2S01a2uaS3hAR2SP2lo4size5start2bl5count1j2S01a2uaS3hAR2SP2lo4size5start2bl5count1j2S01a2uaS3hAR2SP4size5start2bl5count1j2S03SPHS3hAR2SP4size5start2bl5count1j2S03SPH1a2uaFS3hAR2SP2lo5LOIMGS2SP2loS3hAR2SP2lo5LOIMGS3hAR2SP2lo5start1j2S05LOIMG1a2uaS3hAR2SP2lo4size5start2bl5count1j2S05LOIMGS3hAR2SP2lo4size5start2bl5count1j2S05LOIMGS3hAR2SP2lo4size5start2bl5count1j2S05LOIMG1a2uaS3hAR2SP2lo5start1j2S05LOIMGS3hAR2SP2lo4size5start2bl5count1j2S05LOIMG1a2uaS2SP2lo3SPLS3hAR2SP5start1j3SSB2S04HSSBS3hAR2SP5start1j3SSB2S04HSSB1a2uaS3hAR2AL2SP4size5start2bl5count1j2S04IMG'1a2ua1H2H0S3hAR2lo5LOIMGSS3hAR2SP2lo4size5start2bl5count1j2S03SPLS3hAR2SP2lo4size5start2bl5count1j2S03SPL1a2uaS3hAR2SP4size5start2bl5count1j2S03SPHS3hAR2SP4size5start2bl5count1j2S01a2uaS3hAR2SP2lo4size5start2bl5count1j2S03SPLS3hAR2AL2SP4size5start2bl5count1j2S04IMG'1a2uaS3hAR2lo5LOIMG1a2ua3ACESS3hAR2SP5start1j3SSB2S04HSSB1a2uaS3hAR2SP5start1j3SSB2S04HSSBS2SP2lo3SPLS3hAR2SP5start1j3SSB2JB2S04HSSB1a2uaS3hAR2SP5start1j3SSB2JB2S04HSSBS2SPS3hAR2SP4size5start2bl5count1j2S0SSS3hAR2SP4size5start2bl5count1j2S0S2SP2lo3SPLS2SP2lo3SSB1a2ua1x2HxFS3hAR2SP2lo5start1j3SSB2JB5LOIMG4HSSB3SPLS3hAR2SP4size5start2bl5count1j2S01a2ua2UA1x2Hx1HS3hAR2SP4size5start2bl5count1j2S01ES3hAR2SP4size5start2bl5count1j2S01a2uaS3hAR2SP4size5start2bl5count1j2S01a2uaS3hAR2SP4size5start2bl5count1j2S0S3hAR2SP4size5start2bl5count1j2S01a2ua2A02H0FFS3hAR2SP4size5start2bl5count1j2S01a2uaS3hAR2SP4size5start2bl5count1j2S02S11a2uaFSS3hAR2SP2lo4size5start2bl5count1j2S01a2ua1A2sz2H12H21x2HxFS3hAR2SP2lo5start1j3SSB2JB5LOIMG4HSSB1a2ua3ACE2UAS2SP2loS3hAR2SP5start1j2S03SPH1a2uaS3hAR2SP5start1j2S03SPHS3hAR2SP4size5start2bl5count1j2S01a2uaS2SP2lo3SSB1a2ua1x2HxS3hAR2SP4size5start2bl5count1j2S01a2uaS3hAR2SP4size5start2bl5count1j2S0S3hAR2SP4size5start2bl5count1j2S0". (* [comment removed for export] *)
  #[using="AL IMG ALWF CSOKf KL CSmono_s K_apart T_store ROOM_s"] Lemma store_create_cfg : ltac2:(CDefT.buildp (gd_tbl_AW_DepotCfg ()) "Pgp,(14.&40.)Ptp,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)Px5,(14.&40.)Px6,(14.&40.)Px7,(14.&40.)Px12,(14.&40.)Px14,(14.&40.)Px16,(14.&40.)Px17,(14.&40.)Px28,(14.&40.)Pstored,(14.&40.)Palloc,(14.&40.)PSP,$18.PF,(52.&5.(14.&40.))Pfc,(14.&20.)Pm1,P,(14.&40.)(15.(14.&8.))Pmo,$2<.Plo,$18.Pid,$18.Pv,$18.Psize,$18.Ptag,$18.Pstart,$18.Ptf,$18.Pnb,(12.$18.)Pbl,(12.$18.)Zcount,$18.(1:.R6.+1.)Zj,$18.(3>.R5.(39.+2.+14.))ZSSB,$18.(1:.(1:.$58.+10.)(43.+10.R1.))P,(0.(19.=R2.)(27.R2.+1000.))P,(1=.$18.R3.(5;.(5<.$18.R5.)))P,(19.=R9.)P,(27.(1:.R:.+40.)(39.+2.+20.))P,(0.(19.+1.R=.)(19.R=.+1>.))P,(0.(19.=R=.)(27.R=.+100.))P,(0.(19.=R11.)(27.R11.(39.+2.+1?.)))P,(0.(19.=R11.)(27.R11.(39.+2.+1?.)))P,(4;.$2.R16.(1:.R19.->0.)(4.$5.(6.(7.&40.(1:.R19.-88.)))(4.$5.(6.(7.&40.+8701<.))(9.$5.))))P,(4;.$2.R17.R:.(4.$5.(6.(7.&40.=))(4.$5.(11.R1<.)(4.$5.(11.(7.&40.=))(9.$5.)))))P,(4;.$2.R18.$58.(4.$5.(6.(7.&40.R10.))(4.$5.(6.R1<.)(9.$5.))))P,(54.R19.)P,(4=.$2.R1:.R18.(1:.R1=.->0.))P,(19.(35.VhAR,)R19.)P,(19.R1:.(53.R1?.+240.))P,(19.R20.(39.+2.+3>.))P,(1=.$18.(38.R21.+10.)=)P,(3;.A2.VCSf,R16.R15.R1=.(53.R22.R1=.))P,(4:.$2.R20.)P,A3.VK,R18.R17.R20.P,(48.R22.R21.)P,A2.VGs,R1:.R19.(55.$2.(5=.R27.R38.R37.R36.R35.R26.R25.R22.R21.R20.R1?.R1>.R1=.R29.R1;.R1:.R24.)(3?.(40.(41.(7.&40.+871=<.)(7.&40.(1:.R27.->0.))R38.R37.R31.R30.R2?.(7.&40.R1=.)(7.&40.$58.)(7.&40.R17.)(7.&40.$58.)R2>.(7.&40.(1:.R27.-88.))R2=.(7.&40.R19.)R2<.R2;.(7.&40.R19.)(7.&40.(1:.R27.-68.))(7.&40.R1?.)(7.&40.R1>.)(7.&40.+????.)(7.&40.R21.)(7.&40.$45.)(7.&40.R20.)R36.R35.R2:.R34.R33.R32.)R26.(7.&40.$5>.)R25.(46.(14.&40.))R24.(47.$2.))R23.))")
(* [comment removed for export] *).
  Proof.
    intros gp tp s10 s11 t4 t5 t6 x5 x6 x7 x12 x14 x16 x17 x28 stored alloc SP F fc m1 mo lo id v size tag start tf nb bl count j SSB
      JB JL S0 S1 SZ TG ID VB FRA BX SSX CST ST LOIMG SPL SPH SPA SCS MI HK HJ GS.
    facts. dpose CST as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    assert (HSSB : SSB = A_SS + 16 + 16 * j) by reflexivity. clearbody SSB.
    (* [comment removed for export] *)
    pose proof (proj1 (rw_cells_app asegs m1 A_SS [C8 (Z_to_bv 64 tf)] _) SSX) as [SS0 SS8]. cbn [cells_size csize Nat.add] in SS8. clear SSX.
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL (CSf nb bl) (K nb bl) (asc_svc_post SP gp tp s10 s11 F fc lo id v size tag start stored m1) _ _ mo (KL nb bl) HK); [exact HJ| |].
    {
      eapply evtA_cut.
      { eapply (bc_A AL IMG ALWF (CSf nb bl) (CSOKf nb bl)) with (SSB := SSB); try eassumption.
        all: first [ eapply (crange_sub (CSf nb bl) lo (SP - lo)); [exact SCS| lia| lia]
                   | unfold A_SS; unfold A_SS in HSSB; clear - HSSB JB S0 S1 SPL SPH SPA LOIMG; lia
                   | match goal with |- ?G => idtac "BCA" G end]. }
      cbn beta. (intros ms1 dd_H; ddestruct dd_H as (y2 & y3 & y4 & y5 & alloc' & m2 & -> & MU2 & WM2 & MI2 & FR2 & BX2 & AX2 & ST2)).
      assert (CST2 : cstatics m2).
      { eapply (cstatics_transport _ m1 m2 CST MU2). intros A n H. unfold A_SS in *. cbn [disjoint_from]. clear - H LOIMG HSSB JB. lia. }
      dpose CST2 as (G1' & G2' & G3' & G4' & G5' & G6' & G7').
      eapply evtA_mono.
      { eapply (mmapnrdie_pre AL IMG ALWF (CSf nb bl) (CSOKf nb bl)); try eassumption; try lia.
        eapply (crange_sub (CSf nb bl) lo (SP - lo)); [exact SCS| lia| lia]. }
      cbn beta. (intros ms1 dd_H; ddestruct dd_H as (t0' & t1' & t2' & t3' & t4' & t5' & t6' & a6' & mm & fr & -> & MU3 & WM3 & MI3 & FR3 & ST3)).
      unfold asc_svc_post. deexists 11. fold j. rewrite <- HSSB.
      replace (SP + -224 + -32) with (SP + -256) in * by lia.
      split; [reflexivity|].
      split. { eapply munch_trans. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]. clear. intros x Hx. lia. }
               eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]. clear. intros x Hx. lia. }
      split; [eapply wmono_trans; [exact WM2| exact WM3]|]. split; [exact MI3|].
      split. { eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize Nat.add]. clear; lia. }
      split. { eapply rw_cells_transport; [exact BX2| exact MU3| exact WM3|]. unfold A_SS in *; cbn [disjoint_from cells_size csize Nat.add]. clear -LOIMG HSSB JB; lia. }
      split. { eapply rw_cells_transport; [exact AX2| exact MU3| exact WM3|]. unfold A_SS; cbn [disjoint_from cells_size csize Nat.add]. clear -LOIMG; lia. }
      split; [exact FR3| exact ST3]. }
    (* [comment removed for export] *)
    cbn beta. intros ms3 mo3 PRE HK3 MM3 HJ3.
    ddestruct PRE as (t0' & t1' & t2' & t3' & t4' & t5' & t6' & a6' & alloc' & mm & fr & -> & MU3 & WM3 & MI3 & FR2 & BX3 & AX3 & FR3 & ST3).
    fold j in MU3, BX3, FR3. rewrite <- HSSB in MU3, BX3, FR3.
    eapply (aevtS_mmap_anon asegs _) with (nZ := 8388608) (flags := 0x4022).
    { exact (ki_halted (KL nb bl) mo3 HK3). }
    { exact (ki_top (KL nb bl) mo3 HK3). }
    { unfold mmap_anon_args, areg, MSsvc. cbn [ms_regs]. simp_regs.
      repeat split; try reflexivity; try lia.
      - intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia.
      - right. reflexivity. }
    { change 8388608 with (2^23). apply (ROOM_s nb bl mo3 GS HK3). }
    - (* [comment removed for export] *)
      intros e HIn. right. destruct HIn as [<-|[]].
      rewrite nret_MSsvc, mkR_set_a0, apply_mem_none.
      replace (errno_ret ENOMEM) with (Z_to_bv 64 (2^64 - 12)) by (apply bv_eq; vm_compute; reflexivity).
      change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
      pose proof (cstatics_transport _ m1 mm CST MU3 ltac:(intros A n H; unfold A_SS in *; cbn [disjoint_from]; clear - H LOIMG HSSB JB; lia)) as (_ & _ & _ & _ & _ & G6' & G7').
      change (Z_to_bv 64 8388608) with (Z_to_bv 64 ((8388608 + 4095) / 4096 * 4096)).
      eapply (evtA_spinJ_K asegs AL (CSf nb bl) (K nb bl) _ _ mo3 (KL nb bl) HK3).
      {
        eapply (mmapnrdie_post_die AL IMG ALWF (CSf nb bl) (CSOKf nb bl)) with (m0 := mm); try eassumption; try lia.
        apply munch_refl. apply wmono_refl. eapply (crange_sub (CSf nb bl) lo (SP - lo)); [exact SCS| lia| lia]. }
      cbn beta. intros ms5 mo5 PO HK5 _. ddestruct PO as (r' & F' & mm' & ->).
      apply spinningJ_at; [cbn; tauto| exact (ki_halted (KL nb bl) mo5 HK5)].
    - (* [comment removed for export] *)
      intros a AAL A0 ACE RF.
      rewrite nret_MSsvc, mkR_set_a0, apply_mem_zeros.
      change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
      pose proof (bv_unsigned_in_range 64 a) as AR. unfold bv_modulus in AR. change (2 ^ Z.of_N 64) with (2^64) in AR.
      set (ua := bv_unsigned a) in *.
      pose proof aceil_bounds as AC.
      pose proof (K_apart nb bl mo3 a (Z_to_bv 64 8388608) HK3 RF) as AP. fold ua in AP.
      replace (bv_unsigned (Z_to_bv 64 8388608)) with 8388608 in AP by (symmetry; apply unsigned_lit; lia).
      specialize (AP ltac:(clear; lia) ltac:(clear - ACE AC; lia)).
      assert (UA : 0x65f000 <= ua).
      { destruct (Z.le_gt_cases 0x65f000 ua); [assumption|]. exfalso.
        destruct (Z.le_gt_cases 0x10000 ua).
        - apply (AP ua). right; lia. lia.
        - apply (AP 0x10000). right; lia. lia. }
      destruct (T_store nb bl mo3 a GS HK3 AAL A0 ltac:(change (2^23) with 8388608; lia) RF) as [HK4 CR4]. fold ua in HK4, CR4.
      pose proof (J_anon_grant mm mo3 0x4022 a 8388608 HJ3 ltac:(clear; lia) ltac:(fold ua; clear - ACE AC; lia) RF) as HJ4.
      rewrite <- (Z_to_bv_bv_unsigned a). fold ua. change (Z_to_bv 64 ua, Z_to_bv 64 8388608) with (wa ua, Z_to_bv 64 8388608).
      rewrite <- (Z_to_bv_bv_unsigned a) in HK4. fold ua in HK4. change (2 ^ 23) with 8388608 in HK4, CR4.
      rewrite <- (Z_to_bv_bv_unsigned a) in HJ4. fold ua in HJ4. change (Z_to_bv 64 ua, Z_to_bv 64 8388608) with (wa ua, Z_to_bv 64 8388608) in HJ4.
      assert (Ha : 0 <= ua < 2^64) by lia. assert (Hn : 0 <= 8388608 < 2^64) by lia. assert (Han : ua + 8388608 <= 2^64) by lia.
      pose proof (munch_zeros mm ua 8388608 Ha Hn Han [(ua, ua + 8388608)] mm (munch_refl _ mm) ltac:(cbn; lia)) as MUz.
      pose proof (wmono_zeros asegs mm ua 8388608 Ha Hn Han mm (wmono_refl asegs mm)) as WMz.
      assert (MIz : mem_inv asegs (apply_zeros mm [(wa ua, Z_to_bv 64 8388608)])).
      { eapply (mem_inv_zeros asegs mm ua 8388608 Ha Hn Han MI3). intros x Hx.
        destruct (ro_addr asegs x) eqn:E; [|reflexivity]. exfalso. pose proof (asegs_ro_lt x E). lia. }
      pose proof (rw_cells_zeros_new asegs mm ua 8388608 Ha Hn Han : zblock _ ua 8388608) as NEWz.
      set (mz := apply_zeros mm [(wa ua, Z_to_bv 64 8388608)]) in *. clearbody mz.
      assert (APstk : forall A sz, lo <= A -> A + sz <= SP -> 0 < sz -> A + sz <= ua \/ ua + 8388608 <= A).
      { intros A sz H1 H2 H3. eapply (apart_of (fun x => CSf nb bl x \/ al_img_lo AL <= x < al_img_hi AL)); [exact AP| | exact H3| lia].
        intros x Hx. left. apply SCS. lia. }
      assert (APimg : forall A sz, 0x10000 <= A -> A + sz <= 0x65f000 -> 0 < sz -> A + sz <= ua \/ ua + 8388608 <= A).
      { intros A sz H1 H2 H3. eapply (apart_of (fun x => CSf nb bl x \/ al_img_lo AL <= x < al_img_hi AL)); [exact AP| | exact H3| lia].
        intros x Hx. right. lia. }
      (* [comment removed for export] *)
      assert (FR2z : rw_cells asegs mz (SP + -256) [C8 (Z_to_bv 64 count); C8 (Z_to_bv 64 A_SS); C8 (Z_to_bv 64 start); C8 (Z_to_bv 64 0x0871dc)]).
      { eapply rw_cells_transport; [exact FR2| exact MUz| exact WMz|]. cbn [disjoint_from cells_size csize Nat.add]. split; [|exact I]. apply APstk; clear -SPL; lia. }
      assert (FR3z : rw_cells asegs mz (SP + -256 + -48) [CB 12 fr; C4 (Z_to_bv 64 0x4022); C8 (Z_to_bv 64 count); C8 (Z_to_bv 64 SSB); C8 (Z_to_bv 64 (SSB + 12)); C8 (Z_to_bv 64 0x087b20)]).
      { eapply rw_cells_transport; [exact FR3| exact MUz| exact WMz|]. cbn [disjoint_from cells_size csize Nat.add]. split; [|exact I]. apply APstk; clear -SPL; lia. }
      assert (BXz : rw_cells asegs mz SSB [C8 (Z_to_bv 64 0); C4 stored; C4 (Z_to_bv 64 1)]).
      { eapply rw_cells_transport; [exact BX3| exact MUz| exact WMz|]. cbn [disjoint_from cells_size csize Nat.add]. split; [|exact I]. apply APimg; unfold A_SS in HSSB; clear -HSSB JB; lia. }
      assert (AXz : rw_cells asegs mz (A_SS + 8) [C8 alloc']).
      { eapply rw_cells_transport; [exact AX3| exact MUz| exact WMz|]. unfold A_SS; cbn [disjoint_from cells_size csize Nat.add]. split; [|exact I]. apply APimg; clear; lia. }
      assert (STz : stk asegs mz lo (SP + -256 + -48)).
      { eapply stk_transport_disjoint; [exact ST3| exact MUz| exact WMz|]. cbn [disjoint_from]. split; [|exact I]. apply APstk; clear -SPL; lia. }
      assert (MU1z : munch [(lo, SP + -224); (SSB, SSB + 16); (A_SS + 8, A_SS + 16); (ua, ua + 8388608)] m1 mz).
      { eapply munch_trans; [eapply munch_weaken; [|exact MU3] | eapply munch_weaken; [|exact MUz]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
      assert (CSTz : cstatics mz).
      { eapply (cstatics_transport _ m1 mz CST MU1z). intros A n H. unfold A_SS in *; cbn [disjoint_from]. clear -H LOIMG UA HSSB JB. lia. }
      dpose CSTz as (G1z & G2z & G3z & G4z & G5z & G6z & G7z).
      clear FR2 FR3 BX3 AX3 ST3.
      assert (SCS' : crange (CSf nb (bl ++ [ua])) lo (SP - lo)) by (intros x Hx; apply CSmono_s; apply SCS; exact Hx).
      eapply (evtA_aevtS_KJ AL (CSf nb (bl ++ [ua])) (K nb (bl ++ [ua])) (sc_ms_post SP gp tp s10 s11 F fc lo id v size tag start ua stored m1) _ _ _ (KL nb (bl ++ [ua])) HK4); [exact HJ4| |].
      {
        change (Z_to_bv 64 8388608) with (Z_to_bv 64 ((8388608 + 4095) / 4096 * 4096)).
        eapply evtA_cut.
        { eapply (mmapnrdie_post_ok AL IMG ALWF (CSf nb (bl ++ [ua])) (CSOKf nb (bl ++ [ua]))) with (m0 := mz) (a := Z_to_bv 64 ua);
            try eassumption; try (rewrite unsigned_lit by lia); try lia; try apply munch_refl; try apply wmono_refl.
          all: first [eapply (crange_sub (CSf nb (bl ++ [ua])) lo (SP - lo)); [exact SCS'| lia| lia] | match goal with |- ?G => idtac "PO" G end]. }
        cbn beta. (intros ms1 dd_H; ddestruct dd_H as (z0 & z1 & z2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m5 & -> & MU5 & WM5 & MI5 & ST5)).
        replace (ret_pc (Z_to_bv 64 0x087b20)) with (Z_to_bv 64 0x087b20) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
        replace (SP + -256 + -48 + 48) with (SP + -256) in * by lia.
        assert (LO5 : forall A n, A + n <= lo -> disjoint_from [(lo, SP + -256)] A n) by (intros A n H; cbn [disjoint_from]; clear - H; lia).
        assert (FR25 : rw_cells asegs m5 (SP + -256) [C8 (Z_to_bv 64 count); C8 (Z_to_bv 64 A_SS); C8 (Z_to_bv 64 start); C8 (Z_to_bv 64 0x0871dc)])
          by (eapply rw_cells_transport; [exact FR2z| exact MU5| exact WM5| cbn [disjoint_from cells_size csize Nat.add]; clear; lia]).
        assert (BX5 : rw_cells asegs m5 SSB [C8 (Z_to_bv 64 0); C4 stored; C4 (Z_to_bv 64 1)])
          by (eapply rw_cells_transport; [exact BXz| exact MU5| exact WM5| apply LO5; unfold A_SS in HSSB; cbn [cells_size csize Nat.add]; clear -LOIMG HSSB JB; lia]).
        assert (AX5 : rw_cells asegs m5 (A_SS + 8) [C8 alloc'])
          by (eapply rw_cells_transport; [exact AXz| exact MU5| exact WM5| apply LO5; unfold A_SS; cbn [cells_size csize Nat.add]; clear -LOIMG; lia]).
        assert (NEW5 : zblock m5 ua 8388608)
          by (eapply zblock_transport; [exact NEWz| clear; lia| exact MU5| exact WM5| apply LO5; clear -UA ACE AC LOIMG; lia]).
        clear FR2z BXz AXz NEWz STz.
        replace (SP + -256) with (SP + -224 + -32) in * by lia.
        eapply evtA_cut.
        { eapply (bc_B AL IMG ALWF (CSf nb (bl ++ [ua])) (CSOKf nb (bl ++ [ua]))) with (m0 := m5) (W := []) (SSB := SSB);
            [ | | | | exact FR25 | exact BX5 | exact ST5 | | | | | apply munch_refl | apply wmono_refl | exact MI5 | ].
          all: first [ eapply (crange_sub (CSf nb (bl ++ [ua])) lo (SP - lo)); [exact SCS'| lia| lia]
                     | unfold A_SS; unfold A_SS in HSSB; clear - HSSB JB S0 S1 UA ACE AC SPL SPH SPA LOIMG AR; lia
                     | match goal with |- ?G => idtac "BB" G end]. }
        cbn beta. (intros ms1 dd_H; ddestruct dd_H as (m6 & -> & MU6 & WM6 & MI6 & BX6 & ST6)).
        replace (ret_pc (Z_to_bv 64 0x0871dc)) with (Z_to_bv 64 0x0871dc) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
        replace (SP + -224 + -32 + 32) with (SP + -224) in * by lia.
        assert (AX6 : rw_cells asegs m6 (A_SS + 8) [C8 alloc'])
          by (eapply rw_cells_transport; [exact AX5| exact MU6| exact WM6| unfold A_SS in HSSB; unfold A_SS; cbn [disjoint_from cells_size csize Nat.add]; clear -HSSB JB LOIMG SPL; lia]).
        assert (NEW6 : zblock m6 ua 8388608)
          by (eapply zblock_transport; [exact NEW5| clear; lia| exact MU6| exact WM6| unfold A_SS in HSSB; cbn [disjoint_from]; clear -HSSB JB UA ACE AC LOIMG SPL; lia]).
        (* [comment removed for export] *)
        assert (FRA6 : rw_cells asegs m6 (SP + -208 + -16) [C8 (Z_to_bv 64 (SP + -136)); C8 (Z_to_bv 64 0x08701c)]).
        { replace (SP + -208 + -16) with (SP + -224) by lia.
          assert (FRA3 : rw_cells asegs mm (SP + -224) [C8 (Z_to_bv 64 (SP + -136)); C8 (Z_to_bv 64 0x08701c)])
            by (eapply rw_cells_transport; [exact FRA| exact MU3| exact WM3| unfold A_SS in HSSB; unfold A_SS; cbn [disjoint_from cells_size csize Nat.add]; clear -HSSB JB LOIMG SPL; lia]).
          assert (FRAz : rw_cells asegs mz (SP + -224) [C8 (Z_to_bv 64 (SP + -136)); C8 (Z_to_bv 64 0x08701c)])
            by (eapply rw_cells_transport; [exact FRA3| exact MUz| exact WMz| cbn [disjoint_from cells_size csize Nat.add]; split; [|exact I]; apply APstk; clear -SPL; lia]).
          assert (FRA5 : rw_cells asegs m5 (SP + -224) [C8 (Z_to_bv 64 (SP + -136)); C8 (Z_to_bv 64 0x08701c)])
            by (eapply rw_cells_transport; [exact FRAz| exact MU5| exact WM5| cbn [disjoint_from cells_size csize Nat.add]; clear; lia]).
          eapply rw_cells_transport; [exact FRA5| exact MU6| exact WM6| unfold A_SS in HSSB; cbn [disjoint_from cells_size csize Nat.add]; clear -HSSB JB LOIMG SPL; lia]. }
        replace (SP + -224) with (SP + -208 + -16) in * by lia.
        eapply evtA_mono.
        { eapply (ss_alloc_C AL IMG ALWF (CSf nb (bl ++ [ua])) (CSOKf nb (bl ++ [ua]))) with (m0 := m6) (W := []);
            [ | | exact FRA6 | exact ST6 | | | | | | apply munch_refl | apply wmono_refl | exact MI6]; try lia.
          eapply (crange_sub (CSf nb (bl ++ [ua])) lo (SP - lo)); [exact SCS'| lia| lia]. }
        cbn beta. (intros ms1 dd_H; ddestruct dd_H as (m7 & -> & MU7 & WM7 & MI7 & ST7)).
        replace (ret_pc (Z_to_bv 64 0x08701c)) with (Z_to_bv 64 0x08701c) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
        replace (SP + -208 + -16 + 16) with (SP + -208) in * by lia.
        unfold sc_ms_post. deexists 16. fold count j. rewrite <- HSSB. change (2^23) with 8388608. change (2^20) with 1048576.
        split; [reflexivity|].
        split. { eapply munch_trans. { eapply munch_weaken; [| exact MU1z]. unfold sub_fp; cbn [outside]. clear. intros x Hx. lia. }
                 eapply munch_trans. { eapply munch_weaken; [| exact MU5]. unfold sub_fp; cbn [outside]. clear. intros x Hx. lia. }
                 eapply munch_trans. { eapply munch_weaken; [| exact MU6]. unfold sub_fp; cbn [outside]. clear. intros x Hx. lia. }
                 eapply munch_weaken; [| exact MU7]. unfold sub_fp; cbn [outside]. clear. intros x Hx. lia. }
        split. { eapply wmono_trans; [exact WM3|]. eapply wmono_trans; [exact WMz|]. eapply wmono_trans; [exact WM5|]. eapply wmono_trans; [exact WM6| exact WM7]. }
        split; [exact MI7|].
        split. { eapply rw_cells_transport; [exact BX6| exact MU7| exact WM7|]. unfold A_SS in HSSB; cbn [disjoint_from cells_size csize Nat.add]. clear -HSSB JB LOIMG SPL. lia. }
        split. { eapply rw_cells_transport; [exact AX6| exact MU7| exact WM7|]. unfold A_SS; cbn [disjoint_from cells_size csize Nat.add]. clear -LOIMG SPL. lia. }
        split. { eapply zblock_transport; [exact NEW6| clear; lia| exact MU7| exact WM7|]. cbn [disjoint_from]. clear -UA ACE AC LOIMG SPL. lia. }
        exact ST7. }
      (* [comment removed for export] *)
      cbn beta. intros ms8 mo8 PO HK8 MM8 HJ8. apply aevtS_now.
      dexists (Z_to_bv 64 ua), mo8, ms8. rewrite unsigned_lit by lia. change (2^23) with 8388608.
      split; [reflexivity|]. split; [exact PO|]. split; [exact HK8|]. split; [exact HJ8|]. split; [exact CR4|].
      split; [exact AAL|]. split; [exact UA|]. split; [clear -ACE AC; lia|].
      intros x Hx. apply AP. left. exact Hx.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End DepotCfg.

End ARUN_2.
