(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux SysStep ITree Nodes HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed AKinv AKinvS AKFrame. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AJ HMLib.
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
Ltac2 gd_tbl_AKinvM () : Init.string Init.list := ["Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.BHeap.AKinv.kinv"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.JW"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.true"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.ncov"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_destroyed"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.norep_grant"; "Corelib.Init.Datatypes.list"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.AHeap.AVmLib.covers"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "ARUN_1.scar_site"; "Corelib.Init.Logic.iff"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MSsvc"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.atop_ok"; "LinuxProcessSemantics.LinuxProcessSem.State.alloc_top"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.mmap_norep_args"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.ITree.nret"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.spinningJ"; "LinuxProcessSemantics.LinuxProcessSem.State.errno_ret"; "LinuxProcessSemantics.LinuxProcessSem.State.ENOMEM"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_commit"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_fresh"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_GOT_PAGESZ"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_PAGESZ_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DECORATE"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_LIMIT"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_SEALED2"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_DYING"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DYING"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "ARUN_1.MapWithCallbackS.mwc_postS"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_RAR_MAP"].

Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
Definition scar_site (AL : asan_layout) (CS : Z -> Prop) (K : Model -> Prop) (addr nZ : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AKinvM ()) "(0.P,$1.SpLKh,P,$1.Sp(2.(3.VhAR,O5.O4.R1.)(2.(4.(5.(6.O2.O1.)+7???7000.)(5.+10007???8000.O2.))(2.(5.$7.O1.)(2.Pmo,$1.P,A1.O3.R1.(2.(8.$9.(:.(;.(<.R2.))(=.&40.O2.)(=.&40.O1.))$>.)(2.Px,$?.P,(2.(5.O2.R1.)(10.R1.(6.O2.O1.)))(11.(12.(<.R4.))R2.)A1.R3.(13.O2.O1.R2.)))Pmh,$1.P,A1.R2.R1.(2.(8.$9.(14.(15.(16.(17.&40.)(17.&40.))(18.(<.R2.))(;.(<.R2.)))(=.&40.O2.)(=.&40.O1.))$>.)A1.O3.(19.O2.O1.R2.)))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition hole_site (AL : asan_layout) (CS : Z -> Prop) (K : Model -> Prop) (addr nZ : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AKinvM ()) "(0.P,$1.SpLKh,P,$1.Sp(2.(3.VhAR,O5.O4.R1.)Pmo,$1.P,A1.O3.R1.P,(8.$9.(:.(;.(<.R2.))(=.&40.O2.)(=.&40.O1.))$>.)A1.R4.(13.O2.O1.R3.)))")
(* [comment removed for export] *).


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L24295209809.11L37668873945.10L61927738149.1000000<00K00ZS2lo1n1e1A1BS2lo1n2H02H12H2S2lo1n2H02H12H2". (* [comment removed for export] *)
#[using="Type"] Lemma map_contains_covers : ltac2:(CDefT.buildp (gd_tbl_AKinvM ()) "PX,(1:.(16.(17.&40.)(17.&40.)))Plo,$?.Pn,$?.P,(5.=R2.)P,(5.=R2.)P,(10.(6.R4.R3.)(1;.+2.+40.))P,(8.$9.(:.R6.(=.&40.R5.)(=.&40.R4.))$>.)(1<.R7.R6.(6.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros X lo n H0 H1 H2 MC. unfold map_contains in MC. apply existsb_exists in MC. ddestruct MC as (e & He & E).
  rewrite !u64_lit in E by lia. apply andb_prop in E. destruct E as [A B]. apply Z.leb_le in A. apply Z.leb_le in B.
  exists e. split; [exact He| lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma kinv_mono' : forall AL (CS CS' : Z -> Prop) K, (forall x, CS x -> CS' x) -> kinv AL CS' K -> kinv AL CS K.
Proof.
  intros AL CS CS' K HS KL. split.
  - intros mo HK. exact (ki_halted KL mo HK).
  - intros mo HK. exact (ki_top KL mo HK).
  - intros mo acc HK OK. exact (ki_mat KL mo acc HK (acc_ok_mono AL CS CS' acc HS OK)).
Qed.

#[using="Type"] Lemma scar_site_mono : ltac2:(CDefT.buildp (gd_tbl_AKinvM ()) "PAL,$1=.PCS,P,$?.SpPCS',P,$?.SpPK,P,$1.SpPaddr,$?.PnZ,$?.P,(1>.R6.R4.R3.R2.R1.)P,Px,$?.P,A1.R7.R1.A1.R7.R2.(1>.R8.R7.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  (intros AL CS CS' K addr nZ dd_H; ddestruct dd_H as (Kh & KhL & B1 & B2 & S1 & S2); intros HS). exists Kh. split; [exact (kinv_mono' AL CS CS' Kh HS KhL)|]. split; [exact B1|]. split; [exact B2|]. split; [exact S1| exact S2].
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma scar_site_iff : ltac2:(CDefT.buildp (gd_tbl_AKinvM ()) "PAL,$1=.PCS,P,$?.SpPK,P,$1.SpPK',P,$1.SpPaddr,$?.PnZ,$?.P,(1>.R6.R5.R4.R2.R1.)P,Pmo,$1.(1?.A1.R6.R1.A1.R5.R1.)(1>.R8.R7.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  (intros AL CS K K' addr nZ dd_H; ddestruct dd_H as (Kh & KhL & B1 & B2 & S1 & S2); intros E). exists Kh. split; [exact KhL|]. split; [exact B1|]. split; [exact B2|]. split.
  - intros mo HK. exact (S1 mo (proj2 (E mo) HK)).
  - intros mh HKh. destruct (S2 mh HKh) as [A B]. split; [exact A| exact (proj1 (E _) B)].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)
#[using="Type"] Lemma mo_frame_fixrw_destroyed : forall addr nZ mo, mo_frame mo (fixrw_destroyed addr nZ mo).
Proof. intros. unfold fixrw_destroyed. cbv zeta. apply mo_frame_with_mmap_destroyed. Qed.
#[using="Type"] Lemma mo_frame_norep_grant : forall addr nZ mo, mo_frame mo (norep_grant addr nZ mo).
Proof.
  intros. unfold norep_grant. cbv zeta. eapply mo_frame_trans; [apply mo_frame_with_vmmaps| apply mo_frame_with_mmap_backing].
Qed.

#[using="Type"] Lemma scar_site_KF : forall AL CS K mo0 addr nZ, scar_site AL CS K addr nZ -> scar_site AL CS (KF K mo0) addr nZ.
Proof.
  (intros AL CS K mo0 addr nZ dd_H; ddestruct dd_H as (Kh & KhL & B1 & B2 & S1 & S2)). exists (KF Kh mo0). split; [exact (kinv_KF AL CS Kh mo0 KhL)|]. split; [exact B1|]. split; [exact B2|]. split.
  - intros mo [HK FR]. ddestruct (S1 mo HK) as (A & B & C). split; [exact A|]. split; [exact B|]. split; [exact C|].
    eapply mo_frame_trans; [exact FR| apply mo_frame_fixrw_destroyed].
  - intros mh [HKh FR]. destruct (S2 mh HKh) as [A B]. split; [exact A|]. split; [exact B|].
    eapply mo_frame_trans; [exact FR| apply mo_frame_norep_grant].
Qed.

#[using="Type"] Lemma hole_site_KF : forall AL CS K mo0 addr nZ, hole_site AL CS K addr nZ -> hole_site AL CS (KF K mo0) addr nZ.
Proof.
  (intros AL CS K mo0 addr nZ dd_H; ddestruct dd_H as (Kh & KhL & S1)). exists (KF Kh mo0). split; [exact (kinv_KF AL CS Kh mo0 KhL)|].
  intros mo [HK FR] MC. split; [exact (S1 mo HK MC)|]. eapply mo_frame_trans; [exact FR| apply mo_frame_fixrw_destroyed].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma orS_mmap_norep_hole : ltac2:(CDefT.buildp (gd_tbl_AKinvM ()) "PQ,P,$20.SpPR,(21.&5.(17.&40.))PF,(21.&5.(17.&40.))Ppc,(17.&40.)Pfc,(17.&20.)Prv,(22.(17.&40.))Pm,P,(17.&40.)(22.(17.&8.))Pmo,$1.Paddr,$?.PnZ,$?.Zms,$23.(24.R9.R8.R7.(=.&40.+=>.)R6.R5.R4.(25.$26.))P,(8.(22.(17.&40.))(27.R4.)(28.(17.&40.)))P,(29.VhAR,(2:.(<.R5.)))P,(2;.VhAR,R3.R5.R4.)P,(8.$9.(14.(15.(16.(17.&40.)(17.&40.))(18.(<.R7.))(;.(<.R7.)))(=.&40.R6.)(=.&40.R5.))$>.)P,(4.(2<.$26.R?.(2=.(2>.R5.(2?.(=.&40.R7.)(30.(16.(17.&40.)(1:.(17.&8.))))(30.(16.(17.&40.)(17.&40.)))(31.(16.(17.&40.)(17.&40.))(32.(17.&40.)(17.&40.)(=.&40.R7.)(=.&40.R6.))(30.(16.(17.&40.)(17.&40.))))(30.$33.)(30.(16.(17.&40.)$34.))))(19.R7.R6.R8.)))(35.$26.(2=.(2>.R5.(2?.(=.&40.R7.)(30.(16.(17.&40.)(1:.(17.&8.))))(30.(16.(17.&40.)(17.&40.)))(31.(16.(17.&40.)(17.&40.))(32.(17.&40.)(17.&40.)(=.&40.R7.)(=.&40.R6.))(30.(16.(17.&40.)(17.&40.))))(30.$33.)(30.(16.(17.&40.)$34.))))(19.R7.R6.R8.))))P,(35.$26.(2=.(2>.R6.(2?.(36.$37.)(30.(16.(17.&40.)(1:.(17.&8.))))(30.(16.(17.&40.)(17.&40.)))(30.(16.(17.&40.)(17.&40.)))(30.$33.)(30.(16.(17.&40.)$34.))))R9.))(4.(2<.$26.R11.(2=.R7.R:.))(35.$26.(2=.R7.R:.)))")
(* [comment removed for export] *).
Proof.
  intros Q R F pc fc rv m mo addr nZ ms Hh ATOP HA FR [HOK|HSP] HNO.
  - left. eapply (aevtS_mmap_norep_hole asegs Q); eauto.
  - right. assert (E222 : bv_unsigned (Z_to_bv 64 222) = 222) by (vm_compute; reflexivity).
    eapply (spinningJ_sys asegs) with (x8 := Z_to_bv 64 222); [reflexivity| exact Hh| |].
    + intros eff mo' evs Hs.
      destruct (mmap_norep_inv asegs ms (Z_to_bv 64 222) mo addr nZ eff mo' evs E222 HA ATOP Hs) as [-> OUT].
      split; [reflexivity|]. destruct OUT as [| OCC | _].
      * split; [exact Hh|]. split; [reflexivity| exact HNO].
      * congruence.
      * split; [rewrite halted_norep_grant; exact Hh|]. split; [reflexivity| exact HSP].
    + eapply (mmap_norep_no_unmodeled asegs ms (Z_to_bv 64 222)); eauto.
Qed.

Section MapWithCallbackS.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.

  (* [comment removed for export] *)
  Variables (K Kok : Model -> Prop).
  Hypothesis KL : kinv AL CS K.
  Hypothesis KokL : kinv AL CS Kok.

  Variables (addr size name : Z).
  Let nZ := (size + 4095) / 4096 * 4096.

  (* [comment removed for export] *)
  Hypothesis LEDGER : ltac2:(CDefT.buildp (gd_tbl_AKinvM ()) "Pmo,$1.P,A1.VK,R1.(2.(8.$9.(14.(18.(<.R2.))(=.&40.Vaddr,)(=.&40.VnZ,))$>.)(4.(8.$9.(:.(;.(<.R2.))(=.&40.Vaddr,)(=.&40.VnZ,))$>.)(8.$9.(14.(15.(16.(17.&40.)(17.&40.))(18.(<.R2.))(;.(<.R2.)))(=.&40.Vaddr,)(=.&40.VnZ,))$>.)))")
(* [comment removed for export] *).
  Hypothesis T_commit : ltac2:(CDefT.buildp (gd_tbl_AKinvM ()) "Pmo,$1.P,A1.VK,R1.P,(8.$9.(:.(;.(<.R2.))(=.&40.Vaddr,)(=.&40.VnZ,))$>.)A1.VKok,(38.+32.Vaddr,VnZ,R3.)")
(* [comment removed for export] *).
  Hypothesis T_fresh : ltac2:(CDefT.buildp (gd_tbl_AKinvM ()) "Pmo,$1.P,A1.VK,R1.P,(8.$9.(14.(15.(16.(17.&40.)(17.&40.))(18.(<.R2.))(;.(<.R2.)))(=.&40.Vaddr,)(=.&40.VnZ,))$>.)A1.VKok,(39.+32.Vaddr,VnZ,R3.)")
(* [comment removed for export] *).

  Hypothesis ROOM : forall mo, K mo -> fixrw_grantable 0x32 addr nZ mo.
  (* [comment removed for export] *)
  Hypothesis SCAR : scar_site AL CS K addr nZ.

  (* [comment removed for export] *)
  Definition mwc_postS (ok : bool) (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m0 : mem) : config -> Prop :=
    fun c => exists ms' mo' (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem),
      c = mkCfg ms' mo'
      /\ ms' = MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if ok then addr else 0)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None mm (seg_rom asegs)
      /\ munch [(lo, SP); (addr, addr + nZ)] m0 mm /\ wmono asegs m0 mm /\ mem_inv asegs mm /\ stk asegs mm lo SP
      /\ J mm mo'
      /\ (if ok then Kok mo' /\ rw_cells asegs mm addr [CB (Z.to_nat nZ) (repeat (Z_to_bv 8 0) (Z.to_nat nZ))]
          else K mo').

  Local Ltac2 Set LiaOrc.tbl := fun () => "02I0@L10163305637.133L12737330739.140L13654651853.141L13654982357.123L15272425173.122L16159242360.96 L16342829433.130L16343007577.148L16343007577.166L16344773208.167L16344781844.131L16346877028.129L16357739241.128L16570333557.123L16570397805.141L17125266570.145L17901851861.121L18290309477.95 L18290309604.96 L18928394225.149L18928394225.167L18928473206.85 L18930958230.86 L18938958913.129L20135978148.145L20503951697.128L20514386657.148L20514386657.166L20653459879.128L20653739733.145L20655590071.92 L20668206230.176L20668305040.146L20709756104.128L20763562167.130L20763562167.150L20763562167.168L21130222074.128L21675095703.166L22172207656.119L22174304845.139L22700267513.136L22700267513.165L22700267513.173L22700267513.201L23031571949.139L23033669000.119L2418826082.168 L2419054369.132 L2419054380.131 L29038649379.176L30154055423.140L33411638105.143L33751206853.94 L35821110645.121L36107676821.96 L37669248118.166L38832701421.140L38832701429.120L40788849258.87 L41674788627.134L41689647518.134L41689647581.171L41941576815.148L42150857613.140L42150857667.176L42151020997.146L42152890098.128L42153265536.145L42155085282.92 L42509344912.87 L42509560615.148L42511597162.94 L43410297717.122L45129184312.163L47331153942.128L47341753254.148L47341753254.166L47439662351.130L47439662351.150L47439662351.168L47545421154.94 L47801265973.129L47801265973.149L47801265973.167L49363582006.128L5194284791.136 L52747662605.143L52747662613.125L52760426621.153L52760524367.166L53512949285.129L53512949285.149L53512949285.167L54580387064.131L54684059677.153L54684091951.166L54688272109.142L54688272117.124L5476994423.137 L55777059364.131L55777059364.94 L55777061170.89 L55777068136.167L55779016521.130L55779358569.148L55783357012.129L55895014023.166L57467681890.148L57467681890.166L57473955794.128L57553800561.176L58744438605.142L58744438613.124L58748615101.153L58748647311.166L58852426124.175L59113944898.130L59113944898.150L59113944898.168L59314955108.129L59314955108.149L59314955108.167L60560988749.140L60560988757.120L61641781463.129L61652286311.148L61652286311.149L61652286311.167L61654442929.88 L61654445610.94 L62008757933.143L62008757941.125L62021586415.166L62021682141.153L62211500318.170L63220242529.128L63226945260.129L63230809041.148L63230809041.166L63231024113.130L63233220816.167L63233230492.131L64038322146.169L6437205593.140 L65860310473.123L65860310473.152L65860310473.170L67163524134.130L67165663331.131L945261379.128  L951468275.148  L951468275.166  00000U00V00o01H01a02;02W03303O03k04G04c05?05X06106206K06b07907R07k08=08O08h08i08j08k08l09Q0:60:T0;90;^0;_0<;0<W0=30=40=50=N0=g0>m0@30A90B?0BX0C10CZ0DC0Dl0Dm0ER0F60FM0Ff0G@0G_0H80HQ0Hh0IA0IZ0J30JR0K40KV0L80LZ0M<0MW0N50NT0Nl0OE0P00PM0Pj0QG0Qc0R?0R[0S20ST0T60TX0TY0U50UN0Ug0V@0VY0W20WK0Wd0X@0XY0Y20YK0Yd0Z@0Z\0[20[G0[c0\?0\[0]70]P0]l0^H0^d0^e0_>0_W0`00`I0a30aL0ae0b>0b_0c@0ca0d:0dS0do0eK0eg0fC0f[0g00gI0gb0h;0hT0i90iX0j70jV0k50kT0l30lO0m80m90mc0nM0o70o`10I10J10K10LS3hAR4addr4size2nZ2SP2lo2CE5LOIMG3FRBFS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ1x2C12C2S3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBFS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ1x2C1S3hAR4addr4size2nZ1x2C2S3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZS3hAR4addr4size2nZS3hAR4addr4size2nZ2SP3FRBFFFFS3hAR4addr4size2nZ2SP2A02SZ2CE2NZ3FRBS3hAR4addr4size2nZ2SP2A02SZ2CE2NZ3FRBS3hAR4addr4size2nZ2A02SZ2CE2NZS3hAR4addr4size2nZ2SP2A02SZ2CE2NZ3FRBS3hAR4addr4size2nZ2SP2A02SZ2CE2NZ3FRBFS3hAR4addr4size2nZ2SP3FRB2DMS3hAR4addr4size2nZ2SP3FRB2DMS3hAR4addr4size2nZ2SP3FRB2DMFFS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR2AL4addr4size4name2nZ2SP2lo2SZ2NM5ALWF'4IMG'2NZ3ACB2Ha2Hn3FRB1x1HS3hAR2AL4addr4size4name2nZ2SP2lo2SZ2NM5ALWF'4IMG'2NZ3ACB2Ha2Hn3FRB1x1HS3hAR2AL4addr4size4name2nZ2SP2lo2SZ2NM5ALWF'4IMG'2NZ3ACB2Ha2Hn3FRB1x1HS3hAR2AL4addr4size4name2nZ2SP2lo2SZ2NM5ALWF'4IMG'2NZ3ACB2Ha2Hn3FRB1x1HS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2lo2CE5LOIMG3SPL3FRBS3hAR4addr4size2nZ2SP2lo2CE5LOIMG3SPL3FRBS3hAR4addr4size2nZ2SP2lo2CE5LOIMG3SPL3FRBFS3hAR4addr4size2nZ2SP2A02SZ2CE2NZ3FRBS3hAR4addr4size2nZ2SP2A03FRB1A2cs2H2S3hAR4addr4size2nZ1x2HxS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2A01x2C1S3hAR4addr4size2nZ2SP2CE2Hn3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ1H2H0S3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2CE2Hn3FRBS3hAR4addr4size2nZ2SP2lo5LOIMG3FRBS3hAR4addr4size2nZ2SP2lo5LOIMG3FRBS3hAR4addr4size2nZ2SP2lo5LOIMG3FRBS3hAR4addr4size2nZ2SP2lo5LOIMG3FRBS3hAR4addr4size2nZ2SP2lo5LOIMG3FRBS3hAR4addr4size2nZ2lo5LOIMGS3hAR4addr4size2nZ2A02SZ2CE2NZS3hAR4addr4size2nZ2SP2A02Ha3FRBS3hAR4addr4size2nZ2A02HaS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2lo2SZ2CE5LOIMG2NZ3FRBS3hAR4addr4size2nZ2SP3AAL3FRBS3hAR4addr4size2nZ2SP3AAL3FRBS3hAR4addr4size2nZ2SP3AAL3FRBS3hAR4addr4size2nZ2SP3FRB2DMS3hAR4addr4size2nZ2SP3FRB2DMS3hAR4addr4size2nZ2SP3FRB2DMS3hAR4addr4size2nZ1x2HxS3hAR4addr4size2nZ2SP2SZ2NZ2Hn3FRBS3hAR4addr4size2nZ2SP2SZ2NZ2Hn3FRBS3hAR4addr4size2nZ2SP2SZ2NZ2Hn3FRBFS3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2A03FRBS3hAR4addr4size2nZ2SP2CE3FRBS3hAR4addr4size2nZ3HanS3hAR4addr4size2nZ2CES3hAR4addr4size2nZ2SP2CE3FRBS3hAR4addr4size2nZ2SP2CE3FRBS3hAR4addr4size2nZ2SP2CE3FRBS3hAR4addr4size2nZ2SP2CE3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2CE3FRBS3hAR4addr4size2nZ2SP2CE3FRBS3hAR4addr4size2nZ2SP2CE3FRBFS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2lo2CE5LOIMG3FRB1x2HxS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2SZ2NZ3FRB1ES3hAR4addr4size2nZ2SP2SZ2NZ3FRB1ES3hAR4addr4size2nZ2SP2SZ2NZ3FRB1ES3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2Hn3FRBS3hAR4addr4size2nZ2SP2Hn3FRBS3hAR4addr4size2nZ2SP2Hn3FRBS3hAR4addr4size2nZ2SP2Hn3FRBS3hAR4addr4size2nZ2SZ2NZS3hAR4addr4size2nZ2HnS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP3FRBS3hAR4addr4size2nZ2SP2lo2CE5LOIMG3FRBS3hAR4addr4size2nZ2SP2SZ2NZ3FRBS3hAR4addr4size2nZ2SP2SZ2NZ3FRBS3hAR4addr4size2nZ2SP2SZ2NZ3FRBS3hAR4addr4size2nZ2SP2SZ2NZ3FRBS3hAR4addr4size2nZ2SP2SZ2NZ3FRBS3hAR4addr4size2nZ2SP2SZ2NZ3FRBS3hAR4addr4size2nZ2SP2Hn3FRBS3hAR4addr4size2nZ2SP2lo2CE5LOIMG3SPL3FRBFS3hAR4addr4size2nZ2SP2lo5LOIMG3FRB1A2cs2H2S3hAR4addr4size2nZ2SP2lo5LOIMG3FRB1A2cs2H2S3hAR4addr4size2nZ2SP2lo5LOIMG3FRB1A2cs2H2S3hAR4addr4size2nZ2SP2lo2CE5LOIMG3SPL3FRBS3hAR4addr4size2nZ2SP2lo2CE5LOIMG3SPL3FRBFFF". (* [comment removed for export] *)
  #[using="AL IMG ALWF CSOK KL KokL LEDGER T_commit T_fresh ROOM SCAR"] Lemma map_with_callback_cfgS : ltac2:(CDefT.buildp (gd_tbl_AKinvM ()) "PQ,P,$20.SpPra,(17.&40.)Pgp,(17.&40.)Ptp,(17.&40.)Pt0,(17.&40.)Pt1,(17.&40.)Pt2,(17.&40.)Ps0,(17.&40.)Ps1,(17.&40.)Ps2,(17.&40.)Ps3,(17.&40.)Ps4,(17.&40.)Ps5,(17.&40.)Ps6,(17.&40.)Ps7,(17.&40.)Ps8,(17.&40.)Ps9,(17.&40.)Ps10,(17.&40.)Ps11,(17.&40.)Pt3,(17.&40.)Pt4,(17.&40.)Pt5,(17.&40.)Pt6,(17.&40.)Pa0,(17.&40.)Pa4,(17.&40.)Pa5,(17.&40.)Pa6,(17.&40.)Pa7,(17.&40.)PSP,$?.PF,(21.&5.(17.&40.))Pfc,(17.&20.)Pm,P,(17.&40.)(22.(17.&8.))Pmo,$1.Plo,$?.P,(5.+65?000.Vaddr,)P,(8.$?.(3:.Vaddr,+1000.)=)P,(2.(10.=Vsize,)(5.Vsize,(1;.+2.+28.)))P,(5.(6.Vaddr,VnZ,)(3;.VhAR,))P,(2.(10.=Vname,)(10.Vname,(1;.+2.+2?.)))P,Px,(17.&40.)P,(2.(5.Vaddr,(3<.&40.R1.))(10.(3<.&40.R1.)(6.Vaddr,VnZ,)))(8.$9.(3=.$26.R2.)$3>.)P,(3?.$26.R9.$40.(31.$41.(42.(=.&40.$43.))(30.$41.)))P,(3?.$26.R:.$43.(31.$41.(42.(=.&40.+1000.))(30.$41.)))P,(3?.$26.R;.$44.(31.$41.(42.(=.&40.$45.))(30.$41.)))P,(3?.$26.R<.$46.(31.$41.(47.(=.&8.=))(30.$41.)))P,(3?.$26.R=.$48.(31.$41.(42.(=.&40.=))(30.$41.)))P,(3?.$26.R>.$49.(31.$41.(42.(=.&40.+1.))(30.$41.)))P,(3?.$26.R?.$4:.(31.$41.(42.(=.&40.$4;.))(30.$41.)))P,(3?.$26.R10.$4;.(31.$41.(4<.(=.&40.=))(30.$41.)))P,(4=.$26.R11.R?.R14.)P,(5.(3;.VhAR,)R10.)P,(5.R11.(4>.R16.+190.))P,(5.R17.(1;.+2.+3?.))P,(4?.VCS,R13.(4>.R18.R13.))P,(50.$26.R16.)P,A1.VK,R16.P,(51.R18.R17.)P,Pc',$20.P,(52.$>.R38.R1=.R37.R36.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R1<.R1;.R18.R1:.R1.)(2<.$26.R3:.R2.)P,Pc',$20.P,(52.$3>.R39.R1>.R38.R37.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R1=.R1<.R19.R1;.R1.)(4.(2<.$26.R3;.R2.)(35.$26.R2.))(2<.$26.R3:.(2=.(53.(54.R39.(=.&40.R1>.)R38.R37.R36.R35.R34.R33.R32.R23.(=.&40.Vaddr,)(=.&40.Vsize,)(=.&40.Vname,)R22.R21.R20.R1?.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.)R1=.(=.&40.$55.)R1<.(28.(17.&40.))R1;.(25.$26.))R1:.))")
(* [comment removed for export] *).
  Proof.
    intros Q ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 a4 a5 a6 a7 SP F fc m mo lo
      A0 AAL SZ CE NM NONE GOT PGS GOTF DEC LIM SEAL GOTD DYI ST LOIMG SPL SPH SCS MI HK HJ HS HF.
    pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    ddestruct SCAR as (Kh & KhL & SBND & SJW & SC1 & SC2).
    assert (NZ : size <= nZ < size + 4096 /\ nZ mod 4096 = 0).
    { unfold nZ. pose proof (Z.div_mod (size + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (size + 4095) 4096 ltac:(lia)).
      split; [lia|]. apply Z_mod_mult. }
    pose proof aceil_bounds as ACB.
    assert (Ha : 0 <= addr < 2^64) by lia. assert (Hn : 0 <= nZ < 2^64) by lia. assert (Han : addr + nZ <= 2^64) by lia.
    (* [comment removed for export] *)
    assert (WMABS : forall mx : mem, (forall x : word, addr <= bv_unsigned x < addr + nZ -> mx x = None) ->
                      wmono asegs mx (apply_unmaps mx [(wa addr, Z_to_bv 64 nZ)])).
    { intros mx ABSx x Hx.
      destruct (Z.lt_ge_cases (bv_unsigned x) addr) as [C1|C1].
      { unfold wview in *. rewrite (unmaps_outside mx addr nZ Ha Hn Han x ltac:(lia)). exact Hx. }
      destruct (Z.le_gt_cases (addr + nZ) (bv_unsigned x)) as [C2|C2].
      { unfold wview in *. rewrite (unmaps_outside mx addr nZ Ha Hn Han x ltac:(lia)). exact Hx. }
      exfalso. apply Hx. rewrite (wview_high mx x ltac:(lia)). apply ABSx. lia. }
    assert (UNABS : forall mx : mem, forall x : word, addr <= bv_unsigned x < addr + nZ -> apply_unmaps mx [(wa addr, Z_to_bv 64 nZ)] x = None).
    { intros mx x Hx. rewrite apply_unmaps_spec by lia. unfold in_range.
      replace (addr <=? bv_unsigned x) with true by (symmetry; apply Z.leb_le; lia).
      replace (bv_unsigned x <? addr + nZ) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL CS K _ Q _ mo KL HK); [exact HJ| |].
    { eapply (map_pre AL IMG ALWF CS CSOK); try eassumption; lia. }
    cbn beta. intros ms1 mo1 PRE HK1 MM1 HJ1.
    ddestruct PRE as (x5 & x6 & x7 & x28 & x29 & x30 & x31 & xa6 & mm & fr & -> & MU & WM & MI1 & FRM & FR & ST1).
    cbn [ms_mem MSsvc] in HJ1.
    destruct (LEDGER mo1 HK1) as [RF CASES].
    ddestruct (SC1 mo1 HK1) as (MC1 & NC1 & KH1).
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
    (* [comment removed for export] *)
    assert (TR : forall A cs, ro_cells asegs m A cs -> 0x10000 <= A -> A + Z.of_nat (cells_size cs) <= 0x65f000 -> ro_cells asegs mm A cs).
    { intros A cs H H1 H2. eapply ro_cells_transport; [exact H| exact MU|]. cbn [disjoint_from]. split; [lia| exact I]. }
    pose proof (TR _ _ GOT ltac:(unfold A_GOT_PAGESZ; lia) ltac:(unfold A_GOT_PAGESZ; cbn; lia)) as GOTm.
    pose proof (TR _ _ PGS ltac:(unfold A_PAGESZ_CELL; lia) ltac:(unfold A_PAGESZ_CELL; cbn; lia)) as PGSm.
    pose proof (TR _ _ GOTF ltac:(unfold A_GOT_CFLAGS; lia) ltac:(unfold A_GOT_CFLAGS; cbn; lia)) as GOTFm.
    pose proof (TR _ _ LIM ltac:(unfold A_MMAP_LIMIT; lia) ltac:(unfold A_MMAP_LIMIT; cbn; lia)) as LIMm.
    pose proof (TR _ _ SEAL ltac:(unfold A_GOT_SEALED2; lia) ltac:(unfold A_GOT_SEALED2; cbn; lia)) as SEALm.
    pose proof (TR _ _ GOTD ltac:(unfold A_GOT_DYING; lia) ltac:(unfold A_GOT_DYING; cbn; lia)) as GOTDm.
    pose proof (TR _ _ DYI ltac:(unfold A_DYING; lia) ltac:(unfold A_DYING; cbn; lia)) as DYIm.
    (* [comment removed for export] *)
    assert (SPIN2 : forall (Kx : Model -> Prop) (KxL : kinv AL CS Kx) y5 y6 y7 y28 y29 y30 y31 ya6 (m2 : mem) (mo2 : Model) (r : Z),
               Kx mo2 -> 0 <= r < 2^64 -> r <> addr ->
               ro_cells asegs m2 A_GOT_DYING [C8 (Z_to_bv 64 A_DYING)] -> ro_cells asegs m2 A_DYING [C4 (Z_to_bv 64 0)] ->
               stk asegs m2 lo (SP + -64) -> mem_inv asegs m2 ->
               spinningJ asegs (mkCfg (map_norep_answered r SP gp tp y5 y6 y7 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31 ya6 F fc addr size m2) mo2)).
    { intros Kx KxL y5 y6 y7 y28 y29 y30 y31 ya6 m2 mo2 r HKx R0 RNE G1 G2 ST2 MI2.
      eapply (evtA_spinJ_K asegs AL CS Kx _ _ mo2 KxL HKx).
      { eapply (map_norep_post_spin AL IMG ALWF CS CSOK) with (lo := lo); try eassumption; lia. }
      cbn beta. (intros ms5 mo5 dd_H; ddestruct dd_H as (r' & F' & mm' & ->); intros HK5 _).
      apply spinningJ_here; [reflexivity| vm_compute; reflexivity| exact (ki_halted KxL mo5 HK5)]. }
    lazymatch goal with |- aevtS _ _ (mkCfg ?MS1 _) =>
    (* [comment removed for export] *)
    assert (SUCC : forall mo2, fixrw_outcome 0x32 addr nZ mo1 (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)]) mo2 ->
                     aevtS asegs Q (mkCfg (nret MS1 (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)])) mo2))
    end.
    { intros mo2 OUT.
      assert (K2 : Kok mo2 /\ J (apply_zeros mm [(wa addr, Z_to_bv 64 nZ)]) mo2).
      { inversion OUT; subst.
        - split; [apply T_commit; [exact HK1| assumption]| apply (J_fixrw_commit mm mo1 HJ1 addr nZ); lia].
        - split; [apply T_fresh; [exact HK1| assumption]| apply (J_fixrw_fresh mm mo1 HJ1 addr nZ); [lia| lia| lia| assumption]]. }
      destruct K2 as [K2 J2]. clear OUT.
      rewrite nret_MSsvc, mkR_set_a0, apply_mem_zeros.
      change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
      change (Z_to_bv 64 addr, Z_to_bv 64 nZ) with (wa addr, Z_to_bv 64 nZ).
      pose proof (rw_cells_zeros_other asegs mm addr nZ Ha Hn Han _ _ FR ltac:(cbn; lia)) as FRz.
      pose proof (rw_cells_zeros_other asegs mm addr nZ Ha Hn Han _ _ FRM ltac:(cbn; lia)) as FRMz.
      pose proof (stk_zeros asegs mm addr nZ Ha Hn Han _ _ ST1) as STz.
      pose proof (rw_cells_zeros_new asegs mm addr nZ Ha Hn Han) as NEWz.
      assert (MUz : munch [(lo, SP); (addr, addr + nZ)] m (apply_zeros mm [(wa addr, Z_to_bv 64 nZ)])).
      { eapply (munch_zeros mm addr nZ Ha Hn Han). 2:{ cbn. right. left. lia. }
        eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]; intros; lia. }
      assert (MIz : mem_inv asegs (apply_zeros mm [(wa addr, Z_to_bv 64 nZ)])).
      { eapply (mem_inv_zeros asegs mm addr nZ Ha Hn Han MI1). intros x Hx. apply (NONE x Hx). }
      assert (GOTFz : ro_cells asegs (apply_zeros mm [(wa addr, Z_to_bv 64 nZ)]) A_GOT_CFLAGS [C8 (Z_to_bv 64 A_CFLAGS)]).
      { eapply (ro_cells_zeros_other asegs mm addr nZ Ha Hn Han); [exact GOTFm|]. cbn. unfold A_GOT_CFLAGS. lia. }
      assert (LIMz : ro_cells asegs (apply_zeros mm [(wa addr, Z_to_bv 64 nZ)]) A_MMAP_LIMIT [C8 (Z_to_bv 64 0)]).
      { eapply (ro_cells_zeros_other asegs mm addr nZ Ha Hn Han); [exact LIMm|]. cbn. unfold A_MMAP_LIMIT. lia. }
      pose proof (wmono_zeros asegs mm addr nZ Ha Hn Han _ WM) as WMz.
      set (mz := apply_zeros mm [(wa addr, Z_to_bv 64 nZ)]) in *. clearbody mz.
      eapply (evtA_aevtS_KJ AL CS Kok _ Q _ mo2 KokL K2); [exact J2| |].
      { eapply (map_post_ok AL IMG ALWF CS CSOK) with (m0 := mz); try eassumption; try lia.
        apply munch_refl. apply wmono_refl. }
      cbn beta. intros ms3 mo3 PO HK3 MM3 HJ3.
      ddestruct PO as (y5 & y6 & y7 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y28 & y29 & y30 & y31 & mm3 & -> & MU3 & WM3 & MI3 & ST3).
      apply HS. unfold mwc_postS. deexists 17. split; [reflexivity|]. split; [reflexivity|].
      split. { eapply munch_trans; [exact MUz|]. eapply munch_weaken; [|exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
      split; [eapply wmono_trans; [exact WMz| exact WM3]|].
      split; [exact MI3|]. split; [exact ST3|]. split; [exact HJ3|]. split; [exact HK3|].
      eapply rw_cells_transport; [exact NEWz| exact MU3| exact WM3| cbn [disjoint_from cells_size csize]; rewrite ?Z2Nat.id by lia; split; [lia| exact I]]. }
    eapply (aevtS_mmap_fixrw asegs Q) with (addr := addr) (nZ := nZ) (flags := 0x32).
    { exact (ki_halted KL mo1 HK1). }
    { exact (ki_top KL mo1 HK1). }
    { unfold mmap_fixrw_args, areg, MSsvc. cbn [ms_regs]. simp_regs.
      repeat split; try reflexivity; try lia.
      - fold nZ. destruct NZ as [N1 N2]. rewrite unsigned_lit by lia. unfold page_round_up_Z, page_size.
        pose proof (Z.div_mod nZ 4096 ltac:(lia)) as DM. rewrite N2, Z.add_0_r in DM.
        replace ((nZ + 4096 - 1) / 4096) with (nZ / 4096); [lia|].
        apply Z.div_unique with (r := 4095); lia.
      - intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia.
      - left. reflexivity. }
    { exact RF. }
    { exact CASES. }
    { apply ROOM. exact HK1. }
    { exact SUCC. }
    intros eff mo2 OUT.
    destruct OUT as [e HIn | e HIn MC | MC | FRE].
    - (* [comment removed for export] *)
      right. destruct HIn as [<-|[]].
      rewrite nret_MSsvc, mkR_set_a0, apply_mem_none.
      replace (errno_ret ENOMEM) with (Z_to_bv 64 (2^64 - 12)) by (apply bv_eq; vm_compute; reflexivity).
      change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
      eapply (evtA_spinJ_K asegs AL CS K _ _ mo1 KL HK1).
      { eapply (map_refused_pre AL IMG ALWF CS CSOK) with (m0 := mm); try eassumption; try lia.
        apply munch_refl. apply wmono_refl. }
      cbn beta. intros ms3 mo3 PO HK3 MM3.
      ddestruct PO as (y5 & y6 & y7 & y28 & y29 & y30 & y31 & ya6 & m3 & -> & MU3 & WM3 & MI3 & FRM3 & FRH3 & ST3).
      ddestruct (SC1 mo3 HK3) as (MC3 & _ & _).
      assert (TR3 : forall A cs, ro_cells asegs mm A cs -> 0x10000 <= A -> A + Z.of_nat (cells_size cs) <= 0x65f000 -> ro_cells asegs m3 A cs).
      { intros A cs H H1 H2. eapply ro_cells_transport; [exact H| exact MU3|]. cbn [disjoint_from]. split; [lia| exact I]. }
      eapply (spinningJ_mmap_norep_live asegs) with (addr := addr) (nZ := nZ).
      { exact (ki_halted KL mo3 HK3). }
      { exact (ki_top KL mo3 HK3). }
      { unfold mmap_norep_args, areg, MSsvc. cbn [ms_regs]. simp_regs.
        repeat split; try reflexivity; try lia.
        - fold nZ. destruct NZ as [N1 N2]. rewrite unsigned_lit by lia. unfold page_round_up_Z, page_size.
          pose proof (Z.div_mod nZ 4096 ltac:(lia)) as DM. rewrite N2, Z.add_0_r in DM.
          replace ((nZ + 4096 - 1) / 4096) with (nZ / 4096); [lia|].
          apply Z.div_unique with (r := 4095); lia.
        - intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia. }
      { apply contained_not_free; [rewrite unsigned_lit by lia; lia| rewrite !unsigned_lit by lia; lia| exact MC3]. }
      intros e He.
      rewrite nret_MSsvc, mkR_set_a0, apply_mem_none.
      change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
      assert (RV : exists r, errno_ret e = Z_to_bv 64 r /\ 0 <= r < 2^64 /\ r <> addr).
      { destruct He as [-> | ->]; [exists (2^64 - 12)| exists (2^64 - 17)]; (split; [apply bv_eq; vm_compute; reflexivity| lia]). }
      ddestruct RV as (r & -> & R0 & RNE).
      eapply (SPIN2 K KL); try eassumption.
      + apply TR3; [exact GOTDm| unfold A_GOT_DYING; lia| unfold A_GOT_DYING; cbn; lia].
      + apply TR3; [exact DYIm| unfold A_DYING; lia| unfold A_DYING; cbn; lia].
    - (* [comment removed for export] *)
      destruct HIn as [<-|[]].
      rewrite nret_MSsvc, mkR_set_a0, apply_mem_unmaps.
      replace (errno_ret ENOMEM) with (Z_to_bv 64 (2^64 - 12)) by (apply bv_eq; vm_compute; reflexivity).
      change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
      change (Z_to_bv 64 addr, Z_to_bv 64 nZ) with (wa addr, Z_to_bv 64 nZ).
      (* [comment removed for export] *)
      assert (ABS : forall x : word, addr <= bv_unsigned x < addr + nZ -> mm x = None).
      { intros x Hx. exact (J_absent mm mo1 addr nZ HJ1 ltac:(unfold JF; lia) SBND SJW (map_contains_covers _ addr nZ ltac:(lia) ltac:(lia) ltac:(lia) MC1) NC1 x Hx). }
      pose proof (J_fixrw_destroyed mm mo1 HJ1 addr nZ ltac:(lia) ltac:(lia) ltac:(lia)) as HJu.
      pose proof (rw_cells_unmaps_other asegs mm addr nZ Ha Hn Han _ _ FR ltac:(cbn; lia)) as FRu.
      pose proof (rw_cells_unmaps_other asegs mm addr nZ Ha Hn Han _ _ FRM ltac:(cbn; lia)) as FRMu.
      pose proof (stk_unmaps_other asegs mm addr nZ Ha Hn Han _ _ ST1 ltac:(lia)) as STu.
      assert (MUu : munch [(lo, SP); (addr, addr + nZ)] m (apply_unmaps mm [(wa addr, Z_to_bv 64 nZ)])).
      { eapply (munch_unmaps mm addr nZ Ha Hn Han). 2:{ cbn. right. left. lia. }
        eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]; intros; lia. }
      pose proof (mem_inv_unmaps asegs mm addr nZ Ha Hn Han MI1) as MIu.
      assert (WMu : wmono asegs m (apply_unmaps mm [(wa addr, Z_to_bv 64 nZ)])) by (eapply wmono_trans; [exact WM| exact (WMABS mm ABS)]).
      pose proof (UNABS mm) as ABSu.
      assert (TRu : forall A cs, ro_cells asegs mm A cs -> 0x10000 <= A -> A + Z.of_nat (cells_size cs) <= 0x65f000 ->
                                 ro_cells asegs (apply_unmaps mm [(wa addr, Z_to_bv 64 nZ)]) A cs).
      { intros A cs H H1 H2. eapply (ro_cells_unmaps_other asegs mm addr nZ Ha Hn Han); [exact H|]. lia. }
      pose proof (TRu _ _ GOTm ltac:(unfold A_GOT_PAGESZ; lia) ltac:(unfold A_GOT_PAGESZ; cbn; lia)) as GOTu.
      pose proof (TRu _ _ PGSm ltac:(unfold A_PAGESZ_CELL; lia) ltac:(unfold A_PAGESZ_CELL; cbn; lia)) as PGSu.
      pose proof (TRu _ _ SEALm ltac:(unfold A_GOT_SEALED2; lia) ltac:(unfold A_GOT_SEALED2; cbn; lia)) as SEALu.
      pose proof (TRu _ _ GOTDm ltac:(unfold A_GOT_DYING; lia) ltac:(unfold A_GOT_DYING; cbn; lia)) as GOTDu.
      pose proof (TRu _ _ DYIm ltac:(unfold A_DYING; lia) ltac:(unfold A_DYING; cbn; lia)) as DYIu.
      set (mu := apply_unmaps mm [(wa addr, Z_to_bv 64 nZ)]) in *. clearbody mu.
      eapply (evtA_orS_KJ AL CS Kh _ Q _ _ KhL KH1); [exact HJu| |].
      { eapply (map_refused_pre AL IMG ALWF CS CSOK) with (m0 := mu); try eassumption; try lia.
        apply munch_refl. apply wmono_refl. }
      cbn beta. intros ms3 mo3 PO HK3 MM3 HJ3.
      ddestruct PO as (y5 & y6 & y7 & y28 & y29 & y30 & y31 & ya6 & m3 & -> & MU3 & WM3 & MI3 & FRM3 & FRH3 & ST3).
      cbn [ms_mem MSsvc] in HJ3.
      destruct (SC2 mo3 HK3) as (FR3 & _).
      assert (TR3 : forall A cs, ro_cells asegs mu A cs -> 0x10000 <= A -> A + Z.of_nat (cells_size cs) <= 0x65f000 -> ro_cells asegs m3 A cs).
      { intros A cs H H1 H2. eapply ro_cells_transport; [exact H| exact MU3|]. cbn [disjoint_from]. split; [lia| exact I]. }
      eapply (orS_mmap_norep_hole Q) with (addr := addr) (nZ := nZ).
      { exact (ki_halted KhL mo3 HK3). }
      { exact (ki_top KhL mo3 HK3). }
      { unfold mmap_norep_args, areg, MSsvc. cbn [ms_regs]. simp_regs.
        repeat split; try reflexivity; try lia.
        - fold nZ. destruct NZ as [N1 N2]. rewrite unsigned_lit by lia. unfold page_round_up_Z, page_size.
          pose proof (Z.div_mod nZ 4096 ltac:(lia)) as DM. rewrite N2, Z.add_0_r in DM.
          replace ((nZ + 4096 - 1) / 4096) with (nZ / 4096); [lia|].
          apply Z.div_unique with (r := 4095); lia.
        - intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia. }
      { exact FR3. }
      + (* [comment removed for export] *)
        destruct (SC2 mo3 HK3) as (_ & K4).
        pose proof (J_norep_grant m3 mo3 HJ3 addr nZ ltac:(lia) ltac:(lia) ltac:(lia) FR3) as HJ4.
        rewrite nret_MSsvc, mkR_set_a0, apply_mem_unmaps.
        change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
        change (Z_to_bv 64 addr, Z_to_bv 64 nZ) with (wa addr, Z_to_bv 64 nZ).
        (* [comment removed for export] *)
        pose proof (rw_cells_unmaps_other asegs m3 addr nZ Ha Hn Han _ _ FRM3 ltac:(cbn; lia)) as FRM4.
        pose proof (rw_cells_unmaps_other asegs m3 addr nZ Ha Hn Han _ _ FRH3 ltac:(cbn; lia)) as FRH4.
        pose proof (stk_unmaps_other asegs m3 addr nZ Ha Hn Han _ _ ST3 ltac:(lia)) as ST4.
        assert (MU4 : munch [(lo, SP); (addr, addr + nZ)] m (apply_unmaps m3 [(wa addr, Z_to_bv 64 nZ)])).
        { eapply (munch_unmaps m3 addr nZ Ha Hn Han). 2:{ cbn. right. left. lia. }
          eapply munch_trans; [exact MUu|]. eapply munch_weaken; [|exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
        pose proof (mem_inv_unmaps asegs m3 addr nZ Ha Hn Han MI3) as MI4.
        assert (ABS3 : forall x : word, addr <= bv_unsigned x < addr + nZ -> m3 x = None).
        { intros x Hx. rewrite (MU3 x); [apply ABSu; exact Hx| cbn [outside]; split; [lia| exact I]]. }
        assert (WM4 : wmono asegs m (apply_unmaps m3 [(wa addr, Z_to_bv 64 nZ)])).
        { eapply wmono_trans; [exact WMu|]. eapply wmono_trans; [exact WM3| exact (WMABS m3 ABS3)]. }
        set (m4 := apply_unmaps m3 [(wa addr, Z_to_bv 64 nZ)]) in *. clearbody m4.
        eapply (evtA_orS_KJ AL CS K _ Q _ _ KL K4); [exact HJ4| |].
        { eapply (map_norep_post_ok AL IMG ALWF CS CSOK) with (m0 := m4); try eassumption; try lia.
          apply munch_refl. apply wmono_refl. }
        cbn beta. intros ms5 mo5 PO HK5 MM5 HJ5.
        ddestruct PO as (z5 & z6 & z7 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z28 & z29 & z30 & z31 & mm5 & -> & MU5 & WM5 & MI5 & ST5).
        apply HF. unfold mwc_postS. deexists 17. split; [reflexivity|]. split; [reflexivity|].
        split. { eapply munch_trans; [exact MU4|]. eapply munch_weaken; [|exact MU5]. unfold sub_fp; cbn [outside]; intros; lia. }
        split; [eapply wmono_trans; [exact WM4| exact WM5]|].
        split; [exact MI5|]. split; [exact ST5|]. split; [exact HJ5| exact HK5].
      + (* [comment removed for export] *)
        rewrite nret_MSsvc, mkR_set_a0, apply_mem_none.
        replace (errno_ret ENOMEM) with (Z_to_bv 64 (2^64 - 12)) by (apply bv_eq; vm_compute; reflexivity).
        change (Z_to_bv 64 A_MMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b260).
        eapply (SPIN2 Kh KhL); try eassumption; try lia.
        * apply TR3; [exact GOTDu| unfold A_GOT_DYING; lia| unfold A_GOT_DYING; cbn; lia].
        * apply TR3; [exact DYIu| unfold A_DYING; lia| unfold A_DYING; cbn; lia].
    - (* [comment removed for export] *) left. apply SUCC. apply FO_commit. exact MC.
    - (* [comment removed for export] *) left. apply SUCC. apply FO_fresh. exact FRE.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End MapWithCallbackS.

End ARUN_1.
