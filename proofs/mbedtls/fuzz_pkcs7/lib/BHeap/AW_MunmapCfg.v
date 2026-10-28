(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux SysStep ITree Nodes CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed AW_Munmap AKinv AJ AKinvS.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AW_MunmapCfg () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.lt"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.None"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.pow"; "ARUN_1.wmono_out"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_unmaps"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_LIMIT"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "ARUN_1.UnmapOrDieS.uod_post"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Munmap.A_UNMAP_OR_DIE"].

Section ARUN_1. Context {hAR : arun}.
Definition wmono_out (a n : Z) (m m' : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MunmapCfg ()) "Px,(0.&40.)P,(1.(2.(3.&40.R1.)O4.)(4.(5.O4.O3.)(3.&40.R1.)))P,(6.(7.(8.(0.&8.))(9.$:.O2.R2.)(;.(0.&8.))))(6.(7.(8.(0.&8.))(9.$:.O1.R3.)(;.(0.&8.))))")
(* [comment removed for export] *).

#[using="Type"] Lemma wmono_out_of_wmono : forall a n m m', wmono asegs m m' -> wmono_out a n m m'.
Proof. intros a n m m' H x _ Hx. apply H. exact Hx. Qed.

#[using="Type"] Lemma wmono_out_trans : forall a n m1 m2 m3, wmono_out a n m1 m2 -> wmono_out a n m2 m3 -> wmono_out a n m1 m3.
Proof. intros a n m1 m2 m3 H1 H2 x Hx H. apply H2; [exact Hx|]. apply H1; [exact Hx| exact H]. Qed.

#[using="Type"] Lemma wmono_out_unmaps : ltac2:(CDefT.buildp (gd_tbl_AW_MunmapCfg ()) "Pm,P,(0.&40.)(8.(0.&8.))Pa,$<.Pn,$<.P,(=.(4.=R2.)(2.R2.(>.+2.+40.)))P,(=.(4.=R2.)(2.R2.(>.+2.+40.)))P,(4.(5.R4.R3.)(>.+2.+40.))(?.R5.R4.R6.(10.R6.(11.(12.(0.&40.)(0.&40.))(13.(0.&40.)(0.&40.)(14.R5.)(15.&40.R4.))(16.(12.(0.&40.)(0.&40.))))))")
(* [comment removed for export] *).
Proof.
  intros m a n Ha Hn Han x Hx H. unfold wview in *. rewrite (unmaps_outside m a n Ha Hn Han x Hx). exact H.
Qed.

#[using="Type"] Lemma wr_at_transport_out : ltac2:(CDefT.buildp (gd_tbl_AW_MunmapCfg ()) "Pa,$<.Pn,$<.Pm,P,(0.&40.)(8.(0.&8.))Pm',P,(0.&40.)(8.(0.&8.))PA,$<.Pk,$<.P,(17.$:.R4.R2.R1.)P,(?.R7.R6.R5.R4.)P,(1.(4.(5.R4.R3.)R8.)(4.(5.R8.R7.)R4.))(17.$:.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  (intros a n m m' A k dd_H; ddestruct dd_H as (H0 & H1 & H); intros WM Hd). split; [lia|]. split; [lia|]. intros i Hi.
  apply WM; [| apply H; exact Hi]. rewrite wa_unsigned by lia. lia.
Qed.

#[using="Type"] Lemma rw_cells_transport_out : ltac2:(CDefT.buildp (gd_tbl_AW_MunmapCfg ()) "PW,(18.$19.)Pa,$<.Pn,$<.Pm,P,(0.&40.)(8.(0.&8.))Pm',P,(0.&40.)(8.(0.&8.))PA,$<.Pcs,(18.$1:.)P,(1;.$:.R4.R2.R1.)P,(1<.R8.R5.R4.)P,(?.R8.R7.R6.R5.)P,(1=.R:.R5.(1>.(1?.R4.)))P,(1.(4.(5.R6.(1>.(1?.R5.)))R:.)(4.(5.R:.R9.)R6.))(1;.$:.R8.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros W a n m m' A cs [[Hwf Hb] Hw] MU WM Hd Ho. split; [split; [exact Hwf|]|].
  - eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact Hd.
  - eapply wr_at_transport_out; eauto.
Qed.

#[using="Type"] Lemma u64arr_transport_out : ltac2:(CDefT.buildp (gd_tbl_AW_MunmapCfg ()) "PW,(18.$19.)Pa,$<.Pn,$<.Pm,P,(0.&40.)(8.(0.&8.))Pm',P,(0.&40.)(8.(0.&8.))PA,$<.Pws,(18.(0.&40.))P,(20.$:.R4.R2.R1.)P,(1<.R8.R5.R4.)P,(?.R8.R7.R6.R5.)P,(1=.R:.R5.(21.+8.(1>.(22.(0.&40.)R4.))))P,(1.(4.(5.R6.(21.+8.(1>.(22.(0.&40.)R5.))))R:.)(4.(5.R:.R9.)R6.))(20.$:.R8.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros W a n m m' A ws [Hb Hw] MU WM Hd Ho. split.
  - eapply bytes_at_transport; eauto. rewrite u64s_length, Nat2Z.inj_mul. exact Hd.
  - eapply wr_at_transport_out; eauto.
Qed.

Section UnmapOrDieS.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  (* [comment removed for export] *)
  Variables (addr size : Z).
  Let nZ := page_round_up_Z size.
  Variables (K Kd : Model -> Prop).
  Hypothesis KL : kinv AL CS K.
  (* [comment removed for export] *)
  Variable CS' : Z -> Prop.
  Hypothesis CSOK' : cs_ok AL CS'.
  Hypothesis KdL : kinv AL CS' Kd.
  Hypothesis HAS : forall mo, K mo -> map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) = true.
  Hypothesis T_unmap : forall mo, K mo -> Kd (munmap_model addr nZ mo).

  Definition uod_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m0 : mem) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MunmapCfg ()) "Lc,$23.(24.$25.Lms',$25.(24.$26.Lmo',$26.(24.(0.&40.)Lt0,(0.&40.)(24.(0.&40.)Lt1,(0.&40.)(24.(0.&40.)Lt2,(0.&40.)(24.(0.&40.)La0,(0.&40.)(24.(0.&40.)La1,(0.&40.)(24.(0.&40.)La2,(0.&40.)(24.(0.&40.)La3,(0.&40.)(24.(0.&40.)La4,(0.&40.)(24.(0.&40.)La5,(0.&40.)(24.(0.&40.)La6,(0.&40.)(24.(0.&40.)La7,(0.&40.)(24.(0.&40.)Lt3,(0.&40.)(24.(0.&40.)Lt4,(0.&40.)(24.(0.&40.)Lt5,(0.&40.)(24.(0.&40.)Lt6,(0.&40.)(24.P,(0.&40.)(8.(0.&8.))Lmm,P,(0.&40.)(8.(0.&8.))(=.(7.$23.R13.(27.R12.R11.))(=.(7.$25.R12.(28.(29.O14.(15.&40.O13.)O12.O11.R10.R?.R>.O10.O?.R=.R<.R;.R:.R9.R8.R7.R6.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.R5.R4.R3.R2.)O4.(2:.O14.)O3.(;.(0.&40.))R1.(2;.$:.)))(=.(1<.(11.(12.$<.$<.)(13.$<.$<.O2.O13.)(11.(12.$<.$<.)(13.$<.$<.Vaddr,(5.Vaddr,VnZ,))(16.(12.$<.$<.))))O1.R1.)(=.(?.Vaddr,VnZ,O1.R1.)(=.(2<.$:.R1.)(=.(2=.$:.R1.O2.O13.)(=.Px,(0.&40.)P,(=.(4.Vaddr,(3.&40.R1.))(2.(3.&40.R1.)(5.Vaddr,VnZ,)))(7.(8.(0.&8.))A1.R3.R2.(;.(0.&8.)))(=.A1.VKd,R11.(2>.R1.R11.)))))))))))))))))))))))))))")
(* [comment removed for export] *).

  #[using="AL IMG ALWF CSOK KL CSOK' KdL HAS T_unmap"] Lemma unmap_or_die_cfgS : ltac2:(CDefT.buildp (gd_tbl_AW_MunmapCfg ()) "PQ,P,$23.SpPra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)PSP,$<.Praw,$<.PF,(2?.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(8.(0.&8.))Pmo,$26.Plo,$<.P,(4.+65?000.Vaddr,)P,(7.$<.(30.Vaddr,+1000.)=)P,(2.=Vsize,)P,(4.(5.Vaddr,VnZ,)(31.VhAR,))P,(=.(4.=R:.)(2.R:.+2.))P,(32.$:.R8.$33.(11.$1:.(34.(15.&40.$35.))(16.$1:.)))P,(32.$:.R9.$36.(11.$1:.(34.(15.&40.=))(16.$1:.)))P,(2=.$:.R:.R8.R>.)P,(4.(31.VhAR,)R9.)P,(4.R:.(37.R10.+30.))P,(4.R11.(>.+2.+3?.))P,(38.VCS,R<.(37.R12.R<.))P,(38.VCS',R=.(37.R13.R=.))P,(2<.$:.R10.)P,A1.VK,R10.P,(2>.R12.R11.)P,Pc',$23.P,(39.R33.R18.R32.R31.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R16.R15.R12.R14.R1.)(3:.$:.R35.R2.)(3:.$:.R34.(27.(28.(29.R33.(15.&40.R18.)R32.R31.R30.R2?.R2>.R2=.R2<.(15.&40.Vaddr,)(15.&40.Vsize,)(15.&40.R17.)R1=.R1<.R1;.R1:.R19.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R16.(15.&40.$3;.)R15.(;.(0.&40.))R14.(2;.$:.))R13.))")
(* [comment removed for export] *).
  Proof.
    intros Q ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a3 a4 a5 a6 a7 SP raw F fc m mo lo
      A0 AAL SZ CE RW GOTF LIM ST LOIMG SPL SPH SCS SCS' MI HK HJ HS.
    pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    assert (NZ : size <= nZ < size + 4096 /\ nZ mod 4096 = 0).
    { unfold nZ, page_round_up_Z, page_size. pose proof (Z.div_mod (size + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (size + 4096 - 1) 4096 ltac:(lia)).
      split; [lia|]. apply Z_mod_mult. }
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL CS K _ Q _ mo KL HK); [exact HJ| |].
    { eapply (munmap_pre AL IMG ALWF CS CSOK); try eassumption; try lia. }
    cbn beta. intros ms1 mo1 PRE HK1 MM1 HJ1.
    ddestruct PRE as (x5 & x6 & x7 & x28 & x29 & x30 & x31 & xa2 & xa3 & xa4 & xa5 & xa6 & mm & fr & -> & MU & WM & MI1 & FR & ST1).
    (* [comment removed for export] *)
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
    assert (Ha : 0 <= addr < 2^64) by lia. assert (Hn : 0 <= nZ < 2^64) by lia. assert (Han : addr + nZ <= 2^64) by lia.
    eapply (aevtS_munmap asegs Q) with (addr := addr) (nZ := nZ).
    { exact (ki_halted KL mo1 HK1). }
    { unfold munmap_args, areg, MSsvc. cbn [ms_regs]. simp_regs.
      pose proof aceil_bounds as AC.
      repeat split; try reflexivity; try lia.
      - rewrite unsigned_lit by lia. reflexivity.
      - intros E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia. }
    { exact (HAS mo1 HK1). }
    (* [comment removed for export] *)
    rewrite nret_MSsvc, mkR_set_a0, apply_mem_unmaps.
    change (Z_to_bv 64 A_MUNMAP_ECALL + Z_to_bv 64 4)%bv with (Z_to_bv 64 0x7b26c).
    change (Z_to_bv 64 addr, Z_to_bv 64 nZ) with (wa addr, Z_to_bv 64 nZ).
    pose proof (rw_cells_unmaps_other asegs mm addr nZ Ha Hn Han _ _ FR ltac:(cbn; lia)) as FRu.
    pose proof (stk_unmaps_other asegs mm addr nZ Ha Hn Han _ _ ST1 ltac:(lia)) as STu.
    assert (MUu : munch [(lo, SP); (addr, addr + nZ)] m (apply_unmaps mm [(wa addr, Z_to_bv 64 nZ)])).
    { eapply (munch_unmaps mm addr nZ Ha Hn Han). 2:{ cbn. right. left. lia. }
      eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]; intros; lia. }
    pose proof (mem_inv_unmaps asegs mm addr nZ Ha Hn Han MI1) as MIu.
    assert (GOTFu : ro_cells asegs (apply_unmaps mm [(wa addr, Z_to_bv 64 nZ)]) A_GOT_CFLAGS [C8 (Z_to_bv 64 A_CFLAGS)]).
    { eapply (ro_cells_unmaps_other asegs mm addr nZ Ha Hn Han). 2:{ cbn. unfold A_GOT_CFLAGS. lia. }
      eapply ro_cells_transport; [exact GOTF| exact MU| cbn [disjoint_from cells_size csize]; unfold A_GOT_CFLAGS; split; [lia| exact I]]. }
    assert (LIMu : ro_cells asegs (apply_unmaps mm [(wa addr, Z_to_bv 64 nZ)]) A_MMAP_LIMIT [C8 (Z_to_bv 64 0)]).
    { eapply (ro_cells_unmaps_other asegs mm addr nZ Ha Hn Han). 2:{ cbn. unfold A_MMAP_LIMIT. lia. }
      eapply ro_cells_transport; [exact LIM| exact MU| cbn [disjoint_from cells_size csize]; unfold A_MMAP_LIMIT; split; [lia| exact I]]. }
    assert (NONEu : forall x : word, addr <= bv_unsigned x < addr + nZ -> apply_unmaps mm [(wa addr, Z_to_bv 64 nZ)] x = None).
    { intros x Hx. rewrite apply_unmaps_spec by assumption. unfold in_range.
      destruct (Z.leb_spec0 addr (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (addr + nZ)); cbn [andb]; try reflexivity; lia. }
    pose proof (wmono_out_unmaps mm addr nZ Ha Hn Han) as WMu.
    pose proof (J_munmap mm mo1 addr nZ HJ1 ltac:(clear - Ha; lia) ltac:(clear - NZ SZ; lia) ltac:(pose proof aceil_bounds as ACB0; clear - CE ACB0; lia) (HAS mo1 HK1)) as HJu.
    set (mu := apply_unmaps mm [(wa addr, Z_to_bv 64 nZ)]) in *. clearbody mu.
    eapply (evtA_aevtS_KJ AL CS' Kd _ Q _ (munmap_model addr nZ mo1) KdL (T_unmap mo1 HK1)); [exact HJu| |].
    { eapply (munmap_post_ok AL IMG ALWF CS' CSOK') with (m0 := mu); try eassumption; try lia.
      apply munch_refl. apply wmono_refl. }
    cbn beta. intros ms3 mo3 PO HK3 MM3 HJ3.
    ddestruct PO as (y5 & y6 & y7 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y28 & y29 & y30 & y31 & mm3 & -> & MU3 & WM3 & MI3 & ST3).
    apply HS. unfold uod_post. deexists 18. split; [reflexivity|]. split; [reflexivity|].
    split. { eapply munch_trans; [exact MUu|]. eapply munch_weaken; [|exact MU3]. unfold sub_fp; cbn [outside]; intros; lia. }
    split. { eapply wmono_out_trans; [apply wmono_out_of_wmono; exact WM|]. eapply wmono_out_trans; [exact WMu| apply wmono_out_of_wmono; exact WM3]. }
    split; [exact MI3|]. split; [exact ST3|]. split; [| split; [exact HK3| exact HJ3]].
    intros x Hx. rewrite (MU3 x); [apply NONEu; exact Hx|]. cbn. lia.
  Qed.
End UnmapOrDieS.

End ARUN_1.
