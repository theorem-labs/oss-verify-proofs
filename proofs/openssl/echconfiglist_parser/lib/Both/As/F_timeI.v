(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Exec CellsX Arr TacX Frame MState Mem Cells.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes LazyFdNodes LazyCgNode. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsanAllocCons.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import CgNode.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsDriverLaws AsSR AsChain FakeStackRep
     AllocWf AllocKit AllocRep AllocRepFacts AllocRepX SecLazy AsDepotInv AsDepotHash ECH_AImg ECH_Iface AsAuxv F_strspn F_time F_timeW
     AS_InstDefs AS_InstLaws1 AS_InstLaws2 AS_InstLaws3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Inst.
  Context {HCEIL : HeapCeil}.
  Variable p : iparams.

  Lemma ECALL_time : fetch_word asegs (Z_to_bv 64 0x56e494) = Some ECALLW.
  Proof. vm_compute. reflexivity. Qed.

  Theorem atime_inst : atime_stmt (KHp p).
  Proof.
    unfold atime_stmt, atime_stmt_at. cbn [as_VIS as_RHEAP as_AKREL as_SR as_MPRES as_rauxv_ok as_St KHp].
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo x LB lo B vf errv.
    intros VIS A0 HP K RAUX AUX HB ST CLO LO ERR MI TP AC ARL VF HVF RAE.
    destruct x as [s d].
    unfold AsSR.VIS in VIS. unfold AsSR.AKREL in K. cbn [i_s i_d cfg_model cfg_ms] in VIS, K. destruct K as [OK IKx].
    destruct (inst_canary_law p (IST s d) LB m HP) as (can & GOTC & CANC & CANR).
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    unfold ATIME_STACK in LO. acb.
    unfold AsSR.SR.
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo _ OK VIS).
    { eapply (atime_front ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo B vf can errv AUX HB VF HVF);
        [exact GOTC| exact CANC| exact CANR| exact ERR| exact TP| exact ST| exact CLO| unfold ATIME_STACK; exact LO| exact MI| exact A0| exact AC]. }
    cbv beta. intros msF1 mo1 OK1 SBM1 HS1 P1.
    destruct P1 as (x1 & x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x28 & x29 & x30 & x31 & m1 & j16 & j8 & jA & jB
                    & VIS1 & FR0 & FRb & FRc & VF1 & GOT1 & CAN1 & ERR1 & MU1 & WM1 & MI1 & ST1 & AC1 & AUX1).
    unfold A_vdso_func, AGOT_SSP_CELL, ACANARY_CELL, ATIME_STACK in FR0, FRb, FRc, VF1, GOT1, CAN1, MU1.
    (* [comment removed for export] *)
    eapply (sr_ecall_MS (a_L s) (a_S s) (a_Zr s) x1 (Z_to_bv 64 (bv_unsigned sp + -2224)) gp tp x5 x6 x7
              (Z_to_bv 64 (bv_unsigned sp + -2192)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp + -2192))
              x12 x13 x14 x15 x16 (Z_to_bv 64 113) s2 s3 (Z_to_bv 64 APAT) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31
              F 0x56e494 fc None m1 msF1 mo1 _ OK1 VIS1 ECALL_time).
    intros msF2 OK2 VIS2 HS2.
    (* [comment removed for export] *)
    eapply (sreach_cg_lazy asegs (a_L s) (a_S s) (a_Zr s) msF2 mo1 _ (bv_unsigned sp + -2192) _ OK2 VIS2).
    { unfold cg_at_node. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      cbn [ms_mem MSsvc]. apply (rw_cells_wr_at asegs _ _ _ 16 FR0). cbn [cells_size csize]. lia. }
    intros bs msF3 mo3 RT L16 OK3 SBM3 VIS3 HS3.
    rewrite sysret_MSsvc, mkR_set_a0, lit_add_lit in VIS3. cbn [ms_mem MSsvc] in VIS3.
    change (Z_to_bv 64 (5694612 + 4)) with (Z_to_bv 64 5694616 : word) in VIS3.
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF3 _ mo3 _ OK3 VIS3).
    { eapply (atime_back x1 x5 x6 x7 x12 x13 x14 x15 x16 x28 x29 x30 x31 sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 ra s0 s1 s4 F fc
                m m1 lo B can errv bs j16 j8 jA jB L16 FR0 FRb FRc VF1 GOT1 CAN1 CANR ERR1 TP MU1 WM1 MI1 ST1 CLO);
        [unfold ATIME_STACK; exact LO| exact AC| exact AUX| exact HB]. }
    cbv beta. intros msF4 mo4 OK4 SBM4 HS4 P4.
    destruct P4 as (u0 & u1 & u2 & tv & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m4
                    & VIS4 & MI4 & ST4 & AC4 & ERR4 & AUX4 & MU4 & WM4 & VF4).
    unfold A_vdso_func, ATIME_STACK in MU4, VF4.
    (* [comment removed for export] *)
    apply sr_done. unfold atime_post.
    exists u0, u1, u2, tv, w1, w2, w3, w4, w5, w6, w7, u3, u4, u5, u6, m4.
    cbn [cfg_ms cfg_model].
    split; [exact VIS4|].
    split. { unfold AsSR.AKREL. cbn [cfg_model i_s]. split; [exact OK4|].
             apply (IK_mat p (IST s d) mo3 mo4); [| exact SBM4]. apply (IK_mat p (IST s d) mo1 mo3); [| exact SBM3].
             apply (IK_mat p (IST s d) mo mo1); [exact IKx| exact SBM1]. }
    split. { eapply nonvm_same_trans; [exact (nonvm_same_mat _ _ SBM1)|].
             eapply nonvm_same_trans; [exact (nonvm_same_mat _ _ SBM3)| exact (nonvm_same_mat _ _ SBM4)]. }
    split; [exact MI4|]. split; [exact ST4|]. split; [exact AC4|]. split; [exact ERR4|]. split; [exact RAUX|]. split; [exact AUX4|].
    split. { eapply (inst_RHEAP_frame p (IST s d) LB m m4); [exact HP| exact MU4| exact WM4|].
             constructor; [left; cbn; lia|]. constructor; [| constructor]. right; left. unfold aimg_client_w. cbn. lia. }
    unfold ATIME_STACK, A_vdso_func.
    split. { eapply munch_weaken; [| exact MU4]. intros xq Hxq. cbn in Hxq |- *. lia. }
    split; [exact WM4| exact VF4].
  Qed.
End Inst.
