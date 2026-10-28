(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame Mem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsStack0 AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AKit ECH_AsKit ECH_AC7_kit ECH_ALibMF ECH_ALibOK
  ECH_AC1_free ECH_AC6_buf ECH_AC7_new ECH_AC7_newmembuf ECH_AC7_free ECH_AC7_biofreeint.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.


Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis CFX : cfreeex_stmt H.

  Lemma MEMBIO_frame_disj7 : forall LB m m' a R W,
    MEMBIO H LB m a R -> munch W m m' -> wmono asegs m m' ->
    disjoint_from W a BIO_SIZE -> disjoint_from W (mb_bb R) BIOBUFMEM_SIZE -> disjoint_from W (mb_bm R) BUFMEM_SIZE -> disjoint_from W (mb_rp R) BUFMEM_SIZE ->
    MEMBIO H LB m' a R.
  Proof.
    intros LB m m' a R W MB MU WM D1 D2 D3 D4. destruct MB as (C1 & C2 & C3 & C4 & REST).
    split; [| split; [| split; [| split; [| exact REST]]]]; (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [cells_size csize buf_cells bio_cells length Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ]; assumption]).
  Qed.

  Local Ltac mpacc MPA0 MP := let T := fresh "MPX" in pose proof (ah_mpres_trans H HH _ _ _ MPA0 MP) as T; clear MPA0 MP; rename T into MPA0.

  Lemma abiofree_spec : biofree_mem_stmt H.
  Proof.
    unfold biofree_mem_stmt. intros until CH.
    intros VIS A0 ST0 MB APART SHD CPH HP KREL AUX SPB SPA ST CEIL LO ERR MI TP AC MF IM GM METH RL RFS LFB CHN CHS PF HAL RAE.
    unfold BIOFREE_STACK, FR_BIO_free in LO.
    assert (BFS0 : 0 <= BIOFREEINT_STACK).
    { unfold BIOFREEINT_STACK, MEMFREE_STACK, BUFFREE_STACK, CFREE_STACK, CFREEEX_STACK, AFREE_STACK, FR_BIO_free_int, FR_mem_free, FR_mem_buf_free, FR_BUF_MEM_free,
        GETGLOBAL_READY_STACK, NEWEX_INNER, GETDEFCTX_STACK, FR_CRYPTO_free_ex_data, FR_ossl_lib_ctx_get_ex_data_global, FR_get_default_context, AFS_STACK. lia. }
    remember BIOFREEINT_STACK as BST eqn:EBS.
    acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof MB as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & BR1 & BR2 & BR3 & BR4 & _).
    pose proof BR1 as (_ & _ & _ & AH & ACE & _ & AAP). pose proof BR2 as (_ & _ & _ & BBH & BBCE & _). pose proof BR3 as (_ & _ & _ & BMH & BMCE & _). pose proof BR4 as (_ & _ & _ & RPH & RPCE & _).
    unfold AIMG_TOP, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in AH, ACE, BBH, BBCE, BMH, BMCE, RPH, RPCE.
    pose proof (stack0_bounds _ _ _ ST0) as [S0LO S0HI]. unfold AAPP_HI in S0HI.
    assert (EAB : blk_addr (cx_exlock x) + 40 <= aceil).
    { cbn [CTXPH] in CPH. destruct CPH as [_ [(EXI & EXSZ & _ & _) _]]. pose proof (ah_blocks H HH _ _ _ _ HP EXI) as (_ & _ & _ & _ & ECE & _).
      rewrite EXSZ in ECE. unfold MUTEX_SIZE in ECE. exact ECE. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply afr_segA with (lo := lo); [exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MPA (m1 & j0 & jv & VIS1 & MU1 & WM1 & MI1 & ST1 & FRj & RBC1 & FRhi).
    assert (CW1 : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (LW1 : Forall (win_lib_ok LB) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW1]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW1]).
    assert (AC1 : ACONST m1) by (eapply ACONST_stack_frame; [exact AC| exact MU1| exact WM1| lia]).
    assert (ERR1 : rw_cells asegs m1 (errno_addr tp) [C4 errv]) by (subst tp; rewrite unsigned_lit in * by (unfold ATP; lia); eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (MF1 : MEMFLAG m1 1) by (eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (RL1 : arelro_lib m1) by (eapply arelro_across7; [exact RL| exact MU1| constructor; [cbn; lia| constructor]]).
    assert (RFS1 : as_RFS H LF m1) by (eapply (RFS_across_wins H HH); [exact RFS| exact MU1| exact WM1| constructor; [left; cbn; lia| constructor]]).
    assert (CPH1 : CTXPH LB m1 (CtxReady x)) by (eapply CTXPH_frame; [exact CPH| eapply (magree_lib_munch H HH); [exact HP| auto| exact MU1| exact WM1| exact LW1]]).
    assert (MB1 : MEMBIO H LB m1 a R) by (eapply MEMBIO_frame_disj7; [exact MB| exact MU1| exact WM1| ..]; unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE; cbn; lia).
    assert (SHD1 : MEMBIO_shad m1 a R).
    { eapply MEMBIO_shad_across2; [exact MB| exact SHD| exact MU1| exact WM1|]. constructor; [cbn; unfold AHI_LO; lia| constructor]. }
    assert (ST01 : stack0 m1 lo (bv_unsigned sp)) by (eapply stack0_transport; [exact ST0| exact MU1| exact WM1| constructor; [apply stack0_ok_app; cbn; unfold AHI_LO; lia| constructor]]).
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. constructor; [left; cbn; lia| constructor]. }
    assert (CHN1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SPA| lia| lia|]. replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia. rewrite !Z_to_bv_bv_unsigned. exact FRhi. }
    (* [comment removed for export] *)
    pose proof (abiofreeint_mem_spec H HH CFX) as BFI. unfold biofreeint_mem_stmt in BFI.
    eapply (ah_seq H HH).
    { eapply BFI with (lo := lo) (B := B) (LB := LB) (s := s) (x := x) (a := a) (rbp := bv_unsigned sp + -20) (shi := bv_unsigned sp) (R := R) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS1| exact A0| reflexivity| exact RBC1| ..]; rewrite ?unsigned_lit by (unfold ABF_RET, R_BIO_free_BIO_free_int; clear - SPR LO LO0 BFS0; lia).
      all: match goal with |- ?G => first [ lazymatch goal with
           | |- stack0 _ _ _ => exact ST01
           | |- MEMBIO _ _ _ _ _ => exact MB1
           | |- MEMBIO_apart _ _ => exact APART
           | |- MEMBIO_shad _ _ _ => exact SHD1
           | |- CTXPH _ _ _ => exact CPH1
           | |- as_RHEAP _ _ _ _ => exact HP1
           | |- as_AKREL _ _ _ => exact KREL1
           | |- as_rauxv_ok _ _ _ => exact AUX1
           | |- stk _ _ _ _ => exact ST1
           | |- rw_cells _ _ _ [C4 _] => exact ERR1
           | |- mem_inv _ _ => exact MI1
           | |- _ = Z_to_bv 64 ATP => exact TP
           | |- _ mod 16 = 0 => replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia; rewrite Zminus_mod, SPA; reflexivity
           | |- _ mod 4 = 0 => clear - SPA; lia
           | |- ACONST _ => exact AC1
           | |- MEMFLAG _ _ => exact MF1
           | |- IMPL_mem _ => exact IM1
           | |- GOT_mem _ => exact GM1
           | |- METH_mem _ => exact (METH_of_relro _ RL1)
           | |- arelro_lib _ => exact RL1
           | |- as_RFS _ _ _ => exact RFS1
           | |- (_ < AFS_MAXLIVE)%nat => exact LFB
           | |- as_chain _ _ _ _ => exact CHN1
           | |- forall fp' ra', In _ _ -> _ + 16 <= fp' => intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]
           | |- forall fp' ra', In _ _ -> _ \/ _ => intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]
           | |- pf_ok _ _ _ _ => eapply pf_ok_call; [exact PF|]; unfold PF_biofree, ABF_RET; intros q Hq; exact Hq
           | |- _ <= as_AL _ _ => exact HAL
           | |- _ mod 2 = 0 => reflexivity
           | |- _ => first [exact CEIL | clear - SPR SPB LO LO0 BFS0 CEIL EBS S0HI; lia]
           end | idtac "BFI-FAIL:" G; fail ] end. }
    clear BFI. intros [msF2 mo2] PO. unfold biofreeint_mem_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & s2' & LBr & XS &
                    VIS2 & MP2 & KREL2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & HEAP2 & PERM & MF2 & IM2 & GM2 & METH2 & RL2 & CPH2 & RB2 & ST02 & FXS & RFS2 & XP2 & AL2). mpacc MPA MP2.
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia.
    assert (FRhi2 : rw_cells asegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact FRhi| left; cbn; lia|].
      constructor; [cbn; lia|]. unfold mutex_foot. constructor; [| eapply Forall_impl; [| exact FXS]; intros iv P; pose proof (fs_scratch_below_ceil H HH _ _ _ RFS2 P); cbn; lia].
      cbn. lia. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply afr_segZ with (lo := lo); [exact FRhi2| exact ST2| exact CEIL| lia| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 VIS3. mpacc MPA MP3.
    apply (ah_done H HH). unfold biofree_mem_post. cbn [cfg_ms cfg_model].
    do 14 eexists. exists m2, errv2, s2', LBr, XS.
    split; [exact VIS3|]. split; [exact MPA|]. split; [exact KREL3|]. split; [exact MI2|]. split; [exact AC2|].
    split. { pose proof (stk_release asegs m2 lo _ _ ST2 (proj1 (rw_cells_app asegs _ _ _ _) (conj _ _))) as K || idtac.
             (* [comment removed for export] *)
             assert (FRj2 : rw_cells asegs m2 (bv_unsigned sp + -32) [CB 12 j0]).
             { eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2); [exact FRj| left; cbn; lia|].
               constructor; [cbn; lia|]. unfold mutex_foot. constructor; [| eapply Forall_impl; [| exact FXS]; intros iv P; pose proof (fs_scratch_below_ceil H HH _ _ _ RFS2 P); cbn; lia].
               cbn. lia. }
             pose proof (stk_release asegs m2 lo _ _ ST2 FRj2 ltac:(lia)) as K1. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in K1.
             pose proof (stk_release asegs m2 lo _ _ ltac:(lazymatch type of K1 with stk _ _ _ ?h => replace h with (bv_unsigned sp + -20) in K1 by (cbn; lia) end; exact K1) RB2 ltac:(lia)) as K2.
             pose proof (stk_release asegs m2 lo _ _ ltac:(lazymatch type of K2 with stk _ _ _ ?h => replace h with (bv_unsigned sp + -16) in K2 by (cbn; lia) end; exact K2) FRhi2 ltac:(lia)) as K3.
             lazymatch type of K3 with stk _ _ _ ?h => replace h with (bv_unsigned sp) in K3 by (cbn; lia) end. exact K3. }
    split; [exact ERR2|]. split; [exact AUX2|]. split; [exact HEAP2|]. split; [exact PERM|].
    split; [exact MF2|]. split; [exact IM2|]. split; [exact GM2|]. split; [exact METH2|]. split; [exact RL2|]. split; [exact CPH2|].
    split; [exact ST02|]. split; [exact FXS|]. split; [exact RFS2|].
    split.
    { eapply xpres_trans.
      { eapply (xpres_of_munch H _ LBr _ _ _ m2 m m1); [exact HH| exact HEAP2| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
      (* [comment removed for export] *)
      intros q Hq [HC HX]. apply XP2; [exact Hq|]. split.
      - eapply aclient_addr_weaken; [exact HC| lia| intros b Hb; exact Hb].
      - cbn. intros [K|K]; [| exact (HX K)]. destruct (aclient_cases H HH _ _ _ _ q HEAP2 HC Hq); lia. }
    exact AL2.
  Qed.
End W.
