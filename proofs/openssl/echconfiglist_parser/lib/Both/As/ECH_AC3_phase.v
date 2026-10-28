(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCallX AsCall AsWalk AsStack0 ECH_AImg ECH_Xpres ECH_ARep
  ECH_ALib ECH_Iface ECH_AKit ECH_AsKit ECH_AStmt_C0 ECH_AC0_locks ECH_AStmt_C1 ECH_AStmt_C2 ECH_AC2_small ECH_AStmt_C3 ECH_AC3_ready ECH_AC4_frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition AGG_RA : Z := 0x1f7654.     (* [comment removed for export] *)

Ltac ret_lit RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
Ltac ret_lit_any := match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => ret_lit r end.
Ltac show_goal := match goal with |- ?g => idtac "GOAL:" g end.

Section S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  Hypothesis GDF : getdefctx_fresh_stmt H.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma lib_magree_stack : forall s LB m0 m m' W,
    as_RHEAP H s LB m0 -> munch W m m' -> wmono asegs m m' -> Forall (fun iv : Z * Z => aceil <= fst iv) W -> magree (lib_addr LB) m m'.
  Proof.
    intros s LB m0 m m' W HP MU WM FW. acb. eapply (lib_magree_esw H HH); [exact HP| intros b Hb; exact Hb| exact MU| exact WM|].
    eapply Forall_impl; [| exact FW]. cbn beta. intros [l h] K. cbn [fst snd] in *. unfold AIMG_TOP, ALOWSH_LO, AHI_LO.
    split; [lia|]. split; [lia|]. intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (_ & _ & _ & _ & B5 & _). right. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma getdefctx_spec : getdefctx_stmt H.
  Proof.
    unfold getdefctx_stmt, getdefctx_stmt_at. intros [|x]; [exact GDF|].
    unfold getdefctx_stmt_for. intros until CH.
    intros VIS A0 HP KREL BUD BUDC AUX SPB SPA ST CEIL LO SH0 ERR MI TP AC MF IM GM RL CPH RFS LFN CHN CHS PF CLO HAL RAE.
    cbn [CTXPH] in CPH. destruct CPH as [CS CB]. cbn [ctxph_stack] in LO.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| |].
    { pose proof getdefctx_ready_spec as Q; hnf in Q; eapply Q with (lo := lo) (x := x); clear Q; [exact TP| exact CS| exact AC| exact ST| exact CEIL| exact LO| exact MI| exact RAE]. }
    intros msF1 mo1 KREL1 MP1 PO. unfold c3_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & VIS1 & -> & MU1 & WM1 & MI1 & AC1 & ST1 & CS1).
    pose proof (lib_magree_stack _ _ _ _ _ _ HP MU1 WM1 ltac:(apply Forall_cons; [cbn; lia| apply Forall_nil])) as AG1.
    assert (CW : Forall (aclient_write_ok H LB) [(lo, bv_unsigned sp)]) by (apply Forall_cons; [left; cbn; lia| apply Forall_nil]).
    apply (ah_done H HH). unfold getdefctx_post, c3_frame. cbv beta. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m1, errv, s, (@nil block), x, (@nil (Z * Z)). cbn [app].
    split; [exact VIS1|]. split; [exact MP1|].
    split.
    { split; [exact KREL1|]. split; [exact MI1|]. split; [exact AC1|]. split; [exact ST1|].
      split; [eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1| subst tp; unfold ATP; rewrite unsigned_lit by lia; cbn; lia]|].
      split; [eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]|].
      split; [eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]|].
      split; [eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]|].
      split; [eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]|].
      split; [eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]|].
      eapply arelro_across; [exact RL| exact MU1| apply Forall_cons; [cbn; lia| apply Forall_nil]]. }
    split; [cbn; split; reflexivity|]. split; [apply Forall_nil|].
    split; [split; [exact CS1| eapply CTX_blocks_frame; [exact CB| exact AG1]]|].
    split; [intros; discriminate|].
    split; [apply Forall_nil|].
    split; [eapply (ah_RFS_frame H HH); [exact RFS| exact MU1| exact WM1| apply Forall_cons; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE; split; [| lia]|apply Forall_nil]]|].
    2: { split; [| cbn [ctxph_cost]; lia]. cbn [ctxph_foot app].
         eapply (xpres_of_munch H s LB _ _ _ m m m1); [exact HH| exact HP| exact MU1| exact WM1| apply Forall_cons; [left; cbn; lia| apply Forall_nil]]. }
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4). unfold AFS_SIZE, AIMG_TOP in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma gg_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 AGG_RA) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 sp s1
                       (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_get_default_context) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -16)
          /\ rw_cells asegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ossl_lib_ctx_get_ex_data_global) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros ST CEIL LO MI. unfold P_ossl_lib_ctx_get_ex_data_global, P_get_default_context, AGG_RA.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST. do 3 st1. step. step. try if_lit. step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma gg_seg2 :
    forall (sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0 ra : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      rw_cells asegs m (bv_unsigned sp + -16) [C8 s0; C8 ra] -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (fun ms' => exists a1',
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A_defctx_global) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AGG_RA) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 sp s1
                 (Z_to_bv 64 A_defctx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AGG_RA) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros FR MI RAE. unfold AGG_RA, A_defctx, A_defctx_global in *. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR.
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
    st1. if_lit. do 2 st1. if_lit. do 4 st1. step.
    apply evt_done. eexists.
    match goal with |- MS ?R1 _ _ _ _ _ _ = MS ?R2 _ _ _ _ _ _ => replace R1 with R2; [reflexivity|] end.
    f_equal. all: try (apply bv_eq; vm_compute; reflexivity).
  Qed.

  (* [comment removed for export] *)
  Lemma getglobal_spec : getglobal_stmt H.
  Proof.
    unfold getglobal_stmt, getdefctx_stmt_at. intros ph. unfold getdefctx_stmt_for. intros until CH.
    intros VIS A0 HP KREL BUD BUDC AUX SPB SPA ST CEIL LO SH0 ERR MI TP AC MF IM GM RL CPH RFS LFN CHN CHS PF CLO HAL RAE. subst a0. subst tp.
    unfold GETGLOBAL_STACK, FR_ossl_lib_ctx_get_ex_data_global in LO.
    acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (STK0 : 0 <= ctxph_stack ph).
    { destruct ph; cbn [ctxph_stack]; unfold CTXINIT_STACK, AREALLOC_STACK, GETDEFCTX_STACK, CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, FR_get_default_context; lia. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply gg_seg1 with (lo := lo); [exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1).
    pose proof (lib_magree_stack _ _ _ _ _ _ HP MU1 WM1 ltac:(apply Forall_cons; [cbn; lia| apply Forall_nil])) as AG1.
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -16, bv_unsigned sp)]) by (apply Forall_cons; [left; cbn; lia| apply Forall_nil]).
    assert (XP1 : xpres H LB (bv_unsigned sp) (ctxph_foot ph) m m1).
    { eapply (xpres_of_munch H s LB _ _ _ m m m1); [exact HH| exact HP| exact MU1| exact WM1| apply Forall_cons; [left; cbn; lia| apply Forall_nil]]. }
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4). unfold AFS_SIZE, AIMG_TOP in F1, F2.
    (* [comment removed for export] *)
    pose proof getdefctx_spec as GD. unfold getdefctx_stmt, getdefctx_stmt_at, getdefctx_stmt_for in GD.
    eapply (ah_seq H HH).
    { eapply (GD ph) with (lo := lo) (B := B) (LB := LB) (s := s) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH); [exact VIS1| ..]; rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact KREL1| exact BUD| exact BUDC| exact ST1| exact CEIL| exact MI1| exact LFN| exact CLO| exact HAL].
      all: match goal with
           | |- as_RHEAP _ _ _ _ => eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]
           | |- as_rauxv_ok _ _ _ => eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]
           | |- bv_unsigned _ <= _ => lia
           | |- _ mod 16 = 0 => clear - SPA SPR LO STK0; Z.div_mod_to_equations; lia
           | |- _ <= bv_unsigned _ - _ => lia
           | |- ctxph_sh0 _ _ _ _ => destruct ph; [cbn [ctxph_sh0] in SH0 |- *; rewrite unsigned_lit by lia; eapply stack0_sub; [eapply stack0_transport; [exact SH0| exact MU1| exact WM1| apply Forall_cons; [apply stack0_ok_app; unfold AHI_LO; lia| apply Forall_nil]]| lia| lia| clear - SPA SPR; Z.div_mod_to_equations; lia]| exact I]
           | |- _ + -16 <= _ => lia
           | |- _ <= _ - ctxph_stack _ => lia
           | |- rw_cells _ _ _ _ => eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1| unfold ATP; rewrite unsigned_lit by lia; cbn; lia]
           | |- ACONST _ => eapply ACONST_stack_frame; [exact AC| exact MU1| exact WM1| lia]
           | |- MEMFLAG _ _ => eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]
           | |- IMPL_mem _ => eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]
           | |- GOT_mem _ => eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]
           | |- arelro_lib _ => eapply arelro_across; [exact RL| exact MU1| apply Forall_cons; [cbn; lia| apply Forall_nil]]
           | |- CTXPH _ _ _ => eapply CTXPH_frame; [exact CPH| exact AG1]
           | |- as_RFS _ _ _ => eapply (ah_RFS_frame H HH); [exact RFS| exact MU1| exact WM1| apply Forall_cons; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE; lia| apply Forall_nil]]
           | |- as_chain _ _ _ _ => eapply (ah_chain_cons H HH); [eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1| apply Forall_cons; [left; cbn; lia| apply Forall_nil]]| lia| lia| exact SPA| lia| lia| replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia; first [exact FR1| revert FR1; rewrite !Z_to_bv_bv_unsigned; intros FR1; exact FR1]]
           | |- forall fp' ra', In _ _ -> _ => intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]
           | |- pf_ok _ _ _ _ => unfold pf_ok; destruct ph; cbn [PF_ctx PF_ctxinit]; apply Forall_nil
           | |- _ mod 2 = 0 => unfold AGG_RA; rewrite unsigned_lit by lia; reflexivity
           | |- _ => idtac
           end.
    }
    clear GD. intros [msF2 mo2] PO. unfold getdefctx_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & s2' & LBN & x & XS &
                    VIS2 & MP2 & (KREL2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & HEAP2 & MF2 & IM2 & GM2 & RL2) & DELTA & ADDN & CPH2 & KEYS & FXS & RFS2 & XP2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -16)) in ST2, XP2 by lia. unfold AGG_RA in VIS2.
    replace (ret_pc (Z_to_bv 64 0x1f7654)) with (Z_to_bv 64 0x1f7654) in VIS2 by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
    { eapply (xpres_rw_cells' H); [exact XP2| exact FR1| left; cbn; lia|].
      apply Forall_app. split.
      - eapply Forall_impl; [| exact (ctxph_foot_rangeX ph)]. cbn beta. intros iv [K1 K2]. unfold AIMG_TOP in K2. lia.
      - eapply Forall_impl; [| exact FXS]. cbn beta. intros iv Hiv. pose proof (fs_scratch_range H HH _ _ _ RFS2 Hiv) as R. cbn [fst snd] in R |- *. lia. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply gg_seg2; [exact FR2| exact MI2| exact RAE]|].
    intros msF3 mo3 KREL3 MP3 (a1' & VIS3).
    apply (ah_done H HH). unfold getdefctx_post, c3_frame. cbv beta. cbn [cfg_ms cfg_model].
    exists u0, u1, u2, a1', b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, errv2, s2', LBN, x, XS.
    split; [exact VIS3|]. split; [eapply (ah_mpres_trans H HH); [eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]| exact MP3]|].
    split. { split; [exact KREL3|]. split; [exact MI2|]. split; [exact AC2|].
             split. { pose proof (stk_release asegs m2 lo _ _ ST2 FR2 ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
                      replace (bv_unsigned sp + -16 + Z.of_nat 16) with (bv_unsigned sp) in ST3 by lia. exact ST3. }
             split; [exact ERR2|]. split; [exact AUX2|]. split; [exact HEAP2|]. split; [exact MF2|]. split; [exact IM2|]. split; [exact GM2| exact RL2]. }
    split; [exact DELTA|]. split; [exact ADDN|]. split; [exact CPH2|]. split; [exact KEYS|]. split; [exact FXS|]. split; [exact RFS2|].
    split; [| exact AL2].
    eapply (xpres_trans H); [eapply (xpres_weaken H); [exact XP1| lia| auto| intros q K; apply rin_ivs_app; left; exact K]|].
    eapply (xpres_weaken H); [exact XP2| lia| auto| auto].
  Qed.
End S.
