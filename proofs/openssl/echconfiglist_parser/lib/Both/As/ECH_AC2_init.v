(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCallX AsWalk ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AKit ECH_AsKit
  ECH_AStmt_C0 ECH_AC0_locks ECH_AStmt_C2 ECH_AC2_small.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition IC_RA_SM : Z := 0x20939c.  Definition IC_J1 : Z := 0x2093cc.  Definition IC_RA_AL : Z := 0x209448.  Definition IC_RA_RO : Z := 0x209478.
Definition IC_EXIT : Z := 0x209794.  Definition IC_BODY : Z := 0x20936c.

Ltac ret_lit RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
Ltac ret_lit_any := match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => ret_lit r end.
(* [comment removed for export] *)
Ltac aconst_now AC2 MU2 WM2 ACx :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (ACx : ACONST mx)
      by (eapply ACONST_frame; [exact AC2| exact MU2| exact WM2|];
          repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          first [ apply aconst_ok_high; [unfold sh, AIMG_TOP; rewrite ASHADOW_BASE_val; acb; lia| lia]
                | eapply aconst_ok_aapp; [eassumption| lia| unfold AFS_SIZE; lia] ]) end.
Ltac show_goal := match goal with |- evt _ _ (MS ?R _ ?pc _ _ ?mx _) => idtac "PC" pc; idtac R end.

Section S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  Let HSM0 : stack_malloc_0_stmt H := proj1 (proj2 (proj2 HHx)).
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Lemma rw_cells_nil : forall m A, 0 <= A <= 2^64 -> rw_cells asegs m A [].
  Proof.
    intros m A HA. split; [split; [exact I|]|].
    - unfold bytes_at. cbn [length cells_bytes]. repeat split; try lia.
    - unfold wr_at. cbn [cells_size]. repeat split; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ic_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m m1 : mem) (c : errchain) (LF : list fframe) (lo sp1 : Z) (dj : list byte) (gapc : list cell),
    ERR_statics m c -> ACONST m -> arelro_lib m -> as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> athr_cells m -> tp = Z_to_bv 64 ATP ->
    munch [(lo, bv_unsigned sp)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    rw_cells asegs m1 (bv_unsigned sp + -88) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m1 sp1 [CB 8 dj] -> rw_cells asegs m1 (sp1 + 8) gapc -> sp1 + 8 + Z.of_nat (cells_size gapc) = bv_unsigned sp + -88 ->
    bv_unsigned sp + -112 <= sp1 ->
    stk asegs m1 lo sp1 -> aceil <= lo -> lo <= bv_unsigned sp - (96 + 32 + 1024) -> bv_unsigned ra mod 2 = 0 ->
    evt asegs (cinit_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF c lo m)
      (MS (mkR ra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 OPENSSL_INIT_BASE_ONLY) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 IC_BODY) fc None m1 (seg_rom asegs)).
  Proof.
    intros until c. intros LF lo sp1 dj gapc ES AC RL RFS LFN THR TP MU WM MI FR DS GAP SZ SP1 ST CEIL LO RAE.
    unfold AFS_STACK, OPENSSL_INIT_BASE_ONLY, IC_BODY in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (rw_cells_bound _ _ _ _ GAP) as GB.
    (* [comment removed for export] *)
    pose proof (ACONST_shbase m AC) as [GSB SHB0]. pose proof (ACONST_uar m AC) as [GUA UAR].
    unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_UAR, AUAR_CELL, wz in GSB, SHB0, GUA, UAR. rewrite ASHADOW_BASE_val in SHB0.
    pose proof ES as (_ & _ & _ & _ & E5 & E6 & E7 & _ & _ & E10 & _).
    assert (GFD : rw_cells asegs m 0x5e8e28 [C8 (wz P_OPENSSL_init_crypto)])
      by (apply relro_cell; [exact RL| lia| cbn; lia| cbn; tauto| vm_compute; reflexivity]).
    unfold P_OPENSSL_init_crypto in GFD.
    unfold wz, A_stopped, A_base_once, A_base_ret, A_optsdone in *.
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4). pose proof (aapp_not_shadowland _ _ F4) as F5.
    unfold AFS_SIZE, ALOWSH_LO, AHI_LO, AIMG_TOP in F1, F2, F5.
    carry MU WM.
    (* [comment removed for export] *)
    step. step. step. step. st1. st1. st1. st1. step. change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). step. try if_false. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (RFS1 : as_RFS H LF mx)
        by (eapply (ah_RFS_frame H HH); [exact RFS| exact MU| exact WM|];
            apply Forall_cons; [left; cbn [fst snd]; unfold afs_write_ok, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; lia| apply Forall_nil]);
      assert (THR1 : athr_cells mx) by (eapply athr_cells_frame; [exact THR| exact MU| exact WM| apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]]);
      assert (AC1 : ACONST mx) by (eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]) end.
    eapply evt_cut.
    { eapply HSM0 with (lo := lo); try eassumption; rewrite ?unsigned_lit by lia; unfold AFS_STACK; try lia; eassumption. }
    clear RFS1 THR1 AC1 THR.
    intros ms' PO. unfold stack_malloc_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & ff & fp & junk1 & junk2
                    & -> & MU' & WM' & MI' & ST' & RFS2 & FF & SHF & FP & AC2).
    ret_lit_any. rewrite (unsigned_lit sp1) in MU' by lia. rewrite (unsigned_lit sp1) in ST' by lia. unfold AFS_STACK, AFS_FLAGS in MU'.
    change (fsz 0) with 64 in MU', FF. change (fshn 0) with 8 in MU'. change (Z.to_nat (fshn 0)) with 8%nat in SHF. change (Z.to_nat (64 - 40)) with 24%nat in FF.
    (* [comment removed for export] *)
    pose proof (fresh_of_RFS H HH _ _ _ _ _ RFS2) as FRESH.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & _ & _ & _).
    change (fsz 0) with 64 in R2, P6. unfold AFS_HDR, AFS_SIZE, AFS_FLAGS, AIMG_TOP in R1, R2, P1, P2, P3, P4, P5, P6.
    pose proof (SHAD_rw_cells _ _ _ SHF) as SH. cbn [length poison_bytes repeat] in SH.
    set (shf := sh ff) in *.
    assert (SHFB : sh AIMG_TOP + 4608 <= shf /\ shf + 8 <= AHI_LO)
      by (subst shf; unfold sh, AHI_LO, AIMG_TOP; rewrite ASHADOW_BASE_val; clear - R1 R2 ACEILB; Z.div_mod_to_equations; lia).
    let v := eval vm_compute in (sh AIMG_TOP + 4608) in change (sh AIMG_TOP + 4608) with v in SHFB. unfold AHI_LO in SHFB.
    carry MU' WM'.
    (* [comment removed for export] *)
    assert (MUt : munch [(lo, bv_unsigned sp); (as_FSB H, as_FSB H + 4096); (fp, fp + 1); (ff, ff + 64); (shf, shf + 8)] m m2).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU']];
        intros xa Hxa; unfold outside in Hxa |- *; cbn in Hxa |- *; lia. }
    pose proof (wmono_trans _ _ _ _ WM WM') as WMt. clear MU WM MU' WM' MI ST. rename MI' into MI. rename ST' into ST. rename MUt into MU. rename WMt into WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (fp, fp + 1); (ff, ff + 64); (shf, shf + 8)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    (* [comment removed for export] *)
    step. step. step. step. if_cases K0; zify_cond K0; [| kill K0]. clear K0.
    (* [comment removed for export] *)
    step. step. zstep. zstep.
    replace (Z.shiftr ff 3 + 2147450880) with shf by (subst shf; rewrite <- (sh_shiftr ff) by lia; rewrite ASHADOW_BASE_val; reflexivity).
    step. step. st1. step.
    (* [comment removed for export] *)
    st1. st1. st1. step. st1. st1. st1. st1. step. st1. st1. st1. st1.
    (* [comment removed for export] *)
    step. st1. st1. rewrite ?ck8_zxb0. step. try if_false.
    (* [comment removed for export] *)
    zstep. step. step. step. step. step.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    do 4 st1. step. st1. st1. step. step.
    aconst_now AC2 MU2 WM2 ACx.
    assert (ACCO : accessible _ 0xbdd500 8)
      by (assert (IN : In (0xbdd500, 8, 8) aglobals) by (unfold aglobals; cbn; tauto);
          pose proof (ACONST_global_addressable _ 0xbdd500 8 8 ACx IN ltac:(lia)) as AD;
          eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI; lia]).
    ck8_check_lit ACCO 0xbdd500. clear ACCO ACx.
    st1. step. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      match goal with SHc : rw_cells asegs mx shf ?cs |- _ =>
        pose proof (C1_chunk_nth mx shf cs 4 _ SHc eq_refl ltac:(repeat constructor)) as SH4 end end.
    replace (shf + Z.of_nat 4) with (sh (ff + 32)) in SH4 by (subst shf; unfold sh; Z.div_mod_to_equations; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACCT : accessible mx (ff + 32) 8) by (eapply acc8_of_C1; [exact SH4| lia| Z.div_mod_to_equations; lia| unfold AAPP_HI; lia]) end.
    clear SH4.
    ck8_check ACCT (ff + 32). clear ACCT.
    step. st1. st1. st1. step. step.
    release_frame FR0 ST sp1.
    (* [comment removed for export] *)
    step. step. try if_false. st1. step. step. try if_true.
    (* [comment removed for export] *)
    step. step. step. step. step.
    eapply evt_cut.
    { eapply crunonce_spec with (lo := lo) (rest := []);
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
        try (unfold CRUNONCE_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia); try reflexivity. }
    intros ms' PO. unfold c2_post in PO.
    destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m5 & -> & MU5 & WM5 & MI5 & ST5 & _).
    ret_lit_any. rewrite unsigned_lit in MU5, ST5 by lia.
    pose proof MU5 as MU5b. pose proof WM5 as WM5b.
    carry MU5 WM5. extend_munch MU WM MU5 WM5. extend_munch MU2 WM2 MU5b WM5b.
    clear MI ST. rename MI5 into MI. rename ST5 into ST.
    (* [comment removed for export] *)
    step. try if_false. step. st1. change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). step. try if_false. step. step.
    step. try (match goal with |- context [bv_lts ?x ?y] => replace (bv_lts x y) with true by (vm_compute; reflexivity) end; cbv iota).
    (* [comment removed for export] *)
    step. st1. step. step. st1. step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    (* [comment removed for export] *)
    step. do 8 st1. st1. st1. step.
    (* [comment removed for export] *)
    step. zstep. do 11 st1. step. step.
    release_frame DS ST (sp1 + 8). release_frame GAP ST (bv_unsigned sp + -88). release_frame FR ST (bv_unsigned sp).
    pose proof (fs_scratch_of_fresh H _ _ _ _ FRESH) as FSX. change (fsz 0) with 64 in FSX. change (fshn 0) with 8 in FSX. fold shf in FSX.
    unfold AFS_FLAGS in FSX.
    unfold cinit_post. finish.
    + exact FSX.
    + exact MU.
    + eapply ERR_statics_across; [exact ES| exact MU| exact WM|]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_TOP; lia.
    + rewrite <- (lf_remove_head 0 ff fp LF). eapply (ah_release H HH); [exact RFS2| left; reflexivity| exact MU2| exact WM2| |].
      * apply Forall_cons; [left; unfold afs_write_ok; left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; lia|].
        apply Forall_cons; [right; cbn [fst snd]; split; reflexivity|].
        apply Forall_cons; [left; unfold afs_write_ok; right; exists (0, ff, fp); split; [left; reflexivity| cbn [fst snd ff_addr ff_class blk_addr]; change (fsz 0) with 64; lia]|].
        apply Forall_cons; [left; unfold afs_write_ok; left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; lia|].
        apply Forall_nil.
      * lazymatch goal with |- mrd _ ?mx _ = _ => match goal with Hc : rw_cells asegs mx fp _ |- _ => exact (rw_cells_C1_mrd _ _ _ _ _ Hc) end end.
    + eapply ACONST_frame; [exact AC2| exact MU2| exact WM2|].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
        first [ apply aconst_ok_high; [unfold sh, AIMG_TOP; rewrite ASHADOW_BASE_val; acb; lia| lia]
              | eapply aconst_ok_aapp; [eassumption| lia| unfold AFS_SIZE; lia] ].
    + eapply arelro_across; [exact RL| exact MU|]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_TOP in *; lia.
  Qed.

  Lemma cinitcrypto_spec : cinitcrypto_stmt H.
  Proof.
    unfold cinitcrypto_stmt. intros until c. intros LF lo A0 A1 ES AC RL RFS LFN THR TP SPA ST CEIL LO MI RAE. subst a0 a1.
    unfold P_OPENSSL_init_crypto, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, OPENSSL_INIT_BASE_ONLY, AFS_STACK in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 96%nat ST.
    do 14 st1.
    (* [comment removed for export] *)
    zstep. rewrite land_align32 by lia.
    assert (CASES : (bv_unsigned sp + -96) mod 32 = 0 \/ (bv_unsigned sp + -96) mod 32 = 16) by (clear - SPA SPR; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    change (C8 (Z_to_bv 64 0) :: ?rest) with ([C8 (Z_to_bv 64 0)] ++ rest) in FR.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in FR. destruct FR as [C0 FR]. cbn [cells_size csize Nat.add] in FR.
    replace (bv_unsigned sp + -96 + Z.of_nat 8) with (bv_unsigned sp + -88) in FR by lia.
    pose proof (rw_cells_merge asegs _ _ [] [C8 (Z_to_bv 64 0)] [] C0) as C0'. cbn [app cells_size csize cells_bytes cbytes Nat.add] in C0'. clear C0.
    destruct CASES as [CSA|CSB].
    - (* [comment removed for export] *)
      rewrite CSA, Z.sub_0_r.
      eapply ic_tail with (gapc := []); try eassumption; try reflexivity.
      all: lazymatch goal with
           | |- rw_cells _ _ _ [] => apply rw_cells_nil; lia
           | |- _ => cbn [cells_size]; lia
           end.
    - (* [comment removed for export] *)
      rewrite CSB. replace (bv_unsigned sp + -96 - 16) with (bv_unsigned sp + -112) by lia.
      carve_frame 16%nat ST.
      lazymatch type of FR0 with rw_cells _ _ _ [_ _ ?j] =>
        apply (rw_cells_split_CB asegs _ _ [] 16 j [] [8;8]%nat) in FR0; [| reflexivity]; cbn [mk_CB_cells app firstn skipn] in FR0 end.
      lazymatch type of FR0 with rw_cells _ _ _ [?x; ?y] => change [x; y] with ([x] ++ [y]) in FR0 end.
      apply (proj1 (rw_cells_app _ _ _ _ _)) in FR0. destruct FR0 as [DS G1]. cbn [cells_size csize Nat.add] in G1.
      replace (bv_unsigned sp + -112 + Z.of_nat 8) with (bv_unsigned sp + -112 + 8) in G1 by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (GAP : rw_cells asegs mx (bv_unsigned sp + -112 + 8) ([CB 8 _] ++ [CB 8 _]))
        by (apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact G1|]; cbn [cells_size csize Nat.add];
            replace (bv_unsigned sp + -112 + 8 + Z.of_nat 8) with (bv_unsigned sp + -96) by lia; exact C0') end.
      clear G1 C0'. cbn [app] in GAP.
      eapply ic_tail; try eassumption; try reflexivity.
      all: cbn [cells_size csize Nat.add]; lia.
  Qed.
End S.
