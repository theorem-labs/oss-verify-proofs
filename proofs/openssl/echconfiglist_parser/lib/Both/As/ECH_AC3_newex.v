(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCallX AsCall AsWalk AsStack0 ECH_AImg ECH_Xpres ECH_ARep
  ECH_ALib ECH_Iface ECH_AKit ECH_AsKit ECH_AStmt_C0 ECH_AC0_locks ECH_AStmt_C1 ECH_AC1_free ECH_AStmt_C2 ECH_AC2_small ECH_AStmt_C5 ECH_AC5_small
  ECH_AStmt_C3 ECH_AC3_ready.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ANX_BODY  : Z := 0x1fd698.   (* [comment removed for export] *)
Definition ANX_RA_SM : Z := 0x1fd6d0.   (* [comment removed for export] *)
Definition ANX_RA_GG : Z := 0x1fd794.   (* [comment removed for export] *)
Definition ANX_RA_GL : Z := 0x1fd7a8.   (* [comment removed for export] *)
Definition ANX_RA_SN : Z := 0x1fd828.   (* [comment removed for export] *)
Definition ANX_RA_UL : Z := 0x1fd8f8.   (* [comment removed for export] *)
Definition ANX_RA_CF : Z := 0x1fda28.   (* [comment removed for export] *)
Definition ANX_FILE  : Z := 0x4b483.    (* [comment removed for export] *)
Definition ANX_DESCR : Z := 0x26475.    (* [comment removed for export] *)
Definition AGOT_NEWEX_PC : Z := 0x5e8e10.   (* [comment removed for export] *)
Definition AFAKE_MAGIC : Z := 0x41b58ab3.  Definition AFAKE_RETIRED : Z := 0x45e0360e.

Ltac ret_lit RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
Ltac ret_lit_any := match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => ret_lit r end.
Ltac show_goal := match goal with |- ?g => idtac "GOAL:" g end.
Ltac show_regs := match goal with |- evt _ _ (MS ?R _ ?pc _ _ ?mx _) => idtac "PC" pc; idtac R end.
(* [comment removed for export] *)
Ltac aconst_now AC0 MU0 WM0 ACx :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (ACx : ACONST mx)
      by (eapply ACONST_frame; [exact AC0| exact MU0| exact WM0|];
          repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          first [ apply aconst_ok_high; [unfold sh, AIMG_TOP; rewrite ASHADOW_BASE_val; acb; lia| lia]
                | match goal with AP : aapp ?A ?n |- _ => eapply (aconst_ok_aapp _ _ _ _ AP); unfold AFS_SIZE, MUTEX_SIZE in *; lia end ]) end.

(* [comment removed for export] *)
Ltac tr_lock H MU WM F :=
  apply (fun HH0 => rw_cells_transport _ _ _ _ _ _ HH0 MU WM) in H;
  [| cbn; split; [lia| split; [unfold stale in F; clear - F; lia| exact I]]].
Ltac tr_plain H MU WM := apply (fun HH0 => rw_cells_transport _ _ _ _ _ _ HH0 MU WM) in H; [| cbn; lia].
(* [comment removed for export] *)
Ltac extend2 MU WM MU2 WM2 MUc WMc :=
  let MUc2 := fresh "MUc2" in let WMc2 := fresh "WMc2" in
  pose proof MUc as MUc2; pose proof WMc as WMc2; extend_munch MU WM MUc WMc; extend_munch MU2 WM2 MUc2 WMc2.

Section S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  Let HSM2 : stack_malloc_2_stmt H := proj1 (proj2 (proj2 (proj2 HHx))).
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Definition anx_mid (sp : word) (gp tp : word) (F : bvmap 5 word) (fc : bv 32)
      (s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e s1e s0e rae : word) (obj ad xa lo sp1 : Z) (gapc : list cell) (LF : list fframe) (x : ctxinfo) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m2 : mem) (ff fp : Z) (j0 j1 hj sj : list byte),
      ms' = MS (mkR (Z_to_bv 64 ANX_RA_CF) (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1)
                    (Z_to_bv 64 0) (Z_to_bv 64 ANX_FILE) (Z_to_bv 64 259) a3 a4 a5 a6 a7
                    (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 ff) (Z_to_bv 64 (-1)) (Z_to_bv 64 (sh A_defctx_exmeth_bio)) s7e
                    (Z_to_bv 64 A_defctx_exmeth_bio) s9e (Z_to_bv 64 (sh ff)) s11e t3 t4 t5 t6)
               F (Z_to_bv 64 P_CRYPTO_free) fc None m2 (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 256); (sh ff, sh ff + 32); (ad, ad + 16); (xa + 4, xa + 8)]%Z m m2
      /\ wmono asegs m m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo sp1 /\ ACONST m2
      /\ as_RFS H ((2, ff, fp) :: LF) m2 /\ fresh_frame H LF 2 ff fp
      /\ rw_cells asegs m2 (bv_unsigned sp + -104) [C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae]
      /\ rw_cells asegs m2 sp1 [CB 8 j0; C8 (Z_to_bv 64 (ff + 32)); C8 (Z_to_bv 64 ff); C8 (Z_to_bv 64 ff); C8 (Z_to_bv 64 A_defctx_global);
                                C8 (Z_to_bv 64 obj); C8 (Z_to_bv 64 ad); C8 (Z_to_bv 64 ASHADOW_BASE); CB 16 j1; C8 (Z_to_bv 64 ff)]
      /\ rw_cells asegs m2 (sp1 + 88) gapc
      /\ rw_cells asegs m2 ff [CB 248 hj; C8 (Z_to_bv 64 fp)]
      /\ rw_cells asegs m2 (sh ff) [CB 32 sj]
      /\ rw_cells asegs m2 fp [C1 (b8 1)]
      /\ rw_cells asegs m2 ad [C8 (wz 0); C8 (wz 0)]
      /\ CTX_statics m2 x /\ MUTEX m2 xa 0.

  Lemma anx_segA : forall (sp gp tp t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s1e s0e rae : word)
      (F : bvmap 5 word) (fc : bv 32) (m m1 : mem) (LB : list block) (LF : list fframe) (x : ctxinfo)
      (obj ad c0 k0 xp xa bA bN lo sp1 : Z) (jl : list byte) (gapc : list cell),
    (* [comment removed for export] *)
    tp = Z_to_bv 64 ATP -> CTX_statics m x -> cx_exlock x = (xp, xa, 40) -> In (xp, xa, 40) LB -> MUTEX m xa 0 -> aapp xa 40 -> xa mod 16 = 0 ->
    (xa + 40 + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= xa - 16) ->
    ACONST m -> arelro_lib m -> as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> athr_cells m ->
    rw_cells asegs m ad [C8 (wz c0); C8 (wz k0)] -> ad mod 8 = 0 -> accessible m ad 16 ->
    aapp bA bN -> (bA + bN + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= bA - 16) -> bA <= ad -> ad + 16 <= bA + bN ->
    (ad + 16 <= xa \/ xa + 40 <= ad) ->
    (* [comment removed for export] *)
    munch [(lo, bv_unsigned sp)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    rw_cells asegs m1 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1e; C8 s0e; C8 rae] ->
    rw_cells asegs m1 sp1 [CB 88 jl] -> rw_cells asegs m1 (sp1 + 88) gapc -> sp1 + 88 + Z.of_nat (cells_size gapc) = bv_unsigned sp - 104 ->
    bv_unsigned sp - 208 <= sp1 <= bv_unsigned sp - 192 -> sp1 mod 32 = 0 ->
    stk asegs m1 lo sp1 -> aceil <= lo -> lo <= bv_unsigned sp - CNEWEX_READY_STACK ->
    evt asegs (anx_mid sp gp tp F fc s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s1e s0e rae obj ad xa lo sp1 gapc LF x m)
      (MS (mkR rae (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 0) (Z_to_bv 64 CRYPTO_EX_INDEX_BIO) (Z_to_bv 64 obj) (Z_to_bv 64 ad)
                a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ANX_BODY) fc None m1 (seg_rom asegs)).
  Proof.
    intros until gapc. intros TP CS HX XI XM XAP XA16 XFS AC RL RFS LFN THR AD AD8 ACC BAP BFS BLO BHI SEP MU WM MI FR LOC GAP GSZ SP1 SP32 ST CEIL LO.
    unfold ANX_BODY, CNEWEX_READY_STACK, FR_CRYPTO_new_ex_data, FR_ossl_crypto_new_ex_data_ex, NEWEX_INNER, GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK,
      CUNLOCK_STACK, FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock, CFREE_STACK, AFREE_STACK, AFS_STACK,
      FR_ossl_lib_ctx_get_ex_data_global, GETDEFCTX_STACK, FR_get_default_context, CGETLOCAL_STACK, CRYPTO_EX_INDEX_BIO in *. acb.
    (* [comment removed for export] *)
    assert (LO' : lo <= bv_unsigned sp - 8432) by (clear - LO; lia). clear LO. rename LO' into LO.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (rw_cells_bound _ _ _ _ GAP) as GAPB.
    pose proof (aapp_bounds xa 40 XAP ltac:(lia)) as (XB1 & XB2 & XB3 & XB4 & _). pose proof (aapp_not_shadowland _ _ XAP) as XNS.
    pose proof (aapp_bounds bA bN BAP ltac:(lia)) as (BB1 & BB2 & BB3 & BB4 & _). pose proof (aapp_not_shadowland _ _ BAP) as BNS.
    unfold AAPP_HI, ALOWSH_LO, AHI_LO, AIMG_TOP in XB1, XB2, XB3, XNS, BB1, BB2, BB3, BNS.
    (* [comment removed for export] *)
    pose proof (ACONST_shbase m AC) as [GSB SHB0]. pose proof (ACONST_uar m AC) as [GUA UAR].
    unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_UAR, AUAR_CELL, wz in GSB, SHB0, GUA, UAR. rewrite ASHADOW_BASE_val in SHB0.
    assert (GPC : rw_cells asegs m AGOT_NEWEX_PC [C8 (wz P_ossl_crypto_new_ex_data_ex)])
      by (apply relro_cell; [exact RL| unfold AGOT_NEWEX_PC; lia| cbn; unfold AGOT_NEWEX_PC; lia| cbn; tauto| vm_compute; reflexivity]).
    unfold AGOT_NEWEX_PC, P_ossl_crypto_new_ex_data_ex, wz in GPC.
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4). pose proof (aapp_not_shadowland _ _ F4) as F5.
    unfold AFS_SIZE, ALOWSH_LO, AHI_LO, AIMG_TOP in F1, F2, F5. unfold MUTEX in XM.
    carry MU WM.
    (* [comment removed for export] *)
    do 8 st1. change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1). do 4 st1. if_lit. st1. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (RFS1 : as_RFS H LF mx)
        by (eapply (ah_RFS_frame H HH); [exact RFS| exact MU| exact WM|];
            apply Forall_cons; [left; cbn [fst snd]; unfold afs_write_ok, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; lia| apply Forall_nil]);
      assert (THR1 : athr_cells mx) by (eapply athr_cells_frame; [exact THR| exact MU| exact WM| apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]]);
      assert (AC1 : ACONST mx) by (eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]) end.
    eapply evt_cut.
    { eapply HSM2 with (lo := lo); try eassumption; rewrite ?unsigned_lit by lia; unfold AFS_STACK; try lia; eassumption. }
    clear RFS1 THR1 AC1 THR.
    intros ms' PO. unfold stack_malloc_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & ff & fp & junk1 & junk2
                    & -> & MU' & WM' & MI' & ST' & RFS2 & FF & SHF & FP & AC2).
    ret_lit_any. rewrite (unsigned_lit sp1) in MU' by lia. rewrite (unsigned_lit sp1) in ST' by lia. unfold AFS_STACK, AFS_FLAGS in MU'.
    change (fsz 2) with 256 in MU', FF. change (fshn 2) with 32 in MU'. change (Z.to_nat (fshn 2)) with 32%nat in SHF. change (Z.to_nat (256 - 40)) with 216%nat in FF.
    (* [comment removed for export] *)
    pose proof (fresh_of_RFS H HH _ _ _ _ _ RFS2) as FRESH.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & _ & _ & _).
    change (fsz 2) with 256 in R2, P6. unfold AFS_HDR, AFS_SIZE, AFS_FLAGS, AIMG_TOP in R1, R2, P1, P2, P3, P4, P5, P6.
    pose proof (SHAD_rw_cells _ _ _ SHF) as SH. cbn [length poison_bytes repeat] in SH.
    set (shf := sh ff) in *.
    assert (SHFB : sh AIMG_TOP + 4608 <= shf /\ shf + 32 <= AHI_LO)
      by (subst shf; unfold sh, AHI_LO, AIMG_TOP; rewrite ASHADOW_BASE_val; clear - R1 R2 ACEILB; Z.div_mod_to_equations; lia).
    let v := eval vm_compute in (sh AIMG_TOP + 4608) in change (sh AIMG_TOP + 4608) with v in SHFB. unfold AHI_LO in SHFB.
    (* [comment removed for export] *)
    unfold AFS_SIZE in BFS.
    assert (ADFF : ad + 16 <= ff \/ ff + 256 <= ad) by (clear - P5 P6 BLO BHI BFS; lia).
    assert (ADSH : sh AIMG_TOP <= sh ad /\ sh ad + 2 <= AHI_LO /\ (sh ad + 2 <= shf \/ shf + 32 <= sh ad)).
    { subst shf. unfold sh, AHI_LO, AIMG_TOP. rewrite ASHADOW_BASE_val. clear - ADFF BB1 BB3 BLO BHI AD8 M8.
      assert (Q1 : 12599296 / 8 <= ad / 8) by (apply Z.div_le_mono; lia).
      assert (Q2 : ad / 8 + 2 <= 2^44) by (Z.div_mod_to_equations; lia).
      split; [lia|]. split; [lia|].
      destruct ADFF as [D|D]; [left | right].
      - assert (Q3 : (ad + 16) / 8 <= ff / 8) by (apply Z.div_le_mono; lia).
        replace ((ad + 16) / 8) with (ad / 8 + 2) in Q3 by (rewrite <- (Z.div_add ad 2 8) by lia; reflexivity). lia.
      - assert (Q3 : (ff + 256) / 8 <= ad / 8) by (apply Z.div_le_mono; lia).
        replace ((ff + 256) / 8) with (ff / 8 + 32) in Q3 by (rewrite <- (Z.div_add ff 32 8) by lia; reflexivity). lia. }
    let v := eval vm_compute in (sh AIMG_TOP) in change (sh AIMG_TOP) with v in ADSH. unfold AHI_LO in ADSH.
    clear GSB SHB0 GUA UAR.
    (* [comment removed for export] *)
    assert (ADlo : ad + 16 <= lo) by (clear - BLO BHI BB2 CEIL; lia).
    assert (XAlo : xa + 40 <= lo) by (clear - XB2 CEIL; lia).
    unfold AFS_SIZE in XFS.
    assert (ADfsb : ad + 16 <= as_FSB H \/ as_FSB H + 11571200 <= ad) by (clear - BFS BLO BHI; lia).
    assert (ADshf : ad + 16 <= shf \/ shf + 32 <= ad) by (clear - BNS BLO BHI SHFB; lia).
    assert (XAshf : xa + 40 <= shf \/ shf + 32 <= xa) by (clear - XNS SHFB; lia).
    assert (XAff : xa + 40 <= ff \/ ff + 256 <= xa) by (clear - XFS P5 P6; lia).
    assert (ADfp : ad + 16 <= fp \/ fp + 1 <= ad) by (clear - ADfsb P3 P4; lia).
    assert (XAfp : xa + 40 <= fp \/ fp + 1 <= xa) by (clear - XFS P3 P4; lia).
    assert (FFshf : ff + 256 <= shf \/ shf + 32 <= ff) by (clear - F5 P5 P6 SHFB; lia).
    assert (FPshf : fp + 1 <= shf \/ shf + 32 <= fp) by (clear - F5 P3 P4 SHFB; lia).
    assert (ADW : disjoint_from [(sp1 - 1024, sp1); (as_FSB H, as_FSB H + 4096); (fp, fp + 1); (ff, ff + 256); (shf, shf + 32)] ad 16).
    { cbn. split; [clear - ADlo LO SP1; lia|]. split; [clear - ADfsb; lia|]. split; [clear - ADfp; lia|]. split; [clear - ADFF; lia|]. split; [exact ADshf| exact I]. }
    apply (fun HH0 => rw_cells_transport _ _ _ _ _ _ HH0 MU' WM') in AD; [| exact ADW]. clear ADW.
    assert (XAW : disjoint_from [(sp1 - 1024, sp1); (as_FSB H, as_FSB H + 4096); (fp, fp + 1); (ff, ff + 256); (shf, shf + 32)] xa 12).
    { cbn. split; [clear - XAlo LO SP1; lia|]. split; [clear - XFS; lia|]. split; [clear - XAfp; lia|]. split; [clear - XAff; lia|]. split; [clear - XAshf; lia| exact I]. }
    apply (fun HH0 => rw_cells_transport _ _ _ _ _ _ HH0 MU' WM') in XM; [| exact XAW]. clear XAW.
    apply (fun HH0 => rw_cells_transport _ _ _ _ _ _ HH0 MU' WM') in GPC; [| cbn; clear - P1 P3 P4 R1 SHFB SP1 LO CEIL ACEILB; lia].
    apply (fun HH0 => rw_cells_transport _ _ _ _ _ _ HH0 MU' WM') in FR; [| cbn; clear - SP1 SPR F2 P2 P4 R2 CEIL LO SHFB ACEILB; lia].
    apply (fun HH0 => rw_cells_transport _ _ _ _ _ _ HH0 MU' WM') in LOC; [| cbn; clear - SP1 SPR F2 P2 P4 R2 CEIL LO SHFB ACEILB; lia].
    apply (fun HH0 => rw_cells_transport _ _ _ _ _ _ HH0 MU' WM') in GAP; [| cbn; clear - GSZ GAPB SP1 SPR F2 P2 P4 R2 CEIL LO SHFB ACEILB; lia].
    (* [comment removed for export] *)
    assert (DJ1 : chunk_disj ad 16 ff 256) by (unfold chunk_disj; clear - ADFF; lia).
    assert (DJ2 : chunk_disj xa 12 ff 256) by (unfold chunk_disj; clear - XAff; lia).
    assert (DJ3 : chunk_disj shf 32 ff 256) by (unfold chunk_disj; clear - FFshf; lia).
    assert (DJ4 : chunk_disj ad 16 shf 32) by (unfold chunk_disj; clear - ADshf; lia).
    assert (DJ5 : chunk_disj xa 12 shf 32) by (unfold chunk_disj; clear - XAshf; lia).
    assert (DJ6 : chunk_disj ff 256 shf 32) by (unfold chunk_disj; clear - FFshf; lia).
    assert (DJ7 : chunk_disj fp 1 shf 32) by (unfold chunk_disj; clear - FPshf; lia).
    assert (DJ8 : chunk_disj xa 12 ad 16) by (unfold chunk_disj; clear - SEP; lia).
    assert (DJ9 : chunk_disj shf 32 ad 16) by (unfold chunk_disj; clear - ADshf; lia).
    assert (DJ10 : chunk_disj ff 256 ad 16) by (unfold chunk_disj; clear - ADFF; lia).
    assert (DJ11 : chunk_disj fp 1 ad 16) by (unfold chunk_disj; clear - ADfp; lia).
    assert (DJ12 : chunk_disj ad 16 fp 1) by (unfold chunk_disj; clear - ADfp; lia).
    assert (DJ13 : chunk_disj xa 12 fp 1) by (unfold chunk_disj; clear - XAfp; lia).
    assert (DJ14 : chunk_disj shf 32 fp 1) by (unfold chunk_disj; clear - FPshf; lia).
    change (stale (ad + 16 <= as_FSB H \/ as_FSB H + 11571200 <= ad)) in ADfsb. change (stale (ad + 16 <= shf \/ shf + 32 <= ad)) in ADshf.
    change (stale (ad + 16 <= ff \/ ff + 256 <= ad)) in ADFF. change (stale (xa + 40 <= shf \/ shf + 32 <= xa)) in XAshf.
    change (stale (xa + 40 <= ff \/ ff + 256 <= xa)) in XAff. change (stale (ad + 16 <= fp \/ fp + 1 <= ad)) in ADfp.
    change (stale (xa + 40 <= fp \/ fp + 1 <= xa)) in XAfp. change (stale (ff + 256 <= shf \/ shf + 32 <= ff)) in FFshf.
    change (stale (fp + 1 <= shf \/ shf + 32 <= fp)) in FPshf.
    change (stale (bA + bN <= 2147446784 \/ 17594333495296 <= bA)) in BNS. change (stale (xa + 40 <= 2147446784 \/ 17594333495296 <= xa)) in XNS.
    change (stale (as_FSB H + 11571200 <= 2147446784 \/ 17594333495296 <= as_FSB H)) in F5.
    change (stale (bA + bN + 16 <= as_FSB H \/ as_FSB H + 11571200 <= bA - 16)) in BFS.
    change (stale (xa + 40 + 16 <= as_FSB H \/ as_FSB H + 11571200 <= xa - 16)) in XFS.
    change (stale (ad + 16 <= xa \/ xa + 40 <= ad)) in SEP.
    (* [comment removed for export] *)
    assert (MUt : munch [(lo, bv_unsigned sp); (as_FSB H, as_FSB H + 4096); (fp, fp + 1); (ff, ff + 256); (shf, shf + 32); (ad, ad + 16); (xa + 4, xa + 8)] m m2).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU']];
        intros xq Hxq; unfold outside in Hxq |- *; cbn in Hxq |- *; lia. }
    pose proof (wmono_trans _ _ _ _ WM WM') as WMt. clear MU WM MU' WM' MI ST. rename MI' into MI. rename ST' into ST. rename MUt into MU. rename WMt into WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (ff, ff + 256); (shf, shf + 32); (ad, ad + 16); (xa + 4, xa + 8)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    (* [comment removed for export] *)
    do 5 st1. if_cases K0; zify_cond K0; [| kill K0]. clear K0.
    (* [comment removed for export] *)
    do 13 st1.
    replace (Z.shiftr ff 3 + 2147450880) with shf by (subst shf; rewrite <- (sh_shiftr ff) by lia; rewrite ASHADOW_BASE_val; reflexivity).
    (* [comment removed for export] *)
    do 22 st1. step.
    (* [comment removed for export] *)

    aconst_now AC2 MU2 WM2 ACx.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (CSx : CTX_statics mx x)
        by (eapply CTX_statics_across; [exact CS| exact MU| exact WM|];
            repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_TOP; clear - LO CEIL ACEILB F1 P1 R1 SHFB BB1 BLO XB1; lia) end.
    eapply evt_cut.
    { pose proof getglobal_ready_spec as Q; hnf in Q; eapply Q with (lo := lo) (x := x); clear Q; try reflexivity; try (rewrite unsigned_lit by lia); try eassumption;
        try (unfold GETGLOBAL_READY_STACK, FR_ossl_lib_ctx_get_ex_data_global, GETDEFCTX_STACK, FR_get_default_context, CGETLOCAL_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia).
      all: show_goal. all: fail "CUT-GGpre". }
    clear ACx CSx.
    intros ms_ PO. unfold c3_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mg & -> & -> & MUg & WMg & MIg & ACg & STg & CSg).
    ret_lit_any. rewrite (unsigned_lit sp1) in MUg, STg by lia.
    carry MUg WMg. extend2 MU WM MU2 WM2 MUg WMg. clear MI ST. rename MIg into MI. rename STg into ST.
    (* [comment removed for export] *)
    unfold A_defctx_global, A_defctx in *.
    st1. if_lit. do 3 st1. step.
    aconst_now AC2 MU2 WM2 ACx.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (CSx : CTX_statics mx x)
        by (eapply CTX_statics_across; [exact CS| exact MU| exact WM|];
            repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_TOP; clear - LO CEIL ACEILB F1 P1 R1 SHFB BB1 BLO XB1; lia) end.
    eapply evt_cut.
    { pose proof getandlock_spec as Q; hnf in Q; eapply Q with (lo := lo) (x := x) (LB := LB) (rd := 1); clear Q; cbv zeta; rewrite ?HX; cbn [blk_addr blk_size fst snd];
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia;
        try (unfold GETANDLOCK_STACK, FR_get_and_lock, CRWLOCK_STACK, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia).
      all: try (unfold A_defctx_global, A_defctx; reflexivity).
      all: unfold EXLOCK; cbn [blk_addr blk_size fst snd]; split; [exact XI|]; split; [reflexivity|]; split; [| exact XM];
           unfold arange, AIMG_TOP, MUTEX_SIZE; clear - XB1 XB3 XB4 XA16; repeat split; lia. }
    clear ACx CSg CSx.
    intros ms_ PO. rewrite HX in PO. cbn [blk_addr fst snd] in PO. unfold c3_post, mutex_foot in PO.
    destruct PO as (v0 & v1 & v2 & c_0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & ml & -> & -> & MUl & WMl & MIl & ACl & STl & [CSl XMl]).
    ret_lit_any. rewrite (unsigned_lit sp1) in MUl, STl by lia. clear XM. unfold MUTEX, wz in XMl.
    (* [comment removed for export] *)
    tr_lock AD MUl WMl SEP. tr_lock SH MUl WMl XAshf. tr_lock FP MUl WMl XAfp. tr_lock FF MUl WMl XAff.
    tr_plain LOC MUl WMl. tr_plain FR MUl WMl. tr_plain GAP MUl WMl. tr_plain GPC MUl WMl.
    extend2 MU WM MU2 WM2 MUl WMl. clear MI ST. rename MIl into MI. rename STl into ST.
    (* [comment removed for export] *)
    unfold A_defctx_exmeth_bio, A_defctx in *.
    st1. if_lit. do 5 st1. ub_dead. do 4 st1. ubal_any. if_lit. do 3 st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACCx : accessible mx ad 16)
        by (eapply accessible_transport; [exact ACC| exact MU|]; intros q Hq; unfold outside; cbn;
            unfold stale in F5, BNS, XNS; clear - Hq ADSH SHFB ACEILB CEIL LO F5 F1 P1 P2 P3 P4 P5 P6 R1 R2 BNS BLO BHI XNS XB1 AD8; unfold sh in *; rewrite ?ASHADOW_BASE_val in *;
            assert (Q8 : ad / 8 <= q / 8 /\ q / 8 <= ad / 8 + 1) by (clear - Hq AD8; Z.div_mod_to_equations; lia);
            repeat split; lia) end.
    ck8_check ACCx ad. st1. clear ACCx.
    do 3 st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACCx : accessible mx ad 16)
        by (eapply accessible_transport; [exact ACC| exact MU|]; intros q Hq; unfold outside; cbn;
            unfold stale in F5, BNS, XNS; clear - Hq ADSH SHFB ACEILB CEIL LO F5 F1 P1 P2 P3 P4 P5 P6 R1 R2 BNS BLO BHI XNS XB1 AD8; unfold sh in *; rewrite ?ASHADOW_BASE_val in *;
            assert (Q8 : ad / 8 <= q / 8 /\ q / 8 <= ad / 8 + 1) by (clear - Hq AD8; Z.div_mod_to_equations; lia);
            repeat split; lia) end.
    ck8_check ACCx (ad + 8). do 3 st1. if_lit. clear ACCx.
    (* [comment removed for export] *)
    do 2 st1.
    aconst_now AC2 MU2 WM2 ACx.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACG : accessible mx 0xbdd0a0 328)
        by (assert (IN : In (0xbdd0a0, 328, 328) aglobals) by (unfold aglobals; cbn; tauto);
            pose proof (ACONST_global_addressable mx 0xbdd0a0 328 328 ACx IN ltac:(lia)) as AD';
            eapply addressable_accessible; [exact AD'| lia| lia| unfold AAPP_HI; lia]) end.
    ck8_check_lit ACG 0xbdd110. clear ACG.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (CSx : CTX_statics mx x)
        by (eapply CTX_statics_across; [exact CS| exact MU| exact WM|];
            repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_TOP; clear - LO CEIL ACEILB F1 P1 R1 SHFB BB1 BLO XB1; lia) end.
    pose proof CSx as (_ & _ & _ & _ & _ & _ & _ & D8 & _). unfold A_defctx_exmeth_bio, A_defctx, wz in D8. clear CSx.
    do 2 st1. clear D8. st1. step.
    eapply evt_cut.
    { pose proof ask_num_null_spec as Q; hnf in Q; eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia. }
    clear ACx.
    intros ms_ PO. unfold sknull_post in PO.
    destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & mn & -> & MUn & WMn & MIn & ACn & STn).
    ret_lit_any. rewrite (unsigned_lit sp1) in MUn, STn by lia.
    carry MUn WMn. extend2 MU WM MU2 WM2 MUn WMn. clear MI ST. rename MIn into MI. rename STn into ST.
    (* [comment removed for export] *)
    do 3 st1. if_lit. do 5 st1. if_lit. do 3 st1.
    (* [comment removed for export] *)

    aconst_now AC2 MU2 WM2 ACx.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACG : accessible mx 0xbdd0a0 328)
        by (assert (IN : In (0xbdd0a0, 328, 328) aglobals) by (unfold aglobals; cbn; tauto);
            pose proof (ACONST_global_addressable mx 0xbdd0a0 328 328 ACx IN ltac:(lia)) as AD';
            eapply addressable_accessible; [exact AD'| lia| lia| unfold AAPP_HI; lia]);
      assert (CSx : CTX_statics mx x)
        by (eapply CTX_statics_across; [exact CS| exact MU| exact WM|];
            repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_TOP; clear - LO CEIL ACEILB F1 P1 R1 SHFB BB1 BLO XB1; lia) end.
    ck8_check_lit ACG 0xbdd0a8. clear ACG.
    pose proof CSx as (_ & _ & _ & _ & _ & _ & D7 & _). unfold A_defctx_exlock, A_defctx, wz in D7. rewrite HX in D7. cbn [blk_addr fst snd] in D7.
    st1. clear D7 CSx. idtac. step.
    eapply evt_cut.
    { pose proof cunlock_spec as Q; hnf in Q; eapply Q with (lo := lo) (M := xa) (lk := MUTEX_HELD); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia;
        try (unfold MUTEX_SIZE, MUTEX_HELD, CUNLOCK_STACK, FR_mutex_unlock, FR_pthread_mutex_unlock, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock in *; lia).
      all: try (unfold MUTEX, wz; exact XMl).
      all: show_goal. all: fail "CUT-ULpre". }
    clear ACx.
    intros ms_ PO. unfold c2_post, mutex_foot in PO.
    destruct PO as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & mu & -> & MUu & WMu & MIu & STu & XMu).
    ret_lit_any. rewrite (unsigned_lit sp1) in MUu, STu by lia. clear XMl.
    tr_lock AD MUu WMu SEP. tr_lock SH MUu WMu XAshf. tr_lock FP MUu WMu XAfp. tr_lock FF MUu WMu XAff.
    tr_plain LOC MUu WMu. tr_plain FR MUu WMu. tr_plain GAP MUu WMu. tr_plain GPC MUu WMu.
    extend2 MU WM MU2 WM2 MUu WMu. clear MI ST. rename MIu into MI. rename STu into ST.
    (* [comment removed for export] *)
    st1. if_lit. do 2 st1. if_lit. do 3 st1. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
    do 4 st1. step.
    (* [comment removed for export] *)
    aconst_now AC2 MU2 WM2 ACx.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (CSx : CTX_statics mx x)
        by (eapply CTX_statics_across; [exact CS| exact MU| exact WM|];
            repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_TOP; clear - LO CEIL ACEILB F1 P1 R1 SHFB BB1 BLO XB1; lia);
      assert (RFSx : as_RFS H ((2, ff, fp) :: LF) mx)
        by (eapply (ah_RFS_frame H HH); [exact RFS2| exact MU2| exact WM2|];
            unfold stale in F5, ADfsb, XFS;
            repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold afs_write_ok; cbn [fst snd];
            first [ right; exists (2, ff, fp); split; [left; reflexivity| cbn [fst snd ff_addr ff_class blk_addr]; change (fsz 2) with 256; lia]
                  | left; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE; clear - F1 F2 F5 CEIL LO SPR SHFB ADfsb XFS BB1 BLO XB1 ACEILB; lia
                  | show_goal ]) end.
    (* [comment removed for export] *)
    apply rw_cells_flatten in SH. cbn [cells_size csize cells_bytes cbytes Nat.add app] in SH.
    lazymatch type of FF with rw_cells _ ?mx _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5] =>
      change [c0; c1; c2; c3; c4; c5] with ([c0; c1; c2; c3; c4] ++ [c5]) in FF end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in FF. destruct FF as [FFa FFb]. apply rw_cells_flatten in FFa.
    pose proof (proj2 (rw_cells_app _ _ _ _ _) (conj FFa FFb)) as FF. clear FFa FFb.
    cbn [cells_size csize cells_bytes cbytes Nat.add app length] in FF.
    unfold anx_mid. finish.
    all: try exact MU. all: try exact RFSx. all: try exact FRESH. all: try exact FF. all: try exact SH. all: try exact LOC.
    all: try (unfold MUTEX, MUTEX_HELD, wz in *; assumption).
  Qed.
End S.
