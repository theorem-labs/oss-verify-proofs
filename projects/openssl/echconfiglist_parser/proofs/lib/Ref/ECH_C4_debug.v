(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface F_strlen F_strcpy ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Kit2 ECH_Rep ECH_LibState
     ECH_C0_stmt ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C2_stmt ECH_LibFrame ECH_C4_stmt ECH_C4_rep ECH_C4_frame ECH_C4_egs.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Definition ED_RA_M1 : Z := 0xdf08c.   (* [comment removed for export] *)
  Definition ED_RA_M2 : Z := 0xdf0f0.   (* [comment removed for export] *)
  Definition ed_frame (s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma ed_segA :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (c : errchain) (exl : ctxinfo) (E : errst)
           (file line func lo : Z) (fs fsl : list byte) (errv : word),
      a0 = Z_to_bv 64 file -> a1 = Z_to_bv 64 line -> a2 = Z_to_bv 64 func -> 0 <= line < 2^31 -> 0 <= func < 2^64 ->
      ROSTR file fs fsl -> fs <> [] -> 0 < file ->
      tp = Z_to_bv 64 RATP -> rw_cells rsegs m RERRNO [C4 errv] ->
      CTX_statics m exl -> ERR_statics m c -> ERR_chain LB m c -> chain_below c lo ->
      ERRSTm m (blk_addr (ec_es c)) E -> sl_file (slot_at E (es_top E)) = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - (64 + 144) -> mem_inv rsegs m ->
      IMPL_mem m -> GOT_mem m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (fun ms' => exists u0 u1 u2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR (Z_to_bv 64 ED_RA_M1) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 sp (Z_to_bv 64 func)
                       (Z_to_bv 64 (Z.of_nat (length fs) + 1)) (Z_to_bv 64 0) (Z_to_bv 64 0) b3 b4 b5 b6 b7
                       (Z_to_bv 64 line) (Z_to_bv 64 (blk_addr (ec_es c))) (Z_to_bv 64 file)
                       (Z_to_bv 64 (blk_addr (ec_es c) + es_top E * 8)) (Z_to_bv 64 (es_top E)) s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 P_CRYPTO_malloc) fc None m1 (seg_rom rsegs)
          /\ munch [(lo, bv_unsigned sp); (RERRNO, RERRNO + 4)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp + -64)
          /\ rw_cells rsegs m1 (bv_unsigned sp + -64) (ed_frame s6 s5 s4 s3 s2 s1 s0 ra)
          /\ rw_cells rsegs m1 RERRNO [C4 errv]
          /\ ERRSTm m1 (blk_addr (ec_es c)) E /\ IMPL_mem m1 /\ GOT_mem m1)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ERR_set_debug) fc None m (seg_rom rsegs)).
  Proof.
    intros until errv. intros A0 A1 A2 LNR FNR (RSL & RSH & RS) FSN FPOS TP ERR CS ES EC CB EM F0 ST CEIL LO MI IM GM RAE. subst a0 a1 a2 tp.
    unfold P_ERR_set_debug, P_CRYPTO_malloc, ED_RA_M1, ed_frame. hcb.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    unfold RERRNO in *.
    pose proof CS as CS0. pose proof ES as ES0. pose proof EC as EC0.
    assert (ESR : 0 < blk_addr (ec_es c) /\ blk_addr (ec_es c) + 904 <= lo /\ (blk_addr (ec_es c) + 904 <= 65536 \/ 3215360 <= blk_addr (ec_es c))).
    { destruct EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Z5 & _ & _ & RR).
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail RR)))) as R5. unfold rblock_range in R5. rewrite Z5 in R5.
      unfold chain_below, ERRST_SIZE in *. lia. }
    set (es := blk_addr (ec_es c)) in *.
    pose proof (munch_refl [(lo, bv_unsigned sp); (3077076, 3077076 + 4)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof EM as EM0. unfold ERRSTm in EM. destruct EM as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    set (top := es_top E) in *. arr_lens SL.
    unfold IMPL_mem, GOT_mem, A_malloc_impl, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free in IM, GM.
    (* [comment removed for export] *)
    carve_frame 64%nat ST. do 9 st1. step. step. step. step. step. step.
    pose proof (CTX_statics_munch _ _ _ _ CS0 MU WM ltac:(libx_windows)) as CSc.
    pose proof (ERR_statics_munch _ _ _ _ ES0 MU WM ltac:(libx_windows)) as ESc.
    pose proof (ERR_chain_munch _ _ _ _ _ _ EC0 CB MU WM ltac:(chain_windows)) as ECc.
    eapply evt_cut.
    { spec_as Q egs_ready_spec. eapply Q with (lo := lo) (c := c) (exl := exl) (LB := LB) (save := 1) (errv := errv); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia;
        try (unfold EGS_STACK, FR_ossl_err_get_state_int, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, FR_CRYPTO_THREAD_wrap, FR_CRYPTO_THREAD_read_lock; lia). }
    intros ms_ PO_; unfold egsr_post, RERRNO in PO_; revert ms_ PO_.
    land MU WM. clear CSc ESc ECc. fold es.
    match goal with K : rw_cells _ _ (bv_unsigned (Z_to_bv 64 RATP) + -164) _ |- _ => change (bv_unsigned (Z_to_bv 64 RATP) + -164) with 3077076 in K; rename K into ERR end.
    (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
    step. st1. rewrite sx32_wz by lia. unfold wz. zstep. zstep. shl_norm.
    pose proof (u64arr_read_m _ _ _ top _ F7 (slot_nth E top (fun s => wz (sl_file s)) SL TR) ltac:(lia)) as RD.
    cbv beta in RD. fold top in F0. rewrite F0 in RD. unfold wz in RD. step. clear RD.
    step. step. step. step.
    eapply evt_cut.
    { spec_as Q cfree_null_evt_spec. eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia;
        first [ unfold IMPL_mem, A_malloc_impl, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz; exact IM
              | unfold GOT_mem, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz; exact GM ]. }
    land MU WM.
    (* [comment removed for export] *)
    match goal with MIc : mem_inv rsegs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (RS mc MIc) as (BSf & NNf & PADf) end.
    pose proof (bytes_at_bound _ _ _ _ BSf) as FB. rewrite length_app in FB. cbn [length] in FB.
    step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
    destruct fs as [|f0 fs'] eqn:EFS; [congruence|]. rewrite <- EFS in *.
    assert (F0N : bv_unsigned f0 <> 0).
    { intros E0. apply NNf. rewrite EFS. left. apply bv_eq. rewrite E0. reflexivity. }
    pose proof (byte_range f0) as F0R.
    pose proof (u8ro_read rsegs _ file (fs ++ Z_to_bv 8 0 :: fsl) 0 f0 (wa (file + 0)) BSf ltac:(rewrite EFS; reflexivity) ltac:(lia) eq_refl) as RD.
    replace (file + 0) with file in RD by lia.
    step. clear RD. change (zxb f0) with (Z_to_bv 64 (bv_unsigned f0)).
    step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
    step. step. step.
    eapply evt_cut.
    { eapply strlen_spec with (str := fs) (slack := fsl); rewrite ?unsigned_lit by lia; try eassumption. }
    land MU WM.
    (* [comment removed for export] *)
    zstep. step. step. step.
    finish.
    unfold ERRSTm, O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP. fold top.
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
  Qed.
  (* [comment removed for export] *)
  Lemma ed_segB :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (E : errst)
           (es file line func lo A1 : Z) (fs fsl gs gsl junk : list byte) (fo : oblk),
      ROSTR file fs fsl -> ROSTR func gs gsl -> gs <> [] -> 0 < func -> 0 <= line < 2^31 -> tp = Z_to_bv 64 RATP ->
      ERRSTm m es E -> sl_func (slot_at E (es_top E)) = 0 ->
      0 < es -> es + 904 <= lo -> (es + 904 <= 65536 \/ 3215360 <= es) ->
      rw_cells rsegs m A1 [CB (S (length fs)) junk] -> 0 < A1 -> A1 + Z.of_nat (length fs) + 1 <= lo ->
      (A1 + Z.of_nat (length fs) + 1 <= 65536 \/ 3215360 <= A1) -> (A1 + Z.of_nat (length fs) + 1 <= es \/ es + 904 <= A1) ->
      stk rsegs m lo (bv_unsigned sp + -64) -> hceil <= lo -> lo <= bv_unsigned sp - (64 + 16) -> mem_inv rsegs m ->
      IMPL_mem m -> GOT_mem m ->
      evt rsegs (fun ms' => exists u0 u1 u2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR (Z_to_bv 64 ED_RA_M2) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 sp (Z_to_bv 64 func)
                       (Z_to_bv 64 (Z.of_nat (length gs) + 1)) (Z_to_bv 64 0) (Z_to_bv 64 0) b3 b4 b5 b6 b7
                       (Z_to_bv 64 line) (Z_to_bv 64 (es + es_top E * 4)) (Z_to_bv 64 file)
                       (Z_to_bv 64 (es + es_top E * 8)) (Z_to_bv 64 (es_top E * 4)) s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 P_CRYPTO_malloc) fc None m1 (seg_rom rsegs)
          /\ munch [(lo, bv_unsigned sp + -64); (es, es + 904); (A1, A1 + Z.of_nat (length fs) + 1)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp + -64)
          /\ ERRSTm m1 es (es_with_slot E (es_top E) (slot_setfile (slot_at E (es_top E)) A1 fo line))
          /\ IMPL_mem m1 /\ GOT_mem m1)
        (MS (mkR (Z_to_bv 64 ED_RA_M1) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 func)
                 (Z_to_bv 64 A1) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 line) (Z_to_bv 64 es) (Z_to_bv 64 file) (Z_to_bv 64 (es + es_top E * 8)) (Z_to_bv 64 (es_top E)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ED_RA_M1)) fc None m (seg_rom rsegs)).
  Proof.
    intros until fo. intros (RSL & RSH & RS) (RGL & RGH & RG) GSN GPOS LNR TP EM G0 EPOS EBL EOFF BK A1P A1L A1OFF A1ES ST CEIL LO MI IM GM. subst tp.
    unfold P_CRYPTO_malloc, ED_RA_M1, ED_RA_M2, IMG_LO, IMG_HI in *. hcb.
    replace (ret_pc (Z_to_bv 64 0xdf08c)) with (Z_to_bv 64 0xdf08c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp + -64); (es, es + 904); (A1, A1 + Z.of_nat (length fs) + 1)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold ERRSTm in EM. destruct EM as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RGs).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    set (top := es_top E) in *. arr_lens SL.
    unfold IMPL_mem, GOT_mem, A_malloc_impl, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free in IM, GM.
    (* [comment removed for export] *)
    arr_store64 F7 top (wz A1).
    step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
    step. step. step.
    match goal with MIc : mem_inv rsegs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (RS mc MIc) as (BSf & NNf & PADf) end.
    pose proof (bytes_at_bound _ _ _ _ BSf) as FB. rewrite length_app in FB. cbn [length] in FB.
    eapply evt_cut.
    { eapply strcpy_spec with (str := fs) (slack := fsl) (junk := junk) (lo := lo); rewrite ?unsigned_lit by lia; try eassumption; try lia. }
    land MU WM.
    (* [comment removed for export] *)
    step.
    pose proof (u64arr_read_m _ _ _ top _ F9 (slot_nth E top (fun s => wz (sl_func s)) SL TR) ltac:(lia)) as RD.
    cbv beta in RD. fold top in G0. rewrite G0 in RD. unfold wz in RD. step. clear RD.
    zstep. zstep. shl_norm.
    arr_store32 F8 top (wz line).
    step. step. step. step.
    eapply evt_cut.
    { spec_as Q cfree_null_evt_spec. eapply Q with (lo := lo); clear Q;
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try lia;
        first [ unfold IMPL_mem, A_malloc_impl, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz; exact IM
              | unfold GOT_mem, A_got_CRYPTO_malloc, P_CRYPTO_malloc, P_CRYPTO_realloc, P_CRYPTO_free, wz; exact GM ]. }
    land MU WM.
    (* [comment removed for export] *)
    match goal with MIc : mem_inv rsegs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (RG mc MIc) as (BSg & NNg & PADg) end.
    pose proof (bytes_at_bound _ _ _ _ BSg) as GB. rewrite length_app in GB. cbn [length] in GB.
    step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
    destruct gs as [|g0 gs'] eqn:EGS; [congruence|]. rewrite <- EGS in *.
    assert (G0N : bv_unsigned g0 <> 0).
    { intros E0. apply NNg. rewrite EGS. left. apply bv_eq. rewrite E0. reflexivity. }
    pose proof (byte_range g0) as G0R.
    pose proof (u8ro_read rsegs _ func (gs ++ Z_to_bv 8 0 :: gsl) 0 g0 (wa (func + 0)) BSg ltac:(rewrite EGS; reflexivity) ltac:(lia) eq_refl) as RD.
    replace (func + 0) with func in RD by lia.
    step. clear RD. change (zxb g0) with (Z_to_bv 64 (bv_unsigned g0)).
    step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
    step. step. step.
    eapply evt_cut.
    { eapply strlen_spec with (str := gs) (slack := gsl); rewrite ?unsigned_lit by lia; try eassumption. }
    land MU WM.
    zstep. step. step. step.
    finish.
    pose proof (slot_at_own _ E top RGs SL TR) as (O1 & O2 & O3).
    eapply (ERRSTm_with_slot _ es E top (slot_setfile (slot_at E top) A1 fo line)); try eassumption; try reflexivity;
      try (upd_keep_tac E top SL TR); cbn [slot_setfile sl_flags sl_buffer sl_line]; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma ed_segC :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (E : errst)
           (es func lo A2 : Z) (gs gsl junk : list byte) (go : oblk),
      ROSTR func gs gsl ->
      ERRSTm m es E -> 0 < es -> es + 904 <= lo -> (es + 904 <= 65536 \/ 3215360 <= es) ->
      rw_cells rsegs m A2 [CB (S (length gs)) junk] -> 0 < A2 -> A2 + Z.of_nat (length gs) + 1 <= lo ->
      (A2 + Z.of_nat (length gs) + 1 <= 65536 \/ 3215360 <= A2) -> (A2 + Z.of_nat (length gs) + 1 <= es \/ es + 904 <= A2) ->
      stk rsegs m lo (bv_unsigned sp + -64) -> rw_cells rsegs m (bv_unsigned sp + -64) (ed_frame s6 s5 s4 s3 s2 s1 s0 ra) ->
      hceil <= lo -> lo <= bv_unsigned sp - (64 + 16) -> bv_unsigned sp + 8 <= 2^64 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR ra sp gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 A2) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (ret_pc ra) fc None m1 (seg_rom rsegs)
          /\ munch [(lo, bv_unsigned sp); (es, es + 904); (A2, A2 + Z.of_nat (length gs) + 1)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp)
          /\ ERRSTm m1 es (es_with_slot E (es_top E) (slot_setfunc (slot_at E (es_top E)) A2 go)))
        (MS (mkR (Z_to_bv 64 ED_RA_M2) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 func)
                 (Z_to_bv 64 A2) a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 (Z_to_bv 64 (es + es_top E * 8)) x6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ED_RA_M2)) fc None m (seg_rom rsegs)).
  Proof.
    intros until go. intros (RGL & RGH & RG) EM EPOS EBL EOFF BK A2P A2L A2OFF A2ES ST FR CEIL LO SP8 MI.
    unfold ED_RA_M2, ed_frame, IMG_LO, IMG_HI in *. hcb.
    replace (ret_pc (Z_to_bv 64 0xdf0f0)) with (Z_to_bv 64 0xdf0f0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp); (es, es + 904); (A2, A2 + Z.of_nat (length gs) + 1)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold ERRSTm in EM. destruct EM as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RGs).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    set (top := es_top E) in *. arr_lens SL.
    (* [comment removed for export] *)
    arr_store64 F9 top (wz A2).
    step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
    step. do 8 st1. step.
    release_frame FR ST (bv_unsigned sp).
    step. step.
    match goal with MIc : mem_inv rsegs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (RG mc MIc) as (BSg & NNg & PADg) end.
    pose proof (bytes_at_bound _ _ _ _ BSg) as GB. rewrite length_app in GB. cbn [length] in GB.
    eapply evt_cut.
    { eapply strcpy_spec with (str := gs) (slack := gsl) (junk := junk) (lo := lo); rewrite ?unsigned_lit by lia; try eassumption; try lia. }
    land MU WM.
    finish.
    pose proof (slot_at_own _ E top RGs SL TR) as (O1 & O2 & O3).
    eapply (ERRSTm_with_slot _ es E top (slot_setfunc (slot_at E top) A2 go)); try eassumption; try reflexivity;
      try (upd_keep_tac E top SL TR); cbn [slot_setfunc sl_flags sl_buffer sl_line]; lia.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HX : heap_sr_hyps_x H.
  Let HH : heap_sr_hyps H := proj1 HX.
  Let PERM : RHEAP_perm_law H := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).
  Let AUXE : rauxv_elim H := proj1 (proj2 (proj2 (proj2 HX))).

  (* [comment removed for export] *)
  Lemma malloc_world : forall LBx Lall spx m m' c x E,
    C4W LBx m (ErrReady c) x -> xpres Lall spx memflag_foot m m' -> MEMFLAG m' 1 -> (forall b, In b LBx -> In b Lall) ->
    ERRSTm m (blk_addr (ec_es c)) E -> hceil <= spx ->
    (forall b, In b LBx -> rblock_range (blk_addr b) (blk_size b)) ->
    C4W LBx m' (ErrReady c) x /\ ERRSTm m' (blk_addr (ec_es c)) E
    /\ (forall A cs, rw_cells rsegs m A cs -> spx <= A -> rw_cells rsegs m' A cs).
  Proof.
    intros LBx Lall spx m m' c x E CW XP MF' SUB EM CE RBL. hcb.
    pose proof CW as (_ & _ & _ & _ & [_ EC] & _). cbn [ERRPH] in EC. destruct EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    pose proof (RBL _ I5) as RB5. unfold rblock_range in RB5. rewrite Z5 in RB5. unfold ERRST_SIZE in *.
    split; [eapply C4W_xpres_mf; eassumption|].
    split.
    { eapply ERRSTm_xpres; [exact EM| exact XP| | lia| unfold ERRST_SIZE; lia].
      intros a Ha. split; [right; right; exists (ec_es c); split; [apply SUB; exact I5| rewrite Z5; exact Ha]|].
      unfold memflag_foot, A_mem_inited, ERRST_SIZE in *. cbn. lia. }
    intros A cs FR SA. pose proof (rw_cells_bound _ _ _ _ FR) as FB.
    eapply xpres_rw_cells'; [exact XP| exact FR| left; lia|]. unfold memflag_foot, A_mem_inited. constructor; [cbn; lia| constructor].
  Qed.

  Lemma errdebug_spec : errdebug_stmt H.
  Proof.
    unfold errdebug_stmt. intros until errv.
    intros A0 A1 A2 LNR RSF FSN FSL FPOS RSG GSN GSL GPOS SEMP HP KREL BY CN BG AUX SPB ST CEIL LO ERR MI TP MF IM GM RL EP EST CB CP RAE.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    subst tp. rewrite errno_RATP in ERR.
    assert (STK : 64 + 8240 <= bv_unsigned sp - lo).
    { unfold ERRDEBUG_STACK, FR_ERR_set_debug, EGS_STACK, FR_ossl_err_get_state_int, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, FR_CRYPTO_THREAD_wrap,
        FR_CRYPTO_THREAD_read_lock, CMALLOC_STACK, FR_CRYPTO_malloc, RMALLOC_STACK in LO. lia. }
    assert (SP8 : bv_unsigned sp + 8 <= 2^64).
    { destruct (AUXE _ _ AUX) as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & sec & _ & _ & _ & _ & K1 & K2 & _). lia. }
    set (SB := blocks_ERRST E) in *. set (es := blk_addr (ec_es c)) in *. set (top := es_top E) in *.
    cbn [ERRPH CTXPH] in EP, CP. destruct EP as [ES EC]. destruct CP as [CS CBK].
    assert (SUBx : forall b, In b LB -> In b (SB ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    assert (RBL : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)).
    { intros b Hb. eapply (HH_RHEAP_block_range H HH); [exact HP| apply SUBx; exact Hb]. }
    pose proof EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    pose proof (RBL _ I5) as RB5. unfold rblock_range in RB5. rewrite Z5 in RB5. fold es in RB5. unfold ERRST_SIZE in RB5.
    apply ERRST_split in EST. destruct EST as [EM OWN]. pose proof EM as (SL & TR & _). fold top in TR.
    pose proof (slot_at_own _ E top OWN SL TR) as [OF OG]. destruct SEMP as [FE GE]. fold top in FE, GE.
    rewrite FE in OF. rewrite GE in OG. cbn [ofield] in OF, OG.
    pose proof RSF as (RFL & RFH & _). pose proof RSG as (RGL & RGH & _). unfold IMG_LO, IMG_HI in *.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL|
      eapply ed_segA with (lo := lo) (c := c) (exl := x) (LB := LB) (E := E) (fs := fs) (fsl := fsl) (errv := errv); try eassumption; try reflexivity; try lia|].
    intros ms1 (u0 & u1 & u2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & ERR1 & EM1 & IM1 & GM1).
    assert (FW1 : Forall stack_or_errno [(lo, bv_unsigned sp); (RERRNO, RERRNO + 4)]).
    { constructor; [left; cbn; lia|]. constructor; [right; cbn; lia| constructor]. }
    assert (CW1 : C4W LB m1 (ErrReady c) x).
    { eapply C4W_stack; [| exact MU1| exact WM1| exact FW1| exact RBL]. unfold C4W. cbn [ERRPH CTXPH]. tauto. }
    assert (HP1 : hs_RHEAP H s (SB ++ LB) m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|].
      constructor; [left; cbn; lia|]. constructor; [| constructor]. right; left. unfold RERRNO, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK. cbn. lia. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL, RERRNO. constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. }
    (* [comment removed for export] *)
    set (n1 := Z.of_nat (length fs) + 1) in *.
    assert (BYN : forall L, lb_bytes L = lb_bytes L) by reflexivity.
    eapply (sr_seq H HH).
    { pose proof (cmalloc_spec H HH) as CM. unfold cmalloc_stmt, cmalloc_stmt_at in CM.
      eapply CM with (n := n1) (v := 1) (lo := lo) (B := B) (LB := SB ++ LB) (s := s) (errv := errv);
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try (unfold n1; lia);
        try (unfold CMALLOC_STACK, FR_CRYPTO_malloc, RMALLOC_STACK; lia); try (destruct CW1 as (K0 & _); exact K0).
      - unfold n1, ERRDEBUG_BYTES in *. lia.
      - rewrite big1_small by (unfold n1, BIGB; lia). lia. }
    intros [ms2 mo2] PO. unfold cmalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & errv2 & A1v & junk1 & p1 & s2' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & RB1 & HP2 & BK1 & MF2 & IM2 & GM2).
    rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST2, XP2 by lia.
    destruct (malloc_world _ _ _ _ m2 _ _ _ CW1 XP2 MF2 SUBx EM1 ltac:(lia) RBL) as (CW2 & EM2 & TR2).
    pose proof (TR2 _ _ FR1 ltac:(lia)) as FR2.
    (* [comment removed for export] *)
    set (bk1 := (p1, A1v, n1)) in *.
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP2) as ND2. cbn [map] in ND2. inversion ND2 as [|z l NI1 ND2']; subst z l.
    assert (NB1 : ~ In bk1 LB) by (intros K; apply NI1; apply (in_map blk_id) in K; cbn in K; rewrite map_app; apply in_or_app; right; exact K).
    assert (SUB2 : forall b, In b LB -> In b (bk1 :: SB ++ LB)) by (intros b Hb; right; apply SUBx; exact Hb).
    assert (DJ1 : A1v + n1 <= es \/ es + 904 <= A1v).
    { pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ bk1 (ec_es c) HP2 (or_introl eq_refl) (SUB2 _ I5)) as DJ. cbn [blk_id blk_addr blk_size fst snd bk1] in DJ.
      rewrite Z5 in DJ. fold es in DJ. unfold ERRST_SIZE in DJ.
      assert (NE : p1 <> blk_id (ec_es c)).
      { intros EQ. apply NI1. change (blk_id bk1) with p1. rewrite EQ. apply in_map. apply SUBx. exact I5. }
      specialize (DJ NE). lia. }
    unfold rblock_range in RB1.
    replace (Z.to_nat n1) with (S (length fs)) in BK1 by (unfold n1; lia).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2|
      eapply ed_segB with (lo := lo) (es := es) (E := E) (fs := fs) (fsl := fsl) (gs := gs) (gsl := gsl) (A1 := A1v) (junk := junk1)
                          (fo := Some (p1, n1)); try eassumption; try reflexivity; try (unfold n1 in *; lia)|].
    intros ms3 (w0 & w1 & w2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & EM3 & IM3 & GM3).
    assert (FW3 : Forall (heapw c lo (bv_unsigned sp + -64) bk1) [(lo, bv_unsigned sp + -64); (es, es + 904); (A1v, A1v + Z.of_nat (length fs) + 1)]).
    { unfold heapw, ERRST_SIZE. fold es. cbn [blk_addr blk_size fst snd bk1]. unfold n1.
      constructor; [left; cbn; lia|]. constructor; [right; left; cbn; lia|]. constructor; [right; right; cbn; lia| constructor]. }
    rewrite errno_RATP in ERR2.
    destruct (heapw_world H HH _ _ _ _ m3 _ _ lo (bv_unsigned sp + -64) B _ _ _ HP2 SUB2 (or_introl eq_refl) NB1 CW2 AUX2 ERR2 CEIL ltac:(lia) ltac:(lia) MU3 WM3 FW3)
      as (HP3 & CW3 & AUX3 & ERR3 & TR3).
    pose proof (TR3 _ _ FR2 ltac:(lia)) as FR3.
    (* [comment removed for export] *)
    set (n2 := Z.of_nat (length gs) + 1) in *.
    assert (LB1 : lb_bytes (bk1 :: SB ++ LB) = n1 + lb_bytes (SB ++ LB)) by reflexivity.
    eapply (sr_seq H HH).
    { pose proof (cmalloc_spec H HH) as CM. unfold cmalloc_stmt, cmalloc_stmt_at in CM.
      eapply CM with (n := n2) (v := 1) (lo := lo) (B := B) (LB := bk1 :: SB ++ LB) (s := s2') (errv := errv2);
        try reflexivity; try (rewrite unsigned_lit by lia); try eassumption; try (unfold n2; lia);
        try (unfold CMALLOC_STACK, FR_CRYPTO_malloc, RMALLOC_STACK; lia); try (destruct CW3 as (K0 & _); exact K0).
      - rewrite LB1. unfold n1, n2, ERRDEBUG_BYTES in *. lia.
      - cbn [length]. lia.
      - change (lb_big (bk1 :: SB ++ LB)) with (big1 n1 + lb_big (SB ++ LB)). rewrite !big1_small by (unfold n1, n2, BIGB; lia). lia. }
    intros [ms4 mo4] PO. unfold cmalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m4 & errv4 & A2v & junk2 & p2 & s4' &
                    -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & XP4 & RB2 & HP4 & BK2 & MF4 & IM4 & GM4).
    rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST4, XP4 by lia.
    destruct (malloc_world _ _ _ _ m4 _ _ _ CW3 XP4 MF4 SUB2 EM3 ltac:(lia) RBL) as (CW4 & EM4 & TR4).
    pose proof (TR4 _ _ FR3 ltac:(lia)) as FR4.
    set (bk2 := (p2, A2v, n2)) in *.
    pose proof (HH_RHEAP_blocks_nodup H HH _ _ _ HP4) as ND4. cbn [map] in ND4. inversion ND4 as [|z l NI2 ND4']; subst z l.
    assert (SUB4 : forall b, In b LB -> In b (bk2 :: bk1 :: SB ++ LB)) by (intros b Hb; right; apply SUB2; exact Hb).
    assert (NB2 : ~ In bk2 LB) by (intros K; apply NI2; apply SUB2 in K; apply (in_map blk_id) in K; exact K).
    assert (DJ2 : A2v + n2 <= es \/ es + 904 <= A2v).
    { pose proof (HH_RHEAP_blocks_disjoint H HH _ _ _ bk2 (ec_es c) HP4 (or_introl eq_refl) (SUB4 _ I5)) as DJ. cbn [blk_id blk_addr blk_size fst snd bk2] in DJ.
      rewrite Z5 in DJ. fold es in DJ. unfold ERRST_SIZE in DJ.
      assert (NE : p2 <> blk_id (ec_es c)).
      { intros EQ. apply NI2. change (blk_id bk2) with p2. rewrite EQ. right. apply in_map. apply SUBx. exact I5. }
      specialize (DJ NE). lia. }
    unfold rblock_range in RB2.
    replace (Z.to_nat n2) with (S (length gs)) in BK2 by (unfold n2; lia).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL4|
      eapply ed_segC with (lo := lo) (es := es) (E := es_with_slot E (es_top E) (slot_setfile (slot_at E (es_top E)) A1v (Some (p1, n1)) line))
                          (gs := gs) (gsl := gsl) (A2 := A2v) (junk := junk2) (go := Some (p2, n2));
        try eassumption; try reflexivity; try (unfold n2 in *; lia)|].
    intros ms5 (z0 & z1 & z2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & z3 & z4 & z5 & z6 & m5 & -> & MU5 & WM5 & MI5 & ST5 & EM5).
    (* [comment removed for export] *)
    assert (FW5 : Forall (heapw c lo (bv_unsigned sp) bk2) [(lo, bv_unsigned sp); (es, es + 904); (A2v, A2v + Z.of_nat (length gs) + 1)]).
    { unfold heapw, ERRST_SIZE. fold es. cbn [blk_addr blk_size fst snd bk2]. unfold n2.
      constructor; [left; cbn; lia|]. constructor; [right; left; cbn; lia|]. constructor; [right; right; cbn; lia| constructor]. }
    rewrite errno_RATP in ERR4.
    destruct (heapw_world H HH _ _ _ _ m5 _ _ lo (bv_unsigned sp) B _ _ _ HP4 SUB4 (or_introl eq_refl) NB2 CW4 AUX4 ERR4 CEIL ltac:(lia) SPB MU5 WM5 FW5)
      as (HP5 & CW5 & AUX5 & ERR5 & _).
    destruct CW5 as (MF5 & IM5 & GM5 & RL5 & EP5 & CP5).
    (* [comment removed for export] *)
    assert (SL1 : length (es_slots E) = 16%nat) by exact SL.
    rewrite (slot_at_upd E (es_top E) _ SL1 TR) in EM5. rewrite (es_with_slot_twice E (es_top E) _ _ SL1 TR) in EM5.
    change (es_with_slot E (es_top E) (slot_setfunc (slot_setfile (slot_at E (es_top E)) A1v (Some (p1, n1)) line) A2v (Some (p2, n2))))
      with (errst_debug E A1v (Some (p1, n1)) line A2v (Some (p2, n2))) in EM5.
    set (E' := errst_debug E A1v (Some (p1, n1)) line A2v (Some (p2, n2))) in *.
    set (sl' := mkSLOT (sl_flags (slot_at E (es_top E))) (sl_buffer (slot_at E (es_top E))) A1v (Some (p1, n1)) line A2v (Some (p2, n2))).
    assert (PMF : Permutation (bk2 :: bk1 :: SB ++ LB) (blocks_ERRST E' ++ LB)).
    { pose proof (blocks_slots_fill_perm (es_slots E) (Z.to_nat (es_top E)) sl' (slot_clear 0) ltac:(lia)) as PF.
      fold (slot_at E (es_top E)) in PF. unfold blocks_slot at 1 in PF. rewrite FE, GE in PF. specialize (PF eq_refl).
      change (blocks_ERRST E') with (blocks_slots (slot_upd (es_slots E) (Z.to_nat (es_top E)) sl')).
      eapply Permutation_trans; [apply perm_swap|]. change (bk1 :: bk2 :: SB ++ LB) with ((bk1 :: bk2 :: SB) ++ LB).
      apply Permutation_app_tail. exact PF. }
    apply (sr_done H HH). unfold errdebug_post. cbn [cfg_ms cfg_model].
    exists z0, z1, z2, (Z_to_bv 64 A2v), f1, f2, f3, f4, f5, f6, f7, z3, z4, z5, z6, m5, errv4, s4', A1v, A2v, p1, p2. cbv zeta. fold n1 n2 E'.
    split; [reflexivity|]. split; [eapply (mpres_trans H HH); [exact MP2| exact MP4]|].
    split. { unfold c4_frame. cbn [cfg_model]. split; [exact KREL4|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact AUX5|].
             split; [eapply PERM; [exact HP5| exact PMF]|]. tauto. }
    split; [rewrite errno_RATP; exact ERR5|]. split; [unfold rblock_range; exact RB1|]. split; [unfold rblock_range; exact RB2|].
    split; [exact EP5|]. split; [exact CP5|].
    split.
    { apply ERRST_split. split; [exact EM5|].
      apply (ERROWN_upd SB (es_slots E) (Z.to_nat (es_top E)) sl' (es_top E) (es_bottom E) (es_top E) (es_bottom E)); [exact OWN|].
      intros LBx HIN. cbn [sl' sl_file sl_file_o sl_func sl_func_o ofield].
      split; (split; [lia|]; split; [unfold n1, n2; lia|]); apply HIN; cbn [blocks_slot sl' sl_file sl_file_o sl_func sl_func_o blocks_of app]; [left| right; left]; reflexivity. }
    (* [comment removed for export] *)
    set (X := memflag_foot ++ errph_foot (ErrReady c)).
    assert (XE : forall a, blk_addr (ec_es c) <= a < blk_addr (ec_es c) + ERRST_SIZE -> rin_ivs X a).
    { intros a Ha. unfold X. apply rin_ivs_app. right. cbn. left. exact Ha. }
    eapply xpres_trans.
    { eapply xpres_of_munch_gen; [exact MU1| exact WM1|]. intros a Ha [HC _]. unfold RERRNO. cbn. split; [| split; [| exact I]].
      - destruct HC as [K|[[K _]|(b & Hb & Hr)]]; [lia| lia|]. pose proof (RBL b Hb) as RB. unfold rblock_range in RB. lia.
      - destruct HC as [K|[[_ K]|(b & Hb & Hr)]]; [lia| unfold ralloc_static, RERRNO in K; lia|]. pose proof (RBL b Hb) as RB. unfold rblock_range in RB. lia. }
    eapply xpres_trans; [eapply xpres_weaken; [exact XP2| lia| exact SUBx| intros a Ka; unfold X; apply rin_ivs_app; left; exact Ka]|].
    eapply xpres_trans; [eapply (xpres_heapw H HH _ _ LB m2 m2 m3 c lo (bv_unsigned sp + -64) (bv_unsigned sp) X bk1); [exact HP2| exact SUB2| left; reflexivity| exact NB1| exact CEIL| lia| lia| exact XE| exact MU3| exact WM3| exact FW3]|].
    eapply xpres_trans; [eapply xpres_weaken; [exact XP4| lia| exact SUB2| intros a Ka; unfold X; apply rin_ivs_app; left; exact Ka]|].
    eapply (xpres_heapw H HH _ _ LB m4 m4 m5 c lo (bv_unsigned sp) (bv_unsigned sp) X bk2); [exact HP4| exact SUB4| left; reflexivity| exact NB2| exact CEIL| lia| lia| exact XE| exact MU5| exact WM5| exact FW5].
  Qed.
End W.
