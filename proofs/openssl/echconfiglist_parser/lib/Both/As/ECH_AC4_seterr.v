(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCallX AsWalk AsAtomics ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AKit ECH_AsKit ECH_AKitS ECH_AStmt_C0 ECH_AC0_locks ECH_AStmt_C1 ECH_AStmt_C2 ECH_APF_C4 ECH_AStmt_C4 ECH_AC4_rep ECH_AC4_egs.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition VS_RA1 : Z := 0x1f1828.   (* [comment removed for export] *)
Definition VS_NOFMT : Z := 0x1f6780. (* [comment removed for export] *)
Definition VS_CLR : Z := 0x1f19e0.   (* [comment removed for export] *)
Definition VS_FLG : Z := 0x1f6888.   (* [comment removed for export] *)
Definition VS_PACK : Z := 0x1f68b4.  (* [comment removed for export] *)
Definition VS_EXIT : Z := 0x1f697c.  (* [comment removed for export] *)
Definition SE_RA_SM : Z := 0x1f168c. (* [comment removed for export] *)
Definition SE_J1 : Z := 0x1f16bc.    (* [comment removed for export] *)
Definition SE_RA_VS : Z := 0x1f1730. (* [comment removed for export] *)
Definition SE_BODY : Z := 0x1f1644. (* [comment removed for export] *)

Ltac ret_lit RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
Ltac ret_lit_any := match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => ret_lit r end.
Ltac show_goal := match goal with |- evt _ _ (MS ?R _ ?pc _ _ ?mx _) => idtac "PC" pc; idtac R end.
(* [comment removed for export] *)
Ltac acc_now ACC BASE MUS NSW :=
  lazymatch type of BASE with accessible _ ?a ?n =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx a n) by (eapply accessible_across; [exact BASE| exact MUS| exact NSW]) end end.

(* [comment removed for export] *)
Lemma err_pack_reg_a : forall lib reason, 0 < lib < 256 -> 0 < reason < 2^23 ->
  Z.land (Z.lor (Z.shiftr (Z.land (Z.shiftl lib 56) 18446744073709551615) 33) (Z.land reason 8388607)) 4294967295 = ERR_PACK lib reason.
Proof.
  intros lib reason HL HR.
  change 18446744073709551615 with (Z.ones 64). change 8388607 with (Z.ones 23) at 1. change 4294967295 with (Z.ones 32).
  rewrite !Z.land_ones by lia.
  change (2 ^ 23) with 8388608. change (2 ^ 32) with 4294967296. change (2 ^ 64) with 18446744073709551616.
  apply err_pack_reg; assumption.
Qed.

(* [comment removed for export] *)
Ltac aconst_now AC2 MU2 WM2 ACx :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (ACx : ACONST mx)
      by (eapply ACONST_frame; [exact AC2| exact MU2| exact WM2|];
          repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          first [ apply aconst_ok_high; [unfold sh, AIMG_TOP; rewrite ASHADOW_BASE_val; acb; lia| lia]
                | eapply aconst_ok_aapp; [eassumption| lia| unfold AFS_SIZE; lia] ]) end.
(* [comment removed for export] *)
Ltac carry_dj MU WM djtac :=
  lazymatch type of MU with munch ?W ?m0 ?m1 =>
    repeat match goal with
    | H : rw_cells ?segs m0 ?A ?cs |- _ =>
        first [ apply (fun HH => @rw_cells_transport segs W m0 m1 A cs HH MU WM) in H; [| solve [djtac] ]
              | change (stale (rw_cells segs m0 A cs)) in H ]
    end end.

Section S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  Let HSM0 : stack_malloc_0_stmt H := proj1 (proj2 (proj2 HHx)).
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (LF : list fframe) (c : errchain) (E : errst) (exl : ctxinfo) (lib reason lo : Z) (errv : word) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (XS : list (Z * Z)),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ Forall (fs_scratch H LF) XS
      /\ munch ((lo, bv_unsigned sp) :: XS ++ [(ARERRNO, ARERRNO + 4); (blk_addr (ec_es c), blk_addr (ec_es c) + ERRST_SIZE)]) m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv]
      /\ CTX_statics m' exl /\ ERR_statics m' c /\ ERR_chain LB m' c /\ lib_shad (chain_blocks c) m'
      /\ ERRST (blocks_ERRST E) m' (blk_addr (ec_es c)) (errst_seterr E lib reason)
      /\ as_RFS H LF m' /\ ACONST m' /\ arelro_lib m'.

  Lemma avset_null : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (LF : list fframe) (c : errchain) (E : errst) (exl : ctxinfo)
      (lib reason lo : Z) (errv : word),
    a0 = Z_to_bv 64 lib -> a1 = Z_to_bv 64 reason -> a2 = Z_to_bv 64 0 -> 0 < lib < 256 -> lib <> 2 -> 0 < reason < 2^23 ->
    tp = Z_to_bv 64 ATP -> rw_cells asegs m (errno_addr tp) [C4 errv] ->
    CTX_statics m exl -> ERR_statics m c -> ERR_chain LB m c -> chain_below c aceil -> chain_apl H c -> chain_sep c -> lib_shad (chain_blocks c) m ->
    ERRST (blocks_ERRST E) m (blk_addr (ec_es c)) E ->
    ACONST m -> arelro_lib m -> as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> athr_cells m -> bv_unsigned sp mod 16 = 0 ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - (FR_ERR_vset_error + EGS_STACK) -> mem_inv asegs m ->
    bv_unsigned ra mod 2 = 0 ->
    evt asegs (vset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB LF c E exl lib reason lo errv m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 P_ERR_vset_error) fc None m (seg_rom asegs)).
  Proof.
    intros until errv. intros A0 A1 A2 LIBR LIB2 REAS TP ERR CS ES EC CB CA CSEP LS EST AC RL RFS LFN THR SPA ST CEIL LO MI RAE. subst a0 a1 a2.
    unfold P_ERR_vset_error, FR_ERR_vset_error, EGS_STACK, FR_ossl_err_get_state_int, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, AFS_STACK in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    subst tp. unfold ATP in *. rewrite (unsigned_lit 12459152) in ERR by lia. change (12459152 + -164) with 12458988 in ERR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ACONST_shbase m AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    (* [comment removed for export] *)
    pose proof EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CA)))) as R5. cbv beta in R5. rewrite Z5 in R5.
    pose proof R5 as (E1 & E2 & E3 & E4 & E5 & E6 & E7). unfold ERRST_SIZE in *.
    set (es := blk_addr (ec_es c)) in *.
    pose proof (rw_cells_bound _ _ _ _ ERR) as ERRB. cbn [cells_size csize Nat.add length] in ERRB.
    (* [comment removed for export] *)
    carve_frame 128%nat ST.
    bgo. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      change (munch ((lo, bv_unsigned sp) :: [] ++ []) m m1) in MU;
      pose proof (lib4_foot H HH LF m LB lo (bv_unsigned sp) [] [] m m1 c exl RFS (Forall_nil _) (Forall_nil _) CEIL CA MU WM CS ES EC LS) as (CS1 & ES1 & EC1 & LS1);
      assert (AC1 : ACONST m1) by (eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]);
      assert (RL1 : arelro_lib m1) by (eapply arelro_across; [exact RL| exact MU| apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]]);
      assert (RFS1 : as_RFS H LF m1) by (eapply (RFS_stack H HH); [exact RFS| exact MU| exact WM| exact CEIL]);
      assert (THR1 : athr_cells m1) by (eapply athr_cells_frame; [exact THR| exact MU| exact WM| apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]]) end.
    eapply evt_cut.
    { eapply (aegs_ready_spec H HHx) with (lo := lo) (c := c) (exl := exl) (LB := LB) (save := 1) (errv := errv) (LF := LF);
        [ reflexivity| lia| reflexivity| rewrite unsigned_lit by lia; exact ERR| exact CS1| exact ES1| exact EC1| exact CB| exact CA| exact LS1
        | exact AC1| exact RL1| exact RFS1| exact LFN| exact THR1
        | rewrite unsigned_lit by lia; clear - SPA SPR; Z.div_mod_to_equations; lia
        | rewrite unsigned_lit by lia; exact ST| exact CEIL
        | rewrite unsigned_lit by lia; unfold EGS_STACK, FR_ossl_err_get_state_int, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, AFS_STACK; lia
        | exact MI| rewrite unsigned_lit by lia; reflexivity ]. }
    clear CS1 ES1 EC1 LS1 AC1 RL1 RFS1 THR1 THR.
    intros ms' PO. unfold egsr_post in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & XS & -> & FXS & MU' & WM' & MI2 & ST2 & ERR2 & CS2 & ES2 & EC2 & LS2 & RFS2 & AC2 & RL2).
    ret_lit_any. rewrite (unsigned_lit (bv_unsigned sp + -128)) in MU' by lia. rewrite (unsigned_lit (bv_unsigned sp + -128)) in ST2 by lia.
    rewrite (unsigned_lit 12459152) in ERR2 by lia. change (12459152 + -164) with 12458988 in ERR2.
    lazymatch type of MU' with munch _ ?m1 _ => change (munch ((lo, bv_unsigned sp + -128) :: XS ++ ERRNO_X) m1 m2) in MU' end.
    (* [comment removed for export] *)
    pose proof (errno_lit) as FLIT. pose proof (low_lit_ok _ FLIT) as FLIT'.
    lazymatch type of FR with rw_cells _ ?m1 ?A ?cs =>
      assert (FR2 : rw_cells asegs m2 A cs)
        by (eapply rw_cells_transport; [exact FR| exact MU'| exact WM'|]; eapply (dj_foot_hi H HH); [exact RFS| exact FXS| exact FLIT'| exact CEIL| lia| lia]) end.
    lazymatch type of MU' with munch _ ?m1 _ =>
      assert (MU2 : munch ((lo, bv_unsigned sp) :: XS ++ ERRNO_X) m m2) by (eapply munch_stack_then; [exact MU| exact MU'| lia]);
      pose proof (wmono_trans _ _ _ _ WM WM') as WM2 end.
    assert (EST2 : ERRST (blocks_ERRST E) m2 es E).
    { apply ERRST_split in EST. destruct EST as [ESM EOW]. apply ERRST_split. split; [| exact EOW].
      eapply ERRSTm_munch; [exact ESM| exact MU2| exact WM2|]. unfold ERRST_SIZE.
      eapply (dj_foot_blk H HH); [exact RFS| exact FXS| exact FLIT'| exact CEIL| exact R5| lia| lia|].
      apply Forall_cons; [| apply Forall_nil]. intros [P1 _]. exfalso. cbn in P1. unfold AIMG_TOP, ARERRNO, ATP in P1. lia. }
    clear FR MU WM MU' WM' MI ST EST ERR. rename MI2 into MI. rename ST2 into ST.
    (* [comment removed for export] *)
    assert (ACC2 : accessible m2 es 904).
    { pose proof (proj1 (Forall_forall _ _) LS2 _ ltac:(unfold chain_blocks; cbn; do 3 right; left; reflexivity)) as AD. cbv beta in AD.
      fold es in AD. rewrite Z5 in AD. pose proof (aapp_bounds _ _ E7 ltac:(lia)) as (_ & _ & T1 & _).
      eapply addressable_accessible; [exact AD| lia| lia| lia]. }
    fold es.
    (* [comment removed for export] *)
    unfold ERRST in EST2. fold es in EST2.
    destruct EST2 as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & OWN).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    set (top := es_top E) in *. arr_lens SL.
    (* [comment removed for export] *)
    assert (MU3 : munch ((lo, bv_unsigned sp) :: (ARERRNO, ARERRNO + 4) :: (es, es + 904) :: XS) m m2).
    { eapply munch_mono; [exact MU2|]. intros a K. cbn in K |- *. destruct K as (K1 & K2 & K3 & K4). split; [exact K1|].
      apply (proj2 (outside_app _ _ _)). split; [exact K4| cbn; split; [exact K2| exact I]]. }
    clear MU2. unfold ARERRNO, ATP in MU3. unfold AIMG_TOP in E4.
    pose proof (munch_refl [(lo, bv_unsigned sp); (es, es + 904)] m2) as MUS. pose proof (wmono_refl asegs m2) as WMS.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp); (es, es + 904)]).
    { apply Forall_cons; [cbn [fst snd]; unfold AHI_LO; lia|]. apply Forall_cons; [cbn [fst snd]; exact (aapp_not_shadowland _ _ E7)| apply Forall_nil]. }
    assert (ALIT : Forall (lit_ok) [(es, es + 904)]).
    { apply Forall_cons; [| apply Forall_nil]. right. unfold app_ok. cbn [fst snd]. replace (es + 904 - es) with 904 by lia. unfold AIMG_TOP. split; [lia| split; [lia| exact E7]]. }
    (* [comment removed for export] *)
    bgo.
    (* [comment removed for export] *)
    acc_now ACC3 ACC2 MUS NSW. sh_align (es + 896). ck8_check ACC3 (es + 896). clear ACC3.
    bgo. acc_now ACC3 ACC2 MUS NSW. sh_align (es + 512 + top * 4). ck8_check ACC3 (es + 512 + top * 4). clear ACC3.
    pose proof (zero16_byte_m _ _ top F6 TR) as RD. step. clear RD. nrm. unfold wz.
    (* [comment removed for export] *)
    bgo. acc_now ACC3 ACC2 MUS NSW. sh_align (es + 256 + top * 8). ck8_check ACC3 (es + 256 + top * 8). clear ACC3.
    bgo. arr_store64 F4 top (wz 0). rewrite upd_zero16 in F4 by lia.
    (* [comment removed for export] *)
    bgo. acc_now ACC3 ACC2 MUS NSW. sh_align (es + top * 8 + 384). ck8_check ACC3 (es + top * 8 + 384). clear ACC3.
    bgo. arr_store64 F5 top (wz 0). rewrite upd_zero16 in F5 by lia.
    (* [comment removed for export] *)
    bgo. acc_now ACC3 ACC2 MUS NSW. sh_align (es + 512 + top * 4). ck8_check ACC3 (es + 512 + top * 4). clear ACC3.
    bgo. arr_store32 F6 top (wz 0). rewrite upd_zero16 in F6 by lia.
    (* [comment removed for export] *)
    bgo. acc_now ACC3 ACC2 MUS NSW. sh_align (es + 896). ck8_check ACC3 (es + 896). clear ACC3.
    bgo. rewrite (unsigned_lit (es + 128)) by lia. unfold wz. rewrite (unsigned_lit top) by lia. ub_res. bgo.
    (* [comment removed for export] *)
    rewrite (unsigned_lit (es + 128 + top * 8)) by lia.
    acc_now ACC3 ACC2 MUS NSW. sh_align (es + top * 8 + 128). ck8_check ACC3 (es + top * 8 + 128). clear ACC3.
    assert (PKV : Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl lib 56))) 33))) (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl reason 41))) 41))) = ERR_PACK lib reason).
    { assert (EP : ERR_PACK lib reason = Z.lor (lib * 2 ^ 23) reason).
      { rewrite <- (err_pack_reg lib reason) by lia.
        rewrite (Z.shiftl_mul_pow2 lib 56) by lia. rewrite (Z.mod_small (lib * 2 ^ 56)) by lia. rewrite Z.shiftr_div_pow2 by lia.
        replace (2 ^ 56) with (2 ^ 23 * 2 ^ 33) by reflexivity. rewrite Z.mul_assoc, Z.div_mul by lia.
        rewrite (Z.mod_small reason) by lia. apply Z.mod_small. pose proof (lor_lt_pow2 (lib * 2 ^ 23) reason 31 ltac:(lia) ltac:(lia)). lia. }
      rewrite EP. rewrite (Z.shiftl_mul_pow2 lib 56), (Z.shiftl_mul_pow2 reason 41) by lia.
      rewrite (unsigned_lit (lib * 2 ^ 56)), (unsigned_lit (reason * 2 ^ 41)) by lia. rewrite !Z.shiftr_div_pow2 by lia.
      rewrite Z.div_mul by lia. replace (2 ^ 56) with (2 ^ 23 * 2 ^ 33) by reflexivity. rewrite Z.mul_assoc, Z.div_mul by lia.
      rewrite !unsigned_lit by lia. reflexivity. }
    rewrite PKV. clear PKV.
    bgo. pose proof (err_pack_range lib reason ltac:(lia) ltac:(lia)) as EPR.
    rewrite (unsigned_lit (ERR_PACK lib reason)) by lia. rewrite (Z.shiftl_mul_pow2 (ERR_PACK lib reason) 32) by lia.
    rewrite (unsigned_lit (ERR_PACK lib reason * 2 ^ 32)) by lia. rewrite (Z.shiftr_div_pow2 (ERR_PACK lib reason * 2 ^ 32) 32) by lia.
    rewrite (Z.div_mul (ERR_PACK lib reason) (2 ^ 32)) by lia. clear EPR.
    arr_store64 F3 top (wz (ERR_PACK lib reason)).
    (* [comment removed for export] *)
    bgo. step.
    release_frame FR2 ST (bv_unsigned sp).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      change (munch ((lo, bv_unsigned sp) :: [] ++ [(es, es + 904)]) m2 mq) in MUS;
      pose proof (CTX_statics_foot H HH LF m2 lo _ [] _ m2 mq exl RFS2 (Forall_nil _) ALIT CEIL MUS WMS CS2) as CSf;
      pose proof (ERR_statics_foot H HH LF m2 lo _ [] _ m2 mq c RFS2 (Forall_nil _) ALIT CEIL MUS WMS ES2) as ESf;
      assert (ECf : ERR_chain LB mq c)
        by (eapply (ERR_chain_foot H HH); [exact RFS2| apply Forall_nil| exact ALIT| exact CEIL| exact CA| exact CSEP| | exact MUS| exact WMS| exact EC2];
            apply Forall_cons; [| apply Forall_nil]; intros _; cbn [fst snd]; fold es; unfold ERRST_SIZE; lia);
      assert (LSf : lib_shad (chain_blocks c) mq)
        by (eapply (lib_shad_foot H HH); [exact RFS2| apply Forall_nil| exact ALIT| exact CEIL| exact CA| exact LS2| exact MUS| exact WMS]);
      assert (RFSf : as_RFS H LF mq)
        by (eapply (ah_RFS_frame H HH); [exact RFS2| exact MUS| exact WMS|];
            pose proof (RFS_fsb H HH _ _ RFS2) as (Q1 & Q2 & Q3 & Q4); unfold AFS_SIZE, AIMG_TOP in Q1, Q2;
            apply Forall_cons; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE; lia|];
            apply Forall_cons; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; lia| apply Forall_nil]);
      assert (ACf : ACONST mq)
        by (eapply ACONST_frame; [exact AC2| exact MUS| exact WMS|];
            apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; [unfold sh, AIMG_TOP; rewrite ASHADOW_BASE_val; lia| lia]|];
            apply Forall_cons; [eapply aconst_ok_aapp; [exact E7| lia| unfold AFS_SIZE; lia]| apply Forall_nil]);
      assert (RLf : arelro_lib mq)
        by (eapply arelro_across; [exact RL2| exact MUS|]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia);
      assert (MUf : munch ((lo, bv_unsigned sp) :: XS ++ [(ARERRNO, ARERRNO + 4); (es, es + ERRST_SIZE)]) m mq)
        by (eapply munch_mono; [exact MU3|]; intros a K; unfold ARERRNO, ATP, ERRST_SIZE in K; cbn in K |- *; destruct K as [K1 K2];
            apply (proj1 (outside_app _ _ _)) in K2; destruct K2 as (K2 & K3 & K4 & _); repeat split; assumption) end.
    unfold vset_post. finish; [exact FXS| exact MUf|].
    (* [comment removed for export] *)
    assert (TN : (Z.to_nat top < length (es_slots E))%nat) by lia.
    unfold ERRST, errst_seterr. fold es. fold top. cbn [es_slots es_top es_bottom].
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP.
    rewrite !map_slot_upd by exact TN. cbn [sl_flags sl_buffer sl_file sl_line sl_func].
    rewrite (upd_same (map (fun s => wz (sl_flags s)) (es_slots E))), (upd_same (map (fun s => wz (sl_file s)) (es_slots E))),
            (upd_same (map (fun s => wz (sl_line s)) (es_slots E))), (upd_same (map (fun s => wz (sl_func s)) (es_slots E)))
      by (apply slot_nth; [exact SL| lia]).
    split; [rewrite slot_upd_length by exact TN; exact SL|]. split; [exact TR|]. split; [exact BR|].
    repeat match goal with |- _ /\ _ => split end; try assumption.
    apply own_slot_upd; [exact OWN|].
    pose proof (slot_at_own _ E top OWN SL TR) as (O1 & O2 & O3 & O4 & O5). cbn [sl_flags sl_buffer sl_file sl_file_o sl_line sl_func sl_func_o].
    pose proof (err_pack_range lib reason LIBR REAS). repeat split; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
    Lemma rw_cells_nil : forall m A, 0 <= A <= 2^64 -> rw_cells asegs m A [].
  Proof.
    intros m A HA. split; [split; [exact I|]|].
    - unfold bytes_at. cbn [length cells_bytes]. repeat split; try lia.
    - unfold wr_at. cbn [cells_size]. repeat split; try lia.
  Qed.

  Lemma se_tail : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m m1 : mem) (s : as_St H) (LB : list block) (LF : list fframe) (c : errchain) (E : errst) (exl : ctxinfo)
      (lib reason lo sp1 : Z) (errv : word) (dj : list byte) (gapc : list cell) (jt : list byte),
    0 < lib < 256 -> lib <> 2 -> 0 < reason < 2^23 -> tp = Z_to_bv 64 ATP ->
    rw_cells asegs m (errno_addr tp) [C4 errv] ->
    CTX_statics m exl -> ERR_statics m c -> ERR_chain LB m c -> chain_below c aceil -> chain_sep c -> lib_shad (chain_blocks c) m ->
    ERRST (blocks_ERRST E) m (blk_addr (ec_es c)) E ->
    as_RHEAP H s LB m -> ACONST m -> arelro_lib m -> as_RFS H LF m -> (length LF + 2 <= AFS_MAXLIVE)%nat ->
    munch [(lo, bv_unsigned sp)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    rw_cells asegs m1 (bv_unsigned sp + -120) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra; CB 48 jt] ->
    rw_cells asegs m1 sp1 [CB 8 dj] -> rw_cells asegs m1 (sp1 + 8) gapc -> sp1 + 8 + Z.of_nat (cells_size gapc) = bv_unsigned sp + -120 ->
    bv_unsigned sp + -144 <= sp1 -> sp1 mod 32 = 0 ->
    stk asegs m1 lo sp1 -> aceil <= lo -> lo <= bv_unsigned sp - ERRSETERR_STACK -> bv_unsigned ra mod 2 = 0 ->
    evt asegs (errseterr_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF c E exl lib reason lo errv m)
      (MS (mkR ra (Z_to_bv 64 sp1) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -48)) s1 (Z_to_bv 64 lib) (Z_to_bv 64 reason) (Z_to_bv 64 0) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SE_BODY) fc None m1 (seg_rom asegs)).
  Proof.
    intros until errv. intros dj gapc jt LIBR LIB2 REAS TP ERR CS ES EC CB CSEP LS EST HP AC RL RFS LFN MU WM MI FR DS GAP SZ SP1 SPA ST CEIL LO RAE.
    unfold ERRSETERR_STACK, FR_ERR_set_error, FR_ERR_vset_error, EGS_STACK, FR_ossl_err_get_state_int, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, AFS_STACK, SE_BODY in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    subst tp. unfold ATP in *. rewrite (unsigned_lit 12459152) in ERR by lia. change (12459152 + -164) with 12458988 in ERR.
    pose proof (rw_cells_bound _ _ _ _ GAP) as GB. pose proof (rw_cells_bound _ _ _ _ ERR) as ERRB. cbn [cells_size csize Nat.add length] in ERRB.
    (* [comment removed for export] *)
    pose proof (ACONST_shbase m AC) as [GSB SHB0]. pose proof (ACONST_uar m AC) as [GUA UAR].
    unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_UAR, AUAR_CELL, wz in GSB, SHB0, GUA, UAR. rewrite ASHADOW_BASE_val in SHB0.
    assert (GFD : rw_cells asegs m 0x5e8ae8 [C8 (wz P_ERR_set_error)])
      by (apply relro_cell; [exact RL| lia| cbn; lia| cbn; tauto| vm_compute; reflexivity]).
    unfold P_ERR_set_error, wz in GFD.
    pose proof (RFS_fsb H HH _ _ RFS) as (F1 & F2 & F3 & F4). pose proof (aapp_not_shadowland _ _ F4) as F5.
    unfold AFS_SIZE, ALOWSH_LO, AHI_LO, AIMG_TOP in F1, F2, F5.
    (* [comment removed for export] *)
    pose proof (chain_apl_of_RHEAP H HH _ _ _ _ _ HP EC (fun b Hb => Hb)) as CA.
    pose proof EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CA)))) as R5. cbv beta in R5. rewrite Z5 in R5.
    pose proof R5 as (E1 & E2 & E3 & E4 & E5 & E6 & E7). unfold ERRST_SIZE in *. unfold AIMG_TOP in E4.
    set (es := blk_addr (ec_es c)) in *.
    pose proof (ah_thr H HH _ _ _ HP) as THR.
    carry MU WM.
    (* [comment removed for export] *)
    step. step. step. step. step. step. st1. st1. st1. st1. st1. change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
    st1. st1. st1. st1. step. try if_false. step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (RFS1 : as_RFS H LF mx) by (eapply (RFS_stack H HH); [exact RFS| exact MU| exact WM| exact CEIL]);
      assert (THR1 : athr_cells mx) by (eapply athr_cells_frame; [exact THR| exact MU| exact WM| apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]]);
      assert (AC1 : ACONST mx) by (eapply ACONST_stack_frame; [exact AC| exact MU| exact WM| exact CEIL]) end.
    eapply evt_cut.
    { eapply HSM0 with (lo := lo); [exact RFS1| clear - LFN; lia| rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; unfold AFS_STACK; lia
                                   | exact MI| reflexivity| exact AC1| exact THR1]. }
    clear RFS1 THR1 AC1.
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
    assert (SHES : shf + 8 <= es \/ es + 904 <= shf)
      by (subst shf; pose proof (aapp_disjoint_sh es 904 ff 64 E7 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as K; unfold nsh in K; change ((64 + 7) / 8) with 8 in K; lia).
    carry MU' WM'.
    (* [comment removed for export] *)
    assert (MUt : munch [(lo, bv_unsigned sp); (as_FSB H, as_FSB H + 4096); (fp, fp + 1); (ff, ff + 64); (shf, shf + 8)] m m2).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU']];
        intros xa Hxa; unfold outside in Hxa |- *; cbn in Hxa |- *; lia. }
    pose proof (wmono_trans _ _ _ _ WM WM') as WMt. clear MU WM MU' WM' MI ST. rename MI' into MI. rename ST' into ST. rename MUt into MU. rename WMt into WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (ff, ff + 64); (shf, shf + 8)] m2) as MUr. pose proof (wmono_refl asegs m2) as WMr.
    pose proof (fs_scratch_of_fresh H _ _ _ _ FRESH) as FSX. change (fsz 0) with 64 in FSX. change (fshn 0) with 8 in FSX. fold shf in FSX. unfold AFS_FLAGS in FSX.
    (* [comment removed for export] *)
    step. step. step. step. if_cases K0; zify_cond K0; [| kill K0]. clear K0.
    (* [comment removed for export] *)
    st1. step. step. zstep. zstep.
    replace (Z.shiftr ff 3 + 2147450880) with shf by (subst shf; rewrite <- (sh_shiftr ff) by lia; rewrite ASHADOW_BASE_val; reflexivity).
    step. step. st1. step.
    (* [comment removed for export] *)
    st1. st1. st1. step. st1. st1. st1. st1. step. st1. st1. st1. st1.
    (* [comment removed for export] *)
    zstep. st1. zstep. step. step. step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      change (munch ((lo, bv_unsigned sp) :: [(as_FSB H, as_FSB H + 4096); (fp, fp + 1); (ff, ff + 64); (shf, shf + 8)] ++ []) m mx) in MU;
      pose proof (lib4_foot H HH LF m LB lo (bv_unsigned sp) _ [] m mx c exl RFS FSX (Forall_nil _) CEIL CA MU WM CS ES EC LS) as (CS3 & ES3 & EC3 & LS3);
      assert (EST3 : ERRST (blocks_ERRST E) mx es E)
        by (apply ERRST_split in EST; destruct EST as [ESM EOW]; apply ERRST_split; split; [| exact EOW];
            eapply ERRSTm_munch; [exact ESM| exact MU| exact WM|]; unfold ERRST_SIZE;
            eapply (dj_foot_blk H HH); [exact RFS| exact FSX| apply Forall_nil| exact CEIL| exact R5| lia| lia| apply Forall_nil]);
      assert (HP3 : as_RHEAP H s LB mx)
        by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU| exact WM|]; rewrite app_nil_r;
            apply Forall_cons; [left; cbn [fst snd]; lia|]; eapply (fs_scratch_write_ok_Forall H); exact FSX);
      pose proof (ah_thr H HH _ _ _ HP3) as THR3;
      assert (RL3 : arelro_lib mx) by (eapply arelro_across; [exact RL| exact MU|]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia);
      assert (RFS3 : as_RFS H ((0, ff, fp) :: LF) mx)
        by (eapply (ah_RFS_frame H HH); [exact RFS2| exact MUr| exact WMr|];
            apply Forall_cons; [unfold afs_write_ok; left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; lia|];
            apply Forall_cons; [unfold afs_write_ok; right; exists (0, ff, fp); split; [left; reflexivity| cbn [fst snd ff_addr ff_class blk_addr]; change (fsz 0) with 64; lia]|];
            apply Forall_cons; [unfold afs_write_ok; left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; lia|];
            apply Forall_nil) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (AC3 : ACONST mx) end.
    { eapply ACONST_frame; [exact AC2| exact MUr| exact WMr|].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - apply aconst_ok_high; [unfold sh, AIMG_TOP; rewrite ASHADOW_BASE_val; acb; lia| lia].
      - eapply aconst_ok_aapp; [exact F4| lia| unfold AFS_SIZE; lia].
      - apply aconst_ok_high; [unfold sh, AIMG_TOP; rewrite ASHADOW_BASE_val; acb; lia| lia]. }
    rewrite app_nil_r in MU.
    eapply evt_cut.
    { eapply avset_null with (lo := lo) (c := c) (exl := exl) (LB := LB) (E := E) (LF := (0, ff, fp) :: LF) (lib := lib) (reason := reason) (errv := errv);
        [ reflexivity| reflexivity| reflexivity| exact LIBR| exact LIB2| exact REAS| reflexivity
        | rewrite unsigned_lit by lia; exact ERR| exact CS3| exact ES3| exact EC3| exact CB| exact CA| exact CSEP| exact LS3| exact EST3
        | exact AC3| exact RL3| exact RFS3| cbn [length]; clear - LFN; lia| exact THR3
        | rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia
        | rewrite unsigned_lit by lia; exact ST| exact CEIL
        | rewrite unsigned_lit by lia; unfold FR_ERR_vset_error, EGS_STACK, FR_ossl_err_get_state_int, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, AFS_STACK; lia
        | exact MI| rewrite unsigned_lit by lia; reflexivity ]. }
    clear CS3 ES3 EC3 LS3 EST3 HP3 THR3 RL3 AC3.
    intros ms' PO. unfold vset_post in PO.
    destruct PO as (v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m4 & XS1 & -> & FXS1 & MUv & WMv & MI4 & ST4 & ERR4 & CS4 & ES4 & EC4 & LS4 & EST4 & RFS4 & AC4 & RL4).
    ret_lit_any. rewrite (unsigned_lit sp1) in MUv by lia. rewrite (unsigned_lit sp1) in ST4 by lia.
    rewrite (unsigned_lit 12459152) in ERR4 by lia. change (12459152 + -164) with 12458988 in ERR4. unfold ERRST_SIZE in MUv. fold es in MUv, EST4.
    clear ERR MI ST. rename MI4 into MI. rename ST4 into ST.
    (* [comment removed for export] *)
    assert (FLIT2 : Forall (lit_ok) [(ARERRNO, ARERRNO + 4); (es, es + 904)]).
    { apply Forall_cons; [left; apply errno_low_ok|]. apply Forall_cons; [| apply Forall_nil].
      right. unfold app_ok. cbn [fst snd]. replace (es + 904 - es) with 904 by lia. unfold AIMG_TOP. split; [lia| split; [lia| exact E7]]. }
    unfold AFS_SIZE in E6.
    carry_dj MUv WMv ltac:(first
      [ eapply (dj_foot_hi H HH); [exact RFS3| exact FXS1| exact FLIT2| exact CEIL| lia| lia]
      | eapply (dj_foot_img H HH); [exact RFS3| exact FXS1| exact FLIT2| exact CEIL| cbn; lia
                                  | apply Forall_cons; [intros _; cbn; unfold ARERRNO, ATP; lia| apply Forall_cons; [intros _; cbn; lia| apply Forall_nil]]]
      | apply dj_cons; [cbn; lia|]; apply dj_app;
        [ first [ eapply (dj_scratch_live H HH); [exact RFS3| left; reflexivity| exact FXS1| cbn; lia| cbn; unfold fsz; lia]
                | eapply (dj_scratch_live_sh H HH); [exact RFS3| left; reflexivity| exact FXS1| cbn; lia| cbn; unfold fshn; lia]
                | eapply (dj_scratch_live_flag H HH); [exact RFS3| left; reflexivity| exact FXS1] ]
        | unfold ARERRNO, ATP; cbn; lia ] ]).
    (* [comment removed for export] *)
    assert (MUT : munch ((lo, bv_unsigned sp) :: (as_FSB H, as_FSB H + 4096) :: (fp, fp + 1) :: (ff, ff + 64) :: (shf, shf + 8)
                         :: (12459152 - 164, 12459152 - 164 + 4) :: (es, es + 904) :: XS1) m m4).
    { eapply munch_cons_compose; [exact MU| exact MUv| |].
      - intros a K. cbn in K |- *. tauto.
      - intros a K. cbn in K |- *. destruct K as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8). split; [clear - K1 SZ; lia|].
        apply (proj2 (outside_app _ _ _)). split; [exact K8|]. cbn. unfold ARERRNO, ATP. tauto. }
    clear MU MUv MUr WMr. pose proof (wmono_trans _ _ _ _ WM WMv) as WMT. clear WM WMv.
    pose proof (munch_refl [(lo, bv_unsigned sp); (fp, fp + 1); (ff, ff + 64); (shf, shf + 8)] m4) as MU2. pose proof (wmono_refl asegs m4) as WM2.
    (* [comment removed for export] *)
    step. st1. step. step. st1. step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    step. do 8 st1. st1. st1. step.
    (* [comment removed for export] *)
    zstep. do 9 st1. step. step.
    release_frame DS ST (sp1 + 8). release_frame GAP ST (bv_unsigned sp + -120). release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    assert (FXA : Forall (fs_scratch H LF) ([(as_FSB H, as_FSB H + 4096); (fp, fp + 1); (ff, ff + 64); (shf, shf + 8)] ++ XS1)).
    { apply Forall_app. split; [exact FSX| eapply fs_scratch_mono_Forall; exact FXS1]. }
    assert (FLIT3 : Forall lit_ok [(ARERRNO, ARERRNO + 4); (es, es + ERRST_SIZE)]) by (unfold ERRST_SIZE; exact FLIT2).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      assert (MUf : munch ((lo, bv_unsigned sp) :: ([(as_FSB H, as_FSB H + 4096); (fp, fp + 1); (ff, ff + 64); (shf, shf + 8)] ++ XS1)
                           ++ [(ARERRNO, ARERRNO + 4); (es, es + ERRST_SIZE)]) m mq)
        by (eapply munch_mono; [exact MUT|]; intros a K; unfold ARERRNO, ATP, ERRST_SIZE in K; cbn in K |- *;
            destruct K as (K1 & K2 & K3 & K4 & K5 & K6); apply (proj1 (outside_app _ _ _)) in K6; destruct K6 as (K6 & K7 & K8 & _);
            repeat split; assumption);
      pose proof (CTX_statics_foot H HH LF m lo _ _ _ m mq exl RFS FXA FLIT3 CEIL MUf WMT CS) as CSf;
      pose proof (ERR_statics_foot H HH LF m lo _ _ _ m mq c RFS FXA FLIT3 CEIL MUf WMT ES) as ESf;
      assert (ECf : ERR_chain LB mq c)
        by (eapply (ERR_chain_foot H HH); [exact RFS| exact FXA| exact FLIT3| exact CEIL| exact CA| exact CSEP| | exact MUf| exact WMT| exact EC];
            apply Forall_cons; [intros [Q1 _]; exfalso; cbn in Q1; unfold AIMG_TOP, ARERRNO, ATP in Q1; lia|];
            apply Forall_cons; [| apply Forall_nil]; intros _; cbn [fst snd]; fold es; lia);
      assert (LSf : lib_shad (chain_blocks c) mq)
        by (eapply (lib_shad_foot H HH); [exact RFS| exact FXA| exact FLIT3| exact CEIL| exact CA| exact LS| exact MUf| exact WMT]);
      assert (ESTf : ERRST (blocks_ERRST E) mq es (errst_seterr E lib reason))
        by (apply ERRST_split in EST4; destruct EST4 as [ESM EOW]; apply ERRST_split; split; [| exact EOW];
            eapply ERRSTm_munch; [exact ESM| exact MU2| exact WM2|]; unfold ERRST_SIZE; cbn; lia);
      assert (HPf : as_RHEAP H s LB mq)
        by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MUf| exact WMT|];
            apply Forall_cons; [left; cbn [fst snd]; lia|]; apply Forall_app; split; [eapply (fs_scratch_write_ok_Forall H); exact FXA|];
            apply Forall_cons; [right; left; unfold aimg_client_w, ARERRNO, ATLS_PRIV_LO, ATP; cbn [fst snd]; lia|];
            apply Forall_cons; [| apply Forall_nil]; right; right; left; exists (ec_es c); split; [exact I5| cbn [fst snd]; fold es; rewrite Z5; unfold ERRST_SIZE; lia]);
      assert (RFSf : as_RFS H LF mq)
        by (rewrite <- (lf_remove_head 0 ff fp LF); eapply (ah_release H HH); [exact RFS4| left; reflexivity| exact MU2| exact WM2| |];
            [ apply Forall_cons; [left; unfold afs_write_ok; left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; lia|];
              apply Forall_cons; [right; cbn [fst snd]; split; reflexivity|];
              apply Forall_cons; [left; unfold afs_write_ok; right; exists (0, ff, fp); split; [left; reflexivity| cbn [fst snd ff_addr ff_class blk_addr]; change (fsz 0) with 64; lia]|];
              apply Forall_cons; [left; unfold afs_write_ok; left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; lia|];
              apply Forall_nil
            | lazymatch goal with |- mrd _ ?mx _ = _ => match goal with Hc : rw_cells asegs mx fp _ |- _ => exact (rw_cells_C1_mrd _ _ _ _ _ Hc) end end ]);
      assert (ACf : ACONST mq)
        by (eapply ACONST_frame; [exact AC4| exact MU2| exact WM2|];
            apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; [unfold sh, AIMG_TOP; rewrite ASHADOW_BASE_val; lia| lia]|];
            apply Forall_cons; [eapply aconst_ok_aapp; [exact F4| cbn [fst snd]; lia| cbn [fst snd]; unfold AFS_SIZE; lia]|];
            apply Forall_cons; [eapply aconst_ok_aapp; [exact F4| cbn [fst snd]; lia| cbn [fst snd]; unfold AFS_SIZE; lia]|];
            apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; [unfold sh, AIMG_TOP; rewrite ASHADOW_BASE_val; lia| lia]| apply Forall_nil]);
      assert (RLf : arelro_lib mq)
        by (eapply arelro_across; [exact RL4| exact MU2|]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia) end.
    unfold errseterr_post. finish; [exact FXA| exact MUf].
  Qed.

  (* [comment removed for export] *)
  Lemma aerrseterr_spec : errseterr_stmt H.
  Proof.
    unfold errseterr_stmt. intros until errv. intros A0 A1 A2 LIBR LIB2 REAS TP ERR CS ES EC CBL CSEP LS EST HP AC RL RFS LFN SPA ST CEIL LO MI RAE. subst a0 a1 a2.
    unfold P_ERR_set_error in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (LO' : lo <= bv_unsigned sp - 1328)
      by (revert LO; unfold ERRSETERR_STACK, FR_ERR_set_error, FR_ERR_vset_error, EGS_STACK, FR_ossl_err_get_state_int, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, AFS_STACK;
          clear; intros LO; lia).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ERR as ERR0. change (id (rw_cells asegs m (errno_addr tp) [C4 errv])) in ERR0.
    carve_frame 128%nat ST.
    do 12 st1.
    (* [comment removed for export] *)
    zstep. rewrite land_align32 by lia.
    assert (CASES : (bv_unsigned sp + -128) mod 32 = 0 \/ (bv_unsigned sp + -128) mod 32 = 16) by (clear - SPA SPR; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    change (C8 (Z_to_bv 64 0) :: ?rest) with ([C8 (Z_to_bv 64 0)] ++ rest) in FR.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in FR. destruct FR as [C0 FR]. cbn [cells_size csize Nat.add] in FR.
    replace (bv_unsigned sp + -128 + Z.of_nat 8) with (bv_unsigned sp + -120) in FR by lia.
    pose proof (rw_cells_merge asegs _ _ [] [C8 (Z_to_bv 64 0)] [] C0) as C0'. cbn [app cells_size csize cells_bytes cbytes Nat.add] in C0'. clear C0.
    destruct CASES as [CSA|CSB].
    - (* [comment removed for export] *)
      rewrite CSA, Z.sub_0_r.
      eapply se_tail with (gapc := []); try exact ERR0; try eassumption; try reflexivity.
      all: lazymatch goal with
           | |- rw_cells _ _ _ [] => apply rw_cells_nil; lia
           | |- _ => cbn [cells_size]; try lia
           end.
    - (* [comment removed for export] *)
      rewrite CSB. replace (bv_unsigned sp + -128 - 16) with (bv_unsigned sp + -144) by lia.
      carve_frame 16%nat ST.
      lazymatch type of FR0 with rw_cells _ _ _ [_ _ ?j] =>
        apply (rw_cells_split_CB asegs _ _ [] 16 j [] [8;8]%nat) in FR0; [| reflexivity]; cbn [mk_CB_cells app firstn skipn] in FR0 end.
      lazymatch type of FR0 with rw_cells _ _ _ [?x; ?y] => change [x; y] with ([x] ++ [y]) in FR0 end.
      apply (proj1 (rw_cells_app _ _ _ _ _)) in FR0. destruct FR0 as [DS G1]. cbn [cells_size csize Nat.add] in G1.
      replace (bv_unsigned sp + -144 + Z.of_nat 8) with (bv_unsigned sp + -144 + 8) in G1 by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (GAP : rw_cells asegs mx (bv_unsigned sp + -144 + 8) ([CB 8 _] ++ [CB 8 _]))
        by (apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact G1|]; cbn [cells_size csize Nat.add];
            replace (bv_unsigned sp + -144 + 8 + Z.of_nat 8) with (bv_unsigned sp + -128) by lia; exact C0') end.
      clear G1 C0'. cbn [app] in GAP.
      eapply se_tail; try exact ERR0; try eassumption; try reflexivity.
      all: cbn [cells_size csize Nat.add]; try lia.
  Qed.
End S.
