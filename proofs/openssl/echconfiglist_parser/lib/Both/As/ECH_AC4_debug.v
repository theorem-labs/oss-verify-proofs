(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCallX AsWalk AsAtomics ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AKit ECH_AsKit ECH_AKitS ECH_AStmt_C0 ECH_AStmt_C1 ECH_AC1_free ECH_AC1_freeopt ECH_AStmt_C2 ECH_APF_C4 ECH_AStmt_C4 ECH_AC4_rep ECH_AC4_frame ECH_AC4_egs
  N6_strcpy.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition AED_RA_E : Z := 0x1f13b8.    (* [comment removed for export] *)
Definition AED_RA_F1 : Z := 0x1f141c.   (* [comment removed for export] *)
Definition AED_RA_L1 : Z := 0x1f1440.   (* [comment removed for export] *)
Definition AED_RA_M1 : Z := 0x1f1450.   (* [comment removed for export] *)
Definition AED_RA_C1 : Z := 0x1f146c.   (* [comment removed for export] *)
Definition AED_J1 : Z := 0x1f1480.      (* [comment removed for export] *)
Definition AED_RA_F2 : Z := 0x1f14d8.   (* [comment removed for export] *)
Definition AED_RA_L2 : Z := 0x1f14fc.   (* [comment removed for export] *)
Definition AED_RA_M2 : Z := 0x1f150c.   (* [comment removed for export] *)
Definition AED_LIT : Z := 0x40b8f.      (* [comment removed for export] *)
Definition SHBv : Z := 0x7fff8000.

Ltac ret_lit RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
Ltac ret_lit_any := match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => ret_lit r end.
Ltac show_goal := match goal with |- evt _ _ (MS ?R _ ?pc _ _ ?mx _) => idtac "PC" pc; idtac R end.
Ltac acc_now ACC BASE MUS NSW :=
  lazymatch type of BASE with accessible _ ?a ?n =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx a n) by (eapply accessible_across; [exact BASE| exact MUS| exact NSW]) end end.
Ltac ck8_now BASE MUS NSW a := let ACC := fresh "ACC" in acc_now ACC BASE MUS NSW; sh_align a; ck8_check ACC a; clear ACC.

Section S.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Definition aed_frame (s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
    [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition aed_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (LF : list fframe) (c : errchain) (E : errst) (exl : ctxinfo) (file line func lo : Z) (errv : word) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 (XS : list (Z * Z)) j0,
      let es := blk_addr (ec_es c) in let top := es_top E in
      ms' = MS (mkR (Z_to_bv 64 AED_RA_F1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 func)
                   (Z_to_bv 64 (sl_file (slot_at E top))) (Z_to_bv 64 AED_LIT) (Z_to_bv 64 76) a3 a4 a5 a6 a7
                   (Z_to_bv 64 line) (Z_to_bv 64 es) (Z_to_bv 64 file) (Z_to_bv 64 (es + top * 8 + 576)) (Z_to_bv 64 SHBv) (Z_to_bv 64 (top * 8))
                   (Z_to_bv 64 top) (Z_to_bv 64 (Z.shiftr (es + top * 8 + 576) 3 + SHBv)) s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom asegs)
      /\ Forall (fs_scratch H LF) XS
      /\ munch ((lo, bv_unsigned sp) :: XS ++ ERRNO_X) m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo (bv_unsigned sp + -96)
      /\ rw_cells asegs m1 (bv_unsigned sp + -96) (CB 8 j0 :: aed_frame s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
      /\ rw_cells asegs m1 ARERRNO [C4 errv]
      /\ CTX_statics m1 exl /\ ERR_statics m1 c /\ ERR_chain LB m1 c /\ lib_shad (chain_blocks c) m1
      /\ ERRSTm m1 es E /\ accessible m1 es 904
      /\ as_RFS H LF m1 /\ ACONST m1 /\ arelro_lib m1.

  Lemma aed_segA :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (LF : list fframe) (c : errchain) (E : errst) (exl : ctxinfo)
           (file line func lo : Z) (errv : word),
      a0 = Z_to_bv 64 file -> a1 = Z_to_bv 64 line -> a2 = Z_to_bv 64 func -> 0 <= line < 2^31 -> 0 < file < 2^64 -> 0 < func < 2^64 ->
      tp = Z_to_bv 64 ATP -> rw_cells asegs m (errno_addr tp) [C4 errv] ->
      CTX_statics m exl -> ERR_statics m c -> ERR_chain LB m c -> chain_below c aceil -> chain_apl H c -> lib_shad (chain_blocks c) m ->
      ERRSTm m (blk_addr (ec_es c)) E ->
      ACONST m -> arelro_lib m -> as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> athr_cells m -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - (FR_ERR_set_debug + EGS_STACK) -> mem_inv asegs m ->
      evt asegs (aed_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB LF c E exl file line func lo errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ERR_set_debug) fc None m (seg_rom asegs)).
  Proof.
    intros until errv. intros A0 A1 A2 LNR FIR FUR TP ERR CS ES EC CB CA LS EST AC RL RFS LFN THR SPA ST CEIL LO MI. subst a0 a1 a2.
    unfold P_ERR_set_debug, FR_ERR_set_debug, EGS_STACK, FR_ossl_err_get_state_int, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, AFS_STACK in *. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    subst tp. unfold ATP in *. rewrite (unsigned_lit 12459152) in ERR by lia. change (12459152 + -164) with 12458988 in ERR.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (ACONST_shbase m AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    (* [comment removed for export] *)
    pose proof EC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CA)))) as R5. cbv beta in R5. rewrite Z5 in R5.
    pose proof R5 as (E1 & E2 & E3 & E4 & E5 & E6 & E7). unfold ERRST_SIZE in *. unfold AIMG_TOP in E4.
    pose proof (aapp_bounds _ _ E7 ltac:(lia)) as (_ & _ & T5 & _). unfold AAPP_HI in T5.
    set (es := blk_addr (ec_es c)) in *.
    pose proof (rw_cells_bound _ _ _ _ ERR) as ERRB. cbn [cells_size csize Nat.add length] in ERRB.
    (* [comment removed for export] *)
    carve_frame 96%nat ST.
    do 12 st1. step. step. step. step. st1. st1. step. step. step.
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
    ret_lit_any. rewrite (unsigned_lit (bv_unsigned sp + -96)) in MU' by lia. rewrite (unsigned_lit (bv_unsigned sp + -96)) in ST2 by lia.
    rewrite (unsigned_lit 12459152) in ERR2 by lia. change (12459152 + -164) with 12458988 in ERR2.
    lazymatch type of MU' with munch _ ?m1 _ => change (munch ((lo, bv_unsigned sp + -96) :: XS ++ ERRNO_X) m1 m2) in MU' end.
    pose proof (errno_lit) as FLIT. pose proof (low_lit_ok _ FLIT) as FLIT'.
    lazymatch type of FR with rw_cells _ ?m1 ?A ?cs =>
      assert (FR2 : rw_cells asegs m2 A cs)
        by (eapply rw_cells_transport; [exact FR| exact MU'| exact WM'|]; eapply (dj_foot_hi H HH); [exact RFS| exact FXS| exact FLIT'| exact CEIL| lia| lia]) end.
    lazymatch type of MU' with munch _ ?m1 _ =>
      assert (MU2 : munch ((lo, bv_unsigned sp) :: XS ++ ERRNO_X) m m2) by (eapply munch_stack_then; [exact MU| exact MU'| lia]);
      pose proof (wmono_trans _ _ _ _ WM WM') as WM2 end.
    assert (EST2 : ERRSTm m2 es E).
    { eapply ERRSTm_munch; [exact EST| exact MU2| exact WM2|]. unfold ERRST_SIZE.
      eapply (dj_foot_blk H HH); [exact RFS| exact FXS| exact FLIT'| exact CEIL| exact R5| lia| lia|].
      apply Forall_cons; [| apply Forall_nil]. intros [P1 _]. exfalso. cbn in P1. unfold AIMG_TOP, ARERRNO, ATP in P1. lia. }
    clear FR MU WM MU' WM' MI ST EST ERR. rename MI2 into MI. rename ST2 into ST.
    assert (ACC2 : accessible m2 es 904).
    { pose proof (proj1 (Forall_forall _ _) LS2 _ ltac:(unfold chain_blocks; cbn; do 3 right; left; reflexivity)) as AD. cbv beta in AD.
      fold es in AD. rewrite Z5 in AD. unfold ERRST_SIZE in AD. eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI; lia]. }
    pose proof (munch_refl [(es, es + 904)] m2) as MUS.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(es, es + 904)])
      by (apply Forall_cons; [cbn [fst snd]; exact (aapp_not_shadowland _ _ E7)| apply Forall_nil]).
    fold es.
    (* [comment removed for export] *)
    pose proof EST2 as EST0. unfold ERRSTm in EST2. fold es in EST2.
    destruct EST2 as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    set (top := es_top E) in *. arr_lens SL.
    (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
    step. idtac. step. ubal_any. step. if_lit. step. zstep. zstep. ck8_now ACC2 MUS NSW (es + 896).
    bgo. ck8_now ACC2 MUS NSW (es + top * 8 + 576).
    pose proof (u64arr_read_m _ _ _ top _ F7 (slot_nth E top (fun s => wz (sl_file s)) SL TR) ltac:(lia)) as RD.
    replace (es + 576 + top * 8) with (es + top * 8 + 576) in RD by lia. step. clear RD.
    bgo. step.
    unfold aed_postA, AED_RA_F1, AED_LIT, SHBv, P_CRYPTO_free. unfold wz. finish; [exact FXS| exact MU2| exact FR2].
  Qed.

  (* [comment removed for export] *)
  Lemma aed_segB :
    forall (sp gp tp t0 t1 t2 s0 s2 s3 s5 s7 s8 s9 s10 s11 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (file func lo : Z) (fs fsl : list byte),
      AROSTR file fs fsl -> fs <> [] -> Z.of_nat (length fs) < 24 -> 0 < file ->
      ACONST m -> stk asegs m lo (bv_unsigned sp + -96) -> aceil <= lo -> lo <= bv_unsigned sp + -96 - AINTRIN_STACK -> mem_inv asegs m ->
      0 <= bv_unsigned sp + -96 ->
      evt asegs (fun ms' => exists t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1,
          ms' = MS (mkR (Z_to_bv 64 AED_RA_M1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' s0 (Z_to_bv 64 func)
                       (Z_to_bv 64 (Z.of_nat (length fs) + 1)) (Z_to_bv 64 0) (Z_to_bv 64 0) a3' a4' a5' a6' a7'
                       s2 s3 (Z_to_bv 64 file) s5 (Z_to_bv 64 SHBv) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 P_CRYPTO_malloc) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -96 - AINTRIN_STACK, bv_unsigned sp + -96)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -96) /\ ACONST m1)
        (MS (mkR (Z_to_bv 64 AED_RA_F1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 (Z_to_bv 64 func) a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 (Z_to_bv 64 file) s5 (Z_to_bv 64 SHBv) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AED_RA_F1)) fc None m (seg_rom asegs)).
  Proof.
    intros until fsl. intros RSF FNE FLEN FPOS AC ST CEIL LO MI SP0. unfold AED_RA_F1, AED_RA_M1, SHBv, P_CRYPTO_malloc, AINTRIN_STACK in *. ret_lit 0x1f141c. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    destruct RSF as ((RB1 & RB2 & RS) & RACC & RL1 & RL2). unfold IMG_LO, IMG_HI, AIMG_LO, AIMG_TOP in RB1, RB2, RL1, RL2.
    pose proof (RS m MI) as (BSf & NNf & PADf). pose proof (RACC m AC) as ACCf.
    pose proof (bytes_at_bound _ _ _ _ BSf) as FB. rewrite length_app in FB. cbn [length] in FB.
    pose proof (munch_refl [(bv_unsigned sp + -96 - 4096, bv_unsigned sp + -96)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
    zstep. zstep. ck1_load ACCf file sv V1 V2 Hf.
    lazymatch goal with |- evt _ ?P (MS (mkR ?ra_ ?sp_ ?gp_ ?tp_ ?t0_ ?t1_ ?t2_ ?s0_ ?s1_ _ _ ?a2_ ?a3_ ?a4_ ?a5_ ?a6_ ?a7_ ?s2_ ?s3_ ?s4_ ?s5_ ?s6_ ?s7_ ?s8_ ?s9_ ?s10_ ?s11_ ?t3_ ?t4_ ?t5_ ?t6_) ?F_ _ ?fc_ _ ?mx ?rom) =>
    assert (FIN : forall a0x a1x : word,
      evt asegs P (MS (mkR ra_ sp_ gp_ tp_ t0_ t1_ t2_ s0_ s1_ a0x a1x a2_ a3_ a4_ a5_ a6_ a7_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_ t3_ t4_ t5_ t6_)
                       F_ (Z_to_bv 64 0x1f1430) fc_ None mx rom)) end.
    { intros a0x a1x.
      (* [comment removed for export] *)
      destruct fs as [|f0 fs'] eqn:EFS; [congruence|]. rewrite <- EFS in *.
      assert (F0N : bv_unsigned f0 <> 0).
      { intros E0. apply NNf. rewrite EFS. left. apply bv_eq. rewrite E0. reflexivity. }
      pose proof (abyte_range f0) as F0R.
      pose proof (u8ro_read asegs _ file (fs ++ Z_to_bv 8 0 :: fsl) 0 f0 (wa (file + 0)) BSf ltac:(rewrite EFS; reflexivity) ltac:(lia) eq_refl) as RD.
      replace (file + 0) with file in RD by lia.
      step. clear RD. change (zxb f0) with (Z_to_bv 64 (bv_unsigned f0)).
      step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
      step. step.
      eapply evt_cut.
      { eapply (ah_strlen H HH) with (str := fs) (slack := fsl) (lo := lo); rewrite ?unsigned_lit by lia;
          [ exact BSf| exact NNf| exact PADf| exact ACCf
          | apply ACONST_shvis; [exact AC| unfold AIMG_LO; lia| lia| unfold AIMG_TOP; lia]
          | exact ST| exact CEIL| unfold AINTRIN_STACK; lia| exact MI| exact AC| lia
          | left; rewrite ASHADOW_BASE_val; lia
          | left; lia ]. }
      intros ms' PO. unfold astrlen_post in PO.
      destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m1 & -> & MU' & WM' & MI' & ST' & BS' & AC').
      ret_lit_any. rewrite (unsigned_lit (bv_unsigned sp + -96)) in MU', ST' by lia. unfold AINTRIN_STACK in MU'.
      (* [comment removed for export] *)
      zstep. step. step. step.
      finish. }
    ck1_branch_blt file sv V1 V2 Hf FIN.
  Qed.

  (* [comment removed for export] *)
  Lemma aed_segC :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (E : errst)
           (es top file line func lo A1 : Z) (fs fsl junk : list byte) (fo : oblk),
      AROSTR file fs fsl -> fs <> [] -> Z.of_nat (length fs) < 24 -> 0 < file -> 0 <= line < 2^31 ->
      ERRSTm m es E -> top = es_top E ->
      0 < es -> es + 904 < 2^47 -> es mod 16 = 0 -> aapp es 904 -> accessible m es 904 -> es + 904 <= lo ->
      rw_cells asegs m A1 [CB (S (length fs)) junk] -> 0 < A1 -> A1 + Z.of_nat (length fs) + 1 <= lo -> aapp A1 (Z.of_nat (length fs) + 1) ->
      accessible m A1 (Z.of_nat (length fs) + 1) -> shvis m A1 (A1 + Z.of_nat (length fs) + 1) ->
      (A1 + Z.of_nat (length fs) + 1 <= es \/ es + 904 <= A1) ->
      ACONST m -> stk asegs m lo (bv_unsigned sp + -96) -> aceil <= lo -> lo <= bv_unsigned sp + -96 - ASTRCPY_STACK -> mem_inv asegs m ->
      evt asegs (fun ms' => exists u0 u1 u2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR (Z_to_bv 64 AED_RA_F2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp u0 u1 u2 sp (Z_to_bv 64 func)
                       (Z_to_bv 64 (sl_func (slot_at E top))) (Z_to_bv 64 AED_LIT) (Z_to_bv 64 86) b3 b4 b5 b6 b7
                       (Z_to_bv 64 (Z.shiftr (es + top * 8 + 768) 3 + SHBv)) (Z_to_bv 64 (es + top * 8 + 768)) (Z_to_bv 64 file)
                       (Z_to_bv 64 (es + top * 8 + 576)) (Z_to_bv 64 SHBv) (Z_to_bv 64 (top * 8)) (Z_to_bv 64 (top * 4))
                       (Z_to_bv 64 (Z.shiftr (es + top * 8 + 576) 3 + SHBv)) s10 s11 u3 u4 u5 u6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom asegs)
          /\ munch [(es, es + 904); (A1, A1 + Z.of_nat (length fs) + 1); (bv_unsigned sp + -96 - ASTRCPY_STACK, bv_unsigned sp + -96)] m m1
          /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp + -96)
          /\ ERRSTm m1 es (es_with_slot E top (slot_setfile (slot_at E top) A1 fo line))
          /\ rw_cells asegs m1 A1 [CB (S (length fs)) (fs ++ [Z_to_bv 8 0])]
          /\ accessible m1 es 904 /\ ACONST m1)
        (MS (mkR (Z_to_bv 64 AED_RA_M1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 func)
                 (Z_to_bv 64 A1) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 line) (Z_to_bv 64 es) (Z_to_bv 64 file) (Z_to_bv 64 (es + top * 8 + 576)) (Z_to_bv 64 SHBv) (Z_to_bv 64 (top * 8))
                 (Z_to_bv 64 top) (Z_to_bv 64 (Z.shiftr (es + top * 8 + 576) 3 + SHBv)) s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AED_RA_M1)) fc None m (seg_rom asegs)).
  Proof.
    intros until fo. intros RSF FNE FLEN FPOS LNR EST TOP POS BL AL AP ACC0 ESLO DST A1P A1LO A1AP ACCD SHD SEP AC ST CEIL LO MI.
    unfold AED_RA_M1, AED_RA_F2, AED_LIT, SHBv, P_CRYPTO_free, ASTRCPY_STACK in *. ret_lit 0x1f1450. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    destruct RSF as ((RB1 & RB2 & RS) & RACC & RL1 & RL2). unfold IMG_LO, IMG_HI, AIMG_LO, AIMG_TOP in RB1, RB2, RL1, RL2.
    pose proof (RS m MI) as (BSf & NNf & PADf).
    pose proof (bytes_at_bound _ _ _ _ BSf) as FB. rewrite length_app in FB. cbn [length] in FB.
    pose proof (aapp_bounds _ _ A1AP ltac:(lia)) as (Q1 & Q2 & Q3 & Q4 & _). unfold AAPP_HI, AIMG_TOP in Q1, Q3.
    pose proof (munch_refl [(es, es + 904); (A1, A1 + Z.of_nat (length fs) + 1); (bv_unsigned sp + -96 - 8192, bv_unsigned sp + -96)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(es, es + 904); (A1, A1 + Z.of_nat (length fs) + 1); (bv_unsigned sp + -96 - 8192, bv_unsigned sp + -96)]).
    { apply Forall_cons; [cbn [fst snd]; exact (aapp_not_shadowland _ _ AP)|]. apply Forall_cons; [cbn [fst snd]; pose proof (aapp_not_shadowland _ _ A1AP); lia|].
      apply Forall_cons; [cbn [fst snd]; unfold AHI_LO; lia| apply Forall_nil]. }
    unfold ERRSTm in EST. destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG). subst top.
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    set (top := es_top E) in *. arr_lens SL.
    (* [comment removed for export] *)
    step. ub_dead. ck8_now ACC0 MU NSW (es + top * 8 + 576). arr_store64 F7 top (wz A1).
    (* [comment removed for export] *)
    set (sl := slot_at E top) in *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (EMa : ERRSTm mx es (es_with_slot E top (slot_setfile sl A1 fo (sl_line sl))))
        by (eapply (ERRSTm_with_slot _ es E top (slot_setfile sl A1 fo (sl_line sl))); try eassumption; try reflexivity;
            try (upd_keep_tac E top SL TR); cbn [slot_setfile sl_flags sl_buffer sl_line sl_file]; subst sl; try lia;
            pose proof (slot_at_own _ E top RG SL TR) as (O1 & O2 & O3); lia) end.
    clear F1 F2 F3 F4 F5 F6 F7 F8 F9 TB.
    step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
    step. step.
    pose proof (aapp_bounds _ _ AP ltac:(lia)) as (P1 & _). unfold AIMG_TOP in P1.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACx : ACONST mx)
        by (eapply ACONST_frame; [exact AC| exact MU| exact WM|];
            apply Forall_cons; [eapply aconst_ok_aapp; [exact AP| cbn; lia| cbn; lia]|];
            apply Forall_cons; [eapply aconst_ok_aapp; [exact A1AP| cbn; lia| cbn; lia]|];
            apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; [unfold sh, AIMG_TOP; rewrite ASHADOW_BASE_val; lia| lia]| apply Forall_nil]) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (RS mx MI) as (BS1 & NN1 & PAD1);
        pose proof (ACONST_icpt _ ACx) as (_ & _ & RSC & _ & _ & _ & CFR); unfold wz in RSC; unfold b8 in CFR;
        assert (ACCD1 : accessible mx A1 (Z.of_nat (length fs) + 1)) by (eapply accessible_across; [exact ACCD| exact MU| exact NSW]);
        assert (SHD1 : shvis mx A1 (A1 + Z.of_nat (length fs) + 1)) by (eapply shvis_across; [exact SHD| exact MU| exact WM| lia| unfold AAPP_HI; lia| exact NSW]);
        eapply evt_cut;
        [ eapply (strcpy_icpt_ok) with (str := fs) (slack := fsl) (lo := lo) (junk := junk); rewrite ?unsigned_lit by lia;
          [ exact BS1| exact NN1| exact PAD1| exact DST| left; lia| exact (RACC _ ACx)| exact ACCD1
          | apply ACONST_shvis; [exact ACx| unfold AIMG_LO; lia| lia| unfold AIMG_TOP; lia]| exact SHD1
          | eassumption| exact CEIL| unfold ASTRCPY_STACK; lia| exact MI| exact ACx| lia
          | left; rewrite ASHADOW_BASE_val; lia| eapply aapp_in_app_mem; [exact A1AP| lia| lia]
          | eapply aconst_ok_aapp; [exact A1AP| lia| lia]| lia| lia| exact RSC| exact CFR ]
        | ] end.
    intros ms' PO. unfold astrcpy_post in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m1 & -> & MU' & WM' & MI' & ST' & DST' & BS' & AC').
    ret_lit_any. rewrite (unsigned_lit (bv_unsigned sp + -96)) in MU' by lia. rewrite (unsigned_lit A1) in MU' by lia.
    rewrite (unsigned_lit (bv_unsigned sp + -96)) in ST' by lia. rewrite (unsigned_lit A1) in DST' by lia. unfold ASTRCPY_STACK in MU'.
    clear BS1 NN1 PAD1 ACCD1 SHD1 ACx.
    carry MU' WM'.
    assert (EMb : ERRSTm m1 es (es_with_slot E top (slot_setfile sl A1 fo (sl_line sl)))).
    { eapply ERRSTm_munch; [exact EMa| exact MU'| exact WM'|]. unfold ERRST_SIZE. cbn. lia. }
    clear EMa. extend_munch MU WM MU' WM'. clear MI ST DST. rename MI' into MI. rename ST' into ST.
    (* [comment removed for export] *)
    unfold ERRSTm in EMb. destruct EMb as (SL' & TR' & BR' & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG').
    cbn [es_slots es_top es_bottom es_with_slot] in SL', TR', BR', F1, F2, F3, F4, F5, F6, F7, F8, F9, TB, RG'. fold top in TR', F1, F3, F7, F8, F9, TB.
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in F1, F2, F3, F4, F5, F6, F7, F8, F9, TB.
    arr_lens SL'.
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + top * 4 + 704).
    bgo. arr_store32 F8 top (Z_to_bv 64 line).
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + top * 8 + 768).
    set (E1 := es_with_slot E top (slot_setfile sl A1 fo (sl_line sl))) in *.
    assert (SLOT1 : slot_at E1 top = slot_setfile sl A1 fo (sl_line sl)) by (subst E1; apply slot_at_upd; [exact SL| exact TR]).
    assert (TOP1 : es_top E1 = top) by reflexivity.
    assert (TR1 : 0 <= top < 16) by exact TR.
    pose proof (u64arr_read_m _ _ _ top _ F9 (slot_nth E1 top (fun s => wz (sl_func s)) SL' TR1) ltac:(lia)) as RD.
    rewrite SLOT1 in RD. cbn [slot_setfile sl_func] in RD.
    replace (es + 768 + top * 8) with (es + top * 8 + 768) in RD by lia.
    bgo. step. clear RD.
    pose proof (slot_at_own _ E top RG SL TR) as (O1 & O2 & O3). fold sl in O1, O2, O3.
    unfold wz. finish.
    + replace (es_with_slot E top (slot_setfile sl A1 fo line)) with (es_with_slot E1 top (slot_setfile (slot_at E1 top) A1 fo line))
        by (subst E1; rewrite es_with_slot_twice by (exact SL || exact TR || lia); rewrite SLOT1; reflexivity).
      eapply (ERRSTm_with_slot _ es E1 top (slot_setfile (slot_at E1 top) A1 fo line)); rewrite ?TOP1; try eassumption; try reflexivity;
        try (upd_keep_tac E1 top SL' TR1); rewrite ?SLOT1; cbn [slot_setfile sl_flags sl_buffer sl_line sl_file]; try lia.
      apply (upd_keep E1 top (fun s => wz (sl_file s)) (slot_setfile (slot_at E1 top) A1 fo line)); [exact SL'| exact TR1| rewrite SLOT1; reflexivity].
    + eapply accessible_across; [exact ACC0| exact MU| exact NSW].
    + eapply ACONST_frame; [exact AC| exact MU| exact WM|].
      apply Forall_cons; [eapply aconst_ok_aapp; [exact AP| cbn; lia| cbn; lia]|].
      apply Forall_cons; [eapply aconst_ok_aapp; [exact A1AP| cbn; lia| cbn; lia]|].
      apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; [unfold sh, AIMG_TOP; rewrite ASHADOW_BASE_val; lia| lia]| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  Lemma aed_segD :
    forall (sp gp tp t0 t1 t2 s0 s2 s3 s4 s5 s7 s8 s9 s10 s11 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (func lo : Z) (gs gsl : list byte),
      AROSTR func gs gsl -> gs <> [] -> Z.of_nat (length gs) < 32 -> 0 < func ->
      ACONST m -> stk asegs m lo (bv_unsigned sp + -96) -> aceil <= lo -> lo <= bv_unsigned sp + -96 - AINTRIN_STACK -> mem_inv asegs m ->
      0 <= bv_unsigned sp + -96 ->
      evt asegs (fun ms' => exists t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1,
          ms' = MS (mkR (Z_to_bv 64 AED_RA_M2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' s0 (Z_to_bv 64 func)
                       (Z_to_bv 64 (Z.of_nat (length gs) + 1)) (Z_to_bv 64 0) (Z_to_bv 64 0) a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 (Z_to_bv 64 SHBv) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (Z_to_bv 64 P_CRYPTO_malloc) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -96 - AINTRIN_STACK, bv_unsigned sp + -96)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -96) /\ ACONST m1)
        (MS (mkR (Z_to_bv 64 AED_RA_F2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 (Z_to_bv 64 func) a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 (Z_to_bv 64 SHBv) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AED_RA_F2)) fc None m (seg_rom asegs)).
  Proof.
    intros until gsl. intros RSG GNE GLEN GPOS AC ST CEIL LO MI SP0. unfold AED_RA_F2, AED_RA_M2, SHBv, P_CRYPTO_malloc, AINTRIN_STACK in *. ret_lit 0x1f14d8. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    destruct RSG as ((RB1 & RB2 & RS) & RACC & RL1 & RL2). unfold IMG_LO, IMG_HI, AIMG_LO, AIMG_TOP in RB1, RB2, RL1, RL2.
    pose proof (RS m MI) as (BSg & NNg & PADg). pose proof (RACC m AC) as ACCg.
    pose proof (bytes_at_bound _ _ _ _ BSg) as GB. rewrite length_app in GB. cbn [length] in GB.
    pose proof (munch_refl [(bv_unsigned sp + -96 - 4096, bv_unsigned sp + -96)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
    zstep. zstep. ck1_load ACCg func sv V1 V2 Hg.
    lazymatch goal with |- evt _ ?P (MS (mkR ?ra_ ?sp_ ?gp_ ?tp_ ?t0_ ?t1_ ?t2_ ?s0_ ?s1_ _ _ ?a2_ ?a3_ ?a4_ ?a5_ ?a6_ ?a7_ ?s2_ ?s3_ ?s4_ ?s5_ ?s6_ ?s7_ ?s8_ ?s9_ ?s10_ ?s11_ ?t3_ ?t4_ ?t5_ ?t6_) ?F_ _ ?fc_ _ ?mx ?rom) =>
    assert (FIN : forall a0x a1x : word,
      evt asegs P (MS (mkR ra_ sp_ gp_ tp_ t0_ t1_ t2_ s0_ s1_ a0x a1x a2_ a3_ a4_ a5_ a6_ a7_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_ t3_ t4_ t5_ t6_)
                       F_ (Z_to_bv 64 0x1f14ec) fc_ None mx rom)) end.
    { intros a0x a1x.
      destruct gs as [|g0 gs'] eqn:EGS; [congruence|]. rewrite <- EGS in *.
      assert (G0N : bv_unsigned g0 <> 0).
      { intros E0. apply NNg. rewrite EGS. left. apply bv_eq. rewrite E0. reflexivity. }
      pose proof (abyte_range g0) as G0R.
      pose proof (u8ro_read asegs _ func (gs ++ Z_to_bv 8 0 :: gsl) 0 g0 (wa (func + 0)) BSg ltac:(rewrite EGS; reflexivity) ltac:(lia) eq_refl) as RD.
      replace (func + 0) with func in RD by lia.
      step. clear RD. change (zxb g0) with (Z_to_bv 64 (bv_unsigned g0)).
      step. if_cases K1; zify_cond K1; [kill K1|]; clear K1.
      step. step.
      eapply evt_cut.
      { eapply (ah_strlen H HH) with (str := gs) (slack := gsl) (lo := lo); rewrite ?unsigned_lit by lia;
          [ exact BSg| exact NNg| exact PADg| exact ACCg
          | apply ACONST_shvis; [exact AC| unfold AIMG_LO; lia| lia| unfold AIMG_TOP; lia]
          | exact ST| exact CEIL| unfold AINTRIN_STACK; lia| exact MI| exact AC| lia
          | left; rewrite ASHADOW_BASE_val; lia
          | left; lia ]. }
      intros ms' PO. unfold astrlen_post in PO.
      destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m1 & -> & MU' & WM' & MI' & ST' & BS' & AC').
      ret_lit_any. rewrite (unsigned_lit (bv_unsigned sp + -96)) in MU', ST' by lia. unfold AINTRIN_STACK in MU'.
      zstep. step. step. step.
      finish. }
    ck1_branch_blt func sv V1 V2 Hg FIN.
  Qed.

  (* [comment removed for export] *)
  Lemma aed_segE :
    forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (E : errst)
           (es top file func lo A2 : Z) (gs gsl junk j0 : list byte) (go : oblk),
      AROSTR func gs gsl -> gs <> [] -> Z.of_nat (length gs) < 32 -> 0 < func ->
      ERRSTm m es E -> top = es_top E ->
      0 < es -> es + 904 < 2^47 -> es mod 16 = 0 -> aapp es 904 -> accessible m es 904 -> es + 904 <= lo ->
      rw_cells asegs m A2 [CB (S (length gs)) junk] -> 0 < A2 -> A2 + Z.of_nat (length gs) + 1 <= lo -> aapp A2 (Z.of_nat (length gs) + 1) ->
      accessible m A2 (Z.of_nat (length gs) + 1) -> shvis m A2 (A2 + Z.of_nat (length gs) + 1) ->
      (A2 + Z.of_nat (length gs) + 1 <= es \/ es + 904 <= A2) ->
      ACONST m -> stk asegs m lo (bv_unsigned sp + -96) -> aceil <= lo -> lo <= bv_unsigned sp - ASTRCPY_STACK -> mem_inv asegs m ->
      rw_cells asegs m (bv_unsigned sp + -96) (CB 8 j0 :: aed_frame s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (fun ms' => exists u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR ra sp gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 A2) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                   F (ret_pc ra) fc None m1 (seg_rom asegs)
          /\ munch [(es, es + 904); (A2, A2 + Z.of_nat (length gs) + 1); (bv_unsigned sp - ASTRCPY_STACK, bv_unsigned sp)] m m1
          /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp)
          /\ ERRSTm m1 es (es_with_slot E top (slot_setfunc (slot_at E top) A2 go))
          /\ rw_cells asegs m1 A2 [CB (S (length gs)) (gs ++ [Z_to_bv 8 0])]
          /\ ACONST m1)
        (MS (mkR (Z_to_bv 64 AED_RA_M2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 func)
                 (Z_to_bv 64 A2) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (Z.shiftr (es + top * 8 + 768) 3 + SHBv)) (Z_to_bv 64 (es + top * 8 + 768)) (Z_to_bv 64 file)
                 (Z_to_bv 64 (es + top * 8 + 576)) (Z_to_bv 64 SHBv) (Z_to_bv 64 (top * 8)) (Z_to_bv 64 (top * 4))
                 (Z_to_bv 64 (Z.shiftr (es + top * 8 + 576) 3 + SHBv)) s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AED_RA_M2)) fc None m (seg_rom asegs)).
  Proof.
    intros until go. intros RSG GNE GLEN GPOS EST TOP POS BL AL AP ACC0 ESLO DST A2P A2LO A2AP ACCD SHD SEP AC ST CEIL LO MI FR RAE.
    unfold AED_RA_M2, SHBv, ASTRCPY_STACK, aed_frame in *. ret_lit 0x1f150c. acb.
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    destruct RSG as ((RB1 & RB2 & RS) & RACC & RL1 & RL2). unfold IMG_LO, IMG_HI, AIMG_LO, AIMG_TOP in RB1, RB2, RL1, RL2.
    pose proof (aapp_bounds _ _ A2AP ltac:(lia)) as (Q1 & Q2 & Q3 & Q4 & _). unfold AAPP_HI, AIMG_TOP in Q1, Q3.
    pose proof (aapp_bounds _ _ AP ltac:(lia)) as (P1 & _). unfold AIMG_TOP in P1.
    pose proof (munch_refl [(es, es + 904); (A2, A2 + Z.of_nat (length gs) + 1); (bv_unsigned sp - 8192, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(es, es + 904); (A2, A2 + Z.of_nat (length gs) + 1); (bv_unsigned sp - 8192, bv_unsigned sp)]).
    { apply Forall_cons; [cbn [fst snd]; exact (aapp_not_shadowland _ _ AP)|]. apply Forall_cons; [cbn [fst snd]; pose proof (aapp_not_shadowland _ _ A2AP); lia|].
      apply Forall_cons; [cbn [fst snd]; unfold AHI_LO; lia| apply Forall_nil]. }
    unfold ERRSTm in EST. destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG). subst top.
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    set (top := es_top E) in *. arr_lens SL.
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + top * 8 + 768). bgo. arr_store64 F9 top (wz A2).
    set (sl := slot_at E top) in *.
    pose proof (slot_at_own _ E top RG SL TR) as (O1 & O2 & O3). fold sl in O1, O2, O3.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (EMa : ERRSTm mx es (es_with_slot E top (slot_setfunc sl A2 go)))
        by (eapply (ERRSTm_with_slot _ es E top (slot_setfunc sl A2 go)); try eassumption; try reflexivity;
            try (upd_keep_tac E top SL TR); cbn [slot_setfunc sl_flags sl_buffer sl_line sl_file sl_func]; subst sl; lia) end.
    clear F1 F2 F3 F4 F5 F6 F7 F8 F9 TB.
    bgo.
    (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACx : ACONST mx)
        by (eapply ACONST_frame; [exact AC| exact MU| exact WM|];
            apply Forall_cons; [eapply aconst_ok_aapp; [exact AP| cbn; lia| cbn; lia]|];
            apply Forall_cons; [eapply aconst_ok_aapp; [exact A2AP| cbn; lia| cbn; lia]|];
            apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; [unfold sh, AIMG_TOP; rewrite ASHADOW_BASE_val; lia| lia]| apply Forall_nil]) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (RS mx MI) as (BS1 & NN1 & PAD1);
        pose proof (ACONST_icpt _ ACx) as (_ & _ & RSC & _ & _ & _ & CFR); unfold wz in RSC; unfold b8 in CFR;
        assert (ACCD1 : accessible mx A2 (Z.of_nat (length gs) + 1)) by (eapply accessible_across; [exact ACCD| exact MU| exact NSW]);
        assert (SHD1 : shvis mx A2 (A2 + Z.of_nat (length gs) + 1)) by (eapply shvis_across; [exact SHD| exact MU| exact WM| lia| unfold AAPP_HI; lia| exact NSW]);
        eapply evt_cut;
        [ eapply (strcpy_icpt_ok) with (str := gs) (slack := gsl) (lo := lo) (junk := junk); rewrite ?unsigned_lit by lia;
          [ exact BS1| exact NN1| exact PAD1| exact DST| left; lia| exact (RACC _ ACx)| exact ACCD1
          | apply ACONST_shvis; [exact ACx| unfold AIMG_LO; lia| lia| unfold AIMG_TOP; lia]| exact SHD1
          | exact ST| exact CEIL| unfold ASTRCPY_STACK; lia| exact MI| exact ACx| lia
          | left; rewrite ASHADOW_BASE_val; lia| eapply aapp_in_app_mem; [exact A2AP| lia| lia]
          | eapply aconst_ok_aapp; [exact A2AP| lia| lia]| lia| lia| exact RSC| exact CFR ]
        | ] end.
    intros ms' PO. unfold astrcpy_post in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m1 & -> & MU' & WM' & MI' & ST' & DST' & BS' & AC').
    rewrite (unsigned_lit A2) in MU' by lia. rewrite (unsigned_lit A2) in DST' by lia. unfold ASTRCPY_STACK in MU'.
    assert (EMb : ERRSTm m1 es (es_with_slot E top (slot_setfunc sl A2 go))).
    { eapply ERRSTm_munch; [exact EMa| exact MU'| exact WM'|]. unfold ERRST_SIZE. cbn. lia. }
    extend_munch MU WM MU' WM'.
    finish.
    all: match goal with |- ?G => idtac "WE"; idtac G end.
  Qed.
End S.
