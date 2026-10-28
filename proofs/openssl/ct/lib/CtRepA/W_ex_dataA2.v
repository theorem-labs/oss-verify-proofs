(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge RzCPS SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_small R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA AsStruct ImplAX BnIfaceA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 ImplA RtCallA W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_locks W_akit W_bio_push Fr_CRYPTO_free_ex_data W_ex_dataA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

(* [comment removed for export] *)
Lemma c8_blur_at : forall m A pre (v : word) rest,
  rw_cells ctasegs m A (pre ++ C8 v :: rest) -> rw_cells ctasegs m A (pre ++ CB 8 (le8 v) :: rest).
Proof.
  intros m A pre v rest H. apply rw_cells_app in H. destruct H as [H1 H2]. apply rw_cells_app. split; [exact H1|]. apply c8_blur1. exact H2.
Qed.
(* [comment removed for export] *)
Local Notation E_cfed_free := (E_CRYPTO_free_ex_data_1f5ed8 : uk_call 0x1fa524 0x1fa960 0x1fd334).      (* [comment removed for export] *)


Section WithRT2.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CRYPTO_FREE_EX_DATA_A : Z := CFED_ENTRY.

Definition free_ex_data_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (ad lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (ad <= a < ad + 16)) m m'
    /\ AHEAP Σ' OW LB m'
    /\ rt_live RT Σ' = rt_live RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ'
    /\ rw_cells ctasegs m' ad [C8 (wz 0); C8 (wz 0)] /\ exlock_free m' E.
  (* [comment removed for export] *)

Lemma CRYPTO_free_ex_data_cpsA : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (E : ap_env) (lo : Z) (pb : bptr) (bio : Z) (ras : list Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + FREE_EX_DATA_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ap_statics_fixed m E -> exlock_free m E -> In (p_xl E, e_xl E, MUTEX_SIZE) OW ->
  In (pb, bio, BIO_SIZE) OW -> pb <> p_xl E -> rw_cells ctasegs m (bio + 112) [C8 (wz 0); C8 (wz 0)] ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx CRYPTO_FREE_EX_DATA_A (bv_unsigned ra :: ras) ->      (* [comment removed for export] *)
  a0 = Z_to_bv 64 CRYPTO_EX_INDEX_BIO -> a1 = wz bio -> a2 = wz (bio + 112) ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz CRYPTO_FREE_EX_DATA_A) fc None m (seg_rom ctasegs))))
      (fun c => exists Σ', ASTA RT Σ' PMc (free_ex_data_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E (bio + 112) lo m Σ') c
                /\ rt_live RT Σ' = rt_live RT Σ)      (* [comment removed for export] *).
Proof.
  intros until ras. intros HEAP ST CEIL LO SPT SP16 MI -> FLEN CRED SF HXL HXIN HBIN NBX HAD UW CTX -> -> ->.
  pose proof (dc_staticsA_of_fixed _ _ SF) as DC.
  destruct SF as (CS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HXLp & HXM & _).
  unfold CRYPTO_FREE_EX_DATA_A, FREE_EX_DATA_STACK_A, CFED_FRAME, RT_STACK, CRYPTO_EX_INDEX_BIO, BIO_SIZE, MUTEX_SIZE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HBIN' : In (pb, bio, 128) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  assert (HXIN' : In (p_xl E, e_xl E, 40) (OW ++ LB)) by (apply in_or_app; left; exact HXIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (BB0 & _ & _ & BB3 & BB4). cbn [blk_addr blk_size fst snd] in BB0, BB3, BB4.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HXIN') as (XB0 & _ & _ & XB3 & XB4). cbn [blk_addr blk_size fst snd] in XB0, XB3, XB4.
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HXIN)) as ALX. pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HBIN)) as ALB.   (* [comment removed for export] *)
  pose proof (AH_disjoint_gen _ _ _ _ (pb, bio, 128) (p_xl E, e_xl E, 40) HEAP HBIN' HXIN' NBX) as DJX. cbn [blk_addr blk_size fst snd] in DJX.
  assert (XLO : obj_range (e_xl E) 40 lo) by (unfold obj_range, SEGTOP_A; unfold BnHeapA.ACEIL in *; clear - XB0 XB3 XB4 CEIL; lia).
  assert (AL4 : e_xl E mod 4 = 0) by (clear - ALX; Z.div_mod_to_equations; lia).
  unfold AP_DC_EXLOCK, AP_DC_EXMETH_BIO, AP_DC_INT, MallocRep.wz in HXLp, HXM. change (12208768 + 8) with 12208776 in HXLp. change (12208768 + 112) with 12208880 in HXM.
  eapply (cfed_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP | exact ST | exact CEIL | unfold CFED_FRAME, RT_STACK; clear - LO; lia
    | unfold USTACK_TOP; clear - SPT; lia | exact SP16
    | rewrite unsigned_lit by (clear - BB0 BB3 C3; unfold BnHeapA.ACEIL in *; lia); clear - BB0; lia
    | rewrite unsigned_lit by (clear - BB0 BB3 C3; unfold BnHeapA.ACEIL in *; lia); clear - ALB; Z.div_mod_to_equations; lia
    | exact MI | reflexivity | exact FLEN | exact CRED |].
  intros Σ1 m3 f spa g junk gj ra' t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' F' fc' j0 j8 j16 j24 j32 j48 j64 j72 j80 jf24 jf32 jf192
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
  unfold CFED_BODY, MallocRep.wz.
  (* [comment removed for export] *)
  pose proof (@AH_ceil (push AR f 2) _ _ _ _ HEAP3) as (D1 & D2 & D3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in D1, D2, D3. cbn [ar_SP0 push amb] in D1, D2, D3.
  destruct GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 2) with 256 in G3, G5. unfold SEGTOP_A in G4.
  assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 D3; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPAL SPAH SPR LO LO0; lia).
  pose proof (FRESH _ HBIN') as OFFB. unfold off_fr in OFFB. cbn [blk_addr blk_size fst snd] in OFFB. change (fs_size 2) with 256 in OFFB.
  pose proof (FRESH _ HXIN') as OFFX. unfold off_fr in OFFX. cbn [blk_addr blk_size fst snd] in OFFX. change (fs_size 2) with 256 in OFFX.
  pose proof (aclient_lib _ _ _ _ _ AGF) as AGLF.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AGF) in HAD; [| intros a Ha; cbn in Ha; right; right; exists (pb, bio, 128); split; [exact HBIN'| cbn; clear - Ha; lia]].
  unfold exlock_free in HXL.
  apply (rw_cells_agree _ _ _ _ _ AGF) in HXL; [| intros a Ha; cbn in Ha; right; right; exists (p_xl E, e_xl E, 40); split; [exact HXIN'| cbn; clear - Ha; lia]].
  rename HXL into HXL3.
  pose proof (crypto_statics_agree' _ _ _ CS AGLF) as CS3. clear CS.
  pose proof (dc_staticsA_lib _ _ _ DC AGLF) as DC3. clear DC.
  apply (ro_cells_libS OW m m3 _ _ 0xba46c0 0xba8ae0) in HXLp; [| exact AGLF| unfold LIBW_S; cbn; tauto| cbn; clear; lia| cbn; clear; lia].
  apply (ro_cells_libS OW m m3 _ _ 0xba46c0 0xba8ae0) in HXM; [| exact AGLF| unfold LIBW_S; cbn; tauto| cbn; clear; lia| cbn; clear; lia].
  unfold mutex_free_cells, zeros4, MallocRep.wz in HXL3. cbn [repeat] in HXL3.
  assert (HXL30 : frozen (rw_cells ctasegs m3 (e_xl E) mutex_free_cells)) by exact HXL3.
  (* [comment removed for export] *)
  ablock HEAP3 HBIN' ACCB OFFBS.
  assert (ACCG : acc ctasegs m3 12208768 328).
  { eapply (af_lib_acc_lit _ AF Σ1 m3 (0xba4a80, 328, 416)); [exact (@AH_art (push AR f 2) _ _ _ _ HEAP3)| vm_compute; reflexivity| cbn; clear; lia| cbn; clear; lia]. }
  destruct (@AH_shb (push AR f 2) _ _ _ _ HEAP3) as [SHB1 SHB2].
  assert (SHR : 2147450880 <= shad f /\ shad f + 32 <= 17594333495296).
  { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(clear - G1; lia) ltac:(clear; lia)) as DP.
    assert (DQ : f / 8 + 32 <= 2 ^ 44) by (assert (f / 8 < 2 ^ 44 - 32); [apply Z.div_lt_upper_bound; [clear; lia| clear - G3 D3; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia]| clear - H; lia]).
    clear - DP DQ. lia. }
  assert (SHF : shad f + 32 <= lo) by (clear - SHR D2 CEIL; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia).
  ablock HEAP3 HXIN' ACCX OFFXS. clear ACCX.
  pose proof (munch_refl [(e_xl E, e_xl E + 40); (lo, bv_unsigned sp + -16); (bio + 112, bio + 112 + 16)]%Z m3) as MU. pose proof (wmono_refl ctasegs m3) as WM.
  assert (OFF : offshW [(e_xl E, e_xl E + 40); (lo, bv_unsigned sp + -16); (bio + 112, bio + 112 + 16)]%Z).
  { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. cbn [ar_SP0 push amb] in *. split; [revert OFFXS; unfold SHLO, SHHI; clear; intros; lia|].
    split; [clear - D2 CEIL; lia|]. split; [revert OFFBS; unfold SHLO, SHHI; clear; intros; lia| exact I]. }
  assert (WOK : Forall (@BnHeapA.aclient_write_ok (push AR f 2) (OW ++ LB)) [(e_xl E, e_xl E + 40); (lo, bv_unsigned sp + -16); (bio + 112, bio + 112 + 16)]%Z).
  { constructor; [right; right; exists (p_xl E, e_xl E, 40); split; [exact HXIN'| cbn; clear; lia]|].
    constructor; [left; cbn [fst snd]; unfold BnHeapA.ACEIL, USTACK_TOP in *; cbn [ar_SP0 push amb] in *; clear - CEIL SPT; lia|].
    constructor; [right; right; exists (pb, bio, 128); split; [exact HBIN'| cbn; clear; lia]| constructor]. }
  assert (STK : lo <= spa - 65600) by (clear - LO SPAL; lia).
  pose proof CEIL as CEILP. unfold BnHeapA.ACEIL in CEILP.
  destruct DC3 as (DCa & DCb & DCc & DCd & DCe & DCf & DCg).
  unfold AP_DC_INITED, AP_DC_KEY, AP_DC_ONCE1, AP_DC_ONCE1_RET, AP_DC_ONCE2, AP_DC_ONCE2_RET, AP_TSD_DC_SLOT, TSD_MAIN, V_DC_KEY, AP_DC_INT, MallocRep.wz in DCa, DCb, DCc, DCd, DCe, DCf, DCg.
  cbn [Z.add] in DCa, DCb, DCc, DCd, DCe, DCf, DCg.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. ab_shload 8. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep. OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step. rewrite ?zxb_z8, ?sxb_z8. if_false. zstep. zstep.
  pose proof (AH_frame _ _ _ _ _ _ HEAP3 MU WM WOK) as HEAP0.   (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (@get_ex_data_global_specA (push AR f 2)) with (lo := lo);
      [exact HEAP0| rewrite ESPA; exact ST3| exact MI3| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEILP| rewrite ESPA; clear - STK; lia
      | rewrite ESPA; unfold USTACK_TOP; clear - SPAH SPT; lia| reflexivity
      | unfold dc_staticsA, AP_DC_INITED, AP_DC_KEY, AP_DC_ONCE1, AP_DC_ONCE1_RET, AP_DC_ONCE2, AP_DC_ONCE2_RET, AP_TSD_DC_SLOT, TSD_MAIN, V_DC_KEY, AP_DC_INT, MallocRep.wz; cbn [Z.add];
        exact (conj DCa (conj DCb (conj DCc (conj DCd (conj DCe (conj DCf DCg))))))| reflexivity]. }
  clear DCa DCb DCc DCd DCe DCf DCg HEAP0. post_call ctasegs m0. rewrite ?ESPA in *.
  match goal with H : stk ctasegs _ lo spa |- _ => rename H into ST4 end. match goal with H : mem_inv ctasegs _ |- _ => rename H into MI4 end.
  match goal with H : @BnHeapA.AHEAP _ Σ1 OW LB _ |- _ => rename H into HEAP4 end.
  (* [comment removed for export] *)
  unfold AP_DC_EXLOCK, AP_DC_INT. change (12208768 + 8) with 12208776.
  zstep. first [if_false| idtac].
  zstep. zstep. zstep. zstep.
  name_mem m4. eapply evt_cut.
  { eapply (@get_and_lock_specA (push AR f 2)) with (lo := lo) (xl := e_xl E);
      [exact HEAP4| rewrite ESPA; exact ST4| exact MI4| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEILP| rewrite ESPA; clear - STK; lia
      | rewrite ESPA; unfold USTACK_TOP; clear - SPAH SPT; lia| exact HXLp| exact HXL3| exact XLO| exact AL4| reflexivity| reflexivity| reflexivity]. }
  clear HXL3 HEAP4. post_call ctasegs m4. rewrite ?ESPA in *.
  match goal with H : stk ctasegs _ lo spa |- _ => rename H into ST5 end. match goal with H : mem_inv ctasegs _ |- _ => rename H into MI5 end.
  match goal with H : rw_cells ctasegs _ (e_xl E) _ |- _ => rename H into HXL5 end.
  unfold mutex_locked_cells, zeros4, EBUSY, MallocRep.wz in HXL5. cbn [repeat app] in HXL5.
  (* [comment removed for export] *)
  unfold AP_DC_EXMETH_BIO, AP_DC_INT. change (12208768 + 112) with 12208880.
  zstep. first [if_false| idtac].
  zstep. zstep.
  zstep. zstep. zstep.
  name_mem m5.
  match goal with H : stk ctasegs m5 lo spa |- _ => rename H into ST6 end. match goal with H : mem_inv ctasegs m5 |- _ => rename H into MI6 end.
  eapply evt_cut.
  { eapply OPENSSL_sk_num_null_spec with (lo := lo); [rewrite ESPA; exact ST6| exact MI6| unfold SEGTOP_A; clear - CEILP D1 C1 CEIL; cbn [ar_SP0 push amb] in *; lia| rewrite ESPA; clear - STK; lia| reflexivity]. }
  post_call ctasegs m5. rewrite ?ESPA in *.
  match goal with H : stk ctasegs _ lo spa |- _ => rename H into ST7 end. match goal with H : mem_inv ctasegs _ |- _ => rename H into MI7 end.
  (* [comment removed for export] *)
  zstep. first [if_true| idtac].
  zstep. zstep. zstep.
  zstep. name_mem m6.
  match goal with H : stk ctasegs m6 lo spa |- _ => rename H into ST8 end. match goal with H : mem_inv ctasegs m6 |- _ => rename H into MI8 end.
  eapply evt_cut.
  { eapply CRYPTO_THREAD_unlock_spec with (lo := lo) (X := e_xl E);
      [rewrite ESPA; exact ST8| exact MI8| unfold SEGTOP_A; clear - CEILP D1 C1 CEIL; cbn [ar_SP0 push amb] in *; lia| rewrite ESPA; clear - STK; lia
      | exact HXL5| exact XLO| exact AL4| reflexivity]. }
  clear HXL5. post_call ctasegs m6. rewrite ?ESPA in *.
  match goal with H : stk ctasegs _ lo spa |- _ => rename H into ST9 end. match goal with H : mem_inv ctasegs _ |- _ => rename H into MI9 end.
  match goal with H : rw_cells ctasegs _ (e_xl E) _ |- _ => rename H into HXL9 end.
  (* [comment removed for export] *)
  zstep.
  zstep. zstep. zstep. zstep. zstep.
  name_mem m7.
  match goal with H : stk ctasegs m7 lo spa |- _ => rename H into ST10 end. match goal with H : mem_inv ctasegs m7 |- _ => rename H into MI10 end.
  match goal with H : munch _ m3 m7 |- _ => rename H into MU7 end. match goal with H : wmono ctasegs m3 m7 |- _ => rename H into WM7 end.
  (* [comment removed for export] *)
  assert (MU7' : munch [(lo, bv_unsigned sp + -16); (bio + 112, bio + 112 + 16)]%Z m3 m7).
  { eapply (munch_restore _ m3 m7 (e_xl E) mutex_free_cells); change (Z.of_nat (cells_size mutex_free_cells)) with 40.
    - exact MU7.
    - exact HXL30.
    - unfold mutex_free_cells, zeros4, MallocRep.wz. cbn [repeat]. exact HXL9.
    - unfold SEGTOP_A. clear - XB4. lia. }
  assert (WOK' : Forall (@BnHeapA.aclient_write_ok (push AR f 2) (OW ++ LB)) [(lo, bv_unsigned sp + -16); (bio + 112, bio + 112 + 16)]%Z).
  { constructor; [left; cbn [fst snd]; unfold BnHeapA.ACEIL, USTACK_TOP in *; cbn [ar_SP0 push amb] in *; clear - CEIL SPT; lia|].
    constructor; [right; right; exists (pb, bio, 128); split; [exact HBIN'| cbn; clear; lia]| constructor]. }
  pose proof (AH_frame _ _ _ _ m7 _ HEAP3 MU7' WM7 WOK') as HEAP7.
  assert (CS7 : crypto_statics m7).
  { eapply crypto_statics_agree; [apply (agree_on_of_munch_nw _ _ _ MU7')| | exact CS3].
    intros a Ha. cbn [outside fst snd]. revert Ha BB0 BB3 BB4 CEILP D1. unfold libw, LIBW_A, BnHeapA.ACEIL. cbn [rin_ivs fst snd ar_SP0 push amb]. clear. intros. lia. }
  apply evt_done. eapply cps_step_same.
  { eapply (@CRYPTO_free_null_cpsA (push AR f 2) UK BE) with (lo := lo);
      [exact HEAP7| rewrite ESPA; exact ST10| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEILP| rewrite ESPA; unfold CRYPTO_FREE_STACK, RT_STACK; clear - STK; lia
      | rewrite ESPA; unfold USTACK_TOP; clear - SPAH SPT; lia| rewrite ESPA; clear - SPA32; Z.div_mod_to_equations; lia| exact MI10| reflexivity| exact CS7| reflexivity
      | (* [comment removed for export] *)
        rewrite ESPA; eapply (uw_call m m7 spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) ras);
        [ exact UW
        | eapply agree_on_trans; [eapply agree_on_mono; [exact AGF|]; intros a Ha; left; exact Ha
          | eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU7')|]; intros a Ha; cbn [outside fst snd];
            clear - Ha BB0 BB3 BB4 CEIL CEILP LO; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia]
        | reflexivity | clear - SPAH; lia | uchk_open; clear - SP16; Z.div_mod_to_equations; lia | clear - SPT; unfold USTACK_TOP in *; lia
        | apply bv_unsigned_in_range
        | rewrite !Z_to_bv_bv_unsigned; cbn [app]; match goal with H : rw_cells ctasegs m7 (bv_unsigned sp + -16) _ |- _ => exact H end ]
      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_cfed_free CTX)]. }
  cbv beta. intros ms8 PO. unfold cfree_null_post in PO. rewrite ?ESPA in PO.
  destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F8 & fc8 & m8 & -> & MI11 & ST11 & HEAP8 & AG8).
  match goal with H : rw_cells ctasegs m7 spa _ |- _ => rename H into FRL7 end.
  match goal with H : rw_cells ctasegs m7 (bv_unsigned sp + -16) _ |- _ => rename H into FRH7 end.
  match goal with H : rw_cells ctasegs m7 (bio + 112) _ |- _ => rename H into HAD7 end.
  apply (rw_cells_agree _ _ _ _ _ AG8) in FRL7; [| intros a Ha; cbn in Ha; left; unfold USTACK_TOP; clear - Ha SPT SPAH GSZ; lia].
  apply (rw_cells_agree _ _ _ _ _ AG8) in FRH7; [| intros a Ha; cbn in Ha; left; unfold USTACK_TOP; clear - Ha SPT SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ AG8) in HAD7; [| intros a Ha; cbn in Ha; right; right; exists (pb, bio, 128); split; [exact HBIN'| cbn; clear - Ha; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG8) in HXL9; [| intros a Ha; cbn in Ha; right; right; exists (p_xl E, e_xl E, 40); split; [exact HXIN'| cbn; clear - Ha; lia]].
  clear MU7 WM7 HEAP7 CS7 ST10 MI10.
  assert (HXL8f : frozen (rw_cells ctasegs m8 (e_xl E) mutex_free_cells)) by (unfold mutex_free_cells, zeros4, MallocRep.wz; cbn [repeat]; exact HXL9). clear HXL9.
  pose proof (munch_refl [(lo, bv_unsigned sp + -16); (bio + 112, bio + 112 + 16)]%Z m8) as MU8. pose proof (wmono_refl ctasegs m8) as WM8.
  assert (OFF8 : offshW [(lo, bv_unsigned sp + -16); (bio + 112, bio + 112 + 16)]%Z).
  { cbn [offshW]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. cbn [ar_SP0 push amb] in *.
    split; [clear - D2 CEIL; lia|]. split; [revert OFFBS; unfold SHLO, SHHI; clear; intros; lia| exact I]. }
  clear ACCB OFFBS. ablock HEAP8 HBIN' ACCB OFFBS.
  rewrite (ret_pc_even 2074976) by (clear; lia).
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep.
  zstep. zstep. zstep. zstep.
  match goal with H : stk ctasegs m8 lo spa |- _ => rename H into ST12 end. match goal with H : mem_inv ctasegs m8 |- _ => rename H into MI12 end.
  eapply evt_cut.
  { eapply OPENSSL_sk_free_null_spec with (lo := lo); [rewrite ESPA; exact ST12| exact MI12| unfold SEGTOP_A; clear - CEILP D1 C1 CEIL; cbn [ar_SP0 push amb] in *; lia| rewrite ESPA; clear - STK; lia| reflexivity]. }
  post_call ctasegs m8. rewrite ?ESPA in *.
  match goal with H : stk ctasegs _ lo spa |- _ => rename H into ST13 end. match goal with H : mem_inv ctasegs _ |- _ => rename H into MI13 end.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  name_mem m10.
  match goal with H : stk ctasegs m10 lo spa |- _ => rename H into ST14 end. match goal with H : mem_inv ctasegs m10 |- _ => rename H into MI14 end.
  match goal with H : munch _ m8 m10 |- _ => rename H into MU10 end. match goal with H : wmono ctasegs m8 m10 |- _ => rename H into WM10 end.
  pose proof (AH_frame _ _ _ _ m10 _ HEAP8 MU10 WM10 WOK') as HEAP10.
  apply evt_done. eapply cps_step_same.
  { eapply (@asan_memset_cpsA (push AR f 2)) with (lo := lo) (bd := (pb, bio, 128)) (d := bio + 112) (n := 16) (c := Z_to_bv 8 0);
      [exact HEAP10| rewrite ESPA; exact ST14| unfold BnHeapA.ACEIL; cbn [ar_SP0 push amb]; exact CEILP| rewrite ESPA; unfold RT_STACK; clear - STK; lia
      | rewrite ESPA; unfold USTACK_TOP; clear - SPAH SPT; lia| rewrite ESPA; clear - SPA32; Z.div_mod_to_equations; lia| exact MI14| reflexivity
      | exact HBIN'| cbn; clear; lia| cbn; clear; lia| clear; lia| reflexivity| reflexivity| reflexivity]. }
  cbv beta. intros ms11 PO. unfold icall_post in PO. rewrite ?ESPA in PO.
  destruct PO as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F9 & fc9 & m11 & -> & MI15 & ST15 & HEAP11 & WM11 & AG11 & [BY11 WR11]).
  pose proof (zero16_link_cells m11 (bio + 112) BY11 WR11) as HAD11. clear BY11 WR11.
  match goal with H : rw_cells ctasegs m10 spa _ |- _ => rename H into FRL10 end.
  match goal with H : rw_cells ctasegs m10 (bv_unsigned sp + -16) _ |- _ => rename H into FRH10 end.
  apply (rw_cells_agree _ _ _ _ _ AG11) in FRL10;
    [| intros a Ha; cbn in Ha; split; [left; unfold USTACK_TOP; clear - Ha SPT SPAH GSZ; lia| clear - Ha BB3 CEILP STK; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG11) in FRH10;
    [| intros a Ha; cbn in Ha; split; [left; unfold USTACK_TOP; clear - Ha SPT SPAH; lia| clear - Ha BB3 CEILP STK SPAH; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia]].
  rewrite (ret_pc_even 2075024) by (clear; lia).
  (* [comment removed for export] *)
  lazymatch type of FRL10 with rw_cells _ ?mm _ [?c0; ?c1; ?c2; ?c3; ?c4; C8 ?v5; ?c6; C8 ?v7; ?c8; ?c9; C8 ?v10; ?c11] =>
    pose proof (c8_blur_at mm spa [c0; c1; c2; c3; c4] v5 [c6; C8 v7; c8; c9; C8 v10; c11] FRL10) as FRLa; cbn [app] in FRLa;
    pose proof (c8_blur_at mm spa [c0; c1; c2; c3; c4; CB 8 (le8 v5); c6] v7 [c8; c9; C8 v10; c11] FRLa) as FRLb; cbn [app] in FRLb;
    pose proof (c8_blur_at mm spa [c0; c1; c2; c3; c4; CB 8 (le8 v5); c6; CB 8 (le8 v7); c8; c9] v10 [c11] FRLb) as FRLc; cbn [app] in FRLc;
    clear FRLa FRLb
  end.   (* [comment removed for export] *)
  eapply (cfed_epi_cps _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
    [exact HEAP11 | intros b Hb; apply FRESH; apply in_or_app; right; exact Hb | exact ST15 | exact CEIL | clear - STK; lia | unfold USTACK_TOP; clear - SPT; lia
    | exact SPAL | exact SPAH | exact GSZ | exact SAVJ | exact MI15 | exact FRLc | exact FRH10 | reflexivity |].
  intros Σ' m' x10' HEAP' CR' EL' ST' MI' AG'.
  apply (rw_cells_agree _ _ _ _ _ AG') in HAD11; [| intros a Ha; cbn in Ha; right; right; exists (pb, bio, 128); split; [exact HBIN'| cbn; clear - Ha; lia]].
  unfold frozen in HXL8f.
  apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU10)) in HXL8f;
    [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha DJX XB3 CEILP CEIL; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia].
  apply (rw_cells_agree _ _ _ _ _ AG11) in HXL8f;
    [| intros a Ha; cbn in Ha; split; [right; right; exists (p_xl E, e_xl E, 40); split; [exact HXIN'| cbn; clear - Ha; lia]| clear - Ha DJX; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG') in HXL8f; [| intros a Ha; cbn in Ha; right; right; exists (p_xl E, e_xl E, 40); split; [exact HXIN'| cbn; clear - Ha; lia]].
  apply cps_post. intros c Hc. exists Σ'. split; [| rewrite EL', EL1; reflexivity].
  eapply ASTA_conseq; [exact Hc|]. intros ms0 <-. unfold free_ex_data_postA, MallocRep.wz.
  do 17 eexists. exists m'. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|].
  split.
  { assert (INC : forall b : block, In b (OW ++ LB) -> In b (OW ++ LB)) by (intros b Hb; exact Hb).
    assert (WIN : forall m1 m2, munch [(lo, bv_unsigned sp + -16); (bio + 112, bio + 112 + 16)]%Z m1 m2 ->
                   agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (bio + 112 <= a < bio + 112 + 16)) m1 m2).
    { intros m1 m2 MUx. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUx)|].
      intros a [Ha Hx]. cbn [outside fst snd].
      assert (A1 : ~ (bv_unsigned sp - (bv_unsigned sp - lo) <= a < bv_unsigned sp)) by (eapply (acl_off_frame _ _ _ _ _ _ lo); [exact HEAP| exact INC| exact CEIL| clear; lia| exact Ha]).
      clear - A1 Hx. repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
    eapply agree_on_trans; [eapply agree_on_mono; [exact AGF|]; intros a [Ha _]; exact Ha|].
    eapply agree_on_trans; [exact (WIN _ _ MU7')|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AG8|]; intros a [Ha _]; eapply acl_sub; [exact INC| | exact Ha]; clear - SPAH; lia|].
    eapply agree_on_trans; [exact (WIN _ _ MU10)|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AG11|]; intros a [Ha Hx]; split; [eapply acl_sub; [exact INC| | exact Ha]; clear - SPAH; lia| exact Hx]|].
    eapply agree_on_mono; [exact AG'|]. intros a [Ha _]. eapply acl_sub; [exact INC| | exact Ha]. clear - SPAH; lia. }
  split; [exact HEAP'|].
  split; [rewrite EL', EL1; reflexivity|]. split; [rewrite CR', CR1; clear; lia|].
  split; [exact HAD11|].
  unfold exlock_free. exact HXL8f.
Qed.
End WithRT2.
