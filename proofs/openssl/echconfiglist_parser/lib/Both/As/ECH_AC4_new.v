(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCallX AsWalk AsAtomics AsStack0 ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AKit ECH_AsKit ECH_AKitS ECH_AStmt_C0 ECH_AStmt_C1 ECH_AC1_free ECH_AC1_freeopt ECH_AStmt_C2 ECH_APF_C4 ECH_AStmt_C4 ECH_AC4_rep ECH_AC4_frame ECH_AC4_egs.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition AEN_RA1 : Z := 0x1f0fe0.   (* [comment removed for export] *)
Definition AEN_L1 : Z := 0x1f107c.    (* [comment removed for export] *)
Definition AEN_RA2 : Z := 0x1f1204.   (* [comment removed for export] *)
Definition AEN_RA3 : Z := 0x1f1244.   (* [comment removed for export] *)
Definition AEN_FILE : Z := 0x40b8f.   (* [comment removed for export] *)
Definition SHBv : Z := 0x7fff8000.    (* [comment removed for export] *)

Ltac ret_lit RA := replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
Ltac ret_lit_any := match goal with |- context [ret_pc (Z_to_bv 64 ?r)] => ret_lit r end.
Ltac show_goal := match goal with |- evt _ _ (MS ?R _ ?pc _ _ ?mx _) => idtac "PC" pc; idtac R end.
(* [comment removed for export] *)
Ltac acc_now ACC BASE MUS NSW :=
  lazymatch type of BASE with accessible _ ?a ?n =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx a n) by (eapply accessible_across; [exact BASE| exact MUS| exact NSW]) end end.
(* [comment removed for export] *)
Ltac ck8_now BASE MUS NSW a := let ACC := fresh "ACC" in acc_now ACC BASE MUS NSW; sh_align a; ck8_check ACC a; clear ACC.

Ltac cases16 t :=
  let C := fresh "C" in
  assert (C : t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7 \/ t = 8 \/ t = 9 \/ t = 10 \/ t = 11
              \/ t = 12 \/ t = 13 \/ t = 14 \/ t = 15) by lia;
  repeat (destruct C as [C|C]; [subst t|]); [..| subst t].

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Definition aen_frame (j : list byte) (s5 s4 s3 s2 s1 s0 ra : word) : list cell := [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition aen_E0 (E : errst) : errst :=
    let t := err_next (es_top E) in mkERRST (es_slots E) t (if t =? es_bottom E then err_next (es_bottom E) else es_bottom E).

  (* [comment removed for export] *)
  Lemma aen_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      ACONST m -> stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists a0' m1 j,
          ms' = MS (mkR (Z_to_bv 64 AEN_RA1) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 1) a0' a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 SHBv) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_ossl_err_get_state_int) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -64, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -64)
          /\ rw_cells asegs m1 (bv_unsigned sp + -64) (aen_frame j s5 s4 s3 s2 s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ERR_new) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros AC ST CEIL LO MI. unfold P_ERR_new, P_ossl_err_get_state_int, AEN_RA1, SHBv, aen_frame. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (ACONST_shbase m AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 64%nat ST. bgo. step. finish. exact FR.
  Qed.

  (* [comment removed for export] *)
  Lemma aen_seg2a :
    forall (ra0 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es : Z) (E : errst),
      ERRSTm m es E -> 0 < es -> es + 904 < 2^47 -> es mod 16 = 0 -> aapp es 904 -> accessible m es 904 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists a0' a1' a2' a3' m1,
          ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 es) a0' a1' a2' a3' a4 a5 a6 a7
                       s2 (Z_to_bv 64 SHBv) (Z_to_bv 64 (err_next (es_top E))) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 AEN_L1) fc None m1 (seg_rom asegs)
          /\ munch [(es, es + 904)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ ERRSTm m1 es (aen_E0 E) /\ accessible m1 es 904)
        (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 es) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 SHBv) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AEN_RA1)) fc None m (seg_rom asegs)).
  Proof.
    intros until E. intros EST POS BL AL AP ACC0 MI. unfold AEN_RA1, AEN_L1, SHBv. ret_lit 0x1f0fe0.
    pose proof (munch_refl [(es, es + 904)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(es, es + 904)])
      by (apply Forall_cons; [cbn [fst snd]; exact (aapp_not_shadowland _ _ AP)| apply Forall_nil]).
    unfold ERRSTm in EST. destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    set (top := es_top E) in *. set (bot := es_bottom E) in *. arr_lens SL.
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + 896).
    bgo. rewrite sx32_wz by lia. unfold wz. rewrite (unsigned_lit top) by lia. rewrite swrap32_small by lia. if_cases K2; zify_cond K2; [kill K2|]; clear K2.
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + 896).
    bgo.
    lazymatch type of TB with context [C4 (Z_to_bv 64 ?e)] =>
      replace e with (err_next top) in * by (clear - TR; clearbody top; cases16 top; vm_compute; reflexivity) end.
    pose proof (err_next_range top TR) as TR'. set (t' := err_next top) in *.
    (* [comment removed for export] *)
    replace (Z.shiftr (es + 900) 3) with (Z.shiftr (es + 896) 3) by (rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - AL; Z.div_mod_to_equations; lia).
    ck8_now ACC0 MU NSW (es + 896).
    bgo. rewrite sx32_wz by lia. unfold wz.
    if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      finish.
      + unfold ERRSTm, aen_E0. fold top. fold bot. fold t'. cbn [es_slots es_top es_bottom].
        replace (t' =? bot) with false by (symmetry; apply Z.eqb_neq; exact K1).
        unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP, wz.
        repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
      + eapply accessible_across; [exact ACC0| exact MU| exact NSW].
    - (* [comment removed for export] *)
      ck8_now ACC0 MU NSW (es + 896).
      bgo_to AEN_L1.
      match type of TB with context [C4 (Z_to_bv 64 ?e)] => tryif is_var e then fail else
        replace e with (err_next t') in * by (clear - TR'; clearbody t'; cases16 t'; vm_compute; reflexivity) end.
      finish.
      + unfold ERRSTm, aen_E0. fold top. fold bot. fold t'. cbn [es_slots es_top es_bottom].
        replace (t' =? bot) with true by (symmetry; apply Z.eqb_eq; exact K1). rewrite <- K1.
        pose proof (err_next_range t' TR').
        unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP, wz.
        repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
      + eapply accessible_across; [exact ACC0| exact MU| exact NSW].
  Qed.

  (* [comment removed for export] *)
  Lemma aen_seg2b :
    forall (ra0 sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es t : Z) (E : errst),
      ERRSTm m es E -> 0 <= t < 16 -> 0 < es -> es + 904 < 2^47 -> es mod 16 = 0 -> aapp es 904 -> accessible m es 904 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists a3' a4' a5' a6' m1,
          ms' = MS (mkR (Z_to_bv 64 AEN_RA2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 es) (Z_to_bv 64 (sl_file (slot_at E t))) (Z_to_bv 64 AEN_FILE)
                       (Z_to_bv 64 112) a3' a4' a5' a6' a7 (Z_to_bv 64 (es + t * 8 + 576)) (Z_to_bv 64 SHBv) (Z_to_bv 64 (t * 8)) (Z_to_bv 64 (Z.shiftr (es + t * 8 + 576) 3 + SHBv))
                       s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom asegs)
          /\ munch [(es, es + 904)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ ERRSTm m1 es (es_with_slot E t (slot_wipe (slot_at E t))) /\ accessible m1 es 904)
        (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 es) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 SHBv) (Z_to_bv 64 t) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AEN_L1) fc None m (seg_rom asegs)).
  Proof.
    intros until E. intros EST TR' POS BL AL AP ACC0 MI. unfold AEN_RA2, AEN_L1, AEN_FILE, P_CRYPTO_free, SHBv.
    pose proof (munch_refl [(es, es + 904)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(es, es + 904)])
      by (apply Forall_cons; [cbn [fst snd]; exact (aapp_not_shadowland _ _ AP)| apply Forall_nil]).
    unfold ERRSTm in EST. destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    arr_lens SL.
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + t * 4 + 512).
    pose proof (zero16_byte_m _ _ t F6 TR') as RD. replace (es + 512 + t * 4) with (es + t * 4 + 512) in RD by lia. bgo. clear RD. nrm. unfold wz.
    bgo.
    (* [comment removed for export] *)
    ck8_now ACC0 MU NSW (es + t * 8 + 256). bgo. arr_store64 F4 t (wz 0). rewrite upd_zero16 in F4 by lia.
    bgo. ck8_now ACC0 MU NSW (es + t * 8 + 384). bgo. arr_store64 F5 t (wz 0). rewrite upd_zero16 in F5 by lia.
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + t * 4 + 512). bgo. arr_store32 F6 t (wz 0). rewrite upd_zero16 in F6 by lia.
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + t * 4 + 64). bgo. arr_store32 F2 t (wz 0). rewrite upd_zero16 in F2 by lia.
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + t * 4). bgo. arr_store32 F1 t (wz 0).
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + t * 8 + 128). bgo. arr_store64 F3 t (wz 0).
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + t * 4 + 704). bgo.
    arr_store32 F8 t (Z_to_bv 64 (-1)). apply (u32arr_upd_le4 _ _ _ _ _ _ le4_minus1) in F8.
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + t * 8 + 576).
    pose proof (u64arr_read_m _ _ _ t _ F7 (slot_nth E t (fun s => wz (sl_file s)) SL TR') ltac:(lia)) as RD.
    replace (es + 576 + t * 8) with (es + t * 8 + 576) in RD by lia. bgo. clear RD.
    bgo. step. unfold wz.
    finish.
    + eapply (ERRSTm_with_slot _ es E t (slot_wipe (slot_at E t))); try eassumption; try reflexivity;
        try (upd_keep_tac E t SL TR'); cbn [slot_wipe sl_flags sl_buffer sl_line]; lia.
    + eapply accessible_across; [exact ACC0| exact MU| exact NSW].
  Qed.

  (* [comment removed for export] *)
  Lemma aen_seg3 :
    forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es t : Z) (E : errst),
      ERRSTm m es E -> 0 <= t < 16 -> 0 < es -> es + 904 < 2^47 -> aapp es 904 -> accessible m es 904 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 AEN_RA3) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (es + t * 8 + 768)) (Z_to_bv 64 (sl_func (slot_at E t))) (Z_to_bv 64 AEN_FILE)
                       (Z_to_bv 64 114) a3 a4 a5 a6 a7 (Z_to_bv 64 (es + t * 8 + 576)) (Z_to_bv 64 (Z.shiftr (es + t * 8 + 768) 3 + SHBv))
                       (Z_to_bv 64 (t * 8)) (Z_to_bv 64 (Z.shiftr (es + t * 8 + 576) 3 + SHBv)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom asegs)
          /\ munch [(es, es + 904)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ ERRSTm m1 es (es_with_slot E t (slot_file0 (slot_at E t))) /\ accessible m1 es 904)
        (MS (mkR (Z_to_bv 64 AEN_RA2) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 es) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (es + t * 8 + 576)) (Z_to_bv 64 SHBv) (Z_to_bv 64 (t * 8)) (Z_to_bv 64 (Z.shiftr (es + t * 8 + 576) 3 + SHBv)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AEN_RA2)) fc None m (seg_rom asegs)).
  Proof.
    intros until E. intros EST TR' POS BL AP ACC0 MI. unfold AEN_RA2, AEN_RA3, AEN_FILE, P_CRYPTO_free, SHBv. ret_lit 0x1f1204.
    pose proof (munch_refl [(es, es + 904)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(es, es + 904)])
      by (apply Forall_cons; [cbn [fst snd]; exact (aapp_not_shadowland _ _ AP)| apply Forall_nil]).
    unfold ERRSTm in EST. destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    arr_lens SL.
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + t * 8 + 576). bgo. arr_store64 F7 t (wz 0).
    bgo. ck8_now ACC0 MU NSW (es + t * 8 + 768).
    pose proof (u64arr_read_m _ _ _ t _ F9 (slot_nth E t (fun s => wz (sl_func s)) SL TR') ltac:(lia)) as RD.
    replace (es + 768 + t * 8) with (es + t * 8 + 768) in RD by lia. bgo. clear RD.
    bgo. step. unfold wz.
    finish.
    + pose proof (slot_at_own _ E t RG SL TR') as (O1 & O2 & O3).
      eapply (ERRSTm_with_slot _ es E t (slot_file0 (slot_at E t))); try eassumption; try reflexivity;
        try (upd_keep_tac E t SL TR'); cbn [slot_file0 sl_flags sl_buffer sl_line]; lia.
    + eapply accessible_across; [exact ACC0| exact MU| exact NSW].
  Qed.

  (* [comment removed for export] *)
  Lemma aen_seg4 :
    forall (sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (es t lo : Z) (E : errst) (j : list byte),
      ERRSTm m es E -> 0 <= t < 16 -> 0 < es -> es + 904 <= lo -> aapp es 904 -> accessible m es 904 -> lo <= bv_unsigned sp - 64 -> mem_inv asegs m ->
      stk asegs m lo (bv_unsigned sp + -64) -> rw_cells asegs m (bv_unsigned sp + -64) (aen_frame j s5 s4 s3 s2 s1 s0 ra) ->
      evt asegs (fun ms' => exists a0' m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom asegs)
          /\ munch [(es, es + 904)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp)
          /\ ERRSTm m1 es (es_with_slot E t (slot_func0 (slot_at E t))))
        (MS (mkR (Z_to_bv 64 AEN_RA3) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0x (Z_to_bv 64 (es + t * 8 + 768)) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (es + t * 8 + 576)) (Z_to_bv 64 (Z.shiftr (es + t * 8 + 768) 3 + SHBv)) (Z_to_bv 64 (t * 8))
                 (Z_to_bv 64 (Z.shiftr (es + t * 8 + 576) 3 + SHBv)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AEN_RA3)) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros EST TR' POS BL AP ACC0 LO MI ST FR. unfold AEN_RA3, AEN_FILE, SHBv, aen_frame in *. ret_lit 0x1f1244. acb.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(es, es + 904)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(es, es + 904)])
      by (apply Forall_cons; [cbn [fst snd]; exact (aapp_not_shadowland _ _ AP)| apply Forall_nil]).
    unfold ERRSTm in EST. destruct EST as (SL & TR & BR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & TB & RG).
    unfold O_ES_MARKS, O_ES_BUFFER, O_ES_DATA, O_ES_DSIZE, O_ES_DFLAGS, O_ES_FILE, O_ES_LINE, O_ES_FUNC, O_ES_TOP in *.
    arr_lens SL.
    (* [comment removed for export] *)
    bgo. ck8_now ACC0 MU NSW (es + t * 8 + 768). bgo. arr_store64 F9 t (wz 0).
    bgo.
    release_frame FR ST (bv_unsigned sp). step. finish.
    pose proof (slot_at_own _ E t RG SL TR') as (O1 & O2 & O3).
    eapply (ERRSTm_with_slot _ es E t (slot_func0 (slot_at E t))); try eassumption; try reflexivity;
      try (upd_keep_tac E t SL TR'); cbn [slot_func0 sl_flags sl_buffer sl_line]; lia.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Hypothesis EGS : egs_stmt H.
  Let HH : asan_rt_hyps H := proj1 HHx.
  Let PERM : rheap_perm H := HHx_rheap_perm H HHx.

  (* [comment removed for export] *)
  Definition strw (E : errst) (L : list block) (m : mem) : Prop :=
    forall b, In b (blocks_ERRST E) -> In b L ->
      (exists bs, rw_cells asegs m (blk_addr b) [CB (Z.to_nat (blk_size b)) bs]) /\ addressable m (blk_addr b) (blk_size b).

  Lemma strw_es : forall E L s m m' es n,
    as_RHEAP H s L m -> In (es) L -> blk_size es = n -> n = 904 ->
    (forall b, In b (blocks_ERRST E) -> 0 <= blk_size b <= 32) ->
    strw E L m -> munch [(blk_addr es, blk_addr es + 904)] m m' -> wmono asegs m m' -> strw E L m'.
  Proof.
    intros E L s m m' es n HP IES SZ -> SMALL SW MU WM b Hb HbL. destruct (SW b Hb HbL) as [[bs BC] AD].
    pose proof (ablocks_apart_by_size H HH _ _ _ _ _ HP HbL IES ltac:(rewrite SZ; pose proof (SMALL b Hb); lia)) as DJ. rewrite SZ in DJ.
    pose proof (ah_blocks H HH _ _ _ _ HP HbL) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). pose proof (ah_blocks H HH _ _ _ _ HP IES) as (_ & _ & _ & _ & _ & _ & E7). rewrite SZ in E7.
    pose proof (rw_cells_bound _ _ _ _ BC) as BB. cbn [cells_size csize] in BB. rewrite Nat.add_0_r, Z2Nat.id in BB by lia.
    split.
    - exists bs. eapply rw_cells_transport; [exact BC| exact MU| exact WM|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. cbn. lia.
    - eapply addressable_transport; [exact AD| exact MU| exact WM|]. cbn. split; [| exact I].
      pose proof (aapp_bounds _ _ B7 B3) as (_ & _ & T1 & _).
      pose proof (aapp_disjoint_sh (blk_addr es) 904 (blk_addr b) (blk_size b) E7 ltac:(lia) ltac:(lia) B3). lia.
  Qed.
  Lemma strw_xpres : forall E L L' SP m m',
    (forall b, In b (blocks_ERRST E) -> 0 <= blk_size b <= 32) ->
    strw E L m -> xpres H L' SP [] m m' -> (forall b, In b L' -> In b L) -> strw E L' m'.
  Proof.
    intros E L L' SP m m' SMALL SW XP SUB b Hb HbL. destruct (SW b Hb (SUB _ HbL)) as [[bs BC] AD]. pose proof (SMALL b Hb) as SZb.
    pose proof (rw_cells_bound _ _ _ _ BC) as BB. cbn [cells_size csize] in BB. rewrite Nat.add_0_r in BB.
    split.
    - exists bs. eapply xpres_rw_cells'; [exact XP| exact BC| | apply Forall_nil].
      right; right; left. exists b. split; [exact HbL|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. lia.
    - eapply (addressable_agree L'); [| exact HbL| exact AD]. intros a Ha HA. apply XP; [exact Ha|]. split; [| intros K; exact K].
      destruct HA as [HX|[(b' & Hb' & Hr)|(b' & Hb' & Hr)]].
      + apply ac4_static_client. left. exact HX.
      + right; right; left. exists b'. split; [exact Hb'| exact Hr].
      + right; right; right; left. exists b'. split; [exact Hb'| exact Hr].
  Qed.
  Lemma rin_ivs_off : forall X a, Forall (fun iv : Z * Z => a + 1 <= fst iv \/ snd iv <= a) X -> ~ rin_ivs X a.
  Proof.
    intros X a FA. induction X as [|[u v] X IH]; [intros []|]. cbn. pose proof (Forall_inv FA) as K. cbn in K.
    intros [K'|K']; [lia| exact (IH (Forall_inv_tail FA) K')].
  Qed.

  Lemma aerrnew_spec : errnew_stmt H.
  Proof.
    unfold errnew_stmt. intros until CH. intros VIS HP KREL BY CN AUX SPB SPA ST CEIL LO SH0 ERR MI TP AC MF IM GM RL EP EX EB ESH CP RFS LFN CHN CHS PF ECL AL RAE.
    acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (STK1 : 64 + errph_stack ph <= bv_unsigned sp - lo /\ 64 + 8208 <= bv_unsigned sp - lo).
    { unfold ERRNEW_STACK, FR_ERR_new, CFREE_STACK, AFREE_STACK in LO. destruct ph; cbn [errph_stack] in *;
        unfold ERRINIT_STACK, EGS_STACK, FR_ossl_err_get_state_int, CINITCRYPTO_STACK, FR_OPENSSL_init_crypto, AFS_STACK, AREALLOC_STACK in *; lia. }
    set (SB := blocks_ERRST E) in *.
    assert (SUBx : forall b, In b LB -> In b (SB ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    subst tp. unfold ATP in ERR. rewrite (unsigned_lit 12459152) in ERR by lia. change (12459152 + -164) with 12458988 in ERR.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply aen_seg1 with (lo := lo); [exact AC| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (a0' & m1 & j & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1).
    change (munch ((lo, bv_unsigned sp) :: [] ++ []) m m1) in MU1 || (pose proof MU1 as MU1b; clear MU1;
      assert (MU1 : munch ((lo, bv_unsigned sp) :: [] ++ []) m m1) by (eapply munch_mono; [exact MU1b|]; intros a K; cbn in K |- *; destruct K as [K _]; split; [lia| exact I]); clear MU1b).
    assert (CW0 : AC4W LB m ph x) by (split; [exact MF| split; [exact IM| split; [exact GM| split; [exact RL| split; [exact EP| exact CP]]]]]).
    assert (CW1 : AC4W LB m1 ph x).
    { eapply (AC4W_foot H HH) with (XS := []) (LIT := []); [exact RFS| apply Forall_nil| apply Forall_nil| exact CEIL| exact HP| exact SUBx| exact MU1| exact WM1| exact CW0]. }
    assert (HP1 : as_RHEAP H s (SB ++ LB) m1).
    { eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX1 : as_rauxv_ok H m1 B).
    { eapply (ah_rauxv_frame H HH) with (LB := LB); [exact AUX| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (ERR1 : rw_cells asegs m1 12458988 [C4 errv]).
    { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. unfold AIMG_TOP in *. lia. }
    assert (AC1 : ACONST m1) by (eapply ACONST_stack_frame; [exact AC| | exact WM1| exact CEIL]; eapply munch_mono; [exact MU1| intros a K; exact K]).
    assert (RFS1 : as_RFS H LF m1) by (eapply (RFS_stack H HH); [exact RFS| | exact WM1| exact CEIL]; eapply munch_mono; [exact MU1| intros a K; exact K]).
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| eapply munch_mono; [exact MU1| intros a K; exact K]|]. constructor; [left; cbn; lia| constructor]. }
    pose proof (aword_range s0) as S0R.
    assert (CHN1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SPA| lia| lia|].
      pose proof FR1 as FR2. unfold aen_frame in FR2.
      change ([CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) with ([CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -64 + 48) by lia.
      rewrite Z_to_bv_bv_unsigned || idtac. exact FR2 || (revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2). }
    assert (CHS1 : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned sp + -64 + 16 <= fp').
    { intros fp' ra' [E0|Hin]; [injection E0 as <- <-; lia| specialize (CHS _ _ Hin); lia]. }
    clear CH0.
    (* [comment removed for export] *)
    destruct CW1 as (MF1 & IM1 & GM1 & RL1 & EP1 & CP1).
    assert (AGL : magree (lib_addr (SB ++ LB)) m m1).
    { eapply (lib_magree_scratch H HH) with (W := [] ++ []); [exact RFS| | exact MU1| exact WM1| exact CEIL| apply Forall_nil].
      apply Forall_forall. intros b Hb. eapply (ah_blocks H HH); [exact HP| exact Hb]. }
    assert (EX1 : ERRX m1 ph E).
    { destruct ph as [|c0]; [exact EX|]. cbn [ERRX ERRPH] in EX, EP |- *. destruct EP as [_ EC0].
      pose proof EC0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _). pose proof EX as (_ & ESZ & _).
      eapply ERRXR_agree; [exact EX| apply SUBx; exact I5| exact Z5| intros b Hb; apply in_or_app; left; exact Hb
                          | intros b Hb; pose proof (estrs_pos _ _ ESZ Hb); lia| exact AGL]. }
    assert (ESH1 : errph_shad m1 ph).
    { destruct ph as [|c0]; [exact I|]. cbn [errph_shad ERRPH] in ESH, EP |- *. destruct EP as [_ EC0].
      eapply lib_shad_frame; [exact ESH|]. eapply magree_mono; [exact AGL|]. intros a Ha. eapply lib_addr_mono; [| exact Ha].
      intros b Hb. apply SUBx. eapply chain_blocks_in; [exact EC0| exact Hb]. }
    assert (CFp : 0 <= as_Cf H (slot_bytes (slot_at E (err_next (es_top E))))).
    { pose proof (ah_costs H HH) as (_ & _ & CF0 & _). apply CF0. unfold slot_bytes.
      destruct ph as [|c0]; cbn [ERRX] in EX.
      - subst E. unfold slot_at, errst_zero. cbn [es_slots es_top].
        assert (K : forall i, oszb (sl_file_o (nth i (repeat (slot_clear 0) 16) (slot_clear 0))) = 0 /\ oszb (sl_func_o (nth i (repeat (slot_clear 0) 16) (slot_clear 0))) = 0).
        { intros i. destruct (nth_in_or_default i (repeat (slot_clear 0) 16) (slot_clear 0)) as [K|K]; [apply repeat_spec in K|]; rewrite K; split; reflexivity. }
        destruct (K (Z.to_nat (err_next 0))) as [K1 K2]. rewrite K1, K2. lia.
      - destruct EX as ((SL & TR & _) & ESZ & _). pose proof (err_next_range _ TR) as TR'.
        pose proof (slot_at_own _ E (err_next (es_top E)) ESZ SL TR') as [K1 K2]. lia. }
    eapply (ah_seq H HH).
    { eapply (EGS ph E) with (save := 1) (lo := lo) (B := B) (LB := LB) (s := s) (x := x) (errv := errv) (LF := LF) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [ exact VIS1| reflexivity| lia| intros _; right; reflexivity| exact HP1| exact KREL1| exact BY| exact CN| exact AUX1
        | rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia; lia
        | rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia; clear - SPA; Z.div_mod_to_equations; lia
        | rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia; exact ST1
        | exact CEIL
        | rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia; lia
        | eapply errph_sh0_sub; [eapply errph_sh0_munch; [exact SH0| exact MU1| exact WM1| apply Forall_cons; [apply stack0_ok_app; unfold AHI_LO; lia| cbn [app]; apply Forall_nil]]
                               | rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia; lia| rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia; clear - SPA; Z.div_mod_to_equations; lia]
        | rewrite (unsigned_lit ATP) by (unfold ATP; lia); exact ERR1
        | exact MI1| reflexivity| exact AC1| exact MF1| exact IM1| exact GM1| exact RL1| exact EP1| exact EX1| exact EB| exact ESH1| exact CP1
        | exact RFS1| exact LFN| exact CHN1| rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia; exact CHS1
        | rewrite (unsigned_lit AEN_RA1) by (unfold AEN_RA1; lia); eapply pf_ok_call; [exact PF|]; unfold PF_errnew, R_ERR_new_egs, AEN_RA1; apply incl_appl; apply incl_refl
        | exact ECL
        | unfold ERRNEW_COST in AL; lia
        | rewrite (unsigned_lit AEN_RA1) by (unfold AEN_RA1; lia); reflexivity ]. }
    intros [ms2 mo2] PO. unfold egs_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & s2' & LBN & c & XS &
                    VIS2 & MP2 & (KREL2 & MI2 & AC2 & ST2 & AUX2 & HP2 & MF2 & IM2 & GM2 & RL2) & ERR2 & ERRV2 & DL & EP2 & CP2 & EST2 & LS2 & FXS & XP2 & RFS2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST2, XP2 by lia. rewrite (unsigned_lit ATP) in ERR2 by (unfold ATP; lia). unfold ATP in ERR2. change (12459152 + -164) with 12458988 in ERR2.
    specialize (ERRV2 ltac:(lia)). subst errv2.
    (* [comment removed for export] *)
    assert (FXE : forall A n, aceil <= A -> A + n <= AIMG_TOP \/ aceil <= A ->
              Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) (XS ++ ERR_XE)).
    { intros A n HA _. apply Forall_app. split.
      - eapply Forall_impl; [| exact FXS]. intros iv SC. pose proof (fs_scratch_range H HH _ _ _ RFS SC). lia.
      - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key,
          A_master_once_ret, A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf,
          A_keys, A_next_key, A_key_lock, A_tsd_main.
        cbn [app]. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -64) (aen_frame j s5 s4 s3 s2 s1 s0 ra)).
    { eapply xpres_rw_cells'; [exact XP2| exact FR1| left; lia|]. apply FXE; [lia| right; lia]. }
    (* [comment removed for export] *)
    set (es := blk_addr (ec_es c)) in *.
    pose proof EP2 as [ES2 EC2]. pose proof EC2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _).
    assert (SUB2 : forall b, In b (LBN ++ LB) -> In b (SB ++ LBN ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
    pose proof (ah_blocks H HH _ _ _ _ HP2 (SUB2 _ I5)) as BR5. rewrite Z5 in BR5. fold es in BR5. unfold ERRST_SIZE in BR5.
    pose proof BR5 as (B1 & B2 & B3 & B4 & B5 & B6 & B7). pose proof (aapp_bounds _ _ B7 ltac:(lia)) as (_ & _ & T5 & _). unfold AAPP_HI in T5.
    destruct EST2 as (EST & ESZ & ESHs & ESC). apply ERRST_split in EST. destruct EST as [EM2 OWN]. fold es in EM2.
    pose proof (estrs_pos E) as POSE.
    assert (ACC2 : accessible m2 es 904).
    { pose proof (proj1 (Forall_forall _ _) LS2 _ ltac:(unfold chain_blocks; cbn; do 3 right; left; reflexivity)) as AD. cbv beta in AD. fold es in AD. rewrite Z5 in AD.
      unfold ERRST_SIZE in AD. eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI; lia]. }
    assert (CW2 : AC4W (LBN ++ LB) m2 (ErrReady c) x) by (split; [exact MF2| split; [exact IM2| split; [exact GM2| split; [exact RL2| split; [exact EP2| exact CP2]]]]]).
    assert (SW2 : strw E (SB ++ LBN ++ LB) m2).
    { intros b Hb HbL. split; [exact (proj1 (Forall_forall _ _) ESC _ Hb)| exact (proj1 (Forall_forall _ _) ESHs _ Hb)]. }
    (* [comment removed for export] *)
    assert (CHN2 : as_chain H m2 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_ext H HH); [exact CHN1|]. intros fp' ra' a Hin Ha. apply XP2; [| split; [left; specialize (CHS1 _ _ Hin); lia|]].
      - pose proof (ah_chain_range H HH _ _ _ _ _ CHN1 Hin) as (R1 & _). lia.
      - pose proof (ah_chain_range H HH _ _ _ _ _ CHN1 Hin) as (R1 & _). specialize (CHS1 _ _ Hin).
        apply (rin_ivs_off _ a). apply FXE; [lia| right; lia]. }
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply aen_seg2a with (es := es) (E := E); [exact EM2| lia| lia| exact B2| exact B7| exact ACC2| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 (a0_3 & a1_3 & a2_3 & a3_3 & m3 & VIS3 & MU3 & WM3 & MI3 & EM3 & ACC3).
    pose proof EM2 as (SL & TR & _). pose proof (err_next_range _ TR) as TR'. set (t' := err_next (es_top E)) in *.
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3| eapply aen_seg2b with (es := es) (t := t') (E := aen_E0 E); [exact EM3| exact TR'| lia| lia| exact B2| exact B7| exact ACC3| exact MI3]|].
    intros msF4 mo4 KREL4 MP4 (a3_4 & a4_4 & a5_4 & a6_4 & m4 & VIS4 & MU4 & WM4 & MI4 & EM4 & ACC4).
    destruct (aes_world H HH _ _ _ _ m4 _ _ _ _ _ _ _ _ HP2 SUB2 CW2 AUX2 ERR2 ST2 FR2 AC2 LS2 CEIL ltac:(lia) ltac:(lia)
                (munch_trans _ _ _ _ MU3 MU4) (wmono_trans _ _ _ _ WM3 WM4)) as (HP4 & CW4 & AUX4 & ERR4 & ST4 & FR4 & AC4 & LS4).
    assert (SW4 : strw E (SB ++ LBN ++ LB) m4).
    { eapply (strw_es E _ _ m2 m4 (ec_es c)); [exact HP2| exact (SUB2 _ I5)| exact Z5| reflexivity| intros b Hb; exact (POSE b ESZ Hb)| exact SW2
                                              | exact (munch_trans _ _ _ _ MU3 MU4)| exact (wmono_trans _ _ _ _ WM3 WM4)]. }
    assert (CHN4 : as_chain H m4 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (achain_below H HH m2 m4); [exact CHN2| | exact (munch_trans _ _ _ _ MU3 MU4)|]; [intros fp' ra' Hin; specialize (CHS1 _ _ Hin); exact CHS1|].
      apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (RFS4 : as_RFS H LF m4).
    { eapply (ah_RFS_frame H HH); [exact RFS2| exact (munch_trans _ _ _ _ MU3 MU4)| exact (wmono_trans _ _ _ _ WM3 WM4)|].
      pose proof (RFS_fsb H HH _ _ RFS2) as (F1 & F2 & F3 & F4).
      apply Forall_cons; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *; lia| apply Forall_nil]. }
    pose proof MU3 as MU3x. pose proof WM3 as WM3x.
    clear MU3 WM3 MI3 EM3 ACC3 KREL3 VIS3.
    (* [comment removed for export] *)
    set (sl := slot_at E t') in *.
    change (slot_at (aen_E0 E) t') with sl in *.
    pose proof (slot_at_own _ E t' OWN SL TR') as [OF OG]. fold sl in OF, OG.
    assert (FSf : forall b, In b (blocks_of (sl_file sl) (sl_file_o sl)) -> In b SB).
    { intros b Hb. destruct (sl_file_o sl) as [[idf nf]|]; cbn [blocks_of ofield] in *; [| contradiction]. destruct Hb as [<-|[]]. tauto. }
    assert (FSg : forall b, In b (blocks_of (sl_func sl) (sl_func_o sl)) -> In b SB).
    { intros b Hb. destruct (sl_func_o sl) as [[idg ng]|]; cbn [blocks_of ofield] in *; [| contradiction]. destruct Hb as [<-|[]]. tauto. }
    pose proof (ah_costs H HH) as (_ & _ & CF0 & CFM & _ & CFS).
    pose proof (slot_at_own _ E t' ESZ SL TR') as [SZf SZg]. fold sl in SZf, SZg.
    assert (OZ : forall o, oszb' o = oszb o) by (intros [[i n]|]; reflexivity).
    unfold ERRNEW_COST in AL. fold t' in AL. fold sl in AL. unfold slot_bytes in AL.
    assert (CFF : as_Cf H (oszb' (sl_file_o sl)) <= as_AL H s2').
    { rewrite OZ. pose proof (CFM (oszb (sl_file_o sl)) (oszb (sl_file_o sl) + oszb (sl_func_o sl)) ltac:(lia)). lia. }
    eapply (ah_seq H HH).
    { eapply (acfree_opt_spec H HH) with (P := sl_file sl) (o := sl_file_o sl) (LB := SB ++ LBN ++ LB) (lo := lo) (B := B) (s := s2') (errv := errv)
                                          (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [ exact VIS4| reflexivity
        | destruct (sl_file_o sl) as [[idf nf]|] eqn:EO; cbn [ofield] in OF;
          [ destruct OF as (_ & _ & OF); split; [apply in_or_app; left; exact OF|];
            apply (SW4 (idf, sl_file sl, nf)); [apply FSf; cbn; left; reflexivity| apply in_or_app; left; exact OF]
          | exact OF ]
        | exact HP4| exact KREL4| exact AUX4
        | rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia; lia
        | rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia; exact ST4| exact CEIL
        | rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia; unfold CFREE_STACK, AFREE_STACK; lia
        | rewrite (unsigned_lit ATP) by (unfold ATP; lia); exact ERR4| exact MI4| reflexivity
        | rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia; clear - SPA; Z.div_mod_to_equations; lia
        | exact AC4| exact CHN4
        | rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia; exact CHS1
        | rewrite (unsigned_lit AEN_RA2) by (unfold AEN_RA2; lia); eapply pf_ok_call; [exact PF|]; unfold PF_errnew, PF_ERRNEW_READY, PF_cfree, pf_shift, AEN_RA2; cbn;
          intros pp [<-|[]]; apply in_or_app; right; cbn; left; reflexivity
        | exact CFF
        | destruct CW4 as (_ & K & _); exact K| destruct CW4 as (_ & _ & K & _); exact K ]. }
    intros [ms5 mo5] PO. unfold acfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m5 & s5' & L5 &
                    VIS5 & KREL5 & MP5 & MI5 & AC5 & ST5 & ERR5 & AUX5 & PM5 & SUB5 & XP5 & HP5 & IM5 & GM5 & AL5).
    rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST5, XP5 by lia. rewrite (unsigned_lit ATP) in ERR5 by (unfold ATP; lia). unfold ATP in ERR5. change (12459152 + -164) with 12458988 in ERR5.
    (* [comment removed for export] *)
    pose proof (ah_nodup H HH _ _ _ HP2) as ND2.
    assert (KEEP : forall Fr L', Permutation (Fr ++ L') (SB ++ LBN ++ LB) -> (forall b, In b Fr -> In b SB) -> forall b, In b (LBN ++ LB) -> In b L').
    { intros Fr L' PM FS b Hb. eapply perm_keep; [exact PM| apply SUB2; exact Hb|]. intros K.
      eapply (nodup_map_app_excl blk_id SB (LBN ++ LB) b); [exact ND2| apply FS; exact K| exact Hb]. }
    pose proof (KEEP _ _ PM5 FSf) as SUBK5.
    destruct (afree_world H _ _ _ m5 _ _ _ _ _ _ CW4 XP5 SUBK5 FR4 ltac:(lia) EM4 ltac:(fold es; lia) ltac:(fold es; unfold ERRST_SIZE; lia) LS4) as (CW5 & FR5 & EM5 & LS5).
    fold es in EM5.
    pose proof (strw_xpres E _ _ _ _ _ (fun b Hb => POSE b ESZ Hb) SW4 XP5 SUB5) as SW5.
    assert (ACC5 : accessible m5 es 904).
    { pose proof (proj1 (Forall_forall _ _) LS5 _ ltac:(unfold chain_blocks; cbn; do 3 right; left; reflexivity)) as AD. cbv beta in AD. fold es in AD. rewrite Z5 in AD.
      unfold ERRST_SIZE in AD. eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI; lia]. }
    assert (CHN5 : as_chain H m5 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_ext H HH); [exact CHN4|]. intros fp' ra' a Hin Ha. apply XP5; [| split; [left; specialize (CHS1 _ _ Hin); lia| intros []]].
      pose proof (ah_chain_range H HH _ _ _ _ _ CHN4 Hin) as (R1 & _). lia. }
    assert (RFS5 : as_RFS H LF m5) by (eapply (RFS_via_xpres H HH); [exact RFS4| exact XP5| apply Forall_nil]).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL5| exact VIS5
      | eapply aen_seg3 with (es := es) (t := t') (E := es_with_slot (aen_E0 E) t' (slot_wipe sl)); [exact EM5| exact TR'| lia| lia| exact B7| exact ACC5| exact MI5]|].
    intros msF6 mo6 KREL6 MP6 (m6 & VIS6 & MU6 & WM6 & MI6 & EM6 & ACC6).
    assert (SL0 : length (es_slots (aen_E0 E)) = 16%nat) by exact SL.
    rewrite (slot_at_upd (aen_E0 E) t' _ SL0 TR') in EM6, VIS6. rewrite (es_with_slot_twice (aen_E0 E) t' _ _ SL0 TR') in EM6.
    cbn [slot_wipe sl_func] in *.
    assert (HP5' : as_RHEAP H s5' L5 m5) by exact HP5.
    assert (I5' : In (ec_es c) L5) by (apply SUBK5; exact I5).
    destruct (aes_world H HH _ _ _ _ m6 _ _ _ _ _ _ _ _ HP5 SUBK5 CW5 AUX5 ERR5 ST5 FR5 AC5 LS5 CEIL ltac:(lia) ltac:(lia) MU6 WM6)
      as (HP6 & CW6 & AUX6 & ERR6 & ST6 & FR6 & AC6 & LS6).
    assert (SW6 : strw E L5 m6).
    { eapply (strw_es E _ _ m5 m6 (ec_es c)); [exact HP5| exact I5'| exact Z5| reflexivity| intros b Hb; exact (POSE b ESZ Hb)| exact SW5| exact MU6| exact WM6]. }
    assert (RFS6 : as_RFS H LF m6).
    { eapply (ah_RFS_frame H HH); [exact RFS5| exact MU6| exact WM6|]. pose proof (RFS_fsb H HH _ _ RFS2) as (F1 & F2 & F3 & F4).
      apply Forall_cons; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *; lia| apply Forall_nil]. }
    assert (CHN6 : as_chain H m6 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (achain_below H HH m5 m6); [exact CHN5| | exact MU6|]; [intros fp' ra' Hin; specialize (CHS1 _ _ Hin); exact CHS1|].
      apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (CFG : as_Cf H (oszb' (sl_func_o sl)) <= as_AL H s5').
    { rewrite OZ in AL5 |- *. pose proof (CFS (oszb (sl_file_o sl)) (oszb (sl_func_o sl)) ltac:(lia) ltac:(lia)). lia. }
    (* [comment removed for export] *)
    eapply (ah_seq H HH).
    { eapply (acfree_opt_spec H HH) with (P := sl_func sl) (o := sl_func_o sl) (LB := L5) (lo := lo) (B := B) (s := s5') (errv := errv)
                                          (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [ exact VIS6| reflexivity
        | destruct (sl_func_o sl) as [[idg ng]|] eqn:EG; cbn [ofield] in OG;
          [ destruct OG as (_ & _ & OG);
            assert (ING : In (idg, sl_func sl, ng) L5);
            [ eapply perm_keep; [exact PM5| apply in_or_app; left; exact OG|]; intros K;
              (* [comment removed for export] *)
              pose proof (blocks_slots_split (es_slots E) (Z.to_nat t') (slot_clear 0) ltac:(lia)) as SPL; fold (slot_at E t') in SPL; fold sl in SPL;
              unfold blocks_slot in SPL; rewrite EG in SPL;
              assert (NDS : List.NoDup (map blk_id SB)) by (rewrite map_app in ND2; eapply NoDup_app_remove_r; exact ND2);
              unfold SB in NDS; rewrite blocks_ERRST_slots, SPL in NDS;
              eapply (nodup_mid_excl blk_id _ _ _ _ _ NDS K); cbn; left; reflexivity
            | split; [exact ING|]; apply (SW6 (idg, sl_func sl, ng)); [apply FSg; try rewrite EG; cbn; left; reflexivity| exact ING] ]
          | exact OG ]
        | exact HP6| exact KREL6| exact AUX6
        | rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia; lia
        | rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia; exact ST6| exact CEIL
        | rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia; unfold CFREE_STACK, AFREE_STACK; lia
        | rewrite (unsigned_lit ATP) by (unfold ATP; lia); exact ERR6| exact MI6| reflexivity
        | rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia; clear - SPA; Z.div_mod_to_equations; lia
        | exact AC6| exact CHN6
        | rewrite (unsigned_lit (bv_unsigned sp + -64)) by lia; exact CHS1
        | rewrite (unsigned_lit AEN_RA3) by (unfold AEN_RA3; lia); eapply pf_ok_call; [exact PF|]; unfold PF_errnew, PF_ERRNEW_READY, PF_cfree, pf_shift, AEN_RA3; cbn;
          intros pp [<-|[]]; apply in_or_app; right; cbn; right; left; reflexivity
        | exact CFG
        | destruct CW6 as (_ & K & _); exact K| destruct CW6 as (_ & _ & K & _); exact K ]. }
    intros [ms7 mo7] PO. unfold acfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m7 & s7' & L7 &
                    VIS7 & KREL7 & MP7 & MI7 & AC7 & ST7 & ERR7 & AUX7 & PM7 & SUB7 & XP7 & HP7 & IM7 & GM7 & AL7).
    rewrite (unsigned_lit (bv_unsigned sp + -64)) in ST7, XP7 by lia. rewrite (unsigned_lit ATP) in ERR7 by (unfold ATP; lia). unfold ATP in ERR7. change (12459152 + -164) with 12458988 in ERR7.
    assert (SUBK7 : forall b, In b (LBN ++ LB) -> In b L7).
    { intros b Hb. eapply perm_keep; [exact PM7| apply SUBK5; exact Hb|]. intros K.
      eapply (nodup_map_app_excl blk_id SB (LBN ++ LB) b); [exact ND2| apply FSg; exact K| exact Hb]. }
    destruct (afree_world H _ _ _ m7 _ _ _ _ _ _ CW6 XP7 SUBK7 FR6 ltac:(lia) EM6 ltac:(fold es; lia) ltac:(fold es; unfold ERRST_SIZE; lia) LS6) as (CW7 & FR7 & EM7 & LS7).
    fold es in EM7.
    pose proof (strw_xpres E _ _ _ _ _ (fun b Hb => POSE b ESZ Hb) SW6 XP7 SUB7) as SW7.
    assert (ACC7 : accessible m7 es 904).
    { pose proof (proj1 (Forall_forall _ _) LS7 _ ltac:(unfold chain_blocks; cbn; do 3 right; left; reflexivity)) as AD. cbv beta in AD. fold es in AD. rewrite Z5 in AD.
      unfold ERRST_SIZE in AD. eapply addressable_accessible; [exact AD| lia| lia| unfold AAPP_HI; lia]. }
    assert (RFS7 : as_RFS H LF m7) by (eapply (RFS_via_xpres H HH); [exact RFS6| exact XP7| apply Forall_nil]).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL7| exact VIS7
      | eapply aen_seg4 with (es := es) (t := t') (lo := lo) (E := es_with_slot (aen_E0 E) t' (slot_file0 (slot_wipe sl)));
        [exact EM7| exact TR'| lia| lia| exact B7| exact ACC7| lia| exact MI7| exact ST7| exact FR7]|].
    intros msF8 mo8 KREL8 MP8 (a0_8 & m8 & VIS8 & MU8 & WM8 & MI8 & ST8 & EM8).
    rewrite (slot_at_upd (aen_E0 E) t' _ SL0 TR') in EM8. rewrite (es_with_slot_twice (aen_E0 E) t' _ _ SL0 TR') in EM8.
    unfold slot_func0, slot_file0, slot_wipe in EM8. cbn [sl_flags sl_buffer sl_file sl_file_o sl_line sl_func sl_func_o] in EM8.
    change (es_with_slot (aen_E0 E) t' (mkSLOT 0 0 0 None (2 ^ 32 - 1) 0 None)) with (errst_new E) in EM8.
    (* [comment removed for export] *)
    destruct (aes_world H HH _ _ _ _ m8 _ _ _ _ _ _ _ _ HP7 SUBK7 CW7 AUX7 ERR7 ST7 FR7 AC7 LS7 CEIL ltac:(lia) ltac:(lia) MU8 WM8)
      as (HP8 & CW8 & AUX8 & ERR8 & _ & _ & AC8 & LS8).
    destruct CW8 as (MF8 & IM8 & GM8 & RL8 & EP8 & CP8).
    assert (SW8 : strw E L7 m8).
    { eapply (strw_es E _ _ m7 m8 (ec_es c)); [exact HP7| apply SUBK7; exact I5| exact Z5| reflexivity| intros b Hb; exact (POSE b ESZ Hb)| exact SW7| exact MU8| exact WM8]. }
    assert (RFS8 : as_RFS H LF m8).
    { eapply (ah_RFS_frame H HH); [exact RFS7| exact MU8| exact WM8|]. pose proof (RFS_fsb H HH _ _ RFS2) as (F1 & F2 & F3 & F4).
      apply Forall_cons; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    pose proof (blocks_slots_clear_perm (es_slots E) (Z.to_nat t') (2 ^ 32 - 1) (slot_clear 0) ltac:(lia)) as PC.
    fold (slot_at E t') in PC. fold sl in PC. unfold blocks_slot in PC.
    assert (PMF : Permutation L7 (blocks_ERRST (errst_new E) ++ LBN ++ LB)).
    { set (bf := blocks_of (sl_file sl) (sl_file_o sl)) in *. set (bg := blocks_of (sl_func sl) (sl_func_o sl)) in *.
      change (blocks_ERRST (errst_new E)) with (blocks_slots (slot_upd (es_slots E) (Z.to_nat t') (slot_clear (2 ^ 32 - 1)))).
      set (SB' := blocks_slots (slot_upd (es_slots E) (Z.to_nat t') (slot_clear (2 ^ 32 - 1)))) in *.
      apply (Permutation_app_inv_l (bf ++ bg)).
      rewrite <- (app_assoc bf bg L7).
      eapply Permutation_trans; [apply Permutation_app_head; exact PM7|].
      eapply Permutation_trans; [exact PM5|].
      rewrite (app_assoc (bf ++ bg) SB' (LBN ++ LB)). apply Permutation_app_tail. exact PC. }
    assert (NEWSUB : forall b, In b (blocks_ERRST (errst_new E)) -> In b SB /\ In b L7).
    { intros b Hb. split.
      - unfold SB. rewrite blocks_ERRST_slots. eapply Permutation_in; [apply Permutation_sym; exact PC|]. apply in_or_app. right. exact Hb.
      - eapply Permutation_in; [apply Permutation_sym; exact PMF|]. apply in_or_app. left. exact Hb. }
    apply (ah_done H HH). unfold errnew_post. cbn [cfg_ms cfg_model].
    exists w0, w1, w2, a0_8, d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, m8, errv, s7', LBN, c, XS.
    split; [exact VIS8|].
    split. { eapply (ah_mpres_trans H HH); [exact MP1|]. eapply (ah_mpres_trans H HH); [exact MP2|]. eapply (ah_mpres_trans H HH); [exact MP3|].
             eapply (ah_mpres_trans H HH); [exact MP4|]. eapply (ah_mpres_trans H HH); [exact MP5|]. eapply (ah_mpres_trans H HH); [exact MP6|].
             eapply (ah_mpres_trans H HH); [exact MP7| exact MP8]. }
    split. { unfold c4_frame. cbn [cfg_model]. split; [exact KREL8|]. split; [exact MI8|]. split; [exact AC8|]. split; [exact ST8|]. split; [exact AUX8|].
             split; [eapply PERM; [exact HP8| exact PMF]|]. split; [exact MF8|]. split; [exact IM8|]. split; [exact GM8| exact RL8]. }
    split; [rewrite (unsigned_lit ATP) by (unfold ATP; lia); exact ERR8|]. split; [exact DL|]. split; [exact EP8|]. split; [exact CP8|].
    split.
    { split; [| split; [| split]].
      - apply ERRST_split. split; [exact EM8|]. destruct E as [ss top bot]. unfold errst_new. cbn [es_slots es_top es_bottom].
        eapply ERROWN_upd; [exact OWN|]. intros LBx _. cbn [slot_clear sl_file sl_file_o sl_func sl_func_o ofield]. split; reflexivity.
      - unfold estrs_ok, errst_new. cbn [es_slots]. apply own_slot_upd; [exact ESZ| cbn; lia].
      - unfold lib_shad. apply Forall_forall. intros b Hb. destruct (NEWSUB b Hb) as [K1 K2]. exact (proj2 (SW8 b K1 K2)).
      - unfold estrs_cells. apply Forall_forall. intros b Hb. destruct (NEWSUB b Hb) as [K1 K2]. exact (proj1 (SW8 b K1 K2)). }
    split; [exact LS8|]. split; [exact FXS|].
    split.
    { (* [comment removed for export] *)
      set (X := XS ++ ERR_XE ++ errph_foot ph).
      assert (XES : forall ma mb, munch [(es, es + 904)] ma mb -> wmono asegs ma mb -> xpres H LB (bv_unsigned sp) X ma mb).
      { intros ma mb MUx WMx. eapply xpres_of_munch_gen; [exact MUx| exact WMx|].
        intros a Ha [HC HXn]. cbn. split; [| exact I]. intros Hr.
        destruct HC as [K|[K|[(b & Hb & Hrb)|[(b & Hb & Hrb)|[K|[K|K]]]]]].
        - lia.
        - unfold aimg_client, AIMG_TOP in *. lia.
        - assert (NN : ~ (blk_id b <> blk_id (ec_es c))).
          { intros NE. pose proof (ah_disj H HH _ _ _ _ _ HP2 (SUB2 _ (in_or_app _ _ _ (or_intror Hb))) (SUB2 _ I5) NE) as DJ.
            rewrite Z5 in DJ. fold es in DJ. unfold ERRST_SIZE in DJ. lia. }
          apply NN. intros EQid.
          pose proof (nodup_id_inj _ _ _ ND2 (SUB2 _ (in_or_app _ _ _ (or_intror Hb))) (SUB2 _ I5) EQid) as EQB. subst b.
          destruct ph as [|cq]; cbn [errph_delta errph_foot] in *.
          + destruct DL as (_ & _ & FA). pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail FA)))) as IN5.
            assert (NDx : List.NoDup (map blk_id (LBN ++ LB))) by (rewrite map_app in ND2; eapply NoDup_app_remove_l; exact ND2).
            eapply (nodup_map_app_excl blk_id LBN LB (ec_es c)); [exact NDx| exact IN5| exact Hb].
          + destruct DL as [-> _]. apply HXn. unfold X. apply rin_ivs_app. right. apply rin_ivs_app. right. cbn. left. fold es. unfold ERRST_SIZE. lia.
        - (* [comment removed for export] *)
          pose proof (ah_blocks H HH _ _ _ _ HP2 (SUB2 _ (in_or_app _ _ _ (or_intror Hb)))) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
          pose proof (aapp_bounds _ _ Q7 Q3) as (_ & _ & T1 & _).
          pose proof (aapp_disjoint_sh es 904 (blk_addr b) (blk_size b) B7 ltac:(lia) ltac:(lia) Q3). lia.
        - (* [comment removed for export] *) pose proof (RFS_fsb H HH _ _ RFS2) as (F1 & F2 & F3 & F4). unfold AFS_SIZE in *. lia.
        - (* [comment removed for export] *) pose proof (RFS_fsb H HH _ _ RFS2) as (F1 & F2 & F3 & F4). unfold AIMG_TOP in F1.
          pose proof (aapp_bounds _ _ F4 ltac:(unfold AFS_SIZE; lia)) as (U1 & U2 & U3 & U4 & _).
          pose proof (aapp_disjoint_sh es 904 (as_FSB H) AFS_SIZE B7 ltac:(lia) ltac:(lia) ltac:(unfold AFS_SIZE; lia)) as D.
          clear - D K Hr F3. unfold sh, nsh, AFS_SIZE in *. Z.div_mod_to_equations. lia.
        - (* [comment removed for export] *)
          clear - K Hr B7 ACEILB. unfold aapp, aapp_lo, aapp_hi, AHI_LO, ALOWSH_LO, AIMG_TOP, sh in *. rewrite ASHADOW_BASE_val in K. lia. }
      assert (XFR : forall L' ma mb, xpres H L' (bv_unsigned sp + -64) [] ma mb -> (forall b, In b (LBN ++ LB) -> In b L') -> xpres H LB (bv_unsigned sp) X ma mb).
      { intros L' ma mb XPx SUBx'. eapply xpres_weaken; [exact XPx| lia| intros b Hb; apply SUBx'; apply in_or_app; right; exact Hb| intros a []]. }
      eapply xpres_trans.
      { eapply (xpres_weaken H (SB ++ LB) LB); [| apply Z.le_refl| exact SUBx| intros ax K; exact K].
        eapply (xpres_of_munch H s (SB ++ LB)); [exact HH| exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
      eapply xpres_trans; [eapply xpres_weaken; [exact XP2| lia| auto| intros a Ka; unfold X; apply rin_ivs_app in Ka; apply rin_ivs_app; destruct Ka as [Ka|Ka]; [left; exact Ka| right; apply rin_ivs_app; left; exact Ka]]|].
      eapply xpres_trans; [apply (XES _ _ (munch_trans _ _ _ _ MU3x MU4) (wmono_trans _ _ _ _ WM3x WM4))|].
      eapply xpres_trans; [apply (XFR _ _ _ XP5 SUBK5)|].
      eapply xpres_trans; [apply (XES _ _ MU6 WM6)|].
      eapply xpres_trans; [apply (XFR _ _ _ XP7 SUBK7)|].
      apply (XES _ _ MU8 WM8). }
    split; [exact RFS8|].
    rewrite OZ in AL5, AL7. pose proof (CFS (oszb (sl_file_o sl)) (oszb (sl_func_o sl)) ltac:(lia) ltac:(lia)).
    unfold ERRNEW_COST. fold t'. fold sl. unfold slot_bytes. lia.
  Qed.
End W.
