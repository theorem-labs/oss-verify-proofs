(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut Fz_chk RT_iface_pem I_lkit Fz_G_kit Fz_ckit .
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import PLayout Th_mutex Th_mutex_init Th_cond.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_G_pkit Fz_T_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac tslia ::= wp_tslia.
(* [comment removed for export] *)
Local Ltac wp_out Ho SPL unf := cbn [app outside]; unf;
  repeat (split; [ first [ wp_na
                         | (clear - Ho SPL; first [ tauto | lia ])
                         | match goal with H : wp_box (aclient _ _ _ _) |- _ => unfold wp_box in H; lia end
                         | (repeat match goal with H : wp_box _ |- _ => unfold wp_box in H end; lia) ] |]); exact I.
(* [comment removed for export] *)
Local Ltac wg_T := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ifT | |- _ => idtac end.
Local Ltac wg_F := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ifF | |- _ => idtac end.
Local Ltac zstore := zstep; fix_lit_store.
Local Ltac wg_raw H := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => rewrite H; cbv iota end.
Local Ltac wg_at p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => unify p q | |- _ => fail "wgen: unexpected pc" end.

Definition e_OPENSSL_sk_set_copy_thunks : Z := 0x1faa0c.

(* [comment removed for export] *)
Definition OPENSSL_sk_set_copy_thunks_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (p0 : Z) (xa0_num xa0_pad xa0_data xa0_sorted xa0_nalloc xa0_comp xa0_cmpt xa0_freet xa0_copyt : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p0) a1 (Z_to_bv 64 (p0 + 48)) (Z_to_bv 64 0) (Z_to_bv 64 ((p0 + 48) ≫ 3)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(p0, p0 + 56); (bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' p0 [C4 xa0_num; C4 xa0_pad; C8 xa0_data; C4 xa0_sorted; C4 xa0_nalloc; C8 xa0_comp; C8 xa0_cmpt; C8 xa0_freet; C8 a1]
    /\ ro_cells asegs m' 6736696 [C8 (Z_to_bv 64 2147450880)]
    /\ stk asegs m' lo (bv_unsigned sp).

Lemma OPENSSL_sk_set_copy_thunks_s0_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (p0 : Z) (xa0_num xa0_pad xa0_data xa0_sorted xa0_nalloc xa0_comp xa0_cmpt xa0_freet xa0_copyt : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2 ^ 47 ->
  img_untouched m ->
  ro_cells asegs m 0x66cb38 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m p0 [C4 xa0_num; C4 xa0_pad; C8 xa0_data; C4 xa0_sorted; C4 xa0_nalloc; C8 xa0_comp; C8 xa0_cmpt; C8 xa0_freet; C8 xa0_copyt] ->
  acc asegs m p0 56 ->
  p0 mod 8 = 0 ->
  0x10007fff8000 <= p0 ->
  p0 + 56 <= 2 ^ 47 ->
  p0 + 56 <= lo ->
  (negb (bv_eqb (Z_to_bv 64 (Z.land p0 7)) (Z_to_bv 64 0))) = false ->
  mem_inv asegs m ->
  evt asegs (OPENSSL_sk_set_copy_thunks_s0_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 p0 xa0_num xa0_pad xa0_data xa0_sorted xa0_nalloc xa0_comp xa0_cmpt xa0_freet xa0_copyt F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1faa0c) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HIMG HTOP UT G1 HBa0 ACCa0 PALa0 HIa0 TOPa0 STKa0 BR0_2 MI. unfold SEGTOP_A in *.
  pose proof (munch_refl [(p0, p0 + 56); (bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia end.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  zstep.
  do 2 zstore.
  zstep.
  zstep. wg_F.
  do 7 zstep.
  zstep. wg_F.
  zstore.
  do 4 zstep.
  lazymatch goal with STh : stk _ _ lo _ |- _ => release_frame FR STh (bv_unsigned sp) end.
  unfold OPENSSL_sk_set_copy_thunks_s0_post. apply evt_done. do 1 eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split; [eassumption|] end. eassumption.
Qed.

Section OPENSSL_sk_set_copy_thunks_cps.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.

Definition OPENSSL_sk_set_copy_thunks_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (p0 : Z) (xa0_num : word) (xa0_pad : word) (xa0_data : word) (xa0_sorted : word) (xa0_nalloc : word) (xa0_comp : word) (xa0_cmpt : word) (xa0_freet : word) (xa0_copyt : word),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p0 -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + 16 <= bv_unsigned sp ->
  In (p0, 56) (rt_live RT Σ) -> p0 mod 16 = 0 -> rw_cells asegs m p0 [C4 xa0_num; C4 xa0_pad; C8 xa0_data; C4 xa0_sorted; C4 xa0_nalloc; C8 xa0_comp; C8 xa0_cmpt; C8 xa0_freet; C8 xa0_copyt] ->
  (negb (bv_eqb (Z_to_bv 64 (Z.land p0 7)) (Z_to_bv 64 0))) = false ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_OPENSSL_sk_set_copy_thunks m)))
    (fun c => ASTA RT Σ PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p0) m' ms
           /\ rt_after RT Σ (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(p0, p0 + 56)] m m'
           /\ rw_cells asegs m' p0 [C4 xa0_num; C4 xa0_pad; C8 xa0_data; C4 xa0_sorted; C4 xa0_nalloc; C8 xa0_comp; C8 xa0_cmpt; C8 xa0_freet; C8 a1]) c).

Theorem OPENSSL_sk_set_copy_thunks_cps : OPENSSL_sk_set_copy_thunks_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo p0 xa0_num xa0_pad xa0_data xa0_sorted xa0_nalloc xa0_comp xa0_cmpt xa0_freet xa0_copyt
    FDO MST -> -> ART0 MI0 CALL HSTK INP_p0 P16_p0 HBT_p0 BRW0.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 16 /\ 0x10007fff8000 < usp - 16 /\ usp <= USTACK_TOP /\ 0x10007fff8000 <= lo /\ usp <= 2 ^ 47)
    by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  cl_eu usp (-16) EU1.
  assert (WHLO : lo <= usp - 16) by (unfold RT_STACK in *; lia). assert (WHIMG : 0x10007fff8000 <= lo) by lia. assert (WHTOP : usp <= 2 ^ 47) by lia.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (af_live_range RT AF Σ m p0 56 ART0 INP_p0) as (_ & PHI_p0 & _).
  pose proof (afp_live_mem RT GOBJ AFP Σ m p0 56 ART0 INP_p0 ltac:(lia)) as (_ & PT_p0).
  pose proof (afp_live_hi RT GOBJ AFP Σ m p0 56 ART0 INP_p0 ltac:(lia)) as PHH_p0.
  pose proof (wg_mod16_8 _ P16_p0) as PAL_p0. assert (PR64_p0 : 0 <= p0 < 2 ^ 64) by (unfold USTACK_TOP in *; lia).
  assert (PSTK_p0 : p0 + 56 <= lo) by (unfold STACK_WIN in *; lia).
  wp_box1 P16_p0. wp_box1 PAL_p0. wp_box1 PR64_p0.
  pose proof (af_acc_live RT AF Σ m p0 56 ART0 INP_p0) as (WR_p0_1 & ACC_p0_1).
  (* [comment removed for export] *)
  pose proof (OPENSSL_sk_set_copy_thunks_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 p0 xa0_num xa0_pad xa0_data xa0_sorted xa0_nalloc xa0_comp xa0_cmpt xa0_freet xa0_copyt F fc m lo
                ST WHLO WHIMG WHTOP UT SHC HBT_p0 ACC_p0_1 PAL_p0 PHH_p0 PT_p0 PSTK_p0 BRW0 MI0) as W1.
  cl_lift W1 HA c1 Hc1.
  apply Hk.
  apply (ASTA_conseq RT Σ PMc _ _ c1 Hc1). intros ms1 (m1 & -> & MU1 & WM1 & MI1 & H1_0 & H1_1 & ST1). fold usp in MU1, ST1.
  exists m1.
  split; [exists t0, t1, t2, a1, (Z_to_bv 64 (p0 + 48)), (Z_to_bv 64 0), (Z_to_bv 64 ((p0 + 48) ≫ 3)), a5, a6, a7, t3, t4, t5, t6, F, fc; reflexivity|].
  assert (ART1 : ART RT Σ m1).
  { apply (wg_seg_ART RT AF Σ m m1 usp 16 [(p0, p0 + 56)] ART0 ltac:(lia) ltac:(lia) MU1); [|exact WM1].
    intros x Hx. destruct (wg_not_outside_cons _ _ _ _ Hx) as [H|Hx2]; [right; exists p0, 56; split; [exact INP_p0 | lia] | clear Hx; rename Hx2 into Hx]. exfalso; apply Hx; exact I. }
  split; [split; [exact ART1|]; split; [exact MI1|]; split; [exact WM1 | exact ST1]|].
  split.
  { intros a Ha Ho.
    pose proof (cl_split RT AF Σ m usp 16 _ ART0 ltac:(unfold RT_STACK in *; lia) ltac:(lia) Ha) as SPL.
    cbn [app outside] in Ho. 
    rewrite (MU1 a ltac:(wp_out Ho SPL ltac:(idtac))).
    reflexivity. }
  exact H1_0.
Qed.
End OPENSSL_sk_set_copy_thunks_cps.
