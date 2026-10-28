(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_ukit Fz_T_sa Fz_W5_glx Fz_W5_icb Fz_W5_gsi.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Fz_W5_rep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition e_vset_error : Z := 0x1fcd6c.
Definition SITE_vse_gsi : Z := 0x1fcdcc.

(* [comment removed for export] *)
Definition vse_s0_post (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j1 : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_vse_gsi) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 sp a2 (Z_to_bv 64 1) (Z_to_bv 64 6736696)
                 a2 a3 a4 a5 a6 a7 s2 s3 a1 s5 a0 s7 a3 (Z_to_bv 64 0x7fff8000) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_get_state) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -112) [CB 8 j1; C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0]
    /\ stk asegs m' lo (bv_unsigned sp + -112).

Lemma vse_s0_walk : forall ra0 sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 112 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] -> mem_inv asegs m ->
  evt asegs (vse_s0_post sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s5' s7' s10' s11' t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' lo m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
        F (Z_to_bv 64 e_vset_error) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HLOS SPH UT SHC MI. unfold e_vset_error, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 112, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 112, SP)]) by ut_fp_lia.
  th_frame 112%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  do 15 zstep. do 9 zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold vse_s0_post, SITE_vse_gsi, e_get_state. apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Lemma upd_bytes_zeros : forall n k j, (k + j <= n)%nat -> upd_bytes (repeat (Z_to_bv 8 0) n) k (repeat (Z_to_bv 8 0) j) = repeat (Z_to_bv 8 0) n.
Proof.
  intros n k j H. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i n) as [Hi|Hi].
  - rewrite upd_bytes_nth by (rewrite ?repeat_length; lia). rewrite repeat_length.
    destruct (Nat.leb k i && Nat.ltb i (k + j))%bool eqn:Eb.
    + apply andb_prop in Eb. destruct Eb as [Ea Eb]. apply Nat.ltb_lt in Eb. apply Nat.leb_le in Ea. rewrite !nth_error_repeat by lia. reflexivity.
    + reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite upd_bytes_length; rewrite ?repeat_length; lia).
    symmetry. apply nth_error_None. rewrite repeat_length. exact Hi.
Qed.

(* [comment removed for export] *)
Ltac zstore AH BASE len OFF n ADDR :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    let SOK := fresh "SOK" in
    pose proof (u8arr_store_ok_n asegs mX BASE (repeat (Z_to_bv 8 0) len) OFF n (Z_to_bv 64 ADDR) AH ltac:(lia) ltac:(rewrite repeat_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK;
    zstep;
    let A2 := fresh "AZ" in
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
      pose proof (u8arr_write_bytes asegs mX BASE (repeat (Z_to_bv 8 0) len) OFF bs AH ltac:(lia) ltac:(rewrite !repeat_length; cbn; lia)) as A2;
      change bs with (repeat (Z_to_bv 8 0) n) in A2 at 2; rewrite upd_bytes_zeros in A2 by lia
    end;
    replace (BASE + OFF) with ADDR in A2 by lia;
    clear AH; store_done; rename A2 into AH
  end.

(* [comment removed for export] *)
Definition vse_s1_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) (fc : bv 32)
    (E top bot : Z) (fl mk buf fs ls fn : list word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (buf' : list word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (E + 128, E + 576)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ es_rep m' E top bot fl mk buf' fs ls fn.

Lemma vse_s1_walk : forall ra0 sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s10 s11 t3 t4 t5 t6 (reason libw args : word)
    (s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) fc (m : mem) (lo : Z) (j1 : list byte)
    (E top bot : Z) (fl mk buf fs ls fn : list word),
  stk asegs m lo (bv_unsigned sp + -112) -> lo <= bv_unsigned sp - 112 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells asegs m (bv_unsigned sp + -112) [CB 8 j1; C8 s11'; C8 s10'; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  es_rep m E top bot fl mk buf fs ls fn -> acc asegs m E 904 -> E mod 8 = 0 -> 0x10007fff8000 <= E -> E + 904 <= lo ->
  mem_inv asegs m ->
  evt asegs (vse_s1_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F fc E top bot fl mk buf fs ls fn lo m)
    (MS (mkR (Z_to_bv 64 SITE_vse_gsi) (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 0) (Z_to_bv 64 E) a1
             a2 a3 a4 a5 a6 a7 s2 s3 reason s5 libw s7 args (Z_to_bv 64 0x7fff8000) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_vse_gsi) fc None m (seg_rom asegs)).
Proof.
  intros until fn. intros ST HLO HLOS SPH UT SHC FR ES ACCE EAL EHI ELO MI. unfold SITE_vse_gsi, g_shadow_memory_dynamic_address in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 112, SP); (E + 128, E + 576)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 112, SP); (E + 128, E + 576)]) by ut_fp_lia. assert (HWS : sh_fp [(SP - 112, SP); (E + 128, E + 576)]) by sh_fp_lia.
  zstep. if_cases KE; zify_cond KE. { exfalso. rewrite ?unsigned_lit in KE by lia. lia. }
  zstep. zstep.
  zstep. zstep. th_if_lit.
  do 4 zstep.
  zstep. zstep. zstep. th_if_lit. zstep. rewrite (t_sx32_small top) by lia.
  (* [comment removed for export] *)
  zstep. zstep. rewrite (Z.shiftl_mul_pow2 top 2) by lia. change (2 ^ 2) with 4.
  zstep. do 2 zstep. zstep. zstep. th_if_lit.
  pose proof (u8arr_read asegs m (E + 512) (repeat (Z_to_bv 8 0) 64) (top * 4) (Z_to_bv 8 0) (Z_to_bv 64 (E + 512 + top * 4)) A6
                ltac:(apply nth_error_repeat; lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
  zstep. zstep. zstep. rewrite (Z.shiftl_mul_pow2 top 3) by lia. change (2 ^ 3) with 8. zstep. zstep. th_if_lit.
  (* [comment removed for export] *)
  do 3 zstep. zstep. th_if_lit.
  zstore A4 (E + 256) 128%nat (top * 8) 8%nat (E + 256 + top * 8).
  zstep. zstep. do 3 zstep. zstep. th_if_lit. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
  zstore A5 (E + 384) 128%nat (top * 8) 8%nat (E + 384 + top * 8).
  zstep.
  zstep. zstep. th_if_lit.
  zstore A6 (E + 512) 64%nat (top * 4) 4%nat (E + 512 + top * 4).
  (* [comment removed for export] *)
  zstep. zstep. th_if_lit. zstep. rewrite (t_sx32_small top) by lia. zstep.
  zstep. if_cases KLIB; [do 5 zstep | do 3 zstep].
  all: zstep; rewrite (Z.shiftl_mul_pow2 top 3) by lia; change (2 ^ 3) with 8.
  all: zstep; zstep; do 3 zstep; zstep; th_if_lit; zstep; zstep.
  all: pose proof (u64arr_store_ok asegs _ (E + 128) buf top (Z_to_bv 64 (E + 128 + top * 8)) A3 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK3.
  all: zstep.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ (le8 ?v)) _) =>
         pose proof (u64arr_write asegs mX (E + 128) buf top v A3 ltac:(lia)) as A3';
         replace (E + 128 + 8 * top) with (E + 128 + top * 8) in A3' by lia; clear A3; store_done end.
  all: zstep; th_if_lit.
  all: do 13 zstep; zstep; th_release FR SP; zstep.
  all: subst SP; rewrite ?Z_to_bv_bv_unsigned.
  all: unfold vse_s1_post; apply evt_done; do 17 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|].
  all: unfold es_rep; repeat (split; [first [eassumption | rewrite upd_length; exact L3 | lia] |]); lia.
Qed.

Section CVse.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_GSI : get_state_steady_stmt RT.

Definition VSE_W (E : Z) : list (Z * Z) := [(ERRNO_A, ERRNO_A + 4); (E + 128, E + 576)].

Definition err_vset_error_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (od e : word) (k MK SA NODES E LV : Z) (pad tw ne : word) (top bot : Z) (fl mk buf fs ls fn : list word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a2 = Z_to_bv 64 0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 304 <= bv_unsigned sp ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  err_env m od e k MK SA NODES E LV pad tw ne -> err_blocks (rt_live RT Σ) MK SA NODES E -> es_rep m E top bot fl mk buf fs ls fn ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_vset_error m)))
    (fun c => exists (Σ' : rts RT) (e' v : word) (buf' : list word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (VSE_W E) m m'
           /\ err_env m' od e' k MK SA NODES E LV pad tw ne /\ es_rep m' E top bot fl mk buf' fs ls fn) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem err_vset_error_cps : err_vset_error_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo od e k MK SA NODES E LV pad tw ne top bot fl mk buf fs ls fn
    FDO MST -> -> ART0 MI0 CALL HSTK Hfr Hcr ENV BLK ES.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 304 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  set (usp1 := usp + -112).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof BLK as (INM & INS & INN & INE & MKAL & SAAL & NAL & EAL).
  pose proof (af_live_range RT AF Σ m MK 72 ART0 INM) as R1. pose proof (af_live_range RT AF Σ m SA 32 ART0 INS) as R2.
  pose proof (af_live_range RT AF Σ m NODES 128 ART0 INN) as R3. pose proof (af_live_range RT AF Σ m E 904 ART0 INE) as R4.
  (* [comment removed for export] *)
  pose proof (vse_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) UT SHC MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j1 & m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 112 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 112 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG01 : forall a n, a + n <= usp - 112 -> agree_on (fun x => a <= x < a + n) m m1).
  { intros a n H x Hx. cbv beta in Hx. refine (agree_of_munch _ m m1 (fun y => a <= y < a + n) MU1 _ x Hx). intros y Hy. cbv beta in Hy. cbn [outside]. lia. }
  assert (ENV1 : err_env m1 od e k MK SA NODES E LV pad tw ne).
  { apply (err_env_agree m m1 _ _ _ _ _ _ _ _ _ _ _ ENV); [| exact WM1]. intros a n H. apply AG01.
    unfold ERRNO_A, STACK_WIN, RT_STACK in *. destruct ENV as (_ & _ & (_ & _ & HK & _)). lia. }
  pose proof ENV1 as (ICS1 & ERC1 & CH1).
  (* [comment removed for export] *)
  apply (C_GSI Σ PMc (Z_to_bv 64 SITE_vse_gsi) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 6736696) (Z_to_bv 64 0)
           a3 a4 a5 a6 a7 s2 s3 a1 s5 a0 s7 a3 (Z_to_bv 64 0x7fff8000) s10 s11 t3 t4 t5 t6 F fc m1 lo od e k MK SA NODES E LV pad tw ne FDO MST eq_refl eq_refl ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 7. }
  { rewrite EU1. unfold usp1. lia. }
  { exact Hfr. } { exact Hcr. } { exact ICS1. } { exact ERC1. } { exact CH1. }
  { exact INM. } { exact INS. } { exact INN. } { exact INE. } { exact MKAL. } { exact SAAL. } { exact NAL. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & e1 & Hc2 & LV1 & FRS1 & SP1 & CR1 & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ICS2 & ERC2 & CH2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_vse_gsi) in Hc2' by (unfold SITE_vse_gsi; lia).
  assert (AG12 : forall a n, (usp1 <= a /\ a + n <= USTACK_TOP) \/ (E <= a /\ a + n <= E + 904) -> agree_on (fun x => a <= x < a + n) m1 m2).
  { intros a n H x Hx. cbv beta in Hx. apply PRES2.
    - destruct H as [H|H]; [left; unfold usp1 in *; lia|]. right; right; left. exists E, 904. split; [exact INE | lia].
    - unfold usp1, ERRNO_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *. cbn [outside]. lia. }
  assert (WM02 : wmono asegs m m2) by exact (wmono_trans asegs _ _ _ WM1 WM2).
  assert (AG2 : forall a n, usp1 <= a -> a + n <= USTACK_TOP -> agree_on (fun x => a <= x < a + n) m1 m2) by (intros a n H1 H2; apply AG12; left; lia).
  cl_keep FR1 AG2 WM2 FR2.
  assert (ES2 : es_rep m2 E top bot fl mk buf fs ls fn).
  { apply (es_rep_agree m1 m2); [| | exact WM2].
    - apply (es_rep_agree m m1); [exact ES | | exact WM1]. apply (AG01 E 904). unfold STACK_WIN, RT_STACK in *. lia.
    - apply (AG12 E 904). right. lia. }
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  assert (INE2 : In (E, 904) (rt_live RT Σ1)) by (rewrite LV1; exact INE).
  pose proof (afp_live_hi RT GOBJ AFP Σ m E 904 ART0 INE ltac:(lia)) as EHI.
  pose proof (proj2 (af_acc_live RT AF Σ1 m2 E 904 ART2 INE2)) as ACCE2.
  (* [comment removed for export] *)
  pose proof (vse_s1_walk ra sp gp u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 s3 s5 s7 s10 s11 u3 u4 u5 u6 a1 a0 a3 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 m2 lo j1
                E top bot fl mk buf fs ls fn
                ST2 ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) UT2 SHC2 FR2 ES2 ACCE2 EAL EHI
                ltac:(lia) MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & buf' & m3 & -> & MU3 & WM3 & MI3 & ST3 & ES3) & Hc3'). clear Hc3.
  fold usp in ST3.
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 (usp - 112) ART2 ltac:(rewrite SP1; lia)); [| exact WM3]. intros a Ha. apply MU3. cbn [outside].
    split; [intros X; apply Ha; left; unfold USTACK_TOP in *; lia|]. split; [| exact I]. intros X. apply Ha. right; right; left. exists E, 904. split; [exact INE2 | lia]. }
  apply Hk. exists Σ1, e1, d0, buf'.
  split; [| split; [exact LV1 | split; [exact FRS1 | split; [exact SP1 | split; [exact CR1 | exact CG1]]]]].
  eapply ASTA_conseq; [exact Hc3'|]. intros ms <-. exists m3.
  split; [exists v0, v1, v2, d1, d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, F2, fc2; reflexivity|].
  split; [split; [exact ART3 | split; [exact MI3 | split; [exact (wmono_trans asegs _ _ _ WM02 WM3) | exact ST3]]]|].
  split.
  { intros a Ha Ho. unfold VSE_W, ERRNO_A in Ho. cbn [outside] in Ho.
    pose proof (cl_split RT AF Σ m usp 304 _ ART0 ltac:(lia) ltac:(lia) Ha) as SPL.
    rewrite (MU3 a ltac:(cbn [outside]; lia)).
    rewrite (PRES2 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto | auto | unfold usp1; lia]) ltac:(unfold ERRNO_A; cbn [outside]; lia)).
    exact (PR1 a Ha I). }
  split; [| exact ES3].
  pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 INM INE ltac:(intros X; injection X; lia)) as D1.
  pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 INS INE ltac:(intros X; injection X; lia)) as D2.
  pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 INN INE ltac:(intros X; injection X; lia)) as D3.
  apply (err_env_agree m2 m3 _ _ _ _ _ _ _ _ _ _ _ (conj ICS2 (conj ERC2 CH2))); [| exact WM3].
  intros a n H x Hx. cbv beta in Hx. refine (agree_of_munch _ m2 m3 (fun y => a <= y < a + n) MU3 _ x Hx). intros y Hy. cbv beta in Hy.
  unfold ERRNO_A, SEGTOP_A, STACK_WIN, RT_STACK in *. cbn [outside]. lia.
Qed.

End CVse.
