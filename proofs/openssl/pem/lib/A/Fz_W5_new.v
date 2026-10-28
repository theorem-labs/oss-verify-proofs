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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_M_malloc Fz_env Fz_M_free Fz_T_sa Fz_W5_glx Fz_W5_icb Fz_W5_gsi Fz_ukit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Fz_W5_rep Fz_W5_vset.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition e_ERR_new : Z := 0x1fc628.
Definition SITE_new_gsi : Z := 0x1fc65c.        (* [comment removed for export] *)
Definition SITE_new_free1 : Z := 0x1fc804.      (* [comment removed for export] *)
Definition SITE_new_free2 : Z := 0x1fc838.      (* [comment removed for export] *)
Definition SITE_new_join : Z := 0x1fc6e4.        (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma upd_same : forall {X} (l : list X) i x, nth_error l i = Some x -> upd l i x = l.
Proof. induction l as [|y l IH]; intros [|i] x H; cbn in *; [discriminate | discriminate | congruence | rewrite (IH i x H); reflexivity]. Qed.

(* [comment removed for export] *)
Ltac wstore32 AH BASE ws i ADDR :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    let SOK := fresh "SOK" in
    pose proof (u32arr_store_ok asegs mX BASE ws i (Z_to_bv 64 ADDR) AH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK;
    zstep;
    let A2 := fresh "AW" in
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) => pose proof (u32arr_write asegs mX BASE ws i v AH ltac:(lia)) as A2
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mY ?a ?bs) _) =>
        change (write_to_mem mY a bs) with (write_to_mem mY a (le4 (Z_to_bv 64 0))); pose proof (u32arr_write asegs mX BASE ws i (Z_to_bv 64 0) AH ltac:(lia)) as A2
    end;
    replace (BASE + 4 * i) with ADDR in A2 by lia;
    clear AH; store_done; rename A2 into AH
  end.
Ltac wstore64 AH BASE ws i ADDR :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok asegs mX BASE ws i (Z_to_bv 64 ADDR) AH ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK;
    zstep;
    let A2 := fresh "AW" in
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le8 ?v)) _) => pose proof (u64arr_write asegs mX BASE ws i v AH ltac:(lia)) as A2
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mY ?a ?bs) _) =>
        change (write_to_mem mY a bs) with (write_to_mem mY a (le8 (Z_to_bv 64 0))); pose proof (u64arr_write asegs mX BASE ws i (Z_to_bv 64 0) AH ltac:(lia)) as A2
    end;
    replace (BASE + 8 * i) with ADDR in A2 by lia;
    clear AH; store_done; rename A2 into AH
  end.



(* [comment removed for export] *)
Definition new_s0_post (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_new_gsi) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp s1' (Z_to_bv 64 1) a1
                 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0x7fff8000) s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_get_state) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0]
    /\ stk asegs m' lo (bv_unsigned sp + -48).

Lemma new_s0_walk : forall ra0 sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] -> mem_inv asegs m ->
  evt asegs (new_s0_post sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' lo m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_ERR_new) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HLOS SPH UT SHC MI. unfold e_ERR_new, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 48, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 48, SP)]) by ut_fp_lia.
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST.
  zstep. do 6 zstep. zstep. replace (SP + -48 + 48) with SP by lia. do 3 zstep. do 2 zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold new_s0_post, SITE_new_gsi, e_get_state. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
Definition new_top_expr (t : Z) : Z :=
  bv_swrap 32 (t - Z.land (Z.land (t + bv_swrap 32 (bv_wrap 32 (Z.land (bv_swrap 32 (bv_swrap 32 t ≫ 31)) 18446744073709551615) ≫ 28)) 18446744073709551615) 18446744073709551600).
Lemma new_top_arith : forall top, 0 <= top < 16 -> new_top_expr (top + 1) = (top + 1) mod 16.
Proof.
  intros top H. rewrite <- (Z2Nat.id top) by lia. remember (Z.to_nat top) as n eqn:En. assert (Hn : (n < 16)%nat) by lia. clear H En top.
  do 16 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.
Definition new_bot_expr (t : Z) : Z :=
  bv_signed (Z_to_bv 64 (Z.land (bv_swrap 32 (t - Z.land (Z.land (t + Z.land (bv_signed (Z_to_bv 64 (t ≪ 56)) ≫ 3) 18446744073709551615 ≫ 60) 18446744073709551615) 240)) 18446744073709551615 ≪ 56)) ≫ 56.
Lemma new_bot_arith : forall b, 0 <= b < 16 -> new_bot_expr (b + 1) = (b + 1) mod 16.
Proof.
  intros b H. rewrite <- (Z2Nat.id b) by lia. remember (Z.to_nat b) as n eqn:En. assert (Hn : (n < 16)%nat) by lia. clear H En b.
  do 16 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.

(* [comment removed for export] *)
Definition new_s1_post (sp gp tp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (E top : Z) (fl mk buf fs ls fn : list word) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a2 a3 a5 a6 a7 t3 t4 t5 t6 : word) (bot' : Z) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_new_gsi) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 (E + 900)) (Z_to_bv 64 E)
                 a2 a3 (Z_to_bv 64 ((top + 1) mod 16)) a5 a6 a7 (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_new_join) fc None m' (seg_rom asegs)
    /\ munch [(E + 896, E + 904)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ es_rep m' E ((top + 1) mod 16) bot' fl mk buf fs ls fn.

Lemma new_s1_walk : forall sp gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (E top bot : Z) (fl mk buf fs ls fn : list word),
  lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  es_rep m E top bot fl mk buf fs ls fn ->
  acc asegs m E 904 -> E mod 8 = 0 -> 0x10007fff8000 <= E -> E + 904 <= lo -> mem_inv asegs m ->
  evt asegs (new_s1_post sp gp (Z_to_bv 64 0xba3ef0) s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc E top fl mk buf fs ls fn m)
    (MS (mkR (Z_to_bv 64 SITE_new_gsi) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 E) a1
             a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_new_gsi) fc None m (seg_rom asegs)).
Proof.
  intros until fn. intros HLO HLOS SPH UT SHC ES ACCE EAL EHI ELO MI. unfold SITE_new_gsi, g_shadow_memory_dynamic_address in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(E + 896, E + 904)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(E + 896, E + 904)]) by ut_fp_lia. assert (HWS : sh_fp [(E + 896, E + 904)]) by sh_fp_lia.
  zstep. if_cases KE; zify_cond KE. { exfalso. rewrite ?unsigned_lit in KE by lia. lia. }
  zstep.
  do 4 zstep. zstep. th_if_lit.
  zstep. rewrite (t_sx32_small top) by lia.
  zstep. zstep. zstep. do 5 zstep.
  lazymatch goal with |- context [Z_to_bv 64 (bv_swrap 32 ?x)] => change (bv_swrap 32 x) with (new_top_expr (top + 1)) end.
  rewrite (new_top_arith top) by lia. set (NT := (top + 1) mod 16). assert (HNT : 0 <= NT < 16) by (subst NT; clear - HT; Z.div_mod_to_equations; lia).
  zstep.
  zstep. zstep. zstep. th_if_lit. zstep. rewrite (t_sx32_small bot) by lia.
  zstep. if_cases KB; zify_cond KB.
  2: zstep; zstep; th_if_lit; do 9 zstep.
  2: lazymatch goal with |- context [Z_to_bv 64 (bv_signed ?x ≫ 56)] => change (bv_signed x ≫ 56) with (new_bot_expr (NT + 1)) end.
  2: rewrite (new_bot_arith NT) by lia; zstep.
  all: subst SP NT; rewrite ?Z_to_bv_bv_unsigned.
  all: unfold new_s1_post, SITE_new_join; apply evt_done; do 14 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|].
  all: unfold es_rep; repeat (split; [first [eassumption | lia] |]).
  all: clear - HB HT; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Definition NEW_FILE_LIT : Z := 0x49700.          (* [comment removed for export] *)
Definition new_s2_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (E i bot : Z) (fs fn : list word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fl' mk' buf' ls' : list word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_new_free1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 (E + i * 8 + 576)) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (E + i * 8)) (Z_to_bv 64 ((E + i * 8 + 576) ≫ 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_free) fc None m' (seg_rom asegs)
    /\ munch [(E, E + 904)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ es_rep m' E i bot fl' mk' buf' fs ls' fn.

Lemma new_s2_walk : forall sp gp t0 t1 t2 s1 a2 a3 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (E i bot : Z) (fl mk buf fs ls fn : list word),
  lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  es_rep m E i bot fl mk buf fs ls fn -> nth_error fs (Z.to_nat i) = Some (Z_to_bv 64 0) ->
  acc asegs m E 904 -> E mod 8 = 0 -> 0x10007fff8000 <= E -> E + 904 <= lo -> mem_inv asegs m ->
  evt asegs (new_s2_post sp gp (Z_to_bv 64 0xba3ef0) s5 s6 s7 s8 s9 s10 s11 F fc E i bot fs fn m)
    (MS (mkR (Z_to_bv 64 SITE_new_gsi) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 (E + 900)) (Z_to_bv 64 E)
             a2 a3 (Z_to_bv 64 i) a5 a6 a7 (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_new_join) fc None m (seg_rom asegs)).
Proof.
  intros until fn. intros HLO HLOS SPH UT SHC ES FS0 ACCE EAL EHI ELO MI. unfold SITE_new_gsi, SITE_new_join, g_shadow_memory_dynamic_address in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(E, E + 904)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(E, E + 904)]) by ut_fp_lia. assert (HWS : sh_fp [(E, E + 904)]) by sh_fp_lia.
  zstep. rewrite (Z.shiftl_mul_pow2 i 2) by lia. change (2 ^ 2) with 4. zstep. zstep.
  do 3 zstep. zstep. th_if_lit.
  pose proof (u8arr_read asegs m (E + 512) (repeat (Z_to_bv 8 0) 64) (i * 4) (Z_to_bv 8 0) (Z_to_bv 64 (E + i * 4 + 512)) A6
                ltac:(apply nth_error_repeat; lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
  zstep. rewrite (Z.shiftl_mul_pow2 i 3) by lia. change (2 ^ 3) with 8. zstep.
  do 4 zstep. zstep. th_if_lit.
  zstep. zstep. th_if_lit.
  zstore A4 (E + 256) 128%nat (i * 8) 8%nat (E + i * 8 + 256).
  zstep. do 3 zstep. zstep. th_if_lit. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0.
  zstore A5 (E + 384) 128%nat (i * 8) 8%nat (E + i * 8 + 384).
  zstep.
  zstep. zstep. th_if_lit.
  zstore A6 (E + 512) 64%nat (i * 4) 4%nat (E + i * 4 + 512).
  zstep.
  do 3 zstep. zstep. th_if_lit.
  wstore32 A2 (E + 64) mk i (E + i * 4 + 64).
  do 3 zstep. zstep. th_if_lit.
  wstore32 A1 E fl i (E + i * 4).
  do 4 zstep. zstep. th_if_lit.
  wstore64 A3 (E + 128) buf i (E + i * 8 + 128).
  do 4 zstep. zstep. th_if_lit. zstep. zstep.
  wstore32 A8 (E + 704) ls i (E + i * 4 + 704).
  zstep. zstep. zstep. zstep. th_if_lit.
  pose proof (u64arr_read asegs _ (E + 576) fs i (Z_to_bv 64 0) (Z_to_bv 64 (E + i * 8 + 576)) A7 FS0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD. zstep. zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold new_s2_post, SITE_new_free1, e_CRYPTO_free. apply evt_done. do 19 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold es_rep; repeat (split; [first [eassumption | rewrite upd_length; assumption | lia] |]); lia.
Qed.

(* [comment removed for export] *)
Definition new_s3_post (sp gp tp s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (E i bot : Z) (fl mk buf fs ls fn : list word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_new_free2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 (E + i * 8 + 768)) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ((E + i * 8 + 768) ≫ 3 + 2147450880)) (Z_to_bv 64 (E + i * 8)) (Z_to_bv 64 ((E + i * 8 + 576) ≫ 3 + 2147450880))
                 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_free) fc None m' (seg_rom asegs)
    /\ munch [(E, E + 904)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ es_rep m' E i bot fl mk buf fs ls fn.

Lemma new_s3_walk : forall sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (E i bot : Z) (fl mk buf fs ls fn : list word),
  lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> img_untouched m ->
  es_rep m E i bot fl mk buf fs ls fn -> nth_error fs (Z.to_nat i) = Some (Z_to_bv 64 0) -> nth_error fn (Z.to_nat i) = Some (Z_to_bv 64 0) ->
  acc asegs m E 904 -> E mod 8 = 0 -> 0x10007fff8000 <= E -> E + 904 <= lo -> mem_inv asegs m ->
  evt asegs (new_s3_post sp gp (Z_to_bv 64 0xba3ef0) s5 s6 s7 s8 s9 s10 s11 F fc E i bot fl mk buf fs ls fn m)
    (MS (mkR (Z_to_bv 64 SITE_new_free1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 (E + i * 8 + 576)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (E + i * 8)) (Z_to_bv 64 ((E + i * 8 + 576) ≫ 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_new_free1) fc None m (seg_rom asegs)).
Proof.
  intros until fn. intros HLO HLOS SPH UT ES FS0 FN0 ACCE EAL EHI ELO MI. unfold SITE_new_free1 in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(E, E + 904)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(E, E + 904)]) by ut_fp_lia. assert (HWS : sh_fp [(E, E + 904)]) by sh_fp_lia.
  zstep. zstep. th_if_lit.
  wstore64 A7 (E + 576) fs i (E + i * 8 + 576). rewrite (upd_same fs (Z.to_nat i) (Z_to_bv 64 0) FS0) in A7.
  zstep. zstep. zstep. zstep. zstep. th_if_lit.
  pose proof (u64arr_read asegs _ (E + 768) fn i (Z_to_bv 64 0) (Z_to_bv 64 (E + i * 8 + 768)) A9 FN0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD. zstep. zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold new_s3_post, SITE_new_free2, e_CRYPTO_free. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold es_rep; repeat (split; [first [eassumption | lia] |]); lia.
Qed.

(* [comment removed for export] *)
Definition new_s4_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (E i bot lo : Z) (fl mk buf fs ls fn : list word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(E, E + 904)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ es_rep m' E i bot fl mk buf fs ls fn.

Lemma new_s4_walk : forall sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' : word) (F : bvmap 5 word) fc (m : mem) (lo : Z) (E i bot : Z) (fl mk buf fs ls fn : list word),
  stk asegs m lo (bv_unsigned sp + -48) -> lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  es_rep m E i bot fl mk buf fs ls fn -> nth_error fn (Z.to_nat i) = Some (Z_to_bv 64 0) ->
  acc asegs m E 904 -> E mod 8 = 0 -> 0x10007fff8000 <= E -> E + 904 <= lo -> mem_inv asegs m ->
  evt asegs (new_s4_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 F fc E i bot lo fl mk buf fs ls fn m)
    (MS (mkR (Z_to_bv 64 SITE_new_free2) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 (E + i * 8 + 768)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 ((E + i * 8 + 768) ≫ 3 + 2147450880)) s3 s4 s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_new_free2) fc None m (seg_rom asegs)).
Proof.
  intros until fn. intros ST HLO HLOS SPH UT FR ES FN0 ACCE EAL EHI ELO MI. unfold SITE_new_free2 in *.
  pose proof ES as (A1 & L1 & A2 & L2 & A3 & L3 & A4 & A5 & A6 & A7 & L7 & A8 & L8 & A9 & L9 & TB & HT & HB).
  pose proof (repeat_length (Z_to_bv 8 0) 128) as LZ128. pose proof (repeat_length (Z_to_bv 8 0) 64) as LZ64.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(E, E + 904)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(E, E + 904)]) by ut_fp_lia. assert (HWS : sh_fp [(E, E + 904)]) by sh_fp_lia.
  zstep. zstep. th_if_lit.
  wstore64 A9 (E + 768) fn i (E + i * 8 + 768). rewrite (upd_same fn (Z.to_nat i) (Z_to_bv 64 0) FN0) in A9.
  do 6 zstep. zstep. release_frame FR ST SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold new_s4_post. apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  unfold es_rep; repeat (split; [first [eassumption | lia] |]); lia.
Qed.

(* [comment removed for export] *)
Lemma cl_cell_off : forall E x, 0x10007fff8000 <= E -> cl_cell x -> ~ (E <= x < E + 904) /\ outside [(ERRNO_A, ERRNO_A + 4); (E, E + 904)] x.
Proof.
  intros E x HE (lo & hi & Hin & Hx). unfold CL_CELLS, G_MALLOC_IMPL, CL_REALLOC_IMPL, CL_FREE_IMPL, CL_MEMSET_FUNC, G_ALLOW_CUST, ssp_guard in Hin. unfold ERRNO_A. cbn [In outside] in *.
  repeat (destruct Hin as [EQ|Hin]; [injection EQ as <- <-; lia|]). destruct Hin.
Qed.

Section CNew.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_GSI : get_state_steady_stmt RT.
Hypothesis C_FRN : crypto_free_null_env_stmt RT.

Definition NEW_W (E : Z) : list (Z * Z) := [(ERRNO_A, ERRNO_A + 4); (E, E + 904)].

(* [comment removed for export] *)
Definition err_new_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (od e : word) (k MK SA NODES E LV : Z) (pad tw ne : word) (top bot : Z) (fl mk buf fs ls fn : list word)
    (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 240 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_ERR_new (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) [(SITE_new_free1, e_ERR_new); (SITE_new_free2, e_ERR_new)]
                      [(SITE_new_free1, e_CRYPTO_free); (SITE_new_free1, e_free); (SITE_new_free2, e_CRYPTO_free); (SITE_new_free2, e_free)] ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  err_env m od e k MK SA NODES E LV pad tw ne -> err_blocks (rt_live RT Σ) MK SA NODES E -> es_rep m E top bot fl mk buf fs ls fn ->
  nth_error fs (Z.to_nat ((top + 1) mod 16)) = Some (Z_to_bv 64 0) -> nth_error fn (Z.to_nat ((top + 1) mod 16)) = Some (Z_to_bv 64 0) ->
  cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_ERR_new m)))
    (fun c => exists (Σ' : rts RT) (e' v : word) (bot' : Z) (fl' mk' buf' ls' : list word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (NEW_W E) m m'
           /\ err_env m' od e' k MK SA NODES E LV pad tw ne /\ es_rep m' E ((top + 1) mod 16) bot' fl' mk' buf' fs ls' fn /\ cl_env m' lb canary) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem err_new_cps : err_new_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer od e k MK SA NODES E LV pad tw ne top bot fl mk buf fs ls fn
    lb canary FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hcr ENV BLK ES FS0 FN0 CLE.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 240 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  set (usp1 := usp + -48).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof BLK as (INM & INS & INN & INE & MKAL & SAAL & NAL & EAL).
  pose proof (af_live_range RT AF Σ m MK 72 ART0 INM) as R1. pose proof (af_live_range RT AF Σ m SA 32 ART0 INS) as R2.
  pose proof (af_live_range RT AF Σ m NODES 128 ART0 INN) as R3. pose proof (af_live_range RT AF Σ m E 904 ART0 INE) as R4.
  pose proof (afp_live_hi RT GOBJ AFP Σ m E 904 ART0 INE ltac:(lia)) as EHI.
  pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 INM INE ltac:(intros X; injection X; lia)) as D1.
  pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 INS INE ltac:(intros X; injection X; lia)) as D2.
  pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 INN INE ltac:(intros X; injection X; lia)) as D3.
  pose proof ES as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HT & HB).
  (* [comment removed for export] *)
  assert (ENVR : forall a n x, (0xb9f200 <= a /\ a + n <= 0xb9f848) \/ (0xbc52a0 <= a /\ a + n <= 0xbc5698) \/ (ERRNO_A <= a /\ a + n <= ERRNO_A + 4)
               \/ (MK <= a /\ a + n <= MK + 72) \/ (SA <= a /\ a + n <= SA + 32) \/ (NODES <= a /\ a + n <= NODES + 128) -> a <= x < a + n ->
               aclient (rt_live RT Σ) (rt_frames RT Σ) usp x /\ ~ (E <= x < E + 904) /\ x < usp - 64).
  { intros a' n x H Hx. destruct H as [H|[H|[H|[H|[H|H]]]]].
    1-3: split; [right; left; apply client_static_intro; unfold ERRNO_A in H; lia | unfold ERRNO_A, STACK_WIN, RT_STACK in *; clear - H Hx EHI NUM LOW HSTK; lia].
    - split; [apply (acl_live _ _ _ MK 72); [exact INM | lia] | unfold STACK_WIN, RT_STACK in *; clear - H Hx D1 R1 NUM LOW HSTK; lia].
    - split; [apply (acl_live _ _ _ SA 32); [exact INS | lia] | unfold STACK_WIN, RT_STACK in *; clear - H Hx D2 R2 NUM LOW HSTK; lia].
    - split; [apply (acl_live _ _ _ NODES 128); [exact INN | lia] | unfold STACK_WIN, RT_STACK in *; clear - H Hx D3 R3 NUM LOW HSTK; lia]. }
  (* [comment removed for export] *)
  pose proof (new_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) UT SHC MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 48 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  assert (A01 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m1 x = m x).
  { intros x Hx. apply MU1. cbn [outside]. split; [| exact I]. destruct (cl_split RT AF Σ m usp 48 _ ART0 ltac:(lia) ltac:(lia) Hx); lia. }
  assert (ENV1 : err_env m1 od e k MK SA NODES E LV pad tw ne).
  { apply (err_env_agree m m1 _ _ _ _ _ _ _ _ _ _ _ ENV); [| exact WM1]. intros a' n H x Hx. cbv beta in Hx. apply A01. exact (proj1 (ENVR a' n _ H Hx)). }
  pose proof ENV1 as (ICS1 & ERC1 & CH1).
  (* [comment removed for export] *)
  apply (C_GSI Σ PMc (Z_to_bv 64 SITE_new_gsi) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 0x7fff8000) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo od e k MK SA NODES E LV pad tw ne FDO MST eq_refl eq_refl ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 3. }
  { rewrite EU1. unfold usp1. lia. }
  { exact Hfr. } { exact Hcr. } { exact ICS1. } { exact ERC1. } { exact CH1. }
  { exact INM. } { exact INS. } { exact INN. } { exact INE. } { exact MKAL. } { exact SAAL. } { exact NAL. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & e1 & Hc2 & LV1 & FRS1 & SP1 & CR1 & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ICS2 & ERC2 & CH2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_new_gsi) in Hc2' by (unfold SITE_new_gsi; lia).
  assert (A02 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> outside (NEW_W E) (bv_unsigned x) -> m2 x = m x).
  { intros x Hx Ho. rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia]) ltac:(unfold NEW_W in Ho; cbn [outside] in Ho |- *; exact (conj (proj1 Ho) I))).
    exact (A01 x Hx). }
  assert (AG2 : forall a n, usp1 <= a -> a + n <= USTACK_TOP -> agree_on (fun x => a <= x < a + n) m1 m2).
  { intros a' n H1 H2 x Hx. cbv beta in Hx. apply PRES2; [left; lia|]. unfold ERRNO_A. cbn [outside]. unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *. clear - H1 H2 Hx R4 NUM LOW HSTK. lia. }
  cl_keep FR1 AG2 WM2 FR2.
  assert (ES2 : es_rep m2 E top bot fl mk buf fs ls fn).
  { apply (es_rep_agree m m2); [exact ES | | exact (wmono_trans asegs _ _ _ WM1 WM2)]. intros x Hx. cbv beta in Hx.
    rewrite (PRES2 x ltac:(apply (acl_live _ _ _ E 904); [exact INE | lia]) ltac:(unfold ERRNO_A; cbn [outside]; clear - Hx EHI; lia)).
    apply A01. apply (acl_live _ _ _ E 904); [exact INE | lia]. }
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  assert (INE2 : In (E, 904) (rt_live RT Σ1)) by (rewrite LV1; exact INE).
  pose proof (proj2 (af_acc_live RT AF Σ1 m2 E 904 ART2 INE2)) as ACCE2.
  (* [comment removed for export] *)
  pose proof (new_s1_walk sp gp u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 lo E top bot fl mk buf fs ls fn
                ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) UT2 SHC2 ES2 ACCE2 EAL EHI ltac:(lia) MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (v0 & v1 & v2 & d2 & d3 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & bot' & m3 & -> & MU3 & WM3 & MI3 & ES3) & Hc3'). clear Hc3.
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 usp1 ART2 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM3].
    intros x Hx. apply MU3. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ E 904); [exact INE2 | lia]. }
  destruct (af_client_consts RT AF Σ1 m3 ART3) as (_ & SHC3 & _ & _ & UT3).
  pose proof (proj2 (af_acc_live RT AF Σ1 m3 E 904 ART3 INE2)) as ACCE3.
  (* [comment removed for export] *)
  pose proof (new_s2_walk sp gp v0 v1 v2 s1 d2 d3 d5 d6 d7 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F2 fc2 m3 lo E ((top + 1) mod 16) bot' fl mk buf fs ls fn
                ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) UT3 SHC3 ES3 FS0 ACCE3 EAL EHI ltac:(lia) MI3) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc3' c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & fl' & mk' & buf' & ls' & m4 & -> & MU4 & WM4 & MI4 & ES4) & Hc4').
  clear Hc4. fold usp in Hc4'. fold usp1 in Hc4'.
  assert (ART4 : ART RT Σ1 m4).
  { apply (af_frame RT AF Σ1 m3 m4 usp1 ART3 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM4].
    intros x Hx. apply MU4. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ E 904); [exact INE2 | lia]. }
  (* [comment removed for export] *)
  assert (B4 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> m4 x = m2 x).
  { intros x Hx HnE. rewrite (MU4 x ltac:(cbn [outside]; clear - HnE; lia)). apply MU3. cbn [outside]. clear - HnE. lia. }
  assert (ST4 : stk asegs m4 lo usp1).
  { apply (stk_agree_nw asegs m2 m4 _ _ ST2). intros x Hx. cbv beta in Hx.
    rewrite (MU4 x ltac:(cbn [outside]; unfold usp1, STACK_WIN, RT_STACK in *; clear - Hx R4 NUM LOW HSTK; lia)). apply MU3. cbn [outside]. unfold usp1, STACK_WIN, RT_STACK in *; clear - Hx R4 NUM LOW HSTK; lia. }
  assert (AGS4 : forall a n, usp1 <= a -> a + n <= USTACK_TOP -> agree_on (fun x => a <= x < a + n) m2 m4).
  { intros a' n H1 H2 x Hx. cbv beta in Hx. rewrite (MU4 x ltac:(cbn [outside]; unfold usp1, STACK_WIN, RT_STACK in *; clear - H1 Hx R4 NUM LOW HSTK; lia)).
    apply MU3. cbn [outside]. unfold usp1, STACK_WIN, RT_STACK in *; clear - H1 Hx R4 NUM LOW HSTK; lia. }
  pose proof (wmono_trans asegs _ _ _ WM3 WM4) as WM24. cl_keep FR2 AGS4 WM24 FR4.
  assert (AG04 : agree_on (fun x => usp <= x < USTACK_TOP) m m4).
  { intros x Hx. cbv beta in Hx. rewrite (B4 x ltac:(apply acl_stack; exact Hx) ltac:(unfold STACK_WIN, RT_STACK in *; clear - Hx R4 NUM LOW HSTK; lia)).
    apply A02; [apply acl_stack; exact Hx|]. unfold NEW_W, ERRNO_A. cbn [outside]. unfold STACK_WIN, RT_STACK in *; clear - Hx R4 NUM LOW HSTK EHI; lia. }
  assert (CLE4 : cl_env m4 lb canary).
  { apply (cl_env_agree m m4 _ _ CLE). intros x Hx. destruct (cl_cell_off E _ EHI Hx) as [HnE Ho].
    rewrite (B4 x ltac:(right; left; exact (cl_cell_static _ Hx)) HnE). exact (A02 x ltac:(right; left; exact (cl_cell_static _ Hx)) Ho). }
  destruct (cl_chain_call (rt_cg RT Σ) e_ERR_new e_CRYPTO_free SITE_new_free1 m m4 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(left; reflexivity)) (proj2 CGH _ ltac:(left; reflexivity)) UWC AG04
              ltac:(fold usp; replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m4 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR4))
              ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX4 & UWC4).
  rewrite <- CG1 in CTX4.
  (* [comment removed for export] *)
  apply (C_FRN Σ1 PMc (Z_to_bv 64 SITE_new_free1) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 sp (Z_to_bv 64 (E + (top + 1) mod 16 * 8 + 576)) (Z_to_bv 64 0)
           g1 g2 g3 g4 g5 g6 g7 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 (E + (top + 1) mod 16 * 8))
           (Z_to_bv 64 ((E + (top + 1) mod 16 * 8 + 576) ≫ 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F2 fc2 m4 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl ART4 MI4).
  { fold usp in SPA. unfold call_ok. rewrite EU1, SP1. split; [exact ST4|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 3). lia. }
  { rewrite (unsigned_lit SITE_new_free1) by (unfold SITE_new_free1; lia). exact CTX4. }
  { exact UWC4. }
  { rewrite CG1. apply (proj2 CGH). right; left; reflexivity. }
  { exact CLE4. }
  { exact Hc4'. }
  clear Hc4'. intros c5 (v & Hc5).
  destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & CLE5) & Hc5'). clear Hc5.
  destruct RS5 as (x0 & x1 & x2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & x3 & x4 & x5 & x6 & F5 & fc5 & ->).
  rewrite EU1 in ST5, PRES5. rewrite (ret_pc_even SITE_new_free1) in Hc5' by (unfold SITE_new_free1; lia).
  assert (B5 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> m5 x = m2 x).
  { intros x Hx HnE. rewrite (PRES5 x ltac:(rewrite LV1, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia])). exact (B4 x Hx HnE). }
  assert (ES5 : es_rep m5 E ((top + 1) mod 16) bot' fl' mk' buf' fs ls' fn).
  { apply (es_rep_agree m4 m5 _ _ _ _ _ _ _ _ _ ES4); [| exact WM5]. intros x Hx. cbv beta in Hx. apply PRES5. apply (acl_live _ _ _ E 904); [exact INE2 | lia]. }
  destruct (af_client_consts RT AF Σ1 m5 ART5) as (_ & _ & _ & _ & UT5).
  pose proof (proj2 (af_acc_live RT AF Σ1 m5 E 904 ART5 INE2)) as ACCE5.
  (* [comment removed for export] *)
  pose proof (new_s3_walk sp gp x0 x1 x2 v h1 h2 h3 h4 h5 h6 h7 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6 F5 fc5 m5 lo E ((top + 1) mod 16) bot' fl' mk' buf' fs ls' fn
                ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) UT5 ES5 FS0 FN0 ACCE5 EAL EHI ltac:(lia) MI5) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc5' c6 Hc6.
  destruct (ASTA_unpack RT Σ1 _ _ c6 Hc6) as (ms6 & (y0 & y1 & y2 & i1 & i2 & i3 & i4 & i5 & i6 & i7 & y3 & y4 & y5 & y6 & m6 & -> & MU6 & WM6 & MI6 & ES6) & Hc6'). clear Hc6.
  fold usp in Hc6'. fold usp1 in Hc6'.
  assert (ART6 : ART RT Σ1 m6).
  { apply (af_frame RT AF Σ1 m5 m6 usp1 ART5 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM6].
    intros x Hx. apply MU6. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ E 904); [exact INE2 | lia]. }
  assert (B6 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> m6 x = m2 x).
  { intros x Hx HnE. rewrite (MU6 x ltac:(cbn [outside]; clear - HnE; lia)). exact (B5 x Hx HnE). }
  assert (ST6 : stk asegs m6 lo usp1).
  { apply (stk_agree_nw asegs m5 m6 _ _ ST5). intros x Hx. cbv beta in Hx. apply MU6. cbn [outside]. unfold usp1, STACK_WIN, RT_STACK in *; clear - Hx R4 NUM LOW HSTK; lia. }
  assert (FR6 : rw_cells asegs m6 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m4 m6 _ _ FR4); [| exact (wmono_trans asegs _ _ _ WM5 WM6)]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    rewrite (MU6 x ltac:(cbn [outside]; unfold STACK_WIN, RT_STACK in *; clear - Hx R4 NUM LOW HSTK; lia)). apply PRES5. left. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  assert (AG06 : agree_on (fun x => usp <= x < USTACK_TOP) m m6).
  { intros x Hx. cbv beta in Hx. rewrite (B6 x ltac:(apply acl_stack; exact Hx) ltac:(unfold STACK_WIN, RT_STACK in *; clear - Hx R4 NUM LOW HSTK; lia)).
    apply A02; [apply acl_stack; exact Hx|]. unfold NEW_W, ERRNO_A. cbn [outside]. unfold STACK_WIN, RT_STACK in *; clear - Hx R4 NUM LOW HSTK EHI; lia. }
  assert (CLE6 : cl_env m6 lb canary) by (apply (cl_env_seg _ m5 m6 lb canary CLE5 MU6); cl_fp_lia).
  destruct (cl_chain_call (rt_cg RT Σ) e_ERR_new e_CRYPTO_free SITE_new_free2 m m6 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGH _ ltac:(right; left; reflexivity)) (proj2 CGH _ ltac:(right; right; left; reflexivity)) UWC AG06
              ltac:(fold usp; replace (usp - 16) with (usp + -48 + Z.of_nat (cells_size [C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m6 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR6))
              ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX6 & UWC6).
  rewrite <- CG1 in CTX6.
  (* [comment removed for export] *)
  apply (C_FRN Σ1 PMc (Z_to_bv 64 SITE_new_free2) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) y0 y1 y2 sp (Z_to_bv 64 (E + (top + 1) mod 16 * 8 + 768)) (Z_to_bv 64 0)
           i1 i2 i3 i4 i5 i6 i7 (Z_to_bv 64 ((E + (top + 1) mod 16 * 8 + 768) ≫ 3 + 2147450880)) (Z_to_bv 64 (E + (top + 1) mod 16 * 8))
           (Z_to_bv 64 ((E + (top + 1) mod 16 * 8 + 576) ≫ 3 + 2147450880)) s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 F5 fc5 m6 lo (bv_unsigned ra :: outer) lb canary FDO MST eq_refl eq_refl ART6 MI6).
  { fold usp in SPA. unfold call_ok. rewrite EU1, SP1. split; [exact ST6|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as (q & Hq). exists (q - 3). lia. }
  { rewrite (unsigned_lit SITE_new_free2) by (unfold SITE_new_free2; lia). exact CTX6. }
  { exact UWC6. }
  { rewrite CG1. apply (proj2 CGH). right; right; right; left; reflexivity. }
  { exact CLE6. }
  { exact Hc6'. }
  clear Hc6'. intros c7 (v' & Hc7).
  destruct (ASTA_unpack RT Σ1 _ _ c7 Hc7) as (ms7 & (m7 & RS7 & (ART7 & MI7 & WM7 & ST7) & PRES7 & CLE7) & Hc7'). clear Hc7.
  destruct RS7 as (z0 & z1 & z2 & j1 & j2 & j3 & j4 & j5 & j6 & j7 & z3 & z4 & z5 & z6 & F7 & fc7 & ->).
  rewrite EU1 in ST7, PRES7. rewrite (ret_pc_even SITE_new_free2) in Hc7' by (unfold SITE_new_free2; lia).
  assert (B7 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> m7 x = m2 x).
  { intros x Hx HnE. rewrite (PRES7 x ltac:(rewrite LV1, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia])). exact (B6 x Hx HnE). }
  assert (ES7 : es_rep m7 E ((top + 1) mod 16) bot' fl' mk' buf' fs ls' fn).
  { apply (es_rep_agree m6 m7 _ _ _ _ _ _ _ _ _ ES6); [| exact WM7]. intros x Hx. cbv beta in Hx. apply PRES7. apply (acl_live _ _ _ E 904); [exact INE2 | lia]. }
  assert (FR7 : rw_cells asegs m7 (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m6 m7 _ _ FR6); [| exact WM7]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply PRES7. left. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  destruct (af_client_consts RT AF Σ1 m7 ART7) as (_ & _ & _ & _ & UT7).
  pose proof (proj2 (af_acc_live RT AF Σ1 m7 E 904 ART7 INE2)) as ACCE7.
  (* [comment removed for export] *)
  pose proof (new_s4_walk sp gp z0 z1 z2 v' j1 j2 j3 j4 j5 j6 j7 (Z_to_bv 64 (E + (top + 1) mod 16 * 8))
                (Z_to_bv 64 ((E + (top + 1) mod 16 * 8 + 576) ≫ 3 + 2147450880)) s6 s7 s8 s9 s10 s11 z3 z4 z5 z6 ra s0 s1 s2 s3 s4 s5 F7 fc7 m7 lo E ((top + 1) mod 16) bot' fl' mk' buf' fs ls' fn
                ST7 ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) UT7 FR7 ES7 FN0 ACCE7 EAL EHI ltac:(lia) MI7) as W4.
  fold usp usp1 in W4.
  cl_lift W4 Hc7' c8 Hc8.
  destruct (ASTA_unpack RT Σ1 _ _ c8 Hc8) as (ms8 & (q0 & q1 & q2 & r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & q3 & q4 & q5 & q6 & m8 & -> & MU8 & WM8 & MI8 & ST8 & ES8) & Hc8'). clear Hc8.
  fold usp in ST8.
  assert (ART8 : ART RT Σ1 m8).
  { apply (af_frame RT AF Σ1 m7 m8 usp1 ART7 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM8].
    intros x Hx. apply MU8. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ E 904); [exact INE2 | lia]. }
  assert (B8 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (E <= bv_unsigned x < E + 904) -> m8 x = m2 x).
  { intros x Hx HnE. rewrite (MU8 x ltac:(cbn [outside]; clear - HnE; lia)). exact (B7 x Hx HnE). }
  apply Hk. exists Σ1, e1, r0, bot', fl', mk', buf', ls'.
  split; [| split; [exact LV1 | split; [exact FRS1 | split; [exact SP1 | split; [exact CR1 | exact CG1]]]]].
  eapply ASTA_conseq; [exact Hc8'|]. intros ms <-. exists m8.
  split; [exists q0, q1, q2, r1, r2, r3, r4, r5, r6, r7, q3, q4, q5, q6, F7, fc7; reflexivity|].
  assert (WM28 : wmono asegs m2 m8).
  { exact (wmono_trans asegs _ _ _ WM3 (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5 (wmono_trans asegs _ _ _ WM6 (wmono_trans asegs _ _ _ WM7 WM8))))). }
  split; [split; [exact ART8 | split; [exact MI8 | split; [exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM28)) | exact ST8]]]|].
  split.
  { intros x Hx Ho. rewrite (B8 x Hx ltac:(unfold NEW_W in Ho; cbn [outside] in Ho; clear - Ho; lia)). exact (A02 x Hx Ho). }
  split; [| split; [exact ES8 | apply (cl_env_seg _ m7 m8 lb canary CLE7 MU8); cl_fp_lia]].
  apply (err_env_agree m2 m8 _ _ _ _ _ _ _ _ _ _ _ (conj ICS2 (conj ERC2 CH2))); [| exact WM28].
  intros a' n H x Hx. cbv beta in Hx. destruct (ENVR a' n _ H Hx) as (Q1 & Q2 & _). exact (B8 x Q1 Q2).
Qed.
End CNew.
