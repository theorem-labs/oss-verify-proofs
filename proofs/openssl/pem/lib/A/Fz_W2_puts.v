(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_W1_defs Fz_W1_misc Fz_W1_write0 Fz_W1_writec Fz_W1_puts Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition e_BIO_puts : Z := 0x237be4.
Definition SITE_bp_smalloc : Z := 0x237c58.     (* [comment removed for export] *)
Definition SITE_bp_spilled : Z := 0x237c8c.     (* [comment removed for export] *)
Definition SITE_bp_puts : Z := 0x237dd4.        (* [comment removed for export] *)
Definition SITE_bp_release : Z := 0x237f34.     (* [comment removed for export] *)
Definition BP_MAGIC : Z := 0x41b58ab3.
Definition BP_RETIRED : Z := 0x45e0360e.
Definition BP_DESCR : Z := 0x36207.
(* [comment removed for export] *)
Definition bp_shadow : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))].
(* [comment removed for export] *)
Definition bp_frame (c0 c8 c16 : cell) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [c0; c8; c16; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition bp_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (BI STR : Z) (F : bvmap 5 word) (fc : bv 32)
    (lo pd : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1' a2' : word) (j8 j16 : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_bp_smalloc) (Z_to_bv 64 (bv_unsigned sp + -128 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -128 - pd))
                 (Z_to_bv 64 64) a1' a2' a3 a4 a5 a6 a7 s2 (Z_to_bv 64 STR) (Z_to_bv 64 BI) s5 s6 s7 s8 (Z_to_bv 64 0x7fff8000) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (e_stack_malloc 0)) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -128) (bp_frame (C8 (Z_to_bv 64 0)) (CB 8 j8) (CB 8 j16) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ stk asegs m' (bv_unsigned sp + -128 - pd) (bv_unsigned sp + -128)
    /\ stk asegs m' lo (bv_unsigned sp + -128 - pd).

Lemma bp_s0_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo pd BI STR : Z),
  (pd = 0 \/ pd = 16) -> bv_unsigned sp mod 32 = pd -> 0 <= BI < 2^64 -> 0 <= STR < 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)] -> mem_inv asegs m ->
  evt asegs (bp_s0_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 BI STR F fc lo pd m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BI) (Z_to_bv 64 STR) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_BIO_puts) fc None m (seg_rom asegs)).
Proof.
  intros until STR. intros HP HPM HBI HSTR ST HLO HLOS SPH UT SHC UAR MI. unfold e_BIO_puts, g_shadow_memory_dynamic_address, g_detect_stack_use_after_return in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 128, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 128, SP)]) by ut_fp_lia.
  th_frame 128%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  zstep. zstep; lfix. do 13 zstep. zstep.
  zstep.
  rewrite (land_m32_pad (SP + -128) pd) by (first [lia | replace (SP + -128) with (SP + (-4) * 32) by lia; rewrite Z.mod_add by lia; exact HPM]).
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
zstep. if_false. zstep. zstep.
destruct (stk_split asegs _ lo (SP + -128 - pd) (SP + -128) ST ltac:(lia)) as [ST1 GAP].
subst SP. rewrite ?Z_to_bv_bv_unsigned.
unfold bp_s0_post, SITE_bp_smalloc, e_stack_malloc, bp_frame. apply evt_done. do 5 eexists. split; [reflexivity|].
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption|]. split; [exact GAP| exact ST1].
Qed.

(* [comment removed for export] *)
Definition bp_ftail (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition bp_s1a_post (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) (BI STR : Z) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (f lo pd : Z) (fj sj : list byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_bp_smalloc) (Z_to_bv 64 (bv_unsigned sp + -128 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -128 - pd))
                 (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 STR) (Z_to_bv 64 BI) s5 s6 s7 (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_bp_spilled) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp - 104)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -128) (CB 24 j :: bp_ftail s11' s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0)
    /\ stk asegs m' (bv_unsigned sp + -128 - pd) (bv_unsigned sp + -128)
    /\ stk asegs m' lo (bv_unsigned sp + -128 - pd)
    /\ rw_cells asegs m' f [CB 56 fj] /\ rw_cells asegs m' (f / 8 + 2147450880) [CB 8 sj].

Lemma bp_s1a_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (c0 : word) (F : bvmap 5 word) fc (m : mem) (f lo pd BI STR : Z) (j8 j16 fj sj : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 144 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -128) (bp_frame (C8 c0) (CB 8 j8) (CB 8 j16) s11' s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  stk asegs m (bv_unsigned sp + -128 - pd) (bv_unsigned sp + -128) -> stk asegs m lo (bv_unsigned sp + -128 - pd) ->
  rw_cells asegs m f [CB 56 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 8 sj] -> mem_inv asegs m ->
  evt asegs (bp_s1a_post sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s10 s11 t3 t4 t5 t6 BI STR F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' f lo pd fj sj m)
    (MS (mkR (Z_to_bv 64 SITE_bp_smalloc) (Z_to_bv 64 (bv_unsigned sp + -128 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -128 - pd))
             (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 STR) (Z_to_bv 64 BI) s5 s6 s7 s8 (Z_to_bv 64 0x7fff8000) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bp_smalloc) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros HP F0 FIMG FLO FSH HLO HLOS SPH FR GAP ST FB SB MI. unfold SITE_bp_smalloc, bp_frame in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(SP - 128, SP - 104)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 8 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. zstep. if_true.
  destruct HP as [-> | ->].
  1: replace (SP + -128 - 0) with (SP + -128) in * by lia.
  2: replace (SP + -128 - 16) with (SP + -144) in * by lia.
  all: zstep.
  all: pose proof (rw_cells_blur _ _ [_; _; _] _ FR) as FRB; cbn [cells_size csize Nat.add app cells_bytes cbytes] in FRB.
  all: subst SP.
  all: unfold bp_s1a_post, SITE_bp_spilled, bp_ftail.
  all: try replace (bv_unsigned sp + -128 - 0) with (bv_unsigned sp + -128) by lia.
  all: try replace (bv_unsigned sp + -128 - 16) with (bv_unsigned sp + -144) by lia.
  all: apply evt_done; do 2 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact FRB|]; split; [eassumption|]; split; [eassumption|]; split; assumption.
Qed.

(* [comment removed for export] *)
Definition bp_s1b_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (BI STR : Z) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (f lo pd : Z) (j : list byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists (hj tj : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_bp_puts) (Z_to_bv 64 (bv_unsigned sp + -128 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -128 - pd))
                 (Z_to_bv 64 BI) (Z_to_bv 64 STR) (Z_to_bv 64 e_mem_puts) a3 a4 a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 STR) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) t3 t4 t5 t6)
            F (Z_to_bv 64 e_mem_puts) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 BP_MAGIC); C8 (Z_to_bv 64 BP_DESCR); C8 (Z_to_bv 64 e_BIO_puts); CB 8 hj; C8 (Z_to_bv 64 0); CB 16 tj]
    /\ rw_cells asegs m' (f / 8 + 2147450880) bp_shadow
    /\ rw_cells asegs m' (bv_unsigned sp + -128) (CB 24 j :: bp_ftail s11' s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0)
    /\ stk asegs m' (bv_unsigned sp + -128 - pd) (bv_unsigned sp + -128)
    /\ stk asegs m' lo (bv_unsigned sp + -128 - pd).

Lemma bp_s1b_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s10 s11 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) fc (m : mem) (f lo pd BI STR meth fl : Z) (shw rrw numw padw ptrw : word)
    (j fj sj : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 144 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -128) (CB 24 j :: bp_ftail s11' s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  stk asegs m (bv_unsigned sp + -128 - pd) (bv_unsigned sp + -128) -> stk asegs m lo (bv_unsigned sp + -128 - pd) ->
  rw_cells asegs m f [CB 56 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 8 sj] ->
  (meth = MEM_METHOD \/ meth = SECMEM_METHOD) -> rw_cells asegs m BI (bio_head meth) -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) shw fl rrw numw padw ptrw) ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo -> (BI + 128 <= f \/ f + 64 <= BI) ->
  ro_cells asegs m ((meth + 48) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] -> 0 <= STR < 2^64 ->
  mem_inv asegs m ->
  evt asegs (bp_s1b_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 BI STR F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' f lo pd j m)
    (MS (mkR (Z_to_bv 64 SITE_bp_smalloc) (Z_to_bv 64 (bv_unsigned sp + -128 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -128 - pd))
             (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 STR) (Z_to_bv 64 BI) s5 s6 s7 (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bp_spilled) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros HP F0 F64 FIMG FLO FSH HLO HLOS SPH UT FR GAP ST FB SB HM BH BW ACCBI BI0 BIAL BIHI BILO PFB MSB HSTR MI.
  unfold SITE_bp_spilled, bio_head, bio_w1_cells, bp_ftail in *.
  destruct HM as [-> | ->]; unfold MEM_METHOD, SECMEM_METHOD in *.
  all: lazymatch type of MSB with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in MSB end.
  all: pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  all: remember (bv_unsigned sp) as SP eqn:ESP.
  all: pose proof (munch_refl [(f, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  all: assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000)
    by (pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)); assert (f / 8 + 8 <= 2^44) by (Z.div_mod_to_equations; lia); lia).
  all: assert (HWU : ut_fp [(f, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)]) by (clear - F0 FIMG SHR HLO HLOS SPH FLO; ut_fp_lia).
  all: assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  all: assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia).
  all: pose proof (div8_facts f) as Q1.
  all: apply (rw_cells_split_CB asegs _ f [] 56 fj [] [8; 8; 8; 8; 8; 16]%nat) in FB; [| reflexivity]; cbn [mk_CB_cells app] in FB.
  (* [comment removed for export] *)
  all: do 3 zstep; zstep; rewrite (shr3_div f) by lia; do 3 zstep.
  all: do 3 (zstep; lfix).
  all: zstep; zstep; do 4 (zstep; lfix).
  all: zstep; do 4 (zstep; lfix).
  all: zstep; lfix.
  (* [comment removed for export] *)
  all: zstep; if_cases Kb; zify_cond Kb; try (exfalso; rewrite ?unsigned_lit in Kb by lia; lia); try clear Kb.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (ACC1 : acc asegs mX BI 128)
      by (apply (acc_agree m mX _ _ ACCBI ltac:(lia)); apply (agree_of_munch _ m mX _ MU); intros x Hx; cbv beta in Hx; unfold shad, SHB in Hx; cbn [outside];
          clear - Hx PFB FSH BIHI SPH BILO HLO Q1 F0 HLOS BIAL8; Z.div_mod_to_equations; lia) end.
  all: zstep; zstep; zstep; zstep.
  all: cbv beta; zstep; th_if_lit.
  all: zstep; zstep; th_if_lit.
  all: do 4 zstep; cbv beta; zstep; th_if_lit.
  all: zstep; zstep; th_if_lit.
  all: do 4 zstep; cbv beta; zstep; th_if_lit.
  all: zstep; zstep; th_if_lit.
  all: do 4 zstep; cbv beta; zstep; th_if_lit.
  all: zstep; zstep; th_if_lit.
  (* [comment removed for export] *)
  all: do 4 zstep; zstep; th_if_lit.
  all: zstep; zstep; th_if_lit.
  all: zstep; cbv beta; zstep; th_if_lit.
  all: zstep.        (* [comment removed for export] *)
  all: do 4 zstep; cbv beta; zstep; th_if_lit.
  all: zstep; zstep; zstep; zstep; zstep.
  all: subst SP.
  all: unfold bp_s1b_post, SITE_bp_puts, e_mem_puts, BP_MAGIC, BP_DESCR, e_BIO_puts, bp_shadow; apply evt_done; do 3 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; assumption.
Qed.

(* [comment removed for export] *)
Definition bp_s2_post (sp gp tp : word) (BI STR n : Z) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (f lo pd : Z) (j : list byte) (nr nw : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -128 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -128 - pd))
                 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 n) a7
                 (Z_to_bv 64 f) (Z_to_bv 64 STR) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_bp_release) fc None m' (seg_rom asegs)
    /\ munch [(BI + 104, BI + 112); (f, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (BI + 72) (bio_tail nr (Z_to_bv 64 (bv_unsigned nw + n)))
    /\ rw_cells asegs m' (bv_unsigned sp + -128) (CB 24 j :: bp_ftail s11' s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0)
    /\ stk asegs m' (bv_unsigned sp + -128 - pd) (bv_unsigned sp + -128)
    /\ stk asegs m' lo (bv_unsigned sp + -128 - pd).

Lemma bp_s2_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) fc (m : mem) (f lo pd BI STR meth n : Z) (nr nw wr : word)
    (j : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 144 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -128) (CB 24 j :: bp_ftail s11' s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  stk asegs m (bv_unsigned sp + -128 - pd) (bv_unsigned sp + -128) -> stk asegs m lo (bv_unsigned sp + -128 - pd) ->
  rw_cells asegs m f [C8 (Z_to_bv 64 BP_MAGIC)] -> rw_cells asegs m (f + 32) [C8 wr] -> rw_cells asegs m (f / 8 + 2147450880) bp_shadow ->
  rw_cells asegs m BI (bio_head meth) -> rw_cells asegs m (BI + 72) (bio_tail nr nw) ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo -> (BI + 128 <= f \/ f + 64 <= BI) ->
  0 <= n < 2^31 -> 0 <= STR < 2^64 ->
  mem_inv asegs m ->
  evt asegs (bp_s2_post sp gp tp BI STR n F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' f lo pd j nr nw m)
    (MS (mkR (Z_to_bv 64 SITE_bp_puts) (Z_to_bv 64 (bv_unsigned sp + -128 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -128 - pd))
             (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 f) (Z_to_bv 64 STR) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
             (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bp_puts) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HP F0 F64 FIMG FLO FSH HLO HLOS SPH FR GAP ST HDR WRC SB BH BT ACCBI BI0 BIAL BIHI BILO PFB HN HSTR MI.
  unfold SITE_bp_puts, bio_head, bio_tail, bp_ftail, BP_MAGIC, bp_shadow in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(BI + 104, BI + 112); (f, f + 40); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 8 <= 0x10007fff8000)
    by (pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)); assert (f / 8 + 8 <= 2^44) by (Z.div_mod_to_equations; lia); lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia).
  pose proof (div8_facts f) as Q1.
  pose proof (bv_unsigned_in_range 64 nw) as RNW; unfold bv_modulus in RNW; cbn [Z.of_N] in RNW.
  (* [comment removed for export] *)
  zstep. zstep. if_cases Kn; zify_cond Kn.
  { (* [comment removed for export] *)
    assert (N0 : n = 0) by (apply Bool.andb_false_iff in Kn; destruct Kn as [Kn|Kn]; apply Z.ltb_ge in Kn; clear - Kn HN; lia). clear Kn. subst n.
    zstep. cbv beta. zstep. th_if_lit.
    zstep. zstep. th_if_lit.
    do 4 zstep. cbv beta. zstep. th_if_lit.
    zstep. zstep. th_if_lit.
    zstep. zstep. th_if_lit.
    zstep. zstep; lfix. zstep. zstep. zstep; lfix.
    zstep. if_cases KF; zify_cond KF; [exfalso; lia|].
    zstep. do 8 (zstep; lfix).
    subst SP.
    unfold bp_s2_post, SITE_bp_release. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply evt_done. do 16 eexists. split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption. }
  (* [comment removed for export] *)
  rename Kn0 into N1. clear Kn1.
  do 4 zstep. cbv beta. zstep. th_if_lit.
  zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (ACC1 : acc asegs mX BI 128)
      by (apply (acc_agree m mX _ _ ACCBI ltac:(lia)); apply (agree_of_munch _ m mX _ MU); intros x Hx; cbv beta in Hx; unfold shad, SHB in Hx; cbn [outside];
          clear - Hx PFB FSH BIHI SPH BILO HLO Q1 F0 HLOS BIAL8; Z.div_mod_to_equations; lia) end.
  (* [comment removed for export] *)
  zstep. cbv beta. zstep. th_if_lit.
  zstep. zstep. th_if_lit.
  do 4 zstep. cbv beta. zstep. th_if_lit.
  zstep. zstep. th_if_lit.
  zstep. zstep. th_if_lit.
  zstep. zstep. zstep. if_cases K31; zify_cond K31.
  2: { exfalso. revert K31. rewrite ?unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. clear - HN N1. intros K31. apply K31. rewrite Z.div_small; lia. }
  (* [comment removed for export] *)
  zstep. zstep; lfix. zstep. zstep. zstep; lfix.
  zstep. if_cases KF; zify_cond KF; [exfalso; lia|].
  zstep. do 8 (zstep; lfix).
  subst SP.
  unfold bp_s2_post, SITE_bp_release. apply evt_done. do 16 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition bp_s3_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (n : Z) (F : bvmap 5 word) (fc : bv 32)
    (fl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)].

Lemma bp_s3_walk : forall ra1 ra0 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6
    (s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' : word) (F : bvmap 5 word) fc (m : mem) (f fl lo pd n : Z) (j : list byte),
  (pd = 0 \/ pd = 16) -> lo <= bv_unsigned sp - 144 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0 < f -> f + 64 <= lo -> 0 < fl -> fl + 1 <= lo -> 0 <= n < 2^31 ->
  stk asegs m lo (bv_unsigned sp + -128 - pd) -> stk asegs m (bv_unsigned sp + -128 - pd) (bv_unsigned sp + -128) ->
  rw_cells asegs m (bv_unsigned sp + -128) (CB 24 j :: bp_ftail s11' s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  ro_cells asegs m (f + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (bp_s3_post ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' n F fc fl lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -128 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -128 - pd))
             a0 a1 a2 a3 a4 a5 (Z_to_bv 64 n) a7 (Z_to_bv 64 f) s3 s4 s5 s6 s7 (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bp_release) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HP HLO HLOS SPH F0 FLO FL0 FLLO HN ST1 GAP FR FLG FLB MI. unfold SITE_bp_release, bp_ftail in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU; pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUfl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  zstep. clear FLG.
  zstep; lfix.
  zstep. zstep. zstep.
  do 13 zstep.
  pose proof (stk_merge asegs _ lo (SP + -128 - pd) (SP + -128) ST1 GAP ltac:(lia)) as ST2.
  zstep. release_frame FR ST2 SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  rewrite Z.add_0_r, (swrap32_small n) by lia.
  unfold bp_s3_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.

Section CBputs.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM0 : stack_malloc_contract RT 0.
(* [comment removed for export] *)
Hypothesis GO_memmeth : GOBJ M_MEM_A 112.
Hypothesis GO_secmeth : GOBJ M_SECMEM_A 112.

Lemma meth_bputs_sh : forall (Σ : rts RT) (m : mem) meth, ART RT Σ m -> (meth = M_MEM_A \/ meth = M_SECMEM_A) ->
  ro_cells asegs m ((meth + 48) / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
  intros Σ m meth HA [-> | ->].
  - pose proof (afp_gsh_byte RT GOBJ AFP Σ m _ _ (M_MEM_A + 48) HA GO_memmeth ltac:(unfold M_MEM_A; lia) ltac:(unfold M_MEM_A; lia) ltac:(reflexivity)) as X.
    cbn [Z.ltb Z.sub Z.add Z.leb M_MEM_A] in X. exact X.
  - pose proof (afp_gsh_byte RT GOBJ AFP Σ m _ _ (M_SECMEM_A + 48) HA GO_secmeth ltac:(unfold M_SECMEM_A; lia) ltac:(unfold M_SECMEM_A; lia) ltac:(reflexivity)) as X.
    cbn [Z.ltb Z.sub Z.add Z.leb M_SECMEM_A] in X. exact X.
Qed.

(* [comment removed for export] *)
Lemma frame_apart : forall (Σ1 : rts RT) (m1 : mem) Fr k fr usp a,
  ART RT Σ1 m1 -> rt_frames RT Σ1 = (Fr, k) :: fr -> rt_sp0 RT Σ1 - STACK_WIN <= usp -> aclient (rt_live RT Σ1) fr usp a ->
  ~ (Fr <= a < Fr + fs_size k) /\ ~ (shad Fr <= a < shad (Fr + fs_size k)).
Proof.
  intros Σ1 m1 Fr k fr usp a ART1 FRS LU Ha.
  assert (INF : In (Fr, k) (rt_frames RT Σ1)) by (rewrite FRS; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m1 Fr k ART1 INF) as (R0 & R1 & R2 & R3).
  pose proof (af_fshadow_apart RT AF Σ1 m1 Fr k ART1 INF) as (SL & SF).
  pose proof (af_sp0_range RT AF Σ1 m1 ART1) as SPR. pose proof (af_sp0_win RT AF Σ1 m1 ART1) as SPW.
  assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (SH1 : shad (Fr + fs_size k) <= 2^44 + SHB).
  { unfold shad. assert ((Fr + fs_size k) / 8 <= 2^44) by (apply Z.div_le_upper_bound; unfold USTACK_TOP, STACK_WIN in *; lia). lia. }
  assert (SH0 : SHB <= shad Fr) by (unfold shad; assert (0 <= Fr / 8) by (apply Z.div_pos; lia); lia).
  assert (SHM : shad Fr <= shad (Fr + fs_size k)) by (unfold shad; pose proof (Z.div_le_mono Fr (Fr + fs_size k) 8 ltac:(lia) ltac:(lia)); lia).
  destruct Ha as [H|[H|[H|[H|H]]]].
  - split; unfold SHB, USTACK_TOP, STACK_WIN in *; lia.
  - pose proof (client_static_range a H). split; [destruct R2; unfold SEGTOP_A in *; lia|]. unfold SHB, SEGTOP_A in *. lia.
  - destruct H as (p & n & Hin & Hp). destruct (R3 p n Hin); destruct (SL p n Hin); split; lia.
  - destruct H as (f & k' & Hin & Hf).
    destruct (af_frames_disj RT AF Σ1 m1 Fr k f k' [] fr ART1 FRS Hin) as [D|D]; (destruct (SF f k' ltac:(rewrite FRS; right; exact Hin)) as [E|E]); split; lia.
  - destruct H as (f & k' & Hin & Hf).
    assert (INf : In (f, k') (rt_frames RT Σ1)) by (rewrite FRS; right; exact Hin).
    pose proof (af_fshadow_apart RT AF Σ1 m1 f k' ART1 INf) as (_ & SF').
    destruct (af_frames_disj RT AF Σ1 m1 Fr k f k' [] fr ART1 FRS Hin) as [D|D].
    + pose proof (Z.div_le_mono (Fr + fs_size k) f 8 ltac:(lia) D). destruct (SF' Fr k INF) as [E|E]; split; unfold shad in *; lia.
    + assert (FSZ' : 0 <= fs_size k') by (unfold fs_size; apply Z.shiftl_nonneg; lia).
      pose proof (Z.div_le_mono (f + fs_size k') Fr 8 ltac:(lia) D). destruct (SF' Fr k INF) as [E|E]; split; unfold shad in *; lia.
Qed.

(* [comment removed for export] *)
Lemma acl_keep : forall (live1 live2 : list (Z * Z)) fr sp (FP : list (Z * Z)) a,
  (forall p k, In (p, k) live1 -> In (p, k) live2 \/ (forall x, p <= x < p + k -> ~ outside FP x)) ->
  aclient live1 fr sp a -> outside FP a -> aclient live2 fr sp a.
Proof.
  intros live1 live2 fr sp FP a LVK [H|[H|[H|[H|H]]]] Ho.
  - left; exact H. - right; left; exact H.
  - destruct H as (p & k & Hin & Ha). destruct (LVK p k Hin) as [X|X]; [right; right; left; exists p, k; split; [exact X| exact Ha]| exfalso; exact (X a Ha Ho)].
  - right; right; right; left; exact H. - right; right; right; right; exact H.
Qed.

(* [comment removed for export] *)
Definition bputs_entry (sp gp tp : word) (usp1 BI STR f : Z) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  entry_st (Z_to_bv 64 SITE_bp_puts) (Z_to_bv 64 usp1) gp tp t0 t1 t2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 BI) (Z_to_bv 64 STR) (Z_to_bv 64 e_mem_puts) a3 a4 a5 a6 a7
           (Z_to_bv 64 f) (Z_to_bv 64 STR) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
           (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) t3 t4 t5 t6 F fc e_mem_puts m.
Definition bputs_ret (sp gp tp : word) (usp1 BI STR f : Z) (v : word) (m' : mem) (ms : machine_state) : Prop :=
  ret_st (Z_to_bv 64 SITE_bp_puts) (Z_to_bv 64 usp1) gp tp sp (Z_to_bv 64 usp1)
         (Z_to_bv 64 f) (Z_to_bv 64 STR) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
         (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) v m' ms.

(* [comment removed for export] *)
Definition bputs_spec (Σ : rts RT) (PMc : Model -> Prop) (sp gp tp s0 ra : word) (usp lo BI STR : Z) (m : mem)
    (FP : list (Z * Z)) (PQ : rts RT -> Z -> mem -> Prop) : Prop :=
  forall (Σ1 : rts RT) (f pd : Z) (m4 : mem) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  (pd = 0 \/ pd = 16) -> usp mod 32 = pd ->
  rt_live RT Σ1 = rt_live RT Σ -> rt_frames RT Σ1 = (f, 0%nat) :: rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ -> rt_credit RT Σ1 = rt_credit RT Σ - 1 -> rt_cg RT Σ1 = rt_cg RT Σ ->
  ART RT Σ1 m4 -> mem_inv asegs m4 -> wmono asegs m m4 -> call_ok RT Σ1 m4 (Z_to_bv 64 (usp + -128 - pd)) lo ->
  (forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> (bv_unsigned x < usp - 144 \/ usp <= bv_unsigned x) -> m4 x = m x) ->
  rw_cells asegs m4 (usp - 16) [C8 s0; C8 ra] ->
  cps asegs (ASTA RT Σ1 PMc (eq (bputs_entry sp gp tp (usp + -128 - pd) BI STR f t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m4)))
    (fun c => exists (Σ2 : rts RT) (n : Z),
       ASTA RT Σ2 PMc (fun ms => exists m5, bputs_ret sp gp tp (usp + -128 - pd) BI STR f (Z_to_bv 64 n) m5 ms
           /\ ART RT Σ2 m5 /\ mem_inv asegs m5 /\ stk asegs m5 lo (usp + -128 - pd)
           /\ (forall x : word, aclient (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -128 - pd) (bv_unsigned x) -> outside FP (bv_unsigned x) -> m5 x = m4 x)
           /\ PQ Σ2 n m5) c
       /\ rt_frames RT Σ2 = rt_frames RT Σ1 /\ rt_sp0 RT Σ2 = rt_sp0 RT Σ1 /\ 0 <= n < 2^31 /\ In (BI, 128) (rt_live RT Σ2)
       /\ (forall p k, In (p, k) (rt_live RT Σ1) -> In (p, k) (rt_live RT Σ2) \/ (forall x, p <= x < p + k -> ~ outside FP x))).

(* [comment removed for export] *)
Definition bio_puts_wrap_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI STR meth fl : Z) (shw rrw numw padw ptrw nr nw : word) (FP : list (Z * Z)) (PQ : rts RT -> Z -> mem -> Prop),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 STR ->
  (meth = M_MEM_A \/ meth = M_SECMEM_A) -> In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 ->
  rw_cells asegs m BI (bio_head meth) -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) shw fl rrw numw padw ptrw) -> rw_cells asegs m (BI + 72) (bio_tail nr nw) ->
  0 <= STR < 2^64 ->
  (forall x, ~ outside FP x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x) ->
  (forall x, BI <= x < BI + 40 \/ BI + 72 <= x < BI + 128 -> outside FP x) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 144 <= bv_unsigned sp ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  bputs_spec Σ PMc sp gp tp s0 ra (bv_unsigned sp) lo BI STR m FP PQ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_BIO_puts m)))
    (fun c => exists (Σ2 Σ3 : rts RT) (n : Z) (m5 : mem),
       ASTA RT Σ3 PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 n) m' ms
           /\ ART RT Σ3 m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ wmono asegs m5 m'
           /\ (forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned x) -> outside FP (bv_unsigned x) ->
                 ~ (BI + 104 <= bv_unsigned x < BI + 112) -> m' x = m x)
           /\ (forall x : word, aclient (rt_live RT Σ2) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned x) -> ~ (BI + 104 <= bv_unsigned x < BI + 112) -> m' x = m5 x)
           /\ rw_cells asegs m' BI (bio_head meth) /\ rw_cells asegs m' (BI + 72) (bio_tail nr (Z_to_bv 64 (bv_unsigned nw + n)))) c
       /\ PQ Σ2 n m5
       /\ rt_live RT Σ3 = rt_live RT Σ2 /\ rt_frames RT Σ3 = rt_frames RT Σ /\ rt_sp0 RT Σ3 = rt_sp0 RT Σ /\ rt_credit RT Σ3 = rt_credit RT Σ2 /\ rt_cg RT Σ3 = rt_cg RT Σ2
       /\ 0 <= n < 2^31).


Theorem bio_puts_wrap : bio_puts_wrap_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI STR meth fl shw rrw numw padw ptrw nr nw FP PQ
    FDO MST -> -> -> HM INBI BIAL BH BW BT HSTR FPOK FPBI ART0 MI0 CALL HSTK Hfr Hcr MP.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  set (pd := usp mod 32).
  assert (HP : pd = 0 \/ pd = 16) by (unfold pd; clear - SPA; Z.div_mod_to_equations; lia).
  assert (HPM : usp mod 32 = pd) by reflexivity. clearbody pd.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 144 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  set (usp1 := usp + -128 - pd).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO' & _). assert (BILO : BI + 128 <= lo) by (clear - BILO' LOW; lia). clear BILO'.
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI.
  (* [comment removed for export] *)
  pose proof (bp_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pd BI STR
                HP HPM ltac:(clear - BI0 BIHI BILO NUM HSTK; unfold USTACK_TOP, RT_STACK in *; lia) HSTR ST ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia) UT SHC UAR MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a1' & a2' & j8 & j16 & m1 & -> & MU1 & WM1 & MI1 & FR1 & GAP1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, GAP1, ST1, Hc1'. fold usp1 in GAP1, ST1, Hc1'. unfold bp_frame in FR1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 128 [] ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 128 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  (* [comment removed for export] *)
  apply (SM0 Σ PMc (Z_to_bv 64 SITE_bp_smalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 64) a1' a2' a3 a4 a5 a6 a7
           s2 (Z_to_bv 64 STR) (Z_to_bv 64 BI) s5 s6 s7 s8 (Z_to_bv 64 0x7fff8000) s10 s11 t3 t4 t5 t6 F fc m1 lo FDO MST ltac:(left; reflexivity) eq_refl ltac:(clear - Hfr; lia) ltac:(clear - Hcr; lia) ART1 MI1).
  { unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    fold usp in SPA. clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & F0 & F64 & FU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WF2 & WS2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_bp_smalloc) in Hc2' by (unfold SITE_bp_smalloc; lia).
  assert (INF : In (f, 0%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FLO & _ & PF).
  assert (INBI1 : In (BI, 128) (rt_live RT Σ1)) by (rewrite LV1; exact INBI).
  pose proof (PF BI 128 INBI1) as PFB. clear PF. pose proof (proj1 (af_fshadow_apart RT AF Σ1 m2 f 0%nat ART2 INF) BI 128 INBI1) as SLB.
  change (fs_size 0) with 64 in PFB, SLB.
  pose proof (af_frames_align RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FIMG).
  pose proof (af_frames_hi RT AF Σ1 m2 f 0%nat ART2 INF) as FSH.
  rewrite SP1 in FLO. change (fs_size 0) with 64 in FLO, FSH, FU, WF2, WS2. change (64 - 8) with 56 in WF2. change (64 / 8) with 8 in WS2.
  unfold shad, SHB in WS2. unfold SEGTOP_A in FIMG.
  assert (SHF : shad (f + 64) = shad f + 8) by (replace (f + 64) with (f + 64 * 1) by lia; rewrite (shad_add64 f 1 F64); lia).
  rewrite SHF in SLB. unfold shad, SHB in SLB.
  assert (AG2 : forall a n, usp1 <= a -> a + n <= USTACK_TOP -> agree_on (fun x => a <= x < a + n) m1 m2).
  { intros a n H1 H2 x Hx. cbv beta in Hx. apply PRES2. left. lia. }
  cl_keep FR1 AG2 WM2 FR2.
  assert (GAP2 : stk asegs m2 usp1 (usp + -128)).
  { apply (stk_agree_nw asegs m1 m2 _ _ GAP1). intros x Hx. cbv beta in Hx. apply PRES2. left. unfold USTACK_TOP in *. lia. }
  destruct (wr_at_rw_CB m2 f 56 WF2 ltac:(lia)) as (fj & FB2). destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 8 WS2 ltac:(lia)) as (sj & SB2).
  change (Z.to_nat 56) with 56%nat in FB2. change (Z.to_nat 8) with 8%nat in SB2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (bp_s1a_walk sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 s5 s6 s7 s8 s10 s11 u3 u4 u5 u6
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F2 fc2 m2 f lo pd BI STR j8 j16 fj sj
                HP F0 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia) ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                FR2 GAP2 ST2 FB2 SB2 MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (j0 & m3 & -> & MU3 & WM3 & MI3 & FR3 & GAP3 & ST3 & FB3 & SB3) & Hc3'). clear Hc3.
  fold usp in MU3, FR3, GAP3, Hc3'. fold usp1 in GAP3, ST3, Hc3'.
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 (usp - 144) ART2 ltac:(rewrite SP1; lia)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply acl_stack. unfold USTACK_TOP in *. lia. }
  destruct (af_client_consts RT AF Σ1 m3 ART3) as (_ & _ & _ & _ & UT3).

  (* [comment removed for export] *)
  assert (A03 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> (bv_unsigned x < usp - 144 \/ usp <= bv_unsigned x) -> m3 x = m x).
  { intros x Hx Hlt.
    rewrite (MU3 x ltac:(cbn [outside]; clear - Hlt; lia)).
    rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; lia])).
    apply MU1. cbn [outside]. clear - Hlt. lia. }
  assert (AGB3 : forall a k, BI <= a -> a + k <= BI + 128 -> agree_on (fun x => a <= x < a + k) m m3).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply A03; [apply (acl_live _ _ _ BI 128); [exact INBI | lia] | left; clear - Hx H2 BILO HSTK; unfold RT_STACK in *; lia]. }
  assert (WM03 : wmono asegs m m3) by exact (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)).
  assert (BH3 : rw_cells asegs m3 BI (bio_head meth)) by (apply (rw_cells_agree asegs m m3 _ _ BH); [apply AGB3; unfold bio_head; cbn [cells_size csize Nat.add]; lia | exact WM03]).
  assert (BW3 : rw_cells asegs m3 (BI + 40) (bio_w1_cells (Z_to_bv 64 1) shw fl rrw numw padw ptrw))
    by (apply (rw_cells_agree asegs m m3 _ _ BW); [apply AGB3; unfold bio_w1_cells; cbn [cells_size csize Nat.add]; lia | exact WM03]).
  assert (BT3 : rw_cells asegs m3 (BI + 72) (bio_tail nr nw)) by (apply (rw_cells_agree asegs m m3 _ _ BT); [apply AGB3; unfold bio_tail; cbn [cells_size csize Nat.add]; lia | exact WM03]).
  pose proof (proj2 (af_acc_live RT AF Σ1 m3 BI 128 ART3 INBI1)) as ACC3.
  (* [comment removed for export] *)
  pose proof (bp_s1b_walk sp gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s5 s6 s7 s10 s11 u3 u4 u5 u6
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 m3 f lo pd BI STR meth fl shw rrw numw padw ptrw j0 fj sj
                HP F0 F64 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia) ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                UT3 FR3 GAP3 ST3 FB3 SB3 HM BH3 BW3 ACC3 BI0 BIAL BIHI BILO ltac:(clear - PFB; lia) (meth_bputs_sh Σ1 m3 meth ART3 HM) HSTR MI3) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc3' c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (hj & tj & m4 & -> & MU4 & WM4 & MI4 & HDR4 & SB4 & FR4 & GAP4 & ST4) & Hc4'). clear Hc4.
  fold usp in MU4, HDR4, FR4, GAP4, Hc4'. fold usp1 in GAP4, ST4, Hc4'.
  assert (ART4 : ART RT Σ1 m4).
  { apply (af_frame RT AF Σ1 m3 m4 usp1 ART3 ltac:(rewrite SP1; unfold usp1; lia)); [| exact WM4].
    intros a Ha. apply MU4. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia].
    - apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia]. }
  (* [comment removed for export] *)
  assert (A04 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> (bv_unsigned x < usp - 144 \/ usp <= bv_unsigned x) -> m4 x = m x).
  { intros x Hx Hlt.
    destruct (newframe_apart RT AF Σ Σ1 m2 f 0%nat usp _ ART2 FRS1 LV1 SP1 ltac:(lia) Hx) as (N1 & N2).
    change (fs_size 0) with 64 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    rewrite (MU4 x ltac:(cbn [outside]; clear - N1 N2; lia)). exact (A03 x Hx Hlt). }
  assert (WM04 : wmono asegs m m4) by exact (wmono_trans asegs _ _ _ WM03 WM4).
  assert (FRR4 : rw_cells asegs m4 (usp - 16) [C8 s0; C8 ra]).
  { unfold bp_ftail in FR4. pose proof (rw_cells_skip m4 (usp + -128) [CB 24 j0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] _ FR4) as X.
    cbn [cells_size csize Nat.add app] in X. replace (usp + -128 + Z.of_nat 112) with (usp - 16) in X by lia. exact X. }
  (* [comment removed for export] *)
  apply (MP Σ1 f pd m4 u0 u1 u2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 HP HPM LV1 FRS1 SP1 CR1 CG1 ART4 MI4 WM04).
  { fold usp in SPA. unfold call_ok. fold usp1. rewrite EU1, SP1. split; [exact ST4|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; lia|]. split; [unfold USTACK_TOP in *; lia|].
    clear - SPA HP HPM. Z.div_mod_to_equations. lia. }
  { exact A04. }
  { exact FRR4. }
  { exact Hc4'. }
  clear Hc4'. intros c5 (Σ2 & n & Hc5 & FRS2 & SP2 & HN & INBI2 & LVK).
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (m5 & RS5 & ART5 & MI5 & ST5 & PRES5 & HPQ) & Hc5'). clear Hc5.
  destruct RS5 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F5 & fc5 & ->).
  rewrite (ret_pc_even SITE_bp_puts) in Hc5' by (unfold SITE_bp_puts; lia).

  assert (INF2 : In (f, 0%nat) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF).
  pose proof (af_frames_range RT AF Σ2 m5 f 0%nat ART5 INF2) as (_ & _ & _ & PF2).
  pose proof (PF2 BI 128 INBI2) as PFB2. pose proof (proj1 (af_fshadow_apart RT AF Σ2 m5 f 0%nat ART5 INF2) BI 128 INBI2) as SLB2.
  change (fs_size 0) with 64 in PFB2, SLB2. rewrite SHF in SLB2. unfold shad, SHB in SLB2.
  (* [comment removed for export] *)
  assert (NFP : forall x, (usp - 144 <= x < usp) \/ (f <= x < f + 64) \/ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 8) -> outside FP x).
  { intros x Hx. destruct (outside_dec FP x) as [H|H]; [exact H| exfalso]. pose proof (FPOK x H) as AC. fold usp in AC.
    destruct (newframe_apart RT AF Σ Σ1 m2 f 0%nat usp _ ART2 FRS1 LV1 SP1 ltac:(lia) AC) as (N1 & N2).
    change (fs_size 0) with 64 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    pose proof (cl_split RT AF Σ m usp 144 _ ART0 ltac:(lia) ltac:(lia) AC) as N3. clear - Hx N1 N2 N3. lia. }
  assert (AG5 : forall a k, (usp1 <= a /\ a + k <= usp) \/ (f <= a /\ a + k <= f + 56) \/ (f / 8 + 2147450880 <= a /\ a + k <= f / 8 + 2147450880 + 8)
                            \/ (BI <= a /\ a + k <= BI + 40) \/ (BI + 72 <= a /\ a + k <= BI + 128) ->
            agree_on (fun x => a <= x < a + k) m4 m5).
  { intros a k H x Hx. cbv beta in Hx. pose proof (div8_facts f) as Q1. destruct H as [H|[H|[H|[H|H]]]].
    - apply PRES5; [left; unfold usp1 in *; lia | apply NFP; left; unfold usp1 in *; clear - H Hx HP; lia].
    - apply PRES5; [apply (acl_frame _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; lia] | apply NFP; right; left; clear - H Hx; lia].
    - apply PRES5; [apply (acl_fshadow _ _ _ f 0%nat); [exact INF | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia] | apply NFP; right; right; clear - H Hx; lia].
    - apply PRES5; [apply (acl_live _ _ _ BI 128); [exact INBI1 | lia] | apply FPBI; left; clear - H Hx; lia].
    - apply PRES5; [apply (acl_live _ _ _ BI 128); [exact INBI1 | lia] | apply FPBI; right; clear - H Hx; lia]. }
  assert (FR5 : rw_cells asegs m5 (usp + -128) (CB 24 j0 :: bp_ftail s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree_nw asegs m4 m5 _ _ FR4). apply AG5. left. unfold bp_ftail. cbn [cells_size csize Nat.add]. unfold usp1. clear - HP. lia. }
  assert (GAP5 : stk asegs m5 usp1 (usp + -128)).
  { apply (stk_agree_nw asegs m4 m5 _ _ GAP4). intros x Hx. cbv beta in Hx. apply PRES5; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia| apply NFP; left; unfold usp1 in Hx; clear - Hx HP; lia]. }
  assert (HDR5 : rw_cells asegs m5 f [C8 (Z_to_bv 64 BP_MAGIC)]).
  { apply (rw_cells_agree_nw asegs m4 m5 _ _ (rw_cells_head m4 f _ _ HDR4)). apply AG5. right; left. cbn [cells_size csize Nat.add]. lia. }
  assert (WRC5 : rw_cells asegs m5 (f + 32) [C8 (Z_to_bv 64 0)]).
  { pose proof (rw_cells_skip m4 f [C8 (Z_to_bv 64 BP_MAGIC); C8 (Z_to_bv 64 BP_DESCR); C8 (Z_to_bv 64 e_BIO_puts); CB 8 hj] _ HDR4) as X.
    cbn [cells_size csize Nat.add app] in X. replace (f + Z.of_nat 32) with (f + 32) in X by lia.
    apply (rw_cells_agree_nw asegs m4 m5 _ _ (rw_cells_head m4 (f + 32) _ _ X)). apply AG5. right; left. cbn [cells_size csize Nat.add]. lia. }
  assert (SB5 : rw_cells asegs m5 (f / 8 + 2147450880) bp_shadow).
  { apply (rw_cells_agree_nw asegs m4 m5 _ _ SB4). apply AG5. right; right; left. cbn [bp_shadow cells_size csize Nat.add]. lia. }
  assert (AGB4 : forall a k, BI <= a -> a + k <= BI + 128 -> agree_on (fun x => a <= x < a + k) m m4).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply A04; [apply (acl_live _ _ _ BI 128); [exact INBI | lia] | left; clear - Hx H2 BILO HSTK; unfold RT_STACK in *; lia]. }
  assert (BH5 : rw_cells asegs m5 BI (bio_head meth)).
  { apply (rw_cells_agree_nw asegs m4 m5); [apply (rw_cells_agree asegs m m4 _ _ BH); [apply AGB4; unfold bio_head; cbn [cells_size csize Nat.add]; lia | exact WM04]|].
    apply AG5. do 3 right; left. unfold bio_head. cbn [cells_size csize Nat.add]. lia. }
  assert (BT5 : rw_cells asegs m5 (BI + 72) (bio_tail nr nw)).
  { apply (rw_cells_agree_nw asegs m4 m5); [apply (rw_cells_agree asegs m m4 _ _ BT); [apply AGB4; unfold bio_tail; cbn [cells_size csize Nat.add]; lia | exact WM04]|].
    apply AG5. do 4 right. unfold bio_tail. cbn [cells_size csize Nat.add]. lia. }
  pose proof (proj2 (af_acc_live RT AF Σ2 m5 BI 128 ART5 INBI2)) as ACC5.
  (* [comment removed for export] *)
  pose proof (bp_s2_walk sp gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 v3 v4 v5 v6
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F5 fc5 m5 f lo pd BI STR meth n nr nw (Z_to_bv 64 0) j0
                HP F0 F64 FIMG ltac:(lia) ltac:(destruct FSH; [left | right]; lia) ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                FR5 GAP5 ST5 HDR5 WRC5 SB5 BH5 BT5 ACC5 BI0 BIAL BIHI BILO ltac:(clear - PFB2; lia) HN HSTR MI5) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc5' c6 Hc6.
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & (ra1 & w0 & w1 & w2 & g0 & g1 & g2 & g3 & g4 & g5 & g7 & w3 & w4 & w5 & w6 & m6 & -> & MU6 & WM6 & MI6 & BT6 & FR6 & GAP6 & ST6) & Hc6'). clear Hc6.
  fold usp in MU6, FR6, GAP6, Hc6'. fold usp1 in GAP6, ST6, Hc6'.

  assert (ART6 : ART RT Σ2 m6).
  { apply (af_frame RT AF Σ2 m5 m6 usp1 ART5 ltac:(rewrite SP2, SP1; unfold usp1; lia)); [| exact WM6].
    intros a Ha. apply MU6. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
    - apply (acl_live _ _ _ BI 128); [exact INBI2 | lia].
    - apply (acl_frame _ _ _ f 0%nat); [exact INF2 | change (fs_size 0) with 64; lia].
    - apply (acl_fshadow _ _ _ f 0%nat); [exact INF2 | change (fs_size 0) with 64; rewrite SHF; unfold shad, SHB; lia]. }
  (* [comment removed for export] *)
  destruct (af_frame_release RT AF Σ2 m6 f 0%nat (rt_frames RT Σ) ART6 ltac:(rewrite FRS2; exact FRS1)) as (Σ3 & flg & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 0) with 64 in FW. replace (f + 64 - 8) with (f + 56) in FW by lia. rewrite SP2, SP1 in FLW.
  (* [comment removed for export] *)
  pose proof (bp_s3_walk ra1 ra sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 g0 g1 g2 g3 g4 g5 g7 (Z_to_bv 64 STR) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (f + 32))
                (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) w3 w4 w5 w6
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F5 fc5 m6 f flg lo pd n j0
                HP ltac:(fold usp; unfold RT_STACK in *; lia) ltac:(lia) ltac:(fold usp; unfold USTACK_TOP in *; lia)
                F0 ltac:(lia) FL0 ltac:(clear - FLW LOW; lia) ltac:(clear - HN; lia) ST6 GAP6 FR6 FW FLC MI6) as W4.
  fold usp usp1 in W4.
  cl_lift W4 Hc6' c7 Hc7.
  destruct (ASTA_unpack RT Σ2 _ _ c7 Hc7) as (ms7 & (y0 & y1 & y2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & y3 & y4 & y5 & y6 & m7 & -> & MU7 & WM7 & MI7 & ST7 & FLC7) & Hc7'). clear Hc7.
  fold usp in ST7.
  destruct (REL m7 MU7 WM7 FLC7) as (ART7 & FRS3 & LV3 & SP3 & CR3 & AL3 & AM3 & CG3).

  (* [comment removed for export] *)
  assert (NFL2 : forall x, aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp1 x -> x <> flg).
  { intros x Hx Ex. subst x. destruct Hx as [H|H]; [unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; clear - H FLW NUM HP; lia|].
    apply NAC. right. exact H. }
  assert (NFL : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> outside FP x -> x <> flg).
  { intros x Hx Ho. apply NFL2. apply (acl_keep _ _ _ _ FP x LVK); [| exact Ho].
    apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV1; auto | rewrite FRS2, FRS1; intros e' He'; right; exact He' | unfold usp1; clear - HP; lia]. }
  assert (NFL5 : forall x, aclient (rt_live RT Σ2) (rt_frames RT Σ) usp x -> x <> flg).
  { intros x Hx. apply NFL2. apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | rewrite FRS2, FRS1; intros e' He'; right; exact He' | unfold usp1; clear - HP; lia]. }
  (* [comment removed for export] *)
  assert (A57 : forall x : word, aclient (rt_live RT Σ2) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (BI + 104 <= bv_unsigned x < BI + 112) -> m7 x = m5 x).
  { intros x Hx HB.
    destruct (frame_apart Σ2 m5 f 0%nat (rt_frames RT Σ) usp _ ART5 ltac:(rewrite FRS2; exact FRS1) ltac:(rewrite SP2, SP1; lia) Hx) as (N1 & N2).
    change (fs_size 0) with 64 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    rewrite (MU7 x ltac:(cbn [outside]; split; [pose proof (NFL5 _ Hx); lia | exact I])).
    apply MU6. cbn [outside]. clear - N1 N2 HB. lia. }
  apply Hk. exists Σ2, Σ3, n, m5.
  split; [| split; [exact HPQ| split; [exact LV3 | split; [exact FRS3 | split; [rewrite SP3, SP2; exact SP1 | split; [exact CR3 | split; [exact CG3| exact HN]]]]]]].
  eapply ASTA_conseq; [exact (ASTA_switch RT Σ2 Σ3 PMc _ c7 Hc7' AL3 AM3)|]. intros ms <-. exists m7.
  split; [exists y0, y1, y2, h1, h2, h3, h4, h5, h6, h7, y3, y4, y5, y6, F5, fc5; reflexivity|].
  split; [exact ART7|]. split; [exact MI7|]. split; [exact ST7|]. split; [exact (wmono_trans asegs _ _ _ WM6 WM7)|].
  split.
  { intros x Hx Ho HB.
    assert (Hx2 : aclient (rt_live RT Σ2) (rt_frames RT Σ) usp (bv_unsigned x)).
    { apply (acl_keep _ _ _ _ FP _ LVK); [| exact Ho]. rewrite LV1. exact Hx. }
    rewrite (A57 x Hx2 HB).
    rewrite (PRES5 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [rewrite LV1; auto | rewrite FRS1; intros e' He'; right; exact He' | unfold usp1; clear - HP; lia]) Ho).
    apply A04; [exact Hx|]. destruct (cl_split RT AF Σ m usp 144 _ ART0 ltac:(lia) ltac:(lia) Hx) as [Hi|Lo]; [right; exact Hi | left; exact Lo]. }
  split; [exact A57|].
  split.
  { apply (rw_cells_agree_nw asegs m5 m7 _ _ BH5). intros x Hx. cbv beta in Hx. unfold bio_head in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply A57; [apply (acl_live _ _ _ BI 128); [exact INBI2 | clear - Hx; lia] | clear - Hx; lia]. }
  apply (rw_cells_agree_nw asegs m6 m7 _ _ BT6). intros x Hx. cbv beta in Hx. unfold bio_tail in Hx. cbn [cells_size csize Nat.add] in Hx.
  apply MU7. cbn [outside]. split; [| exact I]. pose proof (NFL5 (bv_unsigned x) ltac:(apply (acl_live _ _ _ BI 128); [exact INBI2 | clear - Hx; lia])). clear - H. lia.
Qed.

End CBputs.
