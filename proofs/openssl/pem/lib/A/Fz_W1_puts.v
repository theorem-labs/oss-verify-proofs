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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_W4_kit Fz_env Fz_M_malloc Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_new Fz_W1_sync Fz_W1_grow Fz_W1_write Fz_W1_writec Fz_W1_write0 Fz_M_secure Fz_W1_secre Fz_W1_grows Fz_W1_writes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition SITE_puts_strlen : Z := 0x304560.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition puts_frame (s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition puts_s0_post (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 s0' s1' s2' : word) (BI STR lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m',
    ms = MS (mkR (Z_to_bv 64 SITE_puts_strlen) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 STR) (Z_to_bv 64 STR) a1 a2 a3
                 a4 a5 a6 a7 (Z_to_bv 64 BI) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_strlen) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -32) (puts_frame s2' s1' s0' ra0) /\ stk asegs m' lo (bv_unsigned sp + -32).

Lemma puts_s0_walk : forall ra0 sp gp tp t0 t1 t2 s0' s1' a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI STR : Z),
  lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) ->
  0 < BI < 2^47 -> 0 <= STR < 2^47 -> mem_inv asegs m ->
  evt asegs (puts_s0_post sp gp tp t0 t1 t2 (Z_to_bv 64 STR) a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' BI STR lo m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 BI) (Z_to_bv 64 STR) a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_mem_puts) fc None m (seg_rom asegs)).
Proof.
  intros until STR. intros HLO HLOS SPH ST BI0 STR0 MI.
  unfold e_mem_puts in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 32, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  th_frame 32%nat [8; 8; 8; 8]%nat ST.
  zstep. do 4 zstep. zstep.
  zstep. zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold puts_s0_post, SITE_puts_strlen, e_strlen, puts_frame. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FR| assumption].
Qed.

(* [comment removed for export] *)
Lemma puts_s1_walk : forall ra0 sp gp tp t0 t1 t2 s0' s1' s2' a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI STR n : Z),
  lo <= bv_unsigned sp - 32 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -32) ->
  rw_cells asegs m (bv_unsigned sp + -32) (puts_frame s2' s1' s0' ra0) ->
  0 < BI < 2^47 -> 0 <= STR < 2^47 -> 0 <= n < 2^31 -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 BI) (Z_to_bv 64 STR) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 e_mem_write) fc None m (seg_rom asegs)
                    /\ stk asegs m lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 SITE_puts_strlen) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 STR) (Z_to_bv 64 n) a1 a2 a3
             a4 a5 a6 a7 (Z_to_bv 64 BI) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_puts_strlen) fc None m (seg_rom asegs)).
Proof.
  intros until n. intros HLO HLOS SPH ST FR BI0 STR0 HN MI.
  unfold SITE_puts_strlen, puts_frame in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (SP + -32)) = SP + -32) by (apply unsigned_lit; lia).
  zstep. zstep. rewrite ?(unsigned_lit n) by lia. rewrite (Z.shiftr_div_pow2 n 31) by lia. rewrite (Z.div_small n (2 ^ 31)) by lia.
  zstep. th_if_lit.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  th_release FR SP.
  zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold e_mem_write. apply evt_done. split; [reflexivity| assumption].
Qed.

Section CPuts.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SLC : strlen_icontract RT.
Hypothesis MMV : memmove_icontract RT e_asan_memmove.
Hypothesis MSI : memset_icontract RT e_asan_memset.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.
Hypothesis C_CM : crypto_malloc_env_stmt RT.
Hypothesis C_CCR : crypto_clear_realloc_env_stmt RT.

Lemma src_blk_shrink : forall live IN n n' ex, src_blk live IN n ex -> 0 <= n' <= n -> src_blk live IN n' ex.
Proof.
  intros live IN n n' ex [H | (p & k & Hin & L & H & NE)] Hn; [left; clear - H Hn; lia | right; exists p, k].
  split; [exact Hin|]. split; [exact L|]. split; [clear - H Hn; lia | exact NE].
Qed.

(* [comment removed for export] *)
Definition puts_src (live : list (Z * Z)) (m : mem) (STR : Z) (str slack : list byte) (ex : list Z) : Prop :=
  bytes_at asegs m STR (str ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) str /\ (- (STR + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack)
  /\ Z.of_nat (length str) < 2 ^ 31 /\ src_blk live STR (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) ex.

(* [comment removed for export] *)
Lemma puts_prefix : forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI STR : Z) (str slack : list byte) (ex : list Z) (Q : config -> Prop),
  fdfs_only PMc -> mat_stable PMc -> 0 < BI < 2 ^ 47 -> puts_src (rt_live RT Σ) m STR str slack ex ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 32 <= bv_unsigned sp ->
  (forall (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m2 : mem),
     ART RT Σ m2 -> mem_inv asegs m2 -> wmono asegs m m2 -> stk asegs m2 lo (bv_unsigned sp) ->
     (forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned x) -> m2 x = m x) ->
     cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 BI) (Z_to_bv 64 STR) (Z_to_bv 64 (Z.of_nat (length str))) a3' a4' a5' a6' a7'
                                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F' fc' e_mem_write m2))) Q) ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BI) (Z_to_bv 64 STR) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                          F fc e_mem_puts m))) Q.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI STR str slack ex Q
    FDO MST BIR (SB & NONUL & PAD & HLEN & SRC) ART0 MI0 CALL HSTK K.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  set (len := Z.of_nat (length str)) in *. assert (Hl0 : 0 <= len) by (unfold len; lia).
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 32 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLO1 : lo <= usp - 32) by (clear - HSTK; unfold RT_STACK in *; lia). pose proof (proj1 (proj2 NUM)) as HLOS.
  assert (SPH : usp <= 2 ^ 47) by (clear - NUM; unfold USTACK_TOP in *; lia).
  assert (LENS : Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) = len + 1 + Z.of_nat (length slack)) by (rewrite length_app; cbn [length]; unfold len; lia).
  destruct (src_facts RT AF Σ m STR (len + 1 + Z.of_nat (length slack)) ex usp lo ART0 SRC ltac:(lia) LOW HLOS) as (_ & _ & SLO & STR0 & ACLS & _ & _).
  cl_eu usp (-32) EU1.
  (* [comment removed for export] *)
  pose proof (puts_s0_walk ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI STR
                HLO1 HLOS SPH ST BIR ltac:(clear - SLO STR0 HLO1 SPH Hl0; lia) MI0) as W0.
  fold usp in W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 32 [] ART0 ltac:(lia) ltac:(lia) MU1) as PR1.
  assert (AG1 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m1 x = m x) by (intros x Hx; apply PR1; [exact Hx | exact I]).
  assert (SB1 : bytes_at asegs m1 STR (str ++ Z_to_bv 8 0 :: slack)).
  { apply (bytes_at_agree asegs m m1 _ _ SB). intros x Hx. rewrite LENS in Hx. apply MU1. cbn [outside]. split; [clear - Hx SLO HLO1; lia | exact I]. }
  (* [comment removed for export] *)
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 (usp + -32)) lo).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 2. }
  assert (CHK1 : checked_src RT Σ m1 (Z_to_bv 64 (usp + -32)) lo STR (len + 1)).
  { destruct (src_facts RT AF Σ m1 STR (len + 1) ex usp lo ART1 (src_blk_shrink _ _ _ (len + 1) _ SRC ltac:(clear - Hl0; lia)) ltac:(lia) LOW HLOS) as (AC & RC & _).
    split; [intros _; exact (conj AC RC) | left; clear - SLO; lia]. }
  apply (SLC Σ PMc (Z_to_bv 64 SITE_puts_strlen) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 STR) (Z_to_bv 64 STR) (Z_to_bv 64 STR) a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 BI) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 STR str slack lo FDO MST eq_refl SB1 NONUL ltac:(fold len; clear - HLEN; lia) PAD
           ltac:(clear - SLO STR0 HLO1 SPH; lia) ltac:(left; fold len; clear - SLO; lia) ltac:(fold len; exact CHK1) ART1 MI1 CO1).
  { exact Hc1'. }
  clear Hc1'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & _) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_puts_strlen) in Hc2' by (unfold SITE_puts_strlen; lia).
  fold len in Hc2'.
  (* [comment removed for export] *)
  assert (AG12 : forall x : word, usp - 32 <= bv_unsigned x < USTACK_TOP \/ aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> m2 x = m1 x).
  { intros x Hx. apply PRES2; [| clear; lia]. destruct Hx as [Hx | Hx]; [left; clear - Hx; lia|].
    apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | clear; lia]. }
  assert (FR2 : rw_cells asegs m2 (usp + -32) (puts_frame s2 s1 s0 ra)).
  { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold puts_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply AG12. left. unfold USTACK_TOP in *. clear - Hx NUM. lia. }
  (* [comment removed for export] *)
  pose proof (puts_s1_walk ra sp gp tp u0 u1 u2 s0 s1 s2 b1 b2 b3 b4 b5 b6 b7 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 lo BI STR len
                HLO1 HLOS SPH ST2 FR2 BIR ltac:(clear - SLO STR0 HLO1 SPH Hl0; lia) ltac:(clear - HLEN Hl0; lia) MI2) as W1.
  fold usp in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (-> & ST3) & Hc3'). clear Hc3. fold usp in ST3.
  apply (K u0 u1 u2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 m2 ART2 MI2 (wmono_trans asegs _ _ _ WM1 WM2) ST3
           ltac:(intros x Hx; rewrite (AG12 x (or_intror Hx)); exact (AG1 x Hx)) T c3 Hc3' Hk).
Qed.

(* [comment removed for export] *)
Definition puts_fit_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len max off fl STR : Z) (rrw numw padw rmaxw : word) (str slack : list byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 STR ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM (bufmem_cells len D max (Z_to_bv 64 0)) ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw (Z_to_bv 64 0)) -> BM <> R ->
  In (D, max) (rt_live RT Σ) -> D <> BI -> D <> BB -> D <> BM -> D <> R ->
  0 <= off <= len -> len <= max -> len - off + Z.of_nat (length str) <= max -> max < 2 ^ 31 -> 1 <= Z.of_nat (length str) ->
  puts_src (rt_live RT Σ) m STR str slack [BI; BM; R; D] ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 160 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_puts m)))
    (ASTA RT Σ PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Z.of_nat (length str))) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (WRF_W BI BM R D max) m m'
        /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 BB))
        /\ rw_cells asegs m' BM (bufmem_cells (len - off + Z.of_nat (length str)) D max (Z_to_bv 64 0))
        /\ rw_cells asegs m' R (readp_cells (len - off + Z.of_nat (length str)) D 0 (Z_to_bv 64 max) (Z_to_bv 64 0)))).

Theorem puts_fit_cps : puts_fit_stmt.
Proof.
  pose proof (write_fit_cps RT AF GOBJ AFP MMV MSI MCP) as C_WF.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len max off fl STR rrw numw padw rmaxw str slack
    FDO MST -> -> -> INBI BIAL BW FLOK INBB BBAL BBC INBM BMAL BMC INR RAL RC NMR IND NDBI NDBB NDBM NDR HOFF HLEN HFIT HMAX HINL PSRC ART0 MI0 CALL HSTK.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (usp := bv_unsigned sp) in *. set (inl := Z.of_nat (length str)) in *.
  assert (HLOS : 0x10007fff8000 <= lo) by (clear - LOW SP0W; unfold STACK_WIN in *; lia).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO & _).
  assert (BIR : 0 < BI < 2 ^ 47) by (clear - BI0 BILO SP0R; unfold USTACK_TOP, STACK_WIN in *; lia).
  pose proof PSRC as (SB & _ & _ & _ & SRC).
  pose proof (live_ne_apart RT AF Σ m BI 128 BB 16 ART0 INBI INBB ltac:(intros E; injection E; lia)) as APIB.
  pose proof (live_ne_apart RT AF Σ m BI 128 R 32 ART0 INBI INR ltac:(intros E; injection E; lia)) as APIR.
  pose proof (live_ne_apart RT AF Σ m BI 128 BM 32 ART0 INBI INBM ltac:(intros E; injection E; lia)) as APIM.
  destruct (src_facts RT AF Σ m STR (inl + 1 + Z.of_nat (length slack)) [BI; BM; R; D] usp lo ART0 SRC ltac:(clear; lia) LOW HLOS) as (_ & _ & _ & _ & ACLS & _ & _).
  apply (puts_prefix Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI STR str slack [BI; BM; R; D] _
           FDO MST BIR PSRC ART0 MI0 CALL ltac:(fold usp; clear - HSTK; lia)).
  intros t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m2 ART2 MI2 WM2 ST2 AG2. fold usp in ST2, AG2.
  assert (BW2 : rw_cells asegs m2 (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB))).
  { apply (rw_cells_agree asegs m m2 _ _ BW); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold bio_w1_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply AG2. apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hx; lia]. }
  assert (BBC2 : rw_cells asegs m2 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m m2 _ _ BBC); [| exact WM2]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply AG2. apply (acl_live _ _ _ BB 16); [exact INBB | clear - Hx; lia]. }
  assert (BMC2 : rw_cells asegs m2 BM (bufmem_cells len D max (Z_to_bv 64 0))).
  { apply (rw_cells_agree asegs m m2 _ _ BMC); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold bufmem_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply AG2. apply (acl_live _ _ _ BM 32); [exact INBM | clear - Hx; lia]. }
  assert (RC2 : rw_cells asegs m2 R (readp_cells len D off rmaxw (Z_to_bv 64 0))).
  { apply (rw_cells_agree asegs m m2 _ _ RC); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold readp_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply AG2. apply (acl_live _ _ _ R 32); [exact INR | clear - Hx; lia]. }
  assert (SB2 : bytes_at asegs m2 STR str).
  { apply (bytes_at_agree asegs m m2 _ _ (proj1 (proj1 (bytes_at_app asegs m STR str (Z_to_bv 8 0 :: slack)) SB))). intros x Hx. cbv beta in Hx.
    apply AG2. replace (bv_unsigned x) with (STR + (bv_unsigned x - STR)) by (clear; lia). apply ACLS. clear - Hx. lia. }
  assert (CALL2 : call_ok RT Σ m2 sp lo) by exact (conj ST2 (conj LOW (conj LOR (conj SPT SPA)))).
  eapply cps_conseq; [apply (C_WF Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0' t1' t2' s0 s1 (Z_to_bv 64 BI) (Z_to_bv 64 STR) (Z_to_bv 64 inl) a3' a4' a5' a6' a7'
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m2 lo BI BB BM R D len max off fl STR inl rrw numw padw rmaxw str
                                  FDO MST eq_refl eq_refl eq_refl eq_refl INBI BIAL BW2 FLOK INBB BBAL BBC2 INBM BMAL BMC2 INR RAL RC2 NMR IND NDBI NDBB NDBM NDR
                                  HOFF HLEN HFIT HMAX HINL SB2 eq_refl (src_blk_shrink _ _ _ inl _ SRC ltac:(clear; lia)) ART2 MI2 CALL2 HSTK)
                     | intros c X; exact X |].
  cbv beta. intros c Hc. eapply ASTA_conseq; [exact Hc|]. cbv beta. intros ms (m' & RS & (ART' & MI' & WM' & ST') & PRES' & BW' & BMC' & RC').
  exists m'. split; [exact RS|]. split; [exact (conj ART' (conj MI' (conj (wmono_trans asegs _ _ _ WM2 WM') ST')))|].
  split; [| exact (conj BW' (conj BMC' RC'))].
  intros x Hx Ho. rewrite (PRES' x Hx Ho). exact (AG2 x Hx).
Qed.

(* [comment removed for export] *)
Definition puts_re_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len max off fl STR : Z) (rrw numw padw rmaxw : word) (str slack : list byte) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 STR ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM (bufmem_cells len D max (Z_to_bv 64 0)) ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw (Z_to_bv 64 0)) -> BM <> R ->
  wdata_opt (rt_live RT Σ) BI BB BM R D len max off ->
  0 <= off <= len -> len <= max -> max < len - off + Z.of_nat (length str) -> gr_n (len - off + Z.of_nat (length str)) <= 0x8000000 -> 1 <= Z.of_nat (length str) ->
  puts_src (rt_live RT Σ) m STR str slack [BI; BM; R; D] ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x100 + 224 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_mem_write (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) WR_SITES WR_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost (gr_n (len - off + Z.of_nat (length str))) <= rt_credit RT Σ -> cl_env m lb canary ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_puts m)))
    (fun c => exists (Σ' : rts RT) (q : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Z.of_nat (length str))) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres_fp (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) (WRG_W BI BM R) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 BB))
           /\ rw_cells asegs m' BM (bufmem_cells (len - off + Z.of_nat (length str)) q (gr_n (len - off + Z.of_nat (length str))) (Z_to_bv 64 0))
           /\ rw_cells asegs m' R (readp_cells (len - off + Z.of_nat (length str)) q 0 (Z_to_bv 64 (gr_n (len - off + Z.of_nat (length str)))) (Z_to_bv 64 0))) c
       /\ rt_live RT Σ' = (q, gr_n (len - off + Z.of_nat (length str))) :: live_remove D (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (gr_n (len - off + Z.of_nat (length str))) /\ 0 < q /\ q mod 16 = 0
       /\ q + gr_n (len - off + Z.of_nat (length str)) < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem puts_re_cps : puts_re_stmt.
Proof.
  pose proof (write_re_cps RT AF GOBJ AFP MMV MSI MCP C_CM C_CCR) as C_WR.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len max off fl STR rrw numw padw rmaxw str slack
    outer lb canary
    FDO MST -> -> -> INBI BIAL BW FLOK INBB BBAL BBC INBM BMAL BMC INR RAL RC NMR DOPT HOFF HLEN HGR HN4 HINL PSRC ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr CLE.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (usp := bv_unsigned sp) in *. set (inl := Z.of_nat (length str)) in *.
  assert (HLOS : 0x10007fff8000 <= lo) by (clear - LOW SP0W; unfold STACK_WIN in *; lia).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO & _).
  assert (BIR : 0 < BI < 2 ^ 47) by (clear - BI0 BILO SP0R; unfold USTACK_TOP, STACK_WIN in *; lia).
  pose proof PSRC as (SB & _ & _ & _ & SRC).
  destruct (src_facts RT AF Σ m STR (inl + 1 + Z.of_nat (length slack)) [BI; BM; R; D] usp lo ART0 SRC ltac:(clear; lia) LOW HLOS) as (_ & _ & _ & _ & ACLS & _ & _).
  apply (puts_prefix Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI STR str slack [BI; BM; R; D] _
           FDO MST BIR PSRC ART0 MI0 CALL ltac:(fold usp; clear - HSTK; lia)).
  intros t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m2 ART2 MI2 WM2 ST2 AG2. fold usp in ST2, AG2.
  assert (BW2 : rw_cells asegs m2 (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB))).
  { apply (rw_cells_agree asegs m m2 _ _ BW); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold bio_w1_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply AG2. apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hx; lia]. }
  assert (BBC2 : rw_cells asegs m2 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m m2 _ _ BBC); [| exact WM2]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply AG2. apply (acl_live _ _ _ BB 16); [exact INBB | clear - Hx; lia]. }
  assert (BMC2 : rw_cells asegs m2 BM (bufmem_cells len D max (Z_to_bv 64 0))).
  { apply (rw_cells_agree asegs m m2 _ _ BMC); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold bufmem_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply AG2. apply (acl_live _ _ _ BM 32); [exact INBM | clear - Hx; lia]. }
  assert (RC2 : rw_cells asegs m2 R (readp_cells len D off rmaxw (Z_to_bv 64 0))).
  { apply (rw_cells_agree asegs m m2 _ _ RC); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold readp_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply AG2. apply (acl_live _ _ _ R 32); [exact INR | clear - Hx; lia]. }
  assert (SB2 : bytes_at asegs m2 STR str).
  { apply (bytes_at_agree asegs m m2 _ _ (proj1 (proj1 (bytes_at_app asegs m STR str (Z_to_bv 8 0 :: slack)) SB))). intros x Hx. cbv beta in Hx.
    apply AG2. replace (bv_unsigned x) with (STR + (bv_unsigned x - STR)) by (clear; lia). apply ACLS. clear - Hx. lia. }
  assert (CALL2 : call_ok RT Σ m2 sp lo) by exact (conj ST2 (conj LOW (conj LOR (conj SPT SPA)))).
  assert (UWC2 : uw_chain m2 sp s0 outer).
  { apply (uw_chain_agree outer m m2 sp s0 UWC). intros x Hx. apply AG2. left. exact Hx. }
  assert (CLE2 : cl_env m2 lb canary).
  { apply (cl_env_agree m m2 lb canary CLE). intros x Hx. apply AG2. right; left. exact (cl_cell_static _ Hx). }
  eapply cps_conseq; [apply (C_WR Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0' t1' t2' s0 s1 (Z_to_bv 64 BI) (Z_to_bv 64 STR) (Z_to_bv 64 inl) a3' a4' a5' a6' a7'
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m2 lo BI BB BM R D len max off fl STR inl rrw numw padw rmaxw str outer lb canary
                                  FDO MST eq_refl eq_refl eq_refl eq_refl INBI BIAL BW2 FLOK INBB BBAL BBC2 INBM BMAL BMC2 INR RAL RC2 NMR DOPT
                                  HOFF HLEN HGR HN4 HINL SB2 eq_refl (src_blk_shrink _ _ _ inl _ SRC ltac:(clear; lia)) ART2 MI2 CALL2 HSTK CTX UWC2 CGH Hlen Hcr CLE2)
                     | intros c X; exact X |].
  cbv beta. intros c (Σ' & q & Hc & REST). exists Σ', q. split; [| exact REST].
  eapply ASTA_conseq; [exact Hc|]. cbv beta. intros ms (m' & RS & RAF & PRES' & ENV' & BW' & BMC' & RC').
  exists m'. split; [exact RS|]. split; [exact RAF|]. split; [| exact (conj ENV' (conj BW' (conj BMC' RC')))].
  intros x Hx Ho. rewrite (PRES' x Hx Ho). apply AG2. apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; exact (live_remove_sub _ _ _ He) | auto | clear; lia].
Qed.

(* [comment removed for export] *)
Definition puts_zero_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB fl STR : Z) (rrw numw padw : word) (slack : list byte) (ex : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 STR ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  puts_src (rt_live RT Σ) m STR [] slack ex ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 32 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_puts m)))
    (ASTA RT Σ PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (WRZ_W BI) m m'
        /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 BB)))).

Theorem puts_zero_cps : puts_zero_stmt.
Proof.
  pose proof (write_zero_cps RT AF GOBJ AFP) as C_WZ.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB fl STR rrw numw padw slack ex
    FDO MST -> -> -> INBI BIAL BW FLOK PSRC ART0 MI0 CALL HSTK.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (usp := bv_unsigned sp) in *.
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO & _).
  assert (BIR : 0 < BI < 2 ^ 47) by (clear - BI0 BILO SP0R; unfold USTACK_TOP, STACK_WIN in *; lia).
  apply (puts_prefix Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI STR [] slack ex _
           FDO MST BIR PSRC ART0 MI0 CALL HSTK).
  intros t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m2 ART2 MI2 WM2 ST2 AG2. fold usp in ST2, AG2. cbn [length Z.of_nat].
  assert (BW2 : rw_cells asegs m2 (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB))).
  { apply (rw_cells_agree asegs m m2 _ _ BW); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold bio_w1_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply AG2. apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hx; lia]. }
  assert (CALL2 : call_ok RT Σ m2 sp lo) by exact (conj ST2 (conj LOW (conj LOR (conj SPT SPA)))).
  eapply cps_conseq; [apply (C_WZ Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0' t1' t2' s0 s1 (Z_to_bv 64 BI) (Z_to_bv 64 STR) (Z_to_bv 64 0) a3' a4' a5' a6' a7'
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m2 lo BI BB fl rrw numw padw
                                  FDO MST eq_refl eq_refl eq_refl INBI BIAL BW2 FLOK ART2 MI2 CALL2)
                     | intros c X; exact X |].
  cbv beta. intros c Hc. eapply ASTA_conseq; [exact Hc|]. cbv beta. intros ms (m' & RS & (ART' & MI' & WM' & ST') & PRES' & BW').
  exists m'. split; [exact RS|]. split; [exact (conj ART' (conj MI' (conj (wmono_trans asegs _ _ _ WM2 WM') ST')))|].
  split; [| exact BW'].
  intros x Hx Ho. rewrite (PRES' x Hx Ho). exact (AG2 x Hx).
Qed.
End CPuts.

Section CPutsS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SLC : strlen_icontract RT.
Hypothesis MMV : memmove_icontract RT e_asan_memmove.
Hypothesis MSI : memset_icontract RT e_asan_memset.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.
Hypothesis C_SM : crypto_secure_malloc_env_stmt RT.
Hypothesis C_SCF : crypto_secure_clear_free_env_stmt RT.

(* [comment removed for export] *)
Definition puts_fitw_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len max off fl STR : Z) (rrw numw padw rmaxw flw : word) (str slack : list byte),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 STR ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM (bufmem_cells len D max flw) ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw flw) -> BM <> R ->
  In (D, max) (rt_live RT Σ) -> D <> BI -> D <> BB -> D <> BM -> D <> R ->
  0 <= off <= len -> len <= max -> len - off + Z.of_nat (length str) <= max -> max < 2 ^ 31 -> 1 <= Z.of_nat (length str) ->
  puts_src (rt_live RT Σ) m STR str slack [BI; BM; R; D] ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 160 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_puts m)))
    (ASTA RT Σ PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Z.of_nat (length str))) m' ms
        /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (WRF_W BI BM R D max) m m'
        /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 BB))
        /\ rw_cells asegs m' BM (bufmem_cells (len - off + Z.of_nat (length str)) D max flw)
        /\ rw_cells asegs m' R (readp_cells (len - off + Z.of_nat (length str)) D 0 (Z_to_bv 64 max) flw))).

Theorem puts_fitw_cps : puts_fitw_stmt.
Proof.
  pose proof (write_fitw_cps RT AF GOBJ AFP MMV MSI MCP) as C_WF.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len max off fl STR rrw numw padw rmaxw flw str slack
    FDO MST -> -> -> INBI BIAL BW FLOK INBB BBAL BBC INBM BMAL BMC INR RAL RC NMR IND NDBI NDBB NDBM NDR HOFF HLEN HFIT HMAX HINL PSRC ART0 MI0 CALL HSTK.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (usp := bv_unsigned sp) in *. set (inl := Z.of_nat (length str)) in *.
  assert (HLOS : 0x10007fff8000 <= lo) by (clear - LOW SP0W; unfold STACK_WIN in *; lia).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO & _).
  assert (BIR : 0 < BI < 2 ^ 47) by (clear - BI0 BILO SP0R; unfold USTACK_TOP, STACK_WIN in *; lia).
  pose proof PSRC as (SB & _ & _ & _ & SRC).
  pose proof (live_ne_apart RT AF Σ m BI 128 BB 16 ART0 INBI INBB ltac:(intros E; injection E; lia)) as APIB.
  pose proof (live_ne_apart RT AF Σ m BI 128 R 32 ART0 INBI INR ltac:(intros E; injection E; lia)) as APIR.
  pose proof (live_ne_apart RT AF Σ m BI 128 BM 32 ART0 INBI INBM ltac:(intros E; injection E; lia)) as APIM.
  destruct (src_facts RT AF Σ m STR (inl + 1 + Z.of_nat (length slack)) [BI; BM; R; D] usp lo ART0 SRC ltac:(clear; lia) LOW HLOS) as (_ & _ & _ & _ & ACLS & _ & _).
  apply (puts_prefix RT AF SLC Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI STR str slack [BI; BM; R; D] _
           FDO MST BIR PSRC ART0 MI0 CALL ltac:(fold usp; clear - HSTK; lia)).
  intros t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m2 ART2 MI2 WM2 ST2 AG2. fold usp in ST2, AG2.
  assert (BW2 : rw_cells asegs m2 (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB))).
  { apply (rw_cells_agree asegs m m2 _ _ BW); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold bio_w1_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply AG2. apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hx; lia]. }
  assert (BBC2 : rw_cells asegs m2 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m m2 _ _ BBC); [| exact WM2]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply AG2. apply (acl_live _ _ _ BB 16); [exact INBB | clear - Hx; lia]. }
  assert (BMC2 : rw_cells asegs m2 BM (bufmem_cells len D max flw)).
  { apply (rw_cells_agree asegs m m2 _ _ BMC); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold bufmem_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply AG2. apply (acl_live _ _ _ BM 32); [exact INBM | clear - Hx; lia]. }
  assert (RC2 : rw_cells asegs m2 R (readp_cells len D off rmaxw flw)).
  { apply (rw_cells_agree asegs m m2 _ _ RC); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold readp_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply AG2. apply (acl_live _ _ _ R 32); [exact INR | clear - Hx; lia]. }
  assert (SB2 : bytes_at asegs m2 STR str).
  { apply (bytes_at_agree asegs m m2 _ _ (proj1 (proj1 (bytes_at_app asegs m STR str (Z_to_bv 8 0 :: slack)) SB))). intros x Hx. cbv beta in Hx.
    apply AG2. replace (bv_unsigned x) with (STR + (bv_unsigned x - STR)) by (clear; lia). apply ACLS. clear - Hx. lia. }
  assert (CALL2 : call_ok RT Σ m2 sp lo) by exact (conj ST2 (conj LOW (conj LOR (conj SPT SPA)))).
  eapply cps_conseq; [apply (C_WF Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0' t1' t2' s0 s1 (Z_to_bv 64 BI) (Z_to_bv 64 STR) (Z_to_bv 64 inl) a3' a4' a5' a6' a7'
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m2 lo BI BB BM R D len max off fl STR inl rrw numw padw rmaxw flw str
                                  FDO MST eq_refl eq_refl eq_refl eq_refl INBI BIAL BW2 FLOK INBB BBAL BBC2 INBM BMAL BMC2 INR RAL RC2 NMR IND NDBI NDBB NDBM NDR
                                  HOFF HLEN HFIT HMAX HINL SB2 eq_refl (src_blk_shrink _ _ _ inl _ SRC ltac:(clear; lia)) ART2 MI2 CALL2 HSTK)
                     | intros c X; exact X |].
  cbv beta. intros c Hc. eapply ASTA_conseq; [exact Hc|]. cbv beta. intros ms (m' & RS & (ART' & MI' & WM' & ST') & PRES' & BW' & BMC' & RC').
  exists m'. split; [exact RS|]. split; [exact (conj ART' (conj MI' (conj (wmono_trans asegs _ _ _ WM2 WM') ST')))|].
  split; [| exact (conj BW' (conj BMC' RC'))].
  intros x Hx Ho. rewrite (PRES' x Hx Ho). exact (AG2 x Hx).
Qed.

(* [comment removed for export] *)
Definition puts_res_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo BI BB BM R D len max off fl STR : Z) (rrw numw padw rmaxw : word) (str slack : list byte) (outer : list Z) (lb : byte) (canary : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 STR ->
  In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (BM, 32) (rt_live RT Σ) -> BM mod 16 = 0 -> rw_cells asegs m BM (bufmem_cells len D max (Z_to_bv 64 1)) ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw (Z_to_bv 64 1)) -> BM <> R ->
  wdata_opt (rt_live RT Σ) BI BB BM R D len max off ->
  0 <= off <= len -> len <= max -> max < len - off + Z.of_nat (length str) -> gr_n (len - off + Z.of_nat (length str)) <= 0x8000000 -> 1 <= Z.of_nat (length str) ->
  puts_src (rt_live RT Σ) m STR str slack [BI; BM; R; D] ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x100 + 224 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_mem_write (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) WRS_SITES WRS_CALLS ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost (gr_n (len - off + Z.of_nat (length str))) <= rt_credit RT Σ -> cl_env m lb canary -> sec_off m ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_mem_puts m)))
    (fun c => exists (Σ' : rts RT) (q : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Z.of_nat (length str))) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres_fp (live_remove D (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) (WRG_W BI BM R) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (fl - fl mod 16) rrw numw padw (Z_to_bv 64 BB))
           /\ rw_cells asegs m' BM (bufmem_cells (len - off + Z.of_nat (length str)) q (gr_n (len - off + Z.of_nat (length str))) (Z_to_bv 64 1))
           /\ rw_cells asegs m' R (readp_cells (len - off + Z.of_nat (length str)) q 0 (Z_to_bv 64 (gr_n (len - off + Z.of_nat (length str)))) (Z_to_bv 64 1))) c
       /\ rt_live RT Σ' = (q, gr_n (len - off + Z.of_nat (length str))) :: live_remove D (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (gr_n (len - off + Z.of_nat (length str))) /\ 0 < q /\ q mod 16 = 0
       /\ q + gr_n (len - off + Z.of_nat (length str)) < USTACK_TOP /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem puts_res_cps : puts_res_stmt.
Proof.
  pose proof (write_res_cps RT AF GOBJ AFP MMV MSI MCP C_SM C_SCF) as C_WR.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI BB BM R D len max off fl STR rrw numw padw rmaxw str slack
    outer lb canary
    FDO MST -> -> -> INBI BIAL BW FLOK INBB BBAL BBC INBM BMAL BMC INR RAL RC NMR DOPT HOFF HLEN HGR HN4 HINL PSRC ART0 MI0 CALL HSTK CTX UWC CGH Hlen Hcr CLE SEC.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA). pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (usp := bv_unsigned sp) in *. set (inl := Z.of_nat (length str)) in *.
  assert (HLOS : 0x10007fff8000 <= lo) by (clear - LOW SP0W; unfold STACK_WIN in *; lia).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BI0 & BILO & _).
  assert (BIR : 0 < BI < 2 ^ 47) by (clear - BI0 BILO SP0R; unfold USTACK_TOP, STACK_WIN in *; lia).
  pose proof PSRC as (SB & _ & _ & _ & SRC).
  destruct (src_facts RT AF Σ m STR (inl + 1 + Z.of_nat (length slack)) [BI; BM; R; D] usp lo ART0 SRC ltac:(clear; lia) LOW HLOS) as (_ & _ & _ & _ & ACLS & _ & _).
  apply (puts_prefix RT AF SLC Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI STR str slack [BI; BM; R; D] _
           FDO MST BIR PSRC ART0 MI0 CALL ltac:(fold usp; clear - HSTK; lia)).
  intros t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m2 ART2 MI2 WM2 ST2 AG2. fold usp in ST2, AG2.
  assert (BW2 : rw_cells asegs m2 (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB))).
  { apply (rw_cells_agree asegs m m2 _ _ BW); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold bio_w1_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply AG2. apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hx; lia]. }
  assert (BBC2 : rw_cells asegs m2 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)]).
  { apply (rw_cells_agree asegs m m2 _ _ BBC); [| exact WM2]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply AG2. apply (acl_live _ _ _ BB 16); [exact INBB | clear - Hx; lia]. }
  assert (BMC2 : rw_cells asegs m2 BM (bufmem_cells len D max (Z_to_bv 64 1))).
  { apply (rw_cells_agree asegs m m2 _ _ BMC); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold bufmem_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply AG2. apply (acl_live _ _ _ BM 32); [exact INBM | clear - Hx; lia]. }
  assert (RC2 : rw_cells asegs m2 R (readp_cells len D off rmaxw (Z_to_bv 64 1))).
  { apply (rw_cells_agree asegs m m2 _ _ RC); [| exact WM2]. intros x Hx. cbv beta in Hx. unfold readp_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply AG2. apply (acl_live _ _ _ R 32); [exact INR | clear - Hx; lia]. }
  assert (SB2 : bytes_at asegs m2 STR str).
  { apply (bytes_at_agree asegs m m2 _ _ (proj1 (proj1 (bytes_at_app asegs m STR str (Z_to_bv 8 0 :: slack)) SB))). intros x Hx. cbv beta in Hx.
    apply AG2. replace (bv_unsigned x) with (STR + (bv_unsigned x - STR)) by (clear; lia). apply ACLS. clear - Hx. lia. }
  assert (CALL2 : call_ok RT Σ m2 sp lo) by exact (conj ST2 (conj LOW (conj LOR (conj SPT SPA)))).
  assert (UWC2 : uw_chain m2 sp s0 outer).
  { apply (uw_chain_agree outer m m2 sp s0 UWC). intros x Hx. apply AG2. left. exact Hx. }
  assert (CLE2 : cl_env m2 lb canary).
  { apply (cl_env_agree m m2 lb canary CLE). intros x Hx. apply AG2. right; left. exact (cl_cell_static _ Hx). }
  assert (SEC2 : sec_off m2) by (apply (sec_off_agree m m2 SEC); intros a Ha; apply AG2; right; left; rewrite Ha; exact sec_init_static).
  eapply cps_conseq; [apply (C_WR Σ PMc ra sp gp (Z_to_bv 64 0xba3ef0) t0' t1' t2' s0 s1 (Z_to_bv 64 BI) (Z_to_bv 64 STR) (Z_to_bv 64 inl) a3' a4' a5' a6' a7'
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m2 lo BI BB BM R D len max off fl STR inl rrw numw padw rmaxw str outer lb canary
                                  FDO MST eq_refl eq_refl eq_refl eq_refl INBI BIAL BW2 FLOK INBB BBAL BBC2 INBM BMAL BMC2 INR RAL RC2 NMR DOPT
                                  HOFF HLEN HGR HN4 HINL SB2 eq_refl (src_blk_shrink _ _ _ inl _ SRC ltac:(clear; lia)) ART2 MI2 CALL2 HSTK CTX UWC2 CGH Hlen Hcr CLE2 SEC2)
                     | intros c X; exact X |].
  cbv beta. intros c (Σ' & q & Hc & REST). exists Σ', q. split; [| exact REST].
  eapply ASTA_conseq; [exact Hc|]. cbv beta. intros ms (m' & RS & RAF & PRES' & ENV' & BW' & BMC' & RC').
  exists m'. split; [exact RS|]. split; [exact RAF|]. split; [| exact (conj ENV' (conj BW' (conj BMC' RC')))].
  intros x Hx Ho. rewrite (PRES' x Hx Ho). apply AG2. apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; exact (live_remove_sub _ _ _ He) | auto | clear; lia].
Qed.
End CPutsS.
