(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_T_ekit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_env Th_mutex Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_T_lock Fz_W1_defs Fz_W1_new Fz_W3_iface Fz_W5_rep Fz_W2_exdl Fz_W2_exd Fz_W2_exdc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation wz := (Z_to_bv 64) (only parsing).

Definition e_BIO_new_ex : Z := 0x236798.
Definition SITE_bnx_zalloc : Z := 0x2367e4.
Definition SITE_bnx_newex : Z := 0x236868.
Definition SITE_bnx_create : Z := 0x236890.
Definition BNX_FILE : Z := 0x718c0.            (* [comment removed for export] *)
(* [comment removed for export] *)
Definition mcreate (meth : Z) : Z := if meth =? M_SECMEM_A then e_secmem_new else e_mem_new.

(* [comment removed for export] *)
Definition bnx_cells (libctx meth : word) (shw refw : word) : list cell :=
  [C8 libctx; C8 meth; C8 z64; C8 z64; C8 z64] ++ [C4 z64; C4 shw; C4 z64; C4 z64; C4 z64; C4 z64; C8 z64]
  ++ [C8 z64; C8 z64; C4 refw; C4 z64; C8 z64; C8 z64] ++ [C8 z64; C8 z64].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bnw_w_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem),
       ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_BIO_new_ex) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FZ_BIO_NEW) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST GLO LO SPH MI. unfold FZ_BIO_NEW, e_BIO_new_ex in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  th_frame 16%nat [8; 8]%nat ST.
  zstep. zstep. zstep. zstep.
  zstep. zstep.
  zstep. zstep. zstep. th_release FR (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bne_s0_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (meth lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> 0 <= meth < 2 ^ 64 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (j : list byte) (m' : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_bnx_zalloc) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp s1
                 (Z_to_bv 64 128) (Z_to_bv 64 BNX_FILE) (Z_to_bv 64 83) a3 a4 a5 a6 a7 (Z_to_bv 64 meth) (Z_to_bv 64 0) (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_CRYPTO_zalloc) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ stk asegs m' lo (bv_unsigned sp + -64))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 meth) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_BIO_new_ex) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HLOS SPH HM UT SHC MI. unfold e_BIO_new_ex, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 64, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 64, SP)]) by ut_fp_lia.
  th_frame 64%nat [8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  (* [comment removed for export] *)
  zstep. do 7 zstep. zstep. zstep.
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold SITE_bnx_zalloc, BNX_FILE, e_CRYPTO_zalloc.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bne_s1_walk : forall sp1 gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (meth BI lo : Z),
  0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 < 2 ^ 47 -> 0 <= meth < 2 ^ 64 ->
  acc asegs m BI 128 -> rw_cells asegs m BI (bnx_cells z64 z64 z64 z64) ->
  stk asegs m lo (bv_unsigned sp1) -> 0x10007fff8000 <= lo -> bv_unsigned sp1 <= 2^47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_bnx_newex) sp1 gp tp t0 t1 t2 s0 (Z_to_bv 64 BI)
                 (Z_to_bv 64 12) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 112)) a3 a4 a5 a6 a7 (Z_to_bv 64 meth) (Z_to_bv 64 (BI + 112)) (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_new_ex_data) fc None m' (seg_rom asegs)
       /\ munch [(BI, BI + 128)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' BI (bnx_cells z64 (Z_to_bv 64 meth) (Z_to_bv 64 1) (Z_to_bv 64 1))
       /\ stk asegs m' lo (bv_unsigned sp1))
    (MS (mkR (Z_to_bv 64 SITE_bnx_zalloc) sp1 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BI) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 meth) (Z_to_bv 64 0) (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bnx_zalloc) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros BI0 BIAL BIHI BITOP HM ACC BC ST HLOS SPH MI. unfold SITE_bnx_zalloc in *. unfold bnx_cells in BC. cbn [app] in BC.
  pose proof (bv_unsigned_in_range 64 sp1) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  pose proof (munch_refl [(BI, BI + 128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWS : sh_fp [(BI, BI + 128)]) by (clear - BIHI; sh_fp_lia).
  assert (EUB : bv_unsigned (Z_to_bv 64 BI) = BI) by (apply unsigned_lit; lia).
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  zstep. if_cases KB; zify_cond KB. { exfalso. rewrite ?unsigned_lit in KB by lia. clear - KB BI0. lia. }
  zstep.
  zstep. zstep. zstep. zstep. if_false.
  zstep; lfix.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. if_false.
  zstep; lfix.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. if_false.
  zstep. zstep. zstep; lfix.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. if_false.
  zstep. zstep; lfix. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.
  unfold SITE_bnx_newex, e_new_ex_data, bnx_cells. cbn [app].
  apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption| assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bne_s2_walk : forall sp1 gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (meth BI : Z),
  (meth = M_MEM_A \/ meth = M_SECMEM_A) -> 0 <= BI < 2 ^ 64 ->
  img_untouched m -> ro_cells asegs m ((meth + 72) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] -> mem_inv asegs m ->
  evt asegs (fun ms =>
       ms = MS (mkR (Z_to_bv 64 SITE_bnx_create) sp1 gp tp t0 t1 t2 s0 (Z_to_bv 64 BI)
                 (Z_to_bv 64 BI) (Z_to_bv 64 (mcreate meth)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (meth + 72)) (Z_to_bv 64 (BI + 112)) (Z_to_bv 64 0x7fff8000)
                 (Z_to_bv 64 ((meth + 72) / 8 + 2147450880)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 (mcreate meth)) fc None m (seg_rom asegs))
    (MS (mkR (Z_to_bv 64 SITE_bnx_newex) sp1 gp tp t0 t1 t2 s0 (Z_to_bv 64 BI)
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 meth) (Z_to_bv 64 (BI + 112)) (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bnx_newex) fc None m (seg_rom asegs)).
Proof.
  intros until BI. intros HM HBI UT MSB MI. unfold SITE_bnx_newex, mcreate in *.
  destruct HM as [-> | ->]; unfold M_MEM_A, M_SECMEM_A in *; cbn [Z.eqb Pos.eqb].
  all: lazymatch type of MSB with ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in MSB end.
  all: pose proof (munch_refl ([] : list (Z * Z)) m) as MU; pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  all: zstep; if_false.
  all: zstep; zstep; zstep; zstep; zstep; if_false.
  all: zstep; zstep; if_false.
  all: zstep; zstep.
  all: unfold SITE_bnx_create, e_mem_new, e_secmem_new.
  1: replace ((5538432 + 72) / 8 + 2147450880) with 2148143193 by reflexivity; replace (5538432 + 72) with 5538504 by reflexivity.
  2: replace ((5538592 + 72) / 8 + 2147450880) with 2148143213 by reflexivity; replace (5538592 + 72) with 5538664 by reflexivity.
  all: apply evt_done; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bne_s3_walk : forall ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (e0 e1 e2 e3 e4 e5 : word) (F : bvmap 5 word) fc (m : mem)
    (meth BI lo : Z) (j : list byte),
  (meth = M_MEM_A \/ meth = M_SECMEM_A) -> 0 <= BI < 2 ^ 64 -> lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m ((meth + 72) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m (bv_unsigned sp + -64) [CB 8 j; C8 e5; C8 e4; C8 e3; C8 e2; C8 e1; C8 e0; C8 ra0] -> stk asegs m lo (bv_unsigned sp + -64) -> mem_inv asegs m ->
  evt asegs (fun ms =>
       ms = MS (mkR ra0 sp gp tp t0 t1 t2 e0 e1 (Z_to_bv 64 BI) a1 a2 a3 a4 a5 a6 a7 e2 e3 e4 e5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra0) fc None m (seg_rom asegs)
       /\ stk asegs m lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 SITE_bnx_create) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp (Z_to_bv 64 BI)
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (meth + 72)) (Z_to_bv 64 (BI + 112)) (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 ((meth + 72) / 8 + 2147450880)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bnx_create) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HM HBI HLO HLOS SPH UT MSB FR ST MI. unfold SITE_bnx_create in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  destruct HM as [-> | ->]; unfold M_MEM_A, M_SECMEM_A in *.
  1: replace ((5538432 + 72) / 8 + 2147450880) with 2148143193 in * by reflexivity; replace (5538432 + 72) with 5538504 in * by reflexivity.
  2: replace ((5538592 + 72) / 8 + 2147450880) with 2148143213 in * by reflexivity; replace (5538592 + 72) with 5538664 in * by reflexivity.
  all: pose proof (munch_refl ([] : list (Z * Z)) m) as MU; pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  all: zstep; if_false.
  all: zstep; zstep; if_false.
  all: zstep; zstep; if_true.
  all: zstep. all: do 7 zstep.
  all: zstep; release_frame FR ST SP; zstep.
  all: subst SP; rewrite ?Z_to_bv_bv_unsigned.
  all: apply evt_done; split; [reflexivity | exact ST].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition exd_iface (libenv : mem -> list (Z * Z) -> Z -> Prop) (libenv_fp : list (Z * Z) -> Z -> Prop) : Prop :=
  forall (m : mem) LBL E, libenv m LBL E -> exists kd LK,
       exd_stat m kd LK /\ In (LK, 40) LBL /\ rw_cells asegs m LK (mutex_cells z64 z64)
    /\ forall m' : mem, (forall x : word, libenv_fp LBL (bv_unsigned x) -> ~ (LK <= bv_unsigned x < LK + 40) -> m' x = m x) ->
         rw_cells asegs m' LK (mutex_cells z64 z64) -> libenv m' LBL E.

(* [comment removed for export] *)
Lemma live4_nodup : forall RT (AF : art_facts RT) (Σ : rts RT) (m : mem) R B bb BI L,
  ART RT Σ m -> rt_live RT Σ = (R, 32) :: (B, 32) :: (bb, 16) :: (BI, 128) :: L -> List.NoDup [BI; bb; B; R].
Proof.
  intros RT AF Σ m R B bb BI L HA EQ.
  pose proof (af_live_disj RT AF Σ m R 32 B 32 [] ((B, 32) :: (bb, 16) :: (BI, 128) :: L) HA EQ ltac:(left; reflexivity)) as D1.
  pose proof (af_live_disj RT AF Σ m R 32 bb 16 [] ((B, 32) :: (bb, 16) :: (BI, 128) :: L) HA EQ ltac:(right; left; reflexivity)) as D2.
  pose proof (af_live_disj RT AF Σ m R 32 BI 128 [] ((B, 32) :: (bb, 16) :: (BI, 128) :: L) HA EQ ltac:(right; right; left; reflexivity)) as D3.
  pose proof (af_live_disj RT AF Σ m B 32 bb 16 [(R, 32)] ((bb, 16) :: (BI, 128) :: L) HA EQ ltac:(right; left; reflexivity)) as D4.
  pose proof (af_live_disj RT AF Σ m B 32 BI 128 [(R, 32)] ((bb, 16) :: (BI, 128) :: L) HA EQ ltac:(right; right; left; reflexivity)) as D5.
  pose proof (af_live_disj RT AF Σ m bb 16 BI 128 [(R, 32); (B, 32)] ((BI, 128) :: L) HA EQ ltac:(right; right; left; reflexivity)) as D6.
  apply List.NoDup_cons; [cbn; intros [H|[H|[H|[]]]]; lia|]. apply List.NoDup_cons; [cbn; intros [H|[H|[]]]; lia|].
  apply List.NoDup_cons; [cbn; intros [H|[]]; lia|]. apply List.NoDup_cons; [cbn; intros []|]. apply List.NoDup_nil.
Qed.

(* [comment removed for export] *)
Lemma outside_appD : forall (W1 W2 : list (Z * Z)) x, outside (W1 ++ W2) x -> outside W1 x /\ outside W2 x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x H; cbn in *; [split; [exact I | exact H]|]. destruct H as [H1 H2]. destruct (IH _ _ H2) as [A B]. repeat split; assumption. Qed.
Lemma outside_mapD : forall (L : list (Z * Z)) e x, outside (map (fun e => (fst e, fst e + snd e)) L) x -> In e L -> ~ (fst e <= x < fst e + snd e).
Proof. induction L as [|e0 L IH]; intros e x H Hin; [destruct Hin|]. cbn in H. destruct H as [H1 H2]. destruct Hin as [<- | Hin]; [exact H1 | exact (IH _ _ H2 Hin)]. Qed.

Section CBnew.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_CZ : crypto_zalloc_env_stmt RT.
Hypothesis C_NEWEX : T_newex_stmt RT.
Hypothesis C_MNEW : mem_init_at_stmt RT e_mem_new (fun _ => Z_to_bv 64 0) (fun Σ ra => In (bv_unsigned ra, e_mem_init) (cg_call (rt_cg RT Σ))).
Hypothesis C_SNEW : mem_init_at_stmt RT e_secmem_new (fun _ => Z_to_bv 64 1) (fun Σ ra => In (bv_unsigned ra, e_mem_init) (cg_call (rt_cg RT Σ))).
(* [comment removed for export] *)
Hypothesis GO_memmeth : GOBJ M_MEM_A 112.
Hypothesis GO_secmeth : GOBJ M_SECMEM_A 112.
(* [comment removed for export] *)
Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
Variable libenv_fp : list (Z * Z) -> Z -> Prop.
Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
Hypothesis LEXD : exd_iface libenv libenv_fp.
(* [comment removed for export] *)
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Definition BNX_SITES : list (Z * Z) :=
  [(SITE_bnx_zalloc, FZ_BIO_NEW); (SITE_bnx_newex, FZ_BIO_NEW); (SITE_bnx_create, FZ_BIO_NEW)]
  ++ [(SITE_cz_malloc, e_CRYPTO_zalloc); (SITE_cm_malloc, e_CRYPTO_malloc)] ++ NX_SITES ++ MI_SITES.
Definition BNX_CALLS : list (Z * Z) :=
  [(SITE_bnx_zalloc, e_CRYPTO_zalloc); (SITE_bnx_newex, e_new_ex_data); (SITE_bnx_create, e_mem_new); (SITE_bnx_create, e_secmem_new); (SITE_bnx_create, e_mem_init)]
  ++ [(SITE_cz_malloc, e_CRYPTO_malloc); (SITE_cm_malloc, e_malloc)] ++ NX_CALLS ++ MI_CALLS.
Hypothesis HCG : cg_sub BNX_SITES BNX_CALLS FZ_SITES FZ_CALLS.

Theorem bio_new_mem_proof : bio_new_mem_stmt RT libenv FZ_SITES FZ_CALLS.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer canary LBL E meth
    FDO MST -> -> METH ENV INCL ART0 MI0 CALL HSTK CLE CTX UWC CGH Hfr Hlen Hcr.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA). unfold BNEW_STACK in HSTK. unfold TP_A in *.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 624 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  assert (HLO : lo <= usp - 624) by (unfold RT_STACK in HSTK; lia).
  set (usp1 := usp + -64).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  pose proof (cg_has_of_sub _ _ _ _ _ CGH HCG) as CGB.
  assert (METHR : 0 <= meth < 2 ^ 64) by (clear - METH; destruct METH as [-> | ->]; unfold M_MEM, M_SECMEM, M_MEM_A, M_SECMEM_A; lia).
  assert (METHA : meth = M_MEM_A \/ meth = M_SECMEM_A) by exact METH.
  destruct (LEXD m LBL E ENV) as (kd & LK & EST & INLKL & LKC & LCLOSE). pose proof (INCL _ INLKL) as INLK.
  pose proof EST as (_ & _ & KD & _ & _ & _ & _ & _ & _ & LKAL & _).
  pose proof (af_live_range RT AF Σ m LK 40 ART0 INLK) as RLK. pose proof (afp_live_hi RT GOBJ AFP Σ m LK 40 ART0 INLK ltac:(lia)) as LKHI.
  assert (STA : forall a, client_static a -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ a < usp - 624).
  { intros a Ha. pose proof (client_static_range a Ha) as Ra. split; [right; left; exact Ha|]. unfold SEGTOP_A in *. clear - Ra HLOI HLO. lia. }
  (* [comment removed for export] *)
  pose proof (bnw_w_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 (Z_to_bv 64 meth) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST ltac:(clear - NUM; lia) ltac:(fold usp; clear - HLO; lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia) MI0) as WW.
  cl_lift WW HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & ST1) & Hc1'). clear Hc1. fold usp in MU1, ST1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 16 [] ART0 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  destruct (af_client_consts RT AF Σ m1 ART1) as (_ & SHC1 & _ & _ & UT1).
  (* [comment removed for export] *)
  pose proof (bne_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 meth lo
                ST1 ltac:(fold usp; clear - HLO; lia) ltac:(clear - NUM; lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia) METHR UT1 SHC1 MI1) as W0.
  cl_lift W0 Hc1' c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (j & m2 & -> & MU2 & WM2 & MI2 & FR2 & ST2) & Hc2'). clear Hc2.
  fold usp in MU2, FR2, ST2, Hc2'. fold usp1 in FR2, ST2, Hc2'.
  pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WM02.
  pose proof (cl_seg_ART RT AF Σ m1 m2 usp 64 [] ART1 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia) MU2 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM2) as ART2.
  assert (A02 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x < usp - 624 \/ usp <= bv_unsigned x -> m2 x = m x).
  { intros x Hx Hlt. rewrite (MU2 x ltac:(cbn [outside]; clear - Hlt; lia)). apply MU1. cbn [outside]. clear - Hlt. lia. }
  assert (CLE2 : cl_env m2 (Z_to_bv 8 1) canary).
  { apply (cl_env_agree m m2 _ _ CLE). intros x Hx. destruct (STA _ (cl_cell_static _ Hx)) as (Hc & Hl). exact (A02 x Hc ltac:(left; exact Hl)). }
  assert (AG02 : agree_on (fun x => usp <= x < USTACK_TOP) m m2) by (intros x Hx; cbv beta in Hx; apply A02; [apply acl_stack; exact Hx | right; clear - Hx; lia]).
  assert (SV2 : rw_cells asegs m2 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; clear; lia).
    exact (rw_cells_skip m2 usp1 [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR2). }
  destruct (cl_chain_call (rt_cg RT Σ) FZ_BIO_NEW e_CRYPTO_zalloc SITE_bnx_zalloc m m2 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGB (SITE_bnx_zalloc, FZ_BIO_NEW) ltac:(unfold BNX_SITES; cbn [app In]; left; reflexivity)) (proj2 CGB (SITE_bnx_zalloc, e_CRYPTO_zalloc) ltac:(unfold BNX_CALLS; cbn [app In]; left; reflexivity)) UWC AG02
              ltac:(fold usp; exact SV2) ltac:(rewrite EU1; fold usp; unfold usp1; clear; lia) SPT) as (CTX2 & UWC2).
  (* [comment removed for export] *)
  apply (C_CZ Σ PMc (Z_to_bv 64 SITE_bnx_zalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp s1 (Z_to_bv 64 128) (Z_to_bv 64 BNX_FILE) (Z_to_bv 64 83) a3 a4 a5 a6 a7
           (Z_to_bv 64 meth) (Z_to_bv 64 0) (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 128 lo (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary
           FDO MST eq_refl eq_refl ltac:(clear; lia) ART2 MI2).
  { fold usp in SPA. unfold call_ok. rewrite EU1. split; [exact ST2|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK; lia|].
    split; [unfold USTACK_TOP in *; clear - NUM; lia|]. clear - SPA. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_bnx_zalloc) by (unfold SITE_bnx_zalloc; clear; lia). exact CTX2. }
  { exact UWC2. }
  { apply (cg_has_weaken _ _ _ _ _ CGB); vm_compute; reflexivity. }
  { clear - Hlen. lia. }
  { change (mcost 128) with 0. clear - Hcr. lia. }
  { exact CLE2. }
  { exact Hc2'. }
  clear Hc2'. intros c3 (Σ1 & BI & Hc3 & LV1 & FRS1 & SP1 & CR1 & BI0 & BI16 & BIU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & CLE3 & WR3 & ACC3 & ZER3) & Hc3'). clear Hc3.
  destruct RS3 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & fc3 & ->).
  rewrite EU1 in ST3, PRES3. rewrite (ret_pc_even SITE_bnx_zalloc) in Hc3' by (unfold SITE_bnx_zalloc; clear; lia).
  change (mcost 128) with 0 in CR1. change (Z.to_nat 128) with 128%nat in ZER3.
  assert (INBI1 : In (BI, 128) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
  assert (INLK1 : In (LK, 40) (rt_live RT Σ1)) by (rewrite LV1; right; exact INLK).
  pose proof (af_live_range RT AF Σ1 m3 BI 128 ART3 INBI1) as RBI. rewrite SP1 in RBI. pose proof (afp_live_hi RT GOBJ AFP Σ1 m3 BI 128 ART3 INBI1 ltac:(clear; lia)) as BIHI.
  assert (NBI : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> ~ (BI <= x < BI + 128))
    by (intros x Hx; exact (newchunk_apart RT AF Σ Σ1 m3 BI 128 usp x ART3 LV1 FRS1 SP1 ltac:(clear - NUM; lia) ltac:(clear; lia) Hx)).
  assert (DBL : BI + 128 <= LK \/ LK + 40 <= BI).
  { pose proof (NBI LK ltac:(apply (acl_live _ _ _ LK 40); [exact INLK | clear; lia])). pose proof (NBI (LK + 39) ltac:(apply (acl_live _ _ _ LK 40); [exact INLK | clear; lia])).
    pose proof (live_in_disj RT AF Σ1 m3 _ _ _ _ ART3 INBI1 INLK1 ltac:(intros X; injection X as E1 E2; clear - E1 H; lia)). clear - H H0 H1. lia. }
  assert (BC3 : rw_cells asegs m3 BI (bnx_cells z64 z64 z64 z64)).
  { split; [split; [cbn; repeat split; reflexivity | exact ZER3] | exact WR3]. }
  (* [comment removed for export] *)
  pose proof (bne_s1_walk (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp s1 b1 b2 b3 b4 b5 b6 b7 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F3 fc3 m3 meth BI lo
                BI0 BI16 BIHI ltac:(clear - BIU; unfold USTACK_TOP in BIU; lia) METHR ACC3 BC3 ltac:(rewrite EU1; exact ST3) ltac:(clear - NUM; lia) ltac:(rewrite EU1; unfold usp1, USTACK_TOP in *; clear - NUM; lia) MI3) as W1.
  rewrite EU1 in W1.
  cl_lift W1 Hc3' c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (m4 & -> & MU4 & WM4 & MI4 & BC4 & ST4) & Hc4'). clear Hc4.
  pose proof (wmono_trans asegs _ _ _ WM02 (wmono_trans asegs _ _ _ WM3 WM4)) as WM04.
  assert (ART4 : ART RT Σ1 m4).
  { apply (af_frame RT AF Σ1 m3 m4 usp1 ART3 ltac:(rewrite SP1; unfold usp1; clear - NUM; lia)); [| exact WM4].
    intros a Ha. apply MU4. cbn [outside]. split; [| exact I]. intros Hin; apply Ha. apply (acl_live _ _ _ BI 128); [exact INBI1 | clear - Hin; lia]. }
  (* [comment removed for export] *)
  assert (G4 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x < usp - 624 \/ usp <= bv_unsigned x ->
               bv_unsigned x <> G_ALLOW_CUST -> m4 x = m x).
  { intros x Hx Hlt Hg. rewrite (MU4 x ltac:(cbn [outside]; split; [exact (NBI _ Hx) | exact I])).
    rewrite (PRES3 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto | auto | unfold usp1; clear; lia]) ltac:(cbn [outside]; clear - Hg; lia)). exact (A02 x Hx Hlt). }
  assert (EST4 : exd_stat m4 kd LK).
  { apply (exd_stat_agree m m4 kd LK EST). intros x Hx. destruct (STA _ (exd_fp_static kd _ KD Hx)) as (Hc & Hl).
    apply (G4 x Hc ltac:(left; exact Hl)). unfold exd_fp, G_ALLOW_CUST in *. clear - Hx KD. lia. }
  assert (LKC4 : rw_cells asegs m4 LK (mutex_cells z64 z64)).
  { apply (rw_cells_agree asegs m m4 _ _ LKC); [| exact WM04]. intros x Hx. cbv beta in Hx. cbn [cells_size mutex_cells csize Nat.add] in Hx.
    apply G4; [apply (acl_live _ _ _ LK 40); [exact INLK | clear - Hx; lia] | left; clear - Hx RLK NUM; lia | unfold G_ALLOW_CUST; clear - Hx LKHI; lia]. }
  assert (CLE4 : cl_env m4 (Z_to_bv 8 1) canary) by (apply (cl_env_seg _ m3 m4 _ canary CLE3 MU4); clear - BIHI; cl_fp_lia).
  (* [comment removed for export] *)
  unfold bnx_cells in BC4. rewrite 2 app_assoc in BC4.
  apply (proj1 (rw_cells_app m4 _ _ _)) in BC4. destruct BC4 as [BC4 ADC4].
  apply (proj1 (rw_cells_app m4 _ _ _)) in BC4. destruct BC4 as [BC4 TL4].
  apply (proj1 (rw_cells_app m4 _ _ _)) in BC4. destruct BC4 as [HD4 BW4].
  cbn [cells_size csize Nat.add app] in ADC4, TL4, BW4.
  replace (BI + Z.of_nat 112) with (BI + 112) in ADC4 by (clear; lia). replace (BI + Z.of_nat 72) with (BI + 72) in TL4 by (clear; lia). replace (BI + Z.of_nat 40) with (BI + 40) in BW4 by (clear; lia).
  assert (AG04 : agree_on (fun x => usp <= x < USTACK_TOP) m m4).
  { intros x Hx. cbv beta in Hx. apply G4; [apply acl_stack; exact Hx | right; clear - Hx; lia | unfold G_ALLOW_CUST, USTACK_TOP in *; clear - Hx NUM HLO; lia]. }
  assert (SV4 : rw_cells asegs m4 (usp - 16) [C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m2 m4 _ _ SV2); [| exact (wmono_trans asegs _ _ _ WM3 WM4)]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    rewrite (MU4 x ltac:(cbn [outside]; clear - Hx RBI NUM; lia)). apply PRES3; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia|].
    cbn [outside]. unfold G_ALLOW_CUST, USTACK_TOP in *. clear - Hx NUM HLO. lia. }
  destruct (cl_chain_call (rt_cg RT Σ) FZ_BIO_NEW e_new_ex_data SITE_bnx_newex m m4 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGB (SITE_bnx_newex, FZ_BIO_NEW) ltac:(unfold BNX_SITES; cbn [app In]; right; left; reflexivity)) (proj2 CGB (SITE_bnx_newex, e_new_ex_data) ltac:(unfold BNX_CALLS; cbn [app In]; right; left; reflexivity)) UWC AG04
              ltac:(fold usp; exact SV4) ltac:(rewrite EU1; fold usp; unfold usp1; clear; lia) SPT) as (CTX4 & UWC4).
  rewrite <- CG1 in CTX4.
  (* [comment removed for export] *)
  apply (C_NEWEX Σ1 PMc (Z_to_bv 64 SITE_bnx_newex) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 sp (Z_to_bv 64 BI) (Z_to_bv 64 12) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 112))
           b3 b4 b5 b6 b7 (Z_to_bv 64 meth) (Z_to_bv 64 (BI + 112)) (Z_to_bv 64 0x7fff8000) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F3 fc3 m4 lo (bv_unsigned ra :: outer)
           (Z_to_bv 8 1) canary kd LK (BI + 112) BI 128 (Z_to_bv 64 0) (Z_to_bv 64 0) FDO MST eq_refl eq_refl eq_refl ART4 MI4).
  { fold usp in SPA. unfold call_ok. rewrite EU1, SP1. split; [exact ST4|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK; lia|].
    split; [unfold USTACK_TOP in *; clear - NUM; lia|]. clear - SPA. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1, NEWEX_STACK. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_bnx_newex) by (unfold SITE_bnx_newex; clear; lia). exact CTX4. }
  { exact UWC4. }
  { rewrite CG1. apply (cg_has_weaken _ _ _ _ _ CGB); vm_compute; reflexivity. }
  { rewrite FRS1. exact Hfr. }
  { rewrite CR1. clear - Hcr. lia. }
  { exact EST4. } { exact INLK1. } { exact LKC4. } { exact ADC4. }
  { clear - BI16. Z.div_mod_to_equations. lia. }
  { exact INBI1. }
  { clear - BI16. Z.div_mod_to_equations. lia. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { clear - DBL. lia. }
  { exact CLE4. }
  { exact Hc4'. }
  clear Hc4'. intros c5 (Σ2 & Hc5 & LV2 & FRS2 & SP2 & CR2 & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & CLE5 & EST5 & ADC5 & LKC5) & Hc5'). clear Hc5.
  destruct RS5 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F5 & fc5 & ->).
  rewrite EU1 in ST5, PRES5. rewrite (ret_pc_even SITE_bnx_newex) in Hc5' by (unfold SITE_bnx_newex; clear; lia).
  pose proof (wmono_trans asegs _ _ _ WM04 WM5) as WM05.
  assert (INBI2 : In (BI, 128) (rt_live RT Σ2)) by (rewrite LV2; exact INBI1). assert (INLK2 : In (LK, 40) (rt_live RT Σ2)) by (rewrite LV2; exact INLK1).
  (* [comment removed for export] *)
  assert (P5 : forall x : word, BI <= bv_unsigned x < BI + 112 -> m5 x = m4 x).
  { intros x Hx. apply PRES5; [apply (acl_live _ _ _ BI 128); [exact INBI1 | clear - Hx; lia]|]. unfold NX_W. cbn [outside]. clear - Hx DBL. lia. }
  assert (HD5 : rw_cells asegs m5 BI [C8 z64; C8 (Z_to_bv 64 meth); C8 z64; C8 z64; C8 z64]).
  { apply (rw_cells_agree asegs m4 m5 _ _ HD4); [| exact WM5]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply P5. clear - Hx. lia. }
  assert (BW5 : rw_cells asegs m5 (BI + 40) [C4 z64; C4 (Z_to_bv 64 1); C4 z64; C4 z64; C4 z64; C4 z64; C8 z64]).
  { apply (rw_cells_agree asegs m4 m5 _ _ BW4); [| exact WM5]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply P5. clear - Hx. lia. }
  assert (TL5 : rw_cells asegs m5 (BI + 72) [C8 z64; C8 z64; C4 (Z_to_bv 64 1); C4 z64; C8 z64; C8 z64]).
  { apply (rw_cells_agree asegs m4 m5 _ _ TL4); [| exact WM5]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply P5. clear - Hx. lia. }
  (* [comment removed for export] *)
  assert (MSH8 : (meth + 72) mod 8 = 0) by (clear - METHA; destruct METHA as [-> | ->]; reflexivity).
  assert (MSB5 : ro_cells asegs m5 ((meth + 72) / 8 + 2147450880) [C1 (Z_to_bv 8 0)]).
  { destruct METHA as [EM | EM].
    - pose proof (afp_gsh_byte RT GOBJ AFP Σ2 m5 M_MEM_A 112 (meth + 72) ART5 GO_memmeth ltac:(rewrite EM; clear; lia) ltac:(rewrite EM; unfold M_MEM_A; clear; lia) MSH8) as X.
      rewrite EM in X |- *. replace (if M_MEM_A + 112 - (M_MEM_A + 72) <? 8 then M_MEM_A + 112 - (M_MEM_A + 72) else 0) with 0 in X by reflexivity. exact X.
    - pose proof (afp_gsh_byte RT GOBJ AFP Σ2 m5 M_SECMEM_A 112 (meth + 72) ART5 GO_secmeth ltac:(rewrite EM; clear; lia) ltac:(rewrite EM; unfold M_SECMEM_A; clear; lia) MSH8) as X.
      rewrite EM in X |- *. replace (if M_SECMEM_A + 112 - (M_SECMEM_A + 72) <? 8 then M_SECMEM_A + 112 - (M_SECMEM_A + 72) else 0) with 0 in X by reflexivity. exact X. }
  destruct (af_client_consts RT AF Σ2 m5 ART5) as (_ & _ & _ & _ & UT5).
  pose proof (bne_s2_walk (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 sp d1 d2 d3 d4 d5 d6 d7 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F5 fc5 m5 meth BI
                METHA ltac:(clear - BI0 BIU; unfold USTACK_TOP in BIU; lia) UT5 MSB5 MI5) as W2.
  cl_lift W2 Hc5' c6 Hc6.
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & -> & Hc6'). clear Hc6.
  (* [comment removed for export] *)
  assert (C_CRE : mem_init_at_stmt RT (mcreate meth) (fun _ => Z_to_bv 64 (msec meth)) (fun Σ ra => In (bv_unsigned ra, e_mem_init) (cg_call (rt_cg RT Σ)))).
  { clear - METHA C_MNEW C_SNEW. destruct METHA as [-> | ->]; [exact C_MNEW | exact C_SNEW]. }
  assert (AG05 : agree_on (fun x => usp <= x < USTACK_TOP) m m5).
  { intros x Hx. cbv beta in Hx. rewrite (PRES5 x ltac:(left; unfold usp1; clear - Hx; lia) ltac:(unfold NX_W; cbn [outside]; clear - Hx RBI RLK NUM; lia)). exact (AG04 x Hx). }
  assert (SV5 : rw_cells asegs m5 (usp - 16) [C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m4 m5 _ _ SV4); [| exact WM5]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply PRES5; [left; unfold usp1, USTACK_TOP in *; clear - Hx NUM; lia|]. unfold NX_W. cbn [outside]. clear - Hx RBI RLK NUM. lia. }
  destruct (cl_chain_call (rt_cg RT Σ) FZ_BIO_NEW (mcreate meth) SITE_bnx_create m m5 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              (proj1 CGB (SITE_bnx_create, FZ_BIO_NEW) ltac:(unfold BNX_SITES; cbn [app In]; right; right; left; reflexivity))
              (proj2 CGB (SITE_bnx_create, mcreate meth) ltac:(unfold BNX_CALLS, mcreate; cbn [app In]; clear - METHA; destruct METHA as [-> | ->]; cbn [Z.eqb Pos.eqb M_MEM_A M_SECMEM_A];
                                  [right; right; left; reflexivity | right; right; right; left; reflexivity])) UWC AG05
              ltac:(fold usp; exact SV5) ltac:(rewrite EU1; fold usp; unfold usp1; clear; lia) SPT) as (CTX5 & UWC5).
  rewrite <- CG1, <- CG2 in CTX5.
  apply (C_CRE Σ2 PMc (Z_to_bv 64 SITE_bnx_create) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 sp (Z_to_bv 64 BI) (Z_to_bv 64 BI) (Z_to_bv 64 (mcreate meth)) d2 d3 d4 d5 d6 d7
           (Z_to_bv 64 (meth + 72)) (Z_to_bv 64 (BI + 112)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((meth + 72) / 8 + 2147450880)) s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F5 fc5 m5 lo
           (bv_unsigned ra :: outer) (Z_to_bv 8 1) canary BI 128 0 (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) FDO MST eq_refl eq_refl).
  { rewrite CG2, CG1. rewrite (unsigned_lit SITE_bnx_create) by (unfold SITE_bnx_create; clear; lia). exact (proj2 CGB (SITE_bnx_create, e_mem_init) ltac:(unfold BNX_CALLS; cbn [app In]; right; right; right; right; left; reflexivity)). }
  { exact INBI2. } { clear; lia. } { exact BI16. }
  { exact BW5. }
  { split; [clear; lia | reflexivity]. }
  { exact ART5. } { exact MI5. }
  { fold usp in SPA. unfold call_ok. rewrite EU1, SP2, SP1. split; [exact ST5|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK; lia|].
    split; [unfold USTACK_TOP in *; clear - NUM; lia|]. clear - SPA. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_bnx_create) by (unfold SITE_bnx_create; clear; lia). exact CTX5. }
  { exact UWC5. }
  { rewrite CG2, CG1. apply (cg_has_weaken _ _ _ _ _ CGB); vm_compute; reflexivity. }
  { rewrite LV2, LV1. cbn [length]. clear - Hlen. lia. }
  { clear - CR2 CR1 Hcr. lia. }
  { exact CLE5. }
  { exact Hc6'. }
  clear Hc6'. intros c7 (Σ3 & bb & B & R & Hc7 & LV3 & FRS3 & SP3 & CR3 & BB0 & BB16 & B0 & B16 & R0 & R16 & CG3).
  destruct (ASTA_unpack RT Σ3 _ _ c7 Hc7) as (ms7 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & CLE6 & BW6 & BBC6 & BMC6 & RPC6) & Hc7'). clear Hc7.
  destruct RS6 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F6 & fc6 & ->).
  rewrite EU1 in ST6, PRES6. rewrite (ret_pc_even SITE_bnx_create) in Hc7' by (unfold SITE_bnx_create; clear; lia).
  pose proof (wmono_trans asegs _ _ _ WM05 WM6) as WM06.
  (* [comment removed for export] *)
  assert (MSB6 : ro_cells asegs m6 ((meth + 72) / 8 + 2147450880) [C1 (Z_to_bv 8 0)]).
  { destruct METHA as [EM | EM].
    - pose proof (afp_gsh_byte RT GOBJ AFP Σ3 m6 M_MEM_A 112 (meth + 72) ART6 GO_memmeth ltac:(rewrite EM; clear; lia) ltac:(rewrite EM; unfold M_MEM_A; clear; lia) MSH8) as X.
      rewrite EM in X |- *. replace (if M_MEM_A + 112 - (M_MEM_A + 72) <? 8 then M_MEM_A + 112 - (M_MEM_A + 72) else 0) with 0 in X by reflexivity. exact X.
    - pose proof (afp_gsh_byte RT GOBJ AFP Σ3 m6 M_SECMEM_A 112 (meth + 72) ART6 GO_secmeth ltac:(rewrite EM; clear; lia) ltac:(rewrite EM; unfold M_SECMEM_A; clear; lia) MSH8) as X.
      rewrite EM in X |- *. replace (if M_SECMEM_A + 112 - (M_SECMEM_A + 72) <? 8 then M_SECMEM_A + 112 - (M_SECMEM_A + 72) else 0) with 0 in X by reflexivity. exact X. }
  destruct (af_client_consts RT AF Σ3 m6 ART6) as (_ & _ & _ & _ & UT6).
  assert (FR6 : rw_cells asegs m6 usp1 [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_agree asegs m2 m6 _ _ FR2); [| exact (wmono_trans asegs _ _ _ WM3 (wmono_trans asegs _ _ _ WM4 (wmono_trans asegs _ _ _ WM5 WM6)))].
    intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    rewrite (PRES6 x ltac:(left; unfold USTACK_TOP in *; clear - Hx NUM; lia) ltac:(unfold MI_W, G_ALLOW_CUST; cbn [outside]; unfold usp1, USTACK_TOP in *; clear - Hx RBI NUM HLO; lia)).
    rewrite (PRES5 x ltac:(left; unfold USTACK_TOP in *; clear - Hx NUM; lia) ltac:(unfold NX_W; cbn [outside]; unfold usp1 in Hx; clear - Hx RBI RLK NUM; lia)).
    rewrite (MU4 x ltac:(cbn [outside]; unfold usp1 in Hx; clear - Hx RBI NUM; lia)).
    apply PRES3; [left; unfold USTACK_TOP in *; clear - Hx NUM; lia|]. cbn [outside]. unfold G_ALLOW_CUST, usp1, USTACK_TOP in *. clear - Hx NUM HLO. lia. }
  fold usp1 in ST6.
  pose proof (bne_s3_walk ra sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 s0 s1 s2 s3 s4 s5 F6 fc6 m6 meth BI lo j
                METHA ltac:(clear - BI0 BIU; unfold USTACK_TOP in BIU; lia) ltac:(fold usp; clear - HLO; lia) ltac:(clear - NUM; lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia)
                UT6 MSB6 FR6 ST6 MI6) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc7' c8 Hc8.
  (* [comment removed for export] *)
  apply Hk. exists Σ3.
  split; [| rewrite FRS3, FRS2, SP3, SP2, CR3, CG3, CG2; split; [exact FRS1 | split; [exact SP1 | split; [clear - CR2 CR1; lia | exact CG1]]]].
  apply (ASTA_conseq RT Σ3 PMc _ _ c8 Hc8). intros ms (-> & ST8). fold usp in ST8. exists (Z_to_bv 64 BI), m6.
  split; [exists w0, w1, w2, g1, g2, g3, g4, g5, g6, g7, w3, w4, w5, w6, F6, fc6; reflexivity|].
  split; [exact (conj ART6 (conj MI6 ST8))|].
  (* [comment removed for export] *)
  assert (B6 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> outside (lib_W LBL) (bv_unsigned x) -> m6 x = m x).
  { intros x Hx Ho.
    assert (HoL : outside LIB_W (bv_unsigned x)) by (unfold lib_W in Ho; exact (proj1 (outside_appD _ _ _ Ho))).
    assert (HoB : forall e, In e LBL -> ~ (fst e <= bv_unsigned x < fst e + snd e)).
    { intros e He. unfold lib_W in Ho. exact (outside_mapD _ _ _ (proj2 (outside_appD _ _ _ Ho)) He). }
    assert (NG : bv_unsigned x <> G_ALLOW_CUST) by (intros EQ; unfold LIB_W, G_ALLOW_CUST in *; cbn [outside] in HoL; clear - HoL EQ; lia).
    pose proof (NBI _ Hx) as NB. pose proof (HoB _ INLKL) as NL. cbn [fst snd] in NL.
    rewrite (PRES6 x ltac:(rewrite LV2, LV1, FRS2, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; right; exact He | auto | unfold usp1; clear; lia])
                     ltac:(unfold MI_W; cbn [outside]; clear - NB NG; lia)).
    rewrite (PRES5 x ltac:(rewrite LV1, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; right; exact He | auto | unfold usp1; clear; lia])
                     ltac:(unfold NX_W; cbn [outside]; clear - NB NL; lia)).
    destruct (cl_split RT AF Σ m usp 624 _ ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) Hx) as [Hi|Lo]; [exact (G4 x Hx ltac:(right; exact Hi) NG) | exact (G4 x Hx ltac:(left; exact Lo) NG)]. }
  split; [exact B6|].
  split; [exact CLE6|].
  split; [exact WM06|].
  split.
  { (* [comment removed for export] *)
    apply (LCLOSE m6).
    - intros x Hfp HnL. destruct (libenv_fp_where LBL _ Hfp) as [(HW & HS & HC)|(p & n & Hin & Hr)].
      + destruct (STA _ HS) as (Hc & Hl). pose proof (NBI _ Hc) as NB. pose proof (client_static_range _ HS) as SR.
        assert (NG : bv_unsigned x <> G_ALLOW_CUST) by (intros EQ; apply HC; rewrite EQ; apply (cl_cell_intro G_ALLOW_CUST (G_ALLOW_CUST + 1)); [cbn; tauto | clear; lia]).
        rewrite (PRES6 x ltac:(rewrite LV2, LV1, FRS2, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Hc); [intros e He; right; exact He | auto | unfold usp1; clear; lia])
                         ltac:(unfold MI_W; cbn [outside]; clear - NB NG; lia)).
        rewrite (PRES5 x ltac:(rewrite LV1, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Hc); [intros e He; right; exact He | auto | unfold usp1; clear; lia])
                         ltac:(unfold NX_W; cbn [outside]; unfold SEGTOP_A in SR; clear - NB SR LKHI; lia)).
        exact (G4 x Hc ltac:(left; exact Hl) NG).
      + pose proof (INCL _ Hin) as HinL. pose proof (af_live_range RT AF Σ m p n ART0 HinL) as Rp.
        assert (Hc : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x)) by (apply (acl_live _ _ _ p n); [exact HinL | exact Hr]).
        pose proof (NBI _ Hc) as NB.
        assert (NG : bv_unsigned x <> G_ALLOW_CUST) by (unfold G_ALLOW_CUST, SEGTOP_A in *; clear - Hr Rp; lia).
        assert (NLK : ~ (LK + 4 <= bv_unsigned x < LK + 8)).
        { intros H8. apply HnL. clear - H8. lia. }
        rewrite (PRES6 x ltac:(rewrite LV2, LV1, FRS2, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Hc); [intros e He; right; exact He | auto | unfold usp1; clear; lia])
                         ltac:(unfold MI_W; cbn [outside]; clear - NB NG; lia)).
        rewrite (PRES5 x ltac:(rewrite LV1, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Hc); [intros e He; right; exact He | auto | unfold usp1; clear; lia])
                         ltac:(unfold NX_W; cbn [outside]; clear - NB NLK; lia)).
        apply (G4 x Hc); [left; clear - Hr Rp NUM; lia | exact NG].
    - apply (rw_cells_agree asegs m5 m6 _ _ LKC5); [| exact WM6]. intros x Hx. cbv beta in Hx. cbn [cells_size mutex_cells csize Nat.add] in Hx.
      apply PRES6; [apply (acl_live _ _ _ LK 40); [exact INLK2 | clear - Hx; lia]|]. unfold MI_W, G_ALLOW_CUST. cbn [outside]. clear - Hx DBL LKHI. lia. }
  (* [comment removed for export] *)
  exists (MBK BI bb B R None), BI, bb, B, R. split; [reflexivity|]. split; [reflexivity|]. split; [rewrite LV3, LV2, LV1; reflexivity|].
  assert (P6 : forall x : word, (BI <= bv_unsigned x < BI + 40 \/ BI + 72 <= bv_unsigned x < BI + 128) -> m6 x = m5 x).
  { intros x Hx. apply PRES6; [apply (acl_live _ _ _ BI 128); [exact INBI2 | clear - Hx; lia]|]. unfold MI_W, G_ALLOW_CUST. cbn [outside]. clear - Hx BIHI. lia. }
  exists B. exists (Z.lor 0 4096), (Z_to_bv 64 0), (Z_to_bv 64 (-1)), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0).
  split; [reflexivity|]. split; [reflexivity|]. split; [rewrite LV3, LV2, LV1; right; right; right; left; reflexivity|]. split; [exact BI16|].
  split; [exact (live4_nodup RT AF Σ3 m6 R B bb BI _ ART6 ltac:(rewrite LV3, LV2, LV1; reflexivity))|].
  split; [exact METHA|].
  split.
  { unfold bio_head. apply (rw_cells_agree asegs m5 m6 _ _ HD5); [| exact WM6]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply P6. left. clear - Hx. lia. }
  split; [unfold bio_w1_cells; cbn [k_bb]; exact BW6|].
  split; [change (Z.lor 0 4096) with 4096; split; [clear; lia | reflexivity]|].
  split.
  { unfold bio_tail. change ([C8 z64; C8 z64; C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 z64; C8 z64; C8 z64; C8 z64])
      with ([C8 z64; C8 z64; C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 z64; C8 z64] ++ [C8 z64; C8 z64]).
    apply (proj2 (rw_cells_app m6 (BI + 72) _ _)). cbn [cells_size csize Nat.add]. replace (BI + 72 + Z.of_nat 40) with (BI + 112) by (clear; lia). split.
    - apply (rw_cells_agree asegs m5 m6 _ _ TL5); [| exact WM6]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply P6. right. clear - Hx. lia.
    - apply (rw_cells_agree asegs m5 m6 _ _ ADC5); [| exact WM6]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply P6. right. clear - Hx. lia. }
  exists (Z_to_bv 64 0). cbn [k_bb k_bm k_rp k_d].
  split; [rewrite LV3; right; right; left; reflexivity|]. split; [exact BB16|]. split; [exact BBC6|].
  split; [rewrite LV3; right; left; reflexivity|]. split; [exact B16|]. split; [rewrite LV3; left; reflexivity|]. split; [exact R16|].
  split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|].
  split; [reflexivity|]. split; [unfold bufmem_cells in BMC6; exact BMC6 | exact RPC6].
Qed.
End CBnew.
