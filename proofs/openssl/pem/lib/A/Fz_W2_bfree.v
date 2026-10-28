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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_env Th_mutex Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_M_secure Fz_T_lock Fz_W1_defs Fz_W1_free Fz_W3_iface Fz_W5_rep Fz_W2_exdl Fz_W2_exd Fz_W2_exdf Fz_W2_exdc Fz_W2_bnew.
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

Definition e_bio_free_inner : Z := 0x2369e0.      (* [comment removed for export] *)
Definition SITE_bfw_inner : Z := 0x2369d0.        (* [comment removed for export] *)
Definition SITE_bfi_destroy : Z := 0x236b04.      (* [comment removed for export] *)
Definition SITE_bfi_freeex : Z := 0x236b14.       (* [comment removed for export] *)
Definition SITE_bfi_cfree : Z := 0x236b28.        (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bfr_s0_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem)
    (meth BI lo : Z) (nr nw : word),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> bv_unsigned sp mod 16 = 0 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  (meth = M_MEM_A \/ meth = M_SECMEM_A) -> ro_cells asegs m ((meth + 80) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m BI (bio_head meth) -> rw_cells asegs m (BI + 72) (bio_tail nr nw) -> acc asegs m BI 128 ->
  0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  acc asegs m (bv_unsigned sp - 32) 32 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a2' a3' : word) (j j2 : list byte) (m' : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_bfi_destroy) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -32)) (Z_to_bv 64 BI)
                 (Z_to_bv 64 BI) (Z_to_bv 64 e_mem_free) a2' a3' a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_mem_free) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (BI + 88, BI + 92)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' (bv_unsigned sp + -32) [CB 12 j; C4 (Z_to_bv 64 0); C8 s0; C8 ra]
       /\ rw_cells asegs m' (bv_unsigned sp + -80) [CB 8 j2; C8 s3; C8 s2; C8 s1; C8 sp; C8 (Z_to_bv 64 SITE_bfw_inner)]
       /\ stk asegs m' lo (bv_unsigned sp + -80)
       /\ rw_cells asegs m' BI (bio_head meth)
       /\ rw_cells asegs m' (BI + 72) [C8 z64; C8 z64; C4 (Z_to_bv 64 0); C4 z64; C8 nr; C8 nw; C8 z64; C8 z64])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BI) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FZ_BIO_FREE) fc None m (seg_rom asegs)).
Proof.
  intros until nw. intros ST HLO HLOS SPH SPA UT SHC HM MSB HD TL ACCB BI0 BIAL BIHI BILO ACCS MI.
  unfold FZ_BIO_FREE, g_shadow_memory_dynamic_address, bio_head, bio_tail in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 80, SP); (BI + 88, BI + 92)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 80, SP); (BI + 88, BI + 92)]) by (clear - HLO HLOS SPH BIHI; ut_fp_lia).
  assert (HWS : sh_fp [(SP - 80, SP); (BI + 88, BI + 92)]) by (clear - HLO HLOS SPH BIHI; sh_fp_lia).
  assert (EUB : bv_unsigned (Z_to_bv 64 BI) = BI) by (apply unsigned_lit; lia).
  assert (BIAL8 : BI mod 8 = 0) by (clear - BIAL; Z.div_mod_to_equations; lia).
  assert (SPAL8 : (SP - 32) mod 8 = 0) by (clear - SPA; Z.div_mod_to_equations; lia).
  assert (HMR : 0x500000 <= meth /\ meth + 112 <= 0x5a9d08) by (clear - HM; destruct HM as [-> | ->]; unfold M_MEM_A, M_SECMEM_A; lia).
  assert (HMAL : meth mod 8 = 0) by (clear - HM; destruct HM as [-> | ->]; reflexivity).
  assert (AMO : amo_aligned AW (Z_to_bv 64 (BI + 88)) = true) by (apply th_amo_aligned; [clear - BI0 BILO HLO SPH; lia | clear - BIAL; Z.div_mod_to_equations; lia]).
  (* [comment removed for export] *)
  th_frame 32%nat [12; 4; 8; 8]%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST.
  zstep. zstep; lfix. zstep; lfix. zstep. zstep. zstep. zstep.
  zstep. if_cases KB; zify_cond KB. { exfalso. rewrite ?unsigned_lit in KB by lia. clear - KB BI0. lia. }
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. if_false.
  (* [comment removed for export] *)
  zstep. zstep.
  th_amo_step AMO.
  change (Z_to_le_bytes 4 (bv_unsigned (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 1)))) (Z_to_bv 32 4294967295)))) with (le4 (Z_to_bv 64 0)).
  mem_after_store.
  change (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1).
  (* [comment removed for export] *)
  zstep. zstep. zstep. if_false.
  zstep. zstep; lfix. zstep. if_false.
  zstep. zstep. zstep. if_false.
  zstep. zstep. zstep. if_false.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. if_false. zstep. zstep. if_false.
  zstep. zstep. zstep. zstep. zstep. if_false. zstep. zstep. if_true.
  zstep. zstep. zstep. zstep. zstep. if_false. zstep.
  zstep. if_cases KM; zify_cond KM. { exfalso. rewrite ?unsigned_lit in KM by lia. clear - KM HM. destruct HM as [-> | ->]; unfold M_MEM_A, M_SECMEM_A in KM; lia. }
  zstep. zstep. rewrite (shr3_div (meth + 80)) by lia. zstep. zstep. zstep. if_false.
  (* [comment removed for export] *)
  destruct HM as [-> | ->]; unfold M_MEM_A, M_SECMEM_A in *.
  1: replace (5538432 + 80) with 5538512 in * by reflexivity.
  2: replace (5538592 + 80) with 5538672 in * by reflexivity.
  all: zstep; zstep; if_false; zstep; zstep.
  all: subst SP; rewrite ?Z_to_bv_bv_unsigned in FR0 |- *.
  all: unfold SITE_bfi_destroy, SITE_bfw_inner, e_mem_free.
  all: apply evt_done; do 5 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [eassumption|]; split; [eassumption|]; split; [assumption|]; split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bfr_s1_walk : forall sp1 gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (BI : Z),
  0 <= BI -> BI + 128 < 2 ^ 47 -> mem_inv asegs m ->
  evt asegs (fun ms =>
       ms = MS (mkR (Z_to_bv 64 SITE_bfi_freeex) sp1 gp tp t0 t1 t2 s0 (Z_to_bv 64 BI) (Z_to_bv 64 12) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 112)) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_free_ex_data_A) fc None m (seg_rom asegs))
    (MS (mkR (Z_to_bv 64 SITE_bfi_destroy) sp1 gp tp t0 t1 t2 s0 (Z_to_bv 64 BI) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bfi_destroy) fc None m (seg_rom asegs)).
Proof.
  intros until BI. intros BI0 BIU MI. unfold SITE_bfi_destroy in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUB : bv_unsigned (Z_to_bv 64 BI) = BI) by (apply unsigned_lit; lia).
  zstep. zstep. zstep. zstep.
  unfold SITE_bfi_freeex, e_free_ex_data_A. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bfr_s2_walk : forall sp1 gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (BI : Z),
  mem_inv asegs m ->
  evt asegs (fun ms =>
       ms = MS (mkR (Z_to_bv 64 SITE_bfi_cfree) sp1 gp tp t0 t1 t2 s0 (Z_to_bv 64 BI) (Z_to_bv 64 BI) (Z_to_bv 64 BNX_FILE) (Z_to_bv 64 145) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_CRYPTO_free) fc None m (seg_rom asegs))
    (MS (mkR (Z_to_bv 64 SITE_bfi_freeex) sp1 gp tp t0 t1 t2 s0 (Z_to_bv 64 BI) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bfi_freeex) fc None m (seg_rom asegs)).
Proof.
  intros until BI. intros MI. unfold SITE_bfi_freeex in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep. zstep.
  unfold SITE_bfi_cfree, e_CRYPTO_free, BNX_FILE. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bfr_s3_walk : forall ra0 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (e0 e1 e2 e3 : word) (F : bvmap 5 word) fc (m : mem)
    (BI lo : Z) (j j2 : list byte),
  lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -32) [CB 12 j; C4 (Z_to_bv 64 0); C8 e0; C8 ra0] ->
  rw_cells asegs m (bv_unsigned sp + -80) [CB 8 j2; C8 e3; C8 e2; C8 e1; C8 sp; C8 (Z_to_bv 64 SITE_bfw_inner)] ->
  stk asegs m lo (bv_unsigned sp + -80) -> mem_inv asegs m ->
  evt asegs (fun ms =>
       ms = MS (mkR ra0 sp gp tp t0 t1 t2 e0 e1 s2 a1 a2 a3 a4 a5 a6 a7 e2 e3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra0) fc None m (seg_rom asegs)
       /\ stk asegs m lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 SITE_bfi_cfree) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -32)) (Z_to_bv 64 BI)
             a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bfi_cfree) fc None m (seg_rom asegs)).
Proof.
  intros until j2. intros HLO HLOS SPH FRW FRI ST MI. unfold SITE_bfi_cfree, SITE_bfw_inner in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp) in FRI |- *. rewrite <- ESP in FRI |- *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  zstep. zstep. do 5 zstep.
  zstep. release_frame FRI ST (SP + -32). zstep.
  zstep. zstep.
  zstep. release_frame FRW ST SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  apply evt_done. split; [reflexivity | exact ST].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bfr_null_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 80 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> mem_inv asegs m ->
  evt asegs (fun ms => exists (a1' : word) (m' : mem),
       ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 FZ_BIO_FREE) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HLOS SPH MI. unfold FZ_BIO_FREE in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 80, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  th_frame 32%nat [12; 4; 8; 8]%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep.
  th_frame 48%nat [8; 8; 8; 8; 8; 8]%nat ST.
  zstep. zstep; lfix. zstep; lfix. zstep. zstep. zstep. zstep.
  zstep. if_true.
  (* [comment removed for export] *)
  zstep. zstep. do 5 zstep.
  zstep. release_frame FR0 ST (SP + -32). zstep.
  zstep. zstep.
  zstep. release_frame FR ST SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  apply evt_done. do 2 eexists. split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [assumption| exact ST].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma live_remove_comm : forall p q (l : list (Z * Z)), live_remove p (live_remove q l) = live_remove q (live_remove p l).
Proof.
  intros p q l. unfold live_remove. induction l as [|e l IH]; [reflexivity|]. cbn.
  destruct (stdpp.base.decide (Is_true (negb (fst e =? q)))) as [A|A]; destruct (stdpp.base.decide (Is_true (negb (fst e =? p)))) as [B|B]; cbn.
  - destruct (stdpp.base.decide (Is_true (negb (fst e =? p)))) as [B'|B']; [| exfalso; exact (B' B)].
    destruct (stdpp.base.decide (Is_true (negb (fst e =? q)))) as [A'|A']; [| exfalso; exact (A' A)]. apply (f_equal (cons e)). exact IH.
  - destruct (stdpp.base.decide (Is_true (negb (fst e =? p)))) as [B'|B']; [exfalso; exact (B B') | exact IH].
  - destruct (stdpp.base.decide (Is_true (negb (fst e =? q)))) as [A'|A']; [exfalso; exact (A A') | exact IH].
  - exact IH.
Qed.
Lemma lra_sub : forall ps (l : list (Z * Z)) e, In e (live_remove_all ps l) -> In e l /\ ~ In (fst e) ps.
Proof.
  intros ps l e. induction ps as [|p ps IH]; cbn; intros H; [split; [exact H| intros X; exact X]|].
  apply live_remove_sub in H as H0. destruct (IH H0) as [A B]. split; [exact A|]. intros [E|X]; [| exact (B X)].
  unfold live_remove in H. apply stdpp.base.list_elem_of_In in H. apply stdpp.list_basics.list.list_elem_of_filter in H. destruct H as [H _].
  cbn in H. subst p. rewrite Z.eqb_refl in H. exact H.
Qed.
Lemma lra_keep : forall ps (l : list (Z * Z)) e, In e l -> ~ In (fst e) ps -> In e (live_remove_all ps l).
Proof.
  intros ps l e He NI. induction ps as [|p ps IH]; cbn; [exact He|].
  apply live_remove_keep; [apply IH; intros X; apply NI; right; exact X| intros E; apply NI; left; exact (eq_sym E)].
Qed.

(* [comment removed for export] *)
Lemma bf_chain2 : forall cg G r (m1 mk : mem) (sp ra : word) outer,
  cg_ctx cg e_bio_free_inner (SITE_bfw_inner :: bv_unsigned ra :: outer) -> In (r, e_bio_free_inner) (cg_site cg) -> In (r, G) (cg_call cg) ->
  uw_chain m1 (Z_to_bv 64 (bv_unsigned sp + -32)) sp (bv_unsigned ra :: outer) ->
  agree_on (fun x => bv_unsigned sp + -32 <= x < USTACK_TOP) m1 mk ->
  rw_cells asegs mk (bv_unsigned sp + -48) [C8 sp; C8 (Z_to_bv 64 SITE_bfw_inner)] ->
  80 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
  cg_ctx cg G (r :: SITE_bfw_inner :: bv_unsigned ra :: outer)
  /\ uw_chain mk (Z_to_bv 64 (bv_unsigned sp + -80)) (Z_to_bv 64 (bv_unsigned sp + -32)) (SITE_bfw_inner :: bv_unsigned ra :: outer).
Proof.
  intros cg G r m1 mk sp ra outer CTX HS HC UW AG FR SP80 SPT.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP. unfold USTACK_TOP in *.
  assert (E1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 SITE_bfw_inner) = SITE_bfw_inner) by (apply unsigned_lit; unfold SITE_bfw_inner; lia).
  rewrite <- ES in CTX |- *.
  destruct (cl_chain_call cg e_bio_free_inner G r m1 mk (Z_to_bv 64 SITE_bfw_inner) sp (Z_to_bv 64 (bv_unsigned sp + -32)) (Z_to_bv 64 (bv_unsigned sp + -80)) (bv_unsigned ra :: outer)
              CTX HS HC UW ltac:(rewrite E1; exact AG) ltac:(rewrite E1; replace (bv_unsigned sp + -32 - 16) with (bv_unsigned sp + -48) by lia; exact FR)
              ltac:(rewrite E1, E2; lia) ltac:(rewrite E1; unfold USTACK_TOP; lia)) as [A B].
  exact (conj A B).
Qed.

Section CBfree.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_MF : mem_free_stmt RT.   (* [comment removed for export] *)
Hypothesis C_MFS : mem_free_sec_stmt RT.
Hypothesis C_FREEEX : T_freeex_stmt RT.
Hypothesis C_FR : crypto_free_env_stmt RT.
Hypothesis GO_memmeth : GOBJ M_MEM_A 112.
Hypothesis GO_secmeth : GOBJ M_SECMEM_A 112.
Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
Variable libenv_fp : list (Z * Z) -> Z -> Prop.
Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
Hypothesis LEXD : exd_iface libenv libenv_fp.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Definition BFX_SITES : list (Z * Z) :=
  [(SITE_bfw_inner, FZ_BIO_FREE); (SITE_bfi_destroy, e_bio_free_inner); (SITE_bfi_freeex, e_bio_free_inner); (SITE_bfi_cfree, e_bio_free_inner)]
  ++ MF_SITES ++ MFS_SITES ++ FX_SITES.
Definition BFX_CALLS : list (Z * Z) :=
  [(SITE_bfw_inner, e_bio_free_inner); (SITE_bfi_destroy, e_mem_free); (SITE_bfi_freeex, e_free_ex_data_A); (SITE_bfi_cfree, e_CRYPTO_free); (SITE_bfi_cfree, e_free)]
  ++ MF_CALLS ++ MFS_CALLS ++ FX_CALLS.
Hypothesis HCG : cg_sub BFX_SITES BFX_CALLS FZ_SITES FZ_CALLS.

Theorem bio_free_null_proof : bio_free_null_stmt RT.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary FDO MST -> -> ART0 MI0 CALL HSTK CLE.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA). unfold TP_A in *.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 32 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  pose proof (bfr_null_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST ltac:(fold usp; unfold RT_STACK in HSTK; clear - HSTK; lia) ltac:(clear - NUM; lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia) MI0) as W0.
  cl_lift W0 HA c1 Hc1. apply Hk.
  apply (ASTA_conseq RT Σ PMc _ _ c1 Hc1). intros ms (a1' & m1 & -> & MU1 & WM1 & MI1 & ST1). fold usp in MU1, ST1. exists (Z_to_bv 64 0), m1.
  split; [exists t0, t1, t2, a1', a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, fc; reflexivity|].
  pose proof (cl_seg_ART RT AF Σ m m1 usp 80 [] ART0 ltac:(unfold RT_STACK in HSTK; clear - HSTK LOW; lia) ltac:(clear - NUM; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 80 [] ART0 ltac:(unfold RT_STACK in HSTK; clear - HSTK LOW; lia) ltac:(clear; lia) MU1) as PR1.
  split; [exact (conj ART1 (conj MI1 ST1))|]. split; [exact PR1|].
  split; [exact (cl_env_seg _ m m1 _ canary CLE MU1 ltac:(cl_fp_lia))|]. split; [reflexivity | exact WM1].
Qed.
Theorem bio_free_mem_proof : bio_free_mem_stmt RT libenv FZ_SITES FZ_CALLS.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer canary LBL K E BI BM meth len max off blw
    FDO MST -> -> ENV INCL NINK REP ART0 MI0 CALL HSTK CLE SEC CTX UWC CGH Hfr Hcr.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA). unfold BFREE_STACK in HSTK. unfold TP_A in *.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 688 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (unfold SEGTOP_A, STACK_WIN in *; lia).
  assert (HLO : lo <= usp - 688) by (unfold RT_STACK in HSTK; lia).
  set (usp1 := usp + -80).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; unfold USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  pose proof (cg_has_of_sub _ _ _ _ _ CGH HCG) as CGB.
  (* [comment removed for export] *)
  destruct REP as (fl & rrw & numw & padw & nr & nw & EBI & EBM & INBI & BIAL & ND & METH & HD & BW & FLOK & TL & MBI).
  destruct MBI as (rmaxw & INBB & BBAL & BBC & INBM & BMAL & INRP & RPAL & OFF & LEN & MAX & MD).
  set (BB := k_bb K) in *. set (RP := k_rp K) in *. rewrite <- EBM in *.
  assert (METHA : meth = M_MEM_A \/ meth = M_SECMEM_A) by exact METH.
  unfold mbio_blocks in ND, NINK. rewrite <- EBI, <- EBM in ND, NINK. fold BB RP in ND, NINK.
  destruct (LEXD m LBL E ENV) as (kd & LK & EST & INLKL & LKC & LCLOSE). pose proof (INCL _ INLKL) as INLK.
  pose proof EST as (_ & _ & KD & _ & _ & _ & _ & _ & _ & LKAL & _).
  pose proof (af_live_range RT AF Σ m LK 40 ART0 INLK) as RLK. pose proof (afp_live_hi RT GOBJ AFP Σ m LK 40 ART0 INLK ltac:(lia)) as LKHI.
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as RBI. pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BIHI.
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as RBB. pose proof (af_live_range RT AF Σ m RP 32 ART0 INRP) as RRP. pose proof (af_live_range RT AF Σ m BM 32 ART0 INBM) as RBM.
  assert (NLK : ~ In LK [BI; BB; BM; RP]) by (intros X; apply (NINK _ INLKL); cbn [fst]; clear - X; cbn in X |- *; tauto).
  pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 INBI INLK ltac:(intros X; injection X as E1 E2; apply NLK; left; exact E1)) as DBL.
  assert (STA : forall a, client_static a -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ a < usp - 688 /\ ~ (BI <= a < BI + 128)).
  { intros a Ha. pose proof (client_static_range a Ha) as Ra. split; [right; left; exact Ha|]. unfold SEGTOP_A in *. clear - Ra HLOI HLO BIHI. lia. }
  pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ART0 INBI)) as ACCB.
  pose proof (af_acc_stack RT AF Σ m (usp - 32) 32 ART0 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia)) as ACCS.
  assert (MSH8 : (meth + 80) mod 8 = 0) by (clear - METHA; destruct METHA as [-> | ->]; reflexivity).
  assert (MSB0 : ro_cells asegs m ((meth + 80) / 8 + 2147450880) [C1 (Z_to_bv 8 0)]).
  { destruct METHA as [EM | EM].
    - pose proof (afp_gsh_byte RT GOBJ AFP Σ m M_MEM_A 112 (meth + 80) ART0 GO_memmeth ltac:(rewrite EM; clear; lia) ltac:(rewrite EM; unfold M_MEM_A; clear; lia) MSH8) as X.
      rewrite EM in X |- *. replace (if M_MEM_A + 112 - (M_MEM_A + 80) <? 8 then M_MEM_A + 112 - (M_MEM_A + 80) else 0) with 0 in X by reflexivity. exact X.
    - pose proof (afp_gsh_byte RT GOBJ AFP Σ m M_SECMEM_A 112 (meth + 80) ART0 GO_secmeth ltac:(rewrite EM; clear; lia) ltac:(rewrite EM; unfold M_SECMEM_A; clear; lia) MSH8) as X.
      rewrite EM in X |- *. replace (if M_SECMEM_A + 112 - (M_SECMEM_A + 80) <? 8 then M_SECMEM_A + 112 - (M_SECMEM_A + 80) else 0) with 0 in X by reflexivity. exact X. }
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC0 & _ & _ & UT0).
  (* [comment removed for export] *)
  pose proof (bfr_s0_walk ra sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m meth BI lo nr nw
                ST ltac:(fold usp; clear - HLO; lia) ltac:(clear - NUM; lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia) SPA UT0 SHC0 METHA MSB0
                HD TL ACCB ltac:(clear - RBI; lia) BIAL BIHI ltac:(clear - RBI LOW; lia) ACCS MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a2x & a3x & j & j2 & m1 & -> & MU1 & WM1 & MI1 & FRW1 & FRI1 & ST1 & HD1 & TL1) & Hc1'). clear Hc1.
  fold usp in MU1, FRW1, FRI1, ST1, Hc1'. fold usp1 in FRI1, ST1, Hc1'.
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 usp1 ART0 ltac:(unfold usp1; clear - NUM; lia)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - apply acl_stack. unfold usp1, USTACK_TOP in *. clear - Hin NUM. lia.
    - apply (acl_live _ _ _ BI 128); [exact INBI | clear - Hin; lia]. }
  assert (A01 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> ~ (BI <= bv_unsigned x < BI + 128) ->
               bv_unsigned x < usp - 688 \/ usp <= bv_unsigned x -> m1 x = m x).
  { intros x Hx NB Hlt. apply MU1. cbn [outside]. clear - NB Hlt. lia. }
  assert (CLE1 : cl_env m1 (Z_to_bv 8 1) canary).
  { apply (cl_env_agree m m1 _ _ CLE). intros x Hx. destruct (STA _ (cl_cell_static _ Hx)) as (Hc & Hl & NB). exact (A01 x Hc NB ltac:(left; exact Hl)). }
  assert (SEC1 : sec_off m1).
  { apply (sec_off_agree m m1 SEC). intros x Hx. destruct (STA (bv_unsigned x) ltac:(rewrite Hx; apply client_static_intro; unfold SEC_INIT; clear; lia)) as (Hc & Hl & NB).
    exact (A01 x Hc NB ltac:(left; exact Hl)). }
  assert (AG01 : agree_on (fun x => usp <= x < USTACK_TOP) m m1).
  { intros x Hx. cbv beta in Hx. apply A01; [apply acl_stack; exact Hx | clear - Hx RBI NUM; lia | right; clear - Hx; lia]. }
  (* [comment removed for export] *)
  assert (SVW1 : rw_cells asegs m1 (usp - 16) [C8 s0; C8 ra]).
  { replace (usp - 16) with (usp + -32 + Z.of_nat (cells_size [CB 12 j; C4 (Z_to_bv 64 0)])) by (cbn [cells_size csize Nat.add]; clear; lia).
    exact (rw_cells_skip m1 (usp + -32) [CB 12 j; C4 (Z_to_bv 64 0)] [C8 s0; C8 ra] FRW1). }
  destruct (cl_chain_call (rt_cg RT Σ) FZ_BIO_FREE e_bio_free_inner SITE_bfw_inner m m1 ra s0 sp (Z_to_bv 64 (usp + -32)) outer CTX
              (proj1 CGB (SITE_bfw_inner, FZ_BIO_FREE) ltac:(unfold BFX_SITES; cbn [app In]; left; reflexivity))
              (proj2 CGB (SITE_bfw_inner, e_bio_free_inner) ltac:(unfold BFX_CALLS; cbn [app In]; left; reflexivity)) UWC AG01
              ltac:(fold usp; exact SVW1) ltac:(rewrite EU2; fold usp; clear; lia) SPT) as (CTXW & UWCW).
  fold usp in UWCW.
  assert (SVI1 : rw_cells asegs m1 (usp + -48) [C8 sp; C8 (Z_to_bv 64 SITE_bfw_inner)]).
  { replace (usp + -48) with (usp1 + Z.of_nat (cells_size [CB 8 j2; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; clear; lia).
    exact (rw_cells_skip m1 usp1 [CB 8 j2; C8 s3; C8 s2; C8 s1] [C8 sp; C8 (Z_to_bv 64 SITE_bfw_inner)] FRI1). }
  destruct (bf_chain2 (rt_cg RT Σ) e_mem_free SITE_bfi_destroy m1 m1 sp ra outer CTXW
              (proj1 CGB (SITE_bfi_destroy, e_bio_free_inner) ltac:(unfold BFX_SITES; cbn [app In]; right; left; reflexivity))
              (proj2 CGB (SITE_bfi_destroy, e_mem_free) ltac:(unfold BFX_CALLS; cbn [app In]; right; left; reflexivity))
              UWCW ltac:(intros x Hx; reflexivity) ltac:(fold usp; exact SVI1) ltac:(fold usp; clear - NUM HLO; lia) SPT) as (CTX1 & UWC1).
  fold usp in CTX1, UWC1. fold usp1 in UWC1.
  (* [comment removed for export] *)
  set (D := match k_d K with Some d => d | None => 0 end).
  set (DL := match k_d K with Some d => live_remove d (rt_live RT Σ) | None => rt_live RT Σ end).
  assert (DFACTS : rw_cells asegs m BM (bufmem_cells (bv_unsigned blw) D max (Z_to_bv 64 (msec meth)))
                   /\ bm_data_opt (rt_live RT Σ) BM D max /\ 0 <= max < 2 ^ 40 /\ D <> BB /\ D <> RP
                   /\ (k_d K = None /\ D = 0 \/ exists d, k_d K = Some d /\ D = d /\ In (d, max) (rt_live RT Σ) /\ d <> BM /\ 1 <= max)
                   /\ live_remove D (rt_live RT Σ) = DL /\ List.NoDup ([BI; BB; BM; RP] ++ match k_d K with Some d => [d] | None => [] end)).
  { unfold D, DL. destruct (k_d K) as [d|].
    - destruct MD as (junk & IND & MAXP & BMC & RPC & LJ & DC). pose proof (af_live_range RT AF Σ m d max ART0 IND) as Rd.
      pose proof (List.NoDup_remove_2 [BI; BB; BM; RP] [] d ND) as N5. rewrite app_nil_r in N5. cbn in N5.
      split; [unfold bufmem_cells; rewrite Z_to_bv_bv_unsigned; exact BMC|].
      split; [right; split; [exact IND|]; split; [clear - N5; intuition lia | clear - MAXP MAX; lia]|]. split; [clear - MAXP MAX; lia|].
      split; [clear - N5; intuition lia|]. split; [clear - N5; intuition lia|].
      split; [right; exists d; split; [reflexivity|]; split; [reflexivity|]; split; [exact IND|]; split; [clear - N5; intuition lia | clear - MAXP; lia]|].
      split; [reflexivity | exact ND].
    - destruct MD as (MAX0 & BMC & RPC). subst max.
      split; [unfold bufmem_cells; rewrite Z_to_bv_bv_unsigned; exact BMC|].
      split; [left; reflexivity|]. split; [clear; lia|]. split; [clear - RBB; lia|]. split; [clear - RRP; lia|].
      split; [left; split; reflexivity|]. split; [exact (live_remove_0 RT AF Σ m ART0) | exact ND]. }
  destruct DFACTS as (BMC & DOPT & HMAX & NDBB & NDR & DCASE & DLE & NDX).
  assert (ND4 : List.NoDup [BI; BB; BM; RP]) by exact (List.NoDup_app_remove_r _ _ NDX).
  pose proof ND4 as ND3. apply List.NoDup_cons_iff in ND3 as [N_BI ND3]. apply List.NoDup_cons_iff in ND3 as [N_BB ND3]. apply List.NoDup_cons_iff in ND3 as [N_BM' _].
  assert (N_BM : BM <> RP) by (intros X; apply N_BM'; left; exact (eq_sym X)). clear N_BM'.
  cbn in N_BI, N_BB.
  (* [comment removed for export] *)
  assert (KEEP1 : forall e, In e (rt_live RT Σ) -> fst e <> BB -> fst e <> RP -> fst e <> BM -> ~ In (fst e) (match k_d K with Some d => [d] | None => [] end) ->
                  In e (live_remove BB (live_remove RP (live_remove BM DL)))).
  { intros e He H1 H2 H3 H4. apply live_remove_keep; [| exact H1]. apply live_remove_keep; [| exact H2]. apply live_remove_keep; [| exact H3].
    unfold DL. destruct (k_d K) as [d|]; [apply live_remove_keep; [exact He | intros X; apply H4; left; exact (eq_sym X)] | exact He]. }
  (* [comment removed for export] *)
  unfold bio_head in HD1.
  assert (ADC1 : rw_cells asegs m1 (BI + 112) [C8 z64; C8 z64]).
  { replace (BI + 112) with (BI + 72 + Z.of_nat (cells_size [C8 z64; C8 z64; C4 (Z_to_bv 64 0); C4 z64; C8 nr; C8 nw])) by (cbn [cells_size csize Nat.add]; clear; lia).
    exact (rw_cells_skip m1 (BI + 72) [C8 z64; C8 z64; C4 (Z_to_bv 64 0); C4 z64; C8 nr; C8 nw] [C8 z64; C8 z64] TL1). }
  assert (P1B : forall x : word, (BI <= bv_unsigned x < BI + 88 \/ BB <= bv_unsigned x < BB + 16 \/ BM <= bv_unsigned x < BM + 32 \/ RP <= bv_unsigned x < RP + 32) -> m1 x = m x).
  { intros x Hx. apply MU1. cbn [outside].
    pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 INBI INBB ltac:(intros X; injection X as E1 E2; apply N_BI; left; exact (eq_sym E1))) as D1.
    pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 INBI INBM ltac:(intros X; injection X as E1 E2; apply N_BI; right; left; exact (eq_sym E1))) as D2.
    pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 INBI INRP ltac:(intros X; injection X as E1 E2; apply N_BI; right; right; left; exact (eq_sym E1))) as D3.
    clear - Hx D1 D2 D3 RBI RBB RBM RRP NUM. lia. }
  assert (BW1 : rw_cells asegs m1 (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB))).
  { apply (rw_cells_agree asegs m m1 _ _ BW); [| exact WM1]. intros x Hx. cbv beta in Hx. unfold bio_w1_cells in Hx. cbn [cells_size csize Nat.add] in Hx. apply P1B. clear - Hx. lia. }
  assert (BBC1 : rw_cells asegs m1 BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 RP)]).
  { apply (rw_cells_agree asegs m m1 _ _ BBC); [| exact WM1]. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply P1B. clear - Hx. lia. }
  assert (BMC1 : rw_cells asegs m1 BM (bufmem_cells (bv_unsigned blw) D max (Z_to_bv 64 (msec meth)))).
  { apply (rw_cells_agree asegs m m1 _ _ BMC); [| exact WM1]. intros x Hx. cbv beta in Hx. unfold bufmem_cells in Hx. cbn [cells_size csize Nat.add] in Hx. apply P1B. clear - Hx. lia. }
  assert (MSR : 0 <= msec meth < 2 ^ 64) by (unfold msec; destruct (meth =? M_SECMEM_A); clear; lia).
  (* [comment removed for export] *)
  assert (KONT : forall c2, (exists (Σ1 : rts RT) (v : word),
       ASTA RT Σ1 PMc (fun ms => exists m', ret_st (Z_to_bv 64 SITE_bfi_destroy) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) (Z_to_bv 64 (usp + -32)) (Z_to_bv 64 BI)
                                                (Z_to_bv 64 1) (Z_to_bv 64 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
           /\ rt_after_f RT Σ1 usp1 lo m1 m' /\ rt_pres (rt_live RT Σ1) (rt_frames RT Σ) usp1 m1 m' /\ cl_env m' (Z_to_bv 8 1) canary /\ sec_off m') c2
       /\ rt_live RT Σ1 = live_remove BB (live_remove RP (live_remove BM DL)) /\ rt_frames RT Σ1 = rt_frames RT Σ /\ rt_sp0 RT Σ1 = rt_sp0 RT Σ
       /\ rt_credit RT Σ1 = rt_credit RT Σ /\ rt_cg RT Σ1 = rt_cg RT Σ) -> realizes asegs c2 T).
  2: { (* [comment removed for export] *)
    assert (CALL1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo).
    { fold usp in SPA. unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK; lia|].
      split; [unfold USTACK_TOP in *; clear - NUM; lia|]. clear - SPA. Z.div_mod_to_equations. lia. }
    assert (HSTK1 : lo + RT_STACK + 144 <= bv_unsigned (Z_to_bv 64 usp1)) by (rewrite EU1; unfold usp1; clear - HSTK; lia).
    assert (CTX1' : cg_ctx (rt_cg RT Σ) e_mem_free (bv_unsigned (Z_to_bv 64 SITE_bfi_destroy) :: SITE_bfw_inner :: bv_unsigned ra :: outer))
      by (rewrite (unsigned_lit SITE_bfi_destroy) by (unfold SITE_bfi_destroy; clear; lia); exact CTX1).
    destruct DCASE as [(KDN & D0) | (d & KDS & Dd & IND & NDBM & MAX1)].
    - (* [comment removed for export] *)
      apply (C_MF Σ PMc (Z_to_bv 64 SITE_bfi_destroy) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 (Z_to_bv 64 (usp + -32)) (Z_to_bv 64 BI)
                 (Z_to_bv 64 BI) (Z_to_bv 64 e_mem_free) a2x a3x a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo
                 BI BB BM RP D (bv_unsigned blw) max fl (msec meth) rrw numw padw (SITE_bfw_inner :: bv_unsigned ra :: outer) (Z_to_bv 8 1) canary
                 FDO MST eq_refl eq_refl INBI BIAL BW1 FLOK INBB BBAL BBC1 INBM BMAL BMC1 MSR ltac:(left; exact D0) INRP
                 ltac:(clear - N_BM; exact N_BM) ltac:(clear - N_BB; intros X; apply N_BB; left; exact (eq_sym X)) ltac:(clear - N_BB; intros X; apply N_BB; right; left; exact (eq_sym X))
                 NDBB NDR DOPT HMAX ART1 MI1 CALL1 HSTK1 CTX1' UWC1 ltac:(apply (cg_has_weaken _ _ _ _ _ CGB); vm_compute; reflexivity) CLE1); [exact Hc1'|].
      intros c2 (Σ1 & v & Hc2 & LV1 & FRS1 & SP1 & CR1 & CG1). apply KONT. exists Σ1, v. rewrite <- DLE. split; [| exact (conj LV1 (conj FRS1 (conj SP1 (conj CR1 CG1))))].
      apply (ASTA_conseq RT Σ1 PMc _ _ c2 Hc2). intros ms (m2 & RS & AFT & PRES & CLE2). exists m2. rewrite EU1 in AFT, PRES.
      split; [exact RS|]. split; [exact AFT|]. split; [exact PRES|]. split; [exact CLE2|].
      apply (sec_off_agree m1 m2 SEC1). intros x Hx. apply PRES. right; left. apply client_static_intro. rewrite Hx. unfold SEC_INIT. clear; lia.
    - destruct METHA as [EM | EM].
      + (* [comment removed for export] *)
        assert (MS0 : msec meth = 0) by (rewrite EM; reflexivity).
        apply (C_MF Σ PMc (Z_to_bv 64 SITE_bfi_destroy) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 (Z_to_bv 64 (usp + -32)) (Z_to_bv 64 BI)
                   (Z_to_bv 64 BI) (Z_to_bv 64 e_mem_free) a2x a3x a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo
                   BI BB BM RP D (bv_unsigned blw) max fl (msec meth) rrw numw padw (SITE_bfw_inner :: bv_unsigned ra :: outer) (Z_to_bv 8 1) canary
                   FDO MST eq_refl eq_refl INBI BIAL BW1 FLOK INBB BBAL BBC1 INBM BMAL BMC1 MSR ltac:(right; rewrite MS0; reflexivity) INRP
                   ltac:(clear - N_BM; exact N_BM) ltac:(clear - N_BB; intros X; apply N_BB; left; exact (eq_sym X)) ltac:(clear - N_BB; intros X; apply N_BB; right; left; exact (eq_sym X))
                   NDBB NDR DOPT HMAX ART1 MI1 CALL1 HSTK1 CTX1' UWC1 ltac:(apply (cg_has_weaken _ _ _ _ _ CGB); vm_compute; reflexivity) CLE1); [exact Hc1'|].
        intros c2 (Σ1 & v & Hc2 & LV1 & FRS1 & SP1 & CR1 & CG1). apply KONT. exists Σ1, v. rewrite <- DLE. split; [| exact (conj LV1 (conj FRS1 (conj SP1 (conj CR1 CG1))))].
        apply (ASTA_conseq RT Σ1 PMc _ _ c2 Hc2). intros ms (m2 & RS & AFT & PRES & CLE2). exists m2. rewrite EU1 in AFT, PRES.
        split; [exact RS|]. split; [exact AFT|]. split; [exact PRES|]. split; [exact CLE2|].
        apply (sec_off_agree m1 m2 SEC1). intros x Hx. apply PRES. right; left. apply client_static_intro. rewrite Hx. unfold SEC_INIT. clear; lia.
      + (* [comment removed for export] *)
        assert (MS1 : msec meth = 1) by (rewrite EM; reflexivity).
        apply (C_MFS Σ PMc (Z_to_bv 64 SITE_bfi_destroy) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 (Z_to_bv 64 (usp + -32)) (Z_to_bv 64 BI)
                   (Z_to_bv 64 BI) (Z_to_bv 64 e_mem_free) a2x a3x a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo
                   BI BB BM RP D (bv_unsigned blw) max fl (msec meth) rrw numw padw (SITE_bfw_inner :: bv_unsigned ra :: outer) (Z_to_bv 8 1) canary
                   FDO MST eq_refl eq_refl INBI BIAL BW1 FLOK INBB BBAL BBC1 INBM BMAL BMC1 MSR ltac:(rewrite MS1; reflexivity) INRP
                   ltac:(clear - N_BM; exact N_BM) ltac:(clear - N_BB; intros X; apply N_BB; left; exact (eq_sym X)) ltac:(clear - N_BB; intros X; apply N_BB; right; left; exact (eq_sym X))
                   NDBB NDR ltac:(rewrite Dd; exact IND) ltac:(rewrite Dd; exact NDBM) ltac:(clear - MAX1 HMAX; lia) ART1 MI1 CALL1 HSTK1 CTX1' UWC1
                   ltac:(apply (cg_has_weaken _ _ _ _ _ CGB); vm_compute; reflexivity) CLE1 SEC1); [exact Hc1'|].
        intros c2 (Σ1 & v & Hc2 & LV1 & FRS1 & SP1 & CR1 & CG1). apply KONT. exists Σ1, v. rewrite <- DLE. split; [| exact (conj LV1 (conj FRS1 (conj SP1 (conj CR1 CG1))))].
        apply (ASTA_conseq RT Σ1 PMc _ _ c2 Hc2). intros ms (m2 & RS & AFT & PRES & CLE2 & SEC2). exists m2. rewrite EU1 in AFT, PRES.
        split; [exact RS|]. split; [exact AFT|]. split; [exact PRES|]. split; [exact CLE2| exact SEC2]. }
  intros c2 (Σ1 & v & Hc2 & LV1 & FRS1 & SP1 & CR1 & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & CLE2 & SEC2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite (ret_pc_even SITE_bfi_destroy) in Hc2' by (unfold SITE_bfi_destroy; clear; lia).
  (* [comment removed for export] *)
  assert (INBI1 : In (BI, 128) (rt_live RT Σ1)).
  { rewrite LV1. apply KEEP1; [exact INBI | | |  |]; cbn [fst]; [clear - N_BI; intuition | clear - N_BI; intuition | clear - N_BI; intuition |].
    destruct (k_d K) as [d|]; [| intros []]. pose proof (List.NoDup_remove_2 [BI; BB; BM; RP] [] d NDX) as N5. rewrite app_nil_r in N5. cbn in N5 |- *. clear - N5. intuition. }
  assert (NIN4 : forall y, ~ In y ([BI; BB; BM; RP] ++ match k_d K with Some d => [d] | None => [] end) ->
                 y <> BB /\ y <> RP /\ y <> BM /\ ~ In y (match k_d K with Some d => [d] | None => [] end)).
  { intros y NI. cbn [app In] in NI. split; [intros Ey; apply NI; right; left; exact (eq_sym Ey)|]. split; [intros Ey; apply NI; right; right; right; left; exact (eq_sym Ey)|].
    split; [intros Ey; apply NI; right; right; left; exact (eq_sym Ey)|]. intros X; apply NI. right; right; right; right. exact X. }
  assert (KEEPL : forall e, In e LBL -> In e (rt_live RT Σ1)).
  { intros e He. rewrite LV1. destruct (NIN4 _ (NINK _ He)) as (N1 & N2 & N3 & N4). exact (KEEP1 e (INCL _ He) N1 N2 N3 N4). }
  pose proof (KEEPL _ INLKL) as INLK1.
  assert (P12 : forall x : word, aclient (rt_live RT Σ1) (rt_frames RT Σ) usp1 (bv_unsigned x) -> m2 x = m1 x) by (intros x Hx; exact (PRES2 x Hx)).
  assert (HD2 : rw_cells asegs m2 BI [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 meth); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ HD1). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply P12. apply (acl_live _ _ _ BI 128); [exact INBI1 | clear - Hx; lia]. }
  assert (ADC2 : rw_cells asegs m2 (BI + 112) [C8 z64; C8 z64]).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ ADC1). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply P12. apply (acl_live _ _ _ BI 128); [exact INBI1 | clear - Hx; lia]. }
  assert (FRW2 : rw_cells asegs m2 (usp + -32) [CB 12 j; C4 (Z_to_bv 64 0); C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FRW1). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply P12. apply acl_stack. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  assert (FRI2 : rw_cells asegs m2 usp1 [CB 8 j2; C8 s3; C8 s2; C8 s1; C8 sp; C8 (Z_to_bv 64 SITE_bfw_inner)]).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FRI1). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply P12. apply acl_stack. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  assert (G2 : forall x : word, client_static (bv_unsigned x) -> m2 x = m x).
  { intros x Hs. destruct (STA _ Hs) as (Hc & Hl & NB). rewrite (P12 x ltac:(apply acl_static; exact Hs)). exact (A01 x Hc NB ltac:(left; exact Hl)). }
  assert (EST2 : exd_stat m2 kd LK) by (apply (exd_stat_agree m m2 kd LK EST); intros x Hx; exact (G2 x (exd_fp_static kd _ KD Hx))).
  assert (LKC2 : rw_cells asegs m2 LK (mutex_cells z64 z64)).
  { apply (rw_cells_agree_nw asegs m m2 _ _ LKC). intros x Hx. cbv beta in Hx. cbn [cells_size mutex_cells csize Nat.add] in Hx.
    rewrite (P12 x ltac:(apply (acl_live _ _ _ LK 40); [exact INLK1 | clear - Hx; lia])).
    apply A01; [apply (acl_live _ _ _ LK 40); [exact INLK | clear - Hx; lia] | clear - Hx DBL; lia | left; clear - Hx RLK NUM; lia]. }
  (* [comment removed for export] *)
  pose proof (bfr_s1_walk (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 (Z_to_bv 64 (usp + -32)) v b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 1) (Z_to_bv 64 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
                F2 fc2 m2 BI ltac:(clear - RBI; lia) ltac:(clear - RBI SP0R; unfold USTACK_TOP, STACK_WIN, SEGTOP_A in *; lia) MI2) as W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3.
  assert (AG02 : agree_on (fun x => usp + -32 <= x < USTACK_TOP) m1 m2) by (intros x Hx; cbv beta in Hx; apply P12; apply acl_stack; unfold usp1; clear - Hx; lia).
  assert (SVI2 : rw_cells asegs m2 (usp + -48) [C8 sp; C8 (Z_to_bv 64 SITE_bfw_inner)]).
  { replace (usp + -48) with (usp1 + Z.of_nat (cells_size [CB 8 j2; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; clear; lia).
    exact (rw_cells_skip m2 usp1 [CB 8 j2; C8 s3; C8 s2; C8 s1] [C8 sp; C8 (Z_to_bv 64 SITE_bfw_inner)] FRI2). }
  destruct (bf_chain2 (rt_cg RT Σ) e_free_ex_data_A SITE_bfi_freeex m1 m2 sp ra outer CTXW
              (proj1 CGB (SITE_bfi_freeex, e_bio_free_inner) ltac:(unfold BFX_SITES; cbn [app In]; right; right; left; reflexivity))
              (proj2 CGB (SITE_bfi_freeex, e_free_ex_data_A) ltac:(unfold BFX_CALLS; cbn [app In]; right; right; left; reflexivity))
              UWCW ltac:(fold usp; exact AG02) ltac:(fold usp; exact SVI2) ltac:(fold usp; clear - NUM HLO; lia) SPT) as (CTX2 & UWC2).
  fold usp in CTX2, UWC2. fold usp1 in UWC2. rewrite <- CG1 in CTX2.
  (* [comment removed for export] *)
  apply (C_FREEEX Σ1 PMc (Z_to_bv 64 SITE_bfi_freeex) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) u0 u1 u2 (Z_to_bv 64 (usp + -32)) (Z_to_bv 64 BI) (Z_to_bv 64 12) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 112))
           b3 b4 b5 b6 b7 (Z_to_bv 64 1) (Z_to_bv 64 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 lo (SITE_bfw_inner :: bv_unsigned ra :: outer)
           (Z_to_bv 8 1) canary kd LK (BI + 112) BI 128 FDO MST eq_refl eq_refl eq_refl ART2 MI2).
  { fold usp in SPA. unfold call_ok. rewrite EU1, SP1. split; [exact ST2|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK; lia|].
    split; [unfold USTACK_TOP in *; clear - NUM; lia|]. clear - SPA. Z.div_mod_to_equations. lia. }
  { rewrite EU1. unfold usp1, FREEEX_STACK. clear - HSTK. lia. }
  { rewrite (unsigned_lit SITE_bfi_freeex) by (unfold SITE_bfi_freeex; clear; lia). exact CTX2. }
  { exact UWC2. }
  { rewrite CG1. apply (cg_has_weaken _ _ _ _ _ CGB); vm_compute; reflexivity. }
  { rewrite FRS1. exact Hfr. }
  { rewrite CR1. exact Hcr. }
  { exact EST2. } { exact INLK1. } { exact LKC2. } { exact ADC2. }
  { clear - BIAL. Z.div_mod_to_equations. lia. }
  { exact INBI1. }
  { clear - BIAL. Z.div_mod_to_equations. lia. }
  { clear; lia. } { clear; lia. } { clear; lia. }
  { clear - DBL. lia. }
  { exact CLE2. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & Hc4 & LV2 & FRS2 & SP2 & CR2 & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (vx & m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & CLE3 & EST3 & ADC3 & LKC3) & Hc4'). clear Hc4.
  destruct RS3 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & ->).
  rewrite EU1 in ST3, PRES3. rewrite (ret_pc_even SITE_bfi_freeex) in Hc4' by (unfold SITE_bfi_freeex; clear; lia).
  assert (INBI2 : In (BI, 128) (rt_live RT Σ2)) by (rewrite LV2; exact INBI1).
  assert (P23S : forall x : word, usp1 <= bv_unsigned x < USTACK_TOP -> m3 x = m2 x).
  { intros x Hx. apply PRES3; [left; exact Hx|]. unfold NX_W. cbn [outside]. unfold usp1, USTACK_TOP in *. clear - Hx RBI RLK NUM. lia. }
  assert (FRW3 : rw_cells asegs m3 (usp + -32) [CB 12 j; C4 (Z_to_bv 64 0); C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m2 m3 _ _ FRW2). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply P23S. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  assert (FRI3 : rw_cells asegs m3 usp1 [CB 8 j2; C8 s3; C8 s2; C8 s1; C8 sp; C8 (Z_to_bv 64 SITE_bfw_inner)]).
  { apply (rw_cells_agree_nw asegs m2 m3 _ _ FRI2). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply P23S. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  (* [comment removed for export] *)
  pose proof (bfr_s2_walk (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 (Z_to_bv 64 (usp + -32)) vx d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 1) (Z_to_bv 64 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6
                F3 fc3 m3 BI MI3) as W2.
  cl_lift W2 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & -> & Hc5'). clear Hc5.
  assert (AG03 : agree_on (fun x => usp + -32 <= x < USTACK_TOP) m1 m3).
  { intros x Hx. cbv beta in Hx. rewrite (P23S x ltac:(unfold usp1; clear - Hx; lia)). apply P12. apply acl_stack. unfold usp1; clear - Hx; lia. }
  assert (SVI3 : rw_cells asegs m3 (usp + -48) [C8 sp; C8 (Z_to_bv 64 SITE_bfw_inner)]).
  { replace (usp + -48) with (usp1 + Z.of_nat (cells_size [CB 8 j2; C8 s3; C8 s2; C8 s1])) by (cbn [cells_size csize Nat.add]; unfold usp1; clear; lia).
    exact (rw_cells_skip m3 usp1 [CB 8 j2; C8 s3; C8 s2; C8 s1] [C8 sp; C8 (Z_to_bv 64 SITE_bfw_inner)] FRI3). }
  destruct (bf_chain2 (rt_cg RT Σ) e_CRYPTO_free SITE_bfi_cfree m1 m3 sp ra outer CTXW
              (proj1 CGB (SITE_bfi_cfree, e_bio_free_inner) ltac:(unfold BFX_SITES; cbn [app In]; right; right; right; left; reflexivity))
              (proj2 CGB (SITE_bfi_cfree, e_CRYPTO_free) ltac:(unfold BFX_CALLS; cbn [app In]; right; right; right; left; reflexivity))
              UWCW ltac:(fold usp; exact AG03) ltac:(fold usp; exact SVI3) ltac:(fold usp; clear - NUM HLO; lia) SPT) as (CTX3 & UWC3).
  fold usp in CTX3, UWC3. fold usp1 in UWC3. rewrite <- CG1, <- CG2 in CTX3.
  (* [comment removed for export] *)
  apply (C_FR Σ2 PMc (Z_to_bv 64 SITE_bfi_cfree) (Z_to_bv 64 usp1) gp (Z_to_bv 64 0xba3ef0) v0 v1 v2 (Z_to_bv 64 (usp + -32)) (Z_to_bv 64 BI) (Z_to_bv 64 BI) (Z_to_bv 64 BNX_FILE) (Z_to_bv 64 145)
           d3 d4 d5 d6 d7 (Z_to_bv 64 1) (Z_to_bv 64 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F3 fc3 m3 BI 128 lo (SITE_bfw_inner :: bv_unsigned ra :: outer)
           (Z_to_bv 8 1) canary FDO MST eq_refl eq_refl INBI2 ART3 MI3).
  { fold usp in SPA. unfold call_ok. rewrite EU1, SP2, SP1. split; [exact ST3|]. split; [exact LOW|]. unfold usp1. split; [unfold RT_STACK in *; clear - HSTK; lia|].
    split; [unfold USTACK_TOP in *; clear - NUM; lia|]. clear - SPA. Z.div_mod_to_equations. lia. }
  { rewrite (unsigned_lit SITE_bfi_cfree) by (unfold SITE_bfi_cfree; clear; lia). exact CTX3. }
  { exact UWC3. }
  { rewrite CG2, CG1. rewrite (unsigned_lit SITE_bfi_cfree) by (unfold SITE_bfi_cfree; clear; lia).
    exact (proj2 CGB (SITE_bfi_cfree, e_free) ltac:(unfold BFX_CALLS; cbn [app In]; right; right; right; right; left; reflexivity)). }
  { exact CLE3. }
  { exact Hc5'. }
  clear Hc5'. intros c6 (Σ3 & vf & Hc6 & LV3 & FRS3 & SP3 & CR3 & CG3).
  destruct (ASTA_unpack RT Σ3 _ _ c6 Hc6) as (ms6 & (m4 & RS4 & (ART4 & MI4 & ST4) & PRES4 & CLE4) & Hc6'). clear Hc6.
  destruct RS4 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_bfi_cfree) in Hc6' by (unfold SITE_bfi_cfree; clear; lia).
  assert (P34S : forall x : word, usp1 <= bv_unsigned x < USTACK_TOP -> m4 x = m3 x) by (intros x Hx; apply PRES4; left; exact Hx).
  assert (FRW4 : rw_cells asegs m4 (usp + -32) [CB 12 j; C4 (Z_to_bv 64 0); C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw asegs m3 m4 _ _ FRW3). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply P34S. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  assert (FRI4 : rw_cells asegs m4 usp1 [CB 8 j2; C8 s3; C8 s2; C8 s1; C8 sp; C8 (Z_to_bv 64 SITE_bfw_inner)]).
  { apply (rw_cells_agree_nw asegs m3 m4 _ _ FRI3). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply P34S. unfold usp1, USTACK_TOP in *. clear - Hx NUM. lia. }
  (* [comment removed for export] *)
  unfold usp1 in FRI4, ST4.
  pose proof (bfr_s3_walk ra sp gp (Z_to_bv 64 0xba3ef0) w0 w1 w2 vf g1 g2 g3 g4 g5 g6 g7 (Z_to_bv 64 1) (Z_to_bv 64 0x7fff8000) s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 s0 s1 s2 s3 F4 fc4 m4 BI lo j j2
                ltac:(fold usp; clear - HLO; lia) ltac:(clear - NUM; lia) ltac:(fold usp; unfold USTACK_TOP in *; clear - NUM; lia) FRW4 FRI4 ST4 MI4) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc6' c7 Hc7.
  (* [comment removed for export] *)
  apply Hk. exists Σ3.
  split; [| rewrite LV3, LV2, LV1, FRS3, FRS2, FRS1, SP3, SP2, SP1, CR3, CG3, CG2, CG1; split; [| split; [reflexivity | split; [reflexivity | split; [clear - CR2 CR1; lia | reflexivity]]]]].
  2: { unfold mbio_blocks, DL. rewrite <- EBI, <- EBM. fold BB RP. destruct (k_d K) as [d|]; cbn [live_remove_all app]; rewrite (live_remove_comm RP BM); reflexivity. }
  apply (ASTA_conseq RT Σ3 PMc _ _ c7 Hc7). intros ms (-> & ST7). fold usp in ST7. exists (Z_to_bv 64 1), m4.
  split; [exists w0, w1, w2, g1, g2, g3, g4, g5, g6, g7, w3, w4, w5, w6, F4, fc4; reflexivity|].
  split; [exact (conj ART4 (conj MI4 ST7))|].
  (* [comment removed for export] *)
  assert (KSUB1 : forall e, In e (live_remove_all (mbio_blocks K) (rt_live RT Σ)) -> In e (rt_live RT Σ1) /\ fst e <> BI).
  { intros e He. destruct (lra_sub _ _ _ He) as [He0 NI]. unfold mbio_blocks in NI. rewrite <- EBI, <- EBM in NI. fold BB RP in NI.
    split; [| intros Ey; apply NI; left; exact (eq_sym Ey)]. rewrite LV1. destruct (NIN4 _ NI) as (N1 & N2 & N3 & N4). exact (KEEP1 e He0 N1 N2 N3 N4). }
  assert (KSUB3 : forall e, In e (live_remove_all (mbio_blocks K) (rt_live RT Σ)) -> In e (rt_live RT Σ3)).
  { intros e He. destruct (KSUB1 e He) as [He1 NB]. rewrite LV3, LV2. apply live_remove_keep; [exact He1 | exact NB]. }
  assert (B4 : forall x : word, aclient (live_remove_all (mbio_blocks K) (rt_live RT Σ)) (rt_frames RT Σ) usp (bv_unsigned x) -> outside (lib_W LBL) (bv_unsigned x) -> m4 x = m x).
  { intros x Hx Ho.
    assert (HxL : aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x)).
    { apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; exact (proj1 (lra_sub _ _ _ He)) | auto | clear; lia]. }
    assert (NB : ~ (BI <= bv_unsigned x < BI + 128)).
    { intros HB. destruct (cl_split RT AF Σ m usp 688 _ ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) HxL) as [Hi|Lo]; [clear - Hi HB RBI NUM; lia|].
      destruct Hx as [H|[H|[H|[H|H]]]].
      - clear - H HB RBI NUM. lia.
      - pose proof (client_static_range _ H). unfold SEGTOP_A in *. clear - HB H0 BIHI. lia.
      - destruct H as (p & n & Hin & Hr). destruct (KSUB1 _ Hin) as [Hin1 NBp]. cbn [fst] in NBp.
        pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 (proj1 (lra_sub _ _ _ Hin)) INBI ltac:(intros X; injection X as E1 E2; exact (NBp E1))). clear - H HB Hr. lia.
      - destruct H as (f' & k' & Hin & Hr). pose proof (af_frames_range RT AF Σ m f' k' ART0 Hin) as (_ & _ & _ & PF). pose proof (PF _ _ INBI). clear - HB Hr H. lia.
      - destruct H as (f' & k' & Hin & Hr). pose proof (proj1 (af_fshadow_apart RT AF Σ m f' k' ART0 Hin) _ _ INBI). clear - HB Hr H. lia. }
    assert (HoL : ~ (LK + 4 <= bv_unsigned x < LK + 8)).
    { intros H8. unfold lib_W in Ho. exact (outside_mapD _ _ _ (proj2 (outside_appD _ _ _ Ho)) INLKL ltac:(cbn [fst snd]; clear - H8; lia)). }
    rewrite (PRES4 x ltac:(rewrite FRS2, FRS1; apply (aclient_mono _ _ _ _ _ _ _ Hx); [exact KSUB3 | auto | unfold usp1; clear; lia])).
    rewrite (PRES3 x ltac:(rewrite FRS1; apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; exact (proj1 (KSUB1 e He)) | auto | unfold usp1; clear; lia])
                     ltac:(unfold NX_W; cbn [outside]; clear - NB HoL; lia)).
    rewrite (P12 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [intros e He; exact (proj1 (KSUB1 e He)) | auto | unfold usp1; clear; lia])).
    destruct (cl_split RT AF Σ m usp 688 _ ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) HxL) as [Hi|Lo]; [exact (A01 x HxL NB ltac:(right; exact Hi)) | exact (A01 x HxL NB ltac:(left; exact Lo))]. }
  split; [exact B4|].
  split; [exact CLE4|].
  split; [reflexivity|].
  (* [comment removed for export] *)
  assert (G4 : forall x : word, client_static (bv_unsigned x) -> m4 x = m x).
  { intros x Hs. destruct (STA _ Hs) as (Hc & Hl & NB). pose proof (client_static_range _ Hs) as SR.
    rewrite (PRES4 x ltac:(right; left; exact Hs)). rewrite (PRES3 x ltac:(right; left; exact Hs) ltac:(unfold NX_W; cbn [outside]; unfold SEGTOP_A in SR; clear - SR BIHI LKHI; lia)).
    exact (G2 x Hs). }
  split.
  - apply (LCLOSE m4).
    + intros x Hfp HnL. destruct (libenv_fp_where LBL _ Hfp) as [(HW & HS & HC)|(p & n & Hin & Hr)]; [exact (G4 x HS)|].
      pose proof (INCL _ Hin) as HinL. pose proof (af_live_range RT AF Σ m p n ART0 HinL) as Rp. pose proof (KEEPL _ Hin) as Hin1.
      pose proof (NINK _ Hin) as NIp. cbn [fst app In] in NIp.
      assert (NB : ~ (BI <= bv_unsigned x < BI + 128)).
      { pose proof (live_in_disj RT AF Σ m _ _ _ _ ART0 HinL INBI ltac:(intros X; injection X as E1 E2; apply NIp; left; exact (eq_sym E1))). clear - H Hr. lia. }
      rewrite (PRES4 x ltac:(apply (acl_live _ _ _ p n); [rewrite LV3, LV2; apply live_remove_keep; [exact Hin1 | cbn [fst]; intros Ey; apply NIp; left; exact (eq_sym Ey)] | exact Hr])).
      rewrite (PRES3 x ltac:(apply (acl_live _ _ _ p n); [exact Hin1 | exact Hr]) ltac:(unfold NX_W; cbn [outside]; clear - NB HnL; lia)).
      rewrite (P12 x ltac:(apply (acl_live _ _ _ p n); [exact Hin1 | exact Hr])).
      apply A01; [apply (acl_live _ _ _ p n); [exact HinL | exact Hr] | exact NB | left; clear - Hr Rp NUM; lia].
    + apply (rw_cells_agree_nw asegs m3 m4 _ _ LKC3). intros x Hx. cbv beta in Hx. cbn [cells_size mutex_cells csize Nat.add] in Hx.
      apply PRES4. apply (acl_live _ _ _ LK 40); [| clear - Hx; lia]. rewrite LV3, LV2. apply live_remove_keep; [exact INLK1 | cbn [fst]; clear - DBL; lia].
  - apply (sec_off_agree m2 m4 SEC2). intros x Hx.
    assert (Hs : client_static (bv_unsigned x)) by (rewrite Hx; apply client_static_intro; unfold SEC_INIT; clear; lia). pose proof (client_static_range _ Hs) as SR.
    rewrite (PRES4 x ltac:(right; left; exact Hs)). apply PRES3; [right; left; exact Hs|]. unfold NX_W. cbn [outside]. unfold SEGTOP_A in SR. clear - SR BIHI LKHI. lia.
Qed.
End CBfree.
