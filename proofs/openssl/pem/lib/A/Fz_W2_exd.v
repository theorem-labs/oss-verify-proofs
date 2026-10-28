(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_T_ekit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_ukit Fz_env Th_mutex Fz_M_free Fz_T_lock Fz_W1_defs Fz_W3_iface Fz_W2_exdl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
Definition e_new_ex_data_ex : Z := 0x1f88a0.
Definition SITE_nx_smalloc : Z := 0x1f891c.
Definition SITE_nx_exg : Z := 0x1f89dc.
Definition SITE_nx_gal : Z := 0x1f89f0.
Definition SITE_nx_sknum : Z := 0x1f8a40.
Definition SITE_nx_unlock : Z := 0x1f8b04.
Definition SITE_nx_free : Z := 0x1f8d5c.
Definition J_nx_exit : Z := 0x1f8b10.
Definition SITE_nx_release : Z := 0x1f8bd0.
Definition NX_DESCR : Z := 0x262f4.
Definition W7_MAGIC_NX : Z := 0x41b58ab3.      (* [comment removed for export] *)
Definition W7_RETIRED_NX : Z := 0x45e0360e.    (* [comment removed for export] *)
Definition NX_GOT_SELF : Z := 0x5a5ba0.      (* [comment removed for export] *)
Definition EXD_FILE : Z := 0x494a0.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition nxb_frame (pd : Z) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : cell) (g1 g2 : list byte) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] ++ (if pd =? 0 then [] else [CB 8 g1; CB 8 g2])
  ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma nxb_blur8 : forall (m : mem) A pre w post, rw_cells asegs m A (pre ++ C8 w :: post) -> exists j, rw_cells asegs m A (pre ++ CB 8 j :: post).
Proof.
  intros m A pre w post H. destruct (proj1 (rw_cells_app m A pre (C8 w :: post)) H) as [H1 H2].
  pose proof (rw_cells_blur m _ [C8 w] post H2) as H3. cbn [cells_size csize Nat.add] in H3.
  eexists. apply (proj2 (rw_cells_app m A pre _)). split; [exact H1| exact H3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nx_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo pd : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1' a2' : word) (j0 j1 j2 j3 j4 j5 j6 j8 j9 j10 g1 g2 : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_nx_smalloc) (Z_to_bv 64 (bv_unsigned sp + -192 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -192 - pd))
                 (Z_to_bv 64 160) a1' a2' a3 a4 a5 a6 a7 s2 a3 a1 a0 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (e_stack_malloc 2)) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 208, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -192 - pd)
         (nxb_frame pd (CB 8 j0) (CB 8 j1) (CB 8 j2) (CB 8 j3) (CB 8 j4) (CB 8 j5) (CB 8 j6) (C8 a2) (CB 8 j8) (CB 8 j9) (CB 8 j10) g1 g2
                    s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ stk asegs m' lo (bv_unsigned sp + -192 - pd).

Lemma nx_s0_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo pd : Z),
  (pd = 0 \/ pd = 16) -> bv_unsigned sp mod 32 = pd ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)] -> mem_inv asegs m ->
  evt asegs (nx_s0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo pd m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_new_ex_data_ex) fc None m (seg_rom asegs)).
Proof.
  intros until pd. intros HP HPM ST HLO HLOS SPH UT SHC UAR MI. unfold e_new_ex_data_ex, g_shadow_memory_dynamic_address, g_detect_stack_use_after_return in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 208, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 208, SP)]) by ut_fp_lia.
  assert (LM : Z.land (SP + -192) 18446744073709551584 = SP + -192 - pd)
    by (apply land_m32_pad; [lia| replace (SP + -192) with (SP + (-6) * 32) by lia; rewrite Z.mod_add by lia; exact HPM]).
  destruct HP as [-> | ->].
  - (* [comment removed for export] *)
    th_frame 192%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
    zstep. zstep; lfix. do 13 zstep. zstep. zstep. rewrite LM. replace (SP + -192 - 0) with (SP + -192) in * by lia.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep; if_false. zstep. zstep.
    lazymatch goal with FRh : rw_cells asegs _ (SP + -192) (C8 ?z :: ?tl) |- _ => destruct (nxb_blur8 _ _ [] z tl FRh) as [jz FRz]; cbn [app] in FRz end.
    subst SP. rewrite ?Z_to_bv_bv_unsigned.
    unfold nx_s0_post, SITE_nx_smalloc, e_stack_malloc, nxb_frame; cbn [Z.eqb app].
    replace (bv_unsigned sp + -192 - 0) with (bv_unsigned sp + -192) by lia.
    apply evt_done; cbv beta; do 12 eexists; exists (@nil byte), (@nil byte); eexists; split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FRz| assumption].
  - (* [comment removed for export] *)
    th_frame 208%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
    zstep. zstep; lfix. do 13 zstep. zstep. zstep. rewrite LM. replace (SP + -192 - 16) with (SP + -208) in * by lia.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep; if_false. zstep. zstep.
    lazymatch goal with FRh : rw_cells asegs _ (SP + -208) (?ca :: ?cb :: C8 ?z :: ?tl) |- _ => destruct (nxb_blur8 _ _ [ca; cb] z tl FRh) as [jz FRz]; cbn [app] in FRz end.
    subst SP. rewrite ?Z_to_bv_bv_unsigned.
    unfold nx_s0_post, SITE_nx_smalloc, e_stack_malloc, nxb_frame; cbn [Z.eqb app].
    replace (bv_unsigned sp + -192 - 16) with (bv_unsigned sp + -208) by lia.
    apply evt_done; cbv beta; do 15 eexists; split; [reflexivity|].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FRz| assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nx_shadow_live : list cell :=
  map (fun z => C1 (Z_to_bv 8 z)) [-15; -15; -15; -15; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; -13; -13; -13; -13; -13; -13].
Definition nx_s1_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 obj : word) (ctx cls ad f lo pd : Z) (j0 j1 j2 j3 j4 j5 j6 j8 j9 g1 g2 fj sj : list byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists (jf sjr : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_nx_exg) (Z_to_bv 64 (bv_unsigned sp + -192 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -192 - pd))
                 (Z_to_bv 64 ctx) (Z_to_bv 64 NX_DESCR) (Z_to_bv 64 e_new_ex_data_ex) a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 ad) (Z_to_bv 64 cls) (Z_to_bv 64 ctx) (Z_to_bv 64 0x7fff8000)
                 (Z_to_bv 64 f) s8 s9 s10 (Z_to_bv 64 (f / 8 + 2147450880)) t3 t4 t5 t6)
            F (Z_to_bv 64 e_get_ex_data_global) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -192 - pd + 80, bv_unsigned sp + -192 - pd + 88); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 20)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -192 - pd)
         (nxb_frame pd (CB 8 j0) (CB 8 j1) (CB 8 j2) (CB 8 j3) (CB 8 j4) (CB 8 j5) (CB 8 j6) (C8 obj) (CB 8 j8) (CB 8 j9) (C8 (Z_to_bv 64 f)) g1 g2
                    e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 ra0)
    /\ stk asegs m' lo (bv_unsigned sp + -192 - pd)
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 W7_MAGIC_NX); C8 (Z_to_bv 64 NX_DESCR); C8 (Z_to_bv 64 e_new_ex_data_ex); CB 224 jf]
    /\ rw_cells asegs m' (f / 8 + 2147450880) (nx_shadow_live ++ [CB 12 sjr]).

Lemma nx_s1_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s7 s8 s9 s10 s11 t3 t4 t5 t6 (ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 obj : word)
    (F : bvmap 5 word) fc (m : mem) (ctx cls ad f lo pd : Z) (j0 j1 j2 j3 j4 j5 j6 j8 j9 j10 g1 g2 fj sj : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 256 <= lo -> (f + 256 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 208 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> 0 <= ctx < 2 ^ 64 -> 0 <= cls < 2 ^ 64 -> 0 <= ad < 2 ^ 64 ->
  img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -192 - pd)
    (nxb_frame pd (CB 8 j0) (CB 8 j1) (CB 8 j2) (CB 8 j3) (CB 8 j4) (CB 8 j5) (CB 8 j6) (C8 obj) (CB 8 j8) (CB 8 j9) (CB 8 j10) g1 g2
               e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 ra0) ->
  stk asegs m lo (bv_unsigned sp + -192 - pd) ->
  rw_cells asegs m f [CB 248 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 32 sj] -> mem_inv asegs m ->
  evt asegs (nx_s1_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 F fc ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 obj ctx cls ad f lo pd j0 j1 j2 j3 j4 j5 j6 j8 j9 g1 g2 fj sj m)
    (MS (mkR (Z_to_bv 64 SITE_nx_smalloc) (Z_to_bv 64 (bv_unsigned sp + -192 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -192 - pd))
             (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ad) (Z_to_bv 64 cls) (Z_to_bv 64 ctx) (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_nx_smalloc) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros HP F0 F64 FIMG FLO FSH HLO HLOS SPH CTX CLS AD UT FR ST FB SB MI. unfold SITE_nx_smalloc in *. unfold nxb_frame in FR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(SP + -192 - pd + 80, SP + -192 - pd + 88); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 20)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 32 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 32 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  apply (rw_cells_split_CB asegs _ f [] 248 fj [] [8; 8; 8; 224]%nat) in FB; [| reflexivity]. cbn [mk_CB_cells app] in FB.
  apply (rw_cells_split_CB asegs _ (f / 8 + 2147450880) [] 32 sj [] [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 12]%nat) in SB; [| reflexivity]. cbn [mk_CB_cells app] in SB.
  destruct HP as [-> | ->]; cbn [Z.eqb app] in FR.
  1: replace (SP + -192 - 0) with (SP + -192) in * by lia.
  2: replace (SP + -192 - 16) with (SP + -208) in * by lia.
  1: assert (HWU : ut_fp [(SP + -192 + 80, SP + -192 + 88); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 20)]) by (clear - F0 FIMG SHR HLO HLOS SPH FLO; ut_fp_lia).
  2: assert (HWU : ut_fp [(SP + -208 + 80, SP + -208 + 88); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 20)]) by (clear - F0 FIMG SHR HLO HLOS SPH FLO; ut_fp_lia).
  (* [comment removed for export] *)
  all: zstep; zstep; zstep; zstep; if_true.
  all: zstep.
  (* [comment removed for export] *)
  all: zstep; zstep; zstep; zstep; rewrite (shr3_div f) by lia.
  all: zstep; zstep; zstep.
  all: zstep; lfix. all: zstep; lfix. all: zstep; lfix.
  (* [comment removed for export] *)
  all: zstep; zstep.
  all: do 4 (zstep; lfix).
  all: zstep.
  all: do 2 (zstep; lfix).
  all: do 6 (zstep; lfix).
  all: do 8 (zstep; lfix).
  (* [comment removed for export] *)
  all: zstep; zstep.
  all: subst SP; rewrite ?Z_to_bv_bv_unsigned.
  all: unfold nx_s1_post, nxb_frame, nx_shadow_live, SITE_nx_exg, e_get_ex_data_global, W7_MAGIC_NX, NX_DESCR, e_new_ex_data_ex; cbn [Z.eqb map app].
  all: try replace (bv_unsigned sp + -192 - 0) with (bv_unsigned sp + -192) by lia.
  all: try replace (bv_unsigned sp + -192 - 16) with (bv_unsigned sp + -208) by lia.
  all: apply evt_done; cbv beta; do 3 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact FR|]; split; [eassumption|]; split; [exact FB| exact SB].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nx_s2_post (sp gp tp t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 obj : word) (cls AD LK f lo pd : Z) (j0 j1 j2 j3 j4 j8 j9 g1 g2 : list byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a3 a4 a5 a6 a7 : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_nx_free) (Z_to_bv 64 (bv_unsigned sp + -192 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -192 - pd))
                 (Z_to_bv 64 0) (Z_to_bv 64 EXD_FILE) (Z_to_bv 64 259) a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (Z_to_bv 64 SHB)
                 (Z_to_bv 64 f) (Z_to_bv 64 DC_IP12) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 DC_GLOBAL_LOCK) (Z_to_bv 64 (f / 8 + 2147450880)) t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_free) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 320, bv_unsigned sp - 104); (AD, AD + 16); (LK + 4, LK + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -192 - pd)
         (nxb_frame pd (CB 8 j0) (CB 8 j1) (CB 8 j2) (CB 8 j3) (CB 8 j4) (C8 (Z_to_bv 64 (f + 32))) (C8 (Z_to_bv 64 f)) (C8 obj)
                    (CB 8 j8) (CB 8 j9) (C8 (Z_to_bv 64 f)) g1 g2 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 ra0)
    /\ stk asegs m' lo (bv_unsigned sp + -192 - pd)
    /\ rw_cells asegs m' AD [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] /\ rw_cells asegs m' LK (mutex_cells z64 z64).

Lemma nx_s2a_walk : forall sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s8 s9 s10 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (cls AD f lo pd T kd sb : Z),
  (pd = 0 \/ pd = 16) -> lo <= bv_unsigned sp - 320 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  ro_cells asegs m DC_INITED [C1 (Z_to_bv 8 1)] -> ro_cells asegs m DC_KEY [C4 (Z_to_bv 64 kd)] -> 0 <= kd < 128 ->
  ro_cells asegs m (DC_KEY / 8 + 2147450880) [C1 (Z_to_bv 8 sb)] -> (sb = 0 \/ sb = 4) ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  ro_cells asegs m DC_ONCE1 [C4 (Z_to_bv 64 2)] -> ro_cells asegs m DC_RET1 [C4 (Z_to_bv 64 1)] ->
  ro_cells asegs m DC_ONCE2 [C4 (Z_to_bv 64 2)] -> ro_cells asegs m DC_RET2 [C4 (Z_to_bv 64 1)] ->
  ro_cells asegs m (bv_unsigned tp + -88) [C8 (Z_to_bv 64 T)] -> 88 <= bv_unsigned tp -> bv_unsigned tp <= lo -> 0 <= T ->
  ro_cells asegs m (T + 8 * kd) [C8 z64] -> T + 8 * kd + 8 <= lo ->
  stk asegs m lo (bv_unsigned sp + -192 - pd) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (t1' a1' a2' a3' : word) (m' : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_nx_exg) (Z_to_bv 64 (bv_unsigned sp + -192 - pd)) gp tp t0 t1' t2 sp (Z_to_bv 64 (bv_unsigned sp + -192 - pd))
                 (Z_to_bv 64 DC_GLOBAL_LOCK) a1' a2' a3' a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 AD) (Z_to_bv 64 cls) (Z_to_bv 64 0) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 f) s8 s9
                 s10 (Z_to_bv 64 (f / 8 + 2147450880)) t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_nx_exg) fc None m' (seg_rom asegs)
       /\ munch [(bv_unsigned sp + -192 - pd - 48, bv_unsigned sp + -192 - pd)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -192 - pd))
    (MS (mkR (Z_to_bv 64 SITE_nx_exg) (Z_to_bv 64 (bv_unsigned sp + -192 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -192 - pd))
             (Z_to_bv 64 0) (Z_to_bv 64 NX_DESCR) (Z_to_bv 64 e_new_ex_data_ex) a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 AD) (Z_to_bv 64 cls) (Z_to_bv 64 0) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 f) s8 s9
             s10 (Z_to_bv 64 (f / 8 + 2147450880)) t3 t4 t5 t6)
        F (Z_to_bv 64 e_get_ex_data_global) fc None m (seg_rom asegs)).
Proof.
  intros until sb. intros HP HLO HLOS SPH DCI DCK KD DCKS SB UT SHC O1 R1 O2 R2 TC TP1 TP2 T0 TK TKL ST MI.
  unfold SITE_nx_exg, DC_GLOBAL_LOCK, DC_INITED, DC_KEY, DC_ONCE1, DC_RET1, DC_ONCE2, DC_RET2, DC_CTX, e_get_ex_data_global, g_shadow_memory_dynamic_address, SHB in *.
  pose proof T_exg_proof as XG. unfold T_exg_stmt, DC_GLOBAL_LOCK, DC_INITED, DC_KEY, DC_ONCE1, DC_RET1, DC_ONCE2, DC_RET2, DC_CTX, e_get_ex_data_global, g_shadow_memory_dynamic_address, SHB in XG.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(SP + -192 - pd - 48, SP + -192 - pd)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct HP as [-> | ->].
  1: replace (SP + -192 - 0) with (SP + -192) in * by lia.
  2: replace (SP + -192 - 16) with (SP + -208) in * by lia.
  all: tcall (XG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo T kd sb).
  all: try (rewrite ?unsigned_lit by lia); try first [eassumption | lia].
  all: cbv beta delta [mkR].
  all: subst SP.
  all: try replace (bv_unsigned sp + -192 - 0) with (bv_unsigned sp + -192) by lia.
  all: try replace (bv_unsigned sp + -192 - 16) with (bv_unsigned sp + -208) by lia.
  all: apply evt_done; cbv beta; do 5 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
