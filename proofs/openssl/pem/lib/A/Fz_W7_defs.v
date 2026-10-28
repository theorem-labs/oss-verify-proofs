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
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition e_fuzz_one_body : Z := 0x1f30b0.
Definition SITE_w7_smalloc : Z := 0x1f3124.     (* [comment removed for export] *)
Definition SITE_w7_smem : Z := 0x1f3214.        (* [comment removed for export] *)
Definition SITE_w7_bnew : Z := 0x1f3218.        (* [comment removed for export] *)
Definition SITE_w7_write1 : Z := 0x1f3230.      (* [comment removed for export] *)
Definition SITE_w7_pem : Z := 0x1f3274.         (* [comment removed for export] *)
Definition SITE_w7_slen1 : Z := 0x1f328c.       (* [comment removed for export] *)
Definition SITE_w7_write2 : Z := 0x1f329c.
Definition SITE_w7_slen2 : Z := 0x1f32ac.       (* [comment removed for export] *)
Definition SITE_w7_write3 : Z := 0x1f32c0.
Definition SITE_w7_write4 : Z := 0x1f32d0.
Definition SITE_w7_free1 : Z := 0x1f32fc.  Definition SITE_w7_free2 : Z := 0x1f3310.  Definition SITE_w7_free3 : Z := 0x1f3320.
Definition SITE_w7_sfree1 : Z := 0x1f3338. Definition SITE_w7_sfree2 : Z := 0x1f334c. Definition SITE_w7_sfree3 : Z := 0x1f335c.
Definition SITE_w7_bfree : Z := 0x1f3364.       (* [comment removed for export] *)
Definition SITE_w7_eclear : Z := 0x1f3368.      (* [comment removed for export] *)
Definition J_w7_exit : Z := 0x1f3368.
Definition W7_MAGIC : Z := 0x41b58ab3.           (* [comment removed for export] *)
Definition W7_RETIRED : Z := 0x45e0360e.         (* [comment removed for export] *)
Definition W7_DESCR : Z := 0x12a2b.              (* [comment removed for export] *)
Definition W7_FILE : Z := 0x490a0.               (* [comment removed for export] *)
Definition A_BIO_s_mem : Z := 0x303e8c.   Definition A_BIO_new : Z := 0x236990.   Definition A_BIO_write : Z := 0x2375b4.
Definition A_BIO_free : Z := 0x2369b8.    Definition A_PEM_read_bio_ex : Z := 0x30c090.   Definition A_strlen_icpt : Z := 0x1ac568.
Definition A_CRYPTO_free : Z := 0x1fc430. Definition A_CRYPTO_secure_free : Z := 0x201f98.   Definition A_ERR_clear_error : Z := 0x1fd924.

(* [comment removed for export] *)
Definition W7_SITES_OWN : list (Z * Z) :=
  map (fun ra => (ra, e_fuzz_one_body))
      [SITE_w7_smalloc; SITE_w7_smem; SITE_w7_bnew; SITE_w7_write1; SITE_w7_pem; SITE_w7_slen1; SITE_w7_write2; SITE_w7_slen2; SITE_w7_write3;
       SITE_w7_write4; SITE_w7_free1; SITE_w7_free2; SITE_w7_free3; SITE_w7_sfree1; SITE_w7_sfree2; SITE_w7_sfree3; SITE_w7_bfree; SITE_w7_eclear].
Definition W7_CALLS_OWN : list (Z * Z) :=
  [(SITE_w7_smalloc, e_stack_malloc 2); (SITE_w7_smem, A_BIO_s_mem); (SITE_w7_bnew, A_BIO_new); (SITE_w7_write1, A_BIO_write);
   (SITE_w7_pem, A_PEM_read_bio_ex); (SITE_w7_slen1, A_strlen_icpt); (SITE_w7_write2, A_BIO_write); (SITE_w7_slen2, A_strlen_icpt);
   (SITE_w7_write3, A_BIO_write); (SITE_w7_write4, A_BIO_write); (SITE_w7_free1, A_CRYPTO_free); (SITE_w7_free2, A_CRYPTO_free);
   (SITE_w7_free3, A_CRYPTO_free); (SITE_w7_sfree1, A_CRYPTO_secure_free); (SITE_w7_sfree2, A_CRYPTO_secure_free); (SITE_w7_sfree3, A_CRYPTO_secure_free);
   (SITE_w7_bfree, A_BIO_free); (SITE_w7_eclear, A_ERR_clear_error)].

(* [comment removed for export] *)
Definition w7_shadow_live : list cell :=
  map (fun z => C1 (Z_to_bv 8 z)) [-15; -15; -15; -15; 0; -14; -14; -14; 0; -14; -14; -14; 0; -14; -14; -14; 0; -13; -13; -13].
Definition w7_shadow_dead : list cell :=
  map (fun z => C1 (Z_to_bv 8 z)) [-15; -15; -15; -15; -8; -14; -14; -14; -8; -14; -14; -14; -8; -14; -14; -14; -8; -13; -13; -13].
(* [comment removed for export] *)
Definition w7_fframe (j24 j40 j72 j104 j136 : list byte) (nm hd dt : word) (ol : cell) : list cell :=
  [C8 (Z_to_bv 64 W7_MAGIC); C8 (Z_to_bv 64 W7_DESCR); C8 (Z_to_bv 64 e_fuzz_one_body); CB 8 j24;
   C8 nm; CB 24 j40; C8 hd; CB 24 j72; C8 dt; CB 24 j104; ol; CB 112 j136].

(* [comment removed for export] *)
Definition w7_mframe7 (c0 c1 c2 c3 c4 c5 c6 : cell) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [c0; c1; c2; c3; c4; c5; c6; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition w7_mframe (c1 c2 c3 c4 c5 c6 : cell) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  w7_mframe7 (C8 (Z_to_bv 64 0)) c1 c2 c3 c4 c5 c6 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition w7_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo pd : Z) (m : mem) : machine_state -> Prop :=
  (* [comment removed for export] *)
  fun ms => exists (a1' a2' : word) (j1 j2 j3 j4 j5 j6 : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_w7_smalloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
                 (Z_to_bv 64 160) a1' a2' a3 a4 a5 a6 a7 s2 a0 s4 a1 s6 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (e_stack_malloc 2)) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -160) (w7_mframe (CB 8 j1) (CB 8 j2) (CB 8 j3) (CB 8 j4) (CB 8 j5) (CB 8 j6) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ stk asegs m' (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160)
    /\ stk asegs m' lo (bv_unsigned sp + -160 - pd).

Lemma w7_s0_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo pd : Z),
  (pd = 0 \/ pd = 16) -> bv_unsigned sp mod 32 = pd ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)] -> mem_inv asegs m ->
  evt asegs (w7_s0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo pd m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_fuzz_one_body) fc None m (seg_rom asegs)).
Proof.
  intros until pd. intros HP HPM ST HLO HLOS SPH UT SHC UAR MI. unfold e_fuzz_one_body, g_shadow_memory_dynamic_address, g_detect_stack_use_after_return in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 160, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 160, SP)]) by ut_fp_lia.
  th_frame 160%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST.
  (* [comment removed for export] *)
  zstep. zstep; lfix. do 13 zstep. zstep. zstep.
  rewrite (land_m32_pad (SP + -160) pd) by (first [lia | replace (SP + -160) with (SP + (-5) * 32) by lia; rewrite Z.mod_add by lia; exact HPM]).
  (* [comment removed for export] *)
  do 2 zstep. do 2 zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_false. do 2 zstep.
  destruct (stk_split asegs _ lo (SP + -160 - pd) (SP + -160) ST ltac:(lia)) as [ST1 GAP].
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold w7_s0_post, SITE_w7_smalloc, e_stack_malloc, w7_mframe, w7_mframe7. apply evt_done. do 9 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eassumption|]. split; [exact GAP| exact ST1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition J_w7_lentest : Z := 0x1f3208.
Definition w7_mframe1 (pd f : Z) (j1 j2 j3 j4 j5 j6 : list byte) : cell * cell * cell * cell * cell * cell :=
  if pd =? 0 then (CB 8 j1, CB 8 j2, CB 8 j3, CB 8 j4, CB 8 j5, C8 (Z_to_bv 64 f)) else (CB 8 j1, CB 8 j2, CB 8 j3, C8 (Z_to_bv 64 f), CB 8 j5, CB 8 j6).
Definition w7_s1_post (sp gp tp t0 t1 t2 a5 a6 a7 s4 s8 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (buf len f lo pd : Z) (j1 j2 j3 j4 j5 j6 fj sj : list byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j24 j40 j72 j104 jol j136 sjr : list byte) (m' : mem),
    let '(c1, c2, c3, c4, c5, c6) := w7_mframe1 pd f j1 j2 j3 j4 j5 j6 in
    ms = MS (mkR (Z_to_bv 64 SITE_w7_smalloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
                 (Z_to_bv 64 (len + -2147483648)) (Z_to_bv 64 (-2147483646)) (Z_to_bv 64 e_fuzz_one_body) (Z_to_bv 64 (-14)) (Z_to_bv 64 (-15)) a5 a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 buf) s4 (Z_to_bv 64 len) (Z_to_bv 64 (-8)) (Z_to_bv 64 0x7fff8000) s8 s9
                 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F (Z_to_bv 64 J_w7_lentest) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp - 104); (f, f + 104); (f / 8 + 2147450880, f / 8 + 2147450880 + 20)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -160) (w7_mframe c1 c2 c3 c4 c5 c6 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 ra0)
    /\ stk asegs m' (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160) /\ stk asegs m' lo (bv_unsigned sp + -160 - pd)
    /\ rw_cells asegs m' f (w7_fframe j24 j40 j72 j104 j136 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (CB 8 jol))
    /\ rw_cells asegs m' (f / 8 + 2147450880) (w7_shadow_live ++ [CB 12 sjr]).

Lemma w7_s1_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6
    (ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (F : bvmap 5 word) fc (m : mem) (buf len f lo pd : Z) (j1 j2 j3 j4 j5 j6 fj sj : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 256 <= lo -> (f + 256 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> 0 <= len < 2^31 ->
  img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -160) (w7_mframe (CB 8 j1) (CB 8 j2) (CB 8 j3) (CB 8 j4) (CB 8 j5) (CB 8 j6) e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 ra0) ->
  stk asegs m (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160) -> stk asegs m lo (bv_unsigned sp + -160 - pd) ->
  rw_cells asegs m f [CB 248 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 32 sj] -> mem_inv asegs m ->
  evt asegs (w7_s1_post sp gp tp t0 t1 t2 a5 a6 a7 s4 s8 s9 t3 t4 t5 t6 F fc ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 buf len f lo pd j1 j2 j3 j4 j5 j6 fj sj m)
    (MS (mkR (Z_to_bv 64 SITE_w7_smalloc) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
             (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 buf) s4 (Z_to_bv 64 len) s6 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_w7_smalloc) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros HP F0 F64 FIMG FLO FSH HLO HLOS SPH LEN UT FR GAP ST FB SB MI. unfold SITE_w7_smalloc in *. unfold w7_mframe, w7_mframe7 in FR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(SP - 128, SP - 104); (f, f + 104); (f / 8 + 2147450880, f / 8 + 2147450880 + 20)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 32 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 32 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (HWU : ut_fp [(SP - 128, SP - 104); (f, f + 104); (f / 8 + 2147450880, f / 8 + 2147450880 + 20)]) by (clear - F0 FIMG SHR HLO HLOS SPH FLO; ut_fp_lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  apply (rw_cells_split_CB asegs _ f [] 248 fj [] [8; 8; 8; 8; 8; 24; 8; 24; 8; 24; 8; 112]%nat) in FB; [| reflexivity]. cbn [mk_CB_cells app] in FB.
  apply (rw_cells_split_CB asegs _ (f / 8 + 2147450880) [] 32 sj [] [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 12]%nat) in SB; [| reflexivity]. cbn [mk_CB_cells app] in SB.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. if_true.
  (* [comment removed for export] *)
  destruct HP as [-> | ->].
  1: replace (SP + -160 - 0) with (SP + -160) in * by lia.
  2: replace (SP + -160 - 16) with (SP + -176) in * by lia.
  all: zstep.
  (* [comment removed for export] *)
  all: zstep; zstep; zstep; zstep; rewrite (shr3_div f) by lia.
  all: do 5 zstep.
  all: zstep; lfix. all: zstep; lfix. all: zstep; lfix.
  (* [comment removed for export] *)
  all: zstep; zstep.
  all: do 4 (zstep; lfix).
  all: zstep.
  all: do 4 (zstep; lfix).
  all: do 4 (zstep; lfix).
  all: do 4 (zstep; lfix).
  all: zstep.
  all: do 4 (zstep; lfix).
  (* [comment removed for export] *)
  all: zstep; zstep.
  all: do 3 (zstep; lfix; zstep; lfix).
  all: subst SP; rewrite ?Z_to_bv_bv_unsigned.
  all: unfold w7_s1_post, w7_mframe1, w7_mframe, w7_mframe7, w7_fframe, w7_shadow_live, J_w7_lentest, SITE_w7_smalloc, W7_MAGIC, W7_DESCR, e_fuzz_one_body; cbn [Z.eqb map app].
  all: try replace (bv_unsigned sp + -160 - 0) with (bv_unsigned sp + -160) by lia.
  all: try replace (bv_unsigned sp + -160 - 16) with (bv_unsigned sp + -176) by lia.
  all: apply evt_done; do 8 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact FR|]; split; [eassumption|]; split; [eassumption|]; split; [exact FB| exact SB].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SITE_w7_release : Z := 0x1f340c.      (* [comment removed for export] *)
Definition w7_shadow_retired : list cell := map (fun z => C1 (Z_to_bv 8 z)) (repeat (-11) 32).
Definition w7_x1_post (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (f pd : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ra1 : word) (m' : mem),
    ms = MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
                 (Z_to_bv 64 (-11)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 s5 (Z_to_bv 64 (-8)) s7 s8 s9 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_w7_release) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 32)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' f [C8 (Z_to_bv 64 W7_RETIRED)]
    /\ rw_cells asegs m' (f / 8 + 2147450880) w7_shadow_retired.

Lemma w7_x1_walk : forall ra1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (f lo pd : Z) (hj sj : list byte),
  (pd = 0 \/ pd = 16) -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0 < f -> 0xbc6000 <= f -> f + 256 <= lo -> (f + 256 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  stk asegs m lo (bv_unsigned sp + -160 - pd) ->
  rw_cells asegs m f [CB 8 hj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 32 sj] -> mem_inv asegs m ->
  evt asegs (w7_x1_post sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 t3 t4 t5 t6 F fc f pd m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 s5 (Z_to_bv 64 (-8)) s7 s8 s9 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6)
        F (Z_to_bv 64 J_w7_exit) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros HP HLO HLOS SPH F0 FIMG FLO FSH ST1 HDR SB MI. unfold J_w7_exit in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 32 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 32 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  apply (rw_cells_split_CB asegs _ (f / 8 + 2147450880) [] 32 sj [] (repeat 1%nat 32)) in SB; [| reflexivity]. cbn [repeat mk_CB_cells app] in SB.
  (* [comment removed for export] *)
  do 4 (zstep; lfix). zstep. zstep. zstep; lfix.
  zstep. if_cases KF; zify_cond KF; [exfalso; lia|].
  (* [comment removed for export] *)
  zstep. do 32 (zstep; lfix).
  subst SP.
  unfold w7_x1_post, SITE_w7_release, W7_RETIRED, w7_shadow_retired. cbn [repeat map]. apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition w7_x2_post (ra0 sp gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (F : bvmap 5 word) (fc : bv 32)
    (fl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 e0 e1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)].

Lemma w7_x2_walk : forall ra1 ra0 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6
    (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (F : bvmap 5 word) fc (m : mem) (f fl lo pd : Z) (lowj : list byte),
  (pd = 0 \/ pd = 16) -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0 < f -> f + 256 <= lo -> 0 < fl -> fl + 1 <= lo ->
  stk asegs m lo (bv_unsigned sp + -160 - pd) -> stk asegs m (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160) ->
  rw_cells asegs m (bv_unsigned sp + -160) [CB 56 lowj; C8 e11; C8 e10; C8 e9; C8 e8; C8 e7; C8 e6; C8 e5; C8 e4; C8 e3; C8 e2; C8 e1; C8 e0; C8 ra0] ->
  ro_cells asegs m (f + 248) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (w7_x2_post ra0 sp gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F fc fl lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 f) t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_w7_release) fc None m (seg_rom asegs)).
Proof.
  intros until lowj. intros HP HLO HLOS SPH F0 FLO FL0 FLLO ST1 GAP FR FLG FLB MI. unfold SITE_w7_release in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUfl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  zstep. clear FLG. zstep; lfix. zstep. zstep. zstep.
  (* [comment removed for export] *)
  do 13 zstep.
  pose proof (stk_merge asegs _ lo (SP + -160 - pd) (SP + -160) ST1 GAP ltac:(lia)) as ST2.
  zstep. release_frame FR ST2 SP. zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold w7_x2_post. apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.

(* [comment removed for export] *)
Lemma sxb_small : forall b : byte, bv_unsigned b < 128 -> sxb b = Z_to_bv 64 (bv_unsigned b).
Proof.
  intros b Hb. unfold sxb, bv_signed. f_equal. pose proof (bv_unsigned_in_range 8 b) as R. apply bv_swrap_small.
  unfold bv_half_modulus, bv_modulus in *. cbn [Z.of_N Z.pow_pos Pos.iter Z.mul Z.div Z.pos_div_eucl] in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition w7_mframe2 (pd f : Z) (j1 j2 j3 j4 j5 j6 : list byte) : cell * cell * cell * cell * cell * cell :=
  if pd =? 0 then (CB 8 j1, CB 8 j2, C8 (Z_to_bv 64 (f + 64)), CB 8 j4, CB 8 j5, C8 (Z_to_bv 64 f))
  else (C8 (Z_to_bv 64 (f + 64)), CB 8 j2, CB 8 j3, C8 (Z_to_bv 64 f), CB 8 j5, CB 8 j6).
Definition w7_s2_post (sp gp tp t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (b0 : byte) (buf BI f pd : Z) (j1 j2 j3 j4 j5 j6 : list byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    let '(c1, c2, c3, c4, c5, c6) := w7_mframe2 pd f j1 j2 j3 j4 j5 j6 in
    ms = MS (mkR (Z_to_bv 64 SITE_w7_pem) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
                 (Z_to_bv 64 BI) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 64)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 128)) (Z_to_bv 64 (bv_unsigned b0)) a6 a7
                 (Z_to_bv 64 f) (Z_to_bv 64 buf) (Z_to_bv 64 BI) (Z_to_bv 64 (buf / 8 + 2147450880)) (Z_to_bv 64 (-8)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 128)) (Z_to_bv 64 (f + 96))
                 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6)
            F (Z_to_bv 64 A_PEM_read_bio_ex) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 152, bv_unsigned sp - 128)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -160) (w7_mframe c1 c2 c3 c4 c5 c6 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 ra0)
    /\ stk asegs m' (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160).

Lemma w7_s2_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6
    (ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word) (b0 : byte) (bsr : list byte) (F : bvmap 5 word) fc (m : mem) (buf len BI f lo pd p n : Z) (j1 j2 j3 j4 j5 j6 : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> 0xbc6000 <= f -> f + 256 <= lo -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  2 <= len < 2^31 -> 0 < p -> p <= buf -> buf + 1 <= p + n -> p + n <= lo -> acc asegs m p n -> bytes_at asegs m buf (b0 :: bsr) ->
  (let '(c1, c2, c3, c4, c5, c6) := w7_mframe1 pd f j1 j2 j3 j4 j5 j6 in
   rw_cells asegs m (bv_unsigned sp + -160) (w7_mframe c1 c2 c3 c4 c5 c6 e11 e10 e9 e8 e7 e6 e5 e4 e3 e2 e1 e0 ra0)) ->
  stk asegs m (bv_unsigned sp + -160 - pd) (bv_unsigned sp + -160) -> mem_inv asegs m ->
  evt asegs (w7_s2_post sp gp tp t0 t1 t2 a6 a7 t3 t4 t5 t6 F fc ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 b0 buf BI f pd j1 j2 j3 j4 j5 j6 m)
    (MS (mkR (Z_to_bv 64 SITE_w7_write1) (Z_to_bv 64 (bv_unsigned sp + -160 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -160 - pd))
             (Z_to_bv 64 (len + -1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 buf) (Z_to_bv 64 BI) (Z_to_bv 64 (len + -1)) (Z_to_bv 64 (-8)) (Z_to_bv 64 0x7fff8000) s8 s9
             (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_w7_write1) fc None m (seg_rom asegs)).
Proof.
  intros until j6. intros HP F0 FIMG FLO HLO HLOS SPH LEN P0 PB BP PN ACC BS FR GAP MI. unfold SITE_w7_write1 in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(SP - 152, SP - 128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HSH : sh_fp [(SP - 152, SP - 128)]) by (clear - HLO HLOS; sh_fp_lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUb : bv_unsigned (Z_to_bv 64 buf) = buf) by (apply unsigned_lit; lia).
  pose proof (bytes_at_read asegs m buf (b0 :: bsr) 0 1 BS ltac:(lia) ltac:(cbn; lia)) as RD.
  replace (firstn 1 (skipn (Z.to_nat 0) (b0 :: bsr))) with [b0] in RD by reflexivity. replace (buf + 0) with buf in RD by lia.
  (* [comment removed for export] *)
  destruct (ACC (buf - p) ltac:(lia)) as (sb & SHB0 & SOK). replace (p + (buf - p)) with buf in SHB0, SOK by lia. unfold shad, SHB in SHB0. unfold sh_ok in SOK.
  pose proof (bytes_at_read asegs m (buf / 8 + 2147450880) [sb] 0 1 SHB0 ltac:(lia) ltac:(cbn; lia)) as RDs.
  replace (firstn 1 (skipn (Z.to_nat 0) [sb])) with [sb] in RDs by reflexivity.
  replace (buf / 8 + 2147450880 + 0) with (buf / 8 + 2147450880) in RDs by lia.
  pose proof (bv_unsigned_in_range 8 sb) as SBR. unfold bv_modulus in SBR. cbn [Z.of_N Z.pow_pos Pos.iter Z.mul] in SBR.
  assert (L7 : Z.land buf 7 = buf mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
  unfold w7_mframe1, w7_mframe, w7_mframe7 in FR.
  destruct HP as [-> | ->]; cbn [Z.eqb] in FR.
  1: replace (SP + -160 - 0) with (SP + -160) in * by lia.
  2: replace (SP + -160 - 16) with (SP + -176) in * by lia.
  (* [comment removed for export] *)
  all: zstep; if_false.
  all: zstep; rewrite (shr3_div buf) by lia; zstep.
  all: zstep; rewrite (sxb_small sb) by (clear - SOK SBR; lia).
  all: zstep; if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by (clear - SBR; lia);
       [zstep; zstep; if_cases KT; zify_cond KT;
        [| exfalso; rewrite L7, !bv_signed_small in KT by (rewrite unsigned_lit by (clear - SBR EUb; Z.div_mod_to_equations; lia); clear - SBR EUb; Z.div_mod_to_equations; lia);
           rewrite !unsigned_lit in KT by (clear - SBR EUb; Z.div_mod_to_equations; lia); clear - KS KT SOK; lia] |].
  (* [comment removed for export] *)
  all: zstep; zstep; zstep; zstep; zstep; zstep; zstep.
  all: zstep.
  (* [comment removed for export] *)
  all: zstep; zstep; zstep.
  all: subst SP; unfold w7_s2_post, w7_mframe2, w7_mframe, w7_mframe7, SITE_w7_pem, A_PEM_read_bio_ex; cbn [Z.eqb]; unfold zxb.
  all: try replace (bv_unsigned sp + -160 - 0) with (bv_unsigned sp + -160) by lia.
  all: try replace (bv_unsigned sp + -160 - 16) with (bv_unsigned sp + -176) by lia.
  all: apply evt_done; eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; assumption.
Qed.
