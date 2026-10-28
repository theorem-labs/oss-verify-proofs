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
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_G_pkit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout Th_mutex I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Fz_M_locknew Fz_G_OPENSSL_sk_new_null Fz_G_OPENSSL_sk_set_cmp_thunks Fz_G_OPENSSL_sk_set_copy_thunks Fz_G_OPENSSL_sk_set_thunks Fz_I2_htw Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tslia ::= wp_tslia.
Notation TP_A := (0xba3ef0)%Z (only parsing).
Local Ltac zgo p := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; lfix
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ifF | ifT | ubs_if] end).
Local Ltac zsh := cbv beta; try change (bv_unsigned (Z_to_bv 8 0)) with 0; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
Lemma rw_cells_blur_all' : forall (m : mem) A cs, rw_cells asegs m A cs -> rw_cells asegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof. intros m A cs H. apply (rw_cells_blur m A cs []). rewrite app_nil_r. exact H. Qed.

Definition e_namemap_new : Z := 0x2181cc.
Definition SITE_nm_smalloc : Z := 0x21822c.
Definition SITE_nm_memset : Z := 0x2182e4.
Definition SITE_nm_zalloc : Z := 0x218314.
Definition SITE_nm_locknew : Z := 0x218320.
Definition SITE_nm_htnew : Z := 0x218344.
Definition SITE_nm_sknew : Z := 0x218364.
Definition SITE_nm_cmp : Z := 0x218378.
Definition SITE_nm_copy : Z := 0x218388.
Definition SITE_nm_set : Z := 0x218398.
Definition SITE_nm_release : Z := 0x218430.
Definition NM_CMP_THUNK : Z := 0x21a048.
Definition NM_COPY_THUNK : Z := 0x21a074.
Definition NM_SET_THUNK : Z := 0x21a020.
(* [comment removed for export] *)
Definition nm_shadow : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15));
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))].

(* [comment removed for export] *)
Definition nm_w0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1' a2' : word) (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_nm_smalloc) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 (Z_to_bv 64 128) a1' a2' a3 a4 a5 a6 a7 s2 a0 s4 s5 s6 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (e_stack_malloc 1)) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 24 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' (bv_unsigned sp + -96 - pad) (bv_unsigned sp + -96)
    /\ stk asegs m' lo (bv_unsigned sp + -96 - pad).

Lemma nm_w0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo pad : Z),
  (pad = 0 \/ pad = 16) -> bv_unsigned sp mod 32 = pad ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 112 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)] -> mem_inv asegs m ->
  evt asegs (nm_w0_post ra sp gp tp t0 t1 t2 s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo pad m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_namemap_new) fc None m (seg_rom asegs)).
Proof.
  intros until pad. intros HP HPM ST HLO HLOS SPH UT SHC UAR MI. unfold e_namemap_new, g_shadow_memory_dynamic_address, g_detect_stack_use_after_return in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 96, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 96, SP)]) by ut_fp_lia.
  carve_frame 96%nat ST.
  zgo 0x218200.
  rewrite (land_m32_pad (SP + -96) pad) by (first [lia | replace (SP + -96) with (SP + (-3) * 32) by lia; rewrite Z.mod_add by lia; exact HPM]).
  zgo 0x218220. zstep. if_false. zgo 0x1a6530.
  destruct (stk_split asegs _ lo (SP + -96 - pad) (SP + -96) ST ltac:(lia)) as [ST1 GAP].
  lazymatch goal with FRH : rw_cells asegs ?mm (SP + -96) (?c1 :: ?c2 :: ?rest) |- _ =>
    pose proof (rw_cells_blur mm (SP + -96) [c1; c2] rest FRH) as FRB end.
  cbn [cells_size csize Nat.add] in FRB.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold nm_w0_post, SITE_nm_smalloc, e_stack_malloc. apply evt_done. do 4 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FRB|]. split; [exact GAP| exact ST1].
Qed.
(* [comment removed for export] *)
Definition nm_w1_post (sp gp tp t0 t1 t2 s3 s4 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' : word) (F : bvmap 5 word) (fc : bv 32) (f lo pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j fj : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_nm_memset) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 (Z_to_bv 64 (f + 40)) (Z_to_bv 64 0) (Z_to_bv 64 40) a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_asan_memset) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 120); (f / 8 + 2147450880, f / 8 + 2147450880 + 16); (bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 24 j; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0]
    /\ rw_cells asegs m' f [CB 120 fj]
    /\ rw_cells asegs m' (f / 8 + 2147450880) nm_shadow.

Lemma nm_w1 : forall ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    (s0' s1' s2' s3' s4' s5' s6' s7' : word) (F : bvmap 5 word) fc (m : mem) (f lo pad : Z) (j fj sj : list byte),
  (pad = 0 \/ pad = 16) -> 0 < f -> f + 128 <= 2^47 ->
  (f + 120 <= 0x10000 \/ 0xbc6000 <= f) -> (f + 128 <= 0x7fff8000 \/ 0x10007fff8000 <= f) -> 0x10007fff8000 <= bv_unsigned sp - 112 -> bv_unsigned sp <= 2^47 ->
  (f + 128 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= f) ->
  img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 24 j; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  rw_cells asegs m f [CB 120 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 16 sj] -> mem_inv asegs m ->
  evt asegs (nm_w1_post sp gp tp t0 t1 t2 s3 s4 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra0 s0' s1' s2' s3' s4' s5' s6' s7' F fc f lo pad m)
    (MS (mkR (Z_to_bv 64 SITE_nm_smalloc) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_nm_smalloc) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros HP F0 FH FIMG FSH SPL SPH FSEP UT FR FB SB MI. unfold SITE_nm_smalloc in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(f, f + 120); (f / 8 + 2147450880, f / 8 + 2147450880 + 16); (SP - 96, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 16 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 16 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (HWU : ut_fp [(f, f + 120); (f / 8 + 2147450880, f / 8 + 2147450880 + 16); (SP - 96, SP)]) by ut_fp_lia.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  pose proof (div8_facts f) as Q1.
  zgo 0x21823c. zstep. if_true.
  destruct HP as [-> | ->].
  1: replace (SP + -96 - 0) with (SP + -96) by lia.
  2: replace (SP + -96 - 16) with (SP + -112) by lia.
  all: zgo 0x218270.
  all: rewrite (shr3_div f) by lia.
  all: zgo 0x1c1dbc.
  1: replace (SP + -96) with (SP + -96 - 0) by lia.
  2: replace (SP + -112) with (SP + -96 - 16) by lia.
  all: pose proof (rw_cells_blur _ _ [_; _] _ FR) as FRB; cbn [cells_size csize Nat.add app] in FRB.
  all: pose proof (rw_cells_blur_all' _ _ _ FB) as FBB; cbn [cells_size csize Nat.add app] in FBB.
  all: subst; rewrite ?Z_to_bv_bv_unsigned.
  all: unfold nm_w1_post, SITE_nm_memset, e_asan_memset, nm_shadow; apply evt_done; do 3 eexists; (split; [reflexivity|]).
  all: (split; [assumption|]); (split; [assumption|]); (split; [assumption|]); (split; [exact FRB|]); (split; [exact FBB| exact SB]).
Qed.
(* [comment removed for export] *)
Definition nm_conf0 (ctx : word) : list cell :=
  [C8 ctx; CB 16 (repeat (Z_to_bv 8 0) 16); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 4294967297); CB 8 (repeat (Z_to_bv 8 0) 8)].

Definition nm_w2_post (sp gp tp s3 s4 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (f lo pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_nm_zalloc) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 (Z_to_bv 64 40) (Z_to_bv 64 0x4c680) (Z_to_bv 64 535) a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_zalloc) fc None m' (seg_rom asegs)
    /\ munch [(f + 32, f + 80)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (f + 32) (nm_conf0 s3).

Lemma nm_w2 : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f lo pad : Z) (j32 : list byte),
  0 < f -> 0xbc6000 <= f -> f + 128 <= 2^47 ->
  rw_cells asegs m (f + 32) [CB 8 j32; CB 40 (repeat (Z_to_bv 8 0) 40)] -> mem_inv asegs m ->
  evt asegs (nm_w2_post sp gp tp s3 s4 s8 s9 s10 s11 F fc f lo pad m)
    (MS (mkR (Z_to_bv 64 SITE_nm_memset) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_nm_memset) fc None m (seg_rom asegs)).
Proof.
  intros until j32. intros F0 FIMG FH FC MI. unfold SITE_nm_memset in *.
  pose proof (munch_refl [(f + 32, f + 80)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  apply (rw_cells_split_CB asegs _ _ [_] 40 _ [] [16; 8; 8; 8]%nat) in FC; [| reflexivity]. cbn [mk_CB_cells app firstn skipn repeat] in FC.
  zgo 0x1fbfec.
  unfold nm_w2_post, SITE_nm_zalloc, e_CRYPTO_zalloc, nm_conf0. apply evt_done. do 13 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [assumption|]. split; [assumption|].
  lazymatch goal with |- rw_cells _ ?mm _ _ => apply (rw_cells_recast mm (f + 32) _ _ FC); [cbn; repeat first [exact I | reflexivity | split] | reflexivity] end.
Qed.
(* [comment removed for export] *)
Definition nm_w3_post (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (f nm pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms =>
    ms = MS (mkR (Z_to_bv 64 SITE_nm_locknew) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 (Z_to_bv 64 nm) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 nm) s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_lock_new) fc None m (seg_rom asegs).

Lemma nm_w3 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f nm pad : Z),
  0 < nm -> nm < 2^64 -> mem_inv asegs m ->
  evt asegs (nm_w3_post sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s8 s9 s10 s11 t3 t4 t5 t6 F fc f nm pad m)
    (MS (mkR (Z_to_bv 64 SITE_nm_zalloc) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 nm) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_nm_zalloc) fc None m (seg_rom asegs)).
Proof.
  intros until pad. intros N0 NH MI. unfold SITE_nm_zalloc in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUn : bv_unsigned (Z_to_bv 64 nm) = nm) by (apply unsigned_lit; lia).
  zgo 0x1f5e3c.
  unfold nm_w3_post, SITE_nm_locknew, e_lock_new. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition nm_w4_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s4 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (f nm lk pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_nm_htnew) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (nm + 16)) (Z_to_bv 64 0) a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 nm) s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_ht_new) fc None m' (seg_rom asegs)
    /\ munch [(nm + 16, nm + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' nm [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Lemma nm_w4 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f nm lk pad : Z),
  0 < f -> f + 128 <= 2^47 -> 0x10007fff8000 <= nm -> nm + 40 <= 2^47 -> nm mod 8 = 0 -> 0 < lk -> lk < 2^64 ->
  rw_cells asegs m nm [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> acc asegs m nm 40 -> mem_inv asegs m ->
  evt asegs (nm_w4_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s4 s8 s9 s10 s11 t3 t4 t5 t6 F fc f nm lk pad m)
    (MS (mkR (Z_to_bv 64 SITE_nm_locknew) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 lk) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 nm) s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_nm_locknew) fc None m (seg_rom asegs)).
Proof.
  intros until pad. intros F0 FH NMH NMT NMA LK0 LKH HN ACn MI. unfold SITE_nm_locknew in *.
  pose proof (munch_refl [(nm + 16, nm + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 nm) = nm) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 lk) = lk) by (apply unsigned_lit; lia).
  zgo 0x218330. zsh. zgo 0x21a09c.
  unfold nm_w4_post, SITE_nm_htnew, e_ht_new. apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [assumption|]. split; [assumption| exact HN].
Qed.
(* [comment removed for export] *)
Definition nm_w5_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s4 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (f nm lk ht pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_nm_sknew) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 (Z_to_bv 64 ht) (Z_to_bv 64 (nm + 8)) (Z_to_bv 64 0) a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 nm) s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_OPENSSL_sk_new_null) fc None m' (seg_rom asegs)
    /\ munch [(nm + 8, nm + 16)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' nm [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 ht); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Lemma nm_w5 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f nm lk ht pad : Z),
  0 < f -> f + 128 <= 2^47 -> 0x10007fff8000 <= nm -> nm + 40 <= 2^47 -> nm mod 8 = 0 -> 0 < ht -> ht < 2^64 ->
  rw_cells asegs m nm [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> acc asegs m nm 40 -> mem_inv asegs m ->
  evt asegs (nm_w5_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s4 s8 s9 s10 s11 t3 t4 t5 t6 F fc f nm lk ht pad m)
    (MS (mkR (Z_to_bv 64 SITE_nm_htnew) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 ht) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 nm) s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_nm_htnew) fc None m (seg_rom asegs)).
Proof.
  intros until pad. intros F0 FH NMH NMT NMA HT0 HTH HN ACn MI. unfold SITE_nm_htnew in *.
  pose proof (munch_refl [(nm + 8, nm + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 nm) = nm) by (apply unsigned_lit; lia).
  assert (EUh : bv_unsigned (Z_to_bv 64 ht) = ht) by (apply unsigned_lit; lia).
  zgo 0x218354. zsh. zgo 0x1fa384.
  unfold nm_w5_post, SITE_nm_sknew, e_OPENSSL_sk_new_null. apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [assumption|]. split; [assumption| exact HN].
Qed.

(* [comment removed for export] *)
Definition nm_w6_post (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (f nm sk pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms =>
    ms = MS (mkR (Z_to_bv 64 SITE_nm_cmp) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 (Z_to_bv 64 sk) (Z_to_bv 64 NM_CMP_THUNK) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 nm) (Z_to_bv 64 sk) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_OPENSSL_sk_set_cmp_thunks) fc None m (seg_rom asegs).

Lemma nm_w6 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f nm sk pad : Z),
  mem_inv asegs m ->
  evt asegs (nm_w6_post sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc f nm sk pad m)
    (MS (mkR (Z_to_bv 64 SITE_nm_sknew) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 sk) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 nm) s4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_nm_sknew) fc None m (seg_rom asegs)).
Proof.
  intros until pad. intros MI. unfold SITE_nm_sknew in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zgo 0x1fa9bc.
  unfold nm_w6_post, SITE_nm_cmp, NM_CMP_THUNK, e_OPENSSL_sk_set_cmp_thunks. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition nm_w7_post (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (f nm sk pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms =>
    ms = MS (mkR (Z_to_bv 64 SITE_nm_copy) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 (Z_to_bv 64 sk) (Z_to_bv 64 NM_COPY_THUNK) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 nm) (Z_to_bv 64 sk) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_OPENSSL_sk_set_copy_thunks) fc None m (seg_rom asegs).

Lemma nm_w7 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f nm sk pad : Z),
  mem_inv asegs m ->
  evt asegs (nm_w7_post sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc f nm sk pad m)
    (MS (mkR (Z_to_bv 64 SITE_nm_cmp) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 sk) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 nm) (Z_to_bv 64 sk) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_nm_cmp) fc None m (seg_rom asegs)).
Proof.
  intros until pad. intros MI. unfold SITE_nm_cmp in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zgo 0x1faa0c.
  unfold nm_w7_post, SITE_nm_copy, NM_COPY_THUNK, e_OPENSSL_sk_set_copy_thunks. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition nm_w8_post (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (f nm sk pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms =>
    ms = MS (mkR (Z_to_bv 64 SITE_nm_set) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 (Z_to_bv 64 sk) (Z_to_bv 64 NM_SET_THUNK) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 nm) (Z_to_bv 64 sk) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_OPENSSL_sk_set_thunks) fc None m (seg_rom asegs).

Lemma nm_w8 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f nm sk pad : Z),
  mem_inv asegs m ->
  evt asegs (nm_w8_post sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc f nm sk pad m)
    (MS (mkR (Z_to_bv 64 SITE_nm_copy) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 sk) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 nm) (Z_to_bv 64 sk) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_nm_copy) fc None m (seg_rom asegs)).
Proof.
  intros until pad. intros MI. unfold SITE_nm_copy in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zgo 0x1fa96c.
  unfold nm_w8_post, SITE_nm_set, NM_SET_THUNK, e_OPENSSL_sk_set_thunks. apply evt_done. reflexivity.
Qed.
(* [comment removed for export] *)
Definition SITE_nm_retire : Z := 0x2183c0.
Definition nm_w9_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (f nm lk ht sk pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_nm_set) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 (Z_to_bv 64 sk) (Z_to_bv 64 (nm + 24)) (Z_to_bv 64 0) a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 nm) (Z_to_bv 64 sk) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_nm_retire) fc None m' (seg_rom asegs)
    /\ munch [(nm + 24, nm + 32)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' nm [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 ht); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 sk); C8 (Z_to_bv 64 0)].

Lemma nm_w9 : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f nm lk ht sk pad : Z),
  0 < f -> f + 128 <= 2^47 -> 0x10007fff8000 <= nm -> nm + 40 <= 2^47 -> nm mod 8 = 0 -> 0 < sk -> sk < 2^64 ->
  rw_cells asegs m nm [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 ht); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> acc asegs m nm 40 -> mem_inv asegs m ->
  evt asegs (nm_w9_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 F fc f nm lk ht sk pad m)
    (MS (mkR (Z_to_bv 64 SITE_nm_set) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             (Z_to_bv 64 sk) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 nm) (Z_to_bv 64 sk) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_nm_set) fc None m (seg_rom asegs)).
Proof.
  intros until pad. intros F0 FH NMH NMT NMA SK0 SKH HN ACn MI. unfold SITE_nm_set in *.
  pose proof (munch_refl [(nm + 24, nm + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 nm) = nm) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 sk) = sk) by (apply unsigned_lit; lia).
  zgo 0x2183a8. zsh. zgo 0x2183c0.
  unfold nm_w9_post, SITE_nm_retire. apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [assumption|]. split; [assumption| exact HN].
Qed.

(* [comment removed for export] *)
Definition nm_w10_post (sp gp tp a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (f nm sk lo pad : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a0' : word) (hj sj : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_nm_set) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
                 a0' a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 nm) (Z_to_bv 64 sk) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
                 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_nm_release) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 32); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + -96 - pad)
    /\ rw_cells asegs m' f [CB 32 hj]
    /\ rw_cells asegs m' (f / 8 + 2147450880) [CB 16 sj].

Lemma nm_w10 : forall sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f nm sk lo pad : Z) (hj sj : list byte),
  lo <= bv_unsigned sp - 112 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0 < f -> 0xbc6000 <= f -> f + 128 <= lo -> (f + 128 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  stk asegs m lo (bv_unsigned sp + -96 - pad) ->
  rw_cells asegs m f [CB 32 hj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 16 sj] -> mem_inv asegs m ->
  evt asegs (nm_w10_post sp gp tp a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 F fc f nm sk lo pad m)
    (MS (mkR (Z_to_bv 64 SITE_nm_set) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 nm) (Z_to_bv 64 sk) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_nm_retire) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros HLO HLOS SPH F0 FIMG FLO FSH ST1 FB SB MI. unfold SITE_nm_retire, SITE_nm_set in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl [(f, f + 32); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (div8_facts f) as Q1.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 16 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)). assert (f / 8 + 16 <= 2^44) by (Z.div_mod_to_equations; lia). lia. }
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  zgo 0x218430.
  pose proof (rw_cells_blur_all' _ _ _ FB) as FBB; cbn [cells_size csize Nat.add app] in FBB.
  pose proof (rw_cells_blur_all' _ _ _ SB) as SBB; cbn [cells_size csize Nat.add app] in SBB.
  subst SP. unfold nm_w10_post, SITE_nm_release. apply evt_done. do 4 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FBB| exact SBB].
Qed.
(* [comment removed for export] *)
Definition nm_w11_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (nm fl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 nm) a1 a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)].

Lemma nm_w11 : forall ra0 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 s10 s11 t3 t4 t5 t6
    (s0' s1' s2' s3' s4' s5' s6' s7' : word) (F : bvmap 5 word) fc (m : mem) (nm f sk fl lo pad : Z) (j : list byte),
  (pad = 0 \/ pad = 16) -> lo <= bv_unsigned sp - 112 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0 < f -> f + 128 <= lo -> 0 < fl -> fl + 1 <= lo ->
  stk asegs m lo (bv_unsigned sp + -96 - pad) -> stk asegs m (bv_unsigned sp + -96 - pad) (bv_unsigned sp + -96) ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 24 j; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  ro_cells asegs m (f + 120) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (nm_w11_post ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc nm fl lo m)
    (MS (mkR (Z_to_bv 64 SITE_nm_set) (Z_to_bv 64 (bv_unsigned sp + -96 - pad)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pad))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 nm) (Z_to_bv 64 sk) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_nm_release) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HP HLO HLOS SPH F0 FLO FL0 FLLO ST1 GAP FR FLG FLB MI. unfold SITE_nm_release, SITE_nm_set in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUfl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  zstep. clear FLG.
  zstep; lfix.
  zgo 0x218484.
  pose proof (stk_merge asegs _ lo (SP + -96 - pad) (SP + -96) ST1 GAP ltac:(lia)) as ST2.
  zgo 0x2184ac.
  release_frame FR ST2 SP.
  zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold nm_w11_post. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| assumption].
Qed.
