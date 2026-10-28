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
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_M_malloc Fz_M_zalloc Fz_env Th_mutex Fz_M_locknew Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tslia ::= wp_tslia.
Notation TP_A := (0xba3ef0)%Z (only parsing).
(* [comment removed for export] *)
Local Ltac zgo p := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; lfix
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ifF | ifT | ubs_if] end).
(* [comment removed for export] *)
Local Ltac zsh := cbv beta; try change (bv_unsigned (Z_to_bv 8 0)) with 0; try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).

Definition e_ht_new : Z := 0x21a09c.
Definition SITE_ht_zalloc1 : Z := 0x21a0f4.   (* [comment removed for export] *)
Definition SITE_ht_locknew : Z := 0x21a154.   (* [comment removed for export] *)
Definition SITE_ht_memcpy : Z := 0x21a180.    (* [comment removed for export] *)
Definition SITE_ht_zalloc2 : Z := 0x21a230.   (* [comment removed for export] *)
Definition SITE_ht_anl : Z := 0x21a260.       (* [comment removed for export] *)
Definition SITE_ht_rcu : Z := 0x21a2dc.       (* [comment removed for export] *)
Definition HT_FREE_DFL : Z := 0x21a500.       (* [comment removed for export] *)
Definition HT_HASH_DFL : Z := 0x21a5ec.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ht_conf (ctx : word) : list cell :=
  [C8 ctx; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 512); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].

(* [comment removed for export] *)
Definition ht_w0_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j : list byte) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ht_zalloc1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp s1
                 (Z_to_bv 64 96) (Z_to_bv 64 0x4c8c0) (Z_to_bv 64 186) a3 a4 a5 a6 a7 s2 s3 a0 s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_zalloc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [CB 8 j; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk asegs m' lo (bv_unsigned sp + -96).

Lemma ht_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)(F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] -> mem_inv asegs m ->
  evt asegs (ht_w0_post ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_ht_new) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST HLO HLOS SPH UT SHC MI. unfold e_ht_new, g_shadow_memory_dynamic_address in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 96, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 96, SP)]) by ut_fp_lia.
  carve_frame 96%nat ST.
  zgo 0x1fbfec.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold ht_w0_post, SITE_ht_zalloc1, e_CRYPTO_zalloc. apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FR| assumption].
Qed.
(* [comment removed for export] *)
Definition ht_w1_post (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (nw conf : Z) (m : mem) : machine_state -> Prop :=
  fun ms =>
    ms = MS (mkR (Z_to_bv 64 SITE_ht_locknew) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 nw)
                 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (nw + 64)) (Z_to_bv 64 (conf + 40)) (Z_to_bv 64 conf) s5 (Z_to_bv 64 0x7fff8000)
                 (Z_to_bv 64 (Z.shiftr (conf + 40) 3 + 2147450880)) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_lock_new) fc None m (seg_rom asegs).

Lemma ht_w1 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)(F : bvmap 5 word) fc (m : mem) (nw conf : Z) (ctx : word),
  0 < nw -> nw + 96 <= 2^47 -> nw mod 8 = 0 -> 0 < conf -> conf + 48 <= 2^47 -> conf mod 8 = 0 ->
  rw_cells asegs m conf (ht_conf ctx) -> acc asegs m conf 48 -> mem_inv asegs m ->
  evt asegs (ht_w1_post sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s5 s8 s9 s10 s11 t3 t4 t5 t6 F fc nw conf m)
    (MS (mkR (Z_to_bv 64 SITE_ht_zalloc1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp s1
             (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 conf) s5 (Z_to_bv 64 0x7fff8000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ht_zalloc1) fc None m (seg_rom asegs)).
Proof.
  intros until ctx. intros NW0 NWH NWAL C0 CH CAL HC ACf MI. unfold SITE_ht_zalloc1, ht_conf in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWS : sh_fp ([] : list (Z * Z))) by sh_fp_lia.
  assert (EUn : bv_unsigned (Z_to_bv 64 nw) = nw) by (apply unsigned_lit; lia).
  assert (EUc : bv_unsigned (Z_to_bv 64 conf) = conf) by (apply unsigned_lit; lia).
  pose proof (div8_facts conf) as Q1.
  zgo 0x1f5e3c. zsh.
  unfold ht_w1_post, SITE_ht_locknew, e_lock_new. apply evt_done. reflexivity.
Qed.
(* [comment removed for export] *)
Definition ht_tab0 : list cell :=
  [CB 48 (repeat (Z_to_bv 8 0) 48); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16)].

(* [comment removed for export] *)
Definition ht_w2_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (nw conf lk : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ht_memcpy) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 nw)
                 (Z_to_bv 64 nw) (Z_to_bv 64 conf) (Z_to_bv 64 48) a3 a4 a5 a6 a7 (Z_to_bv 64 (nw + 64)) (Z_to_bv 64 (conf + 40)) (Z_to_bv 64 conf) s5 (Z_to_bv 64 0x7fff8000)
                 (Z_to_bv 64 (Z.shiftr (conf + 40) 3 + 2147450880)) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_asan_memcpy) fc None m' (seg_rom asegs)
    /\ munch [(nw + 56, nw + 64)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' nw [CB 48 (repeat (Z_to_bv 8 0) 48); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16)].

Lemma ht_w2 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word)(F : bvmap 5 word) fc (m : mem) (nw conf lk : Z),
  0x10007fff8000 <= nw -> nw + 96 <= 2^47 -> nw mod 8 = 0 -> 0 < lk -> lk < 2^64 -> 0 <= conf -> conf + 48 <= 2^47 ->
  rw_cells asegs m nw ht_tab0 -> acc asegs m nw 96 -> mem_inv asegs m ->
  evt asegs (ht_w2_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s5 s8 s9 s10 s11 t3 t4 t5 t6 F fc nw conf lk m)
    (MS (mkR (Z_to_bv 64 SITE_ht_locknew) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 nw)
             (Z_to_bv 64 lk) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (nw + 64)) (Z_to_bv 64 (conf + 40)) (Z_to_bv 64 conf) s5 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 (Z.shiftr (conf + 40) 3 + 2147450880)) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ht_locknew) fc None m (seg_rom asegs)).
Proof.
  intros until lk. intros NWH NWT NWA LK0 LKH C0 CH HN ACn MI. unfold SITE_ht_locknew, ht_tab0 in *.
  pose proof (munch_refl [(nw + 56, nw + 64)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  assert (EUn : bv_unsigned (Z_to_bv 64 nw) = nw) by (apply unsigned_lit; lia).
  assert (EUc : bv_unsigned (Z_to_bv 64 conf) = conf) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 lk) = lk) by (apply unsigned_lit; lia).
  zgo 0x21a164. zsh. zgo 0x1c1920.
  unfold ht_w2_post, SITE_ht_memcpy, e_asan_memcpy. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact HN].
Qed.
(* [comment removed for export] *)
Definition ht_tab1 (ctx : word) (lk : Z) : list cell :=
  [C8 ctx; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 512); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16)].
(* [comment removed for export] *)
Definition ht_tab2 (ctx : word) (lk : Z) : list cell :=
  [C8 ctx; C8 (Z_to_bv 64 HT_FREE_DFL); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 512); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 512); CB 16 (repeat (Z_to_bv 8 0) 16)].

(* [comment removed for export] *)
Definition ht_w3_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (nw conf lk : Z) (ctx : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ht_zalloc2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 nw)
                 (Z_to_bv 64 24) (Z_to_bv 64 0x4c8c0) (Z_to_bv 64 218) a3 a4 a5 a6 a7 (Z_to_bv 64 (nw + 64)) (Z_to_bv 64 (conf + 40)) (Z_to_bv 64 conf)
                 (Z_to_bv 64 (nw + 72)) (Z_to_bv 64 0x7fff8000)
                 (Z_to_bv 64 (Z.shiftr (conf + 40) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (nw + 72) 3 + 2147450880)) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_CRYPTO_zalloc) fc None m' (seg_rom asegs)
    /\ munch [(nw, nw + 96)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' nw (ht_tab2 ctx lk).

Lemma ht_w3 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word)(F : bvmap 5 word) fc (m : mem) (nw conf lk : Z) (ctx : word),
  0x10007fff8000 <= nw -> nw + 96 <= 2^47 -> nw mod 8 = 0 -> 0 <= conf -> conf + 48 <= 2^47 ->
  rw_cells asegs m nw (ht_tab1 ctx lk) -> acc asegs m nw 96 -> mem_inv asegs m ->
  evt asegs (ht_w3_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 F fc nw conf lk ctx m)
    (MS (mkR (Z_to_bv 64 SITE_ht_memcpy) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 nw)
             (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (nw + 64)) (Z_to_bv 64 (conf + 40)) (Z_to_bv 64 conf) s5 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 (Z.shiftr (conf + 40) 3 + 2147450880)) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ht_memcpy) fc None m (seg_rom asegs)).
Proof.
  intros until ctx. intros NWH NWT NWA C0 CH HT ACn MI. unfold SITE_ht_memcpy, ht_tab1 in *.
  pose proof (munch_refl [(nw, nw + 96)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  assert (EUn : bv_unsigned (Z_to_bv 64 nw) = nw) by (apply unsigned_lit; lia).
  assert (EUc : bv_unsigned (Z_to_bv 64 conf) = conf) by (apply unsigned_lit; lia).
  zgo 0x21a190. zsh. zgo 0x21a1e4. zsh. zgo 0x21a1fc. zsh. zgo 0x21a20c. zsh. zgo 0x1fbfec.
  unfold ht_w3_post, SITE_ht_zalloc2, e_CRYPTO_zalloc, ht_tab2, HT_FREE_DFL. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact HT].
Qed.
(* [comment removed for export] *)
Definition ht_tab3 (ctx : word) (lk md : Z) : list cell :=
  [C8 ctx; C8 (Z_to_bv 64 HT_FREE_DFL); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 512); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 md); C8 (Z_to_bv 64 512); CB 16 (repeat (Z_to_bv 8 0) 16)].

(* [comment removed for export] *)
Definition e_anl : Z := 0x21a520.
Definition ht_w4_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (nw conf lk md : Z) (ctx : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ht_anl) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 nw)
                 (Z_to_bv 64 512) (Z_to_bv 64 (md + 8)) (Z_to_bv 64 512) a3 a4 a5 a6 a7 (Z_to_bv 64 (nw + 64)) (Z_to_bv 64 (conf + 40)) (Z_to_bv 64 conf)
                 (Z_to_bv 64 (nw + 72)) (Z_to_bv 64 0x7fff8000)
                 (Z_to_bv 64 (Z.shiftr (conf + 40) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (nw + 72) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (nw + 64) 3 + 2147450880)) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_anl) fc None m' (seg_rom asegs)
    /\ munch [(nw + 64, nw + 72)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' nw (ht_tab3 ctx lk md).

Lemma ht_w4 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word)(F : bvmap 5 word) fc (m : mem) (nw conf lk md : Z) (ctx : word),
  0x10007fff8000 <= nw -> nw + 96 <= 2^47 -> nw mod 8 = 0 -> 0 <= conf -> conf + 48 <= 2^47 -> 0 < md -> md + 24 <= 2^47 -> md mod 8 = 0 ->
  rw_cells asegs m nw (ht_tab2 ctx lk) -> acc asegs m nw 96 -> mem_inv asegs m ->
  evt asegs (ht_w4_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 F fc nw conf lk md ctx m)
    (MS (mkR (Z_to_bv 64 SITE_ht_zalloc2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 nw)
             (Z_to_bv 64 md) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (nw + 64)) (Z_to_bv 64 (conf + 40)) (Z_to_bv 64 conf)
             (Z_to_bv 64 (nw + 72)) (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 (Z.shiftr (conf + 40) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (nw + 72) 3 + 2147450880)) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ht_zalloc2) fc None m (seg_rom asegs)).
Proof.
  intros until ctx. intros NWH NWT NWA C0 CH MD0 MDH MDA HT ACn MI. unfold SITE_ht_zalloc2, ht_tab2 in *.
  pose proof (munch_refl [(nw + 64, nw + 72)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  assert (EUn : bv_unsigned (Z_to_bv 64 nw) = nw) by (apply unsigned_lit; lia).
  assert (EUc : bv_unsigned (Z_to_bv 64 conf) = conf) by (apply unsigned_lit; lia).
  assert (EUm : bv_unsigned (Z_to_bv 64 md) = md) by (apply unsigned_lit; lia).
  zgo 0x21a520. zsh.
  unfold ht_w4_post, SITE_ht_anl, e_anl, ht_tab3, HT_FREE_DFL. apply evt_done. eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact HT].
Qed.
(* [comment removed for export] *)
Definition e_rcu_lock_new : Z := 0x1f5920.
Definition ht_w5_post (sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (nw conf md q : Z) (ctx : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a2 : word) (m' : mem),
    ms = MS (mkR (Z_to_bv 64 SITE_ht_rcu) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 nw)
                 (Z_to_bv 64 1) ctx a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (nw + 64)) (Z_to_bv 64 (conf + 40)) (Z_to_bv 64 conf)
                 (Z_to_bv 64 (nw + 72)) (Z_to_bv 64 0x7fff8000)
                 (Z_to_bv 64 (Z.shiftr (conf + 40) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (nw + 72) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (nw + 64) 3 + 2147450880)) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_rcu_lock_new) fc None m' (seg_rom asegs)
    /\ munch [(md, md + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' md [C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 511)].

Lemma ht_w5 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word)(F : bvmap 5 word) fc (m : mem) (nw conf lk md q : Z) (ctx : word),
  0x10007fff8000 <= nw -> nw + 96 <= 2^47 -> nw mod 8 = 0 -> 0 <= conf -> conf + 48 <= 2^47 -> conf mod 8 = 0 ->
  0x10007fff8000 <= md -> md + 24 <= 2^47 -> md mod 8 = 0 -> 0 < q -> q < 2^64 ->
  (nw + 96 <= md \/ md + 24 <= nw) -> (conf + 48 <= nw \/ nw + 96 <= conf) -> (conf + 48 <= md \/ md + 24 <= conf) ->
  rw_cells asegs m nw (ht_tab3 ctx lk md) -> acc asegs m nw 96 ->
  rw_cells asegs m md [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 q); C8 (Z_to_bv 64 0)] -> acc asegs m md 24 ->
  rw_cells asegs m conf (ht_conf ctx) -> acc asegs m conf 48 -> mem_inv asegs m ->
  evt asegs (ht_w5_post sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 F fc nw conf md q ctx m)
    (MS (mkR (Z_to_bv 64 SITE_ht_anl) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 nw)
             (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (nw + 64)) (Z_to_bv 64 (conf + 40)) (Z_to_bv 64 conf)
             (Z_to_bv 64 (nw + 72)) (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 (Z.shiftr (conf + 40) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (nw + 72) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (nw + 64) 3 + 2147450880)) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ht_anl) fc None m (seg_rom asegs)).
Proof.
  intros until ctx. intros NWH NWT NWA C0 CH CAL MDH MDT MDA Q0 QH NM CN CM HT ACn HMD ACm HC ACf MI. unfold SITE_ht_anl, ht_tab3, ht_conf in *.
  pose proof (munch_refl [(md, md + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  assert (EUn : bv_unsigned (Z_to_bv 64 nw) = nw) by (apply unsigned_lit; lia).
  assert (EUc : bv_unsigned (Z_to_bv 64 conf) = conf) by (apply unsigned_lit; lia).
  assert (EUm : bv_unsigned (Z_to_bv 64 md) = md) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  pose proof (div8_facts conf) as Q1.
  zgo 0x21a264. zsh. zgo 0x21a27c. zsh. zgo 0x21a28c. zsh. zgo 0x21a2a0. zsh. zgo 0x21a2b4. zsh. zgo 0x21a2cc. zsh. zgo 0x1f5920.
  unfold ht_w5_post, SITE_ht_rcu, e_rcu_lock_new. apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption| exact HMD].
Qed.
(* [comment removed for export] *)
Definition ht_tab4 (ctx : word) (L lk md : Z) : list cell :=
  [C8 ctx; C8 (Z_to_bv 64 HT_FREE_DFL); C8 (Z_to_bv 64 HT_HASH_DFL); C8 (Z_to_bv 64 512); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 lk); C8 (Z_to_bv 64 md); C8 (Z_to_bv 64 512); CB 16 (repeat (Z_to_bv 8 0) 16)].

(* [comment removed for export] *)
Definition ht_w6_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (nw L lk md lo : Z) (ctx : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1 : word) (m' : mem),
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 nw) a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(nw, nw + 96)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' nw (ht_tab4 ctx L lk md).

Lemma ht_w6 : forall (ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word)(s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' : word)
    (F : bvmap 5 word) fc (m : mem) (nw conf L lk md lo : Z) (ctx : word) (j : list byte),
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0x10007fff8000 <= nw -> nw + 96 <= lo -> nw mod 8 = 0 -> 0 <= conf -> conf + 48 <= 2^47 -> 0 < L -> L < 2^64 ->
  stk asegs m lo (bv_unsigned sp + -96) ->
  rw_cells asegs m (bv_unsigned sp + -96) [CB 8 j; C8 s9'; C8 s8'; C8 s7'; C8 s6'; C8 s5'; C8 s4'; C8 s3'; C8 s2'; C8 s1'; C8 s0'; C8 ra0] ->
  rw_cells asegs m nw (ht_tab3 ctx lk md) -> acc asegs m nw 96 -> mem_inv asegs m ->
  evt asegs (ht_w6_post ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10 s11 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc nw L lk md lo ctx m)
    (MS (mkR (Z_to_bv 64 SITE_ht_rcu) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 nw)
             (Z_to_bv 64 L) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (nw + 64)) (Z_to_bv 64 (conf + 40)) (Z_to_bv 64 conf)
             (Z_to_bv 64 (nw + 72)) (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 (Z.shiftr (conf + 40) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (nw + 72) 3 + 2147450880)) (Z_to_bv 64 (Z.shiftr (nw + 64) 3 + 2147450880)) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_ht_rcu) fc None m (seg_rom asegs)).
Proof.
  intros until j. intros HLO HLOS SPH NWH NWLO NWA C0 CH L0 LH ST1 FR HT ACn MI. unfold SITE_ht_rcu, ht_tab3 in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(nw, nw + 96)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  assert (EUn : bv_unsigned (Z_to_bv 64 nw) = nw) by (apply unsigned_lit; lia).
  assert (EUL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  zgo 0x21a2ec. zsh. zgo 0x21a308. zsh. zgo 0x21a318. zsh. zgo 0x21a424.
  release_frame FR ST1 SP.
  zstep.
  subst SP. rewrite ?Z_to_bv_bv_unsigned.
  unfold ht_w6_post, ht_tab4, HT_FREE_DFL, HT_HASH_DFL. apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption| exact HT].
Qed.
