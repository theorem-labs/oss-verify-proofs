(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Fz_T_ekit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem Fz_kit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_W1_defs Fz_W1_misc Fz_W1_read Fz_W2_puts Fz_W2_gets Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition e_BIO_read : Z := 0x237054.
Definition e_bio_read_intern : Z := 0x237240.
Definition SITE_br_smalloc : Z := 0x2370c0.     (* [comment removed for export] *)
Definition SITE_br_intern : Z := 0x237164.      (* [comment removed for export] *)
Definition SITE_br_release : Z := 0x2371e0.     (* [comment removed for export] *)
Definition SITE_bri_brc : Z := 0x237394.        (* [comment removed for export] *)
Definition BR_DESCR : Z := 0x3d05f.
(* [comment removed for export] *)
Definition br_ftail (s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition e_bread_conv : Z := 0x238fe4.
Definition SITE_brc_read : Z := 0x239068.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition brc_frame (c0 : cell) (s5 s4 s3 s2 s1 s0 ra : word) : list cell := [c0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition brc_s0_post (sp gp tp t0 t1 t2 a1 a2 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (ra0 s0' s1' s2' s3' s4' s5' : word) (BI PR lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j : list byte) (m' : mem),
    munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\
    stk asegs m' lo (bv_unsigned sp + -64) /\
    rw_cells asegs m' (bv_unsigned sp + -64) (brc_frame (CB 8 j) s5' s4' s3' s2' s1' s0' ra0) /\
    ms = MS (mkR (Z_to_bv 64 SITE_brc_read) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2
               sp (Z_to_bv 64 PR) (Z_to_bv 64 BI) a1 a2 (Z_to_bv 64 e_mem_read) a4 a5 a6 a7
               (Z_to_bv 64 BI) s3' (Z_to_bv 64 2147450880) s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_mem_read) fc None m' (seg_rom asegs).

Lemma brc_s0_walk : forall ra0 sp gp t0 t1 t2 s0' s1' a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI OUT n PR meth : Z),
  lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  (meth = M_MEM_A \/ meth = M_SECMEM_A) -> rw_cells asegs m BI (bio_head meth) -> acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  ro_cells asegs m ((meth + 40) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  0 <= OUT < 2^64 -> 1 <= n < 2^31 - 1 -> 0 <= PR < 2^64 -> mem_inv asegs m ->
  evt asegs (brc_s0_post sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 (Z_to_bv 64 OUT) (Z_to_bv 64 n) a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' BI PR lo m)
    (MS (mkR ra0 sp gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 s0' s1' (Z_to_bv 64 BI) (Z_to_bv 64 OUT) (Z_to_bv 64 n) (Z_to_bv 64 PR) a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_bread_conv) fc None m (seg_rom asegs)).
Proof.
  intros ra0 sp gp t0 t1 t2 s0' s1' a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI OUT n PR meth
    STK_ROOM STK_HI SP_HI STACK IMG SHBASE METH BIOHD BIACC BI_POS BI_AL BI_HI BI_ROOM METHSH OUT_RNG N_RNG PR_RNG MINV.
  unfold e_bread_conv, bio_head in *; unfold g_shadow_memory_dynamic_address in SHBASE.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (UTFP : ut_fp [(bv_unsigned sp - 64, bv_unsigned sp)]) by ut_fp_lia.
  assert (SHFP : sh_fp [(bv_unsigned sp - 64, bv_unsigned sp)]) by sh_fp_lia.
  assert (BI8 : BI mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  carve_frame 64%nat STACK.
  destruct METH as [-> | ->]; unfold M_MEM_A, M_SECMEM_A in *.
  - replace ((5538432 + 40) / 8 + 2147450880) with 2148143189 in METHSH by reflexivity.
    repeat lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 3162908) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
         change (negb (bv_eqb z64 z64)) with false; cbv iota
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    end.
    if_cases BRN; zify_cond BRN; [exfalso; lia|].
    repeat lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 3162908) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
         change (negb (bv_eqb z64 z64)) with false; cbv iota
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    end.
    if_cases BRC; zify_cond BRC; [| exfalso; lia].
    repeat lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 3162908) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
         change (negb (bv_eqb z64 z64)) with false; cbv iota
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    end.
    apply evt_done. unfold brc_s0_post. do 2 eexists.
    split; [exact MU|]. split; [exact WM|]. split; [exact MINV|]. split; [exact STACK|].
    split; [unfold brc_frame; exact FR|]. reflexivity.
  - replace ((5538592 + 40) / 8 + 2147450880) with 2148143209 in METHSH by reflexivity.
    repeat lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 3162908) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
         change (negb (bv_eqb z64 z64)) with false; cbv iota
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    end.
    if_cases BRN2; zify_cond BRN2; [exfalso; lia|].
    repeat lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 3162908) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
         change (negb (bv_eqb z64 z64)) with false; cbv iota
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    end.
    if_cases BRC2; zify_cond BRC2; [| exfalso; lia].
    repeat lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 3162908) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
         change (negb (bv_eqb z64 z64)) with false; cbv iota
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    end.
    apply evt_done. unfold brc_s0_post. do 2 eexists.
    split; [exact MU|]. split; [exact WM|]. split; [exact MINV|]. split; [exact STACK|].
    split; [unfold brc_frame; exact FR|]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition brc_s1_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (BI PR k fl : Z) (rrw numw padw ptrw : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    munch [(BI + 48, BI + 52); (PR, PR + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\
    stk asegs m' lo (bv_unsigned sp) /\
    rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (Z.land fl 18446744073709551487) rrw numw padw ptrw) /\
    rw_cells asegs m' PR [C8 (Z_to_bv 64 k)] /\
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 1) (Z_to_bv 64 k) a2 a3 a4 a5 a6 a7
               s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs).

Lemma brc_s1_walk : forall ra0 ra1 sp gp t0 t1 t2 s0' s1' s2' s3' s4' s5' a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI PR k fl : Z) (rrw numw padw ptrw : word) (oldb j : list byte),
  lo <= bv_unsigned sp - 64 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -64) ->
  rw_cells asegs m (bv_unsigned sp + -64) (brc_frame (CB 8 j) s5' s4' s3' s2' s1' s0' ra0) ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw ptrw) -> 0 <= fl < 2^32 ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  rw_cells asegs m PR [CB 8 oldb] -> rw_cells asegs m (PR / 8 + 2147450880) [C1 (Z_to_bv 8 0)] -> 0 < PR -> PR mod 8 = 0 -> PR + 8 <= lo ->
  (PR + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= PR) -> (BI + 128 <= PR \/ PR + 8 <= BI) ->
  1 <= k < 2^31 -> mem_inv asegs m ->
  evt asegs (brc_s1_post ra0 sp gp (Z_to_bv 64 0xba3ef0) s0' s1' s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 F fc BI PR k fl rrw numw padw ptrw lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 0xba3ef0) t0 t1 t2 sp (Z_to_bv 64 PR) (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 BI) s3' (Z_to_bv 64 0x7fff8000) s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_brc_read) fc None m (seg_rom asegs)).
Proof.
  intros ra0 ra1 sp gp t0 t1 t2 s0' s1' s2' s3' s4' s5' a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI PR k fl rrw numw padw ptrw oldb j
    STK_ROOM STK_HI SP_HI STACK FRAME BIOW1 FL_RNG BIACC BI_POS BI_AL BI_HI BI_ROOM PRCELL PRSH PR_POS PR_AL PR_ROOM PR_VALID PR_BI K_RNG MINV.
  unfold SITE_brc_read, bio_w1_cells, brc_frame in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  pose proof (munch_refl [(BI + 48, BI + 52); (PR, PR + 8)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (BI8 : BI mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (EUk : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; lia).
  assert (ZX : bv_unsigned (zx32 (Z_to_bv 64 fl)) = fl).
  { unfold zx32. rewrite (unsigned_lit fl ltac:(lia)), (Z.mod_small fl (2 ^ 32) ltac:(lia)).
    apply unsigned_lit; lia. }
  assert (SIGN : Z.land (Z.land (0 + - Z.b2z (9223372036854775808 <? Z.lxor k 9223372036854775808)) 18446744073709551615) k = k).
  { assert (NOCARRY : Z.land k 9223372036854775808 = 0).
    { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
      change 9223372036854775808 with (2 ^ 63). rewrite Z.pow2_bits_eqb by lia.
      destruct (Z.eqb_spec 63 i) as [<-|NE]; [| now rewrite andb_false_r].
      rewrite (Z.bits_above_log2 k 63); [now rewrite andb_false_l | lia |].
      apply Z.log2_lt_pow2; lia. }
    rewrite <- (Z.add_nocarry_lxor k 9223372036854775808 NOCARRY).
    replace (9223372036854775808 <? k + 9223372036854775808) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [Z.b2z]. change (0 + -1) with (-1). rewrite Z.land_m1_l.
    rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64).
    rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
       change (negb (bv_eqb z64 z64)) with false; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
       change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with false; cbv iota
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
  end.
  if_cases KZERO; zify_cond KZERO; [exfalso; lia|].
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
       change (negb (bv_eqb z64 z64)) with false; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
       change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with false; cbv iota
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
  end.
  if_cases KNEG; zify_cond KNEG; [exfalso; lia|].
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
       change (negb (bv_eqb z64 z64)) with false; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
       change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with false; cbv iota
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
  end.
  rewrite SIGN. rewrite <- (shadow_spell1 PR ltac:(lia)) in PRSH.
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
       change (negb (bv_eqb z64 z64)) with false; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
       change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with false; cbv iota
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
  end.
  release_frame FRAME STACK (bv_unsigned sp).
  apply evt_done. unfold brc_s1_post, bio_w1_cells. rewrite ZX in BIOW1.
  do 14 eexists.
  split; [exact MU|]. split; [exact WM|]. split; [exact MINV|]. split; [exact STACK|].
  split; [exact BIOW1|]. split; [exact PRCELL|]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition bri_frame (s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition bri_s0_post (sp gp tp t0 t1 t2 a5 a6 a7 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' : word)
    (BI OUT n PR meth lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists m' : mem,
    munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\
    stk asegs m' lo (bv_unsigned sp + -96) /\
    rw_cells asegs m' (bv_unsigned sp + -96) (bri_frame s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) /\
    rw_cells asegs m' BI (bio_head meth) /\
    ms = MS (mkR (Z_to_bv 64 SITE_bri_brc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 PR)
               (Z_to_bv 64 BI) (Z_to_bv 64 OUT) (Z_to_bv 64 n) (Z_to_bv 64 PR) (Z_to_bv 64 e_bread_conv) a5 a6 a7
               (Z_to_bv 64 n) (Z_to_bv 64 OUT) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (-2)) (Z_to_bv 64 (BI + 8))
               (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880))
               s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_bread_conv) fc None m' (seg_rom asegs).

Lemma bri_s0_walk : forall ra0 sp gp tp t0 t1 t2 s0' s1' a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI OUT n PR meth fl : Z) (shw rrw numw padw ptrw : word),
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp) -> img_untouched m ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  (meth = M_MEM_A \/ meth = M_SECMEM_A) -> rw_cells asegs m BI (bio_head meth) -> rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) shw fl rrw numw padw ptrw) ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  ro_cells asegs m ((meth + 32) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  0 <= OUT < 2^64 -> 0 <= n < 2^64 -> 0 <= PR < 2^64 -> mem_inv asegs m ->
  evt asegs (bri_s0_post sp gp tp t0 t1 t2 a5 a6 a7 s11 t3 t4 t5 t6 F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' BI OUT n PR meth lo m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 BI) (Z_to_bv 64 OUT) (Z_to_bv 64 n) (Z_to_bv 64 PR) a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_bio_read_intern) fc None m (seg_rom asegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0' s1' a4 a5 a6 a7 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 t3 t4 t5 t6 F fc m lo BI OUT n PR meth fl shw rrw numw padw ptrw
    STK_ROOM STK_HI SP_HI STACK IMG SHBASE METH BIOHD BIOW1 BIACC BI_POS BI_AL BI_HI BI_ROOM METHSH OUT_RNG N_RNG PR_RNG MINV.
  unfold e_bio_read_intern, bio_head, bio_w1_cells in *; unfold g_shadow_memory_dynamic_address in SHBASE.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (UTFP : ut_fp [(bv_unsigned sp - 96, bv_unsigned sp)]) by ut_fp_lia.
  assert (SHFP : sh_fp [(bv_unsigned sp - 96, bv_unsigned sp)]) by sh_fp_lia.
  assert (BI8 : BI mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (EUb : bv_unsigned (Z_to_bv 64 BI) = BI) by (apply unsigned_lit; lia).
  carve_frame 96%nat STACK.
  destruct METH as [-> | ->]; unfold M_MEM_A, M_SECMEM_A in *.
  - replace ((5538432 + 32) / 8 + 2147450880) with 2148143188 in METHSH by reflexivity.
    repeat lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 2330596) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
         change (negb (bv_eqb z64 z64)) with false; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb z64 z64 then _ else _) _ _ _ _) =>
         change (bv_eqb z64 z64) with true; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
         change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with false; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sxb (Z_to_bv 8 0)) z64 then _ else _) _ _ _ _) =>
         change (bv_eqb (sxb (Z_to_bv 8 0)) z64) with true; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) z64)) in
         change (negb (bv_eqb (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) z64) in
         change (bv_eqb (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sx32 (Z_to_bv 64 ?x)) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) in
         change (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sx32 (Z_to_bv 64 ?x)) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (sx32 (Z_to_bv 64 x)) z64) in
         change (bv_eqb (sx32 (Z_to_bv 64 x)) z64) with v; cbv iota
    end.
    if_cases BINZ; zify_cond BINZ; [exfalso; lia|].
    repeat lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 2330596) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
         change (negb (bv_eqb z64 z64)) with false; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb z64 z64 then _ else _) _ _ _ _) =>
         change (bv_eqb z64 z64) with true; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
         change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with false; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sxb (Z_to_bv 8 0)) z64 then _ else _) _ _ _ _) =>
         change (bv_eqb (sxb (Z_to_bv 8 0)) z64) with true; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) z64)) in
         change (negb (bv_eqb (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) z64) in
         change (bv_eqb (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sx32 (Z_to_bv 64 ?x)) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) in
         change (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sx32 (Z_to_bv 64 ?x)) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (sx32 (Z_to_bv 64 x)) z64) in
         change (bv_eqb (sx32 (Z_to_bv 64 x)) z64) with v; cbv iota
    end.
    apply evt_done. unfold bri_s0_post, bri_frame. eexists.
    split; [exact MU|]. split; [exact WM|]. split; [exact MINV|]. split; [exact STACK|].
    split; [exact FR|]. split; [unfold bio_head; exact BIOHD|]. reflexivity.
  - replace ((5538592 + 32) / 8 + 2147450880) with 2148143208 in METHSH by reflexivity.
    repeat lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 2330596) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
         change (negb (bv_eqb z64 z64)) with false; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb z64 z64 then _ else _) _ _ _ _) =>
         change (bv_eqb z64 z64) with true; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
         change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with false; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sxb (Z_to_bv 8 0)) z64 then _ else _) _ _ _ _) =>
         change (bv_eqb (sxb (Z_to_bv 8 0)) z64) with true; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) z64)) in
         change (negb (bv_eqb (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) z64) in
         change (bv_eqb (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sx32 (Z_to_bv 64 ?x)) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) in
         change (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sx32 (Z_to_bv 64 ?x)) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (sx32 (Z_to_bv 64 x)) z64) in
         change (bv_eqb (sx32 (Z_to_bv 64 x)) z64) with v; cbv iota
    end.
    if_cases BINZ2; zify_cond BINZ2; [exfalso; lia|].
    repeat lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 2330596) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
         change (negb (bv_eqb z64 z64)) with false; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb z64 z64 then _ else _) _ _ _ _) =>
         change (bv_eqb z64 z64) with true; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
         change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with false; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sxb (Z_to_bv 8 0)) z64 then _ else _) _ _ _ _) =>
         change (bv_eqb (sxb (Z_to_bv 8 0)) z64) with true; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) z64)) in
         change (negb (bv_eqb (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) z64) in
         change (bv_eqb (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sx32 (Z_to_bv 64 ?x)) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) in
         change (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sx32 (Z_to_bv 64 ?x)) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (sx32 (Z_to_bv 64 x)) z64) in
         change (bv_eqb (sx32 (Z_to_bv 64 x)) z64) with v; cbv iota
    end.
    apply evt_done. unfold bri_s0_post, bri_frame. eexists.
    split; [exact MU|]. split; [exact WM|]. split; [exact MINV|]. split; [exact STACK|].
    split; [exact FR|]. split; [unfold bio_head; exact BIOHD|]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition bri_s1_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (BI n : Z) (nr nw : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    munch [(BI + 96, BI + 104)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\
    stk asegs m' lo (bv_unsigned sp) /\
    rw_cells asegs m' (BI + 72) (bio_tail (Z_to_bv 64 (bv_unsigned nr + n)) nw) /\
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
               s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs).

Lemma bri_s1_walk : forall ra0 sp gp tp t0 t1 t2 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo BI OUT n PR meth : Z) (nr nw : word),
  lo <= bv_unsigned sp - 96 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 -> stk asegs m lo (bv_unsigned sp + -96) ->
  rw_cells asegs m (bv_unsigned sp + -96) (bri_frame s10' s9' s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  rw_cells asegs m BI (bio_head meth) -> rw_cells asegs m (BI + 72) (bio_tail nr nw) ->
  acc asegs m BI 128 -> 0 < BI -> BI mod 16 = 0 -> 0x10007fff8000 <= BI -> BI + 128 <= lo ->
  rw_cells asegs m PR [C8 (Z_to_bv 64 n)] -> rw_cells asegs m (PR / 8 + 2147450880) [C1 (Z_to_bv 8 0)] -> 0 < PR -> PR mod 8 = 0 -> PR + 8 <= 2^47 ->
  (BI + 128 <= PR \/ PR + 8 <= BI) -> 1 <= n < 2^31 -> mem_inv asegs m ->
  evt asegs (bri_s1_post ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 F fc BI n nr nw lo m)
    (MS (mkR (Z_to_bv 64 SITE_bri_brc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 PR)
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 n) (Z_to_bv 64 OUT) (Z_to_bv 64 BI) (Z_to_bv 64 (BI + 16)) (Z_to_bv 64 (-2)) (Z_to_bv 64 (BI + 8))
             (Z_to_bv 64 ((BI + 16) ≫ 3 + 2147450880)) (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 ((BI + 8) ≫ 3 + 2147450880)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_bri_brc) fc None m (seg_rom asegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 F fc m lo BI OUT n PR meth nr nw
    STK_ROOM STK_HI SP_HI STACK FRAME BIOHD BIOTL BIACC BI_POS BI_AL BI_HI BI_ROOM PRCELL PRSH PR_POS PR_AL PR_TOP PR_BI N_RNG MINV.
  unfold SITE_bri_brc, bio_head, bio_tail, bri_frame in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  pose proof (bv_unsigned_in_range 64 nr) as NRR.
  pose proof (munch_refl [(BI + 96, BI + 104)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (BI8 : BI mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (SHFP : sh_fp [(BI + 96, BI + 104)]) by sh_fp_lia.
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  pose proof PRSH as PRSHA. rewrite <- (shadow_spell1 PR ltac:(lia)) in PRSHA.
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
  | |- evt _ _ (MS _ _ (if bv_eqb z64 z64 then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (bv_eqb z64 z64) in
       change (bv_eqb z64 z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (negb (bv_eqb z64 z64)) in
       change (negb (bv_eqb z64 z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (sxb (Z_to_bv 8 0)) z64 then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (bv_eqb (sxb (Z_to_bv 8 0)) z64) in
       change (bv_eqb (sxb (Z_to_bv 8 0)) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) in
       change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) z64) in
       change (bv_eqb (Z_to_bv 64 x) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) z64)) in
       change (negb (bv_eqb (Z_to_bv 64 x) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (sx32 (Z_to_bv 64 ?x)) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_eqb (sx32 (Z_to_bv 64 x)) z64) in
       change (bv_eqb (sx32 (Z_to_bv 64 x)) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (sx32 (Z_to_bv 64 ?x)) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) in
       change (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_lts z64 (Z_to_bv 64 x)) in
       change (bv_lts z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_lts z64 (Z_to_bv 64 x))) in
       change (negb (bv_lts z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) z64) in
       change (bv_lts (Z_to_bv 64 x) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) z64)) in
       change (negb (bv_lts (Z_to_bv 64 x) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_leu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_leu z64 (Z_to_bv 64 x)) in
       change (bv_leu z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_leu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_leu z64 (Z_to_bv 64 x))) in
       change (negb (bv_leu z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_ltu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_ltu z64 (Z_to_bv 64 x)) in
       change (bv_ltu z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_ltu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_ltu z64 (Z_to_bv 64 x))) in
       change (negb (bv_ltu z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  end.
  rewrite <- (shadow_spell1 PR ltac:(lia)) in PRSH.
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
  | |- evt _ _ (MS _ _ (if bv_eqb z64 z64 then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (bv_eqb z64 z64) in
       change (bv_eqb z64 z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (negb (bv_eqb z64 z64)) in
       change (negb (bv_eqb z64 z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (sxb (Z_to_bv 8 0)) z64 then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (bv_eqb (sxb (Z_to_bv 8 0)) z64) in
       change (bv_eqb (sxb (Z_to_bv 8 0)) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) in
       change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) z64) in
       change (bv_eqb (Z_to_bv 64 x) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) z64)) in
       change (negb (bv_eqb (Z_to_bv 64 x) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (sx32 (Z_to_bv 64 ?x)) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_eqb (sx32 (Z_to_bv 64 x)) z64) in
       change (bv_eqb (sx32 (Z_to_bv 64 x)) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (sx32 (Z_to_bv 64 ?x)) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) in
       change (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_lts z64 (Z_to_bv 64 x)) in
       change (bv_lts z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_lts z64 (Z_to_bv 64 x))) in
       change (negb (bv_lts z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) z64) in
       change (bv_lts (Z_to_bv 64 x) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) z64)) in
       change (negb (bv_lts (Z_to_bv 64 x) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_leu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_leu z64 (Z_to_bv 64 x)) in
       change (bv_leu z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_leu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_leu z64 (Z_to_bv 64 x))) in
       change (negb (bv_leu z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_ltu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_ltu z64 (Z_to_bv 64 x)) in
       change (bv_ltu z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_ltu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_ltu z64 (Z_to_bv 64 x))) in
       change (negb (bv_ltu z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  end.
  replace (negb (bv_ltu (Z_to_bv 64 n) (Z_to_bv 64 n))) with true
    by (unfold bv_ltu; rewrite Z.ltb_irrefl; reflexivity).
  cbv iota.
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
  | |- evt _ _ (MS _ _ (if bv_eqb z64 z64 then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (bv_eqb z64 z64) in
       change (bv_eqb z64 z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (negb (bv_eqb z64 z64)) in
       change (negb (bv_eqb z64 z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (sxb (Z_to_bv 8 0)) z64 then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (bv_eqb (sxb (Z_to_bv 8 0)) z64) in
       change (bv_eqb (sxb (Z_to_bv 8 0)) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) in
       change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) z64) in
       change (bv_eqb (Z_to_bv 64 x) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) z64)) in
       change (negb (bv_eqb (Z_to_bv 64 x) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (sx32 (Z_to_bv 64 ?x)) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_eqb (sx32 (Z_to_bv 64 x)) z64) in
       change (bv_eqb (sx32 (Z_to_bv 64 x)) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (sx32 (Z_to_bv 64 ?x)) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) in
       change (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_lts z64 (Z_to_bv 64 x)) in
       change (bv_lts z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_lts z64 (Z_to_bv 64 x))) in
       change (negb (bv_lts z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) z64) in
       change (bv_lts (Z_to_bv 64 x) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) z64)) in
       change (negb (bv_lts (Z_to_bv 64 x) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_leu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_leu z64 (Z_to_bv 64 x)) in
       change (bv_leu z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_leu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_leu z64 (Z_to_bv 64 x))) in
       change (negb (bv_leu z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_ltu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_ltu z64 (Z_to_bv 64 x)) in
       change (bv_ltu z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_ltu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_ltu z64 (Z_to_bv 64 x))) in
       change (negb (bv_ltu z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  end.
  release_frame FRAME STACK (bv_unsigned sp).
  apply evt_done. unfold bri_s1_post, bio_tail. do 15 eexists.
  split; [exact MU|]. split; [exact WM|]. split; [exact MINV|]. split; [exact STACK|].
  split; [exact BIOTL|]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition br_s0_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (BI OUT n : Z) (F : bvmap 5 word) (fc : bv 32) (lo pd : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (j : list byte) (m' : mem),
    munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ img_untouched m' /\
    stk asegs m' lo (bv_unsigned sp + -96 - pd) /\ stk asegs m' (bv_unsigned sp + -96 - pd) (bv_unsigned sp + -96) /\
    rw_cells asegs m' (bv_unsigned sp + -96) (C8 (Z_to_bv 64 0) :: CB 8 j :: br_ftail s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) /\
    ms = MS (mkR (Z_to_bv 64 SITE_br_smalloc) (Z_to_bv 64 (bv_unsigned sp + -96 - pd)) gp tp t0 t1 t2 sp
               (Z_to_bv 64 (bv_unsigned sp + -96 - pd)) (Z_to_bv 64 64)
               (Z_to_bv 64 g_shadow_memory_dynamic_address) (sx32 (Z_to_bv 64 1)) a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 n) (Z_to_bv 64 OUT) (Z_to_bv 64 BI) s6 (Z_to_bv 64 2147450880) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (e_stack_malloc 0%nat)) fc None m' (seg_rom asegs).

Lemma br_s0_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo pd BI OUT n : Z),
  (pd = 0 \/ pd = 16) -> bv_unsigned sp mod 32 = pd -> 0 <= BI < 2^64 -> 0 <= OUT < 2^64 -> 0 <= n < 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 112 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)] -> mem_inv asegs m ->
  evt asegs (br_s0_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 BI OUT n F fc lo pd m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BI) (Z_to_bv 64 OUT) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_BIO_read) fc None m (seg_rom asegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pd BI OUT n
    PD_CASES SP_MOD BI_RNG OUT_RNG N_RNG STACK STK_ROOM STK_HI SP_HI IMG SHBASE DETECT MINV.
  unfold e_BIO_read in *; unfold g_shadow_memory_dynamic_address in SHBASE; unfold g_detect_stack_use_after_return in DETECT.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (UTFP : ut_fp [(bv_unsigned sp - 96, bv_unsigned sp)]) by ut_fp_lia.
  assert (SHFP : sh_fp [(bv_unsigned sp - 96, bv_unsigned sp)]) by sh_fp_lia.
  assert (PADM : (bv_unsigned sp + -96) mod 32 = pd)
    by (replace (bv_unsigned sp + -96) with (bv_unsigned sp + (-3) * 32) by lia; rewrite Z.mod_add by lia; exact SP_MOD).
  assert (SPLIT : forall (mm : mem) (lo1 mid hi1 : Z), lo1 <= mid <= hi1 -> stk asegs mm lo1 hi1 ->
                    stk asegs mm lo1 mid /\ stk asegs mm mid hi1).
  { intros mm lo1 mid hi1 HM (H1 & H2 & H3).
    split; (split; [lia|]; split; [lia|]; intros a Ha; apply H3; lia). }
  carve_frame 96%nat STACK.
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => lfix
  | |- evt _ _ (MS _ _ (Z_to_bv 64 1729468) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
  | |- evt _ _ (MS _ _ (if bv_eqb z64 z64 then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (bv_eqb z64 z64) in
       change (bv_eqb z64 z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (negb (bv_eqb z64 z64)) in
       change (negb (bv_eqb z64 z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (sxb (Z_to_bv 8 0)) z64 then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (bv_eqb (sxb (Z_to_bv 8 0)) z64) in
       change (bv_eqb (sxb (Z_to_bv 8 0)) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) in
       change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) z64) in
       change (bv_eqb (Z_to_bv 64 x) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) z64)) in
       change (negb (bv_eqb (Z_to_bv 64 x) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (sx32 (Z_to_bv 64 ?x)) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_eqb (sx32 (Z_to_bv 64 x)) z64) in
       change (bv_eqb (sx32 (Z_to_bv 64 x)) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (sx32 (Z_to_bv 64 ?x)) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) in
       change (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_lts z64 (Z_to_bv 64 x)) in
       change (bv_lts z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_lts z64 (Z_to_bv 64 x))) in
       change (negb (bv_lts z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) z64) in
       change (bv_lts (Z_to_bv 64 x) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) z64)) in
       change (negb (bv_lts (Z_to_bv 64 x) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_leu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_leu z64 (Z_to_bv 64 x)) in
       change (bv_leu z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_leu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_leu z64 (Z_to_bv 64 x))) in
       change (negb (bv_leu z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_ltu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_ltu z64 (Z_to_bv 64 x)) in
       change (bv_ltu z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_ltu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_ltu z64 (Z_to_bv 64 x))) in
       change (negb (bv_ltu z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  end.
  rewrite (land_m32_pad (bv_unsigned sp + -96) pd ltac:(lia) PADM).
  destruct (SPLIT _ lo (bv_unsigned sp + -96 - pd) (bv_unsigned sp + -96) ltac:(lia) STACK) as [STKLO STKPD].
  apply evt_done. unfold br_s0_post, br_ftail. do 2 eexists.
  split; [exact MU|]. split; [exact WM|]. split; [exact MINV|].
  split; [exact (ut_munch _ _ _ IMG MU UTFP)|].
  split; [exact STKLO|]. split; [exact STKPD|].
  split; [exact FR|]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition br_s1_post (sp gp tp t0 t1 t2 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word) (BI OUT n : Z)
    (F : bvmap 5 word) (fc : bv 32) (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' : word) (f lo pd : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (jj hj pj qj : list byte) (m' : mem),
    munch [(bv_unsigned sp - 96 - pd, bv_unsigned sp - 80); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450888)] m m' /\
    wmono asegs m m' /\ mem_inv asegs m' /\ img_untouched m' /\
    stk asegs m' lo (bv_unsigned sp + -96 - pd) /\ stk asegs m' (bv_unsigned sp + -96 - pd) (bv_unsigned sp + -96) /\
    rw_cells asegs m' (bv_unsigned sp + -96) (CB 16 jj :: br_ftail s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) /\
    rw_cells asegs m' f [C8 (Z_to_bv 64 BP_MAGIC); C8 (Z_to_bv 64 BR_DESCR); C8 (Z_to_bv 64 e_BIO_read);
                         CB 8 hj; CB 8 pj; CB 16 qj] /\
    rw_cells asegs m' (f / 8 + 2147450880) bp_shadow /\
    ms = MS (mkR (Z_to_bv 64 SITE_br_intern) (Z_to_bv 64 (bv_unsigned sp + -96 - pd)) gp tp t0 t1 t2 sp
               (Z_to_bv 64 (bv_unsigned sp + -96 - pd)) (Z_to_bv 64 BI) (Z_to_bv 64 OUT) (Z_to_bv 64 n)
               (Z_to_bv 64 (f + 32)) a4 a5 a6 a7
               (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 OUT) (Z_to_bv 64 BI) (Z_to_bv 64 (f + 32))
               (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 e_bio_read_intern) fc None m' (seg_rom asegs).

Lemma br_s1_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s6 s8 s9 s10 s11 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' : word) (F : bvmap 5 word) fc (m : mem) (f lo pd BI OUT n : Z) (j fj sj : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 112 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m ->
  rw_cells asegs m (bv_unsigned sp + -96) (C8 (Z_to_bv 64 0) :: CB 8 j :: br_ftail s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  stk asegs m (bv_unsigned sp + -96 - pd) (bv_unsigned sp + -96) -> stk asegs m lo (bv_unsigned sp + -96 - pd) ->
  rw_cells asegs m f [CB 56 fj] -> rw_cells asegs m (f / 8 + 2147450880) [CB 8 sj] ->
  0 <= BI < 2^64 -> 0 <= OUT < 2^64 -> 0 <= n < 2^31 ->
  mem_inv asegs m ->
  evt asegs (br_s1_post sp gp tp t0 t1 t2 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 BI OUT n F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' f lo pd m)
    (MS (mkR (Z_to_bv 64 SITE_br_smalloc) (Z_to_bv 64 (bv_unsigned sp + -96 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pd))
             (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) (Z_to_bv 64 OUT) (Z_to_bv 64 BI) s6 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_br_smalloc) fc None m (seg_rom asegs)).
Proof.
  intros sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s6 s8 s9 s10 s11 t3 t4 t5 t6 ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' F fc m f lo pd BI OUT n j fj sj
    PD_CASES F_POS F_AL F_HI F_ROOM F_VALID STK_ROOM STK_HI SP_HI IMG FRAME STKPD STKLO FCELLS FSHAD BI_RNG OUT_RNG N_RNG MINV.
  unfold SITE_br_smalloc, br_ftail in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  pose proof (munch_refl [(bv_unsigned sp - 96 - pd, bv_unsigned sp - 80); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450888)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (UTFP : ut_fp [(bv_unsigned sp - 96 - pd, bv_unsigned sp - 80); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450888)]).
  { apply ut_fp_cons; [unfold IMG_UT_LO, IMG_UT_HI in *; lia|].
    apply ut_fp_cons; [unfold IMG_UT_LO, IMG_UT_HI in *; lia|].
    apply ut_fp_cons; [unfold IMG_UT_LO, IMG_UT_HI in *; Z.div_mod_to_equations; lia|].
    apply ut_fp_nil. }
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (SGn : bv_signed (Z_to_bv 64 n) = n) by (apply SFModel.signed_of_Z; lia).
  destruct PD_CASES as [-> | ->].
  - replace (bv_unsigned sp + -96 - 0) with (bv_unsigned sp + -96) in * by lia.
    repeat lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => lfix
    | |- evt _ _ (MS _ _ (Z_to_bv 64 2323008) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    | |- evt _ _ (MS _ _ (if bv_eqb z64 z64 then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (bv_eqb z64 z64) in
         change (bv_eqb z64 z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (negb (bv_eqb z64 z64)) in
         change (negb (bv_eqb z64 z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sxb (Z_to_bv 8 0)) z64 then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (bv_eqb (sxb (Z_to_bv 8 0)) z64) in
         change (bv_eqb (sxb (Z_to_bv 8 0)) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) in
         change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) z64) in
         change (bv_eqb (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) z64)) in
         change (negb (bv_eqb (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sx32 (Z_to_bv 64 ?x)) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (sx32 (Z_to_bv 64 x)) z64) in
         change (bv_eqb (sx32 (Z_to_bv 64 x)) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sx32 (Z_to_bv 64 ?x)) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) in
         change (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_lts z64 (Z_to_bv 64 x)) in
         change (bv_lts z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_lts z64 (Z_to_bv 64 x))) in
         change (negb (bv_lts z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) z64) in
         change (bv_lts (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) z64)) in
         change (negb (bv_lts (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_leu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_leu z64 (Z_to_bv 64 x)) in
         change (bv_leu z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_leu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_leu z64 (Z_to_bv 64 x))) in
         change (negb (bv_leu z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_ltu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_ltu z64 (Z_to_bv 64 x)) in
         change (bv_ltu z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_ltu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_ltu z64 (Z_to_bv 64 x))) in
         change (negb (bv_ltu z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    end.
    if_cases FNZ; zify_cond FNZ; [| exfalso; lia].
    repeat lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => lfix
    | |- evt _ _ (MS _ _ (Z_to_bv 64 2323008) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    | |- evt _ _ (MS _ _ (if bv_eqb z64 z64 then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (bv_eqb z64 z64) in
         change (bv_eqb z64 z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (negb (bv_eqb z64 z64)) in
         change (negb (bv_eqb z64 z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sxb (Z_to_bv 8 0)) z64 then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (bv_eqb (sxb (Z_to_bv 8 0)) z64) in
         change (bv_eqb (sxb (Z_to_bv 8 0)) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) in
         change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) z64) in
         change (bv_eqb (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) z64)) in
         change (negb (bv_eqb (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sx32 (Z_to_bv 64 ?x)) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (sx32 (Z_to_bv 64 x)) z64) in
         change (bv_eqb (sx32 (Z_to_bv 64 x)) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sx32 (Z_to_bv 64 ?x)) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) in
         change (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_lts z64 (Z_to_bv 64 x)) in
         change (bv_lts z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_lts z64 (Z_to_bv 64 x))) in
         change (negb (bv_lts z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) z64) in
         change (bv_lts (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) z64)) in
         change (negb (bv_lts (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_leu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_leu z64 (Z_to_bv 64 x)) in
         change (bv_leu z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_leu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_leu z64 (Z_to_bv 64 x))) in
         change (negb (bv_leu z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_ltu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_ltu z64 (Z_to_bv 64 x)) in
         change (bv_ltu z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_ltu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_ltu z64 (Z_to_bv 64 x))) in
         change (negb (bv_ltu z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    end.
    rewrite (shadow_spell1 f ltac:(lia)).
    repeat lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => lfix
    | |- evt _ _ (MS _ _ (Z_to_bv 64 2323008) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    | |- evt _ _ (MS _ _ (if bv_eqb z64 z64 then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (bv_eqb z64 z64) in
         change (bv_eqb z64 z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (negb (bv_eqb z64 z64)) in
         change (negb (bv_eqb z64 z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sxb (Z_to_bv 8 0)) z64 then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (bv_eqb (sxb (Z_to_bv 8 0)) z64) in
         change (bv_eqb (sxb (Z_to_bv 8 0)) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) in
         change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) z64) in
         change (bv_eqb (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) z64)) in
         change (negb (bv_eqb (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sx32 (Z_to_bv 64 ?x)) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (sx32 (Z_to_bv 64 x)) z64) in
         change (bv_eqb (sx32 (Z_to_bv 64 x)) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sx32 (Z_to_bv 64 ?x)) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) in
         change (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_lts z64 (Z_to_bv 64 x)) in
         change (bv_lts z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_lts z64 (Z_to_bv 64 x))) in
         change (negb (bv_lts z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) z64) in
         change (bv_lts (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) z64)) in
         change (negb (bv_lts (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_leu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_leu z64 (Z_to_bv 64 x)) in
         change (bv_leu z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_leu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_leu z64 (Z_to_bv 64 x))) in
         change (negb (bv_leu z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_ltu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_ltu z64 (Z_to_bv 64 x)) in
         change (bv_ltu z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_ltu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_ltu z64 (Z_to_bv 64 x))) in
         change (negb (bv_ltu z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    end.
    if_cases NNEG; zify_cond NNEG; [exfalso; lia|].
    repeat lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => lfix
    | |- evt _ _ (MS _ _ (Z_to_bv 64 2323008) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    | |- evt _ _ (MS _ _ (if bv_eqb z64 z64 then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (bv_eqb z64 z64) in
         change (bv_eqb z64 z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (negb (bv_eqb z64 z64)) in
         change (negb (bv_eqb z64 z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sxb (Z_to_bv 8 0)) z64 then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (bv_eqb (sxb (Z_to_bv 8 0)) z64) in
         change (bv_eqb (sxb (Z_to_bv 8 0)) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) in
         change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) z64) in
         change (bv_eqb (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) z64)) in
         change (negb (bv_eqb (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sx32 (Z_to_bv 64 ?x)) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (sx32 (Z_to_bv 64 x)) z64) in
         change (bv_eqb (sx32 (Z_to_bv 64 x)) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sx32 (Z_to_bv 64 ?x)) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) in
         change (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_lts z64 (Z_to_bv 64 x)) in
         change (bv_lts z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_lts z64 (Z_to_bv 64 x))) in
         change (negb (bv_lts z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) z64) in
         change (bv_lts (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) z64)) in
         change (negb (bv_lts (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_leu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_leu z64 (Z_to_bv 64 x)) in
         change (bv_leu z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_leu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_leu z64 (Z_to_bv 64 x))) in
         change (negb (bv_leu z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_ltu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_ltu z64 (Z_to_bv 64 x)) in
         change (bv_ltu z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_ltu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_ltu z64 (Z_to_bv 64 x))) in
         change (negb (bv_ltu z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    end.
    apply (rw_cells_split_CB asegs _ f [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 249951); C8 (Z_to_bv 64 2322516)]
             32 _ [] [8; 8; 16]%nat) in FCELLS; [| reflexivity].
    cbn [mk_CB_cells app] in FCELLS.
    apply (rw_cells_blur _ _ [_; _] _) in FRAME.
    cbn [cells_size csize Nat.add] in FRAME.
    apply evt_done. unfold br_s1_post, br_ftail, BP_MAGIC, BR_DESCR, e_BIO_read, bp_shadow.
    replace (bv_unsigned sp - 96 - 0) with (bv_unsigned sp + -96) by lia.
    replace (bv_unsigned sp + -96 - 0) with (bv_unsigned sp + -96) by lia.
    do 5 eexists.
    split; [exact MU|]. split; [exact WM|]. split; [exact MINV|].
    split; [exact (ut_munch _ _ _ IMG MU UTFP)|].
    split; [exact STKLO|]. split; [exact STKPD|].
    split; [exact FRAME|]. split; [exact FCELLS|]. split; [exact FSHAD|].
    reflexivity.
  - carve_frame 16%nat STKPD.
    repeat lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => lfix
    | |- evt _ _ (MS _ _ (Z_to_bv 64 2323008) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    | |- evt _ _ (MS _ _ (if bv_eqb z64 z64 then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (bv_eqb z64 z64) in
         change (bv_eqb z64 z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (negb (bv_eqb z64 z64)) in
         change (negb (bv_eqb z64 z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sxb (Z_to_bv 8 0)) z64 then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (bv_eqb (sxb (Z_to_bv 8 0)) z64) in
         change (bv_eqb (sxb (Z_to_bv 8 0)) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) in
         change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) z64) in
         change (bv_eqb (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) z64)) in
         change (negb (bv_eqb (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sx32 (Z_to_bv 64 ?x)) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (sx32 (Z_to_bv 64 x)) z64) in
         change (bv_eqb (sx32 (Z_to_bv 64 x)) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sx32 (Z_to_bv 64 ?x)) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) in
         change (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_lts z64 (Z_to_bv 64 x)) in
         change (bv_lts z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_lts z64 (Z_to_bv 64 x))) in
         change (negb (bv_lts z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) z64) in
         change (bv_lts (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) z64)) in
         change (negb (bv_lts (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_leu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_leu z64 (Z_to_bv 64 x)) in
         change (bv_leu z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_leu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_leu z64 (Z_to_bv 64 x))) in
         change (negb (bv_leu z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_ltu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_ltu z64 (Z_to_bv 64 x)) in
         change (bv_ltu z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_ltu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_ltu z64 (Z_to_bv 64 x))) in
         change (negb (bv_ltu z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    end.
    if_cases FNZ; zify_cond FNZ; [| exfalso; lia].
    repeat lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => lfix
    | |- evt _ _ (MS _ _ (Z_to_bv 64 2323008) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    | |- evt _ _ (MS _ _ (if bv_eqb z64 z64 then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (bv_eqb z64 z64) in
         change (bv_eqb z64 z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (negb (bv_eqb z64 z64)) in
         change (negb (bv_eqb z64 z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sxb (Z_to_bv 8 0)) z64 then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (bv_eqb (sxb (Z_to_bv 8 0)) z64) in
         change (bv_eqb (sxb (Z_to_bv 8 0)) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) in
         change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) z64) in
         change (bv_eqb (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) z64)) in
         change (negb (bv_eqb (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sx32 (Z_to_bv 64 ?x)) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (sx32 (Z_to_bv 64 x)) z64) in
         change (bv_eqb (sx32 (Z_to_bv 64 x)) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sx32 (Z_to_bv 64 ?x)) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) in
         change (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_lts z64 (Z_to_bv 64 x)) in
         change (bv_lts z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_lts z64 (Z_to_bv 64 x))) in
         change (negb (bv_lts z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) z64) in
         change (bv_lts (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) z64)) in
         change (negb (bv_lts (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_leu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_leu z64 (Z_to_bv 64 x)) in
         change (bv_leu z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_leu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_leu z64 (Z_to_bv 64 x))) in
         change (negb (bv_leu z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_ltu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_ltu z64 (Z_to_bv 64 x)) in
         change (bv_ltu z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_ltu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_ltu z64 (Z_to_bv 64 x))) in
         change (negb (bv_ltu z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    end.
    rewrite (shadow_spell1 f ltac:(lia)).
    repeat lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => lfix
    | |- evt _ _ (MS _ _ (Z_to_bv 64 2323008) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    | |- evt _ _ (MS _ _ (if bv_eqb z64 z64 then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (bv_eqb z64 z64) in
         change (bv_eqb z64 z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (negb (bv_eqb z64 z64)) in
         change (negb (bv_eqb z64 z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sxb (Z_to_bv 8 0)) z64 then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (bv_eqb (sxb (Z_to_bv 8 0)) z64) in
         change (bv_eqb (sxb (Z_to_bv 8 0)) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) in
         change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) z64) in
         change (bv_eqb (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) z64)) in
         change (negb (bv_eqb (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sx32 (Z_to_bv 64 ?x)) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (sx32 (Z_to_bv 64 x)) z64) in
         change (bv_eqb (sx32 (Z_to_bv 64 x)) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sx32 (Z_to_bv 64 ?x)) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) in
         change (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_lts z64 (Z_to_bv 64 x)) in
         change (bv_lts z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_lts z64 (Z_to_bv 64 x))) in
         change (negb (bv_lts z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) z64) in
         change (bv_lts (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) z64)) in
         change (negb (bv_lts (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_leu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_leu z64 (Z_to_bv 64 x)) in
         change (bv_leu z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_leu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_leu z64 (Z_to_bv 64 x))) in
         change (negb (bv_leu z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_ltu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_ltu z64 (Z_to_bv 64 x)) in
         change (bv_ltu z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_ltu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_ltu z64 (Z_to_bv 64 x))) in
         change (negb (bv_ltu z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    end.
    if_cases NNEG; zify_cond NNEG; [exfalso; lia|].
    repeat lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => lfix
    | |- evt _ _ (MS _ _ (Z_to_bv 64 2323008) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    | |- evt _ _ (MS _ _ (if bv_eqb z64 z64 then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (bv_eqb z64 z64) in
         change (bv_eqb z64 z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (negb (bv_eqb z64 z64)) in
         change (negb (bv_eqb z64 z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sxb (Z_to_bv 8 0)) z64 then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (bv_eqb (sxb (Z_to_bv 8 0)) z64) in
         change (bv_eqb (sxb (Z_to_bv 8 0)) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
         let v := eval vm_compute in (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) in
         change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) z64) in
         change (bv_eqb (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) z64)) in
         change (negb (bv_eqb (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (sx32 (Z_to_bv 64 ?x)) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_eqb (sx32 (Z_to_bv 64 x)) z64) in
         change (bv_eqb (sx32 (Z_to_bv 64 x)) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (sx32 (Z_to_bv 64 ?x)) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) in
         change (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_lts z64 (Z_to_bv 64 x)) in
         change (bv_lts z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_lts z64 (Z_to_bv 64 x))) in
         change (negb (bv_lts z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) z64) in
         change (bv_lts (Z_to_bv 64 x) z64) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) z64)) in
         change (negb (bv_lts (Z_to_bv 64 x) z64)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_leu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_leu z64 (Z_to_bv 64 x)) in
         change (bv_leu z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_leu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_leu z64 (Z_to_bv 64 x))) in
         change (negb (bv_leu z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_ltu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (bv_ltu z64 (Z_to_bv 64 x)) in
         change (bv_ltu z64 (Z_to_bv 64 x)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_ltu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
         is_Zlit x; let v := eval vm_compute in (negb (bv_ltu z64 (Z_to_bv 64 x))) in
         change (negb (bv_ltu z64 (Z_to_bv 64 x))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) in
         change (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
    | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
         is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) in
         change (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
    end.
    release_frame FR STKPD (bv_unsigned sp + -96).
    apply (rw_cells_split_CB asegs _ f [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 249951); C8 (Z_to_bv 64 2322516)]
             32 _ [] [8; 8; 16]%nat) in FCELLS; [| reflexivity].
    cbn [mk_CB_cells app] in FCELLS.
    apply (rw_cells_blur _ _ [_; _] _) in FRAME.
    cbn [cells_size csize Nat.add] in FRAME.
    apply evt_done. unfold br_s1_post, br_ftail, BP_MAGIC, BR_DESCR, e_BIO_read, bp_shadow.
    replace (bv_unsigned sp - 96 - 16) with (bv_unsigned sp + -112) by lia.
    replace (bv_unsigned sp + -96 - 16) with (bv_unsigned sp + -112) by lia.
    do 5 eexists.
    split; [exact MU|]. split; [exact WM|]. split; [exact MINV|].
    split; [exact (ut_munch _ _ _ IMG MU UTFP)|].
    split; [exact STKLO|]. split; [exact STKPD|].
    split; [exact FRAME|]. split; [exact FCELLS|]. split; [exact FSHAD|].
    reflexivity.
Qed.

(* [comment removed for export] *)
Definition br_s2_post (sp gp tp : word) (BI OUT n : Z) (F : bvmap 5 word)
    (fc : bv 32) (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 : word) (f lo pd : Z) (j : list byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists (ra1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (hj : list byte) (m' : mem),
    munch [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450888)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\
    stk asegs m' lo (bv_unsigned sp + -96 - pd) /\ stk asegs m' (bv_unsigned sp + -96 - pd) (bv_unsigned sp + -96) /\
    rw_cells asegs m' (bv_unsigned sp + -96) (CB 16 j :: br_ftail s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) /\
    rw_cells asegs m' f [C8 (Z_to_bv 64 1172321806); C8 (Z_to_bv 64 BR_DESCR); C8 (Z_to_bv 64 e_BIO_read); CB 8 hj] /\
    ms = MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -96 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pd))
               (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 OUT) (Z_to_bv 64 BI)
               (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SITE_br_release) fc None m' (seg_rom asegs).

Lemma br_s2_walk : forall sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6
    (ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' : word) (F : bvmap 5 word) fc (m : mem) (f lo pd BI OUT n : Z) (hj j : list byte),
  (pd = 0 \/ pd = 16) -> 0 < f -> f mod 64 = 0 -> 0xbc6000 <= f -> f + 64 <= lo -> (f + 64 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  lo <= bv_unsigned sp - 112 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -96) (CB 16 j :: br_ftail s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  stk asegs m (bv_unsigned sp + -96 - pd) (bv_unsigned sp + -96) -> stk asegs m lo (bv_unsigned sp + -96 - pd) ->
  rw_cells asegs m f [C8 (Z_to_bv 64 BP_MAGIC); C8 (Z_to_bv 64 BR_DESCR); C8 (Z_to_bv 64 e_BIO_read); CB 8 hj] -> rw_cells asegs m (f + 32) [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m (f / 8 + 2147450880) bp_shadow ->
  1 <= n < 2^31 ->
  mem_inv asegs m ->
  evt asegs (br_s2_post sp gp tp BI OUT n F fc ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 f lo pd j m)
    (MS (mkR (Z_to_bv 64 SITE_br_intern) (Z_to_bv 64 (bv_unsigned sp + -96 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pd))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 OUT) (Z_to_bv 64 BI) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f)
             s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_br_intern) fc None m (seg_rom asegs)).
Proof.
  intros sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 ra0 s0' s1' s2' s3' s4' s5' s6' s7' s8' F fc m f lo pd BI OUT n hj j
    PD_CASES F_POS F_AL F_HI F_ROOM F_VALID STK_ROOM STK_HI SP_HI FRAME STKPD STKLO FCELLS FPR FSHAD N_RNG MINV.
  unfold SITE_br_intern, br_ftail, bp_shadow, BP_MAGIC, BR_DESCR, e_BIO_read in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450888)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (SX : sx32 (Z_to_bv 64 n) = Z_to_bv 64 n).
  { unfold sx32. f_equal. rewrite (unsigned_lit n ltac:(lia)). unfold bv_swrap, bv_wrap.
    change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
    rewrite Z.mod_small by lia. lia. }
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => lfix
  | |- evt _ _ (MS _ _ (Z_to_bv 64 2322912) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
  | |- evt _ _ (MS _ _ (if bv_eqb z64 z64 then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (bv_eqb z64 z64) in
       change (bv_eqb z64 z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (negb (bv_eqb z64 z64)) in
       change (negb (bv_eqb z64 z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (sxb (Z_to_bv 8 0)) z64 then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (bv_eqb (sxb (Z_to_bv 8 0)) z64) in
       change (bv_eqb (sxb (Z_to_bv 8 0)) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) in
       change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) z64) in
       change (bv_eqb (Z_to_bv 64 x) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) z64)) in
       change (negb (bv_eqb (Z_to_bv 64 x) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (sx32 (Z_to_bv 64 ?x)) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_eqb (sx32 (Z_to_bv 64 x)) z64) in
       change (bv_eqb (sx32 (Z_to_bv 64 x)) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (sx32 (Z_to_bv 64 ?x)) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) in
       change (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_lts z64 (Z_to_bv 64 x)) in
       change (bv_lts z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_lts z64 (Z_to_bv 64 x))) in
       change (negb (bv_lts z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) z64) in
       change (bv_lts (Z_to_bv 64 x) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) z64)) in
       change (negb (bv_lts (Z_to_bv 64 x) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_leu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_leu z64 (Z_to_bv 64 x)) in
       change (bv_leu z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_leu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_leu z64 (Z_to_bv 64 x))) in
       change (negb (bv_leu z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_ltu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_ltu z64 (Z_to_bv 64 x)) in
       change (bv_ltu z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_ltu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_ltu z64 (Z_to_bv 64 x))) in
       change (negb (bv_ltu z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  end.
  if_cases FNZ2; zify_cond FNZ2; [exfalso; lia|].
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => lfix
  | |- evt _ _ (MS _ _ (Z_to_bv 64 2322912) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
  | |- evt _ _ (MS _ _ (if bv_eqb z64 z64 then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (bv_eqb z64 z64) in
       change (bv_eqb z64 z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (negb (bv_eqb z64 z64)) in
       change (negb (bv_eqb z64 z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (sxb (Z_to_bv 8 0)) z64 then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (bv_eqb (sxb (Z_to_bv 8 0)) z64) in
       change (bv_eqb (sxb (Z_to_bv 8 0)) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) in
       change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) z64) in
       change (bv_eqb (Z_to_bv 64 x) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) z64)) in
       change (negb (bv_eqb (Z_to_bv 64 x) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (sx32 (Z_to_bv 64 ?x)) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_eqb (sx32 (Z_to_bv 64 x)) z64) in
       change (bv_eqb (sx32 (Z_to_bv 64 x)) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (sx32 (Z_to_bv 64 ?x)) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) in
       change (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_lts z64 (Z_to_bv 64 x)) in
       change (bv_lts z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_lts z64 (Z_to_bv 64 x))) in
       change (negb (bv_lts z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) z64) in
       change (bv_lts (Z_to_bv 64 x) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) z64)) in
       change (negb (bv_lts (Z_to_bv 64 x) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_leu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_leu z64 (Z_to_bv 64 x)) in
       change (bv_leu z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_leu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_leu z64 (Z_to_bv 64 x))) in
       change (negb (bv_leu z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_ltu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_ltu z64 (Z_to_bv 64 x)) in
       change (bv_ltu z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_ltu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_ltu z64 (Z_to_bv 64 x))) in
       change (negb (bv_ltu z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  end.
  rewrite SX.
  apply evt_done. unfold br_s2_post, br_ftail, BR_DESCR, e_BIO_read, SITE_br_release. do 17 eexists.
  split; [exact MU|]. split; [exact WM|]. split; [exact MINV|].
  split; [exact STKLO|]. split; [exact STKPD|].
  split; [exact FRAME|]. split; [exact FCELLS|]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition br_s3_post (ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 : word) (n : Z)
    (F : bvmap 5 word) (fc : bv 32) (fl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\
    stk asegs m' lo (bv_unsigned sp) /\
    rw_cells asegs m' fl [C1 (Z_to_bv 8 0)] /\
    ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0' s1' (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
               s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra0) fc None m' (seg_rom asegs).

Lemma br_s3_walk : forall ra1 ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (s0' s1' s2' s3' s4' s5' s6' s7' s8' : word) (F : bvmap 5 word) fc (m : mem) (f fl lo pd n : Z) (j : list byte),
  (pd = 0 \/ pd = 16) -> lo <= bv_unsigned sp - 112 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  0 < f -> f + 64 <= lo -> 0 < fl -> fl + 1 <= lo -> 0 <= n < 2^31 ->
  stk asegs m lo (bv_unsigned sp + -96 - pd) -> stk asegs m (bv_unsigned sp + -96 - pd) (bv_unsigned sp + -96) ->
  rw_cells asegs m (bv_unsigned sp + -96) (CB 16 j :: br_ftail s8' s7' s6' s5' s4' s3' s2' s1' s0' ra0) ->
  ro_cells asegs m (f + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (br_s3_post ra0 sp gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 n F fc fl lo m)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -96 - pd)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -96 - pd))
             (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 f) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SITE_br_release) fc None m (seg_rom asegs)).
Proof.
  intros ra1 ra0 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0' s1' s2' s3' s4' s5' s6' s7' s8' F fc m f fl lo pd n j
    PD_CASES STK_ROOM STK_HI SP_HI F_POS F_ROOM FL_POS FL_ROOM N_RNG STKLO STKPD FRAME FPTR FLAG MINV.
  unfold SITE_br_release, br_ftail in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => lfix
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
  | |- evt _ _ (MS _ _ (if bv_eqb z64 z64 then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (bv_eqb z64 z64) in
       change (bv_eqb z64 z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb z64 z64) then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (negb (bv_eqb z64 z64)) in
       change (negb (bv_eqb z64 z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (sxb (Z_to_bv 8 0)) z64 then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (bv_eqb (sxb (Z_to_bv 8 0)) z64) in
       change (bv_eqb (sxb (Z_to_bv 8 0)) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (sxb (Z_to_bv 8 0)) z64) then _ else _) _ _ _ _) =>
       let v := eval vm_compute in (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) in
       change (negb (bv_eqb (sxb (Z_to_bv 8 0)) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) z64) in
       change (bv_eqb (Z_to_bv 64 x) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) z64)) in
       change (negb (bv_eqb (Z_to_bv 64 x) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (sx32 (Z_to_bv 64 ?x)) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_eqb (sx32 (Z_to_bv 64 x)) z64) in
       change (bv_eqb (sx32 (Z_to_bv 64 x)) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (sx32 (Z_to_bv 64 ?x)) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) in
       change (negb (bv_eqb (sx32 (Z_to_bv 64 x)) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_lts z64 (Z_to_bv 64 x)) in
       change (bv_lts z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_lts z64 (Z_to_bv 64 x))) in
       change (negb (bv_lts z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) z64 then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) z64) in
       change (bv_lts (Z_to_bv 64 x) z64) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) z64) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) z64)) in
       change (negb (bv_lts (Z_to_bv 64 x) z64)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_leu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_leu z64 (Z_to_bv 64 x)) in
       change (bv_leu z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_leu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_leu z64 (Z_to_bv 64 x))) in
       change (negb (bv_leu z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_ltu z64 (Z_to_bv 64 ?x) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (bv_ltu z64 (Z_to_bv 64 x)) in
       change (bv_ltu z64 (Z_to_bv 64 x)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_ltu z64 (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
       is_Zlit x; let v := eval vm_compute in (negb (bv_ltu z64 (Z_to_bv 64 x))) in
       change (negb (bv_ltu z64 (Z_to_bv 64 x))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_ltu (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_lts (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  | |- evt _ _ (MS _ _ (if bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) in
       change (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) with v; cbv iota
  | |- evt _ _ (MS _ _ (if negb (bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)) then _ else _) _ _ _ _) =>
       is_Zlit x; is_Zlit y; let v := eval vm_compute in (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) in
       change (negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y))) with v; cbv iota
  end.
  pose proof (stk_merge asegs _ lo (bv_unsigned sp + -96 - pd) (bv_unsigned sp + -96) STKLO STKPD ltac:(lia)) as STK96.
  release_frame FRAME STK96 (bv_unsigned sp).
  apply evt_done. unfold br_s3_post. do 15 eexists.
  split; [exact MU|]. split; [exact WM|]. split; [exact MINV|].
  split; [exact STK96|]. split; [exact FLAG|]. reflexivity.
Qed.

Section CBrc.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis GO_memmeth : GOBJ M_MEM_A 112.
Hypothesis GO_secmeth : GOBJ M_SECMEM_A 112.
Hypothesis C_RD : read_data_stmt RT.

Lemma meth_bread_sh : forall (Σ : rts RT) (m : mem) meth, ART RT Σ m -> (meth = M_MEM_A \/ meth = M_SECMEM_A) ->
  ro_cells asegs m ((meth + 40) / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
  intros Σ m meth RUN MEM_OR_SEC.
  assert (SIZED : GOBJ meth 112) by (destruct MEM_OR_SEC as [-> | ->]; assumption).
  assert (GRAIN : (meth + 40) mod 8 = 0) by (destruct MEM_OR_SEC as [-> | ->]; reflexivity).
  pose proof (afp_gsh_byte RT GOBJ AFP Σ m meth 112 (meth + 40) RUN SIZED ltac:(lia) ltac:(lia) GRAIN) as TAIL.
  replace (meth + 112 - (meth + 40)) with 72 in TAIL by lia.
  exact TAIL.
Qed.

(* [comment removed for export] *)
Definition bread_conv_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo BI BB BM R D len max off fl OUT n PR meth : Z)
    (rrw numw padw rmaxw rflw : word) (oldb : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 OUT -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 PR ->
  (meth = M_MEM_A \/ meth = M_SECMEM_A) ->
  rw_cells asegs m BI (bio_head meth) -> In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw rflw) ->
  In (D, max) (rt_live RT Σ) -> D <> BI -> D <> R ->
  0 <= off -> off <= len -> 1 <= n <= len - off -> len <= max -> max < 2 ^ 31 - 1 ->
  dst_blk (rt_live RT Σ) OUT n [BI; R; D] ->
  rw_cells asegs m PR [CB 8 oldb] -> rw_cells asegs m (PR / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  0 < PR -> PR mod 8 = 0 -> PR + 8 <= lo -> (PR + 8 <= 2147450880 \/ 17594333495296 <= PR) ->
  (BI + 128 <= PR \/ PR + 8 <= BI) -> (R + 32 <= PR \/ PR + 8 <= R) ->
  (forall x : Z, PR <= x < PR + 8 \/ x = PR / 8 + 2147450880 ->
     aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x /\
     outside [(BI + 40, BI + 72); (R, R + 32); (OUT, OUT + n)] x) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 64 + 96 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_bread_conv m)))
    (ASTA RT Σ PMc (fun ms => exists (rmaxw' : word) (m' : mem),
           ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after RT Σ (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) ((PR, PR + 8) :: RD_W BI R OUT n) m m'
           /\ rw_cells asegs m' BI (bio_head meth)
           /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (Z.land (fl - fl mod 16) 18446744073709551487) rrw numw padw (Z_to_bv 64 BB))
           /\ rw_cells asegs m' R (readp_cells len D (off + n) rmaxw' rflw)
           /\ rw_cells asegs m' PR [C8 (Z_to_bv 64 n)]
           /\ (exists bsr : list byte, bytes_at asegs m (D + off) bsr /\ Z.of_nat (length bsr) = n /\ bytes_at asegs m' OUT bsr))).

Theorem bread_conv_cps : bread_conv_stmt.
Proof.
  unfold bread_conv_stmt.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo BI BB BM R D len max off fl OUT n PR meth rrw numw padw rmaxw rflw oldb
    FDO MST -> -> -> -> -> METH BIOHD INBI BIAL BIOW1 FLOK INBB BBAL BBC INR RAL RC IND NDBI NDR
    OFF0 OFFLE HN LENMAX MAXB DST PRCELL PRSH PRPOS PRAL PRROOM PRVALID PRBI PRRD PRKEEP ART0 MI0 CALL STKROOM.
  destruct (af_client_consts RT AF Σ m ART0) as (GOTSH & SHBASE & GOTUAR & DETECT & IMG).
  pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ART0 INBI)) as BIACC.
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BIPOS & BIBELOW & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BITOP.
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (BBPOS & BBBELOW & _).
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (RPOS & RBELOW & _).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof CALL as (STK & LOWIN & LOROOM & SPTOP & SPAL).
  destruct DST as (pO & kO & INO & OLO & OHI & ONE).
  pose proof (af_live_range RT AF Σ m pO kO ART0 INO) as (OPOS & OBELOW & _).
  assert (LOHI : 17594333495296 <= lo) by (unfold STACK_WIN in *; lia).
  assert (SPHI : bv_unsigned sp <= 2 ^ 47) by (unfold USTACK_TOP in *; lia).
  assert (BIROOM : BI + 128 <= lo) by (unfold STACK_WIN in *; lia).
  assert (SPROOM : lo <= bv_unsigned sp - 64) by (unfold RT_STACK in *; lia).
  assert (OUTR : 0 <= OUT < 2 ^ 64) by (unfold STACK_WIN in *; lia).
  assert (NR : 1 <= n < 2 ^ 31 - 1) by lia.
  assert (PRR : 0 <= PR < 2 ^ 64) by lia.
  assert (BIR : BI + 128 <= R \/ R + 32 <= BI)
    by (apply (live_ne_apart RT AF Σ m BI 128 R 32 ART0 INBI INR); intros E; injection E; intros; lia).
  assert (BIO : BI + 128 <= pO \/ pO + kO <= BI)
    by (apply (live_ne_apart RT AF Σ m BI 128 pO kO ART0 INBI INO); intros E; injection E; intros; subst;
        apply ONE; left; reflexivity).
  assert (ROO : R + 32 <= pO \/ pO + kO <= R)
    by (apply (live_ne_apart RT AF Σ m R 32 pO kO ART0 INR INO); intros E; injection E; intros; subst;
        apply ONE; right; left; reflexivity).
  pose proof (meth_bread_sh Σ m meth ART0 METH) as METHSH.
  intros T c HA Hk.
  pose proof (brc_s0_walk ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo BI OUT n PR meth
                SPROOM LOHI SPHI STK IMG SHBASE METH BIOHD BIACC BIPOS BIAL BITOP BIROOM METHSH OUTR NR PRR MI0) as W0.
  cl_lift W0 HA c1 HA1.
  destruct (ASTA_unpack RT Σ PMc _ c1 HA1) as (ms1 & (jf & m1 & MU1 & WM1 & MI1 & STK1 & FR1 & ->) & HA2).
  unfold bio_head in BIOHD; unfold bio_w1_cells in BIOW1; unfold readp_cells in RC.
  transport_after_call asegs m m1 MU1 WM1.
  cl_eu (bv_unsigned sp) (-64) EU64.
  eapply (cps_realizes asegs _ _ T c1); [ | exact HA2 | ].
  - eapply C_RD.
    + exact FDO.
    + exact MST.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exact INBI.
    + exact BIAL.
    + exact BIOW1.
    + exact FLOK.
    + exact INBB.
    + exact BBAL.
    + exact BBC.
    + exact INR.
    + exact RAL.
    + exact RC.
    + exact IND.
    + exact NDBI.
    + exact NDR.
    + lia.
    + exact LENMAX.
    + lia.
    + lia.
    + exists pO, kO. split; [exact INO|]. split; [lia|]. split; [lia| exact ONE].
    + exact (cl_seg_ART RT AF Σ m m1 (bv_unsigned sp) 64 [] ART0 ltac:(unfold STACK_WIN in *; lia)
               ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x HX; exfalso; exact (HX I)) WM1).
    + exact MI1.
    + cl_call_ok EU64 STK1 LOWIN SPAL 4.
    + rewrite EU64. unfold RT_STACK in *. lia.
  - intros c2 HA3.
    replace ((len - off) `min` n) with n in HA3 by (symmetry; apply Z.min_r; lia).
    destruct (ASTA_unpack RT Σ PMc _ c2 HA3) as (ms2 & (rmx & m2 & RS2 & AFT2 & PRES2 & BIOW2 & RC2 & BSR) & HA4).
    destruct RS2 as (q0 & q1 & q2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & q3 & q4 & q5 & q6 & F2 & fc2 & ->).
    destruct AFT2 as (ART2 & MI2 & WM2 & STK2).
    rewrite EU64 in STK2, PRES2.
    rewrite (ret_pc_even SITE_brc_read ltac:(unfold SITE_brc_read; lia) ltac:(reflexivity)) in HA4.
    assert (OUTROOM : OUT + n <= lo) by (unfold STACK_WIN in *; lia).
    assert (ACLM : forall x : Z, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x ->
                                 aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp + -64) x)
      by (intros x [HI|HI]; [left; lia | right; exact HI]).
    assert (FRK : rw_cells asegs m2 (bv_unsigned sp + -64) (brc_frame (CB 8 jf) s5 s4 s3 s2 s1 s0 ra)).
    { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2].
      intros x HX. cbn [cells_size csize Nat.add brc_frame] in HX.
      apply PRES2; [left; unfold USTACK_TOP in *; lia|].
      unfold RD_W. cbn [outside]. repeat split; unfold STACK_WIN in *; lia. }
    assert (PRK : rw_cells asegs m2 PR [CB 8 oldb]).
    { apply (rw_cells_agree asegs m1 m2 _ _ PRCELL); [| exact WM2].
      intros x HX. cbn [cells_size csize Nat.add bio_head brc_frame] in HX.
      destruct (PRKEEP (bv_unsigned x) (or_introl HX)) as [ACx OUTx]. cbn [outside] in OUTx.
      apply PRES2; [exact (ACLM _ ACx)|]. unfold RD_W. cbn [outside]. repeat split; lia. }
    assert (PRSK : rw_cells asegs m2 (PR / 8 + 2147450880) [C1 (Z_to_bv 8 0)]).
    { apply (rw_cells_agree asegs m1 m2 _ _ PRSH); [| exact WM2].
      intros x HX. cbn [cells_size csize Nat.add bio_head brc_frame] in HX.
      assert (EX : bv_unsigned x = PR / 8 + 2147450880) by lia.
      destruct (PRKEEP (bv_unsigned x) (or_intror EX)) as [ACx OUTx]. cbn [outside] in OUTx.
      apply PRES2; [exact (ACLM _ ACx)|]. unfold RD_W. cbn [outside]. repeat split; lia. }
    pose proof (proj2 (af_acc_live RT AF Σ m2 BI 128 ART2 INBI)) as BIACC2.
    pose proof (brc_s1_walk ra (Z_to_bv 64 SITE_brc_read) sp gp q0 q1 q2 s0 s1 s2 s3 s4 s5 b1 b2 b3 b4 b5 b6 b7
                  s6 s7 s8 s9 s10 s11 q3 q4 q5 q6 F2 fc2 m2 lo BI PR n (fl - fl mod 16) rrw numw padw (Z_to_bv 64 BB) oldb jf
                  SPROOM LOHI SPHI STK2 FRK BIOW2 ltac:(destruct FLOK; Z.div_mod_to_equations; lia)
                  BIACC2 BIPOS BIAL BITOP BIROOM PRK PRSK PRPOS PRAL PRROOM PRVALID PRBI ltac:(lia) MI2) as W1.
    cl_lift W1 HA4 c3 HA5.
    apply Hk.
    eapply (ASTA_conseq RT Σ PMc _ _ c3 HA5). cbv beta.
    intros ms (w0 & w1 & w2 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & m3 & MU3 & WM3 & MI3 & STK3 & BIOW3 & PRC3 & ->).
    assert (ACL3 : forall a : word, ~ aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned a) -> m3 a = m2 a).
    { intros a NAC. apply MU3. cbn [outside]. split; [| split; [| exact I]].
      { intros HIN. apply NAC. right; right; left. exists BI, 128. split; [exact INBI| lia]. }
      { intros HIN. apply NAC. destruct (PRKEEP (bv_unsigned a) (or_introl HIN)) as [ACp _]. exact ACp. } }
    assert (ART3 : ART RT Σ m3)
      by (exact (af_frame RT AF Σ m2 m3 (bv_unsigned sp) ART2 ltac:(unfold STACK_WIN in *; lia) ACL3 WM3)).
    assert (BIH2 : rw_cells asegs m2 BI (bio_head meth)).
    { apply (rw_cells_agree asegs m1 m2 _ _ BIOHD); [| exact WM2].
      intros x HX. cbn [cells_size csize Nat.add bio_head brc_frame] in HX.
      apply PRES2; [right; right; left; exists BI, 128; split; [exact INBI| lia]|].
      unfold RD_W. cbn [outside]. repeat split; unfold STACK_WIN in *; lia. }
    assert (BIH3 : rw_cells asegs m3 BI (bio_head meth)).
    { apply (rw_cells_agree asegs m2 m3 _ _ BIH2); [| exact WM3].
      intros x HX. cbn [cells_size csize Nat.add bio_head brc_frame] in HX. apply MU3.
      cbn [outside]. repeat split; lia. }
    assert (RC3 : rw_cells asegs m3 R (readp_cells len D (off + n) rmx rflw)).
    { apply (rw_cells_agree asegs m2 m3 _ _ RC2); [| exact WM3].
      intros x HX. cbn [cells_size csize Nat.add readp_cells] in HX. apply MU3.
      cbn [outside]. split; [lia|]. split; [| exact I].
      intros HPR. destruct (PRKEEP (bv_unsigned x) (or_introl HPR)) as [_ OUTx].
      cbn [outside] in OUTx. lia. }
    destruct BSR as (bsr & BSRm1 & BSRlen & BSRout).
    exists rmx, m3. split.
    { do 16 eexists. reflexivity. }
    split.
    { split; [exact ART3|]. split; [exact MI3|].
      split; [exact (wmono_trans asegs m m2 m3 (wmono_trans asegs m m1 m2 WM1 WM2) WM3)| exact STK3]. }
    split.
    { intros a ACa OUTa. cbn [outside] in OUTa. destruct OUTa as (OA & OB).
      transitivity (m2 a).
      1:{ apply MU3. cbn [outside]. split; [| split; [exact OA| exact I]].
        cbn [outside] in OB. clear - OB. destruct OB as (OB1 & _). lia. }
      - transitivity (m1 a); [apply PRES2; [exact (ACLM _ ACa)| exact OB]|].
        apply MU1. cbn [outside]. split; [| exact I].
        destruct (cl_split RT AF Σ m (bv_unsigned sp) 64 (bv_unsigned a) ART0
                    ltac:(unfold STACK_WIN in *; lia) ltac:(lia) ACa); lia. }
    split; [exact BIH3|]. split; [exact BIOW3|]. split; [exact RC3|]. split; [exact PRC3|].
    exists bsr. split; [| split; [exact BSRlen|]].
    2:{ apply (bytes_at_agree asegs m2 m3 _ _ BSRout).
        intros x HX. rewrite BSRlen in HX. apply MU3. cbn [outside]. split; [lia|]. split; [| exact I].
        intros HPR. destruct (PRKEEP (bv_unsigned x) (or_introl HPR)) as [_ OUTx].
        cbn [outside] in OUTx. lia. }
    apply (bytes_at_agree asegs m1 m _ _ BSRm1).
    intros x HX. symmetry. apply MU1. cbn [outside]. split; [| exact I].
    assert (DB : D + max <= lo) by (pose proof (af_live_range RT AF Σ m D max ART0 IND) as (_ & PB & _); unfold STACK_WIN in *; lia).
    lia.
Qed.
End CBrc.

Section CBri.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis GO_memmeth : GOBJ M_MEM_A 112.
Hypothesis GO_secmeth : GOBJ M_SECMEM_A 112.
Hypothesis C_RD : read_data_stmt RT.

Lemma meth_bread2_sh : forall (Σ : rts RT) (m : mem) meth, ART RT Σ m -> (meth = M_MEM_A \/ meth = M_SECMEM_A) ->
  ro_cells asegs m ((meth + 32) / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
  intros Σ m meth RUN MEM_OR_SEC.
  assert (SIZED : GOBJ meth 112) by (destruct MEM_OR_SEC as [-> | ->]; assumption).
  assert (GRAIN : (meth + 32) mod 8 = 0) by (destruct MEM_OR_SEC as [-> | ->]; reflexivity).
  pose proof (afp_gsh_byte RT GOBJ AFP Σ m meth 112 (meth + 32) RUN SIZED ltac:(lia) ltac:(lia) GRAIN) as TAIL.
  replace (meth + 112 - (meth + 32)) with 80 in TAIL by lia.
  exact TAIL.
Qed.

(* [comment removed for export] *)
Definition bri_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo BI BB BM R D len max off fl OUT n PR meth : Z)
    (rrw numw padw rmaxw rflw nr nw : word) (oldb : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 OUT -> a2 = Z_to_bv 64 n -> a3 = Z_to_bv 64 PR ->
  (meth = M_MEM_A \/ meth = M_SECMEM_A) ->
  rw_cells asegs m BI (bio_head meth) -> In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  rw_cells asegs m (BI + 72) (bio_tail nr nw) ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw rflw) ->
  In (D, max) (rt_live RT Σ) -> D <> BI -> D <> R ->
  0 <= off -> off <= len -> 1 <= n <= len - off -> len <= max -> max < 2 ^ 31 - 1 ->
  dst_blk (rt_live RT Σ) OUT n [BI; R; D] ->
  rw_cells asegs m PR [CB 8 oldb] -> rw_cells asegs m (PR / 8 + 2147450880) [C1 (Z_to_bv 8 0)] ->
  0 < PR -> PR mod 8 = 0 -> PR + 8 <= lo -> (PR + 8 <= 2147450880 \/ 17594333495296 <= PR) ->
  (BI + 128 <= PR \/ PR + 8 <= BI) -> (R + 32 <= PR \/ PR + 8 <= R) ->
  (forall x : Z, PR <= x < PR + 8 \/ x = PR / 8 + 2147450880 ->
     aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x /\
     outside [(BI + 40, BI + 72); (R, R + 32); (OUT, OUT + n)] x) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 96 + 64 + 96 <= bv_unsigned sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_bio_read_intern m)))
    (ASTA RT Σ PMc (fun ms => exists (rmaxw' : word) (m' : mem),
           ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
           /\ rt_after RT Σ (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) ((PR, PR + 8) :: (BI + 96, BI + 104) :: RD_W BI R OUT n) m m'
           /\ rw_cells asegs m' BI (bio_head meth)
           /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (Z.land (fl - fl mod 16) 18446744073709551487) rrw numw padw (Z_to_bv 64 BB))
           /\ rw_cells asegs m' (BI + 72) (bio_tail (Z_to_bv 64 (bv_unsigned nr + n)) nw)
           /\ rw_cells asegs m' R (readp_cells len D (off + n) rmaxw' rflw)
           /\ rw_cells asegs m' PR [C8 (Z_to_bv 64 n)]
           /\ (exists bsr : list byte, bytes_at asegs m (D + off) bsr /\ Z.of_nat (length bsr) = n /\ bytes_at asegs m' OUT bsr))).

Theorem bri_cps : bread_conv_stmt RT -> bri_stmt.
Proof.
  intros C_BC.
  unfold bri_stmt.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo BI BB BM R D len max off fl OUT n PR meth rrw numw padw rmaxw rflw nr nw oldb
    FDO MST -> -> -> -> -> METH BIOHD INBI BIAL BIOW1 FLOK BIOTL INBB BBAL BBC INR RAL RC IND NDBI NDR
    OFF0 OFFLE HN LENMAX MAXB DST PRCELL PRSH PRPOS PRAL PRROOM PRVALID PRBI PRRD PRKEEP ART0 MI0 CALL STKROOM.
  destruct (af_client_consts RT AF Σ m ART0) as (GOTSH & SHBASE & GOTUAR & DETECT & IMG).
  pose proof (proj2 (af_acc_live RT AF Σ m BI 128 ART0 INBI)) as BIACC.
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BIPOS & BIBELOW & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BITOP.
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (BBPOS & BBBELOW & _).
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (RPOS & RBELOW & _).
  pose proof (af_live_range RT AF Σ m D max ART0 IND) as (DPOS & DBELOW & _).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof CALL as (STK & LOWIN & LOROOM & SPTOP & SPAL).
  destruct DST as (pO & kO & INO & OLO & OHI & ONE).
  pose proof (af_live_range RT AF Σ m pO kO ART0 INO) as (OPOS & OBELOW & _).
  assert (LOHI : 17594333495296 <= lo) by (unfold STACK_WIN in *; lia).
  assert (SPHI : bv_unsigned sp <= 2 ^ 47) by (unfold USTACK_TOP in *; lia).
  assert (BIROOM : BI + 128 <= lo) by (unfold STACK_WIN in *; lia).
  assert (SPROOM : lo <= bv_unsigned sp - 96) by (unfold RT_STACK in *; lia).
  assert (OUTR : 0 <= OUT < 2 ^ 64) by (unfold STACK_WIN in *; lia).
  assert (OUTROOM : OUT + n <= lo) by (unfold STACK_WIN in *; lia).
  assert (NR : 0 <= n < 2 ^ 64) by lia.
  assert (PRR : 0 <= PR < 2 ^ 64) by lia.
  assert (BIR : BI + 128 <= R \/ R + 32 <= BI)
    by (apply (live_ne_apart RT AF Σ m BI 128 R 32 ART0 INBI INR); intros E; injection E; intros; lia).
  assert (BIO : BI + 128 <= pO \/ pO + kO <= BI)
    by (apply (live_ne_apart RT AF Σ m BI 128 pO kO ART0 INBI INO); intros E; injection E; intros; subst;
        apply ONE; left; reflexivity).
  pose proof (meth_bread2_sh Σ m meth ART0 METH) as METHSH2.
  intros T c HA Hk.
  pose proof (bri_s0_walk ra sp gp (Z_to_bv 64 12205808) t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m lo BI OUT n PR meth fl (Z_to_bv 64 1) rrw numw padw (Z_to_bv 64 BB)
                SPROOM LOHI SPHI STK IMG SHBASE METH BIOHD BIOW1 BIACC BIPOS BIAL BITOP BIROOM METHSH2 OUTR NR PRR MI0) as W0.
  cl_lift W0 HA c1 HA1.
  destruct (ASTA_unpack RT Σ PMc _ c1 HA1) as (ms1 & (m1 & MU1 & WM1 & MI1 & STK1 & FR1 & BIH1 & ->) & HA2).
  unfold bio_w1_cells in BIOW1; unfold readp_cells in RC; unfold bio_tail in BIOTL.
  transport_after_call asegs m m1 MU1 WM1.
  cl_eu (bv_unsigned sp) (-96) EU96.
  assert (ACLM : forall x : Z, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x ->
                               aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp + -96) x)
    by (intros x [HI|HI]; [left; lia | right; exact HI]).
  eapply (cps_realizes asegs _ _ T c1); [ | exact HA2 | ].
  - eapply C_BC.
    + exact FDO.
    + exact MST.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exact METH.
    + exact BIH1.
    + exact INBI.
    + exact BIAL.
    + exact BIOW1.
    + exact FLOK.
    + exact INBB.
    + exact BBAL.
    + exact BBC.
    + exact INR.
    + exact RAL.
    + exact RC.
    + exact IND.
    + exact NDBI.
    + exact NDR.
    + exact OFF0.
    + exact OFFLE.
    + exact HN.
    + exact LENMAX.
    + exact MAXB.
    + exists pO, kO. split; [exact INO|]. split; [lia|]. split; [lia| exact ONE].
    + exact PRCELL.
    + exact PRSH.
    + exact PRPOS.
    + exact PRAL.
    + exact PRROOM.
    + exact PRVALID.
    + exact PRBI.
    + exact PRRD.
    + rewrite EU96. intros x HX. destruct (PRKEEP x HX) as [ACx OUTx]. split; [exact (ACLM _ ACx)| exact OUTx].
    + exact (cl_seg_ART RT AF Σ m m1 (bv_unsigned sp) 96 [] ART0 ltac:(unfold STACK_WIN in *; lia)
               ltac:(unfold USTACK_TOP in *; lia) MU1 ltac:(intros x HX; exfalso; exact (HX I)) WM1).
    + exact MI1.
    + cl_call_ok EU96 STK1 LOWIN SPAL 6.
    + rewrite EU96. unfold RT_STACK in *. lia.
  - intros c2 HA3.
    destruct (ASTA_unpack RT Σ PMc _ c2 HA3)
      as (ms2 & (rmx & m2 & RS2 & AFT2 & PRES2 & BIH2 & BIOW2 & RC2 & PRC2 & BSR) & HA4).
    destruct RS2 as (q0 & q1 & q2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & q3 & q4 & q5 & q6 & F2 & fc2 & ->).
    destruct AFT2 as (ART2 & MI2 & WM2 & STK2).
    rewrite EU96 in STK2, PRES2.
    rewrite (ret_pc_even SITE_bri_brc ltac:(unfold SITE_bri_brc; lia) ltac:(reflexivity)) in HA4.
    assert (BIACC2 : acc asegs m2 BI 128)
      by (exact (proj2 (af_acc_live RT AF Σ m2 BI 128 ART2 INBI))).
    assert (FRK : rw_cells asegs m2 (bv_unsigned sp + -96) (bri_frame s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
    { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2].
      intros x HX. cbn [cells_size csize Nat.add bri_frame] in HX.
      apply PRES2; [left; unfold USTACK_TOP in *; lia|].
      cbn [outside]. unfold RD_W. cbn [outside]. repeat split; unfold STACK_WIN in *; lia. }
    assert (BTK : rw_cells asegs m2 (BI + 72) (bio_tail nr nw)).
    { apply (rw_cells_agree asegs m1 m2 _ _ BIOTL); [| exact WM2].
      intros x HX. cbn [cells_size csize Nat.add bio_tail] in HX.
      apply PRES2; [right; right; left; exists BI, 128; split; [exact INBI| lia]|].
      cbn [outside]. unfold RD_W. cbn [outside]. repeat split;
        first [ lia
              | intros HPR; destruct (PRKEEP (bv_unsigned x) (or_introl HPR)) as [_ OUTq];
                cbn [outside] in OUTq; lia
              | exact I ]. }
    assert (PRSK : rw_cells asegs m2 (PR / 8 + 2147450880) [C1 (Z_to_bv 8 0)]).
    { apply (rw_cells_agree asegs m1 m2 _ _ PRSH); [| exact WM2].
      intros x HX. cbn [cells_size csize Nat.add] in HX.
      assert (EX : bv_unsigned x = PR / 8 + 2147450880) by lia.
      destruct (PRKEEP (bv_unsigned x) (or_intror EX)) as [ACx OUTx]. cbn [outside] in OUTx.
      apply PRES2; [exact (ACLM _ ACx)|]. cbn [outside]. unfold RD_W. cbn [outside]. repeat split;
        first [ lia
              | intros HPR; destruct (PRKEEP (bv_unsigned x) (or_introl HPR)) as [_ OUTq];
                cbn [outside] in OUTq; lia
              | exact I ]. }
    pose proof (bri_s1_walk ra sp gp (Z_to_bv 64 12205808) q0 q1 q2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10
                  b1 b2 b3 b4 b5 b6 b7 s11 q3 q4 q5 q6 F2 fc2 m2 lo BI OUT n PR meth nr nw
                  SPROOM LOHI SPHI STK2 FRK BIH2 BTK BIACC2 BIPOS BIAL BITOP BIROOM PRC2 PRSK PRPOS PRAL
                  ltac:(unfold USTACK_TOP in *; lia) PRBI ltac:(lia) MI2) as W1.
    cl_lift W1 HA4 c3 HA5.
    apply Hk.
    eapply (ASTA_conseq RT Σ PMc _ _ c3 HA5). cbv beta.
    intros ms (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & m3 & MU3 & WM3 & MI3 & STK3 & BTL3 & ->).
    assert (ACL3 : forall a : word, ~ aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned a) -> m3 a = m2 a).
    { intros a NAC. apply MU3. cbn [outside]. split; [| exact I].
      intros HIN. apply NAC. right; right; left. exists BI, 128. split; [exact INBI| lia]. }
    assert (ART3 : ART RT Σ m3).
    { apply (af_frame RT AF Σ m2 m3 (bv_unsigned sp) ART2 ltac:(unfold STACK_WIN in *; lia));
        [| exact WM3].
      intros a NAC. apply ACL3. exact NAC. }
    assert (BIH3 : rw_cells asegs m3 BI (bio_head meth)).
    { apply (rw_cells_agree asegs m2 m3 _ _ BIH2); [| exact WM3].
      intros x HX. cbn [cells_size csize Nat.add bio_head] in HX. apply MU3. cbn [outside]. split; [lia| exact I]. }
    assert (BIOW3 : rw_cells asegs m3 (BI + 40)
              (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (Z.land (fl - fl mod 16) 18446744073709551487) rrw numw padw (Z_to_bv 64 BB))).
    { apply (rw_cells_agree asegs m2 m3 _ _ BIOW2); [| exact WM3].
      intros x HX. cbn [cells_size csize Nat.add bio_w1_cells] in HX. apply MU3. cbn [outside]. split; [lia| exact I]. }
    assert (RC3 : rw_cells asegs m3 R (readp_cells len D (off + n) rmx rflw)).
    { apply (rw_cells_agree asegs m2 m3 _ _ RC2); [| exact WM3].
      intros x HX. cbn [cells_size csize Nat.add readp_cells] in HX. apply MU3. cbn [outside]. split; [lia| exact I]. }
    assert (PRC3 : rw_cells asegs m3 PR [C8 (Z_to_bv 64 n)]).
    { apply (rw_cells_agree asegs m2 m3 _ _ PRC2); [| exact WM3].
      intros x HX. cbn [cells_size csize Nat.add] in HX. apply MU3. cbn [outside]. split; [lia| exact I]. }
    destruct BSR as (bsr & BSRm & BSRlen & BSRout).
    exists rmx, m3. split.
    { do 16 eexists. reflexivity. }
    split.
    { split; [exact ART3|]. split; [exact MI3|].
      split; [exact (wmono_trans asegs m m2 m3 (wmono_trans asegs m m1 m2 WM1 WM2) WM3)| exact STK3]. }
    split.
    { intros a ACa OUTa. cbn [outside] in OUTa. destruct OUTa as (OA & OB & OC).
      transitivity (m2 a).
      1:{ apply MU3. cbn [outside]. split; [exact OB| exact I]. }
      transitivity (m1 a).
      1:{ apply PRES2; [exact (ACLM _ ACa)|]. cbn [outside]. split; [exact OA| exact OC]. }
      apply MU1. cbn [outside]. split; [| exact I].
      destruct (cl_split RT AF Σ m (bv_unsigned sp) 96 (bv_unsigned a) ART0
                  ltac:(unfold STACK_WIN in *; lia) ltac:(lia) ACa); lia. }
    split; [exact BIH3|]. split; [exact BIOW3|]. split; [exact BTL3|]. split; [exact RC3|]. split; [exact PRC3|].
    exists bsr. split; [| split; [exact BSRlen|]].
    2:{ apply (bytes_at_agree asegs m2 m3 _ _ BSRout).
        intros x HX. rewrite BSRlen in HX. apply MU3. cbn [outside]. split; [| exact I].
        clear - HX OLO OHI BIO OPOS OBELOW. lia. }
    apply (bytes_at_agree asegs m1 m _ _ BSRm).
    intros x HX. rewrite BSRlen in HX. symmetry. apply MU1. cbn [outside]. split; [| exact I].
    clear - HX DPOS DBELOW LOWIN SPROOM OFF0 OFFLE HN LENMAX. unfold STACK_WIN in *. lia.
Qed.
End CBri.

Section CBread.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis GO_memmeth : GOBJ M_MEM_A 112.
Hypothesis GO_secmeth : GOBJ M_SECMEM_A 112.
Hypothesis C_RD : read_data_stmt RT.

(* [comment removed for export] *)
Definition bio_read_core_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo BI BB BM R D len max off fl OUT n meth : Z)
    (rrw numw padw rmaxw rflw nr nw : word),
  fdfs_only PMc -> mat_stable PMc ->
  tp = Z_to_bv 64 0xba3ef0 -> a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 OUT -> a2 = Z_to_bv 64 n ->
  (meth = M_MEM_A \/ meth = M_SECMEM_A) ->
  rw_cells asegs m BI (bio_head meth) -> In (BI, 128) (rt_live RT Σ) -> BI mod 16 = 0 ->
  rw_cells asegs m (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) fl rrw numw padw (Z_to_bv 64 BB)) -> fl_ok fl ->
  rw_cells asegs m (BI + 72) (bio_tail nr nw) ->
  In (BB, 16) (rt_live RT Σ) -> BB mod 16 = 0 -> rw_cells asegs m BB [C8 (Z_to_bv 64 BM); C8 (Z_to_bv 64 R)] ->
  In (R, 32) (rt_live RT Σ) -> R mod 16 = 0 -> rw_cells asegs m R (readp_cells len D off rmaxw rflw) ->
  In (D, max) (rt_live RT Σ) -> D <> BI -> D <> R ->
  0 <= off <= len -> 1 <= n <= len - off -> len <= max -> max < 2 ^ 31 - 1 ->
  dst_blk (rt_live RT Σ) OUT n [BI; R; D] ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  lo + RT_STACK + 112 + 96 + 64 + 96 <= bv_unsigned sp ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_BIO_read m)))
    (fun c => exists Σ' : rts RT,
       ASTA RT Σ' PMc (fun ms => exists (rmaxw' : word) (m' : mem),
           ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 n) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) ((BI + 96, BI + 104) :: RD_W BI R OUT n) m m'
           /\ rw_cells asegs m' BI (bio_head meth)
           /\ rw_cells asegs m' (BI + 40) (bio_w1_cells (Z_to_bv 64 1) (Z_to_bv 64 1) (Z.land (fl - fl mod 16) 18446744073709551487) rrw numw padw (Z_to_bv 64 BB))
           /\ rw_cells asegs m' (BI + 72) (bio_tail (Z_to_bv 64 (bv_unsigned nr + n)) nw)
           /\ rw_cells asegs m' R (readp_cells len D (off + n) rmaxw' rflw)) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - 1 <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem bio_read_core_cps : bio_read_core_stmt.
Proof.
  pose proof (bri_cps RT AF GOBJ AFP GO_memmeth GO_secmeth
                (bread_conv_cps RT AF GOBJ AFP GO_memmeth GO_secmeth C_RD)) as C_BRI.
  unfold bio_read_core_stmt.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo BI BB BM R D len max off fl OUT n meth rrw numw padw rmaxw rflw nr nw
    FDO MST -> -> -> -> METH BIOHD INBI BIAL BIOW1 FLOK BIOTL INBB BBAL BBC INR RAL RC IND NDBI NDR
    OFFLEN HN LENMAX MAXB DST ART0 MI0 CALL STKROOM FRMAX CRED.
  destruct (af_client_consts RT AF Σ m ART0) as (GOTSH & SHBASE & GOTUAR & DETECT & IMG).
  pose proof (af_live_range RT AF Σ m BI 128 ART0 INBI) as (BIPOS & BIBELOW & _).
  pose proof (af_live_range RT AF Σ m BB 16 ART0 INBB) as (BBPOS & BBBELOW & _).
  pose proof (af_live_range RT AF Σ m R 32 ART0 INR) as (RPOS & RBELOW & _).
  pose proof (af_live_range RT AF Σ m D max ART0 IND) as (DPOS & DBELOW & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m BI 128 ART0 INBI ltac:(lia)) as BITOP.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof CALL as (STK & LOWIN & LOROOM & SPTOP & SPAL).
  destruct DST as (pO & kO & INO & OLO & OHI & ONE).
  pose proof (af_live_range RT AF Σ m pO kO ART0 INO) as (OPOS & OBELOW & _).
  assert (LOHI : 17594333495296 <= lo) by (try unfold STACK_WIN in *; lia).
  assert (SPHI : bv_unsigned sp <= 2 ^ 47) by (try unfold USTACK_TOP in *; lia).
  assert (BIROOM : BI + 128 <= lo) by (try unfold STACK_WIN in *; lia).
  assert (SPROOM : lo <= bv_unsigned sp - 112) by (try unfold RT_STACK in *; lia).
  assert (OUTR : 0 <= OUT < 2 ^ 64) by (try unfold STACK_WIN in *; lia).
  assert (OUTROOM : OUT + n <= lo) by (try unfold STACK_WIN in *; lia).
  intros T c HA Hk.
  assert (PDC : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16)
    by (clear - SPAL; Z.div_mod_to_equations; lia).
  pose proof (br_s0_walk ra sp gp (Z_to_bv 64 12205808) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m lo (bv_unsigned sp mod 32) BI OUT n
                PDC eq_refl ltac:(lia) OUTR ltac:(lia) STK ltac:(lia) LOHI SPHI IMG SHBASE DETECT MI0) as W0.
  cl_lift W0 HA c1 HA1.
  destruct (ASTA_unpack RT Σ PMc _ c1 HA1) as (ms1 & (jf & m1 & MU1 & WM1 & MI1 & IMG1 & STKLO1 & STKPD1 & FR1 & ->) & HA2).
  unfold bio_head in BIOHD; unfold bio_w1_cells in BIOW1; unfold readp_cells in RC; unfold bio_tail in BIOTL.
  transport_after_call asegs m m1 MU1 WM1.
  assert (EUP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96 - bv_unsigned sp mod 32))
                = bv_unsigned sp + -96 - bv_unsigned sp mod 32)
    by (apply unsigned_lit; pose proof (Z.mod_pos_bound (bv_unsigned sp) 32 ltac:(lia));
        try unfold USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
  assert (ACLM : forall d x : Z, 0 <= d -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x ->
                                 aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp - d) x)
    by (intros d x HD [HI|HI]; [left; lia | right; exact HI]).
  eapply (cps_realizes asegs _ _ T c1); [ | exact HA2 | ].
  - eapply SM0.
    + exact FDO.
    + exact MST.
    + left; reflexivity.
    + reflexivity.
    + exact FRMAX.
    + exact CRED.
    + exact (cl_seg_ART RT AF Σ m m1 (bv_unsigned sp) 96 [] ART0 ltac:(try unfold STACK_WIN in *; lia)
               ltac:(try unfold USTACK_TOP in *; lia) MU1 ltac:(intros x HX; exfalso; exact (HX I)) WM1).
    + exact MI1.
    + unfold call_ok. rewrite EUP. split; [exact STKLO1|].
      split; [exact LOWIN|]. split; [try unfold RT_STACK in *; pose proof (Z.mod_pos_bound (bv_unsigned sp) 32 ltac:(lia)); lia|].
      split; [try unfold USTACK_TOP in *; pose proof (Z.mod_pos_bound (bv_unsigned sp) 32 ltac:(lia)); lia|].
      apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPAL; [| lia]. destruct SPAL as (qq & QQ).
      destruct PDC as [PZ|PZ]; rewrite PZ; [exists (qq - 6); lia | exists (qq - 7); lia].
  - intros c2 HA3.
    destruct HA3 as (Σ1 & f & HA3 & FRS1 & LV1 & SP1 & CR1 & FPOS & FAL & FTOP & CG1).
    destruct (ASTA_unpack RT Σ1 PMc _ c2 HA3) as (ms2 & (m2 & RS2 & AFT2 & PRES2 & WRF & WRS) & HA4).
    destruct RS2 as (q0 & q1 & q2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & q3 & q4 & q5 & q6 & F2 & fc2 & ->).
    destruct AFT2 as (ART2 & MI2 & WM2 & STK2).
    rewrite EUP in STK2, PRES2.
    rewrite (ret_pc_even SITE_br_smalloc ltac:(unfold SITE_br_smalloc; lia) ltac:(reflexivity)) in HA4.
    assert (INF : In (f, 0%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
    pose proof (af_frames_align RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FSEG).
    pose proof (af_frames_range RT AF Σ1 m2 f 0%nat ART2 INF) as (_ & FBELOW & _ & FLIVE).
    pose proof (af_frames_hi RT AF Σ1 m2 f 0%nat ART2 INF) as FHI.
    assert (FS0 : fs_size 0%nat = 64) by reflexivity.
    rewrite FS0 in FBELOW, FLIVE, FHI, WRF, WRS, FTOP.
    rewrite SP1 in FBELOW.
    destruct (wr_at_rw_CB m2 f 56 WRF ltac:(lia)) as (fj & FCELLS).
    destruct (wr_at_rw_CB m2 (shad f) 8 WRS ltac:(lia)) as (sj & FSHAD).
    unfold shad, SHB in FSHAD.
    replace (Z.to_nat 56) with 56%nat in FCELLS by reflexivity.
    replace (Z.to_nat 8) with 8%nat in FSHAD by reflexivity.
    assert (FRK : rw_cells asegs m2 (bv_unsigned sp + -96)
                    (C8 (Z_to_bv 64 0) :: CB 8 jf :: br_ftail s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
    { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2].
      intros x HX. cbn [cells_size csize Nat.add br_ftail] in HX.
      apply PRES2. left. pose proof (Z.mod_pos_bound (bv_unsigned sp) 32 ltac:(lia)).
      unfold USTACK_TOP in *. lia. }
    assert (STKPD2 : stk asegs m2 (bv_unsigned sp + -96 - bv_unsigned sp mod 32) (bv_unsigned sp + -96)).
    { apply (stk_agree_nw asegs m1 m2 _ _ STKPD1). intros x HX. apply PRES2.
      left. pose proof (Z.mod_pos_bound (bv_unsigned sp) 32 ltac:(lia)). unfold USTACK_TOP in *. lia. }
    assert (FROOM : f + 64 <= lo) by (try unfold STACK_WIN in *; lia).
    assert (FVALID : f + 64 <= 2147450880 \/ 17594333495296 <= f)
      by (destruct FHI as [HH|HH]; [left; lia | right; lia]).
    assert (BIRNG : 0 <= BI < 2 ^ 64) by (try unfold STACK_WIN in *; lia).
    assert (NRNG : 0 <= n < 2 ^ 31) by lia.
    destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHBASE2 & _ & DETECT2 & IMG2).
    pose proof (br_s1_walk sp gp (Z_to_bv 64 12205808) q0 q1 q2 b1 b2 b3 b4 b5 b6 b7 s2 s6 s8 s9 s10 s11 q3 q4 q5 q6
                  ra s0 s1 s2 s3 s4 s5 s6 s7 s8 F2 fc2 m2 f lo (bv_unsigned sp mod 32) BI OUT n jf fj sj
                  PDC FPOS FAL FSEG FROOM FVALID
                  SPROOM LOHI SPHI IMG2
                  FRK STKPD2 STK2 FCELLS FSHAD BIRNG OUTR NRNG MI2) as W1.
    cl_lift W1 HA4 c3 HA5.
    destruct (ASTA_unpack RT Σ1 PMc _ c3 HA5)
      as (ms3 & (jj & hj & pj & qj & m3 & MU3 & WM3 & MI3 & IMG3 & STKLO3 & STKPD3 & FRK3 & FC3 & FSH3 & ->) & HA6).
    assert (FS8 : f mod 8 = 0) by (clear - FAL; Z.div_mod_to_equations; lia).
    assert (ART3 : ART RT Σ1 m3).
    { apply (af_frame RT AF Σ1 m2 m3 (bv_unsigned sp + -96 - bv_unsigned sp mod 32) ART2
               ltac:(rewrite SP1; try unfold STACK_WIN in *; lia)); [| exact WM3].
      intros a NAC. apply MU3. cbn [outside]. split; [| split; [| split; [| exact I]]].
      { intros HIN. apply NAC. left. unfold USTACK_TOP in *. lia. }
      { intros HIN. apply NAC. right; right; right; left. exists f, 0%nat. split; [exact INF|]. rewrite FS0. lia. }
      { intros HIN. apply NAC. right; right; right; right. exists f, 0%nat. split; [exact INF|].
        unfold shad, SHB. rewrite FS0. clear - HIN FAL FS8 FPOS. Z.div_mod_to_equations; lia. } }
    assert (ACLF : forall x : Z, f + 32 <= x < f + 32 + 8 \/ x = (f + 32) / 8 + 2147450880 ->
                     aclient (rt_live RT Σ1) (rt_frames RT Σ1) (bv_unsigned sp + -96 - bv_unsigned sp mod 32) x /\
                     outside [(BI + 40, BI + 72); (R, R + 32); (OUT, OUT + n)] x).
    { intros x HX. destruct HX as [HX | HX].
      - split.
        + right; right; right; left. exists f, 0%nat. split; [exact INF|]. rewrite FS0. lia.
        + cbn [outside]. pose proof (FLIVE BI 128 ltac:(rewrite LV1; exact INBI)).
          pose proof (FLIVE R 32 ltac:(rewrite LV1; exact INR)).
          pose proof (FLIVE pO kO ltac:(rewrite LV1; exact INO)).
          repeat split; lia.
      - split.
        + right; right; right; right. exists f, 0%nat. split; [exact INF|].
          unfold shad, SHB. rewrite FS0. subst x. clear - FAL FS8 FPOS. Z.div_mod_to_equations; lia.
        + destruct (af_fshadow_apart RT AF Σ1 m3 f 0%nat ART3 INF) as (SHL & _).
          cbn [outside]. rewrite FS0 in SHL.
          pose proof (SHL BI 128 ltac:(rewrite LV1; exact INBI)).
          pose proof (SHL R 32 ltac:(rewrite LV1; exact INR)).
          pose proof (SHL pO kO ltac:(rewrite LV1; exact INO)).
          unfold shad, SHB in *. subst x. repeat split; clear - H H0 H1 FAL FS8 FPOS OLO OHI; Z.div_mod_to_equations; lia. }
    assert (KEEP12 : forall (p k a : Z) (cs : list cell), rw_cells asegs m1 a cs -> In (p, k) (rt_live RT Σ) ->
              p <= a -> a + Z.of_nat (cells_size cs) <= p + k -> rw_cells asegs m2 a cs).
    { intros p k a cs HC INp LO1 HI1. apply (rw_cells_agree asegs m1 m2 _ _ HC); [| exact WM2].
      intros x HX. apply PRES2. right; right; left. exists p, k. split; [exact INp| lia]. }
    destruct (af_fshadow_apart RT AF Σ1 m3 f 0%nat ART3 INF) as (SHL & _). rewrite FS0 in SHL.
    assert (KEEP23 : forall (p k a : Z) (cs : list cell), rw_cells asegs m2 a cs -> In (p, k) (rt_live RT Σ) ->
              p <= a -> a + Z.of_nat (cells_size cs) <= p + k -> rw_cells asegs m3 a cs).
    { intros p k a cs HC INp LO1 HI1. apply (rw_cells_agree asegs m2 m3 _ _ HC); [| exact WM3].
      intros x HX. apply MU3. cbn [outside].
      pose proof (FLIVE p k ltac:(rewrite LV1; exact INp)) as FL1.
      pose proof (SHL p k ltac:(rewrite LV1; exact INp)) as FL2.
      pose proof (af_live_range RT AF Σ m p k ART0 INp) as (_ & PBELOW & _).
      unfold shad, SHB in FL2.
      pose proof (Z.mod_pos_bound (bv_unsigned sp) 32 ltac:(lia)).
      repeat split; try unfold STACK_WIN in *; lia. }
    assert (KEEP13 : forall (p k a : Z) (cs : list cell), rw_cells asegs m1 a cs -> In (p, k) (rt_live RT Σ) ->
              p <= a -> a + Z.of_nat (cells_size cs) <= p + k -> rw_cells asegs m3 a cs)
      by (intros p k a cs HC INp LO1 HI1; exact (KEEP23 p k a cs (KEEP12 p k a cs HC INp LO1 HI1) INp LO1 HI1)).
    assert (BIOHD3 := KEEP13 BI 128 BI _ BIOHD INBI ltac:(lia) ltac:(cbn [cells_size csize bio_head Nat.add]; lia)).
    assert (BIOW13 := KEEP13 BI 128 (BI + 40) _ BIOW1 INBI ltac:(lia) ltac:(cbn [cells_size csize bio_w1_cells Nat.add]; lia)).
    assert (BIOTL3 := KEEP13 BI 128 (BI + 72) _ BIOTL INBI ltac:(lia) ltac:(cbn [cells_size csize bio_tail Nat.add]; lia)).
    assert (BBC3 := KEEP13 BB 16 BB _ BBC INBB ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)).
    assert (RC3 := KEEP13 R 32 R _ RC INR ltac:(lia) ltac:(cbn [cells_size csize readp_cells Nat.add]; lia)).
    unfold bp_shadow in FSH3.
    apply (proj1 (rw_cells_app m3 f [C8 (Z_to_bv 64 BP_MAGIC); C8 (Z_to_bv 64 BR_DESCR); C8 (Z_to_bv 64 e_BIO_read); CB 8 hj]
                    [CB 8 pj; CB 16 qj])) in FC3.
    destruct FC3 as [FCHEAD FCREST]. cbn [cells_size csize Nat.add] in FCREST.
    apply (proj1 (rw_cells_app m3 (f + 32) [CB 8 pj] [CB 16 qj])) in FCREST.
    destruct FCREST as [FPR FCTOP].
    pose proof FSH3 as FSHFULL.
    apply (proj1 (rw_cells_app m3 (f / 8 + 2147450880)
                    [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15))]
                    [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))])) in FSH3.
    destruct FSH3 as [_ FSHR]. cbn [cells_size csize Nat.add] in FSHR.
    apply (proj1 (rw_cells_app m3 (f / 8 + 2147450880 + 4) [C1 (Z_to_bv 8 0)]
                    [C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))])) in FSHR.
    destruct FSHR as [FPRSH FSHTOP].
    replace (f / 8 + 2147450880 + 4) with ((f + 32) / 8 + 2147450880) in FPRSH
      by (clear - FAL FS8 FPOS; Z.div_mod_to_equations; lia).
    assert (EUF : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96 - bv_unsigned sp mod 32))
                  = bv_unsigned sp + -96 - bv_unsigned sp mod 32) by exact EUP.
    eapply (cps_realizes asegs _ _ T c3); [ | exact HA6 | ].
    + eapply C_BRI with (lo := lo).
      * exact FDO.
      * exact MST.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * exact METH.
      * exact BIOHD3.
      * rewrite LV1; exact INBI.
      * exact BIAL.
      * exact BIOW13.
      * exact FLOK.
      * exact BIOTL3.
      * rewrite LV1; exact INBB.
      * exact BBAL.
      * exact BBC3.
      * rewrite LV1; exact INR.
      * exact RAL.
      * exact RC3.
      * rewrite LV1; exact IND.
      * exact NDBI.
      * exact NDR.
      * exact (proj1 OFFLEN).
      * exact (proj2 OFFLEN).
      * exact HN.
      * exact LENMAX.
      * exact MAXB.
      * exists pO, kO. split; [rewrite LV1; exact INO|]. split; [lia|]. split; [lia| exact ONE].
      * exact FPR.
      * exact FPRSH.
      * lia.
      * clear - FAL FS8 FPOS; Z.div_mod_to_equations; lia.
      * try unfold STACK_WIN in *; lia.
      * destruct FHI as [HH|HH]; [left; lia | right; lia].
      * pose proof (FLIVE BI 128 ltac:(rewrite LV1; exact INBI)). rewrite FS0 in *. lia.
      * pose proof (FLIVE R 32 ltac:(rewrite LV1; exact INR)). rewrite FS0 in *. lia.
      * rewrite EUF. exact ACLF.
      * exact ART3.
      * exact MI3.
      * unfold call_ok. rewrite EUF. split; [exact STKLO3|].
        split; [rewrite SP1; exact LOWIN|].
        split; [try unfold RT_STACK in *; pose proof (Z.mod_pos_bound (bv_unsigned sp) 32 ltac:(lia)); lia|].
        split; [try unfold USTACK_TOP in *; pose proof (Z.mod_pos_bound (bv_unsigned sp) 32 ltac:(lia)); lia|].
        apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPAL; [| lia]. destruct SPAL as (qq & QQ).
        destruct PDC as [PZ|PZ]; rewrite PZ; [exists (qq - 6); lia | exists (qq - 7); lia].
      * rewrite EUF. unfold RT_STACK in *.
        pose proof (Z.mod_pos_bound (bv_unsigned sp) 32 ltac:(lia)). lia.
    + intros c4 HA7.
      destruct (ASTA_unpack RT Σ1 PMc _ c4 HA7)
        as (ms4 & (rmx & m4 & RS4 & AFT4 & PRES4 & BIH4 & BIOW4 & BTL4 & RC4 & PRC4 & BSR) & HA8).
      destruct RS4 as (r0 & r1 & r2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & r3 & r4 & r5 & r6 & F4 & fc4 & ->).
      destruct AFT4 as (ART4 & MI4 & WM4 & STK4).
      rewrite EUF in STK4, PRES4.
      rewrite (ret_pc_even SITE_br_intern ltac:(unfold SITE_br_intern; lia) ltac:(reflexivity)) in HA8.
      assert (FKEEP : forall (a : Z) (cs : list cell), rw_cells asegs m3 a cs ->
                        f <= a -> a + Z.of_nat (cells_size cs) <= f + 32 -> rw_cells asegs m4 a cs).
      { intros a cs HC LO1 HI1. apply (rw_cells_agree asegs m3 m4 _ _ HC); [| exact WM4].
        intros x HX. apply PRES4.
        - right; right; right; left. exists f, 0%nat. split; [rewrite FRS1; left; reflexivity|].
          rewrite FS0. lia.
        - cbn [outside]. unfold RD_W. cbn [outside].
          pose proof (FLIVE BI 128 ltac:(rewrite LV1; exact INBI)) as L1.
          pose proof (FLIVE R 32 ltac:(rewrite LV1; exact INR)) as L2.
          pose proof (FLIVE pO kO ltac:(rewrite LV1; exact INO)) as L3.
          repeat split; lia. }
      assert (FCHEAD4 := FKEEP f _ FCHEAD ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)).
      assert (SKEEP : forall (a : Z) (cs : list cell), rw_cells asegs m3 a cs ->
                        f / 8 + 2147450880 <= a -> a + Z.of_nat (cells_size cs) <= f / 8 + 2147450888 ->
                        rw_cells asegs m4 a cs).
      { intros a cs HC LO1 HI1. apply (rw_cells_agree asegs m3 m4 _ _ HC); [| exact WM4].
        intros x HX. apply PRES4.
        - right; right; right; right. exists f, 0%nat. split; [rewrite FRS1; left; reflexivity|].
          unfold shad, SHB. rewrite FS0. clear - HX LO1 HI1 FAL FS8 FPOS. Z.div_mod_to_equations; lia.
        - cbn [outside]. unfold RD_W. cbn [outside].
          pose proof (SHL BI 128 ltac:(rewrite LV1; exact INBI)) as S1.
          pose proof (SHL R 32 ltac:(rewrite LV1; exact INR)) as S2.
          pose proof (SHL pO kO ltac:(rewrite LV1; exact INO)) as S3.
          unfold shad, SHB in S1, S2, S3.
          repeat split; clear - HX LO1 HI1 S1 S2 S3 FAL FS8 FPOS OLO OHI; Z.div_mod_to_equations; lia. }
      assert (FSH4 := SKEEP _ _ FSHFULL ltac:(lia) ltac:(cbn [cells_size csize Nat.add]; lia)).
      assert (STKEEP : forall (a : Z) (cs : list cell), rw_cells asegs m3 a cs ->
                         bv_unsigned sp + -96 <= a -> a + Z.of_nat (cells_size cs) <= bv_unsigned sp ->
                         rw_cells asegs m4 a cs).
      { intros a cs HC LO1 HI1. apply (rw_cells_agree asegs m3 m4 _ _ HC); [| exact WM4].
        intros x HX. apply PRES4.
        - left. pose proof (Z.mod_pos_bound (bv_unsigned sp) 32 ltac:(lia)). try unfold USTACK_TOP in *. lia.
        - cbn [outside]. unfold RD_W. cbn [outside].
          pose proof (Z.mod_pos_bound (bv_unsigned sp) 32 ltac:(lia)).
          repeat split; try unfold STACK_WIN in *; lia. }
      assert (FRK4 := STKEEP _ _ FRK3 ltac:(lia) ltac:(cbn [cells_size csize br_ftail Nat.add]; lia)).
      assert (STKPD4 : stk asegs m4 (bv_unsigned sp + -96 - bv_unsigned sp mod 32) (bv_unsigned sp + -96)).
      { apply (stk_agree_nw asegs m3 m4 _ _ STKPD3). intros x HX. apply PRES4.
        - left. pose proof (Z.mod_pos_bound (bv_unsigned sp) 32 ltac:(lia)). try unfold USTACK_TOP in *. lia.
        - cbn [outside]. unfold RD_W. cbn [outside].
          pose proof (Z.mod_pos_bound (bv_unsigned sp) 32 ltac:(lia)).
          repeat split; try unfold STACK_WIN in *; lia. }
      assert (PRC44 : rw_cells asegs m4 (f + 32) [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 0)]).
      { apply (proj2 (Fz_T_ekit.t_cells_halves asegs m4 (f + 32) n 0 ltac:(lia) ltac:(lia))).
        replace (n + 2 ^ 32 * 0) with n by lia. exact PRC4. }
      pose proof (br_s2_walk sp gp (Z_to_bv 64 12205808) r0 r1 r2 d1 d2 d3 d4 d5 d6 d7 s9 s10 s11 r3 r4 r5 r6
                    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 F4 fc4 m4 f lo (bv_unsigned sp mod 32) BI OUT n hj jj
                    PDC FPOS FAL FSEG FROOM FVALID SPROOM LOHI SPHI
                    FRK4 STKPD4 STK4 FCHEAD4 PRC44 FSH4 ltac:(lia) MI4) as W2.
      cl_lift W2 HA8 c5 HA9.
      destruct (ASTA_unpack RT Σ1 PMc _ c5 HA9)
        as (ms5 & (ra5 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & hj5 & m5 &
                   MU5 & WM5 & MI5 & STKLO5 & STKPD5 & FRK5 & FC5 & ->) & HA10).
      assert (FRAMES2 : rt_frames RT Σ1 = (f, 0%nat) :: rt_frames RT Σ) by exact FRS1.
      assert (INF2 : In (f, 0%nat) (rt_frames RT Σ1)) by (rewrite FRAMES2; left; reflexivity).
      assert (ART5 : ART RT Σ1 m5).
      { apply (af_frame RT AF Σ1 m4 m5 (bv_unsigned sp + -96 - bv_unsigned sp mod 32) ART4
                 ltac:(rewrite SP1; try unfold STACK_WIN in *; lia)); [| exact WM5].
        intros a NAC. apply MU5. cbn [outside]. split; [| split; [| exact I]].
        { intros HIN. apply NAC. right; right; right; left. exists f, 0%nat.
          split; [exact INF2| rewrite FS0; lia]. }
        { intros HIN. apply NAC. right; right; right; right. exists f, 0%nat.
          split; [exact INF2|]. unfold shad, SHB. rewrite FS0.
          clear - HIN FAL FS8 FPOS. Z.div_mod_to_equations; lia. } }
      destruct (af_frame_release RT AF Σ1 m5 f 0%nat (rt_frames RT Σ) ART5 FRAMES2)
        as (Σ3 & fl' & FLAG1 & FLNA & FLPOS & FLROOM & FPTR & FREL).
      rewrite FS0 in FPTR. replace (f + 64 - 8) with (f + 56) in FPTR by lia.
      pose proof (br_s3_walk ra5 ra sp gp (Z_to_bv 64 12205808) u0 u1 u2 v1 v2 v3 v4 v5 v6 v7
                    (Z_to_bv 64 n) (Z_to_bv 64 OUT) (Z_to_bv 64 BI) (Z_to_bv 64 (f + 32))
                    (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) s9 s10 s11 u3 u4 u5 u6
                    s0 s1 s2 s3 s4 s5 s6 s7 s8 F4 fc4 m5 f fl' lo (bv_unsigned sp mod 32) n jj
                    PDC SPROOM LOHI SPHI FPOS FROOM FLPOS
                    ltac:(rewrite SP1 in FLROOM; try unfold STACK_WIN in *; lia)
                    ltac:(lia) STKLO5 STKPD5 FRK5 FPTR FLAG1 MI5) as W3.
      cl_lift W3 HA10 c6 HA11.
      destruct (ASTA_unpack RT Σ1 PMc _ c6 HA11)
        as (ms6 & (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m6 &
                   MU6 & WM6 & MI6 & STK6 & FLAG0 & ->) & HA12).
      destruct (FREL m6 MU6 WM6 FLAG0) as (ART6 & FRS3 & LV3 & SP3 & CR3 & ALLOW3 & ARTM3 & CG3).
      assert (XFER : forall (Pm : machine_state -> Prop) (cc : config), ASTA RT Σ1 PMc Pm cc -> ASTA RT Σ3 PMc Pm cc).
      { intros Pm cc HH. unfold ASTA, AST in HH |- *. rewrite ALLOW3.
        destruct HH as (MA & PMm & (ARTMo & PMco) & HZc).
        split; [exact MA|]. split; [exact PMm|]. split; [split; [apply ARTM3; exact ARTMo| exact PMco]| exact HZc]. }
      apply Hk. exists Σ3.
      split.
      2:{ split; [rewrite LV3, LV1; reflexivity|].
          split; [rewrite FRS3; reflexivity|].
          split; [rewrite SP3, SP1; reflexivity|].
          split; [rewrite CR3, CR1; lia|].
          rewrite CG3, CG1; reflexivity. }
      eapply (ASTA_conseq RT Σ3 PMc _ _ c6 (XFER _ _ HA12)). cbv beta.
      intros ms <-.
      assert (ACLM2 : forall x : Z, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x ->
                        aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp + -96 - bv_unsigned sp mod 32) x)
        by (intros x [HI|HI];
            [left; pose proof (Z.mod_pos_bound (bv_unsigned sp) 32 ltac:(lia)); lia | right; exact HI]).
      assert (ACL1 : forall x : Z,
                 aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp + -96 - bv_unsigned sp mod 32) x ->
                 aclient (rt_live RT Σ1) (rt_frames RT Σ1) (bv_unsigned sp + -96 - bv_unsigned sp mod 32) x).
      { intros x HI. rewrite LV1, FRS1.
        destruct HI as [HI | [HI | [HI | [HI | HI]]]].
        - left; exact HI.
        - right; left; exact HI.
        - right; right; left; exact HI.
        - right; right; right; left.
          destruct HI as (ff & kk & INff & RG). exists ff, kk. split; [right; exact INff| exact RG].
        - right; right; right; right.
          destruct HI as (ff & kk & INff & RG). exists ff, kk. split; [right; exact INff| exact RG]. }
      assert (WMALL : wmono asegs m m6).
      { exact (wmono_trans asegs m m5 m6
                 (wmono_trans asegs m m4 m5
                    (wmono_trans asegs m m3 m4
                       (wmono_trans asegs m m2 m3
                          (wmono_trans asegs m m1 m2 WM1 WM2) WM3) WM4) WM5) WM6). }
      assert (FAPART : forall a : Z, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) a ->
                         ~ (f <= a < f + 64) /\ ~ (f / 8 + 2147450880 <= a < f / 8 + 2147450888)).
      { intros a ACa.
        destruct (Fz_W2_puts.frame_apart RT AF Σ1 m2 f 0%nat (rt_frames RT Σ) (bv_unsigned sp) a ART2
                    FRS1 ltac:(rewrite SP1; try unfold STACK_WIN in *; lia)
                    ltac:(rewrite LV1; exact ACa)) as (NA1 & NA2).
        rewrite FS0 in NA1, NA2. unfold shad, SHB in NA2.
        split; [exact NA1|]. clear - NA2 FAL FS8 FPOS. Z.div_mod_to_equations; lia. }
      assert (KEEPALL : forall a : word,
                 aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned a) ->
                 outside ((BI + 96, BI + 104) :: RD_W BI R OUT n) (bv_unsigned a) -> m6 a = m a).
      { intros a ACa OUTa. cbn [outside] in OUTa. unfold RD_W in OUTa. cbn [outside] in OUTa.
        destruct OUTa as (OA & OB & OC & OD & _).
        destruct (FAPART (bv_unsigned a) ACa) as (NF & NS).
        pose proof (Z.mod_pos_bound (bv_unsigned sp) 32 ltac:(lia)) as PDB.
        assert (NSTK : ~ (bv_unsigned sp + -96 - bv_unsigned sp mod 32 <= bv_unsigned a < bv_unsigned sp)).
        { destruct (cl_split RT AF Σ m (bv_unsigned sp) (96 + bv_unsigned sp mod 32) (bv_unsigned a) ART0
                      ltac:(try unfold STACK_WIN in *; lia) ltac:(lia) ACa); lia. }
        transitivity (m5 a).
        1:{ apply MU6. cbn [outside]. split; [| exact I].
            intros HIN. assert (AEQ : bv_unsigned a = fl') by lia.
            apply FLNA. rewrite <- AEQ, LV1, FRAMES2.
            destruct ACa as [HI | [HI | [HI | [HI | HI]]]].
            - exfalso. rewrite SP1 in FLROOM. try unfold STACK_WIN in *. lia.
            - right; left; exact HI.
            - right; right; left; exact HI.
            - right; right; right; left.
              destruct HI as (ff & kk & INff & RG). exists ff, kk. split; [right; exact INff| exact RG].
            - right; right; right; right.
              destruct HI as (ff & kk & INff & RG). exists ff, kk. split; [right; exact INff| exact RG]. }
        transitivity (m4 a).
        1:{ apply MU5. cbn [outside]. split; [lia|]. split; [lia| exact I]. }
        transitivity (m3 a).
        1:{ apply PRES4; [exact (ACL1 _ (ACLM2 _ ACa))|].
            cbn [outside]. unfold RD_W. cbn [outside]. repeat split; try lia. }
        transitivity (m2 a).
        1:{ apply MU3. cbn [outside]. repeat split; try lia. }
        transitivity (m1 a).
        1:{ apply PRES2. exact (ACLM2 _ ACa). }
        apply MU1. cbn [outside]. split; [| exact I].
        destruct (cl_split RT AF Σ m (bv_unsigned sp) 96 (bv_unsigned a) ART0
                    ltac:(try unfold STACK_WIN in *; lia) ltac:(lia) ACa); lia. }
      exists rmx, m6.
      split. { do 16 eexists. reflexivity. }
      split. { split; [exact ART6|]. split; [exact MI6|]. split; [exact WMALL| exact STK6]. }
      split. { intros a ACa OUTa. exact (KEEPALL a ACa OUTa). }
      assert (KEEP46 : forall (p k a : Z) (cs : list cell), rw_cells asegs m4 a cs -> In (p, k) (rt_live RT Σ) ->
                p <= a -> a + Z.of_nat (cells_size cs) <= p + k -> rw_cells asegs m6 a cs).
      { intros p k a cs HC INp LO1 HI1.
        assert (STEP5 : rw_cells asegs m5 a cs).
        { apply (rw_cells_agree asegs m4 m5 _ _ HC); [| exact WM5].
          intros x HX. apply MU5. cbn [outside].
          pose proof (FLIVE p k ltac:(rewrite LV1; exact INp)) as L1.
          pose proof (SHL p k ltac:(rewrite LV1; exact INp)) as L2. unfold shad, SHB in L2.
          repeat split; clear - HX LO1 HI1 L1 L2 FAL FS8 FPOS; Z.div_mod_to_equations; lia. }
        apply (rw_cells_agree asegs m5 m6 _ _ STEP5); [| exact WM6].
        intros x HX. apply MU6. cbn [outside]. split; [| exact I].
        intros HIN. apply FLNA. rewrite LV1, FRAMES2.
        right; right; left. exists p, k. split; [exact INp| lia]. }
      assert (BIH6 := KEEP46 BI 128 BI _ BIH4 INBI ltac:(lia) ltac:(cbn [cells_size csize bio_head Nat.add]; lia)).
      assert (BIOW6 := KEEP46 BI 128 (BI + 40) _ BIOW4 INBI ltac:(lia)
                         ltac:(cbn [cells_size csize bio_w1_cells Nat.add]; lia)).
      assert (BTL6 := KEEP46 BI 128 (BI + 72) _ BTL4 INBI ltac:(lia)
                         ltac:(cbn [cells_size csize bio_tail Nat.add]; lia)).
      assert (RC6 := KEEP46 R 32 R _ RC4 INR ltac:(lia)
                         ltac:(cbn [cells_size csize readp_cells Nat.add]; lia)).
      split; [exact BIH6|]. split; [exact BIOW6|]. split; [exact BTL6| exact RC6].
Qed.
End CBread.
