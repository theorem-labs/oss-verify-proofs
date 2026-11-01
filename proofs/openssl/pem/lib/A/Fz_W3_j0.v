(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall Bytes Frame.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit Fz_G_pkit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_misc Fz_W1_pploc Fz_W1_grow Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_aux3 Fz_W3_lits Fz_W3_inik Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tslia ::= wp_tslia.
Notation wz := (Z_to_bv 64) (only parsing).
Local Ltac zgo p := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; lfix end).
Definition SITE_j0_sm : Z := 0x30c118.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition j0_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition j0_w0_post (SP : Z) (gp t0 t1 t2 sp a6 a7 s2 s6 s7 s8 t3 t4 t5 t6 : word) (saved : list cell) (F : bvmap 5 word) (fc : bv 32)
    (BI PN PH PD PLN fl lo pd : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem) (v1 v2 : word) (j1 j2 g : list byte),
    ms = MS (mkR (wz SITE_j0_sm) (wz (SP - 352 - pd)) gp (wz TP_A) t0 t1 t2 sp (wz (SP - 352 - pd)) (wz 96) v1 v2 (wz PD) (wz PLN) (wz fl) a6 a7
                 s2 (wz PLN) (wz fl) (wz PN) s6 s7 s8 (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
            F (wz (e_stack_malloc 1)) fc None m' (seg_rom asegs)
    /\ munch [(SP - 352 - pd, SP)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (SP - 352 - pd)
    /\ rw_cells asegs m' (SP - 352 - pd) [CB 216 j1; C8 (wz BI); CB 24 j2; CB (Z.to_nat pd) g]
    /\ rw_cells asegs m' (SP - 104) saved.

Lemma j0_w0 : forall ra sp gp t0 t1 t2 s0 s1 BI PN PH PD PLN fl a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo pd : Z),
  (pd = 0 \/ pd = 16) -> bv_unsigned sp mod 32 = pd ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 1136 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)] -> mem_inv asegs m ->
  evt asegs (j0_w0_post (bv_unsigned sp) gp t0 t1 t2 sp a6 a7 s2 s6 s7 s8 t3 t4 t5 t6 (j0_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) F fc BI PN PH PD PLN fl lo pd m)
    (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz BI) (wz PN) (wz PH) (wz PD) (wz PLN) (wz fl) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz FZ_PEM_READ_BIO) fc None m (seg_rom asegs)).
Proof.
  intros until pd. intros PDcase PDmod ST LOsp LOasan SPtop UT GSH GUAR MI.
  unfold j0_w0_post, j0_saved, SITE_j0_sm, TP_A, FZ_PEM_READ_BIO, SHB, e_stack_malloc, g_shadow_memory_dynamic_address, g_detect_stack_use_after_return in *.
  pose proof (munch_refl [(bv_unsigned sp - 352 - pd, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(bv_unsigned sp - 352 - pd, bv_unsigned sp)]) by (destruct PDcase; subst; ut_fp_lia).
  pose proof (bv_unsigned_in_range 64 sp) as SPrng. unfold bv_modulus in SPrng. change (2 ^ Z.of_N 64) with (2 ^ 64) in SPrng.
  destruct PDcase as [-> | ->].
  - carve_frame 352%nat ST.
    zgo 3195092.
    assert (ALIGN : Z.land (bv_unsigned sp + -352) 18446744073709551584 = bv_unsigned sp + -352).
    { rewrite (land_m32_pad (bv_unsigned sp + -352) 0) by (Z.div_mod_to_equations; lia). lia. }
    rewrite ALIGN.
    zgo 1729840.
    if_false.
    zgo 1729840.
    replace (bv_unsigned sp - 352 - 0) with (bv_unsigned sp + -352) in * by lia.
    apply (proj1 (rw_cells_app m0 _ [C8 _; CB 208 _; C8 _; CB 24 _] _)) in FR as [Frame Saved].
    cbn [cells_size csize Nat.add] in Saved. change (Z.of_nat 248) with 248 in Saved.
    replace (bv_unsigned sp + -352 + 248) with (bv_unsigned sp - 104) in Saved by lia.
    apply (rw_cells_blur m0 _ [C8 _; CB 208 _] [C8 _; CB 24 _]) in Frame.
    apply (rw_cells_split_CB asegs m0 _ [CB 216 _; C8 _] 24 _ [] [24; 0]%nat) in Frame; [|reflexivity].
    cbn [mk_CB_cells app] in Frame.
    apply evt_done. do 6 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact Frame| exact Saved].
  - carve_frame 368%nat ST.
    zgo 3195092.
    assert (ALIGN : Z.land (bv_unsigned sp + -352) 18446744073709551584 = bv_unsigned sp + -368).
    { rewrite (land_m32_pad (bv_unsigned sp + -352) 16) by (Z.div_mod_to_equations; lia). lia. }
    rewrite ALIGN.
    zgo 1729840.
    if_false.
    zgo 1729840.
    replace (bv_unsigned sp - 352 - 16) with (bv_unsigned sp + -368) in * by lia.
    apply (proj1 (rw_cells_app m0 _ [CB 16 _; C8 _; CB 192 _; C8 _; CB 40 _] _)) in FR as [Frame Saved].
    apply (rw_cells_blur m0 _ [CB 16 _; C8 _; CB 192 _] [C8 _; CB 40 _]) in Frame.
    apply (rw_cells_split_CB asegs m0 _ [CB 216 _; C8 _] 40 _ [] [24; 16]%nat) in Frame; [|reflexivity].
    cbn [mk_CB_cells app] in Frame.
    cbn [cells_size csize Nat.add] in Saved. change (Z.of_nat 264) with 264 in Saved.
    replace (bv_unsigned sp + -368 + 264) with (bv_unsigned sp - 104) in Saved by lia.
    apply evt_done. do 6 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact Frame| exact Saved].
Qed.
(* [comment removed for export] *)
Definition j0_hdr (pcw : word) : list cell := [C8 (wz FF_MAGIC); C8 (wz FF_DESCR); C8 pcw].
Definition j0_sh12 : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4);
   C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))].
Definition SITE_j0_c1 : Z := 0x30c1c4.   (* [comment removed for export] *)
Definition j0_w1a_post (sp1 : Z) (gp t0 t1 t2 sp a6 a7 s7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (f PN PH PD PLN fl : Z) (fj sj : list byte) (m : mem) : machine_state -> Prop :=
  fun ms => exists (m' : mem) (pcw : word),
    ms = MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz (PLN / 8)) (wz 4) pcw (wz (-8)) (wz (-14)) (wz (-15)) a6 a7
                 (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
            F (wz SITE_j0_c1) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 24); (shad f, shad f + 12)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' f (j0_hdr pcw ++ [CB 96 (skipn 24 fj)]) /\ rw_cells asegs m' (shad f) (j0_sh12 ++ [CB 4 (skipn 12 sj)]).

Lemma j0_w1a : forall sp1 gp t0 t1 t2 sp b1 b2 b3 b4 b5 b6 b7 s2 s6 s7 s8 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem)
    (f PN PH PD PLN fl : Z) (fj sj : list byte),
  0 < f -> f + 128 <= 2^47 -> (f + 120 <= 0x10000 \/ SEGTOP_A <= f) -> (f + 128 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0x10007fff8000 <= sp1 -> f + 128 <= sp1 -> 0 < PLN -> PLN + 8 <= 2 ^ 47 ->
  img_untouched m -> rw_cells asegs m f [CB 120 fj] -> rw_cells asegs m (shad f) [CB 16 sj] -> mem_inv asegs m ->
  evt asegs (j0_w1a_post sp1 gp t0 t1 t2 sp b6 b7 s7 t3 t4 t5 t6 F fc f PN PH PD PLN fl fj sj m)
    (MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz f) b1 b2 b3 b4 b5 b6 b7 s2 (wz PLN) (wz fl) (wz PN) s6 s7 s8 (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
        F (wz SITE_j0_sm) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros Fpos Ftop Fseg Fsh SPlo SPhi SPasan FbelowSP PLpos PLtop UT FR SHR MI.
  pose proof (munch_refl [(f, f + 24); (shad f, shad f + 12)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold j0_w1a_post, SITE_j0_sm, SITE_j0_c1, TP_A, shad, SHB in *.
  zstep. zstep. zstep. zstep.
  replace (negb (bv_eqb (Z_to_bv 64 f) (Z_to_bv 64 0))) with true.
  2: { unfold bv_eqb. rewrite (unsigned_lit f) by lia. rewrite (unsigned_lit 0) by lia.
       rewrite (proj2 (Z.eqb_neq f 0)) by lia. reflexivity. }
  cbv iota.
  zstep. zstep. zstep. zstep. rewrite (shr3_div f) by lia.
  zgo 3195332.
  rewrite (shr3_div PLN) by lia.
  repeat rewrite skipn_skipn in FR. repeat rewrite skipn_skipn in SHR. cbn [Nat.add] in FR, SHR.
  replace (f / 8 + 2147450880 + 12) with (f / 8 + 2147450892) in MU by lia.
  apply evt_done. exists m0, (Z_to_bv 64 3195024). split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FR| exact SHR].
Qed.
Local Ltac zsh := cbv beta; try change (bv_unsigned (Z_to_bv 8 0)) with 0; try change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0); try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
Definition SITE_j0_c1x : Z := 0x30c1d4.  (* [comment removed for export] *)
Definition SITE_j0_c2x : Z := 0x30c1e8.  (* [comment removed for export] *)
Definition SITE_j0_c3x : Z := 0x30c1fc.  (* [comment removed for export] *)
Definition SITE_j0_c4 : Z := 0x30c210.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma j0_w1b : forall sp1 gp t0 t1 t2 sp pcw a6 a7 s7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f PN PH PD PLN fl : Z) (x1 x2 x3 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0x10007fff8000 <= sp1 -> 0 < PLN -> PLN + 8 <= 2 ^ 47 -> PLN mod 8 = 0 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 224) [C8 x1; C8 x2; C8 x3] -> ro_cells asegs m (PLN / 8 + SHB) [C1 z8] ->
  evt asegs (fun ms => exists m',
      ms = MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz 0) (wz 4) pcw (wz (-8)) (wz (PLN / 8 + SHB)) (wz (-15)) a6 a7
                   (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
              F (wz SITE_j0_c1x) fc None m' (seg_rom asegs)
      /\ munch [(sp1 + 240, sp1 + 248)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' (sp1 + 224) [C8 x1; C8 x2; C8 (wz f)])
    (MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz (PLN / 8)) (wz 4) pcw (wz (-8)) (wz (-14)) (wz (-15)) a6 a7
             (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
        F (wz SITE_j0_c1) fc None m (seg_rom asegs)).
Proof.
  intros until x3. intros SPlo SPhi SPasan PLpos PLtop PL8 MI Slots SHPL.
  pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(sp1 + 240, sp1 + 248)] m) as MU.
  unfold SITE_j0_c1, SITE_j0_c1x, SITE_j0_sm, TP_A, SHB, z8 in *.
  zstep. zstep. zsh. zstep. zstep. if_false.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact Slots].
Qed.
(* [comment removed for export] *)
Lemma j0_w1c : forall sp1 gp t0 t1 t2 sp pcw a6 a7 s7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f PN PH PD PLN fl : Z) (ol : word),
  0 < PLN -> PLN + 8 <= 2 ^ 47 -> (PLN + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= PLN) -> 0 < PH -> PH + 8 <= 2 ^ 47 -> PH mod 8 = 0 -> mem_inv asegs m ->
  rw_cells asegs m PLN [C8 ol] -> ro_cells asegs m (PH / 8 + SHB) [C1 z8] ->
  evt asegs (fun ms => exists m',
      ms = MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz 0) (wz 4) pcw (wz (PH / 8 + SHB)) (wz (PLN / 8 + SHB)) (wz (-15)) a6 a7
                   (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
              F (wz SITE_j0_c2x) fc None m' (seg_rom asegs)
      /\ munch [(PLN, PLN + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' PLN [C8 (wz 0)])
    (MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz 0) (wz 4) pcw (wz (-8)) (wz (PLN / 8 + SHB)) (wz (-15)) a6 a7
             (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
        F (wz SITE_j0_c1x) fc None m (seg_rom asegs)).
Proof.
  intros until ol. intros PLpos PLtop PLout PHpos PHtop PH8 MI CPL SHPH.
  pose proof (munch_refl [(PLN, PLN + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold SITE_j0_c1x, SITE_j0_c2x, SITE_j0_sm, TP_A, SHB, z8 in *.
  zstep. lfix.
  zstep. rewrite (shr3_div PH) by lia.
  zstep. zstep. zsh.
  zstep. if_false.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact CPL].
Qed.

(* [comment removed for export] *)
Lemma j0_w1d : forall sp1 gp t0 t1 t2 sp pcw a6 a7 s7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f PN PH PD PLN fl : Z) (oh : word),
  0 < PH -> PH + 8 <= 2 ^ 47 -> (PH + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= PH) -> 0 < PN -> PN + 8 <= 2 ^ 47 -> PN mod 8 = 0 -> mem_inv asegs m ->
  rw_cells asegs m PH [C8 oh] -> ro_cells asegs m (PN / 8 + SHB) [C1 z8] ->
  evt asegs (fun ms => exists m',
      ms = MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz 0) (wz 4) pcw (wz (PH / 8 + SHB)) (wz (PLN / 8 + SHB)) (wz (PN / 8 + SHB)) a6 a7
                   (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
              F (wz SITE_j0_c3x) fc None m' (seg_rom asegs)
      /\ munch [(PH, PH + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' PH [C8 (wz 0)])
    (MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz 0) (wz 4) pcw (wz (PH / 8 + SHB)) (wz (PLN / 8 + SHB)) (wz (-15)) a6 a7
             (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
        F (wz SITE_j0_c2x) fc None m (seg_rom asegs)).
Proof.
  intros until oh. intros PHpos PHtop PHout PNpos PNtop PN8 MI CPH SHPN.
  pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(PH, PH + 8)] m) as MU.
  unfold SITE_j0_c2x, SITE_j0_c3x, SITE_j0_sm, TP_A, SHB, z8 in *.
  zstep. lfix.
  zstep. rewrite (shr3_div PN) by lia.
  zstep. zstep. zsh.
  zstep. if_false.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact CPH].
Qed.

(* [comment removed for export] *)
Lemma j0_w1e : forall sp1 gp t0 t1 t2 sp pcw a6 a7 s7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f PN PH PD PLN fl : Z) (on : word),
  0 < PN -> PN + 8 <= 2 ^ 47 -> (PN + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= PN) -> 0 < PD -> PD + 8 <= 2 ^ 47 -> PD mod 8 = 0 -> mem_inv asegs m ->
  rw_cells asegs m PN [C8 on] -> ro_cells asegs m (PD / 8 + SHB) [C1 z8] ->
  evt asegs (fun ms => exists m',
      ms = MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz 0) (wz 4) (wz (PD / 8 + SHB)) (wz (PH / 8 + SHB)) (wz (PLN / 8 + SHB)) (wz (PN / 8 + SHB)) a6 a7
                   (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
              F (wz SITE_j0_c4) fc None m' (seg_rom asegs)
      /\ munch [(PN, PN + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' PN [C8 (wz 0)])
    (MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz 0) (wz 4) pcw (wz (PH / 8 + SHB)) (wz (PLN / 8 + SHB)) (wz (PN / 8 + SHB)) a6 a7
             (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
        F (wz SITE_j0_c3x) fc None m (seg_rom asegs)).
Proof.
  intros until on. intros PNpos PNtop PNout PDpos PDtop PD8 MI CPN SHPD.
  pose proof (munch_refl [(PN, PN + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold SITE_j0_c3x, SITE_j0_c4, SITE_j0_sm, TP_A, SHB, z8 in *.
  zstep. lfix.
  zstep. rewrite (shr3_div PD) by lia.
  zstep. zstep. zsh.
  zstep. if_false.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact CPN].
Qed.

(* [comment removed for export] *)
Lemma j0_w1f : forall sp1 gp t0 t1 t2 sp a6 a7 s7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f PN PH PD PLN fl : Z) (od : word),
  0 < PD -> PD + 8 <= 2 ^ 47 -> 0 <= fl < 256 -> mem_inv asegs m -> rw_cells asegs m PD [C8 od] ->
  evt asegs (fun ms => exists m',
      ms = MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz (Z.land fl 6)) (wz 6) (wz (PD / 8 + SHB)) (wz (PH / 8 + SHB)) (wz (PLN / 8 + SHB)) (wz (PN / 8 + SHB)) a6 a7
                   (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
              F (wz (if Z.land fl 6 =? 6 then J_RAISE0 else J_J0N)) fc None m' (seg_rom asegs)
      /\ munch [(PD, PD + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' PD [C8 (wz 0)])
    (MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz 0) (wz 4) (wz (PD / 8 + SHB)) (wz (PH / 8 + SHB)) (wz (PLN / 8 + SHB)) (wz (PN / 8 + SHB)) a6 a7
             (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
        F (wz SITE_j0_c4) fc None m (seg_rom asegs)).
Proof.
  intros until od. intros PDpos PDtop FLrng MI CPD.
  pose proof (munch_refl [(PD, PD + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold SITE_j0_c4, SITE_j0_sm, TP_A, SHB, J_RAISE0, J_J0N in *.
  zstep. zstep. zstep. lfix.
  pose proof (Z_land_range fl 6 ltac:(lia) ltac:(lia)) as LandRng.
  zstep.
  destruct (Z.eqb_spec (Z.land fl 6) 6) as [Six|NotSix].
  - rewrite Six. if_false. cbv iota.
    apply evt_done. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact CPD].
  - replace (negb (bv_eqb (Z_to_bv 64 (Z.land fl 6)) (Z_to_bv 64 6))) with true.
    2: { unfold bv_eqb. rewrite (unsigned_lit (Z.land fl 6)) by lia. rewrite (unsigned_lit 6) by lia.
         rewrite (proj2 (Z.eqb_neq _ _) NotSix). reflexivity. }
    cbv iota.
    apply evt_done. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact CPD].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_le_to_Z_range' : forall bs : list byte, 0 <= bytes_le_to_Z bs < 256 ^ Z.of_nat (length bs).
Proof.
  intros bs. rewrite bytes_le_to_Z_le_val. pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as H. rewrite length_map in H. exact H.
Qed.
Lemma le_bytes_roundtrip' : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_range' bs) as [Hr _].
  rewrite lor_shiftl8_add by lia. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    rewrite Z.mul_comm, Z_div_plus_full by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. exact IH.
Qed.
Lemma le8_of_junk' : forall bs : list byte, length bs = 8%nat -> cbytes (C8 (le_bytes_to_word bs)) = bs.
Proof.
  intros bs L. cbn [cbytes]. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_range' bs) as Hr. rewrite L in Hr. change (256 ^ Z.of_nat 8) with (2 ^ 64) in Hr.
  rewrite bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia).
  rewrite <- L. apply le_bytes_roundtrip'.
Qed.
Lemma le4_of_junk' : forall bs : list byte, length bs = 4%nat -> cbytes (C4 (le_bytes_to_word bs)) = bs.
Proof.
  intros bs L. cbn [cbytes]. unfold le4, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_range' bs) as Hr. rewrite L in Hr. change (256 ^ Z.of_nat 4) with (2 ^ 32) in Hr.
  rewrite bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia).
  rewrite <- L. apply le_bytes_roundtrip'.
Qed.
(* [comment removed for export] *)
Lemma junk_C8 : forall (m : mem) A pre post bs, rw_cells asegs m A (pre ++ CB 8 bs :: post) -> rw_cells asegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
  intros m A pre post bs Src.
  pose proof Src as [[Wall _] _]. apply cells_wf_app in Wall as [Wpre [Blen Wpost]].
  apply (rw_cells_recast m A (pre ++ CB 8 bs :: post) _ Src).
  - apply cells_wf_app. split; [exact Wpre|]. split; [exact I| exact Wpost].
  - rewrite !cells_bytes_app. cbn [cells_bytes]. rewrite (le8_of_junk' bs Blen). reflexivity.
Qed.
Lemma junk_C4 : forall (m : mem) A pre post bs, rw_cells asegs m A (pre ++ CB 4 bs :: post) -> rw_cells asegs m A (pre ++ C4 (le_bytes_to_word bs) :: post).
Proof.
  intros m A pre post bs Src.
  pose proof Src as [[Wall _] _]. apply cells_wf_app in Wall as [Wpre [Blen Wpost]].
  apply (rw_cells_recast m A (pre ++ CB 4 bs :: post) _ Src).
  - apply cells_wf_app. split; [exact Wpre|]. split; [exact I| exact Wpost].
  - rewrite !cells_bytes_app. cbn [cells_bytes]. rewrite (le4_of_junk' bs Blen). reflexivity.
Qed.

(* [comment removed for export] *)
Ltac zofnat H := repeat match type of H with context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in H end.
Lemma j0_frame_split : forall (m : mem) sp1 j1 bi j2 gap,
  rw_cells asegs m sp1 (CB 216 j1 :: C8 bi :: CB 24 j2 :: gap) ->
  exists j0 jH jF endv jE x1 x2 x3,
       rw_cells asegs m sp1 [CB 24 j0] /\ rw_cells asegs m (sp1 + 24) [CB 56 jH] /\ rw_cells asegs m (sp1 + 80) [CB 24 jF]
    /\ rw_cells asegs m (sp1 + 104) [C8 endv] /\ rw_cells asegs m (sp1 + 112) [CB 104 jE] /\ rw_cells asegs m (sp1 + 216) [C8 bi]
    /\ rw_cells asegs m (sp1 + 224) [C8 x1; C8 x2; C8 x3] /\ rw_cells asegs m (sp1 + 248) gap.
Proof.
  intros m sp1 j1 bi j2 gap Whole.
  apply (rw_cells_split_CB asegs m sp1 [] 216 j1 (C8 bi :: CB 24 j2 :: gap) [24; 56; 24; 8; 104]%nat) in Whole; [|reflexivity].
  cbn [mk_CB_cells app] in Whole.
  apply (junk_C8 m sp1 [CB 24 _; CB 56 _; CB 24 _]) in Whole.
  apply (rw_cells_split_CB asegs m sp1 [CB 24 _; CB 56 _; CB 24 _; C8 _; CB 104 _; C8 bi] 24 j2 gap [8; 8; 8]%nat) in Whole; [|reflexivity].
  cbn [mk_CB_cells app] in Whole.
  apply (junk_C8 m sp1 [CB 24 _; CB 56 _; CB 24 _; C8 _; CB 104 _; C8 bi]) in Whole.
  apply (junk_C8 m sp1 [CB 24 _; CB 56 _; CB 24 _; C8 _; CB 104 _; C8 bi; C8 _]) in Whole.
  apply (junk_C8 m sp1 [CB 24 _; CB 56 _; CB 24 _; C8 _; CB 104 _; C8 bi; C8 _; C8 _]) in Whole.
  pose proof (rw_cells_skip m sp1 [CB 24 _; CB 56 _; CB 24 _; C8 _; CB 104 _; C8 bi] _ Whole) as Upper.
  apply (proj1 (rw_cells_app m _ [C8 _; C8 _; C8 _] gap)) in Upper as [Trio _].
  do 8 eexists.
  split; [exact (rw_cells_head m sp1 _ _ Whole)|].
  split; [exact (rw_cells_head m _ _ _ (rw_cells_skip m sp1 [CB 24 _] _ Whole))|].
  split; [exact (rw_cells_head m _ _ _ (rw_cells_skip m sp1 [CB 24 _; CB 56 _] _ Whole))|].
  split; [exact (rw_cells_head m _ _ _ (rw_cells_skip m sp1 [CB 24 _; CB 56 _; CB 24 _] _ Whole))|].
  split; [exact (rw_cells_head m _ _ _ (rw_cells_skip m sp1 [CB 24 _; CB 56 _; CB 24 _; C8 _] _ Whole))|].
  split; [exact (rw_cells_head m _ _ _ (rw_cells_skip m sp1 [CB 24 _; CB 56 _; CB 24 _; C8 _; CB 104 _] _ Whole))|].
  split; [exact Trio|].
  exact (rw_cells_skip m sp1 [CB 24 _; CB 56 _; CB 24 _; C8 _; CB 104 _; C8 bi; C8 _; C8 _; C8 _] gap Whole).
Qed.

(* [comment removed for export] *)
Lemma j0_ff_split : forall (m : mem) f pcw r,
  rw_cells asegs m f [C8 (wz FF_MAGIC); C8 (wz FF_DESCR); C8 pcw; CB 96 r] ->
  exists hj lenv j1 tav j2 bmv j3, rw_cells asegs m f (ff_cells hj lenv j1 tav j2 bmv j3).
Proof.
  intros m f pcw r Hdr.
  apply (rw_cells_split_CB asegs m f [C8 (wz FF_MAGIC); C8 (wz FF_DESCR); C8 pcw] 96 r [] [8; 4; 12; 4; 12; 8; 48]%nat) in Hdr; [|reflexivity].
  cbn [mk_CB_cells app] in Hdr.
  apply (junk_C8 m f [C8 _; C8 _; C8 _; CB 8 _; CB 4 _; CB 12 _; CB 4 _; CB 12 _]) in Hdr.
  apply (junk_C4 m f [C8 _; C8 _; C8 _; CB 8 _; CB 4 _; CB 12 _]) in Hdr.
  apply (junk_C4 m f [C8 _; C8 _; C8 _; CB 8 _]) in Hdr.
  apply (proj1 (rw_cells_app m f [C8 _; C8 _] _)) in Hdr as [Magic Tail].
  apply (rw_cells_blur m _ [C8 pcw; CB 8 _]) in Tail.
  do 7 eexists. unfold ff_cells.
  apply (proj2 (rw_cells_app m f [C8 (wz FF_MAGIC); C8 (wz FF_DESCR)] _)). split; [exact Magic| exact Tail].
Qed.

(* [comment removed for export] *)
Lemma mbio_rep_offnd : forall live (m : mem) K BI meth len max off,
  mbio_rep live m K BI meth len max off -> 0 <= off <= len /\ List.NoDup (mbio_blocks K).
Proof.
  intros live m K BI meth len max off (BM & fl & rrw & numw & padw & nr & nw & EBI & EBM & IBI & AL & ND & HM & HD & W1 & FL & TL & INR).
  destruct INR as (rmaxw & _ & _ & _ & _ & _ & _ & _ & OFF & _). split; [exact OFF| exact ND].
Qed.

Section CJ0.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
Variable libenv_fp : list (Z * Z) -> Z -> Prop.
Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
Variable errst_at_rest : Z -> list (Z * Z) -> mem -> Prop.
Variable errst_live : Z -> Z -> Z -> list (Z * Z) -> mem -> Prop.
Variable errst_fp : Z -> list (Z * Z) -> Z -> Prop.
Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ in_live strs a.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Hypothesis SM1 : stack_malloc_contract RT 1.
Hypothesis HCG : cg_sub PEM_SITES PEM_CALLS FZ_SITES FZ_CALLS.
Hypothesis H_R0 : RAISE0_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Hypothesis H_J0N : J0N_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_ms := (pem_ms RT).

(* [comment removed for export] *)
Lemma out_loc_facts : forall Σ (m : mem) lo (frames0 : list (Z * nat)) (mm : mem) P,
  ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= lo -> (forall fk, In fk frames0 -> In fk (rt_frames RT Σ)) ->
  P mod 8 = 0 /\ pp_loc frames0 mm USTACK_TOP P ->
  exists f' k', In (f', k') frames0 /\ f' <= P /\ P + 8 <= f' + fs_size k' - 8 /\ bytes_at asegs mm (shad P) [z8]
    /\ 0 < P /\ P + 8 <= lo /\ (P + 8 <= 0x7fff7000 \/ 0x10007fff8000 <= P) /\ P mod 8 = 0
    /\ (forall p n, In (p, n) (rt_live RT Σ) -> P + 8 <= p \/ p + n <= P).
Proof using AF.
  intros Σ m lo frames0 mm P ART0 LOW SUBF [P8 LOC].
  destruct LOC as [(TopLo & TopHi) | (fr & k & INF & FrLo & FrHi & ShZ)]; [unfold USTACK_TOP in *; lia|].
  pose proof (SUBF _ INF) as INF0.
  pose proof (af_frames_range RT AF Σ m fr k ART0 INF0) as (FrPos & FrTop & _ & FrApart).
  pose proof (af_frames_hi RT AF Σ m fr k ART0 INF0) as FrHigh.
  exists fr, k. split; [exact INF|]. split; [exact FrLo|]. split; [exact FrHi|]. split; [exact ShZ|].
  split; [lia|]. split; [lia|]. split; [destruct FrHigh as [Lw|Hg]; [left|right]; lia|]. split; [exact P8|].
  intros p n LIVE. destruct (FrApart p n LIVE) as [Abv|Blw]; [left|right]; lia.
Qed.

Theorem J0_proof : pem_read_bio_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof using All.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer canary LBL K
         E BI meth blen bmax boff PN PH PD PL flags on oh od ol.
  intros FDO MST TPeq A0 A1 A2 A3 A4 A5 FLG LIBE INCL INE NLE NTL REST MB BLT NDP LOCS CPN CPH CPD CPL ART0 MI0 CALL LOR CLE SEC CTX UWC CGH FRN LIVN
         CRD LPOS.
  subst tp a0 a1 a2 a3 a4 a5.
  unfold cps. intros T c HA Hk.
  (* Facts about the caller's stack, frame list and output slots. *)
  destruct CALL as (ST0 & WIN & LORT & SPTOP & SP16).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (_ & GSH & _ & GUAR & UT0).
  destruct (mbio_rep_offnd _ _ _ _ _ _ _ _ MB) as [OFFR NDK].
  pose proof (bv_unsigned_in_range 64 sp) as SPrng. unfold bv_modulus in SPrng. change (2 ^ Z.of_N 64) with (2 ^ 64) in SPrng.
  pose (pd := bv_unsigned sp mod 32). assert (PDM : bv_unsigned sp mod 32 = pd) by reflexivity. clearbody pd.
  assert (PD0 : pd = 0 \/ pd = 16) by (clear - SP16 PDM; Z.div_mod_to_equations; lia).
  assert (LOW : 0x10007fff8000 <= lo) by (clear - WIN SP0W; unfold STACK_WIN in *; lia).
  assert (LOsp : lo <= bv_unsigned sp - 1136) by (clear - LOR; unfold RT_STACK, PEMR_STACK, PEM_CALLEE_STACK in *; lia).
  assert (SPtop : bv_unsigned sp <= 2 ^ 47) by (clear - SPTOP; unfold USTACK_TOP in *; lia).
  rewrite Forall_forall in LOCS.
  destruct (out_loc_facts Σ m lo (rt_frames RT Σ) m PL ART0 WIN (fun fk Hfk => Hfk) (LOCS PL ltac:(cbn; tauto)))
    as (fL & kL & INL & FLlo & FLhi & SHL & PLpos & PLlo & PLsh & PL8 & PLlive).
  destruct (out_loc_facts Σ m lo (rt_frames RT Σ) m PH ART0 WIN (fun fk Hfk => Hfk) (LOCS PH ltac:(cbn; tauto)))
    as (fH & kH & INH & FHlo & FHhi & SHH & PHpos & PHlo & PHsh & PH8 & PHlive).
  destruct (out_loc_facts Σ m lo (rt_frames RT Σ) m PN ART0 WIN (fun fk Hfk => Hfk) (LOCS PN ltac:(cbn; tauto)))
    as (fN & kN & INN & FNlo & FNhi & SHN & PNpos & PNlo & PNsh & PN8 & PNlive).
  destruct (out_loc_facts Σ m lo (rt_frames RT Σ) m PD ART0 WIN (fun fk Hfk => Hfk) (LOCS PD ltac:(cbn; tauto)))
    as (fD & kD & IND & FDlo & FDhi & SHD & PDpos & PDlo & PDsh & PD8 & PDlive).
  (* Prologue: save registers, align the frame, call the fake-stack allocator. *)
  pose proof (j0_w0 ra sp gp t0 t1 t2 s0 s1 BI PN PH PD PL flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pd
                PD0 PDM ST0 LOsp LOW SPtop UT0 GSH GUAR MI0) as Walk0.
  cl_lift Walk0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & Post1 & Hc1A). clear Hc1.
  destruct Post1 as (m1 & v1 & v2 & j1 & j2 & g & -> & MU1 & WM1 & MI1 & ST1 & FR1 & SV1).
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (bv_unsigned sp - 352 - pd) ART0 ltac:(lia)); [| exact WM1].
    intros a NotCl. apply MU1. cbn [outside]. split; [| exact I]. intros Rng. apply NotCl. left. unfold USTACK_TOP in *. lia. }
  assert (CALL1 : call_ok RT Σ m1 (wz (bv_unsigned sp - 352 - pd)) lo).
  { unfold call_ok. rewrite (unsigned_lit (bv_unsigned sp - 352 - pd)) by lia.
    split; [exact ST1|]. split; [exact WIN|]. split; [clear - LOR PD0; unfold RT_STACK, PEMR_STACK, PEM_CALLEE_STACK in *; lia|].
    split; [clear - SPTOP PD0; unfold USTACK_TOP in *; lia|].
    clear - SP16 PDM PD0. Z.div_mod_to_equations. lia. }
  (* The allocator hands back a fresh 128-byte fake frame f. *)
  apply (SM1 Σ PMc (wz SITE_j0_sm) (wz (bv_unsigned sp - 352 - pd)) gp (wz TP_A) t0 t1 t2 sp (wz (bv_unsigned sp - 352 - pd)) (wz 96) v1 v2
            (wz PD) (wz PL) (wz flags) a6 a7 s2 (wz PL) (wz flags) (wz PN) s6 s7 s8 (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6 F fc m1 lo
            FDO MST ltac:(right; left; reflexivity) eq_refl ltac:(lia) ltac:(unfold pem_credit in CRD; lia) ART1 MI1 CALL1 T c1 Hc1A).
  intros c2 (Σ1 & f & Hc2 & FRS1 & LIV1 & SP01 & CRD1 & F0 & F64 & FTOP & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RET2 & AFT2 & PRES2 & WRF2 & WRS2) & Hc2A). clear Hc2.
  destruct RET2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  destruct AFT2 as (ART2 & MI2 & WM2 & ST2).
  rewrite (ret_pc_even SITE_j0_sm) in Hc2A by (unfold SITE_j0_sm; lia).
  assert (INF1 : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 f 1 ART2 INF1) as (_ & FBELOW & _ & FAPART).
  pose proof (af_frames_align RT AF Σ1 m2 f 1 ART2 INF1) as (_ & FSEG).
  pose proof (af_frames_hi RT AF Σ1 m2 f 1 ART2 INF1) as FHI.
  change (fs_size 1) with 128 in FBELOW, FAPART, FHI, FTOP. change (fs_size 1 - 8) with 120 in WRF2. change (fs_size 1 / 8) with 16 in WRS2.
  destruct (wr_at_rw_CB m2 f 120 WRF2 ltac:(lia)) as (fj & FRM2). change (Z.to_nat 120) with 120%nat in FRM2.
  destruct (wr_at_rw_CB m2 (shad f) 16 WRS2 ltac:(lia)) as (sj & SHM2). change (Z.to_nat 16) with 16%nat in SHM2.
  pose proof (af_client_consts RT AF Σ1 m2 ART2) as (_ & _ & _ & _ & UT2).
  (* Write the frame header and its shadow. *)
  pose proof (j0_w1a (bv_unsigned sp - 352 - pd) gp u0 u1 u2 sp b1 b2 b3 b4 b5 b6 b7 s2 s6 s7 s8 u3 u4 u5 u6 F2 fc2 m2 f PN PH PD PL flags fj sj
                F0 ltac:(unfold USTACK_TOP in FTOP; lia) (or_intror FSEG) ltac:(destruct FHI; [left|right]; lia) ltac:(lia) ltac:(unfold USTACK_TOP in *; lia)
                ltac:(lia) ltac:(rewrite SP01 in FBELOW; lia) PLpos ltac:(lia) UT2 FRM2 SHM2 MI2) as Walk1a.
  cl_lift Walk1a Hc2A c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & pcw & -> & MU3 & WM3 & MI3 & FF3 & SH3) & Hc3A). clear Hc3.
  rewrite (unsigned_lit (bv_unsigned sp - 352 - pd)) in ST2, PRES2 by lia.
  assert (SH16 : shad (f + fs_size 1) = shad f + 16) by (change (fs_size 1) with (64 * 2); rewrite (shad_add64 f 2 F64); lia).
  assert (SHlo : shad f + 16 <= lo) by (clear - FTOP LOW; unfold shad, SHB, USTACK_TOP in *; Z.div_mod_to_equations; lia).
  (* Everything the caller can see is untouched up to m3. *)
  assert (PR0 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned a) -> m3 a = m a).
  { intros a CLa.
    destruct (newframe_apart RT AF Σ Σ1 m2 f 1 (bv_unsigned sp) (bv_unsigned a) ART2 FRS1 LIV1 SP01 ltac:(lia) CLa) as (OutF & OutS).
    rewrite SH16 in OutS. change (fs_size 1) with 128 in OutF.
    rewrite (MU3 a) by (cbn [outside]; split; [lia|]; split; [lia| exact I]).
    assert (CL1 : aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp - 352 - pd) (bv_unsigned a))
      by (apply (aclient_mono _ _ (bv_unsigned sp) _ _ _ _ CLa); [intros e X; exact X| intros e X; exact X| lia]).
    rewrite (PRES2 a CL1).
    apply MU1. cbn [outside]. split; [| exact I].
    destruct (aclient_split RT AF Σ m (bv_unsigned sp) (bv_unsigned a) ART0 CLa); lia. }
  assert (SV3 : rw_cells asegs m3 (bv_unsigned sp - 104) (j0_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { apply (rw_cells_agree asegs m1 m3 _ _ SV1); [| exact (wmono_trans asegs m1 m2 m3 WM2 WM3)].
    intros a Ra. unfold j0_saved in Ra. cbn [cells_size csize Nat.add] in Ra. change (Z.of_nat 104) with 104 in Ra.
    rewrite (MU3 a) by (cbn [outside]; split; [lia|]; split; [lia| exact I]).
    apply PRES2. left. unfold USTACK_TOP in *. lia. }
  pose (en := PEMENT RT ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ PMc m lo outer canary LBL E K BI meth blen bmax boff flags
                     PN PH PD PL on oh od ol pd f (skipn 12 sj)).
  assert (COM3 : pem_com en Σ1 m3 boff (pem_credit (blen - boff) - 1) 21 []).
  { cbv beta iota delta [pem_com en e_PL e_sp1 e_plen e_live e_frames pem_saved
      e_ra e_sp e_gp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_Σ e_PMc e_m e_lo e_outer e_canary e_LBL e_E e_K
      e_BI e_meth e_blen e_bmax e_boff e_flags e_PN e_PH e_PD e_PLN e_on e_oh e_od e_ol e_pd e_f e_fsj].
    split.
    { apply (af_frame RT AF Σ1 m2 m3 (bv_unsigned sp - 352 - pd) ART2 ltac:(rewrite SP01; lia)); [| exact WM3].
      intros a NotCl. apply MU3. cbn [outside].
      split; [intros Rf; apply NotCl; apply (acl_frame _ _ _ f 1); [exact INF1| change (fs_size 1) with 128; lia]|].
      split; [intros Rs; apply NotCl; apply (acl_fshadow _ _ _ f 1); [exact INF1| rewrite SH16; lia]| exact I]. }
    split; [exact MI3|].
    split; [apply (stk_munch _ m2 m3 lo _ ST2 MU3 WM3); intros x Rx; cbn [outside]; split; [lia|]; split; [lia| exact I]|].
    split; [exact PD0|]. split; [exact PDM|]. split; [exact SPTOP|].
    split; [rewrite SP01; exact WIN|].
    split; [clear - LOR PD0; unfold RT_STACK, PEMR_STACK, PEM_CALLEE_STACK in *; lia|].
    split; [exact LOW|].
    split; [apply (cl_env_agree m m3 _ _ CLE); intros a CC; apply PR0; right; left; exact (cl_cell_static _ CC)|].
    split; [apply (sec_off_agree m m3 SEC); intros a EQa; apply PR0; right; left; rewrite EQa; exact sec_init_static|].
    split; [exact (libenv_keep libenv libenv_fp libenv_agree libenv_fp_where m m3 LBL E (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) []
                    LIBE (pres_fp_of_pres _ _ _ [] m m3 PR0) INCL (fun x _ => I))|].
    split; [exact INCL|]. split; [exact INE|]. split; [exact NLE|].
    split; [intros e INe; cbn [map]; rewrite app_nil_r; exact (NTL e INe)|].
    split.
    { rewrite LIV1. apply (mbio_rep_keep (rt_live RT Σ) (rt_live RT Σ) m m3 K BI meth blen bmax boff (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) []
                            MB (pres_fp_of_pres _ _ _ [] m m3 PR0)).
      - intros e INe. split; exact (mbio_rep_ents _ _ _ _ _ _ _ _ e MB INe).
      - intros e x _ _. exact I. }
    split; [lia|]. split; [split; [lia| exact BLT]|].
    split; [intros e INe; exact (mbio_rep_ents _ _ _ _ _ _ _ _ e MB INe)|].
    split; [rewrite LIV1; apply Permutation_refl|].
    split; [intros e []|].
    split; [cbn [map app]; constructor; [exact (NTL (E, 904) (or_introl eq_refl))| exact NDK]|].
    split; [rewrite LIV1; exact LPOS|].
    split; [exact FRS1|]. split; [exact FRN|]. split; [exact SP01|]. split; [exact CG1|].
    split; [rewrite LIV1; exact LIVN|]. split; [lia|].
    split; [rewrite CRD1; lia|]. split; [unfold pem_credit; lia|]. split; [exact CRD|].
    split; [rewrite CG1; exact CGH|]. split; [exact HCG|].
    split; [rewrite CG1; exact CTX|].
    split; [apply (uw_chain_agree outer m m3 sp s0 UWC); intros a Ra; apply PR0; left; exact Ra|].
    split; [exact F0|]. split; [exact F64|]. split; [exact FTOP|]. split; [exact FSEG|].
    split; [destruct FHI; [left|right]; lia|].
    split; [exact SH3|].
    split; [exact SV3|].
    split; [exact (pres_fp_of_pres _ _ _ _ m m3 PR0)|].
    split; [exact FLG|]. split; [exact NDP|].
    split; [apply Forall_forall; exact LOCS|].
    split; [exact FDO| exact MST]. }
  pose proof COM3 as (_ & _ & ST3 & _). change (stk asegs m3 lo (bv_unsigned sp - 352 - pd)) in ST3.
  pose proof (wmono_trans asegs m m1 m3 WM1 (wmono_trans asegs m1 m2 m3 WM2 WM3)) as WM03.
  assert (APART : forall P Q, P mod 8 = 0 -> Q mod 8 = 0 -> P <> Q -> P + 8 <= Q \/ Q + 8 <= P)
    by (intros P Q P0 Q0 NE; clear - P0 Q0 NE; Z.div_mod_to_equations; lia).
  pose proof NDP as NDall. apply NoDup_cons_iff in NDall as (NotN & NDall). apply NoDup_cons_iff in NDall as (NotH & NDall).
  apply NoDup_cons_iff in NDall as (NotD & _).
  assert (DNH : PN + 8 <= PH \/ PH + 8 <= PN) by (apply APART; [exact PN8| exact PH8| intros X; apply NotN; left; congruence]).
  assert (DND : PN + 8 <= PD \/ PD + 8 <= PN) by (apply APART; [exact PN8| exact PD8| intros X; apply NotN; right; left; congruence]).
  assert (DNL : PN + 8 <= PL \/ PL + 8 <= PN) by (apply APART; [exact PN8| exact PL8| intros X; apply NotN; right; right; left; congruence]).
  assert (DHD : PH + 8 <= PD \/ PD + 8 <= PH) by (apply APART; [exact PH8| exact PD8| intros X; apply NotH; left; congruence]).
  assert (DHL : PH + 8 <= PL \/ PL + 8 <= PH) by (apply APART; [exact PH8| exact PL8| intros X; apply NotH; right; left; congruence]).
  assert (DDL : PD + 8 <= PL \/ PL + 8 <= PD) by (apply APART; [exact PD8| exact PL8| intros X; apply NotD; left; congruence]).
  (* The 248 + pd bytes below the saved registers, carved into the slots the later blocks expect. *)
  assert (FR3 : rw_cells asegs m3 (bv_unsigned sp - 352 - pd) [CB 216 j1; C8 (wz BI); CB 24 j2; CB (Z.to_nat pd) g]).
  { apply (rw_cells_agree asegs m1 m3 _ _ FR1); [| exact (wmono_trans asegs m1 m2 m3 WM2 WM3)].
    intros a Ra. cbn [cells_size csize] in Ra.
    rewrite (MU3 a) by (cbn [outside]; split; [lia|]; split; [lia| exact I]).
    apply PRES2. left. unfold USTACK_TOP in *. lia. }
  destruct (j0_frame_split m3 (bv_unsigned sp - 352 - pd) j1 (wz BI) j2 [CB (Z.to_nat pd) g] FR3)
    as (jA & jH & jF & endv & jE & x1 & x2 & x3 & Slot0 & SlotH & SlotF & SlotEnd & SlotE & SlotBI & Slot224 & SlotGap).
  destruct (j0_ff_split m3 f pcw (skipn 24 fj) FF3) as (hj & lenv & jj1 & tav & jj2 & bmv & jj3 & FFC3).
  (* Stash the fake frame pointer. *)
  pose proof (out_sh0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ1 m3 boff _ _ [] PL fL kL COM3
                (or_intror (or_intror (or_intror (or_introl eq_refl)))) INL FLlo FLhi SHL) as ShPL3.
  pose proof (j0_w1b (bv_unsigned sp - 352 - pd) gp u0 u1 u2 sp pcw b6 b7 s7 u3 u4 u5 u6 F2 fc2 m3 f PN PH PD PL flags x1 x2 x3
                ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(lia) PLpos ltac:(lia) PL8 MI3 Slot224 ShPL3) as Walk1b.
  cl_lift Walk1b Hc3A c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (m4 & -> & MU4 & WM4 & MI4 & Slot224') & Hc4A). clear Hc4.
  assert (ST4 : stk asegs m4 lo (bv_unsigned sp - 352 - pd))
    by (apply (stk_munch _ m3 m4 lo _ ST3 MU4 WM4); intros x Rx; cbn [outside]; split; [lia| exact I]).
  pose proof (com_seg RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ1 m3 m4 boff _ _ []
                [(bv_unsigned sp - 352 - pd + 240, bv_unsigned sp - 352 - pd + 248)] COM3 MU4 WM4 MI4 ST4
                ltac:(constructor; [| constructor]; left; cbv beta iota delta [en e_sp1 e_PL e_sp e_pd fst snd]; lia)) as COM4.
  (* Clear *PL. *)
  assert (CPL4 : rw_cells asegs m4 PL [C8 ol]).
  { apply (rw_cells_agree asegs m m4 _ _ CPL); [| exact (wmono_trans asegs m m3 m4 WM03 WM4)].
    intros a Ra. cbn [cells_size csize Nat.add] in Ra. change (Z.of_nat 8) with 8 in Ra.
    rewrite (MU4 a) by (cbn [outside]; split; [lia| exact I]). apply PR0. apply (acl_frame _ _ _ fL kL); [exact INL| lia]. }
  pose proof (out_sh0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ1 m4 boff _ _ [] PH fH kH COM4
                (or_intror (or_introl eq_refl)) INH FHlo FHhi SHH) as ShPH4.
  pose proof (j0_w1c (bv_unsigned sp - 352 - pd) gp u0 u1 u2 sp pcw b6 b7 s7 u3 u4 u5 u6 F2 fc2 m4 f PN PH PD PL flags ol
                PLpos ltac:(lia) ltac:(destruct PLsh; [left|right]; lia) PHpos ltac:(lia) PH8 MI4 CPL4 ShPH4) as Walk1c.
  cl_lift Walk1c Hc4A c5 Hc5.
  destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (m5 & -> & MU5 & WM5 & MI5 & ZPL5) & Hc5A). clear Hc5.
  assert (ST5 : stk asegs m5 lo (bv_unsigned sp - 352 - pd))
    by (apply (stk_munch _ m4 m5 lo _ ST4 MU5 WM5); intros x Rx; cbn [outside]; split; [lia| exact I]).
  pose proof (com_out_store RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ1 m4 m5 boff _ _ [] PL fL kL COM4
                (or_intror (or_intror (or_intror (or_introl eq_refl)))) INL FLlo FLhi MU5 WM5 MI5 ST5) as COM5.
  (* Clear *PH. *)
  assert (CPH5 : rw_cells asegs m5 PH [C8 oh]).
  { apply (rw_cells_agree asegs m m5 _ _ CPH); [| exact (wmono_trans asegs m m4 m5 (wmono_trans asegs m m3 m4 WM03 WM4) WM5)].
    intros a Ra. cbn [cells_size csize Nat.add] in Ra. change (Z.of_nat 8) with 8 in Ra.
    rewrite (MU5 a) by (cbn [outside]; split; [lia| exact I]). rewrite (MU4 a) by (cbn [outside]; split; [lia| exact I]).
    apply PR0. apply (acl_frame _ _ _ fH kH); [exact INH| lia]. }
  pose proof (out_sh0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ1 m5 boff _ _ [] PN fN kN COM5
                (or_introl eq_refl) INN FNlo FNhi SHN) as ShPN5.
  pose proof (j0_w1d (bv_unsigned sp - 352 - pd) gp u0 u1 u2 sp pcw b6 b7 s7 u3 u4 u5 u6 F2 fc2 m5 f PN PH PD PL flags oh
                PHpos ltac:(lia) ltac:(destruct PHsh; [left|right]; lia) PNpos ltac:(lia) PN8 MI5 CPH5 ShPN5) as Walk1d.
  cl_lift Walk1d Hc5A c6 Hc6.
  destruct (ASTA_unpack RT Σ1 _ _ c6 Hc6) as (ms6 & (m6 & -> & MU6 & WM6 & MI6 & ZPH6) & Hc6A). clear Hc6.
  assert (ST6 : stk asegs m6 lo (bv_unsigned sp - 352 - pd))
    by (apply (stk_munch _ m5 m6 lo _ ST5 MU6 WM6); intros x Rx; cbn [outside]; split; [lia| exact I]).
  pose proof (com_out_store RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ1 m5 m6 boff _ _ [] PH fH kH COM5
                (or_intror (or_introl eq_refl)) INH FHlo FHhi MU6 WM6 MI6 ST6) as COM6.
  (* Clear *PN. *)
  assert (CPN6 : rw_cells asegs m6 PN [C8 on]).
  { apply (rw_cells_agree asegs m m6 _ _ CPN);
      [| exact (wmono_trans asegs m m5 m6 (wmono_trans asegs m m4 m5 (wmono_trans asegs m m3 m4 WM03 WM4) WM5) WM6)].
    intros a Ra. cbn [cells_size csize Nat.add] in Ra. change (Z.of_nat 8) with 8 in Ra.
    rewrite (MU6 a) by (cbn [outside]; split; [lia| exact I]). rewrite (MU5 a) by (cbn [outside]; split; [lia| exact I]).
    rewrite (MU4 a) by (cbn [outside]; split; [lia| exact I]).
    apply PR0. apply (acl_frame _ _ _ fN kN); [exact INN| lia]. }
  pose proof (out_sh0 RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS en Σ1 m6 boff _ _ [] PD fD kD COM6
                (or_intror (or_intror (or_introl eq_refl))) IND FDlo FDhi SHD) as ShPD6.
  pose proof (j0_w1e (bv_unsigned sp - 352 - pd) gp u0 u1 u2 sp pcw b6 b7 s7 u3 u4 u5 u6 F2 fc2 m6 f PN PH PD PL flags on
                PNpos ltac:(lia) ltac:(destruct PNsh; [left|right]; lia) PDpos ltac:(lia) PD8 MI6 CPN6 ShPD6) as Walk1e.
  cl_lift Walk1e Hc6A c7 Hc7.
  destruct (ASTA_unpack RT Σ1 _ _ c7 Hc7) as (ms7 & (m7 & -> & MU7 & WM7 & MI7 & ZPN7) & Hc7A). clear Hc7.
  assert (ST7 : stk asegs m7 lo (bv_unsigned sp - 352 - pd))
    by (apply (stk_munch _ m6 m7 lo _ ST6 MU7 WM7); intros x Rx; cbn [outside]; split; [lia| exact I]).
  pose proof (com_out_store RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ1 m6 m7 boff _ _ [] PN fN kN COM6
                (or_introl eq_refl) INN FNlo FNhi MU7 WM7 MI7 ST7) as COM7.
  (* Clear *PD and pick the continuation from the flags. *)
  assert (CPD7 : rw_cells asegs m7 PD [C8 od]).
  { apply (rw_cells_agree asegs m m7 _ _ CPD);
      [| exact (wmono_trans asegs m m6 m7 (wmono_trans asegs m m5 m6 (wmono_trans asegs m m4 m5 (wmono_trans asegs m m3 m4 WM03 WM4) WM5) WM6) WM7)].
    intros a Ra. cbn [cells_size csize Nat.add] in Ra. change (Z.of_nat 8) with 8 in Ra.
    rewrite (MU7 a) by (cbn [outside]; split; [lia| exact I]). rewrite (MU6 a) by (cbn [outside]; split; [lia| exact I]).
    rewrite (MU5 a) by (cbn [outside]; split; [lia| exact I]). rewrite (MU4 a) by (cbn [outside]; split; [lia| exact I]).
    apply PR0. apply (acl_frame _ _ _ fD kD); [exact IND| lia]. }
  pose proof (j0_w1f (bv_unsigned sp - 352 - pd) gp u0 u1 u2 sp b6 b7 s7 u3 u4 u5 u6 F2 fc2 m7 f PN PH PD PL flags od
                PDpos ltac:(lia) FLG MI7 CPD7) as Walk1f.
  cl_lift Walk1f Hc7A c8 Hc8.
  destruct (ASTA_unpack RT Σ1 _ _ c8 Hc8) as (ms8 & (m8 & -> & MU8 & WM8 & MI8 & ZPD8) & Hc8A). clear Hc8.
  assert (ST8 : stk asegs m8 lo (bv_unsigned sp - 352 - pd))
    by (apply (stk_munch _ m7 m8 lo _ ST7 MU8 WM8); intros x Rx; cbn [outside]; split; [lia| exact I]).
  pose proof (com_out_store RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ1 m7 m8 boff _ _ [] PD fD kD COM7
                (or_intror (or_intror (or_introl eq_refl))) IND FDlo FDhi MU8 WM8 MI8 ST8) as COM8.
  pose proof (wmono_trans asegs m3 m7 m8 (wmono_trans asegs m3 m6 m7 (wmono_trans asegs m3 m5 m6 (wmono_trans asegs m3 m4 m5 WM4 WM5) WM6) WM7) WM8)
    as WM38.
  pose proof (wmono_trans asegs m4 m7 m8 (wmono_trans asegs m4 m6 m7 (wmono_trans asegs m4 m5 m6 WM5 WM6) WM7) WM8) as WM48.
  (* What the four output stores and the frame-pointer stash leave alone. *)
  assert (LOWKEEP : forall a : word, bv_unsigned a < lo -> ~ (PL <= bv_unsigned a < PL + 8) -> ~ (PH <= bv_unsigned a < PH + 8)
            -> ~ (PN <= bv_unsigned a < PN + 8) -> ~ (PD <= bv_unsigned a < PD + 8) -> m8 a = m3 a).
  { intros a Below NL NH NN ND.
    rewrite (MU8 a) by (cbn [outside]; split; [exact ND| exact I]). rewrite (MU7 a) by (cbn [outside]; split; [exact NN| exact I]).
    rewrite (MU6 a) by (cbn [outside]; split; [exact NH| exact I]). rewrite (MU5 a) by (cbn [outside]; split; [exact NL| exact I]).
    rewrite (MU4 a) by (cbn [outside]; split; [lia| exact I]). reflexivity. }
  assert (HIGHKEEP : forall a : word, lo <= bv_unsigned a -> ~ (bv_unsigned sp - 352 - pd + 240 <= bv_unsigned a < bv_unsigned sp - 352 - pd + 248)
            -> m8 a = m3 a).
  { intros a Above NotStash.
    rewrite (MU8 a) by (cbn [outside]; split; [lia| exact I]). rewrite (MU7 a) by (cbn [outside]; split; [lia| exact I]).
    rewrite (MU6 a) by (cbn [outside]; split; [lia| exact I]). rewrite (MU5 a) by (cbn [outside]; split; [lia| exact I]).
    rewrite (MU4 a) by (cbn [outside]; split; [exact NotStash| exact I]). reflexivity. }
  assert (REST8 : errst_at_rest E [] m8).
  { apply (errst_rest_agree m m8 E [] REST). intros a FPa.
    destruct (errst_fp_where E [] (bv_unsigned a) FPa) as [Ea | (p & n & [] & _)].
    pose proof (af_live_range RT AF Σ m E 904 ART0 INE) as (_ & Etop & _).
    rewrite (LOWKEEP a); [| lia | destruct (PLlive E 904 INE); lia | destruct (PHlive E 904 INE); lia
                         | destruct (PNlive E 904 INE); lia | destruct (PDlive E 904 INE); lia].
    apply PR0. apply (acl_live _ _ _ E 904); [exact INE| lia]. }
  assert (SL0 : rw_cells asegs m8 (bv_unsigned sp - 352 - pd) [CB 24 jA]).
  { apply (rw_cells_agree asegs m3 m8 _ _ Slot0); [| exact WM38]. intros a Ra.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ra. apply HIGHKEEP; lia. }
  assert (SLH : rw_cells asegs m8 (bv_unsigned sp - 352 - pd + 24) [CB 56 jH]).
  { apply (rw_cells_agree asegs m3 m8 _ _ SlotH); [| exact WM38]. intros a Ra.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ra. apply HIGHKEEP; lia. }
  assert (SLF : rw_cells asegs m8 (bv_unsigned sp - 352 - pd + 80) [CB 24 jF]).
  { apply (rw_cells_agree asegs m3 m8 _ _ SlotF); [| exact WM38]. intros a Ra.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ra. apply HIGHKEEP; lia. }
  assert (SLEnd : rw_cells asegs m8 (bv_unsigned sp - 352 - pd + 104) [C8 endv]).
  { apply (rw_cells_agree asegs m3 m8 _ _ SlotEnd); [| exact WM38]. intros a Ra.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ra. apply HIGHKEEP; lia. }
  assert (SLE : rw_cells asegs m8 (bv_unsigned sp - 352 - pd + 112) [CB 104 jE]).
  { apply (rw_cells_agree asegs m3 m8 _ _ SlotE); [| exact WM38]. intros a Ra.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ra. apply HIGHKEEP; lia. }
  assert (SLBI : rw_cells asegs m8 (bv_unsigned sp - 352 - pd + 216) [C8 (wz BI)]).
  { apply (rw_cells_agree asegs m3 m8 _ _ SlotBI); [| exact WM38]. intros a Ra.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ra. apply HIGHKEEP; lia. }
  assert (SL224 : rw_cells asegs m8 (bv_unsigned sp - 352 - pd + 224) [C8 x1; C8 x2; C8 (wz f)]).
  { apply (rw_cells_agree asegs m4 m8 _ _ Slot224'); [| exact WM48]. intros a Ra.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ra.
    rewrite (MU8 a) by (cbn [outside]; split; [lia| exact I]). rewrite (MU7 a) by (cbn [outside]; split; [lia| exact I]).
    rewrite (MU6 a) by (cbn [outside]; split; [lia| exact I]). rewrite (MU5 a) by (cbn [outside]; split; [lia| exact I]). reflexivity. }
  assert (SLGap : rw_cells asegs m8 (bv_unsigned sp - 352 - pd + 248) [CB (Z.to_nat pd) g]).
  { apply (rw_cells_agree asegs m3 m8 _ _ SlotGap); [| exact WM38]. intros a Ra.
    cbn [cells_size csize] in Ra. apply HIGHKEEP; lia. }
  assert (FFC8 : rw_cells asegs m8 f (ff_cells hj lenv jj1 tav jj2 bmv jj3)).
  { apply (rw_cells_agree asegs m3 m8 _ _ FFC3); [| exact WM38]. intros a Ra.
    unfold ff_cells in Ra. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ra.
    assert (SEPL : f + 128 <= fL \/ fL + fs_size kL <= f) by exact (af_frames_disj RT AF Σ1 m2 f 1 fL kL [] (rt_frames RT Σ) ART2 FRS1 INL).
    assert (SEPH : f + 128 <= fH \/ fH + fs_size kH <= f) by exact (af_frames_disj RT AF Σ1 m2 f 1 fH kH [] (rt_frames RT Σ) ART2 FRS1 INH).
    assert (SEPN : f + 128 <= fN \/ fN + fs_size kN <= f) by exact (af_frames_disj RT AF Σ1 m2 f 1 fN kN [] (rt_frames RT Σ) ART2 FRS1 INN).
    assert (SEPD : f + 128 <= fD \/ fD + fs_size kD <= f) by exact (af_frames_disj RT AF Σ1 m2 f 1 fD kD [] (rt_frames RT Σ) ART2 FRS1 IND).
    apply LOWKEEP; lia. }
  assert (OUT8 : out_null RT en m8).
  { split; [| split; [| split]].
    - apply (rw_cells_agree asegs m7 m8 _ _ ZPN7); [| exact WM8]. intros a Ra.
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ra.
      rewrite (MU8 a) by (cbn [outside]; split; [lia| exact I]). reflexivity.
    - apply (rw_cells_agree asegs m6 m8 _ _ ZPH6); [| exact (wmono_trans asegs m6 m7 m8 WM7 WM8)]. intros a Ra.
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ra.
      rewrite (MU8 a) by (cbn [outside]; split; [lia| exact I]). rewrite (MU7 a) by (cbn [outside]; split; [lia| exact I]). reflexivity.
    - exact ZPD8.
    - apply (rw_cells_agree asegs m5 m8 _ _ ZPL5); [| exact (wmono_trans asegs m5 m7 m8 (wmono_trans asegs m5 m6 m7 WM6 WM7) WM8)]. intros a Ra.
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ra.
      rewrite (MU8 a) by (cbn [outside]; split; [lia| exact I]). rewrite (MU7 a) by (cbn [outside]; split; [lia| exact I]).
      rewrite (MU6 a) by (cbn [outside]; split; [lia| exact I]). reflexivity. }
  case_eq (Z.land flags 6 =? 6); intros FL6; rewrite FL6 in Hc8A.
  - exact (H_R0 en Σ1 m8 (pem_credit (blen - boff) - 1) 21 jA [CB 56 jH] [CB 24 jF] endv x1 x2 g hj lenv jj1 tav jj2 bmv jj3 F2 fc2
             (wz SITE_j0_sm) u0 u1 u2 (wz (Z.land flags 6)) (wz 6) (wz (PD / 8 + SHB)) (wz (PH / 8 + SHB)) (wz (PL / 8 + SHB)) (wz (PN / 8 + SHB))
             b6 b7 (wz PL) (wz PN) s7 (wz PD) (wz PH) u3 u4 u5 u6 [CB 104 jE]
             COM8 REST8 ltac:(clear - OFFR; unfold C_END, pem_credit; change (2 ^ 22) with 4194304; lia) ltac:(lia)
             SL0 SLH eq_refl SLF eq_refl SLEnd SLE eq_refl SLBI SL224 SLGap FFC8 OUT8 T c8 Hc8A Hk).
  - assert (GNC : gn_need RT en boff + 4 <= pem_credit (blen - boff) - 1).
    { cbv beta iota delta [gn_need grow_pot grow_cap gr_n en e_plen e_blen e_boff C_END pem_credit].
      change (2 ^ 16) with 65536. change (2 ^ 22) with 4194304. clear - OFFR. Z.div_mod_to_equations. lia. }
    exact (H_J0N en Σ1 m8 (pem_credit (blen - boff) - 1) 21 jA [CB 56 jH] [CB 24 jF] endv x1 x2 g hj lenv jj1 tav jj2 bmv jj3 F2 fc2
             (wz SITE_j0_sm) u0 u1 u2 (wz (Z.land flags 6)) (wz 6) b6 b7 s7 u3 u4 u5 u6 [CB 104 jE]
             COM8 REST8 GNC ltac:(lia) SL0 SLH eq_refl SLF eq_refl SLEnd SLE eq_refl SLBI SL224 SLGap FFC8 OUT8 T c8 Hc8A Hk).
Qed.
End CJ0.
