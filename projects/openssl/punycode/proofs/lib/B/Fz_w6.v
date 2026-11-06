(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.punycode.lib.B Require Import Layout R_small R_m2s I_consts RT_iface D_defs D_kit D_libiface X_atexit Fz_defs Fz_tac.
From OSSVerify.Proofs.openssl.punycode.lib.B Require R_cache_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Definition wc_frame (j : list byte) (s5 s4 s3 s2 s1 s0 ra : word) : list cell := [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma a2_wD : forall (L lo FB6 p : Z) (ra gp tp u0 u1 u2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem),
  stk bsegs m lo L -> 0x7fff7f800000 <= lo <= 2^47 -> lo + 0x1000 <= L -> L < 2^63 ->
  client_consts m -> mem_inv bsegs m ->
  FB6 mod 64 = 0 -> 0xbfd000 <= FB6 -> FB6 + 4096 <= lo -> (FB6 + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= FB6) ->
  0 < p -> p mod 16 = 0 -> p + 40 <= lo ->
  ro_cells bsegs m (shad FB6 + 281) [C1 (Z_to_bv 8 0)] ->
  ro_cells bsegs m (FB6 + 2248) [C8 (Z_to_bv 64 p)] ->
  ro_cells bsegs m (shad p) [C1 (Z_to_bv 8 0)] -> ro_cells bsegs m p [C8 (Z_to_bv 64 0)] ->
  ro_cells bsegs m G_FREE_IMPL [C8 (Z_to_bv 64 e_cfree)] -> ro_cells bsegs m 0x5e2570 [C8 (Z_to_bv 64 e_cfree)] ->
  evt bsegs (fun ms => exists (m1 : mem) (jf : list byte),
      ms = entry_st (Z_to_bv 64 0x273ea4) (Z_to_bv 64 (L + -64)) gp tp u0 (Z_to_bv 64 2025576) u2 (Z_to_bv 64 L) (Z_to_bv 64 (FB6 + 2248))
             (Z_to_bv 64 p) (Z_to_bv 64 185887) (Z_to_bv 64 540) (Z_to_bv 64 2025576) (Z_to_bv 64 6170748) a5 a6 a7 (Z_to_bv 64 185887)
             (Z_to_bv 64 SHB) (Z_to_bv 64 (shad FB6 + 281)) (Z_to_bv 64 0) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc e_free m1
      /\ munch [(L + -80, L)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (L + -64)
      /\ rw_cells bsegs m1 (L + -64) (wc_frame jf (Z_to_bv 64 (FB6 + 2208)) s4 s3 s2 (Z_to_bv 64 L) s0 (Z_to_bv 64 0x43180c)))
    (MS (mkR ra (Z_to_bv 64 L) gp tp u0 u1 u2 s0 (Z_to_bv 64 L) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (FB6 + 2208)) s6 s7 s8 s9 s10 s11
             u3 u4 u5 u6) F (Z_to_bv 64 0x431800) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LOS LO SPH CC MI F64 FLO FHI FBAND Hp P16 PLO SH281 SUBS SHP PAR GF GG.
  destruct CC as (G1 & G2 & G3 & G4).
  unfold entry_st, e_free, wc_frame, e_cfree, G_FREE_IMPL, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar,
    g_detect_stack_use_after_return in *.
  unfold shad, SHB in *.
  assert (EP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (E2248 : (FB6 + 2248) ≫ 3 = FB6 / 8 + 281) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  assert (EP3 : p ≫ 3 = p / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  replace (FB6 / 8 + 2147450880 + 281) with (FB6 / 8 + 2147451161) in SH281 by lia.
  assert (EA1 : Z.land (FB6 + 2208) 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
  assert (EA2 : Z.land p 7 = 0) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(L + -80, L)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  xs_to 0x273e1c%Z.
  carve_frame 64%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat (tryif at_pc 0x1ee868%Z then fail else (xs; rewrite ?EA1, ?EA2; repeat match goal with E : (_ ≫ 3 = _) |- _ => rewrite E end)).
  rename FR into FRC.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8;8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  xs_to 0x1bdf4c%Z.
  release_frame FR ST (L + -64).
  apply evt_done. do 2 eexists. split; [replace (FB6 / 8 + 2147450880 + 281) with (FB6 / 8 + 2147451161) by lia; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|].
  split; [exact WM|]. split; [assumption|]. split; [exact ST | exact FRC].
Qed.

(* [comment removed for export] *)
Lemma a2_wE : forall (L lo FB6 : Z) (gp tp u0 u1 u2 a0 a1 a2 a3 a4 a5 a6 a7 f5 f4 f3 f2 f1 f0 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem) (jf : list byte) (sv : word),
  stk bsegs m lo (L + -64) -> 0x7fff7f800000 <= lo <= 2^47 -> lo + 0x1000 <= L -> L < 2^63 -> mem_inv bsegs m ->
  FB6 mod 64 = 0 -> 0xbfd000 <= FB6 -> FB6 + 4096 <= lo -> (FB6 + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= FB6) ->
  ro_cells bsegs m (shad FB6 + 281) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (FB6 + 2248) [C8 sv] ->
  rw_cells bsegs m (L + -64) (wc_frame jf f5 f4 f3 f2 f1 f0 (Z_to_bv 64 0x43180c)) ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (Z_to_bv 64 0x43180c) (Z_to_bv 64 L) gp tp u0 u1 u2 f0 f1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 f2 f3 f4 f5 s6 s7 s8 s9 s10 s11
                   u3 u4 u5 u6) F (Z_to_bv 64 0x43180c) fc None m1 (seg_rom bsegs)
      /\ munch [(FB6 + 2248, FB6 + 2256)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo L
      /\ rw_cells bsegs m1 (FB6 + 2248) [C8 (Z_to_bv 64 0)])
    (MS (mkR (Z_to_bv 64 0x273ea4) (Z_to_bv 64 (L + -64)) gp tp u0 u1 u2 (Z_to_bv 64 L) (Z_to_bv 64 (FB6 + 2248)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 185887) (Z_to_bv 64 SHB) (Z_to_bv 64 (shad FB6 + 281)) (Z_to_bv 64 0) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x273ea4) fc None m (seg_rom bsegs)).
Proof.
  intros until sv. intros ST LOS LO SPH MI F64 FLO FHI FBAND SH281 SUBS FR.
  unfold wc_frame in *. unfold shad, SHB in *.
  assert (SEPH : FB6 + 4096 <= FB6 / 8 + 2147450880 \/ FB6 / 8 + 2147450880 + 512 <= FB6) by (Z.div_mod_to_equations; lia).
  assert (SEPI : 0xbfd000 <= FB6 / 8 + 2147450880) by (Z.div_mod_to_equations; lia).
  replace (FB6 / 8 + 2147450880 + 281) with (FB6 / 8 + 2147451161) in * by lia.
  pose proof (munch_refl [(FB6 + 2248, FB6 + 2256)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  xs_to 0x43180c%Z.
  release_frame FR ST L.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST | exact SUBS].
Qed.

(* [comment removed for export] *)
Lemma a2_wF : forall (L lo FB6 : Z) (gp tp u0 u1 u2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem) (js : list byte),
  0x7fff7f800000 <= lo <= 2^47 -> L < 2^63 -> lo + 0x1000 <= L -> mem_inv bsegs m ->
  FB6 mod 64 = 0 -> 0xbfd000 <= FB6 -> FB6 + 4096 <= lo -> (FB6 + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= FB6) ->
  ro_cells bsegs m (L + 24) [C8 (Z_to_bv 64 (shad FB6 + 4)); C8 (Z_to_bv 64 FB6); C8 (Z_to_bv 64 FB6)] ->
  rw_cells bsegs m (shad FB6 + 276) [CB 7 js] ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0x431848) (Z_to_bv 64 L) gp tp u0 u1 u2 s0 (Z_to_bv 64 L) (Z_to_bv 64 (shad FB6 + 4)) (Z_to_bv 64 256)
             a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (shad FB6)) (Z_to_bv 64 FB6) s5 s6 s7 s8 (Z_to_bv 64 FB6) s10 (Z_to_bv 64 (shad FB6 + 4))
             u3 u4 u5 u6 F fc (e_set_shadow 0xf8) m1
      /\ munch [(shad FB6 + 276, shad FB6 + 283)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (shad FB6 + 276) (repeat (C1 (Z_to_bv 8 (-8))) 7))
    (MS (mkR (Z_to_bv 64 0x43180c) (Z_to_bv 64 L) gp tp u0 u1 u2 s0 (Z_to_bv 64 L) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (shad FB6))
             s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x43180c) fc None m (seg_rom bsegs)).
Proof.
  intros until js. intros LOS SPH LO MI F64 FLO FHI FBAND SP CSH.
  unfold entry_st, e_set_shadow in *. cbn [repeat]. unfold shad, SHB in *.
  assert (SEPI : 0xbfd000 <= FB6 / 8 + 2147450880) by (Z.div_mod_to_equations; lia).
  assert (SEPS2 : FB6 / 8 + 2147450880 + 512 <= lo) by (Z.div_mod_to_equations; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (FB6 / 8 + 2147450880)) = FB6 / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  replace (FB6 / 8 + 2147450880 + 276) with (FB6 / 8 + 2147451156) in * by lia.
  pose proof (munch_refl [(FB6 / 8 + 2147451156, FB6 / 8 + 2147451156 + 7)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  apply (rw_cells_split_CB bsegs _ _ [] 7 _ [] [1;1;1;1;1;1;1]%nat) in CSH; [| reflexivity].
  cbn [mk_CB_cells app] in CSH.
  xs_to 0x1c02a8%Z.
  apply evt_done. eexists. split; [replace (FB6 / 8 + 2147450880 + 4) with (FB6 / 8 + 2147450884) by lia; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|].
  split; [exact WM|]. split; [assumption | exact CSH].
Qed.

(* [comment removed for export] *)
Lemma a2_wG : forall (L lo FB6 : Z) (gp tp u0 u1 u2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s10 s11 u3 u4 u5 u6 : word) F fc (m : mem) (jh0 : list byte),
  0x7fff7f800000 <= lo <= 2^47 -> L < 2^63 -> lo + 0x1000 <= L -> mem_inv bsegs m ->
  FB6 mod 64 = 0 -> 0xbfd000 <= FB6 -> FB6 + 4096 <= lo ->
  rw_cells bsegs m FB6 [CB 8 jh0] ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0x43186c) (Z_to_bv 64 L) gp tp u0 u1 u2 s0 (Z_to_bv 64 L) (Z_to_bv 64 FB6) (Z_to_bv 64 2368)
             a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 FB6) s5 s6 s7 s8 (Z_to_bv 64 FB6) s10 s11 u3 u4 u5 u6 F fc e_stack_free_6 m1
      /\ munch [(FB6, FB6 + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 FB6 [C8 (Z_to_bv 64 0x45e0360e)])
    (MS (mkR (Z_to_bv 64 0x431848) (Z_to_bv 64 L) gp tp u0 u1 u2 s0 (Z_to_bv 64 L) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 FB6)
             s5 s6 s7 s8 (Z_to_bv 64 FB6) s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x431848) fc None m (seg_rom bsegs)).
Proof.
  intros until jh0. intros LOS SPH LO MI F64 FLO FHI HDR.
  unfold entry_st, e_stack_free_6 in *.
  assert (EF : bv_unsigned (Z_to_bv 64 FB6) = FB6) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(FB6, FB6 + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  xs_to 0x1a1f9c%Z.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption | exact HDR].
Qed.

(* [comment removed for export] *)
Lemma a2_wH : forall (L lo : Z) (gp tp u0 u1 u2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word) F fc (m : mem)
    (f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 : word),
  stk bsegs m lo L -> 0x7fff7f800000 <= lo <= 2^47 -> L + 192 < 2^63 -> lo + 0x1000 <= L -> mem_inv bsegs m ->
  rw_cells bsegs m (L + 88) [C8 f11; C8 f10; C8 f9; C8 f8; C8 f7; C8 f6; C8 f5; C8 f4; C8 f3; C8 f2; C8 f1; C8 f0;
                               C8 (Z_to_bv 64 0x1ee1b8)] ->
  evt bsegs (fun ms =>
      ms = MS (mkR (Z_to_bv 64 0x1ee1b8) (Z_to_bv 64 (L + 192)) gp tp u0 u1 u2 f0 f1 s8 a1 a2 a3 a4 a5 a6 a7 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
                   u3 u4 u5 u6) F (Z_to_bv 64 0x1ee1b8) fc None m (seg_rom bsegs))
    (MS (mkR (Z_to_bv 64 0x43186c) (Z_to_bv 64 L) gp tp u0 u1 u2 (Z_to_bv 64 (L + 192)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
             s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x43186c) fc None m (seg_rom bsegs)).
Proof.
  intros until f0. intros ST LOS SPH LO MI FR.
  assert (EL : bv_unsigned (Z_to_bv 64 (L + 192)) = L + 192) by (apply unsigned_lit; lia).
  xs_to 0x1ee1b8%Z.
  apply evt_done. reflexivity.
Qed.
