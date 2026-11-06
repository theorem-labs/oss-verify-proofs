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
Lemma fz_wF : forall (usp spa lo b : Z) (gp tp u0 u1 u2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word) F fc (m : mem),
  stk bsegs m lo spa -> 0x7fff7f800000 <= lo <= 2^47 -> lo + 0x1000 <= spa -> spa < 2^63 -> mem_inv bsegs m ->
  ro_cells bsegs m G_FREE_IMPL [C8 (Z_to_bv 64 e_cfree)] -> ro_cells bsegs m 0x5e2570 [C8 (Z_to_bv 64 e_cfree)] ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0x1ee1cc) (Z_to_bv 64 spa) gp tp u0 (Z_to_bv 64 2025576) u2 (Z_to_bv 64 usp) (Z_to_bv 64 spa)
             (Z_to_bv 64 b) (Z_to_bv 64 229042) (Z_to_bv 64 35) (Z_to_bv 64 2025576) (Z_to_bv 64 6170748) a5 a6 a7 s2 s3 s4
             (Z_to_bv 64 b) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc e_free m1
      /\ munch [(spa + -16, spa)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo spa)
    (MS (mkR (Z_to_bv 64 0x1ee1b8) (Z_to_bv 64 spa) gp tp u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4
             (Z_to_bv 64 b) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x1ee1b8) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LOS LO SPH MI GF GG.
  unfold entry_st, e_free, e_cfree, G_FREE_IMPL in *.
  pose proof (munch_refl [(spa + -16, spa)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  xs_to 0x1ee868%Z.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8;8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  xs_to 0x1bdf4c%Z.
  release_frame FR ST spa.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption | exact ST].
Qed.

(* [comment removed for export] *)
Lemma fz_wG : forall (usp spa lo FB fl : Z) (gp tp u0 u1 u2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s8 s10 s11 u3 u4 u5 u6 : word) F fc (m : mem)
    (jh0 : list byte) (js : list byte),
  0x7fff7f800000 <= lo <= 2^47 -> lo + 0x1000 <= spa -> spa < 2^63 -> mem_inv bsegs m ->
  FB mod 64 = 0 -> 0xbfd000 <= FB -> FB + 256 <= lo -> (FB + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= FB) ->
  rw_cells bsegs m FB [CB 8 jh0] -> rw_cells bsegs m (shad FB) [CB 32 js] ->
  ro_cells bsegs m (FB + 248) [C8 (Z_to_bv 64 fl)] ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (Z_to_bv 64 0x1ee1cc) (Z_to_bv 64 spa) gp tp u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 fl) a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 FB) s3 s4 s5 (Z_to_bv 64 (shad FB)) (Z_to_bv 64 FB) s8 (Z_to_bv 64 (-8)) s10 s11 u3 u4 u5 u6)
              F (Z_to_bv 64 0x1ee290) fc None m1 (seg_rom bsegs)
      /\ munch [(FB, FB + 8); (shad FB, shad FB + 32)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1)
    (MS (mkR (Z_to_bv 64 0x1ee1cc) (Z_to_bv 64 spa) gp tp u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 FB) s3 s4 s5 (Z_to_bv 64 (shad FB)) (Z_to_bv 64 FB) s8 (Z_to_bv 64 (-8)) s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x1ee1cc) fc None m (seg_rom bsegs)).
Proof.
  intros until js. intros LOS LO SPH MI F64 FLO FHI FBAND HDR CSH LW.
  unfold shad, SHB in *.
  assert (EF : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; lia).
  assert (SEPH : FB + 256 <= FB / 8 + 2147450880 \/ FB / 8 + 2147450880 + 32 <= FB) by (Z.div_mod_to_equations; lia).
  assert (SEPI : 0xbfd000 <= FB / 8 + 2147450880) by (Z.div_mod_to_equations; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (FB / 8 + 2147450880)) = FB / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(FB, FB + 8); (FB / 8 + 2147450880, FB / 8 + 2147450880 + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat) in CSH; [| reflexivity].
  cbn [mk_CB_cells app] in CSH.
  xs_to 0x1ee290%Z.
  apply evt_done. eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM | assumption].
Qed.

(* [comment removed for export] *)
Lemma fz_wH : forall (usp spa lo fl : Z) (gp tp u0 u1 u2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 : word) F fc (m : mem)
    (fv : byte) (c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word),
  0x7fff7f800000 <= lo <= 2^47 -> lo + 0x1000 <= usp + -112 -> usp < 2^63 -> mem_inv bsegs m ->
  0 < fl -> fl + 1 <= lo ->
  rw_cells bsegs m fl [C1 fv] ->
  rw_cells bsegs m (usp + -88) [C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra] ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR cra (Z_to_bv 64 usp) gp tp u0 u1 u2 c0 c1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 c9 s10 s11 u3 u4 u5 u6)
              F (ret_pc cra) fc None m1 (seg_rom bsegs)
      /\ munch [(fl, fl + 1)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 fl [C1 (Z_to_bv 8 0)])
    (MS (mkR (Z_to_bv 64 0x1ee1cc) (Z_to_bv 64 spa) gp tp u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 spa) (Z_to_bv 64 fl) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x1ee290) fc None m (seg_rom bsegs)).
Proof.
  intros until cra. intros LOS LO SPH MI Hfl FLLO FL FR.
  assert (EFL : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  xs. xs. xs. xs.
  do 11 xs. xs. xs.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption | exact FL].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma a2_w0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  evt bsegs (fun ms =>
      ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x4314f4) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4314f0) fc None m (seg_rom bsegs)).
Proof. intros. xs. apply evt_done. reflexivity. Qed.
