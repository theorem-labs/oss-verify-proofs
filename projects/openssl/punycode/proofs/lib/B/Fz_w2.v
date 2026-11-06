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
Definition fz_sh1 : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15));
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14));
   C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))].
(* [comment removed for export] *)
Definition cm_frame (j : list byte) (s3 s2 s1 s0 ra : word) : list cell := [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition fz_WB (spa FB : Z) : list (Z * Z) :=
  [(spa + -48, spa + 8); (FB, FB + 24); (FB + 128, FB + 132); (shad FB, shad FB + 24); (G_LATCH, G_LATCH + 1)].

(* [comment removed for export] *)
Lemma fz_wB : forall (usp spa lo n d FB : Z) (gp tp u0 u1 u2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s9 s10 s11 u3 u4 u5 u6 : word)
    F fc (m : mem) (j0 : list byte) (jh : list byte) (jl : list byte) (jsh : list byte) (lv : byte),
  stk bsegs m lo spa -> lo + 0x1000 <= spa -> 0x7fff7f800000 <= lo -> usp < 2^63 -> spa mod 32 = 0 -> usp - 112 <= spa <= usp - 96 ->
  mem_inv bsegs m ->
  0 <= n < 2^26 ->
  FB mod 64 = 0 -> 0xbfd000 <= FB -> FB + 256 <= lo -> (FB + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= FB) ->
  rw_cells bsegs m spa [CB 8 j0] ->
  rw_cells bsegs m FB [CB 24 jh] -> rw_cells bsegs m (FB + 128) [CB 4 jl] ->
  rw_cells bsegs m (shad FB) [CB 24 jsh] ->
  ro_cells bsegs m G_MALLOC_IMPL [C8 (Z_to_bv 64 e_cmalloc)] -> ro_cells bsegs m 0x5e2558 [C8 (Z_to_bv 64 e_cmalloc)] ->
  rw_cells bsegs m G_LATCH [C1 lv] ->
  evt bsegs (fun ms => exists (m1 : mem) (a1' : word) (jf : list byte) (lv' : byte),
      ms = entry_st (Z_to_bv 64 0x1ee3bc) (Z_to_bv 64 (spa + -48)) gp tp u0 u1 u2 (Z_to_bv 64 spa) (Z_to_bv 64 29)
             (Z_to_bv 64 (n + 1)) a1' (Z_to_bv 64 6169452) (Z_to_bv 64 2024260) (Z_to_bv 64 (-14)) (Z_to_bv 64 (-13)) a6 a7
             (Z_to_bv 64 229042) (Z_to_bv 64 (n + 1)) (Z_to_bv 64 d) s5 (Z_to_bv 64 (shad FB)) (Z_to_bv 64 FB) (Z_to_bv 64 SHB)
             (Z_to_bv 64 (-8)) s10 s11 u3 u4 u5 u6 F fc e_malloc m1
      /\ munch (fz_WB spa FB) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (spa + -48)
      /\ rw_cells bsegs m1 (spa + -48) (cm_frame jf (Z_to_bv 64 n) (Z_to_bv 64 FB) (Z_to_bv 64 spa) (Z_to_bv 64 usp) (Z_to_bv 64 0x1ee154))
      /\ rw_cells bsegs m1 spa [C8 (Z_to_bv 64 FB)]
      /\ rw_cells bsegs m1 FB [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1f688); C8 (Z_to_bv 64 e_fz)]
      /\ rw_cells bsegs m1 (FB + 128) [C4 (Z_to_bv 64 16)]
      /\ rw_cells bsegs m1 (shad FB) fz_sh1
      /\ rw_cells bsegs m1 G_LATCH [C1 lv'] /\ bv_unsigned lv' <> 0)
    (MS (mkR (Z_to_bv 64 0x1ee05c) (Z_to_bv 64 spa) gp tp u0 u1 u2 (Z_to_bv 64 usp) (Z_to_bv 64 spa)
          (Z_to_bv 64 FB) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) (Z_to_bv 64 d) s5 s6 s7 (Z_to_bv 64 SHB) s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x1ee05c) fc None m (seg_rom bsegs)).
Proof.
  intros until lv. intros ST LO LOS SPH S32 SPA MI Hn F64 FLO FHI FBAND C0 CH CL CSH GM GG LT.
  unfold entry_st, e_malloc, e_fz, e_cmalloc, G_MALLOC_IMPL, G_LATCH, fz_sh1, cm_frame, fz_WB in *.
  unfold shad, SHB in *.
  pose proof ST as (STa & STb & _).
  assert (EF : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; lia).
  assert (E3 : FB ≫ 3 = FB / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SEPH : FB + 256 <= FB / 8 + 2147450880 \/ FB / 8 + 2147450880 + 32 <= FB) by (Z.div_mod_to_equations; lia).
  assert (SEPS2 : FB / 8 + 2147450880 + 32 <= lo) by (Z.div_mod_to_equations; lia).
  assert (SEPI : 0xbfd000 <= FB / 8 + 2147450880) by (Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(spa + -48, spa + 8); (FB, FB + 24); (FB + 128, FB + 132); (FB / 8 + 2147450880, FB / 8 + 2147450880 + 24); (12411136, 12411136 + 1)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 8]%nat) in CH; [| reflexivity].
  apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat) in CSH; [| reflexivity].
  cbn [mk_CB_cells app] in CH, CSH.
  xs. xs. xs. xs. xs. xs. xs. xs. xs. rewrite E3.
  xs_to 0x1ee344%Z.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  xs_to 0x1ee3a8%Z. xs.
  assert (LVR : 0 <= bv_unsigned lv < 256) by (pose proof (bv_unsigned_in_range 8 lv) as R; unfold bv_modulus in R; cbn in R; lia).
  destruct (Z.eq_dec (bv_unsigned lv) 0) as [LZ|LNZ].
  - rewrite LZ. if_false. xs_to 0x1bdf50%Z.
    apply evt_done. do 4 eexists. split; [reflexivity|].
    split; [unfold G_LATCH; replace (FB / 8 + 2147450904) with (FB / 8 + 2147450880 + 24) by lia; exact MU|].
    split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split; [exact FR|]. split; [exact C0|]. split; [exact CH|]. split; [exact CL|]. split; [exact CSH|]. split; [exact LT|].
    intros E; vm_compute in E; discriminate E.
  - R_cache_defs.ifT. xs_to 0x1bdf50%Z.
    apply evt_done. do 4 eexists. split; [reflexivity|].
    split; [unfold G_LATCH; replace (FB / 8 + 2147450904) with (FB / 8 + 2147450880 + 24) by lia; exact MU|].
    split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split; [exact FR|]. split; [exact C0|]. split; [exact CH|]. split; [exact CL|]. split; [exact CSH|]. split; [exact LT| exact LNZ].
Qed.
