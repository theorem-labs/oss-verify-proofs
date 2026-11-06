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
From OSSVerify.Proofs.openssl.punycode.lib.A Require Import Layout Shadow R_small R_m2s I_consts RT_iface D_defs D_kit D_libiface X_atexit Fz_defs Fz_tac Fz_w2 Fz_w3.
From OSSVerify.Proofs.openssl.punycode.lib.A Require R_cache_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition a2u_frame2 (jl : list byte) (FB6 : Z) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 (Z_to_bv 64 0); CB 104 jl; C8 (Z_to_bv 64 FB6); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1;
   C8 s0; C8 ra].

Lemma a2_wA : forall (spa lo n d b FB FB6 : Z) (gp tp u0 u1 u2 a1 a2 a3 a4 a5 a6 a7 s10 s11 u3 u4 u5 u6 : word) F fc (m : mem)
    (jl jh js : list byte) (f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra : word),
  0x7fff7f800000 <= lo -> lo + 0x1000 <= spa -> spa < 2^63 -> mem_inv asegs m ->
  FB6 mod 64 = 0 -> 0xbca000 <= FB6 -> FB6 + 4096 <= lo -> (FB6 + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= FB6) ->
  rw_cells asegs m (spa + -224) (a2u_frame jl f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra) ->
  rw_cells asegs m FB6 [CB 24 jh] -> rw_cells asegs m (shad FB6) [CB 4 js] ->
  ro_cells asegs m 0x5a9c70 [C8 (Z_to_bv 64 e_a2u)] ->
  evt asegs (fun ms => exists (m1 : mem) (jl' : list byte),
      ms = entry_st (Z_to_bv 64 0x4080d0) (Z_to_bv 64 (spa + -224)) gp tp u0 u1 u2 (Z_to_bv 64 spa) (Z_to_bv 64 (spa + -224))
             (Z_to_bv 64 (shad FB6 + 4)) (Z_to_bv 64 256) (Z_to_bv 64 4227012) a3 a4 a5 a6 a7 (Z_to_bv 64 SHB) (Z_to_bv 64 (shad FB6))
             (Z_to_bv 64 FB6) (Z_to_bv 64 b) (Z_to_bv 64 16) (Z_to_bv 64 (FB + 144)) (Z_to_bv 64 SHB) (Z_to_bv 64 b) (Z_to_bv 64 FB6)
             (Z_to_bv 64 (shad FB6 + 4)) u3 u4 u5 u6 F fc (e_set_shadow 0xf8) m1
      /\ munch [(spa + -224 + 112, spa + -224 + 120); (FB6, FB6 + 24); (shad FB6, shad FB6 + 4)] m m1 /\ wmono asegs m m1
      /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (spa + -224) (a2u_frame2 jl' FB6 f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 f0 fra)
      /\ rw_cells asegs m1 FB6 [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x16b3c); C8 (Z_to_bv 64 e_a2u)]
      /\ rw_cells asegs m1 (shad FB6) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15))])
    (MS (mkR (Z_to_bv 64 0x408044) (Z_to_bv 64 (spa + -224)) gp tp u0 u1 u2 (Z_to_bv 64 spa) (Z_to_bv 64 (spa + -224))
             (Z_to_bv 64 FB6) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 SHB) (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 b) (Z_to_bv 64 16)
             (Z_to_bv 64 (FB + 144)) (Z_to_bv 64 SHB) (Z_to_bv 64 b) s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x408044) fc None m (seg_rom asegs)).
Proof.
  intros until fra. intros LOS LO SPH MI F64 FLO FHI FBAND FR CH CSH GG.
  unfold entry_st, e_set_shadow, a2u_frame, a2u_frame2, e_a2u in *. unfold shad, SHB in *.
  assert (EF : bv_unsigned (Z_to_bv 64 FB6) = FB6) by (apply unsigned_lit; lia).
  assert (E3 : FB6 ≫ 3 = FB6 / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SEPH : FB6 + 4096 <= FB6 / 8 + 2147450880 \/ FB6 / 8 + 2147450880 + 512 <= FB6) by (Z.div_mod_to_equations; lia).
  assert (SEPS2 : FB6 / 8 + 2147450880 + 512 <= lo) by (Z.div_mod_to_equations; lia).
  assert (SEPI : 0xbca000 <= FB6 / 8 + 2147450880) by (Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(spa + -224 + 112, spa + -224 + 120); (FB6, FB6 + 24); (FB6 / 8 + 2147450880, FB6 / 8 + 2147450880 + 4)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  apply (rw_cells_split_CB asegs _ _ [C8 (Z_to_bv 64 0)] 112 _ _ [104; 8]%nat) in FR; [| reflexivity].
  apply (rw_cells_split_CB asegs _ _ [] 24 _ [] [8; 8; 8]%nat) in CH; [| reflexivity].
  apply (rw_cells_split_CB asegs _ _ [] 4 _ [] [1; 1; 1; 1]%nat) in CSH; [| reflexivity].
  cbn [mk_CB_cells app] in FR, CH, CSH.
  xs. xs. xs. xs. xs. xs. xs. xs. xs. rewrite E3.
  xs_to 0x1c5398%Z.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|].
  split; [exact WM|]. split; [assumption|]. split; [exact FR|]. split; [exact CH | exact CSH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition a2_sh2 (pk : byte) : list cell :=
  repeat (C1 (Z_to_bv 8 (-14))) 16 ++ repeat (C1 pk) 7 ++ repeat (C1 (Z_to_bv 8 (-14))) 5
  ++ [C1 (Z_to_bv 8 (-8)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-8))] ++ repeat (C1 (Z_to_bv 8 (-13))) 5.

Lemma a2_wB : forall (spa lo FB6 : Z) (gp tp u0 u1 u2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 u3 u4 u5 u6 : word) F fc (m : mem)
    (js : list byte),
  0x7fff7f800000 <= lo <= 2^47 -> mem_inv asegs m ->
  FB6 mod 64 = 0 -> 0xbca000 <= FB6 -> FB6 + 4096 <= lo -> (FB6 + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= FB6) ->
  rw_cells asegs m (shad FB6 + 260) [CB 36 js] ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0x40817c) (Z_to_bv 64 (spa + -224)) gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 (shad FB6 + 4)) (Z_to_bv 64 256)
             (Z_to_bv 64 (-8)) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (shad FB6)) s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 (shad FB6 + 4)) u3 u4 u5 u6
             F fc (e_set_shadow 0) m1
      /\ munch [(shad FB6 + 260, shad FB6 + 296)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (shad FB6 + 260) (a2_sh2 (Z_to_bv 8 (-8))))
    (MS (mkR (Z_to_bv 64 0x4080d0) (Z_to_bv 64 (spa + -224)) gp tp u0 u1 u2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (shad FB6))
             s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 (shad FB6 + 4)) u3 u4 u5 u6)
        F (Z_to_bv 64 0x4080d0) fc None m (seg_rom asegs)).
Proof.
  intros until js. intros LOS MI F64 FLO FHI FBAND CSH.
  unfold entry_st, e_set_shadow, a2_sh2 in *. cbn [repeat app]. unfold shad, SHB in *.
  pose proof (munch_refl [(FB6 / 8 + 2147450880 + 260, FB6 / 8 + 2147450880 + 296)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (SEPI : 0xbca000 <= FB6 / 8 + 2147450880) by (Z.div_mod_to_equations; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (FB6 / 8 + 2147450880)) = FB6 / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  apply (rw_cells_split_CB asegs _ _ [] 36 _ [] [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat) in CSH; [| reflexivity].
  cbn [mk_CB_cells app] in CSH.
  replace (FB6 / 8 + 2147450880 + 260) with (FB6 / 8 + 2147451140) in CSH by lia.
  replace (FB6 / 8 + 2147450880 + 260) with (FB6 / 8 + 2147451140) in MU by lia.
  xs_to 0x1c5278%Z.
  apply evt_done. eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|].
  split; [exact WM|]. split; [assumption|].
  replace (FB6 / 8 + 2147450880 + 260) with (FB6 / 8 + 2147451140) by lia. exact CSH.
Qed.
(* [comment removed for export] *)
Lemma land254_even : forall x, bv_unsigned (Z_to_bv 8 (Z.land x 254)) mod 2 = 0.
Proof.
  intros x. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8).
  rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. change (Z.land 254 (Z.ones 8)) with 254.
  rewrite <- (Z.land_ones _ 1) by lia. rewrite <- Z.land_assoc. change (Z.land 254 (Z.ones 1)) with 0. apply Z.land_0_r.
Qed.

(* [comment removed for export] *)
Definition pkt_cells0 (out : Z) (j2 j3 j5 j7 : list byte) (eb : byte) : list cell :=
  [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 out); CB 8 j2; CB 8 j3; C8 (Z_to_bv 64 16); CB 8 j5; C1 eb; CB 7 j7].

Lemma a2_wC : forall (spa lo FB FB6 b : Z) (gp tp u0 u1 u2 a0 a1 a2 a3 a4 a5 a6 a7 u3 u4 u5 u6 : word) F fc (m : mem) (jp : list byte),
  stk asegs m lo (spa + -224) -> 0x7fff7f800000 <= lo <= 2^47 -> lo + 0x1000 <= spa + -224 -> spa < 2^63 ->
  client_consts m -> mem_inv asegs m ->
  FB6 mod 64 = 0 -> 0xbca000 <= FB6 -> FB6 + 4096 <= lo -> (FB6 + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= FB6) ->
  0 < FB -> FB + 256 < 2^63 ->
  rw_cells asegs m (shad FB6 + 260) (a2_sh2 (Z_to_bv 8 (-8))) ->
  rw_cells asegs m (FB6 + 2208) [CB 56 jp] ->
  evt asegs (fun ms => exists (m1 : mem) (a2' a6' : word) (j2 j3 j5 j7 : list byte) (eb : byte),
      ms = MS (mkR (Z_to_bv 64 0x4081c0) (Z_to_bv 64 (spa + -224)) gp tp u0 u1 u2 (Z_to_bv 64 spa) (Z_to_bv 64 (spa + -224))
                 (Z_to_bv 64 (FB6 + 2208)) (Z_to_bv 64 0) a2' (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 SHB) a6' a7 (Z_to_bv 64 SHB)
                 (Z_to_bv 64 (shad FB6)) (Z_to_bv 64 FB6) (Z_to_bv 64 (FB6 + 2208)) (Z_to_bv 64 16) (Z_to_bv 64 (FB + 144))
                 (Z_to_bv 64 (-1)) (Z_to_bv 64 b) (Z_to_bv 64 FB6) (Z_to_bv 64 (shad FB6 + 4)) u3 u4 u5 u6)
              F (Z_to_bv 64 0x26d794) fc None m1 (seg_rom asegs)
      /\ munch [(spa + -240, spa + -224); (shad FB6 + 276, shad FB6 + 283); (FB6 + 2208, FB6 + 2264)] m m1 /\ wmono asegs m m1
      /\ mem_inv asegs m1 /\ stk asegs m1 lo (spa + -224)
      /\ rw_cells asegs m1 (shad FB6 + 260) (a2_sh2 (Z_to_bv 8 0))
      /\ rw_cells asegs m1 (FB6 + 2208) (pkt_cells0 (FB + 144) j2 j3 j5 j7 eb) /\ bv_unsigned eb mod 2 = 0)
    (MS (mkR (Z_to_bv 64 0x40817c) (Z_to_bv 64 (spa + -224)) gp tp u0 u1 u2 (Z_to_bv 64 spa) (Z_to_bv 64 (spa + -224))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 SHB) (Z_to_bv 64 (shad FB6)) (Z_to_bv 64 FB6) (Z_to_bv 64 b) (Z_to_bv 64 16)
             (Z_to_bv 64 (FB + 144)) (Z_to_bv 64 SHB) (Z_to_bv 64 b) (Z_to_bv 64 FB6) (Z_to_bv 64 (shad FB6 + 4)) u3 u4 u5 u6)
        F (Z_to_bv 64 0x40817c) fc None m (seg_rom asegs)).
Proof.
  intros until jp. intros ST LOS LO SPH CC MI F64 FLO FHI FBAND HF0 HF1 CSH CP.
  destruct CC as (G1 & G2 & G3 & G4).
  unfold pkt_cells0, a2_sh2, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  cbn [repeat app] in *. unfold shad, SHB in *.
  assert (EF : bv_unsigned (Z_to_bv 64 FB6) = FB6) by (apply unsigned_lit; lia).
  assert (SEPH : FB6 + 4096 <= FB6 / 8 + 2147450880 \/ FB6 / 8 + 2147450880 + 512 <= FB6) by (Z.div_mod_to_equations; lia).
  assert (SEPS2 : FB6 / 8 + 2147450880 + 512 <= lo) by (Z.div_mod_to_equations; lia).
  assert (SEPI : 0xbca000 <= FB6 / 8 + 2147450880) by (Z.div_mod_to_equations; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (FB6 / 8 + 2147450880)) = FB6 / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  replace (FB6 / 8 + 2147450880 + 260) with (FB6 / 8 + 2147451140) in CSH by lia.
  apply (rw_cells_split_CB asegs _ _ [] 56 _ [] [8;8;8;8;8;8;1;7]%nat) in CP; [| reflexivity].
  cbn [mk_CB_cells app] in CP.
  assert (E2216 : (FB6 + 2216) ≫ 3 = FB6 / 8 + 277) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  assert (E2208 : (FB6 + 2208) ≫ 3 = FB6 / 8 + 276) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  assert (E2240 : (FB6 + 2240) ≫ 3 = FB6 / 8 + 280) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  assert (E2256 : (FB6 + 2256) ≫ 3 = FB6 / 8 + 282) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(spa + -240, spa + -224); (FB6 / 8 + 2147451140 + 16, FB6 / 8 + 2147451140 + 23); (FB6 + 2208, FB6 + 2264)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  xs_to 0x26d694%Z.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat (tryif at_pc 0x26d794%Z then fail else (xs; repeat match goal with E : (_ ≫ 3 = _) |- _ => rewrite E end)).
  release_frame FR ST (spa + -224).
  apply evt_done. do 8 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|].
  split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [replace (FB6 / 8 + 2147450880 + 260) with (FB6 / 8 + 2147451140) by lia; exact CSH|].
  split; [exact CP | apply land254_even].
Qed.
