(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Layout Shadow RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA
     Atp_defsA Pj_defsA El_defsA Dmp_hdefsA Dmp_pj_ifaceA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition DMP_PJ_SMRET_A : Z := 0xaefe8.
Definition DMP_PJ_DISP_A : Z := 0xaf0b8.
Definition DMP_PJ_EXIT_A : Z := 0xaf700.
Definition DMP_PJ_LOOPX_A : Z := 0xaf6a4.
Definition DMP_PJ_CLOSE_A : Z := 0xaf6f4.
Definition DMP_PJ_ALOOP_A : Z := 0xaf618.
Definition DMP_PJ_OLOOP_A : Z := 0xaf890.
Definition DMP_PJ_DESC_A : Z := 0x1c6bd.

Definition pj_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma pj_saved_size : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11, cells_size (pj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) = 104%nat.
Proof. intros. reflexivity. Qed.

Definition pj_locals0 (j0 j1 : list byte) (osp : Z) (j2 j3 : list byte) : list cell := [CB 8 j0; CB 112 j1; C8 (Z_to_bv 64 osp); CB 16 j2; CB 8 j3].

Definition pj_mid0 (q lo osp doc i : Z) (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := fun ms =>
  exists (m1 : mem) (a1' a2' : word) (j0 j1 j2 j3 : list byte),
    ms = entry_st (Z_to_bv 64 DMP_PJ_SMRET_A) (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256)) (Z_to_bv 64 160)
                  a1' a2' a3 a4 a5 a6 a7
                  (Z_to_bv 64 SHB) s3 (Z_to_bv 64 doc) (Z_to_bv 64 i) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_stack_malloc_2 m1
    /\ munch [(q - 256, q)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (q - 256)
    /\ rw_cells asegs m1 (q - 256) (pj_locals0 j0 j1 osp j2 j3)
    /\ rw_cells asegs m1 (q - 104) (pj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

Lemma pj_walk0 : forall (q lo osp doc i : Z) (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo q -> lo <= q - 256 -> 0x6c9000 <= lo -> q < 2^63 -> q mod 32 = 0 -> 0 <= osp < 2^64 -> 0 <= doc < 2^64 -> 0 <= i < 2^64 ->
  client_consts m -> mem_inv asegs m ->
  evt asegs (pj_mid0 q lo osp doc i ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
    (entry_st ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 (Z_to_bv 64 osp) (Z_to_bv 64 doc) (Z_to_bv 64 i) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc DMP_PJ_A m).
Proof.
  intros until m. intros ST LO GLO SPH S32 RO RD RI (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold entry_st, DMP_PJ_A, pj_mid0, pj_saved, pj_locals0, DMP_PJ_SMRET_A, e_stack_malloc_2, TPV_A.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(q - 256, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 256%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 256 _ [] [8; 112; 8; 16; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. do 13 zstep. zstep. zstep.
  rewrite (land_m32 (q + -256)) by lia.
  replace (32 * ((q + -256) / 32)) with (q + -256) by (Z.div_mod_to_equations; lia).
  do 7 zstep. step. rewrite (sx32_small 1) by lia. zstep. ls. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3; c4] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FRs]. cbn [cells_size csize Nat.add] in FRs.
  apply (rw_cells_forget_C8 asegs _ _ [] _ _) in FRl. cbn [app] in FRl.
  replace (q + -256 + Z.of_nat 152) with (q - 104) in FRs by lia.
  replace (q + -256) with (q - 256) in * by lia.
  apply evt_done. do 7 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl| exact FRs].
Qed.

Definition pj_locals1 (j0 j1 : list byte) (osp : Z) (j2 : list byte) (f : Z) : list cell := [CB 8 j0; CB 112 j1; C8 (Z_to_bv 64 osp); CB 16 j2; C8 (Z_to_bv 64 f)].

Definition pj_sh_pro : list byte :=
  repeat (Z_to_bv 8 (-15)) 4 ++ [Z_to_bv 8 (-8); Z_to_bv 8 (-14); Z_to_bv 8 (-8); Z_to_bv 8 (-14); Z_to_bv 8 (-8); Z_to_bv 8 (-14);
                                  Z_to_bv 8 (-8); Z_to_bv 8 (-14); Z_to_bv 8 (-8); Z_to_bv 8 (-14); Z_to_bv 8 (-8); Z_to_bv 8 (-14); Z_to_bv 8 (-8)]
  ++ repeat (Z_to_bv 8 (-13)) 3.
Lemma pj_sh_pro_length : length pj_sh_pro = 20%nat.
Proof. reflexivity. Qed.
Definition pj_shadow0 (ls : list (list byte)) : list cell := map (fun l => CB 1 l) ls.
Definition pj_W1 (q f : Z) : list ivl := [(q - 256 + 144, q - 256 + 152); (f, f + 24); (shad f, shad f + 20)].

Lemma pj_walk1 : forall (q f lo osp doc i : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3x s6 s7x s8 s9 s10x s11 t3 t4 t5 t6 : word)
    (j0 j1 j2 j3 h0 h1 h2 : list byte) (ls : list (list byte)) F fc (m : mem),
  length ls = 20%nat ->
  0 < f -> f + 256 <= lo -> shad f + 32 <= lo -> 0 <= shad f -> (f + 256 <= shad f \/ shad f + 32 <= f) ->
  0x6c9000 <= lo -> lo <= q - 256 -> q < 2^63 -> 0 <= doc < 2^63 -> 0 <= i < 2^64 -> 0 <= osp < 2^64 ->
  (forall m', munch (pj_W1 q f) m m' -> wmono asegs m m' -> shz m' doc 16) ->
  rw_cells asegs m (q - 256) (pj_locals0 j0 j1 osp j2 j3) ->
  rw_cells asegs m f [CB 8 h0; CB 8 h1; CB 8 h2] ->
  rw_cells asegs m (shad f) (pj_shadow0 ls) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a0' a1' a2' a3' a4' : word),
      ms = MS (mkR (Z_to_bv 64 DMP_PJ_SMRET_A) (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256))
                   a0' a1' a2' a3' a4' a5 a6 a7
                   (Z_to_bv 64 SHB) (Z_to_bv 64 f) (Z_to_bv 64 doc) (Z_to_bv 64 i) s6 (Z_to_bv 64 f) s8 s9 (Z_to_bv 64 (shad f)) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 DMP_PJ_DISP_A) fc None m1 (seg_rom asegs)
      /\ munch (pj_W1 q f) m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (q - 256) (pj_locals1 j0 j1 osp j2 f)
      /\ rw_cells asegs m1 f [C8 (Z_to_bv 64 DMP_MAGIC0); C8 (Z_to_bv 64 DMP_PJ_DESC_A); C8 (Z_to_bv 64 DMP_PJ_A)]
      /\ rw_cells asegs m1 (shad f) (map C1 pj_sh_pro))
    (MS (mkR (Z_to_bv 64 DMP_PJ_SMRET_A) (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256)) (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 SHB) s3x (Z_to_bv 64 doc) (Z_to_bv 64 i) s6 s7x s8 s9 s10x s11 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_SMRET_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LS F0 FLO SLO SH0 SEP GLO LSP SPH DR IR OR SHZD FRl FH FS MI.
  do 20 (destruct ls as [|? ls]; [discriminate LS|]). destruct ls; [| discriminate LS]. clear LS.
  unfold pj_W1, pj_locals0, pj_locals1, pj_shadow0, pj_sh_pro, DMP_PJ_SMRET_A, DMP_PJ_DISP_A, DMP_MAGIC0, DMP_PJ_DESC_A, DMP_PJ_A, TPV_A, shad, SHB in *.
  cbn [map app repeat] in *.
  pose proof (munch_refl [(q - 256 + 144, q - 256 + 152); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 20)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 doc) = doc) by (apply unsigned_lit; lia).

  zstep. zstep. zstep. zstep.
  if_cases K; zify_cond K; [| exfalso; lia].

  zstep. zstep. zstep. zstep. rewrite shr3_div.

  zstep. zstep. zstep. zstep. zstep.
  ls. ls. ls.

  zstep. zstep. ls. ls. ls. ls.

  zstep. do 12 ls.

  zstep. rewrite shr3_div. ls. ls. ls. ls. zstep.

  shz_pose SHZD doc. zstep. shz_norm. ls. zstep. if_false.
  apply evt_done. do 6 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Definition DMP_PJ_X2_A : Z := 0xaf794.

Lemma pj_walkX1 : forall (f : Z) (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 : word)
    (h0 : list byte) (ls : list (list byte)) F fc (m : mem),
  length ls = 32%nat -> 0 < f -> f + 256 < 2^63 -> 0 <= shad f -> shad f + 32 < 2^63 -> (f + 256 <= shad f \/ shad f + 32 <= f) ->
  rw_cells asegs m f [CB 8 h0] -> rw_cells asegs m (shad f) (pj_shadow0 ls) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem) (a0' : word),
      ms = MS (mkR ra sp gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 f) s4 s5 s6 (Z_to_bv 64 f) s8 s9 (Z_to_bv 64 (shad f)) s11 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_X2_A) fc None m' (seg_rom asegs)
      /\ munch [(f, f + 8); (shad f, shad f + 32)] m m' /\ wmono asegs m m' /\ mem_inv asegs m')
    (MS (mkR ra sp gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 f) s4 s5 s6 (Z_to_bv 64 f) s8 s9 (Z_to_bv 64 (shad f)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_EXIT_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros L32 F0 FH SH0 SHH SEP FHD FS MI.
  do 32 (destruct ls as [|? ls]; [discriminate L32|]). destruct ls; [| discriminate L32]. clear L32.
  unfold pj_shadow0, DMP_PJ_EXIT_A, DMP_PJ_X2_A, DMP_MAGIC1, TPV_A, shad, SHB in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).

  zstep. zstep. ls. zstep. if_cases K; zify_cond K; [exfalso; lia|]. zstep.

  do 32 ls.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM| eassumption].
Qed.

Lemma pj_walkX2 : forall (q f fl lo : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 : word)
    (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 : word) (LC : list cell) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 < fl -> fl + 1 <= lo ->
  0x6c9000 <= lo -> lo <= q - 256 -> q < 2^63 -> cells_size LC = 152%nat ->
  stk asegs m lo (q - 256) -> rw_cells asegs m (q - 256) LC ->
  rw_cells asegs m (q - 104) (pj_saved xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11) ->
  ro_cells asegs m (f + 248) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem), ret_st xra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 fl) m' ms
      /\ ms_fcsr ms = fc /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q
      /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)])
    (MS (mkR ra (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256)) a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 f) s4 s5 s6 (Z_to_bv 64 f) s8 s9 (Z_to_bv 64 (shad f)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_X2_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros F0 FH FL0 FLLO GLO LSP SPH SZ ST FRl FRs FW FLC MI.
  unfold pj_saved, DMP_PJ_X2_A, TPV_A in *.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EFL : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).

  zstep. ls. zstep.

  replace (q - 104) with (q + -104) in FRs by lia.
  zstep. do 13 zstep. zstep.
  replace (q + -104) with (q - 104) in FRs by lia.
  pose proof (stk_release asegs _ _ _ _ ST FRl ltac:(lia)) as ST1. rewrite SZ in ST1. change (Z.of_nat 152%nat) with 152 in ST1.
  replace (q - 256 + 152) with (q - 104) in ST1 by lia.
  pose proof (stk_release asegs _ _ _ _ ST1 FRs ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
  replace (q - 104 + Z.of_nat 104) with q in ST3 by lia.
  zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST3| eassumption].
Qed.
