(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA Atp_defsA Pj_defsA El_defsA Dmp_hdefsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition dmp_mid0 (usp sp' lo d n : Z) (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := fun ms =>
  exists (m1 : mem) (a1' a2' : word) (j0 jr : list byte),
    ms = entry_st (Z_to_bv 64 DMP_SMRET_A) (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 512)
                  a1' a2' a3 a4 a5 a6 a7
                  s2 (Z_to_bv 64 SHB) s4 (Z_to_bv 64 n) (Z_to_bv 64 d) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc DMP_SM3_A m1
    /\ munch [(sp', usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo sp'
    /\ rw_cells bsegs m1 sp' (dmp_locals0 j0 jr)
    /\ stk bsegs m1 (sp' + 32) (usp - 96)
    /\ rw_cells bsegs m1 (usp - 96) (dmp_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10).

Lemma dmp_walk0_al : forall (usp lo d n : Z) (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 128 -> 0x6d5000 <= lo -> usp < 2^63 -> usp mod 32 = 0 -> client_consts m -> mem_inv bsegs m ->
  evt bsegs (dmp_mid0 usp (usp - 128) lo d n ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
    (entry_st ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO GLO SPH S32 (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold entry_st, e_fuzz, dmp_mid0, dmp_saved, dmp_locals0, DMP_SMRET_A, DMP_SM3_A, TPV_A.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 128, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 128%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 128 _ [] [8; 24; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. do 12 zstep. zstep. zstep.
  rewrite (land_m32 (usp + -128)) by lia.
  replace (32 * ((usp + -128) / 32)) with (usp + -128) by (Z.div_mod_to_equations; lia).
  do 6 zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) =>
    change (c0 :: c1 :: rest) with ([c0; c1] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FRs]. cbn [cells_size csize Nat.add] in FRs.
  apply (rw_cells_forget_C8 bsegs _ _ [] _ _) in FRl. cbn [app] in FRl.
  replace (usp + -128 + Z.of_nat 32) with (usp - 96) in FRs by lia.
  replace (usp + -128) with (usp - 128) in * by lia.
  apply evt_done. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl|].
  split; [| exact FRs].
  replace (usp - 128 + 32) with (usp - 96) by lia. split; [lia|]. split; [lia|]. intros a Ha. lia.
Qed.

Lemma dmp_walk0_un : forall (usp lo d n : Z) (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 144 -> 0x6d5000 <= lo -> usp < 2^63 -> usp mod 32 = 16 -> client_consts m -> mem_inv bsegs m ->
  evt bsegs (dmp_mid0 usp (usp - 144) lo d n ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
    (entry_st ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO GLO SPH S32 (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold entry_st, e_fuzz, dmp_mid0, dmp_saved, dmp_locals0, DMP_SMRET_A, DMP_SM3_A, TPV_A.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 144, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 144%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 144 _ [] [8; 8; 8; 8; 16; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. do 12 zstep. zstep. zstep.
  rewrite (land_m32 (usp + -128)) by lia.
  replace (32 * ((usp + -128) / 32)) with (usp + -144) by (Z.div_mod_to_equations; lia).
  do 6 zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with (([c0] ++ [c1; c2; c3]) ++ [c4] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FR]. apply rw_cells_app in FR. destruct FR as [FRp FRs].
  cbn [cells_size csize Nat.add app] in FRp, FRs.
  pose proof FRl as FRl'. apply rw_cells_app in FRl'. destruct FRl' as [FRa FRb]. cbn [cells_size csize Nat.add app] in FRb.
  destruct (rw_cells_forget bsegs _ _ _ FRb) as [jr FRr]. cbn [cells_size csize Nat.add] in FRr.
  lazymatch type of FRa with rw_cells _ ?mm _ [CB 8 ?ja] =>
    assert (FRL : rw_cells bsegs mm (usp + -144) [CB 8 ja; CB 24 jr])
      by (change [CB 8 ja; CB 24 jr] with ([CB 8 ja] ++ [CB 24 jr]); apply rw_cells_app; split; [exact FRa| cbn [cells_size csize Nat.add]; exact FRr])
  end.
  replace (usp + -144 + Z.of_nat 32 + Z.of_nat 16) with (usp - 96) in FRs by lia.
  pose proof (wr_at_stk _ _ _ (rw_cells_wr_at bsegs _ _ _ 16 FRp ltac:(cbn; lia))) as STp.
  replace (usp + -144 + Z.of_nat 32 + 16) with (usp - 96) in STp by lia.
  replace (usp + -144 + Z.of_nat 32) with (usp - 144 + 32) in STp by lia.
  replace (usp + -144) with (usp - 144) in * by lia.
  apply evt_done. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRL|].
  split; [| exact FRs].
  match goal with |- stk _ _ ?a ?b => replace a with (usp - 144 + 32) by lia; replace b with (usp - 96) by lia end. exact STp.
Qed.

Lemma dmp_prologue : forall (usp lo d n : Z) (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 144 -> 0x6d5000 <= lo -> usp < 2^63 -> usp mod 16 = 0 -> client_consts m -> mem_inv bsegs m ->
  exists sp', usp - 144 <= sp' <= usp - 128 /\ sp' mod 32 = 0 /\
    evt bsegs (dmp_mid0 usp sp' lo d n ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
      (entry_st ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
         t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO GLO SPH S16 CC MI.
  assert (C : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct C as [C|C].
  - exists (usp - 128). split; [lia|]. split; [Z.div_mod_to_equations; lia|]. apply dmp_walk0_al; try assumption; lia.
  - exists (usp - 144). split; [lia|]. split; [Z.div_mod_to_equations; lia|]. apply dmp_walk0_un; assumption.
Qed.

Definition dmp_shadow0 (ls : list (list byte)) : list cell := map (fun l => CB 1 l) ls.

Definition dmp_W1 (sp' f : Z) : list ivl := [(sp', sp' + 8); (f, f + 24); (f + 32, f + 56); (shad f, shad f + 64)].

Lemma dmp_walk1 : forall (usp sp' f lo d n : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2x s4x s7 s8x s9x s10x s11 t3 t4 t5 t6 : word)
    (j0 jr h0 h1 h2 h3 : list byte) (ls : list (list byte))
    (p0 p1 p8 p16 p17 p20 p24 p48 p56 p57 p64 : list byte) F fc (m : mem),
  length ls = 64%nat ->
  0 < f -> f + 512 <= lo -> shad f + 64 <= lo -> 0 <= shad f ->
  (f + 512 <= shad f \/ shad f + 64 <= f) ->
  0x6d5000 <= lo -> lo <= sp' -> sp' + 32 <= usp - 96 -> usp < 2^63 -> 0 <= d < 2^64 -> 0 <= n < 2^64 ->
  rw_cells bsegs m sp' (dmp_locals0 j0 jr) ->
  rw_cells bsegs m f (fz_hdr (CB 8 h0) (CB 8 h1) (CB 8 h2) h3) ->
  rw_cells bsegs m (f + 32) (fz_parser (CB 1 p0) p1 (CB 8 p8) (CB 1 p16) p17 (CB 4 p20) (CB 24 p24) (CB 8 p48) (CB 1 p56) p57 (CB 16 p64)) ->
  rw_cells bsegs m (shad f) (dmp_shadow0 ls) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a3' a5' a6' : word),
      ms = lf_regs10 e_asan_memset (Z_to_bv 64 DMP_MS1RET_A) sp' gp t0 t1 t2 usp (Z_to_bv 64 (f + 56)) (Z_to_bv 64 0) (Z_to_bv 64 24)
             (Z_to_bv 64 12) a3' a5' a6' a7 f (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (f + 56)) s8x s10x s11 t3 t4 t5 t6 F fc m1
      /\ munch (dmp_W1 sp' f) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 sp' (dmp_locals1 f jr)
      /\ rw_cells bsegs m1 f (fz_hdr (C8 (Z_to_bv 64 DMP_MAGIC0)) (C8 (Z_to_bv 64 DMP_HDR_DESC_A)) (C8 (Z_to_bv 64 e_fuzz)) h3)
      /\ rw_cells bsegs m1 (f + 32) (fz_parser (C1 (Z_to_bv 8 0)) p1 (C8 (Z_to_bv 64 0)) (C1 (Z_to_bv 8 0)) p17 (C4 (Z_to_bv 64 12)) (CB 24 p24) (CB 8 p48) (CB 1 p56) p57 (CB 16 p64))
      /\ rw_cells bsegs m1 (shad f) (map C1 dmp_sh_pro))
    (MS (mkR (Z_to_bv 64 DMP_SMRET_A) (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7
             s2x (Z_to_bv 64 SHB) s4x (Z_to_bv 64 n) (Z_to_bv 64 d) s7 s8x s9x s10x s11 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_SMRET_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS F0 FLO SLO SH0 SEP GLO LSP LUSP SPH DR NR FRl FH FP FS MI.
  do 64 (destruct ls as [|? ls]; [discriminate LS|]). destruct ls; [| discriminate LS]. clear LS.
  unfold lf_regs, lf_regs10, e_asan_memset, e_fuzz, dmp_W1, dmp_locals0, dmp_locals1, fz_hdr, fz_parser, dmp_shadow0, dmp_sh_pro, dmp_sh,
    DMP_SMRET_A, DMP_MS1RET_A, DMP_MAGIC0, DMP_MAGIC1, DMP_HDR_DESC_A, TPV_A, shad, SHB in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(sp', sp' + 8); (f, f + 24); (f + 32, f + 56); (f / 8 + 2147450880, f / 8 + 2147450880 + 64)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).

  zstep. zstep. zstep. zstep.
  if_cases K; zify_cond K; [| exfalso; lia].

  ls. zstep. zstep. zstep. zstep. zstep. rewrite shr3_div.

  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  ls. ls. ls.

  zstep. ls. ls. ls. ls. zstep.
  do 60 ls.

  assert (EP : bv_unsigned (Z_to_bv 64 (f + 32)) = f + 32) by (apply unsigned_lit; lia).
  ls. ls. ls. ls. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists _, _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma dmp_walk2 : forall (usp sp' f d n : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8x s10x s11 t3 t4 t5 t6 : word)
    (p1 p17 p24 p48 p56 p57 p64 : list byte) F fc (m : mem),
  0 < f -> f + 512 < 2^63 ->
  rw_cells bsegs m (f + 32) (fz_parser (C1 (Z_to_bv 8 0)) p1 (C8 (Z_to_bv 64 0)) (C1 (Z_to_bv 8 0)) p17 (C4 (Z_to_bv 64 12)) (CB 24 p24) (CB 8 p48) (CB 1 p56) p57 (CB 16 p64)) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = lf_regs10 e_asan_memset (Z_to_bv 64 DMP_MS2RET_A) sp' gp t0 t1 t2 usp (Z_to_bv 64 (f + 96)) (Z_to_bv 64 0) (Z_to_bv 64 16)
             a3 a4 a5 a6 a7 f (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (f + 56)) s8x s10x s11 t3 t4 t5 t6 F fc m1
      /\ munch [(f + 80, f + 89)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (f + 32) (fz_parser (C1 (Z_to_bv 8 0)) p1 (C8 (Z_to_bv 64 0)) (C1 (Z_to_bv 8 0)) p17 (C4 (Z_to_bv 64 12)) (CB 24 p24)
                                              (C8 (Z_to_bv 64 4294967295)) (C1 (Z_to_bv 8 0)) p57 (CB 16 p64)))
    (lf_regs10 DMP_MS1RET_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (f + 56)) s8x s10x s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH FP MI.
  unfold lf_regs10, e_asan_memset, fz_parser, DMP_MS1RET_A, DMP_MS2RET_A, TPV_A in *.
  pose proof (munch_refl [(f + 80, f + 89)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  zstep. zstep.
  ls. ls. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Lemma dmp_walk3 : forall (usp sp' f d n : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8x s10x s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 512 < 2^63 -> 0 <= sp' -> sp' + 32 < 2^63 -> mem_inv bsegs m ->
  evt bsegs (eq (lf_regs10 e_pid (Z_to_bv 64 DMP_PIDRET_A) sp' gp t0 t1 t2 usp (Z_to_bv 64 (sp' + 8)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 56))
                 (Z_to_bv 64 d) (Z_to_bv 64 n) (Z_to_bv 64 1) a6 a7 f (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (f + 56)) s8x s10x s11 t3 t4 t5 t6 F fc m))
    (lf_regs10 DMP_MS2RET_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (Z_to_bv 64 n) (Z_to_bv 64 d) (Z_to_bv 64 (f + 56)) s8x s10x s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH MI. unfold lf_regs10, e_pid, DMP_MS2RET_A, DMP_PIDRET_A, TPV_A.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.
