(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA Atp_defsA Pj_defsA Pj_hdefsA Imp_hdefsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition imp_locals0 (j0 j8 : list byte) (szw : word) (j120 : list byte) : list cell := [CB 8 j0; CB 112 j8; C8 szw; CB 88 j120].

Definition imp_mid0 (usp sp' lo d n : Z) (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := fun ms =>
  exists (m1 : mem) (a1' a3' : word) (j0 j8 j120 : list byte),
    ms = entry_st (Z_to_bv 64 IMP_SMRET_A) (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 1248)
                  a1' (Z_to_bv 64 1) a3' a4 a5 a6 a7
                  (Z_to_bv 64 SHB) s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc IMP_SM5_A m1
    /\ munch [(sp', usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo sp'
    /\ rw_cells bsegs m1 sp' (imp_locals0 j0 j8 (Z_to_bv 64 d) j120)
    /\ stk bsegs m1 (sp' + 216) (usp - 104)
    /\ rw_cells bsegs m1 (usp - 104) (imp_savedA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

Lemma imp_walk0_al : forall (usp lo d n : Z) (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 320 -> 0x6a9000 <= lo -> usp < 2^63 -> usp mod 32 = 0 -> 0 <= n < 2^64 -> client_consts m -> mem_inv bsegs m ->
  evt bsegs (imp_mid0 usp (usp - 320) lo d n ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
    (entry_st ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO GLO SPH S32 NR (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold entry_st, e_fuzz, imp_mid0, imp_savedA, imp_locals0, IMP_SMRET_A, IMP_SM5_A, TPV_A.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 320, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 320%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 320 _ [] [8; 112; 8; 88; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.

  lstep. do 13 zstep. zstep. zstep.
  rewrite (land_m32 (usp + -320)) by lia.
  replace (32 * ((usp + -320) / 32)) with (usp + -320) by (Z.div_mod_to_equations; lia).
  zstep.

  do 5 zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: rest) with ([c0; c1; c2; c3] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FRs]. cbn [cells_size csize Nat.add] in FRs.
  apply (rw_cells_forget_C8 bsegs _ _ [] _ _) in FRl. cbn [app] in FRl.
  replace (usp + -320 + Z.of_nat 216) with (usp - 104) in FRs by lia.
  replace (usp + -320) with (usp - 320) in * by lia.
  apply evt_done. do 6 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl|].
  split; [| exact FRs].
  replace (usp - 320 + 216) with (usp - 104) by lia. split; [lia|]. split; [lia|]. intros a Ha. lia.
Qed.

Lemma imp_walk0_un : forall (usp lo d n : Z) (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 336 -> 0x6a9000 <= lo -> usp < 2^63 -> usp mod 32 = 16 -> 0 <= n < 2^64 -> client_consts m -> mem_inv bsegs m ->
  evt bsegs (imp_mid0 usp (usp - 336) lo d n ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
    (entry_st ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO GLO SPH S32 NR (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold entry_st, e_fuzz, imp_mid0, imp_savedA, imp_locals0, IMP_SMRET_A, IMP_SM5_A, TPV_A.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 336, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 336%nat ST.

  apply (rw_cells_split_CB bsegs _ _ [] 336 _ [] [8; 8; 8; 96; 8; 88; 16; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. do 13 zstep. zstep. zstep.
  rewrite (land_m32 (usp + -320)) by lia.
  replace (32 * ((usp + -320) / 32)) with (usp + -336) by (Z.div_mod_to_equations; lia).
  zstep.
  do 5 zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: rest) with (([c0] ++ [c1; c2; c3] ++ [c4; c5]) ++ [c6] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FR]. apply rw_cells_app in FR. destruct FR as [FRp FRs].
  cbn [cells_size csize Nat.add app] in FRp, FRs.
  pose proof FRl as FRl'. apply rw_cells_app in FRl'. destruct FRl' as [FRa FRbc]. apply rw_cells_app in FRbc. destruct FRbc as [FRb FRc].
  cbn [cells_size csize Nat.add app] in FRb, FRc.
  destruct (rw_cells_forget bsegs _ _ _ FRb) as [jj8 FRj8]. cbn [cells_size csize Nat.add cells_bytes app] in FRj8.
  lazymatch type of FRa with rw_cells _ ?mm _ [CB 8 ?ja] =>
  lazymatch type of FRc with rw_cells _ _ _ [C8 ?w; CB 88 ?jc] =>
    assert (FRL : rw_cells bsegs mm (usp + -336) [CB 8 ja; CB 112 jj8; C8 w; CB 88 jc])
      by (change [CB 8 ja; CB 112 jj8; C8 w; CB 88 jc] with ([CB 8 ja] ++ [CB 112 jj8] ++ [C8 w; CB 88 jc]);
          apply rw_cells_app; split; [exact FRa|]; apply rw_cells_app; split; [cbn [cells_size csize Nat.add]; exact FRj8| cbn [cells_size csize Nat.add]; exact FRc])
  end end.
  replace (usp + -336 + Z.of_nat 216 + Z.of_nat 16) with (usp - 104) in FRs by lia.
  pose proof (wr_at_stk _ _ _ (rw_cells_wr_at bsegs _ _ _ 16 FRp ltac:(cbn; lia))) as STp.
  replace (usp + -336 + Z.of_nat 216 + 16) with (usp - 104) in STp by lia.
  replace (usp + -336 + Z.of_nat 216) with (usp - 336 + 216) in STp by lia.
  replace (usp + -336) with (usp - 336) in * by lia.
  apply evt_done. do 6 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRL|].
  split; [| exact FRs].
  match goal with |- stk _ _ ?a ?b => replace a with (usp - 336 + 216) by lia; replace b with (usp - 104) by lia end. exact STp.
Qed.

Lemma imp_prologue : forall (usp lo d n : Z) (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 336 -> 0x6a9000 <= lo -> usp < 2^63 -> usp mod 16 = 0 -> 0 <= n < 2^64 -> client_consts m -> mem_inv bsegs m ->
  exists sp', usp - 336 <= sp' <= usp - 320 /\ sp' mod 32 = 0 /\
    evt bsegs (imp_mid0 usp sp' lo d n ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
      (entry_st ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
         t3 t4 t5 t6 F fc e_fuzz m).
Proof.
  intros until m. intros ST LO GLO SPH S16 NR CC MI.
  assert (C : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct C as [C|C].
  - exists (usp - 320). split; [lia|]. split; [Z.div_mod_to_equations; lia|]. apply imp_walk0_al; try assumption; lia.
  - exists (usp - 336). split; [lia|]. split; [Z.div_mod_to_equations; lia|]. apply imp_walk0_un; assumption.
Qed.

Definition IMP_SSF8RET_A : Z := 0xb4db8.

Definition imp_locals1 (j0 j8 : list byte) (f : Z) (j48 : list byte) (szw : word) (j128 j152 j192 : list byte) : list cell :=
  [CB 8 j0; CB 32 j8; C8 (Z_to_bv 64 f); CB 72 j48; C8 szw; CB 16 j128; C8 (Z_to_bv 64 SHB); CB 32 j152; C8 (Z_to_bv 64 f); CB 24 j192].

Definition imp_sh20 : list byte := firstn 20 imp_sh_pro.

Definition imp_W1 (sp' f : Z) : list ivl := [(sp' + 40, sp' + 48); (sp' + 144, sp' + 152); (sp' + 184, sp' + 192); (f, f + 24); (shad f, shad f + 20)].

Lemma imp_walk1 : forall (usp sp' f lo d n : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3x s4x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6 : word)
    (j0 j8 j120 h0 h1 h2 h3 jsh : list byte) F fc (m : mem),
  0 < f -> f + 2048 <= lo -> shad f + 156 <= lo -> 0 <= shad f ->
  (f + 2048 <= shad f \/ shad f + 156 <= f) ->
  0x6a9000 <= lo -> lo <= sp' -> sp' + 216 <= usp - 104 -> usp < 2^63 -> 0 <= d < 2^64 -> 0 <= n < 2^64 ->
  rw_cells bsegs m sp' (imp_locals0 j0 j8 (Z_to_bv 64 d) j120) ->
  rw_cells bsegs m f (fz_hdr (CB 8 h0) (CB 8 h1) (CB 8 h2) h3) ->
  rw_cells bsegs m (shad f) [CB 156 jsh] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (j8a j48 j128 j152 j192 jsh20 : list byte),
      ms = MS (mkR (Z_to_bv 64 IMP_SSF8RET_A) (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
                   (Z_to_bv 64 (shad f + 20)) (Z_to_bv 64 68) (Z_to_bv 64 e_fuzz) (Z_to_bv 64 (-15)) a4 a5 a6 a7
                   (Z_to_bv 64 (-8)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 (-14)) (Z_to_bv 64 n) (Z_to_bv 64 f) (Z_to_bv 64 (shad f + 20)) s8x s9x s10x s11x t3 t4 t5 t6)
              F (Z_to_bv 64 (e_set_shadow 0xf8)) fc None m1 (seg_rom bsegs)
      /\ munch (imp_W1 sp' f) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 sp' (imp_locals1 j0 j8a f j48 (Z_to_bv 64 d) j128 j152 j192)
      /\ rw_cells bsegs m1 f (fz_hdr (C8 (Z_to_bv 64 IMP_MAGIC0)) (C8 (Z_to_bv 64 IMP_HDR_DESC_A)) (C8 (Z_to_bv 64 e_fuzz)) h3)
      /\ rw_cells bsegs m1 (shad f) (map C1 imp_sh20 ++ [CB 136 jsh20]))
    (MS (mkR (Z_to_bv 64 IMP_SMRET_A) (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 SHB) s3x s4x (Z_to_bv 64 n) s6x s7x s8x s9x s10x s11x t3 t4 t5 t6)
        F (Z_to_bv 64 IMP_SMRET_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FLO SLO SH0 SEP GLO LSP LUSP SPH DR NR FRl FH FS MI.
  unfold e_fuzz, imp_W1, imp_locals0, imp_locals1, fz_hdr, imp_sh20, imp_sh_pro, imp_sh, IMP_SMRET_A, IMP_SSF8RET_A, IMP_MAGIC0, IMP_HDR_DESC_A, TPV_A, shad, SHB in *.
  cbn [map app repeat firstn e_set_shadow] in *.

  apply (rw_cells_split_CB bsegs _ _ [CB 8 j0] 112 j8 [C8 (Z_to_bv 64 d); CB 88 j120] [32; 8; 72]%nat) in FRl; [| reflexivity]. cbn [mk_CB_cells app] in FRl.
  apply (rw_cells_split_CB bsegs _ _ [CB 8 j0; CB 32 (firstn 32 j8); CB 8 (firstn 8 (skipn 32 j8)); CB 72 (firstn 72 (skipn 8 (skipn 32 j8))); C8 (Z_to_bv 64 d)] 88 j120 [] [16; 8; 32; 8; 24]%nat) in FRl;
    [| reflexivity]. cbn [mk_CB_cells app] in FRl.
  repeat match type of FRl with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "j" in set (j := t) in FRl; clearbody j end.

  apply (rw_cells_split_CB bsegs _ _ [] 156 jsh [] [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;136]%nat) in FS; [| reflexivity]. cbn [mk_CB_cells app] in FS.
  repeat match type of FS with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "j" in set (j := t) in FS; clearbody j end.
  pose proof (munch_refl [(sp' + 40, sp' + 48); (sp' + 144, sp' + 152); (sp' + 184, sp' + 192); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 20)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).

  zstep. ls. zstep. ls. zstep.
  if_cases K; zify_cond K; [| exfalso; lia].
  ls.

  zstep. zstep. zstep. zstep. rewrite shr3_div. zstep. zstep. zstep. zstep. zstep.
  ls. ls. ls.

  zstep. zstep. zstep.
  do 20 ls.
  zstep. zstep. zstep. zstep.
  apply evt_done. eexists _, _, _, _, _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Definition IMP_GTEST_A : Z := 0xb4edc.
Definition imp_sh88 : list byte := skipn 88 imp_sh_pro.

Definition imp_locals2 (j0 j8 : list byte) (f : Z) (j48 : list byte) (szw : word) (j128 j152 j192 : list byte) : list cell :=
  [CB 8 j0; CB 24 j8; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 72 j48; C8 szw; CB 16 j128; C8 (Z_to_bv 64 SHB); CB 32 j152; C8 (Z_to_bv 64 f); CB 24 j192].

Definition imp_W2 (sp' f : Z) : list ivl := [(sp' + 32, sp' + 40); (shad f + 88, shad f + 156)].

Lemma imp_walk2 : forall (usp sp' f lo d n g : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8x s9x s10x s11x t3 t4 t5 t6 : word)
    (j0 j8 j48 j128 j152 j192 jsh88 : list byte) F fc (m : mem),
  0 < f -> f + 2048 <= lo -> shad f + 156 <= lo -> 0 <= shad f ->
  (f + 2048 <= shad f \/ shad f + 156 <= f) ->
  0x6a9000 <= lo -> lo <= sp' -> sp' + 216 <= usp - 104 -> usp < 2^63 -> 0 <= d < 2^64 -> 0 <= n < 2^64 -> 0 <= g <= 1 ->
  rw_cells bsegs m sp' (imp_locals1 j0 j8 f j48 (Z_to_bv 64 d) j128 j152 j192) ->
  rw_cells bsegs m (shad f + 88) [CB 68 jsh88] ->
  ro_cells bsegs m IMP_GUARD_A [C1 (Z_to_bv 8 g)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (j8a : list byte),
      ms = MS (mkR x1 (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
                   (sxb (Z_to_bv 8 g)) a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 (-8)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 (-14)) (Z_to_bv 64 n) (Z_to_bv 64 f) (Z_to_bv 64 (shad f + 20)) s8x s9x s10x s11x t3 t4 t5 t6)
              F (Z_to_bv 64 IMP_GTEST_A) fc None m1 (seg_rom bsegs)
      /\ munch (imp_W2 sp' f) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 sp' (imp_locals2 j0 j8a f j48 (Z_to_bv 64 d) j128 j152 j192)
      /\ rw_cells bsegs m1 (shad f + 88) (map C1 imp_sh88))
    (MS (mkR x1 (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (-8)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 (-14)) (Z_to_bv 64 n) (Z_to_bv 64 f) (Z_to_bv 64 (shad f + 20)) s8x s9x s10x s11x t3 t4 t5 t6)
        F (Z_to_bv 64 IMP_SSF8RET_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FLO SLO SH0 SEP GLO LSP LUSP SPH DR NR GR FRl FS GB MI.
  unfold imp_W2, imp_locals1, imp_locals2, imp_sh88, imp_sh_pro, imp_sh, IMP_SSF8RET_A, IMP_GTEST_A, IMP_GUARD_A, TPV_A, shad, SHB in *.
  cbn [map app repeat skipn] in *.

  apply (rw_cells_split_CB bsegs _ _ [CB 8 j0] 32 j8 _ [24; 8]%nat) in FRl; [| reflexivity]. cbn [mk_CB_cells app] in FRl.
  repeat match type of FRl with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "j" in set (j := t) in FRl; clearbody j end.

  apply (rw_cells_split_CB bsegs _ _ [] 68 jsh88 [] (repeat 1%nat 68)) in FS; [| reflexivity]. cbn [mk_CB_cells app repeat] in FS.
  repeat match type of FS with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "j" in set (j := t) in FS; clearbody j end.
  pose proof (munch_refl [(sp' + 32, sp' + 40); (f / 8 + 2147450880 + 88, f / 8 + 2147450880 + 156)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  replace (f / 8 + 2147450880 + 88) with (f / 8 + 2147450968) in FS by lia.

  do 56 ls. zstep. do 12 ls.

  zstep. zstep. zstep. ls.
  apply evt_done. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. eassumption.
Qed.

Definition IMP_SS00RET_A : Z := 0xb4f34.

Definition imp_locals3 (j0 j8 : list byte) (f : Z) (szw : word) (j64 j112 : list byte) (dw : word) (j128 j152 j192 : list byte) : list cell :=
  [CB 8 j0; CB 16 j8; C8 (Z_to_bv 64 (shad f + 20)); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); C8 szw; C8 (Z_to_bv 64 1); CB 32 j64; C8 (Z_to_bv 64 (f + 1168));
   C8 (Z_to_bv 64 (f + 32)); CB 8 j112; C8 dw; CB 8 j128; C8 (Z_to_bv 64 (f + 832)); C8 (Z_to_bv 64 SHB); CB 32 j152; C8 (Z_to_bv 64 f); CB 24 j192].

Definition imp_W3 (sp' : Z) : list ivl := [(sp' + 24, sp' + 32); (sp' + 48, sp' + 64); (sp' + 96, sp' + 112); (sp' + 136, sp' + 144)].

Lemma imp_walk3 : forall (usp sp' f lo d n A8 : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4x s8x s9x s10x s11x t3 t4 t5 t6 : word)
    (j0 j8 j48 j128 j152 j192 : list byte) F fc (m : mem),
  0 < f -> f + 2048 <= lo -> shad f + 156 <= lo -> 0 <= shad f ->
  0x6a9000 <= lo -> lo <= sp' -> sp' + 216 <= usp - 104 -> usp < 2^63 -> 0 <= d < 2^64 -> 0 <= n < 2^64 -> 0 < A8 -> A8 + 8 < 2^63 ->
  rw_cells bsegs m sp' (imp_locals2 j0 j8 f j48 (Z_to_bv 64 d) j128 j152 j192) ->
  ro_cells bsegs m IMP_VEC_OBJ_A [C8 (Z_to_bv 64 A8); C8 (Z_to_bv 64 (A8 + 8)); C8 (Z_to_bv 64 (A8 + 8))] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (j8a j64 j112 j128a : list byte),
      ms = MS (mkR (Z_to_bv 64 IMP_SS00RET_A) (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
                   (Z_to_bv 64 (shad f + 20)) (Z_to_bv 64 68) a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 (-8)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 A8) (Z_to_bv 64 (A8 + 8)) (Z_to_bv 64 f) (Z_to_bv 64 (shad f + 20)) s8x s9x s10x
                   (Z_to_bv 64 (f + 160)) t3 t4 t5 t6)
              F (Z_to_bv 64 (e_set_shadow 0)) fc None m1 (seg_rom bsegs)
      /\ munch (imp_W3 sp') m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 sp' (imp_locals3 j0 j8a f (Z_to_bv 64 n) j64 j112 (Z_to_bv 64 d) j128a j152 j192))
    (MS (mkR x1 (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (-8)) (Z_to_bv 64 (shad f)) s4x (Z_to_bv 64 n) (Z_to_bv 64 f) (Z_to_bv 64 (shad f + 20)) s8x s9x s10x s11x t3 t4 t5 t6)
        F (Z_to_bv 64 IMP_BODY_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FLO SLO SH0 GLO LSP LUSP SPH DR NR A0 AH FRl VB MI.
  unfold imp_W3, imp_locals2, imp_locals3, IMP_BODY_A, IMP_SS00RET_A, IMP_VEC_OBJ_A, TPV_A, shad, SHB in *.
  cbn [map app repeat skipn e_set_shadow] in *.

  apply (rw_cells_split_CB bsegs _ _ [CB 8 j0] 24 j8 _ [16; 8]%nat) in FRl; [| reflexivity]. cbn [mk_CB_cells app] in FRl.
  lazymatch type of FRl with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: CB 72 j48 :: ?rest) =>
    apply (rw_cells_split_CB bsegs _ _ [c0; c1; c2; c3; c4] 72 j48 rest [8; 8; 32; 8; 8; 8]%nat) in FRl; [| reflexivity]; cbn [mk_CB_cells app] in FRl end.
  lazymatch type of FRl with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: CB 16 j128 :: ?rest) =>
    apply (rw_cells_split_CB bsegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] 16 j128 rest [8; 8]%nat) in FRl; [| reflexivity]; cbn [mk_CB_cells app] in FRl end.
  repeat match type of FRl with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "j" in set (j := t) in FRl; clearbody j end.
  pose proof (munch_refl [(sp' + 24, sp' + 32); (sp' + 48, sp' + 64); (sp' + 96, sp' + 112); (sp' + 136, sp' + 144)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).

  ls. zstep. zstep. zstep. zstep. zstep. try replace (A8 + 8 - A8) with 8 by lia. try replace (A8 + 8 + - A8) with 8 by lia.
  zstep. try replace (Z.shiftr (bv_signed (Z_to_bv 64 8)) 3) with 1 by (vm_compute; reflexivity). try rewrite shr3_div. try change (8 / 8) with 1.
  zstep. ls. zstep. if_false.

  zstep. ls. zstep. zstep. ls. zstep. ls. zstep. ls. zstep. zstep.
  apply evt_done. eexists _, _, _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.
