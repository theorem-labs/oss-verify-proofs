(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import I_lkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_new Sj_h_dtor. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Sj_hkitB Atp_fzwA Atp_h_defsA Atp_h_vkitA Atp_h_vkit2A Pj_lftoi1A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition si_mid0 (usp sp' lo RV FD : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := fun ms =>
  exists (m1 : mem) (a1' a2' : word) (j0 j1 j2 : list byte),
    ms = entry_st (Z_to_bv 64 0xb201c) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 96)
                  a1' a2' a3 a4 a5 a6 a7
                  s2 (Z_to_bv 64 FD) (Z_to_bv 64 RV) s5 s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6 F fc e_stack_malloc_1 m1
    /\ munch [(sp', usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo sp'
    /\ rw_cells asegs m1 sp' [CB 8 j0; CB 8 j1; CB 8 j2]
    /\ stk asegs m1 (sp' + 24) (usp - 104)
    /\ rw_cells asegs m1 (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

Lemma si_walk0_al : forall (usp lo RV FD : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 128 -> 0x6ca000 <= lo -> usp < 2^63 -> usp mod 32 = 0 -> 0 <= RV < 2^64 -> 0 <= FD < 2^64 -> client_consts m -> mem_inv asegs m ->
  evt asegs (si_mid0 usp (usp - 128) lo RV FD ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 RV) (Z_to_bv 64 FD) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc ATPA_SPLITINTO m).
Proof.
  intros until m. intros ST LO GLO SPH S32 VV DD (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold entry_st, ATPA_SPLITINTO, e_stack_malloc_1, si_mid0, fa_saved.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 128, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 128%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 128 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. do 13 zstep. zstep. zstep.
  rewrite (land_m32 (usp + -128)) by lia.
  replace (32 * ((usp + -128) / 32)) with (usp + -128) by (Z.div_mod_to_equations; lia).
  zstep. zstep. zstep. zstep. zstep. zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?rest) => change (c0 :: c1 :: c2 :: rest) with ([c0; c1; c2] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FRs]. cbn [cells_size csize Nat.add] in FRs.
  apply (rw_cells_forget_C8 asegs _ _ [] _ _) in FRl. cbn [app] in FRl.
  replace (usp + -128 + Z.of_nat 24) with (usp - 104) in FRs by lia.
  replace (usp + -128) with (usp - 128) in * by lia.
  apply evt_done. do 6 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl|].
  split; [| exact FRs].
  replace (usp - 128 + 24) with (usp - 104) by lia. split; [lia|]. split; [lia|]. intros a Ha. lia.
Qed.

Lemma si_walk0_un : forall (usp lo RV FD : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 144 -> 0x6ca000 <= lo -> usp < 2^63 -> usp mod 32 = 16 -> 0 <= RV < 2^64 -> 0 <= FD < 2^64 -> client_consts m -> mem_inv asegs m ->
  evt asegs (si_mid0 usp (usp - 144) lo RV FD ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 RV) (Z_to_bv 64 FD) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc ATPA_SPLITINTO m).
Proof.
  intros until m. intros ST LO GLO SPH S32 VV DD (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold entry_st, ATPA_SPLITINTO, e_stack_malloc_1, si_mid0, fa_saved.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 144, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 144%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 144 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. do 13 zstep. zstep. zstep.
  rewrite (land_m32 (usp + -128)) by lia.
  replace (32 * ((usp + -128) / 32)) with (usp + -144) by (Z.div_mod_to_equations; lia).
  zstep. zstep. zstep. zstep. zstep. zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) => change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2] ++ [c3; c4] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FR]. apply rw_cells_app in FR. destruct FR as [FRp FRs].
  cbn [cells_size csize Nat.add] in FRp, FRs.
  apply (rw_cells_forget_C8 asegs _ _ [_; _] _ _) in FRl. cbn [app] in FRl.
  replace (usp + -144 + Z.of_nat 24 + Z.of_nat 16) with (usp - 104) in FRs by lia.
  pose proof (wr_at_stk _ _ _ (rw_cells_wr_at asegs _ _ _ 16 FRp ltac:(cbn; lia))) as STp.
  replace (usp + -144 + Z.of_nat 24 + 16) with (usp - 104) in STp by lia.
  replace (usp + -144 + Z.of_nat 24) with (usp - 144 + 24) in STp by lia.
  replace (usp + -144) with (usp - 144) in * by lia.
  apply evt_done. do 6 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl|].
  split; [| exact FRs].
  match goal with |- stk _ _ ?a ?b => replace a with (usp - 144 + 24) by lia; replace b with (usp - 104) by lia end. exact STp.
Qed.

Lemma si_prologue : forall (usp lo RV FD : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 144 -> 0x6ca000 <= lo -> usp < 2^63 -> usp mod 16 = 0 -> 0 <= RV < 2^64 -> 0 <= FD < 2^64 -> client_consts m -> mem_inv asegs m ->
  exists sp', usp - 144 <= sp' <= usp - 128 /\ sp' mod 32 = 0 /\
    evt asegs (si_mid0 usp sp' lo RV FD ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
      (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 RV) (Z_to_bv 64 FD) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
         t3 t4 t5 t6 F fc ATPA_SPLITINTO m).
Proof.
  intros until m. intros ST LO GLO SPH S16 VV DD CC MI.
  assert (C : usp mod 32 = 0 \/ usp mod 32 = 16) by (Z.div_mod_to_equations; lia).
  destruct C as [C|C].
  - exists (usp - 128). split; [lia|]. split; [Z.div_mod_to_equations; lia|]. apply si_walk0_al; try assumption; lia.
  - exists (usp - 144). split; [lia|]. split; [Z.div_mod_to_equations; lia|]. apply si_walk0_un; assumption.
Qed.

Definition si_hdr (h3 jv jr : list byte) : list cell :=
  [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x22c84); C8 (Z_to_bv 64 0xb1fa8); CB 8 h3; CB 24 jv; CB 64 jr].
Definition si_shadow (g4 g5 g6 : Z) (t : list (list byte)) : list cell :=
  map C1 (repeat (Z_to_bv 8 (-15)) 4 ++ [Z_to_bv 8 g4; Z_to_bv 8 g5; Z_to_bv 8 g6] ++ repeat (Z_to_bv 8 (-13)) 5) ++ map (fun l => CB 1 l) t.
Definition si_shadow0 (ls : list (list byte)) : list cell := map (fun l => CB 1 l) ls.

Definition si_W1 (sp' f : Z) : list ivl := [(sp' + 8, sp' + 16); (f, f + 24); (shad f, shad f + 12)].

Lemma si_walk1 : forall (usp sp' f lo RV FD : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2x s5 s6 s7x s8x s10 s11 t3 t4 t5 t6 : word)
    (j0 j1 j2 h0 h1 h2 h3 jv jr : list byte) (ls t : list (list byte)) F fc (m : mem),
  length ls = 12%nat -> length t = 4%nat ->
  0 < f -> f + 128 <= lo -> shad f + 16 <= lo -> SHB <= shad f -> (f + 128 <= shad f \/ shad f + 16 <= f) ->
  0x6ca000 <= lo -> lo <= sp' -> sp' + 24 <= usp -> usp < 2^63 -> 0 <= RV < 2^64 ->
  rw_cells asegs m sp' [CB 8 j0; CB 8 j1; CB 8 j2] ->
  rw_cells asegs m f [CB 8 h0; CB 8 h1; CB 8 h2; CB 8 h3; CB 24 jv; CB 64 jr] ->
  rw_cells asegs m (shad f) (si_shadow0 (ls ++ t)) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 0xb20c8) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 RV) (Z_to_bv 64 0) (Z_to_bv 64 24)
             (Z_to_bv 64 (-13)) (Z_to_bv 64 (-8)) a5 a6 a7 (Z_to_bv 64 f) (Z_to_bv 64 FD) (Z_to_bv 64 RV) s5 s6 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) s10 s11
             t3 t4 t5 t6 F fc e_asan_memset m1
      /\ munch (si_W1 sp' f) m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 sp' [CB 8 j0; C8 (Z_to_bv 64 f); CB 8 j2]
      /\ rw_cells asegs m1 f (si_hdr h3 jv jr)
      /\ rw_cells asegs m1 (shad f) (si_shadow (-8) (-8) (-8) t))
    (MS (mkR (Z_to_bv 64 0xb201c) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7
             s2x (Z_to_bv 64 FD) (Z_to_bv 64 RV) s5 s6 s7x s8x (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb201c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LS LT F0 FLO SLO SH0 SEP GLO LSP SPU SPH VV FRl FH FS MI.
  do 12 (destruct ls as [|? ls]; [discriminate LS|]). destruct ls; [| discriminate LS]. clear LS.
  do 4 (destruct t as [|? t]; [discriminate LT|]). destruct t; [| discriminate LT]. clear LT.
  unfold entry_st, e_asan_memset, si_W1, si_hdr, si_shadow, si_shadow0, shad, SHB in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(sp' + 8, sp' + 16); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 12)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).

  zstep. zstep. zstep. zstep. if_cases K; zify_cond K; [| exfalso; lia].

  ls. zstep. zstep. zstep. zstep. rewrite shr3_div. zstep. zstep. zstep. zstep. zstep.
  ls. ls. ls.

  zstep. zstep. do 12 ls.

  zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Definition si_regs (pc : Z) (ra : word) (sp' : Z) (gp tp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (f FD RV : Z) (s5 s6 : word)
    (s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 f) (Z_to_bv 64 FD) (Z_to_bv 64 RV) s5 s6 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Lemma si_walk2e : forall (usp sp' f RV FD D : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= FD -> FD + 24 < 2^63 -> 0 < f < 2^63 -> 0 <= D < 2^64 ->
  shz m FD 16 -> rw_cells asegs m FD [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 0)] -> mem_inv asegs m ->
  evt asegs (eq (si_regs 0xb21b8 (Z_to_bv 64 0xb20c8) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 0) a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 f FD RV (Z_to_bv 64 (FD + 8)) s6
                 (Z_to_bv 64 (shad (FD + 8))) s11 t3 t4 t5 t6 F fc m))
    (si_regs 0xb20c8 (Z_to_bv 64 0xb20c8) sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f FD RV s5 s6 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros FD0 FDH FF DD SHD FDC MI. unfold si_regs, shad, SHB in *.
  pose proof (SHD (FD + 8) ltac:(lia)) as RD1.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_true.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma si_walk2n : forall (usp sp' f lo RV FD D L : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) (t : list (list byte)) F fc (m : mem),
  0 <= FD -> FD + 24 < 2^63 -> 0 < f -> f + 128 <= lo -> shad f + 16 <= lo -> SHB <= shad f -> (f + 128 <= shad f \/ shad f + 16 <= f) -> lo <= FD ->
  0 <= D < 2^64 -> 0 < L < 2^64 ->
  x_shz [(shad f + 4, shad f + 7)] m FD 16 -> rw_cells asegs m FD [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 L)] ->
  rw_cells asegs m (shad f) (si_shadow (-8) (-8) (-8) t) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = si_regs ATPA_SPLIT (Z_to_bv 64 0xb2110) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (f + 32)) (Z_to_bv 64 D) (Z_to_bv 64 L) a3 a4 a5 a6 a7 f FD RV (Z_to_bv 64 (FD + 8)) (Z_to_bv 64 (f + 32))
             (Z_to_bv 64 (shad (FD + 8))) (Z_to_bv 64 (shad FD)) t3 t4 t5 t6 F fc m1
      /\ munch [(shad f + 4, shad f + 7)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (shad f) (si_shadow 0 0 0 t))
    (si_regs 0xb20c8 (Z_to_bv 64 0xb20c8) sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f FD RV s5 s6 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros FD0 FDH F0 FLO SLO SH0 SEP LFD DD LL SHD FDC FS MI. unfold si_regs, ATPA_SPLIT, si_shadow, x_shz, shad, SHB in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 7)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHD mm MU' WM' (FD + 8) ltac:(lia)) as RD1 end.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false. clear RD1.
  zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  ls. ls. ls.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHD mm MU' WM' FD ltac:(lia)) as RD0 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false. clear RD0.
  zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption| eassumption].
Qed.

Lemma si_walk3 : forall (usp sp' f lo RV FD b e c : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo sp' -> lo <= sp' - 32 -> 0x6ca000 <= lo -> sp' < 2^63 -> 0 <= FD < 2^64 ->
  0 < f -> f + 128 <= lo -> shad f + 16 <= lo -> SHB <= shad f -> (f + 128 <= shad f \/ shad f + 16 <= f) ->
  0 < RV -> RV + 24 <= lo -> (RV + 24 <= f \/ f + 128 <= RV) -> (RV + 24 <= shad f \/ shad f + 16 <= RV) ->
  0 <= b < 2^64 -> 0 <= e < 2^64 -> 0 <= c < 2^64 ->
  shb_consts m -> v_shz [(sp' - 32, sp'); (RV, RV + 24)] m RV ->
  rw_cells asegs m RV (vcells 0 0 0) -> rw_cells asegs m (f + 32) (vcells b e c) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = si_regs e_asan_memset (Z_to_bv 64 0xb2178) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (f + 32)) (Z_to_bv 64 0) (Z_to_bv 64 24) a3 a4 a5 a6 a7 f FD RV (Z_to_bv 64 (FD + 8)) (Z_to_bv 64 (f + 32))
             (Z_to_bv 64 (shad (FD + 8))) (Z_to_bv 64 (shad FD)) t3 t4 t5 t6 F fc m1
      /\ munch [(sp' - 32, sp'); (RV, RV + 24)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo sp'
      /\ rw_cells asegs m1 RV (vcells b e c) /\ rw_cells asegs m1 (f + 32) (vcells b e c))
    (si_regs 0xb2110 (Z_to_bv 64 0xb2110) sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f FD RV (Z_to_bv 64 (FD + 8)) (Z_to_bv 64 (f + 32))
       (Z_to_bv 64 (shad (FD + 8))) (Z_to_bv 64 (shad FD)) t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros ST LO GLO SPH DD F0 FLO SLO SH0 SEP V0 VLO VF VS BB EE CC (G1 & G2) SHZ VC PC MI.
  unfold si_regs, e_asan_memset, vcells, v_shz, shad, SHB in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(sp' - 32, sp'); (RV, RV + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).

  zstep. zstep.

  zstep. carve_frame 32%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. zstep. lstep. zstep.
  zstep. zstep. zstep. clear G1 G2. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' RV ltac:(lia)) as RD0; pose proof (SHZ mm MU' WM' (RV + 8) ltac:(lia)) as RD1; pose proof (SHZ mm MU' WM' (RV + 16) ltac:(lia)) as RD2 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_true.
  zstep. zstep. zstep. zstep. release_frame FR ST sp'. zstep. zstep.

  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false. clear RD0 RD1 RD2.
  zstep. zstep. ls.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (RV + 8) ltac:(lia)) as RD1 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false. clear RD1.
  zstep. ls. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (RV + 16) ltac:(lia)) as RD2 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false. clear RD2.
  zstep. ls.

  zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; eassumption.
Qed.

Lemma si_walk4 : forall (usp sp' f lo RV FD D L : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j0 j2 : list byte) (t : list (list byte)) F fc (m : mem),
  length t = 4%nat -> stk asegs m lo sp' -> lo <= sp' - 32 -> 0x6ca000 <= lo -> sp' + 24 <= FD -> FD + 24 < 2^63 ->
  0 < f -> f + 128 <= lo -> shad f + 16 <= lo -> SHB <= shad f -> (f + 128 <= shad f \/ shad f + 16 <= f) ->
  0 <= D -> 0 <= L -> D + L < 2^64 ->
  shb_consts m -> x_shz [(sp' - 32, sp'); (sp' + 16, sp' + 24); (shad f + 4, shad f + 7); (FD, FD + 16)] m (sp' + 16) 8 ->
  x_shz [(sp' - 32, sp'); (sp' + 16, sp' + 24); (shad f + 4, shad f + 7); (FD, FD + 16)] m FD 16 ->
  rw_cells asegs m sp' [CB 8 j0; C8 (Z_to_bv 64 f); CB 8 j2] ->
  rw_cells asegs m (f + 32) (vcells 0 0 0) -> rw_cells asegs m (shad f) (si_shadow 0 0 0 t) ->
  rw_cells asegs m FD [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 L)] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a2' : word),
      ms = si_regs 0xb21b8 (Z_to_bv 64 0xb2184) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (D + L)) (Z_to_bv 64 L) a2' a3 a4 a5 a6 a7 f FD RV (Z_to_bv 64 (FD + 8)) (Z_to_bv 64 (f + 32))
             (Z_to_bv 64 (shad (FD + 8))) (Z_to_bv 64 (shad FD)) t3 t4 t5 t6 F fc m1
      /\ munch [(sp' - 32, sp'); (sp' + 16, sp' + 24); (shad f + 4, shad f + 7); (FD, FD + 16)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo sp'
      /\ rw_cells asegs m1 sp' [CB 8 j0; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 (f + 32))]
      /\ rw_cells asegs m1 (shad f) (si_shadow (-8) (-8) (-8) t)
      /\ rw_cells asegs m1 FD [C8 (Z_to_bv 64 (D + L)); C8 (Z_to_bv 64 0)])
    (si_regs 0xb2178 (Z_to_bv 64 0xb2178) sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f FD RV (Z_to_bv 64 (FD + 8)) (Z_to_bv 64 (f + 32))
       (Z_to_bv 64 (shad (FD + 8))) (Z_to_bv 64 (shad FD)) t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros LT ST LO GLO SFD FDH F0 FLO SLO SH0 SEP D0 L0 DL (G1 & G2) SHC SHD FRl PC FS FDC MI.
  do 4 (destruct t as [|? t]; [discriminate LT|]). destruct t; [| discriminate LT]. clear LT.
  unfold si_regs, vcells, si_shadow, x_shz, shad, SHB in *. cbn [map app repeat] in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(sp' - 32, sp'); (sp' + 16, sp' + 24); (f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 7); (FD, FD + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).

  zstep. zstep. zstep.

  zstep. carve_frame 32%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. zstep. lstep. zstep.
  zstep. zstep. zstep. clear G1 G2. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHC mm MU' WM' (sp' + 16) ltac:(lia)) as RD0 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false. clear RD0.
  zstep. zstep. rewrite shr3_div. zstep. replace ((f + 32) / 8 + 2147450880) with (f / 8 + 2147450880 + 4) by (Z.div_mod_to_equations; lia).
  zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_true.
  zstep. zstep. zstep. zstep. release_frame FR ST sp'. zstep. zstep.

  zstep. ls. ls. ls.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHD mm MU' WM' (FD + 8) ltac:(lia)) as RD1; pose proof (SHD mm MU' WM' FD ltac:(lia)) as RD0 end.
  replace ((FD + 8) / 8 + 2147450880) with (FD / 8 + 2147450880 + 1) in * by (Z.div_mod_to_equations; lia).
  zstep. shz_norm. zstep. if_false. zstep. shz_norm. zstep. if_false. clear RD0 RD1.
  zstep. zstep. zstep. zstep. ls.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|].
  split; [eassumption|]. split; eassumption.
Qed.

Lemma si_rel1 : forall (usp sp' f FD RV : Z) (rax gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5x s6x s10x s11x t3 t4 t5 t6 : word)
    (g4 g5 g6 : Z) (t : list (list byte)) (hrest : list cell) F fc (m : mem),
  length t = 4%nat -> 0 < f -> f + 128 < 2^47 -> SHB <= shad f -> (f + 128 <= shad f \/ shad f + 16 <= f) ->
  rw_cells asegs m f (C8 (Z_to_bv 64 0x41b58ab3) :: hrest) -> rw_cells asegs m (shad f) (si_shadow g4 g5 g6 t) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = si_regs 0xb220c rax sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (-11)) a1 a2 a3 a4 a5 a6 a7 f FD RV s5x s6x s10x s11x t3 t4 t5 t6 F fc m1
      /\ munch [(f, f + 8); (shad f, shad f + 16)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1)
    (si_regs 0xb21b8 rax sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f FD RV s5x s6x s10x s11x t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros LT F0 FHI SH0 SEP FH FS MI.
  do 4 (destruct t as [|? t]; [discriminate LT|]). destruct t; [| discriminate LT]. clear LT.
  unfold si_regs, si_shadow, shad, SHB in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.

  zstep. zstep. ls. zstep. if_cases K; zify_cond K; [exfalso; lia| clear K]. zstep.
  do 16 ls.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM| eassumption].
Qed.

Lemma si_rel2 : forall (usp sp' f fl lo FD RV : Z) (rax gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5x s6x s10x s11x t3 t4 t5 t6 : word)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (loc : list cell) F fc (m : mem),
  Z.of_nat (cells_size loc) = 24 ->
  stk asegs m lo sp' -> lo <= sp' -> sp' + 24 <= usp - 104 -> usp < 2^63 -> 0x6ca000 <= lo ->
  0 < f -> f + 128 <= lo -> 0 < fl -> fl + 1 <= lo ->
  rw_cells asegs m sp' loc -> stk asegs m (sp' + 24) (usp - 104) -> rw_cells asegs m (usp - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  ro_cells asegs m (f + 120) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fl) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m1 (seg_rom asegs)
      /\ munch [(fl, fl + 1)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp
      /\ rw_cells asegs m1 fl [C1 (Z_to_bv 8 0)])
    (si_regs 0xb220c rax sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f FD RV s5x s6x s10x s11x t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros LOC ST LO SPU SPH GLO F0 FLO FL0 FLL FRl STp FRs FW FLC MI.
  unfold si_regs, fa_saved, shad, SHB in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).

  zstep. ls. zstep.

  replace (usp - 104) with (usp + -104) in FRs by lia.
  zstep. do 13 zstep. zstep.
  replace (usp + -104) with (usp - 104) in FRs by lia.
  pose proof (stk_release asegs _ _ _ _ ST FRl ltac:(lia)) as ST1. rewrite LOC in ST1.
  pose proof (stk_merge asegs _ _ _ _ ST1 STp ltac:(lia)) as ST2.
  pose proof (stk_release asegs _ _ _ _ ST2 FRs ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
  replace (usp - 104 + Z.of_nat 104) with usp in ST3 by lia. clear ST ST1 ST2. rename ST3 into ST.
  zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| eassumption].
Qed.
