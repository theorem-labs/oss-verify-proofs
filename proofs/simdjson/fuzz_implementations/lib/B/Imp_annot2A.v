(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA R_cache_defs R_m2s R_poison X_ixdefs Imp_annotA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma land_m8_gen : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x - x mod 8.
Proof. intros x Hx. rewrite (land_align x 64 3 18446744073709551608 eq_refl ltac:(lia) Hx). reflexivity. Qed.
Ltac fix_and8 v := match goal with |- context [Z.land ?x 18446744073709551608] =>
  rewrite (land_m8_gen x) by lia; replace (x - x mod 8) with v by (Z.div_mod_to_equations; lia) end.

Lemma annot_frontA : forall (usp lo b e old new : Z) (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - ANNOT_FRAME -> 0x100000000 <= lo -> usp < 2^63 ->
  0 <= b -> b <= old <= e -> b <= new <= e -> old <> new -> e < 2^63 -> e - b < 2^40 -> b mod 8 = 0 -> e mod 8 = 0 ->
  rw_cells bsegs m g_GOT_flags [C8 (wz 0x187178)] -> ro_cells bsegs m g_flags_dco [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m g_GOT_verbosity [C8 (wz g_verbosity)] -> rw_cells bsegs m g_verbosity [C4 (wz 0)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem) (j1 j2 : list byte),
      ms = MS (mkR ra (wz (usp - 2128)) gp tp t0 t1 t2 (wz usp) (wz b) (wz old) (wz old) (wz old) (wz (e - b)) (Z_to_bv 64 (Z.shiftl 1 40)) a5 a6 a7
                   (wz new) (wz 0) (wz old) (wz new) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x88650) fc None m' (seg_rom bsegs)
      /\ munch [(usp - ANNOT_FRAME, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (usp - 2128)
      /\ rw_cells bsegs m' (usp - 2128) [CB 96 j2]
      /\ rw_cells bsegs m' (usp - 2032) [CB 1976 j1; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (entry_st ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz b) (wz e) (wz old) (wz new) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_annot m).
Proof.
  intros until m. intros ST LO GLO SPH B0 BO BN ON EH EB B8 E8 GF FD GV VV MI.
  unfold entry_st, e_annot, ANNOT_FRAME, g_GOT_flags, g_flags_dco, g_GOT_verbosity, g_verbosity in *. change (0x187178 + 96) with 1602008 in FD.
  pose proof (munch_refl [(usp - 2128, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).

  zstep. carve_frame 2032%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 2032 _ [] [1976; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in set (j := t) in FR; clearbody j end.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. carve_frame 96%nat ST.

  zstep. zstep. zstep. zstep. cbv beta. zstep. if_false.

  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_false.

  step. if_cases K; zify_cond K; [| exfalso; lia].

  step. if_cases K2; zify_cond K2; [exfalso; lia|].
  step. if_cases K3; zify_cond K3; [exfalso; lia|].
  step. if_cases K4; zify_cond K4; [exfalso; lia|].

  zstep. zstep. zstep. zstep. step. if_cases K5; zify_cond K5; [exfalso; lia|].

  step. if_cases K6; zify_cond K6; [exfalso; lia|].

  zstep. rewrite (land7_ps e) by lia. rewrite E8. zstep. if_false.
  zstep. zstep. zstep. zstep. rewrite (land7_ps b) by lia. rewrite B8. zstep. if_false. zstep. zstep.
  replace (usp + -2032 + -96) with (usp - 2128) in * by lia. replace (usp + -2032) with (usp - 2032) in * by lia.
  apply evt_done. eexists _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR0| exact FR].
Qed.

Lemma annot_poison8A : forall (usp lo p : Z) (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (shj : list byte) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - ANNOT_FRAME - 64 -> kHighShadowEnd + 8 <= lo -> usp < 2^63 ->
  0 < p -> p mod 16 = 0 -> ((0 <= p /\ p + 8 <= 0x7fff8000) \/ (0x10007fff7fff < p /\ p + 8 <= 0x800000000000)) -> p / 8 + 2147450888 <= lo ->
  rw_cells bsegs m g_GOT_flags [C8 (wz 0x187178)] -> ro_cells bsegs m g_flags_dco [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m g_GOT_verbosity [C8 (wz g_verbosity)] -> rw_cells bsegs m g_verbosity [C4 (wz 0)] ->
  ps_cells m -> rw_cells bsegs m (shad p) [CB 1 shj] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms = MS (mkR ra (wz usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(usp - ANNOT_FRAME - 64, usp); (shad p, shad p + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
      /\ rw_cells bsegs m' (shad p) [CB 1 [Z_to_bv 8 252]])
    (entry_st ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz p) (wz (p + 8)) (wz (p + 8)) (wz p) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_annot m).
Proof.
  intros until m. intros ST LO HLO SPH P0 P16 PCL PSH GF FD GV VV PS SH MI.
  unfold kHighShadowEnd in HLO.
  eapply evt_cut; [eapply (annot_frontA usp lo p (p + 8) (p + 8) p ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST
                             ltac:(unfold ANNOT_FRAME in *; lia) ltac:(lia) SPH ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                             ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) GF FD GV VV MI)|].
  cbv beta. intros ms1 (m1 & j1 & j2 & -> & MU1 & WM1 & MI1 & ST1 & FR96 & FR). unfold ANNOT_FRAME in *.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ SH MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add fst snd]; unfold shad, SHB; lia)) as SH1.
  pose proof (ps_cells_framed m m1 _ PS MU1 WM1 ltac:(cbn [disjoint_from]; unfold img_hull_lo, img_hull_hi; lia)) as PS1.
  clear GF FD GV VV PS SH MI ST.
  pose proof (munch_refl [(usp - 2128 - 64, usp); (shad p, shad p + 1)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  replace (p + 8 - p) with 8 by lia.

  step. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. fix_and8 p. step. if_cases K2; zify_cond K2; [exfalso; lia|].
  zstep. fix_and8 p. zstep. zstep. fix_and8 p. step. if_cases K3; zify_cond K3; [| exfalso; lia].

  zstep. zstep. fix_and8 (p + 8). step. if_cases K4; zify_cond K4; [exfalso; lia|].
  zstep. replace (p + 8 - p) with 8 by lia. zstep. zstep. zstep.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp - 2128)) = usp - 2128) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { change 554444 with ps_entry. rewrite <- EU2 in ST1.
    eapply (poison_small_spec _ _ gp tp _ _ _ _ _ _ _ a5 a6 a7 _ _ _ _ s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc _ p 8 252 lo shj); try eassumption.
    - split; [| unfold kLowMemEnd, kHighShadowEnd, kHighMemEnd; lia]. split; [Z.div_mod_to_equations; lia| split; [reflexivity| lia]].
    - lia. - left; lia. - rewrite EU2. lia. }
  cbv beta. intros ms2 (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & SH2 & ST2).
  rewrite EU2 in MU2, ST2. cbn [Z.div Z.to_nat repeat Pos.to_nat] in SH2. change (Z.to_nat (8 / 8)) with 1%nat in SH2. change (8 / 8) with 1 in MU2. cbn [repeat] in SH2.
  rewrite (ret_pc_even 0x88758) by lia.
  pose proof (rw_cells_transport bsegs _ m1 m2 _ _ FR96 MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add fst snd]; unfold shad, SHB; lia)) as FR96b.
  pose proof (rw_cells_transport bsegs _ m1 m2 _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add fst snd]; unfold shad, SHB; lia)) as FRb.
  assert (MU12 : munch [(usp - 2128 - 64, usp); (shad p, shad p + 1)] m m2).
  { intros x Hx. cbn [outside] in Hx. rewrite (MU2 x) by (cbn [outside]; lia). apply MU1. cbn [outside]. lia. }
  pose proof (wmono_trans _ _ _ _ WM1 WM2) as WM12.
  clear MU WM MU1 WM1 MU2 WM2 FR96 FR MI1 ST1 SH1 PS1.
  pose proof MU12 as MU. pose proof WM12 as WM.

  step. if_cases K5; zify_cond K5; [| exfalso; lia].
  replace (usp - 2128) with (usp + -2032 + -96) in * by lia. replace (usp - 2032) with (usp + -2032) in * by lia.
  zstep. release_frame FR96b ST2 (usp + -2032).
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. release_frame FRb ST2 usp. zstep.
  apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2| exact SH2].
Qed.

Lemma annot_unpoison8A : forall (usp lo p : Z) (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (shj : list byte) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - ANNOT_FRAME - 64 -> kHighShadowEnd + 8 <= lo -> usp < 2^63 ->
  0 < p -> p mod 16 = 0 -> ((0 <= p /\ p + 8 <= 0x7fff8000) \/ (0x10007fff7fff < p /\ p + 8 <= 0x800000000000)) -> p / 8 + 2147450888 <= lo ->
  rw_cells bsegs m g_GOT_flags [C8 (wz 0x187178)] -> ro_cells bsegs m g_flags_dco [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m g_GOT_verbosity [C8 (wz g_verbosity)] -> rw_cells bsegs m g_verbosity [C4 (wz 0)] ->
  ps_cells m -> rw_cells bsegs m (shad p) [CB 1 shj] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms = MS (mkR ra (wz usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(usp - ANNOT_FRAME - 64, usp); (shad p, shad p + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
      /\ rw_cells bsegs m' (shad p) [CB 1 [Z_to_bv 8 0]])
    (entry_st ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz p) (wz (p + 8)) (wz p) (wz (p + 8)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_annot m).
Proof.
  intros until m. intros ST LO HLO SPH P0 P16 PCL PSH GF FD GV VV PS SH MI.
  unfold kHighShadowEnd in HLO.
  eapply evt_cut; [eapply (annot_frontA usp lo p (p + 8) p (p + 8) ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST
                             ltac:(unfold ANNOT_FRAME in *; lia) ltac:(lia) SPH ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                             ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) GF FD GV VV MI)|].
  cbv beta. intros ms1 (m1 & j1 & j2 & -> & MU1 & WM1 & MI1 & ST1 & FR96 & FR). unfold ANNOT_FRAME in *.
  pose proof (rw_cells_transport bsegs _ m m1 _ _ SH MU1 WM1 ltac:(cbn [disjoint_from cells_size csize Nat.add fst snd]; unfold shad, SHB; lia)) as SH1.
  pose proof (ps_cells_framed m m1 _ PS MU1 WM1 ltac:(cbn [disjoint_from]; unfold img_hull_lo, img_hull_hi; lia)) as PS1.
  clear GF FD GV VV PS SH MI ST.
  pose proof (munch_refl [(usp - 2128 - 64, usp); (shad p, shad p + 1)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  replace (p + 8 - p) with 8 by lia.

  step. if_cases K; zify_cond K; [| exfalso; lia].
  zstep. fix_and8 p. step. if_cases K2; zify_cond K2; [exfalso; lia|].
  zstep. zstep. fix_and8 (p + 8). zstep. zstep. fix_and8 (p + 8). step. if_cases K3; zify_cond K3; [| exfalso; lia].
  zstep. replace (p + 8 - p) with 8 by lia. zstep. zstep. zstep.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp - 2128)) = usp - 2128) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { change 554444 with ps_entry. rewrite <- EU2 in ST1.
    eapply (poison_small_spec _ _ gp tp _ _ _ _ _ _ _ a5 a6 a7 _ _ _ _ s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc _ p 8 0 lo shj); try eassumption.
    - split; [| unfold kLowMemEnd, kHighShadowEnd, kHighMemEnd; lia]. split; [Z.div_mod_to_equations; lia| split; [reflexivity| lia]].
    - lia. - right. change (8 / 8) with 1. lia. - rewrite EU2. lia. }
  cbv beta. intros ms2 (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & SH2 & ST2).
  rewrite EU2 in MU2, ST2. cbn [Z.div Z.to_nat repeat Pos.to_nat] in SH2. change (Z.to_nat (8 / 8)) with 1%nat in SH2. change (8 / 8) with 1 in MU2. cbn [repeat] in SH2.
  rewrite (ret_pc_even 0x88758) by lia.
  pose proof (rw_cells_transport bsegs _ m1 m2 _ _ FR96 MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add fst snd]; unfold shad, SHB; lia)) as FR96b.
  pose proof (rw_cells_transport bsegs _ m1 m2 _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add fst snd]; unfold shad, SHB; lia)) as FRb.
  assert (MU12 : munch [(usp - 2128 - 64, usp); (shad p, shad p + 1)] m m2).
  { intros x Hx. cbn [outside] in Hx. rewrite (MU2 x) by (cbn [outside]; lia). apply MU1. cbn [outside]. lia. }
  pose proof (wmono_trans _ _ _ _ WM1 WM2) as WM12.
  clear MU WM MU1 WM1 MU2 WM2 FR96 FR MI1 ST1 SH1 PS1.
  pose proof MU12 as MU. pose proof WM12 as WM.

  step. if_cases K5; zify_cond K5; [| exfalso; lia].
  replace (usp - 2128) with (usp + -2032 + -96) in * by lia. replace (usp - 2032) with (usp + -2032) in * by lia.
  zstep. release_frame FR96b ST2 (usp + -2032).
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. release_frame FRb ST2 usp. zstep.
  apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2| exact SH2].
Qed.
