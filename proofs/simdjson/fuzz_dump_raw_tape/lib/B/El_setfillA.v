(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue Sj_stage1_kit Pj_loc_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_defsA Atp_fzwA Pj_lftoi1A Pj_rtkA Pj_defsA Pj_os_defsA Pj_os_put1A Pj_os_put3A Pj_os_padA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import El_ins_ifaceA El_os_padA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Export El_os_defsA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition sf_mid0 (S lo OSP CP : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := fun ms =>
  exists (m1 : mem) (a1' a2' : word) (j1 j2 j3 j4 j5 j6 : list byte),
    ms = entry_st (wz 0xb2090) (wz (S - 160)) gp tp t0 t1 t2 (wz S) (wz (S - 160)) (wz 64) a1' a2' a3 a4 a5 a6 a7
                  (wz OSP) s3 s4 (wz CP) s6 s7 s8 s9 (wz SHB) s11 t3 t4 t5 t6 F fc (e_stack_malloc 0) m1
    /\ munch [(S - 160, S)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (S - 160)
    /\ rw_cells bsegs m1 (S - 160) [C8 (wz 0); CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6]
    /\ rw_cells bsegs m1 (S - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

Lemma sf_walk0 : forall (S lo OSP CP : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo S -> lo <= S - 160 -> 0x6ce000 <= lo -> S < 2^63 -> S mod 32 = 0 -> 0 <= OSP < 2^64 -> 0 <= CP < 2^64 ->
  client_consts m -> mem_inv bsegs m ->
  evt bsegs (sf_mid0 S lo OSP CP ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
    (entry_st ra (wz S) gp tp t0 t1 t2 s0 s1 (wz OSP) (wz CP) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc 0xb201c m).
Proof.
  intros until m. intros ST LO GLO SPH S32 OR CR (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold entry_st, e_stack_malloc, sf_mid0, fa_saved.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(S - 160, S)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 160%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 160 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. do 13 zstep. zstep. zstep.
  rewrite (land_m32 (S + -160)) by lia.
  replace (32 * ((S + -160) / 32)) with (S + -160) by (Z.div_mod_to_equations; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 (S + -160)) = S + -160) by (apply unsigned_lit; lia).
  do 6 zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: rest) with ([c0; c1; c2; c3; c4; c5; c6] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FRs]. cbn [cells_size csize Nat.add] in FRs.
  replace (S + -160 + Z.of_nat 56) with (S - 104) in FRs by lia.
  apply evt_done. do 9 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl| exact FRs].
Qed.

Definition sf_sh8 : list byte := repeat (Z_to_bv 8 (-15)) 4 ++ [Z_to_bv 8 (-8)] ++ repeat (Z_to_bv 8 (-13)) 3.
Definition f5x8 : list byte := repeat (Z_to_bv 8 (-11)) 8.

Lemma sf_segA1 : forall (S f OS CP c lo : Z) (b : byte) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (j1 j2 j3 j4 j5 j6 h0 h1 h2 : list byte) (ls : list (list byte)) F fc (m : mem),
  length ls = 8%nat ->
  0 < f -> f mod 8 = 0 -> f + 64 <= lo -> 0xd9c00 <= f / 8 -> f / 8 + 2147450880 + 8 <= lo -> (f + 64 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 8 <= f) ->
  0x6ce000 <= OS -> OS + 288 <= lo -> OS mod 16 = 0 -> OS / 8 + 2147450880 + 37 <= lo ->
  (OS + 288 <= f \/ f + 64 <= OS) -> (f + 64 <= OS / 8 + 2147450880 \/ (OS + 288) / 8 + 2147450880 <= f) ->
  (OS + 288 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 8 <= OS) -> (OS + 288 <= OS / 8 + 2147450880 \/ OS / 8 + 2147450880 + 37 <= OS) ->
  0x7fff7f800000 <= lo -> lo <= S - 160 -> S < 2^63 ->
  (f + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= f) -> (OS + 288 <= 0x7fff7000 \/ 0x10007fff8000 <= OS) ->
  0 < CP -> CP + 1 <= 2^47 -> (CP + 1 <= f \/ f + 64 <= CP) -> (CP + 1 <= OS \/ OS + 288 <= CP) -> (CP + 1 <= lo \/ S <= CP) ->
  (CP + 1 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 8 <= CP) ->
  0 <= c < 256 ->
  bytes_at bsegs m (OS / 8 + 2147450880) (repeat z8 36) -> acc bsegs m 0x168e08 24 ->
  bytes_at bsegs m CP [Z_to_bv 8 c] -> bytes_at bsegs m (CP / 8 + 2147450880) [b] -> sh_ok b CP ->
  rw_cells bsegs m (S - 160) [C8 (wz 0); CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6] ->
  rw_cells bsegs m f [CB 8 h0; CB 8 h1; CB 8 h2] -> rw_cells bsegs m (f / 8 + 2147450880) (map (fun l => CB 1 l) ls) ->
  rw_cells bsegs m (OS + 128) [C8 (wz 0x168e30)] ->
  ro_cells bsegs m 0x168e08 [C8 (wz 0x111a64); C8 (wz 0xb0168); C8 (wz 8)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb2090) (wz (S - 160)) gp tp t0 t1 t2 (wz S) (wz (S - 160)) (wz (OS + 283)) (wz (OS + 136)) (wz 0) (wz (-13)) a4 (wz c) a6 a7
                   (wz (OS + 128)) (wz f) (wz (OS + 280)) (wz CP) s6 s7 (wz (f / 8 + 2147450880)) (wz f) (wz 2147450880) (wz ((OS + 280) / 8 + 2147450880)) t3 t4 t5 t6)
              F (wz 0xb2190) fc None m1 (seg_rom bsegs)
      /\ munch [(S - 112, S - 104); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (S - 160) [C8 (wz 0); CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; C8 (wz f)]
      /\ rw_cells bsegs m1 f [C8 (wz 0x41b58ab3); C8 (wz 0x1845f); C8 (wz 0xb201c)]
      /\ rw_cells bsegs m1 (f / 8 + 2147450880) (map C1 sf_sh8))
    (MS (mkR (wz 0xb2090) (wz (S - 160)) gp tp t0 t1 t2 (wz S) (wz (S - 160)) (wz f) a1 a2 a3 a4 a5 a6 a7
             (wz (OS + 128)) s3 s4 (wz CP) s6 s7 s8 s9 (wz 2147450880) s11 t3 t4 t5 t6)
        F (wz 0xb2090) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS F0 F8 FLO FD8 SLO SEP O0 OLO O16 OSLO OF OSH OSH2 OSELF LOW LSP SPH FHIf FHIo C0 CHI CF CO CS CSH RC SHZ0 VTA CB1 CSB SOK FRl FH FS V128 VT MI.
  do 8 (destruct ls as [|? ls]; [discriminate LS|]). destruct ls; [| discriminate LS]. clear LS.
  cbn [map] in FS.
  pose proof (munch_refl [(S - 112, S - 104); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 (S - 160)) = S - 160) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (SHZ : forall m', munch [(S - 112, S - 104); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m m' -> wmono bsegs m m' -> shz m' OS 288).
  { intros m' MU' _. change 288 with (8 * Z.of_nat 36). apply (shz_of_zero_run m' OS 36); [clear - O16; Z.div_mod_to_equations; lia| lia|].
    eapply bytes_at_agree; [exact SHZ0|]. apply (agree_of_munch _ _ _ _ MU'). intros x Hx. rewrite repeat_length in Hx. cbn [outside]. unfold shad, SHB in *.
    clear - Hx OSLO LSP OSH OF FD8 F0 O0 OSELF. split; [| split; [| split; [| exact I]]]; Z.div_mod_to_equations; lia. }

  assert (CPR : forall m', munch [(S - 112, S - 104); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m m' -> wmono bsegs m m' ->
            ov_read_bytes bsegs m' (wa CP) 1 = Some [Z_to_bv 8 c] /\ ov_read_bytes bsegs m' (wa (CP / 8 + 2147450880)) 1 = Some [b]).
  { intros m' MU' _. split.
    - assert (X : bytes_at bsegs m' CP [Z_to_bv 8 c]).
      { eapply bytes_at_agree; [exact CB1|]. apply (agree_of_munch _ _ _ _ MU'). intros x Hx. cbn [length] in Hx. cbn [outside].
        clear - Hx CF CS CSH LSP. repeat split; try exact I; lia. }
      pose proof (bytes_at_read bsegs m' _ _ 0 1 X ltac:(lia) ltac:(cbn; lia)) as R. rewrite Z.add_0_r in R. exact R.
    - assert (X : bytes_at bsegs m' (CP / 8 + 2147450880) [b]).
      { eapply bytes_at_agree; [exact CSB|]. apply (agree_of_munch _ _ _ _ MU'). intros x Hx. cbn [length] in Hx. cbn [outside].
        clear - Hx CF CS LSP LOW CHI C0 FHIf F0 F8. repeat split; try exact I; Z.div_mod_to_equations; lia. }
      pose proof (bytes_at_read bsegs m' _ _ 0 1 X ltac:(lia) ltac:(cbn; lia)) as R. rewrite Z.add_0_r in R. exact R. }
  change (id (bytes_at bsegs m (OS / 8 + 2147450880) (repeat z8 36))) in SHZ0. change (id (bytes_at bsegs m CP [Z_to_bv 8 c])) in CB1.
  change (id (bytes_at bsegs m (CP / 8 + 2147450880) [b])) in CSB.
  do 3 zstep.
  zstep. if_cases K0; zify_cond K0; [| exfalso; lia].
  do 3 zstep. zstep. rewrite shr3_div. do 4 zstep.
  do 3 lstep.
  zstep. zstep.
  do 9 ls.
  zstep. rewrite shr3_div. zstep.
  shz_pose SHZ (OS + 128). zstep. shz_norm.
  lstep.
  zstep. if_false.
  zstep.
  zstep.
  zstep. rewrite ?shr3_div. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (SHV1 : shz mm 0x168e08 24) by (apply (shz_of_acc mm 0x168e08 24); [apply (acc_agreeP m mm _ _ VTA); apply (agree_of_munch _ _ _ _ MU);
      intros x Hx; unfold shad, SHB in Hx; cbn [outside]; clear - Hx FD8 LSP LOW FHIf FHIo; lia| reflexivity| lia]) end.
  pose proof (SHV1 0x168e18 ltac:(lia)) as RD. change (0x168e18 / 8 + 2147450880) with 2147635651 in RD.
  zstep. shz_norm. zstep. if_false.
  zstep.
  zstep.    replace (OS + 128 + 8) with (OS + 136) by lia.
  astep. replace ((OS + 136) mod 8) with 0 by (clear - O16; Z.div_mod_to_equations; lia).
  zstep. if_false.
  zstep. rewrite shr3_div. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (CPR mm MU WM) as [CRD1 CRD2] end.
  zstep.

  lazymatch goal with |- evt _ _ (MS ?rr ?FF ?pc ?fx ?oo ?mm ?rom) =>
  assert (DIA : forall K : machine_state -> Prop,
    (forall a0' a2' : word,
      evt bsegs K (MS (mkR (wz 0xb2090) (wz (S - 160)) gp tp t0 t1 t2 (wz S) (wz (S - 160)) a0' (wz (OS + 136)) a2' (wz (-13)) a4 a5 a6 a7
                       (wz (OS + 128)) (wz f) s4 (wz CP) s6 s7 (wz (f / 8 + 2147450880)) (wz f) (wz 2147450880) s11 t3 t4 t5 t6)
                   F (wz 0xb2164) fc None mm (seg_rom bsegs))) ->
    evt bsegs K (MS rr FF pc fx oo mm rom)) end.
  { intros K HK. destruct (sh_ok_cases b CP SOK) as [-> | (k & -> & K1 & K2)].
    - cbv beta. rewrite sxb_z8. zstep. if_false. apply HK.
    - rewrite (sxb_small7 k) by lia. zstep. if_lia.
      astep.
      zstep. if_lia.
      apply HK. }
  apply DIA. clear DIA CRD2. intros a0' a2'.
  zstep.    replace (OS + 136 + 144) with (OS + 280) by lia.
  zstep. rewrite shr3_div. zstep.
  shz_pose SHZ (OS + 280). zstep. shz_norm.
  astep.
  zstep. if_false.
  zstep.    replace (OS + 136 + 147) with (OS + 283) by lia.
  zstep. rewrite shr3_div. zstep.
  shz_pose SHZ (OS + 283). zstep. shz_norm.
  zstep. if_false.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption| unfold sf_sh8; cbn [map app repeat]; eassumption].
Qed.

Local Ltac segA2_tac SHZ OS :=
  do 4 zstep;
  do 6 zstep;
  zstep; zstep;
  zstep; if_true;
  shz_pose SHZ (OS + 280); zstep; shz_norm; zstep; if_false;
  zstep; rewrite shr3_div; zstep;
  shz_pose SHZ (OS + 283); zstep; shz_norm; zstep; if_false;
  do 4 ls;
  do 2 zstep; lstep;
  zstep; if_false;
  zstep; do 8 ls.

Lemma sf_segA2 : forall (S f OS CP c fill lo : Z) (gp tp t0 t1 t2 a4 a6 a7 s6 s7 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < f -> f + 64 <= lo -> 0xd9c00 <= f / 8 -> f / 8 + 2147450880 + 8 <= lo -> (f + 64 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 8 <= f) ->
  0x6ce000 <= OS -> OS + 288 <= lo -> OS mod 16 = 0 -> OS / 8 + 2147450880 + 37 <= lo ->
  (OS + 288 <= f \/ f + 64 <= OS) -> (f + 64 <= OS / 8 + 2147450880 \/ (OS + 288) / 8 + 2147450880 <= f) ->
  (OS + 288 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 8 <= OS) -> (OS + 288 <= OS / 8 + 2147450880 \/ OS / 8 + 2147450880 + 37 <= OS) ->
  0x7fff7f800000 <= lo -> lo <= S - 160 -> S < 2^63 -> 0 <= c < 256 -> (fill = 0x20 \/ fill = 0x30) -> 0 < CP < 2^64 ->
  bytes_at bsegs m (OS / 8 + 2147450880) (repeat z8 36) ->
  rw_cells bsegs m (OS + 280) [C1 (Z_to_bv 8 fill); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m f [C8 (wz 0x41b58ab3); C8 (wz 0x1845f); C8 (wz 0xb201c)] ->
  rw_cells bsegs m (f / 8 + 2147450880) (map C1 sf_sh8) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a3' a4' : word) (m1 : mem),
      ms = MS (mkR (wz 0xb2090) (wz (S - 160)) gp tp t0 t1 t2 (wz S) (wz (S - 160)) (wz (-11)) (wz (OS + 136)) (wz (-1)) a3' a4' (wz c) a6 a7
                   (wz (OS + 128)) (wz f) (wz (OS + 280)) (wz (OS + 283)) s6 s7 (wz (f / 8 + 2147450880)) (wz f) (wz 2147450880) (wz ((OS + 280) / 8 + 2147450880)) t3 t4 t5 t6)
              F (wz 0xb22c4) fc None m1 (seg_rom bsegs)
      /\ munch [(OS + 280, OS + 284); (f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (OS + 280) [C1 (Z_to_bv 8 c); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
      /\ rw_cells bsegs m1 f [C8 (wz 0x45e0360e); C8 (wz 0x1845f); C8 (wz 0xb201c)]
      /\ rw_cells bsegs m1 (f / 8 + 2147450880) (map C1 f5x8))
    (MS (mkR (wz 0xb2090) (wz (S - 160)) gp tp t0 t1 t2 (wz S) (wz (S - 160)) (wz (OS + 283)) (wz (OS + 136)) (wz 0) (wz (-13)) a4 (wz c) a6 a7
             (wz (OS + 128)) (wz f) (wz (OS + 280)) (wz CP) s6 s7 (wz (f / 8 + 2147450880)) (wz f) (wz 2147450880) (wz ((OS + 280) / 8 + 2147450880)) t3 t4 t5 t6)
        F (wz 0xb2190) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FLO FD8 SLO SEP O0 OLO O16 OSLO OF OSH OSH2 OSELF LOW LSP SPH RC HFL CPR SHZ0 FIL FH FS MI.
  unfold sf_sh8 in FS. cbn [map app repeat] in FS.
  pose proof (munch_refl [(OS + 280, OS + 284); (f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (Z_to_bv 64 (OS + 280)) = OS + 280) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (ESO : bv_unsigned (Z_to_bv 64 ((OS + 280) / 8 + 2147450880)) = (OS + 280) / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (SHZ : forall m', munch [(OS + 280, OS + 284); (f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 8)] m m' -> wmono bsegs m m' -> shz m' OS 288).
  { intros m' MU' _. change 288 with (8 * Z.of_nat 36). apply (shz_of_zero_run m' OS 36); [clear - O16; Z.div_mod_to_equations; lia| lia|].
    eapply bytes_at_agree; [exact SHZ0|]. apply (agree_of_munch _ _ _ _ MU'). intros x Hx. rewrite repeat_length in Hx. cbn [outside]. unfold shad, SHB in *.
    clear - Hx OSLO LSP OSH OSH2 OF FD8 F0 O0 OSELF. split; [| split; [| split; [| exact I]]]; Z.div_mod_to_equations; lia. }
  change (id (bytes_at bsegs m (OS / 8 + 2147450880) (repeat z8 36))) in SHZ0.
  destruct HFL as [-> | ->]; segA2_tac SHZ OS.
  all: apply evt_done; eexists _, _, _; split; [cbv delta [mkR]; reflexivity|].
  all: split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]; split; [exact WM|]; split; [eassumption|]; split; [eassumption|].
  all: split; [eassumption| unfold f5x8; cbn [map app repeat]; eassumption].
Qed.

Lemma sf_exit : forall (S f fl lo OS : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 : word) (LC : list cell) F fc (m : mem),
  0 < f -> f + 64 <= lo -> 0 < fl -> fl + 1 <= lo -> 0 <= OS -> OS + 288 <= lo ->
  0x6ce000 <= lo -> lo <= S - 160 -> cells_size LC = 56%nat -> S < 2^63 ->
  stk bsegs m lo (S - 160) -> rw_cells bsegs m (S - 160) LC ->
  rw_cells bsegs m (S - 104) (fa_saved xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11) ->
  ro_cells bsegs m (f + 56) [C8 (Z_to_bv 64 fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem),
      ms = MS (mkR xra (wz S) gp tp t0 t1 t2 xs0 xs1 (wz (OS + 128)) a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6)
              F (ret_pc xra) fc None m' (seg_rom bsegs)
      /\ munch [(fl, fl + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo S /\ rw_cells bsegs m' fl [C1 (Z_to_bv 8 0)])
    (MS (mkR (wz 0xb2090) (wz (S - 160)) gp tp t0 t1 t2 (wz S) (wz (S - 160)) a0 a1 a2 a3 a4 a5 a6 a7 (wz (OS + 128)) (wz f) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xb22c4) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FLO FL0 FLLO O0 OLO GLO LSP SZ SPH ST FRl FRs FW FLC MI.
  unfold fa_saved in *.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EFL : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  assert (EUS : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  zstep. ls. zstep. zstep. zstep.
  replace (S - 104) with (S + -104) in FRs by lia.
  do 13 zstep. zstep.
  replace (S + -104) with (S - 104) in FRs by lia.
  pose proof (stk_release bsegs _ _ _ _ ST FRl ltac:(lia)) as ST1. rewrite SZ in ST1. change (Z.of_nat 56%nat) with 56 in ST1.
  replace (S - 160 + 56) with (S - 104) in ST1 by lia.
  pose proof (stk_release bsegs _ _ _ _ ST1 FRs ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
  replace (S - 104 + Z.of_nat 104) with S in ST3 by lia.
  zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST3| eassumption].
Qed.

Lemma le4_byte : forall v, 0 <= v < 256 -> le4 (wz v) = [Z_to_bv 8 v; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Proof.
  intros v Hv. unfold le4. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite (Z.shiftr_div_pow2 v 8) by lia. rewrite (Z.div_small v (2^8)) by lia. reflexivity.
Qed.
Lemma fill4_split : forall m A v, 0 <= v < 256 -> rw_cells bsegs m A [C4 (wz v)] -> rw_cells bsegs m A [C1 (Z_to_bv 8 v); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof. intros m A v Hv H. eapply rw_cells_retype; [exact H| cbn; tauto| cbn [cells_bytes cbytes app]; rewrite le4_byte by lia; reflexivity| reflexivity]. Qed.
Lemma fill4_join : forall m A v, 0 <= v < 256 -> rw_cells bsegs m A [C1 (Z_to_bv 8 v); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] -> rw_cells bsegs m A [C4 (wz v)].
Proof. intros m A v Hv H. eapply rw_cells_retype; [exact H| cbn; tauto| cbn [cells_bytes cbytes app]; rewrite le4_byte by lia; reflexivity| reflexivity]. Qed.

Section Lift.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis DCC : forall Σ m, ART RT Σ m -> el_dccA m.

Lemma sf_smalloc0 : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  tp = Z_to_bv 64 0x6abde8 ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  (rt_frames RT Σ = [] -> bv_unsigned sp + 0xa0 <= rt_sp0 RT Σ) ->
  (forall (Σ' : rts RT) (f : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ' (bv_unsigned sp) lo m m' -> rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m' ->
     wr_at bsegs m' f (fs_size 0 - 8) -> wr_at bsegs m' (shad f) (fs_size 0 / 8) ->
     rt_frames RT Σ' = (f, 0%nat) :: rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ' = rt_credit RT Σ - 1 -> 0 < f -> f mod 64 = 0 -> f + fs_size 0 < USTACK_TOP ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 f) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 (e_stack_malloc 0)) fc None m (seg_rom bsegs)).
Proof using RC FDO MST.
  intros until lo. intros ETP FRL CR ART0 MI0 COK TOPC HK.
  eapply (aevt_icall RT PMc).
  - exact (rc_stack_malloc_0 RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lo FDO MST ltac:(left; reflexivity) ETP FRL CR ART0 MI0 COK TOPC).
  - intros c (Σ' & f & HQ & E1 & E2 & E3 & E4 & F1 & F2 & F3). eexists Σ', _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & W1 & W2).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ' K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK Σ' f q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR W1 W2 E1 E2 E3 E4 F1 F2 F3).
Qed.
Local Ltac ul := unfold EL_SETFILL_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem setfill_okA : setfill_cpsA RT PMc.
Proof using AF RC FDO MST DCC.
  unfold setfill_cpsA. intros until m. intros FDO' MST' INF FLO FHI AL16 OX HFL HULL CPB RC8 CPL CPH ART0 MI ST LOW LOR SPT Q32 FRB CRB HK.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & _ & FLIVE).
  pose proof (af_frames_align RT AF Σ m fO kO ART0 INF) as (_ & FSEG).
  pose proof (proj2 (af_fshadow_apart RT AF Σ m fO kO ART0 INF) fO kO INF) as FSELF.
  pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & _ & _ & SHT).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W0.
  pose proof (af_frames_hi RT AF Σ m fO kO ART0 INF) as FHIo. unfold shad, SHB in SHT, FSELF.
  unfold EL_SETFILL_STACK_A in *. unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *. remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (US : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
  assert (US1 : bv_unsigned (wz (q - 160)) = q - 160) by (apply unsigned_lit; lia).
  destruct HULL as [_ SHBY]. destruct OX as (pb & pp & ep & dum & j148 & j284 & OSC & PI).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (sf_walk0 q lo (OS + 128) CP ra gp (wz TPV_A) t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m ST);
                   [lia| lia| lia| exact Q32| lia| lia| exact (af_client_consts RT AF Σ m ART0)| exact MI]|].
  cbv beta. intros ms1 (m1 & a1' & a2' & j1 & j2 & j3 & j4 & j5 & j6 & -> & MU1 & WM1 & MI1 & ST1 & FRl1 & FRs1). apply evt_done.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (q - 160) ART0 ltac:(ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (PRES1 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> m1 a = m a).
  { intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. destruct (aclient_split_c RT AF Σ m q _ ART0 Ha); ul. }

  unfold entry_st.
  eapply (sf_smalloc0 Σ); [reflexivity| exact FRB| lia| exact ART1| exact MI1| | intros Efr0; exfalso; rewrite Efr0 in INF; exact INF|].
  { unfold call_ok. rewrite US1. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul| clear - Q32; Z.div_mod_to_equations; lia]. }
  intros Σ1 f w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 F1 m2 (ART2 & MI2 & WM2 & ST2) PRES2 WRF WRS FRS1 LV1 SP1 CR1 FPOS F64 FTOP1.
  rewrite US1 in ST2, PRES2. rewrite (ret_pc_even 0xb2090) by lia.
  change (fs_size 0) with 64 in *. change (64 / 8) with 8 in WRS. replace (64 - 8) with 56 in WRF by reflexivity.
  assert (INF1 : In (f, 0%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  assert (INO1 : In (fO, kO) (rt_frames RT Σ1)) by (rewrite FRS1; right; exact INF).
  pose proof (fframe_ranges RT AF Σ1 m2 f 0 ART2 INF1) as (_ & FR1' & _ & SHB1 & SHT1).
  pose proof (af_fshadow_apart RT AF Σ1 m2 f 0 ART2 INF1) as (FSL1 & FSF1). pose proof (FSF1 f 0%nat INF1) as FSELF1. pose proof (FSF1 fO kO INO1) as FSO1.
  pose proof (proj2 (af_fshadow_apart RT AF Σ1 m2 fO kO ART2 INO1) f 0%nat INF1) as OSF1.
  pose proof (af_frames_align RT AF Σ1 m2 f 0 ART2 INF1) as (_ & FSEG1).
  pose proof (af_frames_disj RT AF Σ1 m2 f 0 fO kO [] (rt_frames RT Σ) ART2 FRS1 INF) as FDJ.
  change (fs_size 0) with 64 in *. rewrite <- EFSZ in *. rewrite SP1 in FR1', SHT1.
  assert (SHF : shad (f + 64) = shad f + 8) by (unfold shad; Z.div_mod_to_equations; lia).
  rewrite SHF in *. unfold shad, SHB in SHB1, SHT1, FSELF1, FSL1, FSO1, OSF1, WRS.
  assert (FD0 : 0 <= f / 8) by (apply Z.div_pos; lia).
  pose proof (af_sp0_win RT AF Σ1 m2 ART2) as SP0W. rewrite SP1 in SP0W.
  pose proof (af_frames_hi RT AF Σ1 m2 f 0%nat ART2 INF1) as FHI1. change (fs_size 0) with 64 in FHI1.
  assert (FD8 : 0xd9c00 <= f / 8) by (unfold SEGTOP_A in FSEG1; clear - FSEG1; Z.div_mod_to_equations; lia).
  assert (LOW' : 0x7fff7f800000 <= lo) by (clear - SP0W LOW; lia). unfold SEGTOP_A, STACK_WIN, USTACK_TOP in *.

  assert (AG02 : forall (P : Z -> Prop), (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) q x /\ ~ (q - 160 <= x < q)) -> agree_on P m m2).
  { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. rewrite (PRES2 a); [exact (PRES1 a H1)|].
    apply (aclient_mono _ _ _ _ _ _ _ H1); [auto| auto| lia]. }
  assert (AG12 : forall (P : Z -> Prop), (forall x, P x -> q - 160 <= x < q) -> agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2. left. pose proof (HP _ Ha). ul. }
  assert (CL : forall sp' x, (fO <= x < fO + FSZ - 8) \/ (fO / 8 + 2147450880 <= x < (fO + FSZ) / 8 + 2147450880) ->
            aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
  { intros sp' x [H|H]; [right; right; right; left| do 4 right]; [exists fO, kO; rewrite <- EFSZ; split; [exact INF| exact H]
      | exists fO, kO; rewrite <- EFSZ; split; [exact INF| unfold shad, SHB; exact H]]. }
  assert (FRl2 : rw_cells bsegs m2 (q - 160) [C8 (wz 0); CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6]).
  { eapply rw_cells_agree_nw; [exact FRl1|]. apply AG12. intros x Hx. cbn [cells_size csize Nat.add] in Hx. lia. }
  assert (FRs2 : rw_cells bsegs m2 (q - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply rw_cells_agree_nw; [exact FRs1|]. apply AG12. intros x Hx. unfold fa_saved in Hx. cbn [cells_size csize Nat.add] in Hx. lia. }
  assert (OSC2 : rw_cells bsegs m2 OS (os_cellsX OS pb (wz pp) (wz ep) FL W fill dum j148 j284)).
  { eapply rw_cells_agree_nw; [exact OSC|]. apply AG02. intros x Hx. rewrite os_cellsX_size in Hx.
    split; [apply (CL q); left; lia| clear - Hx FHI FTOP LOW LOR; lia]. }
  assert (SHBY2 : bytes_at bsegs m2 (shad OS) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHBY|]. apply AG02. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in *.
    split; [apply (CL q); right| clear - Hx FLO FHI SHT LOW LOR]; Z.div_mod_to_equations; lia. }
  assert (CPB2 : bytes_at bsegs m2 CP [Z_to_bv 8 c]).
  { eapply bytes_at_agree; [exact CPB|]. apply AG02. intros x Hx. cbn [length] in Hx. split; [left; ul| lia]. }
  assert (PRES2' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> m2 a = m a).
  { intros a Ha. apply AG02 with (P := fun x => x = bv_unsigned a); [| reflexivity]. intros x ->. split; [exact Ha|].
    destruct (aclient_split_c RT AF Σ m q _ ART0 Ha); ul. }
  clear PRES1 PRES2 AG12 AG02 FRl1 FRs1 ST1 MI1 ART1 MU1 WM1 OSC SHBY CPB.

  pose proof (af_acc_stack RT AF Σ1 m2 CP 1 ART2 ltac:(rewrite SP1; ul) ltac:(ul)) as ACP.
  destruct (ACP 0 ltac:(lia)) as (b & CSB2 & SOK2). rewrite Z.add_0_r in CSB2, SOK2. unfold shad, SHB in CSB2. clear ACP.
  pose proof (proj1 (vt_accA RT AF Σ1 m2 ART2)) as VTA2. unfold PJ_NULSB_VT_A in VTA2.
  pose proof (DCC Σ1 m2 ART2) as (VT2 & _).

  destruct (wr_at_rw_CB m2 f 24 (wr_at_sub m2 f 56 f 24 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jH & FH2).
  change (Z.to_nat 24) with 24%nat in FH2.
  apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FH2; [| reflexivity]. cbn [mk_CB_cells app] in FH2. forget_junk FH2.
  destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 8 WRS ltac:(lia)) as (jS & FS2).
  change (Z.to_nat 8) with 8%nat in FS2.
  apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] [1;1;1;1;1;1;1;1]%nat) in FS2; [| reflexivity]. cbn [mk_CB_cells app] in FS2.
  lazymatch type of FS2 with rw_cells _ _ _ ?cs =>
    let ls := eval cbv in (map (fun c => match c with CB _ l => l | _ => [] end) cs) in
    change (rw_cells bsegs m2 (f / 8 + 2147450880) (map (fun l => CB 1 l) ls)) in FS2; set (lS := ls) in FS2;
    assert (LS : length lS = 8%nat) by reflexivity; clearbody lS
  end.

  assert (CSEP : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> ~ (f <= a < f + 56) /\ ~ (f / 8 + 2147450880 <= a < f / 8 + 2147450880 + 8)).
  { intros a Ha. destruct Ha as [H|[H|[H|[H|H]]]].
    - clear - H FR1' SHT1 LOW LOR. unfold USTACK_TOP in H. split; intros X; lia.
    - pose proof (client_static_range _ H) as R. unfold SEGTOP_A in R. clear - R FSEG1 SHB1. split; intros X; lia.
    - destruct H as (p & k & Hin & Hr). pose proof (proj2 (proj2 (proj2 (af_frames_range RT AF Σ1 m2 f 0%nat ART2 INF1))) p k ltac:(rewrite LV1; exact Hin)) as Y1.
      pose proof (FSL1 p k ltac:(rewrite LV1; exact Hin)) as Y2. change (fs_size 0) with 64 in Y1. clear - Hr Y1 Y2. split; intros X; lia.
    - destruct H as (f9 & k9 & Hin & Hr). pose proof (af_frames_disj RT AF Σ1 m2 f 0 f9 k9 [] (rt_frames RT Σ) ART2 FRS1 Hin) as Y1.
      pose proof (FSF1 f9 k9 ltac:(rewrite FRS1; right; exact Hin)) as Y2. unfold shad, SHB in Y2. change (fs_size 0) with 64 in Y1.
      pose proof (fframe_ranges RT AF Σ m f9 k9 ART0 Hin) as (_ & _ & Y3 & _). clear - Hr Y1 Y2 Y3. split; intros X; lia.
    - destruct H as (f9 & k9 & Hin & Hr). pose proof (proj2 (af_fshadow_apart RT AF Σ1 m2 f9 k9 ART2 ltac:(rewrite FRS1; right; exact Hin)) f 0%nat INF1) as Y1.
      pose proof (af_frames_disj RT AF Σ1 m2 f 0 f9 k9 [] (rt_frames RT Σ) ART2 FRS1 Hin) as Y2. change (fs_size 0) with 64 in Y1, Y2.
      unfold shad, SHB in Hr, Y1. clear - Hr Y1 Y2 FD0. split; intros X; Z.div_mod_to_equations; lia. }

  pose proof (proj1 (os_cellsX_parts m2 OS pb (wz pp) (wz ep) FL W fill dum j148 j284) OSC2) as (SB2 & V128_2 & IOS2). clear OSC2.
  assert (XOSLO : OS / 8 + 2147450880 + 37 <= lo) by (clear - FLO FHI SHT LOW LOR; Z.div_mod_to_equations; lia).
  assert (XOF : OS + 288 <= f \/ f + 64 <= OS) by (clear - FDJ FLO FHI; lia).
  assert (XOSH : f + 64 <= OS / 8 + 2147450880 \/ (OS + 288) / 8 + 2147450880 <= f) by (clear - OSF1 FLO FHI; Z.div_mod_to_equations; lia).
  assert (XOSH2 : OS + 288 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 8 <= OS) by (clear - FSO1 FLO FHI; lia).
  assert (XOSELF : OS + 288 <= OS / 8 + 2147450880 \/ OS / 8 + 2147450880 + 37 <= OS) by (clear - FSELF FLO FHI; Z.div_mod_to_equations; lia).
  assert (XFHIo : OS + 288 <= 0x7fff7000 \/ 0x10007fff8000 <= OS) by (clear - FHIo FLO FHI F0; lia).
  assert (XCF : CP + 1 <= f \/ f + 64 <= CP) by (right; clear - FR1' LOW LOR CPL; lia).
  assert (XCO : CP + 1 <= OS \/ OS + 288 <= CP) by (right; clear - FTOP FHI LOW LOR CPL FLO; lia).
  assert (XCSH : CP + 1 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 8 <= CP) by (right; clear - SHT1 LOW LOR CPL; lia).

  apply (aevt_evt RT AF PMc MST). unfold SHB. unfold shad, SHB in SHBY2.
  lazymatch type of FH2 with rw_cells _ _ _ [CB 8 ?h0; CB 8 ?h1; CB 8 ?h2] =>
  eapply evt_cut; [eapply (sf_segA1 q f OS CP c lo b gp (wz TPV_A) w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 s3 s4 s6 s7 s8 s9 s11 w3 w4 w5 w6 j1 j2 j3 j4 j5 j6 h0 h1 h2 lS F1 fc m2 LS);
                   [ lia| clear - F64; Z.div_mod_to_equations; lia| lia| exact FD8| lia| exact FSELF1| lia| lia| exact AL16| exact XOSLO| exact XOF| exact XOSH| exact XOSH2| exact XOSELF
                   | exact LOW'| lia| lia| exact FHI1| exact XFHIo| lia| lia| exact XCF| exact XCO| right; exact CPL| exact XCSH| exact RC8
                   | exact SHBY2| exact VTA2| exact CPB2| exact CSB2| exact SOK2| exact FRl2| exact FH2| exact FS2| exact V128_2| exact VT2| exact MI2]|] end.
  cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & FRl3 & FH3 & FS3). apply evt_done.
  assert (AG3 : forall P : Z -> Prop, (forall x, P x -> ~ (q - 112 <= x < q - 104) /\ ~ (f <= x < f + 24) /\ ~ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 8)) -> agree_on P m2 m3).
  { intros P HP a Ha. apply MU3. cbn [outside]. destruct (HP _ Ha) as (H1 & H2 & H3). split; [exact H1| split; [exact H2| split; [exact H3| exact I]]]. }
  assert (ART3 : ART RT Σ1 m3).
  { apply (art_client_write RT AF Σ1 m2 m3 (q - 160) ART2 ltac:(ul)); [| exact WM3]. intros a Ha. apply MU3. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|].
    split; [intros Hin; apply Ha; right; right; right; left; exists f, 0%nat; split; [exact INF1| change (fs_size 0) with 64; lia]|].
    split; [| exact I]. intros Hin; apply Ha. do 4 right. exists f, 0%nat. split; [exact INF1|]. unfold shad, SHB. change (fs_size 0) with 64. clear - Hin FD0. Z.div_mod_to_equations. lia. }
  assert (PRES3 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> m3 a = m a).
  { intros a Ha. rewrite <- (PRES2' a Ha). apply MU3. pose proof (CSEP _ Ha) as [C1 C2]. destruct (aclient_split_c RT AF Σ m q _ ART0 Ha) as [X|X]; cbn [outside];
      (split; [| split; [clear - C1; lia| split; [exact C2| exact I]]]); clear - X LOW LOR; ul. }
  Local Ltac by3 H AG := eapply rw_cells_agree_nw; [exact H|]; apply AG; intros x Hx; cbn [sb_cellsX ios_cellsX fa_saved cells_size csize Nat.add] in Hx.
  assert (FRs3 : rw_cells bsegs m3 (q - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) by (by3 FRs2 AG3; clear - Hx FR1' SHT1 LOW LOR; lia).
  assert (ST3 : stk bsegs m3 lo (q - 160)) by (eapply stk_agree_nw; [exact ST2|]; apply AG3; intros x Hx; cbv beta in Hx; clear - Hx FR1' SHT1 LOW LOR; lia).
  assert (SB3 : rw_cells bsegs m3 OS (sb_cellsX pb (wz pp) (wz ep) dum)) by (by3 SB2 AG3; clear - Hx FLO FHI FTOP LOW LOR FDJ FSO1; lia).
  assert (V128_3 : rw_cells bsegs m3 (OS + 128) [C8 (wz 0x168e30)]) by (by3 V128_2 AG3; clear - Hx FLO FHI FTOP LOW LOR FDJ FSO1; lia).
  assert (IOS3 : rw_cells bsegs m3 (OS + 136) (ios_cellsX OS 0x168e58 FL W fill j148 j284)) by (by3 IOS2 AG3; clear - Hx FLO FHI FTOP LOW LOR FDJ FSO1; lia).
  assert (SHBY3 : bytes_at bsegs m3 (OS / 8 + 2147450880) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHBY2|]. apply AG3. intros x Hx. rewrite repeat_length in Hx.
    clear - Hx FLO FHI F0 SHT LOW LOR OSF1 FDJ. split; [| split]; Z.div_mod_to_equations; lia. }
  clear AG3 MU3 WM3 FRl2 FH2 FS2 FRs2 ST2 SB2 V128_2 IOS2 SHBY2 MI2 WM2 CPB2 CSB2 SOK2.

  unfold ios_cellsX in IOS3. takeZ IOS3 20%nat (OS + 280)%Z IOSa. takeZ IOS3 1%nat (OS + 284)%Z FILc. rename IOS3 into J284.
  apply (fill4_split m3 (OS + 280) fill ltac:(clear - HFL; lia)) in FILc.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (sf_segA2 q f OS CP c fill lo gp (wz TPV_A) w0 w1 w2 c4 c6 c7 s6 s7 w3 w4 w5 w6 F1 fc m3);
                   [ lia| lia| exact FD8| lia| exact FSELF1| lia| lia| exact AL16| exact XOSLO| exact XOF| exact XOSH| exact XOSH2| exact XOSELF
                   | exact LOW'| lia| lia| exact RC8| exact HFL| lia| exact SHBY3| exact FILc| exact FH3| exact FS3| exact MI3]|].
  cbv beta. intros ms4 (a3' & a4' & m4 & -> & MU4 & WM4 & MI4 & FIL4 & FH4 & FS4). apply evt_done.
  assert (AG4 : forall P : Z -> Prop, (forall x, P x -> ~ (OS + 280 <= x < OS + 284) /\ ~ (f <= x < f + 8) /\ ~ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 8)) -> agree_on P m3 m4).
  { intros P HP a Ha. apply MU4. cbn [outside]. destruct (HP _ Ha) as (H1 & H2 & H3). split; [exact H1| split; [exact H2| split; [exact H3| exact I]]]. }
  assert (ART4 : ART RT Σ1 m4).
  { apply (art_client_write RT AF Σ1 m3 m4 (q - 160) ART3 ltac:(ul)); [| exact WM4]. intros a Ha. apply MU4. cbn [outside].
    split; [intros Hin; apply Ha; right; right; right; left; exists fO, kO; split; [exact INO1| lia]|].
    split; [intros Hin; apply Ha; right; right; right; left; exists f, 0%nat; split; [exact INF1| change (fs_size 0) with 64; lia]|].
    split; [| exact I]. intros Hin; apply Ha. do 4 right. exists f, 0%nat. split; [exact INF1|]. unfold shad, SHB. change (fs_size 0) with 64. clear - Hin FD0. Z.div_mod_to_equations. lia. }
  Local Ltac by4 H AG := eapply rw_cells_agree_nw; [exact H|]; apply AG; intros x Hx; cbn [sb_cellsX fa_saved cells_size csize Nat.add] in Hx.
  assert (FRl4 : rw_cells bsegs m4 (q - 160) [C8 (wz 0); CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; C8 (wz f)]) by (by4 FRl3 AG4; clear - Hx FLO FHI FTOP LOW LOR FR1' SHT1; lia).
  assert (FRs4 : rw_cells bsegs m4 (q - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) by (by4 FRs3 AG4; clear - Hx FLO FHI FTOP LOW LOR FR1' SHT1; lia).
  assert (ST4 : stk bsegs m4 lo (q - 160)) by (eapply stk_agree_nw; [exact ST3|]; apply AG4; intros x Hx; cbv beta in Hx; clear - Hx FLO FHI FTOP LOW LOR FR1' SHT1; Z.div_mod_to_equations; lia).

  destruct (af_frame_release RT AF Σ1 m4 f 0%nat (rt_frames RT Σ) ART4 FRS1) as (Σ3 & fl & FLC & NAC & FL0 & FLW & FW & REL).
  change (fs_size 0) with 64 in FW. replace (f + 64 - 8) with (f + 56) in FW by lia. rewrite SP1 in FLW.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (sf_exit q f fl lo OS gp (wz TPV_A) w0 w1 w2 (wz (-11)) (wz (OS + 136)) (wz (-1)) a3' a4' (wz c) c6 c7 _ _ s6 s7 _ _ _ _ w3 w4 w5 w6
                             ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 [C8 (wz 0); CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; C8 (wz f)] F1 fc m4);
                   [lia| lia| exact FL0| ul| lia| lia| lia| lia| reflexivity| lia| exact ST4| exact FRl4| exact FRs4| exact FW| exact FLC| exact MI4]|].
  cbv beta. intros ms5 (m5 & -> & MU5 & WM5 & MI5 & ST5 & FLC5).
  destruct (REL m5 MU5 WM5 FLC5) as (ART5 & FRS5 & LV5 & SP5 & CR5 & AL5 & AM5).
  apply evt_done. apply (aevt_switch RT PMc Σ1 Σ3 K _ AL5 AM5).

  assert (AG35 : forall P : Z -> Prop, (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) q x /\ ~ (OS + 280 <= x < OS + 284)) -> agree_on P m3 m5).
  { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. pose proof (CSEP _ H1) as [C1 C2]. rewrite (MU5 a), (MU4 a); [reflexivity| |].
    - cbn [outside]. clear - H2 C1 C2. repeat split; try exact I; lia.
    - cbn [outside]. split; [| exact I]. intros E. apply NAC. rewrite LV1, FRS1. replace fl with (bv_unsigned a) by lia.
      destruct H1 as [H|[H|[H|[H|H]]]]; [exfalso; clear - H E FLW LOW LOR; ul| right; left; exact H| right; right; left; exact H
        | right; right; right; left; destruct H as (f9 & k9 & Hin & Hr); exists f9, k9; split; [right; exact Hin| exact Hr]
        | do 4 right; destruct H as (f9 & k9 & Hin & Hr); exists f9, k9; split; [right; exact Hin| exact Hr]]. }
  Local Ltac by5 H AG := eapply rw_cells_agree_nw; [exact H|]; apply AG; intros x Hx; cbn [sb_cellsX fa_saved cells_size csize Nat.add] in Hx.
  assert (SB5 : rw_cells bsegs m5 OS (sb_cellsX pb (wz pp) (wz ep) dum)) by (by5 SB3 AG35; split; [apply (CL q); left; lia| lia]).
  assert (V128_5 : rw_cells bsegs m5 (OS + 128) [C8 (wz 0x168e30)]) by (by5 V128_3 AG35; split; [apply (CL q); left; lia| lia]).
  lazymatch type of IOSa with rw_cells _ _ _ ?cs => assert (IOSa5 : rw_cells bsegs m5 (OS + 136) cs) by (by5 IOSa AG35; split; [apply (CL q); left; lia| lia]) end.
  assert (J284_5 : rw_cells bsegs m5 (OS + 284) [CB 4 j284]) by (by5 J284 AG35; split; [apply (CL q); left; lia| lia]).
  assert (FIL5 : rw_cells bsegs m5 (OS + 280) [C4 (wz c)]).
  { apply (fill4_join m5 (OS + 280) c RC8). eapply rw_cells_agree_nw; [exact FIL4|]. apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [| exact I].
    intros E. apply NAC. replace fl with x by lia. right; right; right; left. exists fO, kO. split; [exact INO1| rewrite <- EFSZ; lia]. }
  assert (SHBY5 : bytes_at bsegs m5 (OS / 8 + 2147450880) (repeat z8 36)).
  { eapply bytes_at_agree; [exact SHBY3|]. apply AG35. intros x Hx. rewrite repeat_length in Hx.
    split; [apply (CL q); right; clear - Hx FLO FHI F0; Z.div_mod_to_equations; lia| clear - Hx FLO FHI F0 FSELF; Z.div_mod_to_equations; lia]. }
  glueZ FIL5 J284_5. glueZ IOSa5 FIL5.
  assert (OSC5 : rw_cells bsegs m5 OS (os_cellsX OS pb (wz pp) (wz ep) FL W c dum j148 j284)).
  { apply (proj2 (os_cellsX_parts m5 OS pb (wz pp) (wz ep) FL W c dum j148 j284)). split; [exact SB5|]. split; [exact V128_5|]. unfold ios_cellsX. exact IOSa5. }
  eapply (HK Σ3 w0 w1 w2 (wz (OS + 136)) (wz (-1)) a3' a4' (wz c) c6 c7 w3 w4 w5 w6 F1 m5 ART5 MI5 ST5);
    [| | rewrite LV5, LV1; reflexivity| exact FRS5| rewrite SP5, SP1; reflexivity| rewrite CR5, CR1; lia|].
  - exists pb, pp, ep, dum, j148, j284. split; [exact OSC5| exact PI].
  - split; [| unfold shad, SHB; exact SHBY5]. destruct (rw_cells_forget bsegs m5 OS _ OSC5) as (bo5 & H5). rewrite os_cellsX_size in H5. exists bo5. exact H5.
  - intros a Ha Ho. rewrite <- (PRES3 a Ha). apply (AG35 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->. split; [exact Ha|].
    cbn [outside] in Ho. lia.
Qed.
End Lift.
