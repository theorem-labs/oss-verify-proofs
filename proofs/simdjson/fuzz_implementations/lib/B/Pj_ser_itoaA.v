(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame ZBridge SFModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjPjSer SjPjItoa SjPjDig.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface I_lkit D_rlkit
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_fzwA Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_numdefsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_store ::= first [ pj_solve_store0 | pj_store_wr ].
Local Ltac pj_st_eq_leaf ::=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; lia]
  | |- _ => reflexivity
  end.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma it_land_m32d : forall x, 0 <= x < 2^64 -> x mod 16 = 0 ->
  exists dd, (dd = 0 \/ dd = 16) /\ Z.land x 18446744073709551584 = x - dd /\ (x - dd) mod 32 = 0.
Proof.
  intros x Hx X16. exists (x - 32 * (x / 32)). rewrite (land_m32 x Hx).
  split; [Z.div_mod_to_equations; lia|]. split; [lia| Z.div_mod_to_equations; lia].
Qed.

Definition it_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 : word) : list cell :=
  [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition it_shpat : list byte := map (Z_to_bv 8) [-15; -15; -15; -15; 0; 0; 4; -13; -13; -13; -13; -13].

Lemma it_cells_bytes_map_C1 : forall l : list byte, cells_bytes (map C1 l) = l.
Proof. induction l as [|b l IH]; [reflexivity|]. cbn [map cells_bytes cbytes app]. rewrite IH. reflexivity. Qed.
Lemma it_cells_size_map_C1 : forall l : list byte, cells_size (map C1 l) = length l.
Proof. induction l as [|b l IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. reflexivity. Qed.
Lemma it_u8arr_of_C1s : forall (m : mem) A l, rw_cells bsegs m A (map C1 l) -> u8arr bsegs m A l.
Proof.
  intros m A l H. split.
  - pose proof (rw_cells_bytes_at bsegs m A _ H) as B. rewrite it_cells_bytes_map_C1 in B. exact B.
  - eapply rw_cells_wr_at; [exact H|]. rewrite it_cells_size_map_C1. lia.
Qed.

Lemma it_shadow_read : forall (m : mem) (f idx : Z) (rest : list cell),
  rw_cells bsegs m (f / 8 + 2147450880) (map C1 it_shpat ++ rest) -> 8 * (f / 8) = f -> 0 <= f -> 0 <= idx <= 19 ->
  exists b : byte, ov_read_bytes bsegs m (wa (shad (f + 32 + idx))) 1 = Some [b] /\ (idx <= 15 -> b = z8) /\ (16 <= idx -> b = Z_to_bv 8 4).
Proof.
  intros m f idx rest H Ef F0 Hi. apply rw_cells_app in H. destruct H as [H _]. apply it_u8arr_of_C1s in H.
  assert (C : idx / 8 = 0 \/ idx / 8 = 1 \/ (idx / 8 = 2 /\ 16 <= idx)) by (Z.div_mod_to_equations; lia).
  assert (SH : shad (f + 32 + idx) = f / 8 + 2147450880 + (4 + idx / 8)) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  rewrite SH. destruct C as [C|[C|[C G]]]; rewrite C.
  - exists z8. split; [eapply (u8arr_read bsegs m _ it_shpat 4 z8); [exact H| reflexivity| lia| reflexivity]|]. split; [reflexivity| intros; exfalso; Z.div_mod_to_equations; lia].
  - exists z8. split; [eapply (u8arr_read bsegs m _ it_shpat 5 z8); [exact H| reflexivity| lia| reflexivity]|]. split; [reflexivity| intros; exfalso; Z.div_mod_to_equations; lia].
  - exists (Z_to_bv 8 4). split; [eapply (u8arr_read bsegs m _ it_shpat 6 (Z_to_bv 8 4)); [exact H| reflexivity| lia| reflexivity]|]. split; [intros; exfalso; lia| reflexivity].
Qed.

Lemma it_acc20 : forall (m : mem) (f : Z) (rest : list cell),
  rw_cells bsegs m (f / 8 + 2147450880) (map C1 it_shpat ++ rest) -> 8 * (f / 8) = f -> 0 <= f -> acc bsegs m (f + 32) 20.
Proof.
  intros m f rest H Ef F0 i Hi. apply rw_cells_app in H. destruct H as [H _]. apply it_u8arr_of_C1s in H. destruct H as [HB _].
  assert (C : i / 8 = 0 \/ i / 8 = 1 \/ (i / 8 = 2 /\ i mod 8 < 4)) by (Z.div_mod_to_equations; lia).
  assert (SH : shad (f + 32 + i) = f / 8 + 2147450880 + (4 + i / 8)) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  rewrite SH. destruct C as [C|[C|[C M]]]; rewrite C.
  - exists z8. split; [| left; reflexivity]. change (4 + 0) with (Z.of_nat 4). exact (bytes_at_nth1 bsegs m _ it_shpat 4 z8 HB eq_refl).
  - exists z8. split; [| left; reflexivity]. change (4 + 1) with (Z.of_nat 5). exact (bytes_at_nth1 bsegs m _ it_shpat 5 z8 HB eq_refl).
  - exists (Z_to_bv 8 4). split.
    + change (4 + 2) with (Z.of_nat 6). exact (bytes_at_nth1 bsegs m _ it_shpat 6 _ HB eq_refl).
    + right. change (bv_unsigned (Z_to_bv 8 4)) with 4. split; [lia|].
      replace ((f + 32 + i) mod 8) with (i mod 8) by (Z.div_mod_to_equations; lia). exact M.
Qed.

Section Itoa.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Notation aevt := (aevt RT PMc).

Lemma it_pro1 : forall (pc q lo DST v : Z) (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  (pc = PJ_ITOA_A \/ pc = PJ_UTOA_A) ->
  stk bsegs m lo q -> lo + 112 <= q -> 0x6e0000 <= lo -> q + 16 <= USTACK_TOP -> q mod 16 = 0 -> client_consts m -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (dd : Z) (a1' a2' : word),
      (dd = 0 \/ dd = 16) /\ (q - 96 - dd) mod 32 = 0 /\
      ms = MS (mkR (wz (pc + 100)) (wz (q - 96 - dd)) gp (wz TPV_A) t0 t1 t2 (wz q) (wz (q - 96 - dd)) (wz 96) a1' a2' a3 a4 a5 a6 a7
                   s2 (wz DST) (wz v) s5 s6 (wz 2147450880) s8 s9 s10 s11 t3 t4 t5 t6) F (wz e_stack_malloc_1) fc None m1 (seg_rom bsegs)
      /\ munch [(q - 96, q)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ stk bsegs m1 lo (q - 72) /\ rw_cells bsegs m1 (q - 72) (it_saved ra s0 s1 s2 s3 s4 s5 s6 s7))
    (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz DST) (wz v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz pc) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros HPC ST LO GLO QT Q16 (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold PJ_ITOA_A, PJ_UTOA_A, e_stack_malloc_1, TPV_A, USTACK_TOP, it_saved in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(q - 96, q)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  destruct HPC as [-> | ->].

  all: zstep; carve_frame 96%nat ST;
       (apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [8; 16; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]); cbn [mk_CB_cells app] in FR;
       repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.

  all: lstep; do 9 zstep; zstep; zstep;
       destruct (it_land_m32d (q + -96) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (dd & DD & ELAND & B32); rewrite ELAND.

  all: do 6 zstep; step; rewrite (sx32_small 1) by lia; zstep; zstep; zstep; if_false; zstep; zstep.

  all: lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0; c1] ++ rest) in FR end;
       apply rw_cells_app in FR; destruct FR as [FRl FRs]; cbn [cells_size csize Nat.add] in FRs;
       pose proof (stk_of_rw_cells bsegs _ _ _ FRl) as STl; cbn [cells_size csize Nat.add] in STl;
       pose proof (stk_merge bsegs _ _ _ _ ST STl ltac:(lia)) as ST2;
       replace (q + -96 + Z.of_nat 24) with (q - 72) in FRs, ST2 by lia;
       replace (q + -96 - dd) with (q - 96 - dd) by lia; replace (q + -96 + 96) with q by lia.
  all: apply evt_done; eexists; exists dd; eexists; eexists; split; [exact DD|]; split; [lia|]; split; [cbv delta [mkR]; reflexivity|];
       (split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|]);
       split; [exact WM|]; split; [eassumption|]; split; [exact ST2| exact FRs].
Qed.

Lemma it_hdr : forall (q b f lo DST v : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (h sh : list byte) F fc (m : mem),
  0 < f -> 8 * (f / 8) = f -> (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) -> f + 128 <= lo -> f / 8 + 2147450880 + 16 <= lo ->
  0x6e0000 <= f -> 0x6e0000 <= lo -> lo <= b -> b + 96 <= q -> q + 16 <= USTACK_TOP ->
  stk bsegs m b (q - 72) -> rw_cells bsegs m f [CB 24 h] -> rw_cells bsegs m (f / 8 + 2147450880) [CB 16 sh] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a1' a2' : word) (x12 x13 x14 x15 : list byte),
      ms = MS (mkR (wz 0xb6f90) (wz b) gp (wz TPV_A) t0 t1 t2 (wz q) (wz b) (wz 4) a1' a2' (wz (-13)) (wz (-15)) a5 a6 a7
                   (wz f) (wz DST) (wz v) (wz (f / 8 + 2147450880)) (wz f) (wz 2147450880) s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz 0xb702c) fc None m1 (seg_rom bsegs)
      /\ munch [(b, b + 24); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450896)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ stk bsegs m1 b (q - 72) /\ rw_cells bsegs m1 f [C8 (wz 1102416563); C8 (wz 0x22ef5); C8 (wz 0xb6f2c)]
      /\ rw_cells bsegs m1 (f / 8 + 2147450880)
           [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); CB 1 x12; CB 1 x13; CB 1 x14; CB 1 x15])
    (MS (mkR (wz 0xb6f90) (wz b) gp (wz TPV_A) t0 t1 t2 (wz q) (wz b) (wz f) a1 a2 a3 a4 a5 a6 a7 s2 (wz DST) (wz v) s5 s6 (wz 2147450880) s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xb6f90) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 Ef SHf FLO SFL GF GLO LOB BQ QT STF FH SHC MI.
  unfold TPV_A, USTACK_TOP in *.
  pose proof (munch_refl [(b, b + 24); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450896)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.

  destruct (stk_split bsegs m _ (b + 24) _ STF ltac:(lia)) as [STl GAP].
  destruct (stk_CB bsegs m _ _ STl ltac:(lia)) as (jf & FR). replace (Z.to_nat (b + 24 - b)) with 24%nat in FR by lia.
  apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [16; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?tt] => lazymatch tt with firstn _ _ => idtac end; let j := fresh "j" in set (j := tt) in FR; clearbody j end.

  apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FH; [| reflexivity]. cbn [mk_CB_cells app] in FH.
  repeat match type of FH with context [CB ?k ?tt] => lazymatch tt with firstn _ _ => idtac end; let j := fresh "h" in set (j := tt) in FH; clearbody j end.

  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat) in SHC; [| reflexivity]. cbn [mk_CB_cells app] in SHC.
  repeat match type of SHC with context [CB 1 ?tt] => lazymatch tt with firstn _ _ => idtac end; let j := fresh "z" in set (j := tt) in SHC; clearbody j end.
  assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; lia).

  zstep. step. zstep. step. if_cases K0; zify_cond K0; [clear K0| exfalso; pjnorm_in K0; lia].

  step. zstep. zstep. zstep. zstep. pjnorm. zstep. zstep. zstep. zstep. zstep.

  ls. ls. ls. zstep. zstep.

  do 12 ls.

  pose proof (stk_of_rw_cells bsegs _ _ _ FR) as STl2. cbn [cells_size csize Nat.add] in STl2.
  pose proof (stk_merge bsegs _ _ _ _ STl2 GAP ltac:(lia)) as ST2.
  apply evt_done. eexists. do 6 eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST2|]. split; [exact FH|].
  exact SHC.
Qed.

Section Pieces.
Variables (Σ1 : rts RT) (K : config -> Prop).
Variables (q b f DST lo fN : Z) (kN : nat) (L : list (Z * Z)) (FR : list (Z * nat)) (m0 : mem).
Variables (gp s8 s9 s10 s11 : word) (vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 : word).
Variable fc : bv 32.
Hypothesis F0 : 0 < f.
Hypothesis Ef : 8 * (f / 8) = f.
Hypothesis FLO : f + 128 <= lo.
Hypothesis SFL : f / 8 + 2147450880 + 16 <= lo.
Hypothesis SHf : f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f.
Hypothesis GF : 0x6e0000 <= f.
Hypothesis GLO : 0x6e0000 <= lo.
Hypothesis LOB : lo + RT_STACK <= b.
Hypothesis B16 : b mod 16 = 0.
Hypothesis BQ : b + 96 <= q.
Hypothesis QT : q + 16 <= USTACK_TOP.
Hypothesis D8 : DST mod 8 = 0.
Hypothesis GD : 0x6e0000 <= DST.
Hypothesis DLO : DST + 24 <= lo.
Hypothesis DF : DST + 24 <= f \/ f + 128 <= DST.
Hypothesis DSf : DST + 24 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= DST.
Hypothesis SDf : shad DST + 3 <= f \/ f + 128 <= shad DST.
Hypothesis SDSf : shad DST + 3 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= shad DST.
Hypothesis SDLO : shad DST + 3 <= lo.
Hypothesis SDD : shad DST + 3 <= DST \/ DST + 24 <= shad DST.
Hypothesis FRS1 : rt_frames RT Σ1 = (f, 1%nat) :: FR.
Hypothesis LV1 : rt_live RT Σ1 = L.
Hypothesis SP1 : rt_sp0 RT Σ1 - STACK_WIN <= lo.
Hypothesis INN : In (fN, kN) FR.
Hypothesis DIN : fN <= DST /\ DST + 24 <= fN + fs_size kN - 8.
Hypothesis SDIN : shad fN <= shad DST /\ shad DST + 3 <= shad (fN + fs_size kN).
Hypothesis FRESH : forall a, aclient L FR q a -> ~ (f <= a < f + 128) /\ ~ (f / 8 + 2147450880 <= a < f / 8 + 2147450880 + 16).
Hypothesis CSEP : forall a, aclient L FR q a -> q <= a \/ a < lo.

Notation ITS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xt3 xt4 xt5 xt6 F fc m :=
  (MS (mkR xra (Z_to_bv 64 b) gp (Z_to_bv 64 TPV_A) xt0 xt1 xt2 (Z_to_bv 64 q) (Z_to_bv 64 b) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           (Z_to_bv 64 f) xs3 xs4 (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) s8 s9 s10 s11 xt3 xt4 xt5 xt6)
      F (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).

Definition ITM (m : mem) : Prop :=
  mem_inv bsegs m /\ stk bsegs m lo b /\ stk bsegs m b (q - 72) /\ rw_cells bsegs m (q - 72) (it_saved vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7)
  /\ (exists h0 h1 h2, rw_cells bsegs m f [C8 h0; C8 h1; C8 h2]) /\ stk bsegs m (f + 24) (f + 120)
  /\ (exists x12 x13 x14 x15, rw_cells bsegs m (f / 8 + 2147450880)
        [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); CB 1 x12; CB 1 x13; CB 1 x14; CB 1 x15])
  /\ stk bsegs m DST (DST + 24) /\ bytes_at bsegs m (shad DST) [z8; z8; z8].

Definition PRES (m : mem) : Prop :=
  forall a : word, aclient L FR q (bv_unsigned a) -> ~ (DST <= bv_unsigned a < DST + 24) -> m a = m0 a.

Lemma PRES_mu : forall W m m', PRES m -> munch W m m' -> (forall a, aclient L FR q a -> ~ (DST <= a < DST + 24) -> outside W a) -> PRES m'.
Proof. intros W m m' P MU HW a Ha Hd. rewrite <- (P a Ha Hd). apply MU. apply HW; assumption. Qed.

Lemma ART_mu_it : forall W m m', ART RT Σ1 m -> munch W m m' -> wmono bsegs m m' ->
  (forall a, outside W a \/ (b <= a < q \/ f <= a < f + 120 \/ f / 8 + 2147450880 <= a < f / 8 + 2147450880 + 16 \/ DST <= a < DST + 24)) ->
  ART RT Σ1 m'.
Proof using AF Ef LOB QT SP1 FRS1 INN DIN.
  intros W m m' ART0 MU WM HW.
  apply (art_client_write RT AF Σ1 m m' b ART0); [clear - SP1 LOB; unfold RT_STACK in *; lia| | exact WM].
  intros a Hna. apply MU. destruct (HW (bv_unsigned a)) as [H|H]; [exact H| exfalso; apply Hna].
  destruct H as [H|[H|[H|H]]].
  - left. clear - H QT. unfold USTACK_TOP in *. lia.
  - right; right; right; left. exists f, 1%nat. split; [rewrite FRS1; left; reflexivity| change (fs_size 1) with 128; clear - H; lia].
  - right; right; right; right. exists f, 1%nat. split; [rewrite FRS1; left; reflexivity|]. unfold shad, SHB. change (fs_size 1) with 128.
    replace ((f + 128) / 8) with (f / 8 + 16) by (clear - Ef; Z.div_mod_to_equations; lia). clear - H; lia.
  - right; right; right; left. exists fN, kN. split; [rewrite FRS1; right; exact INN| clear - H DIN; lia].
Qed.

Local Ltac it_open HM :=
  let h0 := fresh "h" in let h1 := fresh "h" in let h2 := fresh "h" in
  let x12 := fresh "x" in let x13 := fresh "x" in let x14 := fresh "x" in let x15 := fresh "x" in
  destruct HM as (MI & ST & STF & FS & (h0 & h1 & h2 & FH) & F3S & (x12 & x13 & x14 & x15 & SHC) & DS & DSH).

Lemma it_rel1 : forall (m : mem) (sg n : Z) (F : bvmap 5 word) (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
  ITM m -> 0 <= sg <= 1 -> 1 <= n -> sg + n <= 20 ->
  evt bsegs (fun ms => exists (m1 : mem) (h1 h2 : word),
      ms = ITS 0xb717c (wz 0xb710c) xt0 xt1 xt2 (wz (DST + sg + n)) (wz (-11)) xa2 xa3 xa4 xa5 xa6 xa7 (wz (DST + sg)) (wz n) xt3 xt4 xt5 xt6 F fc m1
      /\ munch [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450896)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ stk bsegs m1 lo b /\ stk bsegs m1 b (q - 72) /\ rw_cells bsegs m1 (q - 72) (it_saved vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7)
      /\ rw_cells bsegs m1 f [C8 (wz 1172321806); C8 h1; C8 h2] /\ stk bsegs m1 (f + 24) (f + 120)
      /\ rw_cells bsegs m1 (f / 8 + 2147450880) [C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11)); C1 (Z_to_bv 8 (-11))]
      /\ stk bsegs m1 DST (DST + 24) /\ bytes_at bsegs m1 (shad DST) [z8; z8; z8])
    (ITS 0xb710c (wz 0xb710c) xt0 xt1 xt2 (wz (DST + sg)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DST + sg)) (wz n) xt3 xt4 xt5 xt6 F fc m).
Proof using F0 Ef FLO SFL SHf GF GLO LOB BQ QT GD DLO DF DSf SDf SDSf SDLO SDD.
  clear B16 D8 FRS1 LV1 SP1 INN DIN SDIN FRESH CSEP.
  intros m sg n F xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HM HSG HN HSN.
  unfold TPV_A, USTACK_TOP, RT_STACK in *. it_open HM.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450896)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

  zstep. rewrite lnot_mod64 by (clear - GD DLO LOB BQ QT HSG; lia).
  step. if_cases Kc; zify_cond Kc; [exfalso; unfold Z.lnot in Kc; pjnorm_in Kc; clear - Kc GD DLO LOB BQ QT HSG HN HSN; Z.div_mod_to_equations; lia| clear Kc].
  zstep. pjnorm. zstep.

  ls. ls. ls. zstep. zstep. ls. step. if_cases K0; zify_cond K0; [exfalso; pjnorm_in K0; clear - K0 F0; lia| clear K0]. zstep.
  do 16 ls.
  apply evt_done. eexists. eexists. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma it_rel2 : forall (m : mem) (e fl : Z) (F : bvmap 5 word) (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xt3 xt4 xt5 xt6 : word) (h0 h1 h2 : word),
  0 < fl -> fl + 1 <= lo ->
  stk bsegs m lo b -> stk bsegs m b (q - 72) -> rw_cells bsegs m (q - 72) (it_saved vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7) ->
  rw_cells bsegs m f [C8 h0; C8 h1; C8 h2] -> stk bsegs m (f + 24) (f + 120) -> ro_cells bsegs m (f + 120) [C8 (wz fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] ->
  stk bsegs m DST (DST + 24) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem), ret_st vra (wz q) gp (wz TPV_A) vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 s8 s9 s10 s11 (wz e) m' ms
      /\ ms_fcsr ms = fc /\ munch [(fl, fl + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo q /\ rw_cells bsegs m' fl [C1 (Z_to_bv 8 0)]
      /\ stk bsegs m' DST (DST + 24))
    (ITS 0xb717c (wz 0xb710c) xt0 xt1 xt2 (wz e) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xt3 xt4 xt5 xt6 F fc m).
Proof using F0 Ef FLO SFL SHf GF GLO LOB BQ QT GD DLO DF DSf SDf SDSf SDLO SDD.
  clear B16 D8 FRS1 LV1 SP1 INN DIN SDIN FRESH CSEP.
  intros until h2. intros FL0 FLLO ST STF FS FH F3S FW FLC DS MI.
  unfold TPV_A, USTACK_TOP, RT_STACK, it_saved in *.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EFL : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).

  zstep. ls. step. zstep.
  replace (q - 72) with (q + -72) in FS by lia.

  do 9 zstep. zstep.
  replace (q + -72) with (q - 72) in FS by lia.
  pose proof (stk_merge bsegs _ _ _ _ ST STF ltac:(lia)) as ST2.
  pose proof (stk_release bsegs _ _ _ _ ST2 FS ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
  replace (q - 72 + Z.of_nat 72) with q in ST3 by lia. replace (q + -96 + 96) with q by lia.

  zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST3|]. split; [eassumption| eassumption].
Qed.

Definition krel_stmt : Prop :=
  forall (m : mem) (sg n : Z) (F : bvmap 5 word) (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    ITM m -> ART RT Σ1 m -> PRES m -> 0 <= sg <= 1 -> 1 <= n -> sg + n <= 20 ->
    aevt Σ1 K (ITS 0xb710c (wz 0xb710c) xt0 xt1 xt2 (wz (DST + sg)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DST + sg)) (wz n) xt3 xt4 xt5 xt6 F fc m).
Hypothesis KREL : krel_stmt.

Lemma it_lastA : forall (m : mem) (sg idx d : Z) (F : bvmap 5 word) (xra xt0 xt1 xt2 xa0 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
  ITM m -> ART RT Σ1 m -> PRES m -> 0 <= sg <= 1 -> sg <= idx <= 19 -> 0 <= d <= 9 ->
  aevt Σ1 K (ITS 0xb70e0 xra xt0 xt1 xt2 xa0 (wz (f + 32 + idx)) (wz (f + 32)) xa3 xa4 xa5 xa6 xa7 (wz (DST + sg)) (wz d) xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST F0 Ef FLO SFL SHf GF GLO LOB B16 BQ QT D8 GD DLO DF DSf SDf SDSf SDLO SDD FRS1 LV1 SP1 INN DIN SDIN FRESH CSEP KREL.
  intros m sg idx d F xra xt0 xt1 xt2 xa0 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HM ART0 PR HSG HIDX HD.
  unfold TPV_A, USTACK_TOP, RT_STACK in *.
  apply (aevt_evt RT AF PMc MST). it_open HM.
  pose proof (munch_refl [(f + 24, f + 120)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  destruct (it_shadow_read m f idx _ SHC Ef ltac:(clear - F0; lia) ltac:(clear - HIDX HSG; lia)) as (sb & RD & BZ & B4).

  zstep. pjnorm. zstep. change (Z_to_bv 64 ((f + 32 + idx) / 8 + 2147450880)) with (Z_to_bv 64 (shad (f + 32 + idx))). zstep. clear RD.
  lazymatch goal with |- evt _ _ (MS _ ?F1 _ ?fc1 _ ?mm _) =>
  assert (JOIN : forall ya0 ya3 : word,
    evt bsegs (fun ms' => aevt Σ1 K ms')
      (ITS 0xb70f0 xra xt0 xt1 xt2 ya0 (wz (f + 32 + idx)) (wz (f + 32)) ya3 xa4 xa5 xa6 xa7 (wz (DST + sg)) (wz d) xt3 xt4 xt5 xt6 F1 fc1 mm)) end.
  { intros ya0 ya3.

    zstep. zstep. step. pj_store_done. zstep. pjnorm. zstep. zstep. zstep.
    replace (f + 52 - (f + 32 + idx)) with (20 - idx) by (clear; lia).

    destruct (stk_split bsegs _ _ (f + 32 + idx) _ F3S ltac:(clear - HIDX HSG; lia)) as [F3a F3b].
    destruct (stk_split bsegs _ _ (f + 52) _ F3b ltac:(clear - HIDX HSG; lia)) as [F3c F3d].
    destruct (stk_CB bsegs _ _ _ F3c ltac:(clear - HIDX; lia)) as (src & SRC).
    replace (Z.to_nat (f + 52 - (f + 32 + idx))) with (Z.to_nat (20 - idx)) in SRC by (clear; f_equal; lia).
    assert (SRCL : Z.of_nat (length src) = 20 - idx).
    { destruct SRC as [[WF _] _]. cbn in WF. destruct WF as [WF _]. clear - WF HIDX. lia. }
    pose proof (rw_cells_bytes_at bsegs _ _ _ SRC) as SRB. cbn [cells_bytes cbytes app] in SRB. rewrite app_nil_r in SRB.
    pose proof (ART_mu_it _ m _ ART0 MU WM ltac:(intros a; cbn [outside]; clear; lia)) as ART1.
    pose proof (PRES_mu _ m _ PR MU ltac:(intros a Ha _; cbn [outside]; pose proof (FRESH a Ha); clear - H; lia)) as PR1.
    apply evt_done.
    eapply (aevt_memcpyP RT RC PMc FDO MST Σ1 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (DST + sg) (f + 32 + idx) src lo);
      [reflexivity| reflexivity| rewrite SRCL; reflexivity| clear - GD DLO LOB BQ QT HSG; lia| clear - GF FLO LOB BQ QT HIDX HSG; lia| clear - SRCL HIDX HSG; lia| exact SRB
      | | | rewrite SRCL; clear - DF HIDX HSG; lia| exact ART1| exact MI| |].
    -
      rewrite SRCL. split; [intros _; split| left; clear - FLO HIDX; lia].
      + eapply acc_sub; [eapply (it_acc20 _ f); [exact SHC| exact Ef| clear - F0; lia]| clear - HIDX HSG; lia| clear - HIDX; lia].
      + right; left. exists f, 1%nat. split; [rewrite FRS1; left; reflexivity| change (fs_size 1) with 128; clear - HIDX HSG; lia].
    -
      rewrite SRCL. split; [intros _; split| split].
      + intros i Hi. exists z8. split; [| left; reflexivity].
        assert (C : shad (DST + sg + i) = shad DST + 0 \/ shad (DST + sg + i) = shad DST + 1 \/ shad (DST + sg + i) = shad DST + 2)
          by (unfold shad; clear - Hi HSG HIDX D8; Z.div_mod_to_equations; lia).
        destruct C as [C|[C|C]]; rewrite C;
          [exact (bytes_at_nth1 bsegs _ _ [z8; z8; z8] 0 z8 DSH eq_refl)| exact (bytes_at_nth1 bsegs _ _ [z8; z8; z8] 1 z8 DSH eq_refl)
          | exact (bytes_at_nth1 bsegs _ _ [z8; z8; z8] 2 z8 DSH eq_refl)].
      + right; left. exists fN, kN. split; [rewrite FRS1; right; exact INN| clear - DIN HSG HIDX; lia].
      + intros i Hi. right; right; right; left. exists fN, kN. split; [rewrite FRS1; right; exact INN| clear - DIN HSG HIDX Hi; lia].
      + eapply (stk_wr_at _ _ _ _ _ DS); clear - HSG HIDX; lia.
    -
      unfold call_ok, RT_STACK, USTACK_TOP. rewrite (unsigned_lit b) by (clear - LOB GLO QT BQ; lia). split; [exact ST|]. split; [exact SP1|]. clear - LOB B16 BQ QT. lia.
    - intros yt0 yt1 yt2 ya1 ya2 ya3' ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 F' m' (ART' & MI' & WM' & ST') PRX BY.
      rewrite (unsigned_lit b) in ST', PRX by (clear - LOB GLO QT BQ; lia). rewrite SRCL in PRX. rewrite (ret_pc_even 0xb710c) by (clear; lia).

      lazymatch type of DS with stk _ ?mc _ _ =>
      assert (AG : forall (P : Z -> Prop),
        (forall y, P y -> (b <= y < q \/ f <= y < f + 120 \/ f / 8 + 2147450880 <= y < f / 8 + 2147450880 + 16
                           \/ (DST <= y < DST + 24 /\ ~ (DST + sg <= y < DST + sg + (20 - idx))) \/ shad DST <= y < shad DST + 3)) -> agree_on P mc m') end.
      { intros P HP a Ha. apply PRX.
        - destruct (HP _ Ha) as [H|[H|[H|[[H _]|H]]]].
          + left. unfold USTACK_TOP. clear - H QT. lia.
          + right; right; right; left. exists f, 1%nat. split; [rewrite FRS1; left; reflexivity| change (fs_size 1) with 128; clear - H; lia].
          + right; right; right; right. exists f, 1%nat. split; [rewrite FRS1; left; reflexivity|]. unfold shad, SHB. change (fs_size 1) with 128.
            replace ((f + 128) / 8) with (f / 8 + 16) by (clear - Ef; Z.div_mod_to_equations; lia). clear - H; lia.
          + right; right; right; left. exists fN, kN. split; [rewrite FRS1; right; exact INN| clear - H DIN; lia].
          + right; right; right; right. exists fN, kN. split; [rewrite FRS1; right; exact INN| clear - H SDIN; lia].
        - destruct (HP _ Ha) as [H|[H|[H|[[_ H]|H]]]]; [clear - H DLO LOB HSG HIDX; lia| clear - H DF HSG HIDX; lia| clear - H DSf HSG HIDX; lia| exact H
          | clear - H SDD HSG HIDX; lia]. }
      assert (DS' : stk bsegs m' DST (DST + 24)).
      { destruct (stk_split bsegs _ _ (DST + sg) _ DS ltac:(clear - HSG; lia)) as [D1 D2].
        destruct (stk_split bsegs _ _ (DST + sg + (20 - idx)) _ D2 ltac:(clear - HSG HIDX; lia)) as [D3 D4].
        apply (stk_merge bsegs m' _ (DST + sg)); [| | clear - HSG; lia].
        - eapply stk_agree; [exact D1| apply AG; intros y Hy; right; right; right; left; clear - Hy HSG HIDX; lia| exact WM'].
        - apply (stk_merge bsegs m' _ (DST + sg + (20 - idx))); [| | clear - HSG HIDX; lia].
          + replace (DST + sg + (20 - idx)) with (DST + sg + Z.of_nat (cells_size [CB (length src) src])) by (cbn [cells_size csize]; clear - SRCL; lia).
            apply (stk_of_rw_cells bsegs m'). apply rw_cells_of_u8arr. split; [exact BY|]. rewrite SRCL.
            eapply wr_at_transport; [eapply (stk_wr_at _ _ _ _ _ D3); clear; lia| exact WM'].
          + eapply stk_agree; [exact D4| apply AG; intros y Hy; right; right; right; left; clear - Hy HSG HIDX; lia| exact WM']. }
      eapply (KREL m' sg (20 - idx) F'); [| exact ART'| | exact HSG| clear - HIDX; lia| clear - HIDX HSG; lia].
      + split; [exact MI'|]. split; [exact ST'|].
        split; [eapply stk_agree; [exact STF| apply AG; intros y Hy; left; clear - Hy; lia| exact WM']|].
        split; [eapply rw_cells_agree_nw; [exact FS| apply AG; intros y Hy; unfold it_saved in Hy; cbn [cells_size csize Nat.add] in Hy; left; clear - Hy BQ; lia]|].
        split; [do 3 eexists; eapply rw_cells_agree_nw; [exact FH| apply AG; intros y Hy; cbn [cells_size csize Nat.add] in Hy; right; left; clear - Hy; lia]|].
        split. { apply (stk_merge bsegs m' _ (f + 32 + idx)); [| apply (stk_merge bsegs m' _ (f + 52))|]; try (clear - HIDX HSG; lia).
                 - eapply stk_agree; [exact F3a| apply AG; intros y Hy; right; left; clear - Hy HIDX HSG; lia| exact WM'].
                 - eapply stk_agree; [exact F3c| apply AG; intros y Hy; right; left; clear - Hy HIDX HSG; lia| exact WM'].
                 - eapply stk_agree; [exact F3d| apply AG; intros y Hy; right; left; clear - Hy HIDX HSG; lia| exact WM']. }
        split; [do 4 eexists; eapply rw_cells_agree_nw; [exact SHC| apply AG; intros y Hy; cbn [cells_size csize Nat.add] in Hy; right; right; left; clear - Hy; lia]|].
        split; [exact DS'|].
        eapply bytes_at_agree; [exact DSH| apply AG; intros y Hy; cbn [length] in Hy; right; right; right; right; clear - Hy; lia].
      + intros a Ha Hd. rewrite <- (PR1 a Ha Hd). apply PRX; [| clear - Hd HSG HIDX; lia].
        eapply aclient_mono; [exact Ha| rewrite LV1; intros e He; exact He| rewrite FRS1; intros e He; right; exact He| clear - BQ; lia]. }
  destruct (Z_lt_le_dec idx 16) as [LO16|HI16].
  - rewrite (BZ ltac:(clear - LO16; lia)). replace (sxb z8) with (Z_to_bv 64 0) by reflexivity. zstep. try if_false. apply JOIN.
  -
    rewrite (B4 HI16). rewrite (pj_sxb_small7 4) by (clear; lia). zstep.
    if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc; lia].
    zstep. pjnorm. rewrite pj_land7 by (clear - F0 HIDX HSG; lia).
    zstep. if_cases Kc; zify_cond Kc;
      [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - F0 HIDX HSG Ef; Z.div_mod_to_equations; lia); clear - Kc HI16 HIDX Ef; Z.div_mod_to_equations; lia].
    apply JOIN.
Qed.

Lemma it_loopA : forall (fu : nat) (m : mem) (sg idx w : Z) (F : bvmap 5 word) (xra xt0 xt1 xt2 xa1 xt3 xt4 xt5 xt6 : word),
  idx <= Z.of_nat fu -> ITM m -> ART RT Σ1 m -> PRES m -> 0 <= sg <= 1 -> 0 <= idx <= 19 -> 10 <= w < 10 ^ (idx + 1 - sg) -> w < 18446744073709551616 ->
  aevt Σ1 K (ITS 0xb708c xra xt0 xt1 xt2 (wz (f + 32 + idx)) xa1 (wz (f + 32)) (wz 10) (wz (f + 32 + idx)) (wz DIV10_MAGIC) (wz 1) (wz 99)
                (wz (DST + sg)) (wz w) xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST F0 Ef FLO SFL SHf GF GLO LOB B16 BQ QT D8 GD DLO DF DSf SDf SDSf SDLO SDD FRS1 LV1 SP1 INN DIN SDIN FRESH CSEP KREL.
  induction fu as [|fu IH]; intros m sg idx w F xra xt0 xt1 xt2 xa1 xt3 xt4 xt5 xt6 HFU HM ART0 PR HSG HIDX HW W64.
  { exfalso. pose proof (pow10_ge2 w (idx + 1 - sg) HW). lia. }
  pose proof (pow10_ge2 w (idx + 1 - sg) HW) as J2.
  pose proof (pow10_step w (idx + 1 - sg) ltac:(lia) ltac:(lia)) as HQ. replace (idx + 1 - sg - 1) with (idx - 1 + 1 - sg) in HQ by lia.
  unfold TPV_A, USTACK_TOP, RT_STACK in *.
  apply (aevt_evt RT AF PMc MST). it_open HM. unfold DIV10_MAGIC.
  pose proof (munch_refl [(f + 24, f + 120)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  destruct (it_shadow_read m f idx _ SHC Ef ltac:(clear - F0; lia) ltac:(clear - HIDX; lia)) as (sb & RD & BZ & B4).

  step. if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc GF HIDX; lia| clear Kc].
  zstep. zstep. pjnorm. zstep. change (Z_to_bv 64 ((f + 32 + idx) / 8 + 2147450880)) with (Z_to_bv 64 (shad (f + 32 + idx))). zstep. clear RD.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  assert (JOIN : forall ya1 yt1 : word,
    evt bsegs (fun ms' => aevt Σ1 K ms')
      (ITS 0xb70a4 xra (wz w) yt1 xt2 (wz (f + 32 + idx)) ya1 (wz (f + 32)) (wz 10) (wz (f + 32 + idx)) (wz 14757395258967641293) (wz 1) (wz 99)
            (wz (DST + sg)) (wz w) xt3 xt4 xt5 xt6 F fc mm)) end.
  { intros ya1 yt1.

    zstep. zstep. zstep.
    rewrite SFModel.land_W64. change (2 ^ 64) with 18446744073709551616.
    change 14757395258967641293 with DIV10_MAGIC at 2. rewrite (div10_machine w) by (clear - HW W64; lia).

    zstep. zstep. zstep. step. pj_store_done. zstep. zstep. step.
    pose proof (ART_mu_it _ m _ ART0 MU WM ltac:(intros a; cbn [outside]; clear; lia)) as ART1.
    pose proof (PRES_mu _ m _ PR MU ltac:(intros a Ha _; cbn [outside]; pose proof (FRESH a Ha); clear - H; lia)) as PR1.
    if_cases Kc; zify_cond Kc; pjnorm_in Kc.
    - apply evt_done.
      eapply aevt_eq; [| eapply (IH _ sg (idx - 1) (w / 10) F)];
        [pj_st_eq| clear - HFU; lia| | exact ART1| exact PR1| exact HSG| clear - HIDX J2 HSG; lia| | clear - HQ W64; lia].
      + split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [do 3 eexists; eassumption|].
        split; [assumption|]. split; [do 4 eexists; exact SHC|]. split; assumption.
      + split; [apply (div10_ge10 w); clear - Kc HW; lia| exact (proj2 HQ)].
    -   step. apply evt_done.
      eapply aevt_eq; [| eapply (it_lastA _ sg (idx - 1) (w / 10) F)];
        [pj_st_eq| | exact ART1| exact PR1| exact HSG| clear - HIDX J2 HSG HQ Kc HW; lia| ].
      + split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [do 3 eexists; eassumption|].
        split; [assumption|]. split; [do 4 eexists; exact SHC|]. split; assumption.
      + pose proof (div10_ge10 w ltac:(clear - HW; lia)) as DG. clear - Kc DG HQ. lia. }
  destruct (Z_lt_le_dec idx 16) as [LO16|HI16].
  - rewrite (BZ ltac:(clear - LO16; lia)). replace (sxb z8) with (Z_to_bv 64 0) by reflexivity. zstep. try if_false. apply JOIN.
  -
    rewrite (B4 HI16). rewrite (pj_sxb_small7 4) by (clear; lia). zstep.
    if_cases Kc; zify_cond Kc; [clear Kc| exfalso; pjnorm_in Kc; clear - Kc; lia].
    zstep. pjnorm. rewrite pj_land7 by (clear - F0 HIDX; lia).
    zstep. if_cases Kc; zify_cond Kc;
      [clear Kc| exfalso; rewrite !pj_signed_small in Kc by (clear - F0 HIDX Ef; Z.div_mod_to_equations; lia); clear - Kc HI16 HIDX Ef; Z.div_mod_to_equations; lia].
    apply JOIN.
Qed.

Lemma it_bufA : forall (m : mem) (sg w : Z) (F : bvmap 5 word) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
  ITM m -> ART RT Σ1 m -> PRES m -> 0 <= sg <= 1 -> 0 <= w < 10 ^ (20 - sg) -> w < 18446744073709551616 ->
  aevt Σ1 K (ITS 0xb7058 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (wz (DST + sg)) (wz w) xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST F0 Ef FLO SFL SHf GF GLO LOB B16 BQ QT D8 GD DLO DF DSf SDf SDSf SDLO SDD FRS1 LV1 SP1 INN DIN SDIN FRESH CSEP KREL.
  intros m sg w F xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HM ART0 PR HSG HW W64.
  unfold TPV_A, USTACK_TOP, RT_STACK in *.
  apply (aevt_evt RT AF PMc MST). pose proof HM as HM0. it_open HM.

  zstep. zstep. step. if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc GF FLO LOB BQ QT; lia| clear Kc].
  zstep. step. if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc GF FLO LOB BQ QT; lia| clear Kc].
  zstep. zstep. pjnorm. step. if_cases K1; zify_cond K1; pjnorm_in K1.
  -
    zstep. apply evt_done.
    eapply aevt_eq; [| eapply (it_lastA m sg 19 w F)]; [pj_st_eq| exact HM0| exact ART0| exact PR| exact HSG| clear - HSG; lia| clear - K1 HW; lia].
  -
    zstep. step. zstep. pjnorm. zstep. zstep. apply evt_done.
    eapply aevt_eq; [| eapply (it_loopA 19%nat m sg 19 w F)]; [pj_st_eq| clear; lia| exact HM0| exact ART0| exact PR| exact HSG| clear; lia| | exact W64].
    replace (19 + 1 - sg) with (20 - sg) by (clear; lia). clear - K1 HW. lia.
Qed.

Lemma it_signA : forall (m : mem) (v : Z) (F : bvmap 5 word) (xra xt0 xt1 xt2 xa1 xa2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
  ITM m -> ART RT Σ1 m -> PRES m -> 0 <= v < 18446744073709551616 ->
  aevt Σ1 K (ITS 0xb702c xra xt0 xt1 xt2 (wz 4) xa1 xa2 (wz (-13)) (wz (-15)) xa5 xa6 xa7 (wz DST) (wz v) xt3 xt4 xt5 xt6 F fc m).
Proof using AF RC FDO MST F0 Ef FLO SFL SHf GF GLO LOB B16 BQ QT D8 GD DLO DF DSf SDf SDSf SDLO SDD FRS1 LV1 SP1 INN DIN SDIN FRESH CSEP KREL.
  intros m v F xra xt0 xt1 xt2 xa1 xa2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HM ART0 PR HV.
  unfold TPV_A, USTACK_TOP, RT_STACK in *.
  pose proof (u64_lt_pow10_20 v HV) as P20.
  apply (aevt_evt RT AF PMc MST). pose proof HM as HM0. it_open HM.

  step. if_cases Kn; zify_cond Kn; pjnorm_in Kn.
  -
    assert (PW : v < 9223372036854775808).
    { unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in Kn. cbn in Kn. clear - Kn HV. Z.div_mod_to_equations. lia. }
    apply evt_done.
    eapply aevt_eq; [| eapply (it_bufA m 0 v F)]; [pj_st_eq| exact HM0| exact ART0| exact PR| clear; lia| | clear - HV; lia].
    change (10 ^ (20 - 0)) with (10 ^ 20). exact P20.
  -
    assert (NW : 0 < 18446744073709551616 - v <= 9223372036854775808).
    { unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in Kn. cbn in Kn. clear - Kn HV. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl [(DST, DST + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof (bytes_at_read bsegs m (shad DST) [z8; z8; z8] 0 1 DSH ltac:(clear; lia) ltac:(cbn; clear; lia)) as RD. cbn [firstn skipn] in RD.
    replace (shad DST + 0) with (shad DST) in RD by (clear; lia).
    zstep. step. if_cases Kc; zify_cond Kc; [exfalso; pjnorm_in Kc; clear - Kc GD DLO LOB BQ QT; lia| clear Kc].
    zstep. pjnorm. zstep. change (Z_to_bv 64 (DST / 8 + 2147450880)) with (Z_to_bv 64 (shad DST)). zstep. clear RD.
    replace (sxb z8) with (Z_to_bv 64 0) by reflexivity. zstep. try if_false.

    zstep. step. pj_store_done. zstep. zstep.
    replace (Z_to_bv 64 (0 - v)) with (Z_to_bv 64 (18446744073709551616 - v))
      by (apply Z_to_bv_eqm; change (2 ^ 64) with 18446744073709551616; clear - HV; Z.div_mod_to_equations; lia).
    pose proof (ART_mu_it _ m _ ART0 MU WM ltac:(intros a; cbn [outside]; clear; lia)) as ART1.
    pose proof (PRES_mu _ m _ PR MU ltac:(intros a _ Hd; cbn [outside]; clear - Hd; lia)) as PR1.
    apply evt_done.
    eapply aevt_eq; [| eapply (it_bufA _ 1 (18446744073709551616 - v) F)];
      [pj_st_eq| | exact ART1| exact PR1| clear; lia| change (10 ^ (20 - 1)) with 10000000000000000000; clear - NW; lia| clear - NW; lia].
    split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [do 3 eexists; eassumption|].
    split; [assumption|]. split; [do 4 eexists; exact SHC|]. split; assumption.
Qed.

End Pieces.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Theorem itoa_okA : itoa_cpsA RT PMc PJ_ITOA_A.
Proof using AF RC RC2 FDO MST.
  unfold itoa_cpsA.
  intros Σ K DST q lo v fN kN ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk
         FDO' MST' INN DLE DHI D8 DC DSH ART0 MI0 ST0 SPLO LOQ QT Q16 HV FRL CR HK.
  unfold PJ_ITOA_STACK_A, RT_STACK in LOQ. unfold USTACK_TOP in QT.
  pose proof (af_client_consts RT AF Σ m ART0) as CC0. pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
  pose proof (af_frames_range RT AF Σ m fN kN ART0 INN) as (N0 & NWIN & _ & _). pose proof (af_frames_align RT AF Σ m fN kN ART0 INN) as [_ NSEG].
  assert (FSZN : 0 <= fs_size kN) by (unfold fs_size; apply Z.shiftl_nonneg; clear; lia).
  assert (CSEP : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> q <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split_c RT AF Σ m q a ART0 Ha) as [H|H]; [left; exact H| right; clear - H SPLO; lia]. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (it_pro1 PJ_ITOA_A q lo DST v ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (or_introl eq_refl) ST0);
                   [clear - LOQ; lia| clear - SPLO SPW; ul| unfold USTACK_TOP; exact QT| exact Q16| exact CC0| exact MI0]|].
  cbv beta. intros ms1 (m1 & dd & a1' & a2' & DD & B32 & -> & MU1 & WM1 & MI1 & ST1 & FS1). apply evt_done.
  set (b := q - 96 - dd) in *.
  assert (LOB : lo + RT_STACK <= b) by (unfold b, RT_STACK; clear - LOQ DD; lia).
  assert (BQ : b + 96 <= q) by (unfold b; clear - DD; lia).
  assert (B16 : b mod 16 = 0) by (clear - B32; Z.div_mod_to_equations; lia).
  assert (GLO : 0x6e0000 <= lo) by (clear - SPLO SPW; ul).
  assert (EU : bv_unsigned (wz b) = b) by (apply unsigned_lit; clear - LOB GLO BQ QT; unfold RT_STACK in *; lia).
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (q - 96) ART0); [clear - SPLO LOQ; lia| | exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact Logic.I]. intros Hin. apply Ha. left. clear - Hin QT. unfold USTACK_TOP. lia. }
  assert (PRES1 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> m1 a = m a).
  { intros a Ha. apply MU1. cbn [outside]. split; [| exact Logic.I]. destruct (CSEP _ Ha); clear - H LOQ; lia. }
  destruct (stk_split bsegs m1 _ b _ ST1 ltac:(unfold b; clear - LOQ DD; lia)) as [ST1l ST1h].

  eapply (aevt_smalloc1 RT PMc FDO MST RC2 Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo);
    [reflexivity| clear - FRL; unfold FRAMES_MAX2, FRAMES_TOT in *; lia| exact CR| exact ART1| exact MI1| | intros HN; exfalso; rewrite HN in INN; exact INN|].
  { unfold call_ok. rewrite EU. split; [exact ST1l|]. split; [exact SPLO|]. split; [exact LOB|].
    split; [unfold b, USTACK_TOP; clear - QT DD; lia| exact B16]. }
  intros Σ1 f v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 v3 v4 v5 v6 F1 m2 (ART2 & MI2 & WM2 & ST2) PRES2 WRF WRS FRS1 LV1 SPE1 CR1 F0 F64 FTOP.
  assert (SP1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SPE1; exact SPLO).
  rewrite EU in ST2, PRES2. unfold PJ_ITOA_A. rewrite (ret_pc_even (0xb6f2c + 100)) by (clear; lia). change (0xb6f2c + 100) with 0xb6f90.
  change (fs_size 1 - 8) with 120 in WRF. change (fs_size 1 / 8) with 16 in WRS.

  assert (INf : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  assert (INN1 : In (fN, kN) (rt_frames RT Σ1)) by (rewrite FRS1; right; exact INN).
  pose proof (af_frames_range RT AF Σ1 m2 f 1%nat ART2 INf) as (_ & FWIN & _ & _). rewrite SPE1 in FWIN. change (fs_size 1) with 128 in FWIN.
  assert (FLO : f + 128 <= lo) by (clear - FWIN SPLO; lia).
  pose proof (af_frames_align RT AF Σ1 m2 f 1%nat ART2 INf) as [_ GF]. unfold SEGTOP_A in GF.
  pose proof (af_fshadow_apart RT AF Σ1 m2 f 1%nat ART2 INf) as [_ FSF]. change (fs_size 1) with 128 in FSF.
  pose proof (af_fshadow_apart RT AF Σ1 m2 fN kN ART2 INN1) as [_ NSF].
  pose proof (af_frames_disj RT AF Σ1 m2 f 1%nat fN kN [] (rt_frames RT Σ) ART2 FRS1 INN) as FF. change (fs_size 1) with 128 in FF.
  assert (Ef : 8 * (f / 8) = f) by (clear - F64; Z.div_mod_to_equations; lia).
  assert (E128 : (f + 128) / 8 = f / 8 + 16) by (clear - Ef; Z.div_mod_to_equations; lia).
  assert (SHf : f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f).
  { destruct (FSF f 1%nat INf) as [H|H]; change (fs_size 1) with 128 in H; unfold shad, SHB in H; rewrite ?E128 in H; [left| right]; clear - H; lia. }
  assert (SFL : f / 8 + 2147450880 + 16 <= lo) by (clear - FLO SPLO SPW; ul).
  assert (GD : 0x6e0000 <= DST) by (clear - NSEG DLE; ul).
  assert (DLO : DST + 24 <= lo) by (clear - DHI NWIN SPLO; lia).
  assert (DF : DST + 24 <= f \/ f + 128 <= DST) by (clear - FF DLE DHI FSZN; lia).
  assert (DSf : DST + 24 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= DST).
  { destruct (FSF fN kN INN1) as [H|H]; unfold shad, SHB in H; rewrite ?E128 in H; [left| right]; clear - H DLE DHI; lia. }
  assert (SDf : shad DST + 3 <= f \/ f + 128 <= shad DST).
  { destruct (NSF f 1%nat INf) as [H|H]; change (fs_size 1) with 128 in H; [right| left]; unfold shad, SHB in *; clear - H DLE DHI; Z.div_mod_to_equations; lia. }
  assert (SDD : shad DST + 3 <= DST \/ DST + 24 <= shad DST).
  { destruct (NSF fN kN INN1) as [H|H]; [right| left]; unfold shad, SHB in *; clear - H DLE DHI; Z.div_mod_to_equations; lia. }
  assert (SDSf : shad DST + 3 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= shad DST).
  { unfold shad, SHB. destruct FF as [H|H]; [right| left]; clear - H DLE DHI Ef; Z.div_mod_to_equations; lia. }
  assert (SDLO : shad DST + 3 <= lo) by (unfold shad, SHB; clear - DLO SPLO SPW; unfold STACK_WIN in *; Z.div_mod_to_equations; lia).
  assert (SDIN : shad fN <= shad DST /\ shad DST + 3 <= shad (fN + fs_size kN)) by (unfold shad; clear - DLE DHI; Z.div_mod_to_equations; lia).
  assert (FRESH : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> ~ (f <= a < f + 128) /\ ~ (f / 8 + 2147450880 <= a < f / 8 + 2147450880 + 16)).
  { intros a Ha. pose proof (newframe_apartI RT AF Σ Σ1 m2 f 1%nat q a ART2 FRS1 ltac:(rewrite LV1; intros e He; exact He) SPE1 ltac:(clear - LOQ SPLO; lia) Ha) as [N1 N2].
    change (fs_size 1) with 128 in N1, N2. unfold shad, SHB in N2. rewrite E128 in N2. split; [exact N1| clear - N2; lia]. }

  destruct (wr_at_rw_CB m2 f 24 (wr_at_sub m2 f 120 f 24 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jh & FH2). change (Z.to_nat 24) with 24%nat in FH2.
  pose proof (wr_at_stk m2 (f + 24) 96 (wr_at_sub m2 f 120 (f + 24) 96 WRF ltac:(lia) ltac:(lia) ltac:(lia))) as F3S2.
  replace (f + 24 + 96) with (f + 120) in F3S2 by lia.
  destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 16 WRS ltac:(lia)) as (sh & SHC2). change (Z.to_nat 16) with 16%nat in SHC2.

  assert (AG12 : forall (P : Z -> Prop), (forall y, P y -> aclient (rt_live RT Σ) (rt_frames RT Σ) b y) -> agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2. exact (HP _ Ha). }
  assert (STb2 : stk bsegs m2 b (q - 72)).
  { eapply stk_agree_nw; [exact ST1h|]. apply AG12. intros y Hy. left. clear - Hy QT. unfold USTACK_TOP. lia. }
  assert (FS2 : rw_cells bsegs m2 (q - 72) (it_saved ra s0 s1 s2 s3 s4 s5 s6 s7)).
  { eapply rw_cells_agree_nw; [exact FS1|]. apply AG12. intros y Hy. unfold it_saved in Hy. cbn [cells_size csize Nat.add] in Hy. left. unfold b, USTACK_TOP. clear - Hy DD QT. lia. }
  assert (DS2 : stk bsegs m2 DST (DST + 24)).
  { pose proof (stk_of_rw_cells bsegs _ _ _ DC) as DS0. cbn [cells_size csize Nat.add] in DS0. replace (DST + Z.of_nat 24) with (DST + 24) in DS0 by (clear; lia).
    eapply stk_agree_nw; [eapply stk_agree_nw; [exact DS0|]|].
    - eapply agree_of_munch; [exact MU1|]. intros y Hy. cbn [outside]. clear - Hy DLO LOQ. lia.
    - apply AG12. intros y Hy. right; right; right; left. exists fN, kN. split; [exact INN| clear - Hy DLE DHI; lia]. }
  assert (DSH2 : bytes_at bsegs m2 (shad DST) [z8; z8; z8]).
  { eapply bytes_at_agree; [eapply bytes_at_agree; [exact DSH|]|]; cbn [length].
    - eapply agree_of_munch; [exact MU1|]. intros y Hy. cbn [outside]. clear - Hy SDLO LOQ. lia.
    - apply AG12. intros y Hy. right; right; right; right. exists fN, kN. split; [exact INN| clear - Hy SDIN; lia]. }
  assert (PRES2' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> m2 a = m a).
  { intros a Ha. rewrite <- (PRES1 a Ha). apply PRES2. eapply aclient_mono; [exact Ha| intros e He; exact He| intros e He; exact He| clear - BQ; lia]. }
  clear PRES1 ST1 ST1h FS1 WM1 MI1 ART1 WRF WRS.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (it_hdr q b f lo DST v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ jh sh F1 fc m2 F0 Ef SHf FLO SFL GF GLO);
                   [clear - LOB; unfold RT_STACK in *; lia| exact BQ| unfold USTACK_TOP; exact QT| exact STb2| exact FH2| exact SHC2| exact MI2]|].
  cbv beta. intros ms3 (m3 & a1'' & a2'' & x12 & x13 & x14 & x15 & -> & MU3 & WM3 & MI3 & STb3 & FH3 & SHC3).
  apply evt_done.
  assert (ART3 : ART RT Σ1 m3).
  { eapply (ART_mu_it Σ1 q b f DST lo fN kN (rt_frames RT Σ) Ef LOB ltac:(unfold USTACK_TOP; exact QT) FRS1 SP1 INN (conj DLE DHI) _ m2 m3 ART2 MU3 WM3).
    intros a. cbn [outside]. clear - BQ. lia. }
  assert (PR3 : PRES q DST (rt_live RT Σ) (rt_frames RT Σ) m m3).
  { intros a Ha Hd. rewrite <- (PRES2' a Ha). apply MU3. cbn [outside].
    pose proof (FRESH _ Ha) as [N1 N2]. destruct (CSEP _ Ha) as [H|H]; (repeat split; try exact Logic.I); clear - H N1 N2 BQ LOB; unfold RT_STACK in *; lia. }
  assert (HM3 : ITM q b f DST lo ra s0 s1 s2 s3 s4 s5 s6 s7 m3).
  { split; [exact MI3|].
    split. { eapply stk_agree_nw; [exact ST2|]. eapply agree_of_munch; [exact MU3|]. intros y Hy. cbn [outside]. clear - Hy FLO SFL LOB; unfold RT_STACK in *; lia. }
    split; [exact STb3|].
    split. { eapply rw_cells_agree_nw; [exact FS2|]. eapply agree_of_munch; [exact MU3|]. intros y Hy. unfold it_saved in Hy. cbn [cells_size csize Nat.add] in Hy. cbn [outside].
             unfold b in *. clear - Hy DD FLO SFL LOB; unfold RT_STACK in *; lia. }
    split; [do 3 eexists; exact FH3|].
    split. { eapply stk_agree_nw; [exact F3S2|]. eapply agree_of_munch; [exact MU3|]. intros y Hy. cbn [outside]. clear - Hy FLO LOB SHf; unfold RT_STACK in *; lia. }
    split; [do 4 eexists; exact SHC3|].
    split. { eapply stk_agree_nw; [exact DS2|]. eapply agree_of_munch; [exact MU3|]. intros y Hy. cbn [outside]. clear - Hy DLO LOB DF DSf; unfold RT_STACK in *; lia. }
    eapply bytes_at_agree; [exact DSH2|]. eapply agree_of_munch; [exact MU3|]. intros y Hy. cbn [length] in Hy. cbn [outside]. clear - Hy SDLO LOB SDf SDSf; unfold RT_STACK in *; lia. }

  assert (KR : krel_stmt Σ1 K q b f DST lo (rt_live RT Σ) (rt_frames RT Σ) m gp s8 s9 s10 s11 ra s0 s1 s2 s3 s4 s5 s6 s7 fc).
  { unfold krel_stmt. intros m4 sg n F4 yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 HM4 ART4 PR4 HSG HN HSN.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (it_rel1 q b f DST lo gp s8 s9 s10 s11 ra s0 s1 s2 s3 s4 s5 s6 s7 fc F0 Ef FLO SFL SHf GF GLO LOB BQ ltac:(unfold USTACK_TOP; exact QT) GD DLO DF DSf SDf SDSf SDLO SDD m4 sg n F4);
                     [exact HM4| exact HSG| exact HN| exact HSN]|].
    cbv beta. intros ms5 (m5 & h1 & h2 & -> & MU5 & WM5 & MI5 & ST5 & STF5 & FS5 & FH5 & F3S5 & SHC5 & DS5 & DSH5). apply evt_done.
    assert (ART5 : ART RT Σ1 m5).
    { eapply (ART_mu_it Σ1 q b f DST lo fN kN (rt_frames RT Σ) Ef LOB ltac:(unfold USTACK_TOP; exact QT) FRS1 SP1 INN (conj DLE DHI) _ m4 m5 ART4 MU5 WM5).
      intros a. cbn [outside]. clear. lia. }
    assert (PR5 : PRES q DST (rt_live RT Σ) (rt_frames RT Σ) m m5).
    { eapply (PRES_mu q DST _ _ m _ m4 m5 PR4 MU5). intros a Ha _. cbn [outside]. pose proof (FRESH _ Ha) as [N1 N2]. clear - N1 N2. lia. }
    destruct (af_frame_release RT AF Σ1 m5 f 1%nat (rt_frames RT Σ) ART5 FRS1) as (Σ5 & fl & FLC & NAC & FL0 & FLW & FW & REL).
    change (fs_size 1) with 128 in FW. replace (f + 128 - 8) with (f + 120) in FW by (clear; lia). rewrite SPE1 in FLW.
    assert (FLLO : fl + 1 <= lo) by (clear - FLW SPLO; lia).
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (it_rel2 q b f DST lo gp s8 s9 s10 s11 ra s0 s1 s2 s3 s4 s5 s6 s7 fc F0 Ef FLO SFL SHf GF GLO LOB BQ ltac:(unfold USTACK_TOP; exact QT) GD DLO DF DSf SDf SDSf SDLO SDD
                               m5 (DST + sg + n) fl F4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 FL0 FLLO ST5 STF5 FS5 FH5 F3S5 FW FLC DS5 MI5)|].
    cbv beta. intros ms6 (m6 & RS6 & FC6 & MU6 & WM6 & MI6 & ST6 & FLC6 & DS6).
    destruct (REL m6 MU6 WM6 FLC6) as (ART6 & FRS6 & LV6 & SP6 & CR6 & AL6 & AM6).
    apply evt_done. apply (aevt_switch RT PMc Σ1 Σ5 K ms6 AL6 AM6).
    revert FC6. apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ms6 (fun ms => ms_fcsr ms = fc -> aevt Σ5 K ms) RS6).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F5 fc5 FC5. change (fc5 = fc) in FC5. subst fc5.
    assert (NFL : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> ~ (fl <= a < fl + 1)).
    { intros a Ha Hin. replace a with fl in Ha by (clear - Hin; lia). apply NAC. rewrite LV1, FRS1.
      destruct Ha as [H|[H|[H|[H|H]]]]; [exfalso; clear - H FLLO LOB BQ; unfold RT_STACK in *; lia| right; left; exact H| right; right; left; exact H
        | right; right; right; left| right; right; right; right]; destruct H as (f' & k' & Hin' & Hr); exists f', k'; (split; [right; exact Hin'| exact Hr]). }
    destruct (stk_CB bsegs m6 DST (DST + 24) DS6 ltac:(clear; lia)) as (nb & DNB). replace (Z.to_nat (DST + 24 - DST)) with 24%nat in DNB by (clear; lia).
    apply (HK Σ5 (DST + sg + n) q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F5 m6 nb ART6 MI6 ST6).
    - rewrite LV6. exact LV1.
    - exact FRS6.
    - rewrite SP6. exact SPE1.
    - rewrite CR6, CR1. clear; lia.
    - intros a Ha Ho. cbn [outside] in Ho. rewrite (MU6 a); [apply PR5; [exact Ha| clear - Ho; lia]|]. cbn [outside]. split; [exact (NFL _ Ha)| exact Logic.I].
    - clear - HSG HN HSN. lia.
    - exact DNB. }

  eapply aevt_eq; [| eapply (it_signA Σ1 K q b f DST lo fN kN (rt_live RT Σ) (rt_frames RT Σ) m gp s8 s9 s10 s11 ra s0 s1 s2 s3 s4 s5 s6 s7 fc
                               F0 Ef FLO SFL SHf GF GLO LOB B16 BQ ltac:(unfold USTACK_TOP; exact QT) D8 GD DLO DF DSf SDf SDSf SDLO SDD FRS1 LV1 SP1 INN (conj DLE DHI) SDIN FRESH CSEP KR
                               m3 v F1)]; [pj_st_eq| exact HM3| exact ART3| exact PR3| exact HV].
Qed.

End Itoa.
