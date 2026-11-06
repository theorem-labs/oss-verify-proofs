(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 Z10q FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim Stdio Zpb Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zvm Zvw Z4d.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Layout Shadow Zks Zkt Zi4 D_defs D_kit D_clx Z87 Z82 I_lkit Sj_rtf Zpm Zpl Zq2 Zq3
  Sj_new Zpo Z4a Z6y Z45 Z4e Z4l Z4m Z4n.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition fa_shadow3 (t : list byte) : list cell :=
  map C1 (repeat (Z_to_bv 8 (-15)) 4 ++ repeat (Z_to_bv 8 (-8)) 3 ++ repeat (Z_to_bv 8 (-14)) 5 ++ repeat (Z_to_bv 8 (-8)) 10 ++ repeat (Z_to_bv 8 (-13)) 6)
  ++ [CB 4 t].

Lemma fa_walk11 : forall (usp sp' f : Z) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 : word) (r : word) (j20 : list byte) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 <= sp' -> sp' + 120 < 2^63 -> 1 <= bv_unsigned r < 64 ->
  rw_cells asegs m (sp' + 56) (res_cellsA (f + 120) r j20) -> mem_inv asegs m ->
  evt asegs (eq (sa_regs e_pdtor (Z_to_bv 64 0x96c88) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (f + 96)) a1 a2 a3 a4 a5 a6 a7 f s6 s7 s8 t3 t4 t5 t6 F fc m))
    (sa_regs 0x96c78 x1 sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s6 s7 s8 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH RR RC MI. unfold sa_regs, e_pdtor, res_cellsA in *.
  assert (NZ : bv_eqb r (Z_to_bv 64 0) = false).
  { destruct (bv_eqb r (Z_to_bv 64 0)) eqn:E; [| reflexivity]. exfalso. apply bv_eqb_eq in E. subst r. rewrite unsigned_lit in RR by lia. lia. }
  rewrite NZ in RC.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [C4 r; CB 4 j20] [16]%nat) in RC; [| reflexivity]. cbn [mk_CB_cells app] in RC.
  assert (ER : r = Z_to_bv 64 (bv_unsigned r)) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ER in RC.
  zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ER in K; rewrite a_sx32_small in K by lia; rewrite unsigned_lit in K by lia; lia|].
  zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma fa_walk11b : forall (pc usp sp' f : Z) (x1 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 : word) F fc (m : mem),
  pc = 0x96e00 \/ pc = 0x96ecc -> 0 < f -> f + 256 < 2^63 ->
  evt asegs (eq (sa_regs e_pdtor (Z_to_bv 64 0x96c88) sp' gp tp t0 t1 t2 usp (Z_to_bv 64 (f + 96)) a1 a2 a3 a4 a5 a6 a7 f s6 s7 s8 t3 t4 t5 t6 F fc m))
    (sa_regs pc x1 sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s6 s7 s8 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros PC F0 FH. unfold sa_regs, e_pdtor in *.
  destruct PC as [-> | ->]; (zstep; zstep; zstep; apply evt_done; cbv delta [mkR]; reflexivity).
Qed.

Lemma fa_walk12 : forall (usp sp' f : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 : word) (t jr : list byte) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 <= f / 8 -> f / 8 + 2147450880 + 32 < 2^63 -> 0 <= sp' -> sp' + 120 < 2^63 ->
  (f + 256 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= f) -> (sp' + 120 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= sp') ->
  rw_cells asegs m (f / 8 + 2147450880) (fa_shadow2 t) -> rw_cells asegs m (sp' + 56) [CB 24 jr] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (jr' : list byte),
      ms = MS (mkR (Z_to_bv 64 0x96cc0) (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 (sp' + 56)) a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (-8)) (Z_to_bv 64 (f + 120)) s6 s7 s8
                   (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
              F (Z_to_bv 64 ATPA_DESTROY) fc None m1 (seg_rom asegs)
      /\ munch [(f / 8 + 2147450880 + 12, f / 8 + 2147450880 + 22); (sp' + 56, sp' + 64)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (f / 8 + 2147450880) (fa_shadow1 t)
      /\ rw_cells asegs m1 (sp' + 56) [C8 (Z_to_bv 64 (f + 32)); CB 16 jr'])
    (sa_regs 0x96c88 ra sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s6 s7 s8 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH FD SH SP0 SPH SEP SEP2 FS RC MI.
  unfold sa_regs, ATPA_DESTROY, fa_shadow2, fa_shadow1 in *. cbn [map app repeat] in *.
  apply (rw_cells_split_CB asegs _ _ [] 24 _ [] [8; 16]%nat) in RC; [| reflexivity]. cbn [mk_CB_cells app] in RC.
  set (jr' := firstn 16 (skipn 8 jr)) in RC. clearbody jr'.
  pose proof (munch_refl [(f / 8 + 2147450880 + 12, f / 8 + 2147450880 + 22); (sp' + 56, sp' + 64)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  assert (EP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  zstep. do 10 ls.
  zstep. zstep. zstep.
  apply evt_done. eexists. exists jr'. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; eassumption.
Qed.

Definition sx_regs (pc : Z) (ra : word) (sp' : Z) (gp tp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (f : Z) (s6 s7 s8 : word) (t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (-8)) (Z_to_bv 64 (f + 120)) s6 s7 s8
          (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Lemma fa_walk13a : forall (usp sp' f lo : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 : word) (h3 t : list byte) F fc (m : mem),
  0 < f -> f + 256 <= lo -> f / 8 + 2147450880 + 32 <= lo -> 0 <= f / 8 ->
  (f + 256 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 32 <= f) -> lo < 2^63 ->
  rw_cells asegs m f (fz_hdr (C8 (Z_to_bv 64 0x41b58ab3)) (C8 (Z_to_bv 64 0x1e899)) (C8 (Z_to_bv 64 0x969b0)) h3) -> rw_cells asegs m (f / 8 + 2147450880) (fa_shadow1 t) -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem) (a0' : word),
      ms = sx_regs 0x96d60 ra sp' gp tp t0 t1 t2 usp a0' a1 a2 a3 a4 a5 a6 a7 f s6 s7 s8 t3 t4 t5 t6 F fc m'
      /\ munch [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 32)] m m' /\ wmono asegs m m' /\ mem_inv asegs m')
    (sx_regs 0x96cc0 ra sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s6 s7 s8 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FLO SLO FD SEP LOH FH FS MI.
  unfold sx_regs, fz_hdr, fa_shadow1 in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 32)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  do 3 ls.
  zstep. zstep. ls.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. do 32 ls.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM| eassumption].
Qed.

Lemma fa_walk13b : forall (usp sp' f fl lo : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 : word)
    (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 : word) (LC : list cell) F fc (m : mem),
  0 < f -> f + 256 <= lo -> 0 < fl -> fl + 1 <= lo ->
  0x669000 <= lo -> lo <= sp' -> cells_size LC = 120%nat -> sp' + 120 <= usp - 104 -> usp < 2^63 ->
  stk asegs m lo sp' -> rw_cells asegs m sp' LC -> stk asegs m (sp' + 120) (usp - 104) ->
  rw_cells asegs m (usp - 104) (fa_saved xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11) ->
  ro_cells asegs m (f + 248) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs m fl [C1 (Z_to_bv 8 1)] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m' : mem), ret_st xra (Z_to_bv 64 usp) gp tp xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 0) m' ms
      /\ ms_fcsr ms = fc /\ munch [(fl, fl + 1)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp /\ rw_cells asegs m' fl [C1 (Z_to_bv 8 0)])
    (sx_regs 0x96d60 ra sp' gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s6 s7 s8 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FLO FL0 FLLO GLO LSP SZ LUSP SPH ST FRl STp FRs FW FLC MI.
  unfold sx_regs, fa_saved in *.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EFL : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  assert (EUS : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep. ls. zstep. zstep.
  replace (usp - 104) with (usp + -104) in FRs by lia.
  zstep. do 13 zstep. zstep.
  replace (usp + -104) with (usp - 104) in FRs by lia.
  pose proof (stk_release asegs _ _ _ _ ST FRl ltac:(lia)) as ST1. rewrite SZ in ST1. change (Z.of_nat 120%nat) with 120 in ST1.
  pose proof (stk_merge asegs _ _ _ _ ST1 STp ltac:(lia)) as ST2.
  pose proof (stk_release asegs _ _ _ _ ST2 FRs ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
  replace (usp - 104 + Z.of_nat 104) with usp in ST3 by lia.
  zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST3| eassumption].
Qed.

Definition root_x (usp sp' f : Z) (gp t0 t1 t2 s6 s7 s8 t3 t4 t5 t6 : word) (p1 l1 ty1 : Z) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms =>
    (exists (pc ra' : Z) (m1 : mem) (a4 a5 a6 a7 : word),
        ((pc = ATP_OBJ_A /\ ra' = 0x96e00 /\ ty1 = 123) \/ (pc = ATP_ARR_A /\ ra' = 0x96ecc /\ ty1 = 91))
        /\ ms = lvl_entry pc (Z_to_bv 64 ra') sp' gp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (sp' + 32) (sp' + 104) p1 l1 a4 a5 a6 a7
                  (Z_to_bv 64 f) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 120)) s6 s7 s8
                  (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) t3 t4 t5 t6 F fc m1
        /\ munch [(sp' + 104, sp' + 120)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
        /\ rw_cells asegs m1 (sp' + 104) [C8 (Z_to_bv 64 (f + 120)); C8 (Z_to_bv 64 1)])
    \/ (ty1 <> 123 /\ ty1 <> 91 /\ exists a1 a2 a3 a4 a5 a6 a7 : word,
          ms = sa_regs e_pdtor (Z_to_bv 64 0x96c88) sp' gp (Z_to_bv 64 TPV) t0 t1 t2 usp (Z_to_bv 64 (f + 96)) a1 a2 a3 a4 a5 a6 a7 f s6 s7 s8 t3 t4 t5 t6 F fc m).

Lemma fa_walkR : forall (usp sp' f A tape : Z) (p0 l0 p1 l1 : Z) (rest : list cell) (c1 c2 : cell) (drest : list cell) (tws : list Z)
    (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 : word) (j20 jn : list byte) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 <= f / 8 -> 0x669000 <= sp' -> sp' + 120 < 2^47 ->
  0 < A -> A + 32 < 2^63 -> 0 < tape -> tape + 16 < 2^63 -> 0 <= p1 < 2^64 -> 0 <= l1 < 2^64 -> 0 <= p0 < 2^64 -> 0 <= l0 < 2^64 ->
  (2 <= length tws)%nat -> 0 <= Tf tws 1 < 2^64 ->
  rw_cells asegs m (sp' + 56) [C8 (Z_to_bv 64 (f + 120)); C8 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); CB 4 j20] ->
  rw_cells asegs m (sp' + 104) [CB 16 jn] ->
  rw_cells asegs m (f + 32) (C8 (Z_to_bv 64 A) :: c1 :: c2 :: []) ->
  rw_cells asegs m A (C8 (Z_to_bv 64 p0) :: C8 (Z_to_bv 64 l0) :: C8 (Z_to_bv 64 p1) :: C8 (Z_to_bv 64 l1) :: rest) ->
  rw_cells asegs m (f + 120) (C8 (Z_to_bv 64 tape) :: drest) ->
  bytes_at asegs m tape (u64s (map (Z_to_bv 64) tws)) ->
  shz m A 32 -> shz m (f + 120) 8 -> shz m (tape + 8) 8 ->
  mem_inv asegs m ->
  evt asegs (root_x usp sp' f gp t0 t1 t2 s6 s7 s8 t3 t4 t5 t6 p1 l1 (ttype (Tf tws 1)) F fc m)
    (sa_regs 0x96c78 x1 sp' gp (Z_to_bv 64 TPV) t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s6 s7 s8 t3 t4 t5 t6 F fc m).
Proof.
  intros until m. intros F0 FH FD SPL SPH A0 AH T0 TH P1R L1R P0R L0R TWL TW1 RC JN SV EL DOCC TAPEB SHZA SHZD SHZT MI.
  unfold sa_regs, root_x, lvl_entry, ATP_OBJ_A, ATP_ARR_A, e_pdtor, TPV in *.
  assert (EP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (ET : bv_unsigned (Z_to_bv 64 tape) = tape) by (apply unsigned_lit; lia).
  pose proof (tape_read m tape tws 1 TAPEB ltac:(lia)) as RDT. replace (tape + 8 * 1) with (tape + 8) in RDT by lia.
  assert (TTR : 0 <= ttype (Tf tws 1) < 256) by (unfold ttype; Z.div_mod_to_equations; nia).

  zstep. zstep. if_true.

  zstep. astep. chk0 SHZA (A + 16). zstep. if_false.

  astep. chk0 SHZA (A + 24). zstep. if_false.

  zstep. chk0 SHZD (f + 120). zstep. if_false.

  zstep. zstep. astep. astep. chk0 SHZT (tape + 8). zstep. if_false.

  zstep. zstep. zstep. astep. zstep.
  pose proof (munch_refl [(sp' + 104, sp' + 120)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in JN; [| reflexivity]. cbn [mk_CB_cells app] in JN.

  zstep. if_cases K1; zify_cond K1.
  -
    ls. ls. zstep. zstep. zstep.
    apply evt_done. left. exists 0x999c4, 0x96ecc. eexists. do 4 eexists.
    split; [right; split; [reflexivity| split; [reflexivity| clear - K1 TTR; lia]]|]. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption| eassumption].
  -
    zstep. zstep. if_cases K2; zify_cond K2.
    +
      zstep. zstep. apply evt_done. right. split; [clear - K2 TTR; lia|]. split; [clear - K1 TTR; lia|]. do 7 eexists. cbv delta [mkR]. reflexivity.
    +
      ls. ls. zstep. zstep. zstep.
      apply evt_done. left. exists 0x98e6c, 0x96e00. eexists. do 4 eexists.
      split; [left; split; [reflexivity| split; [reflexivity| clear - K2 TTR; lia]]|]. split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [eassumption| eassumption].
Qed.
