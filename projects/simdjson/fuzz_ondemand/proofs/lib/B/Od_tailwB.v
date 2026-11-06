(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Od_hbaseA
  Sj_new Sj_num_amem Atp_h_defsA Od_defsB Od_hkit0A Od_deldtorA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac tl_load_hook :=
  match goal with
  | |- context [ov_read_bytes bsegs ?m ?a 1] =>
      let Ea := addr_expr a in
      lazymatch Ea with
      | (?X / 8 + 2147450880)%Z =>
          lazymatch goal with
          | MU : munch ?W ?m0 m, WM : wmono bsegs ?m0 m |- _ =>
              match goal with
              | SHP : (forall m', munch W m0 m' -> wmono bsegs m0 m' -> shz m' ?a0 ?n0) |- _ =>
                  lazymatch X with
                  | a0 => idtac
                  | (a0 + _)%Z => idtac
                  | _ => lazymatch X with (?L + _)%Z => od_lit_in L a0 n0 | _ => od_lit_in X a0 n0 end
                  end;
                  rewrite (shz_read m a0 n0 X a (SHP m MU WM) ltac:(lia) ltac:(reflexivity))
              end
          end
      | Zpos _ =>

          let X := eval vm_compute in (8 * (Ea - 2147450880))%Z in
          lazymatch goal with
          | MU : munch ?W ?m0 m, WM : wmono bsegs ?m0 m |- _ =>
              match goal with
              | SHP : (forall m', munch W m0 m' -> wmono bsegs m0 m' -> shz m' ?a0 ?n0) |- _ =>
                  od_lit_in X a0 n0;
                  rewrite (shz_read m a0 n0 X a (SHP m MU WM) ltac:(lia) ltac:(reflexivity))
              end
          end
      end
  end;
  load_post.
Local Ltac solve_load ::= first [ tl_load_hook | solve_load_image | solve_load_base ].

Definition OD_TAIL : Z := 0x9b9d4.

Definition tx_regs (pc : Z) (ra : word) (S1 : Z) (gp tp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 : word) (F : Z)
    (s11 t3 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7
          s2 s3 s4 s5 s6 (Z_to_bv 64 2147450880) s8 s9 (Z_to_bv 64 (F + 32)) s11 t3 t4 t5 t6)
     FR (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Lemma od_walkT1 : forall (usp S1 F IMPL : Z) (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 : word)
    (pre8 mid rest : list byte) (idx oc ia : word) FR fc (m : mem),
  0x679000 <= S1 -> S1 + 440 <= usp -> usp < 2^63 -> 0 < IMPL -> IMPL + 96 <= S1 -> IMPL mod 8 = 0 ->
  rw_cells bsegs m IMPL (dl_cells (Z_to_bv 64 OD_DPI_VPTR) pre8 idx mid oc ia rest) ->
  ro_cells bsegs m OD_DPI_VT od_vt_cells ->
  (forall m', munch [] m m' -> wmono bsegs m m' -> shz m' IMPL 96) ->
  (forall m', munch [] m m' -> wmono bsegs m m' -> shz m' OD_DPI_VT 96) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a1' a2' : word),
      ms = tx_regs e_deldtor (Z_to_bv 64 0x9ba18) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 IMPL) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 F s11 t3 t4 t5 t6 FR fc m)
    (tx_regs OD_TAIL ra S1 gp tp t0 t1 t2 usp (Z_to_bv 64 IMPL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 F s11 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros GLO SUS SPH IM0 IMR IM8 DPI VT SZI SZV MI.
  unfold tx_regs, OD_TAIL, e_deldtor, dl_cells, OD_DPI_VPTR, OD_DPI_VT, od_vt_cells in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. ual. zstep. if_true.
  zastep. zastep. zastep. zastep. if_true.
  zastep. zastep. zastep. zastep. zastep. zastep. if_true.
  zastep. zastep.
  apply evt_done. do 2 eexists. cbv delta [mkR]. reflexivity.
Qed.

Lemma od_walkT2 : forall (usp S1 F : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 : word)
    (l12 l13 l14 l15 l16 l17 l18 j432 : list byte) FR fc (m : mem),
  0x679000 <= S1 -> S1 + 440 <= usp -> usp < 2^63 -> 0x679000 <= F -> F / 8 + 2147450880 + 64 <= S1 ->
  rw_cells bsegs m (S1 + 248) [C8 (Z_to_bv 64 (F / 8 + 2147450880))] ->
  rw_cells bsegs m (F / 8 + 2147450880 + 12) [CB 1 l12; CB 1 l13; CB 1 l14; CB 1 l15; CB 1 l16; CB 1 l17; CB 1 l18] ->
  rw_cells bsegs m (S1 + 432) [CB 8 j432] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = tx_regs ATPA_DESTROY (Z_to_bv 64 0x9ba48) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 (S1 + 432)) a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 (-8)) (Z_to_bv 64 (F / 8 + 2147450880)) s4 s5 s6 s8 s9 F s11 t3 t4 t5 t6 FR fc m1
      /\ munch [(F / 8 + 2147450880 + 12, F / 8 + 2147450880 + 19); (S1 + 432, S1 + 440)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (F / 8 + 2147450880 + 12) (map C1 (repeat (Z_to_bv 8 (-8)) 7))
      /\ rw_cells bsegs m1 (S1 + 432) [C8 (Z_to_bv 64 (F + 32))])
    (tx_regs 0x9ba18 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 F s11 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros GLO SUS SPH FB FSH FR248 SHC FR432 MI.
  unfold tx_regs, ATPA_DESTROY in *. cbn [map repeat].
  pose proof (munch_refl [(F / 8 + 2147450880 + 12, F / 8 + 2147450880 + 19); (S1 + 432, S1 + 440)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (FD0 : 0 <= F / 8) by (apply Z.div_pos; lia).
  replace (F / 8 + 2147450880 + 12) with (F / 8 + 2147450892) in * by lia.
  replace (F / 8 + 2147450880 + 19) with (F / 8 + 2147450899) in * by lia.
  zstep. zstep. do 7 ls. ls. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma od_walkT3 : forall (usp S1 F : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 : word)
    (b4 b5 b6 : byte) (h0 : list byte) FR fc (m : mem),
  0x679000 <= S1 -> S1 + 440 <= usp -> usp < 2^63 -> 0x679000 <= F -> F + 512 <= S1 -> F / 8 + 2147450880 + 64 <= S1 ->
  (F + 512 <= F / 8 + 2147450880 \/ F / 8 + 2147450880 + 64 <= F) ->
  rw_cells bsegs m (F / 8 + 2147450880 + 4) [C1 b4; C1 b5; C1 b6] ->
  rw_cells bsegs m (S1 + 120) [C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 F)] ->
  rw_cells bsegs m F [CB 8 h0] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a2' : word),
      ms = tx_regs (e_set_shadow 0xf5) (Z_to_bv 64 0x9ba7c) S1 gp tp t0 t1 t2 usp (Z_to_bv 64 (F / 8 + 2147450880)) (Z_to_bv 64 64) a2' a3 a4 a5 a6 a7
                   (Z_to_bv 64 F) (Z_to_bv 64 (F / 8 + 2147450880)) s4 s5 s6 s8 s9 F s11 t3 t4 t5 t6 FR fc m1
      /\ munch [(F / 8 + 2147450880 + 4, F / 8 + 2147450880 + 7); (F, F + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (F / 8 + 2147450880 + 4) (map C1 (repeat (Z_to_bv 8 (-8)) 3))
      /\ rw_cells bsegs m1 F [C8 (Z_to_bv 64 0x45e0360e)])
    (tx_regs 0x9ba48 ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) (Z_to_bv 64 (F / 8 + 2147450880)) s4 s5 s6 s8 s9 F s11 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros GLO SUS SPH FB FR0 FSH FSD SHC FR120 FH MI.
  unfold tx_regs, e_set_shadow in *. cbn [map repeat].
  pose proof (munch_refl [(F / 8 + 2147450880 + 4, F / 8 + 2147450880 + 7); (F, F + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (FD0 : 0 <= F / 8) by (apply Z.div_pos; lia).
  replace (F / 8 + 2147450880 + 4) with (F / 8 + 2147450884) in * by lia.
  replace (F / 8 + 2147450880 + 7) with (F / 8 + 2147450887) in * by lia.
  do 3 ls. zstep. zstep. zstep. ls. zstep. zstep.
  if_cases K; zify_cond K; [exfalso; lia|]. clear K.
  zstep. zstep. zstep. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma od_walkT4 : forall (usp S1 F fl lo : Z) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 : word)
    (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 : word) (LC : list cell) FR fc (m : mem),
  0 < F -> F + 512 <= lo -> 0 < fl -> fl + 1 <= lo ->
  0x679000 <= lo -> lo <= S1 -> cells_size LC = 440%nat -> S1 + 440 <= usp - 104 -> usp - 560 <= S1 -> usp < 2^63 ->
  stk bsegs m lo S1 -> rw_cells bsegs m S1 LC -> stk bsegs m (S1 + 440) (usp - 104) ->
  rw_cells bsegs m (usp - 104) (fa_saved xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11) ->
  ro_cells bsegs m (F + 504) [C8 (Z_to_bv 64 fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem), ret_st xra (Z_to_bv 64 usp) gp tp xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 0) m' ms
      /\ ms_fcsr ms = fc /\ munch [(fl, fl + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp /\ rw_cells bsegs m' fl [C1 (Z_to_bv 8 0)])
    (tx_regs 0x9ba7c ra S1 gp tp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 F) s3 s4 s5 s6 s8 s9 F s11 t3 t4 t5 t6 FR fc m).
Proof.
  intros until m. intros F0 FLO FL0 FLLO GLO LSP SZ LUSP USL SPH ST FRl STp FRs FW FLC MI.
  unfold tx_regs, fa_saved in *.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 F) = F) by (apply unsigned_lit; lia).
  assert (EFL : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  assert (EUS : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep. ls. zstep. zstep.
  replace (usp - 104) with (usp + -104) in FRs by lia.
  zstep. do 13 zstep. zstep.
  replace (usp + -104) with (usp - 104) in FRs by lia.
  pose proof (stk_release bsegs _ _ _ _ ST FRl ltac:(lia)) as ST1. rewrite SZ in ST1. change (Z.of_nat 440%nat) with 440 in ST1.
  pose proof (stk_merge bsegs _ _ _ _ ST1 STp ltac:(lia)) as ST2.
  pose proof (stk_release bsegs _ _ _ _ ST2 FRs ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
  replace (usp - 104 + Z.of_nat 104) with usp in ST3 by lia.
  zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST3| eassumption].
Qed.
