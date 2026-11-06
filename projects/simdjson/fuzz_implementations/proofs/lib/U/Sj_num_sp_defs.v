(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber SjNumU.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Sj_num_kitu Sj_num_kitn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Definition spathu_post_g (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (OUT lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' (v : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom segs)
    /\ frm0 fc'
    /\ munch [(bv_unsigned sp - SPATHU_STACK, bv_unsigned sp); (OUT, OUT + 8)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
    /\ rw_cells segs m' OUT [C8 v] /\ stk segs m' lo (bv_unsigned sp).
Definition spathu_stmt_g (segs : list Segment) (entry gtop : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (A FIRST LAST OUT lo : Z) (txt : list byte) (v0 : word),
  mem_inv segs m -> frm0 fc ->
  stk segs m lo (bv_unsigned sp) -> (lo + SPATHU_STACK <= bv_unsigned sp)%Z -> (gtop <= lo)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  bytes_at segs m A txt -> (A + Z.of_nat (length txt) <= lo)%Z -> (Z.of_nat (length txt) < NUM_TXT_MAX)%Z -> (0 < A)%Z ->
  (A <= FIRST < LAST)%Z -> (LAST <= A + Z.of_nat (length txt))%Z ->
  rw_cells segs m OUT [C8 v0] -> (bv_unsigned sp <= OUT)%Z -> (OUT mod 8 = 0)%Z ->
  evt segs (spathu_post_g segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FIRST) (Z_to_bv 64 LAST) (Z_to_bv 64 OUT) (Z_to_bv 64 53) (Z_to_bv 64 SPATH_A4) (Z_to_bv 64 1)
             a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

Definition SPATHU_ENTRY : Z := 0x5e7c4.

Record spuenv : Type := mkSpuEnv {
  q_ra : word; q_sp : word; q_gp : word; q_tp : word;
  q_s0 : word; q_s1 : word; q_s2 : word; q_s3 : word; q_s4 : word; q_s5 : word;
  q_s6 : word; q_s7 : word; q_s8 : word; q_s9 : word; q_s10 : word; q_s11 : word;
  q_A : Z; q_FIRST : Z; q_LAST : Z; q_OUT : Z; q_lo : Z; q_txt : list byte; q_m0 : mem }.
Notation q_SP E := (bv_unsigned (q_sp E)).
Notation q_TL E := (Z.of_nat (length (q_txt E))).

Record spu_ok (E : spuenv) : Prop := mkSpuOk {
  so_room : (q_lo E + SPATHU_STACK <= q_SP E)%Z;
  so_gtop : (NUMU_GTOP <= q_lo E)%Z;
  so_sp16 : (q_SP E mod 16 = 0)%Z;
  so_tlo : (q_A E + q_TL E <= q_lo E)%Z;
  so_tmax : (q_TL E < NUM_TXT_MAX)%Z;
  so_a0 : (0 < q_A E)%Z;
  so_first : (q_A E <= q_FIRST E < q_LAST E)%Z;
  so_last : (q_LAST E <= q_A E + q_TL E)%Z;
  so_out : (q_SP E <= q_OUT E)%Z;
  so_out8 : (q_OUT E mod 8 = 0)%Z }.

Definition spu_W (E : spuenv) : list (Z * Z) := [(q_SP E - SPATHU_STACK, q_SP E); (q_OUT E, q_OUT E + 8)]%Z.
Notation spu_post E := (spathu_post_g usegs (q_ra E) (q_sp E) (q_gp E) (q_tp E) (q_s0 E) (q_s1 E) (q_s2 E) (q_s3 E) (q_s4 E) (q_s5 E)
                          (q_s6 E) (q_s7 E) (q_s8 E) (q_s9 E) (q_s10 E) (q_s11 E) (q_OUT E) (q_lo E) (q_m0 E)).
Definition spu_saved (E : spuenv) : list cell :=
  [C8 (q_s11 E); C8 (q_s10 E); C8 (q_s9 E); C8 (q_s8 E); C8 (q_s7 E); C8 (q_s6 E); C8 (q_s5 E); C8 (q_s4 E);
   C8 (q_s3 E); C8 (q_s2 E); C8 (q_s1 E); C8 (q_s0 E); C8 (q_ra E)].

Definition SPUINV (E : spuenv) (mm : mem) (nb IP IL FPT FL : Z) : Prop :=
  (exists j, rw_cells usegs mm (q_SP E + -704) [CB 16 j]) /\
  (exists j, rw_cells usegs mm (q_SP E + -688) [CB 24 j]) /\
  rw_cells usegs mm (q_SP E + -664) [C1 (Z_to_bv 8 nb)] /\ (0 <= nb <= 1)%Z /\
  (exists j, rw_cells usegs mm (q_SP E + -663) [CB 7 j]) /\
  rw_cells usegs mm (q_SP E + -656) [C8 (Z_to_bv 64 IP); C8 (Z_to_bv 64 IL); C8 (Z_to_bv 64 FPT); C8 (Z_to_bv 64 FL)] /\
  (exists j, rw_cells usegs mm (q_SP E + -624) [CB 8 j]) /\
  (exists j, rw_cells usegs mm (q_SP E + -616) [CB 504 j]) /\
  (exists j, rw_cells usegs mm (q_SP E + -112) [CB 8 j]) /\
  rw_cells usegs mm (q_SP E + -104) (spu_saved E) /\
  (exists v, rw_cells usegs mm (q_OUT E) [C8 v]) /\
  bytes_at usegs mm (q_A E) (q_txt E) /\
  mem_inv usegs mm /\ munch (spu_W E) (q_m0 E) mm /\ wmono usegs (q_m0 E) mm /\ stk usegs mm (q_lo E) (q_SP E + -704).

Ltac spu_open H :=
  let j1 := fresh "j" in let j2 := fresh "j" in let j3 := fresh "j" in let j4 := fresh "j" in let j5 := fresh "j" in let j6 := fresh "j" in let v := fresh "v" in
  destruct H as ((j1 & PAD0) & (j2 & PNS) & NEG & ?NBR & (j3 & PNS2) & SPANS & (j4 & PERR) & (j5 & BG) & (j6 & DGC) & SAVED & (v & OUTC) & TXT & MI & MU & WM & ST);
  unfold spu_saved in SAVED; unfold spu_W, SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK in MU;
  let TXB := fresh "TXB" in pose proof (bytes_at_bound _ _ _ _ TXT) as TXB.
Ltac spu_forget_obj :=
  lazymatch goal with
  | |- exists j, rw_cells ?s ?m ?A [CB ?n j] =>
      first [ eexists; eassumption
            | lazymatch goal with
              | H : rw_cells s m A ?cs |- _ =>
                  let j := fresh "j" in let Hj := fresh "Hj" in
                  destruct (rw_cells_forget s m A cs H) as [j Hj]; exists j; exact Hj
              end ]
  end.
Ltac spu_close :=
  lazymatch goal with
  | |- SPUINV _ _ _ _ _ _ _ =>
      split; [spu_forget_obj|]; split; [spu_forget_obj|]; split; [eassumption|]; split; [lia|]; split; [spu_forget_obj|];
      split; [eassumption|]; split; [spu_forget_obj|]; split; [spu_forget_obj|]; split; [spu_forget_obj|];
      split; [eassumption|]; split; [eexists; eassumption|];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Notation SPS E pc xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm :=
  (MS (mkR xra (Z_to_bv 64 (q_SP E + -704)) (q_gp E) (q_tp E) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) xF (Z_to_bv 64 pc) xfc None mm (seg_rom usegs)).

Ltac spu_env OK :=
  let ROOM := fresh "ROOM" in let GTOP := fresh "GTOP" in let SP16 := fresh "SP16" in let TLO := fresh "TLO" in let TMAX := fresh "TMAX" in
  let A0 := fresh "A0" in let HF := fresh "HFIRST" in let HL := fresh "HLAST" in let HO := fresh "HOUT" in let HO8 := fresh "HOUT8" in
  destruct OK as [ROOM GTOP SP16 TLO TMAX A0 HF HL HO HO8];
  unfold SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK, NUMU_GTOP, NUM_TXT_MAX in *;
  lazymatch goal with E : spuenv |- _ =>
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 (q_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR end.

Section SPUDEFS.
  Variable E : spuenv.
  Hypothesis OK : spu_ok E.

  Lemma spu_exit : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc ->
    evt usegs (spu_post E) (SPS E 0x6009c xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until FL. intros INV FRM. spu_open INV. spu_env OK.
    do 13 zstep. zstep. zstep.
    release_frame PAD0 ST (q_SP E + -688)%Z.
    release_frame PNS ST (q_SP E + -664)%Z.
    release_frame NEG ST (q_SP E + -663)%Z.
    release_frame PNS2 ST (q_SP E + -656)%Z.
    release_frame SPANS ST (q_SP E + -624)%Z.
    release_frame PERR ST (q_SP E + -616)%Z.
    release_frame BG ST (q_SP E + -112)%Z.
    release_frame DGC ST (q_SP E + -104)%Z.
    release_frame SAVED ST (q_SP E).
    apply evt_done. unfold spathu_post_g. do 17 eexists. exists mm, v.
    split; [cbv delta [mkR]; reflexivity|].
    unfold SPATHU_STACK, NDCU_STACK, P5U_STACK, LMU_STACK, LAFU_STACK.
    split; [exact FRM|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact OUTC| exact ST].
  Qed.

  Lemma spu_0a8 : forall xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm nb IP IL FPT FL,
    SPUINV E mm nb IP IL FPT FL -> frm0 xfc ->
    evt usegs (spu_post E) (SPS E 0x60060 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 (q_OUT E)) xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until FL. intros INV FRM. pose proof INV as INV0. spu_open INV0. spu_env OK.
    assert (D1 : IsData xs0) by exact I. assert (D2 : IsData xs2) by exact I. assert (D3 : IsData xa3) by exact I.
    uwalk ltac:(fun pc => lazymatch pc with
      | 0x60118%Z => u_trap pc
      | 0x6009c%Z => first [ num_cur_mem ltac:(fun m1 => assert (INV1 : SPUINV E m1 nb IP IL FPT FL) by spu_close); eapply spu_exit; [exact INV1 | exact FRM] | fail 100 "cut" pc ]
      end).
  Qed.
End SPUDEFS.
