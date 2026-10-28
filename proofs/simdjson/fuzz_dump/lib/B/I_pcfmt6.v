(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_small R_m2s R_thread I_consts I_qck X_atexit D_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import I_pck I_pcrr I_pcbits I_pcseg I_pchead I_pcms I_pcdint I_pcfmt I_pcd6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section WithRIP6.
Hypothesis RIP : rip_stmt.

Lemma pcom_head6_spec : forall (q A ap : Z) (fmt : list byte) (lo : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  sp = Z_to_bv 64 q -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 ap ->
  stk bsegs m lo q -> lo <= q - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> q <= 2^47 -> q mod 16 = 0 ->
  cstr_at m A fmt -> (1 <= length fmt)%nat -> (A + Z.of_nat (length fmt) + 1 <= lo \/ q <= A) -> A + Z.of_nat (length fmt) + 1 <= 2^47 ->
  chk_ok m A (Z.of_nat (length fmt) + 1) -> pctx m -> mem_inv bsegs m ->
  evt bsegs (pch_post q A ap ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6db6c) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until m. intros -> -> -> ST LO LOLO SPH S16 CS L1 AB AH CHK PCX MI.
  pose proof (cstr_bound m A fmt CS) as (A0 & AB').
  unfold kHighShadowEnd in LOLO.
  pose proof (munch_refl [(q - PCOM_DEPTH, q)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (EUA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  carve_frame 104%nat ST. rename FR into FRh.
  carve_frame 2072%nat ST. rename FR into FRb.
  carve_frame 40%nat ST. rename FR into DIR.
  carve_frame 24%nat ST. rename FR into FRa.
  apply (rw_cells_split_CB bsegs _ _ [] 104 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRh; [| reflexivity].
  cbn [mk_CB_cells app] in FRh.
  apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FRa; [| reflexivity]. cbn [mk_CB_cells app] in FRa.
  xsteps_to 0x91c58%Z.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (CS1 : cstr_at mm A fmt) by
    (apply (cstr_agree m mm A fmt CS); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside] in *; lia) end.
  call internal_strlen_spec; [reflexivity| exact CS1| assumption|].
  assert (EUq : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CHK1 : chk_ok mm A (Z.of_nat (length fmt) + 1)) by
      (eapply chk_ok_agree; [exact CHK | lia | lia | apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside]; unfold SHB in *; lia]);
    assert (PCX1 : pctx mm) by
      (apply (pctx_munch _ m mm PCX MU); [assumption| intros ?x ?Hx; unfold in_PCR in Hx; cbn [outside]; lia]);
    destruct PCX1 as (M2S1 & PC1) end.
  call (pcf_check RIP (q + -2240) A (Z.of_nat (length fmt))).
  all: first [ exact ST | exact CHK1 | exact M2S1 | exact PC1 | assumption | lia | idtac ].
  destruct (cstr_byte _ A fmt 0 CS ltac:(lia)) as (b0 & Hb0 & Bnz0 & _). rewrite Z.add_0_r in Hb0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (Hb0' : bytes_at bsegs mm A [b0]) by
    (apply (bytes_at_agree bsegs m mm _ _ Hb0); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx; cbn [outside length] in *; lia) end.
  pose proof (ro_C1_of_bytes _ _ _ Hb0') as CB0. clear Hb0 Hb0'.
  pose proof (z8_neq b0 Bnz0) as BNZ.
  xsteps_to 0x6dc80%Z.
  replace (q - 4096) with (q + -4096) by lia.
  xsteps_to 0x6dc80%Z.
  pose proof (bv_unsigned_in_range 8 b0) as BR0. unfold bv_modulus in BR0. change (2 ^ Z.of_N 8) with 256 in BR0.
  brF K0.
  xsteps_to 0x6dc80%Z.
  replace (q - 4096) with (q + -4096) by lia.
  xsteps_to 0x6dc80%Z.
  rewrite EUq in POST.
  apply rw_forget in FRa. cbn [cells_size csize Nat.add] in FRa.
  apply evt_done. unfold pch_post. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact POST|]. split; [exact FRh|].
  split; [eexists; exact FRb|]. split; [eexists; exact DIR| eexists; exact FRa].
Qed.

Definition FMT6 (fmt : list Z) : Prop :=
  (exists c, (c = 100 \/ c = 117 \/ c = 120) /\ fmt = [37; 108; c]) \/ fmt = [37; 46; 42; 103].

Lemma FMT6_txt : forall fmt, FMT6 fmt -> Forall (fun c => 0 < c < 256) fmt /\ (3 <= length fmt <= 4)%nat.
Proof.
  intros fmt [(c & CC & ->) | ->]; (split; [repeat constructor; lia | cbn; lia]).
Qed.

Lemma pcom6_spec : forall (A : Z) (fmt : list Z) (ap lo : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 ap -> FMT6 fmt ->
  cstr_at m A (zb8 fmt) -> (A + Z.of_nat (length fmt) + 1 <= lo \/ bv_unsigned sp <= A) -> A + 8 <= 2^47 ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp <= 2^47 ->
  bv_unsigned sp mod 16 = 0 -> 0 <= ap -> ap + 16 < 2^63 ->
  chk_ok m A (Z.of_nat (length fmt) + 1) -> pctx m -> mem_inv bsegs m ->
  evt bsegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6db6c) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until m. intros -> -> FM CS AB AH ST LO LOLO SPH S16 AP0 AP2 CHK PCX MI.
  set (q := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 q) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  unfold kHighShadowEnd in LOLO.
  pose proof (cstr_bound _ _ _ CS) as (A0 & _).
  pose proof (FMT6_txt fmt FM) as (FMB & FML).
  pose proof (munch_refl [(q - PCOM_DEPTH, q)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  call (pcom_head6_spec q A ap (zb8 fmt) lo);
    [ reflexivity | reflexivity | reflexivity | exact ST | lia | (unfold kHighShadowEnd; lia) | lia | exact S16
    | exact CS | rewrite length_zb8; lia | rewrite length_zb8; lia | rewrite length_zb8; lia | rewrite length_zb8; exact CHK | exact PCX | exact MI | ].
  destruct PC1 as (jb & FRb). destruct PC2 as (jd & DIR). destruct POST as (ja & FRa). rename PC into ST, PC0 into FRh.
  call (pcom_setup_spec q jd); [reflexivity | reflexivity | reflexivity | reflexivity | exact DIR | exact S16 | lia | assumption | ].
  destruct FM as [(c & CC & ->) | ->].
  all: cbn [length] in AB.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (BY1 : bytes_at bsegs mm A (zb8 _ ++ [z8])) by
    (apply (bytes_at_agree bsegs _ _ _ _ (proj1 CS)); apply (agree_of_munch _ _ _ _ MU); intros ?x ?Hx;
     cbn [outside length zb8 map app] in *; lia) end.
  1: call (pcom_dl0_spec q A ap c lo);
      [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | exact CC | exact BY1 | assumption | exact ST | lia | lia | lia | lia | lia | lia | assumption | ].
  2: call (pcom_dg0_spec q A ap lo);
      [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | exact BY1 | assumption | exact ST | lia | lia | lia | lia | lia | lia | assumption | ].
  all: destruct POST0 as (jd3 & DIR3).
  all: call (pcom_epi_spec q ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); [reflexivity | exact FRh | lia | assumption | ].
  all: release_frame FRa PC (q + -2216); release_frame DIR3 PC (q + -2176); release_frame FRb PC (q + -104).
  all: unfold pcom_saved in FRh; release_frame FRh PC q.
  all: apply evt_done; unfold pcom_post; rewrite (unsigned_lit q) by lia; do 16 eexists; split; [reflexivity|].
  all: split; [exact MU|]; split; [exact WM|]; split; [assumption| exact PC].
Qed.
End WithRIP6.
