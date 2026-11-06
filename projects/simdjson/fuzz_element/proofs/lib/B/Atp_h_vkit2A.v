(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2
  Sj_new Sj_h_dtor Sj_hkitB Atp_h_vkitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition VB_SBCTOR : Z := 0xb6f04.
Definition VB_SBCTOR_MID : Z := 0xb6f7c.
Definition VB_OPNEW_RET : Z := 0x171c54.
Definition VB_SBDTOR : Z := 0xb728c.

Lemma psigned_small : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite zb_signed, unsigned_lit by lia. replace (z <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.
Lemma pshiftr_16_4 : forall c, 0 <= c -> Z.shiftr (16 * c) 4 = c.
Proof. intros c Hc. rewrite Z.shiftr_div_pow2 by lia. replace (16 * c) with (c * 2 ^ 4) by lia. apply Z.div_mul. lia. Qed.
Lemma pshiftr_16_3 : forall c, 0 <= c -> Z.shiftr (16 * c) 3 = 2 * c.
Proof. intros c Hc. rewrite Z.shiftr_div_pow2 by lia. replace (16 * c) with ((2 * c) * 2 ^ 3) by lia. apply Z.div_mul. lia. Qed.
Lemma pshiftr_small0 : forall x n, 0 <= x < 2^n -> 0 <= n -> Z.shiftr x n = 0.
Proof. intros x n Hx Hn. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
Lemma pshiftl_4 : forall c, Z.shiftl c 4 = 16 * c.
Proof. intros c. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Lemma rw_cells_of_bytes : forall (m : mem) a cs, cells_wf cs -> bytes_at bsegs m a (cells_bytes cs) -> wr_at bsegs m a (Z.of_nat (cells_size cs)) -> rw_cells bsegs m a cs.
Proof. intros m a cs WF HB HW. split; [split; [exact WF| exact HB]| exact HW]. Qed.

Definition sbj (j0 j1 j2 j3 j4 : list byte) : list cell := [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4].
Definition sb5 (fi b e c al : Z) : list cell := [C8 (Z_to_bv 64 fi); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 c); C8 (Z_to_bv 64 al)].
Definition sb_cells (fi bb ce al : Z) : list cell :=
  [C8 (Z_to_bv 64 fi); C8 (Z_to_bv 64 bb); C8 (Z_to_bv 64 bb); C8 (Z_to_bv 64 ce); C8 (Z_to_bv 64 al)].

Definition sbc_frame (j : list byte) (s5 s4 s3 s2 s1 s0 ra : word) : list cell := [CB 8 j; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition opn_frame (X : Z) : list cell := [C8 (Z_to_bv 64 (X + 24)); C8 (Z_to_bv 64 VB_SBCTOR_MID)].

Lemma sbctor_walkA : forall (usp X n size al lo : Z) (j0 j1 j2 j3 j4 : list byte)
    (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 80 -> 0x6d9000 <= lo -> usp <= X -> X + 40 < 2^63 ->
  1 <= n < 2^58 -> 0 <= size < 2^58 -> 0 <= al < 2^64 ->
  shb_consts m -> x_shz [(usp - 80, usp); (X, X + 40)] m X 40 ->
  rw_cells bsegs m X (sbj j0 j1 j2 j3 j4) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a2' : word) (j : list byte),
      ms = entry_st (Z_to_bv 64 VB_OPNEW_RET) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (16 * n)) (Z_to_bv 64 n)
             (Z_to_bv 64 (16 * n)) (Z_to_bv 64 n) a2' (Z_to_bv 64 al) a4 a5 a6 a7
             (Z_to_bv 64 X) (Z_to_bv 64 size) (Z_to_bv 64 ((X + 24) / 8 + SHB)) (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_malloc m1
      /\ munch [(usp - 80, usp); (X, X + 40)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -80)
      /\ rw_cells bsegs m1 (usp + -80) (opn_frame X)
      /\ rw_cells bsegs m1 (usp + -64) (sbc_frame j s5 s4 s3 s2 s1 s0 ra)
      /\ rw_cells bsegs m1 X [CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 al)] /\ shb_consts m1)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 n) (Z_to_bv 64 size) (Z_to_bv 64 al) a4 a5 a6 a7
       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc VB_SBCTOR m).
Proof.
  intros until m. intros ST LO GLO UX XH N SZ AL (G1 & G2) SHZ SB MI.
  unfold entry_st, VB_SBCTOR, VB_SBCTOR_MID, VB_OPNEW_RET, e_malloc, sbj, sbc_frame, opn_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 80, usp); (X, X + 40)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 64%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep.
  zstep. zstep. zstep.
  zstep. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (X + 24) ltac:(lia)) as RD3 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false. clear RD3.
  zstep.
  lstep.
  zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (X + 32) ltac:(lia)) as RD4 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false. clear RD4.
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep.
  zstep.

  zstep.
  rename FR into FR1. carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep.
  zstep. rewrite (pshiftr_small0 n 60) by lia. zstep. if_false.
  zstep. rewrite pshiftl_4.
  zstep. zstep.
  try replace (usp + -64 + -16 + 16) with (usp + -64) by lia.
  release_frame FR ST (usp + -64).
  zstep.

  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. zstep.
  zstep. zstep.
  replace (Z.b2z (16 * n <? 1)) with 0 by (destruct (Z.ltb_spec (16 * n) 1); [lia| reflexivity]). rewrite Z.add_0_r.
  zstep. zstep.
  try replace (usp + -64 + -16) with (usp + -80) in * by lia.
  apply evt_done. do 3 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR|]. split; [exact FR1|]. split; [exact SB|].
  split; assumption.
Qed.

Lemma sbctor_walkB : forall (usp X p n size al lo : Z) (j0 j1 j2 j : list byte)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s5c s4c s3c s2c s1c s0c rac : word) F fc (m : mem),
  stk bsegs m lo (usp + -80) -> lo <= usp - 80 -> 0x6d9000 <= lo -> usp < 2^63 -> usp <= X -> X + 40 < 2^63 ->
  0 < p -> p + 16 * n < 2^63 -> 1 <= n < 2^58 -> 0 <= size <= n -> 0 <= al < 2^64 ->
  x_shz [(usp - 80, usp); (X, X + 40)] m X 40 ->
  rw_cells bsegs m (usp + -80) (opn_frame X) ->
  rw_cells bsegs m (usp + -64) (sbc_frame j s5c s4c s3c s2c s1c s0c rac) ->
  rw_cells bsegs m X [CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 al)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a0' a1' a2' a3' a4' a5' : word),
      ms = MS (mkR rac (Z_to_bv 64 usp) gp tp t0 t1 t2 s0c s1c a0' a1' a2' a3' a4' a5' a6 a7 s2c s3c s4c s5c s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc rac) fc None m1 (seg_rom bsegs)
      /\ munch [(usp - 80, usp); (X, X + 40)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
      /\ rw_cells bsegs m1 X (sb5 p (p + 16 * size) (p + 16 * size) (p + 16 * n) al))
    (MS (mkR (Z_to_bv 64 VB_OPNEW_RET) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (16 * n)) (Z_to_bv 64 n) (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 X) (Z_to_bv 64 size) (Z_to_bv 64 ((X + 24) / 8 + SHB)) (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 VB_OPNEW_RET) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH UX XH P PN N SZ AL SHZ FRo FR SB MI.
  unfold opn_frame, sbc_frame, sb5 in *. unfold VB_OPNEW_RET, VB_SBCTOR_MID, SHB in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 80, usp); (X, X + 40)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].
  zstep. zstep. zstep.
  try replace (usp + -80 + 16) with (usp + -64) in * by lia.
  release_frame FRo ST (usp + -64).
  zstep.
  zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' X ltac:(lia)) as RD0 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false. clear RD0.
  zstep. rewrite pshiftl_4. zstep.
  zstep. zstep.
  replace (0 <? p) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (16 * size + p <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  zstep.
  zstep. if_false.
  zstep. zstep. zstep. zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; revert K; rewrite ?Z.shiftr_div_pow2 by lia; intros K; lia| clear K].
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (X + 16) ltac:(lia)) as RD2 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false. clear RD2.
  zstep.
  zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (X + 8) ltac:(lia)) as RD1 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false. clear RD1.
  zstep. rewrite pshiftl_4. zstep.
  zstep. replace (16 * n + p <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  zstep.
  zstep. if_false.
  zstep. zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; revert K; rewrite ?Z.shiftr_div_pow2 by lia; intros K; lia| clear K].
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHZ mm MU' WM' (X + 24) ltac:(lia)) as RD3 end.
  zstep. shz_norm. zstep. if_false. clear RD3.
  zstep.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  release_frame FR ST usp.
  zstep.
  replace (16 * size + p) with (p + 16 * size) in SB by lia. replace (16 * n + p) with (p + 16 * n) in SB by lia.
  apply evt_done. do 7 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact SB].
Qed.

Lemma sbdtor_walk : forall (usp X fi bb ce al lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 16 -> 0x6d9000 <= lo -> usp <= X -> X + 40 < 2^63 ->
  0 < fi < 2^63 -> 0 <= bb < 2^63 -> fi <= ce < 2^63 -> 0 < al < 2^64 ->
  shb_consts m -> x_shz [(usp - 16, usp)] m X 40 ->
  rw_cells bsegs m X (sb_cells fi bb ce al) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a2' a3' a4' a5' a6' a7' : word),
      ms = entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fi) (Z_to_bv 64 (ce - fi)) a2' a3' a4' a5' a6' a7'
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_del m1
      /\ munch [(usp - 16, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
      /\ rw_cells bsegs m1 X (sb_cells fi bb ce al))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc VB_SBDTOR m).
Proof.
  intros until m. intros ST LO GLO UX XH FI BB CE AL (G1 & G2) SHZ SB MI.
  unfold entry_st, VB_SBDTOR, e_del, sb_cells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep.
  zstep. zstep. zstep. clear G1 G2.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' X ltac:(lia)) as RD0; pose proof (SHZ mm MU' WM' (X + 8) ltac:(lia)) as RD1;
    pose proof (SHZ mm MU' WM' (X + 16) ltac:(lia)) as RD2; pose proof (SHZ mm MU' WM' (X + 24) ltac:(lia)) as RD3;
    pose proof (SHZ mm MU' WM' (X + 32) ltac:(lia)) as RD4 end.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. zstep. rewrite shr3_div.
  zstep. if_cases K; zify_cond K; [clear K| exfalso; lia].
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep.
  zstep. zstep. release_frame FR ST usp. zstep.
  apply evt_done. do 7 eexists. split; [cbv delta [mkR]; replace (ce + - fi) with (ce - fi) by lia; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact SB].
Qed.

Lemma sbdtor0_walk : forall (usp X bb ce al lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 16 -> 0x6d9000 <= lo -> usp <= X -> X + 40 < 2^63 ->
  0 <= bb < 2^63 -> 0 <= ce < 2^63 -> 0 <= al < 2^64 ->
  shb_consts m -> x_shz [(usp - 16, usp)] m X 40 ->
  rw_cells bsegs m X (sb_cells 0 bb ce al) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a0' a1' a2' a3' a4' a5' a6' a7' : word),
      ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom bsegs)
      /\ munch [(usp - 16, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
      /\ rw_cells bsegs m1 X (sb_cells 0 bb ce al))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc VB_SBDTOR m).
Proof.
  intros until m. intros ST LO GLO UX XH BB CE AL (G1 & G2) SHZ SB MI.
  unfold entry_st, VB_SBDTOR, sb_cells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep.
  zstep. zstep. zstep. clear G1 G2.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' X ltac:(lia)) as RD0; pose proof (SHZ mm MU' WM' (X + 8) ltac:(lia)) as RD1;
    pose proof (SHZ mm MU' WM' (X + 16) ltac:(lia)) as RD2 end.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  zstep. zstep. rewrite shr3_div.
  zstep. if_cases K; zify_cond K; [clear K| exfalso; lia].
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  zstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].
  zstep. zstep. release_frame FR ST usp. zstep.
  apply evt_done. do 9 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact SB].
Qed.

Section VKit2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition sbctor_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (X n size al lo : Z) (m : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (p : Z),
    ASTA RT Σ' PMc (fun ms => exists (r : word) m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(X, X + 40)] m m'
         /\ rw_cells bsegs m' X (sb5 p (p + 16 * size) (p + 16 * size) (p + 16 * n) al)
         /\ wr_at bsegs m' p (16 * n) /\ acc bsegs m' p (16 * n)) c
    /\ rt_live RT Σ' = (p, 16 * n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (16 * n) /\ 0 < p /\ p mod 16 = 0 /\ p + 16 * n < USTACK_TOP.

Lemma sbctor_cps :
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (X n size al lo : Z) (j0 j1 j2 j3 j4 : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 X -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 al -> tp = Z_to_bv 64 TPVB ->
  1 <= n -> 16 * n <= 0x20001000 -> 0 <= size <= n -> 0 <= al < 2^64 ->
  rw_cells bsegs m X (sbj j0 j1 j2 j3 j4) -> bv_unsigned sp <= X -> X + 40 <= USTACK_TOP -> X mod 8 = 0 ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost (16 * n) <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 80 + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc VB_SBCTOR m)))
            (sbctor_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X n size al lo m).
Proof using AF RTF.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X n size al lo j0 j1 j2 j3 j4
    FDO MST -> -> -> -> -> N1 N2 SZ AL SB UX XT X8 LVM CR ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (FPC : fp_client RT Σ lo [(usp - 80, usp); (X, X + 40)]).
  { constructor; [left; cbn [fst snd]; ul|]. constructor; [left; cbn [fst snd]; ul| constructor]. }
  assert (SHZ0 : x_shz [(usp - 80, usp); (X, X + 40)] m X 40).
  { intros m' MU WM. apply (shz_stackv RT AF Σ m'); [exact (art_fp_client RT AF Σ m m' lo _ ART0 LOW FPC MU WM)| ul| lia| ul]. }
  pose proof (sbctor_walkA usp X n size al lo j0 j1 j2 j3 j4 ra gp (Z_to_bv 64 TPVB) t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                ST0 ltac:(ul) ltac:(ul) UX ltac:(ul) ltac:(lia) ltac:(lia) AL (conj G1 G2) SHZ0 SB MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X0 =>
    assert (W1' : forall ms, eq X0 ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a2' & j & -> & MU1 & WM1 & MI1 & ST1 & FRo1 & FR1 & SB1 & SHB1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1) as ART1.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -80)) = usp + -80) by (apply unsigned_lit; ul).
  apply ((rf_malloc RT RTF) Σ PMc (Z_to_bv 64 VB_OPNEW_RET) (Z_to_bv 64 (usp + -80)) gp (Z_to_bv 64 TPVB) t0 t1 t2 (Z_to_bv 64 (16 * n)) (Z_to_bv 64 n)
           (Z_to_bv 64 (16 * n)) (Z_to_bv 64 n) a2' (Z_to_bv 64 al) a4 a5 a6 a7
           (Z_to_bv 64 X) (Z_to_bv 64 size) (Z_to_bv 64 ((X + 24) / 8 + SHB)) (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 (16 * n) lo
           FDO MST ltac:(lia) eq_refl eq_refl LVM CR ART1 MI1);
    [| | split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  - unfold call_ok. rewrite EU2. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul|].
    replace (usp + -80) with (usp + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact SPA.
  - unfold unwind_ok. rewrite EU2, unsigned_lit by ul. left. ul.
  - intros c2 ((Σ1 & p & Hc2 & LV1 & FRS1 & SP1 & CR1 & P0 & P16 & PTOP) & FC2).
    destruct (ASTA_unpack_f RT Σ1 _ _ c2 Hc2 FC2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WR2 & ACC2) & FRM2 & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2.
    unfold VB_OPNEW_RET in Hc2'. rewrite (ret_pc_even 0x171c54) in Hc2' by lia.
    assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
    assert (INN1 : In (p, 16 * n) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
    pose proof (af_live_range RT AF Σ1 m2 p (16 * n) ART2 INN1) as (_ & PW & _).

    assert (FRo2 : rw_cells bsegs m2 (usp + -80) (opn_frame X)).
    { apply (rw_cells_agree bsegs m1 m2 _ _ FRo1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2).
      intros x Hx. unfold opn_frame in Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
    assert (FR2 : rw_cells bsegs m2 (usp + -64) (sbc_frame j s5 s4 s3 s2 s1 s0 ra)).
    { apply (rw_cells_agree bsegs m1 m2 _ _ FR1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2).
      intros x Hx. unfold sbc_frame in Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
    assert (SB2 : rw_cells bsegs m2 X [CB 8 j0; CB 8 j1; CB 8 j2; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 al)]).
    { apply (rw_cells_agree bsegs m1 m2 _ _ SB1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
    assert (FPC1 : fp_client RT Σ1 lo [(usp - 80, usp); (X, X + 40)]).
    { constructor; [left; cbn [fst snd]; ul|]. constructor; [left; cbn [fst snd]; ul| constructor]. }
    assert (SHZ2 : x_shz [(usp - 80, usp); (X, X + 40)] m2 X 40).
    { intros m' MU WM. apply (shz_stackv RT AF Σ1 m'); [exact (art_fp_client RT AF Σ1 m2 m' lo _ ART2 LOW1 FPC1 MU WM)| ul| lia| ul]. }
    pose proof (sbctor_walkB usp X p n size al lo j0 j1 j2 j gp (Z_to_bv 64 TPVB) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
                  s5 s4 s3 s2 s1 s0 ra F2 fc2 m2 ST2 ltac:(ul) ltac:(ul) ltac:(ul) UX ltac:(ul) P0 ltac:(ul) ltac:(lia) SZ AL SHZ2 FRo2 FR2 SB2 MI2) as W2.
    lazymatch type of W2 with evt bsegs _ ?X0 =>
      assert (W2' : forall ms, eq X0 ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
    apply Hk. split; [| apply (cfrm0_of_asta RT Σ1 PMc _ c3 Hc3); intros ms (m3 & a0' & a1' & a2'' & a3' & a4' & a5' & E & _); rewrite E; exact FRM2].
    exists Σ1, p. split; [| repeat split; assumption].
    eapply ASTA_conseq; [exact Hc3|]. intros ms (m3 & a0' & a1' & a2'' & a3' & a4' & a5' & -> & MU3 & WM3 & MI3 & ST3 & SB3).
    exists a0', m3. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [exact (art_fp_client RT AF Σ1 m2 m3 lo _ ART2 LOW1 FPC1 MU3 WM3)| split; [exact MI3| split; [| exact ST3]]]|].
    { eapply wmono_trans; [exact WM1|]. eapply wmono_trans; [exact WM2| exact WM3]. }
    split.
    {
      intros a Ha Hout. cbn [outside] in Hout. destruct Hout as (HO & _).
      pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
      rewrite (MU3 a). 2:{ cbn [outside]. split; [ul|]. split; [exact HO| exact I]. }
      rewrite (PRES2 a). 2:{ apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia]. }
      apply MU1. cbn [outside]. split; [ul|]. split; [exact HO| exact I]. }
    split; [exact SB3|].
    exact (af_acc_live RT AF Σ1 m3 p (16 * n) (art_fp_client RT AF Σ1 m2 m3 lo _ ART2 LOW1 FPC1 MU3 WM3) INN1).
Qed.

Lemma sbdtor_cps :
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (X fi bb ce al nf lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 X -> tp = Z_to_bv 64 TPVB ->
  rw_cells bsegs m X (sb_cells fi bb ce al) -> bv_unsigned sp <= X -> X + 40 <= USTACK_TOP -> X mod 8 = 0 ->
  0 <= bb < 2^63 -> fi <= ce < 2^63 -> 0 < al < 2^64 ->
  In (fi, nf) (rt_live RT Σ) ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> unwind_ok ra s0 sp -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc VB_SBDTOR m)))
            (free_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fi lo m).
Proof using AF RTF.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X fi bb ce al nf lo
    FDO MST -> -> SB UX XT X8 BB CE AL INF0 ART0 MI0 ST0 LOW LOR SPT SPA UOK FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_live_range RT AF Σ m fi nf ART0 INF0) as (FI0 & FI1 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (FPC : fp_client RT Σ lo [(usp - 16, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  assert (SHZ0 : x_shz [(usp - 16, usp)] m X 40).
  { intros m' MU WM. apply (shz_stackv RT AF Σ m'); [exact (art_fp_client RT AF Σ m m' lo _ ART0 LOW FPC MU WM)| ul| lia| ul]. }
  pose proof (sbdtor_walk usp X fi bb ce al lo ra gp (Z_to_bv 64 TPVB) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) UX ltac:(ul) ltac:(ul) BB CE AL (conj G1 G2) SHZ0 SB MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X0 =>
    assert (W1' : forall ms, eq X0 ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a2' & a3' & a4' & a5' & a6' & a7' & -> & MU1 & WM1 & MI1 & ST1 & SB1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1) as ART1.
  apply (del_ok RT AF (rf_free RT RTF) Σ PMc ra sp gp (Z_to_bv 64 TPVB) t0 t1 t2 s0 s1 (Z_to_bv 64 fi) (Z_to_bv 64 (ce - fi)) a2' a3' a4' a5' a6' a7'
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 fi nf lo FDO MST INF0 eq_refl eq_refl ART1 MI1);
    [| exact UOK| exact FRM| split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  - unfold call_ok. fold usp. split; [exact ST1|]. split; [ul|]. split; [ul|]. split; [ul| exact SPA].
  - intros c2 ((Σ1 & v & Hc2 & LV1 & FRS1 & SP1 & CR1) & FC2).
    apply Hk. split; [| exact FC2]. exists Σ1, v. split; [| repeat split; assumption].
    eapply ASTA_conseq; [exact Hc2|]. intros ms (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2). exists m2.
    split; [exact RS2|]. split; [split; [exact ART2| split; [exact MI2| exact ST2]]|].
    intros a Ha. fold usp in Ha.
    assert (Ha1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp (bv_unsigned a)) by (rewrite FRS1; exact Ha).
    pose proof (aclient_split_c RT AF Σ1 m2 usp (bv_unsigned a) ART2 Ha1) as SPL. rewrite SP1 in SPL.
    rewrite (PRES2 a Ha). apply MU1. cbn [outside]. split; [ul| exact I].
Qed.

Lemma sbdtor0_cps :
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (X bb ce al lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 X -> tp = Z_to_bv 64 TPVB ->
  rw_cells bsegs m X (sb_cells 0 bb ce al) -> bv_unsigned sp <= X -> X + 40 <= USTACK_TOP -> X mod 8 = 0 ->
  0 <= bb < 2^63 -> 0 <= ce < 2^63 -> 0 <= al < 2^64 ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 16 <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc VB_SBDTOR m)))
    (ASTA RT Σ PMc (fun ms => exists (r : word) m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r m' ms
         /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m')).
Proof using AF.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X bb ce al lo
    FDO MST -> -> SB UX XT X8 BB CE AL ART0 MI0 ST0 LOW LOR SPT FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (FPC : fp_client RT Σ lo [(usp - 16, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  assert (SHZ0 : x_shz [(usp - 16, usp)] m X 40).
  { intros m' MU WM. apply (shz_stackv RT AF Σ m'); [exact (art_fp_client RT AF Σ m m' lo _ ART0 LOW FPC MU WM)| ul| lia| ul]. }
  pose proof (sbdtor0_walk usp X bb ce al lo ra gp (Z_to_bv 64 TPVB) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) UX ltac:(ul) BB CE AL (conj G1 G2) SHZ0 SB MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X0 =>
    assert (W1' : forall ms, eq X0 ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  apply Hk. split; [| apply (cfrm0_of_asta RT Σ PMc _ c1 Hc1); intros ms (m1 & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & E & _); rewrite E; exact FRM].
  eapply ASTA_conseq; [exact Hc1|]. intros ms (m1 & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & -> & MU1 & WM1 & MI1 & ST1 & SB1).
  exists a0', m1. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [exact (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1)| split; [exact MI1| split; [exact WM1| exact ST1]]]|].
  intros a Ha. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
  apply MU1. cbn [outside]. split; [ul| exact I].
Qed.

End VKit2.
