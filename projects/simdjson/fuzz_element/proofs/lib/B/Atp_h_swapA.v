(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim AtpModel.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2
  Sj_new Sj_h_dtor Sj_hkitB Atp_h_defsA Atp_h_vkitA Atp_h_vkit2A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition VB_SWAPOUT : Z := 0xb7074.
Definition SO_RET1 : Z := 0xb70b8.
Definition SO_RET2 : Z := 0xb7158.

Lemma neg_land64 : forall c, 0 < c < 2^64 -> Z.land (0 + - c) 18446744073709551615 = 18446744073709551616 - c.
Proof.
  intros c Hc. change 18446744073709551615 with (2^64 - 1). rewrite zb_land_mask by lia.
  replace (0 + - c) with ((18446744073709551616 - c) + (-1) * 2^64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma slti_neg16a : forall c, 1 <= c -> 16 * c <= 2^63 -> (Z.lxor (18446744073709551616 - 16 * c) 9223372036854775808 <? 9223372036854775808) = true.
Proof.
  intros c Hc Hc'. change 9223372036854775808 with (2^63). rewrite zb_lxor_sign by lia.
  replace (18446744073709551616 - 16 * c + 2 ^ 63) with ((2^63 - 16 * c) + 1 * 2^64) by lia. rewrite Z.mod_add by lia.
  rewrite Z.mod_small by lia. apply Z.ltb_lt. lia.
Qed.
Lemma slti_neg16b : forall c, 1 <= c -> 16 * c <= 2^63 -> (Z.lxor (18446744073709551616 - 16 * c) 9223372036854775808 <? 0 + 9223372036854775808) = true.
Proof. intros c Hc Hc'. rewrite Z.add_0_l. apply slti_neg16a; assumption. Qed.

Definition so_frame (s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma so_walk1 : forall (usp V X lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 80 -> 0x6d9000 <= lo -> usp < 2^63 -> 0 <= V < 2^64 -> 0 <= X < 2^64 ->
  shb_consts m -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a1' : word),
      ms = entry_st (Z_to_bv 64 SO_RET1) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 V) (Z_to_bv 64 V) a1'
             a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc VB_ANNDEL m1
      /\ munch [(usp - 80, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -80)
      /\ rw_cells bsegs m1 (usp + -80) (so_frame s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) /\ shb_consts m1)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 X) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc VB_SWAPOUT m).
Proof.
  intros until m. intros ST LO GLO SPH VV XX (G1 & G2) MI.
  unfold entry_st, VB_SWAPOUT, VB_ANNDEL, SO_RET1, so_frame, SHB in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 80, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 80%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 80 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep.
  zstep. zstep. zstep.
  zstep. zstep.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR|]. split; assumption.
Qed.

Lemma so_walk2 : forall (usp V X A cap NEW cap' lo : Z)
    (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo (usp + -80) -> lo <= usp - 80 -> 0x6d9000 <= lo -> usp <= X -> X + 40 < 2^63 -> 0 < V -> V + 24 <= lo ->
  0 <= A -> A + 16 * cap < 2^63 -> 0 <= cap -> A mod 8 = 0 -> 0 < NEW -> NEW + 16 * cap' < 2^63 -> cap <= cap' ->
  shz m V 24 -> shz m X 40 ->
  rw_cells bsegs m V (vcells A (A + 16 * cap) (A + 16 * cap)) ->
  rw_cells bsegs m X (sb5 NEW (NEW + 16 * cap) (NEW + 16 * cap + 16) (NEW + 16 * cap') V) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a3' a4' : word),
      ms = entry_st (Z_to_bv 64 SO_RET2) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 V)
                 (Z_to_bv 64 NEW) (Z_to_bv 64 A) (Z_to_bv 64 (16 * cap)) a3' a4' a5 a6 a7
                 (Z_to_bv 64 (V + 8)) (Z_to_bv 64 (X + 8)) (Z_to_bv 64 NEW) (Z_to_bv 64 SHB)
                 (Z_to_bv 64 ((V + 8) / 8 + SHB)) (Z_to_bv 64 ((X + 8) / 8 + SHB)) (Z_to_bv 64 (V / 8 + SHB)) s9 s10 s11 t3 t4 t5 t6 F fc e_asan_memcpy m)
    (MS (mkR (Z_to_bv 64 SO_RET1) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 V) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 SO_RET1) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO UX XH V0 VLO A0 AH C0 A8 N0 NH CC SHV SHX VC SB MI.
  unfold entry_st, e_asan_memcpy, vcells, sb5, SO_RET1, SO_RET2, SHB in *.
  pose proof ST as (STa & STb & _).
  pose proof (SHX (X + 8) ltac:(lia)) as RD0. pose proof (SHV (V + 8) ltac:(lia)) as RD1. pose proof (SHV V ltac:(lia)) as RD2.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep.
  zstep. replace (A + 16 * cap + - A) with (16 * cap) by lia.
  zstep. replace (NEW + 16 * cap + - (16 * cap)) with NEW by lia.
  zstep. zstep.
  replace (0 <? NEW + 16 * cap) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (NEW <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  zstep. if_false.
  zstep. rewrite (psigned_small (16 * cap)) by lia. rewrite (pshiftr_16_4 cap) by lia.
  zstep. zstep. zstep. zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; revert K; rewrite ?Z.shiftr_div_pow2 by lia; intros K; lia| clear K].

  lazymatch goal with |- evt _ ?QQ (MS _ _ _ _ _ ?mx _) =>
    assert (REST : forall xa3 xa4 : word, bv_unsigned xa3 = (18446744073709551616 - 16 * cap) mod 2^64 ->
      evt bsegs QQ (MS (mkR (Z_to_bv 64 0xb70b8) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 V)
                           (Z_to_bv 64 1) (Z_to_bv 64 A) (Z_to_bv 64 (16 * cap)) xa3 xa4 a5 a6 a7
                           (Z_to_bv 64 (V + 8)) (Z_to_bv 64 (X + 8)) (Z_to_bv 64 (NEW + 16 * cap)) (Z_to_bv 64 2147450880)
                           (Z_to_bv 64 ((V + 8) / 8 + 2147450880)) (Z_to_bv 64 ((X + 8) / 8 + 2147450880)) (Z_to_bv 64 (V / 8 + 2147450880)) s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0xb7144) fc None mx (seg_rom bsegs))) end.
  2:{ destruct (Z.eq_dec cap 0) as [CZ|CNZ].
      - zstep.
        replace (Z_to_bv 64 (0 + - cap)) with (Z_to_bv 64 0) by (rewrite CZ; reflexivity).
        zstep. zstep. zstep.
        replace (NEW <? NEW + 16 * cap) with false by (symmetry; apply Z.ltb_ge; lia).
        replace (9223372036854775808 <? 9223372036854775808) with false by reflexivity.
        cbn [Z.b2z Z.add Z.land Z.lxor Pos.lxor]. zstep. zstep. cbn [Z.b2z Z.add Z.land Z.lxor Pos.lxor].
        zstep. if_false.
        apply (REST _ _). rewrite CZ. reflexivity.
      - zstep.
        replace (Z_to_bv 64 (0 + - cap)) with (Z_to_bv 64 (18446744073709551616 - cap))
          by (apply Z_to_bv_eqm; replace (0 + - cap) with ((18446744073709551616 - cap) + (-1) * 2^64) by lia; rewrite Z.mod_add by lia; reflexivity).
        zstep.
        replace (Z_to_bv 64 (Z.shiftl (18446744073709551616 - cap) 4)) with (Z_to_bv 64 (18446744073709551616 - 16 * cap))
          by (apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2 by lia; replace ((18446744073709551616 - cap) * 2 ^ 4) with ((18446744073709551616 - 16 * cap) + 15 * 2^64) by lia;
              rewrite Z.mod_add by lia; reflexivity).
        zstep. zstep.
        replace (NEW <? NEW + 16 * cap) with true by (symmetry; apply Z.ltb_lt; lia).
        first [rewrite (slti_neg16a cap) by lia| rewrite (slti_neg16b cap) by lia].
        cbn [Z.b2z Z.add Z.land Z.lxor Pos.lxor]. zstep. zstep. cbn [Z.b2z Z.add Z.land Z.lxor Pos.lxor].
        zstep. if_false.
        apply (REST _ _). rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
  intros xa3 xa4 HX3.
  zstep. rewrite (land7_mod8 A A8). zstep. if_false.
  zstep.
  rewrite HX3.
  replace (Z_to_bv 64 (NEW + 16 * cap + (18446744073709551616 - 16 * cap) mod 2 ^ 64)) with (Z_to_bv 64 NEW)
    by (apply Z_to_bv_eqm; rewrite Z.add_mod_idemp_r by lia; replace (NEW + 16 * cap + (18446744073709551616 - 16 * cap)) with (NEW + 1 * 2^64) by lia;
        rewrite Z.mod_add by lia; reflexivity).
  zstep. zstep.
  apply evt_done. do 2 eexists. cbv delta [mkR]. reflexivity.
Qed.

Definition so_W (usp X V : Z) : list ivl := [(usp - 80, usp); (X, X + 40); (V, V + 24)].

Lemma so_walk3 : forall (usp V X A cap NEW cap' lo : Z)
    (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 s8c s7c s6c s5c s4c s3c s2c s1c s0c rac : word) F fc (m : mem),
  stk bsegs m lo (usp + -80) -> lo <= usp - 80 -> 0x6d9000 <= lo -> usp < 2^63 -> usp <= X -> X + 40 < 2^63 -> 0 < V -> V + 24 <= lo ->
  0 <= A -> A + 16 * cap < 2^63 -> 0 <= cap -> 0 < NEW -> NEW + 16 * cap' < 2^63 -> cap + 1 <= cap' ->
  v_shz (so_W usp X V) m V -> x_shz (so_W usp X V) m X 40 ->
  rw_cells bsegs m (usp + -80) (so_frame s8c s7c s6c s5c s4c s3c s2c s1c s0c rac) ->
  rw_cells bsegs m V (vcells A (A + 16 * cap) (A + 16 * cap)) ->
  rw_cells bsegs m X (sb5 NEW (NEW + 16 * cap) (NEW + 16 * cap + 16) (NEW + 16 * cap') V) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = entry_st rac (Z_to_bv 64 usp) gp tp t0 t1 t2 s0c s1c (Z_to_bv 64 V) (Z_to_bv 64 (cap + 1)) (Z_to_bv 64 A) a3 a4 a5 a6 a7
             s2c s3c s4c s5c s6c s7c s8c s9 s10 s11 t3 t4 t5 t6 F fc VB_ANNNEW m1
      /\ munch (so_W usp X V) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
      /\ rw_cells bsegs m1 V (vcells NEW (NEW + 16 * (cap + 1)) (NEW + 16 * cap'))
      /\ rw_cells bsegs m1 X (sb_cells A A (A + 16 * cap) V))
    (MS (mkR (Z_to_bv 64 SO_RET2) (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 V) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (V + 8)) (Z_to_bv 64 (X + 8)) (Z_to_bv 64 NEW) (Z_to_bv 64 SHB)
             (Z_to_bv 64 ((V + 8) / 8 + SHB)) (Z_to_bv 64 ((X + 8) / 8 + SHB)) (Z_to_bv 64 (V / 8 + SHB)) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SO_RET2) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH UX XH V0 VLO A0 AH C0 N0 NH SC SHV SHX FR VC SB MI.
  unfold entry_st, VB_ANNNEW, vcells, sb5, sb_cells, so_frame, SO_RET2, SHB in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl (so_W usp X V) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold so_W in MU, SHV, SHX.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHX mm MU' WM' (X + 8) ltac:(lia)) as RD0 end.
  zstep. shz_norm. zstep. if_false. clear RD0.
  zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHV mm MU' WM' V ltac:(lia)) as RD0; pose proof (SHV mm MU' WM' (V + 8) ltac:(lia)) as RD1 end.
  zstep. shz_norm. zstep. if_false.
  zstep. shz_norm. zstep. if_false. clear RD0 RD1.
  zstep. zstep. zstep. zstep.
  zstep. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHX mm MU' WM' (X + 16) ltac:(lia)) as RD0 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false. clear RD0.
  zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHV mm MU' WM' (V + 16) ltac:(lia)) as RD0 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false. clear RD0.
  zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHX mm MU' WM' (X + 24) ltac:(lia)) as RD0 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false. clear RD0.
  zstep. zstep. zstep.
  zstep. rewrite shr3_div. zstep.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ => pose proof (SHX mm MU' WM' X ltac:(lia)) as RD0 end.
  zstep. zstep. shz_norm. zstep. if_false. clear RD0.
  zstep. zstep. zstep. zstep. zstep.
  zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  release_frame FR ST usp. zstep.
  replace (NEW + 16 * cap + 16) with (NEW + 16 * (cap + 1)) in * by lia.
  replace (Z.shiftr (bv_signed (Z_to_bv 64 (NEW + 16 * (cap + 1) + - NEW))) 4) with (cap + 1).
  2:{ replace (NEW + 16 * (cap + 1) + - NEW) with (16 * (cap + 1)) by lia. rewrite (psigned_small (16 * (cap + 1))) by lia.
      symmetry. apply pshiftr_16_4. lia. }
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; assumption.
Qed.

Section Swap.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis ANN : annotate_contract RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition swapout_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (lo V X A cap NEW cap' : Z) (els L0 : list (Z * Z)) (m : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT),
    ASTA RT Σ' PMc (fun ms => exists (r : word) m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(X, X + 40); (V, V + 24); (NEW, NEW + 16 * cap)] m m'
         /\ rw_cells bsegs m' V (vcells NEW (NEW + 16 * (cap + 1)) (NEW + 16 * cap'))
         /\ rw_cells bsegs m' X (sb_cells A A (A + 16 * cap) V)
         /\ bytes_at bsegs m' NEW (cells_bytes (velts els))) c
    /\ rt_live RT Σ' = ann_block NEW (16 * cap') (16 * (cap + 1)) ++ vblockA A cap cap ++ L0
    /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ.

Lemma swapout_cps :
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (V X A cap NEW cap' : Z) (els L0 : list (Z * Z)) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 X -> tp = Z_to_bv 64 TPVB ->
  rw_cells bsegs m V (vcells A (A + 16 * cap) (A + 16 * cap)) -> fobj RT Σ m V 24 ->
  rw_cells bsegs m X (sb5 NEW (NEW + 16 * cap) (NEW + 16 * cap + 16) (NEW + 16 * cap') V) ->
  bv_unsigned sp <= X -> X + 40 <= USTACK_TOP -> X mod 8 = 0 ->
  rt_live RT Σ = (NEW, 16 * cap') :: vblockA A cap cap ++ L0 ->
  ((cap = 0 /\ A = 0) \/ (1 <= cap /\ A mod 16 = 0 /\ 0 < A /\ rw_cells bsegs m A (velts els))) -> cap = zlength els ->
  cap + 1 <= cap' -> 16 * cap' <= 0x20001000 -> 0 < NEW -> NEW + 16 * cap' < USTACK_TOP ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 96 + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc VB_SWAPOUT m)))
    (swapout_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo V X A cap NEW cap' els L0 m).
Proof using AF RTF ANN.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V X A cap NEW cap' els L0 lo
    FDO MST -> -> -> VC FOBJ0 SB UX XT X8 LV OLD ELS CC NB N0 NT ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof FOBJ0 as (V8 & _ & (f & kf & INF & FLO & FHI) & _). change ((24 + 7) / 8) with 3 in FHI.
  pose proof (fframe_ranges RT AF Σ m f kf ART0 INF) as (F0 & F1 & FSZ & _).
  unfold zlength in ELS. assert (CAP0 : 0 <= cap) by lia.
  assert (INN : In (NEW, 16 * cap') (rt_live RT Σ)) by (rewrite LV; left; reflexivity).

  assert (OLDL : cap = 0 \/ (1 <= cap /\ 0 < A /\ In (A, 16 * cap) (rt_live RT Σ) /\ A + 16 * cap <= rt_sp0 RT Σ - STACK_WIN /\ (NEW + 16 * cap' <= A \/ A + 16 * cap <= NEW))).
  { destruct OLD as [[C0 _]|(C1 & _ & A0 & _)]; [left; exact C0| right].
    assert (VB : vblockA A cap cap = [(A, 16 * cap)]).
    { unfold vblockA. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). apply ann_block_plain. }
    assert (INA : In (A, 16 * cap) (rt_live RT Σ)) by (rewrite LV, VB; right; left; reflexivity).
    pose proof (af_live_range RT AF Σ m A (16 * cap) ART0 INA) as (_ & A1 & _).
    pose proof (af_live_disj RT AF Σ m NEW (16 * cap') A (16 * cap) [] (vblockA A cap cap ++ L0) ART0 LV ltac:(rewrite VB; left; reflexivity)) as DJ.
    split; [exact C1|]. split; [exact A0|]. split; [exact INA|]. split; [exact A1| exact DJ]. }
  assert (AR : 0 <= A /\ A + 16 * cap <= rt_sp0 RT Σ - STACK_WIN).
  { destruct OLD as [(C0 & AZ)|(C1 & _ & A0 & _)]; [subst A; rewrite C0; ul|]. destruct OLDL as [?|(_ & _ & _ & A1 & _)]; lia. }
  destruct AR as [AR0 AR1].

  assert (FPC1 : fp_client RT Σ lo [(usp - 80, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  pose proof (so_walk1 usp V X lo ra gp (Z_to_bv 64 TPVB) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) (conj G1 G2) MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a1' & -> & MU1 & WM1 & MI1 & ST1 & FR1 & SHB1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC1 MU1 WM1) as ART1.
  pose proof (fobj_munch RT AF Σ m m1 lo _ V 24 ART0 LOW FPC1 MU1 FOBJ0) as FOBJ1.
  assert (VC1 : rw_cells bsegs m1 V (vcells A (A + 16 * cap) (A + 16 * cap))).
  { apply (rw_cells_agree bsegs m m1 _ _ VC); [| exact WM1]. apply (agree_of_munch _ _ _ _ MU1). intros x Hx. unfold vcells in Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [ul| exact I]. }
  assert (SB1 : rw_cells bsegs m1 X (sb5 NEW (NEW + 16 * cap) (NEW + 16 * cap + 16) (NEW + 16 * cap') V)).
  { apply (rw_cells_agree bsegs m m1 _ _ SB); [| exact WM1]. apply (agree_of_munch _ _ _ _ MU1). intros x Hx. unfold sb5 in Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [ul| exact I]. }
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -80)) = usp + -80) by (apply unsigned_lit; ul).

  assert (MID : forall (Σ1 : rts RT) (m2 : mem) (c2 : config) (r : word) (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (F2 : bvmap 5 word) (fc2 : bv 32),
    frm0 fc2 -> rt_live RT Σ1 = rt_live RT Σ -> rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ -> rt_credit RT Σ1 = rt_credit RT Σ ->
    ART RT Σ1 m2 -> mem_inv bsegs m2 -> wmono bsegs m1 m2 -> stk bsegs m2 lo (usp + -80) ->
    rt_pres (rt_live RT Σ) (rt_frames RT Σ) (usp + -80) m1 m2 ->
    ASTA RT Σ1 PMc (eq (MS (mkR (Z_to_bv 64 0xb70b8) (Z_to_bv 64 (usp + -80)) gp (Z_to_bv 64 TPVB) u0 u1 u2 (Z_to_bv 64 X) (Z_to_bv 64 V) r b1 b2 b3 b4 b5 b6 b7
                             s2 s3 s4 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F2 (Z_to_bv 64 0xb70b8) fc2 None m2 (seg_rom bsegs))) c2 ->
    realizes bsegs c2 T).
  2:{ destruct OLD as [(C0 & AZ)|(C1 & A16 & A0 & ELS0)].
      -
        subst A. rewrite C0 in VC1. change (0 + 16 * 0) with 0 in VC1.
        apply (anndel0_cps RT AF Σ PMc (Z_to_bv 64 0xb70b8) (Z_to_bv 64 (usp + -80)) gp (Z_to_bv 64 TPVB) t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 V)
                 (Z_to_bv 64 V) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 V 0 0 lo
                 FDO MST eq_refl eq_refl VC1 FOBJ1 eq_refl eq_refl ART1 MI1); [rewrite EU2; exact ST1| exact LOW| rewrite EU2; ul| rewrite EU2; ul| exact FRM| |].
        { split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM]. }
        intros c2 (Hc2 & FC2).
        destruct (ASTA_unpack_f RT Σ _ _ c2 Hc2 FC2) as (ms2 & (r & m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & _) & FRM2 & Hc2'). clear Hc2.
        destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
        cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2. rewrite (ret_pc_even 0xb70b8) in Hc2' by lia.
        exact (MID Σ m2 c2 r u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 FRM2 eq_refl eq_refl eq_refl eq_refl ART2 MI2 WM2 ST2 PRES2 Hc2').
      -
        assert (VB : vblockA A cap cap = ann_block A (16 * cap) (16 * cap)).
        { unfold vblockA. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
        assert (LVx : rt_live RT Σ = [(NEW, 16 * cap')] ++ ann_block A (16 * cap) (16 * cap) ++ L0) by (rewrite LV, VB; reflexivity).
        destruct OLDL as [C0|(_ & _ & INA & A1 & DJ)]; [lia|].
        apply (anndel_cps RT AF ANN Σ PMc (Z_to_bv 64 0xb70b8) (Z_to_bv 64 (usp + -80)) gp (Z_to_bv 64 TPVB) t0 t1 t2 (Z_to_bv 64 X) (Z_to_bv 64 V)
                 (Z_to_bv 64 V) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 V A (16 * cap) (16 * cap) [(NEW, 16 * cap')] L0 lo
                 FDO MST eq_refl eq_refl VC1 FOBJ1 LVx); [constructor; [cbn; lia| constructor]| lia| | | lia| exact ART1| exact MI1| rewrite EU2; exact ST1| exact LOW| rewrite EU2; ul| rewrite EU2; ul| rewrite EU2| exact FRM| |].
        { rewrite Z.mul_comm. apply Z.mod_mul. lia. }
        { rewrite Z.mul_comm. apply Z.mod_mul. lia. }
        { replace (usp + -80) with (usp + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact SPA. }
        { split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM]. }
        intros c2 ((Σ1 & Hc2 & LV1 & FRS1 & SP1 & CR1) & FC2).
        destruct (ASTA_unpack_f RT Σ1 _ _ c2 Hc2 FC2) as (ms2 & (r & m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2) & FRM2 & Hc2'). clear Hc2.
        destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
        cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2. rewrite (ret_pc_even 0xb70b8) in Hc2' by lia.
        rewrite <- LVx in LV1.
        exact (MID Σ1 m2 c2 r u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 FRM2 LV1 FRS1 SP1 CR1 ART2 MI2 WM2 ST2 PRES2 Hc2'). }

  intros Σ1 m2 c2 r u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 FRM2 LV1 FRS1 SP1 CR1 ART2 MI2 WM2 ST2 PRES2 Hc2.
  assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
  assert (INN1 : In (NEW, 16 * cap') (rt_live RT Σ1)) by (rewrite LV1; exact INN).
  pose proof (af_live_range RT AF Σ1 m2 NEW (16 * cap') ART2 INN1) as (_ & N1 & _).
  pose proof (af_frames_range RT AF Σ m f kf ART0 INF) as (_ & _ & _ & FLV). specialize (FLV NEW (16 * cap') INN).
  assert (INF1 : In (f, kf) (rt_frames RT Σ1)) by (rewrite FRS1; exact INF).
  assert (CLV1 : forall sp' x, V <= x < V + 24 -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) sp' x).
  { intros sp' x Hx. right; right; right; left. exists f, kf. split; [exact INF1| lia]. }

  assert (CLV : forall x, V <= x < V + 24 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + -80) x).
  { intros x Hx. right; right; right; left. exists f, kf. split; [exact INF| lia]. }
  assert (FR2 : rw_cells bsegs m2 (usp + -80) (so_frame s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree bsegs m1 m2 _ _ FR1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2).
    intros x Hx. unfold so_frame in Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
  assert (VC2 : rw_cells bsegs m2 V (vcells A (A + 16 * cap) (A + 16 * cap))).
  { apply (rw_cells_agree bsegs m1 m2 _ _ VC1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2).
    intros x Hx. unfold vcells in Hx. cbn [cells_size csize Nat.add] in Hx. apply CLV. lia. }
  assert (SB2 : rw_cells bsegs m2 X (sb5 NEW (NEW + 16 * cap) (NEW + 16 * cap + 16) (NEW + 16 * cap') V)).
  { apply (rw_cells_agree bsegs m1 m2 _ _ SB1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2).
    intros x Hx. unfold sb5 in Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
  pose proof (fobj_pres RT AF Σ Σ1 _ _ m1 m2 V 24 ART1 FOBJ1 PRES2 FRS1) as FOBJ2.

  set (bs := cells_bytes (velts els)).
  assert (LBS : Z.of_nat (length bs) = 16 * cap).
  { subst bs. rewrite cells_bytes_length by apply velts_wf. rewrite velts_size. lia. }
  assert (SRC2 : bytes_at bsegs m2 A bs).
  { destruct OLD as [(C0 & AZ)|(C1 & A16 & A0 & ELS0)].
    - assert (els = []) as -> by (destruct els; [reflexivity| cbn in ELS; lia]). subst bs A. cbn. unfold bytes_at. cbn [length Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia.
    - destruct OLDL as [C0|(_ & _ & INA & A1 & DJ)]; [lia|].
      assert (ELS1 : rw_cells bsegs m1 A (velts els)).
      { apply (rw_cells_agree bsegs m m1 _ _ ELS0); [| exact WM1]. apply (agree_of_munch _ _ _ _ MU1).
        intros x Hx. rewrite velts_size in Hx. cbn [outside]. split; [ul| exact I]. }
      assert (ELS2 : rw_cells bsegs m2 A (velts els)).
      { apply (rw_cells_agree bsegs m1 m2 _ _ ELS1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2).
        intros x Hx. rewrite velts_size in Hx. right; right; left. exists A, (16 * cap). split; [exact INA| lia]. }
      exact (rw_cells_bytes_at bsegs m2 A _ ELS2). }

  assert (A8 : A mod 8 = 0) by (destruct OLD as [(_ & ->)|(_ & A16 & _)]; [reflexivity| apply mod8_of_mod16; exact A16]).
  pose proof (so_walk2 usp V X A cap NEW cap' lo gp (Z_to_bv 64 TPVB) u0 u1 u2 r b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2
                ST2 ltac:(ul) ltac:(ul) UX ltac:(ul) ltac:(ul) ltac:(ul) AR0 ltac:(ul) CAP0 A8 N0 ltac:(ul) ltac:(lia)
                (fobj_shz RT AF Σ1 m2 V 24 ART2 FOBJ2) (shz_stackv RT AF Σ1 m2 X 40 ART2 ltac:(ul) ltac:(lia) ltac:(ul)) VC2 SB2 MI2) as W2.
  lazymatch type of W2 with evt bsegs _ ?X =>
    assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
  clear W2.
  apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2). clear W2'. intros c2x Hc2x.
  destruct (ASTA_unpack RT Σ1 _ _ c2x Hc2x) as (ms2x & (xa3 & xa4 & ->) & Hc2'). clear Hc2x.

  rewrite <- LBS in Hc2'.
  apply ((rf_asan_memcpy RT RTF) Σ1 PMc (Z_to_bv 64 0xb7158) (Z_to_bv 64 (usp + -80)) gp (Z_to_bv 64 TPVB) u0 u1 u2 (Z_to_bv 64 X) (Z_to_bv 64 V)
           (Z_to_bv 64 NEW) (Z_to_bv 64 A) (Z_to_bv 64 (Z.of_nat (length bs))) xa3 xa4 b5 b6 b7
           (Z_to_bv 64 (V + 8)) (Z_to_bv 64 (X + 8)) (Z_to_bv 64 NEW) (Z_to_bv 64 SHB)
           (Z_to_bv 64 ((V + 8) / 8 + SHB)) (Z_to_bv 64 ((X + 8) / 8 + SHB)) (Z_to_bv 64 (V / 8 + SHB)) s9 s10 s11 u3 u4 u5 u6
           F2 fc2 m2 NEW A bs lo FDO MST eq_refl eq_refl eq_refl ltac:(ul) ltac:(ul) ltac:(lia) SRC2);
    [| | | exact ART2| exact MI2| | split; [exact Hc2'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c2x Hc2'); intros ms0 <-; exact FRM2] |].
  {   unfold checked_src. rewrite EU2, LBS. split.
    - intros POS. destruct OLDL as [C0|(C1 & A0 & INA & A1 & DJ)]; [lia|]. rewrite <- LV1 in INA.
      split; [exact (acc_sub bsegs m2 A (16 * cap) A (16 * cap) (proj2 (af_acc_live RT AF Σ1 m2 A (16 * cap) ART2 INA)) ltac:(lia) ltac:(lia))|].
      left. exists A, (16 * cap). split; [exact INA| lia].
    - left. destruct OLDL as [C0|(C1 & A0 & INA & A1 & DJ)]; [destruct OLD as [(_ & ->)|(C1 & _)]; [ul| lia]| ul]. }
  {   unfold checked_dst. rewrite EU2, LBS.
    pose proof (af_acc_live RT AF Σ1 m2 NEW (16 * cap') ART2 INN1) as [WRN ACN].
    split; [intros POS; split; [exact (acc_sub bsegs m2 NEW (16 * cap') NEW (16 * cap) ACN ltac:(lia) ltac:(lia))| left; exists NEW, (16 * cap'); split; [exact INN1| lia]]|].
    split; [| exact (wr_at_sub m2 NEW (16 * cap') NEW (16 * cap) WRN ltac:(lia) ltac:(lia) ltac:(lia))].
    intros i Hi. right; right; left. exists NEW, (16 * cap'). split; [exact INN1| lia]. }
  {   rewrite LBS. destruct OLDL as [C0|(C1 & A0 & INA & A1 & DJ)]; [destruct OLD as [(_ & ->)|(C1 & _)]; [right; lia| lia]| lia]. }
  { unfold call_ok. rewrite EU2. split; [exact ST2|]. split; [ul|]. split; [ul|]. split; [ul|].
    replace (usp + -80) with (usp + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact SPA. }
  intros c3 (Hc3 & FC3).
  destruct (ASTA_unpack_f RT Σ1 _ _ c3 Hc3 FC3) as (ms3 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & BY3) & FRM3 & Hc3'). clear Hc3.
  destruct RS3 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & ->).
  cbn [ms_fcsr] in FRM3. rewrite EU2 in ST3, PRES3. rewrite LBS in PRES3. rewrite (ret_pc_even 0xb7158) in Hc3' by lia.

  assert (FR3 : rw_cells bsegs m3 (usp + -80) (so_frame s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree bsegs m2 m3 _ _ FR2); [| exact WM3]. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES3).
    intros x Hx. unfold so_frame in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul| ul]. }
  assert (VC3 : rw_cells bsegs m3 V (vcells A (A + 16 * cap) (A + 16 * cap))).
  { apply (rw_cells_agree bsegs m2 m3 _ _ VC2); [| exact WM3]. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES3).
    intros x Hx. unfold vcells in Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply CLV1; lia| lia]. }
  assert (SB3 : rw_cells bsegs m3 X (sb5 NEW (NEW + 16 * cap) (NEW + 16 * cap + 16) (NEW + 16 * cap') V)).
  { apply (rw_cells_agree bsegs m2 m3 _ _ SB2); [| exact WM3]. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES3).
    intros x Hx. unfold sb5 in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul| ul]. }
  pose proof (fobj_pres_ex_live RT AF Σ1 Σ1 _ _ _ _ NEW (16 * cap') m2 m3 V 24 ART2 FOBJ2 PRES3 ltac:(rewrite LV1; auto) eq_refl INN1 ltac:(lia) ltac:(lia)) as FOBJ3.
  assert (FPC3 : fp_client RT Σ1 lo (so_W usp X V)).
  { unfold so_W. constructor; [left; cbn [fst snd]; ul|]. constructor; [left; cbn [fst snd]; ul|]. constructor; [| constructor].
    right; right. exists f, kf. cbn [fst snd]. split; [exact INF1| lia]. }

  pose proof (so_walk3 usp V X A cap NEW cap' lo gp (Z_to_bv 64 TPVB) v0 v1 v2 (Z_to_bv 64 NEW) d1 d2 d3 d4 d5 d6 d7 s9 s10 s11 v3 v4 v5 v6
                s8 s7 s6 s5 s4 s3 s2 s1 s0 ra F3 fc3 m3
                ST3 ltac:(ul) ltac:(ul) ltac:(ul) UX ltac:(ul) ltac:(ul) ltac:(ul) AR0 ltac:(ul) CAP0 N0 ltac:(ul) CC
                (v_shz_of_fp RT AF Σ1 m3 lo _ V ART3 LOW1 FPC3 FOBJ3) (x_shz_of_fp RT AF Σ1 m3 lo _ X 40 ART3 LOW1 FPC3 ltac:(ul) ltac:(lia) ltac:(ul))
                FR3 VC3 SB3 MI3) as W3.
  lazymatch type of W3 with evt bsegs _ ?X =>
    assert (W3' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W3) end.
  clear W3.
  apply (cps_realizes bsegs _ _ _ c3 (asta_evt_c RT AF Σ1 PMc _ _ MST W3') Hc3'). clear W3'. intros c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (m4 & -> & MU4 & WM4 & MI4 & ST4 & VC4 & SB4) & Hc4'). clear Hc4.
  pose proof (art_fp_client RT AF Σ1 m3 m4 lo _ ART3 LOW1 FPC3 MU4 WM4) as ART4.
  pose proof (fobj_munch RT AF Σ1 m3 m4 lo _ V 24 ART3 LOW1 FPC3 MU4 FOBJ3) as FOBJ4.

  assert (LVy : rt_live RT Σ1 = [] ++ ann_block NEW (16 * cap') (16 * cap') ++ (vblockA A cap cap ++ L0)) by (rewrite ann_block_plain, LV1, LV; reflexivity).
  apply (annnew_cps RT AF ANN Σ1 PMc ra sp gp (Z_to_bv 64 TPVB) v0 v1 v2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 (cap + 1)) (Z_to_bv 64 A) d3 d4 d5 d6 d7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F3 fc3 m4 V NEW (16 * cap') (NEW + 16 * (cap + 1)) (cap + 1) [] (vblockA A cap cap ++ L0) lo
           FDO MST eq_refl eq_refl eq_refl VC4 FOBJ4 ltac:(ul) LVy ltac:(constructor) ltac:(lia) ltac:(lia) ltac:(rewrite Z.mul_comm; apply Z.mod_mul; lia) ltac:(lia) ART4 MI4);
    [fold usp; exact ST4| exact LOW1| fold usp; ul| fold usp; exact SPT| exact SPA| exact FRM3| split; [rewrite <- ESP in Hc4'; exact Hc4'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c4 Hc4'); intros ms0 <-; exact FRM3] |].
  intros c5 ((Σ2 & Hc5 & LV2 & FRS2 & SP2 & CR2) & FC5).
  apply Hk. split; [| exact FC5]. exists Σ2.
  split; [| split; [rewrite LV2; reflexivity| split; [rewrite FRS2; exact FRS1| split; [rewrite SP2; exact SP1| rewrite CR2; exact CR1]]]].
  eapply ASTA_conseq; [exact Hc5|]. intros ms (r5 & m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5). fold usp in ST5, PRES5.
  exists r5, m5. split; [exact RS5|].
  split; [split; [exact ART5| split; [exact MI5| split; [| exact ST5]]]|].
  { eapply wmono_trans; [exact WM1|]. eapply wmono_trans; [exact WM2|]. eapply wmono_trans; [exact WM3|]. eapply wmono_trans; [exact WM4| exact WM5]. }
  split.
  {
    intros a Ha Hout. cbn [outside] in Hout. destruct Hout as (HO1 & HO2 & HO3 & _).
    pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
    assert (Ha1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp (bv_unsigned a)) by (rewrite LV1, FRS1; exact Ha).
    rewrite (PRES5 a Ha1). rewrite (MU4 a). 2:{ unfold so_W. cbn [outside]. split; [ul|]. split; [exact HO1|]. split; [exact HO2| exact I]. }
    rewrite (PRES3 a). 2:{ apply (aclient_mono _ _ _ _ _ _ _ Ha1); auto. lia. } 2:{ exact HO3. }
    rewrite (PRES2 a). 2:{ apply (aclient_mono _ _ _ _ _ _ _ Ha); auto. lia. }
    apply MU1. cbn [outside]. split; [ul| exact I]. }
  split.
  { apply (rw_cells_agree bsegs m4 m5 _ _ VC4); [| exact WM5]. apply (agree_of_pres _ _ _ _ _ _ PRES5).
    intros x Hx. unfold vcells in Hx. cbn [cells_size csize Nat.add] in Hx. apply CLV1. lia. }
  split.
  { apply (rw_cells_agree bsegs m4 m5 _ _ SB4); [| exact WM5]. apply (agree_of_pres _ _ _ _ _ _ PRES5).
    intros x Hx. unfold sb_cells in Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }

  apply (bytes_at_agree bsegs m4 m5 _ _). 2:{ apply (agree_of_pres _ _ _ _ _ _ PRES5). intros x Hx. rewrite LBS in Hx. right; right; left. exists NEW, (16 * cap'). split; [exact INN1| lia]. }
  apply (bytes_at_agree bsegs m3 m4 _ _ BY3). apply (agree_of_munch _ _ _ _ MU4). intros x Hx. rewrite LBS in Hx. unfold so_W. cbn [outside].
  split; [ul|]. split; [ul|]. split; [lia| exact I].
Qed.

End Swap.
