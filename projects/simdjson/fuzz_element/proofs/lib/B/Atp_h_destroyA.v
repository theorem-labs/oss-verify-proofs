(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast SysStep FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Stdio AtpModel.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2
  Sj_new Sj_h_dtor Atp_fzwA Atp_hkit4A Atp_hkit5A Atp_hkit6A Atp_defsA Atp_h_defsA Atp_h_vkitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition VB_CLEAR : Z := 0xb7914.
Definition VB_ANNSHRINK : Z := 0xb6e4c.
Definition VB_ANNSHRINK_RET : Z := 0xb6ed4.
Definition DES_RET1 : Z := 0xbc288.
Definition DES_RET2 : Z := 0xbc2a4.

Lemma clear_loop : forall (n : nat) (b : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < b -> b + 16 * (Z.of_nat n + 1) < 2^63 ->
  evt bsegs (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 b) a4 (Z_to_bv 64 16) (Z_to_bv 64 b) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0xb7970) fc None m (seg_rom bsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 b) a4 (Z_to_bv 64 16) (Z_to_bv 64 (b + 16 * (Z.of_nat n + 1))) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb7960) fc None m (seg_rom bsegs)).
Proof.
  induction n as [|n IH]; intros until m; intros B0 BH.
  - change (Z.of_nat 0 + 1) with 1.
    zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
    zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
    zstep.
    zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
    apply evt_done. atp_st_eq_goal.
  - zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
    zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
    zstep.
    zstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].
    eapply evt_eq. 2: { apply (IH b ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m B0 ltac:(lia)). }
    atp_st_eq_goal.
Qed.

Lemma clear_tail : forall (q V b e c lo : Z) (W : list ivl) (m0 : mem) (ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (j : list byte) F fc (m : mem),
  W = [(q - 16, q); (V + 8, V + 16)] ->
  stk bsegs m lo (q + -16) -> lo <= q - 16 -> q < 2^63 -> 0 < V -> V + 24 <= lo ->
  0 < b < 2^63 -> b <= e < 2^63 -> 0 <= c < 2^63 -> (e - b) mod 16 = 0 ->
  munch W m0 m -> wmono bsegs m0 m -> v_shz W m0 V ->
  rw_cells bsegs m (q + -16) [CB 8 j; C8 ra] -> rw_cells bsegs m V (vcells b e c) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = entry_st ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 ((e - b) / 16)) (Z_to_bv 64 0) (Z_to_bv 64 b) (Z_to_bv 64 e) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc VB_ANNSHRINK m1
      /\ munch W m0 m1 /\ wmono bsegs m0 m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo q /\ rw_cells bsegs m1 V (vcells b b c))
    (MS (mkR ra (Z_to_bv 64 (q + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 (V + 8)) (Z_to_bv 64 ((V + 8) / 8 + 2147450880)) (Z_to_bv 64 b) (Z_to_bv 64 e) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7970) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros -> ST LO SPH V0 VLO B0 E0 C0 EB16 MU WM SHZ FR VC MI.
  unfold entry_st, VB_ANNSHRINK, vcells in *.
  pose proof ST as (STa & STb & _).
  assert (EV : bv_unsigned (Z_to_bv 64 V) = V) by (apply unsigned_lit; lia).
  assert (EQ16 : bv_unsigned (Z_to_bv 64 (q + -16)) = q + -16) by (apply unsigned_lit; lia).
  pose proof (SHZ m MU WM (V + 8) ltac:(lia)) as RD1.
  zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  rewrite (a_signed_small (e + - b)) by lia. rewrite (Z.shiftr_div_pow2 (e + - b) 4) by lia. change (2 ^ 4) with 16. replace (e + - b) with (e - b) by lia.
  ls.
  zstep. zstep. release_frame FR ST q. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| assumption].
Qed.

Lemma clear_walk : forall (q V b e c lo : Z) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo q -> lo <= q - 16 -> 0x6d9000 <= lo -> q < 2^63 -> 0 < V -> V + 24 <= lo ->
  0 < b < 2^63 -> b <= e < 2^63 -> 0 <= c < 2^63 -> (e - b) mod 16 = 0 ->
  shb_consts m -> v_shz [(q - 16, q); (V + 8, V + 16)] m V ->
  rw_cells bsegs m V (vcells b e c) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a5' a6' : word),
      ms = entry_st ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 ((e - b) / 16)) (Z_to_bv 64 0) (Z_to_bv 64 b) (Z_to_bv 64 e) a5' a6' a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc VB_ANNSHRINK m1
      /\ munch [(q - 16, q); (V + 8, V + 16)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo q /\ rw_cells bsegs m1 V (vcells b b c))
    (entry_st ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc VB_CLEAR m).
Proof.
  intros until m. intros ST LO GLO SPH V0 VLO B0 E0 C0 EB16 (G1 & G2) SHZ VC MI.
  unfold entry_st, VB_CLEAR, vcells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(q - 16, q); (V + 8, V + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (EV : bv_unsigned (Z_to_bv 64 V) = V) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep.
  zstep. zstep. zstep. clear G1 G2.
  zstep.
  chk0 SHZ (V + 8). zstep. if_false.
  chk0 SHZ V. zstep. if_false.
  zstep. zstep.
  zstep. if_cases K; zify_cond K.
  -
    rewrite ?unsigned_lit in K by lia. subst e.
    lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm, FR' : rw_cells bsegs ?mm (q + -16) _ |- _ =>
      eapply evt_cut; [eapply (clear_tail q V b b c lo _ m ra gp tp t0 t1 t2 s0 s1 _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ F fc mm eq_refl);
        [eassumption| lia| lia| lia| lia| lia| lia| lia| lia| exact MU'| exact WM'| exact SHZ| exact FR'| eassumption| eassumption] |] end.
    intros ms' (m1 & -> & MU1 & WM1 & MI1 & ST1 & VC1). apply evt_done. exists m1, a5, a6. split; [reflexivity|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1| exact VC1].
  -
    rewrite ?unsigned_lit in K by lia.
    zstep. zstep.
    assert (NX : exists n : nat, e = b + 16 * (Z.of_nat n + 1)).
    { exists (Z.to_nat ((e - b) / 16 - 1)). rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia. }
    destruct NX as [n EN].
    lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm, FR' : rw_cells bsegs ?mm (q + -16) _ |- _ =>
      eapply evt_cut; [eapply evt_eq; [| apply (clear_loop n b ra (Z_to_bv 64 (q + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 (V + 8))
                                                  (Z_to_bv 64 ((V + 8) / 8 + 2147450880)) (Z_to_bv 64 e) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mm (proj1 B0) ltac:(lia))];
                        rewrite EN; atp_st_eq_goal |];
      intros ms' <-;
      eapply evt_cut; [eapply (clear_tail q V b e c lo _ m ra gp tp t0 t1 t2 s0 s1 _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ F fc mm eq_refl);
        [eassumption| lia| lia| lia| lia| lia| lia| lia| lia| exact MU'| exact WM'| exact SHZ| exact FR'| eassumption| eassumption] |] end.
    intros ms' (m1 & -> & MU1 & WM1 & MI1 & ST1 & VC1). apply evt_done. exists m1, (Z_to_bv 64 16), (Z_to_bv 64 b). split; [reflexivity|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1| exact VC1].
Qed.

Lemma annshrink_walk1 : forall (q V b e c k lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo q -> lo <= q - 16 -> 0x6d9000 <= lo -> q < 2^63 -> 0 < V -> V + 24 <= lo ->
  0 < b < 2^63 -> b <= e < 2^63 -> 0 <= c < 2^63 -> 0 <= k -> b + 16 * k < 2^63 ->
  shb_consts m -> v_shz [(q - 16, q)] m V ->
  rw_cells bsegs m V (vcells b e c) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a3' a4' a5' a6' : word),
      ms = entry_st (Z_to_bv 64 VB_ANNSHRINK_RET) (Z_to_bv 64 (q + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 (b + 16 * k)) (Z_to_bv 64 e)
             a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc VB_ANNOTATE m1
      /\ munch [(q - 16, q)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (q + -16)
      /\ rw_cells bsegs m1 (q + -16) [C8 s0; C8 ra]
      /\ rw_cells bsegs m1 V (vcells b e c) /\ shb_consts m1)
    (entry_st ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 V) (Z_to_bv 64 k) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc VB_ANNSHRINK m).
Proof.
  intros until m. intros ST LO GLO SPH V0 VLO B0 E0 C0 K0 BK (G1 & G2) SHZ VC MI.
  unfold entry_st, VB_ANNSHRINK, VB_ANNSHRINK_RET, VB_ANNOTATE, vcells in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(q - 16, q)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (EV : bv_unsigned (Z_to_bv 64 V) = V) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep.
  zstep. zstep. zstep.
  chk0 SHZ V. zstep. if_false.
  zstep. zstep.
  zstep. replace (Z.shiftl k 4) with (16 * k) by (rewrite Z.shiftl_mul_pow2 by lia; lia). zstep.
  zstep. zstep.
  replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (b + 16 * k <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  zstep. if_false.
  zstep. zstep. zstep. zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; revert K; rewrite ?Z.shiftr_div_pow2 by lia; intros K; lia| clear K].
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep.
  chk0 SHZ (V + 8). zstep. if_false.
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. replace (e <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor Pos.lxor]. zstep.
  zstep. if_false.
  zstep.
  apply evt_done. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR|]. split; [assumption|].
  split; assumption.
Qed.

Lemma annshrink_walk2 : forall (q lo : Z) (gp tp t0 t1 t2 s0x s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0c rac : word)
    F fc (m : mem),
  stk bsegs m lo (q + -16) -> lo <= q - 16 -> q < 2^63 ->
  rw_cells bsegs m (q + -16) [C8 s0c; C8 rac] -> mem_inv bsegs m ->
  evt bsegs (fun ms => ret_st rac (Z_to_bv 64 q) gp tp s0c s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 m ms /\ ms_fcsr ms = fc /\ stk bsegs m lo q)
    (MS (mkR (Z_to_bv 64 VB_ANNSHRINK_RET) (Z_to_bv 64 (q + -16)) gp tp t0 t1 t2 s0x s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 VB_ANNSHRINK_RET) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO SPH FR MI. pose proof ST as (STa & STb & _). unfold VB_ANNSHRINK_RET.
  zstep. zstep. zstep. release_frame FR ST q. zstep.
  apply evt_done. split; [unfold ret_st; do 16 eexists; reflexivity| split; [reflexivity| exact ST]].
Qed.

Definition des_frame (s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

Lemma des_walk1 : forall (usp C V b e c lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo usp -> lo <= usp - 32 -> 0x6d9000 <= lo -> usp <= C -> C + 8 < 2^63 -> 0 < V -> V + 24 <= lo -> V mod 8 = 0 ->
  0 < b < 2^63 -> b <= e < 2^63 -> 0 <= c < 2^63 ->
  shb_consts m -> x_shz [(usp - 32, usp)] m C 8 -> v_shz [(usp - 32, usp)] m V ->
  rw_cells bsegs m C [C8 (Z_to_bv 64 V)] -> rw_cells bsegs m V (vcells b e c) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = entry_st (Z_to_bv 64 DES_RET1) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 2147450880) (Z_to_bv 64 V) (Z_to_bv 64 b)
             a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (C / 8 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc VB_CLEAR m1
      /\ munch [(usp - 32, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -32)
      /\ rw_cells bsegs m1 (usp + -32) (des_frame s2 s1 s0 ra)
      /\ rw_cells bsegs m1 C [C8 (Z_to_bv 64 V)] /\ rw_cells bsegs m1 V (vcells b e c) /\ shb_consts m1)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc ATPA_DESTROY m).
Proof.
  intros until m. intros ST LO GLO UC CH V0 VLO V8 B0 E0 C0 (G1 & G2) SHX SHZ RC VC MI.
  unfold entry_st, ATPA_DESTROY, DES_RET1, VB_CLEAR, vcells, des_frame in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EV : bv_unsigned (Z_to_bv 64 V) = V) by (apply unsigned_lit; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  zstep. zstep. zstep. zstep.
  zstep. zstep. zstep.
  zstep.
  chk0 SHX C. zstep. if_false.
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. replace (Z.land V 7) with 0 by (rewrite Z.land_ones with (n := 3) by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  zstep. if_false.
  chk0 SHZ V. zstep. if_false.
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR|]. split; [assumption|]. split; [assumption|].
  split; assumption.
Qed.

Lemma des_walk2 : forall (usp C V lo : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  0 <= C -> C + 8 < 2^63 -> 0 < V -> V + 24 < 2^63 -> V mod 8 = 0 -> x_shz [(usp - 32, usp)] m C 8 -> rw_cells bsegs m C [C8 (Z_to_bv 64 V)] -> mem_inv bsegs m ->
  evt bsegs (eq (MS (mkR (Z_to_bv 64 DES_RET2) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 2147450880) (Z_to_bv 64 V) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 (C / 8 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 VB_ANNDEL) fc None m (seg_rom bsegs)))
    (MS (mkR (Z_to_bv 64 DES_RET1) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 2147450880) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (C / 8 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 DES_RET1) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros UC CH V0 VH V8 SHX RC MI. unfold VB_ANNDEL, DES_RET1, DES_RET2.
  pose proof (SHX m (munch_refl _ m) (wmono_refl bsegs m) C ltac:(lia)) as RDC.
  assert (ES : bv_unsigned (Z_to_bv 64 (C / 8 + 2147450880)) = C / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; lia).
  zstep. shz_norm. zstep. if_false.
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. replace (Z.land V 7) with 0 by (rewrite Z.land_ones with (n := 3) by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  zstep. if_false.
  zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma des_walk3 : forall (usp C V b c lo : Z) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s2c s1c s0c rac : word) (ce : cell) F fc (m : mem),
  stk bsegs m lo (usp + -32) -> lo <= usp - 32 -> usp < 2^63 -> 0 <= C -> C + 8 < 2^63 -> 0 < V -> V + 24 < 2^63 -> V mod 8 = 0 -> 0 < b < 2^63 -> b <= c < 2^63 ->
  x_shz [(usp - 32, usp)] m C 8 -> v_shz [(usp - 32, usp)] m V ->
  rw_cells bsegs m C [C8 (Z_to_bv 64 V)] -> rw_cells bsegs m V [C8 (Z_to_bv 64 b); ce; C8 (Z_to_bv 64 c)] -> csize ce = 8%nat ->
  rw_cells bsegs m (usp + -32) (des_frame s2c s1c s0c rac) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a2' : word),
      ms = entry_st rac (Z_to_bv 64 usp) gp tp t0 t1 t2 s0c s1c (Z_to_bv 64 b) (Z_to_bv 64 (c - b)) a2' a3 a4 a5 a6 a7
             s2c s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_del m
      /\ stk bsegs m lo usp)
    (MS (mkR (Z_to_bv 64 DES_RET2) (Z_to_bv 64 (usp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 2147450880) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (C / 8 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 DES_RET2) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO SPH UC CH V0 VH V8 B0 C0 SHX SHZ RC VC CE FR MI. unfold e_del, des_frame, DES_RET2 in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 32, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (SHX m MU WM C ltac:(lia)) as RDC.
  assert (ES : bv_unsigned (Z_to_bv 64 (C / 8 + 2147450880)) = C / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  assert (EV : bv_unsigned (Z_to_bv 64 V) = V) by (apply unsigned_lit; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; lia).
  assert (VC2 : rw_cells bsegs m (V + 16) [C8 (Z_to_bv 64 c)]).
  { change ([C8 (Z_to_bv 64 b); ce; C8 (Z_to_bv 64 c)]) with ([C8 (Z_to_bv 64 b); ce] ++ [C8 (Z_to_bv 64 c)]) in VC.
    apply Sj_stage1_kit.rw_cells_app in VC. destruct VC as [_ X]. cbn [cells_size Nat.add] in X. rewrite CE in X. cbn [csize Nat.add] in X.
    replace (V + Z.of_nat 16) with (V + 16) in X by lia. exact X. }
  zstep. shz_norm. zstep. if_false.
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
  zstep. replace (Z.land V 7) with 0 by (rewrite Z.land_ones with (n := 3) by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  zstep. if_false.
  chk0 SHZ V. zstep. if_false.
  zstep.
  chk0 SHZ (V + 16). zstep. if_false.
  zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. release_frame FR ST usp. zstep.
  apply evt_done. eexists. split; [unfold entry_st; cbv delta [mkR]; replace (c + - b) with (c - b) by lia; reflexivity| exact ST].
Qed.

Section Destroy.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis ANN : annotate_contract RT.

Local Ltac ul := unfold ATPA_DESTROY_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma annshrink_cps :
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (V b n v' k : Z) (l1 L0 : list (Z * Z)) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 k -> tp = Z_to_bv 64 TPVB ->
  rw_cells bsegs m V (vcells b (b + v') (b + n)) -> fobj RT Σ m V 24 ->
  rt_live RT Σ = l1 ++ ann_block b n (16 * k) ++ L0 -> Forall (fun e => fst e <> b) l1 ->
  0 <= v' <= n -> 0 <= k -> 16 * k <= n -> v' mod 16 = 0 -> n mod 16 = 0 -> 1 <= n <= 0x20001000 ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 16 + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc VB_ANNSHRINK m)))
    (ann_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo b n v' l1 L0 m).
Proof using AF ANN.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m V b n v' k l1 L0 lo
    FDO MST -> -> -> VC FOBJ0 LV L1 V0 K0 KN V16 N16 NB ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof FOBJ0 as (V8 & _ & (f & kf & INF & FLO & FHI) & _). change ((24 + 7) / 8) with 3 in FHI.
  pose proof (fframe_ranges RT AF Σ m f kf ART0 INF) as (F0 & F1 & FSZ & _).
  assert (INB : In (b, 16 * k) (rt_live RT Σ)) by (rewrite LV; apply in_or_app; right; apply in_or_app; left; apply ann_block_vis).
  pose proof (af_live_range RT AF Σ m b (16 * k) ART0 INB) as (B0 & B1 & _).
  assert (FPC : fp_client RT Σ lo [(usp - 16, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  assert (FPC2 : fp_client RT Σ lo [(usp - 32, usp + -16)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  pose proof (v_shz_of_fp RT AF Σ m lo _ V ART0 LOW FPC FOBJ0) as SHZ0.

  pose proof (annshrink_walk1 usp V b (b + v') (b + n) k lo ra gp (Z_to_bv 64 TPVB) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) K0 ltac:(ul)
                (conj G1 G2) SHZ0 VC MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a3' & a4' & a5' & a6' & -> & MU1 & WM1 & MI1 & ST1 & FR1 & VC1 & SHB1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1) as ART1.
  pose proof (fobj_munch RT AF Σ m m1 lo _ V 24 ART0 LOW FPC MU1 FOBJ0) as FOBJ1.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -16)) = usp + -16) by (apply unsigned_lit; ul).

  pose proof (v_shz_of_fp RT AF Σ m1 lo _ V ART1 LOW FPC2 FOBJ1) as SHZ1.
  replace (usp - 32) with (usp + -16 - 16) in SHZ1 by lia.
  pose proof (annwrap_walk (usp + -16) V b (b + v') (b + n) (b + 16 * k) (b + v') lo (Z_to_bv 64 VB_ANNSHRINK_RET) gp (Z_to_bv 64 TPVB)
                t0 t1 t2 s0 s1 a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
                ST1 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) SHB1 SHZ1 VC1 MI1) as W2.
  unfold entry_st in W2 at 2.
  lazymatch type of W2 with evt bsegs _ ?X =>
    assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
  clear W2.
  apply (cps_realizes bsegs _ _ _ c1 (asta_evt_c RT AF Σ PMc _ _ MST W2') Hc1'). clear W2'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & a4'' & a5'' & -> & MU2 & WM2 & MI2 & ST2 & VC2) & Hc2'). clear Hc2.
  pose proof (art_fp_client RT AF Σ m1 m2 lo _ ART1 LOW FPC2 ltac:(replace (usp - 32) with (usp + -16 - 16) by lia; exact MU2) WM2) as ART2.
  assert (FR2 : rw_cells bsegs m2 (usp + -16) [C8 s0; C8 ra]).
  { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FR1). apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [lia| exact I]. }

  apply (ANN Σ PMc (Z_to_bv 64 VB_ANNSHRINK_RET) (Z_to_bv 64 (usp + -16)) gp (Z_to_bv 64 TPVB) t0 t1 t2 s0 s1
           (Z_to_bv 64 b) (Z_to_bv 64 (b + n)) (Z_to_bv 64 (b + 16 * k)) (Z_to_bv 64 (b + v')) a4'' a5'' a6' a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 b n (16 * k) v' l1 L0 lo FDO MST LV L1);
    try reflexivity; try assumption; try (clear - V0 K0 KN V16 N16 NB; Z.div_mod_to_equations; lia).
  - unfold call_ok. rewrite EU2. split; [exact ST2|]. split; [ul|]. split; [ul|]. split; [ul|].
    replace (usp + -16) with (usp + (-1) * 16) by lia. rewrite Z.mod_add by lia. exact SPA.
  - intros c3 (Σ1 & r & Hc3 & LV1 & FRS1 & SP1 & CR1).
    destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3) & Hc3'). clear Hc3.
    destruct RS3 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & ->).
    rewrite EU2 in ST3, PRES3.
    unfold VB_ANNSHRINK_RET in Hc3'. rewrite (ret_pc_even 0xb6ed4) in Hc3' by lia.
    assert (FR3 : rw_cells bsegs m3 (usp + -16) [C8 s0; C8 ra]).
    { apply (rw_cells_agree bsegs m2 m3 _ _ FR2); [| exact WM3]. apply (agree_of_pres _ _ _ _ _ _ PRES3).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. ul. }
    pose proof (annshrink_walk2 usp lo gp (Z_to_bv 64 TPVB) u0 u1 u2 s0 s1 r b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  u3 u4 u5 u6 s0 ra F3 fc m3 ST3 ltac:(ul) ltac:(ul) FR3 MI3) as W3.
    unfold VB_ANNSHRINK_RET in W3.
    lazymatch type of W3 with evt bsegs _ ?X =>
      assert (W3' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W3) end.
    clear W3.
    apply (cps_realizes bsegs _ _ _ c3 (asta_evt_c RT AF Σ1 PMc _ _ MST W3') Hc3'). clear W3'. intros c4 Hc4.
    apply Hk. split; [| apply (cfrm0_of_asta RT Σ1 PMc _ c4 Hc4); intros ms (_ & E & _); rewrite E; exact FRM].
    exists Σ1. split; [| repeat split; assumption].
    eapply ASTA_conseq; [exact Hc4|]. intros ms (RS4 & _ & ST4). exists r, m3.
    split; [rewrite ESP; exact RS4|].
    split; [split; [exact ART3| split; [exact MI3| split; [exact (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WM1 WM2) WM3)| exact ST4]]]|].
    intros a Ha. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
    rewrite (PRES3 a), (MU2 a), (MU1 a); [reflexivity| | |].
    + cbn [outside]. split; [ul| exact I].
    + cbn [outside]. split; [ul| exact I].
    + apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
Qed.

Theorem vdestroy_ok : vdestroy_cpsA RT.
Proof using AF RTF ANN.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m C V A cap size els L0 lo
    FDO MST -> -> UC CT CM8 RC VR VL LVPOS CAP1 FOBJ0 ART0 MI0 ST0 LOW LOR SPT SPA UOK FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct VR as (ESZ & SZR & CAPB & A0 & AH & SV & [(C0 & _)|(CP1 & A16 & APOS & EL)]); [lia|].
  unfold vliveA, vblockA in VL. destruct (Z.eqb_spec cap 0) as [|_]; [lia|].
  set (n := 16 * cap) in *.
  pose proof FOBJ0 as (V8 & _ & (f & kf & INF & FLO & FHI) & _). change ((24 + 7) / 8) with 3 in FHI.
  pose proof (fframe_ranges RT AF Σ m f kf ART0 INF) as (F0 & F1 & FSZ & _).
  assert (INA : In (A, 16 * size) (rt_live RT Σ)) by (rewrite VL; apply in_or_app; left; apply ann_block_vis).
  pose proof (af_live_range RT AF Σ m A _ ART0 INA) as (_ & AR1 & _).
  assert (FPC : fp_client RT Σ lo [(usp - 32, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  assert (FPC2 : fp_client RT Σ lo [(usp + -32 - 16, usp + -32); (V + 8, V + 16)]).
  { constructor; [left; cbn [fst snd]; ul|]. constructor; [| constructor]. right; right. exists f, kf. cbn [fst snd]. split; [exact INF| lia]. }
  assert (SHX0 : x_shz [(usp - 32, usp)] m C 8).
  { intros m' MU WM. apply (shz_stackv RT AF Σ m' C 8 (art_fp_client RT AF Σ m m' lo _ ART0 LOW FPC MU WM)); ul. }
  pose proof (v_shz_of_fp RT AF Σ m lo _ V ART0 LOW FPC FOBJ0) as SHZ0.

  pose proof (des_walk1 usp C V A (A + 16 * size) (A + n) lo ra gp (Z_to_bv 64 0x6b6ea8) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) UC ltac:(ul) ltac:(ul) ltac:(ul) V8 ltac:(subst n; ul) ltac:(subst n; ul) ltac:(subst n; ul)
                (conj G1 G2) SHX0 SHZ0 RC SV MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & RC1 & VC1 & SHB1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1) as ART1.
  pose proof (fobj_munch RT AF Σ m m1 lo _ V 24 ART0 LOW FPC MU1 FOBJ0) as FOBJ1.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; ul).

  pose proof (v_shz_of_fp RT AF Σ m1 lo _ V ART1 LOW FPC2 FOBJ1) as SHZ1.
  pose proof (clear_walk (usp + -32) V A (A + 16 * size) (A + n) lo (Z_to_bv 64 DES_RET1) gp (Z_to_bv 64 0x6b6ea8) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 2147450880)
                (Z_to_bv 64 A) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (C / 8 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
                ST1 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(subst n; ul) ltac:(subst n; ul) ltac:(subst n; ul)
                ltac:(replace (A + 16 * size - A) with (size * 16) by lia; apply Z.mod_mul; lia) SHB1 SHZ1 VC1 MI1) as W2.
  unfold entry_st in W2 at 2.
  lazymatch type of W2 with evt bsegs _ ?X =>
    assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
  clear W2.
  apply (cps_realizes bsegs _ _ _ c1 (asta_evt_c RT AF Σ PMc _ _ MST W2') ltac:(unfold entry_st, DES_RET1 in Hc1' |- *; exact Hc1')). clear W2'. intros c2 Hc2.
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & a5' & a6' & -> & MU2 & WM2 & MI2 & ST2 & VC2) & Hc2'). clear Hc2.
  pose proof (art_fp_client RT AF Σ m1 m2 lo _ ART1 LOW FPC2 MU2 WM2) as ART2.
  pose proof (fobj_munch RT AF Σ m1 m2 lo _ V 24 ART1 LOW FPC2 MU2 FOBJ1) as FOBJ2.
  assert (FR2 : rw_cells bsegs m2 (usp + -32) (des_frame s2 s1 s0 ra)).
  { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FR1). apply (agree_of_munch _ _ _ _ MU2). intros x Hx. unfold des_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    cbn [outside]. split; [lia|]. split; [clear - Hx FHI F1 LOW LOR; ul| exact I]. }
  assert (RC2 : rw_cells bsegs m2 C [C8 (Z_to_bv 64 V)]).
  { apply (rw_cells_agree_nw bsegs m1 m2 _ _ RC1). apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn [cells_size csize Nat.add] in Hx.
    cbn [outside]. split; [clear - Hx UC; lia|]. split; [clear - Hx UC FHI F1 LOW LOR; ul| exact I]. }
  replace ((A + 16 * size - A) / 16) with size in Hc2' by (replace (A + 16 * size - A) with (size * 16) by lia; rewrite Z.div_mul by lia; reflexivity).
  assert (VC2' : rw_cells bsegs m2 V (vcells A (A + 0) (A + n))) by (rewrite Z.add_0_r; exact VC2).

  apply (annshrink_cps Σ PMc (Z_to_bv 64 DES_RET1) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0x6b6ea8) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 2147450880)
           (Z_to_bv 64 V) (Z_to_bv 64 size) (Z_to_bv 64 0) (Z_to_bv 64 A) (Z_to_bv 64 (A + 16 * size)) a5' a6' a7 (Z_to_bv 64 (C / 8 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2
           V A n 0 size [] L0 lo FDO MST eq_refl eq_refl eq_refl VC2' FOBJ2 VL (Forall_nil _));
    [subst n; lia| lia| subst n; lia| reflexivity| subst n; clear - CP1; Z.div_mod_to_equations; lia| subst n; clear - CP1 CAPB; lia
    | exact ART2| exact MI2| rewrite EU2; exact ST2| exact LOW| rewrite EU2; ul| rewrite EU2; ul
    | rewrite EU2; replace (usp + -32) with (usp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact SPA| exact FRM
    | split; [unfold entry_st, DES_RET1 in Hc2' |- *; exact Hc2'| apply (cfrm0_of_asta RT Σ PMc (eq _) c2 Hc2'); intros ms0 <-; exact FRM] |].
  intros c3 ((Σ1 & Hc3 & LV1 & FRS1 & SP1 & CR1) & FC3).
  destruct (ASTA_unpack_f RT Σ1 _ _ c3 Hc3 FC3) as (ms3 & (r1 & m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3) & FRM3 & Hc3'). clear Hc3.
  destruct RS3 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F3 & fc3 & ->).
  cbn [ms_fcsr] in FRM3. rewrite EU2 in ST3, PRES3. unfold DES_RET1 in Hc3'. rewrite (ret_pc_even 0xbc288) in Hc3' by lia. cbn [app] in LV1.
  assert (PR3 : forall a : word, usp - 32 <= bv_unsigned a < USTACK_TOP \/ in_fframe (rt_frames RT Σ) (bv_unsigned a) -> m3 a = m2 a).
  { intros a [Ha|Ha]; apply PRES3; [left; ul| right; right; right; left; exact Ha]. }
  assert (FR3 : rw_cells bsegs m3 (usp + -32) (des_frame s2 s1 s0 ra)).
  { apply (rw_cells_agree bsegs m2 m3 _ _ FR2); [| exact WM3]. intros a Ha. unfold des_frame in Ha. cbn [cells_size csize Nat.add] in Ha. apply PR3. left. ul. }
  assert (RC3 : rw_cells bsegs m3 C [C8 (Z_to_bv 64 V)]).
  { apply (rw_cells_agree bsegs m2 m3 _ _ RC2); [| exact WM3]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply PR3. left. ul. }
  assert (VC3 : rw_cells bsegs m3 V (vcells A (A + 0) (A + n))).
  { apply (rw_cells_agree bsegs m2 m3 _ _ VC2'); [| exact WM3]. intros a Ha. unfold vcells in Ha. cbn [cells_size csize Nat.add] in Ha.
    apply PR3. right. exists f, kf. split; [exact INF| lia]. }
  pose proof (fobj_pres RT AF Σ Σ1 (rt_live RT Σ) (usp + -32) m2 m3 V 24 ART2 FOBJ2 PRES3 FRS1) as FOBJ3.
  assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
  assert (FPC1 : fp_client RT Σ1 lo [(usp - 32, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  assert (SHX3 : x_shz [(usp - 32, usp)] m3 C 8).
  { intros m' MU WM. apply (shz_stackv RT AF Σ1 m' C 8 (art_fp_client RT AF Σ1 m3 m' lo _ ART3 LOW1 FPC1 MU WM)); rewrite ?SP1; ul. }

  pose proof (des_walk2 usp C V lo gp (Z_to_bv 64 0x6b6ea8) u0 u1 u2 r1 b1 b2 b3 b4 b5 b6 b7 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F3 fc3 m3
                ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) V8 SHX3 RC3 MI3) as W3.
  unfold DES_RET1 in W3.
  lazymatch type of W3 with evt bsegs _ ?X =>
    assert (W3' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W3) end.
  clear W3.
  apply (cps_realizes bsegs _ _ _ c3 (asta_evt_c RT AF Σ1 PMc _ _ MST W3') Hc3'). clear W3'. intros c4 Hc4.
  destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & <- & Hc4'). clear Hc4.

  apply (anndel_cps RT AF ANN Σ1 PMc (Z_to_bv 64 DES_RET2) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0x6b6ea8) u0 u1 u2 (Z_to_bv 64 C) (Z_to_bv 64 2147450880)
           (Z_to_bv 64 V) (Z_to_bv 64 0) b2 b3 b4 b5 b6 b7 (Z_to_bv 64 (C / 8 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F3 fc3 m3
           V A n 0 [] L0 lo FDO MST eq_refl eq_refl VC3 FOBJ3 LV1 (Forall_nil _));
    [subst n; lia| reflexivity| subst n; clear - CP1; Z.div_mod_to_equations; lia| subst n; clear - CP1 CAPB; lia
    | exact ART3| exact MI3| rewrite EU2; exact ST3| exact LOW1| rewrite EU2; ul| rewrite EU2; ul
    | rewrite EU2; replace (usp + -32) with (usp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact SPA| exact FRM3
    | split; [unfold DES_RET2 in Hc4' |- *; exact Hc4'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c4 Hc4'); intros ms0 <-; exact FRM3] |].
  intros c5 ((Σ2 & Hc5 & LV2 & FRS2 & SP2 & CR2) & FC5).
  destruct (ASTA_unpack_f RT Σ2 _ _ c5 Hc5 FC5) as (ms5 & (r2 & m4 & RS5 & (ART4 & MI4 & WM4 & ST4) & PRES4) & FRM4 & Hc5'). clear Hc5.
  destruct RS5 as (y0 & y1 & y2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & F4 & fc4 & ->).
  cbn [ms_fcsr] in FRM4. rewrite EU2 in ST4, PRES4. unfold DES_RET2 in Hc5'. rewrite (ret_pc_even 0xbc2a4) in Hc5' by lia. cbn [app] in LV2. rewrite ann_block_plain in LV2.
  assert (PR4 : forall a : word, usp - 32 <= bv_unsigned a < USTACK_TOP \/ in_fframe (rt_frames RT Σ) (bv_unsigned a) -> m4 a = m3 a).
  { intros a [Ha|Ha]; apply PRES4; [left; ul| right; right; right; left; rewrite FRS1; exact Ha]. }
  assert (FR4 : rw_cells bsegs m4 (usp + -32) (des_frame s2 s1 s0 ra)).
  { apply (rw_cells_agree bsegs m3 m4 _ _ FR3); [| exact WM4]. intros a Ha. unfold des_frame in Ha. cbn [cells_size csize Nat.add] in Ha. apply PR4. left. ul. }
  assert (RC4 : rw_cells bsegs m4 C [C8 (Z_to_bv 64 V)]).
  { apply (rw_cells_agree bsegs m3 m4 _ _ RC3); [| exact WM4]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply PR4. left. ul. }
  assert (VC4 : rw_cells bsegs m4 V (vcells A (A + 0) (A + n))).
  { apply (rw_cells_agree bsegs m3 m4 _ _ VC3); [| exact WM4]. intros a Ha. unfold vcells in Ha. cbn [cells_size csize Nat.add] in Ha.
    apply PR4. right. exists f, kf. split; [exact INF| lia]. }
  pose proof (fobj_pres RT AF Σ1 Σ2 (rt_live RT Σ1) (usp + -32) m3 m4 V 24 ART3 FOBJ3 PRES4 ltac:(rewrite FRS2; reflexivity)) as FOBJ4.
  assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2; exact LOW1).
  assert (FPC3 : fp_client RT Σ2 lo [(usp - 32, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  assert (SHX4 : x_shz [(usp - 32, usp)] m4 C 8).
  { intros m' MU WM. apply (shz_stackv RT AF Σ2 m' C 8 (art_fp_client RT AF Σ2 m4 m' lo _ ART4 LOW2 FPC3 MU WM)); rewrite ?SP2, ?SP1; ul. }
  pose proof (v_shz_of_fp RT AF Σ2 m4 lo _ V ART4 LOW2 FPC3 FOBJ4) as SHZ4.

  unfold vcells in VC4.
  pose proof (des_walk3 usp C V A (A + n) lo gp (Z_to_bv 64 0x6b6ea8) y0 y1 y2 r2 d1 d2 d3 d4 d5 d6 d7 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6
                s2 s1 s0 ra (C8 (Z_to_bv 64 (A + 0))) F4 fc4 m4 ST4 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) V8 ltac:(ul) ltac:(subst n; ul)
                SHX4 SHZ4 RC4 VC4 eq_refl FR4 MI4) as W5.
  rewrite <- ESP in W5. unfold DES_RET2 in W5.
  lazymatch type of W5 with evt bsegs _ ?X =>
    assert (W5' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W5) end.
  clear W5.
  apply (cps_realizes bsegs _ _ _ c5 (asta_evt_c RT AF Σ2 PMc _ _ MST W5') Hc5'). clear W5'. intros c6 Hc6.
  destruct (ASTA_unpack RT Σ2 _ _ c6 Hc6) as (ms6 & (a2'' & -> & ST6) & Hc6'). clear Hc6.
  assert (INA2 : In (A, n) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
  apply (del_ok RT AF (rf_free RT RTF) Σ2 PMc ra sp gp (Z_to_bv 64 0x6b6ea8) y0 y1 y2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 (A + n - A)) a2'' d3 d4 d5 d6 d7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 F4 fc4 m4 A n lo FDO MST INA2 eq_refl eq_refl ART4 MI4);
    [| exact UOK| exact FRM4| split; [exact Hc6'| apply (cfrm0_of_asta RT Σ2 PMc (eq _) c6 Hc6'); intros ms0 <-; exact FRM4] |].
  { unfold call_ok. fold usp. split; [exact ST6|]. split; [exact LOW2|]. split; [ul|]. split; [ul| exact SPA]. }
  intros c7 ((Σ3 & v & Hc7 & LV3 & FRS3 & SP3 & CR3) & FC7).

  assert (LV3' : rt_live RT Σ3 = L0).
  { rewrite LV3, LV2. apply live_remove_hd. intros [p k] Hin E. cbn [fst] in E. subst p.
    pose proof (af_live_disj RT AF Σ2 m4 A n A k [] L0 ART4 ltac:(rewrite LV2; reflexivity) Hin). pose proof (LVPOS A k Hin). subst n. lia. }
  apply Hk. split; [| exact FC7]. exists Σ3.
  split; [| split; [exact LV3'| split; [rewrite FRS3, FRS2; exact FRS1| split; [rewrite SP3, SP2; exact SP1| rewrite CR3, CR2; exact CR1]]]].
  eapply ASTA_conseq; [exact Hc7|]. intros ms (m5 & RS7 & AFT & PRES7). exists v, m5. split; [exact RS7|]. split; [exact AFT|].
  intros a Ha Hout. fold usp in Ha. cbn [outside] in Hout. destruct Hout as (Ho & _).
  assert (HaL : aclient (rt_live RT Σ3) (rt_frames RT Σ2) usp (bv_unsigned a)) by (rewrite LV3', FRS2, FRS1; exact Ha).
  pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 ltac:(apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite VL; intros e He; apply in_or_app; right; exact He| auto| lia])) as SPL.
  rewrite (PRES7 a HaL), (PRES4 a), (PRES3 a), (MU2 a), (MU1 a); [reflexivity| | | |].
  - cbn [outside]. split; [ul| exact I].
  - cbn [outside]. split; [ul|]. split; [lia| exact I].
  - apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite VL; intros e He; apply in_or_app; right; exact He| auto| lia].
  - apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1; intros e He; apply in_or_app; right; exact He| rewrite FRS1; auto| lia].
Qed.

End Destroy.
