(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg RtCells AProto ABase F_tryinit. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aunwind. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.F_aunwind. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_m2s_b.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AKit AKit2 FsKit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.

Definition GCMAGIC : Z := 0xf5f5f5f5f5f5f5f5.
Definition gcN (c : Z) : Z := 2 ^ (14 - c).
Definition gflags (fs c : Z) : Z := fs + 4096 + (32768 - 2 ^ (15 - c)).
Definition gflag (fs c pos : Z) : Z := gflags fs c + pos.
Definition gframe (fs c pos : Z) : Z := fs + 36864 + c * 1048576 + pos * 2 ^ (6 + c).

Definition gc_head (pc : Z) (ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32)
    (spf fs bot cur c i : Z) (m : amem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 spf) gp tp t0 t1 (Z_to_bv 64 1) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 cur)
          a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 bot) (Z_to_bv 64 (14 - c)) (Z_to_bv 64 c) (Z_to_bv 64 (c + 6)) (Z_to_bv 64 0xd9ab8) (Z_to_bv 64 GCMAGIC)
          (Z_to_bv 64 (gflags fs c)) (Z_to_bv 64 fs) (Z_to_bv 64 0) (Z_to_bv 64 i)
          (Z_to_bv 64 6) t4 t5 t6) FR (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Definition gc_next0 (ra gp tp t0 t1 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32) (spf fs bot cur c i : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 a6 a7,
    (i + 1 < gcN c /\ ms' = gc_head 0x47ff8 ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 FR fc spf fs bot cur c (i + 1) m)
    \/ (i + 1 = gcN c /\ ms' = gc_head 0x47f88 ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 FR fc spf fs bot cur c (i + 1) m).

Definition gc_step (W : list (Z * Z)) (Q : amem -> Prop) (ra gp tp t1 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32)
    (spf fs bot cur c i : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0' m', gc_next0 ra gp tp t0' t1 t4 t5 t6 FR fc spf fs bot cur c i m' ms'
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ Q m'.

Lemma shr_gcN : forall c x, 0 <= c < 11 -> 0 <= x -> (x ≫ (14 - c) = 0 <-> x < 2 ^ (14 - c)).
Proof.
  intros c x C X. rewrite Z.shiftr_div_pow2 by lia.
  assert (0 < 2 ^ (14 - c)) by (apply Z.pow_pos_nonneg; lia).
  split; intros H1.
  - apply Z.div_small_iff in H1; lia.
  - apply Z.div_small. lia.
Qed.

Lemma gc_tail : forall RNG ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem) (spf fs bot cur c i : Z),
  0 <= c < 11 -> 0 <= i < gcN c ->
  evtF asegs RNG (gc_next0 ra gp tp t0 t1 t4 t5 t6 FR fc spf fs bot cur c i m)
    (gc_head 0x47fec ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 FR fc spf fs bot cur c i m).
Proof.
  intros until i. intros C I.
  unfold gc_next0, gc_head, gcN in *.
  assert (PN : 0 < 2 ^ (14 - c) <= 16384) by (split; [apply Z.pow_pos_nonneg; lia| change 16384 with (2^14); apply Z.pow_le_mono_r; lia]).
  zstep.
  zstep.
  zstep. if_cases Ke; zify_cond Ke.
  - rewrite ?Z.mod_small in Ke by lia.
    assert (EN : i + 1 = 2 ^ (14 - c)).
    { destruct (Z.eq_dec (i + 1) (2 ^ (14 - c))) as [E|NE]; [exact E|]. exfalso. apply Ke. apply shr_gcN; lia. }
    apply evtF_done. do 8 eexists. right. split; [exact EN|]. cbv delta [mkR]. reflexivity.
  - rewrite ?Z.mod_small in Ke by lia. apply shr_gcN in Ke; [|lia|lia].
    apply evtF_done. do 8 eexists. left. split; [exact Ke|]. cbv delta [mkR]. reflexivity.
Qed.

Lemma gc_iter_zero : forall RNG ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem) (spf fs bot cur c i : Z),
  mem_inv asegs m ->
  0 <= c < 11 -> 0 <= i < gcN c -> 0 <= fs -> fs + 11571200 <= 2^47 ->
  rw_cells asegs m (gflag fs c i) [C1 (Z_to_bv 8 0)] ->
  rng RNG fs 11571200 ->
  evtF asegs RNG (gc_next0 ra gp tp t0 t1 t4 t5 t6 FR fc spf fs bot cur c i m)
    (gc_head 0x47ff8 ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 FR fc spf fs bot cur c i m).
Proof.
  intros until i. intros MI C I F0 FB FL RFS.
  pose proof (gc_tail RNG ra gp tp t0 t1) as TAIL.
  unfold gc_head, gflag, gflags, gcN in *.
  assert (P15 : 0 < 2 ^ (15 - c) <= 32768) by (split; [apply Z.pow_pos_nonneg; lia| change 32768 with (2^15); apply Z.pow_le_mono_r; lia]).
  assert (P14 : 2 ^ (15 - c) = 2 * 2 ^ (14 - c)) by (replace (15 - c) with (Z.succ (14 - c)) by lia; rewrite Z.pow_succ_r by lia; reflexivity).
  remember (fs + 4096 + (32768 - 2 ^ (15 - c))) as fbase eqn:FBASE.
  remember (fbase + i) as flag eqn:FLAG.
  assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG FBASE P15 P14 I; lia).
  zstep. rewrite <- FLAG.
  zstep; rewrite zxb_lit by lia.
  zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].
  rewrite FBASE. eapply TAIL; assumption.
Qed.

Lemma gc_iter_keep : forall RNG ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem) (spf fs bot cur c i : Z) (b : byte) (rs : Z),
  mem_inv asegs m ->
  0 <= c < 11 -> 0 <= i < gcN c -> 0 <= fs -> fs + 11571200 <= 2^47 ->
  0 <= bot < 2^64 -> 0 <= cur < 2^64 -> 0 <= rs < 2^64 ->
  rw_cells asegs m (gflag fs c i) [C1 b] -> bv_unsigned b <> 0 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] ->
  rw_cells asegs m (gframe fs c i + 24) [C8 (Z_to_bv 64 rs)] ->
  (rs <= bot \/ cur <= rs) ->
  rng RNG fs 11571200 ->
  evtF asegs RNG (gc_next0 ra gp tp t0 t1 t4 t5 t6 FR fc spf fs bot cur c i m)
    (gc_head 0x47ff8 ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 FR fc spf fs bot cur c i m).
Proof.
  intros until rs. intros MI C I F0 FB BOT CUR RS FL NZ LOG FRS KEEP RFS.
  pose proof (gc_tail RNG ra gp tp t0 t1) as TAIL.
  unfold gc_head, gflag, gflags, gframe, gcN in *.
  assert (P15 : 0 < 2 ^ (15 - c) <= 32768) by (split; [apply Z.pow_pos_nonneg; lia| change 32768 with (2^15); apply Z.pow_le_mono_r; lia]).
  assert (P14 : 2 ^ (15 - c) = 2 * 2 ^ (14 - c)) by (replace (15 - c) with (Z.succ (14 - c)) by lia; rewrite Z.pow_succ_r by lia; reflexivity).
  assert (P6 : 64 <= 2 ^ (6 + c)) by (change 64 with (2^6); apply Z.pow_le_mono_r; lia).
  assert (PM : 2 ^ (14 - c) * 2 ^ (6 + c) = 1048576) by (rewrite <- Z.pow_add_r by lia; replace (14 - c + (6 + c)) with 20 by lia; reflexivity).
  remember (fs + 4096 + (32768 - 2 ^ (15 - c))) as fbase eqn:FBASE.
  remember (fbase + i) as flag eqn:FLAG.
  remember (fs + 36864 + c * 1048576 + i * 2 ^ (6 + c)) as F eqn:FEQ.
  assert (FRNG : fs + 36864 <= F /\ F + 2 ^ (6 + c) <= fs + 11571200) by (clear - FEQ C I P6 PM; nia).
  assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG FBASE P15 P14 I; lia).
  assert (RFR : rng RNG (F + 24) 8) by (eapply rng_sub'; [exact RFS|]; clear - FRNG P6; lia).
  zstep. rewrite <- FLAG.
  zstep.
  zstep. if_cases Kd; zify_cond Kd.
  { exfalso. pose proof (bv_unsigned_in_range 8 b) as RB8. change (bv_modulus 8) with 256 in RB8. rewrite ?Z.mod_small in Kd by lia. lia. }
  zstep.
  zstep. zstep. zstep.
  zstep. zstep. zstep. zstep.
  match goal with |- context [Z_to_bv 64 (fs + 4096 + Z.shiftl c 20 + 32768 + Z.shiftl i ((c + 6) mod 64))] =>
    replace (fs + 4096 + Z.shiftl c 20 + 32768 + Z.shiftl i ((c + 6) mod 64)) with F
      by (rewrite (Z.mod_small (c + 6)) by lia; rewrite !Z.shiftl_mul_pow2 by lia; change (2^20) with 1048576; replace (c + 6) with (6 + c) by lia; lia) end.
  zstep.
  zstep. if_cases Kb; zify_cond Kb.
  - rewrite FBASE. eapply TAIL; assumption.
  - zstep. if_cases Kc; zify_cond Kc.
    + rewrite FBASE. eapply TAIL; assumption.
    + exfalso. clear - Kb Kc KEEP BOT CUR RS. rewrite ?Z.mod_small in * by lia. lia.
Qed.

Local Ltac ss_cont :=
  let Kl := fresh "Kl" in
  zstep;
  zstep; zstep; zstep;
  zstep; if_cases Kl; zify_cond Kl; [| exfalso; clear - Kl; cbn in Kl; lia].
Local Ltac ss_last :=
  let Kl := fresh "Kl" in
  zstep;
  zstep; zstep; zstep;
  zstep; if_cases Kl; zify_cond Kl; [exfalso; clear - Kl; cbn in Kl; lia|];
  zstep.
Local Ltac ss_tail cls FBASE TAIL stores :=
  let Kt := fresh "Kt" in
  zstep; if_cases Kt; zify_cond Kt; [exfalso; clear - Kt; lia|];
  zstep; zstep;
  lazymatch goal with SHF : shad ?F = _ |- _ =>
    replace (2147450880 + Z.shiftr F 3) with (shad F) by (rewrite SHF, Z.shiftr_div_pow2 by lia; reflexivity) end;
  zstep;
  stores;
  lazymatch goal with MU : munch _ _ ?m0, WM : wmono _ _ ?m0, FL : rw_cells _ ?m0 _ [C1 (Z_to_bv 8 0)] |- _ =>
    eapply evtF_mono;
    [ rewrite FBASE; eapply TAIL with (c := cls); [lia | unfold gcN; lia]
    | cbv beta; let ms' := fresh "ms'" in let H := fresh "H" in intros ms' H; eexists _, m0; split; [exact H|];
      split; [exact MU|]; split; [exact WM|]; split; [assumption| exact FL] ] end.

Lemma gc_iter_free : forall RNG ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem) (spf fs bot cur c i : Z)
    (b : byte) (rs : Z) (v0 fsz : word) (ws : list word),
  mem_inv asegs m ->
  0 <= c <= 2 -> 0 <= i < gcN c -> ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  0 <= bot < 2^64 -> 0 <= cur < 2^64 -> 0 <= rs < 2^64 ->
  rw_cells asegs m (gflag fs c i) [C1 b] -> bv_unsigned b <> 0 ->
  rw_cells asegs m (fs + 88) [C8 (Z_to_bv 64 20)] ->
  rw_cells asegs m (gframe fs c i + 24) [C8 (Z_to_bv 64 rs)] ->
  bot < rs < cur ->
  rt_shbase m -> rt_layout m ->
  rw_cells asegs m spf [C8 v0; C8 (Z_to_bv 64 0xda7a0); C8 (Z_to_bv 64 0xda7b0); C8 (Z_to_bv 64 0xda7a8); C8 fsz] ->
  length ws = Z.to_nat (2 ^ c) -> rw_cells asegs m (shad (gframe fs c i)) (map C8 ws) ->
  ATOP <= spf -> spf + 40 <= 2^64 ->
  rng_aimg RNG -> rng RNG spf 40 -> rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF asegs RNG (gc_step [(gflag fs c i, gflag fs c i + 1); (shad (gframe fs c i), shad (gframe fs c i) + 8 * 2 ^ c)]
                          (fun m' => rw_cells asegs m' (gflag fs c i) [C1 (Z_to_bv 8 0)])
                          ra gp tp t1 t4 t5 t6 FR fc spf fs bot cur c i m)
    (gc_head 0x47ff8 ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 FR fc spf fs bot cur c i m).
Proof.
  intros until ws. intros MI C I FLO FHI FAL BOT CUR RS FL NZ LOG FRS FREE SHB LAY FRM LWS SHW SPLO SPHI RIMG RSP RFS RSH.
  pose proof (gc_tail RNG ra gp tp) as TAIL.
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & FB). unfold AIMG_HI in FLOL.
  assert (CC : c = 0 \/ c = 1 \/ c = 2) by lia.
  unfold gc_step, gc_head, gflag, gflags, gframe, gcN in *.
  destruct CC as [-> | [-> | ->]].
  -
    change (2 ^ (15 - 0)) with 32768 in *. change (2 ^ (14 - 0)) with 16384 in *. change (2 ^ (6 + 0)) with 64 in *. change (2 ^ 0) with 1 in *.
    change (Z.to_nat 1) with 1%nat in LWS.
    destruct ws as [|w0 [|w1 ws]]; try (cbn in LWS; lia). cbn [map] in SHW.
    remember (fs + 4096 + (32768 - 32768)) as fbase eqn:FBASE.
    remember (fbase + i) as flag eqn:FLAG.
    remember (fs + 36864 + 0 * 1048576 + i * 64) as F eqn:FEQ.
    assert (FRNG : fs + 36864 <= F /\ F + 64 <= fs + 11571200) by (clear - FEQ I; lia).
    assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (SHD : shad F + 8 * 1 <= fs \/ fs + 11571200 <= shad F).
    { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FRNG ATR. lia. }
    assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG FBASE I; lia).
    assert (RFR : rng RNG (F + 24) 8) by (eapply rng_sub'; [exact RFS|]; clear - FRNG; lia).
    assert (RSF : rng RNG (shad F) (8 * 1)).
    { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      clear - FLOL FB FRNG. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl [(flag, flag + 1); (shad F, shad F + 8 * 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. rewrite <- FLAG.
    zstep.
    zstep. if_cases Kd; zify_cond Kd.
    { exfalso. pose proof (bv_unsigned_in_range 8 b) as RB8. change (bv_modulus 8) with 256 in RB8. rewrite ?Z.mod_small in Kd by lia. lia. }
    zstep.
    zstep. zstep. zstep.
    zstep. zstep. zstep. zstep.
    replace (fs + 36864 + Z.shiftl i 6) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^6) with 64; lia).
    zstep.
    zstep. if_cases Kb; zify_cond Kb.
    { exfalso. clear - Kb FREE BOT CUR RS. rewrite ?Z.mod_small in Kb by lia. lia. }
    zstep. if_cases Kc; zify_cond Kc.
    { exfalso. clear - Kc FREE BOT CUR RS. rewrite ?Z.mod_small in Kc by lia. lia. }
    zstep.
    zstep.
    zstep. zstep. fold_lits. zsimp. zstep. zstep.
    zstep. if_cases K; zify_cond K.
    + ss_tail 0 FBASE TAIL ltac:(ss_last).
    + assert (HIGH : 0x10007fff8000 <= F) by (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; clear - FLOB FRNG K; lia).
      do 5 zstep. fold_lits. zsimp.
      zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2 FB FRNG F0. lia. }
      do 4 zstep.
      zstep. if_cases K3; zify_cond K3. { exfalso. clear - K3 FB FRNG F0. lia. }
      zstep. if_cases K4; zify_cond K4. { exfalso. clear - K4 HIGH. lia. }
      ss_tail 0 FBASE TAIL ltac:(ss_last).
  -
    change (2 ^ (15 - 1)) with 16384 in *. change (2 ^ (14 - 1)) with 8192 in *. change (2 ^ (6 + 1)) with 128 in *. change (2 ^ 1) with 2 in *.
    change (Z.to_nat 2) with 2%nat in LWS.
    destruct ws as [|w0 [|w1 [|w2 ws]]]; try (cbn in LWS; lia). cbn [map] in SHW.
    remember (fs + 4096 + (32768 - 16384)) as fbase eqn:FBASE.
    remember (fbase + i) as flag eqn:FLAG.
    remember (fs + 36864 + 1 * 1048576 + i * 128) as F eqn:FEQ.
    assert (FRNG : fs + 36864 <= F /\ F + 128 <= fs + 11571200) by (clear - FEQ I; lia).
    assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (SHD : shad F + 8 * 2 <= fs \/ fs + 11571200 <= shad F).
    { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FRNG ATR. lia. }
    assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG FBASE I; lia).
    assert (RFR : rng RNG (F + 24) 8) by (eapply rng_sub'; [exact RFS|]; clear - FRNG; lia).
    assert (RSF : rng RNG (shad F) (8 * 2)).
    { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      clear - FLOL FB FRNG. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl [(flag, flag + 1); (shad F, shad F + 8 * 2)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. rewrite <- FLAG.
    zstep.
    zstep. if_cases Kd; zify_cond Kd.
    { exfalso. pose proof (bv_unsigned_in_range 8 b) as RB8. change (bv_modulus 8) with 256 in RB8. rewrite ?Z.mod_small in Kd by lia. lia. }
    zstep.
    zstep. zstep. zstep.
    zstep. zstep. zstep. zstep.
    replace (fs + 1085440 + Z.shiftl i 7) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^7) with 128; lia).
    zstep.
    zstep. if_cases Kb; zify_cond Kb.
    { exfalso. clear - Kb FREE BOT CUR RS. rewrite ?Z.mod_small in Kb by lia. lia. }
    zstep. if_cases Kc; zify_cond Kc.
    { exfalso. clear - Kc FREE BOT CUR RS. rewrite ?Z.mod_small in Kc by lia. lia. }
    zstep.
    zstep.
    zstep. zstep. fold_lits. zsimp. zstep. zstep.
    zstep. if_cases K; zify_cond K.
    + ss_tail 1 FBASE TAIL ltac:(ss_cont; ss_last).
    + assert (HIGH : 0x10007fff8000 <= F) by (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; clear - FLOB FRNG K; lia).
      do 5 zstep. fold_lits. zsimp.
      zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2 FB FRNG F0. lia. }
      do 4 zstep.
      zstep. if_cases K3; zify_cond K3. { exfalso. clear - K3 FB FRNG F0. lia. }
      zstep. if_cases K4; zify_cond K4. { exfalso. clear - K4 HIGH. lia. }
      ss_tail 1 FBASE TAIL ltac:(ss_cont; ss_last).
  -
    change (2 ^ (15 - 2)) with 8192 in *. change (2 ^ (14 - 2)) with 4096 in *. change (2 ^ (6 + 2)) with 256 in *. change (2 ^ 2) with 4 in *.
    change (Z.to_nat 4) with 4%nat in LWS.
    destruct ws as [|w0 [|w1 [|w2 [|w3 [|w4 ws]]]]]; try (cbn in LWS; lia). cbn [map] in SHW.
    remember (fs + 4096 + (32768 - 8192)) as fbase eqn:FBASE.
    remember (fbase + i) as flag eqn:FLAG.
    remember (fs + 36864 + 2 * 1048576 + i * 256) as F eqn:FEQ.
    assert (FRNG : fs + 36864 <= F /\ F + 256 <= fs + 11571200) by (clear - FEQ I; lia).
    assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (SHD : shad F + 8 * 4 <= fs \/ fs + 11571200 <= shad F).
    { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FRNG ATR. lia. }
    assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG FBASE I; lia).
    assert (RFR : rng RNG (F + 24) 8) by (eapply rng_sub'; [exact RFS|]; clear - FRNG; lia).
    assert (RSF : rng RNG (shad F) (8 * 4)).
    { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      clear - FLOL FB FRNG. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl [(flag, flag + 1); (shad F, shad F + 8 * 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. rewrite <- FLAG.
    zstep.
    zstep. if_cases Kd; zify_cond Kd.
    { exfalso. pose proof (bv_unsigned_in_range 8 b) as RB8. change (bv_modulus 8) with 256 in RB8. rewrite ?Z.mod_small in Kd by lia. lia. }
    zstep.
    zstep. zstep. zstep.
    zstep. zstep. zstep. zstep.
    replace (fs + 2134016 + Z.shiftl i 8) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; lia).
    zstep.
    zstep. if_cases Kb; zify_cond Kb.
    { exfalso. clear - Kb FREE BOT CUR RS. rewrite ?Z.mod_small in Kb by lia. lia. }
    zstep. if_cases Kc; zify_cond Kc.
    { exfalso. clear - Kc FREE BOT CUR RS. rewrite ?Z.mod_small in Kc by lia. lia. }
    zstep.
    zstep.
    zstep. zstep. fold_lits. zsimp. zstep. zstep.
    zstep. if_cases K; zify_cond K.
    + ss_tail 2 FBASE TAIL ltac:(ss_cont; ss_cont; ss_cont; ss_last).
    + assert (HIGH : 0x10007fff8000 <= F) by (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; clear - FLOB FRNG K; lia).
      do 5 zstep. fold_lits. zsimp.
      zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2 FB FRNG F0. lia. }
      do 4 zstep.
      zstep. if_cases K3; zify_cond K3. { exfalso. clear - K3 FB FRNG F0. lia. }
      zstep. if_cases K4; zify_cond K4. { exfalso. clear - K4 HIGH. lia. }
      ss_tail 2 FBASE TAIL ltac:(ss_cont; ss_cont; ss_cont; ss_last).
Qed.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import RtCells.TwinB AProto.TwinB ABase.TwinB F_tryinit.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aunwind.TwinB.F_aunwind.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import F_m2s_b.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AKit.TwinB AKit2.TwinB FsKit.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.

Definition GCMAGIC : Z := 0xf5f5f5f5f5f5f5f5.
Definition gcN (c : Z) : Z := 2 ^ (14 - c).
Definition gflags (fs c : Z) : Z := fs + 4096 + (32768 - 2 ^ (15 - c)).
Definition gflag (fs c pos : Z) : Z := gflags fs c + pos.
Definition gframe (fs c pos : Z) : Z := fs + 36864 + c * 1048576 + pos * 2 ^ (6 + c).

Definition gc_head (pc : Z) (ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32)
    (spf fs bot cur c i : Z) (m : amem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 spf) gp tp t0 t1 (Z_to_bv 64 1) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 cur)
          a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 bot) (Z_to_bv 64 (14 - c)) (Z_to_bv 64 c) (Z_to_bv 64 (c + 6)) (Z_to_bv 64 0xdbc78) (Z_to_bv 64 GCMAGIC)
          (Z_to_bv 64 (gflags fs c)) (Z_to_bv 64 fs) (Z_to_bv 64 0) (Z_to_bv 64 i)
          (Z_to_bv 64 6) t4 t5 t6) FR (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Definition gc_next0 (ra gp tp t0 t1 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32) (spf fs bot cur c i : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 a6 a7,
    (i + 1 < gcN c /\ ms' = gc_head 0x48988 ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 FR fc spf fs bot cur c (i + 1) m)
    \/ (i + 1 = gcN c /\ ms' = gc_head 0x48918 ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 FR fc spf fs bot cur c (i + 1) m).

Definition gc_step (W : list (Z * Z)) (Q : amem -> Prop) (ra gp tp t1 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32)
    (spf fs bot cur c i : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0' m', gc_next0 ra gp tp t0' t1 t4 t5 t6 FR fc spf fs bot cur c i m' ms'
    /\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ Q m'.

Lemma shr_gcN : forall c x, 0 <= c < 11 -> 0 <= x -> (x ≫ (14 - c) = 0 <-> x < 2 ^ (14 - c)).
Proof.
  intros c x C X. rewrite Z.shiftr_div_pow2 by lia.
  assert (0 < 2 ^ (14 - c)) by (apply Z.pow_pos_nonneg; lia).
  split; intros H1.
  - apply Z.div_small_iff in H1; lia.
  - apply Z.div_small. lia.
Qed.

Lemma gc_tail : forall RNG ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem) (spf fs bot cur c i : Z),
  0 <= c < 11 -> 0 <= i < gcN c ->
  evtF bsegs RNG (gc_next0 ra gp tp t0 t1 t4 t5 t6 FR fc spf fs bot cur c i m)
    (gc_head 0x4897c ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 FR fc spf fs bot cur c i m).
Proof.
  intros until i. intros C I.
  unfold gc_next0, gc_head, gcN in *.
  assert (PN : 0 < 2 ^ (14 - c) <= 16384) by (split; [apply Z.pow_pos_nonneg; lia| change 16384 with (2^14); apply Z.pow_le_mono_r; lia]).
  zstep.
  zstep.
  zstep. if_cases Ke; zify_cond Ke.
  - rewrite ?Z.mod_small in Ke by lia.
    assert (EN : i + 1 = 2 ^ (14 - c)).
    { destruct (Z.eq_dec (i + 1) (2 ^ (14 - c))) as [E|NE]; [exact E|]. exfalso. apply Ke. apply shr_gcN; lia. }
    apply evtF_done. do 8 eexists. right. split; [exact EN|]. cbv delta [mkR]. reflexivity.
  - rewrite ?Z.mod_small in Ke by lia. apply shr_gcN in Ke; [|lia|lia].
    apply evtF_done. do 8 eexists. left. split; [exact Ke|]. cbv delta [mkR]. reflexivity.
Qed.

Lemma gc_iter_zero : forall RNG ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem) (spf fs bot cur c i : Z),
  mem_inv bsegs m ->
  0 <= c < 11 -> 0 <= i < gcN c -> 0 <= fs -> fs + 11571200 <= 2^47 ->
  rw_cells bsegs m (gflag fs c i) [C1 (Z_to_bv 8 0)] ->
  rng RNG fs 11571200 ->
  evtF bsegs RNG (gc_next0 ra gp tp t0 t1 t4 t5 t6 FR fc spf fs bot cur c i m)
    (gc_head 0x48988 ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 FR fc spf fs bot cur c i m).
Proof.
  intros until i. intros MI C I F0 FB FL RFS.
  pose proof (gc_tail RNG ra gp tp t0 t1) as TAIL.
  unfold gc_head, gflag, gflags, gcN in *.
  assert (P15 : 0 < 2 ^ (15 - c) <= 32768) by (split; [apply Z.pow_pos_nonneg; lia| change 32768 with (2^15); apply Z.pow_le_mono_r; lia]).
  assert (P14 : 2 ^ (15 - c) = 2 * 2 ^ (14 - c)) by (replace (15 - c) with (Z.succ (14 - c)) by lia; rewrite Z.pow_succ_r by lia; reflexivity).
  remember (fs + 4096 + (32768 - 2 ^ (15 - c))) as fbase eqn:FBASE.
  remember (fbase + i) as flag eqn:FLAG.
  assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG FBASE P15 P14 I; lia).
  zstep. rewrite <- FLAG.
  zstep; rewrite zxb_lit by lia.
  zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].
  rewrite FBASE. eapply TAIL; assumption.
Qed.

Lemma gc_iter_keep : forall RNG ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem) (spf fs bot cur c i : Z) (b : byte) (rs : Z),
  mem_inv bsegs m ->
  0 <= c < 11 -> 0 <= i < gcN c -> 0 <= fs -> fs + 11571200 <= 2^47 ->
  0 <= bot < 2^64 -> 0 <= cur < 2^64 -> 0 <= rs < 2^64 ->
  rw_cells bsegs m (gflag fs c i) [C1 b] -> bv_unsigned b <> 0 ->
  rw_cells bsegs m (fs + 88) [C8 (Z_to_bv 64 20)] ->
  rw_cells bsegs m (gframe fs c i + 24) [C8 (Z_to_bv 64 rs)] ->
  (rs <= bot \/ cur <= rs) ->
  rng RNG fs 11571200 ->
  evtF bsegs RNG (gc_next0 ra gp tp t0 t1 t4 t5 t6 FR fc spf fs bot cur c i m)
    (gc_head 0x48988 ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 FR fc spf fs bot cur c i m).
Proof.
  intros until rs. intros MI C I F0 FB BOT CUR RS FL NZ LOG FRS KEEP RFS.
  pose proof (gc_tail RNG ra gp tp t0 t1) as TAIL.
  unfold gc_head, gflag, gflags, gframe, gcN in *.
  assert (P15 : 0 < 2 ^ (15 - c) <= 32768) by (split; [apply Z.pow_pos_nonneg; lia| change 32768 with (2^15); apply Z.pow_le_mono_r; lia]).
  assert (P14 : 2 ^ (15 - c) = 2 * 2 ^ (14 - c)) by (replace (15 - c) with (Z.succ (14 - c)) by lia; rewrite Z.pow_succ_r by lia; reflexivity).
  assert (P6 : 64 <= 2 ^ (6 + c)) by (change 64 with (2^6); apply Z.pow_le_mono_r; lia).
  assert (PM : 2 ^ (14 - c) * 2 ^ (6 + c) = 1048576) by (rewrite <- Z.pow_add_r by lia; replace (14 - c + (6 + c)) with 20 by lia; reflexivity).
  remember (fs + 4096 + (32768 - 2 ^ (15 - c))) as fbase eqn:FBASE.
  remember (fbase + i) as flag eqn:FLAG.
  remember (fs + 36864 + c * 1048576 + i * 2 ^ (6 + c)) as F eqn:FEQ.
  assert (FRNG : fs + 36864 <= F /\ F + 2 ^ (6 + c) <= fs + 11571200) by (clear - FEQ C I P6 PM; nia).
  assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG FBASE P15 P14 I; lia).
  assert (RFR : rng RNG (F + 24) 8) by (eapply rng_sub'; [exact RFS|]; clear - FRNG P6; lia).
  zstep. rewrite <- FLAG.
  zstep.
  zstep. if_cases Kd; zify_cond Kd.
  { exfalso. pose proof (bv_unsigned_in_range 8 b) as RB8. change (bv_modulus 8) with 256 in RB8. rewrite ?Z.mod_small in Kd by lia. lia. }
  zstep.
  zstep. zstep. zstep.
  zstep. zstep. zstep. zstep.
  match goal with |- context [Z_to_bv 64 (fs + 4096 + Z.shiftl c 20 + 32768 + Z.shiftl i ((c + 6) mod 64))] =>
    replace (fs + 4096 + Z.shiftl c 20 + 32768 + Z.shiftl i ((c + 6) mod 64)) with F
      by (rewrite (Z.mod_small (c + 6)) by lia; rewrite !Z.shiftl_mul_pow2 by lia; change (2^20) with 1048576; replace (c + 6) with (6 + c) by lia; lia) end.
  zstep.
  zstep. if_cases Kb; zify_cond Kb.
  - rewrite FBASE. eapply TAIL; assumption.
  - zstep. if_cases Kc; zify_cond Kc.
    + rewrite FBASE. eapply TAIL; assumption.
    + exfalso. clear - Kb Kc KEEP BOT CUR RS. rewrite ?Z.mod_small in * by lia. lia.
Qed.

Local Ltac ss_cont :=
  let Kl := fresh "Kl" in
  zstep;
  zstep; zstep; zstep;
  zstep; if_cases Kl; zify_cond Kl; [| exfalso; clear - Kl; cbn in Kl; lia].
Local Ltac ss_last :=
  let Kl := fresh "Kl" in
  zstep;
  zstep; zstep; zstep;
  zstep; if_cases Kl; zify_cond Kl; [exfalso; clear - Kl; cbn in Kl; lia|];
  zstep.
Local Ltac ss_tail cls FBASE TAIL stores :=
  let Kt := fresh "Kt" in
  zstep; if_cases Kt; zify_cond Kt; [exfalso; clear - Kt; lia|];
  zstep; zstep;
  lazymatch goal with SHF : shad ?F = _ |- _ =>
    replace (2147450880 + Z.shiftr F 3) with (shad F) by (rewrite SHF, Z.shiftr_div_pow2 by lia; reflexivity) end;
  zstep;
  stores;
  lazymatch goal with MU : munch _ _ ?m0, WM : wmono _ _ ?m0, FL : rw_cells _ ?m0 _ [C1 (Z_to_bv 8 0)] |- _ =>
    eapply evtF_mono;
    [ rewrite FBASE; eapply TAIL with (c := cls); [lia | unfold gcN; lia]
    | cbv beta; let ms' := fresh "ms'" in let H := fresh "H" in intros ms' H; eexists _, m0; split; [exact H|];
      split; [exact MU|]; split; [exact WM|]; split; [assumption| exact FL] ] end.

Lemma gc_iter_free : forall RNG ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 (FR : bvmap 5 word) fc (m : amem) (spf fs bot cur c i : Z)
    (b : byte) (rs : Z) (v0 fsz : word) (ws : list word),
  mem_inv bsegs m ->
  0 <= c <= 2 -> 0 <= i < gcN c -> ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  0 <= bot < 2^64 -> 0 <= cur < 2^64 -> 0 <= rs < 2^64 ->
  rw_cells bsegs m (gflag fs c i) [C1 b] -> bv_unsigned b <> 0 ->
  rw_cells bsegs m (fs + 88) [C8 (Z_to_bv 64 20)] ->
  rw_cells bsegs m (gframe fs c i + 24) [C8 (Z_to_bv 64 rs)] ->
  bot < rs < cur ->
  rt_shbase m -> rt_layout m ->
  rw_cells bsegs m spf [C8 v0; C8 (Z_to_bv 64 0xdc960); C8 (Z_to_bv 64 0xdc970); C8 (Z_to_bv 64 0xdc968); C8 fsz] ->
  length ws = Z.to_nat (2 ^ c) -> rw_cells bsegs m (shad (gframe fs c i)) (map C8 ws) ->
  ATOP <= spf -> spf + 40 <= 2^64 ->
  rng_aimg RNG -> rng RNG spf 40 -> rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF bsegs RNG (gc_step [(gflag fs c i, gflag fs c i + 1); (shad (gframe fs c i), shad (gframe fs c i) + 8 * 2 ^ c)]
                          (fun m' => rw_cells bsegs m' (gflag fs c i) [C1 (Z_to_bv 8 0)])
                          ra gp tp t1 t4 t5 t6 FR fc spf fs bot cur c i m)
    (gc_head 0x48988 ra gp tp t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 t4 t5 t6 FR fc spf fs bot cur c i m).
Proof.
  intros until ws. intros MI C I FLO FHI FAL BOT CUR RS FL NZ LOG FRS FREE SHB LAY FRM LWS SHW SPLO SPHI RIMG RSP RFS RSH.
  pose proof (gc_tail RNG ra gp tp) as TAIL.
  pose proof (ablk_lin _ _ FLO) as (FLOL & F0 & _ & FB). unfold AIMG_HI in FLOL.
  assert (CC : c = 0 \/ c = 1 \/ c = 2) by lia.
  unfold gc_step, gc_head, gflag, gflags, gframe, gcN in *.
  destruct CC as [-> | [-> | ->]].
  -
    change (2 ^ (15 - 0)) with 32768 in *. change (2 ^ (14 - 0)) with 16384 in *. change (2 ^ (6 + 0)) with 64 in *. change (2 ^ 0) with 1 in *.
    change (Z.to_nat 1) with 1%nat in LWS.
    destruct ws as [|w0 [|w1 ws]]; try (cbn in LWS; lia). cbn [map] in SHW.
    remember (fs + 4096 + (32768 - 32768)) as fbase eqn:FBASE.
    remember (fbase + i) as flag eqn:FLAG.
    remember (fs + 36864 + 0 * 1048576 + i * 64) as F eqn:FEQ.
    assert (FRNG : fs + 36864 <= F /\ F + 64 <= fs + 11571200) by (clear - FEQ I; lia).
    assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (SHD : shad F + 8 * 1 <= fs \/ fs + 11571200 <= shad F).
    { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FRNG ATR. lia. }
    assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG FBASE I; lia).
    assert (RFR : rng RNG (F + 24) 8) by (eapply rng_sub'; [exact RFS|]; clear - FRNG; lia).
    assert (RSF : rng RNG (shad F) (8 * 1)).
    { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      clear - FLOL FB FRNG. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl [(flag, flag + 1); (shad F, shad F + 8 * 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep. rewrite <- FLAG.
    zstep.
    zstep. if_cases Kd; zify_cond Kd.
    { exfalso. pose proof (bv_unsigned_in_range 8 b) as RB8. change (bv_modulus 8) with 256 in RB8. rewrite ?Z.mod_small in Kd by lia. lia. }
    zstep.
    zstep. zstep. zstep.
    zstep. zstep. zstep. zstep.
    replace (fs + 36864 + Z.shiftl i 6) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^6) with 64; lia).
    zstep.
    zstep. if_cases Kb; zify_cond Kb.
    { exfalso. clear - Kb FREE BOT CUR RS. rewrite ?Z.mod_small in Kb by lia. lia. }
    zstep. if_cases Kc; zify_cond Kc.
    { exfalso. clear - Kc FREE BOT CUR RS. rewrite ?Z.mod_small in Kc by lia. lia. }
    zstep.
    zstep.
    zstep. zstep. fold_lits. zsimp. zstep. zstep.
    zstep. if_cases K; zify_cond K.
    + ss_tail 0 FBASE TAIL ltac:(ss_last).
    + assert (HIGH : 0x10007fff8000 <= F) by (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; clear - FLOB FRNG K; lia).
      do 5 zstep. fold_lits. zsimp.
      zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2 FB FRNG F0. lia. }
      do 4 zstep.
      zstep. if_cases K3; zify_cond K3. { exfalso. clear - K3 FB FRNG F0. lia. }
      zstep. if_cases K4; zify_cond K4. { exfalso. clear - K4 HIGH. lia. }
      ss_tail 0 FBASE TAIL ltac:(ss_last).
  -
    change (2 ^ (15 - 1)) with 16384 in *. change (2 ^ (14 - 1)) with 8192 in *. change (2 ^ (6 + 1)) with 128 in *. change (2 ^ 1) with 2 in *.
    change (Z.to_nat 2) with 2%nat in LWS.
    destruct ws as [|w0 [|w1 [|w2 ws]]]; try (cbn in LWS; lia). cbn [map] in SHW.
    remember (fs + 4096 + (32768 - 16384)) as fbase eqn:FBASE.
    remember (fbase + i) as flag eqn:FLAG.
    remember (fs + 36864 + 1 * 1048576 + i * 128) as F eqn:FEQ.
    assert (FRNG : fs + 36864 <= F /\ F + 128 <= fs + 11571200) by (clear - FEQ I; lia).
    assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (SHD : shad F + 8 * 2 <= fs \/ fs + 11571200 <= shad F).
    { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FRNG ATR. lia. }
    assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG FBASE I; lia).
    assert (RFR : rng RNG (F + 24) 8) by (eapply rng_sub'; [exact RFS|]; clear - FRNG; lia).
    assert (RSF : rng RNG (shad F) (8 * 2)).
    { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      clear - FLOL FB FRNG. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl [(flag, flag + 1); (shad F, shad F + 8 * 2)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep. rewrite <- FLAG.
    zstep.
    zstep. if_cases Kd; zify_cond Kd.
    { exfalso. pose proof (bv_unsigned_in_range 8 b) as RB8. change (bv_modulus 8) with 256 in RB8. rewrite ?Z.mod_small in Kd by lia. lia. }
    zstep.
    zstep. zstep. zstep.
    zstep. zstep. zstep. zstep.
    replace (fs + 1085440 + Z.shiftl i 7) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^7) with 128; lia).
    zstep.
    zstep. if_cases Kb; zify_cond Kb.
    { exfalso. clear - Kb FREE BOT CUR RS. rewrite ?Z.mod_small in Kb by lia. lia. }
    zstep. if_cases Kc; zify_cond Kc.
    { exfalso. clear - Kc FREE BOT CUR RS. rewrite ?Z.mod_small in Kc by lia. lia. }
    zstep.
    zstep.
    zstep. zstep. fold_lits. zsimp. zstep. zstep.
    zstep. if_cases K; zify_cond K.
    + ss_tail 1 FBASE TAIL ltac:(ss_cont; ss_last).
    + assert (HIGH : 0x10007fff8000 <= F) by (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; clear - FLOB FRNG K; lia).
      do 5 zstep. fold_lits. zsimp.
      zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2 FB FRNG F0. lia. }
      do 4 zstep.
      zstep. if_cases K3; zify_cond K3. { exfalso. clear - K3 FB FRNG F0. lia. }
      zstep. if_cases K4; zify_cond K4. { exfalso. clear - K4 HIGH. lia. }
      ss_tail 1 FBASE TAIL ltac:(ss_cont; ss_last).
  -
    change (2 ^ (15 - 2)) with 8192 in *. change (2 ^ (14 - 2)) with 4096 in *. change (2 ^ (6 + 2)) with 256 in *. change (2 ^ 2) with 4 in *.
    change (Z.to_nat 4) with 4%nat in LWS.
    destruct ws as [|w0 [|w1 [|w2 [|w3 [|w4 ws]]]]]; try (cbn in LWS; lia). cbn [map] in SHW.
    remember (fs + 4096 + (32768 - 8192)) as fbase eqn:FBASE.
    remember (fbase + i) as flag eqn:FLAG.
    remember (fs + 36864 + 2 * 1048576 + i * 256) as F eqn:FEQ.
    assert (FRNG : fs + 36864 <= F /\ F + 256 <= fs + 11571200) by (clear - FEQ I; lia).
    assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (SHD : shad F + 8 * 4 <= fs \/ fs + 11571200 <= shad F).
    { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FRNG ATR. lia. }
    assert (RFL : rng RNG flag 1) by (eapply rng_sub'; [exact RFS|]; clear - FLAG FBASE I; lia).
    assert (RFR : rng RNG (F + 24) 8) by (eapply rng_sub'; [exact RFS|]; clear - FRNG; lia).
    assert (RSF : rng RNG (shad F) (8 * 4)).
    { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      clear - FLOL FB FRNG. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl [(flag, flag + 1); (shad F, shad F + 8 * 4)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep. rewrite <- FLAG.
    zstep.
    zstep. if_cases Kd; zify_cond Kd.
    { exfalso. pose proof (bv_unsigned_in_range 8 b) as RB8. change (bv_modulus 8) with 256 in RB8. rewrite ?Z.mod_small in Kd by lia. lia. }
    zstep.
    zstep. zstep. zstep.
    zstep. zstep. zstep. zstep.
    replace (fs + 2134016 + Z.shiftl i 8) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; lia).
    zstep.
    zstep. if_cases Kb; zify_cond Kb.
    { exfalso. clear - Kb FREE BOT CUR RS. rewrite ?Z.mod_small in Kb by lia. lia. }
    zstep. if_cases Kc; zify_cond Kc.
    { exfalso. clear - Kc FREE BOT CUR RS. rewrite ?Z.mod_small in Kc by lia. lia. }
    zstep.
    zstep.
    zstep. zstep. fold_lits. zsimp. zstep. zstep.
    zstep. if_cases K; zify_cond K.
    + ss_tail 2 FBASE TAIL ltac:(ss_cont; ss_cont; ss_cont; ss_last).
    + assert (HIGH : 0x10007fff8000 <= F) by (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; clear - FLOB FRNG K; lia).
      do 5 zstep. fold_lits. zsimp.
      zstep. if_cases K2; zify_cond K2. 2:{ exfalso. clear - K2 FB FRNG F0. lia. }
      do 4 zstep.
      zstep. if_cases K3; zify_cond K3. { exfalso. clear - K3 FB FRNG F0. lia. }
      zstep. if_cases K4; zify_cond K4. { exfalso. clear - K4 HIGH. lia. }
      ss_tail 2 FBASE TAIL ltac:(ss_cont; ss_cont; ss_cont; ss_last).
Qed.
End CANSEC1.
End TwinB.
