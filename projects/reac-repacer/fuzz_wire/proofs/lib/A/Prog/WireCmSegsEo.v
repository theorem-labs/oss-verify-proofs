(* WireCmSegsEo: two footprint (lib/Lib/ExecF.v evtF) segments of check_meter (fuzz_wire.asan 0x80340), the length
   test at 0x80440 and the computation of the offset eo into s9, stepped by lib/Lib/StepF.v. The walk's other segments
   and its cut points are listed in lib/A/Prog/WireCmSegs.v. Shadow-check idioms: the released libreac/fuzz_decode
   lib/A/Prog/reac_frame_is_reac_F.v (the case split of a shadow check) and lib/A/Prog/reac_frame_counter_F.v
   (cm_shadow_byte_rng); segment form: reac-repacer/fuzz_uci lib/A/Prog/UciCvSegs.v. The model facts are the
   plain walk's lib/Prog/check_meter.v meter_eo_16 and meter_eo_12.
     cm_seg3_F  0x80440 -> 0x804e0  n < 14: `bltu s4, a0` (a0 = 14) is taken; s10 := 0, s9 := 12, `j 0x804e0`;
     cm_seg4_F  0x80440 -> 0x80484  14 <= n: the `bltu` falls through; a0 := f + 12, its shadow byte is loaded into a1
                and checked, a0 := f[12]; when f[12] = 0x81, a0 := f + 13, its shadow byte is checked the same way and
                a0 := f[13]; s9 := 16 when f[12] = 0x81 and f[13] = 0 (0x8060c), else s9 := 12 (0x80480).
   Each shadow check is `lb` of the shadow byte k, `bnez` to a slow arm that computes a2 := address & 7 and returns
   to the fast arm by `blt a2, a1`, else calls __asan_report_load1. The premise `addressable m (f + 12) 2` gives
   k = 0 or (address mod 8 < k <= 7), so both arms join and no report call is reached. No segment writes memory. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import
PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_meter_counter_c check_meter.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module PMC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_meter_counter_c.

(* the shadow byte of a + i, 0 <= i < n, lies in the shadow range of the buffer [a, a + n) *)
Lemma cm_shadow_byte_rng : forall RNG a n i, 0 <= i < n ->
  ExecF.rng RNG (shadow_addr a) (shadow_addr (a + n - 1) - shadow_addr a + 1) ->
  ExecF.rng RNG (shadow_addr (a + i)) 1.
Proof.
  intros RNG a n i Hi H. eapply rng_sub'; [exact H|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* cm_seg3_F : 0x80440 -> 0x804e0 when n < 14                          *)
(* ------------------------------------------------------------------ *)

(* 0x80440 -> 0x804e0 when n < 14: the length test is taken, s10 := 0 and s9 := 12, no memory is touched. *)
Lemma cm_seg3_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z),
    0 <= n < 14 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 n) s5 s6 s7
                     s8 (Z_to_bv 64 12) (Z_to_bv 64 0) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x804e0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 n) s5 s6 s7
             s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x80440) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n HN.
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  (* 0x80440 `bltu s4, a0`: n < 14, taken to 0x804d0 *)
  step. if_true.
  (* 0x804d0 `li s10, 0`; 0x804d4 `li s9, 12`; 0x804d8 `j 0x804e0` *)
  do 3 step.
  apply evtF_done. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* cm_seg4_F : 0x80440 -> 0x80484 when 14 <= n                         *)
(* ------------------------------------------------------------------ *)

(* 0x80440 -> 0x80484 when 14 <= n: f[12] and f[13] are read behind their shadow checks and s9 becomes the
   offset eo (16 when f[12] = 0x81 and f[13] = 0, else 12). No memory is touched. *)
Lemma cm_seg4_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n : Z) (bs : list byte),
    14 <= n < 2 ^ 64 ->
    (14 <= length bs)%nat -> bytes_at rsegs m f bs ->
    addressable m (f + 12) 2 ->
    0 <= f -> f + 20 <= 2 ^ 64 ->
    ExecF.rng RNG (f + 12) 2 ->
    ExecF.rng RNG (shadow_addr (f + 12)) (shadow_addr (f + 12 + 2 - 1) - shadow_addr (f + 12) + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a0' a1' a2',
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 (Z_to_bv 64 f) (Z_to_bv 64 n)
                     s5 s6 s7 (Z_to_bv 64 ASAN_K) (Z_to_bv 64 (Z.of_nat (PMC.meter_eo n bs))) s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x80484) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 14) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 f) (Z_to_bv 64 n)
             s5 s6 s7 (Z_to_bv 64 ASAN_K) s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x80440) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m f n bs
    HN LEN BA ADR F0 FE RBUF RSH.
  pose proof (cm_shadow_byte_rng RNG (f + 12) 2 0 ltac:(lia) RSH) as RS12.
  pose proof (cm_shadow_byte_rng RNG (f + 12) 2 1 ltac:(lia) RSH) as RS13.
  rewrite Z.add_0_r in RS12.
  replace (f + 12 + 1) with (f + 13) in RS13 by lia.
  clear RSH.
  destruct ADR as (_ & _ & _ & AB).
  destruct (AB 0 ltac:(lia)) as (_ & k12 & MK12 & SK12).
  destruct (AB 1 ltac:(lia)) as (_ & k13 & MK13 & SK13).
  clear AB.
  rewrite Z.add_0_r in MK12, SK12.
  replace (f + 12 + 1) with (f + 13) in MK13, SK13 by lia.
  unfold shadow_addr, shadow_ok, ASAN_K in *.
  pose proof (bytes_nth m f bs 12 BA ltac:(lia)) as F12.
  pose proof (bytes_nth m f bs 13 BA ltac:(lia)) as F13.
  change (Z.of_nat 12) with 12 in F12. change (Z.of_nat 13) with 13 in F13.
  remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
  remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
  assert (ZB12 : bv_unsigned (zxb b12) = bv_unsigned b12) by apply zxb_u.
  assert (ZB13 : bv_unsigned (zxb b13) = bv_unsigned b13) by apply zxb_u.
  pose proof (Z.mod_pos_bound (f + 12) 8 ltac:(lia)) as MB12.
  pose proof (Z.mod_pos_bound (f + 13) 8 ltac:(lia)) as MB13.
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (UF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  remember (Z_to_bv 64 f) as wf eqn:EWF.
  (* 0x80440 `bltu s4, a0`: 14 <= n, not taken *)
  step. if_false.
  (* 0x80444 `addi a0, s3, 12`; 0x80448 `srli a1, a0, 3`; 0x8044c `add a1, a1, s8`: a1 = the shadow address *)
  step. gen_addi wf w12 U12. rewrite UF in U12.
  step. gen_shr w12 g12 G12. rewrite U12 in G12.
  step. gen_addi g12 h12 H12.
  pose proof (rng_sub' _ _ _ (bv_unsigned h12) 1 RS12 ltac:(lia)) as RH12.
  (* 0x80450 `lb a1, 0(a1)`: the shadow byte k12 *)
  pose proof (rdw0 m h12 _ _ MK12 ltac:(lia)) as R. step. clear R.
  (* 0x80454 `bnez a1`: k12 = 0 falls through to 0x80458; else 0x80614 `andi a2, a0, 7` and 0x80618 `blt a2, a1`
     return to 0x80458, as (f + 12) mod 8 < k12 *)
  step.
  destruct SK12 as [C|[C Cu]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k12) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U12, (lts_low ((f + 12) mod 8) k12 MB12), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
  (* 0x80458 `lbu a0, 0(a0)`: f[12]; 0x8045c `li a1, 129`; 0x80460 `bne a0, a1` to 0x80480 *)
  all: pose proof (rng_sub' _ _ _ (bv_unsigned w12) 1 RBUF ltac:(lia)) as RW12.
  all: pose proof (rdw0 m w12 _ _ F12 ltac:(lia)) as R; step; clear R.
  all: do 2 step.
  all: destruct (Z.eqb_spec (bv_unsigned b12) 129) as [E81|N81].
  (* f[12] <> 0x81: taken to 0x80480 `li s9, 12`, eo = 12 *)
  2, 4: if_true; step;
        assert (Heo : PMC.meter_eo n bs = 12%nat)
          by (apply check_meter.meter_eo_12; right; left; unfold PMC.meter_byte; rewrite <- E12; exact N81);
        rewrite Heo; apply evtF_done; do 3 eexists; reflexivity.
  (* f[12] = 0x81: 0x80464 `addi a0, s3, 13`; 0x80468 `srli a1, a0, 3`; 0x8046c `add a1, a1, s8` *)
  all: if_false.
  all: step; gen_addi wf w13 U13.
  all: rewrite UF in U13.
  all: step; gen_shr w13 g13 G13.
  all: rewrite U13 in G13.
  all: step; gen_addi g13 h13 H13.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned h13) 1 RS13 ltac:(lia)) as RH13.
  (* 0x80470 `lb a1, 0(a1)`: the shadow byte k13; 0x80474 `bnez a1`: k13 = 0 falls through to 0x80478; else
     0x8063c `andi a2, a0, 7` and 0x80640 `blt a2, a1` return to 0x80478, as (f + 13) mod 8 < k13 *)
  all: pose proof (rdw0 m h13 _ _ MK13 ltac:(lia)) as R; step; clear R.
  all: step.
  all: destruct SK13 as [C'|[C' Cu']].
  1, 3: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C'); cbn [negb].
  all: try (rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k13) 0) ltac:(lia)); cbn [negb]; step; step;
        rewrite land7, U13, (lts_low ((f + 13) mod 8) k13 MB13), (proj2 (Z.ltb_lt _ _) C'); cbn [negb]).
  (* 0x80478 `lbu a0, 0(a0)`: f[13]; 0x8047c `beqz a0` to 0x8060c *)
  all: pose proof (rng_sub' _ _ _ (bv_unsigned w13) 1 RBUF ltac:(lia)) as RW13.
  all: pose proof (rdw0 m w13 _ _ F13 ltac:(lia)) as R; step; clear R.
  all: step.
  all: destruct (Z.eqb_spec (bv_unsigned b13) 0) as [EZ13|NZ13].
  (* f[13] = 0: taken to 0x8060c `li s9, 16`; 0x80610 `j 0x80484`, eo = 16 *)
  1, 3, 5, 7: if_true; do 2 step;
              assert (Heo : PMC.meter_eo n bs = 16%nat)
                by (apply check_meter.meter_eo_16;
                    [ lia
                    | unfold PMC.meter_byte; rewrite <- E12; exact E81
                    | unfold PMC.meter_byte; rewrite <- E13; exact EZ13 ]);
              rewrite Heo; apply evtF_done; do 3 eexists; reflexivity.
  (* f[13] <> 0: falls through to 0x80480 `li s9, 12`, eo = 12 *)
  all: if_false; step;
       assert (Heo : PMC.meter_eo n bs = 12%nat)
         by (apply check_meter.meter_eo_12; right; right; unfold PMC.meter_byte; rewrite <- E13; exact NZ13);
       rewrite Heo; apply evtF_done; do 3 eexists; reflexivity.
Qed.
