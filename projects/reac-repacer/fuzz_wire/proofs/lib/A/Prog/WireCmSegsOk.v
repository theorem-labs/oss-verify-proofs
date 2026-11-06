(* WireCmSegsOk: cm_seg5_F, the footprint (lib/Lib/ExecF.v evtF) run of check_meter (fuzz_wire.asan 0x80340) from
   0x80484 to the join 0x804e0, stepped by lib/Lib/StepF.v. Form and idioms: lib/A/Prog/WireCmSegs.v (cm_seg1_F),
   reac-repacer/fuzz_uci lib/A/Prog/UciCvSegs.v, and the released libreac/fuzz_decode lib/B/Prog/reac_frame_inspect_F.v
   (the case split of a shadow check) and lib/A/Prog/reac_frame_counter_F.v (cm_shadow_byte_rng). The model facts are
   the released plain walk lib/Prog/check_meter.v (meter_ok_short, meter_ok_eo, meter_eo_cases, chk_seqz_byte).
   The code (s3 = f, s4 = n, s8 = ASAN_K, s9 = eo):
     80484 `li a0, 1000`; 80488 `bltu s4, a0` to 804dc (n < 1000: `li s10, 0` and on to 804e0);
     8048c `add a0, s3, s9`; `srli a1, a0, 3`; `add a1, a1, s8`; `lb a1, 0(a1)` (the shadow byte of f + eo);
     8049c `bnez a1` to 80648 (`andi a2, a0, 7`; `blt a2, a1` back to 804a0, else __asan_report_load1);
     804a0 `lbu a1, 0(a0)` (f[eo]); `li a2, 136`; 804a8 `bne a1, a2` to 804dc (`li s10, 0`);
     804ac `addi a0, a0, 1`; `srli a1, a0, 3`; `add a1, a1, s8`; `lb a1, 0(a1)` (the shadow byte of f + eo + 1);
     804bc `bnez a1` to 80654 (`andi a2, a0, 7`; `blt a2, a1` back to 804c0, else __asan_report_load1);
     804c0 `lbu a0, 0(a0)` (f[eo + 1]); `addi a0, a0, -25`; 804c8 `seqz s10, a0`; 804cc `j 804e0`.
   Only a0, a1, a2 and s10 change; memory is only read. The addressability of [f + 12, f + 20) gives each shadow byte
   k with k = 0 or (address mod 8 < k <= 7), so each check falls through or returns from its partial-granule test and
   no report call is reached. *)
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

(* `zify_cond` on a byte test, with the zero-extension of the loaded byte read back (lib/Prog/check_meter.v). *)
Ltac cm5_byte_cond H := zify_cond H; rewrite ?zxb_u in H.

(* One shadow check after its `bnez`: k = 0 falls through; otherwise the slow arm's `andi a2, a0, 7` and
   `blt a2, a1` return to the fast arm, because (address mod 8) < k. U is the address word's value, MB its mod-8
   bound. *)
Ltac cm5_shadow SK k U MB :=
  let C := fresh "C" in let Cu := fresh "Cu" in
  destruct SK as [C|[C Cu]];
  [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]
  | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
    rewrite land7, U, (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb] ].

(* 0x80484 -> 0x804e0: the 1000-byte test, then f[eo] against 0x88 and f[eo+1] against 0x19, each behind its
   shadow check; s10 becomes the meter test. No memory is touched. *)
Lemma cm_seg5_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n : Z) (bs : list byte),
    14 <= n < 2 ^ 64 ->
    (1000 <= n -> (20 <= length bs)%nat) -> bytes_at rsegs m f bs ->
    (1000 <= n -> addressable m (f + 12) 8) ->
    0 <= f -> f + 20 <= 2 ^ 64 ->
    (1000 <= n -> ExecF.rng RNG (f + 12) 8) ->
    (1000 <= n -> ExecF.rng RNG (shadow_addr (f + 12))
                    (shadow_addr (f + 12 + 8 - 1) - shadow_addr (f + 12) + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a0' a1' a2',
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 (Z_to_bv 64 f) (Z_to_bv 64 n)
                     s5 s6 s7 (Z_to_bv 64 ASAN_K) (Z_to_bv 64 (Z.of_nat (PMC.meter_eo n bs)))
                     (Z_to_bv 64 (if PMC.meter_ok n bs then 1 else 0)) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x804e0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 f) (Z_to_bv 64 n)
             s5 s6 s7 (Z_to_bv 64 ASAN_K) (Z_to_bv 64 (Z.of_nat (PMC.meter_eo n bs))) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x80484) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s10 s11 t3 t4 t5 t6 F fc m f n bs
    HN LEN BA ADR F0 FE RBUF RSH.
  (* s3 = f and s4 = n as opaque words with their values; s8 = the shadow base as a literal *)
  assert (U3 : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (U4 : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  revert U3 U4. generalize (Z_to_bv 64 f) (Z_to_bv 64 n). intros s3 s4 U3 U4.
  unfold ASAN_K.
  destruct (Z_lt_le_dec n 1000) as [HS|HL].
  - (* n < 1000: 0x80488 `bltu s4, a0` taken, 0x804dc `li s10, 0`; the meter declines *)
    rewrite (check_meter.meter_ok_short n bs HS).
    step. step. if_true. step.
    apply evtF_done. do 3 eexists. reflexivity.
  - (* 1000 <= n: s9 = eo, which is 12 or 16, so f + eo and f + eo + 1 lie in [f + 12, f + 20) *)
    specialize (LEN HL). specialize (ADR HL). specialize (RBUF HL). specialize (RSH HL).
    rewrite (check_meter.meter_ok_eo n bs (PMC.meter_eo n bs) eq_refl HL).
    pose proof (check_meter.meter_eo_cases n bs) as HE.
    revert HE. generalize (PMC.meter_eo n bs). intros eo HE.
    assert (HE' : (12 <= eo <= 16)%nat) by lia. clear HE.
    destruct ADR as (P0 & N0 & PE & AB).
    destruct (AB (Z.of_nat eo - 12) ltac:(lia)) as (APP0 & k0 & MK0 & SK0).
    destruct (AB (Z.of_nat eo - 11) ltac:(lia)) as (APP1 & k1 & MK1 & SK1).
    pose proof (cm_shadow_byte_rng RNG (f + 12) 8 (Z.of_nat eo - 12) ltac:(lia) RSH) as RS0.
    pose proof (cm_shadow_byte_rng RNG (f + 12) 8 (Z.of_nat eo - 11) ltac:(lia) RSH) as RS1.
    clear RSH AB.
    replace (f + 12 + (Z.of_nat eo - 12)) with (f + Z.of_nat eo) in APP0, MK0, SK0, RS0 by lia.
    replace (f + 12 + (Z.of_nat eo - 11)) with (f + Z.of_nat eo + 1) in APP1, MK1, SK1, RS1 by lia.
    unfold shadow_addr, shadow_ok, ASAN_K in MK0, SK0, MK1, SK1, RS0, RS1.
    pose proof (bytes_nth m f bs eo BA ltac:(lia)) as B0.
    pose proof (bytes_nth m f bs (eo + 1) BA ltac:(lia)) as B1.
    pose proof (Z.mod_pos_bound (f + Z.of_nat eo) 8 ltac:(lia)) as MB0.
    pose proof (Z.mod_pos_bound (f + Z.of_nat eo + 1) 8 ltac:(lia)) as MB1.
    unfold PMC.meter_byte.
    (* 0x80484 `li a0, 1000`; 0x80488 `bltu s4, a0` not taken *)
    step. step. if_false.
    (* 0x8048c .. 0x80498: a0 = f + eo, a1 = its shadow address, then its shadow byte k0 *)
    step. gen_addi s3 w0 U0. rewrite U3 in U0.
    pose proof (rng_sub' _ _ _ (bv_unsigned w0) 1 RBUF ltac:(lia)) as RW0.
    step. gen_shr w0 g0 G0. rewrite U0 in G0.
    step. gen_addi g0 h0 H0.
    pose proof (rng_sub' _ _ _ (bv_unsigned h0) 1 RS0 ltac:(lia)) as RH0.
    pose proof (rdw0 m h0 _ _ MK0 ltac:(lia)) as R. step. clear R.
    (* 0x8049c `bnez a1` *)
    step. cm5_shadow SK0 k0 U0 MB0.
    (* 0x804a0 `lbu a1, 0(a0)` (f[eo]); 0x804a4 `li a2, 136`; 0x804a8 `bne a1, a2` *)
    all: pose proof (rdw0 m w0 _ _ B0 ltac:(lia)) as R; step; clear R.
    all: step; step.
    all: let HB := fresh "HB" in if_cases HB; cm5_byte_cond HB.
    (* f[eo] <> 0x88: 0x804dc `li s10, 0` *)
    1, 3: step; rewrite (proj2 (Z.eqb_neq _ _) HB), andb_false_l;
          apply evtF_done; do 3 eexists; reflexivity.
    (* f[eo] = 0x88: 0x804ac .. 0x804b8, a0 = f + eo + 1, a1 = its shadow address, then its shadow byte k1 *)
    all: rewrite (proj2 (Z.eqb_eq _ _) HB), andb_true_l.
    all: step; gen_addi w0 w1 U1; rewrite U0 in U1.
    all: pose proof (rng_sub' _ _ _ (bv_unsigned w1) 1 RBUF ltac:(lia)) as RW1.
    all: step; gen_shr w1 g1 G1; rewrite U1 in G1.
    all: step; gen_addi g1 h1 H1.
    all: pose proof (rng_sub' _ _ _ (bv_unsigned h1) 1 RS1 ltac:(lia)) as RH1.
    all: pose proof (rdw0 m h1 _ _ MK1 ltac:(lia)) as R; step; clear R.
    (* 0x804bc `bnez a1` *)
    all: step; cm5_shadow SK1 k1 U1 MB1.
    (* 0x804c0 `lbu a0, 0(a0)` (f[eo + 1]); `addi a0, a0, -25`; 0x804c8 `seqz s10, a0`; 0x804cc `j 0x804e0` *)
    all: pose proof (rdw0 m w1 _ _ B1 ltac:(lia)) as R; step; clear R.
    all: step; step; rewrite (check_meter.chk_seqz_byte _ 25 (-25)) by lia; step.
    all: apply evtF_done; do 3 eexists; reflexivity.
Qed.
