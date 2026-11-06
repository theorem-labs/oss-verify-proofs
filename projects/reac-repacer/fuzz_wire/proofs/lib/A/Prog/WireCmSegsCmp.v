(* WireCmSegsCmp: cm_seg7_F, the piece 0x80508 -> 0x80568 of the footprint (lib/Lib/ExecF.v evtF) walk of check_meter
   (fuzz_wire.asan 0x80340), stepped by lib/Lib/StepF.v. The list of the walk's pieces is the header of
   lib/A/Prog/WireCmSegs.v. Form: reac-repacer/fuzz_uci lib/A/Prog/UciCvSegs.v; cm_shadow_byte_rng is the released
   libreac/fuzz_decode lib/A/Prog/reac_frame_counter_F.v's; the model facts are those of the plain walk lib/Prog/check_meter.v.
   The piece, after the call of rp_meter_counter (a0 = its result, s10 = the meter test, s5 = &ctr, s3 = f, s9 = eo,
   s8 = the shadow base):
     0x80508 `bne a0, s10` to the abort: not taken (a0 = s10);
     0x8050c `lhu a2, 0(s5)`: a2 := the counter;
     0x80510 `beqz s10` to 0x8055c:
       s10 = 0: taken; 0x8055c `lui a0, 0xa`, 0x80560 `addiw a0, a0, 1475` (a0 := 0xa5c3) and 0x80564 `bne a2, a0` to
                the abort, not taken: the counter still holds 0xa5c3;
       s10 = 1: 0x80514 a1 := f + eo, a0 := f + eo + 2, the shadow check of a0 (a3, and a4 on its slow arm),
                0x8052c a1 := f + eo + 3, its shadow check, 0x8053c `lbu a0` := f[eo + 2], 0x80544 `lbu a1` := f[eo + 3],
                `slli`, `or` (a0 := f[eo + 2] | f[eo + 3] << 8) and 0x80550 `beq a0, a2` to 0x80568, taken: the counter
                holds meter_value = f[eo + 2] + 256 * f[eo + 3].
   No instruction of the piece writes memory; a0 .. a4 are the only registers it changes. *)
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
Module PCM := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.check_meter.

(* the shadow byte of a + i, 0 <= i < n, lies in the shadow range of the buffer [a, a + n) *)
Lemma cm_shadow_byte_rng : forall RNG a n i, 0 <= i < n ->
  ExecF.rng RNG (shadow_addr a) (shadow_addr (a + n - 1) - shadow_addr a + 1) ->
  ExecF.rng RNG (shadow_addr (a + i)) 1.
Proof.
  intros RNG a n i Hi H. eapply rng_sub'; [exact H|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

(* The two bytes at a, read as one 2-byte access (the `lhu` of the counter). *)
Lemma cm_rd_le2 : forall m a v, bytes_at rsegs m a (le2 v) -> ov_read_bytes rsegs m (wa a) 2 = Some (le2 v).
Proof.
  intros m a v H. rewrite <- (Z.add_0_r a).
  rewrite (bytes_at_read rsegs m a (le2 v) 0 2 H ltac:(lia)) by (rewrite length_le2; lia).
  reflexivity.
Qed.

(* 0x80508 -> 0x80568, the piece after the call of the leaf: the result against s10, the counter read back, and
   either f[eo+2] and f[eo+3] behind their shadow checks or the untouched value 0xa5c3. Neither the `bne` at
   0x80508 nor the one at 0x80564 nor the `beq` at 0x80550 reaches the abort at 0x80554, and no report call is
   reached. No memory is touched. *)
Lemma cm_seg7_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n ctr : Z) (bs : list byte),
    0 <= n < 2 ^ 64 ->
    (1000 <= n -> (20 <= length bs)%nat) -> (1000 <= n -> bytes_at rsegs m f bs) ->
    (1000 <= n -> addressable m (f + 12) 8) ->
    (1000 <= n -> 0 <= f /\ f + 20 <= 2 ^ 64) -> 0 <= ctr -> ctr + 2 <= 2 ^ 64 ->
    (1000 <= n -> ExecF.rng RNG (f + 12) 8) ->
    (1000 <= n -> ExecF.rng RNG (shadow_addr (f + 12))
                    (shadow_addr (f + 12 + 8 - 1) - shadow_addr (f + 12) + 1)) ->
    ExecF.rng RNG ctr 2 ->
    bytes_at rsegs m ctr
      (if PMC.meter_ok n bs then le2 (Z_to_bv 64 (PMC.meter_value n bs)) else le2 (Z_to_bv 64 42435)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a0' a1' a2' a3' a4',
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5 a6 a7 s2 (Z_to_bv 64 f) (Z_to_bv 64 n)
                     (Z_to_bv 64 ctr) s6 s7 (Z_to_bv 64 ASAN_K) (Z_to_bv 64 (Z.of_nat (PMC.meter_eo n bs)))
                     (Z_to_bv 64 (if PMC.meter_ok n bs then 1 else 0)) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x80568) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if PMC.meter_ok n bs then 1 else 0)) a1 a2 a3 a4 a5 a6 a7 s2
             (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 ctr) s6 s7 (Z_to_bv 64 ASAN_K)
             (Z_to_bv 64 (Z.of_nat (PMC.meter_eo n bs)))
             (Z_to_bv 64 (if PMC.meter_ok n bs then 1 else 0)) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x80508) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s11 t3 t4 t5 t6 F fc m f n ctr bs
    HN LEN BA ADR HF Hc0 Hc1 RF RSH RC BC.
  unfold ASAN_K.
  pose proof (PCM.meter_eo_cases n bs) as EOC.
  assert (EOB : (12 <= PMC.meter_eo n bs <= 16)%nat) by (destruct EOC as [E|E]; rewrite E; lia).
  remember (Z.of_nat (PMC.meter_eo n bs)) as e eqn:Ee.
  remember (Z_to_bv 64 f) as wf eqn:Ewf.
  remember (Z_to_bv 64 ctr) as wc eqn:Ewc.
  remember (Z_to_bv 64 e) as we eqn:Ewe.
  assert (UC : bv_unsigned wc = ctr) by (subst wc; apply unsigned_lit; lia).
  assert (UE : bv_unsigned we = e) by (subst we e; apply unsigned_lit; lia).
  rewrite <- UC in RC.
  pose proof (cm_rd_le2 m ctr) as RD2. change (wa ctr) with (Z_to_bv 64 ctr) in RD2. rewrite <- Ewc in RD2.
  revert BC. destruct (PMC.meter_ok n bs) eqn:Hok; intros BC; cbv iota in BC |- *.
  - (* the meter held: f[eo + 2] and f[eo + 3] behind their shadow checks *)
    assert (H1000 : 1000 <= n).
    { destruct (Z.lt_ge_cases n 1000) as [Hl|Hl]; [|exact Hl].
      rewrite (PCM.meter_ok_short n bs Hl) in Hok. discriminate. }
    specialize (LEN H1000). specialize (ADR H1000). specialize (RF H1000). specialize (RSH H1000).
    specialize (BA H1000). destruct (HF H1000) as [Hf0 Hf1].
    assert (UF : bv_unsigned wf = f) by (subst wf; apply unsigned_lit; lia).
    pose proof (RD2 _ BC) as RDC. clear RD2.
    pose proof (PCM.meter_value_range n bs) as VR.
    destruct ADR as (P0 & N0 & PE & AB).
    destruct (AB (e - 10) ltac:(lia)) as (_ & k2 & MK2 & SK2).
    destruct (AB (e - 9) ltac:(lia)) as (_ & k3 & MK3 & SK3).
    pose proof (cm_shadow_byte_rng RNG (f + 12) 8 (e - 10) ltac:(lia) RSH) as RS2.
    pose proof (cm_shadow_byte_rng RNG (f + 12) 8 (e - 9) ltac:(lia) RSH) as RS3.
    replace (f + 12 + (e - 10)) with (f + e + 2) in MK2, SK2, RS2 by lia.
    replace (f + 12 + (e - 9)) with (f + e + 3) in MK3, SK3, RS3 by lia.
    unfold shadow_addr, shadow_ok, ASAN_K in MK2, SK2, MK3, SK3, RS2, RS3.
    clear AB RSH.
    remember (nth (PMC.meter_eo n bs + 2) bs (Z_to_bv 8 0)) as b2 eqn:E2.
    remember (nth (PMC.meter_eo n bs + 3) bs (Z_to_bv 8 0)) as b3 eqn:E3.
    assert (F2 : mrd rsegs m (wa (f + e + 2)) = Some b2).
    { subst b2. replace (f + e + 2) with (f + Z.of_nat (PMC.meter_eo n bs + 2)) by lia.
      apply bytes_nth; [exact BA | lia]. }
    assert (F3 : mrd rsegs m (wa (f + e + 3)) = Some b3).
    { subst b3. replace (f + e + 3) with (f + Z.of_nat (PMC.meter_eo n bs + 3)) by lia.
      apply bytes_nth; [exact BA | lia]. }
    pose proof (Z.mod_pos_bound (f + e + 2) 8 ltac:(lia)) as MB2.
    pose proof (Z.mod_pos_bound (f + e + 3) 8 ltac:(lia)) as MB3.
    assert (EV : Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned b3) 8))) (bv_unsigned b2))
                 = Z_to_bv 64 (PMC.meter_value n bs)).
    { rewrite PCM.chk_lor16. f_equal. rewrite (PCM.meter_value_eo n bs _ eq_refl). unfold PMC.meter_byte.
      subst b2 b3. reflexivity. }
    (* 0x80508 `bne a0, s10`: both 1 *)
    step. if_false.
    (* 0x8050c `lhu a2, 0(s5)`: a2 := meter_value *)
    step. rewrite (PCM.zx16_lit (PMC.meter_value n bs)) by exact VR.
    (* 0x80510 `beqz s10`: s10 = 1, not taken *)
    step. if_false.
    (* 0x80514 `add a1, s3, s9`: a1 := f + eo; 0x80518 `addi a0, a1, 2`: a0 := f + eo + 2 *)
    step. gen_add wf we w1 U1. rewrite UF, UE in U1.
    step. gen_addi w1 w2 U2. rewrite U1 in U2.
    pose proof (rng_sub' _ _ _ (bv_unsigned w2) 1 RF ltac:(lia)) as RW2.
    (* 0x8051c .. 0x80528: a3 := the shadow byte of f + eo + 2, `bnez a3` to the slow arm 0x80620 .. 0x80624 *)
    step. gen_shr w2 g2 G2. rewrite U2 in G2.
    step. gen_addi g2 h2 H2.
    pose proof (rng_sub' _ _ _ (bv_unsigned h2) 1 RS2 ltac:(lia)) as RH2.
    pose proof (rdw0 m h2 _ _ MK2 ltac:(lia)) as R. step. clear R.
    step.
    destruct SK2 as [C|[C Cu]];
      [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]
      | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k2) 0) ltac:(lia)); cbn [negb]; step; step;
        rewrite land7, U2, (lts_low ((f + e + 2) mod 8) k2 MB2), (proj2 (Z.ltb_lt _ _) C); cbn [negb] ].
    (* 0x8052c `addi a1, a1, 3`: a1 := f + eo + 3; 0x80530 .. 0x80538: a3 := its shadow byte *)
    all: step; gen_addi w1 w3 U3.
    all: rewrite U1 in U3.
    all: pose proof (rng_sub' _ _ _ (bv_unsigned w3) 1 RF ltac:(lia)) as RW3.
    all: step; gen_shr w3 g3 G3.
    all: rewrite U3 in G3.
    all: step; gen_addi g3 h3 H3.
    all: pose proof (rng_sub' _ _ _ (bv_unsigned h3) 1 RS3 ltac:(lia)) as RH3.
    all: pose proof (rdw0 m h3 _ _ MK3 ltac:(lia)) as R; step; clear R.
    (* 0x8053c `lbu a0, 0(a0)`: a0 := f[eo + 2]; 0x80540 `bnez a3` to the slow arm 0x8062c .. 0x80630 *)
    all: pose proof (rdw0 m w2 _ _ F2 ltac:(lia)) as R; step; clear R.
    all: step.
    all: destruct SK3 as [C'|[C' Cu']];
      [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C'); cbn [negb]
      | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k3) 0) ltac:(lia)); cbn [negb]; step; step;
        rewrite land7, U3, (lts_low ((f + e + 3) mod 8) k3 MB3), (proj2 (Z.ltb_lt _ _) C'); cbn [negb] ].
    (* 0x80544 `lbu a1, 0(a1)`: a1 := f[eo + 3]; `slli`, `or`: a0 := f[eo + 2] | f[eo + 3] << 8 = meter_value *)
    all: pose proof (rdw0 m w3 _ _ F3 ltac:(lia)) as R; step; clear R.
    all: step; step.
    all: unfold zxb; rewrite !zxb_u, EV.
    (* 0x80550 `beq a0, a2`: taken, to 0x80568 *)
    all: step; if_true.
    all: apply evtF_done; do 5 eexists; reflexivity.
  - (* the meter declined: the counter still holds 0xa5c3 *)
    pose proof (RD2 _ BC) as RDC. clear RD2.
    (* 0x80508 `bne a0, s10`: both 0 *)
    step. if_false.
    (* 0x8050c `lhu a2, 0(s5)`: a2 := 0xa5c3 *)
    step. rewrite (PCM.zx16_lit 42435) by lia.
    (* 0x80510 `beqz s10`: taken, to 0x8055c; `lui`, `addiw`: a0 := 0xa5c3 *)
    step. if_true.
    step. step.
    (* 0x80564 `bne a2, a0`: not taken *)
    step. if_false.
    apply evtF_done. do 5 eexists. reflexivity.
Qed.
