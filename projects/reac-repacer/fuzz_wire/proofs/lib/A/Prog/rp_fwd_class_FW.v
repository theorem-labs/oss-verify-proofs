(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/B/Prog/is_tagged_reac_F.v, with its module paths, module names and numbers changed; 151 of its 178 lines of code are new or changed and 165 lines of the source are left out. *)
(* Modified by Theorem Labs: the footprint walk of reac-repacer/fuzz_wire's rp_fwd_class in image A, against the frozen lib/A/Prog/rp_fwd_class_F_c.v rp_fwd_class_contract_F. It is proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_F.v (at commit 88154566652a; decode's released guarded, non-writing leaf walk: StepF's step, one rng fact per access, the shadow byte test of each byte load closed from addressable; its is_reac_shadow_byte_rng is fwd_shadow_byte_rng here) with the branch structure and the model closing of this unit's plain walk lib/Prog/rp_fwd_class.v (its zc / bfacts / fin tactics and its tail16 split, carried to the footprint run). *)
(* rp_fwd_class of fuzz_wire.asan (entry 0x80ec4, 0x11c bytes): `addi sp, sp, -0x10`, `sd ra, 8(sp)`, `li a3, 18`,
   `bltu a1, a3` to the exit 0x80f40 (a0 = 0); past it the shadow base through the GOT word 0x987e8 and the cell
   0xa0778, then the byte loads f[12] (0x80ef4), f[13] (0x80f14), f[0] (0x80f34, only when a2 <> 0: `beqz a2` at
   0x80f20), f[16] (0x80f64) and f[17] (0x80f80). Before each `lbu` of a byte at x it loads the shadow byte k of x,
   (x >> 3) + 0x7fff8000, and when k <> 0 runs `andi t, x, 7`; `blt t, k, back` (0x80f98, 0x80fa8, 0x80fb8, 0x80fc4,
   0x80fd4), else falls into `jal __asan_report_load1`. The premise `addressable m f 18` gives each of the five shadow
   bytes with k = 0 \/ x mod 8 < k, so each test returns to `back` (shck below) and no report call is reached. The
   exits 0x80f40 (a0 = 0), 0x80f88 (a0 = 2) and 0x80f90 (a0 = 1) end in `ld ra, 8(sp)`; `addi sp, sp, 16`; `ret`. The
   only store is the ra save into the frame, so every shadow byte and every byte of f is read through the munch fact
   of that store from the entry memory (fwd_sh_tp, fwd_byte_tp). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA AsanKAProof rp_fwd_class_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The shadow byte of a + i, 0 <= i < n, lies in the shadow range of the buffer [a, a + n)
   (reac_frame_is_reac_F.v is_reac_shadow_byte_rng). *)
Lemma fwd_shadow_byte_rng : forall RNG a n i, 0 <= i < n ->
  ExecF.rng RNG (shadow_addr a) (shadow_addr (a + n - 1) - shadow_addr a + 1) ->
  ExecF.rng RNG (shadow_addr (a + i)) 1.
Proof.
  intros RNG a n i Hi H. eapply rng_sub'; [exact H|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

(* The shadow byte of an application address lies outside the frame [s - 16, s), itself application memory, so the
   ra save leaves that byte unchanged. *)
Lemma fwd_sh_tp : forall m m' (s a : Z) k,
  munch [(s + -16, s)] m m' -> app_mem (s + -16) -> app_mem (s - 1) -> app_mem a ->
  mrd rsegs m (wa (shadow_addr a)) = Some k -> mrd rsegs m' (wa (shadow_addr a)) = Some k.
Proof.
  intros m m' s a k MU H1 H2 Ha H.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1, H2, Ha.
  apply (mrd_tp m m' (s + -16) s _ k MU); [| | exact H];
    unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* A byte of [p, p + 18), a buffer off the frame, is unchanged by the ra save. *)
Lemma fwd_byte_tp : forall m m' (s p : Z) bs i, munch [(s + -16, s)] m m' ->
  bytes_at rsegs m p bs -> (i < length bs)%nat -> (i < 18)%nat -> 0 <= p -> p + 18 <= 2^64 ->
  (p + 18 <= s - 16 \/ s <= p) ->
  mrd rsegs m' (wa (p + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0)).
Proof.
  intros m m' s p bs i MU B Hi H18 P0 P1 D.
  apply (mrd_tp m m' (s + -16) s); [exact MU | lia | lia | apply bytes_nth; assumption].
Qed.

Local Ltac zc H := zify_cond H; rewrite ?zxb_u in H.

Local Ltac bfacts :=
  repeat match goal with
  | H : ?x = ?c |- context [Z.eqb ?x ?c] => rewrite (proj2 (Z.eqb_eq x c) H)
  | H : ?x <> ?c |- context [Z.eqb ?x ?c] => rewrite (proj2 (Z.eqb_neq x c) H)
  | H : ?x < ?c |- context [Z.ltb ?x ?c] => rewrite (proj2 (Z.ltb_lt x c) H)
  | H : ?c <= ?x |- context [Z.ltb ?x ?c] => rewrite (proj2 (Z.ltb_ge x c) H)
  end.

(* At a `ret` to ra: close the post. a0 is the literal the exit set; fwd_class_result is evaluated with the branch
   facts the walk collected (lib/Prog/rp_fwd_class.v fin), and the frame is given back to the stack. *)
Local Ltac fin :=
  apply evtF_done; unfold PFC.fwd_class_result, PFC.fwd_byte;
  repeat match goal with Eb : ?b = nth ?i ?l ?d |- context [nth ?i ?l ?d] => rewrite <- Eb end;
  bfacts;
  do 6 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|];
  lazymatch goal with
  | FR : rw_cells _ _ _ _, ST : stk _ _ _ _ |- stk _ _ _ (bv_unsigned ?s) =>
      release_frame FR ST (bv_unsigned s); exact ST
  end.

(* At the `bnez` on the shadow byte k of the byte at x (tu: the rewrite of the `andi` operand to x): k = 0 falls
   through to the `lbu`; k <> 0 runs `andi t, x, 7`; `blt t, k, back`, which returns to the `lbu` because
   x mod 8 < k, so the `jal __asan_report_load1` after it is not reached. *)
Local Ltac shck SK k x tu :=
  let C := fresh "C" in let Cu := fresh "Cu" in let MB := fresh "MB" in
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as MB;
  destruct SK as [C|[C Cu]];
  [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]
  | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
    rewrite land7; tu; rewrite (lts_low (x mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb] ].

Theorem rp_fwd_class_holds_F : rp_fwd_class_contract_F.
Proof.
  unfold rp_fwd_class_contract_F, RP_FWD_CLASS, RP_FWD_CLASS_FRAME, RP_FWD_CLASS_SPAN.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs
    lo ST HLO HB RFR RGOT RCELL RBUF RSH.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  carve_frame 16%nat ST.
  (* addi sp, sp, -16; sd ra, 8(sp); li a3, 18; bltu a1, a3, 0x80f40 *)
  step. step. step. step. if_cases HL.
  { zc HL. do 4 step. fin. }
  zc HL.
  assert (HL' : 18 <= bv_unsigned a1) by lia.
  specialize (RGOT HL'). specialize (RCELL HL'). specialize (RBUF HL'). specialize (RSH HL').
  (* the shadow byte of each byte read is a one-byte window of the shadow range of [f, f + 18) *)
  pose proof (fwd_shadow_byte_rng RNG (bv_unsigned a0) 18 0 ltac:(lia) RSH) as RS0.
  pose proof (fwd_shadow_byte_rng RNG (bv_unsigned a0) 18 12 ltac:(lia) RSH) as RS12.
  pose proof (fwd_shadow_byte_rng RNG (bv_unsigned a0) 18 13 ltac:(lia) RSH) as RS13.
  pose proof (fwd_shadow_byte_rng RNG (bv_unsigned a0) 18 16 ltac:(lia) RSH) as RS16.
  pose proof (fwd_shadow_byte_rng RNG (bv_unsigned a0) 18 17 ltac:(lia) RSH) as RS17.
  rewrite Z.add_0_r in RS0. clear RSH.
  pose proof (rng_sub' _ _ _ (bv_unsigned a0) 1 RBUF ltac:(lia)) as RW0.
  destruct (HB HL') as (LEN & BA & D0 & APS1 & APS2 & CELLS & DG & DS & ADR).
  clear HB.
  destruct CELLS as (CK & GCK & _).
  destruct ADR as (P0 & N0 & PE & AB).
  destruct (AB 0 ltac:(lia)) as (APP0 & k0 & MK0 & SK0).
  destruct (AB 12 ltac:(lia)) as (APP12 & k12 & MK12 & SK12).
  destruct (AB 13 ltac:(lia)) as (APP13 & k13 & MK13 & SK13).
  destruct (AB 16 ltac:(lia)) as (APP16 & k16 & MK16 & SK16).
  destruct (AB 17 ltac:(lia)) as (APP17 & k17 & MK17 & SK17).
  clear AB.
  rewrite Z.add_0_r in APP0, MK0, SK0.
  unfold off_stk in D0, DG, DS.
  unfold APPMEM_END in PE.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  (* the shadow bytes, read in the memory after the ra save *)
  pose proof (fwd_sh_tp m m0 _ _ _ MU1 APS1 APS2 APP0 MK0) as M0.
  pose proof (fwd_sh_tp m m0 _ _ _ MU1 APS1 APS2 APP12 MK12) as M12.
  pose proof (fwd_sh_tp m m0 _ _ _ MU1 APS1 APS2 APP13 MK13) as M13.
  pose proof (fwd_sh_tp m m0 _ _ _ MU1 APS1 APS2 APP16 MK16) as M16.
  pose proof (fwd_sh_tp m m0 _ _ _ MU1 APS1 APS2 APP17 MK17) as M17.
  clear MK0 MK12 MK13 MK16 MK17 APP0 APP12 APP13 APP16 APP17 APS1 APS2.
  (* the five bytes of f it reads, in the memory after the ra save *)
  pose proof (fwd_byte_tp m m0 _ _ bs 0 MU1 BA ltac:(lia) ltac:(lia) P0 ltac:(lia) D0) as F0.
  pose proof (fwd_byte_tp m m0 _ _ bs 12 MU1 BA ltac:(lia) ltac:(lia) P0 ltac:(lia) D0) as F12.
  pose proof (fwd_byte_tp m m0 _ _ bs 13 MU1 BA ltac:(lia) ltac:(lia) P0 ltac:(lia) D0) as F13.
  pose proof (fwd_byte_tp m m0 _ _ bs 16 MU1 BA ltac:(lia) ltac:(lia) P0 ltac:(lia) D0) as F16.
  pose proof (fwd_byte_tp m m0 _ _ bs 17 MU1 BA ltac:(lia) ltac:(lia) P0 ltac:(lia) D0) as F17.
  change (Z.of_nat 0) with 0 in F0. rewrite Z.add_0_r in F0.
  change (Z.of_nat 12) with 12 in F12. change (Z.of_nat 13) with 13 in F13.
  change (Z.of_nat 16) with 16 in F16. change (Z.of_nat 17) with 17 in F17.
  remember (nth 0 bs (Z_to_bv 8 0)) as b0 eqn:E0.
  remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
  remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
  remember (nth 16 bs (Z_to_bv 8 0)) as b16 eqn:E16.
  remember (nth 17 bs (Z_to_bv 8 0)) as b17 eqn:E17.
  (* the GOT word GOT_CELL_K and the shadow base CELL_K, read in the memory after the ra save *)
  unfold GOT_CELL_K, CELL_K in DG, DS, CK, GCK, RGOT, RCELL. unfold ASAN_K in CK.
  pose proof (bytes_tp m m0 _ _ 624616 (le8 (wa 657272)) MU1 ltac:(rewrite length_le8; lia) GCK) as GOT0.
  pose proof (bytes_tp m m0 _ _ 657272 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as SV0.
  assert (RDG : ov_read_bytes rsegs m0 (wa 624616) 8 = Some (le8 (wa 657272))).
  { replace (wa 624616) with (wa (624616 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 624616 _ 0 8 GOT0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RDS : ov_read_bytes rsegs m0 (wa 657272) 8 = Some (le8 (wa 2147450880))).
  { replace (wa 657272) with (wa (657272 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 657272 _ 0 8 SV0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  clear GOT0 SV0 CK GCK D0 DG DS.
  unfold shadow_addr, ASAN_K in M0, M12, M13, M16, M17, RS0, RS12, RS13, RS16, RS17.
  unfold shadow_ok in SK0, SK12, SK13, SK16, SK17.
  (* auipc a1, 0x18; ld a1, -1772(a1) = GOT_CELL_K; ld a3, 0(a1) = CELL_K *)
  step. step. step.
  clear RDG RDS.
  (* 0x80ee0: f[12]: addi a1, a0, 12; srli a4, a1, 3; add a4, a4, a3; lb a4, 0(a4); bnez a4, 0x80f98 *)
  step. gen_addi a0 w12 U12.
  pose proof (rng_sub' _ _ _ (bv_unsigned w12) 1 RBUF ltac:(lia)) as RW12.
  step. gen_shr w12 g12 G12. rewrite U12 in G12.
  step. gen_addi g12 h12 Hh12.
  pose proof (rng_sub' _ _ _ (bv_unsigned h12) 1 RS12 ltac:(lia)) as RH12.
  pose proof (rdw0 _ h12 _ _ M12 ltac:(lia)) as R. step. clear R.
  step.
  shck SK12 k12 (bv_unsigned a0 + 12) ltac:(rewrite U12).
  (* 2 goals: lbu a1, 0(a1); li a4, 136; bne a1, a4, 0x80f40 *)
  all: pose proof (rdw0 _ w12 _ _ F12 ltac:(lia)) as R; step; clear R.
  all: step; step; if_cases HC12; zc HC12.
  (* 4 goals; the odd ones are f[12] <> 0x88: RP_FWD_DROP at 0x80f40 *)
  1,3: do 4 step; fin.
  (* 0x80f00: f[13]: addi a1, a0, 13; srli a4, a1, 3; add a4, a4, a3; lb a4, 0(a4); bnez a4, 0x80fa8 *)
  all: step; gen_addi a0 w13 U13.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned w13) 1 RBUF ltac:(lia)) as RW13.
  all: step; gen_shr w13 g13 G13; rewrite U13 in G13.
  all: step; gen_addi g13 h13 Hh13.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned h13) 1 RS13 ltac:(lia)) as RH13.
  all: pose proof (rdw0 _ h13 _ _ M13 ltac:(lia)) as R; step; clear R.
  all: step.
  all: shck SK13 k13 (bv_unsigned a0 + 13) ltac:(rewrite U13).
  (* 4 goals: lbu a1, 0(a1); li a4, 25; bne a1, a4, 0x80f40 *)
  all: pose proof (rdw0 _ w13 _ _ F13 ltac:(lia)) as R; step; clear R.
  all: step; step; if_cases HC13; zc HC13.
  (* 8 goals; the odd ones are f[13] <> 0x19: RP_FWD_DROP at 0x80f40 *)
  1,3,5,7: do 4 step; fin.
  (* 0x80f20: beqz a2, 0x80f50 *)
  all: step; if_cases HZ; zc HZ.
  (* 8 goals; odd: bcast_only = 0, at 0x80f50. even: 0x80f24, f[0]: srli a1, a0, 3; add a1, a1, a3;
     lb a1, 0(a1); bnez a1, 0x80fb8; lbu a1, 0(a0); li a2, 255; beq a1, a2, 0x80f50 *)
  2,4,6,8: (step; gen_shr a0 g0 G0;
            step; gen_addi g0 h0 Hh0;
            pose proof (rng_sub' _ _ _ (bv_unsigned h0) 1 RS0 ltac:(lia)) as RH0;
            pose proof (rdw0 _ h0 _ _ M0 ltac:(lia)) as R; step; clear R;
            step;
            shck SK0 k0 (bv_unsigned a0) ltac:(idtac);
            (pose proof (rdw0 _ a0 _ _ F0 ltac:(lia)) as R; step; clear R;
             step; step; if_cases HC0; zc HC0;
             [ idtac | do 4 step; fin ])).
  (* 12 goals, all at 0x80f50: f[16]: addi a1, a0, 16; srli a2, a1, 3; add a2, a2, a3; lb a2, 0(a2);
     bnez a2, 0x80fc4 *)
  all: step; gen_addi a0 w16 U16.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned w16) 1 RBUF ltac:(lia)) as RW16.
  all: step; gen_shr w16 g16 G16; rewrite U16 in G16.
  all: step; gen_addi g16 h16 Hh16.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned h16) 1 RS16 ltac:(lia)) as RH16.
  all: pose proof (rdw0 _ h16 _ _ M16 ltac:(lia)) as R; step; clear R.
  all: step.
  all: shck SK16 k16 (bv_unsigned a0 + 16) ltac:(rewrite U16).
  (* 24 goals: lbu a1, 0(a1); bnez a1, 0x80f88 (RP_FWD_CTRL), else 0x80f6c: f[17] *)
  all: pose proof (rdw0 _ w16 _ _ F16 ltac:(lia)) as R; step; clear R.
  all: (step; if_cases HC16; zc HC16;
        [ do 5 step; fin
        | step; gen_addi a0 w17 U17;
          pose proof (rng_sub' _ _ _ (bv_unsigned w17) 1 RBUF ltac:(lia)) as RW17;
          step; gen_shr w17 g17 G17; rewrite U17 in G17;
          step; gen_addi g17 h17 Hh17;
          pose proof (rng_sub' _ _ _ (bv_unsigned h17) 1 RS17 ltac:(lia)) as RH17;
          (pose proof (rdw0 _ h17 _ _ M17 ltac:(lia)) as R; step; clear R);
          step;
          shck SK17 k17 (bv_unsigned a0 + 17) ltac:(rewrite U17);
          (pose proof (rdw0 _ w17 _ _ F17 ltac:(lia)) as R; step; clear R;
           step; if_cases HC17; zc HC17; do 5 step; fin) ]).
Qed.
