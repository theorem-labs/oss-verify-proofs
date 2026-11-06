(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths changed; 166 of its 215 lines of code are new or changed and 3804 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/joined_byte.v; 58 of its 188 lines of code are new or changed and 85 lines of the source are left out. *)
(* The footprint twin of joined_byte, image B (asan-ubsan v1.9.0, entry 0x836ac): joined_byte_holds_F proves
   joined_byte_contract_F (lib/B/Prog/joined_byte_c.v), the same run as an ExecF.evtF under a footprint RNG, by the
   script of the plain proof joined_byte.v (joined_byte_holds; a working branch 3803efccea0, blob 8bf3e6b3d841)
   over StepF's step (route 2). Each access of the run is closed from one rng premise: the store and reload of ra
   (the frame), the two 8-byte loads of the GOT cell and the runtime cell, the 1-byte loads of nb and b, and the
   1-byte load of the shadow byte of each. The plain proof file is not on this branch, so its lemmas are restated
   here under the jbF_ prefix. joined_byte_holds_of_F re-derives the old contract from the footprint form
   (joined_byte_contract_of_F at RNG_all). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcLib RcRecLib RcLeafLib RcAsan RcAsanLib RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT joined_byte_c.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* A shadow address is [x / 8 + ASAN_K]: its access side goal needs the Euclidean equations of the division, which
   StepF's [alia] does not add, so the shadow loads go through StepF's acc_hint hook (the form of
   lib/B/Prog/reac_ports_parseF.v). *)
Ltac has_div E := lazymatch E with context [Z.div _ _] => idtac end.

Ltac solve_acc_div_with H E :=
  lazymatch goal with
  | |- acc_in ?RNG (_, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with
      | rng _ ?lo ?len =>
          apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true));
          split; try unfold ASAN_K in *; Z.div_mod_to_equations; lia
      end
  end.

Ltac acc_hintF :=
  lazymatch goal with
  | |- acc_in ?RNG (?a, _) =>
      let E := addr_expr a in
      has_div E;
      match goal with
      | H : rng RNG ?lo _ |- _ => has_div lo; solve_acc_div_with H E
      end
  end.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= acc_hintF.

(* T2: `not a1,a0` then `bltu a1,a2`: ~(p + 5) < i is false when p + 5 + i < 2^64 (jb_not of joined_byte.v). *)
Lemma jbF_not : forall x y, 0 <= x -> 0 <= y -> x + y < 2^64 ->
  bv_ltu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) 18446744073709551615)) (Z_to_bv 64 y) = false.
Proof.
  intros x y Hx Hy Hxy. rewrite (unsigned_lit x) by lia. rewrite lnot_mod64 by lia.
  assert (E : Z.lnot x mod 2^64 = 2^64 - 1 - x)
    by (rewrite Z.lnot_eq_pred_opp; symmetry; apply Z.mod_unique_pos with (q := -1); lia).
  rewrite E. unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia.
Qed.

(* subw, addiw: a 32-bit result in [0, 2^31) sign-extends to itself. *)
Lemma jbF_swrap : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

Lemma jbF_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. pose proof (byte_range b). unfold zxb. apply unsigned_lit. lia. Qed.

Lemma jbF_rd : forall segs m A (b : byte) A', bytes_at segs m A [b] -> A' = A ->
  ov_read_bytes segs m (wa A') 1 = Some [b].
Proof.
  intros segs m A b A' H ->. rewrite <- (Z.add_0_r A). exact (rcl_rd segs m A [b] 0 b H eq_refl).
Qed.

(* addressable survives writes apart from the shadow bytes of its range. *)
Lemma jbF_addr_munch : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall x, in_shadow x -> outside W x) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) Hm HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (rt_app_shadow (p + i) Hap) as Hs. pose proof (rt_shadow_bound _ Hs) as Hbd.
  unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. apply HW, Hs.
Qed.

(* The instrumented check of the 1-byte load at X (X addressable): the shadow byte k at X / 8 + ASAN_K is readable
   and passes (k = 0, or X mod 8 < k). *)
Lemma jbF_shadow : forall mc X, addressable mc X 1 ->
  exists k : byte, ov_read_bytes rsegs mc (wa (X / 8 + ASAN_K)) 1 = Some [k]
                   /\ (bv_signed k = 0 \/ X mod 8 < bv_signed k) /\ -128 <= bv_signed k < 128.
Proof.
  intros mc X HA.
  pose proof (rt_shadow_rd mc X 1 [] HA (fun _ _ => I)) as HSR.
  pose proof (rt_addressable mc X 1 HA) as HAD.
  destruct (asan_shadow_read rsegs mc ASAN_K X 1 [] 0 HSR ltac:(lia)) as (k & RK & BK).
  pose proof (Z.mod_pos_bound (X + 0) 8 ltac:(lia)) as MB.
  pose proof (asan_check_lt rsegs mc ASAN_K X 1 0 1 k HAD ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) BK) as OK.
  rewrite Z.add_0_r in RK, OK.
  exists k. split; [exact RK|]. split; [lia | apply rc_byte_signed].
Qed.

Lemma jbF_app : forall m p n, addressable m p n -> 0 <= p /\ p + n <= 2^47.
Proof. intros m p n H. pose proof (rt_addressable_bound m p n H). lia. Qed.

Ltac jb_cond := unfold bv_eqb, bv_ltu, bv_lts, bv_leu, zxb; cbn [negb]; fold_lit_ux;
  repeat (rewrite unsigned_lit by lia); solve_cond_rec.

Ltac jb_if v :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with v; [cbv iota | symmetry; jb_cond]
  end.

(* The instrumented check of a load, as chk_core of joined_byte.v over evtF goals: SH gives the shadow byte k of the
   load at X, its read at X / 8 + ASAN_K and the check fact (k = 0, or X mod 8 < k); `pre` steps to the shadow
   address (srli; add), then the load of k and `bnez` go on when k = 0; else the slow path `andi r, X, 7` and
   `blt r, k` go on as the check passes. The register r is generalized at the join, and the call of
   __asan_report_load1 is not reached. *)
Ltac steps_until_if :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; steps_until_if
  | _ => idtac
  end.

Ltac bjoin G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.

Ltac chk_core X RX r SH pre :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
  destruct SH as (k & RK & OK & KR);
  pre X RX; steps_until_if; clear RK;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (clear -KR; lia);
  lazymatch goal with
  | |- evtF ?segs ?RN ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RN Q (MS (bvmap_set r rr R) F B fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin G r
        | step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_land7;
          step;
          let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
          rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (clear -MB KR; lia);
          replace (X mod 8 <? bv_signed k) with true
            by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia]);
          clear MB; bjoin G r ]
      | intros ?; simp_regs; clear OK KR ]
  end.

Ltac pre_sr X RX := step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_shr3.

(* 0x8371c .. 0x83738: the check of the load at X (a0 = X), the load of b (`lbu a0,0(a0)`), the reload of ra, the
   release of the frame and `ret`. *)
Ltac jb_tail X RX SH RDb m m1 MU WM WVS ST FR S :=
  chk_core X RX (Z_to_bv 5 12) SH pre_sr;
  step; clear RDb; step; step; step;
  release_frame FR ST (bv_unsigned S);
  apply evtF_done; cbv beta; do 7 eexists; split; [reflexivity|];
  split; [exact MU|]; split; [exact WM|];
  split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WVS)|];
  exact ST.

(* The walk of joined_byte.v: 0x836ac `addi sp,sp,-16`, `sd ra,8(sp)`; T1; the shadow offset read through the GOT
   cell at 0xa08f0 (`auipc a3,0x1d` at 0x836bc, `ld a3,0x234(a3)`) and the cell it names (GOT_CELL_K = 0xa08f0,
   CELL_K = 0xa96b8 of lib/B/AsanRT.v); the check of the load of nb at p + 4; `bgeu`; the body path (T2) or the
   last path (T3-T5); the check of the load at ja; `lbu a0`; `ld ra`; `ret`. *)
Theorem joined_byte_holds_F : joined_byte_contract_F.
Proof.
  unfold joined_byte_contract_F, JOINED_BYTE, JOINED_BYTE_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    i nb b Hi Ha2 Hal HN Hq HB ST HLO DN DB HCE HSW HAN HAB HW RFR RGOT RCELL RN RB RSN RSB.
  subst a2.
  unfold GOT_CELL_K, CELL_K in RGOT, RCELL. unfold shadow_addr in RSN, RSB.
  assert (Ri : 9 <= i <= 10) by lia.
  pose proof (zr_word a0) as R0. pose proof (zr_word a1) as R1. unfold inr64 in R0, R1.
  pose proof (byte_range nb) as Bn.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  assert (HWs : forall x, in_shadow x -> outside [(bv_unsigned sp - 16, bv_unsigned sp)] x)
    by (intros x Hx; apply HW; right; right; exact Hx).
  pose proof (rt_asan_rt m _ HCE HW) as HRT.
  pose proof (jbF_app m _ _ HAN) as AN. pose proof (jbF_app m _ _ HAB) as AB.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (WVS : forall x, bv_unsigned sp - 16 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; apply (rc_wv_stk rsegs m lo (bv_unsigned sp)); [exact ST | lia]).
  clear HCE HSW HW.
  carve_frame 16%nat ST.
  step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (asan_rt_munch rsegs m m1 _ _ ASAN_K _ _ HRT MU (fun x Hx => Hx)) as HRT1.
  pose proof (asan_rt_got_read rsegs m1 _ _ ASAN_K _ HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs m1 _ _ ASAN_K _ HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  pose proof (jbF_addr_munch _ m m1 _ _ HAN MU HWs) as HAN1.
  pose proof (jbF_addr_munch _ m m1 _ _ HAB MU HWs) as HAB1.
  clear HRT HRT1 HAN HAB.
  (* +0x08 andi, +0x0c bnez: T1 (p mod 4 = 0) *)
  step. rewrite rcl_land3, Hal.
  step. jb_if false.
  (* +0x10 auipc, +0x14 ld (the GOT cell), +0x18 ld (the shadow offset) *)
  step. step. step.
  (* +0x1c addi a3 = p + 4; +0x20 .. +0x2c and 0x83740 .. 0x83744: the check of the load of nb *)
  pose proof (jbF_shadow m1 _ HAN1) as SH1.
  assert (RX1 : 0 <= bv_unsigned a0 + 4 < 2^64) by lia.
  step.
  chk_core (bv_unsigned a0 + 4) RX1 (Z_to_bv 5 16) SH1 pre_sr.
  (* +0x30 lbu a3 = nb; +0x34 bgeu a2,a3 *)
  pose proof (jbF_rd rsegs m1 (bv_unsigned a0 + 4) nb (bv_unsigned a0 + 4) HN eq_refl) as RDn.
  step. clear RDn RN RSN.
  step.
  destruct (Z.ltb_spec i (bv_unsigned nb)) as [E | E].
  - (* body path: i < nb *)
    assert (EJ : jb_addr (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned nb) i = bv_unsigned a0 + 5 + i)
      by (unfold jb_addr; rewrite (proj2 (Z.ltb_lt _ _) E); reflexivity).
    rewrite EJ in HB, HAB1, AB, RB, RSB. clear EJ DB.
    jb_if false.
    (* +0x38 addi a0 = p + 5; +0x3c not a1; +0x40 bltu a1,a2: T2 *)
    step. step.
    step. rewrite (jbF_not (bv_unsigned a0 + 5) i) by lia. cbv iota.
    (* +0x44 add a0 = p + 5 + i; +0x48 j 0x8371c *)
    step. step.
    pose proof (jbF_shadow m1 _ HAB1) as SH2.
    assert (RX2 : 0 <= bv_unsigned a0 + 5 + i < 2^64) by lia.
    pose proof (jbF_rd rsegs m1 (bv_unsigned a0 + 5 + i) b (bv_unsigned a0 + 5 + i) HB eq_refl) as RDb.
    jb_tail (bv_unsigned a0 + 5 + i) RX2 SH2 RDb m m1 MU WM WVS ST FR sp.
  - (* last path: nb <= i *)
    pose proof (Hq E) as Hq0.
    assert (EJ : jb_addr (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned nb) i
                 = i - bv_unsigned nb + 9 + bv_unsigned a1)
      by (unfold jb_addr; rewrite (proj2 (Z.ltb_ge _ _) E); lia).
    rewrite EJ in HB, HAB1, AB, RB, RSB. clear EJ DB.
    jb_if true.
    (* +0x4c subw a2 = i - nb; +0x50 addiw a0 = 9 + i - nb *)
    step. rewrite (unsigned_lit i) by lia. rewrite jbF_zxb. rewrite (jbF_swrap (i - bv_unsigned nb)) by lia.
    step. rewrite (unsigned_lit (i - bv_unsigned nb)) by lia. rewrite (jbF_swrap (i - bv_unsigned nb + 9)) by lia.
    (* +0x54 add a0 = t = q + (9 + i - nb); +0x58 bltu t,q: T3 *)
    step.
    step. jb_if false.
    (* +0x5c snez, +0x60 seqz, +0x64 xor, +0x68 beqz: T4 *)
    step. step. step.
    step. rewrite rc_ubchk by (try rewrite unsigned_lit by lia; lia). cbv iota.
    (* +0x6c beqz a1: T5 *)
    step. rewrite (rc_neq0w a1) by lia. cbv iota.
    pose proof (jbF_shadow m1 _ HAB1) as SH2.
    assert (RX2 : 0 <= i - bv_unsigned nb + 9 + bv_unsigned a1 < 2^64) by lia.
    pose proof (jbF_rd rsegs m1 _ b _ HB eq_refl) as RDb.
    jb_tail (i - bv_unsigned nb + 9 + bv_unsigned a1) RX2 SH2 RDb m m1 MU WM WVS ST FR sp.
Qed.

(* The old contract as a corollary of the footprint form (joined_byte_contract_of_F, RNG_all). *)
Theorem joined_byte_holds_of_F : joined_byte_contract.
Proof. exact (joined_byte_contract_of_F joined_byte_holds_F). Qed.
