(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* The walk of check_events_step (fuzz/fuzz_decode.c:152-185) on fuzz_decode.ubsan, at 0x137a8 (44 instructions
   walked, 0x137a8-0x13854; no call and no frame on the paths that return, sp never moves), against
   lib/U/Prog/check_events_step_c.v. Three paths end at the `ret` at 0x13854: rd <> 1 (7 instructions), a
   message whose status is not F0 (32 instructions), and an F0 message (44 instructions).
   The model's equalities are substituted first: rd = code into a2, and for rd = 1 the fields of msg_agrees and
   the event kind into the event's cells, so each test that branches to the abort compares a register with
   itself.
   Abort site: the `jal abort` at 0x13860, reached through 0x13858. The ten `bne` to 0x13858 are not taken
   by check_events_step_ok = true:
   - 0x137b4 (rd against ow's code; lw sign-extends, and the code is a C int);
   - 0x137d0, 0x137dc (msg.offset, msg.len), 0x137e8, 0x137f4, 0x13800, 0x1380c (status, running, d1, d2);
   - 0x13838, 0x13844 (for F0: msg.sysex against b + sysex_at, msg.sysex_len);
   - 0x13850 (ev->kind against ow's event kind).
   UBSan traps, each a branch to the unimp at 0x13864:
   - 0x137a8 `andi a4, a1, 7` / 0x137ac `bnez a4` (o misaligned) is not taken by the premise o mod 8 = 0;
   - 0x137c0 `andi a2, a3, 7` / 0x137c4 `bnez a2` (e misaligned, reached when rd = 1) is not taken by the
     premise e mod 8 = 0;
   - for an F0 message, 0x13820 `bltu a2, a0` (b + sysex_at wraps) and 0x13824-0x13830 `snez` / `seqz` /
     `xor` / `beqz` (b is NULL exactly when the sum is not) are not taken by the premise 0 < b,
     0 <= sysex_at and b + sysex_at < 2^64.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnDecHarness.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import DgnChkLib.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import DgnLayout check_events_step_c.
Import ListNotations.
Open Scope Z_scope.

(* andi x, 7: the low three bits are the residue mod 8 *)
Lemma land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(* snez of a pointer that is not NULL *)
Lemma snez_pos : forall z, 0 < z < 2^64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 z) = Z_to_bv 64 1.
Proof.
  intros z Hz. rewrite v_sltu_b2z. rewrite (unsigned_lit z) by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  destruct (Z.ltb_spec 0 z); [reflexivity | lia].
Qed.

(* seqz of a pointer that is not NULL *)
Lemma seqz_pos : forall z, 0 < z < 2^64 -> v_sltiu (Z_to_bv 64 z) 1 = Z_to_bv 64 0.
Proof.
  intros z Hz. rewrite v_sltiu_b2z. rewrite (unsigned_lit z) by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec z 1); [lia | reflexivity].
Qed.

(* a bne of a register with itself *)
Local Ltac same := step; rewrite ?eqb_same; cbv beta iota delta [negb].

(* the `ret` at 0x13854 and the postcondition: nothing below sp was written *)
Local Ltac fin MI ST :=
  step;
  apply evt_done; do 16 eexists; split; [reflexivity|];
  split; [apply munch_refl|]; split; [apply wmono_refl|]; split; [exact MI | exact ST].

Theorem check_events_step_holds : check_events_step_contract.
Proof.
  unfold check_events_step_contract, CHECK_EVENTS_STEP, CHECK_EVENTS_STEP_FRAME, OW_SIZE, DE_SIZE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    b o e rd lo ow ev p1 p2 mpad OK RC RS SX0 OA EA SXR MO ME ST HLO DO DE MI.
  destruct ow as [[code at_ mlen next st run d1 d2 sto sxa sxl] se lsbm nxt stout].
  destruct ev as [kind strip button zone on right addr lsbmiss value delta mask segm elen text seg dots device
                  [dst drun dd1 dd2 dsx dsxl doff dlen]].
  cbn [ow_m ow_e sm_code sm_status sm_sysex_at] in RC, RS, SX0, SXR.
  pose proof (ro_cells_bound _ _ _ _ MO) as BO. rewrite owed_cells_size in BO.
  pose proof (ro_cells_bound _ _ _ _ ME) as BE. rewrite event_cells_size in BE.
  unfold check_events_step_ok, msg_agrees in OK.
  cbn [ow_m ow_e de_msg de_kind sm_code sm_at sm_len sm_status sm_running sm_d1 sm_d2 sm_sysex_at sm_sysex_len
       dm_offset dm_len dm_status dm_running dm_d1 dm_d2 dm_sysex dm_sysex_len] in OK.
  apply andb_true_iff in OK. destruct OK as [E0 OK]. apply Z.eqb_eq in E0. subst rd.
  unfold owed_cells, spec_msg_cells, spec_event_cells, arr_cells in MO.
  cbn [map seq app ow_m ow_e ow_lsb_missing ow_next ow_status_out sm_code sm_at sm_len sm_next sm_status
       sm_running sm_d1 sm_d2 sm_status_out sm_sysex_at sm_sysex_len] in MO.
  unfold event_cells, dmsg_cells, arr_cells in ME.
  cbn [map seq app de_kind de_strip de_button de_zone de_on de_right de_addr de_lsb_missing de_value de_delta
       de_mask de_segments de_len de_text de_seg de_dots de_device de_msg dm_status dm_running dm_d1 dm_d2
       dm_sysex dm_sysex_len dm_offset dm_len] in ME.
  (* UBSan 0x137a8 / 0x137ac: o is 8-aligned *)
  step. rewrite (unsigned_lit o) by lia. rewrite land7_mod8, OA.
  step. if_false.
  (* 0x137b0 lw a4, 0(a1): ow's code; 0x137b4 bne a2, a4 to the abort: rd = code *)
  step. rewrite (sx32_int code) by lia.
  same.
  (* 0x137b8 / 0x137bc: rd <> 1 returns *)
  step. step. rewrite (eqb_int64 code 1) by lia.
  destruct (Z.eqb_spec code 1) as [C1|C1]; cbv beta iota delta [negb].
  2: fin MI ST.
  subst code. change (1 =? 1) with true in OK. cbn [implb] in OK.
  rewrite !andb_true_iff in OK.
  destruct OK as [[[[[[[Eo El] Es] Er] E1] E2] EF] Ek].
  apply Z.eqb_eq in Eo, El, Es, Er, E1, E2, Ek.
  subst doff dlen dst drun dd1 dd2 kind.
  (* UBSan 0x137c0 / 0x137c4: e is 8-aligned *)
  step. rewrite (unsigned_lit e) by lia. rewrite land7_mod8, EA.
  step. if_false.
  (* the six compares of ev->msg with ow's message *)
  step. step. same.                                        (* 0x137d0 msg.offset *)
  step. step. same.                                        (* 0x137dc msg.len *)
  step. step. same.                                        (* 0x137e8 status *)
  step. step. same.                                        (* 0x137f4 running *)
  step. step. same.                                        (* 0x13800 d1 *)
  step. step. same.                                        (* 0x1380c d2 *)
  (* 0x13810 / 0x13814: the F0 test *)
  step. rewrite (zxb_b8 st) by lia. step. rewrite (eqb_int64 st 240) by lia.
  destruct (Z.eqb_spec st 240) as [F0|F0]; cbv beta iota delta [negb].
  - subst st. change (240 =? 240) with true in EF. cbn [implb] in EF.
    apply andb_true_iff in EF. destruct EF as [Ex Exl]. apply Z.eqb_eq in Ex, Exl. subst dsx dsxl.
    specialize (SX0 eq_refl). destruct (SXR eq_refl) as (B0 & S0 & BS).
    assert (SP : sysex_ptr b sxa = sxa + b).
    { unfold sysex_ptr. destruct (Z.eqb_spec sxa 0); [contradiction | lia]. }
    rewrite SP in ME.
    (* 0x13818 ld a2, 0x28(a1); 0x1381c add a2, a2, a0: b + sysex_at *)
    step. step.
    (* UBSan 0x13820 bltu a2, a0: the sum does not wrap *)
    step. unfold bv_ltu. rewrite (unsigned_lit (sxa + b)), (unsigned_lit b) by lia. if_false.
    (* UBSan 0x13824-0x13830: b is not NULL, the sum is not NULL *)
    step. rewrite (snez_pos b) by lia.
    step. rewrite (seqz_pos (sxa + b)) by lia.
    step. step. if_false.
    step. same.                                            (* 0x13838 msg.sysex *)
    step. step. same.                                      (* 0x13844 msg.sysex_len *)
    step. step. same.                                      (* 0x13850 kind *)
    fin MI ST.
  - step. step. same.                                      (* 0x13850 kind *)
    fin MI ST.
Qed.
