(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* The footprint walk of reac-repacer/fuzz_wire's is_tagged_reac in image B, against the frozen
   lib/B/Prog/is_tagged_reac_F_c.v is_tagged_reac_contract_F (= lib/B/Prog/is_tagged_reac_cg.v
   wire_is_tagged_reac_holds_stmt). The script is this unit's lib/B/Prog/rp_ret_accept_FW.v, itself
   libreac/fuzz_decode's released lib/B/Prog/reac_frame_is_reac_F_nosh.v (recipes commit 98c99a85e4): StepF's step, one
   rng fact per access, each shadow byte read from the `addressable` premise, the bytes of f and the two cells carried
   over the frame store by the munch fact of the frame. is_tagged_reac has no early exit before its loads: it checks
   f == NULL and the wrap of f + 12 (UBSan) and then reads four bytes, f[12], f[13], f[16], f[17], each after the
   check of its shadow byte and each but the first after the UBSan check of its own wrap. So the premises have no
   guard, the walk steps over the five UBSan checks with `if_false`, and it splits only on the three byte tests that
   return 0. Each of the four shadow checks has two paths that meet again at the byte load (they differ only in the
   register the slow path writes); the lemmas ck_<pc> below join them, in the form of reac-repacer/fuzz_uci's released
   lib/B/Prog/rp_hot_clamp_FW.v ck_<pc> (recipes commit 0295462466b2) for a one-byte access, so the walk is one path
   per byte test. The GOT word and the cell are image B's (624760 = 0x98878 and 657400 = 0xa07f8). *)
(* is_tagged_reac of fuzz_wire.asan-ubsan (the listing of image B; entry 0x8103c, 0x108 bytes):
     0x8103c `addi sp, sp, -0x10`, 0x81040 `sd ra, 8(sp)`;
     0x81044 `beqz a0, 0x81104`, 0x81048 `addi a1, zero, -0xc`, 0x8104c `bgeu a0, a1, 0x81104` (UBSan; `unimp` at
     0x81104): a0 <> 0 and f + 18 <= APPMEM_END make both fall through;
     0x81050 `auipc a1, 0x18`, 0x81054 `ld a1, -0x7d8(a1)` (the GOT word 0x98878), 0x81058 `ld a2, 0(a1)` (the shadow
     base in 0xa07f8);
     0x8105c .. 0x8106c: a1 = f + 12, its shadow byte k12 in a3, `bnez a3, 0x81108`; the check 0x81108 `andi a4, a1, 7`
     / 0x8110c `blt a4, a3, 0x81070` goes back because (f + 12) mod 8 < k12 when k12 <> 0 (`addressable`), so the
     error path (`jal 0x57e5c` at 0x81114) is not reached;
     0x81070 `lbu a1, 0(a1)` (f[12]), 0x81074 `addi a3, zero, 0x81`, 0x81078 `bne a1, a3, 0x810f4` (f[12] <> 0x81: 0);
     0x8107c `addi a1, zero, -0xe`, 0x81080 `bltu a1, a0, 0x81104` (UBSan): falls through as above;
     0x81084 .. 0x81094: a1 = f + 13, its shadow byte k13 in a3, `bnez a3, 0x81118`; the check 0x81118 / 0x8111c goes
     back to 0x81098 likewise, the error path at 0x81124 is not reached;
     0x81098 `lbu a1, 0(a1)` (f[13]), 0x8109c `bnez a1, 0x810f4` (f[13] <> 0: 0);
     0x810a0 `addi a1, zero, -0x11`, 0x810a4 `bltu a1, a0, 0x81104` (UBSan): falls through;
     0x810a8 .. 0x810b8: a1 = f + 16, its shadow byte k16 in a3, `bnez a3, 0x81128`; the check 0x81128 / 0x8112c goes
     back to 0x810bc, the error path at 0x81134 is not reached;
     0x810bc `lbu a1, 0(a1)` (f[16]), 0x810c0 `addi a3, zero, 0x88`, 0x810c4 `bne a1, a3, 0x810f4` (f[16] <> 0x88: 0);
     0x810c8 `addi a1, zero, -0x12`, 0x810cc `bltu a1, a0, 0x81104` (UBSan): falls through;
     0x810d0 .. 0x810e0: a0 = f + 17, its shadow byte k17 in a1, `bnez a1, 0x81138`; the check 0x81138
     `andi a2, a0, 7` / 0x8113c `blt a2, a1, 0x810e4` goes back, the error path at 0x81140 is not reached;
     0x810e4 `lbu a0, 0(a0)` (f[17]), 0x810e8 `addi a0, a0, -0x19`, 0x810ec `seqz a0, a0`, 0x810f0 `j 0x810f8`;
     0x810f4 `mv a0, zero`; 0x810f8 `ld ra, 8(sp)`, 0x810fc `addi sp, sp, 0x10`, 0x81100 `ret`. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA AsanKAProof is_tagged_reac_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_copy_untag_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require is_tagged_reac_cg.
Import ListNotations.
Open Scope Z_scope.
Module PCU := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_copy_untag_c.

(* the shadow check of a one-byte access at X passes on shadow byte k (AsanCells.v shadow_ok without its k <= 7) *)
Definition shok1 (k : byte) (X : Z) : Prop := bv_signed k = 0 \/ X mod 8 < bv_signed k.

(* the shadow check from its `bnez` back to the access: on k = 0 the `bnez` falls through; else the check `andi`
   (X mod 8) / `blt` goes back *)
Local Ltac chk1 HX C K :=
  unfold shok1 in C;
  lazymatch type of C with bv_signed ?k = 0 \/ _ =>
  lazymatch type of HX with bv_unsigned _ = ?X =>
    let MB := fresh "MB" in
    pose proof (Z.mod_pos_bound X 8 ltac:(lia)) as MB;
    step; rewrite sxb_eq0; destruct C as [C|C];
    [ rewrite (proj2 (Z.eqb_eq _ _) C); cbn [negb]; apply K
    | rewrite (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb];
      step; step;
      rewrite land7, HX, (lts_low (X mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb]; apply K ]
  end end.

Section Walk.
Variables (RNG : footprint) (Q : machine_state -> Prop)
  (ra sp1 gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32).

(* the states of the walk: sp1 is the frame's sp; r0 .. r4 are a0 .. a4, the registers the function writes *)
Local Abbreviation SW pc m r0 r1 r2 r3 r4 :=
  (MS (mkR ra sp1 gp tp t0 t1 t2 s0 s1 r0 r1 r2 r3 r4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* 0x8106c: `bnez a3` on the shadow byte of the load of f[12] at a1; its check (`andi a4, a1, 7`; `blt a4, a3`)
   goes back to 0x81070: the error path (`jal` at 0x81114) is not reached. *)
Lemma ck_8106c : forall m (r0 r1 r2 r4 : word) (k : byte) X,
  bv_unsigned r1 = X -> shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (SW 0x81070 m r0 r1 r2 (sxb k) v)) ->
  evtF rsegs RNG Q (SW 0x8106c m r0 r1 r2 (sxb k) r4).
Proof. intros m r0 r1 r2 r4 k X HX C K. chk1 HX C K. Qed.

(* 0x81094: `bnez a3` on the shadow byte of the load of f[13] at a1; its check (`andi a4, a1, 7`; `blt a4, a3`)
   goes back to 0x81098: the error path (`jal` at 0x81124) is not reached. *)
Lemma ck_81094 : forall m (r0 r1 r2 r4 : word) (k : byte) X,
  bv_unsigned r1 = X -> shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (SW 0x81098 m r0 r1 r2 (sxb k) v)) ->
  evtF rsegs RNG Q (SW 0x81094 m r0 r1 r2 (sxb k) r4).
Proof. intros m r0 r1 r2 r4 k X HX C K. chk1 HX C K. Qed.

(* 0x810b8: `bnez a3` on the shadow byte of the load of f[16] at a1; its check (`andi a4, a1, 7`; `blt a4, a3`)
   goes back to 0x810bc: the error path (`jal` at 0x81134) is not reached. *)
Lemma ck_810b8 : forall m (r0 r1 r2 r4 : word) (k : byte) X,
  bv_unsigned r1 = X -> shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (SW 0x810bc m r0 r1 r2 (sxb k) v)) ->
  evtF rsegs RNG Q (SW 0x810b8 m r0 r1 r2 (sxb k) r4).
Proof. intros m r0 r1 r2 r4 k X HX C K. chk1 HX C K. Qed.

(* 0x810e0: `bnez a1` on the shadow byte of the load of f[17] at a0; its check (`andi a2, a0, 7`; `blt a2, a1`)
   goes back to 0x810e4: the error path (`jal` at 0x81140) is not reached. *)
Lemma ck_810e0 : forall m (r0 r2 r3 r4 : word) (k : byte) X,
  bv_unsigned r0 = X -> shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (SW 0x810e4 m r0 (sxb k) v r3 r4)) ->
  evtF rsegs RNG Q (SW 0x810e0 m r0 (sxb k) r2 r3 r4).
Proof. intros m r0 r2 r3 r4 k X HX C K. chk1 HX C K. Qed.

End Walk.

(* apply a check lemma at its `bnez`: the access address is X, its address register holds X by U, the check passes
   by C; v names the register the check may write *)
Local Ltac ckapp L x U C v := eapply L with (X := x); [exact U | exact C | intros v].

Theorem is_tagged_reac_holds_F : is_tagged_reac_contract_F.
Proof.
  unfold is_tagged_reac_contract_F, IS_TAGGED_REAC, IS_TAGGED_REAC_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    HNZ HLEN HB ST HLO HOFF APS1 APS2 HAC HOG HOC HAD12 HAD16 RFR RGOT RCELL R12 R16 RS12 RS16.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  (* the four bytes the function reads, from bytes_at before the frame store (bs may reach past f + 18) *)
  pose proof (bytes_nth m _ bs 12 HB ltac:(lia)) as F12m.
  pose proof (bytes_nth m _ bs 13 HB ltac:(lia)) as F13m.
  pose proof (bytes_nth m _ bs 16 HB ltac:(lia)) as F16m.
  pose proof (bytes_nth m _ bs 17 HB ltac:(lia)) as F17m.
  change (Z.of_nat 12) with 12 in F12m. change (Z.of_nat 13) with 13 in F13m.
  change (Z.of_nat 16) with 16 in F16m. change (Z.of_nat 17) with 17 in F17m.
  clear HB.
  carve_frame 16%nat ST.
  (* addi sp, sp, -16; sd ra, 8(sp) *)
  step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  destruct HAC as (CK & GCK & _).
  destruct HAD12 as (P12 & _ & PE12 & AB12).
  destruct HAD16 as (P16 & _ & PE16 & AB16).
  destruct (AB12 0 ltac:(lia)) as (APP12 & k12 & MK12 & SK12).
  destruct (AB12 1 ltac:(lia)) as (APP13 & k13 & MK13 & SK13).
  destruct (AB16 0 ltac:(lia)) as (APP16 & k16 & MK16 & SK16).
  destruct (AB16 1 ltac:(lia)) as (APP17 & k17 & MK17 & SK17).
  clear AB12 AB16.
  unfold off_stk, GOT_CELL_K, CELL_K, shadow_addr, ASAN_K, shadow_ok in *.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP12, APP13, APP16, APP17, APS1, APS2.
  rewrite Z.add_0_r in APP12, MK12, SK12, APP16, MK16, SK16.
  replace (bv_unsigned a0 + 12 + 1) with (bv_unsigned a0 + 13) in APP13, MK13, SK13 by lia.
  replace (bv_unsigned a0 + 16 + 1) with (bv_unsigned a0 + 17) in APP17, MK17, SK17 by lia.
  assert (DV12 : (bv_unsigned a0 + 12) / 8 <= (bv_unsigned a0 + 13) / 8) by (apply Z.div_le_mono; lia).
  assert (DV16 : (bv_unsigned a0 + 16) / 8 <= (bv_unsigned a0 + 17) / 8) by (apply Z.div_le_mono; lia).
  (* the two cells, the four shadow bytes and the four bytes of f, carried over the frame store *)
  pose proof (bytes_tp m m0 _ _ 624760 (le8 (wa 657400)) MU1 ltac:(rewrite length_le8; lia) GCK) as GOT0.
  pose proof (bytes_tp m m0 _ _ 657400 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as SV0.
  assert (RDG : ov_read_bytes rsegs m0 (wa 624760) 8 = Some (le8 (wa 657400))).
  { replace (wa 624760) with (wa (624760 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 624760 _ 0 8 GOT0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RDS : ov_read_bytes rsegs m0 (wa 657400) 8 = Some (le8 (wa 2147450880))).
  { replace (wa 657400) with (wa (657400 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 657400 _ 0 8 SV0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 12) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK12) as M12.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 13) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK13) as M13.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 16) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK16) as M16.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 17) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK17) as M17.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + 12) _ MU1 ltac:(lia) ltac:(lia) F12m) as F12.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + 13) _ MU1 ltac:(lia) ltac:(lia) F13m) as F13.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + 16) _ MU1 ltac:(lia) ltac:(lia) F16m) as F16.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + 17) _ MU1 ltac:(lia) ltac:(lia) F17m) as F17.
  clear GOT0 SV0 CK GCK MK12 MK13 MK16 MK17 F12m F13m F16m F17m.
  remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
  remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
  remember (nth 16 bs (Z_to_bv 8 0)) as b16 eqn:E16.
  remember (nth 17 bs (Z_to_bv 8 0)) as b17 eqn:E17.
  assert (C12 : shok1 k12 (bv_unsigned a0 + 12)) by (unfold shok1; tauto).
  assert (C13 : shok1 k13 (bv_unsigned a0 + 13)) by (unfold shok1; tauto).
  assert (C16 : shok1 k16 (bv_unsigned a0 + 16)) by (unfold shok1; tauto).
  assert (C17 : shok1 k17 (bv_unsigned a0 + 17)) by (unfold shok1; tauto).
  clear SK12 SK13 SK16 SK17.
  (* the UBSan checks of f: `beqz a0` and `bgeu a0, a1` (a1 = -12) fall through *)
  step. if_false.
  step. step. if_false.
  (* the shadow base through its GOT word *)
  step. step. step.
  (* f + 12: its shadow byte and check, then f[12]; addi a3, zero, 0x81; bne a1, a3 *)
  step. gen_addi a0 w12 U12.
  assert (RW12 : ExecF.rng RNG (bv_unsigned w12) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ R12); lia).
  step. gen_shr w12 g12 G12. rewrite U12 in G12.
  step. gen_addi g12 h12 H12.
  assert (RH12 : ExecF.rng RNG (bv_unsigned h12) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS12); lia).
  pose proof (rdw0 m0 h12 _ _ M12 ltac:(lia)) as R. step. clear R.
  ckapp ck_8106c (bv_unsigned a0 + 12) U12 C12 v12.
  pose proof (rdw0 m0 w12 _ _ F12 ltac:(lia)) as R. step. clear R.
  step. step. if_cases HC12; zify_cond HC12; rewrite zxb_u in HC12.
  { (* f[12] <> 0x81: mv a0, zero; ld ra; addi sp; ret *)
    assert (W : is_tagged_result bs = 0)
      by (unfold is_tagged_result, PCU.cu_tagged, PCU.cu_byte; rewrite <- E12, (proj2 (Z.eqb_neq _ _) HC12);
          reflexivity).
    do 4 step. apply evtF_done. rewrite W. do 5 eexists. split; [reflexivity|]. split; [eassumption|].
    split; [eassumption|]. release_frame FR ST (bv_unsigned sp). exact ST. }
  (* the UBSan check `bltu a1, a0` (a1 = -14) falls through *)
  step. step. if_false.
  (* f + 13: its shadow byte and check, then f[13]; bnez a1 *)
  step. gen_addi a0 w13 U13.
  assert (RW13 : ExecF.rng RNG (bv_unsigned w13) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ R12); lia).
  step. gen_shr w13 g13 G13. rewrite U13 in G13.
  step. gen_addi g13 h13 H13.
  assert (RH13 : ExecF.rng RNG (bv_unsigned h13) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS12); lia).
  pose proof (rdw0 m0 h13 _ _ M13 ltac:(lia)) as R. step. clear R.
  ckapp ck_81094 (bv_unsigned a0 + 13) U13 C13 v13.
  pose proof (rdw0 m0 w13 _ _ F13 ltac:(lia)) as R. step. clear R.
  step. if_cases HC13; zify_cond HC13; rewrite zxb_u in HC13.
  { (* f[13] <> 0: mv a0, zero; ld ra; addi sp; ret *)
    assert (W : is_tagged_result bs = 0)
      by (unfold is_tagged_result, PCU.cu_tagged, PCU.cu_byte; rewrite <- E12, <- E13, HC12;
          rewrite (proj2 (Z.eqb_neq _ _) HC13); reflexivity).
    do 4 step. apply evtF_done. rewrite W. do 5 eexists. split; [reflexivity|]. split; [eassumption|].
    split; [eassumption|]. release_frame FR ST (bv_unsigned sp). exact ST. }
  (* the UBSan check `bltu a1, a0` (a1 = -17) falls through *)
  step. step. if_false.
  (* f + 16: its shadow byte and check, then f[16]; addi a3, zero, 0x88; bne a1, a3 *)
  step. gen_addi a0 w16 U16.
  assert (RW16 : ExecF.rng RNG (bv_unsigned w16) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ R16); lia).
  step. gen_shr w16 g16 G16. rewrite U16 in G16.
  step. gen_addi g16 h16 H16.
  assert (RH16 : ExecF.rng RNG (bv_unsigned h16) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS16); lia).
  pose proof (rdw0 m0 h16 _ _ M16 ltac:(lia)) as R. step. clear R.
  ckapp ck_810b8 (bv_unsigned a0 + 16) U16 C16 v16.
  pose proof (rdw0 m0 w16 _ _ F16 ltac:(lia)) as R. step. clear R.
  step. step. if_cases HC16; zify_cond HC16; rewrite zxb_u in HC16.
  { (* f[16] <> 0x88: mv a0, zero; ld ra; addi sp; ret *)
    assert (W : is_tagged_result bs = 0)
      by (unfold is_tagged_result, PCU.cu_tagged, PCU.cu_byte; rewrite <- E12, <- E13, <- E16, HC12, HC13;
          rewrite (proj2 (Z.eqb_neq _ _) HC16); reflexivity).
    do 4 step. apply evtF_done. rewrite W. do 5 eexists. split; [reflexivity|]. split; [eassumption|].
    split; [eassumption|]. release_frame FR ST (bv_unsigned sp). exact ST. }
  (* the UBSan check `bltu a1, a0` (a1 = -18) falls through *)
  step. step. if_false.
  (* f + 17: its shadow byte and check, then f[17]; addi a0, a0, -25; seqz a0, a0; j; ld ra; addi sp; ret *)
  step. gen_addi a0 w17 U17.
  assert (RW17 : ExecF.rng RNG (bv_unsigned w17) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ R16); lia).
  step. gen_shr w17 g17 G17. rewrite U17 in G17.
  step. gen_addi g17 h17 H17.
  assert (RH17 : ExecF.rng RNG (bv_unsigned h17) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS16); lia).
  pose proof (rdw0 m0 h17 _ _ M17 ltac:(lia)) as R. step. clear R.
  ckapp ck_810e0 (bv_unsigned a0 + 17) U17 C17 v17.
  pose proof (rdw0 m0 w17 _ _ F17 ltac:(lia)) as R. step. clear R.
  do 6 step. apply evtF_done.
  assert (A0 : v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b17) + -25)) 1 = Z_to_bv 64 (is_tagged_result bs)).
  { unfold v_sltiu, is_tagged_result, PCU.cu_tagged, PCU.cu_byte, zxb.
    rewrite <- E12, <- E13, <- E16, <- E17, zxb_u. rewrite HC12, HC13, HC16.
    pose proof (byte_range b17) as X17.
    destruct (Z.eq_dec (bv_unsigned b17) 25) as [E|E].
    - rewrite E. vm_compute. reflexivity.
    - rewrite (proj2 (Z.eqb_neq _ _) E), andb_false_r.
      rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
      replace ((bv_unsigned b17 + -25) mod 2 ^ 64 <? 1) with false; [reflexivity|].
      symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia. }
  rewrite A0. do 5 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|].
  release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

(* The statement of the footprint walk, as the close takes it. *)
Theorem wire_is_tagged_reac_holds : is_tagged_reac_cg.wire_is_tagged_reac_holds_stmt.
Proof. exact is_tagged_reac_holds_F. Qed.
