(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import AWUb AWAuto HttpAllocA HttpRepA AWKit H_membuffer_insert AWRng.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.

Definition at_insert (lo MB SRC n len : Z) (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz MB) (wz SRC) (wz n) (wz len) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz membuffer_insert_entryA) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m'.

#[using="Type"] Lemma append_prefix : forall (lo MB SRC n A len cap : Z) ra (q : Z) gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 16 -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m MB (mbuf_cells A len cap) -> 0x609000 <= MB -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 ->
  accessible m MB 32 -> win_ok MB 32 ->
  evt asegs (at_insert lo MB SRC n len ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz MB) (wz SRC) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz membuffer_append_entryA) fc None m (seg_rom asegs)).
Proof.
  intros lo MB SRC n A len cap ra q gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 MBC MBLO MBHI AL ACC WK. unfold mbuf_cells, MEMBUF_DEF_SIZE_INC, membuffer_append_entryA in *.
  a0_prologue AE0 [(lo, q)]%Z m.
  carve_frame 16%nat ST.
  walk_ub_to 0x8cd5c%Z.
  env_now AE0 MU WM. release_to q. step.
  apply evt_done. unfold at_insert, membuffer_insert_entryA. do 12 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

#[using="IC"] Lemma append_str_prefix : forall (lo MB SRC A len cap : Z) (str slack : list byte) ra (q : Z) gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 32 - A0_RT_STACK -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m MB (mbuf_cells A len cap) -> 0x609000 <= MB -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 ->
  shw m MB 32 ->
  bytes_at asegs m SRC (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (SRC + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) -> 0 < SRC ->
  shw m SRC (Z.of_nat (length str) + 1) ->
  (SRC + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= alloc_ceiling \/ (q <= SRC /\ SRC + Z.of_nat (length str) + 1 < 2^47)) ->
  Z.of_nat (length str) + 1 <= 2^43 ->
  evt asegs (at_insert lo MB SRC (Z.of_nat (length str)) len ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz MB) (wz SRC) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz membuffer_append_str_entryA) fc None m (seg_rom asegs)).
Proof.
  intros lo MB SRC A len cap str slack ra q gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 MBC MBLO MBHI AL SHWM STR NONUL PAD S0 SHWS SDJ STRB.
  unfold mbuf_cells, MEMBUF_DEF_SIZE_INC, membuffer_append_str_entryA in *. unfold A0_RT_STACK in LO.
  pose proof (bytes_at_bound _ _ _ _ STR) as B3. rewrite length_app in B3. cbn [length] in B3.
  pose proof (shw_win_ok _ _ _ SHWM) as WK.
  a0_prologue AE0 [(lo, q)]%Z m.
  carve_frame 32%nat ST.
  walk_ub_to 0x8d0b0%Z.
  step.
  pose proof SHWS as SHWS1. shw_now SHWS1 MU. env_now AE0 MU WM.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (ic_strlen IC) with (str := str) (slack := slack) (lo := lo);
      first [ exact STR | exact NONUL | exact PAD | exact (proj1 SHWS1) | exact (proj1 (proj2 SHWS1)) | exact AE | reflexivity
            | lia | (split; [exact (proj2 (proj2 SHWS1))| split; lia]) | assumption ]
    | post_call asegs mm ] end.
  clear SHWS1.
  walk_ub_to 0x8d0ec%Z.
  env_now AE0 MU WM. release_to q. step.
  apply evt_done. unfold at_insert, membuffer_insert_entryA. do 12 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

Variable FI : fs_if.
Variable AI : am_if FI.
Variable J : a0_judg FI AI.
Variable AC : am_contracts FI AI J.
Hypothesis ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi.
Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
Local Notation K := (am_K FI AI).
Local Notation BL := (list (block K)).

#[using="Type"] Lemma msrcA_sub : forall (LB : BL) q st SRC n SRC' n', msrcA FI AI LB q st SRC n -> SRC <= SRC' -> SRC' + n' <= SRC + n -> msrcA FI AI LB q st SRC' n'.
Proof.
  intros LB q st SRC n SRC' n' [H|(H1 & H2 & lo & hi & H3 & H4 & H5)] L1 L2; [left; eapply (mblocA_sub FI AI); eauto|].
  right. split; [lia|]. split; [lia|]. exists lo, hi. split; [exact H3|]. lia.
Qed.

#[using="IC AC ASL AMS"] Lemma insert_after_prefix : forall (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : aps FI AI) (LB : BL) (st : fsstate FI) (ok : option K)
    (MB SRC n A len cap lo : Z) (src bs : list byte) (ms0 : machine_state),
  RHEAP_A FI AI s LB m -> RFAKE FI st m ->
  alloc_ceiling <= lo -> lo <= q - 112 - A0_RT_STACK -> q mod 16 = 0 -> q + 16 <= am_stack_top FI AI ->
  rw_cells asegs m MB (mbuf_cells A len cap) -> 0 <= len <= cap -> cap + n + 8 <= 2^28 -> am_budget_le FI AI s LB (cap + n + 6) ->
  mownA FI AI m LB A cap ok bs ->
  mblocA FI AI (lb_keepA FI AI ok LB) q st MB 32 -> MB + 32 <= alloc_ceiling -> MB mod 8 = 0 -> shw m MB 32 ->
  bytes_at asegs m SRC src -> Z.of_nat (length src) = n -> 0 < SRC ->
  msrcA FI AI (lb_keepA FI AI ok LB) q st SRC n -> shw m SRC n -> SRC + n < 2^47 -> (SRC + n <= MB \/ MB + 32 <= SRC) ->
  evt asegs (at_insert lo MB SRC n len ra q gp (wz A0_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m) ms0 ->
  AJ FI AI J (membuffer_append_post_A FI AI ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s LB ok MB A len cap n lo src bs m) ms0 s LB.
Proof.
  intros ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB st ok MB SRC n A len cap lo src bs ms0.
  intros HR RF CLO LO QAL QTOP MBC HLC HNC BUD OWN MBL MBHI AL SHWM SRCB LEN S0 MSRC SHWS SRCHI DJS PRE.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (N0 : 0 <= n) by lia.
  assert (LO' : lo <= q - 112 - 4096) by (unfold A0_RT_STACK in LO; exact LO).
  assert (SUB : forall b, In b (lb_keepA FI AI ok LB) -> In b LB) by (intros b Hb; eapply (lb_keepA_sub FI AI); exact Hb).
  destruct (msrcA_lo FI AI s LB _ q st m SRC n HR SUB RF MSRC ltac:(lia) N0) as (_ & SLO & SHI47).
  assert (SLOx : SRC + n <= alloc_ceiling \/ (q <= SRC /\ SRC + n < 2^47)) by (clear - SLO SRCHI; lia). clear SLO. rename SLOx into SLO.
  assert (BIV1 : Forall (blk_iv FI AI LB) [(lo, q)]) by (constructor; [left; cbn; lia| constructor]).
  eapply (aj_evt FI AI J); [exact PRE|].
  intros ms' (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1 & AE1).
  pose proof (rheap_blk_write FI AI s LB m m1 _ HR MU1 WM1 BIV1) as HR1.
  pose proof (rfake_blk_write FI AI s LB st m m1 _ HR RF MU1 WM1 ltac:(constructor; [split; [left; cbn; lia| cbn; lia]| constructor])) as RF1.
  pose proof (shw_frame _ m m1 MB 32 SHWM MU1 (app_ivs_blk FI AI s LB m _ HR BIV1)) as SHWM1.
  pose proof (shw_frame _ m m1 SRC n SHWS MU1 (app_ivs_blk FI AI s LB m _ HR BIV1)) as SHWS1.
  pose proof (bytes_at_transport asegs _ m m1 _ _ SRCB MU1 ltac:(cbn; lia)) as SRCB1.
  pose proof (rw_cells_transport asegs _ m m1 _ _ MBC MU1 WM1 ltac:(unfold mbuf_cells; cbn [disjoint_from cells_size csize Nat.add]; lia)) as MBC1.
  assert (OWN1 : mownA FI AI m1 LB A cap ok bs).
  { destruct ok as [k|]; cbn in OWN |- *; [| exact OWN]. destruct OWN as [HIN BLK]. split; [exact HIN|].
    destruct (am_block_range FI AI s LB m _ HR HIN) as (R1 & R2 & R3 & R4 & R5 & R5d & _). cbn [blk_addr blk_size fst snd] in *.
    eapply rw_cells_transport; [exact BLK| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; lia]. }
  assert (HP1 : apx FI AI [(MB, MB + 32)] (lb_keepA FI AI ok LB) q m m1).
  { eapply (apx_seg FI AI ASL s LB _ q _ _ m m m1 HR SUB MU1 WM1). constructor; [left; cbn; lia| constructor]. }
  eapply (aj_mono FI AI J).
  { eapply (membuffer_insert_end_spec_A IC FI AI J AC ASL AMS) with (lo := lo) (ok := ok) (MB := MB) (SRC := SRC) (n := n) (A := A) (len := len) (cap := cap) (src := src) (bs := bs);
      first [ exact HR1 | exact RF1 | exact AE1 | exact ST1 | exact CLO | exact LO | exact QAL | exact QTOP | exact MI1 | exact MBC1 | exact HLC | exact HNC
            | exact BUD | exact OWN1 | exact MBL | exact MBHI | exact AL | exact SHWM1 | exact SRCB1 | exact LEN | exact S0 | exact MSRC | exact SHWS1 | exact SRCHI | exact DJS | reflexivity ]. }
  intros s' LB' ms' P. unfold membuffer_append_post_A in *.
  destruct P as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m' & A' & cap' & ok' & bs' & E & P1 & P2 & P3 & P4 & P5 & REST).
  exists v0, v1, v2, c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, m', A', cap', ok', bs'.
  split; [exact E|]. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
  split; [eapply (apx_trans FI AI); [exact HP1| exact P5]| exact REST].
Qed.

#[using="IC AC ASL AMS"] Theorem membuffer_append_spec_A : membuffer_append_stmt_A FI AI J.
Proof.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB st ok MB SRC n A len cap lo src bs.
  intros HR RF AE ST CLO LO QAL QTOP MI MBC HLC HNC BUD OWN MBL MBHI AL SHWM SRCB LEN S0 MSRC SHWS SRCHI DJS -> -> ->.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  assert (SUB : forall b, In b (lb_keepA FI AI ok LB) -> In b LB) by (intros b Hb; eapply (lb_keepA_sub FI AI); exact Hb).
  destruct (mblocA_range FI AI s LB _ q st m MB 32 HR SUB RF MBL ltac:(unfold A0_RT_STACK in LO; lia) ltac:(lia)) as (MBLO & _ & _).
  eapply (insert_after_prefix ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB st ok MB SRC n A len cap lo src bs); try eassumption.
  eapply (append_prefix lo MB SRC n A len cap); try eassumption; [unfold A0_RT_STACK in LO; lia| lia| exact (proj1 SHWM)| exact (shw_win_ok _ _ _ SHWM)].
Qed.

#[using="IC AC ASL AMS"] Theorem membuffer_append_str_spec_A : membuffer_append_str_stmt_A FI AI J.
Proof.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB st ok MB SRC A len cap lo str slack bs.
  intros HR RF AE ST CLO LO QAL QTOP MI MBC HLC HNC BUD OWN MBL MBHI AL SHWM STR NONUL PAD S0 MSRC SHWS SDJ STRB DJS -> ->.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  assert (SUB : forall b, In b (lb_keepA FI AI ok LB) -> In b LB) by (intros b Hb; eapply (lb_keepA_sub FI AI); exact Hb).
  destruct (mblocA_range FI AI s LB _ q st m MB 32 HR SUB RF MBL ltac:(unfold A0_RT_STACK in LO; lia) ltac:(lia)) as (MBLO & _ & _).
  pose proof (proj1 (bytes_at_app asegs m SRC str _) STR) as [SRCB _].
  eapply (insert_after_prefix ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB st ok MB SRC (Z.of_nat (length str)) A len cap lo str bs); try eassumption; try lia.
  - eapply msrcA_sub; [exact MSRC| lia| lia].
  - eapply shw_sub; [exact SHWS| lia| lia| lia].
  - eapply (append_str_prefix lo MB SRC A len cap str slack); try eassumption; [unfold A0_RT_STACK in *; lia| lia].
Qed.
End W.
