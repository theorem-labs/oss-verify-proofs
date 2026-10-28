(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA Atp_defsA Atp_activewA Atp_pidiA Pj_defsA Pj_hdefsA Imp_hdefsA Imp_lftoi1A Imp_lftoi2A Imp_lftoi3A Imp_lftoi4A Imp_segdefsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition slotW (I : Z) : list ivl := [(I + 16, I + 24); (I + 32, I + 48); (I + 72, I + 80)].

Lemma cells_bytes_map_C1' : forall l : list byte, cells_bytes (map C1 l) = l.
Proof. induction l as [|b l IH]; [reflexivity|]. cbn [map cells_bytes cbytes app]. rewrite IH. reflexivity. Qed.

Lemma sh68_pick : forall (m : mem) a i, rw_cells bsegs m a (map C1 (repeat z8 68)) -> 0 <= i < 68 -> 0 <= a -> a + 68 < 2^64 ->
  ro_cells bsegs m (a + i) [C1 z8].
Proof.
  intros m a i [[WF BY] _] Hi A0 AH. split; [cbn; repeat split; exact I|]. cbn [cells_bytes].
  rewrite cells_bytes_map_C1' in BY.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  apply (bytes_at_nth1 bsegs m a (repeat z8 68)); [exact BY|]. apply nth_error_repeat. lia.
Qed.

Lemma imp_slot_default : forall (usp sp' f lo k : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
  stk bsegs m lo sp' -> lo <= sp' - 64 -> 0x6e0000 <= lo -> sp' + 216 < 2^63 -> 0x6e0000 <= f -> f + 2048 <= lo -> 0 <= shad f -> shad f + 256 <= lo ->
  (f + 2048 <= shad f \/ shad f + 256 <= f) -> f mod 8 = 0 -> 1 <= k <= 3 ->
  client_consts m ->
  slot0A m (f + 160 + 136 * k) ->
  rw_cells bsegs m (shad f + 20) (map C1 (repeat z8 68)) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a0' a1' a2' t1' : word),
      ms = dtor_st IMP_DLOOP_A (Z_to_bv 64 IMP_PDRET_A) sp' gp t0 t1' t2 usp a0' a1' a2' a3 a4 a5 a6 a7 f
             (f + 160 + 136 * (k - 1) + 8) (-544 + 136 * (3 - (k - 1))) s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m1
      /\ munch ((sp' - 64, sp') :: slotW (f + 160 + 136 * k)) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo sp'
      /\ slot0A m1 (f + 160 + 136 * k))
    (dtor_st IMP_DLOOP_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (f + 160 + 136 * k + 8) (-544 + 136 * (3 - k)) s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m).
Proof.
  intros until m. intros ST LO GLO SPH FSEG FLO SH0 SLO SEP F8 KR CC (S16 & S32 & S72 & S112) SH MI.
  set (I := f + 160 + 136 * k) in *.

  assert (SHR : 0 <= shad f + 20 /\ shad f + 20 + 68 < 2^64) by (unfold shad, SHB in *; lia).
  assert (EP : (I + 8) / 8 = f / 8 + 21 + 17 * k) by (subst I; Z.div_mod_to_equations; lia).
  assert (Z1 : ro_cells bsegs m ((I + 8) / 8 + 2147450881) [C1 z8]).
  { replace ((I + 8) / 8 + 2147450881) with (shad f + 20 + (2 + 17 * k)) by (unfold shad, SHB; lia). apply (sh68_pick m _ _ SH); lia. }
  assert (Z3 : ro_cells bsegs m ((I + 8) / 8 + 2147450883) [C1 z8]).
  { replace ((I + 8) / 8 + 2147450883) with (shad f + 20 + (4 + 17 * k)) by (unfold shad, SHB; lia). apply (sh68_pick m _ _ SH); lia. }
  assert (Z4 : ro_cells bsegs m ((I + 8) / 8 + 2147450884) [C1 z8]).
  { replace ((I + 8) / 8 + 2147450884) with (shad f + 20 + (5 + 17 * k)) by (unfold shad, SHB; lia). apply (sh68_pick m _ _ SH); lia. }
  assert (Z8 : ro_cells bsegs m ((I + 8) / 8 + 2147450888) [C1 z8]).
  { replace ((I + 8) / 8 + 2147450888) with (shad f + 20 + (9 + 17 * k)) by (unfold shad, SHB; lia). apply (sh68_pick m _ _ SH); lia. }

  eapply evt_cut.
  { apply (imp_walk10s usp sp' f k x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 z8 (repeat z8 23) Fr fc m);
      [lia| lia| lia| reflexivity| subst I; exact S112| exact MI]. }
  cbv beta. intros ms1 (a0x & -> & ->).

  eapply evt_cut.
  { apply (imp_pdtor0_walk usp sp' f lo (I + 8) (-544 + 136 * (3 - k)) gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m);
      [exact ST| lia| lia| lia| lia| lia| lia| lia| exact SEP| subst I; lia| subst I; lia| subst I; Z.div_mod_to_equations; lia| exact CC
      | replace (I + 8 + 8) with (I + 16) by lia; exact S16| replace (I + 8 + 24) with (I + 32) by lia; exact S32| replace (I + 8 + 64) with (I + 72) by lia; exact S72
      | exact Z1| exact Z3| exact Z4| exact Z8| exact MI]. }
  cbv beta. intros ms2 (m1 & a0' & a1' & a2' & t1' & -> & MU1 & WM1 & MI1 & ST1 & C16 & C32 & C72).

  subst I.
  eapply evt_cut.
  { apply (imp_walk10c usp sp' f k (Z_to_bv 64 IMP_PDRET_A) gp t0 t1' t2 a0' a1' a2' a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m1). lia. }
  cbv beta. intros ms3 <-.
  assert (KP : Z.ltb 0 k = true) by (apply Z.ltb_lt; lia). rewrite KP.
  apply evt_done. eexists m1, a0', a1', a2', t1'. split; [reflexivity|].
  split.
  { eapply munch_weaken; [| exact MU1]. intros x Hx. unfold pdtor0_W, slotW in *. cbn [outside] in *. lia. }
  split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
  split; [replace (f + 160 + 136 * k + 16) with (f + 160 + 136 * k + 8 + 8) by lia; exact C16|].
  split; [replace (f + 160 + 136 * k + 32) with (f + 160 + 136 * k + 8 + 24) by lia; exact C32|].
  split; [replace (f + 160 + 136 * k + 72) with (f + 160 + 136 * k + 8 + 64) by lia; exact C72|].

  apply (rw_cells_agree_nw bsegs m m1 _ _ S112). apply (agree_of_munch _ _ _ _ MU1).
  intros x Hx. unfold out_shortA in Hx. cbn [cells_size csize Nat.add length] in Hx. unfold pdtor0_W. cbn [outside]. lia.
Qed.

Definition slots321W (sp' f : Z) : list ivl := (sp' - 64, sp') :: slotW (f + 568) ++ slotW (f + 432) ++ slotW (f + 296).

Lemma imp_slots321 : forall (usp sp' f lo : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
  stk bsegs m lo sp' -> lo <= sp' - 64 -> 0x6e0000 <= lo -> sp' + 216 < 2^63 -> 0x6e0000 <= f -> f + 2048 <= lo -> 0 <= shad f -> shad f + 256 <= lo ->
  (f + 2048 <= shad f \/ shad f + 256 <= f) -> f mod 8 = 0 ->
  client_consts m ->
  slot0A m (f + 296) -> slot0A m (f + 432) -> slot0A m (f + 568) ->
  rw_cells bsegs m (shad f + 20) (map C1 (repeat z8 68)) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a0' a1' a2' t1' : word),
      ms = dtor_st IMP_DLOOP_A (Z_to_bv 64 IMP_PDRET_A) sp' gp t0 t1' t2 usp a0' a1' a2' a3 a4 a5 a6 a7 f (f + 160 + 136 * 0 + 8) (-544 + 136 * (3 - 0)) s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m1
      /\ munch (slots321W sp' f) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo sp'
      /\ slot0A m1 (f + 296) /\ slot0A m1 (f + 432) /\ slot0A m1 (f + 568))
    (dtor_st IMP_DLOOP_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (f + 576) (-544) s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m).
Proof.
  intros until m. intros ST LO GLO SPH FSEG FLO SH0 SLO SEP F8 CC S1 S2 S3 SH MI.

  assert (CCK : forall mx my W, client_consts mx -> munch W mx my -> Forall (fun iv => 0x6e0000 <= fst iv) W -> client_consts my).
  { intros mx my W (G1 & G2 & G3 & G4) MU HW.
    unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
    assert (AGW : forall a : word, bv_unsigned a < 0x6e0000 -> my a = mx a).
    { intros a Ha. apply MU. clear - HW Ha. induction W as [|[l h] W IH]; [exact I|]. apply Forall_cons_iff in HW. destruct HW as [H1 HW].
      cbn [outside fst] in *. split; [lia| exact (IH HW)]. }
    split; [| split; [| split]];
      first [ apply (ro_cells_agree bsegs mx my _ _ G1) | apply (ro_cells_agree bsegs mx my _ _ G2) | apply (ro_cells_agree bsegs mx my _ _ G3) | apply (ro_cells_agree bsegs mx my _ _ G4) ];
      intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply AGW; lia. }
  assert (SHK : forall mx my W, rw_cells bsegs mx (shad f + 20) (map C1 (repeat z8 68)) -> munch W mx my -> wmono bsegs mx my ->
            Forall (fun iv => (sp' - 64 <= fst iv /\ snd iv <= sp') \/ (f <= fst iv /\ snd iv <= f + 2048)) W -> rw_cells bsegs my (shad f + 20) (map C1 (repeat z8 68))).
  { intros mx my W H MU WM HW. apply (rw_cells_agree_nw bsegs mx my _ _ H). intros a Ha. rewrite cells_size_map_C1' in Ha. rewrite repeat_length in Ha.
    apply MU. clear - HW Ha SLO LO SEP FLO. induction W as [|[l h] W IH]; [exact I|]. apply Forall_cons_iff in HW. destruct HW as [H1 HW].
    cbn [outside fst snd] in *. split; [lia| exact (IH HW)]. }
  assert (SLK : forall mx my W Ia, slot0A mx Ia -> munch W mx my -> wmono bsegs mx my -> Forall (fun iv => snd iv <= Ia + 16 \/ Ia + 136 <= fst iv) W -> slot0A my Ia).
  { intros mx my W Ia H MU WM HW. apply (slot0A_agree mx my Ia H). intros a Ha. apply MU. clear - HW Ha. induction W as [|[l h] W IH]; [exact I|].
    apply Forall_cons_iff in HW. destruct HW as [H1 HW]. cbn [outside fst snd] in *. split; [lia| exact (IH HW)]. }

  eapply evt_cut.
  { replace (f + 576) with (f + 160 + 136 * 3 + 8) by lia. change (-544) with (-544 + 136 * (3 - 3)).
    apply (imp_slot_default usp sp' f lo 3 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m);
      [exact ST| lia| lia| lia| lia| lia| lia| lia| exact SEP| exact F8| lia| exact CC| replace (f + 160 + 136 * 3) with (f + 568) by lia; exact S3| exact SH| exact MI]. }
  cbv beta. intros ms1 (m1 & a01 & a11 & a21 & t11 & -> & MU1 & WM1 & MI1 & ST1 & S3').
  replace (f + 160 + 136 * 3) with (f + 568) in MU1, S3' by lia.
  pose proof (CCK m m1 _ CC MU1 ltac:(unfold slotW; repeat constructor; cbn [fst]; lia)) as CC1.
  pose proof (SHK m m1 _ SH MU1 WM1 ltac:(unfold slotW; repeat constructor; cbn [fst snd]; lia)) as SH1.
  pose proof (SLK m m1 _ (f + 432) S2 MU1 WM1 ltac:(unfold slotW; repeat constructor; cbn [fst snd]; lia)) as S21.
  pose proof (SLK m m1 _ (f + 296) S1 MU1 WM1 ltac:(unfold slotW; repeat constructor; cbn [fst snd]; lia)) as S11.

  eapply evt_cut.
  { replace (3 - 1) with 2 by lia.
    apply (imp_slot_default usp sp' f lo 2 (Z_to_bv 64 IMP_PDRET_A) gp t0 t11 t2 a01 a11 a21 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m1);
      [exact ST1| lia| lia| lia| lia| lia| lia| lia| exact SEP| exact F8| lia| exact CC1| replace (f + 160 + 136 * 2) with (f + 432) by lia; exact S21| exact SH1| exact MI1]. }
  cbv beta. intros ms2 (m2 & a02 & a12 & a22 & t12 & -> & MU2 & WM2 & MI2 & ST2 & S2').
  replace (f + 160 + 136 * 2) with (f + 432) in MU2, S2' by lia.
  pose proof (CCK m1 m2 _ CC1 MU2 ltac:(unfold slotW; repeat constructor; cbn [fst]; lia)) as CC2.
  pose proof (SHK m1 m2 _ SH1 MU2 WM2 ltac:(unfold slotW; repeat constructor; cbn [fst snd]; lia)) as SH2.
  pose proof (SLK m1 m2 _ (f + 568) S3' MU2 WM2 ltac:(unfold slotW; repeat constructor; cbn [fst snd]; lia)) as S32.
  pose proof (SLK m1 m2 _ (f + 296) S11 MU2 WM2 ltac:(unfold slotW; repeat constructor; cbn [fst snd]; lia)) as S12.

  eapply evt_cut.
  { replace (2 - 1) with 1 by lia.
    apply (imp_slot_default usp sp' f lo 1 (Z_to_bv 64 IMP_PDRET_A) gp t0 t12 t2 a02 a12 a22 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m2);
      [exact ST2| lia| lia| lia| lia| lia| lia| lia| exact SEP| exact F8| lia| exact CC2| replace (f + 160 + 136 * 1) with (f + 296) by lia; exact S12| exact SH2| exact MI2]. }
  cbv beta. intros ms3 (m3 & a03 & a13 & a23 & t13 & -> & MU3 & WM3 & MI3 & ST3 & S1').
  replace (f + 160 + 136 * 1) with (f + 296) in MU3, S1' by lia.
  pose proof (SLK m2 m3 _ (f + 568) S32 MU3 WM3 ltac:(unfold slotW; repeat constructor; cbn [fst snd]; lia)) as S33.
  pose proof (SLK m2 m3 _ (f + 432) S2' MU3 WM3 ltac:(unfold slotW; repeat constructor; cbn [fst snd]; lia)) as S23.
  replace (1 - 1) with 0 by lia.
  apply evt_done. eexists m3, a03, a13, a23, t13. split; [reflexivity|].
  split.
  { intros a Ha. rewrite (MU3 a), (MU2 a), (MU1 a); [reflexivity| | |];
      revert Ha; unfold slots321W, slotW; cbn [outside app]; intros Ha; tauto. }
  split; [exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3))|]. split; [exact MI3|]. split; [exact ST3|].
  split; [exact S1'|]. split; [exact S23| exact S33].
Qed.
