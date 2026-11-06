(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.AmLiaKD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMMemB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.AmLiaKD.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= am_lia_kd.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).

Lemma nth_repeat_in {A} (a d : A) (m j : nat) : (j < m)%nat -> nth j (repeat a m) d = a.
Proof. revert j. induction m as [|m IH]; intros [|j] Hj; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); try lia; [reflexivity | apply IH; lia]. Qed.

Section FPGen.
Context {fx : FPState}.

Section MEMB.
  (* [comment removed for export] *)
  Variables (M : word -> option byte) (S m : word) (T n id fillw : Z) (h1 : byte) (w0 w8 w16 wc : word).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation c := (class_of (needed n)).

  Definition mb_1 : word -> option byte := wbytes M (at_ m (rz n - 8)) (LE8 (Z_to_bv 64 (0 * 2 ^ 32 + id))).
  Definition mb_2 : word -> option byte :=
    if (n <? 8)%Z then mb_1
    else wbytes (ps_frame mb_1 sp2 (at_ ARB 0x4ca4c) (Z_to_bv 64 1) (Z_to_bv 64 n) m (Z_to_bv 64 (needed n)) (at_ m (rz n)) (at_ m (rz n - 16)))
                (Z_to_bv 64 (shad (at_ m (rz n)))) (repeat (cbyte (Z_to_bv 64 0)) (Z.to_nat (shlen (Z_to_bv 64 (n - n mod 8))))).
  Definition mb_3 : word -> option byte :=
    if (n mod 8 =? 0)%Z then mb_2 else wbytes mb_2 (Z_to_bv 64 (SB + (U m + rz n + (n - n mod 8)) / 8)) [Z_to_bv 8 (n mod 8)].
  Definition mb_4 : word -> option byte :=
    wbytes (wbytes mb_3 (at_ sp2 (-8)) (LE8 (at_ ARB 0x4cae4))) (at_ sp2 (-24)) (LE8 (at_ ARB 0x78004)).
  Definition mb_5 : word -> option byte := wbytes (wbytes (wbytes mb_4 (at_ thr 2800) (LE8 w0)) (at_ thr 2808) (LE8 w8)) (at_ thr 2816) (LE8 w16).
  Definition mb_6 : word -> option byte := wbytes mb_5 (at_ thr (2912 + 8 * c)) (LE8 wc).
  Definition mb_7 : word -> option byte := wbytes mb_6 (at_ m (rz n)) (repeat (cbyte (Z_to_bv 64 fillw)) (Z.to_nat (Z.min n 4096))).
  Definition mb_8 : word -> option byte := amE3_mem m n h1 mb_7.
  Definition mb_9 : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes mb_8 (at_ sp2 (-8)) (LE8 (at_ ARB 0x4ccc8))) (at_ sp2 (-16)) (LE8 (Z_to_bv 64 1)))
                   (at_ sp2 (-24)) (LE8 (Z_to_bv 64 n))) (at_ sp2 (-32)) (LE8 m).

  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z.
  (* [comment removed for export] *)
  Hypothesis GT : ((4096 <= T /\ TSIDE T) /\ T + 4096 <= U S - 3584)%Z.
  Hypothesis Gn : (1 <= n <= 64512)%Z.
  Hypothesis Gm : (0x10007fff8000 <= U m /\ U m + needed n <= U S - 3584 /\ U m mod 16 = 0)%Z.

  Lemma mbn : (24 <= needed n <= 65536)%Z /\ (16 <= rz n <= 1024)%Z /\ (rz n + 8 <= needed n)%Z /\ (needed n = rounded n + rz n)%Z
              /\ (Z.max n 8 <= rounded n)%Z /\ (1 <= c <= 30)%Z /\ (rz n = 16 <-> rz_log n = 0)%Z /\ (0 <= n mod 8 < 8)%Z /\ (n mod 8 <= n)%Z.
  Proof using Gm Gn m S.
    pose proof (needed_facts n Gn) as [N1 N2]. pose proof (rz_log_range n) as RL.
    assert (Hrz : (16 <= rz n <= 1024)%Z /\ (rz n = 16 <-> rz_log n = 0)%Z).
    { (lazymatch goal with |- ?G => let G' := eval unfold rz in G in change_no_check G' end). destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E; split; lia. }
    assert (Hnd : (needed n = rounded n + rz n)%Z) by reflexivity.
    assert (Hrd : (Z.max n 8 <= rounded n)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold rounded, RoundUp in G in change_no_check G' end); pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)); lia).
    pose proof (Z.mod_pos_bound n 8 ltac:(lia)). pose proof (Z.mod_le n 8 ltac:(lia) ltac:(lia)).
    repeat split; try lia. apply AsArith3.class_of_range; lia. apply AsArith3.class_of_range; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mb_shad : shad (at_ m (rz n)) = (SB + (U m + rz n) / 8)%Z /\ shlen (Z_to_bv 64 (n - n mod 8)) = (n / 8)%Z
                  /\ ((U m + rz n) mod 8 = 0)%Z /\ ((U m + rz n + (n - n mod 8)) / 8 = (U m + rz n) / 8 + n / 8)%Z
                  /\ (SB + (U m + rz n) / 8 + n / 8 + 1 < 2 ^ 45)%Z /\ (0 < SB)%Z.
  Proof using Gm Gn GS S.
    clear M T id fillw h1 w0 w8 w16 wc GT. pose proof mbn as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9). destruct Gm as (G1 & G2 & G3). destruct GS as [G4 G5]. pose proof (u64_range S). pose proof (u64_range m).
    pose proof (rz_mod16 n) as R16.
    (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen, SB in G in change_no_check G' end). rewrite at_u by lia. unorm.
    Z.div_mod_to_equations. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Definition mb_foot (x : word) : Prop :=
    (U m + rz n - 16 <= U x < U m + rz n + n)%Z                                   (* [comment removed for export] *)
    \/ (rz_log n <> 0%Z /\ U m <= U x < U m + 16)%Z                                 (* [comment removed for export] *)
    \/ (SB + (U m + rz n) / 8 <= U x < SB + (U m + rz n) / 8 + n / 8 + (if (n mod 8 =? 0)%Z then 0 else 1))%Z   (* [comment removed for export] *)
    \/ (U S - 2336 <= U x < U S - 2272)%Z                                          (* [comment removed for export] *)
    \/ (T + 2800 <= U x < T + 2824)%Z \/ (T + 2912 + 8 * c <= U x < T + 2912 + 8 * c + 8)%Z.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac lenN := first [rewrite length_N_to_le_bytes | rewrite repeat_length | progress ((lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end))].
  Ltac pside := lenN; rewrite ?Z2Nat.id by lia; rewrite ?at_at; rewrite ?at_u; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.of_nat Pos.of_succ_nat Pos.succ Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.of_nat Pos.of_succ_nat Pos.succ Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); lia ].
  Ltac peel D := unfold hide in D; (etransitivity; [apply wbytes_outside; [pside | pside] | ]); hidehyp D.

  Lemma mb_9_outside : forall x : word,
    (U x < U m + rz n - 16 \/ U m + rz n + n <= U x)%Z ->
    (rz_log n <> 0%Z -> U x < U m \/ U m + 16 <= U x)%Z ->
    (U x < SB + (U m + rz n) / 8 \/ SB + (U m + rz n) / 8 + n / 8 + (if (n mod 8 =? 0)%Z then 0 else 1) <= U x)%Z ->
    (U x < U S - 2336 \/ U S - 2272 <= U x)%Z ->
    (U x < T + 2800 \/ T + 2824 <= U x)%Z ->
    (U x < T + 2912 + 8 * c \/ T + 2912 + 8 * c + 8 <= U x)%Z ->
    mb_9 x = M x.
  Proof using Gm Gn GT GS.
    intros x D1 D2 D3 D4 D5 D6.
    pose proof mbn as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9). pose proof mb_shad as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6).
    destruct Gm as (G1 & G2 & G3). destruct GS as [G4 G5]. destruct GT as [[G6 GTS] G7]. pose proof (u64_range S). pose proof (u64_range m). pose proof (u64_range x).
    hidehyp D1. hidehyp D2. hidehyp D3. hidehyp D4. hidehyp D5. hidehyp D6.
    (lazymatch goal with |- ?G => let G' := eval unfold mb_9 in G in change_no_check G' end). do 4 (peel D4).
    (lazymatch goal with |- ?G => let G' := eval unfold mb_8, amE3_mem in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    assert (E7 : mb_7 x = M x).
    { (lazymatch goal with |- ?G => let G' := eval unfold mb_7 in G in change_no_check G' end). peel D1. (lazymatch goal with |- ?G => let G' := eval unfold mb_6 in G in change_no_check G' end). peel D6. (lazymatch goal with |- ?G => let G' := eval unfold mb_5 in G in change_no_check G' end). do 3 (peel D5). (lazymatch goal with |- ?G => let G' := eval unfold mb_4 in G in change_no_check G' end). do 2 (peel D4).
      (lazymatch goal with |- ?G => let G' := eval unfold mb_3 in G in change_no_check G' end).
      assert (E2 : mb_2 x = M x).
      { (lazymatch goal with |- ?G => let G' := eval unfold mb_2 in G in change_no_check G' end). destruct (n <? 8)%Z eqn:E8.
        - (lazymatch goal with |- ?G => let G' := eval unfold mb_1 in G in change_no_check G' end). peel D1. reflexivity.
        - apply Z.ltb_ge in E8. unfold hide in D3. etransitivity; [apply wbytes_outside|].
          { rewrite repeat_length, SH1, SH2, Z2Nat.id by lia. unorm. lia. }
          { rewrite repeat_length, SH1, SH2, Z2Nat.id by lia. unorm. destruct (n mod 8 =? 0)%Z; lia. }
          hidehyp D3. (lazymatch goal with |- ?G => let G' := eval unfold ps_frame in G in change_no_check G' end). do 7 (peel D4). (lazymatch goal with |- ?G => let G' := eval unfold mb_1 in G in change_no_check G' end). peel D1. reflexivity. }
      destruct (n mod 8 =? 0)%Z eqn:Em; [exact E2|].
      unfold hide in D3. etransitivity; [apply wbytes_outside; [(lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); wd_ulia | (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite SH4; wd_ulia] | exact E2]. }
    destruct (rz_log n =? 0)%Z eqn:Erz.
    - do 2 (peel D1). exact E7.
    - apply Z.eqb_neq in Erz. unfold hide in D2. specialize (D2 Erz). hidehyp D2. peel D2. peel D2. peel D1. peel D1. exact E7.   (* [comment removed for export] *)
  Qed.

  Lemma mb_9_foot : forall x : word, mb_9 x <> M x -> mb_foot x.
  Proof using Gm Gn GT GS.
    intros x NE. (lazymatch goal with |- ?G => let G' := eval unfold mb_foot in G in change_no_check G' end).
    destruct (Z.lt_ge_cases (U x) (U m + rz n - 16)) as [A1|A1]; destruct (Z.lt_ge_cases (U x) (U m + rz n + n)) as [A2|A2]; try lia;
    destruct (decide (rz_log n <> 0%Z /\ U m <= U x < U m + 16)%Z) as [B|B]; try am_tauto;
    destruct (Z.lt_ge_cases (U x) (SB + (U m + rz n) / 8)) as [C1|C1];
    destruct (Z.lt_ge_cases (U x) (SB + (U m + rz n) / 8 + n / 8 + (if (n mod 8 =? 0)%Z then 0 else 1))) as [C2|C2]; try lia;
    destruct (Z.lt_ge_cases (U x) (U S - 2336)) as [E1|E1]; destruct (Z.lt_ge_cases (U x) (U S - 2272)) as [E2|E2]; try lia;
    destruct (Z.lt_ge_cases (U x) (T + 2800)) as [F1|F1]; destruct (Z.lt_ge_cases (U x) (T + 2824)) as [F2|F2]; try lia;
    destruct (Z.lt_ge_cases (U x) (T + 2912 + 8 * c)) as [G1|G1]; destruct (Z.lt_ge_cases (U x) (T + 2912 + 8 * c + 8)) as [G2|G2]; try lia;
    exfalso; apply NE; apply mb_9_outside; try lia; intros Hrz; pose proof (u64_range x); 
    destruct (Z.lt_ge_cases (U x) (U m)); destruct (Z.lt_ge_cases (U x) (U m + 16)); try lia; exfalso; apply B; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mb_1_outside : forall x : word, (U x < U m + rz n - 8 \/ U m + rz n <= U x)%Z -> mb_1 x = M x.
  Proof using Gm Gn GS S.
    clear T fillw h1 w0 w8 w16 wc GT. intros x D1. pose proof mbn as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
    destruct Gm as (G1 & G2 & G3). destruct GS as [G4 G5]. pose proof (u64_range S). pose proof (u64_range m). pose proof (u64_range x).
    hidehyp D1. (lazymatch goal with |- ?G => let G' := eval unfold mb_1 in G in change_no_check G' end). peel D1. reflexivity.
  Qed.
  Lemma mb_2_outside : forall x : word,
    (U x < U m + rz n - 8 \/ U m + rz n <= U x)%Z ->
    (U x < SB + (U m + rz n) / 8 \/ SB + (U m + rz n) / 8 + n / 8 <= U x)%Z ->
    (U x < U S - 2336 \/ U S - 2272 <= U x)%Z ->
    mb_2 x = M x.
  Proof using Gm Gn GS.
    clear T fillw h1 w0 w8 w16 wc GT. intros x D1 D3 D4.
    pose proof mbn as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9). pose proof mb_shad as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6).
    destruct Gm as (G1 & G2 & G3). destruct GS as [G4 G5]. pose proof (u64_range S). pose proof (u64_range m). pose proof (u64_range x).
    hidehyp D1. hidehyp D3. hidehyp D4.
    (lazymatch goal with |- ?G => let G' := eval unfold mb_2 in G in change_no_check G' end). destruct (n <? 8)%Z eqn:E8.
    - (lazymatch goal with |- ?G => let G' := eval unfold mb_1 in G in change_no_check G' end). peel D1. reflexivity.
    - apply Z.ltb_ge in E8. unfold hide in D3. etransitivity; [apply wbytes_outside|].
      { rewrite repeat_length, SH1, SH2, Z2Nat.id by lia. unorm. lia. }
      { rewrite repeat_length, SH1, SH2, Z2Nat.id by lia. unorm. lia. }
      hidehyp D3. (lazymatch goal with |- ?G => let G' := eval unfold ps_frame in G in change_no_check G' end). do 7 (peel D4). (lazymatch goal with |- ?G => let G' := eval unfold mb_1 in G in change_no_check G' end). peel D1. reflexivity.
  Qed.

  Lemma mb_3_outside : forall x : word,
    (U x < U m + rz n - 8 \/ U m + rz n <= U x)%Z ->
    (U x < SB + (U m + rz n) / 8 \/ SB + (U m + rz n) / 8 + n / 8 + (if (n mod 8 =? 0)%Z then 0 else 1) <= U x)%Z ->
    (U x < U S - 2336 \/ U S - 2272 <= U x)%Z ->
    mb_3 x = M x.
  Proof using Gm Gn GS.
    clear T fillw h1 w0 w8 w16 wc GT. intros x D1 D3 D4.
    pose proof mbn as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9). pose proof mb_shad as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6).
    destruct Gm as (G1 & G2 & G3). destruct GS as [G4 G5]. pose proof (u64_range S). pose proof (u64_range m). pose proof (u64_range x).
    hidehyp D1. hidehyp D3. hidehyp D4.
    (lazymatch goal with |- ?G => let G' := eval unfold mb_3 in G in change_no_check G' end).
    assert (E2 : mb_2 x = M x).
    { (lazymatch goal with |- ?G => let G' := eval unfold mb_2 in G in change_no_check G' end). destruct (n <? 8)%Z eqn:E8.
      - (lazymatch goal with |- ?G => let G' := eval unfold mb_1 in G in change_no_check G' end). peel D1. reflexivity.
      - apply Z.ltb_ge in E8. unfold hide in D3. etransitivity; [apply wbytes_outside|].
        { rewrite repeat_length, SH1, SH2, Z2Nat.id by lia. unorm. lia. }
        { rewrite repeat_length, SH1, SH2, Z2Nat.id by lia. unorm. destruct (n mod 8 =? 0)%Z; lia. }
        hidehyp D3. (lazymatch goal with |- ?G => let G' := eval unfold ps_frame in G in change_no_check G' end). do 7 (peel D4). (lazymatch goal with |- ?G => let G' := eval unfold mb_1 in G in change_no_check G' end). peel D1. reflexivity. }
    destruct (n mod 8 =? 0)%Z eqn:Em; [exact E2|].
    unfold hide in D3. etransitivity; [apply wbytes_outside; [(lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); wd_ulia | (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite SH4; wd_ulia] | exact E2].
  Qed.

  Lemma mb_5_outside : forall x : word,
    (U x < U m + rz n - 8 \/ U m + rz n <= U x)%Z ->
    (U x < SB + (U m + rz n) / 8 \/ SB + (U m + rz n) / 8 + n / 8 + (if (n mod 8 =? 0)%Z then 0 else 1) <= U x)%Z ->
    (U x < U S - 2336 \/ U S - 2272 <= U x)%Z ->
    (U x < T + 2800 \/ T + 2824 <= U x)%Z ->
    mb_5 x = M x.
  Proof using Gm Gn GT GS.
    clear fillw h1 wc. intros x D1 D3 D4 D5.
    pose proof mbn as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9). pose proof mb_shad as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6).
    destruct Gm as (G1 & G2 & G3). destruct GS as [G4 G5]. destruct GT as [[G6 GTS] G7]. pose proof (u64_range S). pose proof (u64_range m). pose proof (u64_range x).
    hidehyp D1. hidehyp D3. hidehyp D4. hidehyp D5.
    (lazymatch goal with |- ?G => let G' := eval unfold mb_5 in G in change_no_check G' end). do 3 (peel D5). (lazymatch goal with |- ?G => let G' := eval unfold mb_4 in G in change_no_check G' end). do 2 (peel D4).
    apply mb_3_outside; unfold hide in *; assumption.
  Qed.

  Lemma mb_7_outside : forall x : word,
    (U x < U m + rz n - 8 \/ U m + rz n + Z.min n 4096 <= U x)%Z ->
    (U x < SB + (U m + rz n) / 8 \/ SB + (U m + rz n) / 8 + n / 8 + (if (n mod 8 =? 0)%Z then 0 else 1) <= U x)%Z ->
    (U x < U S - 2336 \/ U S - 2272 <= U x)%Z ->
    (U x < T + 2800 \/ T + 2824 <= U x)%Z ->
    (U x < T + 2912 + 8 * c \/ T + 2912 + 8 * c + 8 <= U x)%Z ->
    mb_7 x = M x.
  Proof using Gm Gn GT GS.
    clear h1. intros x D1 D3 D4 D5 D6.
    pose proof mbn as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9). pose proof mb_shad as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6).
    destruct Gm as (G1 & G2 & G3). destruct GS as [G4 G5]. destruct GT as [[G6 GTS] G7]. pose proof (u64_range S). pose proof (u64_range m). pose proof (u64_range x).
    assert (D1' : (U x < U m + rz n - 8 \/ U m + rz n <= U x)%Z) by lia.
    hidehyp D1. hidehyp D3. hidehyp D4. hidehyp D5. hidehyp D6. hidehyp D1'.
    (lazymatch goal with |- ?G => let G' := eval unfold mb_7 in G in change_no_check G' end). peel D1. (lazymatch goal with |- ?G => let G' := eval unfold mb_6 in G in change_no_check G' end). peel D6.
    apply mb_5_outside; unfold hide in *; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma mb_8_outside : forall x : word,
    (U x < U m + rz n - 16 \/ U m + rz n + Z.min n 4096 <= U x)%Z ->
    (rz_log n <> 0%Z -> U x < U m \/ U m + 16 <= U x)%Z ->
    (U x < SB + (U m + rz n) / 8 \/ SB + (U m + rz n) / 8 + n / 8 + (if (n mod 8 =? 0)%Z then 0 else 1) <= U x)%Z ->
    (U x < U S - 2336 \/ U S - 2272 <= U x)%Z ->
    (U x < T + 2800 \/ T + 2824 <= U x)%Z ->
    (U x < T + 2912 + 8 * c \/ T + 2912 + 8 * c + 8 <= U x)%Z ->
    mb_8 x = M x.
  Proof using Gm Gn GT GS.
    intros x D1 D2 D3 D4 D5 D6.
    pose proof mbn as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9). pose proof mb_shad as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6).
    destruct Gm as (G1 & G2 & G3). destruct GS as [G4 G5]. destruct GT as [[G6 GTS] G7]. pose proof (u64_range S). pose proof (u64_range m). pose proof (u64_range x).
    assert (D1' : (U x < U m + rz n - 8 \/ U m + rz n + Z.min n 4096 <= U x)%Z) by lia.
    hidehyp D1. hidehyp D2. hidehyp D3. hidehyp D4. hidehyp D5. hidehyp D6. hidehyp D1'.
    (lazymatch goal with |- ?G => let G' := eval unfold mb_8, amE3_mem in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    destruct (rz_log n =? 0)%Z eqn:Erz.
    - do 2 (peel D1). apply mb_7_outside; unfold hide in *; assumption.
    - apply Z.eqb_neq in Erz. unfold hide in D2. specialize (D2 Erz). hidehyp D2. do 2 (peel D2). do 2 (peel D1).
      apply mb_7_outside; unfold hide in *; assumption.
  Qed.

  Lemma mb_shadow_range : (2 ^ 32 < SB + (U m + rz n) / 8)%Z /\ (SB + (U m + rz n) / 8 + n / 8 + 1 < 0x10007fff8000)%Z.
  Proof using Gm Gn GS S.
    clear M T id fillw h1 w0 w8 w16 wc GT.
    pose proof mbn as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9). destruct Gm as (G1 & G2 & G3). destruct GS as [G4 G5]. pose proof (u64_range S).
    (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end). Z.div_mod_to_equations. lia.
  Qed.
  Lemma mb_9_grows_1 : mem_grows M mb_1.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mb_1 in G in change_no_check G' end). eapply mem_grows_trans; [apply mem_grows_refl | apply wbytes_grows]. Qed.
  Ltac grows_tac := repeat (first [ apply mem_grows_refl
                  | eapply mem_grows_trans; [|apply wbytes_grows]
                  | lazymatch goal with |- mem_grows _ (if ?b then _ else _) => destruct b end ]).
  Lemma mb_9_grows_2 : mem_grows M mb_2.  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mb_2, mb_1, ps_frame in G in change_no_check G' end). grows_tac. Qed.
  Lemma mb_9_grows_3 : mem_grows M mb_3.  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mb_3, mb_2, mb_1, ps_frame in G in change_no_check G' end). grows_tac. Qed.
  Lemma mb_9_grows_4 : mem_grows M mb_4.  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mb_4, mb_3, mb_2, mb_1, ps_frame in G in change_no_check G' end). grows_tac. Qed.
  Lemma mb_9_grows_5 : mem_grows M mb_5.  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mb_5, mb_4, mb_3, mb_2, mb_1, ps_frame in G in change_no_check G' end). grows_tac. Qed.
  Lemma mb_9_grows_6 : mem_grows M mb_6.  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mb_6, mb_5, mb_4, mb_3, mb_2, mb_1, ps_frame in G in change_no_check G' end). grows_tac. Qed.
  Lemma mb_9_grows_7 : mem_grows M mb_7.  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mb_7, mb_6, mb_5, mb_4, mb_3, mb_2, mb_1, ps_frame in G in change_no_check G' end). grows_tac. Qed.
  Lemma mb_9_grows_8 : mem_grows M mb_8.  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mb_8, amE3_mem, mb_7, mb_6, mb_5, mb_4, mb_3, mb_2, mb_1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). grows_tac. Qed.
  Lemma mb_9_grows : mem_grows M mb_9.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold mb_9, mb_8, amE3_mem, mb_7, mb_6, mb_5, mb_4, mb_3, mb_2, mb_1, ps_frame in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    repeat (first [ apply mem_grows_refl
                  | eapply mem_grows_trans; [|apply wbytes_grows]
                  | lazymatch goal with |- mem_grows _ (if ?b then _ else _) => destruct b end ]).
  Qed.

End MEMB.
End FPGen.
End BoAllocMMemB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.
Import BoAllocMMemB.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).

Lemma nth_repeat_in {A} (a d : A) (m j : nat) : (j < m)%nat -> nth j (repeat a m) d = a.
Proof. revert j. induction m as [|m IH]; intros [|j] Hj; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); try lia; [reflexivity | apply IH; lia]. Qed.

Section FPGen.
Context {fx : FPState}.

Section MEMB2.
  (* [comment removed for export] *)
  Variables (M : word -> option byte) (S m : word) (T n id fillw : Z) (h1 : byte) (w0 w8 w16 wc : word).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation c := (class_of (needed n)).
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z.
  (* [comment removed for export] *)
  Hypothesis GT : ((4096 <= T /\ TSIDE T) /\ T + 4096 <= U S - 3584)%Z.
  Hypothesis Gn : (1 <= n <= 64512)%Z.
  Hypothesis Gm : (0x10007fff8000 <= U m /\ U m + needed n <= U S - 3584 /\ U m mod 16 = 0)%Z.
  (* [comment removed for export] *)
  #[local] Abbreviation mb_1 := (BoAllocMMemB.mb_1 M m n id).
  #[local] Abbreviation mb_2 := (BoAllocMMemB.mb_2 M S m n id).
  #[local] Abbreviation mb_3 := (BoAllocMMemB.mb_3 M S m n id).
  #[local] Abbreviation mb_4 := (BoAllocMMemB.mb_4 M S m n id).
  #[local] Abbreviation mb_5 := (BoAllocMMemB.mb_5 M S m T n id w0 w8 w16).
  #[local] Abbreviation mb_6 := (BoAllocMMemB.mb_6 M S m T n id w0 w8 w16 wc).
  #[local] Abbreviation mb_7 := (BoAllocMMemB.mb_7 M S m T n id fillw w0 w8 w16 wc).
  #[local] Abbreviation mb_8 := (BoAllocMMemB.mb_8 M S m T n id fillw h1 w0 w8 w16 wc).
  #[local] Abbreviation mb_9 := (BoAllocMMemB.mb_9 M S m T n id fillw h1 w0 w8 w16 wc).
  #[local] Abbreviation mbn := (BoAllocMMemB.mbn S m n Gn Gm).
  #[local] Abbreviation mb_shad := (BoAllocMMemB.mb_shad S m n GS Gn Gm).
  #[local] Abbreviation mb_shadow_range := (BoAllocMMemB.mb_shadow_range S m n GS Gn Gm).
  #[local] Abbreviation mb_9_outside := (BoAllocMMemB.mb_9_outside M S m T n id fillw h1 w0 w8 w16 wc GS GT Gn Gm).
  #[local] Abbreviation mb_7_outside := (BoAllocMMemB.mb_7_outside M S m T n id fillw w0 w8 w16 wc GS GT Gn Gm).
  Ltac lenN := first [rewrite length_N_to_le_bytes | rewrite repeat_length | progress ((lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end))].
  Ltac pside := lenN; rewrite ?Z2Nat.id by lia; rewrite ?at_at; rewrite ?at_u; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.of_nat Pos.of_succ_nat Pos.succ Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.of_nat Pos.of_succ_nat Pos.succ Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); lia ].
  Ltac peel D := unfold hide in D; (etransitivity; [apply wbytes_outside; [pside | pside] | ]); hidehyp D.
  (* [comment removed for export] *)
  Ltac prep := pose proof mbn as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9); pose proof mb_shad as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6);
               pose proof mb_shadow_range as [SR1 SR2];
               destruct Gm as (G1 & G2 & G3); destruct GS as [G4 G5]; destruct GT as [[G6 GTS] G7]; pose proof (u64_range S); pose proof (u64_range m);
               assert (Hif : (0 <= (if (n mod 8 =? 0)%Z then 0 else 1) <= 1)%Z) by (destruct (n mod 8 =? 0)%Z; lia);
               assert (R32 : rz_log n <> 0%Z -> (32 <= rz n)%Z) by
                 (intros Hrz'; pose proof (rz_log_range n); unfold rz in *;
                  destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E in *; lia);
               hidehyp N7; hidehyp R32.
  (* [comment removed for export] *)
  Ltac peel1 D := unfold hide in D; (etransitivity; [apply wbytes_outside; [pside | pside] | ]); hidehyp D.

  (* [comment removed for export] *)
  Lemma mb_9_stack : forall x : word, (U S - 2272 <= U x < U S)%Z -> mb_9 x = M x.
  Proof using Gm Gn GT GS. intros x Hx. prep. pose proof (u64_range x). apply mb_9_outside; try (intros; lia); lia. Qed.
  Lemma mb_9_img : forall x : word, (AIMGLO <= U x /\ U x + 1 <= AIMGHI)%Z -> mb_9 x = M x.   (* [comment removed for export] *)
  Proof using Gm Gn GT GS. intros x Hx. prep. pose proof (u64_range x). unfold hideW in GTS. destruct GTS as [[GI|GI] _]; (apply mb_9_outside; try (intros; lia); lia). Qed.
  Lemma mb_9_Tlow : forall x : word, (U m + needed n <= T \/ T + 4096 <= U m)%Z -> (T <= U x < T + 2800)%Z -> mb_9 x = M x.
  Proof using Gm Gn GT GS. intros x GmT Hx. prep. pose proof (u64_range x). unfold hideW in GTS. destruct GTS as [_ [GB|GB]]; (apply mb_9_outside; try (intros; (first [clear - N5 N4 N2 Hx GmT N1 GB SR1 GT N6 Hif SR2 | idtac]; lia)); lia). Qed.
  Lemma mb_9_hdr_mid : forall x : word, (U m + needed n <= T \/ T + 4096 <= U m)%Z -> (U m + rz n - 14 <= U x < U m + rz n - 8)%Z -> mb_9 x = M x.
  Proof using Gm Gn GT GS.
    intros x GmT Hx. prep. pose proof (u64_range x).
    assert (D4 : (U x < U S - 2336 \/ U S - 2272 <= U x)%Z) by lia.
    assert (D1 : (U x < U m + rz n - 8 \/ U m + rz n + Z.min n 4096 <= U x)%Z) by lia.
    assert (Da : (U x < U m + rz n - 15 \/ U m + rz n - 15 + 1 <= U x)%Z) by lia.
    assert (Db : (U x < U m + rz n - 16 \/ U m + rz n - 16 + 1 <= U x)%Z) by lia.
    assert (Dc : rz_log n <> 0%Z -> (U x < U m \/ U m + 16 <= U x)%Z) by (intros Hrz; specialize (R32 Hrz); lia).
    hidehyp D4. hidehyp D1. hidehyp Da. hidehyp Db.
    (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_9 in G in change_no_check G' end). do 4 (peel1 D4). (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_8, amE3_mem in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    destruct (rz_log n =? 0)%Z eqn:Erz.
    - peel1 Db. peel1 Da. apply mb_7_outside; unfold hide in *; (first [clear - Hx Hif SR2 N2 Gm N1 GmT N6 | idtac]; lia).
    - apply Z.eqb_neq in Erz. specialize (Dc Erz). hidehyp Dc. do 2 (peel1 Dc). peel1 Db. peel1 Da. apply mb_7_outside; unfold hide in *; (first [clear - Hx Hif SR2 N2 Gm N1 GmT N6 | idtac]; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma mb_9_ctx : (U m + needed n <= T \/ T + 4096 <= U m)%Z -> (0 <= id < 2 ^ 32)%Z -> rdn BSEGS mb_9 (at_ m (rz n - 8)) 8 = Some (LE8 (Z_to_bv 64 id)).
  Proof using Gm Gn GT GS.
    intros GmT Hid. prep.
    assert (HB : rdn BSEGS mb_1 (at_ m (rz n - 8)) 8 = Some (LE8 (Z_to_bv 64 id))).
    { (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_1 in G in change_no_check G' end). change (0 * 2 ^ 32 + id)%Z with id. apply rdn_wbytes_hitw. rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    eapply (rd_same BSEGS); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact HB].
    intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. pose proof (u64_range x).
    assert (D4 : (U x < U S - 2336 \/ U S - 2272 <= U x)%Z) by lia.
    assert (Dm : (U x < U m + rz n \/ U m + rz n + Z.min n 4096 <= U x)%Z) by lia.
    assert (Da : (U x < U m + rz n - 15 \/ U m + rz n - 15 + 1 <= U x)%Z) by lia.
    assert (Db : (U x < U m + rz n - 16 \/ U m + rz n - 16 + 1 <= U x)%Z) by lia.
    assert (Dc : rz_log n <> 0%Z -> (U x < U m \/ U m + 16 <= U x)%Z) by (intros Hrz; specialize (R32 Hrz); lia).
    assert (D5 : (U x < T + 2800 \/ T + 2824 <= U x)%Z) by (first [clear - Hx GTS N2 N1 GmT | idtac]; (unfold hideW in GTS; lia)).
    assert (D6 : (U x < T + 2912 + 8 * c \/ T + 2912 + 8 * c + 8 <= U x)%Z) by (first [clear - Hx GTS N6 N2 N1 GmT | idtac]; (unfold hideW in GTS; lia)).
    assert (D3 : (U x < SB + (U m + rz n) / 8 \/ SB + (U m + rz n) / 8 + n / 8 + 1 <= U x)%Z) by lia.
    hidehyp D4. hidehyp Dm. hidehyp Da. hidehyp Db. hidehyp D5. hidehyp D6. hidehyp D3.
    (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_9 in G in change_no_check G' end). do 4 (peel1 D4). (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_8, amE3_mem in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    assert (E7 : mb_7 x = mb_1 x).
    { (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_7 in G in change_no_check G' end). peel1 Dm. (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_6 in G in change_no_check G' end). peel1 D6. (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_5 in G in change_no_check G' end). do 3 (peel1 D5). (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_4 in G in change_no_check G' end). do 2 (peel1 D4).
      (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_3 in G in change_no_check G' end). assert (E2 : mb_2 x = mb_1 x).
      { (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_2 in G in change_no_check G' end). destruct (n <? 8)%Z eqn:E8; [reflexivity|]. apply Z.ltb_ge in E8. unfold hide in D3.
        etransitivity; [apply wbytes_outside|].
        { rewrite repeat_length, SH1, SH2, Z2Nat.id by lia. unorm. lia. }
        { rewrite repeat_length, SH1, SH2, Z2Nat.id by lia. unorm. lia. }
        hidehyp D3. (lazymatch goal with |- ?G => let G' := eval unfold ps_frame in G in change_no_check G' end). do 7 (peel1 D4). reflexivity. }
      destruct (n mod 8 =? 0)%Z eqn:Em; [exact E2|]. unfold hide in D3.
      etransitivity; [apply wbytes_outside; [(lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); wd_ulia | (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite SH4; wd_ulia] | exact E2]. }
    destruct (rz_log n =? 0)%Z eqn:Erz.
    - peel1 Db. peel1 Da. exact E7.
    - apply Z.eqb_neq in Erz. specialize (Dc Erz). hidehyp Dc. do 2 (peel1 Dc). peel1 Db. peel1 Da. exact E7.
  Qed.

  (* [comment removed for export] *)
  Lemma mb_9_state : mb_9 (at_ m (rz n - 16)) = Some (Z_to_bv 8 2)
                   /\ mb_9 (at_ m (rz n - 15)) = Some (Z_to_bv 8 (U (hb2w (Z_to_bv 64 (U h1))))).
  Proof using Gm Gn GT GS.
    prep.
    assert (D4 : forall k, (k = 15 \/ k = 16)%Z -> (U (at_ m (rz n - k)) < U S - 2336 \/ U S - 2272 <= U (at_ m (rz n - k)))%Z) by (intros k Hk; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    pose proof (D4 16%Z ltac:(lia)) as Db. pose proof (D4 15%Z ltac:(lia)) as Da. clear D4. hidehyp Da. hidehyp Db.
    (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_9, mb_8, amE3_mem in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). split.
    - do 4 (peel1 Db). destruct (rz_log n =? 0)%Z eqn:Erz.
      + rewrite wbytes_inside; [rewrite Z.sub_diag; reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
      + apply Z.eqb_neq in Erz.
        specialize (R32 Erz). assert (Dc : (U (at_ m (rz n - 16)) < U m \/ U m + 16 <= U (at_ m (rz n - 16)))%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]). hidehyp Dc.
        do 2 (peel1 Dc). rewrite wbytes_inside; [rewrite Z.sub_diag; reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
    - do 4 (peel1 Da). destruct (rz_log n =? 0)%Z eqn:Erz.
      + etransitivity; [apply wbytes_outside; [(lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ]] |].
        rewrite wbytes_inside; [rewrite Z.sub_diag; reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
      + apply Z.eqb_neq in Erz.
        specialize (R32 Erz). assert (Dc : (U (at_ m (rz n - 15)) < U m \/ U m + 16 <= U (at_ m (rz n - 15)))%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]). hidehyp Dc.
        do 2 (peel1 Dc). etransitivity; [apply wbytes_outside; [(lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ]] |].
        rewrite wbytes_inside; [rewrite Z.sub_diag; reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
  Qed.

  (* [comment removed for export] *)
  Lemma mb_9_lch : rz_log n <> 0%Z ->
    rdn BSEGS mb_9 m 8 = Some (LE8 (Z_to_bv 64 MAGIC)) /\ rdn BSEGS mb_9 (at_ m 8) 8 = Some (LE8 (at_ m (rz n - 16))).
  Proof using Gm Gn GT GS.
    intros Hrz. prep.
    assert (HB : rdn BSEGS mb_8 m 8 = Some (LE8 (Z_to_bv 64 MAGIC)) /\ rdn BSEGS mb_8 (at_ m 8) 8 = Some (LE8 (at_ m (rz n - 16)))).
    { (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_8, amE3_mem in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). replace (rz_log n =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact Hrz). split.
      - apply rdn_wbytes_hitw. lia.
      - rewrite wc_rdn_wbytes_out3; [ | rd8_side ]. apply rdn_wbytes_hitw. rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    destruct HB as [HB1 HB2].
    assert (XF : forall (a : word) bs, (U m <= U a)%Z -> (U a + 8 <= U m + 16)%Z -> rdn BSEGS mb_8 a 8 = Some bs -> rdn BSEGS mb_9 a 8 = Some bs).
    { intros a bs Ha1 Ha2 Hr. eapply (rd_same BSEGS); [| (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Hr]. intros x Hx. cbn in Hx. pose proof (u64_range x).
      assert (D4 : (U x < U S - 2336 \/ U S - 2272 <= U x)%Z) by lia. hidehyp D4.
      (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_9 in G in change_no_check G' end). do 4 (peel1 D4). reflexivity. }
    split; [apply XF; [lia | lia | exact HB1] | apply XF; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact HB2]].
  Qed.

  (* [comment removed for export] *)
  Lemma mb_9_shadow0 : forall i, (0 <= i < n / 8)%Z -> mb_9 (Z_to_bv 64 (SB + (U m + rz n) / 8 + i)) = Some (Z_to_bv 8 0).
  Proof using Gm Gn GT GS.
    intros i Hi. prep.
    set (x := Z_to_bv 64 (SB + (U m + rz n) / 8 + i)).
    assert (Ux : U x = (SB + (U m + rz n) / 8 + i)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold x in G in change_no_check G' end); unorm; reflexivity).
    assert (D4 : (U x < U S - 2336 \/ U S - 2272 <= U x)%Z) by lia.
    assert (Dm : (U x < U m + rz n - 16 \/ U m + rz n + Z.min n 4096 <= U x)%Z) by lia.
    assert (Dc : rz_log n <> 0%Z -> (U x < U m \/ U m + 16 <= U x)%Z) by lia.
    assert (D5 : (U x < T + 2800 \/ T + 2824 <= U x)%Z) by (first [clear - Ux GTS SR2 SR1 Hi | idtac]; (unfold hideW in GTS; lia)).
    assert (D6 : (U x < T + 2912 + 8 * c \/ T + 2912 + 8 * c + 8 <= U x)%Z) by (first [clear - Ux GTS SR2 SR1 N6 Hi | idtac]; (unfold hideW in GTS; lia)).
    assert (E8 : (n <? 8)%Z = false) by (apply Z.ltb_ge; Z.div_mod_to_equations; lia).
    hidehyp D4. hidehyp Dm. hidehyp D5. hidehyp D6.
    transitivity (mb_3 x).
    { transitivity (mb_7 x).
      - (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_9 in G in change_no_check G' end). do 4 (peel1 D4). (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_8, amE3_mem in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). destruct (rz_log n =? 0)%Z eqn:Erz.
        + do 2 (peel1 Dm). reflexivity.
        + apply Z.eqb_neq in Erz. specialize (Dc Erz). hidehyp Dc. do 2 (peel1 Dc). do 2 (peel1 Dm). reflexivity.
      - (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_7 in G in change_no_check G' end). peel1 Dm. (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_6 in G in change_no_check G' end). peel1 D6. (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_5 in G in change_no_check G' end). do 3 (peel1 D5). (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_4 in G in change_no_check G' end). do 2 (peel1 D4). reflexivity. }
    (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_3 in G in change_no_check G' end).
    assert (E2 : mb_2 x = Some (Z_to_bv 8 0)).
    { (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_2 in G in change_no_check G' end). rewrite E8. rewrite wbytes_inside.
      - rewrite nth_repeat_in by (rewrite SH1, SH2; wd_ulia). reflexivity.
      - rewrite repeat_length, SH1, SH2, Z2Nat.id by lia. unorm. lia.
      - rewrite repeat_length, SH1, SH2, Z2Nat.id by lia. unorm. lia. }
    destruct (n mod 8 =? 0)%Z eqn:Em; [exact E2|].
    etransitivity; [apply wbytes_outside; [(lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); wd_ulia | (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite SH4; wd_ulia] | exact E2].
  Qed.

  Lemma mb_9_shadowp : (n mod 8 <> 0)%Z -> mb_9 (Z_to_bv 64 (SB + (U m + rz n) / 8 + n / 8)) = Some (Z_to_bv 8 (n mod 8)).
  Proof using Gm Gn GT GS.
    intros Hm. prep.
    set (x := Z_to_bv 64 (SB + (U m + rz n) / 8 + n / 8)).
    assert (Ux : U x = (SB + (U m + rz n) / 8 + n / 8)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold x in G in change_no_check G' end); unorm; reflexivity).
    assert (D4 : (U x < U S - 2336 \/ U S - 2272 <= U x)%Z) by lia.
    assert (Dm : (U x < U m + rz n - 16 \/ U m + rz n + Z.min n 4096 <= U x)%Z) by lia.
    assert (Dc : rz_log n <> 0%Z -> (U x < U m \/ U m + 16 <= U x)%Z) by lia.
    assert (D5 : (U x < T + 2800 \/ T + 2824 <= U x)%Z) by (first [clear - Ux GTS SR2 SR1 Gn | idtac]; (unfold hideW in GTS; lia)).
    assert (D6 : (U x < T + 2912 + 8 * c \/ T + 2912 + 8 * c + 8 <= U x)%Z) by (first [clear - Ux GTS SR2 SR1 N6 Gn | idtac]; (unfold hideW in GTS; lia)).
    hidehyp D4. hidehyp Dm. hidehyp D5. hidehyp D6.
    transitivity (mb_3 x).
    { transitivity (mb_7 x).
      - (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_9 in G in change_no_check G' end). do 4 (peel1 D4). (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_8, amE3_mem in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). destruct (rz_log n =? 0)%Z eqn:Erz.
        + do 2 (peel1 Dm). reflexivity.
        + apply Z.eqb_neq in Erz. specialize (Dc Erz). hidehyp Dc. do 2 (peel1 Dc). do 2 (peel1 Dm). reflexivity.
      - (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_7 in G in change_no_check G' end). peel1 Dm. (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_6 in G in change_no_check G' end). peel1 D6. (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_5 in G in change_no_check G' end). do 3 (peel1 D5). (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_4 in G in change_no_check G' end). do 2 (peel1 D4). reflexivity. }
    (lazymatch goal with |- ?G => let G' := eval unfold BoAllocMMemB.mb_3 in G in change_no_check G' end). replace (n mod 8 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact Hm).
    replace (Z_to_bv 64 (SB + (U m + rz n + (n - n mod 8)) / 8)) with x by ((lazymatch goal with |- ?G => let G' := eval unfold x in G in change_no_check G' end); f_equal; rewrite SH4; lia).
    rewrite wbytes_inside; [rewrite Z.sub_diag; reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); lia].
  Qed.
End MEMB2.
End FPGen.
