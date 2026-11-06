From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge FP Image.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import printf_facts_c snprintf_c memcpy_c reac_rate_drivable_csv_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import dcsv_lib dcsv_defs.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
Import ListNotations.
Open Scope Z_scope.

(** One pass of drivable_csv's loop (UBSan 0x14e5c .. 0x14ef8): the inlined reac_rate_bit compare chain on
    ordered[i] ([dcsv_chain]), the 64-bit `and` with the mask and its `beqz` ([dcsv_pass]); for a set bit the
    separator choice and snprintf, the dead `bltz` / `bltu 31` skips, trap test 0x14ec0, memcpy into tmp, trap test
    0x14ed4 and the NUL store ([dcsv_set]); then the loop counter and `bnez s6`. *)

Section Pass.
Variables (gp tp mask : word) (S0 lo n buf : Z) (sv : list cell) (m0 : word -> option byte) (canary : word)
  (junk : list byte) (F0 : bvmap 5 word).
Hypothesis HK : lo + 6112 <= S0.
Hypothesis HI : 0x50cc8 <= lo.
Hypothesis H63 : S0 < 2^63.
Hypothesis HBL : 0 < n -> buf + n <= lo \/ S0 <= buf.
Hypothesis Hsv : cells_size sv = 104%nat.
Hypothesis TK0 : MemNorm.task_mem rsegs m0.
Hypothesis ST0 : stk rsegs m0 lo S0.
Hypothesis SNP : snprintf_contract.
Hypothesis MCP : memcpy_contract.

Local Abbreviation OK := (dok S0 lo n buf mask sv m0 canary junk F0).
Local Abbreviation ST := (dst gp tp mask S0).

Definition dnext (Q : machine_state -> Prop) (i : nat) : Prop :=
  forall (pc len' r6' r9' : Z) (m' : word -> option byte) (F' : bvmap 5 word) (fc' : bv 32)
         (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
    ((S i < 3)%nat /\ pc = 0x14e5c \/ S i = 3%nat /\ pc = 0x14efc) -> OK (S i) len' r6' r9' m' F' fc' ->
    evt rsegs Q (ST pc len' r6' r9' F' fc' m' y1 y5 y6 y7 (Z_to_bv 64 96000) y9 y10 y11 y12 y13 y14 y15 y16 y17
                    y28 y29 y30 y31).

Lemma dcsv_chain : forall Q (i : nat) len r6 r9 m F fc
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  (i < 3)%nat -> r9 = 0x10644 + 4 * Z.of_nat i -> mem_inv rsegs m ->
  evt rsegs Q (ST 0x14e88 len r6 r9 F fc m x1 x5 x6 x7 (Z_to_bv 64 96000) x9
                  (Z_to_bv 64 (rate_bit (nth i closed_list 0))) x11 x12 x13 (Z_to_bv 64 (nth i closed_list 0))
                  x15 x16 x17 x28 x29 x30 x31) ->
  evt rsegs Q (ST 0x14e5c len r6 r9 F fc m x1 x5 x6 x7 (Z_to_bv 64 96000) x9 x10 x11 x12 x13 x14 x15 x16 x17
                  x28 x29 x30 x31).
Proof.
  intros Q i len r6 r9 m F fc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hi E9 MI K.
  subst r9. unfold dst in *.
  destruct i as [|[|[|i]]]; [| | | lia].
  - change (0x10644 + 4 * Z.of_nat 0) with 0x10644 in *. run_to 0x14e88. exact K.
  - change (0x10644 + 4 * Z.of_nat 1) with 0x10648 in *. run_to 0x14e88. exact K.
  - change (0x10644 + 4 * Z.of_nat 2) with 0x1064c in *. run_to 0x14e88. exact K.
Qed.

Lemma dcsv_len : forall i, (i <= 3)%nat -> (length (csv_prefix (bv_unsigned mask) i) <= 17)%nat.
Proof.
  intros i Hi. apply csv_prefix_length; [exact Hi|]. pose proof (bv_unsigned_in_range 64 mask). lia.
Qed.

(** A set bit: from 0x14e9c (a3 = the separator) to the loop head of pass i + 1. *)
Lemma dcsv_set : forall Q (i : nat) len r6 r9 m F fc
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x15 x16 x17 x28 x29 x30 x31 : word),
  (i < 3)%nat -> Z.testbit (bv_unsigned mask) (Z.of_nat i) = true -> OK i len r6 r9 m F fc ->
  x13 = Z_to_bv 64 (sep_of len) -> dnext Q i ->
  evt rsegs Q (ST 0x14e9c len r6 r9 F fc m x1 x5 x6 x7 (Z_to_bv 64 96000) x9 x10 x11 x12 x13
                  (Z_to_bv 64 (nth i closed_list 0)) x15 x16 x17 x28 x29 x30 x31).
Proof.
  intros Q i len r6 r9 m F fc x1 x5 x6 x7 x9 x10 x11 x12 x13 x15 x16 x17 x28 x29 x30 x31 Hi TB OKi E13 K.
  subst x13.
  destruct OKi as (El & E6 & E9 & DM & FC & FK).
  destruct DM as (KP & STl & SC & BP & MI & WM & MU).
  pose proof STl as (Hlo & _ & _).
  pose proof (dcsv_len i ltac:(lia)) as LP. pose proof (dcsv_len (S i) ltac:(lia)) as LP1.
  pose proof (csv_prefix_set (bv_unsigned mask) i TB) as EP1. rewrite <- El in EP1.
  pose proof (dcsv_rate_len i Hi) as RL. pose proof (sep_str_len len) as SL.
  assert (LT : length (csv_prefix (bv_unsigned mask) (S i)) =
               Nat.add (length (csv_prefix (bv_unsigned mask) i)) (length (sep_str len ++ csv_dec (nth i closed_list 0))))
    by (rewrite EP1, length_app; reflexivity).
  rewrite length_app, RL in LT.
  assert (TKm : MemNorm.task_mem rsegs m) by (eapply dcsv_task; [exact TK0 | exact ST0 | exact MU]).
  pose proof KP as (_ & _ & GG & GD & _).
  unfold dst in *.
  (* addi a0, sp, 0x18; addi a1, zero, 16; mv a2, s4; jal snprintf *)
  step. step. step. step.
  eapply evt_cut.
  { eapply (dcsv_snp SNP m lo S0 len i fc canary F);
      [exact STl | eapply stk_sub; [exact SC | lia | lia | lia] | exact HK | exact HI | exact H63 | exact GG
      | exact GD | exact MI | exact TKm | exact FC | exact Hi]. }
  intros ms' PP. unfold printf_post in PP.
  destruct PP as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & F1 & fc1 & m1
                  & E & MU1 & WM1 & MI1 & TK1 & FC1 & FK1 & ST1 & BY1).
  subst ms'. rewrite (ret_pc_even 0x14eac) by (first [lia | reflexivity]).
  rewrite (unsigned_lit (S0 + -176)) in MU1, ST1 by lia.
  set (T := sep_str len ++ csv_dec (nth i closed_list 0)) in *.
  assert (LTT : length T = (length (sep_str len) + 5)%nat) by (unfold T; rewrite length_app, RL; reflexivity).
  (* the memory after snprintf *)
  assert (KP1 : dkeep S0 lo n buf sv canary junk m1).
  { eapply dkeep_tr; [exact KP | exact MU1 | exact WM1 | | exact Hsv | exact HI | exact HK | exact HBL].
    intros y Hy. cbn [outside] in Hy. lia. }
  assert (SC1 : stk rsegs m1 (S0 + -152) (S0 + -104)).
  { eapply stk_tr; [exact SC | exact MU1 | exact WM1 |]. intros x Hx.
    destruct (Z_lt_le_dec x (S0 + -152 + Z.of_nat (length T) + 1)) as [X|X].
    - right. eapply bytes_at_mrd; [exact BY1 | rewrite length_pf_bytes, length_app; cbn [length]; lia].
    - left. cbn [outside]. lia. }
  assert (BP1 : bytes_at rsegs m1 (S0 + -136) (csv_bytes (csv_prefix (bv_unsigned mask) i ++ [0]))).
  { eapply bytes_at_tr; [exact BP | exact MU1 |]. intros x Hx. cbn [outside]. lia. }
  assert (MU1' : munch [(lo, S0)] m0 m1).
  { eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU1]].
    intros x Hx; cbn [outside] in *; lia. }
  pose proof (wmono_trans rsegs _ _ _ WM WM1) as WM1'.
  clear KP SC BP MU WM MU1 STl GG GD TKm.
  (* bltz a0 (dead) *)
  step. rewrite ltz_lit by lia. try if_false.
  (* mv a2, a0; add s1, s2, a0; addi a0, zero, 31; bltu a0, s1 (dead) *)
  step. step. step. step. rewrite ltu_lit by lia. if_false.
  (* trap test 0x14ec0: bltu s8, s2 *)
  step. rewrite ltu_lit by lia. if_false.
  (* addi a0, sp, 0x28; add a0, a0, s2; addi a1, sp, 0x18; jal memcpy *)
  step. step. step. step.
  destruct (stk_cb_at m1 (S0 + -152) (S0 + -104) (S0 + -136 + len) (length T) SC1 ltac:(lia) ltac:(lia))
    as [jt RT].
  assert (BYT : bytes_at rsegs m1 (S0 + -152) (pf_bytes T)).
  { rewrite pf_bytes_app in BY1. apply bytes_at_app in BY1. exact (proj1 BY1). }
  eapply evt_cut.
  { eapply MCP with (src := pf_bytes T) (junk := jt).
    - rewrite unsigned_lit by lia. exact BYT.
    - rewrite unsigned_lit by lia. rewrite length_pf_bytes. lia.
    - rewrite !unsigned_lit by lia. replace (Z.to_nat (Z.of_nat (length T))) with (length T) by lia. exact RT.
    - rewrite !unsigned_lit by lia. left. lia.
    - exact MI1. }
  intros ms' PP. unfold memcpy_post in PP.
  destruct PP as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m2
                  & E & MU2 & WM2 & MI2 & RW2 & BY2).
  subst ms'. rewrite (ret_pc_even 0x14ed4) by (first [lia | reflexivity]).
  rewrite !unsigned_lit in MU2, RW2 by lia.
  replace (Z.to_nat (Z.of_nat (length T))) with (length T) in RW2 by lia.
  assert (KP2 : dkeep S0 lo n buf sv canary junk m2).
  { eapply dkeep_tr; [exact KP1 | exact MU2 | exact WM2 | | exact Hsv | exact HI | exact HK | exact HBL].
    intros y Hy. cbn [outside] in Hy. lia. }
  pose proof (rwc_cb _ _ _ _ RW2) as (_ & BT2).
  assert (SC2 : stk rsegs m2 (S0 + -152) (S0 + -104)).
  { eapply stk_tr; [exact SC1 | exact MU2 | exact WM2 |]. intros x Hx.
    destruct (Z_lt_le_dec x (S0 + -136 + len)) as [X|X];
      [|destruct (Z_lt_le_dec x (S0 + -136 + len + Z.of_nat (length T))) as [X'|X']].
    - left. cbn [outside]. lia.
    - right. eapply bytes_at_mrd; [exact BT2 | rewrite length_pf_bytes; lia].
    - left. cbn [outside]. lia. }
  assert (BP2 : bytes_at rsegs m2 (S0 + -136) (csv_bytes (csv_prefix (bv_unsigned mask) i))).
  { rewrite csv_bytes_app in BP1. apply bytes_at_app in BP1.
    eapply bytes_at_tr; [exact (proj1 BP1) | exact MU2 |]. intros x Hx. rewrite csv_bytes_length in Hx.
    cbn [outside]. lia. }
  assert (ST2 : stk rsegs m2 lo (S0 + -176)).
  { eapply stk_tr; [exact ST1 | exact MU2 | exact WM2 |]. intros x Hx. left. cbn [outside]. lia. }
  assert (MU2' : munch [(lo, S0)] m0 m2).
  { eapply munch_trans; [exact MU1' | eapply munch_weaken; [| exact MU2]].
    intros x Hx; cbn [outside] in *; lia. }
  pose proof (wmono_trans rsegs _ _ _ WM1' WM2) as WM2'.
  clear KP1 SC1 BP1 MU1' WM1' MU2 ST1 RT BYT BY1 BY2 RW2.
  (* trap test 0x14ed4: bltu s8, s1 *)
  step. rewrite ltu_lit by lia. if_false.
  (* addi a0, sp, 0x28; add a0, a0, s1 *)
  step. step.
  set (A1 := S0 + -136 + (len + Z.of_nat (length T))) in *.
  assert (EA1 : A1 = S0 + -136 + (len + Z.of_nat (length T))) by reflexivity.
  clearbody A1.
  destruct (stk_cb_at m2 (S0 + -152) (S0 + -104) A1 1 SC2 ltac:(lia) ltac:(lia)) as [j1 R1].
  pose proof (munch_refl [(A1, A1 + 1)] m2) as MU3. pose proof (wmono_refl rsegs m2) as WM3.
  assert (KEEP : dkeep S0 lo n buf sv canary junk m2 /\ stk rsegs m2 (S0 + -152) (S0 + -104) /\
                 bytes_at rsegs m2 (S0 + -136) (csv_bytes (csv_prefix (bv_unsigned mask) i)) /\
                 bytes_at rsegs m2 (S0 + -136 + len) (pf_bytes T) /\ stk rsegs m2 lo (S0 + -176) /\
                 munch [(lo, S0)] m0 m2 /\ wmono rsegs m0 m2)
    by exact (conj KP2 (conj SC2 (conj BP2 (conj BT2 (conj ST2 (conj MU2' WM2')))))).
  clear KP2 SC2 BP2 BT2 ST2 MU2' WM2'.
  (* sb zero, 0(a0) *)
  step. fix_zero_store.
  destruct KEEP as (KP3 & SC3 & BP3 & BT3 & ST3 & MU3' & WM3').
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  assert (KP4 : dkeep S0 lo n buf sv canary junk m3).
  { eapply dkeep_tr; [exact KP3 | exact MU3 | exact WM3 | | exact Hsv | exact HI | exact HK | exact HBL].
    intros y Hy. cbn [outside] in Hy. lia. }
  destruct R1 as [[_ B1] _]. cbn [cells_bytes cbytes] in B1. rewrite app_nil_r in B1.
  assert (SC4 : stk rsegs m3 (S0 + -152) (S0 + -104)).
  { eapply stk_tr; [exact SC3 | exact MU3 | exact WM3 |]. intros x Hx.
    destruct (Z.eq_dec x A1) as [X|X].
    - right. eapply bytes_at_mrd; [exact B1 | cbn [length]; lia].
    - left. cbn [outside]. lia. }
  assert (BP4 : bytes_at rsegs m3 (S0 + -136) (csv_bytes (csv_prefix (bv_unsigned mask) i))).
  { eapply bytes_at_tr; [exact BP3 | exact MU3 |]. intros x Hx. rewrite csv_bytes_length in Hx.
    cbn [outside]. lia. }
  assert (BT4 : bytes_at rsegs m3 (S0 + -136 + len) (pf_bytes T)).
  { eapply bytes_at_tr; [exact BT3 | exact MU3 |]. intros x Hx. rewrite length_pf_bytes in Hx.
    cbn [outside]. lia. }
  assert (ST4 : stk rsegs m3 lo (S0 + -176)).
  { eapply stk_tr; [exact ST3 | exact MU3 | exact WM3 |]. intros x Hx. left. cbn [outside]. lia. }
  assert (MU4 : munch [(lo, S0)] m0 m3).
  { eapply munch_trans; [exact MU3' | eapply munch_weaken; [| exact MU3]].
    intros x Hx; cbn [outside] in *; lia. }
  pose proof (wmono_trans rsegs _ _ _ WM3' WM3) as WM4.
  clear KP3 SC3 BP3 BT3 ST3 MU3' WM3' MU3 WM3.
  (* j 8; mv s2, s1; addi s6, s6, -1; addi s9, s9, 4; bnez s6 *)
  step. step. step. step. step.
  rewrite eqb_lit by lia.
  unfold dnext in K.
  destruct (Z.eqb_spec (r6 + -1) 0) as [Z0|Z0]; cbn [negb]; first [if_true | if_false | idtac];
    (eapply K; [first [right; split; lia | left; split; lia] |]).
  all: unfold dok; split; [rewrite EP1, length_app; lia|]; split; [lia|]; split; [lia|].
  all: split; [|split; [exact FC1 | intros k Hk; rewrite FK1 by exact Hk; apply FK; exact Hk]].
  all: unfold dmem; rewrite EP1; split; [exact KP4|]; split; [exact ST4|]; split; [exact SC4|].
  all: split; [|split; [assumption | split; [exact WM4 | exact MU4]]].
  all: rewrite <- app_assoc, !csv_bytes_app; apply bytes_at_app; split; [exact BP4|]; apply bytes_at_app; split.
  all: rewrite csv_bytes_length.
  1, 3: replace (S0 + -136 + Z.of_nat (length (csv_prefix (bv_unsigned mask) i))) with (S0 + -136 + len) by lia;
        exact BT4.
  all: rewrite csv_bytes_length;
       replace (S0 + -136 + Z.of_nat (length (csv_prefix (bv_unsigned mask) i)) + Z.of_nat (length T)) with A1
         by lia; exact B1.
Qed.

(** From 0x14e88 (a0 = reac_rate_bit(ordered[i]), a4 = ordered[i]) to the loop head of pass i + 1. *)
Lemma dcsv_pass : forall Q (i : nat) len r6 r9 m F fc
    (x1 x5 x6 x7 x9 x11 x12 x13 x15 x16 x17 x28 x29 x30 x31 : word),
  (i < 3)%nat -> OK i len r6 r9 m F fc -> dnext Q i ->
  evt rsegs Q (ST 0x14e88 len r6 r9 F fc m x1 x5 x6 x7 (Z_to_bv 64 96000) x9
                  (Z_to_bv 64 (rate_bit (nth i closed_list 0))) x11 x12 x13 (Z_to_bv 64 (nth i closed_list 0))
                  x15 x16 x17 x28 x29 x30 x31).
Proof.
  intros Q i len r6 r9 m F fc x1 x5 x6 x7 x9 x11 x12 x13 x15 x16 x17 x28 x29 x30 x31 Hi OKi K.
  pose proof OKi as (El & E6 & E9 & DM & FC & FK).
  pose proof (dcsv_bit_range i Hi) as BR.
  pose proof (bv_unsigned_in_range 64 mask) as RM. change (bv_modulus 64) with (2^64) in RM.
  pose proof (dcsv_len i ltac:(lia)) as LP.
  unfold dst.
  (* and a0, a0, s3; beqz a0 *)
  step. rewrite (unsigned_lit (rate_bit (nth i closed_list 0))) by lia.
  step.
  pose proof (dcsv_land_range (rate_bit (nth i closed_list 0)) (bv_unsigned mask) ltac:(lia) ltac:(lia)) as LR.
  rewrite eqb_lit by lia. rewrite (csv_bit (bv_unsigned mask) i Hi).
  destruct (Z.testbit (bv_unsigned mask) (Z.of_nat i)) eqn:TB; cbn [negb].
  - (* bit set: mv a3, s7; beqz s2 (len = 0 keeps ""); else mv a3, s11 *)
    first [if_false | idtac].
    step. step. rewrite eqb_lit by lia.
    destruct (Z.eqb_spec len 0) as [L0|L0].
    + first [if_true | idtac].
      eapply (dcsv_set Q i len r6 r9 m F fc); [exact Hi | exact TB | exact OKi | | exact K].
      unfold sep_of. rewrite (proj2 (Z.eqb_eq len 0) L0). reflexivity.
    + first [if_false | idtac]. step.
      eapply (dcsv_set Q i len r6 r9 m F fc); [exact Hi | exact TB | exact OKi | | exact K].
      unfold sep_of. rewrite (proj2 (Z.eqb_neq len 0) L0). reflexivity.
  - (* bit clear: addi s6, s6, -1; addi s9, s9, 4; bnez s6 *)
    first [if_true | idtac].
    step. step. step. rewrite eqb_lit by lia.
    unfold dnext in K.
    destruct (Z.eqb_spec (r6 + -1) 0) as [Z0|Z0]; cbn [negb]; first [if_true | if_false | idtac];
      (eapply K; [first [right; split; lia | left; split; lia] |]).
    all: unfold dok; rewrite (csv_prefix_clear _ _ TB).
    all: split; [exact El|]; split; [lia|]; split; [lia|].
    all: split; [eapply dmem_same; [exact (csv_prefix_clear _ _ TB) | exact DM] | split; [exact FC | exact FK]].
Qed.


End Pass.
