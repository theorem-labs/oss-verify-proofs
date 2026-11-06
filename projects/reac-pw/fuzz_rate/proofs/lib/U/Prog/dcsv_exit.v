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

(** The exit of drivable_csv (UBSan 0x14efc .. 0x14f8c): buflen = 0 returns len at once; else copy =
    min(len, buflen - 1), memcpy(buf, tmp, copy) (0x14f24 -> 0x1d214), the trap tests 0x14f2c (buf + copy wraps),
    0x14f40 (buf <> 0 xor buf + copy = 0) and 0x14f48 (buf = 0) are not taken, the NUL store at buf + copy; then the
    epilogue restores ra, s0 .. s11 and returns len. *)

Section Exit.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mask : word) (S0 lo n buf : Z)
  (m0 : word -> option byte) (canary : word) (junk : list byte) (F0 : bvmap 5 word).
Hypothesis HK : lo + 6112 <= S0.
Hypothesis HI : 0x50cc8 <= lo.
Hypothesis H63 : S0 < 2^63.
Hypothesis Hn : 0 <= n <= 23.
Hypothesis HB0 : 0 < n -> 0 < buf /\ (buf + n <= lo \/ S0 <= buf).
Hypothesis HBR : 0 < n -> rw_cells rsegs m0 buf [CB (Z.to_nat n) junk].
Hypothesis TK0 : MemNorm.task_mem rsegs m0.
Hypothesis ST0 : stk rsegs m0 lo S0.
Hypothesis MCP : memcpy_contract.

Local Abbreviation SV := (dsv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Abbreviation OK := (dok S0 lo n buf mask SV m0 canary junk F0).
Local Abbreviation ST := (dst gp tp mask S0).
Local Abbreviation POST := (dpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 m0 lo S0 buf n
                          (csv_list (bv_unsigned mask))).

(** The epilogue (0x14f50 .. 0x14f8c): a0 = len, the 13 restores, the frame release, ret. *)
Lemma dcsv_epi : forall len r6 r9 m F fc
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  len = Z.of_nat (length (csv_list (bv_unsigned mask))) ->
  rw_cells rsegs m (S0 + -104) SV -> stk rsegs m lo S0 -> mem_inv rsegs m -> wmono rsegs m0 m ->
  MemNorm.task_mem rsegs m -> frm0 fc -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F k = reg_get F0 k) ->
  (n = 0 -> munch [(lo, S0)] m0 m) ->
  (0 < n -> munch [(lo, S0); (buf, buf + n)] m0 m /\
            bytes_at rsegs m buf (csv_bytes (csv_cut (csv_list (bv_unsigned mask)) n ++ [0]))) ->
  evt rsegs POST (ST 0x14f50 len r6 r9 F fc m x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
  intros len r6 r9 m F fc x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
    El FS STF MI WM TK FC FK H0 H1.
  subst len. unfold dst, dsv in *.
  do 16 step.
  finish.
Qed.

Lemma dcsv_frame : forall m j0, rw_cells rsegs m (S0 + -176) [CB 8 j0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 buf)] ->
  stk rsegs m lo (S0 + -176) -> stk rsegs m (S0 + -152) (S0 + -104) -> rw_cells rsegs m (S0 + -104) SV ->
  stk rsegs m lo S0.
Proof.
  intros m j0 FA STl SC FS.
  pose proof (stk_of_rw_cells rsegs m _ _ FA) as S1. pose proof (stk_of_rw_cells rsegs m _ _ FS) as S3.
  rewrite dsv_size in S3. cbn [cells_size csize Nat.add] in S1.
  replace (S0 + -176 + Z.of_nat 24) with (S0 + -152) in S1 by lia.
  replace (S0 + -104 + Z.of_nat 104) with S0 in S3 by lia.
  eapply stk_merge; [eapply stk_merge; [eapply stk_merge; [exact STl | exact S1 | lia] | exact SC | lia] | exact S3 | lia].
Qed.

(** buflen > 0: from 0x14f14 (s0 = copy) to the return. *)
Lemma dcsv_copy : forall copy len r6 r9 m F fc
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  0 < n -> copy = Z.min len (n - 1) -> OK 3 len r6 r9 m F fc ->
  evt rsegs POST (ST 0x14f14 len r6 r9 F fc m x1 x5 x6 x7 (Z_to_bv 64 copy) x9 x10 x11 x12 x13 x14 x15 x16 x17
                     x28 x29 x30 x31).
Proof.
  intros copy len r6 r9 m F fc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hn0 Ec OK3.
  destruct OK3 as (El & _ & _ & DM & FC & FK).
  destruct DM as (KP & STl & SC & BP & MI & WM & MU).
  destruct KP as ((j0 & FA) & FS & _ & _ & HBC).
  change (csv_prefix (bv_unsigned mask) 3) with (csv_list (bv_unsigned mask)) in *.
  set (L := csv_list (bv_unsigned mask)) in *.
  pose proof (csv_list_length (bv_unsigned mask) ltac:(pose proof (bv_unsigned_in_range 64 mask); lia)) as LL.
  fold L in LL.
  pose proof (HB0 Hn0) as (Hb0 & Hbl). pose proof (HBC Hn0) as RB.
  pose proof (rwc_stk _ _ _ _ RB) as SB. rewrite Z2Nat.id in SB by lia.
  pose proof SB as (_ & Hb64 & _).
  pose proof (dcsv_frame m j0 FA STl SC FS) as STF.
  assert (BS : bytes_at rsegs m (S0 + -136) (csv_bytes (csv_cut L n))).
  { rewrite csv_bytes_app in BP. apply bytes_at_app in BP. destruct BP as [BL _].
    unfold csv_cut. rewrite <- (firstn_skipn (Z.to_nat (Z.min (Z.of_nat (length L)) (n - 1))) L) in BL.
    rewrite csv_bytes_app in BL. apply bytes_at_app in BL. exact (proj1 BL). }
  assert (LS : length (csv_bytes (csv_cut L n)) = Z.to_nat copy).
  { rewrite csv_bytes_length, csv_cut_length by lia. subst copy. rewrite El. reflexivity. }
  destruct (stk_cb_at m buf (buf + n) buf (Z.to_nat copy) SB ltac:(lia) ltac:(lia)) as [jb RBc].
  clear SC BP HBC RB STl.
  unfold dst.
  (* addi a1, sp, 0x28; ld s1, 0x10(sp); mv a0, s1; mv a2, s0; jal memcpy *)
  step. step. step. step. step.
  eapply evt_cut.
  { eapply MCP with (src := csv_bytes (csv_cut L n)) (junk := jb).
    - rewrite unsigned_lit by lia. exact BS.
    - rewrite unsigned_lit by lia. exact LS.
    - rewrite !unsigned_lit by lia. exact RBc.
    - rewrite !unsigned_lit by lia. lia.
    - exact MI. }
  intros ms' PP. unfold memcpy_post in PP.
  destruct PP as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m2
                  & E & MU2 & WM2 & MI2 & RW2 & BY2).
  subst ms'. rewrite (ret_pc_even 0x14f28) by (first [lia | reflexivity]).
  rewrite !unsigned_lit in MU2, RW2 by lia.
  pose proof (rwc_cb _ _ _ _ RW2) as (_ & BYB).
  assert (FS2 : rw_cells rsegs m2 (S0 + -104) SV).
  { eapply rw_cells_tr; [exact FS | exact MU2 | exact WM2 |]. rewrite dsv_size.
    intros x Hx. cbn [outside]. lia. }
  assert (FA2 : rw_cells rsegs m2 (S0 + -176) [CB 8 j0; C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 buf)]).
  { eapply rw_cells_tr; [exact FA | exact MU2 | exact WM2 |]. cbn [cells_size csize Nat.add].
    intros x Hx. cbn [outside]. lia. }
  assert (STF2 : stk rsegs m2 lo S0).
  { eapply stk_tr; [exact STF | exact MU2 | exact WM2 |]. intros x Hx. left. cbn [outside]. lia. }
  assert (SB2 : stk rsegs m2 buf (buf + n)).
  { eapply stk_tr; [exact SB | exact MU2 | exact WM2 |]. intros x Hx.
    destruct (Z_lt_le_dec x (buf + copy)) as [X|X].
    - right. eapply bytes_at_mrd; [exact BYB | lia].
    - left. cbn [outside]. lia. }
  assert (MU' : munch [(lo, S0); (buf, buf + n)] m0 m2).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]];
      intros x Hx; cbn [outside] in *; lia. }
  pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM'.
  clear FS FA STF SB MU MU2 WM WM2 RW2 BY2 BS RBc.
  (* add s0, s1, s0; bltu s0, s1 (trap 0x14f2c) *)
  step. step. rewrite ltu_lit by lia. if_false.
  (* ld a0, 0x10(sp); snez a0, a0; seqz a1, s0; xor a0, a0, a1; beqz a0 (trap 0x14f40) *)
  step. step.
  replace (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 buf)) with (Z_to_bv 64 1)
    by (unfold v_sltu, c_ltu; rewrite ltu_lit by lia; rewrite (proj2 (Z.ltb_lt 0 buf)) by lia; reflexivity).
  step.
  replace (v_sltiu (Z_to_bv 64 (buf + copy)) 1) with (Z_to_bv 64 0)
    by (unfold v_sltiu; rewrite unsigned_lit by lia; change (bv_wrap 64 1) with 1;
        rewrite (proj2 (Z.ltb_ge (buf + copy) 1)) by lia; reflexivity).
  step. step. first [if_false | idtac].
  (* ld a0, 0x10(sp); beqz a0 (trap 0x14f48) *)
  step. step. rewrite eqb_lit by lia. first [if_false | idtac].
  (* sb zero, 0(s0) *)
  set (A2 := buf + copy) in *. assert (EA2 : A2 = buf + copy) by reflexivity. clearbody A2.
  destruct (stk_cb_at m2 buf (buf + n) A2 1 SB2 ltac:(lia) ltac:(lia)) as [j2 R2].
  pose proof (munch_refl [(A2, A2 + 1)] m2) as MU3. pose proof (wmono_refl rsegs m2) as WM3.
  assert (KEEP : rw_cells rsegs m2 (S0 + -104) SV /\ stk rsegs m2 lo S0 /\
                 bytes_at rsegs m2 buf (csv_bytes (csv_cut L n)) /\ munch [(lo, S0); (buf, buf + n)] m0 m2 /\
                 wmono rsegs m0 m2)
    by exact (conj FS2 (conj STF2 (conj BYB (conj MU' WM')))).
  clear FS2 STF2 BYB MU' WM' FA2 SB2.
  step. fix_zero_store.
  destruct KEEP as (FS3 & STF3 & BYB3 & MU3' & WM3').
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  destruct R2 as [[_ B2] _]. cbn [cells_bytes cbytes] in B2. rewrite app_nil_r in B2.
  assert (FS4 : rw_cells rsegs m3 (S0 + -104) SV).
  { eapply rw_cells_tr; [exact FS3 | exact MU3 | exact WM3 |]. rewrite dsv_size.
    intros x Hx. cbn [outside]. lia. }
  assert (STF4 : stk rsegs m3 lo S0).
  { eapply stk_tr; [exact STF3 | exact MU3 | exact WM3 |]. intros x Hx. left. cbn [outside]. lia. }
  assert (BYB4 : bytes_at rsegs m3 buf (csv_bytes (csv_cut L n))).
  { eapply bytes_at_tr; [exact BYB3 | exact MU3 |]. intros x Hx. rewrite LS in Hx. cbn [outside]. lia. }
  assert (MU4 : munch [(lo, S0); (buf, buf + n)] m0 m3).
  { eapply munch_trans; [exact MU3' | eapply munch_weaken; [| exact MU3]].
    intros x Hx; cbn [outside] in *; lia. }
  pose proof (wmono_trans rsegs _ _ _ WM3' WM3) as WM4.
  pose proof (dcsv_task2 m0 m3 lo S0 buf n junk TK0 ST0 (HBR Hn0) ltac:(lia) MU4) as TK4.
  eapply dcsv_epi; [exact El | exact FS4 | exact STF4 | assumption | exact WM4 | exact TK4 | exact FC | exact FK
                   | intros H0; exfalso; lia |].
  intros _. split; [exact MU4|].
  rewrite csv_bytes_app. apply bytes_at_app. split; [exact BYB4|].
  fold L. rewrite LS. replace (buf + Z.of_nat (Z.to_nat copy)) with A2 by lia. exact B2.
Qed.

(** From the loop's exit (0x14efc, i = 3) to the return. *)
Lemma dcsv_exit : forall len r6 r9 m F fc
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  OK 3 len r6 r9 m F fc ->
  evt rsegs POST (ST 0x14efc len r6 r9 F fc m x1 x5 x6 x7 (Z_to_bv 64 96000) x9 x10 x11 x12 x13 x14 x15 x16 x17
                     x28 x29 x30 x31).
Proof.
  intros len r6 r9 m F fc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 OK3.
  pose proof OK3 as (El & _ & _ & DM & FC & FK).
  destruct DM as (KP & STl & SC & BP & MI & WM & MU). destruct KP as ((j0 & FA) & FS & _ & _ & _).
  change (csv_prefix (bv_unsigned mask) 3) with (csv_list (bv_unsigned mask)) in El.
  pose proof (csv_list_length (bv_unsigned mask) ltac:(pose proof (bv_unsigned_in_range 64 mask); lia)) as LL.
  unfold dst.
  (* ld a0, 8(sp); beqz a0 *)
  step. step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec n 0) as [N0|N0].
  - first [if_true | idtac].
    eapply dcsv_epi; [exact El | exact FS | eapply dcsv_frame; eassumption | exact MI | exact WM
                     | eapply dcsv_task; [exact TK0 | exact ST0 | exact MU] | exact FC | exact FK
                     | intros _; exact MU | intros H; exfalso; lia].
  - first [if_false | idtac].
    (* addi a0, a0, -1; mv s0, s2; bltu s2, a0, 8 (mv s0, a0 when len >= buflen - 1) *)
    step. step. step. rewrite ltu_lit by lia.
    destruct (Z.ltb_spec len (n + -1)) as [C|C].
    + first [if_true | idtac]. eapply (dcsv_copy len len); [lia | lia | exact OK3].
    + first [if_false | idtac]. step. eapply (dcsv_copy (n + -1) len); [lia | lia | exact OK3].
Qed.

End Exit.
