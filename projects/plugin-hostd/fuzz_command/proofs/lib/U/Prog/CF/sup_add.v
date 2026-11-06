(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_canonical.v, with its module paths and module names changed; 696 of its 835 lines of code are new or changed and 2224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v, with its addresses and numbers changed; 1646 of its 1730 lines of code are new or changed and 751 lines of the source are left out. *)
From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import printf_facts_c snprintf_c mix_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecAns.
Import ListNotations.
Open Scope Z_scope.

Definition sa_sel (u : word) : word := if Z.eqb (bv_unsigned u) 0 then Z_to_bv 64 0x108b0 else u.

Lemma sa_pf_dec : forall v, -2^31 <= v < 2^31 -> pf_bytes (pf_dec v) = dec v.
Proof.
  intros c Hc. unfold pf_dec, dec. unfold pf_bytes.
  assert (P : 10 ^ Z.of_nat (S 9) = 10000000000) by reflexivity.
  destruct (Z.ltb_spec c 0) as [N|N].
  - cbn [map app]. f_equal. replace (Z.abs c) with (- c) by lia.
    exact (pf_digits_digits 9 11 (- c) [] ltac:(rewrite P; lia) ltac:(lia)).
  - cbn [app]. replace (Z.abs c) with c by lia.
    exact (pf_digits_digits 9 11 c [] ltac:(rewrite P; lia) ltac:(lia)).
Qed.

Definition SA_FMT : list Z := [37; 100].
Definition SA_PS : list pf_piece := [Pd].

Lemma sa_parse : pf_parse SA_FMT = Some SA_PS.
Proof. reflexivity. Qed.

Lemma sa_text : forall v, pf_text SA_PS [AInt v] = Some (pf_dec v).
Proof. intros v. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma sa_fmt_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10828 (pf_bytes (SA_FMT ++ [0])).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma sa_sx32_lit : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma sa_rf_nz : forall rf, -2 ^ 31 <= rf < 2 ^ 31 -> rf <> 0 -> bv_eqb (Z_to_bv 64 rf) (Z_to_bv 64 0) = false.
Proof.
  intros rf Hr N. unfold bv_eqb. apply Z.eqb_neq. rewrite !unsigned_lit_wrap.
  change (2 ^ 64) with 18446744073709551616. rewrite Zmod_0_l. intros H.
  apply Z.mod_divide in H; [|lia]. destruct H as [k Hk]. lia.
Qed.

Lemma sa_srl : forall id, -2^31 <= id < 2^31 ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 id))) 4) = (id mod 2^32) / 16.
Proof.
  intros id H. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32). change (bv_modulus 64) with (2^64).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  Z.div_mod_to_equations. lia.
Qed.

Lemma sa_run0 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 80 <= bv_unsigned sp -> 2 ^ 21 <= lo ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16034) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2 a1 s1 (Z_to_bv 64 0)
                     a1 a2 a3 a4 a5 a6 a7 a3 a2 a0 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16000) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 48%nat junk [] [8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 13 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  split; [eassumption|]. split; eassumption.
Qed.

Lemma sa_run1 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16040) sp gp tp t0 t1 t2 s0 a0 a0 s4 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16034) fc None m (seg_rom rsegs)).
Proof. intros. do 3 step. apply evt_done. reflexivity. Qed.

Definition sa_mid2 (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo v e : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' slack,
    ms' = MS (mkR (Z_to_bv 64 0x16064) sp gp tp t0 t1 t2 (Z_to_bv 64 v) (Z_to_bv 64 e) (Z_to_bv 64 e)
                  sp a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 0x161c4) fc' None m' (seg_rom rsegs)
    /\ munch [(lo, bv_unsigned sp + 16)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
    /\ length slack = (15 - length (dec v))%nat
    /\ bytes_at rsegs m' (bv_unsigned sp) (dec v ++ Z_to_bv 8 0 :: slack).

Lemma sa_run2 : snprintf_contract ->
  forall ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo v e : Z) (canary : word),
  -2^31 <= v < 2^31 ->
  stk rsegs m lo (bv_unsigned sp + 16) -> lo + SNPRINTF_K <= bv_unsigned sp -> 2 ^ 21 <= lo ->
  bv_unsigned sp + 16 < 2^63 ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  evt rsegs (sa_mid2 sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo v e m)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 v) (Z_to_bv 64 e) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x16040) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v e canary HV ST LO IE S63 FRM MI TM GG GW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold SNPRINTF_K, IMG_END, GOT_GUARD, GUARD in *.
  pose proof (dec_length v HV) as DL.
  pose proof (sa_pf_dec v HV) as PD.
  assert (TL : length (pf_dec v) = length (dec v)) by (rewrite <- PD; unfold pf_bytes; rewrite length_map; reflexivity).
  carve_frame 16%nat ST.
  match type of ST with stk _ _ _ ?h => replace h with (bv_unsigned sp) in ST by lia end.
  match type of FR with rw_cells _ _ ?h _ => replace h with (bv_unsigned sp) in FR by lia end.
  do 6 step.
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
  assert (BJ : bytes_at rsegs m (bv_unsigned sp) junk).
  { destruct FR as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_bound _ _ _ _ BJ) as BJL.
  assert (JL : length junk = 16%nat) by (destruct FR as [[[HJ _] _] _]; exact HJ).
  eapply evt_cut.
  { eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo canary SA_FMT SA_PS
              [AInt v] (pf_dec v) junk).
    - rewrite unsigned_lit by lia. apply sa_fmt_at. exact MI.
    - rewrite unsigned_lit by lia. unfold RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold RO_END, SA_FMT. cbn [length]. lia.
    - exact sa_parse.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact HV | apply lit_mod32].
    - exact (sa_text v).
    - rewrite !unsigned_lit by lia. exact FR.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - lia.
    - rewrite !unsigned_lit by lia. right. lia.
    - rewrite !unsigned_lit by lia. apply pf_img_free_hi. lia.
    - exact ST.
    - unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - lia.
    - exact FRM.
    - exact MI.
    - exact TM.
    - exact GG.
    - exact GW. }
  intros ms' PO. unfold printf_post in PO.
  destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Ft & fc' & m2
    & -> & MU2 & WM2 & MI2 & TM2 & FRM2 & FK & ST2 & BT).
  rewrite !unsigned_lit in MU2, BT by lia.
  change (Z.to_nat (16 - 1)) with 15%nat in BT, MU2.
  rewrite (firstn_all2 (n := 15%nat)) in MU2, BT by lia.
  replace (ret_pc (Z_to_bv 64 0x16058)) with (Z_to_bv 64 0x16058) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct (bytes_at_firstn_skipn _ _ _ _ (S (length (pf_dec v))) BJ) as [_ BJT].
  rewrite firstn_length_le in BJT by lia.
  assert (BJT2 : bytes_at rsegs m2 (bv_unsigned sp + Z.of_nat (S (length (pf_dec v))))
                   (skipn (S (length (pf_dec v))) junk)).
  { apply (bytes_at_transport rsegs _ m m2 _ _ BJT MU2). cbn [disjoint_from]. rewrite length_skipn.
    split; [lia | split; [lia | exact I]]. }
  assert (PB : pf_bytes (pf_dec v ++ [0]) = dec v ++ [Z_to_bv 8 0]).
  { unfold pf_bytes. rewrite map_app. change (map (Z_to_bv 8) (pf_dec v)) with (pf_bytes (pf_dec v)).
    rewrite PD. reflexivity. }
  rewrite PB in BT.
  assert (BUF : bytes_at rsegs m2 (bv_unsigned sp) (dec v ++ Z_to_bv 8 0 :: skipn (S (length (pf_dec v))) junk)).
  { replace (dec v ++ Z_to_bv 8 0 :: skipn (S (length (pf_dec v))) junk) with
      ((dec v ++ [Z_to_bv 8 0]) ++ skipn (S (length (pf_dec v))) junk)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BT|]. rewrite length_app, <- TL. cbn [length].
    replace (Z.of_nat (length (pf_dec v) + 1)) with (Z.of_nat (S (length (pf_dec v)))) by lia. exact BJT2. }
  clear BT BJT BJT2 BJ BJL FR.
  do 3 step.
  apply evt_done. unfold sa_mid2.
  do 16 eexists. exists (skipn (S (length (pf_dec v))) junk). split; [reflexivity|].
  split.
  { eapply munch_weaken; [|exact MU2].
    unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | split; [lia | exact I]]. }
  split; [exact WM2|].
  split; [exact MI2|]. split; [exact FRM2|]. split; [exact FK|].
  split; [rewrite length_skipn, JL, TL; lia|].
  exact BUF.
Qed.

Lemma sa_run3 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' =>
       ms' = MS (mkR (Z_to_bv 64 0x16080) sp gp tp t0 t1 t2 s0 s1 s1 (sa_sel s3) a2 a3 a4 a5 a6 a7
                     s2 s3 (Z_to_bv 64 0x108b0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16064) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 4 step.
  destruct (Z.eq_dec (bv_unsigned s3) 0) as [Z1|Z1].
  - if_true. do 2 step.
    unfold sa_sel. rewrite (proj2 (Z.eqb_eq _ _) Z1).
    apply evt_done. reflexivity.
  - if_false. do 3 step.
    unfold sa_sel. rewrite (proj2 (Z.eqb_neq _ _) Z1).
    apply evt_done. reflexivity.
Qed.

Lemma sa_run4 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' =>
       ms' = MS (mkR (Z_to_bv 64 0x16094) sp gp tp t0 t1 t2 s0 s1 s1 (sa_sel s2) a2 a3 a4 a5 a6 a7
                     s2 s3 (sa_sel s2) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0x108b0) s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x16080) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  step.
  destruct (Z.eq_dec (bv_unsigned s2) 0) as [Z1|Z1].
  - if_true. do 3 step.
    unfold sa_sel. rewrite (proj2 (Z.eqb_eq _ _) Z1).
    apply evt_done. reflexivity.
  - if_false. do 4 step.
    unfold sa_sel. rewrite (proj2 (Z.eqb_neq _ _) Z1).
    apply evt_done. reflexivity.
Qed.

Lemma sa_seg_rng :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (id : Z),
  0 <= id < 10000 ->
  evt rsegs (fun ms' => exists b0 b1,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 id) s1 b0 b1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x160b8) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 id) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x16094) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m id HI.
  do 2 step.
  rewrite (sa_srl id) by lia.
  replace ((id mod 2^32) / 16) with (id / 16) by (rewrite Z.mod_small by lia; reflexivity).
  assert (Q : 0 <= id / 16 < 625) by (Z.div_mod_to_equations; lia).
  step.
  unfold bv_ltu. rewrite (unsigned_lit (id / 16)) by lia.
  if_true.
  apply evt_done. do 2 eexists. reflexivity.
Qed.

Lemma sa_seg_oor :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (id : Z),
  -2^31 <= id < 2^31 -> ~ (0 <= id < 10000) ->
  evt rsegs (fun ms' =>
       ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 id) s1 sp (Z_to_bv 64 32)
                     (Z_to_bv 64 0x10982) (Z_to_bv 64 (-1)) a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16100) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 id) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x16094) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m id HB HI.
  do 2 step.
  rewrite (sa_srl id) by lia.
  assert (Q : 625 <= (id mod 2^32) / 16 < 2^28) by (Z.div_mod_to_equations; lia).
  step.
  unfold bv_ltu. rewrite (unsigned_lit ((id mod 2^32) / 16)) by lia.
  if_false.
  do 6 step.
  apply evt_done. reflexivity.
Qed.

Lemma sa_seg_ref :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (rf : Z),
  rw_cells rsegs m 0x34028 [C4 (Z_to_bv 64 rf)] -> -2 ^ 31 <= rf < 2 ^ 31 -> rf <> 0 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x160d8) sp gp tp t0 t1 t2 s0 s1 s1 (Z_to_bv 64 0) (Z_to_bv 64 0)
                     a3 a4 a5 a6 a7 (Z_to_bv 64 0x33ff0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16310) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x160b8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m rf RC Hrf Nrf.
  do 4 step. rewrite sa_sx32_lit by lia. rewrite (sa_rf_nz rf Hrf Nrf). cbv iota.
  do 4 step.
  apply evt_done. reflexivity.
Qed.

Lemma sa_run_mix : mix_call_contract ->
  forall ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo e h fn : Z) (args : list (word * list byte)) (sp1 : word),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp1) -> lo + 96 <= bv_unsigned sp1 -> 0x343e0 <= lo ->
  rw_cells rsegs m 0x34028 [C4 (Z_to_bv 64 0)] ->
  bytes_at rsegs m e (le4 (Z_to_bv 64 fn) ++ le4 (Z_to_bv 64 (Z.of_nat (length args)))) ->
  -2^31 <= fn < 2^31 -> 0 < e -> e mod 8 = 0 -> e + 56 <= 0x343d8 -> (length args <= 6)%nat ->
  (forall k p, nth_error args k = Some p -> mc_arg m (bv_unsigned sp1 - 96) (bv_unsigned sp1) e k p) ->
  rw_cells rsegs m 0x343d8 [C8 (Z_to_bv 64 h)] -> 0 <= h < 2 ^ 64 ->
  evt rsegs (fun ms' => exists t0' t1' t2' b4 b5 b6 b7 t3' t4' t5' t6' m',
       ms' = MS (mkR (Z_to_bv 64 0x160e8) sp1 gp tp t0' t1' t2' s0 (Z_to_bv 64 e)
                     sp1 (Z_to_bv 64 32) (Z_to_bv 64 0x10982) s0 b4 b5 b6 b7
                     (Z_to_bv 64 0x33ff0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x16100) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp1 - 96, bv_unsigned sp1); (0x343d8, 0x343e0)] m m'
       /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x343d8 [C8 (Z_to_bv 64 (mixcall h fn (map snd args)))])
    (MS (mkR ra sp1 gp tp t0 t1 t2 s0 (Z_to_bv 64 e) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x160b8) fc None m (seg_rom rsegs)).
Proof.
  intros MIX ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo e h fn args sp1 MI ST LO LO2 RC EF HFN E0 E8 E56 LA HARG ES Hh.
  assert (MIX' := MIX). unfold mix_call_contract, MIX_CALL_FRAME in MIX'.
  pose proof (bv_unsigned_in_range 64 sp1) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp1 - 96, bv_unsigned sp1); (0x343d8, 0x343e0)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step. try (rewrite sa_sx32_lit by lia). if_true.
  do 3 step.
  call (MIX' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo fn args).
  - exact MI.
  - exact ST.
  - lia.
  - exact HFN.
  - exact LA.
  - rewrite unsigned_lit by lia. exact EF.
  - rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. exact E8.
  - intros k p Hk. rewrite unsigned_lit by lia. exact (HARG k p Hk).
  - eapply ro_bytes_at; [exact MI | unfold FNV_B0_ADDR; lia | rewrite length_le8; unfold FNV_B0_ADDR; lia |].
    apply ro_bytes_b_sound. vm_compute. reflexivity.
  - unfold FNV_B0_ADDR. lia.
  - rewrite (unsigned_lit h) by lia.
    do 6 step.
    apply evt_done. do 12 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Definition sa_mid (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo v : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' slack,
    ms' = MS (mkR (Z_to_bv 64 0x1610c) sp gp tp t0 t1 t2 s0 s1
                  sp a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 0x16284) fc' None m' (seg_rom rsegs)
    /\ munch [(lo, bv_unsigned sp + 32)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
    /\ length slack = (31 - length (resp v))%nat
    /\ bytes_at rsegs m' (bv_unsigned sp) (resp v ++ Z_to_bv 8 0 :: slack).

Lemma sa_run_snp : snprintf_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo v : Z) (canary : word),
  -2^31 <= v < 2^31 ->
  stk rsegs m lo (bv_unsigned sp + 32) -> lo + SNPRINTF_K <= bv_unsigned sp -> 2 ^ 21 <= lo ->
  bv_unsigned sp + 32 <= TASK_SIZE ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  evt rsegs (sa_mid sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo v m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 sp (Z_to_bv 64 32) (Z_to_bv 64 0x10982)
             (Z_to_bv 64 v) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16100) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v canary HV ST LO IE HTS FRM MI TM GG GW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold SNPRINTF_K, TASK_SIZE in *.
  pose proof (munch_refl [(lo, bv_unsigned sp + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  rewrite ?Z.add_0_r in ST, FR.
  pose proof (resp_len v HV) as RL.
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
  assert (BJ : bytes_at rsegs m (bv_unsigned sp) junk).
  { destruct FR as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_bound _ _ _ _ BJ) as BJL.
  assert (JL : length junk = 32%nat) by (destruct FR as [[[HJ _] _] _]; exact HJ).
  step.
  eapply evt_cut.
  { eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo canary RESP_FMT RESP_PS
              [AInt v] (RESP_HEAD ++ pf_dec v) junk).
    - rewrite unsigned_lit by lia. apply resp_fmt_at. exact MI.
    - rewrite unsigned_lit by lia. unfold RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold RO_END, RESP_FMT. cbn [length]. lia.
    - exact resp_parse.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact HV | apply lit_mod32].
    - exact (resp_text v).
    - rewrite !unsigned_lit by lia. exact FR.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - lia.
    - rewrite !unsigned_lit by lia. right. lia.
    - rewrite !unsigned_lit by lia. apply pf_img_free_hi. lia.
    - exact ST.
    - unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - lia.
    - exact FRM.
    - exact MI.
    - exact TM.
    - exact GG.
    - exact GW. }
  intros ms' PO. unfold printf_post in PO.
  destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Ft & fc' & m2
    & -> & MU2 & WM2 & MI2 & TM2 & FRM2 & FK & ST2 & BT).
  rewrite !unsigned_lit in MU2, BT by lia.
  change (Z.to_nat (32 - 1)) with 31%nat in BT, MU2.
  rewrite (firstn_all2 (n := 31%nat)) in MU2, BT by lia.
  replace (ret_pc (Z_to_bv 64 0x16104)) with (Z_to_bv 64 0x16104) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct (bytes_at_firstn_skipn _ _ _ _ (S (length (RESP_HEAD ++ pf_dec v))) BJ) as [_ BJT].
  rewrite firstn_length_le in BJT by lia.
  assert (BJT2 : bytes_at rsegs m2 (bv_unsigned sp + Z.of_nat (S (length (RESP_HEAD ++ pf_dec v))))
                   (skipn (S (length (RESP_HEAD ++ pf_dec v))) junk)).
  { apply (bytes_at_transport rsegs _ m m2 _ _ BJT MU2). cbn [disjoint_from]. rewrite length_skipn.
    split; [lia | split; [lia | exact I]]. }
  assert (PB : pf_bytes ((RESP_HEAD ++ pf_dec v) ++ [0]) = resp v ++ [Z_to_bv 8 0]).
  { unfold pf_bytes. rewrite map_app. change (map (Z_to_bv 8) (RESP_HEAD ++ pf_dec v)) with
      (pf_bytes (RESP_HEAD ++ pf_dec v)). rewrite pf_resp by exact HV. reflexivity. }
  assert (LR : length (resp v) = length (RESP_HEAD ++ pf_dec v)).
  { rewrite <- (pf_resp v HV). unfold pf_bytes. apply length_map. }
  rewrite PB in BT.
  assert (BUF : bytes_at rsegs m2 (bv_unsigned sp)
                  (resp v ++ Z_to_bv 8 0 :: skipn (S (length (RESP_HEAD ++ pf_dec v))) junk)).
  { replace (resp v ++ Z_to_bv 8 0 :: skipn (S (length (RESP_HEAD ++ pf_dec v))) junk) with
      ((resp v ++ [Z_to_bv 8 0]) ++ skipn (S (length (RESP_HEAD ++ pf_dec v))) junk)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BT|]. rewrite length_app, LR. cbn [length].
    replace (Z.of_nat (length (RESP_HEAD ++ pf_dec v) + 1))
      with (Z.of_nat (S (length (RESP_HEAD ++ pf_dec v)))) by lia. exact BJT2. }
  clear BT BJT BJT2 BJ BJL FR.
  do 2 step.
  apply evt_done. unfold sa_mid.
  do 17 eexists. exists (skipn (S (length (RESP_HEAD ++ pf_dec v))) junk). split; [reflexivity|].
  split.
  { eapply munch_weaken; [|exact MU2]. intros x Hx. cbn [outside] in Hx |- *. lia. }
  split; [exact WM2|]. split; [exact MI2|]. split; [exact FRM2|]. split; [exact FK|].
  split; [rewrite length_skipn, JL, LR; lia|]. exact BUF.
Qed.

Lemma sa_seg_epi :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 s03 s04 : word),
  rw_cells rsegs m (bv_unsigned sp0 + -48) [C8 s04; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  80 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 a0 a1 a2 a3 a4 a5 a6 a7
                     s02 s03 s04 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra0) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1610c) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 s03 s04 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 8 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 + -80 + 80)) with sp0
    by (replace (bv_unsigned sp0 + -80 + 80) with (bv_unsigned sp0) by ring; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Lemma sa_seg_ansret :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 s03 s04 : word),
  rw_cells rsegs m (bv_unsigned sp0 + -48) [C8 s04; C8 s03; C8 s02; C8 s01; C8 s00; C8 ra0] ->
  80 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 a0 a1 a2 a3 a4 a5 a6 a7
                     s02 s03 s04 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra0) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x160d8) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 s03 s04 FR SPR.
  step.
  exact (sa_seg_epi ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m sp0 ra0 s00 s01 s02 s03 s04 FR SPR).
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01 YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecKindB RecSeq RecStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecGlue RecTail RecAnsB RecStubU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import xmalloc_c record_c arg_s_c answer_c hand_back_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require sup_remove.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Local Open Scope Z_scope.

Definition sa_kx (xs : list Z) (R R' : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> ~ In r xs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).

Lemma sa_kx_trans : forall xs R1 R2 R3, sa_kx xs R1 R2 -> sa_kx xs R2 R3 -> sa_kx xs R1 R3.
Proof. intros xs R1 R2 R3 H1 H2 r Hr N. rewrite (H2 r Hr N). exact (H1 r Hr N). Qed.

Lemma sa_kx_of_pres : forall xs R R', regs_preserved R R' -> sa_kx xs R R'.
Proof. intros xs R R' H r Hr _. exact (H r Hr). Qed.

Lemma sa_kx_pres : forall xs R R', sa_kx xs R R' ->
  (forall r, In r xs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) -> regs_preserved R R'.
Proof.
  intros xs R R' K E r Hr. destruct (in_dec Z.eq_dec r xs) as [H|H]; [exact (E r H) | exact (K r Hr H)].
Qed.

Ltac sa_kx_one X :=
  first [ exfalso; match goal with N : ~ In _ _ |- _ => apply N end; cbn [In]; lia
        | match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
          simp_regs; first [reflexivity | unfold getr; reflexivity] ].

Ltac sa_kx_tac X :=
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in let Nrr := fresh "Nrr" in
  intros rr Hrr Nrr; unfold callee_saved in Hrr;
  assert (CC : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
               rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr;
  repeat (destruct CC as [CC|CC]; [subst rr; sa_kx_one X|]);
  subst rr; sa_kx_one X.

Lemma sa_cell4 : forall m a v, GLOB_LO <= a -> a + 4 <= GLOB_LO + Z.of_nat GLOB_N ->
  bytes_at rsegs m a (le4 v) -> rw_cells rsegs m a [C4 v].
Proof.
  intros m a v H1 H2 H. apply (rw_cells_same_bytes _ _ [CB (length (le4 v)) (le4 v)]).
  - apply bytes_rw_cells; [lia | rewrite length_le4; lia | exact H].
  - cbn. split; exact I.
  - cbn [cells_bytes cbytes]. reflexivity.
  - cbn [cells_size csize]. rewrite length_le4. reflexivity.
Qed.

Lemma sa_combine_snd : forall (X Y : Type) (l1 : list X) (l2 : list Y), length l1 = length l2 ->
  map snd (combine l1 l2) = l2.
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H |- *;
    [reflexivity | discriminate | discriminate | rewrite (IH l2 ltac:(lia)); reflexivity].
Qed.

Lemma sa_nth_combine : forall (X Y : Type) (l1 : list X) (l2 : list Y) k a b,
  nth_error (combine l1 l2) k = Some (a, b) -> nth_error l1 k = Some a /\ nth_error l2 k = Some b.
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] [|k] a b H; cbn in H |- *; try discriminate.
  - injection H as -> ->. split; reflexivity.
  - exact (IH l2 k a b H).
Qed.

Definition sa_m (R : rstate) (As : list (list byte)) (id : Z) : rstate * list byte :=
  let R1 := rec_record R REC_ADD As in
  if (id <? 0) || (10000 <=? id) then hand_back R1 (resp (-1))
  else if negb (r_refuse R1 =? 0) then hand_back R1 (resp (r_code R1))
  else hand_back (rec_mix R1 (REC_ADD, As)) (resp id).

Definition sa_rom_chk (a : Z) (bs : list byte) : bool :=
  forallb (fun i => ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat i)) &&
     match PropExec.seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)), nth_error bs i with
     | Some b, Some c => Z.eqb (bv_unsigned b) (bv_unsigned c)
     | _, _ => false
     end) (seq 0 (length bs)).

Lemma sa_rom_bytes : forall m a bs, ro_agree rsegs m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  sa_rom_chk a bs = true -> bytes_at rsegs m a bs.
Proof.
  intros m a bs RA H0 H1 C. split; [lia|]. split; [lia|]. intros i Hi. unfold sa_rom_chk in C.
  pose proof (proj1 (forallb_forall _ _) C i ltac:(apply in_seq; lia)) as Ci. cbv beta in Ci.
  apply andb_prop in Ci as [Cr Cv]. unfold wa. rewrite (RA _ Cr).
  destruct (PropExec.seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i))) as [b|]; [|discriminate].
  destruct (nth_error bs i) as [c|]; [|discriminate].
  apply Z.eqb_eq in Cv. f_equal. apply bv_eq. exact Cv.
Qed.

Lemma sa_sel_nz : forall p, 0 <= p < 2 ^ 64 -> p <> 0 -> bv_unsigned (sa_sel (Z_to_bv 64 p)) = p.
Proof.
  intros p Hp N. unfold sa_sel. rewrite (unsigned_lit p) by lia. rewrite (proj2 (Z.eqb_neq _ _) N).
  apply unsigned_lit. lia.
Qed.

Lemma sa_sel_z : bv_unsigned (sa_sel (Z_to_bv 64 0)) = 0x108b0.
Proof. vm_compute. reflexivity. Qed.

Section H.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis GRD : ms_guard B = 0x54730.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis SNP : snprintf_contract.
Hypothesis HB : forall fx0 : YK11.FPState, @hand_back_contract fx0 rc B API.
Hypothesis MIX : mix_call_contract.
Hypothesis ANSF : forall fx0 : YK11.FPState, @answer_contract fx0 rc B API.

Definition sa_tret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (O : list (Z * Z)) (R' : rstate) (t : list byte) (b bpre : sbound) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' O' q,
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    fp_kept fx fx' /\
    call_post_rec B (aa_MR API) SUP_ADD_K L A regs mem md rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 q /\
    g_rec_rep (ms_segs B) L' A' mem' R' O' /\ owns_new L A O O' /\
    (forall pn, In pn (blocks L' A') ->
       (In pn (blocks L A) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
    In (q, Z.of_nat (length t) + 1) (blocks L' A') /\ fresh_block B q (Z.of_nat (length t) + 1) /\
    ~ In q (map fst O') /\
    Mem.bytes_at (ms_segs B) mem' q (t ++ [Z_to_bv 8 0]) /\
    others_kept (ms_segs B) L A mem L' A' mem' O /\
    (forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
       ptr_addr L p + k <= q \/ q + Z.of_nat (length t) + 1 <= ptr_addr L p) /\
    ro_agree (ms_segs B) mem' /\ f18_words (ms_segs B) mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    sb_le (sb_shift b A A') (sb_malloc (sb_malloc bpre (Z.of_nat (length t) + 1)) (Z.of_nat (length t) + 1)) /\
    res_ok_slots A' (sb_shift b A A').

Ltac sa_pres X5 PR2 X1 KT R1 :=
  match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X5 eq_refl); simp_regs;
    first [ reflexivity
          | transitivity (getr R1 (Z_to_bv 5 k)); [exact (PR2 k ltac:(unfold callee_saved; lia))|];
            rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X1 eq_refl); simp_regs;
            exact (KT k ltac:(unfold callee_saved; lia) ltac:(cbn [In]; lia)) ]
  end.

Lemma sa_resp : forall L A regs mem md O Lc Ac mc mdc Rc Oc bc bpre regs1 v,
  call_pre_t B API SUP_ADD_K L A regs mem md ->
  sinv B API SUP_ADD_K (spZ regs) L A mem md O Lc Ac mc mdc Rc Oc bc ->
  getr regs1 2 = Z_to_bv 64 (spZ regs - 80) -> getr regs1 10 = Z_to_bv 64 (spZ regs - 80) ->
  getr regs1 11 = Z_to_bv 64 32 -> getr regs1 12 = Z_to_bv 64 0x10982 -> getr regs1 13 = Z_to_bv 64 v ->
  -2^31 <= v < 2^31 ->
  sa_kx [2; 8; 9; 18; 19; 20] regs regs1 ->
  rw_cells rsegs mc (spZ regs - 48)
    [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  frm_zero fp_csr -> sb_le (sb_shift bc A Ac) bpre ->
  room_ag (sb_malloc (sb_malloc (sb_shift bc A Ac) (Z.of_nat (length (resp v)) + 1))
                (Z.of_nat (length (resp v)) + 1)) (Z.of_nat (length (resp v)) + 1) ->
  SR rsegs (mkCfg (mkst regs1 (Z_to_bv 64 0x16100) mc (seg_rom rsegs)) mdc)
    (sa_tret L A regs mem md O (fst (hand_back Rc (resp v))) (resp v) bc bpre).
Proof using SEGS ERRNO_LOW GOTG GRD GOWN AX CTX SNP HB.
  intros L A regs mem md O Lc Ac mc mdc Rc Oc bc bpre regs1 v PRE SI E2 E10 E11 E12 E13 HV KT FR FRM BLE ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & HTS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_ADD_K in HCEIL, HWS. unfold TASK_SIZE in HTS.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  pose proof RJ as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  destruct (mr_model B _ LAWS Lc Ac mc mdc HM) as (Hh & Hl & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (resp_length v HV) as RL.
  pose proof F18 as (GG & canary & GW).
  assert (GGb : bytes_at rsegs mc snprintf_c.GOT_GUARD (le8 (Z_to_bv 64 snprintf_c.GUARD))).
  { destruct GG as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GWb : bytes_at rsegs mc snprintf_c.GUARD (le8 canary)).
  { destruct GW as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (ST0 : stk rsegs (normalize_cj rsegs mc) (bv_unsigned sp - 12464)
                  (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 80)) + 32)).
  { rewrite unsigned_lit by lia. apply stk_normalize_cj; [lia | unfold TASK_SIZE; lia |].
    intros a Ha. rewrite <- SEGS. apply HSC. left. unfold SUP_ADD_K. lia. }
  pose proof (bytes_at_normalize_cj_low rsegs mc snprintf_c.GOT_GUARD (le8 (Z_to_bv 64 snprintf_c.GUARD)) RA
    ltac:(rewrite length_le8; unfold snprintf_c.GOT_GUARD, TASK_SIZE; lia) GGb) as GGn.
  pose proof (bytes_at_normalize_cj_low rsegs mc snprintf_c.GUARD (le8 canary) RA
    ltac:(rewrite length_le8; unfold snprintf_c.GUARD, TASK_SIZE; lia) GWb) as GWn.
  assert (Q2 : reg_get regs1 2 = Z_to_bv 64 (bv_unsigned sp - 80)) by exact E2.
  assert (Q10 : reg_get regs1 10 = Z_to_bv 64 (bv_unsigned sp - 80)) by exact E10.
  assert (Q11 : reg_get regs1 11 = Z_to_bv 64 32) by exact E11.
  assert (Q12 : reg_get regs1 12 = Z_to_bv 64 0x10982) by exact E12.
  assert (Q13 : reg_get regs1 13 = Z_to_bv 64 v) by exact E13.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q2, Q10, Q11, Q12, Q13.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RA |].
    eapply (sa_run_snp SNP) with (lo := bv_unsigned sp - 12464) (canary := canary);
      [exact HV | exact ST0 | rewrite unsigned_lit by lia; unfold SNPRINTF_K; lia | lia
      | rewrite unsigned_lit by lia; unfold TASK_SIZE; lia | exact FRM
      | exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs mc))
      | exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs mc)) | exact GGn | exact GWn]. }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F1 & fc1 & m1n
    & slack & -> & MU1n & WM1n & MI1n & FRM1 & FK1 & SL & BUF1n).
  destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ (mem_rel_cj_normalize rsegs mc RA) MR1r RO1 MU1n) as MU1.
  pose proof (wmono_rel_cj rsegs _ _ _ _ (mem_rel_cj_normalize rsegs mc RA) MR1r RO1 WM1n) as WM1.
  pose proof (ro_agree_same_cj rsegs _ _ RA RO1) as RA1.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR1r BUF1n) as BUF1.
  destruct (CF.RecAnsB.eqv_mkst_fx _ _ _ _ _ _ _ EQ1) as (R1 & -> & X1).
  clear MU1n WM1n MI1n BUF1n EQ1 MR1r.
  rewrite (unsigned_lit (bv_unsigned sp - 80)) in MU1, BUF1 by lia.
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x1610c) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 80))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = getr regs 4).
  { rewrite (getr_of_eqv _ _ 4 X1 eq_refl). simp_regs. exact (KT 4 ltac:(unfold callee_saved; lia) ltac:(cbn [In]; lia)). }
  assert (E1_10 : getr R1 10 = Z_to_bv 64 (bv_unsigned sp - 80))
    by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 80) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (HWm : forall a, 0 <= a < 2 ^ 64 -> ~ outside [(bv_unsigned sp - 12464, bv_unsigned sp - 80 + 32)] a ->
                bv_unsigned sp - SUP_ADD_K <= a < bv_unsigned sp).
  { intros a Ra Hm. cbn [outside] in Hm. unfold SUP_ADD_K. lia. }
  pose proof (sinv_stack B API SEGS GOWN AX SUP_ADD_K (bv_unsigned sp) L A mem md O Lc Ac mc mdc Rc Oc bc m1 _
                SI MU1 WM1 HWm) as SI1.
  assert (FR1 : rw_cells rsegs m1 (bv_unsigned sp - 48)
    [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transport rsegs _ mc m1 _ _ FR MU1 WM1). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  pose proof SI1 as (RJ1 & GR1 & _ & _ & _ & _ & F181 & RS1).
  pose proof RJ1 as RJ1x.
  destruct RJ1x as (HM1 & HWA & HW1 & HBd & HL & HLen & HV1 & HK1 & HK2 & HK3 & HF & HRM & HKP & HSC1 & HAX).
  assert (BRNG : forall q k, In (q, k) (blocks Lc Ac) -> 4096 <= q /\ q + k <= alloc_ceiling).
  { intros q k Hq. unfold blocks in Hq. apply in_map_iff in Hq as ([p k'] & E & Hp). cbn in E. injection E as <- <-.
    exact (mr_blocks_range B _ LAWS Lc Ac m1 mdc p k' HM1 Hp). }
  rewrite <- SEGS.
  eapply SR_bind.
  { eapply (HB (mkFP F1 fc1) Lc Ac R1 m1 mdc (bv_unsigned sp - 80) (resp v) slack Rc Oc (sb_shift bc A Ac)).
    - apply (call_pre_k_of_rjr B _ SUP_ADD_K (bv_unsigned sp) rec_area _ L A mem md Lc Ac m1 mdc HAND_BACK_K R1 RJ1).
      + rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP1. replace (bv_unsigned sp - 80) with (bv_unsigned sp + (-5) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold HAND_BACK_K, XMALLOC_K, ALLOC_STACK. lia.
      + rewrite SP1. unfold SUP_ADD_K, HAND_BACK_K, XMALLOC_K, ALLOC_STACK. lia.
      + rewrite SP1. lia.
      + rewrite E1_4. exact HTP.
    - exact E1_10.
    - rewrite SEGS. exact BUF1.
    - exact (resp_no0 v).
    - unfold LMAX. lia.
    - rewrite SL. pose proof (Z.mod_pos_bound (- (bv_unsigned sp - 80 + Z.of_nat (length (resp v)) + 1)) 8
        ltac:(lia)). lia.
    - right. rewrite SP1. lia.
    - left. rewrite SP1. lia.
    - rewrite SEGS. exact GR1.
    - intros [q k] Hin. pose proof (BRNG q k (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR1 Hin)).
      unfold iv_apart. cbn [fst snd]. rewrite length_app. cbn [length]. lia.
    - exact RS1.
    - exact ROOM.
    - rewrite SEGS. exact RA1. }
  intros cf2 RET.
  destruct RET as (L2 & A2 & R2 & m2 & md2 & p1 & p2 & old & O2 & -> & OLDB & POST2 & A0' & P12 & AL1 & AL2 & FR1h
    & FR2h & (c1 & c2 & HBk & HIFF & NI1 & NI2) & BK & UBK & GREP' & HO' & HO2 & HBC & BY1 & BY2 & BYS & RA2 & GK2
    & INIT2 & REG2 & GR2 & RES2).
  pose proof POST2 as (PM2 & PW2 & PB2 & PL2 & PA2 & PR2 & PV2 & PF2 & PK2 & PS2).
  destruct (mr_model B _ LAWS L2 A2 m2 md2 PM2) as (Hh2 & Hl2 & _).
  set (n := Z.of_nat (length (resp v)) + 1) in *.
  assert (HF12 : forall a, alloc_ceiling <= a < 2 ^ 64 ->
     ~ (bv_unsigned sp - 80 - HAND_BACK_K <= a < bv_unsigned sp - 80) ->
     mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
     (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
  { intros a Ha Hs. apply PF2.
    - left. exact Ha.
    - intro Ho. destruct (owned_low B _ LAWS _ _ _ _ _ HM1 Ho). lia.
    - intro Ho. destruct (owned_low B _ LAWS _ _ _ _ _ PM2 Ho). lia.
    - unfold scratch_k. rewrite SP1. intros [H|H]; [lia | pose proof ERRNO_LOW; lia].
    - intros HE. cbv beta in HE. destruct HE as [H|[(k & Hk & H)|[H|H]]].
      + unfold G_REC, OFF_ANSWER in H. lia.
      + pose proof (BRNG old k Hk). lia.
      + destruct FR1h as (F1a & F1b & F1c). lia.
      + destruct FR2h as (F2a & F2b & F2c). lia. }
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 48)
    [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi. rewrite <- SEGS.
    destruct (HF12 (bv_unsigned sp - 48 + i) ltac:(lia) ltac:(unfold HAND_BACK_K, XMALLOC_K, ALLOC_STACK; lia))
      as [Q12m Q12w].
    split; [exact Q12m | tauto]. }
  rewrite E1_1, SEGS.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. cbn [fp_regs fp_csr]. unfold Regs6ss.mkR_of.
    assert (Q2' : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp + -80)).
    { replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by ring.
      exact (eq_trans (PR2 2 ltac:(unfold callee_saved; lia)) E1_2). }
    rewrite Q2'.
    eapply sa_seg_epi; [ | lia].
    replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by ring. exact FR2. }
  intros ms5 (can5 & Q5 & EQ5). subst can5.
  destruct (CF.RecAnsB.eqv_mkst_fx _ _ _ _ _ _ _ EQ5) as (R5 & -> & X5). clear EQ5.
  assert (HB' : exists kold, (old = 0 /\ blocks Lc Ac = c1 ++ c2) \/
                             (old <> 0 /\ In (old, kold) Oc /\ blocks Lc Ac = c1 ++ (old, kold) :: c2)).
  { destruct HBk as [H|(k & H)]; [exists 0; left; exact H | exists k; right; exact H]. }
  destruct HB' as [kold HB'].
  assert (STAB : forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
            In (p, k) (user_blocks Ac) /\ ptr_addr Lc p = ptr_addr L p).
  { intros p k Hu Hno.
    split; [exact (rjr_in_cur B (aa_MR API) SUP_ADD_K (bv_unsigned sp) rec_area (fun pn => In pn O) L A mem md
                     Lc Ac m1 mdc p k RJ1 Hu Hno)|].
    exact (ptr_addr_stable A L Lc p k HWA Hu HL). }
  assert (R2r : rjr B (aa_MR API) SUP_ADD_K (bv_unsigned sp) rec_area (fun pn => In pn O) L A mem md L2 A2 m2 md2).
  { apply (rjr_post B (aa_MR API) SEGS LAWS AX ERRNO_LOW SUP_ADD_K (bv_unsigned sp) rec_area (fun pn => In pn O)
             L A mem md Lc Ac m1 mdc HAND_BACK_K R1 _ (fun a => a = old) L2 A2 R2 m2 md2 RJ1 POST2).
    - rewrite SP1. unfold SUP_ADD_K, HAND_BACK_K, XMALLOC_K, ALLOC_STACK. lia.
    - rewrite SP1. lia.
    - intros a Ha Hf. cbv beta in Ha.
      destruct Ha as [H|[(k & Hk & H)|[H|H]]].
      + unfold rec_area, G_REC, REC_SC, OFF_ANSWER, SC_SIZE, REC_SIZE, SUP_ADD_K in *. split; [lia|]. lia.
      + exfalso. unfold blocks in Hk. apply in_map_iff in Hk as ([pq kq] & Eq & Uq). cbn [fst snd] in Eq.
        injection Eq as Eo Ek. subst kq.
        pose proof (mr_blocks_range B _ LAWS Lc Ac m1 mdc pq k HM1 Uq).
        pose proof (ax_blocks_img AX Lc Ac m1 mdc pq k (a - ptr_addr Lc pq) HM1 Uq ltac:(lia)) as NI.
        replace (ptr_addr Lc pq + (a - ptr_addr Lc pq)) with a in NI by ring.
        destruct Hf as [Hf|(Hf & _)]; [lia | exact (NI Hf)].
      + exfalso. destruct FR1h as (F1a & F1b & F1c).
        destruct Hf as [Hf|(Hf & _)]; [lia|].
        apply (F1c (a - p1)); [lia|]. replace (p1 + (a - p1)) with a by ring. exact Hf.
      + exfalso. destruct FR2h as (F2a & F2b & F2c).
        destruct Hf as [Hf|(Hf & _)]; [lia|].
        apply (F2c (a - p2)); [lia|]. replace (p2 + (a - p2)) with a by ring. exact Hf.
    - intros p k Hu Hno Hk E.
      destruct (STAB p k Hu Hno) as [Hu1 Ep].
      pose proof (mr_blocks_range B (aa_MR API) LAWS L A mem md p k HMR Hu) as Hr.
      destruct HB' as [(E0 & _)|(NZ & Ho & EB)]; [lia|].
      assert (Hob : In (old, kold) (blocks Lc Ac)) by (rewrite EB; apply in_or_app; right; left; reflexivity).
      pose proof (user_in_blocks Lc Ac p k Hu1) as Hb. rewrite Ep, E in Hb.
      pose proof (rec_rep_pos rsegs G_REC REC_SC Lc Ac m1 Rc Oc (old, kold) GR1 Ho) as Hk0. cbn [snd] in Hk0.
      assert (Ek : k = kold) by exact (blocks_same_addr B (aa_MR API) LAWS Lc Ac m1 mdc old k kold HM1 Hb Hob Hk Hk0).
      subst k. rewrite E in Hno.
      destruct (ON _ Ho) as [H|H]; [exact (Hno H)|]. apply H. rewrite <- E. exact (user_in_blocks L A p kold Hu).
    - intros p k Hu Hu1 Hu'.
      destruct (in_dec pair_dec (ptr_addr L p, k) O) as [H|H]; [exact H|]. exfalso. apply Hu'. apply UBK; [exact Hu1|].
      rewrite (ptr_addr_stable A L Lc p k HWA Hu HL). intros Ho.
      destruct (ON _ Ho) as [H'|H']; [exact (H H') | exact (H' (user_in_blocks L A p k Hu))].
    - exact REG2.
    - rewrite INIT2. discriminate. }
  assert (RP : regs_preserved regs R5).
  { intros r Hr.
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold callee_saved in Hr; lia).
    repeat (destruct C as [C|C]; [subst r; sa_pres X5 PR2 X1 KT R1|]).
    subst r. sa_pres X5 PR2 X1 KT R1. }
  pose proof (rjr_final B (aa_MR API) CTX SUP_ADD_K rec_area (fun pn => In pn O) (fun a => In a (map fst O))
                L A regs mem md L2 A2 R5 m2 md2 PRK R2r RP ltac:(intros a k G; exact (in_map fst O (a, k) G))) as FIN.
  pose proof (rjr_others_kept B (aa_MR API) SUP_ADD_K (bv_unsigned sp) rec_area (fun pn => In pn O) L A mem md
                L2 A2 m2 md2 O R2r (fun pn H => H)) as OK.
  destruct (tail_owns_blocks (blocks L A) (blocks Lc Ac) (blocks L2 A2) O Oc O2 c1 c2 old kold p1 p2 n
              ON B1 B2 HB' NI1 HO' HBC) as [OWN BLK].
  assert (Hq : In (p2, n) (blocks L2 A2)) by (apply HIFF; right; right; reflexivity).
  assert (RPC : ret_pc (getr regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  apply SR_ret. unfold sa_tret.
  exists (mkFP F1 fc1), L2, A2, R5, m2, md2, O2, p2.
  split; [rewrite SEGS, RPC; reflexivity|].
  split.
  { unfold fp_kept. cbn [fp_regs fp_csr]. split; [exact FRM1|].
    intros r Hr. apply FK1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    unfold fs_saved in Hr. rewrite Z.mod_small by lia. lia. }
  split; [exact FIN|].
  split; [rewrite (getr_of_eqv _ _ 10 X5 eq_refl); simp_regs; exact A0'|].
  split; [exact GREP'|].
  split; [exact OWN|].
  split; [exact BLK|].
  split; [exact Hq|].
  split; [exact FR2h|].
  split; [intros Hin; apply in_map_iff in Hin as (pn & Epn & Hpn); exact (HO2 pn Hpn Epn)|].
  split; [exact BY2|].
  split; [exact OK|].
  split.
  { intros p0 k0 Hu0 Hno0.
    enough (D : ptr_addr L p0 + k0 <= p2 \/ p2 + n <= ptr_addr L p0) by (unfold n in D; lia).
    revert p0 k0 Hu0 Hno0.
    apply (q_apart_tail B (aa_MR API) LAWS (ms_segs B) L A mem L2 A2 m2 md2 O p2 n PM2 OK Hq).
    intros p k Hu Hno. destruct (STAB p k Hu Hno) as [Hu1 Ep].
    apply (tail_q_distinct (blocks L A) (blocks Lc Ac) O Oc c1 c2 old kold p2 n (ptr_addr L p, k) ON HB' NI2).
    - exact (user_in_blocks L A p k Hu).
    - exact Hno.
    - rewrite <- Ep. exact (user_in_blocks Lc Ac p k Hu1). }
  split; [exact RA2|].
  split.
  { destruct (ax_statics AX L2 A2 m2 md2 PM2) as (_ & (g & Hg & HGW) & _).
    rewrite SEGS. apply (CF.RecAnsB.f18_words_after m1 m2 g F181); [| exact Hg | rewrite SEGS, GRD in HGW; exact HGW].
    intros i Hi. unfold snprintf_c.GOT_GUARD. rewrite <- GOTG, <- SEGS. exact (GK2 i Hi). }
  split; [exact INIT2|]. split; [lia|].
  rewrite <- (sb_shift_trans bc A Ac A2).
  split; [eapply sb_le_trans; [exact GR2 | apply sb_malloc_mono; apply sb_malloc_mono; exact BLE] | exact RES2].
Qed.

Lemma sa_oor : forall L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id,
  call_pre_t B API SUP_ADD_K L A regs mem md ->
  sinv B API SUP_ADD_K (spZ regs) L A mem md O Lc Ac mc mdc (rec_record R REC_ADD As) Oc b ->
  -2^31 <= id < 2^31 -> ~ (0 <= id < 10000) ->
  sb_le (sb_shift b A Ac) bpre ->
  room_ag (sb_malloc (sb_malloc bpre (Z.of_nat (length (resp (-1))) + 1)) (Z.of_nat (length (resp (-1))) + 1))
    (Z.of_nat (length (resp (-1))) + 1) ->
  frm_zero fp_csr ->
  rw_cells rsegs mc (spZ regs - 48)
    [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  getr regs_t 2 = Z_to_bv 64 (spZ regs - 80) -> getr regs_t 8 = Z_to_bv 64 id ->
  sa_kx [2; 8; 9; 18; 19; 20] regs regs_t ->
  SR rsegs (mkCfg (mkst regs_t (Z_to_bv 64 0x16094) mc (seg_rom rsegs)) mdc)
    (sa_tret L A regs mem md O (fst (hand_back (rec_record R REC_ADD As) (resp (-1)))) (resp (-1)) b bpre).
Proof using SEGS ERRNO_LOW GOTG GRD GOWN AX CTX SNP HB.
  intros L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id PRE SI HID OR BLE ROOM FRM FR T2 T8 KT.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & _).
  pose proof RJ as (HM & _).
  destruct (mr_model B _ LAWS Lc Ac mc mdc HM) as (Hh & Hl & _).
  destruct (rjr_bounds B _ SUP_ADD_K (spZ regs) rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  unfold SUP_ADD_K in HK1.
  assert (Q8 : reg_get regs_t 8 = Z_to_bv 64 id) by exact T8.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q8. eapply sa_seg_oor; [exact HID | exact OR]. }
  intros ms1 (can1 & E1 & EQ1). subst can1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2).
  apply (sa_resp L A regs mem md O Lc Ac mc mdc _ Oc b bpre R2 (-1) PRE SI).
  - rewrite (getr_of_eqv _ _ 2 X2 eq_refl). simp_regs. exact T2.
  - rewrite (getr_of_eqv _ _ 10 X2 eq_refl). simp_regs. exact T2.
  - rewrite (getr_of_eqv _ _ 11 X2 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 12 X2 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 13 X2 eq_refl). simp_regs. reflexivity.
  - lia.
  - apply (sa_kx_trans _ regs regs_t R2 KT). sa_kx_tac X2.
  - exact FR.
  - exact FRM.
  - exact BLE.
  - eapply room_slots_mono; [| | exact ROOM]; [apply sb_malloc_mono, sb_malloc_mono; exact BLE | lia].
Qed.

Lemma sa_ref : forall L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t,
  call_pre_t B API SUP_ADD_K L A regs mem md ->
  sinv B API SUP_ADD_K (spZ regs) L A mem md O Lc Ac mc mdc (rec_record R REC_ADD As) Oc b ->
  (length (r_calls R) <= 16)%nat -> r_refuse (rec_record R REC_ADD As) <> 0 ->
  sb_le (sb_shift b A Ac) bpre ->
  room_ag (sb_malloc (sb_malloc bpre (Z.of_nat (length (resp (r_code (rec_record R REC_ADD As)))) + 1))
                (Z.of_nat (length (resp (r_code (rec_record R REC_ADD As)))) + 1))
    (Z.of_nat (length (resp (r_code (rec_record R REC_ADD As)))) + 1) ->
  frm_zero fp_csr ->
  rw_cells rsegs mc (spZ regs - 48)
    [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  getr regs_t 2 = Z_to_bv 64 (spZ regs - 80) -> getr regs_t 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  sa_kx [2; 8; 9; 18; 19; 20] regs regs_t ->
  SR rsegs (mkCfg (mkst regs_t (Z_to_bv 64 0x160b8) mc (seg_rom rsegs)) mdc)
    (sa_tret L A regs mem md O (fst (hand_back (rec_record R REC_ADD As) (resp (r_code (rec_record R REC_ADD As)))))
       (resp (r_code (rec_record R REC_ADD As))) b bpre).
Proof using SEGS ERRNO_LOW AX CTX SLACK ANSF.
  intros L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t PRE SI H16 RNZ BLE ROOM FRM FR T2 T9 KT.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_ADD_K in HCEIL, HWS. unfold TASK_SIZE in TS.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  pose proof RJ as (HM & _).
  destruct (mr_model B _ LAWS Lc Ac mc mdc HM) as (Hh & Hl & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  set (R1 := rec_record R REC_ADD As) in *.
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & HC & HA & HP & HX & HW).
  pose proof HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  assert (RC1 : rw_cells rsegs mc 0x34028 [C4 (Z_to_bv 64 (r_refuse R1))]).
  { apply sa_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |].
    replace 0x34028 with (G_REC + OFF_REFUSE) by (unfold G_REC, OFF_REFUSE; lia). exact X1. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. eapply sa_seg_ref; [exact RC1 | exact X6 | exact RNZ]. }
  intros ms1 (can1 & E1 & EQ1). subst can1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2r).
  assert (E2_1 : getr R2 1 = Z_to_bv 64 0x160d8) by (rewrite (getr_of_eqv _ _ 1 X2r eq_refl); simp_regs; reflexivity).
  assert (E2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 80))
    by (rewrite (getr_of_eqv _ _ 2 X2r eq_refl); simp_regs; exact T2).
  assert (E2_4 : getr R2 4 = getr regs 4).
  { rewrite (getr_of_eqv _ _ 4 X2r eq_refl). simp_regs. exact (KT 4 ltac:(unfold callee_saved; lia) ltac:(cbn [In]; lia)). }
  assert (E2_10 : getr R2 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 10 X2r eq_refl); simp_regs; exact T9).
  assert (E2_11 : getr R2 11 = Z_to_bv 64 0) by (rewrite (getr_of_eqv _ _ 11 X2r eq_refl); simp_regs; reflexivity).
  assert (E2_12 : getr R2 12 = Z_to_bv 64 0) by (rewrite (getr_of_eqv _ _ 12 X2r eq_refl); simp_regs; reflexivity).
  assert (KR2 : sa_kx [2; 8; 9; 18; 19; 20] regs R2) by (apply (sa_kx_trans _ regs regs_t R2 KT); sa_kx_tac X2r).
  assert (SP2 : spZ R2 = bv_unsigned sp - 80) by (unfold spZ; rewrite E2_2; apply unsigned_lit; lia).
  assert (ESA : rec_answer R1 (REC_ADD, As) [] false = hand_back R1 (resp (r_code R1))).
  { unfold rec_answer. rewrite (proj2 (Z.eqb_neq _ _) RNZ). reflexivity. }
  eapply SR_bind.
  { apply (CF.sup_remove.answer_call B API SEGS AX ERRNO_LOW (ANSF fx) SLACK SUP_ADD_K (bv_unsigned sp) L A mem md O
             Lc Ac R2 mc mdc R1 Oc b bpre (rec_entry G_REC REC_SC R) 0 (REC_ADD, As) [] false SI).
    - rewrite E2_1. apply bv_eq. vm_compute. reflexivity.
    - rewrite SP2. replace (bv_unsigned sp - 80) with (bv_unsigned sp + (-5) * 16) by ring. rewrite Z.mod_add by lia.
      exact HAL.
    - rewrite SP2. assert (AK : ANSWER_K = 12384) by reflexivity. rewrite AK. unfold SUP_ADD_K. lia.
    - rewrite SP2. lia.
    - rewrite SP2. unfold TASK_SIZE. lia.
    - rewrite E2_4. exact HTP.
    - exact E2_10.
    - exact E2_11.
    - rewrite E2_12. reflexivity.
    - intros H. exfalso. exact (RNZ H).
    - intros H. exfalso. exact (RNZ H).
    - exact FRM.
    - exact BLE.
    - rewrite ESA. cbn [snd hand_back].
      eapply room_slots_mono; [| | exact ROOM]; [apply sb_malloc_mono, sb_malloc_mono; exact BLE | lia]. }
  intros c5 MID. unfold CF.sup_remove.ans_mid in MID. rewrite ESA in MID. cbv zeta in MID.
  change (snd (hand_back R1 (resp (r_code R1)))) with (resp (r_code R1)) in MID.
  destruct MID as (fx' & L' & A' & R5 & m5 & md5 & O' & q & -> & FPK & RJ5 & PR5 & KST5 & A05 & GR5 & ON5 & BL5 & INq
    & FRq & NIq & BYq & OK5 & AP5 & RA5 & F185 & INIT5 & RG5 & SB5 & RS5).
  pose proof RJ5 as (HM5 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM5) as (Hh5 & Hl5 & _).
  assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp - 48)
    [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs mc); [exact FR|]. intros i Hi. cbn in Hi.
    destruct (KST5 (bv_unsigned sp - 48 + i)) as [Ea Eb]; [rewrite SP2; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  assert (Q52 : reg_get R5 2 = Z_to_bv 64 (bv_unsigned sp + -80)).
  { replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by ring.
    exact (eq_trans (PR5 2 ltac:(unfold callee_saved; lia)) E2_2). }
  rewrite E2_1.
  eapply evt_SR_canon; [ | exact Hh5 | exact Hl5 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q52.
    eapply sa_seg_ansret; [ | lia].
    replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by ring. exact FR5. }
  intros ms6 (can6 & Q6 & EQ6). subst can6.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ6) as (R6 & -> & Y6). clear EQ6.
  assert (RP : regs_preserved regs R6).
  { apply (sa_kx_pres [2; 8; 9; 18; 19; 20]).
    - apply (sa_kx_trans _ _ _ _ KR2). apply (sa_kx_trans _ _ _ _ (sa_kx_of_pres _ _ _ PR5)). sa_kx_tac Y6.
    - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
        match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k Y6 eq_refl) end;
        simp_regs; first [reflexivity | unfold getr; reflexivity]. }
  assert (E6_10 : getr R6 10 = Z_to_bv 64 q) by (rewrite (getr_of_eqv _ _ 10 Y6 eq_refl); simp_regs; exact A05).
  assert (RPC : ret_pc (getr regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  apply SR_ret. unfold sa_tret. rewrite SEGS.
  exists (mkFP (@fp_regs fx') (@fp_csr fx')), L', A', R6, m5, md5, O', q.
  split; [rewrite RPC; reflexivity|].
  split.
  { destruct FPK as [FZ' FK']. split; [exact FZ'|]. intros r Hr. cbn [fp_regs]. exact (FK' r Hr). }
  split.
  { apply (rjr_final B (aa_MR API) CTX SUP_ADD_K rec_area (fun pn => In pn O) (fun a => In a (map fst O)) L A regs mem md
             L' A' R6 m5 md5 PRK RJ5 RP).
    intros a0 k0 G. exact (in_map fst O (a0, k0) G). }
  split; [exact E6_10|]. split; [exact GR5|]. split; [exact ON5|]. split; [exact BL5|]. split; [exact INq|].
  split; [exact FRq|]. split; [exact NIq|]. split; [exact BYq|]. split; [exact OK5|].
  split; [intros p0 k0 H1 H2; pose proof (AP5 p0 k0 H1 H2); lia|].
  split; [exact RA5|]. split; [exact F185|]. split; [exact INIT5|]. split; [exact RG5|].
  split; [exact SB5 | exact RS5].
Qed.

Lemma sa_mixarm : forall L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id,
  call_pre_t B API SUP_ADD_K L A regs mem md ->
  sinv B API SUP_ADD_K (spZ regs) L A mem md O Lc Ac mc mdc (rec_record R REC_ADD As) Oc b ->
  (length (r_calls R) <= 16)%nat -> length As = 4%nat ->
  Forall (fun s => Z.of_nat (length s) <= LMAX) As -> r_refuse (rec_record R REC_ADD As) = 0 ->
  -2^31 <= id < 2^31 ->
  sb_le (sb_shift b A Ac) bpre ->
  room_ag (sb_malloc (sb_malloc bpre (Z.of_nat (length (resp id)) + 1)) (Z.of_nat (length (resp id)) + 1))
    (Z.of_nat (length (resp id)) + 1) ->
  frm_zero fp_csr ->
  rw_cells rsegs mc (spZ regs - 48)
    [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  getr regs_t 2 = Z_to_bv 64 (spZ regs - 80) -> getr regs_t 8 = Z_to_bv 64 id ->
  getr regs_t 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  sa_kx [2; 8; 9; 18; 19; 20] regs regs_t ->
  SR rsegs (mkCfg (mkst regs_t (Z_to_bv 64 0x160b8) mc (seg_rom rsegs)) mdc)
    (sa_tret L A regs mem md O (fst (hand_back (rec_mix (rec_record R REC_ADD As) (REC_ADD, As)) (resp id)))
       (resp id) b bpre).
Proof using SEGS ERRNO_LOW GOTG GRD GOWN AX CTX SLACK SNP HB MIX.
  intros L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id PRE SI H16 LA4 LXA RZ HID BLE ROOM FRM FR
    T2 T8 T9 KT.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof alloc_ceiling_value as ACV.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_ADD_K in HCEIL, HWS. unfold TASK_SIZE in TS.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  pose proof RJ as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  destruct (mr_model B _ LAWS Lc Ac mc mdc HM) as (Hh & Hl & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  destruct (rec_entry_bounds R H16) as (EB1 & EB2 & EB3).
  destruct (rec_entry_at rsegs Lc Ac mc R REC_ADD As Oc GR) as (P & CA).
  set (R1 := rec_record R REC_ADD As) in *.
  pose proof GR as (Q & HRep & HO).
  pose proof HRep as (HS & HC & HA & HP & HX & HW).
  pose proof HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  assert (RC1 : rw_cells rsegs mc 0x34028 [C4 (Z_to_bv 64 (r_refuse R1))]).
  { apply sa_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |].
    replace 0x34028 with (G_REC + OFF_REFUSE) by (unfold G_REC, OFF_REFUSE; lia). exact X1. }
  rewrite RZ in RC1.
  destruct CA as (CF1 & CF2 & CLP & CFN & CNA & CND & CKA). cbn [fst snd] in *.
  set (e := rec_entry G_REC REC_SC R) in *.
  set (args := combine (map (fun pn => Z_to_bv 64 (fst pn)) P) As).
  assert (LP : length (map (fun pn => Z_to_bv 64 (fst pn)) P) = length As) by (rewrite length_map; exact CLP).
  assert (LA : length args = length As) by (unfold args; rewrite length_combine, LP; lia).
  assert (U2 : bv_unsigned (reg_get regs_t 2) = bv_unsigned sp - 80).
  { change (reg_get regs_t 2) with (getr regs_t 2). rewrite T2. apply unsigned_lit. lia. }
  assert (ARGS : forall k p, nth_error args k = Some p ->
            mc_arg (normalize rsegs mc) (bv_unsigned sp - 80 - 96) (bv_unsigned sp - 80) e k p).
  { intros k [w s] Hk. destruct (sa_nth_combine _ _ _ _ k w s Hk) as (Hw & Hs).
    rewrite nth_error_map in Hw. destruct (nth_error P k) as [[q kq]|] eqn:EP; cbn in Hw; [|discriminate].
    injection Hw as <-.
    destruct (CKA k s (q, kq) Hs EP) as (BP & PNZ & PIN & PSZ & PBS & PN0). cbn [fst snd] in *.
    assert (LXs : Z.of_nat (length s) <= LMAX).
    { rewrite Forall_forall in LXA. apply LXA. exact (nth_error_In _ _ Hs). }
    destruct (block_facts B _ LAWS Lc Ac mc mdc q kq 0 HM PIN ltac:(lia)) as (_ & BQ1 & BQ2 & _).
    destruct (slack_rebuild mc q s PBS ltac:(lia) ltac:(unfold LMAX in *; lia)) as (slack & BPs & ALp & SL7 & SLe).
    { intros a Ha. destruct (Z_lt_ge_dec a (q + kq)) as [Hlt|Hge].
      - replace a with (q + (a - q)) by ring.
        exact (proj1 (block_facts B _ LAWS Lc Ac mc mdc q kq (a - q) HM PIN ltac:(lia))).
      - apply (SLACK Lc Ac mc mdc q kq a HM PIN). split; [lia|]. Z.div_mod_to_equations. lia. }
    unfold mc_arg. cbn [fst snd]. rewrite unsigned_lit by lia.
    split; [apply (bytes_at_normalize rsegs mc _ _ RA); unfold CALL_OFF_ARGS in BP; exact BP|].
    split; [exact PN0|]. split; [exact LXs|]. split; [lia|]. split; [unfold LMAX in *; lia|].
    exists slack. split; [exact (bytes_at_normalize rsegs mc _ _ RA BPs)|]. split; [exact ALp|].
    left. destruct ACV as (_ & ACM). Z.div_mod_to_equations. lia. }
  assert (EF : bytes_at rsegs (normalize rsegs mc) e
                 (le4 (Z_to_bv 64 REC_ADD) ++ le4 (Z_to_bv 64 (Z.of_nat (length args))))).
  { apply (bytes_at_normalize rsegs mc _ _ RA). apply bytes_at_app. split.
    - unfold CALL_OFF_FN in CFN. rewrite Z.add_0_r in CFN. exact CFN.
    - rewrite LA. replace (e + Z.of_nat (length (le4 (Z_to_bv 64 REC_ADD)))) with (e + CALL_OFF_NARGS)
        by (rewrite length_le4; unfold CALL_OFF_NARGS; reflexivity). exact CNA. }
  assert (STn : stk rsegs (normalize rsegs mc) (bv_unsigned sp - 12464) (bv_unsigned sp - 80)).
  { apply stk_norm; [lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSC. left. unfold SUP_ADD_K. lia. }
  assert (RC1n : rw_cells rsegs (normalize rsegs mc) 0x34028 [C4 (Z_to_bv 64 0)]).
  { apply rw_cells_norm_glob; [exact RA | unfold GLOB_LO; lia | cbn; unfold GLOB_LO, GLOB_N; lia | exact RC1]. }
  assert (ESn : rw_cells rsegs (normalize rsegs mc) 0x343d8 [C8 (Z_to_bv 64 (r_state R1))]).
  { apply rw_cells_norm_glob; [exact RA | unfold GLOB_LO; lia | cbn; unfold GLOB_LO, GLOB_N; lia |].
    apply bytes_cell8; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |].
    replace 0x343d8 with (G_REC + OFF_STATE) by (unfold G_REC, OFF_STATE; lia). exact X4. }
  assert (E56 : e + 56 <= 0x343d8).
  { unfold e, rec_entry. destruct (Nat.ltb_spec (length (r_calls R)) 16);
      unfold G_REC, OFF_CALLS, CALL_SIZE, REC_SC; lia. }
  assert (Q9 : reg_get regs_t 9 = Z_to_bv 64 e) by exact T9.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q9.
    eapply (evt_normalize rsegs); [exact WX | exact RA |].
    eapply (sa_run_mix MIX) with (lo := bv_unsigned sp - 12464) (args := args);
      [apply mem_inv_normalize | rewrite U2; exact STn | rewrite U2; lia | lia | exact RC1n
      | exact EF | unfold REC_ADD; lia | unfold REC_SC in EB1; lia | exact EB3 | exact E56 | rewrite LA, LA4; lia
      | | exact ESn | exact X9].
    intros k p Hk. rewrite U2. exact (ARGS k p Hk). }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & b4 & b5 & b6 & b7 & t3' & t4' & t5' & t6' & m1n & -> & MU1n & WM1n & ES1n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs mc RA) MR1r RO1 MU1n) as MU1.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mc RA) MR1r RO1 WM1n) as WM1.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR1r ES1n) as ES1.
  clear MU1n WM1n ES1n MR1r.
  rewrite U2 in MU1. unfold args in ES1. rewrite (sa_combine_snd _ _ _ _ LP) in ES1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2r).
  assert (SI2 : sinv B API SUP_ADD_K (bv_unsigned sp) L A mem md O Lc Ac m1 mdc (rec_mix R1 (REC_ADD, As)) Oc b).
  { apply (sinv_state B API SEGS GOWN AX SUP_ADD_K (bv_unsigned sp) L A mem md O Lc Ac mc mdc R1 Oc b m1 _
             (mixcall (r_state R1) REC_ADD As) SI MU1 WM1).
    - intros a Ra Hm. cbn in Hm. unfold G_REC, OFF_STATE, SUP_ADD_K. lia.
    - apply mixcall_range. exact X9.
    - unfold G_REC, OFF_STATE. exact (cells_c8 m1 _ _ ES1). }
  assert (FR2 : rw_cells rsegs m1 (bv_unsigned sp - 48)
    [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transport rsegs _ mc m1 _ _ FR MU1 WM1). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  apply (sa_resp L A regs mem md O Lc Ac m1 mdc (rec_mix R1 (REC_ADD, As)) Oc b bpre R2 id PRE SI2).
  - rewrite (getr_of_eqv _ _ 2 X2r eq_refl). simp_regs. exact T2.
  - rewrite (getr_of_eqv _ _ 10 X2r eq_refl). simp_regs. exact T2.
  - rewrite (getr_of_eqv _ _ 11 X2r eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 12 X2r eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 13 X2r eq_refl). simp_regs. exact T8.
  - exact HID.
  - apply (sa_kx_trans _ regs regs_t R2 KT). sa_kx_tac X2r.
  - exact FR2.
  - exact FRM.
  - exact BLE.
  - eapply room_slots_mono; [| | exact ROOM]; [apply sb_malloc_mono, sb_malloc_mono; exact BLE | lia].
Qed.

Lemma sa_tail : forall L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id,
  call_pre_t B API SUP_ADD_K L A regs mem md ->
  sinv B API SUP_ADD_K (spZ regs) L A mem md O Lc Ac mc mdc (rec_record R REC_ADD As) Oc b ->
  (length (r_calls R) <= 16)%nat -> length As = 4%nat ->
  Forall (fun s => Z.of_nat (length s) <= LMAX) As -> -2^31 <= id < 2^31 ->
  sb_le (sb_shift b A Ac) bpre ->
  room_ag (sb_malloc (sb_malloc bpre (Z.of_nat (length (snd (sa_m R As id))) + 1))
                (Z.of_nat (length (snd (sa_m R As id))) + 1)) (Z.of_nat (length (snd (sa_m R As id))) + 1) ->
  frm_zero fp_csr ->
  rw_cells rsegs mc (spZ regs - 48)
    [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  getr regs_t 2 = Z_to_bv 64 (spZ regs - 80) -> getr regs_t 8 = Z_to_bv 64 id ->
  getr regs_t 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  sa_kx [2; 8; 9; 18; 19; 20] regs regs_t ->
  SR rsegs (mkCfg (mkst regs_t (Z_to_bv 64 0x16094) mc (seg_rom rsegs)) mdc)
    (sa_tret L A regs mem md O (fst (sa_m R As id)) (snd (sa_m R As id)) b bpre).
Proof using SEGS ERRNO_LOW GOTG GRD GOWN AX CTX SLACK SNP HB MIX ANSF.
  intros L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id PRE SI H16 LA4 LXA HID BLE ROOM FRM FR
    T2 T8 T9 KT.
  unfold sa_m in ROOM |- *. cbv zeta in ROOM |- *.
  destruct (Z_lt_le_dec id 0) as [N0|P0].
  1: { assert (RG : ((id <? 0) || (10000 <=? id)) = true) by (apply orb_true_iff; left; apply Z.ltb_lt; lia).
       rewrite RG in ROOM |- *.
       exact (sa_oor L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id PRE SI HID ltac:(lia) BLE ROOM FRM FR
                T2 T8 KT). }
  destruct (Z_lt_le_dec id 10000) as [P1|N1].
  2: { assert (RG : ((id <? 0) || (10000 <=? id)) = true) by (apply orb_true_iff; right; apply Z.leb_le; lia).
       rewrite RG in ROOM |- *.
       exact (sa_oor L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id PRE SI HID ltac:(lia) BLE ROOM FRM FR
                T2 T8 KT). }
  assert (RG : ((id <? 0) || (10000 <=? id)) = false)
    by (apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.leb_gt]; lia).
  rewrite RG in ROOM |- *.
  pose proof (aa_laws API) as LAWS.
  pose proof SI as (RJ & _). pose proof RJ as (HM & _).
  destruct (mr_model B _ LAWS Lc Ac mc mdc HM) as (Hh & Hl & _).
  assert (Q8 : reg_get regs_t 8 = Z_to_bv 64 id) by exact T8.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q8. eapply sa_seg_rng. lia. }
  intros ms1 (can1 & (b0 & b1 & E1) & EQ1). subst can1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2).
  assert (KT2 : sa_kx [2; 8; 9; 18; 19; 20] regs R2)
    by (apply (sa_kx_trans _ regs regs_t R2 KT); sa_kx_tac X2).
  assert (U2 : getr R2 2 = Z_to_bv 64 (spZ regs - 80))
    by (rewrite (getr_of_eqv _ _ 2 X2 eq_refl); simp_regs; exact T2).
  assert (U8 : getr R2 8 = Z_to_bv 64 id) by (rewrite (getr_of_eqv _ _ 8 X2 eq_refl); simp_regs; reflexivity).
  assert (U9 : getr R2 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 9 X2 eq_refl); simp_regs; exact T9).
  destruct (Z.eq_dec (r_refuse (rec_record R REC_ADD As)) 0) as [RZ|RNZ].
  - rewrite (proj2 (Z.eqb_eq _ _) RZ) in ROOM |- *. cbn [negb] in ROOM |- *.
    exact (sa_mixarm L A regs mem md O Lc Ac mc mdc R As Oc b bpre R2 id PRE SI H16 LA4 LXA RZ HID BLE ROOM FRM FR
             U2 U8 U9 KT2).
  - rewrite (proj2 (Z.eqb_neq _ _) RNZ) in ROOM |- *. cbn [negb] in ROOM |- *.
    exact (sa_ref L A regs mem md O Lc Ac mc mdc R As Oc b bpre R2 PRE SI H16 RNZ BLE ROOM FRM FR U2 U9 KT2).
Qed.

Hypothesis ARGS : forall fx0 : YK11.FPState, @arg_s_contract fx0 rc B API.

Lemma sa_cl : forall L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id v,
  call_pre_t B API SUP_ADD_K L A regs mem md ->
  sinv B API SUP_ADD_K (spZ regs) L A mem md O Lc Ac mc mdc (rec_record R REC_ADD As) Oc b ->
  (length (r_calls R) <= 16)%nat -> length As = 3%nat ->
  Forall (fun s => Z.of_nat (length s) <= LMAX) (As ++ [sarg v]) -> -2^31 <= id < 2^31 ->
  arg_s_src B Lc Ac (spZ regs - 80) mc (bv_unsigned (sa_sel (getr regs_t 18))) v ->
  sb_le (sb_shift b A Ac) bpre ->
  room_ag (sb_malloc (sb_shift b A Ac) (Z.of_nat (length (sarg v)) + 1)) (Z.of_nat (length (sarg v)) + 1) ->
  room_ag (sb_malloc (sb_malloc (sb_malloc bpre (Z.of_nat (length (sarg v)) + 1))
                (Z.of_nat (length (snd (sa_m R (As ++ [sarg v]) id))) + 1))
                (Z.of_nat (length (snd (sa_m R (As ++ [sarg v]) id))) + 1))
    (Z.of_nat (length (snd (sa_m R (As ++ [sarg v]) id))) + 1) ->
  frm_zero fp_csr ->
  rw_cells rsegs mc (spZ regs - 48)
    [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  getr regs_t 2 = Z_to_bv 64 (spZ regs - 80) -> getr regs_t 8 = Z_to_bv 64 id ->
  getr regs_t 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr regs_t 20 = Z_to_bv 64 0x108b0 ->
  getr regs_t 4 = getr regs 4 ->
  sa_kx [2; 8; 9; 18; 19; 20] regs regs_t ->
  SR rsegs (mkCfg (mkst regs_t (Z_to_bv 64 0x16080) mc (seg_rom rsegs)) mdc)
    (sa_tret L A regs mem md O (fst (sa_m R (As ++ [sarg v]) id)) (snd (sa_m R (As ++ [sarg v]) id)) b
       (sb_malloc bpre (Z.of_nat (length (sarg v)) + 1))).
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK SNP HB MIX ANSF ARGS.
  intros L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id v PRE SI H16 LA3 LXA HID SRC BLE ROOM1 ROOM FRM FR
    T2 T8 T9 T20 T4 KT.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_ADD_K in HCEIL, HWS. unfold TASK_SIZE in TS.
  pose proof SI as (RJ & _). pose proof RJ as (HM & _).
  destruct (mr_model B _ LAWS Lc Ac mc mdc HM) as (Hh & Hl & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (Q20 : reg_get regs_t 20 = Z_to_bv 64 0x108b0) by exact T20.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q20. apply sa_run4. }
  intros ms1 (can1 & E1 & EQ1). subst can1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2).
  assert (E2_1 : getr R2 1 = Z_to_bv 64 0x16094) by (rewrite (getr_of_eqv _ _ 1 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 80))
    by (rewrite (getr_of_eqv _ _ 2 X2 eq_refl); simp_regs; exact T2).
  assert (E2_4 : getr R2 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X2 eq_refl); simp_regs; exact T4).
  assert (E2_10 : getr R2 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 10 X2 eq_refl); simp_regs; exact T9).
  assert (E2_11 : getr R2 11 = Z_to_bv 64 (bv_unsigned (sa_sel (getr regs_t 18)))).
  { rewrite (getr_of_eqv _ _ 11 X2 eq_refl). simp_regs. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (KR2 : sa_kx [2; 8; 9; 18; 19; 20] regs R2) by (apply (sa_kx_trans _ regs regs_t R2 KT); sa_kx_tac X2).
  assert (SP2 : spZ R2 = bv_unsigned sp - 80) by (unfold spZ; rewrite E2_2; apply unsigned_lit; lia).
  assert (E2_8 : getr R2 8 = Z_to_bv 64 id) by (rewrite (getr_of_eqv _ _ 8 X2 eq_refl); simp_regs; exact T8).
  assert (E2_9 : getr R2 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 9 X2 eq_refl); simp_regs; exact T9).
  apply (sinv_arg_sn (fx := fx) B API SEGS ERRNO_LOW GFACT GOWN AX (ARGS fx) SUP_ADD_K (bv_unsigned sp) L A mem md O
           Lc Ac mc mdc R REC_ADD As Oc b R2 (bv_unsigned (sa_sel (getr regs_t 18))) v _ SI).
  { rewrite LA3. lia. }
  { rewrite E2_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP2. replace (bv_unsigned sp - 80) with (bv_unsigned sp + (-5) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP2. unfold SUP_ADD_K, ARG_S_K, XMALLOC_K, ALLOC_STACK. lia. }
  { rewrite SP2. lia. }
  { rewrite E2_4. exact HTP. }
  { exact E2_10. }
  { exact E2_11. }
  { rewrite SP2. exact SRC. }
  { exact ROOM1. }
  intros L2 A2 regs2 m2 md2 p SI3 SH3 INIT3 RP3 KST3.
  rewrite E2_1.
  assert (FR3 : rw_cells rsegs m2 (bv_unsigned sp - 48)
    [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs mc); [exact FR|]. intros i Hi. cbn in Hi.
    destruct (KST3 (bv_unsigned sp - 48 + i)) as [Ea Eb]; [rewrite SP2; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  apply (sa_tail L A regs mem md O L2 A2 m2 md2 R (As ++ [sarg v]) (Oc ++ [(p, Z.of_nat (length (sarg v)) + 1)]) b
           (sb_malloc bpre (Z.of_nat (length (sarg v)) + 1)) regs2 id PRE SI3 H16).
  - rewrite length_app, LA3. reflexivity.
  - exact LXA.
  - exact HID.
  - rewrite SH3. apply sb_malloc_mono. exact BLE.
  - exact ROOM.
  - exact FRM.
  - exact FR3.
  - exact (eq_trans (RP3 2 ltac:(unfold callee_saved; lia)) E2_2).
  - exact (eq_trans (RP3 8 ltac:(unfold callee_saved; lia)) E2_8).
  - exact (eq_trans (RP3 9 ltac:(unfold callee_saved; lia)) E2_9).
  - exact (sa_kx_trans _ _ _ _ KR2 (sa_kx_of_pres _ _ _ RP3)).
Qed.

Lemma sa_dash_src : forall L A sp m, ro_agree rsegs m -> 0x108b8 <= sp - ARG_S_K ->
  arg_s_src B L A sp m 0x108b0 (Some (bstr "-"%string)).
Proof using SEGS.
  intros L A sp m RA HS. cbn [arg_s_src]. rewrite SEGS.
  assert (LN : Z.of_nat (length (bstr "-"%string)) = 1) by reflexivity.
  assert (BS : bytes_at rsegs m 0x108b0 (bstr "-"%string ++ [Z_to_bv 8 0])).
  { apply sa_rom_bytes; [exact RA | lia | rewrite length_app, Nat2Z.inj_add, LN; cbn; lia | vm_compute; reflexivity]. }
  destruct (rs_bytes_pad rsegs m 0x108b0 _ 6%nat BS) as (sl & SL & BS2).
  { rewrite length_app, Nat2Z.inj_add, LN. cbn. lia. }
  { intros j Hj.
    do 6 (destruct j as [|j]; [rewrite (mbyte_ro_agree _ _ _ RA) by (vm_compute; reflexivity);
      let H := fresh in intro H; vm_compute in H; discriminate H|]).
    lia. }
  rewrite <- app_assoc in BS2. cbn [app] in BS2.
  split; [lia|]. split; [apply no0_nz; vm_compute; reflexivity|]. split; [rewrite LN; unfold LMAX; lia|].
  exists sl. split; [exact BS2|].
  split; [rewrite LN, SL; vm_compute; congruence|].
  split; [left; rewrite length_app, Nat2Z.inj_add, LN; cbn [length]; rewrite SL; lia|].
  unfold str_home. right. right. rewrite LN. split; [lia|]. split; [lia|]. intros i Hi. rewrite SEGS.
  apply (proj2 (rs_ro_rsegs (0x108b0 + i) ltac:(lia))). lia.
Qed.

Lemma sa_src : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc p v sp',
  sinv B API K S L A mem md O Lc Ac mc mdc Rc Oc bc -> ro_agree rsegs mem ->
  S - K <= sp' - ARG_S_K -> sp' <= S -> 0x108b8 <= sp' - ARG_S_K ->
  str_arg B L A O S K mem p v ->
  arg_s_src B Lc Ac sp' mc (bv_unsigned (sa_sel (Z_to_bv 64 p))) (Some (darg v (bstr "-"%string))).
Proof using SEGS ERRNO_LOW SLACK.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc p v sp' SI RA H1 H2 H3 SA.
  pose proof SI as (_ & _ & _ & _ & _ & RAc & _).
  destruct v as [x|].
  - pose proof (sinv_arg_src B API SEGS ERRNO_LOW SLACK K S L A mem md O Lc Ac mc mdc Rc Oc bc p (Some x) sp'
      SI RA H1 H2 SA) as SRC.
    pose proof SRC as (NZ & _ & _ & slack & (B0 & B1 & _) & _).
    rewrite length_app in B1. cbn [length] in B1.
    rewrite (sa_sel_nz p) by lia. exact SRC.
  - cbn [str_arg] in SA. subst p. rewrite sa_sel_z. exact (sa_dash_src Lc Ac sp' mc RAc H3).
Qed.

Lemma sa_pl : forall L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id vp vc pp pc,
  call_pre_t B API SUP_ADD_K L A regs mem md ->
  sinv B API SUP_ADD_K (spZ regs) L A mem md O Lc Ac mc mdc (rec_record R REC_ADD As) Oc b ->
  (length (r_calls R) <= 16)%nat -> length As = 2%nat ->
  Forall (fun s => Z.of_nat (length s) <= LMAX) ((As ++ [darg vp (bstr "-"%string)]) ++ [darg vc (bstr "-"%string)]) ->
  -2^31 <= id < 2^31 -> ro_agree rsegs mem ->
  str_arg B L A O (spZ regs) SUP_ADD_K mem pp vp -> str_arg B L A O (spZ regs) SUP_ADD_K mem pc vc ->
  getr regs_t 19 = Z_to_bv 64 pp -> getr regs_t 18 = Z_to_bv 64 pc ->
  sb_le (sb_shift b A Ac) bpre ->
  room_ag (sb_malloc (sb_shift b A Ac) (Z.of_nat (length (darg vp (bstr "-"%string))) + 1))
    (Z.of_nat (length (darg vp (bstr "-"%string))) + 1) ->
  room_ag (sb_malloc (sb_malloc (sb_shift b A Ac) (Z.of_nat (length (darg vp (bstr "-"%string))) + 1))
      (Z.of_nat (length (darg vc (bstr "-"%string))) + 1))
    (Z.of_nat (length (darg vc (bstr "-"%string))) + 1) ->
  room_ag (sb_malloc (sb_malloc (sb_malloc (sb_malloc bpre (Z.of_nat (length (darg vp (bstr "-"%string))) + 1))
                (Z.of_nat (length (darg vc (bstr "-"%string))) + 1))
                (Z.of_nat (length (snd (sa_m R ((As ++ [darg vp (bstr "-"%string)]) ++ [darg vc (bstr "-"%string)]) id)))
                 + 1))
                (Z.of_nat (length (snd (sa_m R ((As ++ [darg vp (bstr "-"%string)]) ++ [darg vc (bstr "-"%string)]) id)))
                 + 1))
    (Z.of_nat (length (snd (sa_m R ((As ++ [darg vp (bstr "-"%string)]) ++ [darg vc (bstr "-"%string)]) id))) + 1) ->
  frm_zero fp_csr ->
  rw_cells rsegs mc (spZ regs - 48)
    [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  getr regs_t 2 = Z_to_bv 64 (spZ regs - 80) -> getr regs_t 8 = Z_to_bv 64 id ->
  getr regs_t 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr regs_t 4 = getr regs 4 ->
  sa_kx [2; 8; 9; 18; 19; 20] regs regs_t ->
  SR rsegs (mkCfg (mkst regs_t (Z_to_bv 64 0x16064) mc (seg_rom rsegs)) mdc)
    (sa_tret L A regs mem md O (fst (sa_m R ((As ++ [darg vp (bstr "-"%string)]) ++ [darg vc (bstr "-"%string)]) id))
       (snd (sa_m R ((As ++ [darg vp (bstr "-"%string)]) ++ [darg vc (bstr "-"%string)]) id)) b
       (sb_malloc (sb_malloc bpre (Z.of_nat (length (darg vp (bstr "-"%string))) + 1))
          (Z.of_nat (length (darg vc (bstr "-"%string))) + 1))).
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK SNP HB MIX ANSF ARGS.
  intros L A regs mem md O Lc Ac mc mdc R As Oc b bpre regs_t id vp vc pp pc PRE SI H16 LA2 LXA HID RA SPL SCL
    T19 T18 BLE ROOM1 ROOM2 ROOM FRM FR T2 T8 T9 T4 KT.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_ADD_K in HCEIL, HWS. unfold TASK_SIZE in TS.
  pose proof SI as (RJ & _). pose proof RJ as (HM & _).
  destruct (mr_model B _ LAWS Lc Ac mc mdc HM) as (Hh & Hl & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply sa_run3. }
  intros ms1 (can1 & E1 & EQ1). subst can1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2).
  assert (E2_1 : getr R2 1 = Z_to_bv 64 0x16080) by (rewrite (getr_of_eqv _ _ 1 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 80))
    by (rewrite (getr_of_eqv _ _ 2 X2 eq_refl); simp_regs; exact T2).
  assert (E2_4 : getr R2 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X2 eq_refl); simp_regs; exact T4).
  assert (E2_10 : getr R2 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 10 X2 eq_refl); simp_regs; exact T9).
  assert (E2_11 : getr R2 11 = Z_to_bv 64 (bv_unsigned (sa_sel (getr regs_t 19)))).
  { rewrite (getr_of_eqv _ _ 11 X2 eq_refl). simp_regs. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (KR2 : sa_kx [2; 8; 9; 18; 19; 20] regs R2) by (apply (sa_kx_trans _ regs regs_t R2 KT); sa_kx_tac X2).
  assert (SP2 : spZ R2 = bv_unsigned sp - 80) by (unfold spZ; rewrite E2_2; apply unsigned_lit; lia).
  assert (E2_8 : getr R2 8 = Z_to_bv 64 id) by (rewrite (getr_of_eqv _ _ 8 X2 eq_refl); simp_regs; exact T8).
  assert (E2_9 : getr R2 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 9 X2 eq_refl); simp_regs; exact T9).
  assert (E2_18 : getr R2 18 = Z_to_bv 64 pc) by (rewrite (getr_of_eqv _ _ 18 X2 eq_refl); simp_regs; exact T18).
  assert (E2_20 : getr R2 20 = Z_to_bv 64 0x108b0)
    by (rewrite (getr_of_eqv _ _ 20 X2 eq_refl); simp_regs; reflexivity).
  assert (SRCp : arg_s_src B Lc Ac (bv_unsigned sp - 80) mc (bv_unsigned (sa_sel (getr regs_t 19)))
                   (Some (darg vp (bstr "-"%string)))).
  { rewrite T19. apply (sa_src SUP_ADD_K (bv_unsigned sp) L A mem md O Lc Ac mc mdc _ Oc b pp vp _ SI RA).
    - unfold SUP_ADD_K, ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
    - lia.
    - unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
    - exact SPL. }
  apply (sinv_arg_sn (fx := fx) B API SEGS ERRNO_LOW GFACT GOWN AX (ARGS fx) SUP_ADD_K (bv_unsigned sp) L A mem md O
           Lc Ac mc mdc R REC_ADD As Oc b R2 (bv_unsigned (sa_sel (getr regs_t 19))) (Some (darg vp (bstr "-"%string)))
           _ SI).
  { rewrite LA2. lia. }
  { rewrite E2_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP2. replace (bv_unsigned sp - 80) with (bv_unsigned sp + (-5) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP2. unfold SUP_ADD_K, ARG_S_K, XMALLOC_K, ALLOC_STACK. lia. }
  { rewrite SP2. lia. }
  { rewrite E2_4. exact HTP. }
  { exact E2_10. }
  { exact E2_11. }
  { rewrite SP2. exact SRCp. }
  { exact ROOM1. }
  intros L2 A2 regs2 m2 md2 p SI3 SH3 INIT3 RP3 KST3.
  rewrite E2_1.
  assert (FR3 : rw_cells rsegs m2 (bv_unsigned sp - 48)
    [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs mc); [exact FR|]. intros i Hi. cbn in Hi.
    destruct (KST3 (bv_unsigned sp - 48 + i)) as [Ea Eb]; [rewrite SP2; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  assert (U18 : getr regs2 18 = Z_to_bv 64 pc) by exact (eq_trans (RP3 18 ltac:(unfold callee_saved; lia)) E2_18).
  apply (sa_cl L A regs mem md O L2 A2 m2 md2 R (As ++ [darg vp (bstr "-"%string)])
           (Oc ++ [(p, Z.of_nat (length (darg vp (bstr "-"%string))) + 1)]) b
           (sb_malloc bpre (Z.of_nat (length (darg vp (bstr "-"%string))) + 1)) regs2 id
           (Some (darg vc (bstr "-"%string))) PRE SI3 H16).
  - rewrite length_app, LA2. reflexivity.
  - exact LXA.
  - exact HID.
  - change (spZ regs) with (bv_unsigned sp). rewrite U18.
    apply (sa_src SUP_ADD_K (bv_unsigned sp) L A mem md O L2 A2 m2 md2 _ _ b pc vc _ SI3 RA).
    + unfold SUP_ADD_K, ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
    + lia.
    + unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia.
    + exact SCL.
  - rewrite SH3. apply sb_malloc_mono. exact BLE.
  - rewrite SH3. exact ROOM2.
  - exact ROOM.
  - exact FRM.
  - exact FR3.
  - exact (eq_trans (RP3 2 ltac:(unfold callee_saved; lia)) E2_2).
  - exact (eq_trans (RP3 8 ltac:(unfold callee_saved; lia)) E2_8).
  - exact (eq_trans (RP3 9 ltac:(unfold callee_saved; lia)) E2_9).
  - exact (eq_trans (RP3 20 ltac:(unfold callee_saved; lia)) E2_20).
  - exact (eq_trans (RP3 4 ltac:(unfold callee_saved; lia)) E2_4).
  - exact (sa_kx_trans _ _ _ _ KR2 (sa_kx_of_pres _ _ _ RP3)).
Qed.

End H.

Lemma sa_m_len : forall R As id, -2^31 <= id < 2^31 -> -2^31 <= r_code R < 2^31 ->
  (6 <= length (snd (sa_m R As id)) <= 16)%nat.
Proof.
  intros R As id H HC. unfold sa_m. cbv zeta.
  assert (HC1 : -2^31 <= r_code (rec_record R REC_ADD As) < 2^31) by (rewrite CF.sup_remove.srm_code_record; exact HC).
  destruct ((id <? 0) || (10000 <=? id)); [exact (resp_length (-1) ltac:(lia))|].
  destruct (negb (r_refuse (rec_record R REC_ADD As) =? 0));
    [exact (resp_length _ HC1) | exact (resp_length id H)].
Qed.

Lemma sa_mod8 : forall s0 k, s0 mod 16 = 0 -> 1 <= k <= 11 -> (- (s0 - 80 + k + 1)) mod 8 <= 15 - k.
Proof. intros s0 k H1 H2. Z.div_mod_to_equations. lia. Qed.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis GRD : ms_guard B = 0x54730.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis REC : record_contract B API.
Hypothesis SNP : snprintf_contract.
Hypothesis HB : forall fx0 : YK11.FPState, @hand_back_contract fx0 rc B API.
Hypothesis MIX : mix_call_contract.
Hypothesis ANSF : forall fx0 : YK11.FPState, @answer_contract fx0 rc B API.
Hypothesis ARGS : forall fx0 : YK11.FPState, @arg_s_contract fx0 rc B API.

Theorem sup_add_holds : sup_add_contract B API.
Proof using SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK REC SNP HB MIX ANSF ARGS.
  unfold sup_add_contract.
  intros L A regs mem md pu pp pc uri id pl cl R O b PRE AU AI HID APL ACL SU SPL SCL GR RA FRM F18 RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & HTS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_ADD_K in HCEIL, HWS. unfold TASK_SIZE in HTS.
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  rewrite SEGS in GR, RA, F18, HWS |- *.
  change (sup_add_m R uri id pl cl) with (sa_m R [sarg uri; dec id; darg pl (bstr "-"%string); darg cl (bstr "-"%string)] id)
    in ROOM.
  unfold sb_mallocs, sup_add_sizes in ROOM. cbn [fold_left] in ROOM.
  pose proof (sinv_init B API SUP_ADD_K L A regs mem md R O b PRK ltac:(unfold SUP_ADD_K; lia) GR RA F18 RES) as SI0.
  pose proof GR as (Q0 & (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & HCODE & _) & _) & _).
  pose proof (rec_rep_calls_le _ _ _ _ _ _ _ _ GR) as H16.
  pose proof (dec_length id HID) as DL.
  pose proof (sa_m_len R [sarg uri; dec id; darg pl (bstr "-"%string); darg cl (bstr "-"%string)] id HID HCODE) as TL.
  destruct (rec_entry_bounds R H16) as (EB1 & EB2 & EB3).
  set (e := rec_entry G_REC REC_SC R) in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (sarg_facts B _ _ _ _ _ _ (sinv_arg_src B API SEGS ERRNO_LOW SLACK SUP_ADD_K (bv_unsigned sp) L A mem md O
    L A mem md R O b pu uri (bv_unsigned sp - 80) SI0 RA ltac:(unfold SUP_ADD_K, ARG_S_K, XMALLOC_K, ALLOC_STACK; lia)
    ltac:(lia) SU)) as (_ & LU).
  pose proof (sarg_facts B _ _ _ _ _ _ (sa_src B API SEGS ERRNO_LOW SLACK SUP_ADD_K (bv_unsigned sp) L A mem md O
    L A mem md R O b pp pl (bv_unsigned sp - 80) SI0 RA ltac:(unfold SUP_ADD_K, ARG_S_K, XMALLOC_K, ALLOC_STACK; lia)
    ltac:(lia) ltac:(unfold ARG_S_K, XMALLOC_K, ALLOC_STACK; lia) SPL)) as (_ & LP).
  pose proof (sarg_facts B _ _ _ _ _ _ (sa_src B API SEGS ERRNO_LOW SLACK SUP_ADD_K (bv_unsigned sp) L A mem md O
    L A mem md R O b pc cl (bv_unsigned sp - 80) SI0 RA ltac:(unfold SUP_ADD_K, ARG_S_K, XMALLOC_K, ALLOC_STACK; lia)
    ltac:(lia) ltac:(unfold ARG_S_K, XMALLOC_K, ALLOC_STACK; lia) SCL)) as (_ & LC).
  cbn [sarg] in LP, LC.
  assert (ST0 : stk rsegs mem (bv_unsigned sp - 12464) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. unfold SUP_ADD.
    eapply sa_run0 with (lo := bv_unsigned sp - 12464); [exact ST0 | lia | lia]. }
  intros ms1 (can1 & (m1 & -> & MU1 & WM1 & FR1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x16034) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 80))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 id) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; exact AI).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 0) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_18 : getr R1 18 = Z_to_bv 64 pc) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); simp_regs; exact ACL).
  assert (E1_19 : getr R1 19 = Z_to_bv 64 pp) by (rewrite (getr_of_eqv _ _ 19 X1 eq_refl); simp_regs; exact APL).
  assert (E1_20 : getr R1 20 = Z_to_bv 64 pu) by (rewrite (getr_of_eqv _ _ 20 X1 eq_refl); simp_regs; exact AU).
  assert (KR1 : sa_kx [2; 8; 9; 18; 19; 20] regs R1) by sa_kx_tac X1.
  assert (SP1 : spZ R1 = bv_unsigned sp - 80) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  pose proof (sinv_stack B API SEGS GOWN AX SUP_ADD_K (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                ltac:(intros a Ra Hm; cbn in Hm; unfold SUP_ADD_K; lia)) as SI1.
  apply (sinv_record B API SEGS ERRNO_LOW AX REC SUP_ADD_K (bv_unsigned sp) L A mem md O L A m1 md R O b R1 REC_ADD _
           SI1).
  { rewrite E1_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP1. replace (bv_unsigned sp - 80) with (bv_unsigned sp + (-5) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP1. unfold SUP_ADD_K, RECORD_K, ALLOC_STACK. lia. }
  { rewrite SP1. lia. }
  { rewrite E1_4. exact HTP. }
  { exact E1_10. }
  { unfold REC_FN_COUNT, REC_ADD. lia. }
  intros L1 A1 regs_r m_r md_r O_r SIr BLEr RPr R10 KSTr.
  rewrite E1_1.
  pose proof SIr as (RJr & GRr & ONr & B1r & B2r & RAr & F18r & RESr).
  pose proof RJr as (HMr & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HMr) as (Hhr & Hlr & _).
  rewrite sb_shift_refl in BLEr. pose proof BLEr as (BL1 & BL2 & BL3).
  assert (Er2 : getr regs_r 2 = Z_to_bv 64 (bv_unsigned sp - 80))
    by exact (eq_trans (RPr 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (Er4 : getr regs_r 4 = reg_get regs 4) by exact (eq_trans (RPr 4 ltac:(unfold callee_saved; lia)) E1_4).
  assert (Er8 : getr regs_r 8 = Z_to_bv 64 id) by exact (eq_trans (RPr 8 ltac:(unfold callee_saved; lia)) E1_8).
  assert (Er18 : getr regs_r 18 = Z_to_bv 64 pc) by exact (eq_trans (RPr 18 ltac:(unfold callee_saved; lia)) E1_18).
  assert (Er19 : getr regs_r 19 = Z_to_bv 64 pp) by exact (eq_trans (RPr 19 ltac:(unfold callee_saved; lia)) E1_19).
  assert (Er20 : getr regs_r 20 = Z_to_bv 64 pu) by exact (eq_trans (RPr 20 ltac:(unfold callee_saved; lia)) E1_20).
  assert (KRr : sa_kx [2; 8; 9; 18; 19; 20] regs regs_r) by exact (sa_kx_trans _ _ _ _ KR1 (sa_kx_of_pres _ _ _ RPr)).
  assert (FRr : rw_cells rsegs m_r (bv_unsigned sp - 48)
    [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
     C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    destruct (KSTr (bv_unsigned sp - 48 + i)) as [Ea Eb]; [rewrite SP1; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  eapply evt_SR_canon; [ | exact Hhr | exact Hlr | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply sa_run1. }
  intros ms2 (can2 & E2 & EQ2). subst can2.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
  assert (E2_1 : getr R2 1 = Z_to_bv 64 0x16040) by (rewrite (getr_of_eqv _ _ 1 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 80))
    by (rewrite (getr_of_eqv _ _ 2 X2 eq_refl); simp_regs; exact Er2).
  assert (E2_4 : getr R2 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X2 eq_refl); simp_regs; exact Er4).
  assert (E2_8 : getr R2 8 = Z_to_bv 64 id) by (rewrite (getr_of_eqv _ _ 8 X2 eq_refl); simp_regs; exact Er8).
  assert (E2_9 : getr R2 9 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 9 X2 eq_refl); simp_regs; exact R10).
  assert (E2_10 : getr R2 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X2 eq_refl); simp_regs; exact R10).
  assert (E2_11 : getr R2 11 = Z_to_bv 64 pu) by (rewrite (getr_of_eqv _ _ 11 X2 eq_refl); simp_regs; exact Er20).
  assert (E2_18 : getr R2 18 = Z_to_bv 64 pc) by (rewrite (getr_of_eqv _ _ 18 X2 eq_refl); simp_regs; exact Er18).
  assert (E2_19 : getr R2 19 = Z_to_bv 64 pp) by (rewrite (getr_of_eqv _ _ 19 X2 eq_refl); simp_regs; exact Er19).
  assert (KR2 : sa_kx [2; 8; 9; 18; 19; 20] regs R2) by (apply (sa_kx_trans _ regs regs_r R2 KRr); sa_kx_tac X2).
  assert (SP2 : spZ R2 = bv_unsigned sp - 80) by (unfold spZ; rewrite E2_2; apply unsigned_lit; lia).
  apply (sinv_arg_s (fx := fx) B API SEGS ERRNO_LOW GFACT GOWN AX (ARGS fx) SUP_ADD_K (bv_unsigned sp) L A mem md O
           L1 A1 m_r md_r R REC_ADD O_r b R2 pu uri _ SIr).
  { rewrite E2_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP2. replace (bv_unsigned sp - 80) with (bv_unsigned sp + (-5) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP2. unfold SUP_ADD_K, ARG_S_K, XMALLOC_K, ALLOC_STACK. lia. }
  { rewrite SP2. lia. }
  { rewrite E2_4. exact HTP. }
  { exact E2_10. }
  { exact E2_11. }
  { rewrite SP2. exact (sinv_arg_src B API SEGS ERRNO_LOW SLACK SUP_ADD_K (bv_unsigned sp) L A mem md O
      L1 A1 m_r md_r _ O_r b pu uri (bv_unsigned sp - 80) SIr RA ltac:(unfold SUP_ADD_K, ARG_S_K, XMALLOC_K, ALLOC_STACK; lia)
      ltac:(lia) SU). }
  { refine (room_slots_mono _ _ _ _ _ _ ROOM).
    - unfold sb_le, sb_malloc. cbn [sb_live sb_bytes sb_cap]. lia.
    - unfold LMAX in *. lia. }
  intros L2 A2 regs2 m2 md2 p2 SI2 SH2 INIT2 RP2 KST2.
  rewrite E2_1.
  pose proof SI2 as (RJ2 & GR2 & ON2 & B12 & B22 & RA2 & F182 & RES2).
  pose proof RJ2 as (HM2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC2 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM2) as (Hh2 & Hl2 & _).
  assert (Q2_2 : reg_get regs2 2 = Z_to_bv 64 (bv_unsigned sp - 80))
    by exact (eq_trans (RP2 2 ltac:(unfold callee_saved; lia)) E2_2).
  assert (Q2_4 : getr regs2 4 = reg_get regs 4) by exact (eq_trans (RP2 4 ltac:(unfold callee_saved; lia)) E2_4).
  assert (Q2_8 : reg_get regs2 8 = Z_to_bv 64 id) by exact (eq_trans (RP2 8 ltac:(unfold callee_saved; lia)) E2_8).
  assert (Q2_9 : reg_get regs2 9 = Z_to_bv 64 e) by exact (eq_trans (RP2 9 ltac:(unfold callee_saved; lia)) E2_9).
  assert (Q2_18 : getr regs2 18 = Z_to_bv 64 pc) by exact (eq_trans (RP2 18 ltac:(unfold callee_saved; lia)) E2_18).
  assert (Q2_19 : getr regs2 19 = Z_to_bv 64 pp) by exact (eq_trans (RP2 19 ltac:(unfold callee_saved; lia)) E2_19).
  assert (KR2' : sa_kx [2; 8; 9; 18; 19; 20] regs regs2) by exact (sa_kx_trans _ _ _ _ KR2 (sa_kx_of_pres _ _ _ RP2)).
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 48)
    [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
     C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m_r); [exact FRr|]. intros i Hi. cbn in Hi.
    destruct (KST2 (bv_unsigned sp - 48 + i)) as [Ea Eb]; [rewrite SP2; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  pose proof F182 as (GG2 & canary & GW2).
  assert (GGb : bytes_at rsegs m2 snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD))).
  { destruct GG2 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GWb : bytes_at rsegs m2 snprintf_c.GUARD (Mem.le8 canary)).
  { destruct GW2 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (STn : stk rsegs (normalize_cj rsegs m2) (bv_unsigned sp - 12464) (bv_unsigned sp - 64)).
  { apply stk_normalize_cj; [lia | unfold TASK_SIZE; lia | intros a Ha; rewrite <- SEGS; apply HSC2; left; unfold SUP_ADD_K; lia]. }
  pose proof (bytes_at_normalize_cj_low rsegs m2 snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD)) RA2
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GOT_GUARD, TASK_SIZE; lia) GGb) as GGn.
  pose proof (bytes_at_normalize_cj_low rsegs m2 snprintf_c.GUARD (Mem.le8 canary) RA2
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GUARD, TASK_SIZE; lia) GWb) as GWn.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q2_8, Q2_9, Q2_2.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RA2 |].
    eapply (sa_run2 SNP) with (lo := bv_unsigned sp - 12464) (canary := canary).
    - exact HID.
    - rewrite unsigned_lit by lia. replace (bv_unsigned sp - 80 + 16) with (bv_unsigned sp - 64) by ring. exact STn.
    - rewrite unsigned_lit by lia. unfold SNPRINTF_K. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - exact FRM.
    - exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs m2)).
    - exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs m2)).
    - exact GGn.
    - exact GWn. }
  intros ms3 (can3 & (s3n & Q3' & REL3 & RO3) & EQ3).
  unfold sa_mid2 in Q3'.
  destruct Q3' as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F1 & fc1 & m3n & slack
    & -> & MU3n & WM3n & MI3n & FRM1 & FK1 & SL & BUF3n).
  destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL3) as [EC3 MR3r].
  revert EC3 MR3r RO3 EQ3. generalize (ms_mem can3) as m3. intros m3 EC3 MR3r RO3 EQ3. subst can3.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ (mem_rel_cj_normalize rsegs m2 RA2) MR3r RO3 MU3n) as MU3.
  pose proof (wmono_rel_cj rsegs _ _ _ _ (mem_rel_cj_normalize rsegs m2 RA2) MR3r RO3 WM3n) as WM3.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR3r BUF3n) as BUF3.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ3) as (R3 & -> & X3).
  clear MU3n WM3n MI3n BUF3n EQ3 MR3r.
  rewrite unsigned_lit in MU3, BUF3 by lia.
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x16064) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 80))
    by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_4 : getr R3 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X3 eq_refl); simp_regs; exact Q2_4).
  assert (E3_8 : getr R3 8 = Z_to_bv 64 id) by (rewrite (getr_of_eqv _ _ 8 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_9 : getr R3 9 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 9 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_10 : getr R3 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_11 : getr R3 11 = Z_to_bv 64 (bv_unsigned sp - 80))
    by (rewrite (getr_of_eqv _ _ 11 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_18 : getr R3 18 = Z_to_bv 64 pc) by (rewrite (getr_of_eqv _ _ 18 X3 eq_refl); simp_regs; exact Q2_18).
  assert (E3_19 : getr R3 19 = Z_to_bv 64 pp) by (rewrite (getr_of_eqv _ _ 19 X3 eq_refl); simp_regs; exact Q2_19).
  assert (KR3 : sa_kx [2; 8; 9; 18; 19; 20] regs R3) by (apply (sa_kx_trans _ regs regs2 R3 KR2'); sa_kx_tac X3).
  assert (SP3 : spZ R3 = bv_unsigned sp - 80) by (unfold spZ; rewrite E3_2; apply unsigned_lit; lia).
  pose proof (sinv_stack B API SEGS GOWN AX SUP_ADD_K (bv_unsigned sp) L A mem md O L2 A2 m2 md2 _ _ b m3 _ SI2 MU3 WM3
                ltac:(intros a Ra Hm; cbn in Hm; unfold SUP_ADD_K; lia)) as SI3.
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 48)
    [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
     C8 (reg_get regs 1)]).
  { apply (rw_out rsegs _ m2 m3 _ _ FR2 MU3). intros i Hi. cbn in Hi. split; [lia|]. cbn [outside].
    split; [lia | exact I]. }
  apply (sinv_arg_sn (fx := mkFP F1 fc1) B API SEGS ERRNO_LOW GFACT GOWN AX (ARGS _) SUP_ADD_K (bv_unsigned sp) L A mem md
           O L2 A2 m3 md2 R REC_ADD [sarg uri] (O_r ++ [(p2, Z.of_nat (length (sarg uri)) + 1)]) b R3
           (bv_unsigned sp - 80) (Some (dec id)) _ SI3).
  { cbn [length]. lia. }
  { rewrite E3_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP3. replace (bv_unsigned sp - 80) with (bv_unsigned sp + (-5) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP3. unfold SUP_ADD_K, ARG_S_K, XMALLOC_K, ALLOC_STACK. lia. }
  { rewrite SP3. lia. }
  { rewrite E3_4. exact HTP. }
  { exact E3_10. }
  { exact E3_11. }
  { cbn [arg_s_src]. rewrite SP3, SEGS.
    split; [lia|]. split; [apply dec_no0|]. split; [unfold LMAX; lia|].
    exists slack. split; [exact BUF3|].
    split; [rewrite SL; pose proof (sa_mod8 (bv_unsigned sp) (Z.of_nat (length (dec id))) HAL ltac:(lia)); lia|].
    split; [right; lia|]. left. split; lia. }
  { rewrite SH2. cbn [sarg]. refine (room_slots_mono _ _ _ _ _ _ ROOM).
    - unfold sb_le, sb_malloc. cbn [sb_live sb_bytes sb_cap]. lia.
    - unfold LMAX in *. lia. }
  intros L3 A3 regs3 m4 md3 p3 SI4 SH3 INIT3 RP3 KST3.
  rewrite E3_1.
  assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp - 48)
    [C8 (reg_get regs 20); C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
     C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m3); [exact FR3|]. intros i Hi. cbn in Hi.
    destruct (KST3 (bv_unsigned sp - 48 + i)) as [Ea Eb]; [rewrite SP3; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  eapply SR_mono.
  { apply (sa_pl (fx := mkFP F1 fc1) B API SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX CTX SLACK SNP HB MIX ANSF ARGS
             L A regs mem md O L3 A3 m4 md3 R [sarg uri; dec id]
             ((O_r ++ [(p2, Z.of_nat (length (sarg uri)) + 1)]) ++ [(p3, Z.of_nat (length (dec id)) + 1)]) b
             (sb_malloc (sb_malloc b (Z.of_nat (length (sarg uri)) + 1)) (Z.of_nat (length (dec id)) + 1))
             regs3 id pl cl pp pc PRE SI4 H16).
    - reflexivity.
    - cbn [app]. repeat (apply Forall_cons; [unfold LMAX in *; lia|]). apply Forall_nil.
    - exact HID.
    - exact RA.
    - exact SPL.
    - exact SCL.
    - exact (eq_trans (RP3 19 ltac:(unfold callee_saved; lia)) E3_19).
    - exact (eq_trans (RP3 18 ltac:(unfold callee_saved; lia)) E3_18).
    - rewrite SH3, SH2. cbn [sarg]. unfold sb_le, sb_malloc. cbn [sb_live sb_bytes sb_cap]. lia.
    - rewrite SH3, SH2. cbn [sarg]. refine (room_slots_mono _ _ _ _ _ _ ROOM).
      + unfold sb_le, sb_malloc. cbn [sb_live sb_bytes sb_cap]. lia.
      + unfold LMAX in *. lia.
    - rewrite SH3, SH2. cbn [sarg]. refine (room_slots_mono _ _ _ _ _ _ ROOM).
      + unfold sb_le, sb_malloc. cbn [sb_live sb_bytes sb_cap]. lia.
      + unfold LMAX in *. lia.
    - cbn [app]. refine (room_slots_mono _ _ _ _ _ _ ROOM).
      + apply sb_le_refl.
      + unfold LMAX in *. lia.
    - cbn [fp_csr]. exact FRM1.
    - exact FR4.
    - exact (eq_trans (RP3 2 ltac:(unfold callee_saved; lia)) E3_2).
    - exact (eq_trans (RP3 8 ltac:(unfold callee_saved; lia)) E3_8).
    - exact (eq_trans (RP3 9 ltac:(unfold callee_saved; lia)) E3_9).
    - exact (eq_trans (RP3 4 ltac:(unfold callee_saved; lia)) E3_4).
    - exact (sa_kx_trans _ _ _ _ KR3 (sa_kx_of_pres _ _ _ RP3)). }
  intros c' (fx' & L' & A' & regs' & mem' & md' & O' & q & -> & FPK & REST).
  exists fx', L', A', regs', mem', md', (fst (sup_add_m R uri id pl cl)), O', (snd (sup_add_m R uri id pl cl)), q.
  split; [apply surjective_pairing|].
  split; [reflexivity|].
  split.
  { destruct FPK as [FZ' FK']. split; [exact FZ'|]. intros r Hr. rewrite (FK' r Hr). cbn [fp_regs].
    apply FK1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    unfold fs_saved in Hr. rewrite Z.mod_small by lia. lia. }
  exact REST.
Qed.

End P.
