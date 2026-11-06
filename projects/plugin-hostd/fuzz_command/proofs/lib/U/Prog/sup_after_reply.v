(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 1051 of its 1066 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_open.v, with its module paths, module names and numbers changed; 647 of its 708 lines of code are new or changed and 1005 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/arg_i.v, with its module paths, addresses and numbers changed; 388 of its 482 lines of code are new or changed and 614 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import printf_facts_c snprintf_c RecAns.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma sar_pf_dec : forall v, (-2^31 <= v < 2^31)%Z -> pf_bytes (pf_dec v) = dec v.
Proof.
  intros c Hc. unfold pf_dec, dec. unfold pf_bytes.
  assert (P : (10 ^ Z.of_nat (S 9) = 10000000000)%Z) by reflexivity.
  destruct (Z.ltb_spec c 0) as [N|N].
  - cbn [map app]. f_equal. replace (Z.abs c) with (- c)%Z by lia.
    exact (pf_digits_digits 9 11 (- c) [] ltac:(rewrite P; lia) ltac:(lia)).
  - cbn [app]. replace (Z.abs c) with c by lia.
    exact (pf_digits_digits 9 11 c [] ltac:(rewrite P; lia) ltac:(lia)).
Qed.

Definition SAR_FMT : list Z := [37%Z; 100%Z].
Definition SAR_PS : list pf_piece := [Pd].

Lemma sar_parse : pf_parse SAR_FMT = Some SAR_PS.
Proof. reflexivity. Qed.

Lemma sar_text : forall v, pf_text SAR_PS [AInt v] = Some (pf_dec v).
Proof. intros v. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma sar_fmt_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10828 (pf_bytes (SAR_FMT ++ [0%Z])).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma sar_run0 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> (lo + 48 <= bv_unsigned sp)%Z -> (2 ^ 21 <= lo)%Z ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x1705c) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 a1 a0 (Z_to_bv 64 19)
                     a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1612c) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp - 32)%Z [C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17038) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  carve_frame 16%nat ST.
  clear FR0.
  do 9 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  split; [eassumption|]. split; eassumption.
Qed.

Definition sar_mid1 (sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo v e : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' slack,
    ms' = MS (mkR (Z_to_bv 64 0x17084) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 v) (Z_to_bv 64 e) sp
                  a2 a3 a4 a5 a6 a7 (Z_to_bv 64 e) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 0x161c4) fc' None m' (seg_rom rsegs)
    /\ munch [(lo, bv_unsigned sp + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k)
    /\ length slack = (15 - length (dec v))%nat
    /\ bytes_at rsegs m' (bv_unsigned sp) (dec v ++ Z_to_bv 8 0 :: slack).

Lemma sar_run1 : snprintf_contract ->
  forall ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo v e : Z) (canary : word),
  (-2^31 <= v < 2^31)%Z ->
  stk rsegs m lo (bv_unsigned sp + 16) -> (lo + SNPRINTF_K <= bv_unsigned sp)%Z -> (2 ^ 21 <= lo)%Z ->
  (bv_unsigned sp + 16 < 2^63)%Z ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> (bv_unsigned sp + 16 <= TASK_SIZE)%Z ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  evt rsegs (sar_mid1 sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo v e m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 v) (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x1705c) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v e canary HV ST LO IE S63 FRM MI TM HTS GG GW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold SNPRINTF_K, IMG_END, GOT_GUARD, GUARD in *.
  pose proof (dec_length v HV) as DL.
  pose proof (sar_pf_dec v HV) as PD.
  assert (TL : length (pf_dec v) = length (dec v)) by (rewrite <- PD; unfold pf_bytes; rewrite length_map; reflexivity).
  carve_frame 16%nat ST.
  match type of ST with stk _ _ _ ?h => replace h with (bv_unsigned sp) in ST by lia end.
  match type of FR with rw_cells _ _ ?h _ => replace h with (bv_unsigned sp) in FR by lia end.
  do 7 step.
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
  assert (BJ : bytes_at rsegs m (bv_unsigned sp) junk).
  { destruct FR as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_bound _ _ _ _ BJ) as BJL.
  assert (JL : length junk = 16%nat) by (destruct FR as [[[HJ _] _] _]; exact HJ).
  eapply evt_cut.
  { eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo canary SAR_FMT SAR_PS
              [AInt v] (pf_dec v) junk).
    - rewrite unsigned_lit by lia. apply sar_fmt_at. exact MI.
    - rewrite unsigned_lit by lia. unfold RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold RO_END, SAR_FMT. cbn [length]. lia.
    - exact sar_parse.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact HV | apply lit_mod32].
    - exact (sar_text v).
    - rewrite !unsigned_lit by lia. exact FR.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - lia.
    - right. lia.
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
  replace (ret_pc (Z_to_bv 64 0x17078)) with (Z_to_bv 64 0x17078) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct (bytes_at_firstn_skipn _ _ _ _ (S (length (pf_dec v))) BJ) as [_ BJT].
  rewrite firstn_length_le in BJT by lia.
  assert (BJT2 : bytes_at rsegs m2 (bv_unsigned sp + Z.of_nat (S (length (pf_dec v))))%Z
                   (skipn (S (length (pf_dec v))) junk)).
  { apply (bytes_at_transport rsegs _ m m2 _ _ BJT MU2). cbn [disjoint_from]. rewrite length_skipn.
    split; [lia | split; [lia | exact I]]. }
  assert (PB : pf_bytes (pf_dec v ++ [0%Z]) = dec v ++ [Z_to_bv 8 0]).
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
  apply evt_done. unfold sar_mid1.
  do 16 eexists. exists (skipn (S (length (pf_dec v))) junk). split; [reflexivity|].
  split.
  { eapply munch_weaken; [|exact MU2].
    unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | split; [lia | exact I]]. }
  split; [eapply wmono_trans; [apply wmono_refl | exact WM2]|].
  split; [exact MI2|]. split; [exact FRM2|]. split; [exact FK|].
  split; [rewrite length_skipn, JL, TL; lia|].
  exact BUF.
Qed.

Lemma sar_run2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x17090) sp gp tp t0 t1 t2 s0 s1 s2 s0 a2
                                      a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17084) fc None m (seg_rom rsegs)).
Proof. intros. do 3 step. apply evt_done. reflexivity. Qed.

Lemma sar_run3 :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s00 s01 s02 : word),
  rw_cells rsegs m (bv_unsigned sp0 + -32)%Z [C8 s02; C8 s01; C8 s00; C8 ra0] -> (48 <= bv_unsigned sp0)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s00 s01 a0 a1 a2 a3 a4 a5 a6 a7
                                      s02 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc ra0) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + -48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17090) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s00 s01 s02 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 6 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 + -48 + 48)) with sp0
    by (replace (bv_unsigned sp0 + -48 + 48)%Z with (bv_unsigned sp0) by ring; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB RecSeq RecStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecGlue RecTail RecAnsB RecStubU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import xmalloc_c record_c arg_s_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import sup_after_reply_c.
Local Open Scope Z_scope.

Definition sar_kept (R R' : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).

Lemma sar_kept_trans : forall R1 R2 R3, sar_kept R1 R2 -> sar_kept R2 R3 -> sar_kept R1 R3.
Proof.
  intros R1 R2 R3 H1 H2 r Hr N2 N8 N9 N18. rewrite (H2 r Hr N2 N8 N9 N18). exact (H1 r Hr N2 N8 N9 N18).
Qed.

Lemma sar_kept_of_pres : forall R R', regs_preserved R R' -> sar_kept R R'.
Proof. intros R R' H r Hr _ _ _ _. exact (H r Hr). Qed.

Ltac sar_kept_tac X :=
  intros rr Hrr Nrr2 Nrr8 Nrr9 Nrr18; unfold callee_saved in Hrr;
  assert (CC : rr = 3 \/ rr = 4 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/
               rr = 25 \/ rr = 26 \/ rr = 27) by lia;
  clear Hrr Nrr2 Nrr8 Nrr9 Nrr18;
  repeat (destruct CC as [CC|CC]; [subst rr; match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
    simp_regs; first [reflexivity | unfold getr; reflexivity]|]);
  subst rr; match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X eq_refl) end;
  simp_regs; first [reflexivity | unfold getr; reflexivity].

Lemma sar_pres : forall (regs R : bvmap 5 word), sar_kept regs R ->
  getr R (Z_to_bv 5 2) = getr regs (Z_to_bv 5 2) -> getr R (Z_to_bv 5 8) = getr regs (Z_to_bv 5 8) ->
  getr R (Z_to_bv 5 9) = getr regs (Z_to_bv 5 9) -> getr R (Z_to_bv 5 18) = getr regs (Z_to_bv 5 18) ->
  regs_preserved regs R.
Proof.
  intros regs R KR E2 E8 E9 E18 r Hr.
  destruct (Z.eq_dec r 2) as [->|N2]; [exact E2|].
  destruct (Z.eq_dec r 8) as [->|N8]; [exact E8|].
  destruct (Z.eq_dec r 9) as [->|N9]; [exact E9|].
  destruct (Z.eq_dec r 18) as [->|N18]; [exact E18|].
  exact (KR r Hr N2 N8 N9 N18).
Qed.

Lemma sar_mod8 : forall s0 k, s0 mod 16 = 0 -> 1 <= k <= 11 -> (- (s0 - 48 + k + 1)) mod 8 <= 15 - k.
Proof. intros s0 k H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma sar_malloc_le2 : forall b b' n n', sb_le b b' -> n <= n' -> sb_le (sb_malloc b n) (sb_malloc b' n').
Proof. intros b b' n n' H Hn. unfold sb_le, sb_malloc in *. cbn. lia. Qed.

Section Main.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis REC : record_contract B API.
Hypothesis SNP : snprintf_contract.
Hypothesis ARGS : forall fx' : YK11.FPState, @arg_s_contract fx' rc B API.

Theorem sup_after_reply_holds : sup_after_reply_contract B API.
Proof using SEGS ERRNO_LOW GFACT GOWN AX CTX SLACK REC SNP ARGS.
  unfold sup_after_reply_contract.
  intros L A regs mem md id pv verb R O b PRE GA HID GP SA GR RA FRM F18 RES ROOM.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof ERRNO_LOW as EL.
  pose proof PRE as (PRK & HTS).
  change SUP_AFTER_REPLY_K with 8384 in PRK, SA |- *.
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  rewrite SEGS in GR, RA, F18, HWS |- *.
  pose proof (sinv_init B API 8384 L A regs mem md R O b PRK ltac:(lia) GR RA F18 RES) as SI0.
  pose proof (rec_rep_calls_le _ _ _ _ _ _ _ _ GR) as H16.
  pose proof (dec_length id HID) as DL.
  assert (LN : Z.of_nat (length (sarg verb)) <= LMAX).
  { destruct verb as [x|]; [destruct SA as (_ & _ & HL & _); exact HL | apply Z.leb_le; vm_compute; reflexivity]. }
  unfold sup_after_reply_sizes in ROOM.
  destruct (rec_entry_bounds R H16) as (EB1 & EB2 & EB3).
  set (e := rec_entry G_REC REC_SC R) in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST0 : stk rsegs mem (bv_unsigned sp - 8384) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. unfold SUP_AFTER_REPLY.
    eapply sar_run0 with (lo := bv_unsigned sp - 8384); [exact ST0 | lia | lia]. }
  intros ms1 (can1 & (m1 & -> & MU1 & WM1 & FR1) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x1705c) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 pv) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; exact GP).
  assert (E1_9 : getr R1 9 = Z_to_bv 64 id) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; exact GA).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 19) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (KR1 : sar_kept regs R1) by sar_kept_tac X1.
  assert (SP1 : spZ R1 = bv_unsigned sp - 48) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  pose proof (sinv_stack B API SEGS GOWN AX 8384 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
  apply (sinv_record B API SEGS ERRNO_LOW AX REC 8384 (bv_unsigned sp) L A mem md O L A m1 md R O b R1
           REC_AFTER_REPLY _ SI1).
  { rewrite E1_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP1. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP1. unfold RECORD_K, ALLOC_STACK. lia. }
  { rewrite SP1. lia. }
  { rewrite E1_4. exact HTP. }
  { exact E1_10. }
  { unfold REC_FN_COUNT, REC_AFTER_REPLY. lia. }
  intros L1 A1 regs_r m_r md_r O_r SIr BLEr RPr R10 KSTr.
  rewrite E1_1.
  pose proof SIr as (RJr & GRr & ONr & B1r & B2r & RAr & F18r & RESr).
  pose proof RJr as (HMr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSCr & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HMr) as (Hhr & Hlr & _).
  assert (Er2 : getr regs_r 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by exact (eq_trans (RPr 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (Er4 : getr regs_r 4 = reg_get regs 4) by exact (eq_trans (RPr 4 ltac:(unfold callee_saved; lia)) E1_4).
  assert (Er8 : getr regs_r 8 = Z_to_bv 64 pv) by exact (eq_trans (RPr 8 ltac:(unfold callee_saved; lia)) E1_8).
  assert (Er9 : getr regs_r 9 = Z_to_bv 64 id) by exact (eq_trans (RPr 9 ltac:(unfold callee_saved; lia)) E1_9).
  assert (KRr : sar_kept regs regs_r) by exact (sar_kept_trans _ _ _ KR1 (sar_kept_of_pres _ _ RPr)).
  assert (FRr : rw_cells rsegs m_r (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    destruct (KSTr (bv_unsigned sp - 32 + i)) as [Ea Eb]; [rewrite SP1; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  pose proof F18r as (GGr & canary & GWr).
  assert (GGb : bytes_at rsegs m_r snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD))).
  { destruct GGr as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GWb : bytes_at rsegs m_r snprintf_c.GUARD (Mem.le8 canary)).
  { destruct GWr as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (STn : stk rsegs (normalize_cj rsegs m_r) (bv_unsigned sp - 8384) (bv_unsigned sp - 32)).
  { apply stk_normalize_cj; [lia | lia | intros a Ha; rewrite <- SEGS; apply HSCr; left; lia]. }
  pose proof (bytes_at_normalize_cj_low rsegs m_r snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD)) RAr
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GOT_GUARD, TASK_SIZE; lia) GGb) as GGn.
  pose proof (bytes_at_normalize_cj_low rsegs m_r snprintf_c.GUARD (Mem.le8 canary) RAr
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GUARD, TASK_SIZE; lia) GWb) as GWn.
  assert (Q9 : reg_get regs_r 9 = Z_to_bv 64 id) by exact Er9.
  assert (Q10 : reg_get regs_r 10 = Z_to_bv 64 e) by exact R10.
  assert (Q2 : reg_get regs_r 2 = Z_to_bv 64 (bv_unsigned sp - 48)) by exact Er2.
  eapply evt_SR_canon; [ | exact Hhr | exact Hlr | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q9, Q10, Q2.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RAr |].
    eapply (sar_run1 SNP) with (lo := bv_unsigned sp - 8384) (canary := canary).
    - exact HID.
    - rewrite unsigned_lit by lia. replace (bv_unsigned sp - 48 + 16) with (bv_unsigned sp - 32) by ring. exact STn.
    - rewrite unsigned_lit by lia. unfold SNPRINTF_K. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - exact FRM.
    - exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs m_r)).
    - exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs m_r)).
    - rewrite unsigned_lit by lia. lia.
    - exact GGn.
    - exact GWn. }
  intros ms2 (can2 & (s2n & Q2' & REL2 & RO2) & EQ2).
  unfold sar_mid1 in Q2'.
  destruct Q2' as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F1 & fc1 & m2n & slack
    & -> & MU2n & WM2n & MI2n & FRM1 & FK1 & SL & BUF2n).
  destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL2) as [EC2 MR2r].
  revert EC2 MR2r RO2 EQ2. generalize (ms_mem can2) as m2. intros m2 EC2 MR2r RO2 EQ2. subst can2.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ (mem_rel_cj_normalize rsegs m_r RAr) MR2r RO2 MU2n) as MU2.
  pose proof (wmono_rel_cj rsegs _ _ _ _ (mem_rel_cj_normalize rsegs m_r RAr) MR2r RO2 WM2n) as WM2.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR2r BUF2n) as BUF2.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ2) as (R2 & -> & X2).
  clear MU2n WM2n MI2n BUF2n EQ2 MR2r.
  rewrite unsigned_lit in MU2, BUF2 by lia.
  assert (E2_1 : getr R2 1 = Z_to_bv 64 0x17084) by (rewrite (getr_of_eqv _ _ 1 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (rewrite (getr_of_eqv _ _ 2 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_4 : getr R2 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X2 eq_refl); simp_regs; exact Er4).
  assert (E2_8 : getr R2 8 = Z_to_bv 64 pv) by (rewrite (getr_of_eqv _ _ 8 X2 eq_refl); simp_regs; exact Er8).
  assert (E2_10 : getr R2 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_11 : getr R2 11 = Z_to_bv 64 (bv_unsigned sp - 48))
    by (rewrite (getr_of_eqv _ _ 11 X2 eq_refl); simp_regs; reflexivity).
  assert (E2_18 : getr R2 18 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 18 X2 eq_refl); simp_regs; reflexivity).
  assert (KR2 : sar_kept regs_r R2) by sar_kept_tac X2.
  assert (SP2 : spZ R2 = bv_unsigned sp - 48) by (unfold spZ; rewrite E2_2; apply unsigned_lit; lia).
  pose proof (sinv_stack B API SEGS GOWN AX 8384 (bv_unsigned sp) L A mem md O L1 A1 m_r md_r
                (rec_record R REC_AFTER_REPLY []) O_r b m2 _ SIr MU2 WM2 ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI2.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_out rsegs _ m_r m2 _ _ FRr MU2). intros i Hi. cbn in Hi. split; [lia|]. cbn [outside].
    split; [lia | exact I]. }
  apply (sinv_arg_s (fx := mkFP F1 fc1) B API SEGS ERRNO_LOW GFACT GOWN AX (ARGS _) 8384 (bv_unsigned sp) L A mem md O
           L1 A1 m2 md_r R REC_AFTER_REPLY O_r b R2 (bv_unsigned sp - 48) (Some (dec id)) _ SI2).
  { rewrite E2_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP2. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP2. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia. }
  { rewrite SP2. lia. }
  { rewrite E2_4. exact HTP. }
  { exact E2_10. }
  { exact E2_11. }
  { cbn [arg_s_src]. rewrite SP2, SEGS.
    split; [lia|]. split; [apply dec_no0|]. split; [unfold LMAX; lia|].
    exists slack. split; [exact BUF2|].
    split; [rewrite SL; pose proof (sar_mod8 (bv_unsigned sp) (Z.of_nat (length (dec id))) HAL ltac:(lia)); lia|].
    split; [right; lia|]. left. split; lia. }
  { cbn [sarg].
    apply (room_slots_mono _ (sb_mallocs b [Z.of_nat (length (dec id)) + 1; Z.of_nat (length (sarg verb)) + 1]) _
             (LMAX + 1)); [| unfold LMAX; lia | exact ROOM].
    unfold sb_mallocs. cbn [fold_left].
    rewrite sb_shift_refl in BLEr.
    apply (sb_le_trans _ (sb_malloc b (Z.of_nat (length (dec id)) + 1))); [exact (sb_malloc_mono _ _ _ BLEr)|].
    apply sb_le_malloc; lia. }
  intros L3 A3 R3 m3 md3 p SI3 EQB3 INIT3 PR3 KST3.
  rewrite E2_1.
  pose proof SI3 as (RJ3 & _).
  pose proof RJ3 as (HM3 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM3) as (Hh3 & Hl3 & _).
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m2); [exact FR2|]. intros i Hi. cbn in Hi.
    destruct (KST3 (bv_unsigned sp - 32 + i)) as [Ea Eb]; [rewrite SP2; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite canon_mkst. cbn [fp_regs fp_csr]. unfold Regs6ss.mkR_of. eapply sar_run2. }
  intros ms4 (can4 & Q4 & EQ4). subst can4.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ4) as (R4 & -> & X4). clear EQ4.
  assert (E4_1 : getr R4 1 = Z_to_bv 64 0x17090) by (rewrite (getr_of_eqv _ _ 1 X4 eq_refl); simp_regs; reflexivity).
  assert (E4_2 : getr R4 2 = Z_to_bv 64 (bv_unsigned sp - 48)).
  { rewrite (getr_of_eqv _ _ 2 X4 eq_refl); simp_regs. exact (eq_trans (PR3 2 ltac:(unfold callee_saved; lia)) E2_2). }
  assert (E4_4 : getr R4 4 = reg_get regs 4).
  { rewrite (getr_of_eqv _ _ 4 X4 eq_refl); simp_regs. exact (eq_trans (PR3 4 ltac:(unfold callee_saved; lia)) E2_4). }
  assert (E4_10 : getr R4 10 = Z_to_bv 64 e).
  { rewrite (getr_of_eqv _ _ 10 X4 eq_refl); simp_regs.
    exact (eq_trans (PR3 18 ltac:(unfold callee_saved; lia)) E2_18). }
  assert (E4_11 : getr R4 11 = Z_to_bv 64 pv).
  { rewrite (getr_of_eqv _ _ 11 X4 eq_refl); simp_regs. exact (eq_trans (PR3 8 ltac:(unfold callee_saved; lia)) E2_8). }
  assert (KR4 : sar_kept R3 R4) by sar_kept_tac X4.
  assert (SP4 : spZ R4 = bv_unsigned sp - 48) by (unfold spZ; rewrite E4_2; apply unsigned_lit; lia).
  assert (BLE3 : sb_le (sb_shift b A A3) (sb_malloc b (Z.of_nat (length (dec id)) + 1))).
  { rewrite EQB3. apply sb_malloc_mono. rewrite sb_shift_refl in BLEr. exact BLEr. }
  apply (sinv_arg_sn (fx := mkFP F1 fc1) B API SEGS ERRNO_LOW GFACT GOWN AX (ARGS _) 8384 (bv_unsigned sp) L A mem md O
           L3 A3 m3 md3 R REC_AFTER_REPLY [dec id] (O_r ++ [(p, Z.of_nat (length (dec id)) + 1)]) b R4 pv verb _ SI3).
  { cbn [length]. lia. }
  { rewrite E4_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP4. replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring. rewrite Z.mod_add by lia.
    exact HAL. }
  { rewrite SP4. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia. }
  { rewrite SP4. lia. }
  { rewrite E4_4. exact HTP. }
  { exact E4_10. }
  { exact E4_11. }
  { rewrite SP4.
    apply (sinv_arg_src B API SEGS ERRNO_LOW SLACK 8384 (bv_unsigned sp) L A mem md O L3 A3 m3 md3 _ _ b pv verb
             (bv_unsigned sp - 48) SI3 RA); [unfold ARG_S_K, XMALLOC_K, ALLOC_STACK; lia | lia | exact SA]. }
  { apply (room_slots_mono _ (sb_mallocs b [Z.of_nat (length (dec id)) + 1; Z.of_nat (length (sarg verb)) + 1]) _
             (LMAX + 1)); [| lia | exact ROOM].
    unfold sb_mallocs. cbn [fold_left]. apply sar_malloc_le2; [exact BLE3 | lia]. }
  intros L5 A5 R5 m5 md5 p2 SI5 EQB5 INIT5 PR5 KST5.
  rewrite E4_1.
  pose proof SI5 as (RJ5 & _).
  pose proof RJ5 as (HM5 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM5) as (Hh5 & Hl5 & _).
  assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp - 32)
                  [C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m3); [exact FR3|]. intros i Hi. cbn in Hi.
    destruct (KST5 (bv_unsigned sp - 32 + i)) as [Ea Eb]; [rewrite SP4; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  assert (Q52 : reg_get R5 2 = Z_to_bv 64 (bv_unsigned sp + -48))
    by exact (eq_trans (PR5 2 ltac:(unfold callee_saved; lia)) E4_2).
  eapply evt_SR_canon; [ | exact Hh5 | exact Hl5 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q52.
    eapply sar_run3; [exact FR5 | lia]. }
  intros ms6 (can6 & Q6 & EQ6). subst can6.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ6) as (R6 & -> & X6). clear EQ6.
  assert (KR6 : sar_kept R5 R6) by sar_kept_tac X6.
  assert (RP : regs_preserved regs R6).
  { apply sar_pres.
    - apply (sar_kept_trans _ _ _ KRr). apply (sar_kept_trans _ _ _ KR2).
      apply (sar_kept_trans _ _ _ (sar_kept_of_pres _ _ PR3)). apply (sar_kept_trans _ _ _ KR4).
      exact (sar_kept_trans _ _ _ (sar_kept_of_pres _ _ PR5) KR6).
    - rewrite (getr_of_eqv _ _ (Z_to_bv 5 2) X6 eq_refl). simp_regs. first [reflexivity | unfold getr; reflexivity].
    - rewrite (getr_of_eqv _ _ (Z_to_bv 5 8) X6 eq_refl). simp_regs. first [reflexivity | unfold getr; reflexivity].
    - rewrite (getr_of_eqv _ _ (Z_to_bv 5 9) X6 eq_refl). simp_regs. first [reflexivity | unfold getr; reflexivity].
    - rewrite (getr_of_eqv _ _ (Z_to_bv 5 18) X6 eq_refl). simp_regs. first [reflexivity | unfold getr; reflexivity]. }
  assert (RPC : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  destruct (sinv_ret B API SEGS CTX 8384 L A regs mem md O L5 A5 R6 m5 md5 _ _ b PRK SI5 RP)
    as (POST & GRf & ONf & BLf & OKf & RAf & F18f & LENf & RESf).
  apply SR_ret. cbv beta. unfold sup_after_reply_ret. rewrite SEGS.
  exists (mkFP F1 fc1), L5, A5, R6, m5, md5,
    ((O_r ++ [(p, Z.of_nat (length (dec id)) + 1)]) ++ [(p2, Z.of_nat (length (sarg verb)) + 1)]).
  split; [rewrite RPC; reflexivity|].
  split.
  { split; [exact FRM1|]. intros r Hr. cbn [fp_regs].
    apply FK1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    unfold fs_saved in Hr. rewrite Z.mod_small by lia. lia. }
  split; [exact POST|]. split; [exact GRf|]. split; [exact ONf|]. split; [exact BLf|]. split; [exact OKf|].
  split; [exact RAf|]. split; [exact F18f|]. split; [exact INIT5|]. split; [exact LENf|].
  split; [|exact RESf].
  unfold sup_after_reply_sizes, sb_mallocs. cbn [fold_left]. rewrite EQB5.
  apply sar_malloc_le2; [exact BLE3 | lia].
Qed.

End Main.
