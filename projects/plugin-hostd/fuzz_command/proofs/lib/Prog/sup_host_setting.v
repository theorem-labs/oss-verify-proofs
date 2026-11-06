(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecStub.
Import ListNotations.
Open Scope Z_scope.

Lemma hs_pre_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat),
  stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  evt rsegs (fun ms' => exists b0 b1 b2 m',
       ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10)
                     (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) b0 b1 b2 a3 a4 a5 a6 a7 a2 a1 a0
                     s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16214) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (0x33d50, 0x33d54)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 64)
       /\ rw_cells rsegs m' (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x161a0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n ST LO LO2 NC Hn.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (0x33d50, 0x33d54)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 64%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 64%nat junk [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 17 step.
  rewrite sx32_lit by lia.
  assert (C1 : negb (bv_eqb (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 16)) = true).
  { unfold bv_eqb. rewrite !unsigned_lit by lia. apply negb_true_iff, Z.eqb_neq. lia. }
  rewrite C1. cbv iota.
  do 7 step.
  rewrite da_addr by lia.
  apply evt_done.
  do 4 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma hs_rec :
  forall ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (jk : list byte),
  rw_cells rsegs m e [CB 8 jk] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16228) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 e)
                     (Z_to_bv 64 e) s4 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15e64) fc None m' (seg_rom rsegs)
       /\ munch [(e, e + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' e [C4 (Z_to_bv 64 6); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 e) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16214) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e jk EW.
  pose proof (rw_cells_bound _ _ _ _ EW) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (munch_refl [(e, e + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 2 step.
  apply (rw_cells_same_bytes _ _ _ [C4 (Z_to_bv 64 6); C4 (Z_to_bv 64 0)]) in EW;
    [| cbn; tauto | vm_compute; reflexivity | reflexivity].
  do 3 step.
  apply evt_done.
  eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma hs_seg_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (n : nat) (jk : list byte),
  stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))] -> (n < 16)%nat ->
  rw_cells rsegs m (0x33d58 + 56 * Z.of_nat n) [CB 8 jk] ->
  evt rsegs (fun ms' => exists b2 m',
       ms' = MS (mkR (Z_to_bv 64 0x16228) (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10)
                     (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) (Z_to_bv 64 (0x33d58 + 56 * Z.of_nat n)) a0
                     b2 a3 a4 a5 a6 a7 a2 a1 a0 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15e64) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (0x33d50, 0x33d54);
                 (0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)] m m'
       /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 64)
       /\ rw_cells rsegs m' (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells rsegs m' 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n + 1))]
       /\ rw_cells rsegs m' (0x33d58 + 56 * Z.of_nat n) [C4 (Z_to_bv 64 6); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x161a0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n jk ST LO LO2 NC Hn EW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply evt_cut; [eapply hs_pre_lt; [exact ST | exact LO | exact LO2 | exact NC | exact Hn] |].
  intros ms1 (b0 & b1 & b2 & m1 & -> & MU1 & WM1 & ST1 & FR1 & NC1).
  assert (EW1 : rw_cells rsegs m1 (0x33d58 + 56 * Z.of_nat n) [CB 8 jk]).
  { apply (rw_cells_transport rsegs [(bv_unsigned sp - 64, bv_unsigned sp); (0x33d50, 0x33d54)] m m1 _ _ EW MU1 WM1).
    cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
  eapply evt_cut; [eapply hs_rec; exact EW1 |].
  intros ms2 (m2 & -> & MU2 & WM2 & EN2).
  apply evt_done. exists b2, m2. split; [reflexivity|].
  split.
  { apply (munch_trans _ m m1 m2).
    - apply (munch_weaken [(bv_unsigned sp - 64, bv_unsigned sp); (0x33d50, 0x33d54)]); [|exact MU1].
      intros x (H1 & H2 & H3 & _). split; [exact H1 | split; [exact H2 | exact I]].
    - apply (munch_weaken [(0x33d58 + 56 * Z.of_nat n, 0x33d58 + 56 * Z.of_nat n + 8)]); [|exact MU2].
      intros x (H1 & H2 & H3 & _). split; [exact H3 | exact I]. }
  split; [exact (wmono_trans rsegs _ _ _ WM1 WM2)|].
  split.
  { apply (stk_transport_disjoint rsegs _ m1 m2 _ _ ST1 MU2 WM2). cbn [disjoint_from]. repeat split; lia. }
  split.
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ FR1 MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  split; [|exact EN2].
  apply (rw_cells_transport rsegs _ m1 m2 _ _ NC1 MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
  repeat split; lia.
Qed.

Lemma hs_seg_eq :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp -> 0x34100 <= lo ->
  rw_cells rsegs m 0x33d50 [C4 (Z_to_bv 64 16)] ->
  evt rsegs (fun ms' => exists b2 m',
       ms' = MS (mkR (Z_to_bv 64 0x161f0) (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 0x33d10)
                     s1 (Z_to_bv 64 0x33d10) (Z_to_bv 64 1) b2 a3 a4 a5 a6 a7
                     a2 a1 a0 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x155f0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono rsegs m m'
       /\ stk rsegs m' lo (bv_unsigned sp - 64)
       /\ rw_cells rsegs m' (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x161a0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2 NC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 64%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 64%nat junk [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 17 step.
  rewrite sx32_lit by lia.
  if_false.
  do 3 step.
  apply evt_done.
  do 2 eexists. split; [reflexivity|].
  repeat (split; [eassumption|]). eassumption.
Qed.

Lemma hs_ret16 :
  forall ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (jk : list byte),
  rw_cells rsegs m 0x33d10 [CB 8 jk] ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR (Z_to_bv 64 0x16228) sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) (Z_to_bv 64 0x33d10)
                     (Z_to_bv 64 0x33d10) s4 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15e64) fc None m' (seg_rom rsegs)
       /\ munch [(0x33d10, 0x33d10 + 8)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x33d10 [C4 (Z_to_bv 64 6); C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x161f0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m jk EW.
  do 2 step.
  eapply hs_rec. exact EW.
Qed.

Lemma hs_mid :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16234) sp gp tp t0 t1 t2 s0 s1 s1 s2 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x15b1c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16228) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 3 step.
  apply evt_done. reflexivity.
Qed.

From Stdlib Require Import Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL01 YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecSeq RecStep RecGlue RecTail RecAnsB RecCore.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import rec_calls_free_c arg_i_c arg_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import rec_canonical_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strlen_c strcat_c mix_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import sup_host_setting_c.

Lemma hs_pw_in2 : forall {X} (Rl : X -> X -> Prop) l x y, pairwise Rl l -> In x l -> In y l -> x <> y ->
  Rl x y \/ Rl y x.
Proof.
  intros X Rl l. induction l as [|z l IH]; intros x y HP Hx Hy Hne; cbn in *; [destruct Hx|].
  destruct HP as [Hz HP]. destruct Hx as [<-|Hx], Hy as [<-|Hy].
  - congruence.
  - left. apply Hz. exact Hy.
  - right. apply Hz. exact Hx.
  - apply IH; assumption.
Qed.

Lemma hs_in_rm : forall (b1 b2 : list (Z * Z)) x pn, In pn (b1 ++ x :: b2) -> pn <> x -> In pn (b1 ++ b2).
Proof.
  intros b1 b2 x pn H N. apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H | congruence | right; exact H].
Qed.

Lemma hs_assoc_nd : forall {X : Type} (l : list (X * Z)) p k n, List.NoDup (map fst l) -> In (p, k) l -> In (p, n) l ->
  k = n.
Proof.
  intros X. induction l as [|[p0 k0] l IH]; intros p k n ND H1 H2; [destruct H1|].
  cbn in ND. inversion ND as [|? ? NI ND']; subst.
  destruct H1 as [E1|H1], H2 as [E2|H2].
  - congruence.
  - injection E1 as <- <-. exfalso. apply NI. apply in_map_iff. exists (p0, n). split; [reflexivity | exact H2].
  - injection E2 as <- <-. exfalso. apply NI. apply in_map_iff. exists (p0, k). split; [reflexivity | exact H1].
  - exact (IH p k n ND' H1 H2).
Qed.

Section TMP.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22a68.
Hypothesis GRD : ms_guard B = 0x54450.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.

Definition sinvT (T : Z * Z) (K S : Z) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (O : list (Z * Z)) (Lc : layout) (Ac : astate) (mc : word -> option byte) (mdc : Model) (Rc : rstate)
    (Oc : list (Z * Z)) (bc : sbound) : Prop :=
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc /\
  g_rec_rep rsegs Lc Ac mc Rc Oc /\ owns_new L A O Oc /\
  (forall pn, In pn (blocks Lc Ac) -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn Oc \/ pn = T) /\
  (forall pn, In pn (blocks L A) -> ~ In pn (blocks Lc Ac) -> In pn O) /\
  ro_agree rsegs mc /\ f18_words rsegs mc /\ res_ok_slots Ac (sb_shift bc A Ac) /\
  In T (blocks Lc Ac) /\ ~ In T Oc /\ (In T (blocks L A) -> In T O) /\ 0 < snd T.

Lemma hs_blk_disj : forall L A mem md (x y : Z * Z), aa_MR API L A mem md -> In x (blocks L A) -> In y (blocks L A) ->
  x <> y -> ranges_disjoint x y \/ ranges_disjoint y x.
Proof.
  intros L A mem md x y HM Hx Hy N.
  exact (hs_pw_in2 _ _ x y (mr_blocks_disjoint B _ (aa_laws API) L A mem md HM) Hx Hy N).
Qed.

Lemma hs_blk_img : forall L A mem md a k i, aa_MR API L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  ~ in_img B (a + i).
Proof using AX.
  intros L A mem md a k i HM Hin Hi. unfold blocks in Hin. apply in_map_iff in Hin as ([q k'] & E & Hq).
  cbn in E. injection E as <- <-. exact (ax_blocks_img AX L A mem md q k' i HM Hq Hi).
Qed.

Lemma sinvT_munch : forall T K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W,
  sinvT T K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  munch W mc m' -> wmono rsegs mc m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ fst T <= a < fst T + snd T) ->
  sinvT T K S L A mem md O Lc Ac m' mdc Rc Oc bc.
Proof using SEGS AX GOWN GOTG GRD.
  intros T K S L A mem md O Lc Ac mc mdc Rc Oc bc m' W SI MU WM HW.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS & TI & TO & TA & TP).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & HWA & HWc & HBd & HL & _).
  destruct T as [t n]. cbn [fst snd] in *.
  assert (TB : forall i, 0 <= i < n -> present mc (t + i) /\ 4096 <= t /\ t + n <= alloc_ceiling /\
                 ~ owned B Lc Ac (t + i) /\ ~ in_img B (t + i)).
  { intros i Hi. destruct (block_facts B _ LAWS Lc Ac mc mdc t n i HM TI Hi) as (P1 & P2 & P3 & P4).
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
    exact (hs_blk_img Lc Ac mc mdc t n i HM TI Hi). }
  assert (TBl : 4096 <= t /\ t + n <= alloc_ceiling) by (destruct (TB 0 ltac:(lia)) as (_ & X1 & X2 & _); lia).
  assert (OUT : forall a, 0 <= a < 2 ^ 64 -> ~ (S - K <= a < S) -> ~ (t <= a < t + n) -> outside W a).
  { intros a Ra H1 H2. destruct (outside_dec W a) as [H|H]; [exact H|]. destruct (HW a Ra H); contradiction. }
  assert (BLK : forall q k i, In (q, k) (blocks Lc Ac) -> (q, k) <> (t, n) -> 0 <= i < k ->
            0 <= q + i < 2 ^ 64 /\ outside W (q + i)).
  { intros q k i Hin Hne Hi. destruct (block_facts B _ LAWS Lc Ac mc mdc q k i HM Hin Hi) as (_ & P2 & P3 & _).
    split; [lia|]. apply OUT; [lia | lia |].
    destruct (hs_blk_disj Lc Ac mc mdc (q, k) (t, n) HM Hin TI Hne) as [D|D]; unfold ranges_disjoint in D;
      cbn [fst snd] in D; lia. }
  split.
  { apply (rjr_munch B (aa_MR API) SEGS LAWS K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc m' W RJ MU);
      [rewrite SEGS; exact WM | | | | |].
    - intros a Ra Hn Hf. destruct (HW a Ra Hn) as [H|H]; [left; exact H|]. exfalso.
      destruct (TB (a - t) ltac:(lia)) as (_ & _ & X3 & _ & X5). replace (t + (a - t)) with a in X5 by ring.
      destruct Hf as [Hf|(Hf & _)]; [lia | exact (X5 Hf)].
    - intros a Ra Hn Ho. destruct (HW a Ra Hn) as [H|H].
      + pose proof (mr_owned_low B _ LAWS Lc Ac mc mdc a HM Ho). lia.
      + destruct (TB (a - t) ltac:(lia)) as (_ & _ & _ & X4 & _). replace (t + (a - t)) with a in X4 by ring.
        exact (X4 Ho).
    - intros a Ha. apply OUT; lia.
    - intros p k i Hin Hg Hi.
      pose proof (rjr_in_cur B _ K S rec_area _ L A mem md Lc Ac mc mdc p k RJ Hin Hg) as Hc.
      pose proof (ptr_addr_stable A L Lc p k HWA Hin HL) as EP.
      assert (Hb : In (ptr_addr Lc p, k) (blocks Lc Ac))
        by (unfold blocks; exact (in_map (fun b => (ptr_addr Lc (fst b), snd b)) (user_blocks Ac) (p, k) Hc)).
      assert (Hne : (ptr_addr Lc p, k) <> (t, n)).
      { intros E. apply Hg. rewrite <- EP. rewrite E. apply TA. rewrite <- E, EP. unfold blocks.
        exact (in_map (fun b => (ptr_addr L (fst b), snd b)) (user_blocks A) (p, k) Hin). }
      rewrite <- EP. exact (proj2 (BLK _ _ i Hb Hne Hi)).
    - intros p k i Hin Hi.
      assert (Hb : In (ptr_addr Lc p, k) (blocks Lc Ac))
        by (unfold blocks; exact (in_map (fun b => (ptr_addr Lc (fst b), snd b)) (user_blocks Ac) (p, k) Hin)).
      destruct (block_facts B _ LAWS Lc Ac mc mdc _ k i HM Hb Hi) as (P1 & P2 & P3 & _).
      destruct (outside_dec W (ptr_addr Lc p + i)) as [Ho|Ho].
      + exact (munch_present W mc m' (ptr_addr Lc p + i) MU ltac:(lia) Ho P1).
      + destruct (HW (ptr_addr Lc p + i) ltac:(lia) Ho) as [H|H]; [lia|].
        apply (present_of_writable_out B SEGS m' (ptr_addr Lc p + i) ltac:(lia)).
        * destruct (TB (ptr_addr Lc p + i - t) ltac:(lia)) as (_ & _ & _ & _ & X5).
          replace (t + (ptr_addr Lc p + i - t)) with (ptr_addr Lc p + i) in X5 by ring. exact X5.
        * apply WM. exact (present_writable rsegs mc _ P1). }
  split.
  { unfold g_rec_rep in *. apply (rec_rep_keep rsegs G_REC REC_SC Lc Ac mc m' Rc Oc GR).
    - intros a Ha. assert (Hg : GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
        by (unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *; lia).
      apply (munch_mbyte rsegs W mc m'); [exact MU | unfold GLOB_LO, GLOB_N in Hg; lia|].
      apply OUT; [unfold GLOB_LO, GLOB_N in Hg; lia | unfold GLOB_LO, GLOB_N in Hg; lia |].
      intros Ht. destruct (TB (a - t) ltac:(lia)) as (_ & _ & _ & _ & X5). replace (t + (a - t)) with a in X5 by ring.
      exact (X5 (glob_in_img B SEGS a Hg)).
    - intros a Ha _. apply glob_writable. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - intros p k i Hin Hi. pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hin) as Hb.
      assert (Hne : (p, k) <> (t, n)) by (intros E; apply TO; rewrite <- E; exact Hin).
      destruct (BLK p k i Hb Hne Hi) as [Rr Oo]. exact (munch_mbyte rsegs W mc m' _ MU Rr Oo). }
  split; [exact ON|]. split; [exact B1|]. split; [exact B2|].
  split.
  { apply (ro_out W mc m' RA MU). intros a Ha Hro. apply OUT; [lia | lia |].
    intros Ht. destruct (TB (a - t) ltac:(lia)) as (_ & _ & _ & _ & X5). replace (t + (a - t)) with a in X5 by ring.
    exact (X5 (ro_in_img B SEGS a ltac:(lia) Hro)). }
  split.
  { apply (f18_out W mc m' F18 MU). intros i Hi.
    assert (G1 : static_owned B (snprintf_c.GOT_GUARD + i))
      by (unfold static_owned, snprintf_c.GOT_GUARD; rewrite GOTG; right; right; right; right; left; lia).
    assert (G2 : static_owned B (snprintf_c.GUARD + i))
      by (unfold static_owned, snprintf_c.GUARD; rewrite GRD; right; right; right; right; right; left; lia).
    split; apply OUT; unfold snprintf_c.GOT_GUARD, snprintf_c.GUARD in *; try lia; intros Ht.
    - destruct (TB (0x22a68 + i - t) ltac:(lia)) as (_ & _ & _ & X4 & _).
      replace (t + (0x22a68 + i - t)) with (0x22a68 + i) in X4 by ring. exact (X4 (or_intror G1)).
    - destruct (TB (0x54450 + i - t) ltac:(lia)) as (_ & _ & _ & X4 & _).
      replace (t + (0x54450 + i - t)) with (0x54450 + i) in X4 by ring. exact (X4 (or_intror G2)). }
  split; [exact RS|]. split; [exact TI|]. split; [exact TO|]. split; [exact TA | exact TP].
Qed.

Lemma sinvT_malloc : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc Kc regs_c L' A' regs' m' md' p n,
  sinv B API K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  S - K <= spZ regs_c - Kc -> spZ regs_c <= S ->
  call_post_k B (aa_MR API) Kc Lc Ac regs_c mc mdc (fun _ => False) L' A' regs' m' md' ->
  0 < n -> fresh_block B p n ->
  (exists b1 b2, blocks L' A' = b1 ++ (p, n) :: b2 /\ blocks Lc Ac = b1 ++ b2) ->
  (forall q k, In (q, k) (user_blocks Ac) -> In (q, k) (user_blocks A')) ->
  blocks_kept B Lc Ac mc m' (fun _ => False) ->
  (length (st_regions Ac) <= length (st_regions A'))%nat ->
  st_init_done A' = true ->
  res_ok_slots A' (sb_malloc (sb_shift bc A Ac) n) ->
  ro_agree rsegs m' -> guard_kept B mc m' ->
  sinvT (p, n) K S L A mem md O L' A' m' md' Rc Oc bc.
Proof using SEGS AX GOWN GFACT ERRNO_LOW GOTG GRD.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc Kc regs_c L' A' regs' m' md' p n
    SI HLO HHI POST Hn FB (b1 & b2 & EB' & EB) UB BK RGN INI RS' RA' GK.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & _).
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  unfold blocks_kept in BK. rewrite SEGS in BK, PF.
  pose proof FB as (FB1 & FB2 & FB3).
  assert (PIN : In (p, n) (blocks L' A')) by (rewrite EB'; apply in_elt).
  assert (PERM : Permutation (blocks L' A') ((b1 ++ b2) ++ [(p, n)])).
  { rewrite EB'. eapply Permutation_trans; [apply Permutation_sym, Permutation_middle | apply Permutation_cons_append]. }
  assert (NOTC : ~ In (p, n) (blocks Lc Ac)).
  { rewrite EB. intros H. exact (perm_not_both _ _ _ (p, n) PERM (mr_blocks_disjoint B _ LAWS L' A' m' md' PM)
                                   Hn H (or_introl eq_refl)). }
  assert (CUR : forall pn, In pn (blocks Lc Ac) -> In pn (blocks L' A')).
  { intros pn Hpn. rewrite EB'. rewrite EB in Hpn. exact (in_mid_inv b1 b2 (p, n) pn Hpn). }
  assert (RJ' : rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' m' md').
  { apply (rjr_post B _ SEGS LAWS AX ERRNO_LOW K S rec_area _ L A mem md Lc Ac mc mdc Kc regs_c (fun _ => False)
             (fun _ => False) L' A' regs' m' md' RJ (call_post_k_rec B _ _ _ _ _ _ _ _ _ _ _ _ _ POST) HLO HHI).
    - intros a [].
    - intros p0 n0 _ _ _ [].
    - intros p0 n0 _ Hc Hn0. exfalso. exact (Hn0 (UB p0 n0 Hc)).
    - exact RGN.
    - intros Hf. rewrite INI in Hf. discriminate. }
  assert (GR' : g_rec_rep rsegs L' A' m' Rc Oc).
  { unfold g_rec_rep in *. apply (rec_rep_frame rsegs G_REC REC_SC Lc Ac mc Rc Oc L' A' m' GR).
    - intros a Ha.
      assert (Hg : GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
        by (unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *; lia).
      destruct (GFACT a (glob_in a Hg)) as (Gi & _ & _ & Ge).
      assert (NS : ~ scratch_k B Kc regs_c a).
      { unfold scratch_k. intros [H|H]; [unfold GLOB_LO, GLOB_N in Hg; lia | exact (Ge H)]. }
      destruct (PF a (or_intror Gi) (GOWN Lc Ac mc mdc a HM (glob_in a Hg)) (GOWN L' A' m' md' a PM (glob_in a Hg))
                   NS (fun H => H)) as [E1 E2].
      split; [exact E1 | exact (proj1 E2)].
    - intros q k i Hin Hi. exact (BK q k i (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hin) (fun H => H) Hi).
    - intros pn Hpn. exact (CUR pn (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hpn)). }
  split; [exact RJ'|]. split; [exact GR'|]. split; [exact ON|].
  split.
  { intros pn Hpn. rewrite EB' in Hpn. apply in_app_or in Hpn as [H|[H|H]].
    - destruct (B1 pn ltac:(rewrite EB; apply in_or_app; left; exact H)) as [X|X];
        [left; exact X | right; left; exact X].
    - right. right. symmetry. exact H.
    - destruct (B1 pn ltac:(rewrite EB; apply in_or_app; right; exact H)) as [X|X];
        [left; exact X | right; left; exact X]. }
  split.
  { intros pn H1 H2. apply B2; [exact H1|]. intros Hc. exact (H2 (CUR pn Hc)). }
  split; [exact RA'|].
  split.
  { destruct (ax_statics AX L' A' m' md' PM) as (_ & (g & Hg & HWg) & _).
    rewrite GRD, SEGS in HWg.
    apply (f18_words_after mc m' g F18); [|exact Hg | exact HWg].
    intros i Hi. pose proof (GK i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  split.
  { rewrite <- (sb_shift_trans bc A Ac A'). rewrite <- (sb_shift_add (sb_shift bc A Ac) Lc Ac L' A' b1 b2 p n EB' EB).
    exact RS'. }
  split; [exact PIN|].
  split; [intros Hin; exact (NOTC (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hin))|].
  split; [intros Hb; exact (B2 _ Hb NOTC)|].
  exact Hn.
Qed.

Lemma sinvT_free : forall K S L A mem md O Lc Ac mc mdc Rc Oc bc regs_c L' A' regs' m' md' q n,
  sinvT (ptr_addr Lc q, n) K S L A mem md O Lc Ac mc mdc Rc Oc bc ->
  S - K <= spZ regs_c - ALLOC_STACK -> spZ regs_c <= S ->
  In (q, n) (user_blocks Ac) ->
  call_post B (aa_MR API) Lc Ac regs_c mc mdc (fun a => ptr_addr Lc q <= a < ptr_addr Lc q + n) L' A' regs' m' md' ->
  (exists b1 b2, blocks Lc Ac = b1 ++ (ptr_addr Lc q, n) :: b2 /\ blocks L' A' = b1 ++ b2) ->
  blocks_kept B Lc Ac mc m' (fun a => a = ptr_addr Lc q) ->
  ro_agree rsegs m' -> guard_kept B mc m' ->
  (forall q' k, In (q', k) (user_blocks Ac) -> q' <> q -> In (q', k) (user_blocks A')) ->
  st_init_done A' = true ->
  (length (st_regions Ac) <= length (st_regions A'))%nat ->
  res_ok_slots A' (sb_free (sb_shift bc A Ac) n) ->
  sinv B API K S L A mem md O L' A' m' md' Rc Oc bc.
Proof using SEGS AX GOWN GFACT ERRNO_LOW GOTG GRD.
  intros K S L A mem md O Lc Ac mc mdc Rc Oc bc regs_c L' A' regs' m' md' q n
    SI HLO HHI QIN POST (b1 & b2 & EB & EB') BK RA' GK UB INI RGN RS'.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS & TI & TO & TA & TP).
  cbn [fst snd] in TP.
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & HWA & HWc & HBd & HL & _).
  apply (proj1 (call_post_k_alloc B (aa_MR API) _ _ _ _ _ _ _ _ _ _ _)) in POST.
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  unfold blocks_kept in BK. rewrite SEGS in BK, PF.
  set (t := ptr_addr Lc q) in *.
  assert (TB : forall i, 0 <= i < n -> t + i < alloc_ceiling /\ ~ in_img B (t + i)).
  { intros i Hi. destruct (block_facts B _ LAWS Lc Ac mc mdc t n i HM TI Hi) as (_ & _ & P3 & _).
    split; [lia | exact (hs_blk_img Lc Ac mc mdc t n i HM TI Hi)]. }
  assert (NOT' : ~ In (t, n) (blocks L' A')).
  { rewrite EB'. intros H. pose proof (blocks_mid_disjoint B _ LAWS Lc Ac mc mdc b1 b2 t n t n HM EB H). lia. }
  assert (CUR : forall pn, In pn (blocks Lc Ac) -> pn <> (t, n) -> In pn (blocks L' A')).
  { intros pn Hpn Hne. rewrite EB'. rewrite EB in Hpn. exact (hs_in_rm b1 b2 _ pn Hpn Hne). }
  assert (BACK : forall pn, In pn (blocks L' A') -> In pn (blocks Lc Ac)).
  { intros pn Hpn. rewrite EB. rewrite EB' in Hpn. exact (in_mid_inv b1 b2 _ pn Hpn). }
  assert (RJ' : rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' m' md').
  { apply (rjr_post B _ SEGS LAWS AX ERRNO_LOW K S rec_area _ L A mem md Lc Ac mc mdc ALLOC_STACK regs_c
             (fun a => t <= a < t + n) (fun _ => False) L' A' regs' m' md' RJ
             (call_post_k_rec B _ _ _ _ _ _ _ _ _ _ _ _ _ POST) HLO HHI).
    - intros a Ha Hf. exfalso. destruct (TB (a - t) ltac:(lia)) as (X1 & X2).
      replace (t + (a - t)) with a in X1, X2 by ring.
      destruct Hf as [Hf|(Hf & _)]; [lia | exact (X2 Hf)].
    - intros p0 n0 _ _ _ [].
    - intros p0 n0 Hin Hc Hn0.
      destruct (YI04.sptr_eq_dec p0 q) as [E|E]; [|exfalso; exact (Hn0 (UB p0 n0 Hc E))].
      subst p0.
      pose proof (hs_assoc_nd (user_blocks Ac) q n0 n (user_block_ptrs_NoDup Ac HWc) Hc QIN) as <-.
      pose proof (ptr_addr_stable A L Lc q n0 HWA Hin HL) as EQ.
      assert (HB : In (ptr_addr L q, n0) (blocks L A))
        by (unfold blocks; exact (in_map (fun b => (ptr_addr L (fst b), snd b)) (user_blocks A) (q, n0) Hin)).
      rewrite <- EQ in HB |- *. exact (TA HB).
    - exact RGN.
    - intros Hf. rewrite INI in Hf. discriminate. }
  assert (GR' : g_rec_rep rsegs L' A' m' Rc Oc).
  { unfold g_rec_rep in *. apply (rec_rep_frame rsegs G_REC REC_SC Lc Ac mc Rc Oc L' A' m' GR).
    - intros a Ha.
      assert (Hg : GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
        by (unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *; lia).
      destruct (GFACT a (glob_in a Hg)) as (Gi & _ & _ & Ge).
      assert (NS : ~ scratch_k B ALLOC_STACK regs_c a).
      { unfold scratch_k. intros [H|H]; [unfold GLOB_LO, GLOB_N, ALLOC_STACK in *; lia | exact (Ge H)]. }
      assert (NE : ~ (t <= a < t + n)).
      { intros H. destruct (TB (a - t) ltac:(lia)) as (_ & X2). replace (t + (a - t)) with a in X2 by ring.
        exact (X2 Gi). }
      destruct (PF a (or_intror Gi) (GOWN Lc Ac mc mdc a HM (glob_in a Hg)) (GOWN L' A' m' md' a PM (glob_in a Hg))
                   NS NE) as [E1 E2].
      split; [exact E1 | exact (proj1 E2)].
    - intros a k i Hin Hi. pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hin) as Hb.
      apply (BK a k i Hb); [|exact Hi]. intros Ea. subst a.
      pose proof (rec_rep_pos _ _ _ _ _ _ _ _ _ GR Hin) as Hk. cbn in Hk.
      pose proof (blocks_same_addr B _ LAWS Lc Ac mc mdc t k n HM Hb TI Hk TP) as ->. exact (TO Hin).
    - intros pn Hpn. apply CUR; [exact (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hpn)|].
      intros E. apply TO. rewrite <- E. exact Hpn. }
  split; [exact RJ'|]. split; [exact GR'|]. split; [exact ON|].
  split.
  { intros pn Hpn. destruct (B1 pn (BACK pn Hpn)) as [X|[X|X]]; [left; exact X | right; exact X |].
    exfalso. apply NOT'. rewrite <- X. exact Hpn. }
  split.
  { intros pn H1 H2. destruct (in_dec pair_dec pn (blocks Lc Ac)) as [Hc|Hc]; [|exact (B2 pn H1 Hc)].
    destruct (pair_dec pn (t, n)) as [E|E]; [subst pn; exact (TA H1) | exfalso; exact (H2 (CUR pn Hc E))]. }
  split; [exact RA'|].
  split.
  { destruct (ax_statics AX L' A' m' md' PM) as (_ & (g & Hg & HWg) & _).
    rewrite GRD, SEGS in HWg.
    apply (f18_words_after mc m' g F18); [|exact Hg | exact HWg].
    intros i Hi. pose proof (GK i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  rewrite <- (sb_shift_trans bc A Ac A'). rewrite <- (sb_shift_del (sb_shift bc A Ac) Lc Ac L' A' b1 b2 t n EB EB').
  exact RS'.
Qed.

Lemma sinvT_arg : forall T K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc Kc regs_c Ec L' A' regs' m' md' x p k,
  sinvT T K S L A mem md O Lc Ac mc mdc (rec_record Rp fn As) Oc bc ->
  (length As < 6)%nat ->
  S - K <= spZ regs_c - Kc -> spZ regs_c <= S ->
  call_post_k B (aa_MR API) Kc Lc Ac regs_c mc mdc Ec L' A' regs' m' md' ->
  (forall a, Ec a ->
     rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS <= a < rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS + 4 \/
     rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a <
       rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8 \/
     p <= a < p + k) ->
  p <> 0 -> fresh_block B p k ->
  (exists b1 b2, blocks L' A' = b1 ++ (p, k) :: b2 /\ blocks Lc Ac = b1 ++ b2) ->
  (forall q n, In (q, n) (user_blocks Ac) -> In (q, n) (user_blocks A')) ->
  blocks_kept B Lc Ac mc m' (fun _ => False) ->
  (length (st_regions Ac) <= length (st_regions A'))%nat ->
  bytes_at rsegs m' (rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS) (le4 (Z_to_bv 64 (Z.of_nat (length As) + 1))) ->
  bytes_at rsegs m' (rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) (le8 (Z_to_bv 64 p)) ->
  bytes_at rsegs m' p (x ++ [Z_to_bv 8 0]) ->
  no0 x -> Z.of_nat (length x) <= LMAX -> Z.of_nat (length x) + 1 <= k <= LMAX + 2 ->
  st_init_done A' = true ->
  res_ok_slots A' (sb_malloc (sb_shift bc A Ac) k) ->
  ro_agree rsegs m' -> f18_words rsegs m' ->
  sinvT T K S L A mem md O L' A' m' md' (rec_record Rp fn (As ++ [x])) (Oc ++ [(p, k)]) bc.
Proof using SEGS AX GOWN GFACT ERRNO_LOW.
  intros T K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc Kc regs_c Ec L' A' regs' m' md' x p k
    SI H6 HLO HHI POST HEc Hp0 FB (b1 & b2 & EB' & EB) UB BK RGN BN BS BX Hno Hlx Hsz INI RS' RA' F18'.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & ON & B1 & B2 & RA & F18 & RS & TI & TO & TA & TP).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & _).
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  unfold blocks_kept in BK. rewrite SEGS in BK, PF.
  pose proof FB as (FB1 & FB2 & FB3).
  assert (HN : (length (r_calls Rp) <= 16)%nat).
  { pose proof GR as (Q0 & (_ & (C1 & _) & _) & _). unfold rec_record in C1.
    destruct (Nat.ltb (length (r_calls Rp)) 16) eqn:E; [apply Nat.ltb_lt in E; lia | exact C1]. }
  assert (ER : REC_SC <= rec_entry G_REC REC_SC Rp /\ rec_entry G_REC REC_SC Rp + CALL_SIZE <= G_REC + REC_SIZE).
  { unfold rec_entry. destruct (Nat.ltb (length (r_calls Rp)) 16) eqn:E.
    - apply Nat.ltb_lt in E. unfold REC_SC, G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. lia.
    - unfold REC_SC, G_REC, CALL_SIZE, REC_SIZE. lia. }
  set (e := rec_entry G_REC REC_SC Rp) in *.
  assert (Hk : 0 < k) by lia.
  assert (PIN : In (p, k) (blocks L' A')) by (rewrite EB'; apply in_elt).
  assert (PERM : Permutation (blocks L' A') ((b1 ++ b2) ++ [(p, k)])).
  { rewrite EB'. eapply Permutation_trans; [apply Permutation_sym, Permutation_middle | apply Permutation_cons_append]. }
  assert (NOTC : ~ In (p, k) (blocks Lc Ac)).
  { rewrite EB. intros H. exact (perm_not_both _ _ _ (p, k) PERM (mr_blocks_disjoint B _ LAWS L' A' m' md' PM)
                                   Hk H (or_introl eq_refl)). }
  assert (CUR : forall pn, In pn (blocks Lc Ac) -> In pn (blocks L' A')).
  { intros pn Hpn. rewrite EB'. rewrite EB in Hpn. exact (in_mid_inv b1 b2 (p, k) pn Hpn). }
  assert (APT : forall lo n, 0 < n -> (forall a, lo <= a < lo + n -> in_img B a) -> iv_apart p k lo n).
  { intros lo n Hn HI. unfold iv_apart. destruct (Z_le_gt_dec (p + k) lo) as [H|H]; [left; exact H|].
    destruct (Z_le_gt_dec (lo + n) p) as [H'|H']; [right; exact H'|]. exfalso.
    apply (FB3 (Z.max p lo - p)); [lia|]. replace (p + (Z.max p lo - p)) with (Z.max p lo) by lia. apply HI. lia. }
  assert (RIMG' : forall a, REC_SC <= a < G_REC + REC_SIZE -> GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
    by (intros a Ha; unfold REC_SC, G_REC, REC_SIZE, GLOB_LO, GLOB_N in *; lia).
  assert (RJ' : rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md L' A' m' md').
  { apply (rjr_post B _ SEGS LAWS AX ERRNO_LOW K S rec_area _ L A mem md Lc Ac mc mdc Kc regs_c Ec (fun _ => False)
             L' A' regs' m' md' RJ (call_post_k_rec B _ _ _ _ _ _ _ _ _ _ _ _ _ POST) HLO HHI).
    - intros a Ha Hf. destruct (HEc a Ha) as [H|[H|H]].
      + unfold rec_area, G_REC, REC_SC, REC_SIZE, SC_SIZE, CALL_SIZE, CALL_OFF_NARGS in *. split; lia.
      + unfold rec_area, G_REC, REC_SC, REC_SIZE, SC_SIZE, CALL_SIZE, CALL_OFF_ARGS in *. split; lia.
      + exfalso. destruct Hf as [Hf|(Hi & _)]; [lia|].
        apply (FB3 (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Hi.
    - intros p0 n0 _ _ _ [].
    - intros p0 n0 _ Hc Hn. exfalso. exact (Hn (UB p0 n0 Hc)).
    - exact RGN.
    - intros Hf. rewrite INI in Hf. discriminate. }
  assert (NQ : ~ In p (map fst Oc)).
  { intros Hq. apply in_map_iff in Hq as ([q k'] & Eq & Hq). cbn in Eq. subst q.
    pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hq) as Hb.
    pose proof (rec_rep_pos _ _ _ _ _ _ _ _ _ GR Hq) as Hk'. cbn in Hk'.
    pose proof (blocks_same_addr B _ LAWS L' A' m' md' p k k' PM PIN (CUR _ Hb) Hk Hk') as <-.
    exact (NOTC Hb). }
  assert (GR' : g_rec_rep rsegs L' A' m' (rec_record Rp fn (As ++ [x])) (Oc ++ [(p, k)])).
  { unfold g_rec_rep in *.
    apply (rec_rep_arg rsegs G_REC REC_SC Lc Ac mc L' A' m' Rp fn As Oc x p k GR H6 BN BS).
    - intros a Ha N1 N2.
      assert (Hg : GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N)
        by (apply RIMG'; unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in *; lia).
      destruct (GFACT a (glob_in a Hg)) as (Gi & _ & _ & Ge).
      assert (NS : ~ scratch_k B Kc regs_c a).
      { unfold scratch_k. intros [H|H]; [unfold GLOB_LO, GLOB_N in Hg; lia | exact (Ge H)]. }
      assert (NE : ~ Ec a).
      { intros HE. destruct (HEc a HE) as [H|[H|H]]; [contradiction | contradiction |].
        apply (FB3 (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Gi. }
      exact (proj1 (PF a (or_intror Gi) (GOWN Lc Ac mc mdc a HM (glob_in a Hg)) (GOWN L' A' m' md' a PM (glob_in a Hg))
                       NS NE)).
    - intros a Ha _. apply glob_writable. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - intros pn Hpn. pose proof (rec_rep_O_in _ _ _ _ _ _ _ _ _ GR Hpn) as Hb.
      split; [exact (CUR pn Hb)|]. intros i Hi. destruct pn as [q n]. cbn [fst snd] in *.
      exact (BK q n i Hb (fun H => H) Hi).
    - exact NQ.
    - exact Hp0.
    - exact PIN.
    - exact Hno.
    - exact Hlx.
    - exact Hsz.
    - exact BX.
    - apply APT; [unfold REC_SIZE; lia|]. intros a Ha. apply (glob_in_img B SEGS).
      unfold G_REC, REC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - apply APT; [unfold SC_SIZE; lia|]. intros a Ha. apply (glob_in_img B SEGS).
      unfold REC_SC, SC_SIZE, GLOB_LO, GLOB_N in *. lia. }
  split; [exact RJ'|]. split; [exact GR'|].
  split.
  { intros pn Hpn. apply in_app_or in Hpn as [H|[<-|[]]]; [exact (ON pn H)|].
    destruct (in_dec pair_dec (p, k) O) as [H|H]; [left; exact H | right; intros Hb].
    destruct (in_dec pair_dec (p, k) (blocks Lc Ac)) as [Hc|Hc]; [exact (NOTC Hc) | exact (H (B2 _ Hb Hc))]. }
  split.
  { intros pn Hpn. rewrite EB' in Hpn. apply in_app_or in Hpn as [H|[H|H]].
    - destruct (B1 pn ltac:(rewrite EB; apply in_or_app; left; exact H)) as [X|[X|X]];
        [left; exact X | right; left; apply in_or_app; left; exact X | right; right; exact X].
    - subst pn. right. left. apply in_or_app. right. left. reflexivity.
    - destruct (B1 pn ltac:(rewrite EB; apply in_or_app; right; exact H)) as [X|[X|X]];
        [left; exact X | right; left; apply in_or_app; left; exact X | right; right; exact X]. }
  split.
  { intros pn H1 H2. apply B2; [exact H1|]. intros Hc. exact (H2 (CUR pn Hc)). }
  split; [exact RA'|]. split; [exact F18'|].
  split.
  { rewrite <- (sb_shift_trans bc A Ac A'). rewrite <- (sb_shift_add (sb_shift bc A Ac) Lc Ac L' A' b1 b2 p k EB' EB).
    exact RS'. }
  split; [exact (CUR T TI)|].
  split.
  { intros Hin. apply in_app_or in Hin as [H|[H|[]]]; [exact (TO H)|]. rewrite <- H in TI. exact (NOTC TI). }
  split; [exact TA | exact TP].
Qed.

Lemma sinvT_sarg : forall T K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc Kc regs_c L' A' regs' m' md' m'' W x p k,
  sinvT T K S L A mem md O Lc Ac mc mdc (rec_record Rp fn As) Oc bc ->
  (length As < 6)%nat ->
  S - K <= spZ regs_c - Kc -> spZ regs_c <= S ->
  call_post_k B (aa_MR API) Kc Lc Ac regs_c mc mdc (fun a => p <= a < p + k) L' A' regs' m' md' ->
  munch W m' m'' -> wmono rsegs m' m'' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a ->
     rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS <= a < rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS + 4 \/
     rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) <= a <
       rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As) + 8) ->
  p <> 0 -> fresh_block B p k ->
  (exists b1 b2, blocks L' A' = b1 ++ (p, k) :: b2 /\ blocks Lc Ac = b1 ++ b2) ->
  (forall q n, In (q, n) (user_blocks Ac) -> In (q, n) (user_blocks A')) ->
  blocks_kept B Lc Ac mc m' (fun _ => False) ->
  (length (st_regions Ac) <= length (st_regions A'))%nat ->
  bytes_at rsegs m'' (rec_entry G_REC REC_SC Rp + CALL_OFF_NARGS) (le4 (Z_to_bv 64 (Z.of_nat (length As) + 1))) ->
  bytes_at rsegs m'' (rec_entry G_REC REC_SC Rp + CALL_OFF_ARGS + 8 * Z.of_nat (length As)) (le8 (Z_to_bv 64 p)) ->
  bytes_at rsegs m' p (x ++ [Z_to_bv 8 0]) ->
  no0 x -> Z.of_nat (length x) <= LMAX -> Z.of_nat (length x) + 1 <= k <= LMAX + 2 ->
  st_init_done A' = true ->
  res_ok_slots A' (sb_malloc (sb_shift bc A Ac) k) ->
  ro_agree rsegs m' -> f18_words rsegs m' ->
  sinvT T K S L A mem md O L' A' m'' md' (rec_record Rp fn (As ++ [x])) (Oc ++ [(p, k)]) bc.
Proof using SEGS AX GOWN GFACT ERRNO_LOW.
  intros T K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc Kc regs_c L' A' regs' m' md' m'' W x p k
    SI H6 HLO HHI POST MU WM HW Hp0 FB EBS UB BK RGN BN BS BX Hno Hlx Hsz INI RS' RA' F18'.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & GR & _).
  assert (HN : (length (r_calls Rp) <= 16)%nat).
  { pose proof GR as (Q0 & (_ & (C1 & _) & _) & _). unfold rec_record in C1.
    destruct (Nat.ltb (length (r_calls Rp)) 16) eqn:E; [apply Nat.ltb_lt in E; lia | exact C1]. }
  assert (ER : REC_SC <= rec_entry G_REC REC_SC Rp /\ rec_entry G_REC REC_SC Rp + CALL_SIZE <= G_REC + REC_SIZE).
  { unfold rec_entry. destruct (Nat.ltb (length (r_calls Rp)) 16) eqn:E.
    - apply Nat.ltb_lt in E. unfold REC_SC, G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. lia.
    - unfold REC_SC, G_REC, CALL_SIZE, REC_SIZE. lia. }
  assert (HWR : forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> rec_area a).
  { intros a Ra Hn. destruct (HW a Ra Hn) as [H|H];
      unfold rec_area, G_REC, REC_SC, REC_SIZE, SC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia. }
  assert (OUTW : forall a, 0 <= a < 2 ^ 64 -> ~ rec_area a -> outside W a).
  { intros a Ra Hr. destruct (outside_dec W a) as [H|H]; [exact H|]. exfalso. exact (Hr (HWR a Ra H)). }
  pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  rewrite SEGS in PF, PK, PS.
  assert (BLW : forall q n i, In (q, n) (user_blocks A') -> 0 <= i < n ->
            0 <= ptr_addr L' q + i < 2 ^ 64 /\ outside W (ptr_addr L' q + i)).
  { intros q n i Hin Hi. destruct (mr_blocks B _ LAWS L' A' m' md' q n i PM Hin Hi) as (Q1 & Q2 & Q3 & _).
    split; [lia|]. apply OUTW; [lia|]. intros Hr. apply (ax_blocks_img AX L' A' m' md' q n i PM Hin Hi).
    apply (glob_in_img B SEGS). exact (RecStub.rec_area_glob _ Hr). }
  assert (PM2 : aa_MR API L' A' m'' md').
  { apply (mr_keep B _ LAWS L' A' m' m'' md' W PM MU).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a PM Ho) as [Hl1 Hl2].
      apply OUTW; [lia|]. intros Hr. exact (GOWN L' A' m' md' a PM (glob_in a (RecStub.rec_area_glob a Hr)) Ho).
    - intros q n i Hin Hi. exact (proj2 (BLW q n i Hin Hi)). }
  assert (POST2 : call_post_k B (aa_MR API) Kc Lc Ac regs_c mc mdc
                    (fun a => p <= a < p + k \/ (0 <= a < 2 ^ 64 /\ ~ outside W a)) L' A' regs' m'' md').
  { split; [exact PM2|]. split; [exact PW|]. split; [exact PB|]. split; [exact PL|]. split; [exact PA|].
    split; [exact PR|]. split; [exact PV|]. rewrite SEGS.
    split.
    { intros a Hr Hn1 Hn2 Hs He.
      assert (Ra : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (in_img_low B SEGS a Hr); lia]).
      assert (Oa : outside W a).
      { destruct (outside_dec W a) as [H|H]; [exact H|]. exfalso. apply He. right. split; assumption. }
      destruct (PF a Hr Hn1 Hn2 Hs (fun H => He (or_introl H))) as [E1 E2].
      rewrite (munch_mbyte rsegs W m' m'' a MU Ra Oa). split; [exact E1|].
      rewrite E2. exact (munch_writable rsegs W m' m'' a MU Ra Oa). }
    split.
    { intros q n i H1 H2 Hi. rewrite <- (PK q n i H1 H2 Hi). rewrite <- (PA q n H1 H2).
      destruct (BLW q n i H2 Hi) as [Rr Oo]. exact (munch_mbyte rsegs W m' m'' _ MU Rr Oo). }
    intros a Hs. exact (WM _ (PS a Hs)). }
  pose proof FB as (FB1 & FB2 & FB3).
  pose proof (bytes_at_bound _ _ _ _ BX) as BXB. rewrite length_app in BXB. cbn [length] in BXB.
  apply (sinvT_arg T K S L A mem md O Lc Ac mc mdc Rp fn As Oc bc Kc regs_c _ L' A' regs' m'' md' x p k
           SI H6 HLO HHI POST2).
  - intros a [Ha|(Ra & Ha)]; [right; right; exact Ha|].
    destruct (HW a Ra Ha) as [H|H]; [left; exact H | right; left; exact H].
  - exact Hp0.
  - exact FB.
  - exact EBS.
  - exact UB.
  - unfold blocks_kept in *. rewrite SEGS in BK |- *. intros a0 k0 i Hin Hg Hi.
    rewrite <- (BK a0 k0 i Hin Hg Hi).
    destruct (rjr_blk_out B API SEGS AX K S O L A mem md Lc Ac mc mdc W RJ
                (fun a Ra Hn => or_intror (HWR a Ra Hn)) a0 k0 i Hin Hi) as [Rr Oo].
    exact (munch_mbyte rsegs W m' m'' _ MU Rr Oo).
  - exact RGN.
  - exact BN.
  - exact BS.
  - apply (bytes_at_transfer rsegs m' m'' p _ BX). intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    apply (munch_mbyte rsegs W m' m'' _ MU); [lia|]. apply OUTW; [lia|]. intros Hr.
    apply (FB3 i); [lia|]. apply (glob_in_img B SEGS). exact (RecStub.rec_area_glob _ Hr).
  - exact Hno.
  - exact Hlx.
  - exact Hsz.
  - exact INI.
  - exact RS'.
  - apply (ro_out W m' m'' RA' MU). intros a Ha Hro. apply OUTW; [lia|].
    intros Hr. rewrite glob_ro_false in Hro by exact (RecStub.rec_area_glob a Hr). discriminate.
  - apply (f18_out W m' m'' F18' MU). intros i Hi.
    split; (apply OUTW; unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, snprintf_c.GOT_GUARD, snprintf_c.GUARD; lia).
Qed.

End TMP.

Lemma hs_mix : mix_call_contract ->
  forall ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo e h : Z) (args : list (word * list byte))
    (sp1 ra0 q0 q1 q2 q3 q4 q5 q6 : word),
  mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp1) -> lo + 80 <= bv_unsigned sp1 -> 0x34108 <= lo ->
  rw_cells rsegs m (bv_unsigned sp1) [C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 ra0] ->
  bytes_at rsegs m e (le4 (Z_to_bv 64 6) ++ le4 (Z_to_bv 64 (Z.of_nat (length args)))) ->
  0x33d10 <= e -> e + 56 <= 0x340f8 -> (length args <= 6)%nat ->
  (forall k p, nth_error args k = Some p -> mc_arg m (bv_unsigned sp1 - 80) (bv_unsigned sp1) e k p) ->
  rw_cells rsegs m 0x34100 [C8 (Z_to_bv 64 h)] -> 0 <= h < 2 ^ 64 ->
  evt rsegs (fun ms' => exists t0' t1' t2' b0 b1 b2 b3 b4 b5 b6 b7 t3' t4' t5' t6' m',
       ms' = MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp1 + 64)) gp tp t0' t1' t2' q0 q1 b0
                     b1 b2 b3 b4 b5 b6 b7 q2 q3 q4 q5 q6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp1 - 80, bv_unsigned sp1); (0x34100, 0x34108)] m m'
       /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x34100 [C8 (Z_to_bv 64 (mixcall h 6 (map snd args)))])
    (MS (mkR ra sp1 gp tp t0 t1 t2 (Z_to_bv 64 0x33d10) (Z_to_bv 64 e) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x162f4) fc None m (seg_rom rsegs)).
Proof.
  intros MIX ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo e h args sp1 ra0 q0 q1 q2 q3 q4 q5 q6 MI ST LO LO2 FR EF E0 E1 LA HARG ES Hh.
  assert (MIX' := MIX). unfold mix_call_contract, MIX_CALL_FRAME in MIX'.
  pose proof (bv_unsigned_in_range 64 sp1) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (munch_refl [(bv_unsigned sp1 - 80, bv_unsigned sp1); (0x34100, 0x34108)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 3 step.
  call (MIX' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo 6 args).
  - exact MI.
  - exact ST.
  - lia.
  - lia.
  - exact LA.
  - rewrite unsigned_lit by lia. exact EF.
  - rewrite unsigned_lit by lia. lia.
  - intros k p Hk. rewrite unsigned_lit by lia. exact (HARG k p Hk).
  - eapply ro_bytes_at; [exact MI | unfold FNV_B0_ADDR; lia | rewrite length_le8; unfold FNV_B0_ADDR; lia |].
    apply ro_bytes_b_sound. vm_compute. reflexivity.
  - unfold FNV_B0_ADDR. lia.
  - rewrite (unsigned_lit h) by lia.
    do 11 step.
    apply evt_done. do 16 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma hs_len_cons : forall w ws, sup_host_setting_len (w :: ws) = Z.of_nat (length w) + 1 + sup_host_setting_len ws.
Proof. reflexivity. Qed.

Lemma hs_join_len : forall ws, ws <> [] -> Z.of_nat (length (join_sp ws)) + 1 = sup_host_setting_len ws.
Proof.
  induction ws as [|w ws IH]; intros H; [congruence|]. rewrite hs_len_cons.
  destruct ws as [|w2 ws'].
  - cbn [join_sp]. unfold sup_host_setting_len. cbn [fold_right]. lia.
  - change (join_sp (w :: w2 :: ws')) with (w ++ SPACE :: join_sp (w2 :: ws')).
    rewrite length_app. cbn [length]. specialize (IH ltac:(discriminate)). lia.
Qed.

Lemma hs_entry_bounds : forall R, 0x33d10 <= rec_entry G_REC REC_SC R /\ rec_entry G_REC REC_SC R + 56 <= 0x340f8.
Proof.
  intros R. unfold rec_entry. destruct (Nat.ltb (length (r_calls R)) 16) eqn:E.
  - apply Nat.ltb_lt in E. unfold G_REC, OFF_CALLS, CALL_SIZE. lia.
  - unfold REC_SC. lia.
Qed.

Lemma hs_pad_le : forall e c a, e <= c -> a < e + (- e) mod 8 -> a < 8 * ((c + 7) / 8).
Proof.
  intros e c a H1 H2.
  pose proof (Z.div_mod (- e) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (- e) 8 ltac:(lia)).
  pose proof (Z.div_mod (c + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (c + 7) 8 ltac:(lia)).
  lia.
Qed.

Lemma hs_present : forall segs m a, present m a -> mbyte segs m a <> None.
Proof. intros segs m a [b E]. unfold mbyte. rewrite E. discriminate. Qed.

Lemma hs_combine_snd : forall (X Y : Type) (l1 : list X) (l2 : list Y), length l1 = length l2 ->
  map snd (combine l1 l2) = l2.
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H |- *;
    [reflexivity | discriminate | discriminate | rewrite (IH l2 ltac:(lia)); reflexivity].
Qed.

Lemma hs_nth_combine : forall (X Y : Type) (l1 : list X) (l2 : list Y) k a b,
  nth_error (combine l1 l2) k = Some (a, b) -> nth_error l1 k = Some a /\ nth_error l2 k = Some b.
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] [|k] a b H; cbn in H |- *; try discriminate.
  - injection H as -> ->. split; reflexivity.
  - exact (IH l2 k a b H).
Qed.

Lemma hs_r_host_record : forall R fn As, r_host (rec_record R fn As) = r_host R.
Proof. intros R fn As. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.


Lemma hs_st3 :
  forall ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (junk : list byte),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 2)] ->
  rw_cells rsegs m (e + 24) [CB 8 junk] ->
  evt rsegs (fun ms' => exists b1 b2 m',
       ms' = MS (mkR (Z_to_bv 64 0x162f4) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 e) s4 b1 b2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x188cc) fc None m' (seg_rom rsegs)
       /\ munch [(e + 4, e + 8); (e + 24, e + 32)] m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 3)]
       /\ rw_cells rsegs m' (e + 24) [C8 a0])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 e) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x162d4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e junk EN EA.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  pose proof (rw_cells_bound _ _ _ _ EA) as EB8. cbn [cells_size csize Nat.add] in EB8.
  pose proof (munch_refl [(e + 4, e + 8); (e + 24, e + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step.
  rewrite sx32_lit by lia.
  replace (Z.shiftl (bv_unsigned (Z_to_bv 64 2)) 3) with 16 by reflexivity.
  replace (bv_unsigned (Z_to_bv 64 2) + 1) with 3 by reflexivity.
  do 4 step.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma hs_join_no0 : forall ws, Forall no0 ws -> no0 (join_sp ws).
Proof.
  intros ws HF. induction HF as [|w ws Hw HF IH]; [intros []|].
  destruct ws as [|w2 ws']; [exact Hw|].
  change (join_sp (w :: w2 :: ws')) with (w ++ SPACE :: join_sp (w2 :: ws')).
  apply no0_app; [exact Hw|]. intros [E|E]; [|exact (IH E)].
  apply (f_equal bv_unsigned) in E. unfold SPACE in E. rewrite !byte_unsigned in E by lia. discriminate.
Qed.

Lemma hs_eqb64 : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma hs_eqb64t : forall x y, x = y -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof. intros x y ->. unfold bv_eqb. apply Z.eqb_refl. Qed.

Lemma hs_eqb64f : forall x y, 0 < x < 2 ^ 64 -> 0 < y <= 2 ^ 64 -> x <> y ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof.
  intros x y Hx Hy N. unfold bv_eqb. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Z.eqb_neq.
  destruct (Z.eq_dec y (2 ^ 64)) as [E|E]; [rewrite E, Z_mod_same_full; lia | rewrite Z.mod_small by lia; lia].
Qed.

Lemma hs_signed_lit : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z H. unfold bv_signed. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.

Lemma hs_sltiu : forall (z : Z) (I : Z), 0 < z < 2 ^ 64 -> bv_wrap 64 I = 1 ->
  PropExec.v_sltiu (Z_to_bv 64 z) I = Z_to_bv 64 0.
Proof.
  intros z I Hz HI. unfold PropExec.v_sltiu. rewrite unsigned_lit by lia. rewrite HI.
  replace (z <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Definition tokf (m : word -> option byte) (p : Z) (w : list byte) : Prop :=
  exists slack, bytes_at rsegs m p (w ++ Z_to_bv 8 0 :: slack) /\ no0 w /\
    (- (p + Z.of_nat (length w) + 1)) mod 8 <= Z.of_nat (length slack) /\ 0 <= p.

Lemma tokf_same : forall m m' p w, tokf m p w -> munch [] m m' -> tokf m' p w.
Proof.
  intros m m' p w (slack & HP & NZ & SL & P0) MU. exists slack. split; [|auto].
  eapply bytes_at_transport; [exact HP | exact MU |]. cbn [disjoint_from]. exact I.
Qed.

Lemma hs_len_nn : forall ws, 0 <= sup_host_setting_len ws.
Proof. induction ws as [|w ws IH]; [unfold sup_host_setting_len; cbn; lia | rewrite hs_len_cons; lia]. Qed.

Section E1.
Variables (sp gp tp s0 s1 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (endp : Z).
Hypothesis STRLEN : strlen_contract.

Lemma hs_len_loop : forall (pl : list Z) (ws : list (list byte)) s2 s3 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m acc cur,
  mem_inv rsegs m -> Forall2 (tokf m) pl ws ->
  bytes_at rsegs m cur (concat (map (fun p => le8 (Z_to_bv 64 p)) pl)) ->
  endp = cur + 8 * Z.of_nat (length pl) -> pl <> [] -> 0 <= cur -> endp <= 2 ^ 64 ->
  0 <= acc -> acc + sup_host_setting_len ws < 2 ^ 63 ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
       ms' = MS (mkR (Z_to_bv 64 0x16250) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 (Z_to_bv 64 (acc + sup_host_setting_len ws)) (Z_to_bv 64 endp) (Z_to_bv 64 endp)
                     s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x16260) fc None m' (seg_rom rsegs)
       /\ munch [] m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 acc) (Z_to_bv 64 endp)
             (Z_to_bv 64 cur) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16248) fc None m (seg_rom rsegs)).
Proof.
  induction pl as [|p pl IH]; intros ws s2 s3 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m acc cur
    MI TK PB Hend Hne Hc He Ha Hl; [congruence|].
  inversion TK as [|? w ? ws' TP TK' E1 E2]; subst ws.
  destruct TP as (slack & HP & NZ & SL & P0).
  cbn [map concat] in PB. apply bytes_at_app in PB as [PB1 PB2]. rewrite length_le8 in PB2.
  change (Z.of_nat 8) with 8 in PB2.
  pose proof (bytes_at_bound _ _ _ _ HP) as BP. rewrite length_app in BP. cbn [length] in BP.
  pose proof (bytes_at_bound _ _ _ _ PB1) as B1. rewrite length_le8 in B1.
  cbn [length] in Hend.
  assert (RS : ov_read_bytes rsegs m (wa (cur + 0)) 8 = Some (le8 (Z_to_bv 64 p))).
  { rewrite (bytes_at_read rsegs m _ _ 0 8 PB1) by (rewrite ?length_le8; lia).
    change (Z.to_nat 0) with 0%nat. rewrite skipn_O. f_equal; apply firstn_all2; rewrite ?length_le8; lia. }
  assert (HPu : bytes_at rsegs m (bv_unsigned (Z_to_bv 64 p)) (w ++ Z_to_bv 8 0 :: slack))
    by (rewrite unsigned_lit by lia; exact HP).
  assert (SLu : (- (bv_unsigned (Z_to_bv 64 p) + Z.of_nat (length w) + 1)) mod 8 <= Z.of_nat (length slack))
    by (rewrite unsigned_lit by lia; exact SL).
  clear HP PB1.
  pose proof (munch_refl [] m) as MU.
  step. step.
  eapply evt_cut; [eapply STRLEN with (str := w) (slack := slack); [exact HPu | exact NZ | exact SLu | exact MI] |].
  post_call rsegs m.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
  assert (TK1 : Forall2 (tokf m1) pl ws') by (eapply Forall2_impl; [|exact TK']; intros p0 w0 Hq0; exact (tokf_same m m1 p0 w0 Hq0 MU)).
  step. step. step. step.
  destruct pl as [|p2 pl2].
  - inversion TK' as [E3 E4|]; subst ws'. cbn [length Z.of_nat] in Hend.
    rewrite (hs_eqb64t (cur + 8) endp) by lia. cbn [negb]. cbv iota.
    replace (Z_to_bv 64 (cur + 8)) with (Z_to_bv 64 endp) by (f_equal; lia).
    replace (Z_to_bv 64 (acc + Z.of_nat (length w) + 1)) with (Z_to_bv 64 (acc + sup_host_setting_len [w]))
      by (f_equal; unfold sup_host_setting_len; cbn [fold_right]; lia).
    apply evt_done. do 15 eexists. exists m1. split; [reflexivity|].
    split; [exact MU | exact MI1].
  - rewrite (hs_eqb64f (cur + 8) endp) by (cbn [length] in Hend; lia). cbn [negb]. cbv iota.
    eapply evt_mono.
    { eapply (IH ws' s2 s3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (acc + Z.of_nat (length w) + 1) (cur + 8));
        [exact MI1 | exact TK1 | exact PB2 | cbn [length] in Hend |- *; lia | discriminate | lia | lia | lia |].
      rewrite hs_len_cons in Hl. lia. }
    intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & MI2).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m2. split.
    + rewrite hs_len_cons.
      replace (acc + (Z.of_nat (length w) + 1 + sup_host_setting_len ws')) with
        (acc + Z.of_nat (length w) + 1 + sup_host_setting_len ws') by lia. reflexivity.
    + split; [exact (munch_trans _ _ _ _ MU MU2) | exact MI2].
Qed.

Lemma hs_e1 : forall ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 m (pl : list Z) ws ptok,
  mem_inv rsegs m -> Forall2 (tokf m) pl ws ->
  bytes_at rsegs m ptok (concat (map (fun p => le8 (Z_to_bv 64 p)) pl)) ->
  (1 <= length pl <= 64)%nat -> 0 <= ptok -> ptok + 8 * Z.of_nat (length pl) <= 2 ^ 64 ->
  sup_host_setting_len ws <= LMAX + 1 ->
  endp = ptok + 8 * Z.of_nat (length pl) ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
       ms' = MS (mkR (Z_to_bv 64 0x16278) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (sup_host_setting_len ws + 1))
                     a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (Z.of_nat (length pl))) (Z_to_bv 64 ptok)
                     (Z_to_bv 64 (sup_host_setting_len ws)) (Z_to_bv 64 endp) (Z_to_bv 64 endp)
                     s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x18a0c) fc None m' (seg_rom rsegs)
       /\ munch [] m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat (length pl))) (Z_to_bv 64 ptok)
             s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16234) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 m pl ws ptok MI TK PB NL P0 PE LW Hend.
  assert (SS : bv_signed (Z_to_bv 64 (Z.of_nat (length pl))) = Z.of_nat (length pl)) by (apply hs_signed_lit; lia).
  assert (US : bv_unsigned (Z_to_bv 64 (Z.of_nat (length pl))) = Z.of_nat (length pl)) by (apply unsigned_lit; lia).
  step. if_false. step. step. step. step.
  replace (Z_to_bv 64 (ptok + Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.of_nat (length pl)))) 3)) with (Z_to_bv 64 endp)
    by (f_equal; rewrite US, Z.shiftl_mul_pow2 by lia; lia).
  pose proof (hs_len_nn ws) as LN. unfold LMAX in LW.
  eapply evt_cut.
  { eapply (hs_len_loop pl ws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m 0 ptok);
      [exact MI | exact TK | exact PB | lia | destruct pl; [cbn in NL; lia | discriminate] | lia | lia | lia |
       lia]. }
  intros ms (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & MI1).
  step. step. step.
  match goal with |- context [PropExec.v_sltiu (Z_to_bv 64 ?z) ?I] =>
    rewrite (hs_sltiu z I) by first [lia | reflexivity] end.
  step. step.
  replace (Z_to_bv 64 (0 + sup_host_setting_len ws + 1)) with (Z_to_bv 64 (sup_host_setting_len ws + 1)) by (f_equal; lia).
  replace (Z_to_bv 64 (0 + sup_host_setting_len ws)) with (Z_to_bv 64 (sup_host_setting_len ws)) by (f_equal; lia).
  apply evt_done. do 14 eexists. exists m1. split; [reflexivity|]. split; [exact MU1 | exact MI1].
Qed.
End E1.

Lemma hs_join_snoc : forall X w,
  join_sp (X ++ [w]) = match X with [] => w | _ :: _ => join_sp X ++ SPACE :: w end.
Proof.
  induction X as [|x X IH]; intros w; [reflexivity|].
  destruct X as [|y X']; [reflexivity|].
  replace ((x :: y :: X') ++ [w]) with (x :: ((y :: X') ++ [w])) by reflexivity.
  replace (join_sp (x :: ((y :: X') ++ [w]))) with (x ++ SPACE :: join_sp ((y :: X') ++ [w])) by reflexivity.
  rewrite IH. change (join_sp (x :: y :: X')) with (x ++ SPACE :: join_sp (y :: X')).
  rewrite <- app_assoc. reflexivity.
Qed.

Definition hs_D (X : list (list byte)) : list byte := match X with [] => [] | _ :: _ => join_sp X ++ [SPACE] end.

Lemma hs_D_snoc : forall X w, join_sp (X ++ [w]) = hs_D X ++ w.
Proof. intros X w. rewrite hs_join_snoc. destruct X; [reflexivity|]. cbn [hs_D]. rewrite <- app_assoc. reflexivity. Qed.

Lemma hs_len_app : forall X Y, sup_host_setting_len (X ++ Y) = sup_host_setting_len X + sup_host_setting_len Y.
Proof.
  induction X as [|x X IH]; intros Y.
  - cbn [app]. change (sup_host_setting_len []) with 0. lia.
  - cbn [app]. rewrite !hs_len_cons, IH. lia.
Qed.

Lemma hs_D_len : forall X, Z.of_nat (length (hs_D X)) = sup_host_setting_len X.
Proof.
  intros [|x X]; [reflexivity|]. cbn [hs_D]. rewrite length_app. cbn [length].
  rewrite <- (hs_join_len (x :: X)) by discriminate. lia.
Qed.

Lemma hs_D_no0 : forall X, Forall no0 X -> no0 (hs_D X).
Proof.
  intros [|x X] HF; [intros []|]. cbn [hs_D]. apply no0_app; [exact (hs_join_no0 _ HF)|].
  intros [E|[]]. apply (f_equal bv_unsigned) in E. unfold SPACE in E. rewrite !byte_unsigned in E by lia. discriminate.
Qed.

Lemma hs_rw_mk : forall m a cs, cells_wf cs -> bytes_at rsegs m a (cells_bytes cs) ->
  wr_at rsegs m a (Z.of_nat (cells_size cs)) -> rw_cells rsegs m a cs.
Proof. intros m a cs H1 H2 H3. split; [split|]; assumption. Qed.

Lemma hs_wr_sub : forall m a n d k, wr_at rsegs m a n -> 0 <= d -> 0 <= k -> d + k <= n -> wr_at rsegs m (a + d) k.
Proof.
  intros m a n d k (H1 & H2 & H3) Hd Hk Hn. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + d + i) with (a + (d + i)) by ring. apply H3. lia.
Qed.

Section E2.
Variables (sp gp tp s0 s1 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (buf size Tlen lo : Z) (m0 : word -> option byte).
Hypothesis STRLEN : strlen_contract.
Hypothesis STRCAT : strcat_contract.
Hypothesis HBUF : 4096 <= buf.
Hypothesis HSZ : 0 < size.
Hypothesis HTL : size <= Tlen.
Hypothesis HTA : (buf + Tlen) mod 8 = 0.
Hypothesis HTLO : buf + Tlen <= lo.
Hypothesis HSP : lo + 48 <= bv_unsigned sp.

Definition jinvX (m : word -> option byte) (X : list byte) : Prop :=
  mem_inv rsegs m /\ stk rsegs m lo (bv_unsigned sp) /\
  munch [(bv_unsigned sp - 48, bv_unsigned sp); (buf, buf + size)] m0 m /\ wmono rsegs m0 m /\
  wr_at rsegs m buf size /\ bytes_at rsegs m buf X /\ Z.of_nat (length X) = Tlen.

Lemma hs_jpad : forall J junk, Z.of_nat (length (J ++ Z_to_bv 8 0 :: junk)) = Tlen ->
  (- (buf + Z.of_nat (length J) + 1)) mod 8 <= Z.of_nat (length junk).
Proof.
  intros J junk HL. rewrite length_app in HL. cbn [length] in HL.
  assert (E : (- (buf + Tlen)) mod 8 = 0) by (apply Z_mod_zero_opp_full; exact HTA).
  replace (- (buf + Z.of_nat (length J) + 1)) with (Z.of_nat (length junk) + - (buf + Tlen)) by lia.
  rewrite Zplus_mod, E, Z.add_0_r, Z.mod_mod by lia. apply Z.mod_le; lia.
Qed.

Lemma jinv_store : forall m P x S c, jinvX m (P ++ x :: S) -> Z.of_nat (length P) < size ->
  jinvX (write_to_mem m (wa (buf + Z.of_nat (length P))) [c]) (P ++ c :: S).
Proof.
  intros m P x S c (MI & ST & MU & WM & HW & HB & HL) Hp.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB. cbn [length] in BB.
  rewrite length_app in HL. cbn [length] in HL.
  assert (SO : store_ok rsegs m (wa (buf + Z.of_nat (length P))) (length [c]) = true)
    by (apply (wr_at_store_ok rsegs m buf size); [exact HW | lia | cbn [length]; lia]).
  apply bytes_at_app in HB as [HB1 HB2]. replace (x :: S) with ([x] ++ S) in HB2 by reflexivity.
  apply bytes_at_app in HB2 as [_ HB3]. cbn [length] in HB3.
  split; [exact (mem_inv_store rsegs m _ [c] MI SO)|].
  split; [apply stk_write; [exact ST | lia | cbn [length]; lia]|].
  split; [apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length Z.of_nat]; right; left; lia]|].
  split; [apply wmono_write; exact WM|].
  split; [apply wr_at_write; exact HW|].
  split; [|rewrite length_app; cbn [length]; lia].
  apply bytes_at_app. split.
  - apply bytes_at_write_other; [exact HB1 | lia | cbn [length]; lia | cbn [length]; lia].
  - replace (c :: S) with ([c] ++ S) by reflexivity. apply bytes_at_app. split.
    + apply bytes_at_write_same; cbn [length]; lia.
    + apply bytes_at_write_other; [exact HB3 | lia | cbn [length]; lia | cbn [length]; lia].
Qed.

Lemma jinv_strlen : forall m m' X, jinvX m X -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> jinvX m' X.
Proof.
  intros m m' X (MI & ST & MU & WM & HW & HB & HL) MU' WM' MI'.
  split; [exact MI'|].
  split; [apply (stk_transport_disjoint rsegs [] m m' _ _ ST MU' WM'); cbn [disjoint_from]; exact I|].
  split; [apply (munch_trans _ m0 m m' MU); apply (munch_weaken [] _ m m'); [intros x _; exact I | exact MU']|].
  split; [exact (wmono_trans rsegs _ _ _ WM WM')|].
  split; [exact (wr_at_transport rsegs m m' _ _ HW WM')|].
  split; [|exact HL].
  apply (bytes_at_transport rsegs [] m m' _ _ HB MU'). cbn [disjoint_from]. exact I.
Qed.

Lemma jinv_strcat : forall m m' D dslack w, jinvX m (D ++ Z_to_bv 8 0 :: dslack) ->
  munch [(bv_unsigned sp - 48, bv_unsigned sp);
         (buf + Z.of_nat (length D), buf + Z.of_nat (length D) + Z.of_nat (length w) + 1)] m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
  bytes_at rsegs m' buf (D ++ w ++ [Z_to_bv 8 0]) ->
  Z.of_nat (length D) + Z.of_nat (length w) + 1 <= size ->
  jinvX m' ((D ++ w) ++ Z_to_bv 8 0 :: skipn (length w) dslack).
Proof.
  intros m m' D dslack w (MI & ST & MU & WM & HW & HB & HL) MU' WM' MI' ST' HB' Hs.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB. cbn [length] in BB.
  rewrite length_app in HL. cbn [length] in HL.
  assert (LW : (length w <= length dslack)%nat) by lia.
  split; [exact MI'|]. split; [exact ST'|].
  split.
  { apply (munch_trans _ m0 m m' MU). eapply munch_weaken; [|exact MU'].
    intros x Hx. cbn [outside] in *. lia. }
  split; [exact (wmono_trans rsegs _ _ _ WM WM')|].
  split; [exact (wr_at_transport rsegs m m' _ _ HW WM')|].
  split.
  - assert (E : (D ++ w) ++ Z_to_bv 8 0 :: skipn (length w) dslack = (D ++ w ++ [Z_to_bv 8 0]) ++ skipn (length w) dslack)
      by (rewrite <- !app_assoc; reflexivity).
    rewrite E. apply bytes_at_app. split; [exact HB'|].
    apply bytes_at_app in HB as [_ HB2].
    replace (Z_to_bv 8 0 :: dslack) with ((Z_to_bv 8 0 :: firstn (length w) dslack) ++ skipn (length w) dslack) in HB2
      by (cbn [app]; rewrite firstn_skipn; reflexivity).
    apply bytes_at_app in HB2 as [_ HB3]. cbn [length] in HB3. rewrite length_firstn in HB3.
    rewrite !length_app. cbn [length].
    replace (buf + Z.of_nat (length D + (length w + 1))) with
      (buf + Z.of_nat (length D) + Z.of_nat (S (Nat.min (length w) (length dslack)))) by lia.
    apply (bytes_at_transport rsegs _ m m' _ _ HB3 MU'). cbn [disjoint_from]. rewrite length_skipn. lia.
  - rewrite !length_app. cbn [length]. rewrite length_skipn. lia.
Qed.

Definition tokj (p : Z) (w : list byte) : Prop :=
  exists slack, bytes_at rsegs m0 p (w ++ Z_to_bv 8 0 :: slack) /\ no0 w /\
    (- (p + Z.of_nat (length w) + 1)) mod 8 <= Z.of_nat (length slack) /\ 0 <= p /\
    (p + Z.of_nat (length (w ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= p) /\
    (p + Z.of_nat (length (w ++ Z_to_bv 8 0 :: slack)) <= buf \/ buf + size <= p).

Lemma hs_join_head : forall dws junk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s2 s3,
  jinvX m (join_sp dws ++ Z_to_bv 8 0 :: junk) -> Forall no0 dws ->
  sup_host_setting_len dws + 1 < size -> (length dws <= 64)%nat ->
  evt rsegs (fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' dslack,
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 buf)
                     (Z_to_bv 64 (Z.of_nat (length dws))) (Z_to_bv 64 32) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x162a8) fc None m' (seg_rom rsegs)
       /\ jinvX m' (hs_D dws ++ Z_to_bv 8 0 :: dslack))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 buf)
             (Z_to_bv 64 (Z.of_nat (length dws))) (Z_to_bv 64 32) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16290) fc None m (seg_rom rsegs)).
Proof.
  intros dws junk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s2 s3 JI NZ HL HN.
  destruct dws as [|w0 dws0].
  - change (Z.of_nat (length (@nil (list byte)))) with 0.
    step. if_true.
    apply evt_done. do 16 eexists. exists m, junk. split; [reflexivity | exact JI].
  - set (J := join_sp (w0 :: dws0)) in *.
    pose proof (hs_join_len (w0 :: dws0) ltac:(discriminate)) as JL. fold J in JL.
    assert (NZJ : no0 J) by exact (hs_join_no0 _ NZ).
    assert (US : bv_unsigned (Z_to_bv 64 (Z.of_nat (length (w0 :: dws0)))) = Z.of_nat (length (w0 :: dws0)))
      by (apply unsigned_lit; lia).
    pose proof JI as (_ & _ & _ & _ & _ & HB & HLX).
    pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB. cbn [length] in BB.
    assert (UB : bv_unsigned (Z_to_bv 64 buf) = buf) by (apply unsigned_lit; lia).
    assert (HBu : bytes_at rsegs m (bv_unsigned (Z_to_bv 64 buf)) (J ++ Z_to_bv 8 0 :: junk)) by (rewrite UB; exact HB).
    assert (SLu : (- (bv_unsigned (Z_to_bv 64 buf) + Z.of_nat (length J) + 1)) mod 8 <= Z.of_nat (length junk))
      by (rewrite UB; exact (hs_jpad J junk HLX)).
    pose proof JI as (MI & _).
    clear HB.
    pose proof (munch_refl [] m) as MUr. pose proof (wmono_refl rsegs m) as WMr.
    assert (KP : (1 <= length (w0 :: dws0))%nat) by (cbn [length]; lia).
    step. if_false. step. step.
    eapply evt_cut; [eapply STRLEN with (str := J) (slack := junk); [exact HBu | exact NZJ | exact SLu | exact MI] |].
    post_call rsegs m.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
    pose proof (jinv_strlen m m1 _ JI MUr WMr MI1) as JI1.
    step.
    pose proof JI1 as (_ & _ & _ & _ & HW1 & _).
    assert (HS1 : store_ok rsegs m1 (wa (buf + Z.of_nat (length J) + 0)) 1 = true).
    { replace (buf + Z.of_nat (length J) + 0) with (buf + Z.of_nat (length J)) by lia.
      apply (wr_at_store_ok rsegs m1 buf size); [exact HW1 | lia | lia]. }
    step.
    replace (le1 (Z_to_bv 64 32)) with [SPACE] by (vm_compute; reflexivity).
    replace (wa (buf + Z.of_nat (length J) + 0)) with (wa (buf + Z.of_nat (length J))) by (f_equal; lia).
    pose proof (jinv_store m1 J (Z_to_bv 8 0) junk SPACE JI1 ltac:(lia)) as JI2.
    set (m2 := write_to_mem m1 (wa (buf + Z.of_nat (length J))) [SPACE]) in *. clearbody m2.
    destruct junk as [|j0 junk'].
    { exfalso. rewrite length_app in HLX. cbn [length] in HLX. lia. }
    replace (J ++ SPACE :: j0 :: junk') with ((J ++ [SPACE]) ++ j0 :: junk') in JI2 by (rewrite <- app_assoc; reflexivity).
    pose proof JI2 as (_ & _ & _ & _ & HW2 & _).
    assert (HS2 : store_ok rsegs m2 (wa (buf + Z.of_nat (length J) + 1)) 1 = true).
    { rewrite <- Z.add_assoc. apply (wr_at_store_ok rsegs m2 buf size); [exact HW2 | lia | lia]. }
    step.
    match goal with |- context [write_to_mem _ _ (le1 ?v)] => replace (le1 v) with [Z_to_bv 8 0] by (vm_compute; reflexivity) end.
    replace (wa (buf + Z.of_nat (length J) + 1)) with (wa (buf + Z.of_nat (length (J ++ [SPACE]))))
      by (f_equal; rewrite length_app; cbn [length]; lia).
    pose proof (jinv_store m2 (J ++ [SPACE]) j0 junk' (Z_to_bv 8 0) JI2 ltac:(rewrite length_app; cbn [length]; lia)) as JI3.
    assert (JI3' : jinvX (write_to_mem m2 (Z_to_bv 64 (buf + Z.of_nat (length J) + 1)) [Z_to_bv 8 0])
                     (hs_D (w0 :: dws0) ++ Z_to_bv 8 0 :: junk')).
    { replace (Z_to_bv 64 (buf + Z.of_nat (length J) + 1)) with (wa (buf + Z.of_nat (length (J ++ [SPACE]))))
        by (unfold wa; f_equal; rewrite length_app; cbn [length]; lia). exact JI3. }
    apply evt_done. do 16 eexists. eexists. exists junk'. split; [reflexivity | exact JI3'].
Qed.

Lemma hs_join_cat : forall dws w p cur dslack ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s2,
  jinvX m (hs_D dws ++ Z_to_bv 8 0 :: dslack) -> Forall no0 dws -> tokj p w ->
  bytes_at rsegs m0 cur (le8 (Z_to_bv 64 p)) ->
  (cur + 8 <= lo \/ bv_unsigned sp <= cur) -> (cur + 8 <= buf \/ buf + size <= cur) ->
  sup_host_setting_len dws + Z.of_nat (length w) + 1 <= size ->
  evt rsegs (fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' dslack',
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 (cur + 8))
                     (Z_to_bv 64 buf) (Z_to_bv 64 (Z.of_nat (length dws) + 1)) (Z_to_bv 64 32)
                     s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x162bc) fc None m' (seg_rom rsegs)
       /\ jinvX m' (join_sp (dws ++ [w]) ++ Z_to_bv 8 0 :: dslack'))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 cur) (Z_to_bv 64 buf)
             (Z_to_bv 64 (Z.of_nat (length dws))) (Z_to_bv 64 32) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x162a8) fc None m (seg_rom rsegs)).
Proof.
  intros dws w p cur dslack ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s2 JI NZ TK PB HC1 HC2 HS.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (hs_D_len dws) as DL. pose proof (hs_D_no0 dws NZ) as DN.
  set (D := hs_D dws) in *.
  destruct TK as (tsl & TP & TN & TS & TP0 & TW1 & TW2).
  rewrite length_app in TW1, TW2. cbn [length] in TW1, TW2.
  pose proof JI as (MI & ST & MU & WM & HW & HB & HL).
  pose proof (hs_jpad D dslack HL) as PAD.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB, HL. cbn [length] in BB, HL.
  pose proof (bytes_at_bound _ _ _ _ TP) as BT. rewrite length_app in BT. cbn [length] in BT.
  assert (UB : bv_unsigned (Z_to_bv 64 buf) = buf) by (apply unsigned_lit; lia).
  assert (UP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (PBm : bytes_at rsegs m cur (le8 (Z_to_bv 64 p))).
  { apply (bytes_at_transport rsegs _ m0 m _ _ PB MU). cbn [disjoint_from]. rewrite length_le8.
    change (Z.of_nat 8) with 8. lia. }
  pose proof (bytes_at_bound _ _ _ _ PBm) as BC. rewrite length_le8 in BC. change (Z.of_nat 8) with 8 in BC.
  assert (RS : ov_read_bytes rsegs m (wa (cur + 0)) 8 = Some (le8 (Z_to_bv 64 p))).
  { rewrite (bytes_at_read rsegs m _ _ 0 8 PBm) by (rewrite ?length_le8; lia).
    change (Z.to_nat 0) with 0%nat. rewrite skipn_O. f_equal; apply firstn_all2; rewrite ?length_le8; lia. }
  assert (HPu : bytes_at rsegs m (bv_unsigned (Z_to_bv 64 p)) (w ++ Z_to_bv 8 0 :: tsl)).
  { rewrite UP. apply (bytes_at_transport rsegs _ m0 m _ _ TP MU). cbn [disjoint_from].
    rewrite length_app. cbn [length]. lia. }
  assert (HDu : bytes_at rsegs m (bv_unsigned (Z_to_bv 64 buf)) (D ++ Z_to_bv 8 0 :: dslack)) by (rewrite UB; exact HB).
  assert (LW : (length w <= length dslack)%nat) by lia.
  assert (RW : rw_cells rsegs m (bv_unsigned (Z_to_bv 64 buf) + Z.of_nat (length D))
                 [CB (S (length w)) (Z_to_bv 8 0 :: firstn (length w) dslack)]).
  { rewrite UB. apply hs_rw_mk.
    - cbn [cells_wf cell_wf length]. rewrite length_firstn, Nat.min_l by exact LW. split; [reflexivity | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. pose proof HB as HB0. apply bytes_at_app in HB0 as [_ HB2].
      replace (Z_to_bv 8 0 :: dslack) with ((Z_to_bv 8 0 :: firstn (length w) dslack) ++ skipn (length w) dslack) in HB2
        by (cbn [app]; rewrite firstn_skipn; reflexivity).
      apply bytes_at_app in HB2 as [HB2 _]. exact HB2.
    - cbn [cells_size csize]. apply (hs_wr_sub m buf size); [exact HW | lia | lia | lia]. }
  clear HB PB TP.
  step. step. step.
  eapply evt_cut.
  { eapply STRCAT with (dstr := D) (dslack := dslack) (str := w) (slack := tsl)
      (junk := Z_to_bv 8 0 :: firstn (length w) dslack) (lo := lo);
      [exact HDu | exact DN | rewrite UB; exact PAD | exact RW | exact HPu | exact TN | rewrite UP; exact TS
      | lia | exact ST | exact HSP | lia | lia | lia | exact MI]. }
  intros ms' PO. unfold strcat_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU' & WM' & MI' & ST' & HB' & _ & _).
  subst ms'. rewrite UB in MU', HB'.
  replace (ret_pc (Z_to_bv 64 0x162b4)) with (Z_to_bv 64 0x162b4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (jinv_strcat m m' D dslack w JI MU' WM' MI' ST' HB' ltac:(lia)) as JI'.
  step. step.
  apply evt_done. do 16 eexists. exists m', (skipn (length w) dslack). split; [reflexivity|].
  rewrite hs_D_snoc. exact JI'.
Qed.

Lemma hs_join_loop : forall (pl : list Z) ws dws (n endp cur : Z) junk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m,
  jinvX m (join_sp dws ++ Z_to_bv 8 0 :: junk) -> Forall no0 dws -> Forall2 tokj pl ws -> pl <> [] ->
  bytes_at rsegs m0 cur (concat (map (fun p => le8 (Z_to_bv 64 p)) pl)) ->
  endp = cur + 8 * Z.of_nat (length pl) -> (endp <= lo \/ bv_unsigned sp <= cur) -> (endp <= buf \/ buf + size <= cur) ->
  n = Z.of_nat (length dws + length pl) -> (length dws + length pl <= 64)%nat ->
  sup_host_setting_len (dws ++ ws) + 1 <= size ->
  evt rsegs (fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' slack,
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 n) (Z_to_bv 64 endp)
                     (Z_to_bv 64 buf) (Z_to_bv 64 n) (Z_to_bv 64 32) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x162c0) fc None m' (seg_rom rsegs)
       /\ jinvX m' (join_sp (dws ++ ws) ++ Z_to_bv 8 0 :: slack))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 n) (Z_to_bv 64 cur) (Z_to_bv 64 buf)
             (Z_to_bv 64 (Z.of_nat (length dws))) (Z_to_bv 64 32) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16290) fc None m (seg_rom rsegs)).
Proof.
  induction pl as [|p pl IH]; intros ws dws n endp cur junk ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m
    JI NZ TK Hne PB Hend HD1 HD2 Hn HN HS; [congruence|].
  inversion TK as [|? w ? ws' TP TK' E1 E2]; subst ws.
  cbn [map concat] in PB. apply bytes_at_app in PB as [PB1 PB2]. rewrite length_le8 in PB2.
  change (Z.of_nat 8) with 8 in PB2.
  cbn [length] in Hend, Hn, HN.
  pose proof (bytes_at_bound _ _ _ _ PB1) as B1. rewrite length_le8 in B1. change (Z.of_nat 8) with 8 in B1.
  pose proof HS as HS'. rewrite hs_len_app, hs_len_cons in HS'.
  pose proof (hs_len_nn ws') as LN0. pose proof (hs_len_nn dws) as LN1.
  pose proof TP as (_ & _ & TN & _).
  eapply evt_cut.
  { eapply (hs_join_head dws junk); [exact JI | exact NZ | lia | lia]. }
  intros ms (ra1 & t01 & t11 & t21 & a01 & a11 & a21 & a31 & a41 & a51 & a61 & a71 & t31 & t41 & t51 & t61 &
             m1 & dsl1 & -> & JI1).
  eapply evt_cut.
  { eapply (hs_join_cat dws w p cur dsl1); [exact JI1 | exact NZ | exact TP | exact PB1 | lia | lia | lia]. }
  intros ms (ra2 & t02 & t12 & t22 & a02 & a12 & a22 & a32 & a42 & a52 & a62 & a72 & t32 & t42 & t52 & t62 &
             m2 & dsl2 & -> & JI2).
  step.
  rewrite hs_eqb64 by lia.
  destruct pl as [|p2 pl2].
  - inversion TK' as [E3 E4|]; subst ws'. cbn [length] in Hend, Hn, HN.
    rewrite (proj2 (Z.eqb_eq n (Z.of_nat (length dws) + 1))) by lia. cbn [negb]. cbv iota.
    replace (Z_to_bv 64 (cur + 8)) with (Z_to_bv 64 endp) by (f_equal; lia).
    replace (Z_to_bv 64 (Z.of_nat (length dws) + 1)) with (Z_to_bv 64 n) by (f_equal; lia).
    apply evt_done. do 16 eexists. exists m2, dsl2. split; [reflexivity | exact JI2].
  - rewrite (proj2 (Z.eqb_neq n (Z.of_nat (length dws) + 1))) by (cbn [length] in Hn; lia). cbn [negb]. cbv iota.
    replace (Z_to_bv 64 (Z.of_nat (length dws) + 1)) with (Z_to_bv 64 (Z.of_nat (length (dws ++ [w]))))
      by (f_equal; rewrite length_app; cbn [length]; lia).
    eapply evt_mono.
    { eapply (IH ws' (dws ++ [w]) n endp (cur + 8) dsl2);
        [exact JI2 | apply Forall_app; split; [exact NZ | constructor; [exact TN | constructor]]
        | exact TK' | discriminate | exact PB2 | cbn [length] in Hend |- *; lia | lia | lia
        | rewrite length_app; cbn [length] in Hn |- *; lia | rewrite length_app; cbn [length] in HN |- *; lia
        | rewrite <- app_assoc; exact HS]. }
    intros ms' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
                m' & sl & -> & JI').
    do 16 eexists. exists m', sl. split; [reflexivity|]. rewrite <- app_assoc in JI'. exact JI'.
Qed.

Lemma hs_e2 : forall (pl : list Z) ws ptok X ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 m,
  jinvX m X -> Forall2 tokj pl ws ->
  bytes_at rsegs m0 ptok (concat (map (fun p => le8 (Z_to_bv 64 p)) pl)) ->
  (ptok + 8 * Z.of_nat (length pl) <= lo \/ bv_unsigned sp <= ptok) ->
  (ptok + 8 * Z.of_nat (length pl) <= buf \/ buf + size <= ptok) ->
  (1 <= length pl <= 64)%nat -> sup_host_setting_len ws + 1 <= size ->
  evt rsegs (fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' slack,
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     (Z_to_bv 64 (Z.of_nat (length pl))) (Z_to_bv 64 (ptok + 8 * Z.of_nat (length pl)))
                     (Z_to_bv 64 buf) (Z_to_bv 64 (Z.of_nat (length pl))) (Z_to_bv 64 32)
                     s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x162c0) fc None m' (seg_rom rsegs)
       /\ jinvX m' (join_sp ws ++ Z_to_bv 8 0 :: slack))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat (length pl)))
             (Z_to_bv 64 ptok) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16278) fc None m (seg_rom rsegs)).
Proof.
  intros pl ws ptok X ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6 m JI TK PB HD1 HD2 NL HS.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (UB : bv_unsigned (Z_to_bv 64 buf) = buf) by (apply unsigned_lit; lia).
  assert (SN : bv_signed (Z_to_bv 64 (Z.of_nat (length pl))) = Z.of_nat (length pl)) by (apply hs_signed_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 (Z.of_nat (length pl))) = Z.of_nat (length pl)) by (apply unsigned_lit; lia).
  pose proof JI as (_ & _ & _ & _ & HW & _ & HL).
  destruct X as [|x0 S]; [cbn [length] in HL; lia|].
  assert (HS0 : store_ok rsegs m (wa (buf + 0)) 1 = true)
    by (apply (wr_at_store_ok rsegs m buf size); [exact HW | lia | lia]).
  pose proof (jinv_store m [] x0 S (Z_to_bv 8 0) JI ltac:(cbn [length]; lia)) as JI0.
  clear JI HW.
  step. if_false. step. step.
  match goal with |- context [write_to_mem _ _ (le1 ?v)] => replace (le1 v) with [Z_to_bv 8 0] by (vm_compute; reflexivity) end.
  match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?a [Z_to_bv 8 0]) _) =>
    replace a with (wa (buf + Z.of_nat (length (@nil byte)))) by (unfold wa; f_equal; cbn [length Z.of_nat]; lia) end.
  set (m1 := write_to_mem m (wa (buf + Z.of_nat (length (@nil byte)))) [Z_to_bv 8 0]) in *. clearbody m1.
  step. if_false. step. step.
  eapply evt_mono.
  { eapply (hs_join_loop pl ws [] (Z.of_nat (length pl)) (ptok + 8 * Z.of_nat (length pl)) ptok S);
      [exact JI0 | constructor | exact TK | destruct pl; [cbn in NL; lia | discriminate] | exact PB | reflexivity
      | exact HD1 | exact HD2 | reflexivity | cbn [length Nat.add]; lia | exact HS]. }
  intros ms' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
              m' & sl & -> & JI').
  do 16 eexists. exists m', sl. split; [reflexivity | exact JI'].
Qed.

End E2.

Lemma hs_concat_len : forall pl, Z.of_nat (length (concat (map (fun p => le8 (Z_to_bv 64 p)) pl))) = 8 * Z.of_nat (length pl).
Proof.
  induction pl as [|p pl IH]; [reflexivity|].
  cbn [map concat]. rewrite length_app, length_le8. cbn [length]. lia.
Qed.

Lemma hs_pre_xs :
  forall ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z),
  rw_cells rsegs m (e + 4) [C4 (Z_to_bv 64 2)] ->
  evt rsegs (fun ms' => exists b1,
       ms' = MS (mkR (Z_to_bv 64 0x162d4) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 e) s4 b1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15780) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 e) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x162c0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m e EN.
  pose proof (rw_cells_bound _ _ _ _ EN) as EB. cbn [cells_size csize Nat.add] in EB.
  do 3 step.
  rewrite sx32_lit by lia.
  if_false.
  do 2 step.
  apply evt_done. eexists. reflexivity.
Qed.

Lemma hs_e2x : strlen_contract -> strcat_contract ->
  forall (sp gp tp s0 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (buf size Tlen lo e : Z)
    (m0 : word -> option byte) (pl : list Z) ws ptok X ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 t3 t4 t5 t6,
  4096 <= buf -> 0 < size -> size <= Tlen -> (buf + Tlen) mod 8 = 0 -> buf + Tlen <= lo ->
  lo + 48 <= bv_unsigned sp ->
  jinvX sp buf size Tlen lo m0 m0 X -> Forall2 (tokj sp buf size lo m0) pl ws ->
  bytes_at rsegs m0 ptok (concat (map (fun p => le8 (Z_to_bv 64 p)) pl)) ->
  (ptok + 8 * Z.of_nat (length pl) <= lo \/ bv_unsigned sp <= ptok) ->
  (ptok + 8 * Z.of_nat (length pl) <= buf \/ buf + size <= ptok) ->
  (1 <= length pl <= 64)%nat -> sup_host_setting_len ws + 1 <= size ->
  rw_cells rsegs m0 (e + 4) [C4 (Z_to_bv 64 2)] ->
  (e + 8 <= buf \/ buf + size <= e + 4) -> e + 8 <= bv_unsigned sp - 48 ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' slack,
       ms' = MS (mkR (Z_to_bv 64 0x162d4) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 e) (Z_to_bv 64 buf)
                     a1' a2' a3' a4' a5' a6' a7'
                     (Z_to_bv 64 (Z.of_nat (length pl))) (Z_to_bv 64 (ptok + 8 * Z.of_nat (length pl)))
                     (Z_to_bv 64 buf) (Z_to_bv 64 (Z.of_nat (length pl))) (Z_to_bv 64 32)
                     s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x15780) fc None m' (seg_rom rsegs)
       /\ jinvX sp buf size Tlen lo m0 m' (join_sp ws ++ Z_to_bv 8 0 :: slack))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 e) (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (Z.of_nat (length pl))) (Z_to_bv 64 ptok) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16278) fc None m0 (seg_rom rsegs)).
Proof.
  intros SL SC sp gp tp s0 s7 s8 s9 s10 s11 F fc buf size Tlen lo e m0 pl ws ptok X ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7
    s4 s5 s6 t3 t4 t5 t6 HB HS HT HA HL HP JI TK PB PW1 PW2 NL SZ NA ND1 ND2.
  eapply evt_cut.
  { eapply hs_e2 with (buf := buf) (size := size) (Tlen := Tlen) (lo := lo) (m0 := m0); eassumption. }
  intros ms (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & slack
    & -> & JI').
  pose proof JI' as (_ & _ & MU' & WM' & _).
  assert (NA' : rw_cells rsegs m' (e + 4) [C4 (Z_to_bv 64 2)]).
  { apply (rw_cells_transport rsegs _ m0 m' _ _ NA MU' WM'). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  eapply evt_mono; [eapply hs_pre_xs; exact NA' |].
  intros ms' (b1 & ->).
  exists t0', t1', t2', b1, a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', slack.
  split; [reflexivity | exact JI'].
Qed.

Lemma hs_nra_apart : forall s Ln lo hi, (forall a, s <= a < s + Ln -> ~ rec_area a) ->
  REC_SC <= lo -> hi <= G_REC + REC_SIZE -> lo < hi -> 0 < Ln -> s + Ln <= lo \/ hi <= s.
Proof.
  intros s Ln lo hi H H1 H2 H3 H4. destruct (Z_le_gt_dec (s + Ln) lo) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec hi s) as [D'|D']; [right; exact D'|]. exfalso.
  unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in *.
  destruct (Z_le_gt_dec s lo) as [D1|D1].
  - apply (H lo); [lia|]. destruct (Z_lt_ge_dec lo 212296); [left | right]; lia.
  - apply (H s); [lia|]. destruct (Z_lt_ge_dec s 212296); [left | right]; lia.
Qed.

Lemma hs_er : forall R, rec_entry G_REC REC_SC R mod 8 = 0 /\ REC_SC <= rec_entry G_REC REC_SC R /\
  rec_entry G_REC REC_SC R + CALL_SIZE <= G_REC + REC_SIZE.
Proof.
  intros R. unfold rec_entry. destruct (Nat.ltb (length (r_calls R)) 16) eqn:E.
  - apply Nat.ltb_lt in E. unfold G_REC, OFF_CALLS, CALL_SIZE, REC_SC, REC_SIZE.
    split; [|lia]. apply Z.mod_divide; [lia|]. exists (26539 + 7 * Z.of_nat (length (r_calls R))). lia.
  - unfold REC_SC, G_REC, CALL_SIZE, REC_SIZE. split; [reflexivity | lia].
Qed.
Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALLOC_PC : ms_malloc B = 0x18a0c.
Hypothesis FREE_PC : ms_free B = 0x188cc.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22a68.
Hypothesis GRD : ms_guard B = 0x54450.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis RCF : rec_calls_free_contract B API.
Hypothesis ARGL : arg_line_contract B API.
Hypothesis ARGI : arg_i_contract B API.
Hypothesis MALLOC : forall fx0 : YK11.FPState, malloc_contract (fx := fx0) B API.
Hypothesis FREE : forall fx0 : YK11.FPState, free_contract (fx := fx0) B API.
Hypothesis XSD : forall fx0 : YK11.FPState, xstrdup_contract (fx := fx0) B API.
Hypothesis STRLEN : strlen_contract.
Hypothesis STRCAT : strcat_contract.
Hypothesis MIX : mix_call_contract.

Lemma hs_mc_arg : forall Lc Ac mc mdc e k pn s lo hi,
  aa_MR API Lc Ac mc mdc -> ro_agree rsegs mc ->
  bytes_at rsegs mc (e + CALL_OFF_ARGS + 8 * Z.of_nat k) (le8 (Z_to_bv 64 (fst pn))) ->
  In pn (blocks Lc Ac) -> Z.of_nat (length s) + 1 <= snd pn ->
  bytes_at rsegs mc (fst pn) (s ++ [Z_to_bv 8 0]) -> no0 s -> Z.of_nat (length s) <= LMAX ->
  alloc_ceiling <= lo ->
  mc_arg (normalize rsegs mc) lo hi e k (Z_to_bv 64 (fst pn), s).
Proof using SEGS SLACK.
  intros Lc Ac mc mdc e k [q n] s lo hi HM RA BP Hb Hn BS N0 LX HLO. cbn [fst snd] in *.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_value as ACV.
  pose proof Hb as Hb0.
  unfold blocks in Hb. apply in_map_iff in Hb as ([u n'] & Eu & Hu). cbn in Eu. injection Eu as E0 E2. subst n'.
  assert (E1 : ptr_addr Lc u = q) by (rewrite <- E0; reflexivity). clear E0.
  pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. cbn [length] in BB.
  destruct (mr_blocks B _ LAWS Lc Ac mc mdc u n 0 HM Hu ltac:(lia)) as (_ & HQ1 & HQ2 & _). rewrite E1 in HQ1, HQ2.
  pose proof (Z.mod_pos_bound (- (q + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as Hpad.
  assert (CE : forall a, a < q + Z.of_nat (length s) + 1 + (- (q + Z.of_nat (length s) + 1)) mod 8 ->
            a < alloc_ceiling).
  { intros a Ha. pose proof (hs_pad_le (q + Z.of_nat (length s) + 1) (q + n) a ltac:(lia) Ha) as X.
    pose proof (Z.div_mod (q + n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (q + n + 7) 8 ltac:(lia)).
    pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)). destruct ACV as (_ & ACM). lia. }
  destruct (rs_bytes_pad rsegs mc q (s ++ [Z_to_bv 8 0])
              (Z.to_nat ((- (q + Z.of_nat (length s) + 1)) mod 8)) BS) as (sl & LS & BS2).
  - rewrite length_app. cbn [length].
    pose proof (CE (q + Z.of_nat (length s) + 1 + (- (q + Z.of_nat (length s) + 1)) mod 8 - 1) ltac:(lia)). lia.
  - intros j Hj. rewrite length_app. cbn [length].
    destruct (Z_lt_le_dec (q + Z.of_nat (length s + 1) + Z.of_nat j) (q + n)) as [Hl|Hl].
    + destruct (mr_blocks B _ LAWS Lc Ac mc mdc u n (Z.of_nat (length s + 1) + Z.of_nat j) HM Hu ltac:(lia))
        as (Hp & _).
      rewrite E1 in Hp. apply hs_present. replace (q + Z.of_nat (length s + 1) + Z.of_nat j)
        with (q + (Z.of_nat (length s + 1) + Z.of_nat j)) by ring. exact Hp.
    + apply hs_present. apply (SLACK Lc Ac mc mdc q n _ HM Hb0). split; [exact Hl|].
      apply (hs_pad_le (q + Z.of_nat (length s) + 1) (q + n)); lia.
  - unfold mc_arg. cbn [fst snd]. rewrite unsigned_lit by lia.
    split; [apply bytes_at_normalize; [exact RA | unfold CALL_OFF_ARGS in BP; exact BP]|].
    split; [exact N0|]. split; [exact LX|].
    exists sl. rewrite <- app_assoc in BS2. cbn [app] in BS2.
    split; [apply bytes_at_normalize; [exact RA | exact BS2]|].
    rewrite LS, Z2Nat.id by lia. split; [lia|]. left.
    pose proof (CE (q + Z.of_nat (length s) + 1 + (- (q + Z.of_nat (length s) + 1)) mod 8 - 1) ltac:(lia)). lia.
Qed.

Lemma hs_tstr : forall T K S L A mem md O Lc Ac mc mdc Rc Oc bc p x,
  sinvT B API T K S L A mem md O Lc Ac mc mdc Rc Oc bc -> fst T mod 8 = 0 ->
  ro_agree rsegs mem -> str_arg B L A O S K mem p (Some x) ->
  exists sl, bytes_at rsegs mc p (x ++ Z_to_bv 8 0 :: sl) /\ no0 x /\ 0 <= p /\
    (- (p + Z.of_nat (length x) + 1)) mod 8 = Z.of_nat (length sl) /\
    (p + Z.of_nat (length (x ++ Z_to_bv 8 0 :: sl)) <= S - K \/ S <= p) /\
    (p + Z.of_nat (length (x ++ Z_to_bv 8 0 :: sl)) <= fst T \/ fst T + snd T <= p).
Proof using SEGS ERRNO_LOW SLACK AX.
  intros T K S L A mem md O Lc Ac mc mdc Rc Oc bc p x SI TA RA H.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & _ & _ & _ & B2 & RAc & _ & _ & TI & _ & TAo & TP).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  destruct H as (Hp0 & N0 & LX & slack & BS & AL & DJ & HOME & NRA).
  rewrite SEGS in BS.
  pose proof RJ as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _ & HK & _).
  rewrite SEGS in HF, HK.
  destruct T as [t nT]. cbn [fst snd] in *.
  destruct (block_facts B _ LAWS Lc Ac mc mdc t nT 0 HM TI ltac:(lia)) as (_ & T1 & T2 & _).
  pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB. cbn [length] in BB.
  rewrite length_app in DJ, NRA. cbn [length] in DJ, NRA.
  set (pad := (- (p + Z.of_nat (length x) + 1)) mod 8) in *.
  assert (PADR : 0 <= pad < 8) by (unfold pad; apply Z.mod_pos_bound; lia).
  assert (PADA : (p + Z.of_nat (length x) + 1 + pad) mod 8 = 0).
  { unfold pad. rewrite Zplus_mod_idemp_r. replace (p + Z.of_nat (length x) + 1 + - (p + Z.of_nat (length x) + 1)) with 0
      by ring. reflexivity. }
  assert (PR0 : forall j, 0 <= j < pad -> mbyte rsegs mem (p + Z.of_nat (length x) + 1 + j) <> None).
  { intros j Hj E. pose proof BS as (_ & _ & HB).
    assert (Hlt : (Z.to_nat (Z.of_nat (length x) + 1 + j) < length (x ++ Z_to_bv 8 0 :: slack))%nat)
      by (rewrite length_app; cbn [length]; lia).
    specialize (HB (Z.to_nat (Z.of_nat (length x) + 1 + j)) Hlt).
    change (mrd rsegs mem (wa (p + Z.of_nat (Z.to_nat (Z.of_nat (length x) + 1 + j)))))
      with (mbyte rsegs mem (p + Z.of_nat (Z.to_nat (Z.of_nat (length x) + 1 + j)))) in HB.
    rewrite Z2Nat.id in HB by lia.
    replace (p + (Z.of_nat (length x) + 1 + j)) with (p + Z.of_nat (length x) + 1 + j) in HB by ring.
    rewrite E in HB. symmetry in HB. apply nth_error_None in HB. lia. }
  assert (TX0 : bytes_at rsegs mem p (x ++ [Z_to_bv 8 0])).
  { replace (x ++ Z_to_bv 8 0 :: slack) with ((x ++ [Z_to_bv 8 0]) ++ slack) in BS
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BS. exact (proj1 BS). }
  assert (LX1 : Z.of_nat (length (x ++ [Z_to_bv 8 0])) = Z.of_nat (length x) + 1)
    by (rewrite length_app; cbn [length]; lia).
  assert (SAME : (forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)) ->
                 bytes_at rsegs mc p (x ++ [Z_to_bv 8 0]) /\
                 (forall j, 0 <= j < pad -> mbyte rsegs mc (p + Z.of_nat (length x) + 1 + j) <> None)).
  { intros KE. split.
    - apply (bytes_at_transfer rsegs mem); [exact TX0|]. intros i Hi. rewrite LX1 in Hi. apply KE. lia.
    - intros j Hj. replace (p + Z.of_nat (length x) + 1 + j) with (p + (Z.of_nat (length x) + 1 + j)) by ring.
      rewrite KE by lia. replace (p + (Z.of_nat (length x) + 1 + j)) with (p + Z.of_nat (length x) + 1 + j) by ring.
      exact (PR0 j Hj). }
  assert (CASES : bytes_at rsegs mc p (x ++ [Z_to_bv 8 0]) /\
                  (forall j, 0 <= j < pad -> mbyte rsegs mc (p + Z.of_nat (length x) + 1 + j) <> None) /\
                  (p + Z.of_nat (length x) + 1 + pad <= t \/ t + nT <= p)).
  { destruct HOME as [(H1 & H2) | [(q & k & Hq & Hnq & H1 & H2) | (H1 & H2 & H3)]].
    - assert (KE : forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)).
      { intros i Hi. refine (proj1 (HF (p + i) _ _ _ _)).
        - unfold free_a. left. lia.
        - lia.
        - lia.
        - intros Hr. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in Hr. lia. }
      destruct (SAME KE) as [S1 S2]. split; [exact S1 | split; [exact S2 | right; lia]].
    - assert (NG : ~ In (q, k) O).
      { intros Ho. apply Hnq. apply in_map_iff. exists (q, k). split; [reflexivity | exact Ho]. }
      assert (QC : In (q, k) (blocks Lc Ac)).
      { destruct (in_dec pair_dec (q, k) (blocks Lc Ac)) as [Hc|Hc]; [exact Hc|]. exfalso. exact (NG (B2 _ Hq Hc)). }
      assert (NTq : (q, k) <> (t, nT)).
      { intros E. apply NG. rewrite E. apply TAo. rewrite <- E. exact Hq. }
      assert (DT : q + k <= t \/ t + nT <= q).
      { destruct (hs_blk_disj B API Lc Ac mc mdc (q, k) (t, nT) HM QC TI NTq) as [D|D];
          unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
      pose proof Hq as Hq'. unfold blocks in Hq'. apply in_map_iff in Hq' as ([pp k'] & E & Hp). cbn [fst snd] in E.
      injection E as E1 E2. subst k'.
      split.
      { apply (bytes_at_transfer rsegs mem); [exact TX0|]. intros i Hi. rewrite LX1 in Hi.
        assert (Hng : ~ (fun pn => In pn O) (ptr_addr L pp, k)) by (intros Hg; apply NG; rewrite <- E1; exact Hg).
        pose proof (HK pp k (p + i - q) Hp Hng ltac:(lia)) as E. rewrite E1 in E.
        replace (q + (p + i - q)) with (p + i) in E by ring. exact E. }
      split.
      { intros j Hj.
        assert (PRc : present mc (p + Z.of_nat (length x) + 1 + j)).
        { destruct (Z_lt_ge_dec (p + Z.of_nat (length x) + 1 + j) (q + k)) as [Hlt|Hge].
          - replace (p + Z.of_nat (length x) + 1 + j) with (q + (p + Z.of_nat (length x) + 1 + j - q)) by ring.
            exact (proj1 (block_facts B _ LAWS Lc Ac mc mdc q k (p + Z.of_nat (length x) + 1 + j - q) HM QC ltac:(lia))).
          - apply (SLACK Lc Ac mc mdc q k _ HM QC). split; [lia|]. Z.div_mod_to_equations. lia. }
        destruct PRc as [bb E]. unfold mbyte. rewrite E. discriminate. }
      destruct DT as [D|D]; [left | right; lia].
      pose proof (Z.div_mod (p + Z.of_nat (length x) + 1 + pad) 8 ltac:(lia)) as M1.
      pose proof (Z.div_mod t 8 ltac:(lia)) as M2. rewrite PADA in M1. rewrite TA in M2. lia.
    - pose proof H3 as H3'. rewrite SEGS in H3'.
      assert (ROALL : forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> ro_addr rsegs (Z_to_bv 64 (p + i)) = true).
      { intros i Hi. destruct (Z_lt_ge_dec i (Z.of_nat (length x) + 1)) as [Hl|Hl]; [exact (H3' i ltac:(lia))|].
        pose proof (H3' (Z.of_nat (length x)) ltac:(lia)) as Hlast. apply rs_ro_rsegs in Hlast; [|lia].
        apply rs_ro_rsegs; [lia|]. Z.div_mod_to_equations. lia. }
      assert (KE : forall i, 0 <= i < Z.of_nat (length x) + 1 + pad -> mbyte rsegs mc (p + i) = mbyte rsegs mem (p + i)).
      { intros i Hi. pose proof (ROALL i Hi) as RO.
        rewrite (mbyte_ro_agree _ _ _ RAc RO), (mbyte_ro_agree _ _ _ RA RO). reflexivity. }
      destruct (SAME KE) as [S1 S2].
      split; [exact S1 | split; [exact S2|]].
      destruct (Z_le_gt_dec (p + Z.of_nat (length x) + 1 + pad) t) as [D1|D1]; [left; exact D1|].
      destruct (Z_le_gt_dec (t + nT) p) as [D2|D2]; [right; exact D2|]. exfalso.
      apply (hs_blk_img B API AX Lc Ac mc mdc t nT (Z.max p t - t) HM TI ltac:(lia)).
      replace (t + (Z.max p t - t)) with (Z.max p t) by ring.
      apply (ro_in_img B SEGS); [lia|]. replace (Z.max p t) with (p + (Z.max p t - p)) by ring. apply ROALL. lia. }
  destruct CASES as (TX & PADP & DT).
  destruct (rs_bytes_pad rsegs mc p (x ++ [Z_to_bv 8 0]) (Z.to_nat pad) TX) as (sl & SL & BS').
  { rewrite LX1, Z2Nat.id by lia. lia. }
  { intros j Hj. rewrite LX1. replace (p + (Z.of_nat (length x) + 1) + Z.of_nat j)
      with (p + Z.of_nat (length x) + 1 + Z.of_nat j) by ring. apply PADP. lia. }
  rewrite <- app_assoc in BS'. cbn [app] in BS'.
  exists sl.
  split; [exact BS'|]. split; [exact N0|]. split; [lia|].
  split; [change ((- (p + Z.of_nat (length x) + 1)) mod 8) with pad; rewrite SL, Z2Nat.id by lia; reflexivity|].
  split; [rewrite length_app; cbn [length]; rewrite SL; destruct DJ as [D|D]; [left; lia | right; exact D]|].
  rewrite length_app; cbn [length]; rewrite SL. lia.
Qed.

Lemma hs_home_T : forall T K S L A mem md O Lc Ac mc mdc Rc Oc bc s n,
  sinvT B API T K S L A mem md O Lc Ac mc mdc Rc Oc bc -> 0 < n ->
  buf_home B L A O S s n -> s + n <= fst T \/ fst T + snd T <= s.
Proof using SEGS AX.
  intros T K S L A mem md O Lc Ac mc mdc Rc Oc bc s n SI Hn HOME.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof SI as (RJ & _ & _ & _ & B2 & _ & _ & _ & TI & _ & TAo & TP).
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & _).
  destruct T as [t nT]. cbn [fst snd] in *.
  destruct (block_facts B _ LAWS Lc Ac mc mdc t nT 0 HM TI ltac:(lia)) as (_ & T1 & T2 & _).
  unfold buf_home in HOME. rewrite SEGS in HOME.
  destruct HOME as [(H1 & H2) | [(q & k & Hq & Hnq & H1 & H2) | (H1 & H2 & H3)]].
  - right. lia.
  - assert (NG : ~ In (q, k) O).
    { intros Ho. apply Hnq. apply in_map_iff. exists (q, k). split; [reflexivity | exact Ho]. }
    assert (QC : In (q, k) (blocks Lc Ac)).
    { destruct (in_dec pair_dec (q, k) (blocks Lc Ac)) as [Hc|Hc]; [exact Hc|]. exfalso. exact (NG (B2 _ Hq Hc)). }
    assert (NTq : (q, k) <> (t, nT)).
    { intros E. apply NG. rewrite E. apply TAo. rewrite <- E. exact Hq. }
    destruct (hs_blk_disj B API Lc Ac mc mdc (q, k) (t, nT) HM QC TI NTq) as [D|D];
      unfold ranges_disjoint in D; cbn [fst snd] in D; lia.
  - destruct (Z_le_gt_dec (s + n) t) as [D1|D1]; [left; exact D1|].
    destruct (Z_le_gt_dec (t + nT) s) as [D2|D2]; [right; exact D2|]. exfalso.
    apply (hs_blk_img B API AX Lc Ac mc mdc t nT (Z.max s t - t) HM TI ltac:(lia)).
    replace (t + (Z.max s t - t)) with (Z.max s t) by ring.
    apply (ro_in_img B SEGS); [lia|]. replace (Z.max s t) with (s + (Z.max s t - s)) by ring. apply H3. lia.
Qed.

Section Run.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (pl ptok : Z) (ps : list Z) (line : list byte) (toks : list (list byte)) (R : rstate) (O : list (Z * Z))
  (b : sbound).
Hypothesis PRE : call_pre_t B API SUP_HOST_SETTING_K L A regs mem md.
Hypothesis A10 : getr regs 10 = Z_to_bv 64 pl.
Hypothesis A11 : getr regs 11 = Z_to_bv 64 ptok.
Hypothesis A12 : getr regs 12 = Z_to_bv 64 (Z.of_nat (length toks)).
Hypothesis NT : (1 <= length toks <= 64)%nat.
Hypothesis SA : str_arg B L A O (spZ regs) SUP_HOST_SETTING_K mem pl (Some line).
Hypothesis PT0 : ptok <> 0.
Hypothesis PT8 : ptok mod 8 = 0.
Hypothesis PTB : Mem.bytes_at (ms_segs B) mem ptok (concat (map (fun p => Mem.le8 (Z_to_bv 64 p)) ps)).
Hypothesis PTW : ptok + 8 * Z.of_nat (length toks) <= spZ regs - SUP_HOST_SETTING_K \/ spZ regs <= ptok.
Hypothesis PTH : buf_home B L A O (spZ regs) ptok (8 * Z.of_nat (length toks)).
Hypothesis PTR : forall a, ptok <= a < ptok + 8 * Z.of_nat (length toks) -> ~ rec_area a.
Hypothesis TKS : Forall2 (fun p w => str_arg B L A O (spZ regs) SUP_HOST_SETTING_K mem p (Some w)) ps toks.
Hypothesis TLEN : sup_host_setting_len toks <= LMAX + 1.
Hypothesis GR : g_rec_rep (ms_segs B) L A mem R O.
Hypothesis RA : ro_agree (ms_segs B) mem.
Hypothesis FRM : frm_zero fp_csr.
Hypothesis F18 : f18_words (ms_segs B) mem.
Hypothesis RES : res_ok_slots A b.
Hypothesis ROOM : room_slots (sb_mallocs b (sup_host_setting_sizes line toks)) (LMAX + 2).

Lemma hs_args_len : Forall (fun s => Z.of_nat (length s) <= LMAX)
  [canon line; dec (Z.of_nat (length toks)); join_sp toks].
Proof.
  pose proof SA as (_ & _ & LX & _).
  pose proof (canon_length line) as CL.
  pose proof (dec_length (Z.of_nat (length toks)) ltac:(lia)) as DL.
  pose proof (hs_join_len toks ltac:(destruct toks; [cbn in NT; lia | discriminate])) as JL.
  repeat constructor; unfold LMAX in *; lia.
Qed.

Lemma hs_tail : forall (fx' : YK11.FPState) L9 A9 R9 m9 md9 O9,
  sinv B API SUP_HOST_SETTING_K (spZ regs) L A mem md O L9 A9 m9 md9
    (rec_record R REC_HOST_SETTING [canon line; dec (Z.of_nat (length toks)); join_sp toks]) O9 b ->
  sb_le (sb_shift b A A9) (sb_mallocs b (sup_host_setting_sizes line toks)) ->
  st_init_done A9 = true -> fp_kept fx fx' ->
  getr R9 2 = Z_to_bv 64 (spZ regs - 64) -> getr R9 8 = Z_to_bv 64 0x33d10 ->
  getr R9 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  kept_ex [2; 8; 9; 18; 19; 20; 21; 22] regs R9 ->
  rw_cells rsegs m9 (spZ regs - 64)
    [C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
     C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  SR rsegs (mkCfg (@mkst fx' R9 (Z_to_bv 64 0x162f4) m9 (seg_rom rsegs)) md9)
    (sup_host_setting_ret (fx := fx) B API L A regs mem md line toks R O b).
Proof.
  intros fx' L9 A9 R9 m9 md9 O9 SI BLE INI FK T2 T8 T9 KT FR.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_HOST_SETTING_K in HCEIL, HWS, SI.
  pose proof SI as (RJ & GR9 & ON & B1 & B2 & RA9 & F189 & RS9).
  pose proof RJ as (HM & _ & _ & _ & _ & HLen & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  destruct (mr_model B _ LAWS L9 A9 m9 md9 HM) as (Hh & Hl & _).
  pose proof hs_args_len as LXA.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (HN : (length (r_calls R) <= 16)%nat).
  { pose proof GR as (Q0 & (_ & (C1 & _) & _) & _). exact C1. }
  pose proof (hs_entry_bounds R) as (EB1 & EB2).
  set (As3 := [canon line; dec (Z.of_nat (length toks)); join_sp toks]) in *.
  set (R3 := rec_record R REC_HOST_SETTING As3) in *.
  pose proof GR9 as (Q & HRep & HO).
  pose proof HRep as (HS & HC & HA & HP & HX & HW).
  pose proof HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  destruct (rec_rep_entry _ _ _ _ _ _ _ _ _ _ GR9 HN) as (P & CA).
  destruct CA as (CF1 & CF2 & CLP & CFN & CNA & CND & CKA). cbn [fst snd] in *.
  set (e := rec_entry G_REC REC_SC R) in *.
  set (args := combine (map (fun pn => Z_to_bv 64 (fst pn)) P) As3).
  assert (LP : length (map (fun pn => Z_to_bv 64 (fst pn)) P) = length As3) by (rewrite length_map; exact CLP).
  assert (LA : length args = length As3) by (unfold args; rewrite length_combine, LP; lia).
  assert (U2 : bv_unsigned (reg_get R9 2) = bv_unsigned sp - 64).
  { change (reg_get R9 2) with (getr R9 2). rewrite T2. apply unsigned_lit. lia. }
  assert (ARGS : forall k p, nth_error args k = Some p ->
            mc_arg (normalize rsegs m9) (bv_unsigned sp - 64 - 80) (bv_unsigned sp - 64) e k p).
  { intros k [w s] Hk. destruct (hs_nth_combine _ _ _ _ k w s Hk) as (Hw & Hs).
    rewrite nth_error_map in Hw. destruct (nth_error P k) as [pn|] eqn:EP; cbn in Hw; [|discriminate].
    injection Hw as <-.
    destruct (CKA k s pn Hs EP) as (BP & PNZ & PIN & PSZ & PBS & PN0).
    apply (hs_mc_arg L9 A9 m9 md9 e k pn s); [exact HM | exact RA9 | exact BP | exact PIN | lia | exact PBS | exact PN0 | |].
    - rewrite Forall_forall in LXA. apply LXA. exact (nth_error_In _ _ Hs).
    - lia. }
  assert (EF : bytes_at rsegs (normalize rsegs m9) e
                 (le4 (Z_to_bv 64 6) ++ le4 (Z_to_bv 64 (Z.of_nat (length args))))).
  { apply bytes_at_normalize; [exact RA9|]. apply bytes_at_app. split.
    - unfold CALL_OFF_FN in CFN. rewrite Z.add_0_r in CFN. exact CFN.
    - rewrite LA. replace (e + Z.of_nat (length (le4 (Z_to_bv 64 6)))) with (e + CALL_OFF_NARGS)
        by (rewrite length_le4; unfold CALL_OFF_NARGS; reflexivity). exact CNA. }
  assert (STn : stk rsegs (normalize rsegs m9) (bv_unsigned sp - 8320) (bv_unsigned sp - 64)).
  { apply stk_norm; [lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSC. left. lia. }
  assert (FRn : rw_cells rsegs (normalize rsegs m9) (bv_unsigned sp - 64)
                  [C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
                   C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply rw_cells_normalize; [exact RA9 | exact FR |]. intros i Hi. cbn in Hi. unfold wa. apply ro_addr_hi. lia. }
  assert (ESn : rw_cells rsegs (normalize rsegs m9) 0x34100 [C8 (Z_to_bv 64 (r_host R3))]).
  { apply rw_cells_normalize; [exact RA9 | | intros i Hi; cbn in Hi; apply glob_ro_false; unfold GLOB_LO, GLOB_N; lia].
    apply rc_cell8; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia |].
    replace 0x34100 with (G_REC + OFF_HOST) by (unfold G_REC, OFF_HOST; lia). exact X5. }
  assert (Q8 : reg_get R9 8 = Z_to_bv 64 0x33d10) by exact T8.
  assert (Q9 : reg_get R9 9 = Z_to_bv 64 e) by exact T9.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q8, Q9.
    eapply (evt_normalize rsegs); [exact WX | exact RA9 |].
    eapply (hs_mix MIX) with (lo := bv_unsigned sp - 8320);
      [apply mem_inv_normalize | rewrite U2; exact STn | rewrite U2; lia | lia | rewrite U2; exact FRn
      | exact EF | lia | lia | rewrite LA; cbn; lia | | exact ESn | exact X10].
    intros k p Hk. rewrite U2. exact (ARGS k p Hk). }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & b0' & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3' & t4' & t5' & t6' & m1n & -> & MU1n
    & WM1n & ES1n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m9 RA9) MR1r RO1 MU1n) as MU1.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m9 RA9) MR1r RO1 WM1n) as WM1.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR1r ES1n) as ES1.
  rewrite U2 in MU1. unfold args in ES1. rewrite (hs_combine_snd _ _ _ _ LP) in ES1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R10 & -> & X10r).
  assert (HWW : forall a, 0 <= a < 2 ^ 64 ->
            ~ outside [(bv_unsigned sp - 64 - 80, bv_unsigned sp - 64); (0x34100, 0x34108)] a ->
            bv_unsigned sp - 8320 <= a < bv_unsigned sp \/ rec_area a).
  { intros a Ra Hm. cbn in Hm. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE. lia. }
  assert (SI2 : sinv B API 8320 (bv_unsigned sp) L A mem md O L9 A9 m1 md9 (rec_mix_host R3 (REC_HOST_SETTING, As3)) O9 b).
  { apply (sinv_munch_core B API SEGS GOWN AX 8320 (bv_unsigned sp) L A mem md O L9 A9 m9 md9 R3 O9 b m1 _
             (rec_mix_host R3 (REC_HOST_SETTING, As3)) SI MU1 WM1 HWW).
    unfold g_rec_rep in *. unfold rec_mix_host. cbn [fst snd].
    apply (rec_rep_set_host rsegs G_REC REC_SC L9 A9 m9 m1 R3 O9 (mixcall (r_host R3) REC_HOST_SETTING As3) GR9).
    - apply mixcall_range. exact X10.
    - replace (G_REC + OFF_HOST) with 0x34100 by (unfold G_REC, OFF_HOST; lia). exact (rc_c8_bytes m1 0x34100 _ ES1).
    - intros a Ha N. apply (munch_mbyte rsegs _ m9 m1 a MU1); [unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha; lia|].
      match goal with |- outside ?W a => destruct (outside_dec W a) as [H|H]; [exact H|] end. exfalso.
      cbn in H. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE, OFF_HOST in *. lia.
    - intros a Ha _. apply glob_writable. unfold G_REC, REC_SIZE, REC_SC, SC_SIZE, GLOB_LO, GLOB_N in *. lia.
    - exact (sinv_kept B API SEGS AX 8320 (bv_unsigned sp) L A mem md O L9 A9 m9 md9 R3 O9 b m1 _ SI MU1 HWW). }
  assert (E10_2 : getr R10 2 = sp).
  { rewrite (getr_of_eqv _ _ 2 X10r eq_refl). simp_regs. rewrite U2.
    replace (bv_unsigned sp - 64 + 64) with (bv_unsigned sp) by ring. apply Z_to_bv_bv_unsigned. }
  assert (RP10 : regs_preserved regs R10).
  { apply (kept_ex_pres [2; 8; 9; 18; 19; 20; 21; 22]).
    - apply (kept_ex_trans _ regs R9 R10 KT). kept_ex_tac X10r.
    - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|Hr]; [exact E10_2|].
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
        match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv _ _ k X10r eq_refl) end;
        simp_regs; first [reflexivity | unfold getr; reflexivity]. }
  pose proof SI2 as (RJ2 & GR2 & ON2 & B12 & B22 & RA2 & F182 & RS2).
  apply SR_ret. unfold sup_host_setting_ret.
  exists fx', L9, A9, R10, m1, md9, O9.
  split; [rewrite SEGS, (ret_pc_of_ok _ HRA); reflexivity|].
  split; [exact FK|].
  split.
  { apply (rjr_final B (aa_MR API) CTX 8320 rec_area (fun pn => In pn O) (fun a => In a (map fst O)) L A regs mem md
             L9 A9 R10 m1 md9 PRK RJ2 RP10).
    intros a0 k0 G. exact (in_map fst O (a0, k0) G). }
  split; [rewrite SEGS; exact GR2|].
  split; [exact ON2|].
  split; [exact B12|].
  split; [exact (rjr_others_kept B (aa_MR API) 8320 (bv_unsigned sp) rec_area (fun pn => In pn O) L A mem md
                   L9 A9 m1 md9 O RJ2 (fun pn H => H))|].
  split; [rewrite SEGS; exact RA2|].
  split; [rewrite SEGS; exact F182|].
  split; [exact INI|].
  split; [pose proof RJ2 as (_ & _ & _ & _ & _ & HLen2 & _); exact HLen2|].
  split; [exact BLE | exact RS2].
Qed.


Lemma hs_toks_no0 : Forall no0 toks.
Proof.
  pose proof TKS as H. clear -H. induction H as [|p w ps' ws' Hp _ IH]; [constructor|].
  constructor; [|exact IH]. destruct Hp as (_ & N0 & _). exact N0.
Qed.

Lemma hs_xs : forall (fx' : YK11.FPState) Lj Aj Rj mj mdj Oj (q : sptr) slack,
  sinvT B API (ptr_addr Lj q, sup_host_setting_len toks + 1) SUP_HOST_SETTING_K (spZ regs) L A mem md O Lj Aj mj mdj
    (rec_record R REC_HOST_SETTING [canon line; dec (Z.of_nat (length toks))]) Oj b ->
  In (q, sup_host_setting_len toks + 1) (user_blocks Aj) ->
  sb_le (sb_shift b A Aj)
    (sb_malloc (sb_malloc (sb_malloc b (Z.of_nat (length line) + 1))
       (Z.of_nat (length (dec (Z.of_nat (length toks)))) + 1)) (sup_host_setting_len toks + 1)) ->
  fp_kept fx fx' ->
  getr Rj 1 = Z_to_bv 64 0x162d4 -> getr Rj 2 = Z_to_bv 64 (spZ regs - 64) -> getr Rj 4 = getr regs 4 ->
  getr Rj 8 = Z_to_bv 64 0x33d10 -> getr Rj 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  getr Rj 10 = Z_to_bv 64 (ptr_addr Lj q) -> getr Rj 20 = Z_to_bv 64 (ptr_addr Lj q) ->
  kept_ex [2; 8; 9; 18; 19; 20; 21; 22] regs Rj ->
  rw_cells rsegs mj (spZ regs - 64)
    [C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
     C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  bytes_at rsegs mj (ptr_addr Lj q) (join_sp toks ++ Z_to_bv 8 0 :: slack) ->
  (- (ptr_addr Lj q + Z.of_nat (length (join_sp toks)) + 1)) mod 8 <= Z.of_nat (length slack) ->
  ptr_addr Lj q + Z.of_nat (length (join_sp toks ++ Z_to_bv 8 0 :: slack)) <= alloc_ceiling ->
  SR rsegs (mkCfg (@mkst fx' Rj (Z_to_bv 64 0x15780) mj (seg_rom rsegs)) mdj)
    (sup_host_setting_ret (fx := fx) B API L A regs mem md line toks R O b).
Proof.
  intros fx' Lj Aj Rj mj mdj Oj q slack SI QIN BLE FK E1 E2 E4 E8 E9 E10 E20 KE FR BJ AL SLB.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_HOST_SETTING_K in HCEIL, HWS, SI.
  pose proof SI as (RJ & GR9 & ON & B1 & B2 & RA9 & F189 & RS9 & TI & TO & TA & TP).
  pose proof RJ as (HM & _).
  pose proof (hs_entry_bounds R) as (EB1 & EB2).
  assert (HN : (length (r_calls R) <= 16)%nat).
  { pose proof GR as (Q0 & (_ & (C1 & _) & _) & _). exact C1. }
  destruct (rec_rep_entry _ _ _ _ _ _ _ _ _ _ GR9 HN) as (P & CA).
  destruct CA as (_ & _ & _ & _ & CNA & _). cbn [snd length Z.of_nat] in CNA.
  set (e := rec_entry G_REC REC_SC R) in *.
  assert (EE : e = rec_entry G_REC REC_SC R) by reflexivity.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (SPj : spZ Rj = bv_unsigned sp - 64) by (unfold spZ; rewrite E2; apply unsigned_lit; lia).
  set (t := ptr_addr Lj q) in *.
  set (nT := sup_host_setting_len toks + 1) in *.
  set (x := join_sp toks) in *.
  assert (TNE : toks <> []) by (destruct toks; [cbn in NT; lia | discriminate]).
  pose proof (hs_join_len toks TNE) as JL. fold x in JL.
  assert (XN0 : no0 x) by exact (hs_join_no0 toks hs_toks_no0).
  assert (XL : Z.of_nat (length x) <= LMAX) by (unfold LMAX in *; lia).
  set (kx := Z.of_nat (length x) + 1) in *.
  pose proof (bytes_at_bound _ _ _ _ BJ) as SB. rewrite length_app in SB. cbn [length] in SB.
  destruct (block_facts B _ LAWS Lj Aj mj mdj t nT 0 HM TI ltac:(cbn in TP; lia)) as (_ & T1 & T2 & _).
  pose proof (XSD fx') as XS. unfold xstrdup_contract in XS. rewrite SEGS in XS.
  assert (ROOMx : room_slots (sb_malloc (sb_shift b A Aj) kx) kx).
  { unfold sb_mallocs, sup_host_setting_sizes in ROOM. cbn [fold_left] in ROOM. fold x kx in ROOM.
    eapply room_slots_mono; [apply sb_malloc_mono; exact BLE | | exact ROOM]. unfold kx, LMAX in *. lia. }
  eapply SR_bind.
  { apply (XS Lj Aj Rj mj mdj t x slack (sb_shift b A Aj)).
    - apply (call_pre_k_of_rjr B _ 8320 (bv_unsigned sp) rec_area _ L A mem md Lj Aj mj mdj XSTRDUP_K Rj RJ).
      + rewrite E1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SPj. replace (bv_unsigned sp - 64) with (bv_unsigned sp + (-4) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SPj. unfold XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SPj. lia.
      + rewrite E4. exact HTP.
    - exact E10.
    - exact BJ.
    - exact XN0.
    - exact XL.
    - exact AL.
    - left. rewrite SPj. unfold XSTRDUP_K, ALLOC_STACK. lia.
    - right. left. exists t, nT. split; [exact TI|]. unfold nT, kx in *. lia.
    - exact RS9.
    - exact ROOMx.
    - exact RA9. }
  intros c2 RET.
  destruct RET as (L8 & A8 & R8 & m8 & md8 & p & -> & POST8 & A0' & NZ & AL16 & FB8 & BLK8 & BK8 & UB8 & BYT8 & SRC8
    & RA8 & GK8 & INI8 & RGN8 & RS8).
  rewrite SEGS in RA8, BYT8 |- *.
  pose proof POST8 as (PM8 & _ & _ & _ & PA8 & RP8 & _ & PF8 & _).
  pose proof FB8 as (FBa & FBb & FBc).
  assert (POST8' : call_post_k B (aa_MR API) XSTRDUP_K Lj Aj Rj mj mdj (fun a => p <= a < p + kx) L8 A8 R8 m8 md8).
  { pose proof POST8 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
    split; [exact Q6|]. split; [exact Q7|]. split; [|split; [exact Q9 | exact Q10]].
    intros a H1 H2 H3 H4 H5. apply Q8; [exact H1 | exact H2 | exact H3 | exact H4 | cbv beta in H5 |- *; unfold kx in *; lia]. }
  assert (FR8 : rw_cells rsegs m8 (bv_unsigned sp - 64)
                  [C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
                   C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs mj); [exact FR|]. intros i Hi. cbn in Hi.
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW XSTRDUP_K Lj Aj Rj mj mdj _ L8 A8 R8 m8 md8 (bv_unsigned sp - 64 + i)
                HM POST8 ltac:(lia) ltac:(rewrite SPj; unfold XSTRDUP_K, ALLOC_STACK; lia)) as [K1 K2].
    - intros H. cbv beta in H. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (GK : forall a, GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N -> mbyte rsegs m8 a = mbyte rsegs mj a).
  { intros a Ha. destruct (GFACT a (glob_in a Ha)) as (Gi & _ & _ & Ge).
    rewrite SEGS in PF8.
    refine (proj1 (PF8 a (or_intror Gi) (GOWN Lj Aj mj mdj a HM (glob_in a Ha)) (GOWN L8 A8 m8 md8 a PM8 (glob_in a Ha))
                    _ _)).
    - unfold scratch_k. rewrite SPj. unfold XSTRDUP_K, ALLOC_STACK.
      intros [H|H]; [unfold GLOB_LO, GLOB_N in Ha; lia | exact (Ge H)].
    - cbv beta. intros H. apply (FBc (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Gi. }
  assert (NA8 : rw_cells rsegs m8 (e + 4) [C4 (Z_to_bv 64 2)]).
  { apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia|].
    apply (bytes_at_transfer rsegs mj); [unfold CALL_OFF_NARGS in CNA; exact CNA|]. intros i Hi. rewrite length_le4 in Hi.
    apply GK. unfold GLOB_LO, GLOB_N; lia. }
  destruct (glob_rw_cells m8 (e + 24) 8 ltac:(unfold GLOB_LO; lia) ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW8].
  assert (NAn : rw_cells rsegs (normalize rsegs m8) (e + 4) [C4 (Z_to_bv 64 2)]).
  { apply rw_cells_normalize; [exact RA8 | exact NA8 |]. intros i Hi. cbn in Hi.
    apply glob_ro_false. unfold GLOB_LO, GLOB_N; lia. }
  assert (EWn : rw_cells rsegs (normalize rsegs m8) (e + 24) [CB 8 junk]).
  { apply rw_cells_normalize; [exact RA8 | exact EW8 |]. intros i Hi. cbn in Hi.
    apply glob_ro_false. unfold GLOB_LO, GLOB_N; lia. }
  destruct (ax_statics AX L8 A8 m8 md8 PM8) as (_ & (g & Hg & HWg) & _).
  rewrite GRD, SEGS in HWg.
  assert (F188 : f18_words rsegs m8).
  { apply (f18_words_after mj m8 g F189); [|exact Hg | exact HWg].
    intros i Hi. pose proof (GK8 i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  destruct (mr_model B _ LAWS L8 A8 m8 md8 PM8) as (Hh8 & Hl8 & _).
  assert (R8_9 : reg_get R8 9 = Z_to_bv 64 e) by exact (eq_trans (RP8 9 ltac:(unfold callee_saved; lia)) E9).
  rewrite E1.
  eapply evt_SR_canon; [ | exact Hh8 | exact Hl8 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite R8_9.
    eapply (evt_normalize rsegs); [exact WX | exact RA8 |].
    eapply hs_st3; [exact NAn | exact EWn]. }
  intros ms9 (can9 & (s9n & Q9 & REL9 & RO9) & EQ9).
  destruct Q9 as (b91 & b92 & m9n & -> & MU9n & WM9n & NA9n & EA9n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL9) as [EC9 MR9r].
  revert EC9 MR9r RO9 EQ9. generalize (ms_mem can9) as m9. intros m9 EC9 MR9r RO9 EQ9. subst can9.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m8 RA8) MR9r RO9 MU9n) as MU9.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m8 RA8) MR9r RO9 WM9n) as WM9.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR9r NA9n) as NA9.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR9r EA9n) as EA9.
  clear MU9n WM9n NA9n EA9n MR9r.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ9 eq_refl eq_refl) as (R9 & -> & X9).
  assert (BN9 : bytes_at rsegs m9 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS)
                  (le4 (Z_to_bv 64 (Z.of_nat (length [canon line; dec (Z.of_nat (length toks))]) + 1)))).
  { apply cells_bytes_at in NA9. cbn [cells_bytes cbytes] in NA9. rewrite app_nil_r in NA9. exact NA9. }
  assert (BS9 : bytes_at rsegs m9 (rec_entry G_REC REC_SC R + CALL_OFF_ARGS +
                    8 * Z.of_nat (length [canon line; dec (Z.of_nat (length toks))])) (le8 (Z_to_bv 64 p))).
  { apply cells_bytes_at in EA9. cbn [cells_bytes cbytes] in EA9. rewrite app_nil_r in EA9.
    replace (rec_entry G_REC REC_SC R + CALL_OFF_ARGS + 8 * Z.of_nat (length [canon line; dec (Z.of_nat (length toks))]))
      with (e + 24) by (rewrite EE; unfold CALL_OFF_ARGS; cbn [length Z.of_nat]; lia).
    assert (Q : reg_get R8 10 = Z_to_bv 64 p) by exact A0'. rewrite Q in EA9. exact EA9. }
  pose proof (sinvT_sarg B API SEGS ERRNO_LOW GFACT GOWN AX (t, nT) 8320 (bv_unsigned sp) L A mem md O Lj Aj mj mdj R
                REC_HOST_SETTING [canon line; dec (Z.of_nat (length toks))] Oj b XSTRDUP_K Rj L8 A8 R8 m8 md8 m9
                [(e + 4, e + 8); (e + 24, e + 32)] x p kx
                SI ltac:(cbn; lia) ltac:(rewrite SPj; unfold XSTRDUP_K, ALLOC_STACK; lia) ltac:(rewrite SPj; lia)
                POST8' MU9 WM9
                ltac:(intros a Ra Hm; cbn in Hm; rewrite <- EE; unfold CALL_OFF_NARGS, CALL_OFF_ARGS; cbn [length Z.of_nat]; lia)
                NZ FB8 BLK8 UB8 BK8 RGN8 BN9 BS9 BYT8 XN0 XL ltac:(unfold kx, LMAX in *; lia) INI8 RS8 RA8 F188) as SI9.
  cbn [app] in SI9.
  assert (PQ : ptr_addr L8 q = t) by exact (PA8 q nT QIN (UB8 q nT QIN)).
  rewrite <- PQ in SI9.
  pose proof SI9 as (RJ9 & _ & _ & _ & _ & RA9' & _ & RS9' & TI9 & _).
  pose proof RJ9 as (HM9 & _).
  assert (KR9 : kept_ex [2; 8; 9; 18; 19; 20; 21; 22] regs R9).
  { apply (kept_ex_trans _ regs Rj R9 KE). apply (kept_ex_trans _ Rj R8 R9 (kept_ex_of_pres _ _ _ RP8)).
    kept_ex_tac X9. }
  assert (R9_1 : getr R9 1 = Z_to_bv 64 0x162f4) by (rewrite (getr_of_eqv _ _ 1 X9 eq_refl); simp_regs; reflexivity).
  assert (R9_2 : getr R9 2 = Z_to_bv 64 (bv_unsigned sp - 64)).
  { rewrite (getr_of_eqv _ _ 2 X9 eq_refl). simp_regs. exact (eq_trans (RP8 2 ltac:(unfold callee_saved; lia)) E2). }
  assert (R9_4 : getr R9 4 = getr regs 4).
  { rewrite (getr_of_eqv _ _ 4 X9 eq_refl). simp_regs. exact (eq_trans (RP8 4 ltac:(unfold callee_saved; lia)) E4). }
  assert (R9_8 : getr R9 8 = Z_to_bv 64 0x33d10).
  { rewrite (getr_of_eqv _ _ 8 X9 eq_refl). simp_regs. exact (eq_trans (RP8 8 ltac:(unfold callee_saved; lia)) E8). }
  assert (R9_9 : getr R9 9 = Z_to_bv 64 e).
  { rewrite (getr_of_eqv _ _ 9 X9 eq_refl). simp_regs. reflexivity. }
  assert (R9_10 : getr R9 10 = Z_to_bv 64 (ptr_addr L8 q)).
  { rewrite (getr_of_eqv _ _ 10 X9 eq_refl). simp_regs. rewrite PQ.
    exact (eq_trans (RP8 20 ltac:(unfold callee_saved; lia)) E20). }
  assert (SP9 : spZ R9 = bv_unsigned sp - 64) by (unfold spZ; rewrite R9_2; apply unsigned_lit; lia).
  assert (FR9 : rw_cells rsegs m9 (bv_unsigned sp - 64)
                  [C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
                   C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transport rsegs _ m8 m9 _ _ FR8 MU9 WM9). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  assert (BLE8 : sb_le (sb_shift b A A8) (sb_mallocs b (sup_host_setting_sizes line toks))).
  { destruct BLK8 as (bl1 & bl2 & EB1' & EB2').
    rewrite <- (sb_shift_trans b A Aj A8).
    rewrite <- (sb_shift_add (sb_shift b A Aj) Lj Aj L8 A8 bl1 bl2 p _ EB1' EB2').
    unfold sb_mallocs, sup_host_setting_sizes. cbn [fold_left]. fold x kx. fold nT.
    apply sb_malloc_mono. exact BLE. }
  replace (Z_to_bv 64 0x188cc) with (Z_to_bv 64 (ms_free B)) by (rewrite FREE_PC; reflexivity).
  pose proof (FREE fx') as FRE. unfold free_contract in FRE. rewrite SEGS in FRE.
  eapply SR_bind.
  { apply (FRE L8 A8 R9 m9 md8 q nT (sb_shift b A A8)).
    - apply (proj2 (call_pre_k_alloc B (aa_MR API) _ _ _ _ _)).
      apply (call_pre_k_of_rjr B _ 8320 (bv_unsigned sp) rec_area _ L A mem md L8 A8 m9 md8 ALLOC_STACK R9 RJ9).
      + rewrite R9_1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP9. replace (bv_unsigned sp - 64) with (bv_unsigned sp + (-4) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold ALLOC_STACK. lia.
      + rewrite SP9. unfold ALLOC_STACK. lia.
      + rewrite SP9. lia.
      + rewrite R9_4. exact HTP.
    - exact RA9'.
    - exact (UB8 q nT QIN).
    - exact R9_10.
    - exact RS9'. }
  intros c10 (Lf & Af & Rf & mf & mdf & -> & POST10 & BLK10 & BK10 & RA10 & GK10 & UB10 & INI10 & RGN10 & RS10).
  pose proof (sinvT_free B API SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX 8320 (bv_unsigned sp) L A mem md O L8 A8 m9 md8
                (rec_record R REC_HOST_SETTING [canon line; dec (Z.of_nat (length toks)); x]) (Oj ++ [(p, kx)]) b
                R9 Lf Af Rf mf mdf q nT) as SIF.
  pose proof POST10 as POST10k. apply (proj1 (call_post_k_alloc B (aa_MR API) _ _ _ _ _ _ _ _ _ _ _)) in POST10k.
  pose proof POST10k as (PM10 & _ & _ & _ & _ & RP10 & _).
  assert (SI10 := SIF SI9 ltac:(rewrite SP9; unfold ALLOC_STACK; lia) ltac:(rewrite SP9; lia) (UB8 q nT QIN)
                    POST10 BLK10 BK10 RA10 GK10 UB10 (INI10 INI8) RGN10 RS10).
  rewrite R9_1.
  apply (hs_tail fx' Lf Af Rf mf mdf (Oj ++ [(p, kx)]) SI10).
  - destruct BLK10 as (bl1 & bl2 & EB1' & EB2').
    rewrite <- (sb_shift_trans b A A8 Af).
    rewrite PQ in EB1'. rewrite <- (sb_shift_del (sb_shift b A A8) L8 A8 Lf Af bl1 bl2 t nT EB1' EB2').
    eapply sb_le_trans; [apply sb_free_le; unfold nT; lia | exact BLE8].
  - exact (INI10 INI8).
  - exact FK.
  - exact (eq_trans (RP10 2 ltac:(unfold callee_saved; lia)) R9_2).
  - exact (eq_trans (RP10 8 ltac:(unfold callee_saved; lia)) R9_8).
  - exact (eq_trans (RP10 9 ltac:(unfold callee_saved; lia)) R9_9).
  - exact (kept_ex_trans _ regs R9 Rf KR9 (kept_ex_of_pres _ _ _ RP10)).
  - apply (rw_cells_transfer rsegs m9); [exact FR9|]. intros i Hi. cbn in Hi.
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW ALLOC_STACK L8 A8 R9 m9 md8 _ Lf Af Rf mf mdf (bv_unsigned sp - 64 + i)
                HM9 POST10k ltac:(lia) ltac:(rewrite SP9; unfold ALLOC_STACK; lia)) as [K1 K2].
    + intros H. cbv beta in H.
      destruct (block_facts B _ LAWS L8 A8 m9 md8 _ nT 0 HM9 TI9 ltac:(cbn in TP; unfold nT in *; lia)) as (_ & _ & X3 & _).
      lia.
    + split; [exact K1 | exact (proj1 K2)].
Qed.

Definition hs_m_goal : Prop := forall (fx' : YK11.FPState) L2 A2 R2 m2 md2 O2,
  sinv B API SUP_HOST_SETTING_K (spZ regs) L A mem md O L2 A2 m2 md2
    (rec_record R REC_HOST_SETTING [canon line; dec (Z.of_nat (length toks))]) O2 b ->
  sb_le (sb_shift b A A2)
    (sb_malloc (sb_malloc b (Z.of_nat (length line) + 1)) (Z.of_nat (length (dec (Z.of_nat (length toks)))) + 1)) ->
  fp_kept fx fx' ->
  getr R2 2 = Z_to_bv 64 (spZ regs - 64) -> getr R2 4 = getr regs 4 ->
  getr R2 8 = Z_to_bv 64 0x33d10 -> getr R2 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  getr R2 18 = getr regs 12 -> getr R2 19 = getr regs 11 ->
  kept_ex [2; 8; 9; 18; 19; 20; 21; 22] regs R2 ->
  rw_cells rsegs m2 (spZ regs - 64)
    [C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
     C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  SR rsegs (mkCfg (@mkst fx' R2 (Z_to_bv 64 0x16234) m2 (seg_rom rsegs)) md2)
    (sup_host_setting_ret (fx := fx) B API L A regs mem md line toks R O b).

Lemma hs_room : forall k, 0 <= k <= LMAX + 2 -> forall bb,
  sb_le bb (sb_mallocs b (sup_host_setting_sizes line toks)) -> room_slots bb k.
Proof.
  intros k Hk bb H. eapply room_slots_mono; [exact H | exact Hk | exact ROOM].
Qed.

Lemma hs_ble : forall bb, sb_le bb (sb_malloc (sb_malloc b (Z.of_nat (length line) + 1))
    (Z.of_nat (length (dec (Z.of_nat (length toks)))) + 1)) ->
  sb_le bb (sb_mallocs b (sup_host_setting_sizes line toks)).
Proof.
  intros bb H. unfold sb_mallocs, sup_host_setting_sizes. cbn [fold_left].
  assert (TNE : toks <> []) by (destruct toks; [cbn in NT; lia | discriminate]).
  pose proof (hs_join_len toks TNE) as JL.
  eapply sb_le_trans; [exact H|].
  eapply sb_le_trans; [|apply sb_le_malloc; lia]. apply sb_le_malloc; lia.
Qed.

Lemma hs_argi : hs_m_goal -> forall L2 A2 R3 m2 md2 O2,
  sinv B API SUP_HOST_SETTING_K (spZ regs) L A mem md O L2 A2 m2 md2
    (rec_record R REC_HOST_SETTING [canon line]) O2 b ->
  sb_le (sb_shift b A A2) (sb_malloc b (Z.of_nat (length line) + 1)) ->
  getr R3 1 = Z_to_bv 64 0x16234 -> getr R3 2 = Z_to_bv 64 (spZ regs - 64) -> getr R3 4 = getr regs 4 ->
  getr R3 8 = Z_to_bv 64 0x33d10 -> getr R3 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  getr R3 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R3 11 = getr regs 12 ->
  getr R3 18 = getr regs 12 -> getr R3 19 = getr regs 11 ->
  kept_ex [2; 8; 9; 18; 19; 20; 21; 22] regs R3 ->
  rw_cells rsegs m2 (spZ regs - 64)
    [C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
     C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  bytes_at rsegs m2 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS) (le4 (Z_to_bv 64 1)) ->
  SR rsegs (mkCfg (mkst R3 (Z_to_bv 64 0x15b1c) m2 (seg_rom rsegs)) md2)
    (sup_host_setting_ret (fx := fx) B API L A regs mem md line toks R O b).
Proof.
  intros HMG L2 A2 R3 m2 md2 O2 SI2 BLE2 E1 E2 E4 E8 E9 E10 E11 E18 E19 KE2 FR2 NA2.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_HOST_SETTING_K in HCEIL, SI2.
  pose proof (hs_er R) as ER.
  pose proof (dec_length (Z.of_nat (length toks)) ltac:(lia)) as DL.
  set (e := rec_entry G_REC REC_SC R) in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (SP3 : spZ R3 = bv_unsigned sp - 64) by (unfold spZ; rewrite E2; apply unsigned_lit; lia).
  pose proof SI2 as (RJ2 & _ & _ & _ & _ & RA2 & F182 & RS2).
  pose proof RJ2 as (HM2 & _).
  pose proof ARGI as AI. unfold arg_i_contract in AI. rewrite SEGS in AI.
  eapply SR_bind.
  { apply (AI L2 A2 R3 m2 md2 e (Z.of_nat (length toks)) 1 (sb_shift b A A2)).
    - split; [|rewrite SP3; lia].
      apply (call_pre_k_of_rjr B _ 8320 (bv_unsigned sp) rec_area _ L A mem md L2 A2 m2 md2 ARG_I_K R3 RJ2).
      + rewrite E1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP3. replace (bv_unsigned sp - 64) with (bv_unsigned sp + (-4) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP3. unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK. lia.
      + rewrite SP3. lia.
      + rewrite E4. exact HTP.
    - exact E10.
    - rewrite E11. exact A12.
    - lia.
    - exact (proj1 ER).
    - exact (proj1 (proj2 ER)).
    - exact (proj2 (proj2 ER)).
    - apply glob_wr_at; unfold REC_SC, G_REC, REC_SIZE, CALL_SIZE, GLOB_LO, GLOB_N in *; lia.
    - exact NA2.
    - lia.
    - exact F182.
    - exact FRM.
    - exact RS2.
    - apply hs_room; [unfold LMAX; lia|]. apply hs_ble.
      eapply sb_le_trans; [apply sb_malloc_mono; exact BLE2|]. apply sb_le_refl.
    - exact RA2. }
  intros c2 (fx' & L3 & A3 & R4 & m3 & md3 & -> & FK & BK3 & UB3 & _ & RA3 & _ & F183 & RGN3 & ALT).
  destruct ALT as [(H06 & _)|(_ & p & POST3 & Hp0 & _ & FB3 & BLK3 & BN3 & BS3 & BX3 & INI3 & RS3)]; [lia|].
  rewrite SEGS in RA3, F183, BN3, BS3, BX3 |- *.
  pose proof (sinv_arg B API SEGS ERRNO_LOW GFACT GOWN AX 8320 (bv_unsigned sp) L A mem md O L2 A2 m2 md2 R
                REC_HOST_SETTING [canon line] O2 b ARG_I_K R3 _ L3 A3 R4 m3 md3 (dec (Z.of_nat (length toks))) p
                (Z.of_nat (length (dec (Z.of_nat (length toks)))) + 1)
                SI2 ltac:(cbn; lia) ltac:(rewrite SP3; unfold ARG_I_K, XSTRDUP_K, ALLOC_STACK; lia)
                ltac:(rewrite SP3; lia) POST3 ltac:(intros a Ha; cbv beta in Ha; cbn [length Z.of_nat]; lia)
                Hp0 FB3 BLK3 UB3 BK3 RGN3 BN3 BS3 BX3 (dec_no0 _) ltac:(unfold LMAX; lia) ltac:(unfold LMAX; lia)
                INI3 RS3 RA3 F183) as SI3.
  cbn [app] in SI3.
  pose proof POST3 as (PM3 & _ & _ & _ & _ & RP3 & _).
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 64)
                  [C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
                   C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs m2); [exact FR2|]. intros i Hi. cbn in Hi.
    destruct FB3 as (_ & FBb & _).
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW ARG_I_K L2 A2 R3 m2 md2 _ L3 A3 R4 m3 md3 (bv_unsigned sp - 64 + i)
                HM2 POST3 ltac:(lia) ltac:(rewrite SP3; lia)) as [K1 K2].
    - intros H. cbv beta in H. unfold G_REC, REC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (BLE3 : sb_le (sb_shift b A A3) (sb_malloc (sb_malloc b (Z.of_nat (length line) + 1))
                   (Z.of_nat (length (dec (Z.of_nat (length toks)))) + 1))).
  { destruct BLK3 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A A2 A3).
    rewrite <- (sb_shift_add (sb_shift b A A2) L2 A2 L3 A3 bl1 bl2 p _ EB1 EB2).
    apply sb_malloc_mono. exact BLE2. }
  rewrite E1.
  apply (HMG fx' L3 A3 R4 m3 md3 (O2 ++ [(p, Z.of_nat (length (dec (Z.of_nat (length toks)))) + 1)]) SI3 BLE3 FK).
  - exact (eq_trans (RP3 2 ltac:(unfold callee_saved; lia)) E2).
  - exact (eq_trans (RP3 4 ltac:(unfold callee_saved; lia)) E4).
  - exact (eq_trans (RP3 8 ltac:(unfold callee_saved; lia)) E8).
  - exact (eq_trans (RP3 9 ltac:(unfold callee_saved; lia)) E9).
  - exact (eq_trans (RP3 18 ltac:(unfold callee_saved; lia)) E18).
  - exact (eq_trans (RP3 19 ltac:(unfold callee_saved; lia)) E19).
  - exact (kept_ex_trans _ regs R3 R4 KE2 (kept_ex_of_pres _ _ _ RP3)).
  - exact FR3.
Qed.

Lemma hs_argl : hs_m_goal -> forall L1 A1 R1 m1 md1 O1,
  sinv B API SUP_HOST_SETTING_K (spZ regs) L A mem md O L1 A1 m1 md1 (rec_record R REC_HOST_SETTING []) O1 b ->
  sb_le (sb_shift b A A1) b ->
  getr R1 1 = Z_to_bv 64 0x16228 -> getr R1 2 = Z_to_bv 64 (spZ regs - 64) -> getr R1 4 = getr regs 4 ->
  getr R1 8 = Z_to_bv 64 0x33d10 -> getr R1 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  getr R1 10 = Z_to_bv 64 (rec_entry G_REC REC_SC R) -> getr R1 11 = getr regs 10 ->
  getr R1 18 = getr regs 12 -> getr R1 19 = getr regs 11 ->
  kept_ex [2; 8; 9; 18; 19; 20; 21; 22] regs R1 ->
  rw_cells rsegs m1 (spZ regs - 64)
    [C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
     C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  bytes_at rsegs m1 (rec_entry G_REC REC_SC R + CALL_OFF_NARGS) (le4 (Z_to_bv 64 0)) ->
  SR rsegs (mkCfg (mkst R1 (Z_to_bv 64 0x15e64) m1 (seg_rom rsegs)) md1)
    (sup_host_setting_ret (fx := fx) B API L A regs mem md line toks R O b).
Proof.
  intros HMG L1 A1 R1 m1 md1 O1 SI1 BLE1 E1 E2 E4 E8 E9 E10 E11 E18 E19 KE1 FR1 NA1.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_HOST_SETTING_K in HCEIL, SI1.
  pose proof (hs_er R) as ER.
  pose proof SA as SA0. unfold SUP_HOST_SETTING_K in SA0.
  set (e := rec_entry G_REC REC_SC R) in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (SP1 : spZ R1 = bv_unsigned sp - 64) by (unfold spZ; rewrite E2; apply unsigned_lit; lia).
  pose proof SI1 as (RJ1 & _ & _ & _ & _ & RA1 & F181 & RS1).
  pose proof RJ1 as (HM1 & _).
  assert (Hp0 : pl <> 0) by exact (proj1 SA0).
  pose proof RA as RA0. rewrite SEGS in RA0.
  destruct (sinv_str B API SEGS ERRNO_LOW SLACK 8320 (bv_unsigned sp) L A mem md O L1 A1 m1 md1 _ O1 b pl (Some line)
              SI1 RA0 ltac:(unfold NULL_LIT; lia) SA0)
    as (s & slack & P0 & PS & S0 & BS & N0 & LX & ALN & DJ & HOME & NRA).
  change (sarg (Some line)) with line in BS, N0, LX, ALN, DJ, HOME, NRA.
  assert (ES : s = pl) by (rewrite <- PS; destruct (Z.eqb_spec pl 0); [contradiction | reflexivity]).
  clear PS. subst s.
  pose proof ARGL as AL. unfold arg_line_contract in AL. rewrite SEGS in AL.
  eapply SR_bind.
  { apply (AL L1 A1 R1 m1 md1 e pl 0 line slack (sb_shift b A A1)).
    - apply (call_pre_k_of_rjr B _ 8320 (bv_unsigned sp) rec_area _ L A mem md L1 A1 m1 md1 ARG_LINE_K R1 RJ1).
      + rewrite E1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP1. replace (bv_unsigned sp - 64) with (bv_unsigned sp + (-4) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold ARG_LINE_K, REC_CANONICAL_K, ALLOC_STACK. lia.
      + rewrite SP1. unfold ARG_LINE_K, REC_CANONICAL_K, ALLOC_STACK. lia.
      + rewrite SP1. lia.
      + rewrite E4. exact HTP.
    - exact E10.
    - rewrite E11. exact A10.
    - exact (proj1 ER).
    - exact (proj1 (proj2 ER)).
    - exact (proj2 (proj2 ER)).
    - apply glob_wr_at; unfold REC_SC, G_REC, REC_SIZE, CALL_SIZE, GLOB_LO, GLOB_N in *; lia.
    - exact NA1.
    - lia.
    - exact BS.
    - exact N0.
    - exact LX.
    - exact ALN.
    - rewrite SP1. unfold ARG_LINE_K, REC_CANONICAL_K, ALLOC_STACK. lia.
    - rewrite SP1. destruct HOME as [H1|[H1|H1]]; [left; lia | right; left; exact H1 | right; right; exact H1].
    - unfold iv_apart. apply (hs_nra_apart pl _ e (e + CALL_SIZE)).
      + intros a Ha. apply NRA. rewrite length_app. cbn [length]. lia.
      + exact (proj1 (proj2 ER)).
      + exact (proj2 (proj2 ER)).
      + unfold CALL_SIZE. lia.
      + lia.
    - exact RS1.
    - apply hs_room; [unfold LMAX in *; lia|]. apply hs_ble.
      eapply sb_le_trans; [apply sb_malloc_mono; exact BLE1|]. apply sb_le_malloc.
      pose proof (dec_length (Z.of_nat (length toks)) ltac:(lia)). lia.
    - exact RA1. }
  intros c3 (L3 & A3 & R4 & m3 & md3 & -> & BK3 & UB3 & _ & RA3 & GK3 & RGN3 & ALT3).
  destruct ALT3 as [(H6 & _)|(_ & p2 & POST3 & Hp2 & _ & FB3 & BLK3 & BN3 & BS3 & BX3 & INI3 & RS3)]; [lia|].
  rewrite SEGS in RA3, BN3, BS3, BX3 |- *.
  pose proof POST3 as (PM3 & _ & _ & _ & _ & RP4 & _).
  destruct (ax_statics AX L3 A3 m3 md3 PM3) as (_ & (g & Hg & HWg) & _).
  rewrite GRD, SEGS in HWg.
  assert (F183 : f18_words rsegs m3).
  { apply (f18_words_after m1 m3 g F181); [|exact Hg | exact HWg].
    intros i Hi. pose proof (GK3 i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
  pose proof (sinv_arg B API SEGS ERRNO_LOW GFACT GOWN AX 8320 (bv_unsigned sp) L A mem md O L1 A1 m1 md1 R
                REC_HOST_SETTING [] O1 b ARG_LINE_K R1 _ L3 A3 R4 m3 md3 (canon line) p2 (Z.of_nat (length line) + 1)
                SI1 ltac:(cbn; lia) ltac:(rewrite SP1; unfold ARG_LINE_K, REC_CANONICAL_K, ALLOC_STACK; lia)
                ltac:(rewrite SP1; lia) POST3
                ltac:(intros a Ha; cbv beta in Ha; cbn [length Z.of_nat]; lia)
                Hp2 FB3 BLK3 UB3 BK3 RGN3 BN3 BS3 BX3 (canon_no0 line N0)
                ltac:(pose proof (canon_length line); unfold LMAX in *; lia)
                ltac:(pose proof (canon_length line); unfold LMAX in *; lia)
                INI3 RS3 RA3 F183) as SI3.
  cbn [app] in SI3.
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 64)
                  [C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
                   C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    destruct FB3 as (_ & FBb & _).
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW ARG_LINE_K L1 A1 R1 m1 md1 _ L3 A3 R4 m3 md3 (bv_unsigned sp - 64 + i)
                HM1 POST3 ltac:(lia) ltac:(rewrite SP1; lia)) as [K1 K2].
    - intros H. cbv beta in H. unfold G_REC, REC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS in *. lia.
    - split; [exact K1 | exact (proj1 K2)]. }
  assert (BLE3 : sb_le (sb_shift b A A3) (sb_malloc b (Z.of_nat (length line) + 1))).
  { destruct BLK3 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A A1 A3).
    rewrite <- (sb_shift_add (sb_shift b A A1) L1 A1 L3 A3 bl1 bl2 p2 _ EB1 EB2).
    apply sb_malloc_mono. exact BLE1. }
  destruct (mr_model B _ LAWS L3 A3 m3 md3 PM3) as (Hh3 & Hl3 & _).
  rewrite E1.
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply hs_mid. }
  intros ms5 (can5 & -> & EQ5).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
  apply (hs_argi HMG L3 A3 R5 m3 md3 (O1 ++ [(p2, Z.of_nat (length line) + 1)]) SI3 BLE3).
  - rewrite (getr_of_eqv _ _ 1 X5 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 2 X5 eq_refl). simp_regs. exact (eq_trans (RP4 2 ltac:(unfold callee_saved; lia)) E2).
  - rewrite (getr_of_eqv _ _ 4 X5 eq_refl). simp_regs. exact (eq_trans (RP4 4 ltac:(unfold callee_saved; lia)) E4).
  - rewrite (getr_of_eqv _ _ 8 X5 eq_refl). simp_regs. exact (eq_trans (RP4 8 ltac:(unfold callee_saved; lia)) E8).
  - rewrite (getr_of_eqv _ _ 9 X5 eq_refl). simp_regs. exact (eq_trans (RP4 9 ltac:(unfold callee_saved; lia)) E9).
  - rewrite (getr_of_eqv _ _ 10 X5 eq_refl). simp_regs. exact (eq_trans (RP4 9 ltac:(unfold callee_saved; lia)) E9).
  - rewrite (getr_of_eqv _ _ 11 X5 eq_refl). simp_regs.
    exact (eq_trans (RP4 18 ltac:(unfold callee_saved; lia)) E18).
  - rewrite (getr_of_eqv _ _ 18 X5 eq_refl). simp_regs.
    exact (eq_trans (RP4 18 ltac:(unfold callee_saved; lia)) E18).
  - rewrite (getr_of_eqv _ _ 19 X5 eq_refl). simp_regs.
    exact (eq_trans (RP4 19 ltac:(unfold callee_saved; lia)) E19).
  - apply (kept_ex_trans _ regs R1 R5 KE1). apply (kept_ex_trans _ R1 R4 R5 (kept_ex_of_pres _ _ _ RP4)).
    kept_ex_tac X5.
  - exact FR3.
  - exact BN3.
Qed.

Lemma hs_main : hs_m_goal ->
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 SUP_HOST_SETTING) mem (seg_rom (ms_segs B))) md)
    (sup_host_setting_ret (fx := fx) B API L A regs mem md line toks R O b).
Proof.
  intros HMG.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold SUP_HOST_SETTING_K in PRK, HCEIL, HWS.
  pose proof GR as GR0. pose proof RA as RA0. pose proof F18 as F180.
  rewrite SEGS in GR0, RA0, F180, HWS |- *.
  pose proof (sinv_init B API 8320 L A regs mem md R O b PRK ltac:(lia) GR0 RA0 F180 RES) as SI0.
  pose proof GR0 as (Q & HRep & HO).
  pose proof HRep as (HS & (G1 & G2 & G3 & G4 & G5 & G6) & _ & _ & HX & _).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (ST : stk rsegs mem (bv_unsigned sp - 8320) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  set (n := length (r_calls R)) in *.
  assert (NC : rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 (Z.of_nat n))])
    by (apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia | exact G3]).
  destruct (Nat.lt_ge_cases n 16) as [Hn|Hn].
  - destruct (glob_rw_cells mem (0x33d58 + 56 * Z.of_nat n) 8 ltac:(unfold GLOB_LO; lia)
                ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW].
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
      eapply hs_seg_lt; [exact ST | lia | lia | exact NC | exact Hn | exact EW]. }
    intros ms1 (can1 & (b2 & m1 & -> & MU1 & WM1 & ST1 & FR1 & NC1 & EN1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    pose proof (sinv_record_lt B API SEGS GOWN AX 8320 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _
                  REC_HOST_SETTING SI0 Hn ltac:(unfold REC_FN_COUNT, REC_HOST_SETTING; lia) MU1 WM1
                  ltac:(intros a Ra Hm; cbn in Hm; lia) NC1 EN1) as SI1.
    pose proof EN1 as ENb. apply cells_bytes_at in ENb. cbn [cells_bytes cbytes] in ENb. rewrite app_nil_r in ENb.
    apply bytes_at_app in ENb as [_ EA]. rewrite length_le4 in EA.
    apply (hs_argl HMG L A R1 m1 md O SI1 ltac:(rewrite sb_shift_refl; apply sb_le_refl)).
    + rewrite (getr_of_eqv _ _ 1 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 2 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 4 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 8 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (rec_entry_lt G_REC REC_SC R Hn). rewrite (getr_of_eqv _ _ 9 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (rec_entry_lt G_REC REC_SC R Hn). rewrite (getr_of_eqv _ _ 10 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 11 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 18 X1 eq_refl). simp_regs. reflexivity.
    + rewrite (getr_of_eqv _ _ 19 X1 eq_refl). simp_regs. reflexivity.
    + kept_ex_tac X1.
    + exact FR1.
    + rewrite (rec_entry_lt G_REC REC_SC R Hn).
      replace (G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat n + CALL_OFF_NARGS) with (0x33d58 + 56 * Z.of_nat n + Z.of_nat 4)
        by (unfold G_REC, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS; lia).
      exact EA.
  - assert (H16 : n = 16%nat) by (pose proof G1; lia).
    assert (NC16 : rw_cells rsegs mem 0x33d50 [C4 (Z_to_bv 64 16)]) by (rewrite H16 in NC; exact NC).
    eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
      eapply hs_seg_eq; [exact ST | lia | lia | exact NC16]. }
    intros ms1 (can1 & (b2 & m1 & -> & MU1 & WM1 & ST1 & FR1) & EQ1).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    assert (E1_1 : getr R1 1 = Z_to_bv 64 0x161f0) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 64))
      by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_8 : getr R1 8 = Z_to_bv 64 0x33d10) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_18 : getr R1 18 = getr regs 12) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_19 : getr R1 19 = getr regs 11) by (rewrite (getr_of_eqv _ _ 19 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_20 : getr R1 20 = getr regs 10) by (rewrite (getr_of_eqv _ _ 20 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_10 : getr R1 10 = Z_to_bv 64 0x33d10)
      by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
    assert (E1_11 : getr R1 11 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 11 X1 eq_refl); simp_regs; reflexivity).
    assert (SP1 : spZ R1 = bv_unsigned sp - 64) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
    pose proof (sinv_stack B API SEGS GOWN AX 8320 (bv_unsigned sp) L A mem md O L A mem md R O b m1 _ SI0 MU1 WM1
                  ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI1.
    apply (sinv_rcf B API SEGS ERRNO_LOW GOTG GRD GOWN AX RCF 8320 (bv_unsigned sp) L A mem md O L A m1 md R O b R1 _
             SI1 H16 E1_10 E1_11).
    + rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
    + rewrite SP1. replace (bv_unsigned sp - 64) with (bv_unsigned sp + (-4) * 16) by ring.
      rewrite Z.mod_add by lia. exact HAL.
    + rewrite SP1. unfold RCF_K, ALLOC_STACK. lia.
    + rewrite SP1. lia.
    + rewrite E1_4. exact HTP.
    + intros L' A' regs' m' md' RP' POST FRK.
      rewrite E1_1.
      pose proof POST as (RJ' & _ & _ & _ & _ & RA' & _ & _ & BLE & _).
      destruct (mr_model B _ LAWS L' A' m' md' (proj1 RJ')) as (Hh' & Hl' & _).
      assert (R8' : getr regs' 8 = Z_to_bv 64 0x33d10) by exact (eq_trans (RP' 8 ltac:(unfold callee_saved; lia)) E1_8).
      assert (FR' : rw_cells rsegs m' (bv_unsigned sp - 64)
                      [C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
                       C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
      { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
        apply FRK. rewrite SP1. lia. }
      destruct (glob_rw_cells m' 0x33d10 8 ltac:(unfold GLOB_LO; lia) ltac:(unfold GLOB_LO, GLOB_N; lia)) as [junk EW].
      eapply evt_SR_canon; [ | exact Hh' | exact Hl' | ].
      { rewrite canon_mkst. unfold Regs6ss.mkR_of.
        assert (Q8 : reg_get regs' 8 = Z_to_bv 64 0x33d10) by exact R8'.
        rewrite Q8.
        eapply hs_ret16. exact EW. }
      intros ms2 (can2 & (m2 & -> & MU2 & WM2 & EN2) & EQ2).
      destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
      destruct (sinv_record_full B API SEGS GOWN AX 8320 (bv_unsigned sp) L A mem md O L A m1 R O b L' A' m' md' m2
                  _ REC_HOST_SETTING POST ltac:(unfold REC_FN_COUNT, REC_HOST_SETTING; lia) MU2 WM2
                  ltac:(intros a Ra Hm; cbn in Hm; unfold REC_SC; lia) EN2) as (Oc' & SI2).
      assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 64)
                      [C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
                       C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
      { apply (rw_cells_transport rsegs _ m' m2 _ _ FR' MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
        repeat split; lia. }
      pose proof EN2 as ENb. apply cells_bytes_at in ENb. cbn [cells_bytes cbytes] in ENb. rewrite app_nil_r in ENb.
      apply bytes_at_app in ENb as [_ EA]. rewrite length_le4 in EA.
      rewrite sb_shift_refl in BLE.
      apply (hs_argl HMG L' A' R2 m2 md' Oc' SI2 BLE).
      * rewrite (getr_of_eqv _ _ 1 X2 eq_refl). simp_regs. reflexivity.
      * rewrite (getr_of_eqv _ _ 2 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 2 ltac:(unfold callee_saved; lia)) E1_2).
      * rewrite (getr_of_eqv _ _ 4 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 4 ltac:(unfold callee_saved; lia)) E1_4).
      * rewrite (getr_of_eqv _ _ 8 X2 eq_refl). simp_regs. reflexivity.
      * rewrite (rec_entry_full G_REC REC_SC R H16). rewrite (getr_of_eqv _ _ 9 X2 eq_refl). simp_regs. reflexivity.
      * rewrite (rec_entry_full G_REC REC_SC R H16). rewrite (getr_of_eqv _ _ 10 X2 eq_refl). simp_regs. reflexivity.
      * rewrite (getr_of_eqv _ _ 11 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 20 ltac:(unfold callee_saved; lia)) E1_20).
      * rewrite (getr_of_eqv _ _ 18 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 18 ltac:(unfold callee_saved; lia)) E1_18).
      * rewrite (getr_of_eqv _ _ 19 X2 eq_refl). simp_regs.
        exact (eq_trans (RP' 19 ltac:(unfold callee_saved; lia)) E1_19).
      * apply (kept_ex_trans _ regs R1 R2); [kept_ex_tac X1|].
        apply (kept_ex_trans _ R1 regs' R2 (kept_ex_of_pres _ _ _ RP')). kept_ex_tac X2.
      * exact FR2.
      * rewrite (rec_entry_full G_REC REC_SC R H16).
        replace (REC_SC + CALL_OFF_NARGS) with (0x33d10 + Z.of_nat 4) by (unfold REC_SC, CALL_OFF_NARGS; lia).
        exact EA.
Qed.

Lemma hs_ptok : forall Lc Ac mc mdc,
  rjr B (aa_MR API) 8320 (spZ regs) rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc ->
  ro_agree rsegs mc -> bytes_at rsegs mc ptok (concat (map (fun p => le8 (Z_to_bv 64 p)) ps)).
Proof.
  intros Lc Ac mc mdc RJ RAc. pose proof alloc_ceiling_val as AC.
  pose proof RJ as (_ & _ & _ & _ & _ & _ & _ & K1 & K2 & K3 & HF & HRM & HKP & _).
  pose proof (Forall2_length TKS) as LT.
  pose proof PTB as BX. rewrite SEGS in BX.
  pose proof RA as RA0. rewrite SEGS in RA0.
  pose proof PTH as HOME. unfold buf_home in HOME. rewrite SEGS in HOME.
  apply (bytes_at_transfer rsegs mem); [exact BX|]. intros i Hi. rewrite hs_concat_len, LT in Hi.
  destruct HOME as [(H1 & H2) | [(qb & kb & Hq & Hnq & H1 & H2) | (H1 & H2 & H3)]].
  - rewrite <- SEGS. refine (proj1 (HF (ptok + i) _ _ _ _)).
    + unfold free_a. left. lia.
    + lia.
    + pose proof ERRNO_LOW. lia.
    + apply PTR. lia.
  - unfold blocks in Hq. apply in_map_iff in Hq as ([pb kb'] & E & Hpb). cbn [fst snd] in E.
    injection E as E1 E2. subst qb kb.
    rewrite <- SEGS. replace (ptok + i) with (ptr_addr L pb + (ptok + i - ptr_addr L pb)) by ring.
    apply (HKP pb kb' (ptok + i - ptr_addr L pb) Hpb); [|lia].
    intros G. apply Hnq. apply in_map_iff. exists (ptr_addr L pb, kb'). split; [reflexivity | exact G].
  - rewrite (mbyte_ro_agree _ _ _ RAc (H3 i Hi)), (mbyte_ro_agree _ _ _ RA0 (H3 i Hi)). reflexivity.
Qed.

Lemma hs_toks_f : forall Lc Ac mc mdc Rc Oc bc,
  sinv B API 8320 (spZ regs) L A mem md O Lc Ac mc mdc Rc Oc bc -> ro_agree rsegs mc ->
  Forall2 (tokf (normalize rsegs mc)) ps toks.
Proof.
  intros Lc Ac mc mdc Rc Oc bc SI RAc. pose proof RA as RA0. rewrite SEGS in RA0.
  pose proof alloc_ceiling_val as AC. pose proof PRE as (PRK & _).
  pose proof PRK as (_ & _ & _ & _ & _ & HCEIL & _). unfold SUP_HOST_SETTING_K in HCEIL.
  eapply Forall2_impl; [|exact TKS]. intros p w Hp. unfold SUP_HOST_SETTING_K in Hp.
  destruct (sinv_str B API SEGS ERRNO_LOW SLACK 8320 (spZ regs) L A mem md O Lc Ac mc mdc Rc Oc bc p (Some w)
              SI RA0 ltac:(unfold NULL_LIT; lia) Hp) as (s & slack & P0 & PS & S0 & BS & N0 & LX & ALN & _).
  change (sarg (Some w)) with w in BS, N0, LX, ALN.
  assert (Hp0 : p <> 0) by exact (proj1 Hp).
  assert (ES : s = p) by (rewrite <- PS; destruct (Z.eqb_spec p 0); [contradiction | reflexivity]).
  clear PS. subst s.
  unfold tokf. exists slack.
  split; [exact (bytes_at_normalize rsegs mc _ _ RAc BS)|]. split; [exact N0|]. split; [exact ALN | lia].
Qed.

Lemma hs_am : forall (fx' : YK11.FPState) L4 A4 R4 m4 md4 O4 (q : sptr),
  sinvT B API (ptr_addr L4 q, sup_host_setting_len toks + 1) SUP_HOST_SETTING_K (spZ regs) L A mem md O L4 A4 m4 md4
    (rec_record R REC_HOST_SETTING [canon line; dec (Z.of_nat (length toks))]) O4 b ->
  In (q, sup_host_setting_len toks + 1) (user_blocks A4) -> ptr_addr L4 q mod 16 = 0 ->
  sb_le (sb_shift b A A4)
    (sb_malloc (sb_malloc (sb_malloc b (Z.of_nat (length line) + 1))
       (Z.of_nat (length (dec (Z.of_nat (length toks)))) + 1)) (sup_host_setting_len toks + 1)) ->
  fp_kept fx fx' ->
  getr R4 2 = Z_to_bv 64 (spZ regs - 64) -> getr R4 4 = getr regs 4 ->
  getr R4 8 = Z_to_bv 64 0x33d10 -> getr R4 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R) ->
  getr R4 10 = Z_to_bv 64 (ptr_addr L4 q) -> getr R4 18 = getr regs 12 -> getr R4 19 = getr regs 11 ->
  kept_ex [2; 8; 9; 18; 19; 20; 21; 22] regs R4 ->
  rw_cells rsegs m4 (spZ regs - 64)
    [C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
     C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  SR rsegs (mkCfg (@mkst fx' R4 (Z_to_bv 64 0x16278) m4 (seg_rom rsegs)) md4)
    (sup_host_setting_ret (fx := fx) B API L A regs mem md line toks R O b).
Proof.
  intros fx' L4 A4 R4 m4 md4 O4 q SI QIN QA BLE FK E2 E4 E8 E9 E10 E18 E19 KE FR.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof alloc_ceiling_value as ACV.
  pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_HOST_SETTING_K in HCEIL, HWS, SI.
  pose proof RA as RA0. rewrite SEGS in RA0.
  pose proof PTW as PTW0. unfold SUP_HOST_SETTING_K in PTW0.
  pose proof SI as (RJ & GR4 & _ & _ & B2 & RA4 & F184 & RS4 & TI & TO & TAo & TP).
  pose proof RJ as (HM & _ & _ & _ & _ & HLen & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  destruct (mr_model B _ LAWS L4 A4 m4 md4 HM) as (Hh & Hl & _).
  assert (HN : (length (r_calls R) <= 16)%nat).
  { pose proof GR as (Q0 & (_ & (C1 & _) & _) & _). exact C1. }
  destruct (rec_rep_entry _ _ _ _ _ _ _ _ _ _ GR4 HN) as (P & CA).
  destruct CA as (_ & _ & _ & _ & CNA & _). cbn [snd length Z.of_nat] in CNA.
  pose proof (hs_entry_bounds R) as (EB1 & EB2).
  pose proof (Forall2_length TKS) as LT.
  set (e := rec_entry G_REC REC_SC R) in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  set (t := ptr_addr L4 q) in *.
  set (nT := sup_host_setting_len toks + 1) in *.
  assert (NTE : nT = sup_host_setting_len toks + 1) by reflexivity.
  cbn [fst snd] in TP.
  destruct (block_facts B _ LAWS L4 A4 m4 md4 t nT 0 HM TI ltac:(lia)) as (_ & T1 & T2 & _).
  set (Tlen := 8 * ((t + nT + 7) / 8) - t).
  assert (TLE : Tlen = 8 * ((t + nT + 7) / 8) - t) by reflexivity.
  assert (TLa : nT <= Tlen /\ (t + Tlen) mod 8 = 0 /\ t + Tlen <= alloc_ceiling).
  { destruct ACV as (_ & ACM).
    pose proof (Z.div_mod (t + nT + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (t + nT + 7) 8 ltac:(lia)).
    pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)).
    rewrite TLE. replace (t + (8 * ((t + nT + 7) / 8) - t)) with (8 * ((t + nT + 7) / 8)) by ring.
    split; [lia|]. split; [rewrite Z.mul_comm, Z_mod_mult; reflexivity | lia]. }
  destruct TLa as (TL1 & TL2 & TL3).
  assert (U2 : bv_unsigned (reg_get R4 2) = bv_unsigned sp - 64).
  { change (reg_get R4 2) with (getr R4 2). rewrite E2. apply unsigned_lit. lia. }
  assert (NRO : forall i, 0 <= i < nT -> ro_addr rsegs (Z_to_bv 64 (t + i)) = false).
  { intros i Hi. destruct (ro_addr rsegs (Z_to_bv 64 (t + i))) eqn:E; [|reflexivity]. exfalso.
    apply (hs_blk_img B API AX L4 A4 m4 md4 t nT i HM TI Hi). apply (ro_in_img B SEGS); [lia | exact E]. }
  destruct (rs_bytes_pad rsegs m4 t [] (Z.to_nat Tlen)) as (X0 & X0L & X0B).
  { split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi. lia. }
  { cbn [length]. lia. }
  { intros j Hj. replace (t + Z.of_nat (length (@nil byte)) + Z.of_nat j) with (t + Z.of_nat j) by (cbn [length]; lia).
    apply hs_present.
    destruct (Z_lt_ge_dec (Z.of_nat j) nT) as [Hjl|Hjg].
    - exact (proj1 (block_facts B _ LAWS L4 A4 m4 md4 t nT (Z.of_nat j) HM TI ltac:(lia))).
    - apply (SLACK L4 A4 m4 md4 t nT _ HM TI). lia. }
  cbn [app] in X0B.
  assert (JI : jinvX (reg_get R4 2) t nT Tlen (bv_unsigned sp - 8320) (normalize rsegs m4) (normalize rsegs m4) X0).
  { split; [apply mem_inv_normalize|].
    split.
    { rewrite U2. apply stk_norm; [lia | lia |]. intros a Ha. rewrite <- SEGS. apply HSC. left. lia. }
    split; [apply munch_refl|].
    split; [apply wmono_refl|].
    split.
    { split; [lia|]. split; [lia|]. intros i Hi.
      destruct (block_facts B _ LAWS L4 A4 m4 md4 t nT i HM TI Hi) as ((bb & Eb) & _).
      apply (present_writable rsegs _ (t + i)). exists bb. unfold normalize. cbv beta. rewrite (NRO i Hi). exact Eb. }
    split; [exact (bytes_at_normalize rsegs m4 _ _ RA4 X0B)|].
    rewrite X0L. lia. }
  assert (TA8 : t mod 8 = 0) by lia.
  assert (TKJ : Forall2 (tokj (reg_get R4 2) t nT (bv_unsigned sp - 8320) (normalize rsegs m4)) ps toks).
  { eapply Forall2_impl; [|exact TKS]. intros p w Hp. unfold SUP_HOST_SETTING_K in Hp.
    destruct (hs_tstr _ 8320 (bv_unsigned sp) L A mem md O L4 A4 m4 md4 _ O4 b p w SI TA8 RA0 Hp)
      as (sl & BS & N0 & P0 & PAD & DJ & DT).
    unfold tokj. exists sl.
    split; [exact (bytes_at_normalize rsegs m4 _ _ RA4 BS)|]. split; [exact N0|].
    split; [rewrite PAD; lia|]. split; [exact P0|]. rewrite U2.
    split; [destruct DJ as [D|D]; [left; lia | right; lia]|]. exact DT. }
  pose proof (bytes_at_normalize rsegs m4 _ _ RA4 (hs_ptok L4 A4 m4 md4 RJ RA4)) as PBn.
  assert (PW2 : ptok + 8 * Z.of_nat (length ps) <= t \/ t + nT <= ptok).
  { rewrite LT. exact (hs_home_T _ 8320 (bv_unsigned sp) L A mem md O L4 A4 m4 md4 _ O4 b ptok
                         (8 * Z.of_nat (length toks)) SI ltac:(lia) PTH). }
  assert (NAn : rw_cells rsegs (normalize rsegs m4) (e + 4) [C4 (Z_to_bv 64 2)]).
  { apply rw_cells_normalize; [exact RA4 | | intros i Hi; cbn in Hi; apply glob_ro_false; unfold GLOB_LO, GLOB_N; lia].
    apply bytes_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia|]. unfold CALL_OFF_NARGS in CNA. exact CNA. }
  assert (ND1 : e + 8 <= t \/ t + nT <= e + 4).
  { destruct (Z_le_gt_dec (e + 8) t) as [D1|D1]; [left; exact D1|].
    destruct (Z_le_gt_dec (t + nT) (e + 4)) as [D2|D2]; [right; exact D2|]. exfalso.
    apply (hs_blk_img B API AX L4 A4 m4 md4 t nT (Z.max (e + 4) t - t) HM TI ltac:(lia)).
    replace (t + (Z.max (e + 4) t - t)) with (Z.max (e + 4) t) by ring.
    assert (GI : GLOB_LO <= Z.max (e + 4) t < GLOB_LO + Z.of_nat GLOB_N) by (unfold GLOB_LO, GLOB_N; lia).
    exact (proj1 (GFACT (Z.max (e + 4) t) (glob_in (Z.max (e + 4) t) GI))). }
  assert (Q9 : reg_get R4 9 = Z_to_bv 64 e) by exact E9.
  assert (Q10 : reg_get R4 10 = Z_to_bv 64 t) by exact E10.
  assert (Q18 : reg_get R4 18 = Z_to_bv 64 (Z.of_nat (length ps))) by (rewrite LT; exact (eq_trans E18 A12)).
  assert (Q19 : reg_get R4 19 = Z_to_bv 64 ptok) by exact (eq_trans E19 A11).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q9, Q10, Q18, Q19.
    eapply (evt_normalize rsegs); [exact WX | exact RA4 |].
    eapply (hs_e2x STRLEN STRCAT _ _ _ _ _ _ _ _ _ _ _ t nT Tlen (bv_unsigned sp - 8320) e (normalize rsegs m4)
              ps toks ptok X0);
      [lia | lia | lia | exact TL2 | lia | rewrite U2; lia | exact JI | exact TKJ | exact PBn
      | rewrite U2; rewrite LT; lia | exact PW2 | rewrite LT; lia | lia | exact NAn | exact ND1 | rewrite U2; lia]. }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m5n & slack
    & -> & JI5).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m5. intros m5 EC1 MR1r RO1 EQ1. subst can1.
  destruct JI5 as (MI5 & ST5 & MU5n & WM5n & HW5 & HB5 & HL5).
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m4 RA4) MR1r RO1 MU5n) as MU5.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m4 RA4) MR1r RO1 WM5n) as WM5.
  pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ MR1r) HB5) as BJ.
  rewrite U2 in MU5.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R5 & -> & X5).
  assert (SI5 : sinvT B API (t, nT) 8320 (bv_unsigned sp) L A mem md O L4 A4 m5 md4
                  (rec_record R REC_HOST_SETTING [canon line; dec (Z.of_nat (length toks))]) O4 b).
  { apply (sinvT_munch B API SEGS GOTG GRD GOWN AX (t, nT) 8320 (bv_unsigned sp) L A mem md O L4 A4 m4 md4 _ O4 b m5 _
             SI MU5 WM5).
    intros a Ra Hm. cbn [outside] in Hm. cbn [fst snd]. lia. }
  assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp - 64)
                  [C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
                   C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transport rsegs _ m4 m5 _ _ FR MU5 WM5). cbn [disjoint_from cells_size csize Nat.add].
    repeat split; lia. }
  pose proof HL5 as HL5'. rewrite length_app in HL5'. cbn [length] in HL5'.
  apply (hs_xs fx' L4 A4 R5 m5 md4 O4 q slack SI5 QIN BLE FK).
  - rewrite (getr_of_eqv _ _ 1 X5 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 2 X5 eq_refl). simp_regs. exact E2.
  - rewrite (getr_of_eqv _ _ 4 X5 eq_refl). simp_regs. exact E4.
  - rewrite (getr_of_eqv _ _ 8 X5 eq_refl). simp_regs. exact E8.
  - rewrite (getr_of_eqv _ _ 9 X5 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 10 X5 eq_refl). simp_regs. reflexivity.
  - rewrite (getr_of_eqv _ _ 20 X5 eq_refl). simp_regs. reflexivity.
  - apply (kept_ex_trans _ regs R4 R5 KE). kept_ex_tac X5.
  - exact FR5.
  - exact BJ.
  - change (ptr_addr L4 q) with t.
    assert (EM : (- (t + Tlen)) mod 8 = 0) by (apply Z_mod_zero_opp_full; exact TL2).
    replace (- (t + Z.of_nat (length (join_sp toks)) + 1)) with (Z.of_nat (length slack) + - (t + Tlen)) by lia.
    rewrite Zplus_mod, EM, Z.add_0_r, Z.mod_mod by lia. apply Z.mod_le; lia.
  - change (ptr_addr L4 q) with t. rewrite HL5. lia.
Qed.

Lemma hs_m : hs_m_goal.
Proof.
  unfold hs_m_goal. intros fx' L2 A2 R2 m2 md2 O2 SI2 BLE2 FK E2 E4 E8 E9 E18 E19 KE2 FR2.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof PRE as (PRK & TS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  unfold SUP_HOST_SETTING_K in HCEIL, HWS, SI2.
  pose proof SI2 as (RJ2 & _ & _ & _ & _ & RA2 & F182 & RS2).
  pose proof RJ2 as (HM2 & _).
  destruct (mr_model B _ LAWS L2 A2 m2 md2 HM2) as (Hh & Hl & _).
  pose proof (Forall2_length TKS) as LT.
  pose proof (hs_len_nn toks) as LN.
  pose proof (hs_toks_f L2 A2 m2 md2 _ O2 b SI2 RA2) as TF.
  pose proof (bytes_at_normalize rsegs m2 _ _ RA2 (hs_ptok L2 A2 m2 md2 RJ2 RA2)) as PBn.
  pose proof (bytes_at_bound _ _ _ _ PBn) as PBB. rewrite hs_concat_len in PBB.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (Q18 : reg_get R2 18 = Z_to_bv 64 (Z.of_nat (length ps))) by (rewrite LT; exact (eq_trans E18 A12)).
  assert (Q19 : reg_get R2 19 = Z_to_bv 64 ptok) by exact (eq_trans E19 A11).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q18, Q19.
    eapply (evt_normalize rsegs); [exact WX | exact RA2 |].
    eapply (hs_e1 _ _ _ _ _ _ _ _ _ _ _ _ (ptok + 8 * Z.of_nat (length ps)) STRLEN);
      [apply mem_inv_normalize | exact TF | exact PBn | rewrite LT; lia | lia | lia | lia | reflexivity]. }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1n & -> & MU1n
    & MI1n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m3. intros m3 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR1r RO1 MU1n) as MU1.
  assert (WM1 : wmono rsegs m2 m3).
  { intros x Hx. unfold wview in *. rewrite (MU1 x I). exact Hx. }
  pose proof (ro_agree_of_mem_rel rsegs _ _ MR1r) as RA3.
  pose proof (sinv_stack B API SEGS GOWN AX 8320 (bv_unsigned sp) L A mem md O L2 A2 m2 md2 _ O2 b m3 [] SI2 MU1 WM1
                ltac:(intros a Ra Hm; exfalso; exact (Hm I))) as SI3.
  pose proof SI3 as (RJ3 & _ & _ & _ & _ & _ & _ & RS3).
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 64)
                  [C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
                   C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transport rsegs [] m2 m3 _ _ FR2 MU1 WM1). cbn [disjoint_from]. exact I. }
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R3 & -> & X3).
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x16278) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp - 64))
    by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs; exact E2).
  assert (E3_4 : getr R3 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X3 eq_refl); simp_regs; exact E4).
  assert (E3_8 : getr R3 8 = Z_to_bv 64 0x33d10) by (rewrite (getr_of_eqv _ _ 8 X3 eq_refl); simp_regs; exact E8).
  assert (E3_9 : getr R3 9 = Z_to_bv 64 (rec_entry G_REC REC_SC R))
    by (rewrite (getr_of_eqv _ _ 9 X3 eq_refl); simp_regs; exact E9).
  assert (E3_10 : getr R3 10 = Z_to_bv 64 (sup_host_setting_len toks + 1))
    by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_18 : getr R3 18 = getr regs 12).
  { rewrite (getr_of_eqv _ _ 18 X3 eq_refl). simp_regs. rewrite A12, LT. reflexivity. }
  assert (E3_19 : getr R3 19 = getr regs 11).
  { rewrite (getr_of_eqv _ _ 19 X3 eq_refl). simp_regs. rewrite A11. reflexivity. }
  assert (KE3 : kept_ex [2; 8; 9; 18; 19; 20; 21; 22] regs R3).
  { apply (kept_ex_trans _ regs R2 R3 KE2). kept_ex_tac X3. }
  assert (SP3 : spZ R3 = bv_unsigned sp - 64) by (unfold spZ; rewrite E3_2; apply unsigned_lit; lia).
  replace (Z_to_bv 64 0x18a0c) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALLOC_PC; reflexivity).
  pose proof (MALLOC fx') as MAL. unfold malloc_contract in MAL. rewrite SEGS in MAL.
  eapply SR_bind.
  { apply (MAL L2 A2 R3 m3 md2 (sup_host_setting_len toks + 1) (sb_shift b A A2)).
    - apply (proj2 (call_pre_k_alloc B (aa_MR API) _ _ _ _ _)).
      apply (call_pre_k_of_rjr B _ 8320 (bv_unsigned sp) rec_area _ L A mem md L2 A2 m3 md2 ALLOC_STACK R3 RJ3).
      + rewrite E3_1. apply bv_eq. vm_compute. reflexivity.
      + rewrite SP3. replace (bv_unsigned sp - 64) with (bv_unsigned sp + (-4) * 16) by ring.
        rewrite Z.mod_add by lia. exact HAL.
      + unfold ALLOC_STACK. lia.
      + rewrite SP3. unfold ALLOC_STACK. lia.
      + rewrite SP3. lia.
      + rewrite E3_4. exact HTP.
    - exact RA3.
    - exact E3_10.
    - exact RS3.
    - apply hs_room; [unfold LMAX in *; lia|]. apply hs_ble. exact BLE2. }
  intros c4 (L4 & A4 & R4 & m4 & md4 & res & -> & POST4 & A04 & NZ & AL16 & FB4 & BLK4 & BK4 & RA4 & GK4 & UB4
    & INI4 & RGN4 & RS4).
  rewrite SEGS in RA4.
  pose proof (sinvT_malloc B API SEGS ERRNO_LOW GOTG GRD GFACT GOWN AX 8320 (bv_unsigned sp) L A mem md O L2 A2 m3 md2 _
                O2 b ALLOC_STACK R3 L4 A4 R4 m4 md4 res (sup_host_setting_len toks + 1) SI3
                ltac:(rewrite SP3; unfold ALLOC_STACK; lia) ltac:(rewrite SP3; lia) POST4 ltac:(lia) FB4 BLK4 UB4 BK4
                RGN4 INI4 RS4 RA4 GK4) as SIT.
  assert (INB : In (res, sup_host_setting_len toks + 1) (blocks L4 A4)).
  { destruct BLK4 as (bl1 & bl2 & EB1 & _). rewrite EB1. apply in_or_app. right. left. reflexivity. }
  unfold blocks in INB. apply in_map_iff in INB as ([q k'] & EQ & QIN). cbn [fst snd] in EQ.
  injection EQ as QE1 QE2. subst k'.
  rewrite <- QE1 in SIT, A04, AL16.
  pose proof POST4 as (PM4 & _ & _ & _ & _ & RP4 & _).
  assert (BLE4 : sb_le (sb_shift b A A4)
                   (sb_malloc (sb_malloc (sb_malloc b (Z.of_nat (length line) + 1))
                      (Z.of_nat (length (dec (Z.of_nat (length toks)))) + 1)) (sup_host_setting_len toks + 1))).
  { destruct BLK4 as (bl1 & bl2 & EB1 & EB2).
    rewrite <- (sb_shift_trans b A A2 A4).
    rewrite <- (sb_shift_add (sb_shift b A A2) L2 A2 L4 A4 bl1 bl2 res _ EB1 EB2).
    apply sb_malloc_mono. exact BLE2. }
  pose proof RJ3 as (HM3 & _).
  assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp - 64)
                  [C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
                   C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs m3); [exact FR3|]. intros i Hi. cbn in Hi.
    destruct (post_k_keep_hi B API SEGS ERRNO_LOW ALLOC_STACK L2 A2 R3 m3 md2 _ L4 A4 R4 m4 md4 (bv_unsigned sp - 64 + i)
                HM3 POST4 ltac:(lia) ltac:(rewrite SP3; unfold ALLOC_STACK; lia)) as [K1 K2].
    - intros H. exact H.
    - split; [exact K1 | exact (proj1 K2)]. }
  rewrite E3_1, SEGS.
  apply (hs_am fx' L4 A4 R4 m4 md4 O2 q SIT QIN AL16 BLE4 FK).
  - exact (eq_trans (RP4 2 ltac:(unfold callee_saved; lia)) E3_2).
  - exact (eq_trans (RP4 4 ltac:(unfold callee_saved; lia)) E3_4).
  - exact (eq_trans (RP4 8 ltac:(unfold callee_saved; lia)) E3_8).
  - exact (eq_trans (RP4 9 ltac:(unfold callee_saved; lia)) E3_9).
  - exact A04.
  - exact (eq_trans (RP4 18 ltac:(unfold callee_saved; lia)) E3_18).
  - exact (eq_trans (RP4 19 ltac:(unfold callee_saved; lia)) E3_19).
  - exact (kept_ex_trans _ regs R3 R4 KE3 (kept_ex_of_pres _ _ _ RP4)).
  - exact FR4.
Qed.

End Run.

Theorem sup_host_setting_holds : sup_host_setting_contract B API.
Proof.
  unfold sup_host_setting_contract.
  intros L A regs mem md pl ptok ps line toks R O b PRE A10 A11 A12 NT SA PT0 PT8 PTB PTW PTH PTR TKS TLEN GR RA FRM
    F18 RES ROOM.
  eapply hs_main; try eassumption.
  eapply hs_m; eassumption.
Qed.

End P.
